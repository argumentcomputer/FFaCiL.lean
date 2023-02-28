import FF.NewField

/--
Curves with Weierstrass form satisfying the equation `y² = x³ + a x + b`
for a prime field `F` such that `char K > 3`
-/
structure Curve (F : Type _) [PrimeField F] where
  a : F
  b : F

structure ProjectivePoint {F : Type _} [PrimeField F] (C : Curve F) where
  X : F
  Y : F
  Z : F

instance [ToString F] [PrimeField F] {C : Curve F} : ToString $ ProjectivePoint C where
  toString := fun ⟨x, y, z⟩ => s!"({x} : {y} : {z})"

def ProjectivePoint.isInfinity {F : Type _} [PrimeField F] {C : Curve F} (P : ProjectivePoint C) :=
  P.X == 0 && P.Y == 1 && P.Z == 0

def ProjectivePoint.infinity {F : Type _} [PrimeField F] {C : Curve F} : ProjectivePoint C :=
  ⟨0, 1, 0⟩

def ProjectivePoint.add {F : Type _} [PrimeField F] {C : Curve F} : ProjectivePoint C → ProjectivePoint C → ProjectivePoint C
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => 
    let a := y₂ * z₁ - y₁ * z₂
    let b := x₂ * z₁ - x₁ * z₂
    let c := a^2 * z₁ * z₂ - b^3 - (2 : Nat) * b^2 * x₁ * z₂
    let x₃ := b * c
    let y₃ := a * (b^2 * x₁ * z₂ - c) - b^3 * y₁ * z₂
    let z₃ := b^3 * z₁ * z₂
    ⟨x₃, y₃, z₃⟩

partial def ProjectivePoint.scaleAux {F : Type _} [PrimeField F] {C : Curve F} (n : Nat) 
  (P acc : ProjectivePoint C) : ProjectivePoint C :=
  if n == 0 then acc else
    if n % 2 == 0 then
      scaleAux (n >>> 1) (add P P) (add P acc)
    else
      scaleAux (n >>> 1) (add P P) acc
  

inductive AffinePoint {F : Type _} [PrimeField F] (C : Curve F) where
  | affine (X : F) (Y : F) : AffinePoint C
  | infinity : AffinePoint C

def AffinePoint.add {F : Type _} [PrimeField F] {C : Curve F} : AffinePoint C → AffinePoint C → AffinePoint C
  | .infinity, _ => .infinity
  | _, .infinity => .infinity
  | .affine x₁ y₁, .affine x₂ y₂ =>
      let lambda := (y₁ + y₂) / (x₁ + y₂)
      let x₃ := lambda^2 + lambda + x₁ + x₂ + Curve.a C
      let y₃ := lambda * (x₁ + x₃) + x₃ + x₁
      .affine x₃ y₃

class CurveGroup {F : Type _} [PrimeField F] (C : Curve F) (K : outParam $ Type _) where 
  zero : K
  inv : K → K
  add : K → K → K
  double : K → K

instance {F K : Type _} [PrimeField F] (C : Curve F) [CurveGroup C K] : Add K where
  add := CurveGroup.add C

instance {F K : Type _} [PrimeField F] (C : Curve F) [CurveGroup C K] : Neg K where
  neg := CurveGroup.inv C

open CurveGroup in
partial def smulAux [PrimeField F] (C : Curve F)
  [CurveGroup C K] (n : Nat) (p : K) (acc : K) : K :=
  if n == 0 then acc
  else match n % 2 == 0 with
    | true => smulAux C (n >>> 1) (add C p p) (add C p acc)
    | false => smulAux C (n >>> 1) (add C p p) acc

open CurveGroup in
/--
Montgomery's ladder for fast scalar-point multiplication
-/
def smul [PrimeField F] {C : Curve F}
  [CurveGroup C K] (n : Nat) (p : K) : K := smulAux C n p (zero C)

instance {F K : Type _} [f : PrimeField F] (C : Curve F) [gr : CurveGroup C K] : HMul Nat K K where
  hMul := @smul F K f C gr
  
open ProjectivePoint in
instance {F : Type _} [PrimeField F] {C : Curve F} : CurveGroup C (ProjectivePoint C) where 
  zero := infinity
  inv := fun ⟨x, y, z⟩ => ⟨x, 0 - y, z⟩ 
  add := ProjectivePoint.add
  double := fun ⟨x, y, z⟩ =>
    let a := C.a * z^2 + (3 : Nat) * x^2
    let b := y * z
    let c := x * y * b
    let d := a^2 - (8 : Nat) * c
    let x₁ := (2 : Nat) * b * d
    let y₁ := a * ((4 : Nat) * c - d) - b^3 * y * z
    let z₁ := (8 : Nat) * b^3
    ⟨x₁, y₁, z₁⟩

def affineDouble [PrimeField F] {C : Curve F} :
  AffinePoint C → AffinePoint C
  | .affine x y =>
    let lambda := ((3 : Nat) * x^2 + Curve.a C) / (2 : Nat) * y
    let x' := lambda^2 - (2 : Nat) * x
    let y' := lambda * (x - x') - y
    .affine x' y'
  | .infinity => .infinity

instance {F : Type _} [PrimeField F] {C : Curve F} : CurveGroup C (AffinePoint C) where 
  zero := .infinity
  inv p :=
    match p with
      | .affine X Y => .affine X (- Y)
      | x           => x
  add := AffinePoint.add
  double := affineDouble

new_field Fp with
  prime: 101
  generator: 2

instance : ToString Fp where
  toString n := toString ∘ NewField.natRepr $ n

def NewCurve : Curve Fp where
  a := 2
  b := 3  

def G : ProjectivePoint NewCurve := ⟨52, 74, 1⟩

#eval G + G
def mulBy2 := ProjectivePoint.scaleAux 2 G .infinity
#eval mulBy2

#eval 2 * G
#eval CurveGroup.double NewCurve G