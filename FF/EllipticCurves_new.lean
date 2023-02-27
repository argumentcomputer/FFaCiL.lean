import FF.NewField

import YatimaStdLib.Bit

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

def ProjectivePoint.add {F : Type _} [PrimeField F] {C : Curve F} (P Q : ProjectivePoint C) : ProjectivePoint C :=
  let ⟨x₁, y₁, z₁⟩ := P
  let ⟨x₂, y₂, z₂⟩ := Q
    match P.isInfinity, Q.isInfinity with
      | true, _ => Q
      | _, true => P
      | false, false =>
        let y₁z₂ := y₁ * z₂
        let x₁z₂ := x₁ * z₂
        let z₁z₂ := z₁ * z₂
        let u := y₂ * z₁ - y₁z₂
        let uSquare := u * u
        let v := x₂ * z₁ - x₁z₂
        let vSquare := v^2
        let vCube := v^3
        let r := vSquare * x₁z₂
        let a := uSquare * z₁z₂ - vCube - (2 : Nat) * r
        ⟨v * a, u * (r - a) - vCube * y₁z₂, vCube * z₁z₂⟩

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
partial def smulAux [PrimeField F] {C : Curve F}
  [CurveGroup C K] (n : Nat) (p : K) (acc : K) : K :=
  if n == 0 then acc
  else match n % 2 == 0 with
    | true => @smulAux _ _ _ C _ (n >>> 1) (add C p p) (add C p acc)
    | false => @smulAux _ _ _ C _ (n >>> 1) (add C p p) acc

open CurveGroup in
/--
Montgomery's ladder for fast scalar-point multiplication
-/
def smul [PrimeField F] {C : Curve F}
  [CurveGroup C K] (n : Nat) (p : K) : K := Id.run do
  @smulAux _ _ _ C _ n p (zero C)
/--
  let mut p₁ := p
  let mut p₂ := double C p
  let n₂ := n.toBits
  for i in [0:n₂.length - 1] do
    if List.get? n₂ i == some 0 then
    p₁ := double C p₁
    p₂ := add C p₁ p₂
    else
    p₁ := add C p₁ p₂
    p₂ := double C p₂
  return p₂
-/

instance {F K : Type _} [f : PrimeField F] (C : Curve F) [gr : CurveGroup C K] : HMul Nat K K where
  hMul := @smul F K f C gr
  
open ProjectivePoint in
instance {F : Type _} [PrimeField F] {C : Curve F} : CurveGroup C (ProjectivePoint C) where 
  zero := infinity
  inv := fun ⟨x, y, z⟩ => ⟨x, 0 - y, z⟩ 
  add := ProjectivePoint.add
  double := fun p@⟨x, y, z⟩ => if p.isInfinity then infinity
    else
    let xSquare := x * x
    let zSquare := z * z
    let w := C.a * zSquare + (3 : Nat) * xSquare
    let s := (2 : Nat) * y * z
    let sCube := s * s * s
    let r := y * s
    let rSquare := r * r
    let xr := r + x
    let b := xr * xr - xSquare - xr
    let h := w * w - (2 : Nat) * C.b
    ⟨h * s, w * (b - h) - (2 : Nat) * rSquare, sCube⟩

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
      | .affine X Y => .affine X (0 - Y)
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

#eval G + G + G
def mulBy2 := ProjectivePoint.scaleAux 2 G .infinity
#eval mulBy2

#eval 3 * G
#eval CurveGroup.double NewCurve G