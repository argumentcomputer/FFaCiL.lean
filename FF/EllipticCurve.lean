import FF.NewField

-- TODO: Add this notation to `Ring.lean` in YatimaStdLib

postfix:max "⁻¹" => Field.inv
/-!
TODO: Major items to consider before we can finally settle on this design:
* Does the design allow for specific optimizations for specific curves?
  (for example, GLV optimization for scalar mul?)
* 

-/

/--
Curves with Weierstrass form satisfying the equation `y² = x³ + a x + b`
for a prime field `F` such that `char K > 3`
-/
structure Curve (F : Type _) [Field F] where
  a : F
  b : F

/-
TODO: Add more methods relative to curves. This includes things like
* Order
* Cofactor
* different forms (Weierstrass, Jacobian)
* some repr for Curve
-/

/-
TODO: Add more curve point operations
* Hash to curve
* random curve point
* onCurve and projectiveOnCurve
* Frobenius? (Only makes sense if we define curves over `Galois Fields`)
-/

structure ProjectivePoint {F : Type _} [Field F] (C : Curve F) where
  X : F
  Y : F
  Z : F

namespace ProjectivePoint 

variable {F : Type _} [Field F] {C : Curve F}

def scale (f : F) : ProjectivePoint C → ProjectivePoint C
  | ⟨x, y, z⟩ => ⟨f * x, f * y, f * z⟩

def norm : ProjectivePoint C → ProjectivePoint C
  | P@⟨_, y, z⟩ =>
    if z != 0 then P.scale z⁻¹ else
    if y != 0 then P.scale y⁻¹ else
    ⟨1, 0, 0⟩

instance  : BEq $ ProjectivePoint C where
  beq P Q :=
    let ⟨x₁, y₁, z₁⟩ := P.norm
    let ⟨x₂, y₂, z₂⟩ := Q.norm
    x₁ == x₂ && y₁ == y₂ && z₁ == z₂

instance [ToString F] : ToString $ ProjectivePoint C where
  toString := fun ⟨x, y, z⟩ => s!"({x} : {y} : {z})"

def isInfinity (P : ProjectivePoint C) := P.X == 0 && P.Y == 1 && P.Z == 0

def infinity : ProjectivePoint C := ⟨0, 1, 0⟩

def double : ProjectivePoint C → ProjectivePoint C
  | ⟨x, y, z⟩ =>
    let a := C.a * z^2 + (3 : Nat) * x^2
    let b := y * z
    let c := x * y * b
    let d := a^2 - (8 : Nat) * c
    let x₁ := (2 : Nat) * b * d
    let y₁ := a * ((4 : Nat) * c - d) - b^3 * y * z
    let z₁ := (8 : Nat) * b^3
    ⟨x₁, y₁, z₁⟩

def add (p₁ p₂ : ProjectivePoint C) 
  : ProjectivePoint C :=
    if p₁ == p₂ then ProjectivePoint.double p₁ else
    match p₁, p₂ with
    | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => 
      let a := y₂ * z₁ - y₁ * z₂
      let b := x₂ * z₁ - x₁ * z₂
      let c := a^2 * z₁ * z₂ - b^3 - (2 : Nat) * b^2 * x₁ * z₂
      let x₃ := b * c
      let y₃ := a * (b^2 * x₁ * z₂ - c) - b^3 * y₁ * z₂
      let z₃ := b^3 * z₁ * z₂
      ⟨x₃, y₃, z₃⟩

end ProjectivePoint

inductive AffinePoint {F : Type _} [Field F] (C : Curve F) where
  | affine (X : F) (Y : F) : AffinePoint C
  | infinity : AffinePoint C

def AffinePoint.add {F : Type _} [Field F] {C : Curve F} 
  : AffinePoint C → AffinePoint C → AffinePoint C
    | .infinity, _ => .infinity
    | _, .infinity => .infinity
    | .affine x₁ y₁, .affine x₂ y₂ =>
        let lambda := (y₁ + y₂) / (x₁ + y₂)
        let x₃ := lambda^2 + lambda + x₁ + x₂ + Curve.a C
        let y₃ := lambda * (x₁ + x₃) + x₃ + x₁
        .affine x₃ y₃

class CurveGroup {F : Type _} [Field F] (C : Curve F) (K : outParam $ Type _) where 
  zero : K
  inv : K → K
  add : K → K → K
  double : K → K
  -- toPoint : F → F → Option K -- TODO: I think we should add this to `ProjectivePoint` and
                                -- `AffinePoint` separately
  -- frobenius : K → K -- TODO: I'm not sure we need/want Frobenius for `CurveGroup`

instance {F K : Type _} [Field F] (C : Curve F) [CurveGroup C K] : Add K where
  add := CurveGroup.add C

instance {F K : Type _} [Field F] (C : Curve F) [CurveGroup C K] : Neg K where
  neg := CurveGroup.inv C

open CurveGroup in
partial def smulAux [Field F] (C : Curve F)
  [CurveGroup C K] (n : Nat) (p : K) (acc : K) : K :=
  if n == 0 then acc
  else match n % 2 == 0 with
    | true => smulAux C (n >>> 1) (double C p) (add C p acc)
    | false => smulAux C (n >>> 1) (double C p) acc

open CurveGroup in
/--
Montgomery's ladder for fast scalar-point multiplication
-/
def smul [Field F] {C : Curve F}
  [CurveGroup C K] (n : Nat) (p : K) : K := smulAux C n p (zero C)

instance {F K : Type _} [f : Field F] (C : Curve F) [gr : CurveGroup C K] : HMul Nat K K where
  hMul := @smul F K f C gr
  
open ProjectivePoint in
instance {F : Type _} [Field F] {C : Curve F} : CurveGroup C (ProjectivePoint C) where 
  zero := infinity
  inv := fun ⟨x, y, z⟩ => ⟨x, 0 - y, z⟩ 
  add := ProjectivePoint.add
  double := ProjectivePoint.double
  -- toPoint x y :=
  --   let p := ⟨x, y, 1⟩
  --   let isDef := fun (⟨x, y, z⟩ : ProjectivePoint C) =>
  --     (x * x + C.a * z * z) * x == (y * y - C.b * z * z) * z
  --   if isDef p then some p else none
  -- frobenius :=
  --   fun ⟨x, y, z⟩ =>
  --   let frob := fun (x : F) => x^(Field.char F)
  --   ⟨ frob x, frob y, frob z⟩

def affineDouble [Field F] {C : Curve F} :
  AffinePoint C → AffinePoint C
  | .affine x y =>
    let lambda := ((3 : Nat) * x^2 + Curve.a C) / (2 : Nat) * y
    let x' := lambda^2 - (2 : Nat) * x
    let y' := lambda * (x - x') - y
    .affine x' y'
  | .infinity => .infinity

instance {F : Type _} [Field F] {C : Curve F} : CurveGroup C (AffinePoint C) where 
  zero := .infinity
  inv p :=
    match p with
      | .affine X Y => .affine X (- Y)
      | x           => x
  add := AffinePoint.add
  double := affineDouble
  -- toPoint x y :=
  --   let p := .affine x y
  --   if (x * x + C.a * x) * x + C.b == y * y then some p else none
  -- frobenius p :=
  --   match p with
  --     | .infinity => .infinity
  --     | .affine x y => .affine (x^(Field.char F)) (y^(Field.char F))

