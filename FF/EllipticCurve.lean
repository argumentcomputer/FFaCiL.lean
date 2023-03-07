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

def isInfinity (P : ProjectivePoint C) := P.X == 0 && P.Y == 1 && P.Z == 0

def infinity : ProjectivePoint C := ⟨0, 1, 0⟩

abbrev zero : ProjectivePoint C := infinity

instance : Inhabited $ ProjectivePoint C where
  default := infinity  

def onCurve (C : Curve F) (x y z : F) : Bool := z * y^2 == x^3 + C.a * x * z^2 + C.b * z^3

def mk? (x y z : F) : Option $ ProjectivePoint C :=
  if onCurve C x y z then some ⟨x, y, z⟩ else none

def mkD (x y z : F) : ProjectivePoint C :=
  if onCurve C x y z then ⟨x, y, z⟩ else default

def scale (f : F) : ProjectivePoint C → ProjectivePoint C
  | ⟨x, y, z⟩ => ⟨f * x, f * y, f * z⟩

instance : HMul F (ProjectivePoint C) (ProjectivePoint C) where
  hMul := scale

def norm : ProjectivePoint C → ProjectivePoint C
  | P@⟨_, y, z⟩ =>
    if z != 0 then z⁻¹ * P else
    if y != 0 then y⁻¹ * P else
    ⟨1, 0, 0⟩

instance  : BEq $ ProjectivePoint C where
  beq P Q :=
    let ⟨x₁, y₁, z₁⟩ := P.norm
    let ⟨x₂, y₂, z₂⟩ := Q.norm
    x₁ == x₂ && y₁ == y₂ && z₁ == z₂

instance [ToString F] : ToString $ ProjectivePoint C where
  toString := fun ⟨x, y, z⟩ => s!"({x} : {y} : {z})"

def double (p : ProjectivePoint C) : ProjectivePoint C := Id.run do
  let a := C.a
  let b := C.b
  let b₃ := (3 : Nat) * b
  let ⟨X, Y, Z⟩ := p
  let mut (t₀, t₁, t₂, t₃) := (X * X, Y * Y, Z * Z, X * Y)
  t₃ := t₃ + t₃
  let mut Z₃ := X * Z
  Z₃ := Z₃ + Z₃
  let mut X₃ := a * Z₃
  let mut Y₃ := b₃ * t₂
  Y₃ := X₃ + Y₃
  X₃ := t₁ - Y₃
  Y₃ := t₁ + Y₃
  Y₃ := X₃ * Y₃
  X₃ := t₃ * X₃
  Z₃ := b₃ * Z₃
  t₂ := a * t₂
  t₃ := t₀ - t₂
  t₃ := a * t₃
  t₃ := t₃ + Z₃
  Z₃ := t₀ + t₀
  t₀ := Z₃ + t₀
  t₀ := t₀ + t₂
  t₀ := t₀ * t₃
  Y₃ := Y₃ + t₀
  t₂ := Y * Z
  t₂ := t₂ + t₂
  t₀ := t₂ * t₃
  X₃ := X₃ - t₀
  Z₃ := t₂ * t₁
  Z₃ := Z₃ + Z₃
  Z₃ := Z₃ + Z₃
  return ⟨X₃, Y₃, Z₃⟩

def add (p₁ p₂ : ProjectivePoint C) : ProjectivePoint C :=
  let a := C.a
  let b := C.b
  match p₁, p₂ with
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ =>
    let z₁z₂ := z₁ * z₂
    let x₁z₂x₂z₁ := x₁ * z₂ + x₂ * z₁
    let ax₁z₂x₂z₁ := a * x₁z₂x₂z₁
    let b3 := (3 : Nat) * b
    let t₁ := b3 * x₁z₂x₂z₁ - a^2 * z₁z₂
    let x₃ :=
      (x₁ * y₂ + x₂ * y₁) * 
      (y₂ * y₁ - ax₁z₂x₂z₁ - b3 * z₁z₂) -
      (y₁ * z₂ + y₂ * z₁) *
      (a * x₁ * x₂ + t₁)
    let y₃ := ((3 : Nat) * x₁ * x₂ + a * z₁ * z₂) *
      (a * x₁ * x₂ + t₁) +
      (y₁ * y₂ + ax₁z₂x₂z₁ + b3 * z₁z₂) * (y₁ * y₂ - ax₁z₂x₂z₁ - b3 * z₁z₂)
    let z₃ := (y₁ * z₂ + y₂ * z₁) * (y₁ * y₂ + ax₁z₂x₂z₁ + b3 * z₁z₂) +
      (x₁ * y₂ + x₂ * y₁) * ((3 : Nat) * x₁ * x₂ + a * z₁ * z₂)
    ⟨x₃, y₃, z₃⟩

end ProjectivePoint

inductive AffinePoint {F : Type _} [Field F] (C : Curve F) where
  | affine (X : F) (Y : F) : AffinePoint C
  | infinity : AffinePoint C
  deriving BEq

variable {F : Type _} [Field F] {C : Curve F}

instance [ToString F] : ToString (AffinePoint C) where
  toString p :=
    match p with
      | .infinity => "O"
      | .affine x y => s!"({x} : {y})"

namespace AffinePoint

def zero : AffinePoint C := .infinity

open ProjectivePoint in
def add {F : Type _} [Field F] {C : Curve F} 
  : AffinePoint C → AffinePoint C → AffinePoint C
    | .infinity, p => p
    | p, .infinity => p
    | .affine x₁ y₁, .affine x₂ y₂ =>
      let p₁ : ProjectivePoint C := mkD x₁ y₁ 1 
      let p₂ : ProjectivePoint C := mkD x₂ y₂ 1 
      let p₁p₂ : ProjectivePoint C :=
        norm $ @ProjectivePoint.add F _ C p₁ p₂
      if p₁p₂.isInfinity then infinity else
      .affine p₁p₂.X p₁p₂.Y

def double [Field F] {C : Curve F} :
  AffinePoint C → AffinePoint C
  | .affine x y =>
    let xx := x^2
    let lambda := (xx + xx + xx + Curve.a C) / (y + y)
    let x' := lambda^2 - (2 : Nat) * x
    let y' := lambda * (x - x') - y
    .affine x' y'
  | .infinity => .infinity

def scale (a : F) : AffinePoint C → AffinePoint C
  | .infinity => .infinity
  | .affine x y => .affine (a * x) (a * y)

instance : HMul F (AffinePoint C) (AffinePoint C) where
  hMul := scale

def onCurve (C : Curve F) (x y : F) : Bool := y * y == (x * x + C.a) * x + C.b

end AffinePoint

variable {F K : Type _} [Field F] (C : Curve F) 

def ProjectivePoint.toAffine (P : ProjectivePoint C) : AffinePoint C :=
  let P' := P.norm
  if P.Z == 0 then .infinity else .affine P'.X P'.Y

def AffinePoint.toProjective : AffinePoint C → ProjectivePoint C
  | .infinity => .infinity
  | .affine x y => ⟨x, y, 1⟩

class CurveGroup {F : Type _} [Field F] (C : Curve F) (K : outParam $ Type _) where 
  zero : K
  inv : K → K
  add : K → K → K
  double : K → K
  -- frobenius : K → K -- TODO: I'm not sure we need/want Frobenius for `CurveGroup`

instance [CurveGroup C K] : Add K where
  add := CurveGroup.add C

instance [CurveGroup C K] : Neg K where
  neg := CurveGroup.inv C

open CurveGroup in
partial def smulAux [CurveGroup C K] (n : Nat) (p : K) (acc : K) : K :=
  if n == 0 then acc
  else match n % 2 == 1 with
    | true => smulAux (n >>> 1) (double C p) (add C p acc)
    | false => smulAux (n >>> 1) (double C p) acc

open CurveGroup in
/--
Montgomery's ladder for fast scalar-point multiplication
-/
def smul [CurveGroup C K] (n : Nat) (p : K) : K := smulAux C n p (zero C)

instance [CurveGroup C K] : HMul Nat K K where
  hMul := smul C 
  
open ProjectivePoint in
instance : CurveGroup C (ProjectivePoint C) where 
  zero := infinity
  inv := fun ⟨x, y, z⟩ => ⟨x, 0 - y, z⟩ 
  add := ProjectivePoint.add
  double := ProjectivePoint.double

open AffinePoint in
instance : CurveGroup C (AffinePoint C) where 
  zero := infinity
  inv p := match p with
    | affine X Y => affine X (- Y)
    | x           => x
  add := add
  double := double

