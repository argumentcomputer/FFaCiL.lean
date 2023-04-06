import FFaCiL.PrimeField

/-!
# Elliptic Curves and EC arithmetic

This module defines elliptic curves, and the arithmetic on their points.

## TODOs:
* Add different curve forms (Jacobian, Edwards, etc...)
-/

/--
Curves with Weierstrass form satisfying the equation `y² = x³ + a x + b`
for a prime field `F` such that `char F > 3`.
-/
structure Curve (F : Type _) [Field F] where
  a : F
  b : F

namespace Curve

variable {F : Type _} [Field F] (C : Curve F)

instance [ToString F] : ToString $ Curve F where
  toString C :=
    match C.a == 0, C.b == 0 with 
      | true, true => "y² = x³"
      | true, false => s!"y² = x³ + {C.b}"
      | false, true => s!"y² = x³ + {C.a} x"
      | false, false =>
        match C.a == 1 with 
          | true => s!"y² = x³ + x + {C.b}"
          | false => s!"y² = x³ + {C.a} x + {C.b}"

/--
The discriminant of an elliptic curve.
-/
def discriminant : F := (- (16 : Nat)) * ((4 : Nat) * C.a^3 + (27 : Nat) * C.b^2)

/--
The `j`-invariant of an elliptic curve.
-/
def j : F := (1728 : Nat) * C.a^3 / ((4 : Nat) * C.discriminant)

end Curve

/--
The type of points on the projective plane.
-/
structure ProjectivePoint {F : Type _} [Field F] (C : Curve F) where
  X : F
  Y : F
  Z : F

namespace ProjectivePoint

variable {F : Type _} [Field F] {C : Curve F}

/--
Checks if a given point is at infinity for a curved in Weierstrass form.
-/
def isInfinity (P : ProjectivePoint C) := P.X == 0 && P.Y == 1 && P.Z == 0

/--
The point at infinity of a projective curve.
-/
def infinity : ProjectivePoint C := ⟨0, 1, 0⟩

/--
The zero element of the Abelian group of projective points is the point at infinity.
-/
abbrev zero : ProjectivePoint C := infinity

instance : Inhabited $ ProjectivePoint C where
  default := infinity  

open Random in
/--
Generates a random point of a projective curve.
-/
partial def randomAux [PrimeField F] {gen : Type _} [Inhabited gen] [RandomGen gen] (g : gen) 
    : (ProjectivePoint C) × gen :=
  let (X, g) := random g
  let (pos, g) := randBool g
  match PrimeField.sqrt (X^3 + C.a * X + C.b) with
  | some Y => if pos then (⟨X, Y, 1⟩, g) else (⟨X, -Y, 1⟩, g)
  | none => randomAux g

instance [PrimeField F] : Random $ ProjectivePoint C where
  random g := randomAux g

/--
Checks if a given triple of field elements is a well-formed point.
-/
def onCurve (C : Curve F) (x y z : F) : Bool := z * y^2 == x^3 + C.a * x * z^2 + C.b * z^3

/--
Constructs a point whenever a given triple is well-formed.
-/
def mk? (x y z : F) : Option $ ProjectivePoint C :=
  if onCurve C x y z then some ⟨x, y, z⟩ else none

/--
Similar to `mk?` but returns the default `infinity` if a triple is not well-formed.
-/
def mkD (x y z : F) : ProjectivePoint C :=
  if onCurve C x y z then ⟨x, y, z⟩ else default

/--
Scales a point, given `f : F`, `scale : ⟨x, y, z⟩ ↦ ⟨f * x, f * y, f * z⟩`.
-/
def scale (f : F) : ProjectivePoint C → ProjectivePoint C
  | ⟨x, y, z⟩ => ⟨f * x, f * y, f * z⟩

instance : HMul F (ProjectivePoint C) (ProjectivePoint C) where
  hMul := scale

/--
Point normalisation: if `z ≠ 0`, then `norm : ⟨x, y, z⟩ ↦ ⟨ z⁻¹ * x, z⁻¹ * y, 1⟩`,
and `infinity` otherwise
-/
def norm : ProjectivePoint C → ProjectivePoint C
  | P@⟨_, _, z⟩ =>
    if z != 0 then z⁻¹ * P else
    infinity

/--
Projective point equality
-/
instance  : BEq $ ProjectivePoint C where
  beq P Q :=
    match P, Q with
    | ⟨x₁, _, z₁⟩, ⟨x₂, _, z₂⟩ =>
      if z₁ == 0 || z₂ == 0 then
        x₁ == 0 && x₂ == 0
      else
        let ⟨X, Y, _⟩ := z₂ * P
        let ⟨U, W, _⟩ := z₁ * Q
        X == U && Y == W

instance [ToString F] : ToString $ ProjectivePoint C where
  toString := fun ⟨x, y, z⟩ => s!"({x} : {y} : {z})"

/--
`double : p ↦ 2 * p`

Point doubling algorithm based on https://eprint.iacr.org/2015/1060.pdf
-/
def double (p : ProjectivePoint C) : ProjectivePoint C := 
  Id.run do
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

instance : Neg $ ProjectivePoint C where
  neg := fun ⟨x, y, z⟩ => ⟨x, -y, z⟩

/--
Addition in the Abelian group of projective points.
The implementation is based on 
Handbook of elliptic and hyperelliptic curve cryptography by Henri Cohen, et al., 13.2.1.b.
-/
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

/--
The algebraic data type of affine points.
-/
inductive AffinePoint {F : Type _} [Field F] (C : Curve F) where
  /--
  An affine point that stores a pair of coefficients for finite points.
  -/
  | affine (X : F) (Y : F) : AffinePoint C
  /--
  The point at infinity.
  -/
  | infinity : AffinePoint C
  deriving BEq

variable {F : Type _} [Field F] {C : Curve F}

instance [ToString F] : ToString (AffinePoint C) where
  toString p :=
    match p with
      | .infinity => "O"
      | .affine x y => s!"({x} : {y})"

namespace AffinePoint

instance : Inhabited $ AffinePoint C where
  default := infinity
/-
Checks whether an affine point is on the curve `C`.
-/
def onCurve : AffinePoint C → Bool
  | infinity => true
  | affine x y => y^2 == x^3 + C.a * x + C.b

/--
The zero element is the point at infinity.
-/
def zero : AffinePoint C := infinity


/--
Affine point negation
-/
def neg : AffinePoint C → AffinePoint C 
  | infinity => infinity
  | affine x y => affine x (-y)

/--
Affine point doubling algorithm based on
Handbook of elliptic and hyperelliptic curve cryptography by Henri Cohen, et al., 13.2.1.a.
-/
def double [Field F] {C : Curve F} :
  AffinePoint C → AffinePoint C
  | affine x y =>
    let xx := x^2
    let lambda := (xx + xx + xx + Curve.a C) / (y + y)
    let x' := lambda^2 - (2 : Nat) * x
    let y' := lambda * (x - x') - y
    affine x' y'
  | infinity => infinity

/--
Affine point addition, based on https://eprint.iacr.org/2015/1060.pdf.
-/
def add {F : Type _} [Field F] {C : Curve F} 
  : AffinePoint C → AffinePoint C → AffinePoint C
    | .infinity, p => p
    | p, .infinity => p
    | P@(.affine x₁ y₁), Q@(.affine x₂ y₂) =>
      if P == Q then double P else
      if P == neg Q then .infinity else
      let lambda := (y₁ - y₂)/(x₁ - x₂)
      let x₃ := (lambda^2 - x₁ - x₂)
      .affine x₃ (lambda*(x₁ - x₃) - y₁)

/--
Checks if a give tuple of field elements forms an affine point for the curve `C`.
-/
def fieldEltsOnCurve (C : Curve F) (x y : F) : Bool := y * y == (x * x + C.a) * x + C.b

open Random in
/--
Generated a random affine point.
-/
partial def randomAux [PrimeField F] {gen : Type _} [Inhabited gen] [RandomGen gen] (g : gen) 
    : (AffinePoint C) × gen :=
  let (X, g) := random g
  let (pos, g) := randBool g
  match PrimeField.sqrt (X^3 + C.a * X + C.b) with
  | some Y => if pos then (affine X Y, g) else (affine X (-Y), g)
  | none => randomAux g

instance [PrimeField F] : Random $ AffinePoint C where
  random g := randomAux g

end AffinePoint

/--
Normalizes a projective point to the standard affine chart.
-/
def ProjectivePoint.toAffine (P : ProjectivePoint C) : AffinePoint C :=
  let P' := P.norm
  if P.Z == 0 then .infinity else .affine P'.X P'.Y

/--
Converts an affine point to a projective one.
-/
def AffinePoint.toProjective : AffinePoint C → ProjectivePoint C
  | infinity => .infinity
  | affine x y => ⟨x, y, 1⟩

/--
`CurveGroup` is a type class that defines basic algebraic operations.
-/
class CurveGroup {F : outParam $ Type _} [Field F] (K : Type _) (C : outParam $ Curve F)  where 
  /--
  The identity element
  -/
  zero : K

  /--
  The Abelian group inversion
  -/
  inv : K → K

  /--
  The Abelian group addition operation
  -/
  add : K → K → K

  /--
  Doubling
  -/
  double : K → K

/-
TODO: Add more methods to `CurveGroup`. This includes things like
* Order
* Cofactor
-/

namespace CurveGroup

instance [CurveGroup K C] : Add K where
  add := CurveGroup.add 

instance [CurveGroup K C] : Neg K where
  neg := CurveGroup.inv 

open CurveGroup in
partial def smulAux [CurveGroup K C] (n : Nat) (p : K) (acc : K) : K :=
  if n == 0 then acc
  else match n % 2 == 1 with
    | true => smulAux (n >>> 1) (double p) (add p acc)
    | false => smulAux (n >>> 1) (double p) acc

open CurveGroup in
/--
Double and add algorithm for the fast scalar-point multiplication algorithm.
-/
def smul [CurveGroup K C] (n : Nat) (p : K) : K := smulAux n p (zero)

instance [CurveGroup K C] : HMul Nat K K where
  hMul := smul  
  
instance [CurveGroup K C] : HMul Int K K where
  hMul n p := match n with
    | .ofNat n => n * p
    | .negSucc n => (n + 1) * (- p)

instance : CurveGroup (ProjectivePoint C) C where 
  zero := ProjectivePoint.infinity
  inv := fun ⟨x, y, z⟩ => ⟨x, -y, z⟩ 
  add := ProjectivePoint.add
  double := ProjectivePoint.double

instance : CurveGroup (AffinePoint C) C where 
  zero := AffinePoint.infinity
  inv := AffinePoint.neg
  add := AffinePoint.add
  double := AffinePoint.double

end CurveGroup

/--
Given a curve `C`, `Curve.points` generates the array of all projective points of `C`.
-/
def Curve.points {F} [PrimeField F] (C : Curve F) : Array (ProjectivePoint C) := Id.run do
  let mut answer := #[.zero]
  for x in [:PrimeField.char F] do
    match PrimeField.sqrt ((x : F)^3 + C.a * x + C.b) with
    | none => continue
    | some s => 
      answer := answer.push ⟨x, s, 1⟩
      answer := answer.push ⟨x, -s, 1⟩
  return answer