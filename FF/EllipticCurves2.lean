import FF.NewField

/-- Curves with Weierstrass form satisfying the equation `y² = x³ + a x + b` -/
class Curve (K : Type _) (F : outParam (Type _)) [PrimeField F] where
  /-- `a` coefficient -/
  a : F
  /-- `b` coefficient -/
  b : F
  /-- Curve order -/
  order : Nat
  /-- Curve cofactor -/
  cofactor : Nat
  /-- Curve characteristic -/
  characteristic : Nat
  /- More here -/

class EdwardsCurve (C : Type _) (F : Type _) [PrimeField F] extends Curve C F where
  edwardsForm : F × F × F

namespace Curve

/-- `y² = x³ + a x + b ↦ (a, b)`   -/
def weierstrassForm (C : Type _) [PrimeField F] [Curve C F] : F × F := 
  (Curve.a C, Curve.b C) 

def jacobianForm (C : Type _) [PrimeField F] [Curve C F] : F × F := sorry 

end Curve

/--
`CurvePoint` provides algebraic operations on elliptic curve points and related constants
-/
class CurvePoint {F : Type _} (C : Type _) (K : Type _) [PrimeField F] [Curve C F] where
  /-- The neutral element of the Abelian group of points. -/
  zero : K
  /-- The base point. -/
  base : K
  /-- `inv` inverses a given point. -/
  inv : K → K
  /-- Point addition. -/
  add : K → K → K
  /-- `double : p ↦ 2 ⬝ p` -/
  double : K → K := fun x => add x x 
  /-- Number-point multiplication. -/
  smul : Nat → K → K
  /-- `toPoint` form a point from prime field elements whenever it is possible -/
  toPoint : F → F → Option K
  /-- Frobenius endomorphism -/
  frobenius : F → F

structure AffinePoint (F : Type _) [PrimeField F] where
  x : F
  y : F
  isInfty : Bool

structure ProjectivePoint (F : Type _) [PrimeField F] where
  x : F
  y : F
  z : F

def infinity [PrimeField F] : ProjectivePoint F :=
  ProjectivePoint.mk 0 1 0

def ProjectivePoint.isInfinity {F : Type _} [PrimeField F] : ProjectivePoint F → Bool
  | c => c.z == 0

-- P₁ : AffinePoint, P₂ : ProjectivePoint ==> P₁ + P₂
-- (x, y) : AffinePoint => (x, y, 1) : ProjectivePoint
-- (x, y, z) : ProjectivePoint => (x/z, y/z) : AffinePoint
-- If z ≠ 0
-- If z = 0

/-
TODO: get rid of [OfNat F 2] [OfNat F 3] somehow
-/
instance {F} [PrimeField F] [OfNat F 2] [OfNat F 3] [Curve C F] : CurvePoint C (AffinePoint F) where
  base := sorry
  zero := sorry
  inv := sorry
  add := fun ⟨x, y, i⟩ ⟨u, v, j⟩ => 
    match i, j with
    | true, true => sorry
    | true, false => sorry
    | false, true => sorry
    | false, false => sorry
  double := fun ⟨x, y, i⟩ =>
    let lambda := (3 * x^2 + Curve.a C) / 2 * y
    let x' := lambda^2 - 2*x
    let y' := lambda * (x - x') - y
    ⟨x', y', i⟩
  smul := sorry
  toPoint := sorry
  frobenius := sorry

instance {F} [PrimeField F] [Curve C F] : CurvePoint C (ProjectivePoint F) where
  zero := sorry
  base := sorry
  inv := sorry
  add := sorry
  smul := sorry
  toPoint := sorry
  frobenius := sorry
  double := sorry


structure BLS12381 where

instance [PrimeField F] : Curve BLS12381 F where
  a := 0
  b := (4 : Nat)
  order := 0x923480928340981
