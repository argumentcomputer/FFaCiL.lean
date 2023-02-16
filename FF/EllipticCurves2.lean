import FF.NewField

/-- Curves with Weierstrass form-/
class Curve (K : Type _) (F : outParam (Type _)) [PrimeField F] where
  a : F
  b : F
  order : Nat
  /- More here -/

class EdwardsCurve (C : Type _) (F : Type _) [PrimeField F] extends Curve C F where
  edwardsForm : F × F × F

namespace Curve

/-- `y^2 = x^3 + a x + b ↦ (a, b)`   -/
def weierstrassForm (C : Type _) [PrimeField F] [Curve C F] : F × F := sorry 

def jacobianForm (C : Type _) [PrimeField F] [Curve C F] : F × F := sorry 

end Curve

class CurvePoint {F : Type _} (C : Type _) (K : Type _) [PrimeField F] [Curve C F] where
  zero : K
  inv : K → K 
  add : K → K → K
  double : K → K := fun x => add x x
  smul : Nat → K → K  

structure AffinePoint (F : Type _) [PrimeField F] where
  x : F
  y : F
  isInfty : Bool

structure ProjectivePoint (F : Type _) [PrimeField F] where
  x : F
  y : F
  z : F

def ProjectivePoint.isInfinity {F : Type _} [PrimeField F] : ProjectivePoint F → Bool
  | c => c.z == 0

-- P₁ : AffinePoint, P₂ : ProjectivePoint ==> P₁ + P₂
-- (x, y) : AffinePoint => (x, y, 1) : ProjectivePoint
-- (x, y, z) : ProjectivePoint => (x/z, y/z) : AffinePoint
-- If z ≠ 0
-- If z = 0

instance {F} [PrimeField F] [Curve C F] : CurvePoint C (AffinePoint F) where
  zero := sorry
  inv := sorry
  add := fun ⟨x, y, i⟩ ⟨u, v, j⟩ => 
    match i, j with
    | true, true => sorry
    | true, false => sorry
    | false, true => sorry
    | false, false => sorry
  smul := sorry

instance {F} [PrimeField F] [Curve C F] : CurvePoint C (ProjectivePoint F) where
  zero := sorry
  inv := sorry
  add := sorry
  smul := sorry

structure BLS12381 where

instance [PrimeField F] [OfNat F 4] : Curve BLS12381 F where
  a := 0
  b := 4
  order := 0x923480928340981
