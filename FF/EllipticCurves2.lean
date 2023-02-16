import FF.NewField

variable (F : Type _) [PrimeField F]

class Curve (_ : Type _) (F : Type _) [PrimeField F] where
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

class CurvePoint (C : Type _) (K : Type _) [PrimeField F] [Curve C F] where


structure AffinePoint (F) where
  x : F
  y : F

structure ProjectivePoint (F) where
  x : F
  y : F
  z : F

def ProjectivePoint.isInfinity : ProjectivePoint F → Bool
  | c => c.z == 0

-- P₁ : AffinePoint, P₂ : ProjectivePoint ==> P₁ + P₂
-- (x, y) : AffinePoint => (x, y, 1) : ProjectivePoint
-- (x, y, z) : ProjectivePoint => (x/z, y/z) : AffinePoint
-- If z ≠ 0
-- If z = 0
--  

-- instance : CurvePoint C (AffinePoint F) where
--   sorry

structure BLS12381 where

instance [NewField F] [OfNat F 4] : Curve BLS12381 F where
  a := 0
  b := 4
  order := 0x923480928340981
