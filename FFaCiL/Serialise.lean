import FFaCiL.EllipticCurve
import FFaCiL.GaloisField
import FFaCiL.PrimeField

class Serialise (A : Type _) where
  serialise : A → ByteArray
  deserialise : ByteArray → Option A

/- TODO:
instance [PrimeField F] : Serialise F where
-/

namespace CurveSerialise

variable {F : Type _} [PrimeField F] (C : Curve F)

/- TODO:
instance [PrimeField F] : Serialise (AffinePoint C) where

instance [PrimeField F] : Serialise (ProjectivePoint C) where
-/

end CurveSerialise