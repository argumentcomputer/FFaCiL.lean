import FFaCiL.EllipticCurve
import FFaCiL.GaloisField
import FFaCiL.PrimeField

class Serialise (A : Type _) where
  serialise : A → ByteArray
  deserialise : ByteArray → Option A

instance [PrimeField F] : Serialise F where
  serialise := sorry
  deserialise := sorry

instance [GaloisField F] : Serialise F where
  serialise := sorry
  deserialise := sorry

namespace CurveSerialise

variable {F : Type _} [PrimeField F] (C : Curve F)

instance : Serialise (AffinePoint C) where
  serialise := sorry
  deserialise := sorry

instance : Serialise (ProjectivePoint C) where
  serialise := sorry
  deserialise := sorry

end CurveSerialise