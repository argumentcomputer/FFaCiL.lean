import FFaCiL.EllipticCurve
import FFaCiL.PrimeField

class Serialise (A : Type _) where
  serialise : A → ByteArray
  deserialise : ByteArray → Option A

instance : Serialise (Zmod n) where
  serialise := sorry
  deserialise := sorry

instance [PrimeField F] : Serialise F where
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