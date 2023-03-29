import FFaCiL.EllipticCurve
import FFaCiL.PrimeField

import YatimaStdLib.ByteArray
import YatimaStdLib.Encodable

import LightData

variable {F : Type _} [PrimeField F] 

instance : Encodable F LightData where
  encode a := Encodable.encode (PrimeField.natRepr a)
  decode data := @Encodable.decode Nat LightData _ data

namespace CurveSerialise

variable [Encodable F ByteArray] (C : Curve F)

instance proj : Encodable (ProjectivePoint C) LightData where
  encode p :=
    if ProjectivePoint.onCurve C p.X p.Y p.Z then _ 
    else panic "a given point is not serialisable"
  decode := sorry

instance : Encodable (AffinePoint C) LightData where
  encode a := Encodable.encode $ AffinePoint.toProjective a
  decode a := Except.map ProjectivePoint.toAffine (Encodable.decode a)

end CurveSerialise