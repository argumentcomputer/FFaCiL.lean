import FFaCiL.EllipticCurve
import FFaCiL.PrimeField

import YatimaStdLib.ByteArray
import YatimaStdLib.Encodable

def coreLen (p : Nat) : Nat := Id.run do
  let mut param : Nat := 0
  while p >= 2^param do
    param := param + 1
  return (7 + param) / 8

variable {F : Type _} [PrimeField F] 

instance : Encodable F ByteArray where
  encode a := sorry 
  /-
    Id.run do
    let mut acc : ByteArray := ByteArray.empty
    for (b : UInt8) in [0:(coreLen (PrimeField.char F) - 1)] do
      acc := ByteArray.set! acc (b : Nat).size (UInt8.shiftRight (PrimeField.natRepr a) (8 * b))
    return acc
  -/
  decode bytes :=
    let integer := (bytes.foldl (fun a b => UInt8.shiftLeft a 8 ||| b) 0).val.val
    if bytes.size != coreLen (PrimeField.char F) || integer >= (PrimeField.char F)
    then .error "this bytestring is undecodable"
    else .ok (PrimeField.fromNat bytes.asBEtoNat)

namespace CurveSerialise

variable [Encodable F ByteArray] (C : Curve F)

instance proj : Encodable (ProjectivePoint C) ByteArray where
  encode p :=
    if ProjectivePoint.onCurve C p.X p.Y p.Z then _ 
    else panic "a given point is not serialisable"
  decode := sorry

instance : Encodable (AffinePoint C) ByteArray where
  encode a :=
    match a with
      | .infinity => sorry
      | .affine x y => proj.encode (ProjectivePoint.mkD x y 1)
  decode := sorry

end CurveSerialise