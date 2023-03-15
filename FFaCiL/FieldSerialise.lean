import FFaCiL.PrimeField

class FieldSerialise (F : Type _) extends PrimeField F where
  serialise : K → ByteArray
  deserialise : ByteArray → Option K

-- TODO: instances 