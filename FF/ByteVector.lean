import YatimaStdLib.ByteVector

def byteVecAdd (x : ByteVector n) (y : ByteVector n) : ByteVector n := sorry

instance : Add (ByteVector n) where
  add := sorry

def byteVecSub (x : ByteVector n) (y : ByteVector n) : ByteVector n := sorry

instance : Sub (ByteVector n) where
  sub := sorry

def byteVecMul (x : ByteVector n) (y : ByteVector n) : ByteVector n := sorry

instance : Mul (ByteVector n) where
  mul := sorry

def byteVecInv (x : ByteVector n) : ByteVector n := sorry

instance : Inv (ByteVector n) where
  inv := sorry

def byteVecDiv (x : ByteVector n) (y : ByteVector n) : ByteVector n := sorry

instance : Div (ByteVector n) where
  div := sorry