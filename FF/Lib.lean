import FF.BitVec
import YatimaStdLib.Ring

class PrimeField (K : Type _) extends Field K where
  «from» : UInt64 → K
  /- Fields -/
  /--
  Characteristic `p` of field and order of prime subfield.
  -/
  char : Nat
  
  /-- How many bits are needed to represent an element of this field. -/
  numBits : Nat

  /-- A fixed multiplicative generator of `modulus - 1` order. 
    This element must also be a quadratic nonresidue. -/
  multiplicativeGenerator : K
  
  /-- An integer `s` satisfying the equation `2^s * t = modulus - 1` with `t` odd. 
  
    This is the number of leading zero bits in the little-endian bit representation of `modulus - 1`. -/
  s : Nat

  /-- Generator of the `t-order` multiplicative subgroup. -/
  delta : K

/-- How many bits of information can be reliably stored in the field element.
  This is usually `numBits - 1`. -/
def capacity [PrimeField K] : Nat := PrimeField.numBits K - 1

def twoInv [PrimeField K] : K := Field.inv 2

/-- The `2^s` root of unity. 
It can be calculated by exponentiating `multiplicativeGenerator` by `t`, where `t = (char - 1) >> s`.
-/
def rootOfUnity [f : PrimeField K] : K :=
  let deg := (PrimeField.char K - 1) >>> PrimeField.s K
  @PrimeField.multiplicativeGenerator K f ^ deg

/-- Inverse of `rootOfUnity`. -/
def rootOfUnityInv [PrimeField K] : K := Field.inv rootOfUnity

/-- TODO: move these and make more efficient -/
partial def _root_.Nat.toUInt64sAux (n : Nat) : Array UInt64 :=
  if n = 0 then
    #[]
  else 
    (n / UInt64.size).toUInt64sAux.push n.toUInt64

partial def _root_.Nat.toUInt64s (n : Nat) : Array UInt64 :=
  if n = 0 then
    #[0]
  else 
    n.toUInt64sAux

class Representation (K : Type _) (Repr : outParam $ Type _) extends PrimeField K where
  asRef : Repr → ByteArray
  toRepr : K → Repr
  fromRepr : Repr → Option K

/-- The subset of prime-order fields such that `(modulus - 1)` is divisible by `N`.
  If `N` is prime, there will be `N - 1` valid choices of `ZETA`.
  TODO: IDK what I'm doing here?? -/
class WithSmallOrderMulGroup (K : Type _) extends PrimeField K where
  /-- A field element of small multiplicative order `N`. -/
  zeta : K

/-- This represents the bits of an element of a prime field. -/
class PrimeFieldBits (K : Type _) extends PrimeField K where
  /-- Converts an element of the prime field into a little-endian sequence of bits. -/
  toLEBits : K → BitArray
  /-- Returns the bits of the field characteristic (the modulus) in little-endian order. -/
  charLEBits : BitArray