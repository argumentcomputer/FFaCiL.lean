import FF.BitVec

namespace FF

class Field (K : Type _) extends Neg K, Add K, Sub K, Mul K where
  /-- The zero element of the field, the additive identity. -/
  zero : K
  /-- The one element of the field, the multiplicative identity. -/
  one : K
  /-- Squares this element. -/
  square : K → K
  /-- Doubles this element. -/
  double : K → K
  /-- Computes the multiplicative inverse of this element.
    Following mathlib convention, we do not fail on 0.
    
    TODO: Maybe should be `K → Option K` -/
  inv : K → K
  sqrtRatio : K → K → Bool × K

namespace Field

variable [Field K]

/-- Returns true iff this element is zero.
  TODO: should it be `BEq` or `DecidableEq`?
  also should `Field` extend `BEq`? -/
def isZero [BEq K] (k : K) := k == zero

def cube (k : K) := square k * k

def sqrtAlt (k : K) : Bool × K :=
  sqrtRatio k one

/-- Returns the square root of the field element, if it is a quadratic residue.-/
def sqrt (k : K) :=
  let (isSquare, res) := sqrtRatio k one
  match isSquare with
  | false => none
  | true => some res


/-- I have no idea what I'm doing here lol -/
def npowRec : Nat → K → K
  | 0, _ => one
  | n + 1, a => a * npowRec n a

def pow (k : K) (n : Nat) : K :=
  npowRec n k

instance : Pow K Nat where
  pow := pow

end Field

class PrimeField (K : Type _) (Repr : outParam $ Type _) extends Field K where
  «from» : UInt64 → K
  asRef : Repr → ByteArray
  /-- TODO: This is not good Lean design, I think -/
  toRepr : K → Repr
  fromRepr : Repr → Option K
  isOdd : K → Bool
  /- Fields -/
  /-- Modulus of the field written as a string for debugging purposes.
    TODO: why is it `String`...? -/
  MODULUS : String
  /-- How many bits are needed to represent an element of this field. -/
  NUM_BITS : Nat
  /-- How many bits of information can be reliably stored in the field element.

    This is usually `NUM_BITS - 1`. -/
  CAPACITY : Nat
  /-- Inverse of 2 in the field. -/
  TWO_INV : K
  /-- A fixed multiplicative generator of `modulus - 1` order. 
    This element must also be a quadratic nonresidue. -/
  MULTIPLICATIVE_GENERATOR : K
  /-- An integer `s` satisfying the equation `2^s * t = modulus - 1` with `t` odd. 
  
    This is the number of leading zero bits in the little-endian bit representation of `modulus - 1`. -/
  S : Nat
  /-- The `2^s` root of unity. 
  
    It can be calculated by exponentiating `MULTIPLICATIVE_GENERATOR` by `t`, 
    where `t = (modulus - 1) >> S`. 
    
    TODO: Enforce with proof? -/
  ROOT_OF_UNITY : K
  /-- Inverse of `ROOT_OF_UNITY`. 
  
    TODO: Enforce with proof? -/
  ROOT_OF_UNITY_INV : K
  /-- Generator of the `t-order` multiplicative subgroup. -/
  DELTA : K

namespace PrimeField
open Field

variable (Repr : Type _) [PrimeField K Repr]


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

/-- TODO: impl `UInt128` -/
def fromNat (v : Nat) : K := Id.run do
  let u64s := v.toUInt64s
  let mut res : K := PrimeField.from u64s[u64s.size - 1]!
  let u64s := u64s.pop
  for u64 in u64s do
    for _ in [0:64] do
      res := double res
    res := res + PrimeField.from u64
  return res

def fromStr (s : String) : Option K :=
  s.toNat?.map $ fromNat Repr

def isEven (k : K) : Bool := !(isOdd k)

end PrimeField

/-- The subset of prime-order fields such that `(modulus - 1)` is divisible by `N`.
  If `N` is prime, there will be `N - 1` valid choices of `ZETA`.
  TODO: IDK what I'm doing here?? -/
class WithSmallOrderMulGroup (K : Type _) (Repr : outParam $ Type _) extends PrimeField K Repr where
  /-- A field element of small multiplicative order `N`. -/
  ZETA : K

/-- This represents the bits of an element of a prime field. -/
class PrimeFieldBits (K : Type _) (Repr : outParam $ Type _) extends PrimeField K Repr where
  /-- Converts an element of the prime field into a little-endian sequence of bits. -/
  toLEBits : K → BitArray
  /-- Returns the bits of the field characteristic (the modulus) in little-endian order. -/
  charLEBits : BitArray

end FF