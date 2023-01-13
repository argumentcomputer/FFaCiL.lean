
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
    Following mathlib convention, we do not fail on 0 -/
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
variable (Repr : Type _) [PrimeField K Repr]

def fromStr (s : String) : Option K :=
  sorry

/-- TODO: impl `UInt128` -/
def fromNat (v : Nat): K := 

  sorry

def isEven (k : K) : Bool := !(isOdd k)

end PrimeField
end FF