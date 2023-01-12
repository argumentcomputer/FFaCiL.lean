
namespace FF

class Field (K : Type _) extends Neg K, Add K, Sub K, Mul K where
  zero : K
  one : K
  square : K → K
  double : K → K
  /-- Following mathlib convention, we do not fail on 0 -/
  inv : K → K
  sqrtRatio : K → K → Bool × K



namespace Field

variable [Field K]

-- TODO: should it be `BEq` or `DecidableEq`?
-- also should `BEq` be part of the class?
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
  MODULUS : String
  NUM_BITS : Nat
  CAPACITY : Nat
  TWO_INV : K
  MULTIPLICATIVE_GENERATOR : K
  S : Nat
  ROOT_OF_UNITY : K
  ROOT_OF_UNITY_INV : K
  DELTA : K

namespace PrimeField
variable (Repr : Type _) [PrimeField K Repr]

def fromStr (s : String) : Option K :=
  sorry

/-- TODO: impl `UInt128` -/
def fromUInt128 : K := sorry

def isEven (k : K) : Bool := !(isOdd k)

end PrimeField
end FF