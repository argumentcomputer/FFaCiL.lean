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

  /-- The `2^s` root of unity. 
  It can be calculated by exponentiating `multiplicativeGenerator` by `t`, where `t = (char - 1) >> s`.
  -/
  rootOfUnity : K

variable {K : Type _} [f : PrimeField K]

/-- How many bits of information can be reliably stored in the field element.
  This is usually `numBits - 1`. -/
def capacity : Nat := PrimeField.numBits K - 1

/--
Inverse of `2` in the field
-/
def twoInv : K := Field.inv 2

/--
Returns true iff this element is even.
-/
def isEven (x : K) : Bool := x / 2 == 0

/--
Returns true iff this element is odd.
-/
def isOdd : K → Bool := not ∘ isEven

/-- Inverse of `rootOfUnity`. -/
def rootOfUnityInv : K := Field.inv PrimeField.rootOfUnity

class Representation (K : Type _) (Repr : outParam $ Type _) extends PrimeField K where
  asRef : Repr → ByteArray
  toRepr : K → Repr
  fromRepr : Repr → Option K

/-- The subset of prime-order fields such that `(modulus - 1)` is divisible by `N`.
  If `N` is prime, there will be `N - 1` valid choices of `ZETA`.
-/
class WithSmallOrderMulGroup (K : Type _) extends PrimeField K where
  /-- A field element of small multiplicative order `N`. -/
  zeta : K