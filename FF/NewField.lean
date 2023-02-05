import YatimaStdLib.Zmod

open Lean Syntax

macro (name := defineNewField)
doc?:optional(docComment) "new_field" name:ident "with" 
  "prime: " p:num
  "generator: " g:num
  : command => do
    -- Names here
    -- Pre-computed constants
    let prime := mkIdent `prime
    let content := mkIdent `content
    let r := mkIdent `r
    let rMask := mkIdent `rMask
    let pInv := mkIdent `pInv
    let zero := mkIdent `zero
    let one := mkIdent `one

    -- Montgomery functions
    let wrap := mkIdent `wrap
    let unwrap := mkIdent `unwrap
    let reduce := mkIdent `reduce
    
    -- Arithmetic operations
    let add := mkIdent `add
    let mul := mkIdent `mul
    let neg := mkIdent `neg
    let sub := mkIdent `sub
    let powAux := mkIdent `powAux
    let pow := mkIdent `pow
    let invAux := mkIdent `invAux
    let inv := mkIdent `inv
    let sqrt? := mkIdent `sqrt?

    -- Syntax creation here
    `(
      $[$doc?:docComment]? structure $name where
        data : Nat
        wrapped : Bool := Bool.false

      namespace $name

      /-- The number of bits encodable by elements of the field -/
      def $content : Nat := $p |>.log2 |> (· + 1)

      /-- The wrapping `R` used in Montgomery arithmetic -/
      def $r : Nat := 2 ^ $content

      private def $rMask : Nat := $r - 1

      /-- Characteristic <-> number of elements of the prime field -/
      def $prime : Nat := $p

      private def $pInv : Int := Nat.xgcd $p $r |>.fst

      def $zero : $name := ⟨0, false⟩

      instance : OfNat $name (nat_lit 0) where
        ofNat := $zero

      def $one : $name := ⟨1, false⟩

      instance : OfNat $name (nat_lit 1) where
        ofNat := $one

      /-- The Montgomery reduction algorithm -/
      def $reduce (x : Nat) : Nat :=
        let q := (x * $pInv) &&& $rMask
        match (x - q * $p) with
        | .ofNat n => n >>> $content
        | .negSucc n => $p - (n + 1) >>> $content

      /-- Bring a field element into Montgomery form -/
      def $wrap (x : $name) : $name := 
        if x.wrapped then x else ⟨x.data <<< $content |>.mod $p, true⟩

      /-- Bring a field element out of Montgomery form -/
      def $unwrap (x: $name) : $name := 
        if x.wrapped then ⟨$reduce x.data, false⟩ else x

      partial def $add (x y : $name) : $name := -- TODO: Eliminate partial
        match x.wrapped, y.wrapped with
        | true, true =>
          let answer := x.data + y.data
          if $p ≤ answer then ⟨answer - $p, true⟩ else ⟨answer, true⟩
        | false, true =>
          let x := $wrap x
          $add x y
        | true, false =>
          let y := $wrap y
          $add x y
        | false, false =>
          let answer := x.data +  y.data
          if $p ≤ answer then ⟨answer - $p, false⟩ else ⟨answer, false⟩

      instance : Add $name where
        add := $add

      partial def $mul (x y : $name) : $name := -- TODO: Eliminate partial
        match x.wrapped, y.wrapped with
        | true, true => ⟨$reduce <| x.data * y.data, true⟩
        | true, false => 
          let y := $wrap y
          $mul x y
        | false, true => 
          let x := $wrap x
          $mul x y
        | false, false => ⟨x.data * y.data % $p, false⟩

      instance : Mul $name where
        mul := $mul

      def $neg (x : $name) : $name :=
        ⟨$p - x.data, x.wrapped⟩

      instance : Neg $name where
        neg := $neg

      def $sub (x y : $name) : $name :=
        $add x ($neg y)

      instance : Sub $name where
        sub := $sub

      def $powAux (base : $name) (exp : Nat) : $name :=
        let rec go (base acc : $name) (exp : Nat) : $name :=
          if h : exp = 0 then acc
          else
            let exp' := exp / 2
            have : exp' < exp := Nat.div2_lt h
            if exp % 2 = 0
            then go (base * base) acc exp'   
            else go (base * base) (acc * base) exp'
        go base 1 exp

      def $pow (x : $name) (exp : Nat) : $name :=
        if 3 < exp then
          let x := $wrap x
          $powAux x exp |> ($unwrap ·) 
        else
          $powAux x exp

      instance : HPow $name Nat $name where
        hPow := $pow

      private def $invAux (x : Nat) : Nat := sorry

      /-- 
      Calculates the inverse of an element. If the element is wrapped, applies Montgomery inversion:
      <https://ieeexplore.ieee.org/document/403725>
      Otherwise calculates the inverse using the extended Euclidean Algorithm
      -/
      def $inv (x : $name) : $name :=
        if x.wrapped then 
          ⟨$invAux x.data, true⟩
        else 
          let ans := Nat.gcdA x.data $p
          let ans := if ans < 0 then ans + $p |>.toNat else ans.toNat
          ⟨ans, false⟩
      
      def $sqrt? (x : $name) : Option $name :=
        sorry

      -- Instances: 
      instance : ToString $name where
        toString x := if x.wrapped then s!"{x.data}ₘ" else s!"{x.data}"

      instance : BEq $name where
        beq x y := ($wrap x).data == ($wrap y).data
      
      instance : Ring $name where

      instance : Field $name where
        inv := $inv
        sqrt := $sqrt?

      end $name
    )

section big_field_tests

/-- A test implementation of the scalar field for BLS12_381 -/
new_field BLS12_381 with
  prime: 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
  generator: 83

end big_field_tests

section small_field_tests

new_field SmallTest with
  prime: 2011
  generator: 3

end small_field_tests

section implementation_tests

end implementation_tests

#eval Nat.gcdA 3 2011

#eval Int.toNat (2)