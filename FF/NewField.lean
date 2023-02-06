import YatimaStdLib.AddChain
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
    let legNum := mkIdent `legNum
    let frobAC := mkIdent `frobAC
    let legAC := mkIdent `legAC

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
    let legendre := mkIdent `legendre
    let frob := mkIdent `frob

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

      def $legNum : Nat := $p >>> 1
      
      open AddChain in
      def $legAC : Array ChainStep := $(mkIdent `buildSteps) $ $legNum |>.$(mkIdent `minChain) 

      open AddChain in
      def $frobAC : Array ChainStep := $(mkIdent `buildSteps) $ $p |>.$(mkIdent `minChain)

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

      def $invAux (x : Nat) : Nat := Id.run do
        let mut (u, v, r, s, k) := ($p, x, 0, 1, 0)

        while v > 0 do
          if u % 2 == 0 then 
            u := u >>> 1
            s := s <<< 1
          else if v % 2 == 0 then
            v := v >>> 1
            r := r <<< 1
          else if v < u then
            u := (u - v) >>> 1
            r := r + s
            s := s <<< 1
          else if u ≤ v then
            v := (v - u) >>> 1
            s := s + r 
            r := r <<< 1
          k := k + 1
        
        if $p ≤ r then 
          r := 2 * $p - r
        else
          r := $p - r

        for _ in [1: k - 11 + 1] do
          if r % 2 == 0 then
            r := r >>> 1
          else
            r := (r + $p) >>> 1
        
        return r
      
      /-- 
      Calculates the inverse of an element. If the element is wrapped, applies Montgomery inversion:
      <https://ieeexplore.ieee.org/document/403725>
      Otherwise calculates the inverse using the extended Euclidean Algorithm
      -/
      def $inv (x : $name) : $name :=
        if x.wrapped then 
          ⟨$invAux <| $reduce x.data, true⟩
        else 
          let ans := Nat.gcdA x.data $p
          let ans := if ans < 0 then ans + $p |>.toNat else ans.toNat
          ⟨ans, false⟩

      instance : Square $name where
        mul := $mul
        square x := x * x

      open Square in
      def $legendre (x : $name) : Nat :=
        $(mkIdent `chainExp) $legAC x |> $unwrap |>.data
      
      open Square in
      def $frob (x : $name) : $name :=
        $(mkIdent `chainExp) $frobAC x
      
      def $sqrt? (x : $name) : Option $ $name × $name := sorry
        -- if $legendre x != 1 then none else Id.run do
        -- let mut q := $p - 1
        -- let mut s := 0
        -- while q % 2 == 0 do
        --   q := q / 2
        --   s := s + 1
        -- if s == 1 then
        --   let r := powMod p n ((p + 1) / 4)
        --   return some (r, p - r)
        -- let mut zMax := 2
        -- for z in [2 : p] do
        --   zMax := z
        --   if p - 1 == legendre z p then break
        -- let mut c := powMod p zMax q
        -- let mut r := powMod p n $ (q + 1) / 2  -- TODO : Group together these two exponetiations into a
        -- let mut t := powMod p n q              --        bached Exp to avoid re-calculating some powers
        -- let mut m := s
        -- while (t - 1) % p != 0 do
        --   let mut t2 := (t * t) % p
        --   let mut iMax := 1
        --   for i in [1:m] do
        --     iMax := i
        --     if (t2 - 1) % p == 0 then
        --       break
        --     t2 := (t2 * t2) % p
        --   let b := powMod p c (2^(m - iMax - 1))
        --   r := (r * b) % p
        --   c := (b * b) % p
        --   t := (t * c) % p
        --   m := iMax
        -- return some (r, p - r)

      -- Instances: 
      instance : ToString $name where
        toString x := if x.wrapped then s!"{x.data}ₘ" else s!"{x.data}"

      instance : BEq $name where
        beq x y := ($wrap x).data == ($wrap y).data
      
      instance : Ring $name where

      instance : Field $name where
        inv := $inv
        sqrt := fun x => Prod.fst <$> $sqrt? x

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
