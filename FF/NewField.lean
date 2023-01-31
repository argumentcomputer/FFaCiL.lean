open Lean Syntax

inductive Bit | zero | one

instance : ToString Bit where
  toString
    | .zero => "0"
    | .one => "1"

def getBit (a : Nat) : Bit :=
  if a % 2 == 0 then .zero else .one

open Nat in
def getBits (a : Nat) : Array Bit :=
  let rec loop (m : Nat) (acc : Array Bit) : Array Bit :=
    match h : m with
    | 0 => acc.push .zero
    | 1 => acc.push .one
    | n + 1 => 
      have : m / 2 < m := bitwise_rec_lemma (h ▸ succ_ne_zero _)
      loop (m / 2) (acc.push <| getBit m)
  loop a #[]

def func (a b : Nat) : Nat := a + b

def myFunc := func 3

macro (name := defineNewField)
doc?:optional(docComment) "new_field" id:ident "with" 
  "prime: " p:num
  "generator: " g:num
  : command => do
    -- Extract the inputs here

    -- Do a bunch of calculations here
    let legP ← `(($p - 1) / 2)
    let gen ← `($g)
    -- make all the names here
    let legIdent := mkIdent `legendreConst
    let generatorIdent := mkIdent `generator
    let myfuncIdent := mkIdent `myFunc
    let bitsIdent := mkIdent `bits

    let blah ← `(func $gen)
    let foo2 ← `(getBits $gen)
    -- put it all together here
    `(
      $[$doc?:docComment]? structure $id where
        data : Nat
        wrapped : Bool := Bool.false

      namespace $id

      instance : ToString $id where
        toString := fun  ⟨data, wrap⟩ => if wrap then s!"{data}ₘ" else s!"{data}"

      def $legIdent : Nat := $legP

      def $generatorIdent : $id where data := $gen

      /-- adds the generator -/
      def $myfuncIdent : Nat → Nat := $blah

      def $bitsIdent : Array Bit := $foo2

      end $id
    )

/-- define the new field -/
new_field newfield with 
  prime: 117
  generator: 19

#eval newfield.legendreConst

#eval newfield.myFunc 6

#eval newfield.bits