import FFaCiL.EllipticCurve
import YatimaStdLib.ByteArray
import Std.Data.HashMap.Basic

def naiveMSM {F : Type _} [PrimeField F] {C : Curve F} (params : Array $ Nat × ProjectivePoint C )
    : ProjectivePoint C :=
  params.foldl (init := .zero) fun acc (n, p) => acc + n * p

section Actions

variable {F : Type _} [Field F] {C : Curve F}

private def bAAction (ba : ByteArray) (P : ProjectivePoint C) : ProjectivePoint C := 
  ba.toUInt64LE!.toNat * P -- TODO : Unsafe, assumes chunks have `size < 8`

end Actions
section MSM

variable {F : Type _} [Field F] {C : Curve F}

def CHUNK_LENGTH := 4

def coeffsToByteArray (ns : Array Nat) : Array ByteArray :=
  ns.map fun n => n.toByteArrayLE

abbrev BASlice := ByteArray

def chunk (ba : ByteArray) : Array BASlice := Id.run do
  let mut answer := #[]
  let mut head := 0
  while head < ba.size do
    answer := answer.push $ ba.slice head CHUNK_LENGTH
    head := head + CHUNK_LENGTH
  return answer

def getChunks (ns : Array Nat) : Array (Array BASlice) :=
  ns.map fun n => chunk n.toByteArrayLE

def getMaxSize (bas : Array (Array BASlice)) : Nat := 
  Array.maxD (bas.map fun ba => ba.size) 0

def splitChunks (bas : Array (Array BASlice)) : Array (Array BASlice) := Id.run do
  let mut answer := #[]
  let mut subanswer := #[]
  let max := getMaxSize bas
  for idx in [:max] do -- TODO : Replace `bas[0]!.size` with the max size of any of the BAs
    subanswer := #[]
    for ba in bas do
      subanswer := subanswer.push $ ba.getD idx (.mk #[0])
    answer := answer.push subanswer

  return answer

def seedChunks : Array Nat → Array (Array BASlice) := 
  splitChunks ∘ getChunks 

def splitMSM (pnP : Array (Nat × ProjectivePoint C))
    : Array $ (Array BASlice) × Array (ProjectivePoint C) := Id.run do
  let coeffs := pnP.map fun p => p.fst
  let points := pnP.map fun p => p.snd
  let chunks := seedChunks coeffs
  let mut answer := #[]
  for chunk in chunks do
    answer := answer.push (chunk, points)
  return answer

end MSM

section smallMSM

namespace Better

open Std 

variable {F : Type _} [Field F] {C : Curve F}

def CHUNK_LENGTH := 4

def CHUNK_WIDTH := 8 * CHUNK_LENGTH

def CHUNK_CONTENT := 2 ^ CHUNK_WIDTH

def maxContent (ns : Array Nat) : Nat :=
  ns.map (fun n => n.log2) |> (Array.maxD · 0)

def numChunks (ns : Array Nat) : Nat :=
  let max := maxContent ns
  max / (8 * CHUNK_LENGTH) + 1

def _root_.Nat.chunk (n idx : Nat) : Nat :=
  let n' := n >>> (CHUNK_WIDTH * idx)
  n' % CHUNK_CONTENT

abbrev _root_.MSMInstance {F} [Field F] (C : Curve F) := HashMap Nat (ProjectivePoint C)

instance : ToString $ MSMInstance C where
  toString := fun x => s!"{x.size}"

def generateInstances {F} [Field F] {C : Curve F} (pairs : Array (Nat × ProjectivePoint C))
    : Array $ MSMInstance C := Id.run do
  let size := numChunks $ pairs.map fun (n, _) => n
  let mut answer := Array.mkEmpty size
  for idx in [:size] do
    let mut inst : MSMInstance C := .empty
    for (n, P) in pairs do
      if inst.contains $ n.chunk idx then
        inst := inst.insert (n.chunk idx) $ inst.find! n + P
      else
        inst := inst.insert (n.chunk idx) P
    answer := answer.push inst
  return answer

def _root_.MSMInstance.evaluate (inst : MSMInstance C) : ProjectivePoint C := 
  inst.fold (init := .zero) fun acc key val => acc + key * val

end Better

end smallMSM