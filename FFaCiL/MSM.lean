import FFaCiL.EllipticCurve
import YatimaStdLib.ByteArray
import Std.Data.HashMap.Basic

def naiveMSM {F : Type _} [PrimeField F] {C : Curve F} (params : Array $ Nat × ProjectivePoint C )
    : ProjectivePoint C :=
  params.foldl (init := .zero) fun acc (n, p) => acc + n * p

open Std 

variable {F : Type _} [Field F] {C : Curve F}

def CHUNK_LENGTH := 2

def CHUNK_WIDTH := 8 * CHUNK_LENGTH

def CHUNK_CONTENT := 2 ^ CHUNK_WIDTH

def maxContent (ns : Array Nat) : Nat :=
  ns.map (fun n => n.log2) |> (Array.maxD · 0)

def numChunks (ns : Array Nat) : Nat :=
  let max := maxContent ns
  max / (8 * CHUNK_LENGTH) + 1

def Nat.chunk (n idx : Nat) : Nat :=
  let n' := n >>> (CHUNK_WIDTH * idx)
  n' % CHUNK_CONTENT

abbrev MSMInstance {F} [Field F] (C : Curve F) := HashMap Nat (ProjectivePoint C)

def generateInstances {F} [Field F] {C : Curve F} (pairs : Array (Nat × ProjectivePoint C))
    : Array $ MSMInstance C := Id.run do
  let size := numChunks $ pairs.map fun (n, _) => n
  let mut answer := Array.mkEmpty size
  for idx in [:size] do
    let mut inst : MSMInstance C := .empty 
    for (n, P) in pairs do
      if inst.contains $ n.chunk idx then
        inst := inst.insert (n.chunk idx) $ inst.find! (n.chunk idx) + P
      else
        inst := inst.insert (n.chunk idx) P
    answer := answer.push inst
  return answer

def MSMInstance.evaluate (inst : MSMInstance C) (offset : Nat) : ProjectivePoint C := Id.run do
  let mut idx := CHUNK_CONTENT - 1
  let mut counter := .zero
  let mut answer : ProjectivePoint C := .zero
  for _ in [1:CHUNK_CONTENT] do
    counter := counter + inst.findD idx .zero
    answer := answer + counter
    idx := idx - 1
  return (Nat.repeat ProjectivePoint.double offset) answer

def pippengerMSM (pairs : Array (Nat × ProjectivePoint C)) : ProjectivePoint C :=
  let instances := generateInstances pairs
  let answers := instances.mapIdx fun idx inst => Task.spawn fun () => inst.evaluate (CHUNK_WIDTH * idx)
  answers.foldl (init := .zero) fun acc P => acc + P.get
