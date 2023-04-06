import FFaCiL.EllipticCurve
import YatimaStdLib.ByteArray
import Std.Data.HashMap.Basic

/-!
# Multiscalar Multiplication

This module implements Pippenger's algorithm to calculate an MSM on generic curves.

The implementation is based off https://cr.yp.to/papers/pippenger.pdf and 
https://www.slideshare.net/GusGutoski/multiscalar-multiplication-state-of-the-art-and-new-ideas
-/

/--
The naive implementation of multi-scalar multiplication. Useful mostly as a reference for testing.
-/
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

/-
Calculates the chunk at index `idx` of the natural number `n`, where each chunk is a length 
`CHUNK_WIDTH` binary substring of the binary expansion of `n`. 
-/
def Nat.chunk (n idx : Nat) : Nat :=
  let n' := n >>> (CHUNK_WIDTH * idx)
  n' % CHUNK_CONTENT

/--
An `MSMInstance` stores the points `Gᵢ` and coefficients `nᵢ` in an MSM calculation `∑ nᵢGᵢ`. 
-/
abbrev MSMInstance {F} [Field F] (C : Curve F) := HashMap Nat (ProjectivePoint C)

/--
Generates an Array of MSM Instances from a single MSM instance by splitting the coefficients into
chunks of width `CHUNK_WIDTH`. These are later recombined in `pippengerMSM`.
-/
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

/--
Evaluates an `inst : MSMInstance` with an `offset : Nat` corresponding to the number of squarings
to evaluate at the end of the calculation.

The evaluation is done using Pippenger's bucket method.
-/
def MSMInstance.evaluate (inst : MSMInstance C) (offset : Nat) : ProjectivePoint C := Id.run do
  let mut idx := CHUNK_CONTENT - 1
  let mut counter := .zero
  let mut answer : ProjectivePoint C := .zero
  for _ in [1:CHUNK_CONTENT] do
    counter := counter + inst.findD idx .zero
    answer := answer + counter
    idx := idx - 1
  return (Nat.repeat ProjectivePoint.double offset) answer

/--
Pippenger's algorithm for recombining the separate evaluations from `MSMInstance.evaluate`.
This implementation is parallelized and evaluates each `MSMInstance` as a separate task.
-/
def pippengerMSM (pairs : Array (Nat × ProjectivePoint C)) : ProjectivePoint C :=
  let instances := generateInstances pairs
  let answers := instances.mapIdx fun idx inst => 
    Task.spawn fun () => inst.evaluate (CHUNK_WIDTH * idx)
  answers.foldl (init := .zero) fun acc P => acc + P.get
