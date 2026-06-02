/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import LeanPool.Polylean.ConjInvLength.Length
import Std.Data.HashMap

/-!
# Cached proof nodes for conjugacy-invariant length bounds
-/

namespace LeanPool.Polylean

/-- A node recording which inequality or equality was used to derive a word-length bound. -/
inductive ProofNode : Type
| empty : ProofNode
| gen : (l : Letter) → ProofNode
| triang : (w₁ w₂ : Wrd) → ProofNode
| conj : (l : Letter) → (w : Wrd) → ProofNode
| power : (n : Nat) → (w : Wrd) → ProofNode
deriving Repr, BEq

open ProofNode

namespace ProofNode

/-- The word whose length bound is justified by a proof node. -/
def top : ProofNode → Wrd
| empty => #[]
| gen l => #[l]
| triang w₁ w₂ => w₁ ++ w₂
| conj l w => w ^ l
| power _ w => w

/-- Render a proof node as a human-readable proof step. -/
def toString : ProofNode → String
| empty => "l(e) = 0 (trivial word)"
| gen l => s!"l({l}) = 1 (normalization)"
| triang w₁ w₂ => s!"l({w₁ ++ w₂}) ≤ l({w₁}) + l({w₂}) (triangle inequality)"
| conj l w => s!"l({w}^{l}) = l({w}) (conjugacy invariance)"
| power n w => s!"l(w) ≤  l({w^n})/{n} (homogeneity)"

instance : ToString ProofNode := ⟨ProofNode.toString⟩

/-- The previously derived words needed by this proof node. -/
def base : ProofNode → List Wrd
| empty => []
| gen _ => []
| triang w₁ w₂ => [w₁, w₂]
| conj _ w => [w]
| power n w => [w ^ n]


/-- Length immediately justified by a base proof node, if any. -/
def baseLength : ProofNode → Option Nat
| empty => some 0
| gen _ => some 1
| _ => none

end ProofNode


/-- Cache of floating-point length bounds for array-backed words. -/
initialize floatNormCache :
    IO.Ref (Std.HashMap Wrd Float) ← IO.mkRef Std.HashMap.emptyWithCapacity

/-- Cache of proof nodes witnessing the best known bound for each word. -/
initialize proofCache :
    IO.Ref (Std.HashMap Wrd ProofNode) ← IO.mkRef Std.HashMap.emptyWithCapacity

/-- Look up a cached floating-point length bound. -/
private def cacheLength? (w : Wrd) : IO (Option Float) :=
    do
    let cache ← floatNormCache.get
    match cache.get? w with
    | some n => pure (some n)
    | none => pure none

/-- Compute a floating-point length bound while caching the proof nodes used. -/
def lengthNodes (w : Wrd) : IO Float := do
  match ← cacheLength? w with
  | some n =>
      pure n
  | none =>
    match h : w.size with
    | 0 =>
      floatNormCache.set <| (← floatNormCache.get).insert #[] 0
      proofCache.set <| (← proofCache.get).insert #[] empty
      return 0
    | m + 1 => do
      let x := w.back
      let ys : Wrd := w.pop
      have ysize : ys.size = m := by
        rw [Array.size_pop, h]
        rfl
      have _ : ys.size < w.size := by
        rw [ysize, h]
        exact Nat.lt_succ_self m
      let base := 1 + (← lengthNodes ys)
      let derived ←  (ys.splits x⁻¹).mapM fun ⟨(fst, snd), hfst_snd⟩ => do
        have hsplit : fst.size + snd.size < w.size := by
          rw [h, ← ysize]
          exact Nat.lt_trans hfst_snd (Nat.lt_succ_self _)
        have _ : fst.size < w.size := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hsplit
        have _ : snd.size < w.size := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hsplit
        return ((← lengthNodes fst) + (← lengthNodes snd), fst, snd)
      let (res, nodes) := derived.foldl (
          fun (l₁, ns) (l₂, fst, snd) =>
            if l₂ < l₁ then (l₂, [triang fst (snd^(x⁻¹)), conj (x⁻¹) snd]) else (l₁, ns)
      ) (base, [gen x, triang ys #[x]])
      floatNormCache.set <| (← floatNormCache.get).insert w res
      for node in nodes do
        proofCache.set <| (← proofCache.get).insert (node.top) node
      return res
termination_by w.size

/-- Improve a word-length bound using a power of the word. -/
def powerLength : Wrd → Nat → IO Float
| w, n => do
  let pl ← lengthNodes (w ^ n)
  let res := pl / n.toFloat
  match ← cacheLength? w with
  | none =>
    floatNormCache.set <| (← floatNormCache.get).insert w res
    if n > 1 then
      proofCache.set <| (← proofCache.get).insert w (power n w)
    return res
  | some l₀ =>
    if res < l₀ then
      IO.println s!"updated cache for {w}"
      floatNormCache.set <| (← floatNormCache.get).insert w res
      if n > 1 then
        proofCache.set <| (← proofCache.get).insert w (power n w)
      return res
    else
      return l₀

/-- Recursively expand cached proof nodes with a bounded traversal fuel. -/
private def resolveProofWithFuel : Nat → Wrd → IO ((List ProofNode) × (List Wrd))
| 0, w => return ([], [w])
| fuel + 1, w => do
  let cache ← proofCache.get
  match cache.get? w with
  | none => return ([], [w])
  | some node =>
    let ws := node.base
    let offspring ←  ws.mapM (resolveProofWithFuel fuel)
    return offspring.foldl (fun (ns, ws) (ns', ws') => (ns ++ ns', ws ++ ws') ) ([node], [])

/-- Recursively expand cached proof nodes needed to justify a word. -/
def resolveProof (w : Wrd) : IO ((List ProofNode) × (List Wrd)) := do
  let cache ← proofCache.get
  resolveProofWithFuel (cache.size + 1) w

/-- Recompute a derived length with a bounded traversal fuel. -/
private def derivedLengthWithFuel : Nat → Wrd → IO Float
| 0, w => throw <| IO.userError s!"proof cache recursion exhausted at {w}"
| fuel + 1, w => do
  let cache ← proofCache.get
  match cache.get? w with
  | none => panic! s!"no cached node for {w}"
  | some node =>
    match node with
    | empty => return 0.0
    | gen _ => return 1.0
    | triang w₁ w₂ => return (← derivedLengthWithFuel fuel w₁) + (← derivedLengthWithFuel fuel w₂)
    | conj _ w => derivedLengthWithFuel fuel w
    | power n w => return (← derivedLengthWithFuel fuel (w^n)) / n.toFloat

/-- Recompute the derived length from cached proof nodes, panicking if a node is absent. -/
def derivedLength (w : Wrd) : IO Float := do
  let cache ← proofCache.get
  derivedLengthWithFuel (cache.size + 1) w

/-- Recompute the derived length from cached proof nodes, panicking if a node is absent. -/
private def derivedLength! (w : Wrd) : IO Float := do
  derivedLength w

/-- Recompute a derived length proof with a bounded traversal fuel. -/
private def derivedProofWithFuel : Nat → Wrd → IO (Float × (List ProofNode))
| 0, w => throw <| IO.userError s!"proof cache recursion exhausted at {w}"
| fuel + 1, w => do
  let cache ← proofCache.get
  match cache.get? w with
  | none => panic! s!"no cached node for {w}"
  | some node =>
    match node with
    | empty => return (0.0, [empty])
    | gen l => return (1.0, [gen l])
    | triang w₁ w₂ =>
      let (l₁, ns₁) ← derivedProofWithFuel fuel w₁
      let (l₂, ns₂) ← derivedProofWithFuel fuel w₂
      return (l₁ + l₂, ns₁ ++ ns₂ ++ [triang w₁ w₂])
    | conj l w =>
      let (l₀, ns) ← derivedProofWithFuel fuel w
      return (l₀, ns ++ [conj l w])
    | power n w =>
      let (l₀, ns) ← derivedProofWithFuel fuel (w^n)
      return (l₀ / n.toFloat, ns ++ [power n w])

/-- Recompute the derived length together with the list of proof nodes used. -/
def derivedProof (w : Wrd) : IO (Float × (List ProofNode)) := do
  let cache ← proofCache.get
  derivedProofWithFuel (cache.size + 1) w

/-- Recompute the derived length together with the list of proof nodes used. -/
private def derivedProof! (w : Wrd) : IO (Float × (List ProofNode)) := do
  derivedProof w

end LeanPool.Polylean
