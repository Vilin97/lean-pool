/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Optimal

/-!
# The search meets its specification

The two halves of the correctness proof meet here.

* `dfsNode_reach` (soundness, `IsoGraph/Canon/Search.lean`) says the leaf the search settles on
  really is a leaf of the whole tree.
* `dfsNode_dom` (optimality, `IsoGraph/Canon/Optimal.lean`) says every leaf of the whole tree is
  dominated by it.

Instantiating the second at the root gives `canonSt_dom`, and together they give
`canonSt_bestKey` — the search's answer satisfies `BestKey`, the specification stated back in
`IsoGraph/Canon/Search.lean`.  Since `BestKey` is manifestly an isomorphism invariant
(`bestKey_transfer`) and determines its key uniquely (`bestKey_unique`), the certificate the
search returns does not depend on how the vertices were named: `canonical_cert_relabel`.

That is exactly what `Spec.LabellingInvariant` needs, once `certOf_get` is used to read the
adjacency matrix back out of the packed certificate (`canonical_get`).
-/

namespace IsoGraph
namespace Canon


theorem stopDepth_zero (ab : Option Nat) : stopDepth 0 ab = 0 := by
  cases ab with
  | none => rfl
  | some j => simp [stopDepth]

theorem ancReach_root (n : Nat) (f : Nat → Nat → Bool) (k : List (List UInt64)) :
    ancReach n f #[] 0 k ↔ Leafkey n f k := Iff.rfl

/-- **The search finds the best leaf.**  Instantiating `dfsNode_dom` at the root: the state the
search ends in dominates every leaf of the whole tree. -/
theorem canonSt_dom (n : Nat) (f : Nat → Nat → Bool) (k : List (List UInt64))
    (hk : Leafkey n f k) : Dom (canonSt n f) k := by
  have h := dfsNode_dom n f (n + 1) #[] (rootInv n f) (rootPart n f)
    { best := none, first := none, autos := #[], nodes := 0, abortTo := none }
    (fun _ => False) Node.root (by omega) rfl
    ⟨by simp, by simp, by simp⟩ (by intro l hl; rcases hl with hl | hl <;> simp at hl)
    (by intro l hl; rcases hl with hl | hl <;> simp at hl)
  have hd := h.2.1 k
  rw [show (#[] : Array Nat).size = 0 from rfl, stopDepth_zero] at hd
  exact (hd ((ancReach_root n f k).2 hk)).elim id False.elim

/-- **The search meets its specification.**  The key of the leaf it settles on is the largest key
of any leaf of the (unpruned) tree. -/
theorem canonSt_bestKey (n : Nat) (f : Nat → Nat → Bool) (b : Leaf)
    (hb : (canonSt n f).best = some b) : BestKey n f (leafKey b.invPath b.cert) := by
  refine ⟨canonSt_leafkey n f b hb, fun k' hk' => ?_⟩
  obtain ⟨l, hl, hle⟩ := canonSt_dom n f k' hk'
  rw [hb] at hl
  cases hl
  exact hle

/-- Reading the winner's certificate back gives the adjacency in the canonical order. -/
theorem canonical_get (n : Nat) (f : Nat → Nat → Bool) {i j : Nat} (hi : i < n) (hj : j < n) :
    certGet n (canonical (Graph.ofOracle n f)).cert i j
      = f (canonical (Graph.ofOracle n f)).lab[i]! (canonical (Graph.ofOracle n f)).lab[j]! := by
  have h := certOf_get (G := Graph.ofOracle n f) (lab := (canonical (Graph.ofOracle n f)).lab)
    (i := i) (j := j) (by simpa using hi) (by simpa using hj)
  rw [ofOracle_n] at h
  rw [canonical_cert, h]
  exact ofOracle_adj n f _ _ ((canonical_ok n f).lt i (by simpa using hi))
    ((canonical_ok n f).lt j (by simpa using hj))

/-- **The winner's certificate is an isomorphism invariant.**  The search on the renamed graph
settles on a leaf with the same certificate as the search on the original. -/
theorem canonical_cert_relabel (n : Nat) (f : Nat → Nat → Bool) {s : Nat → Nat}
    (hs : IsPerm n s) :
    (canonical (Graph.ofOracle n (fun v w => f (s v) (s w)))).cert
      = (canonical (Graph.ofOracle n f)).cert := by
  obtain ⟨b, hb, hcert, -⟩ := canonical_cert_leaf n f
  obtain ⟨b', hb', hcert', -⟩ := canonical_cert_leaf n (fun v w => f (s v) (s w))
  have hB : BestKey n f (leafKey b.invPath b.cert) := canonSt_bestKey n f b hb
  have hB' : BestKey n f (leafKey b'.invPath b'.cert) :=
    (bestKey_transfer hs _).1 (canonSt_bestKey n (fun v w => f (s v) (s w)) b' hb')
  rw [hcert, hcert', (leafKey_inj (bestKey_unique hB' hB)).2]

end Canon
end IsoGraph
