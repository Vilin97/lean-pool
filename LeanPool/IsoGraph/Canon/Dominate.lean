/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Leaves

/-!
# Domination bookkeeping for the optimality proof

Small lemmas about *how far down* a returning search call has guaranteed that every leaf key is
dominated by the incumbent, and about moving a subtree along an automorphism.

* `Beaten.dom` — a strictly beaten key is in particular dominated.
* `stopDepth` — the depth a returning call vouches for: its own depth when it ran to completion,
  and the backjump target's child depth when it was cut short.
* `leafUpdate_dom_new` — after recording a leaf, that leaf's key is dominated.
* `leafUpdate_abort` — a backjump request always points at the branch point with a leaf the state
  already holds, and only when the certificates tie.
* `partEquiv_inv`, `subR_inv` — an automorphism fixing a node carries the leaves below the child
  `γ w` onto the leaves below the child `w`, so the two children are interchangeable.
-/

namespace IsoGraph
namespace Canon

/-! ## Domination helpers -/

theorem Beaten.dom {st : St} {k : List (List UInt64)} (h : Beaten st k) : Dom st k := by
  obtain ⟨l, hl, hk⟩ := h
  exact ⟨l, hl, by rw [hk]; simp⟩

/-- The depth to which a returning call guarantees that everything below is dominated:
the node itself if it finished, the backjump target's child if it was cut short. -/
def stopDepth (d : Nat) : Option Nat → Nat
  | none => d
  | some j => min (j + 1) d

/-- A leaf update dominates the leaf it was given. -/
theorem leafUpdate_dom_new (G : Graph) (path : Array Nat) (invPath : Array UInt64)
    (lab : Array Nat) (st : St) :
    Dom (leafUpdate G path invPath lab st) (leafKey invPath (certOf G lab)) := by
  rw [leafUpdate]
  simp only [Id.run]
  repeat' split
  all_goals first
    | exact ⟨_, rfl, cmp_le_refl _⟩
    | exact ⟨_, by simp only [addAuto_best] at *; assumption, by rw [compare_leafKey]; simp_all⟩
    | exact ⟨_, by assumption, by rw [compare_leafKey]; simp_all⟩

/-- A leaf update only ever asks to backjump to the branch point with a leaf it already
holds, and only when the certificates tie. -/
theorem leafUpdate_abort {G : Graph} {path : Array Nat} {invPath : Array UInt64}
    {lab : Array Nat} {st : St} {j : Nat}
    (h : (leafUpdate G path invPath lab st).abortTo = some j) :
    ∃ l, (st.first = some l ∨ st.best = some l) ∧ lexCmpU64 (certOf G lab) l.cert = .eq
      ∧ j = commonPrefix path l.path := by
  rw [leafUpdate] at h
  simp only [Id.run] at h
  repeat' split at h
  all_goals try rw [Nat.min_def] at h
  all_goals try split at h
  all_goals first
    | simp at h
    | exact ⟨_, Or.inl (by assumption), by simp_all, (Option.some.inj h).symm⟩
    | exact ⟨_, Or.inr (by assumption), by simp_all, (Option.some.inj h).symm⟩
    | exact ⟨_, Or.inr (by simp only [addAuto_best] at *; assumption), by simp_all,
        (Option.some.inj h).symm⟩

/-! ## Moving a subtree back along an automorphism -/

theorem partEquiv_inv {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} (hg : IsAutoArr n f g)
    {p : Part} (he : PartEquiv n (fun x => g[x]!) p p) :
    PartEquiv n (fun x => (invAuto n g)[x]!) p p := by
  refine ⟨he.cst, he.cen, fun v hv => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hg.perm.surj hv
  rw [invAuto_get hg.perm hu]
  exact (he.cell u hu).symm

/-- **Orbit pruning, the direction the search needs.**  If `γ` fixes the node, the leaves below
the child `γ w` are exactly the leaves below the child `w`. -/
theorem subR_inv {n : Nat} {f : Nat → Nat → Bool} {g : Array Nat} (hg : IsAutoArr n f g)
    {p : Part} (hp : Part.WF n p) (he : PartEquiv n (fun x => g[x]!) p p)
    {invPath : Array UInt64} {w : Nat} (hw : w < n) {k : List (List UInt64)}
    (h : SubR n f invPath p g[w]! k) : SubR n f invPath p w k := by
  have := reach_child_auto (invAuto_isAuto hg) hp (partEquiv_inv hg he) (hg.perm.lt w hw) h
  rwa [invAuto_get hg.perm hw] at this

end Canon
end IsoGraph
