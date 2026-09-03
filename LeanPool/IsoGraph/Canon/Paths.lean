/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Monotone

/-!
# Where the search records its leaves

Two bookkeeping facts that the optimality argument needs, neither of which says anything about
which leaf is *best*.

* `extract_nodup` — the children of a node are pairwise distinct.  A node's child list is a slice
  of `Part.lab`, and `Part.lab` is a permutation of the vertices, so no vertex is visited twice.
* `dfsNode_paths` — a call to `dfsNode` at `path` only ever records leaves *below* `path`.  It is
  stated parametrically in a predicate `P` on paths: if everything the state already holds
  satisfies `P`, and everything extending `path` satisfies `P`, then that is still true when the
  call returns.  Instantiating `P` differently at each use turns this one lemma into the running
  invariant "the incumbent's path does not go down a branch we have not explored yet".
-/

namespace IsoGraph
namespace Canon

/-! ## The children of a node are distinct -/

theorem lab_nodup {n : Nat} {p : Part} (hp : Part.WF n p) : p.lab.toList.Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [Array.length_toList, hp.labSize] at hi hj
  intro he
  have h1 := hp.posLab i hi
  have h2 := hp.posLab j hj
  rw [show p.lab[i]! = p.lab.toList[i] by
    rw [getElem!_pos p.lab i (by rw [hp.labSize]; exact hi)]; simp] at h1
  rw [show p.lab[j]! = p.lab.toList[j] by
    rw [getElem!_pos p.lab j (by rw [hp.labSize]; exact hj)]; simp] at h2
  rw [he] at h1
  omega

theorem extract_nodup {n : Nat} {p : Part} (hp : Part.WF n p) (a b : Nat) :
    (p.lab.extract a b).toList.Nodup := by
  have h : (p.lab.extract a b).toList.Sublist p.lab.toList := by
    rw [Array.toList_extract]
    exact ((p.lab.toList.drop a).take_sublist _).trans (p.lab.toList.drop_sublist a)
  exact (lab_nodup hp).sublist h

/-! ## Prefixes of paths -/

/-- `a` is an initial segment of `b`. -/
def PathPre (a b : Array Nat) : Prop := a.size ≤ b.size ∧ ∀ i, i < a.size → a[i]! = b[i]!

theorem PathPre.refl (a : Array Nat) : PathPre a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem PathPre.trans {a b c : Array Nat} (h1 : PathPre a b) (h2 : PathPre b c) : PathPre a c :=
  ⟨h1.1.trans h2.1, fun i hi => (h1.2 i hi).trans (h2.2 i (Nat.lt_of_lt_of_le hi h1.1))⟩

theorem PathPre.push_self (a : Array Nat) (v : Nat) : PathPre a (a.push v) :=
  ⟨by simp, fun i hi => (push_getElemD_lt a v hi).symm⟩

theorem PathPre.of_push {a b : Array Nat} {v : Nat} (h : PathPre (a.push v) b) : PathPre a b :=
  (PathPre.push_self a v).trans h

theorem PathPre.push_iff {a b : Array Nat} {v : Nat} :
    PathPre (a.push v) b ↔ (PathPre a b ∧ a.size < b.size ∧ b[a.size]! = v) := by
  constructor
  · intro h
    have hsz : a.size < b.size := by have := h.1; rw [Array.size_push] at this; omega
    refine ⟨⟨hsz.le, fun i hi => ?_⟩, hsz, ?_⟩
    · have := h.2 i (by rw [Array.size_push]; omega)
      rwa [push_getElemD_lt a v hi] at this
    · have := h.2 a.size (by rw [Array.size_push]; omega)
      rw [push_getElemD_eq] at this
      exact this.symm
  · rintro ⟨h, hsz, hb⟩
    refine ⟨by rw [Array.size_push]; omega, fun i hi => ?_⟩
    rw [Array.size_push] at hi
    rcases Nat.lt_or_ge i a.size with h1 | h1
    · rw [push_getElemD_lt a v h1]; exact h.2 i h1
    · have : i = a.size := by omega
      subst this
      rw [push_getElemD_eq]; exact hb.symm

/-! ## The search only records leaves of the subtree it is in -/

/-- Every leaf a state remembers — incumbent or first — has a path satisfying `P`. -/
def StQ (P : Array Nat → Prop) (st : St) : Prop :=
  (∀ l, st.best = some l → P l.path) ∧ (∀ l, st.first = some l → P l.path)

theorem StQ.mono {P P' : Array Nat → Prop} {st : St} (h : StQ P st) (hPP : ∀ Q, P Q → P' Q) :
    StQ P' st :=
  ⟨fun l hb => hPP _ (h.1 l hb), fun l hf => hPP _ (h.2 l hf)⟩

theorem StQ.addAuto {P : Array Nat → Prop} {st : St} (h : StQ P st) (g : Array Nat) :
    StQ P (st.addAuto g) :=
  ⟨fun l hb => h.1 l ((addAuto_best st g) ▸ hb), fun l hf => h.2 l ((addAuto_first st g) ▸ hf)⟩

theorem StQ.unwind {P : Array Nat → Prop} {st : St} (h : StQ P st) (path : Array Nat) :
    StQ P (Canon.unwind path st) :=
  ⟨fun l hb => h.1 l ((unwind_best path st) ▸ hb), fun l hf => h.2 l ((unwind_first path st) ▸ hf)⟩

theorem pruneNode_Q {P : Array Nat → Prop} {invPath : Array UInt64} {st st' : St}
    (h : pruneNode invPath st = some st') (hst : StQ P st) : StQ P st' := by
  rw [pruneNode] at h
  split at h
  · cases h; exact hst
  · split at h
    · exact absurd h (by simp)
    · cases h; exact ⟨by simp, hst.2⟩
    · cases h; exact hst

theorem leafUpdate_Q {P : Array Nat → Prop} {G : Graph} {path : Array Nat}
    {invPath : Array UInt64} {lab : Array Nat} {st : St} (hp : P path) (hst : StQ P st) :
    StQ P (leafUpdate G path invPath lab st) := by
  refine ⟨fun l hb => ?_, fun l hf => ?_⟩
  · rcases leafUpdate_best G path invPath lab st with h | h
    · exact hst.1 l (h ▸ hb)
    · rw [h] at hb; cases hb; exact hp
  · rcases leafUpdate_first G path invPath lab st with h | h
    · exact hst.2 l (h ▸ hf)
    · rw [h] at hf; cases hf; exact hp

/-- **The leaves a node records lie below it.**  Anything the state already held keeps whatever
property it had; anything added while the node runs has a path extending the node's. -/
theorem dfsNode_paths (n : Nat) (f : Nat → Nat → Bool) (P : Array Nat → Prop) :
    ∀ (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St),
      (∀ Q, PathPre path Q → P Q) → StQ P st →
        StQ P (dfsNode (Graph.ofOracle n f) fuel path invPath p st) := by
  refine dfsNode.induct (Graph.ofOracle n f)
    (motive1 := fun fuel path invPath p st =>
      (∀ Q, PathPre path Q → P Q) → StQ P st →
        StQ P (dfsNode (Graph.ofOracle n f) fuel path invPath p st))
    (motive2 := fun fuel path invPath p verts processed orb st =>
      (∀ Q, PathPre path Q → P Q) → StQ P st →
        StQ P (dfsChildren (Graph.ofOracle n f) fuel path invPath p verts processed orb st))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 => intro path invPath p st _ hst; rw [dfsNode_zero]; exact hst
  case refine_2 =>
    intro path invPath p st fuel habort _ hst
    rw [dfsNode_abort habort]; exact hst
  case refine_3 =>
    intro path invPath p st fuel habort hprune _ hst
    rw [dfsNode_pruned (by simpa using habort) hprune]; exact hst
  case refine_4 =>
    intro path invPath p st fuel habort st1 hprune htc hpre hst
    rw [dfsNode_leaf (by simpa using habort) hprune htc]
    have h1 : StQ P st1 := pruneNode_Q hprune hst
    exact leafUpdate_Q (hpre path (PathPre.refl path)) h1
  case refine_5 =>
    intro path invPath p st fuel habort st1 hprune st2 c htc verts orb ih hpre hst
    rw [dfsNode_branch (by simpa using habort) hprune htc]
    have h1 : StQ P st1 := pruneNode_Q hprune hst
    exact ih hpre h1
  case refine_6 =>
    intro fuel path invPath p processed orb st _ hst
    rw [dfsChildren_nil]; exact hst
  case refine_7 =>
    intro fuel path invPath p processed orb st v vs habort _ hst
    rw [dfsChildren_abort habort]; exact hst
  case refine_8 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark ih hpre hst
    rw [dfsChildren_marked (by simpa using habort) hmark]
    exact ih hpre hst
  case refine_9 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 ih1 hpre hst
    rw [dfsChildren_step_stop (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href habort2]
    exact (ih1 (fun Q hQ => hpre Q hQ.of_push) hst).unwind path
  case refine_10 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 orb2 ih1 _ih1' ih2 hpre hst
    rw [dfsChildren_step_go (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href
      (by simp only [Bool.not_eq_true] at habort2; exact habort2)]
    exact ih2 hpre ((ih1 (fun Q hQ => hpre Q hQ.of_push) hst).unwind path)

end Canon
end IsoGraph
