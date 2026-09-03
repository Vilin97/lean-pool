/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Progress

/-!
# The incumbent never gets worse

The search keeps one leaf, `St.best`, and replaces it only when it finds a better one.  This file
makes that precise: whatever the search ends up holding is at least as good as anything it held
on the way.

There is one place where the incumbent is *dropped* rather than improved — `pruneNode`, when the
node's invariant path already beats the incumbent's.  That is still monotone, but only because of
`Progress.lean`: the node is then guaranteed to come back with a leaf of its own subtree
(`dfsNode_best`, `dfsNode_reach`), and every leaf of that subtree beats what was dropped
(`pruneNode_cleared`).  `dfsNode_mono_cleared` packages the two, and `dfsNode_prune_shift` — that
clearing the incumbent does not change what the node does next — is what lets it be applied to the
whole `dfsNode` call rather than to its innards.

The comparison used throughout is `compare k k' ≠ .gt` on `leafKey`s, the same order `BestKey`
is stated with.
-/

namespace IsoGraph
namespace Canon

open Std

/-! ## Order helpers -/

theorem cmp_le_refl (k : List (List UInt64)) : compare k k ≠ .gt := by
  have := ReflCmp.isLE_rfl (cmp := compare (α := List (List UInt64))) (a := k)
  revert this; cases compare k k <;> simp [Ordering.isLE]

theorem cmp_le_trans {a b c : List (List UInt64)} (h1 : compare a b ≠ .gt)
    (h2 : compare b c ≠ .gt) : compare a c ≠ .gt := by
  have h1' : (compare a b).isLE := by revert h1; cases compare a b <;> simp [Ordering.isLE]
  have h2' : (compare b c).isLE := by revert h2; cases compare b c <;> simp [Ordering.isLE]
  have := TransCmp.isLE_trans h1' h2'
  revert this; cases compare a c <;> simp [Ordering.isLE]

theorem lexCmpU64_gt_symm {a b : Array UInt64} (h : lexCmpU64 a b = .gt) :
    lexCmpU64 b a = .lt := by
  rw [lexCmpU64_eq_compare] at h ⊢
  exact OrientedCmp.lt_of_gt h

/-! ## Domination -/

/-- `k` is no better than the leaf the state holds. -/
def Dom (st : St) (k : List (List UInt64)) : Prop :=
  ∃ l, st.best = some l ∧ compare k (leafKey l.invPath l.cert) ≠ .gt

/-- The incumbent never gets worse. -/
def BestMono (st st' : St) : Prop :=
  ∀ l, st.best = some l → Dom st' (leafKey l.invPath l.cert)

theorem BestMono.rfl (st : St) : BestMono st st :=
  fun l hl => ⟨l, hl, cmp_le_refl _⟩

theorem Dom.mono {st st' : St} {k : List (List UInt64)} (h : Dom st k) (hm : BestMono st st') :
    Dom st' k := by
  obtain ⟨l, hl, hk⟩ := h
  obtain ⟨l', hl', hk'⟩ := hm l hl
  exact ⟨l', hl', cmp_le_trans hk hk'⟩

theorem BestMono.trans {st st' st'' : St} (h : BestMono st st') (h' : BestMono st' st'') :
    BestMono st st'' := fun l hl => (h l hl).mono h'

theorem BestMono.of_best_eq {st st' : St} (h : st'.best = st.best) : BestMono st st' :=
  fun l hl => ⟨l, h.trans hl, cmp_le_refl _⟩

/-! ## `leafUpdate` improves the incumbent -/

theorem leafUpdate_best_ge (G : Graph) (path : Array Nat) (invPath : Array UInt64)
    (lab : Array Nat) (st : St) :
    (leafUpdate G path invPath lab st).best = st.best
      ∨ ((leafUpdate G path invPath lab st).best
            = some { path, invPath, cert := certOf G lab, lab }
          ∧ ∀ b, st.best = some b →
              lexCmpU64 invPath b.invPath = .gt ∨
                (lexCmpU64 invPath b.invPath = .eq
                  ∧ lexCmpU64 (certOf G lab) b.cert = .gt)) := by
  rw [leafUpdate]
  simp only [Id.run]
  repeat' split
  all_goals first
    | exact Or.inl rfl
    | exact Or.inl (addAuto_best _ _)
    | exact Or.inl ((addAuto_best _ _).trans (addAuto_best _ _))
    | (refine Or.inr ⟨rfl, ?_⟩; intro b hb; simp_all [addAuto_best])

theorem leafUpdate_mono (G : Graph) (path : Array Nat) (invPath : Array UInt64)
    (lab : Array Nat) (st : St) : BestMono st (leafUpdate G path invPath lab st) := by
  intro b hb
  rcases leafUpdate_best_ge G path invPath lab st with h | ⟨h, hcmp⟩
  · exact ⟨b, h.trans hb, cmp_le_refl _⟩
  · refine ⟨_, h, ?_⟩
    rw [compare_leafKey]
    rcases hcmp b hb with hgt | ⟨heq, hgt⟩
    · rw [lexCmpU64_gt_symm hgt]; simp
    · rw [← lexCmpU64_eq_iff.1 heq, lexCmpU64_refl, lexCmpU64_gt_symm hgt]; simp

/-! ## `pruneNode` only discards a dominated incumbent -/

theorem pruneNode_mono {invPath : Array UInt64} {st st' : St}
    (h : pruneNode invPath st = some st') :
    st'.best = st.best ∨ (st'.best = none ∧ ∀ b, st.best = some b →
      lexCmpU64 invPath (b.invPath.extract 0 invPath.size) = .gt) := by
  rw [pruneNode] at h
  split at h
  · cases h; exact Or.inl rfl
  · rename_i b hb
    split at h
    · exact absurd h (by simp)
    · cases h
      refine Or.inr ⟨rfl, fun b' hb' => ?_⟩
      rw [hb] at hb'; cases hb'; assumption
    · cases h; exact Or.inl rfl

theorem compare_append_gt {ip b : List UInt64} (tail : List UInt64)
    (h : compare ip (b.take ip.length) = .gt) : compare (ip ++ tail) b = .gt := by
  induction ip generalizing b with
  | nil => exact absurd h (by simp)
  | cons a ip ih =>
    cases b with
    | nil => rw [List.cons_append, List.compare_cons_nil]
    | cons x b =>
      rw [List.length_cons, List.take_succ_cons, List.compare_cons_cons] at h
      rw [List.cons_append, List.compare_cons_cons]
      cases hax : compare a x with
      | gt => rfl
      | lt => rw [hax] at h; simp at h
      | eq => rw [hax] at h; simpa using ih (by simpa using h)

theorem compare_leafKey_gt {ip b tail c c' : List UInt64}
    (h : compare ip (b.take ip.length) = .gt) : compare [ip ++ tail, c] [b, c'] = .gt := by
  rw [List.compare_cons_cons, compare_append_gt tail h]; rfl

/-- When `pruneNode` throws the incumbent away, every leaf below the node beats it. -/
theorem pruneNode_cleared {n : Nat} {f : Nat → Nat → Bool} {invPath : Array UInt64} {p : Part}
    {st st' : St} {b : Leaf} {k : List (List UInt64)} (h : pruneNode invPath st = some st')
    (hnone : st'.best = none) (hb : st.best = some b) (hk : Reach n f invPath p k) :
    compare (leafKey b.invPath b.cert) k ≠ .gt := by
  rcases pruneNode_mono h with heq | ⟨_, hgt⟩
  · rw [heq, hb] at hnone; exact absurd hnone (by simp)
  · obtain ⟨tail, c, rfl⟩ := reach_extends hk
    have h1 : compare invPath.toList (b.invPath.toList.take invPath.toList.length) = .gt := by
      have := hgt b hb
      rw [lexCmpU64_extract] at this
      simpa using this
    have h2 : compare [invPath.toList ++ tail, c] (leafKey b.invPath b.cert) = .gt := by
      rw [leafKey]; exact compare_leafKey_gt h1
    rw [OrientedCmp.lt_of_gt h2]
    simp

theorem pruneNode_mono' {invPath : Array UInt64} {st st' : St}
    (h : pruneNode invPath st = some st') :
    st' = st ∨ (st' = { st with best := none } ∧ ∀ b, st.best = some b →
      lexCmpU64 invPath (b.invPath.extract 0 invPath.size) = .gt) := by
  rw [pruneNode] at h
  split at h
  · cases h; exact Or.inl rfl
  · rename_i b hb
    split at h
    · exact absurd h (by simp)
    · cases h
      refine Or.inr ⟨rfl, fun b' hb' => ?_⟩
      rw [hb] at hb'; cases hb'; assumption
    · cases h; exact Or.inl rfl

/-- Discarding the incumbent at a node does not change what the node does next. -/
theorem dfsNode_prune_shift {G : Graph} {fuel : Nat} {path : Array Nat} {invPath : Array UInt64}
    {p : Part} {st st' : St} (habort : st.abortTo.isSome = false)
    (hprune : pruneNode invPath st = some st') (hnone : st'.best = none) :
    dfsNode G (fuel + 1) path invPath p st = dfsNode G (fuel + 1) path invPath p st' := by
  have habort' : st'.abortTo.isSome = false := by rw [pruneNode_abortTo hprune]; exact habort
  have hprune' : pruneNode invPath st' = some st' := by rw [pruneNode, hnone]
  rcases hc : p.targetCell G.n with _ | c
  · rw [dfsNode_leaf habort hprune hc, dfsNode_leaf habort' hprune' hc]
  · rw [dfsNode_branch habort hprune hc, dfsNode_branch habort' hprune' hc]

/-- The clearing case of monotonicity: if the node throws the incumbent away, the leaf it comes
back with is one from below the node, and every such leaf beats what was thrown away. -/
theorem dfsNode_mono_cleared (n : Nat) (f : Nat → Nat → Bool) (fuel : Nat) (path : Array Nat)
    (invPath : Array UInt64) (p : Part) (st st' : St) (hp : Part.WF n p)
    (hfuel : n + 1 ≤ numCells n p + fuel) (habort : st.abortTo.isSome = false)
    (hprune : pruneNode invPath st = some st') (hnone : st'.best = none) :
    BestMono st (dfsNode (Graph.ofOracle n f) fuel path invPath p st) := by
  have habort' : st'.abortTo.isSome = false := by rw [pruneNode_abortTo hprune]; exact habort
  cases fuel with
  | zero => have := numCells_le (n := n) p; omega
  | succ m =>
    rw [dfsNode_prune_shift habort hprune hnone]
    intro b hb
    have hgood : st'.abortTo.isSome = true → st'.best.isSome = true :=
      fun h => absurd h (by rw [habort']; simp)
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1
      (dfsNode_best n f (m + 1) path invPath p st' hp hfuel hgood)
    refine ⟨l, hl, ?_⟩
    have hr : StP (Reach n f invPath p) (dfsNode (Graph.ofOracle n f) (m + 1) path invPath p st') :=
      dfsNode_reach n f _ (m + 1) path invPath p st' hp (fun _ h => h)
        (by intro l' hl'; rw [hnone] at hl'; exact absurd hl' (by simp))
    exact pruneNode_cleared hprune hnone hb (hr l hl)

/-- **The incumbent never gets worse.** -/
theorem dfsNode_mono (n : Nat) (f : Nat → Nat → Bool) :
    ∀ (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St),
      Part.WF n p → n + 1 ≤ numCells n p + fuel →
        BestMono st (dfsNode (Graph.ofOracle n f) fuel path invPath p st) := by
  refine dfsNode.induct (Graph.ofOracle n f)
    (motive1 := fun fuel path invPath p st =>
      Part.WF n p → n + 1 ≤ numCells n p + fuel →
        BestMono st (dfsNode (Graph.ofOracle n f) fuel path invPath p st))
    (motive2 := fun fuel path invPath p verts processed orb st =>
      Part.WF n p → (∀ v ∈ verts, v < n) →
      (∀ v ∈ verts, numCells n p < numCells n (child (Graph.ofOracle n f) p v).1) →
      n ≤ numCells n p + fuel →
        BestMono st (dfsChildren (Graph.ofOracle n f) fuel path invPath p verts processed orb st))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 =>
    intro path invPath p st _ _
    rw [dfsNode_zero]; exact BestMono.rfl st
  case refine_2 =>
    intro path invPath p st fuel habort _ _
    rw [dfsNode_abort habort]; exact BestMono.rfl st
  case refine_3 =>
    intro path invPath p st fuel habort hprune _ _
    rw [dfsNode_pruned (by simpa using habort) hprune]; exact BestMono.rfl st
  case refine_4 =>
    intro path invPath p st fuel habort st1 hprune htc hp hfuel
    rcases pruneNode_mono' hprune with rfl | ⟨rfl, _⟩
    · rw [dfsNode_leaf (by simpa using habort) hprune htc]
      refine BestMono.trans ?_ (leafUpdate_mono (Graph.ofOracle n f) path invPath p.lab _)
      exact BestMono.of_best_eq rfl
    · exact dfsNode_mono_cleared n f (fuel + 1) path invPath p st _ hp hfuel
        (by simpa using habort) hprune rfl
  case refine_5 =>
    intro path invPath p st fuel habort st1 hprune st2 c htc verts orb ih hp hfuel
    have hc : c < n := targetCell_lt n p c htc
    rcases pruneNode_mono' hprune with rfl | ⟨rfl, _⟩
    · rw [dfsNode_branch (by simpa using habort) hprune htc]
      refine BestMono.trans ?_ (ih hp (fun v hv => mem_extract_lt hp hv)
        (fun v hv => numCells_child hp htc (mem_extract_lt hp hv)
          (mem_extract_cell hp hc (targetCell_cst hp htc) hv)) (by omega))
      exact BestMono.of_best_eq rfl
    · exact dfsNode_mono_cleared n f (fuel + 1) path invPath p st _ hp hfuel
        (by simpa using habort) hprune rfl
  case refine_6 =>
    intro fuel path invPath p processed orb st _ _ _ _
    rw [dfsChildren_nil]; exact BestMono.rfl st
  case refine_7 =>
    intro fuel path invPath p processed orb st v vs habort _ _ _ _
    rw [dfsChildren_abort habort]; exact BestMono.rfl st
  case refine_8 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark ih hp hverts hnc hfuel
    rw [dfsChildren_marked (by simpa using habort) hmark]
    exact ih hp (fun w hw => hverts w (List.mem_cons_of_mem _ hw))
      (fun w hw => hnc w (List.mem_cons_of_mem _ hw)) hfuel
  case refine_9 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 ih1 hp hverts hnc hfuel
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hwf'' : Part.WF n p'' := by
      have h2 : p'' = (child (Graph.ofOracle n f) p v).1 := by rw [hchild]
      rw [h2, child]
      exact refine_wf (individualize_wf' hp (hverts v (by simp))) _ _
    have hnc' : numCells n p < numCells n p'' := by
      have := hnc v (by simp)
      rwa [hchild] at this
    rw [dfsChildren_step_stop (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href habort2]
    exact (ih1 hwf'' (by omega)).trans (BestMono.of_best_eq (unwind_best _ _))
  case refine_10 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 orb2 ih1 _ih1' ih2 hp hverts hnc hfuel
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hwf'' : Part.WF n p'' := by
      have h2 : p'' = (child (Graph.ofOracle n f) p v).1 := by rw [hchild]
      rw [h2, child]
      exact refine_wf (individualize_wf' hp (hverts v (by simp))) _ _
    have hnc' : numCells n p < numCells n p'' := by
      have := hnc v (by simp)
      rwa [hchild] at this
    rw [dfsChildren_step_go (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href
      (by simp only [Bool.not_eq_true] at habort2; exact habort2)]
    refine ((ih1 hwf'' (by omega)).trans
      (BestMono.of_best_eq
        (unwind_best path
          (dfsNode (Graph.ofOracle n f) fuel (path.push v) childInv' p'' st)))).trans ?_
    exact ih2 hp (fun w hw => hverts w (List.mem_cons_of_mem _ hw))
      (fun w hw => hnc w (List.mem_cons_of_mem _ hw)) hfuel

end Canon
end IsoGraph
