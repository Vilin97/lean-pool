/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeNormal

/-!
# Partial closure: gluing a fragment into a test fragment

The accompanying paper's `G_z` (Lemma 3.3(b)): given a
`(u, v)`-fragment `z`
and a test fragment `G` on the interleaved boundary
`(s + u) + (t + v)`, glue each open end of `z` to the matching
`z`-block end of `G`.  The survivors are exactly the `x`-block
ends of `G`, so the result is an `(s + t)`-fragment.  The
absorption theorem `pairClose (tensorFragment x z) G ≃
pairClose x (partialClose z G)` lives in `TensorIdeal.lean`; this
file provides the construction: the gluing pair list, its
well-formedness, the survivor identification, and congruence.
-/

namespace RS

/-- The `z`-gluing pairs: `z`'s high block against the last block
of `G`, then `z`'s low block against the second block of `G`
(top pair first within each block). -/
noncomputable def zClosePairs (s t u v : ℕ) :
    List ((Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ×
      (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))) :=
  (List.finRange v).reverse.map (fun l =>
    (Sum.inl ⟨u + l.val, by have := l.isLt; omega⟩,
     Sum.inr ⟨(s + u) + (t + l.val), by have := l.isLt; omega⟩)) ++
  (List.finRange u).reverse.map (fun j =>
    (Sum.inl ⟨j.val, by have := j.isLt; omega⟩,
     Sum.inr ⟨s + j.val, by have := j.isLt; omega⟩))

/-- Membership in the flattened `z`-gluing pairs: every `z`-label,
and the two `z`-blocks of `G`-labels. -/
theorem mem_zClosePairs_flat (s t u v : ℕ)
    (x : Fin (u + v) ⊕ Fin ((s + u) + (t + v))) :
    x ∈ (zClosePairs s t u v).flatMap (fun p => [p.1, p.2]) ↔
      (∃ a : Fin (u + v), x = Sum.inl a) ∨
      (∃ b : Fin ((s + u) + (t + v)), x = Sum.inr b ∧
        ((s ≤ b.val ∧ b.val < s + u) ∨ (s + u) + t ≤ b.val)) := by
  unfold zClosePairs
  rw [List.flatMap_append, List.flatMap_map, List.flatMap_map,
    List.mem_append]
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_finRange,
    List.mem_cons, List.not_mem_nil, or_false, true_and]
  constructor
  · rintro (⟨l, hl | hl⟩ | ⟨j, hj | hj⟩)
    · exact Or.inl ⟨_, hl⟩
    · exact Or.inr ⟨_, hl, Or.inr (by simp)⟩
    · exact Or.inl ⟨_, hj⟩
    · exact Or.inr ⟨_, hj, Or.inl (by simp)⟩
  · rintro (⟨a, rfl⟩ | ⟨b, rfl, hb | hb⟩)
    · by_cases ha : a.val < u
      · refine Or.inr ⟨⟨a.val, ha⟩, Or.inl ?_⟩
        exact congrArg Sum.inl (Fin.ext rfl)
      · refine Or.inl ⟨⟨a.val - u, by have := a.isLt; omega⟩,
          Or.inl ?_⟩
        exact congrArg Sum.inl (Fin.ext (by simp; omega))
    · refine Or.inr ⟨⟨b.val - s, by omega⟩, Or.inr ?_⟩
      exact congrArg Sum.inr (Fin.ext (by simp; omega))
    · refine Or.inl ⟨⟨b.val - ((s + u) + t),
        by have := b.isLt; omega⟩, Or.inr ?_⟩
      exact congrArg Sum.inr (Fin.ext (by simp; omega))

/-- The `z`-gluing pairs are well-formed. -/
theorem zClosePairs_wf (s t u v : ℕ) :
    Fragment.PairsWF (zClosePairs s t u v) := by
  unfold Fragment.PairsWF zClosePairs
  rw [List.flatMap_append, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun l _ => by simp, ?_⟩
    rw [List.pairwise_reverse]
    refine (List.nodup_finRange v).pairwise_of_forall_ne ?_
    intro k _ m _ hkm x hxm hxk
    simp only [List.mem_cons, List.not_mem_nil, or_false]
      at hxm hxk
    rcases hxm with rfl | rfl <;> rcases hxk with h | h
    · rw [Sum.inl.injEq, Fin.mk.injEq] at h
      exact hkm (Fin.ext (by omega)).symm
    · exact Sum.inl_ne_inr h
    · exact Sum.inr_ne_inl h
    · rw [Sum.inr.injEq, Fin.mk.injEq] at h
      exact hkm (Fin.ext (by omega)).symm
  · rw [List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun j _ => by simp, ?_⟩
    rw [List.pairwise_reverse]
    refine (List.nodup_finRange u).pairwise_of_forall_ne ?_
    intro k _ m _ hkm x hxm hxk
    simp only [List.mem_cons, List.not_mem_nil, or_false]
      at hxm hxk
    rcases hxm with rfl | rfl <;> rcases hxk with h | h
    · rw [Sum.inl.injEq, Fin.mk.injEq] at h
      exact hkm (Fin.ext (by omega)).symm
    · exact Sum.inl_ne_inr h
    · exact Sum.inr_ne_inl h
    · rw [Sum.inr.injEq, Fin.mk.injEq] at h
      exact hkm (Fin.ext (by omega)).symm
  · intro x hxv y hy
    rw [List.flatMap_map] at hxv hy
    simp only [List.mem_flatMap, List.mem_reverse,
      List.mem_finRange, List.mem_cons, List.not_mem_nil,
      or_false, true_and] at hxv hy
    obtain ⟨l, hl⟩ := hxv
    obtain ⟨j, hj⟩ := hy
    have hlv := l.isLt
    have hju := j.isLt
    rcases hl with rfl | rfl <;> rcases hj with rfl | rfl
    · intro h
      rw [Sum.inl.injEq, Fin.mk.injEq] at h
      omega
    · exact Sum.inl_ne_inr
    · exact Sum.inr_ne_inl
    · intro h
      rw [Sum.inr.injEq, Fin.mk.injEq] at h
      omega

/-- The survivor predicate of the `z`-gluing: no `z`-label
survives, and a `G`-label survives iff it lies in one of the two
`x`-blocks. -/
def pcSurvPred (s t u v : ℕ) :
    Fin (u + v) ⊕ Fin ((s + u) + (t + v)) → Prop :=
  Sum.elim (fun _ => False)
    (fun b => b.val < s ∨ ((s + u) ≤ b.val ∧ b.val < (s + u) + t))

/-- Avoiding the `z`-gluing pairs is the survivor predicate. -/
theorem pcSurv_iff (s t u v : ℕ)
    (x : Fin (u + v) ⊕ Fin ((s + u) + (t + v))) :
    x ∉ (zClosePairs s t u v).flatMap (fun p => [p.1, p.2]) ↔
      pcSurvPred s t u v x := by
  rw [mem_zClosePairs_flat]
  rcases x with a | b
  · simp [pcSurvPred]
  · simp only [pcSurvPred, Sum.elim_inr, reduceCtorEq,
      exists_false, false_or, Sum.inr.injEq, exists_eq_left']
    have := b.isLt
    omega

/-- The surviving `G`-labels of the `z`-gluing, identified with
the `(s + t)`-boundary: first `x`-block by value, second by
offset. -/
def pcSurvValEquiv (s t u v : ℕ) :
    {x : Fin (u + v) ⊕ Fin ((s + u) + (t + v)) //
      pcSurvPred s t u v x} ≃ Fin (s + t) where
  toFun x :=
    match x with
    | ⟨Sum.inl _, h⟩ => absurd h not_false
    | ⟨Sum.inr b, h⟩ =>
        if hb : b.val < s then ⟨b.val, by omega⟩
        else ⟨s + (b.val - (s + u)), by
          rcases h with h | h
          · omega
          · omega⟩
  invFun k :=
    if hk : k.val < s then
      ⟨Sum.inr ⟨k.val, by omega⟩, Or.inl hk⟩
    else
      ⟨Sum.inr ⟨(s + u) + (k.val - s), by have := k.isLt; omega⟩,
       Or.inr ⟨by show (s + u) ≤ (s + u) + (k.val - s); omega,
         by show (s + u) + (k.val - s) < (s + u) + t
            have := k.isLt; omega⟩⟩
  left_inv x := by
    obtain ⟨x, h⟩ := x
    rcases x with a | b
    · exact absurd h not_false
    · by_cases hb : b.val < s
      · simp only [dif_pos hb]
      · have hb2 : (s + u) ≤ b.val ∧ b.val < (s + u) + t := by
          rcases h with h | h
          · omega
          · exact h
        simp only [dif_neg hb,
          dif_neg (show ¬ s + (b.val - (s + u)) < s by omega)]
        exact Subtype.ext (congrArg Sum.inr (Fin.ext (by
          show (s + u) + (s + (b.val - (s + u)) - s) = b.val
          omega)))
  right_inv k := by
    by_cases hk : k.val < s
    · simp only [dif_pos hk]
    · simp only [dif_neg hk,
        dif_neg (show ¬ (s + u) + (k.val - s) < s by omega)]
      exact Fin.ext (by
        show s + ((s + u) + (k.val - s) - (s + u)) = k.val
        omega)

/-- The survivor identification of the `z`-gluing. -/
noncomputable def pcSurvEquiv (s t u v : ℕ) :
    Fragment.FoldSurviving (Fin (u + v) ⊕ Fin ((s + u) + (t + v)))
      (zClosePairs s t u v) ≃ Fin (s + t) :=
  (_root_.Equiv.subtypeEquivRight (fun x =>
      (forall_ne_iff_not_mem_flat _ x).trans
        (pcSurv_iff s t u v x))).trans
    (pcSurvValEquiv s t u v)

/-- **Partial closure**: glue every open end of `z` into the
matching `z`-block end of the test fragment `G`; the surviving
`x`-block ends form the `(s + t)`-boundary. -/
noncomputable def partialClose {s t u v : ℕ}
    (z : Fragment (Fin (u + v)))
    (G : Fragment (Fin ((s + u) + (t + v)))) :
    Fragment (Fin (s + t)) :=
  (Fragment.glueList (z.disjUnion G) (zClosePairs s t u v)
    (zClosePairs_wf s t u v)).relabel (pcSurvEquiv s t u v)

end RS
