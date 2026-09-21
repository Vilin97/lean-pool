/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.CompositionEquiv

/-!
# The identity law: stage equivalences

Composing with a strand bundle is the identity up to fragment
equivalence.  The proof runs by descending induction through
`glueInterface` with the invariant that the stage-`t'` fragment is
equivalent to `(strandBundle t').disjUnion F` relabelled along a
stage equivalence relocating the not-yet-glued interface labels of
`F` into the left label block.

The stage equivalence is assembled from block decompositions: the
five blocks are the strand-in labels `A`, the strand-out labels
`A'`, the already-glued interface labels `B`, the not-yet-glued
interface labels `C`, and the outer labels `D`; the shuffle
`(A ⊕ A') ⊕ ((B ⊕ C) ⊕ D) ≃ ((A ⊕ C) ⊕ A') ⊕ (B ⊕ D)` is a plain
constructor permutation with definitional inverses.
-/

namespace RS

/-- The five-block shuffle underlying the stage equivalence. -/
def stageShuffle (A A' B C D : Type) :
    (A ⊕ A') ⊕ ((B ⊕ C) ⊕ D) ≃ ((A ⊕ C) ⊕ A') ⊕ (B ⊕ D) where
  toFun x := match x with
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl (Sum.inl a))
    | Sum.inl (Sum.inr a') => Sum.inl (Sum.inr a')
    | Sum.inr (Sum.inl (Sum.inl b)) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inl (Sum.inr c)) => Sum.inl (Sum.inl (Sum.inr c))
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  invFun y := match y with
    | Sum.inl (Sum.inl (Sum.inl a)) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inl (Sum.inr c)) => Sum.inr (Sum.inl (Sum.inr c))
    | Sum.inl (Sum.inr a') => Sum.inl (Sum.inr a')
    | Sum.inr (Sum.inl b) => Sum.inr (Sum.inl (Sum.inl b))
    | Sum.inr (Sum.inr d) => Sum.inr (Sum.inr d)
  left_inv x := by
    rcases x with (a | a') | ((b | c) | d) <;> rfl
  right_inv y := by
    rcases y with ((a | c) | a') | (b | d) <;> rfl

/-- The stage relabelling for the identity law: on the left, the
`t'` strand-in labels, then the `t - t'` not-yet-glued interface
labels of `F`, then the `t'` strand-out labels; on the right, the
`t'` already-glued interface labels, then the `u` outer labels. -/
def stageEquiv (t t' u : ℕ) (ht : t' ≤ t) :
    (Fin (t' + t') ⊕ Fin (t + u)) ≃ (Fin (t + t') ⊕ Fin (t' + u)) :=
  (Equiv.sumCongr finSumFinEquiv.symm
      (((finCongr (by omega : t + u = (t' + (t - t')) + u)).trans
          finSumFinEquiv.symm).trans
        (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl (Fin u))))).trans
    ((stageShuffle (Fin t') (Fin t') (Fin t') (Fin (t - t'))
        (Fin u)).trans
      (Equiv.sumCongr
        ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin t'))).trans
          ((Equiv.sumCongr (finCongr (by omega : t' + (t - t') = t))
              (Equiv.refl (Fin t'))).trans finSumFinEquiv))
        finSumFinEquiv))

/-! ### Label evaluations -/

/-- Evaluation of the stage equivalence on a right label: an
already-glued interface label stays right, a not-yet-glued interface
label relocates to the left block, and an outer label stays right
with an offset. -/
theorem stageEquiv_inr (t t' u : ℕ) (ht : t' ≤ t) (ℓ : Fin (t + u)) :
    stageEquiv t t' u ht (Sum.inr ℓ) =
      if h₁ : ℓ.val < t' then Sum.inr ⟨ℓ.val, by omega⟩
      else if h₂ : ℓ.val < t then Sum.inl ⟨ℓ.val, by omega⟩
      else Sum.inr ⟨t' + (ℓ.val - t), by omega⟩ := by
  by_cases h₁ : ℓ.val < t'
  · -- ═══════ CASE: already-glued interface label ═══════
    rw [dif_pos h₁]
    simp only [stageEquiv, stageShuffle, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inr, finCongr_apply]
    rw [show finSumFinEquiv.symm
        (Fin.cast (by omega : t + u = (t' + (t - t')) + u) ℓ) =
        Sum.inl ⟨ℓ.val, by omega⟩ from by
      rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp)]
    simp only [Sum.map_inl]
    rw [show (finSumFinEquiv.symm ⟨ℓ.val, by omega⟩ :
        Fin t' ⊕ Fin (t - t')) = Sum.inl ⟨ℓ.val, h₁⟩ from by
      rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp)]
    simp only [Equiv.coe_fn_mk, Sum.map_inr]
    exact congrArg Sum.inr (Fin.ext (by simp [finSumFinEquiv_apply_left]))
  · rw [dif_neg h₁]
    by_cases h₂ : ℓ.val < t
    · -- ═══════ CASE: not-yet-glued interface label ═══════
      rw [dif_pos h₂]
      simp only [stageEquiv, stageShuffle, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inr, finCongr_apply]
      rw [show finSumFinEquiv.symm
        (Fin.cast (by omega : t + u = (t' + (t - t')) + u) ℓ) =
          Sum.inl ⟨ℓ.val, by omega⟩ from by
        rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp)]
      simp only [Sum.map_inl]
      rw [show (finSumFinEquiv.symm ⟨ℓ.val, by omega⟩ :
          Fin t' ⊕ Fin (t - t')) = Sum.inr ⟨ℓ.val - t', by omega⟩ from by
        rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp; omega)]
      simp only [Equiv.coe_fn_mk, Sum.map_inl]
      exact congrArg Sum.inl (Fin.ext (by
        simp [finSumFinEquiv_apply_right, finCongr_apply]; omega))
    · -- ═══════ CASE: outer label ═══════
      rw [dif_neg h₂]
      simp only [stageEquiv, stageShuffle, Equiv.trans_apply,
        Equiv.sumCongr_apply, Sum.map_inr, finCongr_apply]
      rw [show finSumFinEquiv.symm
        (Fin.cast (by omega : t + u = (t' + (t - t')) + u) ℓ) =
          Sum.inr ⟨ℓ.val - (t' + (t - t')), by omega⟩ from by
        rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp; omega)]
      simp only [Equiv.coe_fn_mk, Sum.map_inr]
      exact congrArg Sum.inr
        (Fin.ext (by simp [finSumFinEquiv_apply_right]; omega))

/-- Evaluation of the stage equivalence on a left (strand) label:
a strand-in label stays left with its index, a strand-out label
goes left with an offset past the interface block. -/
theorem stageEquiv_inl (t t' u : ℕ) (ht : t' ≤ t) (a : Fin (t' + t')) :
    stageEquiv t t' u ht (Sum.inl a) =
      if h : a.val < t' then Sum.inl ⟨a.val, by omega⟩
      else Sum.inl ⟨t + (a.val - t'), by omega⟩ := by
  by_cases h : a.val < t'
  · -- ═══════ CASE: strand-in label ═══════
    rw [dif_pos h]
    simp only [stageEquiv, stageShuffle, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inl]
    rw [show (finSumFinEquiv.symm a : Fin t' ⊕ Fin t') =
        Sum.inl ⟨a.val, h⟩ from by
      rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp)]
    simp only [Equiv.coe_fn_mk, Sum.map_inl]
    exact congrArg Sum.inl (Fin.ext (by
      simp [finSumFinEquiv_apply_left, finCongr_apply]))
  · -- ═══════ CASE: strand-out label ═══════
    rw [dif_neg h]
    simp only [stageEquiv, stageShuffle, Equiv.trans_apply,
      Equiv.sumCongr_apply, Sum.map_inl]
    rw [show (finSumFinEquiv.symm a : Fin t' ⊕ Fin t') =
        Sum.inr ⟨a.val - t', by omega⟩ from by
      rw [Equiv.symm_apply_eq]; exact Fin.ext (by simp; omega)]
    simp only [Equiv.coe_fn_mk]
    exact congrArg Sum.inl (Fin.ext (by simp [finSumFinEquiv_apply_right]))

/-! ### The base case -/

/-- Evaluation of the stage-zero equivalence on a right label: an
interface label relocates to the left block, an outer label stays
right. -/
theorem stageEquiv_zero_inr (t u : ℕ) (ℓ : Fin (t + u)) :
    stageEquiv t 0 u (Nat.zero_le t) (Sum.inr ℓ) =
      if h : ℓ.val < t then Sum.inl ⟨ℓ.val, by omega⟩
      else Sum.inr ⟨ℓ.val - t, by omega⟩ := by
  rw [stageEquiv_inr]
  simp only [Nat.not_lt_zero, dite_false]
  split
  · exact congrArg Sum.inl (Fin.ext rfl)
  · exact congrArg Sum.inr (Fin.ext (by simp))

/-- The empty bundle has no flags. -/
instance strandBundleZero_flag_isEmpty : IsEmpty (strandBundle 0).Flag :=
  ⟨fun ⟨k, _⟩ => k.elim0⟩

/-- Nor any vertices — it is the empty fragment. -/
instance strandBundleZero_vertex_isEmpty : IsEmpty (strandBundle 0).Vertex :=
  ⟨fun x => x.elim⟩

/-- The base case of the identity law: after zero interface gluings,
the triply-relabelled strand-0/F union is equivalent to F. -/
noncomputable def stageZeroEquiv (t u : ℕ) (F : Fragment (Fin (t + u))) :
    ((glueInterface t 0 u (((strandBundle 0).disjUnion F).relabel
      (stageEquiv t 0 u (Nat.zero_le t)))).relabel finSumFinEquiv).Equiv F where
  flagEquiv := Equiv.emptySum _ _
  vertexEquiv := Equiv.emptySum _ _
  attach_comm := fun f => by
    change F.attach ((Equiv.emptySum _ _) f) =
      (((glueInterface t 0 u (((strandBundle 0).disjUnion F).relabel
        (stageEquiv t 0 u (Nat.zero_le t)))).relabel finSumFinEquiv).attach
          f).map
        (Equiv.emptySum _ _) id
    cases f with
    | inl x => exact (IsEmpty.false x).elim
    | inr g =>
      simp only [Equiv.emptySum_apply_inr]
      show F.attach g =
        (((((F.attach g).map Sum.inr Sum.inr).map id
          (stageEquiv t 0 u (Nat.zero_le t))).map id
          (Equiv.sumCongr (finCongr (by omega : t + 0 = t))
            (finCongr (by omega : 0 + u = u)))).map id finSumFinEquiv).map
          (Equiv.emptySum _ _) id
      rcases ha : F.attach g with v | ℓ
      · simp
      · simp only [Sum.map_inr]
        congr 1
        rw [stageEquiv_zero_inr]
        split
        · rename_i h
          simp [finSumFinEquiv_apply_left]
        · rename_i h
          simp [finSumFinEquiv_apply_right, finCongr_apply, Fin.ext_iff]
          omega
  pairing_comm := fun f => by
    cases f with
    | inl x => exact (IsEmpty.false x).elim
    | inr g => rfl
  circles_eq := Nat.zero_add _

/-! ### The descent step -/

/-- The boundary flag at the left interface label in the relabelled
disjoint union: it is the outgoing end of strand `t'`. -/
theorem stageStep_leftBoundary (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :
    (((strandBundle (t' + 1)).disjUnion F).relabel
      (stageEquiv t (t' + 1) u ht)).boundaryFlag
      (Sum.inl ⟨t + t', by omega⟩) =
    Sum.inl (⟨t', by omega⟩, true) := by
  show ((strandBundle (t' + 1)).disjUnion F).boundaryFlag
    ((stageEquiv t (t' + 1) u ht).symm (Sum.inl ⟨t + t', by omega⟩)) =
    Sum.inl (⟨t', by omega⟩, true)
  have hsymm : (stageEquiv t (t' + 1) u ht).symm (Sum.inl ⟨t + t', by omega⟩) =
      Sum.inl ⟨(t' + 1) + t', by omega⟩ := by
    rw [Equiv.symm_apply_eq, stageEquiv_inl]
    split
    · next h =>
        exact absurd h
          (show ¬ ((t' + 1) + t' : ℕ) < t' + 1 from by omega)
    · exact congrArg Sum.inl
        (Fin.ext (show t + t' = t + ((t' + 1) + t' - (t' + 1)) from by omega))
  rw [hsymm]
  change Sum.inl
    ((strandBundle (t' + 1)).boundaryFlag ⟨(t' + 1) + t', by omega⟩) =
    Sum.inl (⟨t', by omega⟩, true)
  rw [strandBundle_boundaryFlag_high (t' + 1) ⟨(t' + 1) + t', by omega⟩
    (show ¬ ((t' + 1) + t' : ℕ) < t' + 1 from by omega)]
  exact congrArg Sum.inl
    (Prod.ext (Fin.ext (show (t' + 1) + t' - (t' + 1) = t' from by omega)) rfl)

/-- The boundary flag at the right interface label in the relabelled
disjoint union: it is F's boundary flag at label `t'`. -/
theorem stageStep_rightBoundary (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :
    (((strandBundle (t' + 1)).disjUnion F).relabel
      (stageEquiv t (t' + 1) u ht)).boundaryFlag
      (Sum.inr ⟨t', by omega⟩) =
    Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := by
  show ((strandBundle (t' + 1)).disjUnion F).boundaryFlag
    ((stageEquiv t (t' + 1) u ht).symm (Sum.inr ⟨t', by omega⟩)) =
    Sum.inr (F.boundaryFlag ⟨t', by omega⟩)
  have hsymm : (stageEquiv t (t' + 1) u ht).symm (Sum.inr ⟨t', by omega⟩) =
      Sum.inr ⟨t', by omega⟩ := by
    rw [Equiv.symm_apply_eq, stageEquiv_inr]
    split
    · exact congrArg Sum.inr (Fin.ext rfl)
    · next h => exact absurd (show (t' : ℕ) < t' + 1 from by omega) h
  rw [hsymm]
  rfl

/-- The glue in the descent step is always the open case. -/
theorem stageStep_hopen (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :
    (((strandBundle (t' + 1)).disjUnion F).relabel
      (stageEquiv t (t' + 1) u ht)).pairing
      ((((strandBundle (t' + 1)).disjUnion F).relabel
        (stageEquiv t (t' + 1) u ht)).boundaryFlag
        (Sum.inl ⟨t + t', by omega⟩)) ≠
    (((strandBundle (t' + 1)).disjUnion F).relabel
      (stageEquiv t (t' + 1) u ht)).boundaryFlag
      (Sum.inr ⟨t', by omega⟩) := by
  rw [stageStep_leftBoundary, stageStep_rightBoundary]
  simp [Fragment.relabel, Fragment.disjUnion, strandBundle]

/-- The pairing partner of the left boundary flag in the relabelled
fragment: it is (t', false), the incoming end of strand t'. -/
theorem stageStep_leftPairing (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :
    (((strandBundle (t' + 1)).disjUnion F).relabel
      (stageEquiv t (t' + 1) u ht)).pairing
      (Sum.inl (⟨t', by omega⟩, true)) =
    Sum.inl (⟨t', by omega⟩, false) := by
  rfl

/-- The flag equivalence for the descent step: surviving flags of the
open glue at stage `t' + 1` correspond to flags of the stage-`t'`
disjoint union `(strandBundle t').disjUnion F`. -/
noncomputable def stageStepFlagEquiv (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :
    Fragment.SurvivingFlag
      (((strandBundle (t' + 1)).disjUnion F).relabel (stageEquiv t (t' + 1) u
        ht))
      (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩) ≃
    (Fin t' × Bool) ⊕ F.Flag where
  toFun x :=
    match x.val with
    | Sum.inl (⟨k, _⟩, b) =>
      if hlt : k < t' then Sum.inl (⟨k, hlt⟩, b)
      else Sum.inr (F.boundaryFlag ⟨t', by omega⟩)
    | Sum.inr g => Sum.inr g
  invFun y :=
    match y with
    | Sum.inl (⟨k, hk⟩, b) =>
      ⟨Sum.inl (⟨k, by omega⟩, b), by
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [stageStep_leftBoundary] at h
          have hkeq : k = t' := congrArg Fin.val
            (congrArg Prod.fst (Sum.inl.inj h))
          omega
        · rw [stageStep_rightBoundary] at h; simp at h⟩
    | Sum.inr g =>
      if hg : g = F.boundaryFlag ⟨t', by omega⟩ then
        ⟨Sum.inl (⟨t', by omega⟩, false), by
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [stageStep_leftBoundary] at h
            have hbeq : (false : Bool) = true :=
              congrArg Prod.snd (Sum.inl.inj h)
            exact absurd hbeq (by decide)
          · rw [stageStep_rightBoundary] at h; simp at h⟩
      else
        ⟨Sum.inr g, by
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [stageStep_leftBoundary] at h; simp at h
          · rw [stageStep_rightBoundary] at h
            exact hg (Sum.inr.inj h)⟩
  left_inv x := by
    obtain ⟨f, hne⟩ := x
    rcases f with ⟨⟨k, hk⟩, b⟩ | g
    · -- f = Sum.inl (⟨k, hk⟩, b)
      dsimp only
      by_cases hlt : k < t'
      · simp only [dif_pos hlt]
      · have hk_eq : k = t' := by omega
        simp only [dif_neg hlt]
        have hb : b = false := by
          by_contra hbt
          have hbtrue : b = true := by cases b <;> simp_all
          exact hne.1 (by
            rw [stageStep_leftBoundary]
            exact hk_eq ▸ hbtrue ▸ congrArg Sum.inl (Prod.ext (Fin.ext rfl)
              rfl))
        exact Subtype.ext (hk_eq ▸ hb ▸ congrArg Sum.inl (Prod.ext (Fin.ext rfl)
          rfl))
    · -- f = Sum.inr g
      dsimp only
      have hg : g ≠ F.boundaryFlag ⟨t', by omega⟩ := by
        intro heq
        exact hne.2 (by
          rw [stageStep_rightBoundary]
          exact congrArg Sum.inr heq)
      simp only [dif_neg hg]
  right_inv y := by
    match y with
    | Sum.inl (⟨k, hk⟩, b) =>
      dsimp only
      simp only [dif_pos hk]
    | Sum.inr g =>
      dsimp only
      by_cases hg : g = F.boundaryFlag ⟨t', by omega⟩
      · simp only [dif_pos hg, dif_neg (show ¬ (t' : ℕ) < t' from Nat.lt_irrefl
        t')]
        exact congrArg Sum.inr hg.symm
      · simp only [dif_neg hg]

/-! ### interfaceStepEquiv evaluation lemmas -/

private theorem interfaceStepEquiv_symm_inl (s t u : ℕ) (j : Fin (s + t)) :
    ((interfaceStepEquiv s t u).symm (Sum.inl j)).val =
    Sum.inl ⟨j.val, by omega⟩ := by
  simp only [interfaceStepEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Sum.map_inl]
  have key : ((finRemoveEquiv (⟨s + t, Nat.lt_succ_self _⟩ : Fin (s + t +
    1))).symm j).val =
      ⟨j.val, by omega⟩ := by
    simp only [finRemoveEquiv, Equiv.coe_fn_symm_mk]
    rw [finSuccEquiv'_symm_some_below]
    · rfl
    · exact Fin.mk_lt_mk.mpr j.isLt
  change ((sumRemoveSplitEquiv _ _).symm (Sum.inl _)).val = _
  simp only [sumRemoveSplitEquiv]
  exact congrArg Sum.inl key

private theorem interfaceStepEquiv_symm_inr_below (s t u : ℕ) (j : Fin (t + u))
    (hj : j.val < t) :
    ((interfaceStepEquiv s t u).symm (Sum.inr j)).val =
    Sum.inr ⟨j.val, by omega⟩ := by
  simp only [interfaceStepEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Sum.map_inr]
  change ((sumRemoveSplitEquiv _ _).symm (Sum.inr _)).val = _
  simp only [sumRemoveSplitEquiv]
  apply congrArg Sum.inr; ext
  simp only [rightRemoveEquiv, Equiv.symm_trans_apply,
    Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply,
    finCongr_symm, finCongr_apply]
  simp only [finRemoveEquiv, Equiv.coe_fn_symm_mk]
  rw [finSuccEquiv'_symm_some_below]
  · simp [Fin.castSucc]
  · simp [Fin.lt_def, Fin.castSucc]; exact hj

private theorem interfaceStepEquiv_symm_inr_above (s t u : ℕ) (j : Fin (t + u))
    (hj : ¬ j.val < t) :
    ((interfaceStepEquiv s t u).symm (Sum.inr j)).val =
    Sum.inr ⟨j.val + 1, by omega⟩ := by
  simp only [interfaceStepEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Sum.map_inr]
  change ((sumRemoveSplitEquiv _ _).symm (Sum.inr _)).val = _
  simp only [sumRemoveSplitEquiv]
  apply congrArg Sum.inr; ext
  simp only [rightRemoveEquiv, Equiv.symm_trans_apply,
    Equiv.subtypeEquiv_symm, Equiv.subtypeEquiv_apply,
    finCongr_symm, finCongr_apply]
  simp only [finRemoveEquiv, Equiv.coe_fn_symm_mk]
  rw [finSuccEquiv'_symm_some_above]
  · simp [Fin.succ]
  · simp [Fin.le_iff_val_le_val, Fin.castSucc]; omega

/-- Evaluation of `interfaceStepEquiv` on a left surviving label. -/
theorem interfaceStepEquiv_eval_inl (s t u : ℕ) (j : ℕ) (hj : j < s + t) :
    (interfaceStepEquiv s t u)
      ⟨Sum.inl ⟨j, by omega⟩,
       fun h => by simp [Fin.ext_iff] at h; omega,
       fun h => by simp at h⟩ =
    Sum.inl ⟨j, hj⟩ := by
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  exact Subtype.ext (interfaceStepEquiv_symm_inl s t u ⟨j, hj⟩).symm

/-- Evaluation of `interfaceStepEquiv` on a right surviving label
below the cut. -/
theorem interfaceStepEquiv_eval_inr_below (s t u : ℕ) (j : ℕ) (hj : j < t) :
    (interfaceStepEquiv s t u)
      ⟨Sum.inr ⟨j, by omega⟩,
       fun h => by simp at h,
       fun h => by simp [Fin.ext_iff] at h; omega⟩ =
    Sum.inr ⟨j, by omega⟩ := by
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  exact Subtype.ext
    (interfaceStepEquiv_symm_inr_below s t u ⟨j, by omega⟩ hj).symm

/-- Evaluation of `interfaceStepEquiv` on a right surviving label
above the cut. -/
theorem interfaceStepEquiv_eval_inr_above (s t u : ℕ) (j : ℕ)
    (hj : t < j) (hj' : j < t + 1 + u) :
    (interfaceStepEquiv s t u)
      ⟨Sum.inr ⟨j, hj'⟩,
       fun h => by simp at h,
       fun h => by simp [Fin.ext_iff] at h; omega⟩ =
    Sum.inr ⟨j - 1, by omega⟩ := by
  have key : (interfaceStepEquiv s t u).symm (Sum.inr ⟨j - 1, by omega⟩) =
      ⟨Sum.inr ⟨j, hj'⟩,
       fun h => by simp at h,
       fun h => by simp [Fin.ext_iff] at h; omega⟩ := by
    apply Subtype.ext
    rw [interfaceStepEquiv_symm_inr_above s t u ⟨j - 1, by omega⟩
      (show ¬ (j - 1 : ℕ) < t from by omega)]
    exact congrArg Sum.inr (Fin.ext (show j - 1 + 1 = j from by omega))
  exact (Equiv.apply_eq_iff_eq_symm_apply _).mpr key.symm

/-! ### The stage step equivalence -/

private abbrev baseFragment (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :=
  ((strandBundle (t' + 1)).disjUnion F).relabel (stageEquiv t (t' + 1) u ht)

private abbrev targetFragment (t t' u : ℕ) (ht' : t' ≤ t)
    (F : Fragment (Fin (t + u))) :=
  ((strandBundle t').disjUnion F).relabel (stageEquiv t t' u ht')

private noncomputable abbrev sourceFragment (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :=
  ((baseFragment t t' u ht F).gluePairOpen
    (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
    (by simp) (stageStep_hopen t t' u ht F)).relabel (interfaceStepEquiv t t' u)

-- Raised budget: the four equivalence fields are checked against
-- the glued fragment at once, each on both label halves.
/-- The descent step: after one open glue (at the `t'`-th interface
pair), the resulting fragment is equivalent to the stage-`t'`
disjoint union relabelled by the stage-`t'` equivalence. -/
private noncomputable def stageStepEquiv (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :
    (sourceFragment t t' u ht F).Equiv (targetFragment t t' u (by omega) F)
      where
  flagEquiv := stageStepFlagEquiv t t' u ht F
  vertexEquiv := Equiv.refl _
  circles_eq := rfl
  attach_comm := fun f => by
    obtain ⟨fval, hne⟩ := f
    rcases fval with ⟨⟨k, hk⟩, b⟩ | g
    · -- ═══════ CASE: strand flag (⟨k, hk⟩, b) ═══════
      by_cases hlt : k < t'
      · -- Case 1: k < t'
        have hflag : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, b),
          hne⟩ =
            Sum.inl (⟨k, hlt⟩, b) := by
          have key : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, b),
            hne⟩ =
            if hlt' : k < t' then Sum.inl (⟨k, hlt'⟩, b)
            else Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := rfl
          rw [key, dif_pos hlt]
        set common : (targetFragment t t' u (by omega) F).Vertex ⊕
            (Fin (t + t') ⊕ Fin (t' + u)) :=
          Sum.inr (Sum.inl ⟨if b then t + k else k, by split <;> omega⟩)
        have hLHS : (targetFragment t t' u (by omega) F).attach
          (Sum.inl (⟨k, hlt⟩, b)) =
            common := by
          change (((strandBundle t').disjUnion F).attach (Sum.inl (⟨k, hlt⟩,
            b))).map id
            (stageEquiv t t' u _) = _
          change (((strandBundle t').attach (⟨k, hlt⟩, b)).map Sum.inl
            Sum.inl).map id
            (stageEquiv t t' u _) = _
          simp only [strandBundle, Sum.map, Sum.elim, Function.comp]
          apply congrArg Sum.inr; cases b
          · simp only [ite_false, Bool.false_eq_true]
            rw [stageEquiv_inl t t' u (by omega) ⟨k, by omega⟩, dif_pos hlt]
          · simp only [ite_true]
            rw [stageEquiv_inl t t' u (by omega) ⟨t' + k, by omega⟩,
                dif_neg (show ¬ (t' + k : ℕ) < t' from by omega)]
            exact congrArg Sum.inl (Fin.ext (by simp))
        have hRHS : (sourceFragment t t' u ht F).attach ⟨Sum.inl (⟨k, hk⟩, b),
          hne⟩ =
            common := by
          change ((Fragment.glueAttach (baseFragment t t' u ht F)
              (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
              ⟨Sum.inl (⟨k, hk⟩, b), hne⟩).map id (interfaceStepEquiv t t' u)) =
                _
          have hba : (baseFragment t t' u ht F).attach (Sum.inl (⟨k, hk⟩, b)) =
              Sum.inr (Sum.inl ⟨if b then t + k else k, by split <;> omega⟩) :=
                by
            change (((strandBundle (t' + 1)).disjUnion F).attach
              (Sum.inl (⟨k, hk⟩, b))).map id (stageEquiv t (t' + 1) u ht) = _
            change (((strandBundle (t' + 1)).attach (⟨k, hk⟩, b)).map Sum.inl
              Sum.inl).map id
              (stageEquiv t (t' + 1) u ht) = _
            simp only [strandBundle, Sum.map, Sum.elim, Function.comp]
            apply congrArg Sum.inr; cases b
            · simp only [ite_false, Bool.false_eq_true]
              rw [stageEquiv_inl t (t' + 1) u ht ⟨k, by omega⟩,
                  dif_pos (show (k : ℕ) < t' + 1 from by omega)]
            · simp only [ite_true]
              rw [stageEquiv_inl t (t' + 1) u ht ⟨(t' + 1) + k, by omega⟩,
                  dif_neg (show ¬ ((t' + 1) + k : ℕ) < t' + 1 from by omega)]
              exact congrArg Sum.inl (Fin.ext (by simp))
          refine Fragment.glueAttach_cases _ (fun v hv => ?_)
            (fun ℓ hℓ => ?_)
          · exact absurd (hv.symm.trans hba) (nomatch ·)
          · obtain ⟨ℓ, _hs₁, _hs₂⟩ := ℓ
            simp only [Sum.map_inr]
            have hℓ_eq : ℓ =
                Sum.inl ⟨if b then t + k else k, by split <;> omega⟩ :=
              Sum.inr.inj (hℓ.symm.trans hba)
            subst hℓ_eq; refine congrArg Sum.inr ?_
            cases b
            · exact interfaceStepEquiv_eval_inl t t' u k (by omega)
            · exact interfaceStepEquiv_eval_inl t t' u (t + k) (by omega)
        exact (hflag ▸ hLHS).trans
          (by rw [hRHS]; rfl : ((sourceFragment t t' u ht F).attach
            ⟨Sum.inl (⟨k, hk⟩, b), hne⟩).map (Equiv.refl _) id = common).symm
      · -- Case 2: k ≥ t' (must be k = t', b = false)
        have hk_eq : k = t' := by omega
        have hb : b = false := by
          by_contra hbt
          have hbtrue : b = true := by cases b <;> simp_all
          exact hne.1 (by
            rw [stageStep_leftBoundary]
            exact congrArg Sum.inl (Prod.ext (Fin.ext hk_eq) hbtrue))
        have hflag : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, b),
          hne⟩ =
            Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := by
          have key : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, b),
            hne⟩ =
            if hlt' : k < t' then Sum.inl (⟨k, hlt'⟩, b)
            else Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := rfl
          rw [key, dif_neg hlt]
        set common : (targetFragment t t' u (by omega) F).Vertex ⊕
            (Fin (t + t') ⊕ Fin (t' + u)) := Sum.inr (Sum.inl ⟨t', by omega⟩)
        have hLHS : (targetFragment t t' u (by omega) F).attach
            (Sum.inr (F.boundaryFlag ⟨t', by omega⟩)) = common := by
          change (((strandBundle t').disjUnion F).attach
            (Sum.inr (F.boundaryFlag ⟨t', by omega⟩))).map id (stageEquiv t t' u
              _) = _
          change
            ((F.attach (F.boundaryFlag ⟨t', by omega⟩)).map Sum.inr Sum.inr).map
            id
            (stageEquiv t t' u _) = _
          rw [F.attach_boundaryFlag]; simp only [Sum.map_inr]; refine congrArg
            Sum.inr ?_
          rw [stageEquiv_inr t t' u (by omega) ⟨t', by omega⟩,
              dif_neg (show ¬ (t' : ℕ) < t' from Nat.lt_irrefl t'),
              dif_pos (show (t' : ℕ) < t from by omega)]
        have hRHS : (sourceFragment t t' u ht F).attach
            ⟨Sum.inl (⟨k, hk⟩, b), hne⟩ = common := by
          change ((Fragment.glueAttach (baseFragment t t' u ht F)
              (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
              ⟨Sum.inl (⟨k, hk⟩, b), hne⟩).map id (interfaceStepEquiv t t' u)) =
                _
          have hba : (baseFragment t t' u ht F).attach (Sum.inl (⟨k, hk⟩, b)) =
              Sum.inr (Sum.inl ⟨t', by omega⟩) := by
            change (((strandBundle (t' + 1)).disjUnion F).attach
              (Sum.inl (⟨k, hk⟩, b))).map id (stageEquiv t (t' + 1) u ht) = _
            change (((strandBundle (t' + 1)).attach (⟨k, hk⟩, b)).map Sum.inl
              Sum.inl).map id
              (stageEquiv t (t' + 1) u ht) = _
            simp only [strandBundle, Sum.map, Sum.elim, Function.comp]
            refine congrArg Sum.inr ?_
            rw [show (if (b : Bool) = true then
                  (⟨(t' + 1) + k, by omega⟩ : Fin ((t' + 1) + (t' + 1)))
                else ⟨k, by omega⟩) =
                (⟨k, by omega⟩ : Fin ((t' + 1) + (t' + 1))) from
                  by rw [hb]; rfl]
            rw [stageEquiv_inl t (t' + 1) u ht ⟨k, by omega⟩,
                dif_pos (show (k : ℕ) < t' + 1 from by omega)]
            exact congrArg Sum.inl (Fin.ext (by omega))
          refine Fragment.glueAttach_cases _ (fun v hv => ?_)
            (fun ℓ hℓ => ?_)
          · exact absurd (hv.symm.trans hba) (nomatch ·)
          · obtain ⟨ℓ, _hs₁, _hs₂⟩ := ℓ
            simp only [Sum.map_inr]
            have hℓ_eq : ℓ = Sum.inl ⟨t', by omega⟩ := Sum.inr.inj
              (hℓ.symm.trans hba)
            subst hℓ_eq; refine congrArg Sum.inr ?_
            exact interfaceStepEquiv_eval_inl t t' u t' (by omega)
        exact (hflag ▸ hLHS).trans
          (by rw [hRHS]; rfl : ((sourceFragment t t' u ht F).attach
            ⟨Sum.inl (⟨k, hk⟩, b), hne⟩).map (Equiv.refl _) id = common).symm
    · -- ═══════ CASE 3: F-flag g ═══════
      have hflag : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inr g, hne⟩ = Sum.inr g
        := rfl
      have hg_ne : g ≠ F.boundaryFlag ⟨t', by omega⟩ := by
        intro heq
        exact hne.2
          (by rw [stageStep_rightBoundary]; exact congrArg Sum.inr heq)
      rcases ha : F.attach g with v | ℓ
      · -- F.attach g = Sum.inl v (vertex)
        set common : (targetFragment t t' u (by omega) F).Vertex ⊕
            (Fin (t + t') ⊕ Fin (t' + u)) := Sum.inl (Sum.inr v)
        have hLHS : (targetFragment t t' u (by omega) F).attach (Sum.inr g) =
            common := by
          change (((strandBundle t').disjUnion F).attach (Sum.inr g)).map id
            (stageEquiv t t' u _) = _
          change ((F.attach g).map Sum.inr Sum.inr).map id (stageEquiv t t' u _)
            = _
          rw [ha]; rfl
        have hRHS : (sourceFragment t t' u ht F).attach ⟨Sum.inr g, hne⟩ =
            common := by
          change ((Fragment.glueAttach (baseFragment t t' u ht F)
              (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
              ⟨Sum.inr g, hne⟩).map id (interfaceStepEquiv t t' u)) = _
          have hba : (baseFragment t t' u ht F).attach (Sum.inr g) =
              Sum.inl (Sum.inr v) := by
            change (((strandBundle (t' + 1)).disjUnion F).attach (Sum.inr
              g)).map id
              (stageEquiv t (t' + 1) u ht) = _
            change ((F.attach g).map Sum.inr Sum.inr).map id (stageEquiv t (t' +
              1) u ht) = _
            rw [ha]; rfl
          refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
            (fun ℓ' hℓ' => ?_)
          · simp only [Sum.map_inl, id_eq]
            exact congrArg Sum.inl (Sum.inl.inj (hv'.symm.trans hba))
          · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
            exact absurd (hℓ'.symm.trans hba) (nomatch ·)
        exact (hflag ▸ hLHS).trans
          (by rw [hRHS]; rfl : ((sourceFragment t t' u ht F).attach
            ⟨Sum.inr g, hne⟩).map (Equiv.refl _) id = common).symm
      · -- F.attach g = Sum.inr ℓ (label)
        have hℓ_ne_t' : ℓ.val ≠ t' := by
          intro heq
          have hatt : F.attach g = Sum.inr ⟨t', by omega⟩ := by
            exact ha.trans (congrArg Sum.inr (Fin.ext heq))
          exact hg_ne (F.eq_boundaryFlag ⟨t', by omega⟩ g hatt)
        by_cases hℓ_lt_t' : ℓ.val < t'
        · -- Case 3b: ℓ.val < t'
          set common : (targetFragment t t' u (by omega) F).Vertex ⊕
              (Fin (t + t') ⊕ Fin (t' + u)) := Sum.inr
                (Sum.inr ⟨ℓ.val, by omega⟩)
          have hLHS : (targetFragment t t' u (by omega) F).attach (Sum.inr g) =
              common := by
            change (((strandBundle t').disjUnion F).attach (Sum.inr g)).map id
              (stageEquiv t t' u _) = _
            change ((F.attach g).map Sum.inr Sum.inr).map id (stageEquiv t t' u
              _) = _
            rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
            rw [stageEquiv_inr t t' u (by omega) ℓ, dif_pos hℓ_lt_t']
          have hRHS : (sourceFragment t t' u ht F).attach ⟨Sum.inr g, hne⟩ =
              common := by
            change ((Fragment.glueAttach (baseFragment t t' u ht F)
                (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
                ⟨Sum.inr g, hne⟩).map id (interfaceStepEquiv t t' u)) = _
            have hba : (baseFragment t t' u ht F).attach (Sum.inr g) =
                Sum.inr (Sum.inr ⟨ℓ.val, by omega⟩) := by
              change (((strandBundle (t' + 1)).disjUnion F).attach (Sum.inr
                g)).map id
                (stageEquiv t (t' + 1) u ht) = _
              change ((F.attach g).map Sum.inr Sum.inr).map id (stageEquiv t (t'
                + 1) u ht) = _
              rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
              rw [stageEquiv_inr t (t' + 1) u ht ℓ,
                  dif_pos (show ℓ.val < t' + 1 from by omega)]
            refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
              (fun ℓ' hℓ' => ?_)
            · exact absurd (hv'.symm.trans hba) (nomatch ·)
            · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
              simp only [Sum.map_inr]
              have hℓ'_eq : ℓ' = Sum.inr ⟨ℓ.val, by omega⟩ :=
                Sum.inr.inj (hℓ'.symm.trans hba)
              subst hℓ'_eq; refine congrArg Sum.inr ?_
              exact interfaceStepEquiv_eval_inr_below t t' u ℓ.val hℓ_lt_t'
          exact (hflag ▸ hLHS).trans
            (by rw [hRHS]; rfl : ((sourceFragment t t' u ht F).attach
              ⟨Sum.inr g, hne⟩).map (Equiv.refl _) id = common).symm
        · by_cases hℓ_lt_t : ℓ.val < t
          · -- Case 3c: t' < ℓ.val < t
            set common : (targetFragment t t' u (by omega) F).Vertex ⊕
                (Fin (t + t') ⊕ Fin (t' + u)) := Sum.inr
                  (Sum.inl ⟨ℓ.val, by omega⟩)
            have hLHS : (targetFragment t t' u (by omega) F).attach (Sum.inr g)
              =
                common := by
              change (((strandBundle t').disjUnion F).attach (Sum.inr g)).map id
                (stageEquiv t t' u _) = _
              change ((F.attach g).map Sum.inr Sum.inr).map id (stageEquiv t t'
                u _) = _
              rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
              rw [stageEquiv_inr t t' u (by omega) ℓ,
                  dif_neg (show ¬ ℓ.val < t' from hℓ_lt_t'), dif_pos hℓ_lt_t]
            have hRHS : (sourceFragment t t' u ht F).attach ⟨Sum.inr g, hne⟩ =
                common := by
              change ((Fragment.glueAttach (baseFragment t t' u ht F)
                  (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
                  ⟨Sum.inr g, hne⟩).map id (interfaceStepEquiv t t' u)) = _
              have hba : (baseFragment t t' u ht F).attach (Sum.inr g) =
                  Sum.inr (Sum.inl ⟨ℓ.val, by omega⟩) := by
                change (((strandBundle (t' + 1)).disjUnion F).attach (Sum.inr
                  g)).map id
                  (stageEquiv t (t' + 1) u ht) = _
                change ((F.attach g).map Sum.inr Sum.inr).map id
                  (stageEquiv t (t' + 1) u ht) = _
                rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
                rw [stageEquiv_inr t (t' + 1) u ht ℓ,
                    dif_neg (show ¬ ℓ.val < t' + 1 from by omega), dif_pos
                      hℓ_lt_t]
              refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
                (fun ℓ' hℓ' => ?_)
              · exact absurd (hv'.symm.trans hba) (nomatch ·)
              · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
                simp only [Sum.map_inr]
                have hℓ'_eq : ℓ' = Sum.inl ⟨ℓ.val, by omega⟩ :=
                  Sum.inr.inj (hℓ'.symm.trans hba)
                subst hℓ'_eq; refine congrArg Sum.inr ?_
                exact interfaceStepEquiv_eval_inl t t' u ℓ.val (by omega)
            exact (hflag ▸ hLHS).trans (by rw [hRHS]; rfl :
                ((sourceFragment t t' u ht F).attach
                ⟨Sum.inr g, hne⟩).map (Equiv.refl _) id = common).symm
          · -- Case 3d: ℓ.val ≥ t
            set common : (targetFragment t t' u (by omega) F).Vertex ⊕
                (Fin (t + t') ⊕ Fin (t' + u)) :=
              Sum.inr (Sum.inr ⟨t' + (ℓ.val - t), by omega⟩)
            have hLHS : (targetFragment t t' u (by omega) F).attach (Sum.inr g)
              =
                common := by
              change (((strandBundle t').disjUnion F).attach (Sum.inr g)).map id
                (stageEquiv t t' u _) = _
              change ((F.attach g).map Sum.inr Sum.inr).map id (stageEquiv t t'
                u _) = _
              rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
              rw [stageEquiv_inr t t' u (by omega) ℓ,
                  dif_neg (show ¬ ℓ.val < t' from hℓ_lt_t'), dif_neg hℓ_lt_t]
            have hRHS : (sourceFragment t t' u ht F).attach ⟨Sum.inr g, hne⟩ =
                common := by
              change ((Fragment.glueAttach (baseFragment t t' u ht F)
                  (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
                  ⟨Sum.inr g, hne⟩).map id (interfaceStepEquiv t t' u)) = _
              have hba : (baseFragment t t' u ht F).attach (Sum.inr g) =
                  Sum.inr (Sum.inr ⟨(t' + 1) + (ℓ.val - t), by omega⟩) := by
                change (((strandBundle (t' + 1)).disjUnion F).attach (Sum.inr
                  g)).map id
                  (stageEquiv t (t' + 1) u ht) = _
                change ((F.attach g).map Sum.inr Sum.inr).map id
                  (stageEquiv t (t' + 1) u ht) = _
                rw [ha]; simp only [Sum.map_inr]; refine congrArg Sum.inr ?_
                rw [stageEquiv_inr t (t' + 1) u ht ℓ,
                    dif_neg (show ¬ ℓ.val < t' + 1 from by omega), dif_neg
                      hℓ_lt_t]
              refine Fragment.glueAttach_cases _ (fun v' hv' => ?_)
                (fun ℓ' hℓ' => ?_)
              · exact absurd (hv'.symm.trans hba) (nomatch ·)
              · obtain ⟨ℓ', _hs₁, _hs₂⟩ := ℓ'
                have hℓ'_eq : ℓ' = Sum.inr ⟨(t' + 1) + (ℓ.val - t), by omega⟩ :=
                  Sum.inr.inj (hℓ'.symm.trans hba)
                subst hℓ'_eq
                simp only [Sum.map_inr]
                exact congrArg Sum.inr ((interfaceStepEquiv_eval_inr_above t t'
                  u
                  ((t' + 1) + (ℓ.val - t)) (by omega) (by omega)).trans
                  (congrArg Sum.inr (Fin.ext (by simp))))
            exact hLHS.trans
              (by rw [hRHS]; rfl : ((sourceFragment t t' u ht F).attach
                ⟨Sum.inr g, hne⟩).map (Equiv.refl _) id = common).symm
  pairing_comm := fun f => by
    obtain ⟨fval, hne⟩ := f
    show (stageStepFlagEquiv t t' u ht F)
      (Fragment.rewire (stageStep_hopen t t' u ht F) ⟨fval, hne⟩) =
      (targetFragment t t' u (by omega) F).pairing
      ((stageStepFlagEquiv t t' u ht F) ⟨fval, hne⟩)
    rcases fval with ⟨⟨k, hk⟩, b⟩ | g
    · -- ═══════ CASE: strand flag (⟨k, hk⟩, b) ═══════
      by_cases hlt : k < t'
      · -- Case 1: k < t', rewire "neither" branch
        have hni : (baseFragment t t' u ht F).pairing (Sum.inl (⟨k, hk⟩, b)) ≠
            (baseFragment t t' u ht F).boundaryFlag (Sum.inl ⟨t + t', by omega⟩)
              := by
          change Sum.inl (⟨k, hk⟩, !b) ≠
            (baseFragment t t' u ht F).boundaryFlag (Sum.inl ⟨t + t', by omega⟩)
          rw [stageStep_leftBoundary]; intro h
          have := congrArg Prod.fst (Sum.inl.inj h)
          exact absurd (Fin.ext_iff.mp this) (Nat.ne_of_lt hlt)
        have hnj : (baseFragment t t' u ht F).pairing (Sum.inl (⟨k, hk⟩, b)) ≠
            (baseFragment t t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
              by
          change Sum.inl (⟨k, hk⟩, !b) ≠
            (baseFragment t t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)
          rw [stageStep_rightBoundary]; exact (nomatch ·)
        have hrewire_val : (Fragment.rewire (stageStep_hopen t t' u ht F)
            ⟨Sum.inl (⟨k, hk⟩, b), hne⟩).val = Sum.inl (⟨k, hk⟩, !b) := by
          unfold Fragment.rewire
          simp only [show (baseFragment t t' u ht F).pairing (Sum.inl (⟨k, hk⟩,
            b)) =
            Sum.inl (⟨k, hk⟩, !b) from rfl]
          rw [dif_neg hni, dif_neg hnj]
        have heq_rw : Fragment.rewire (stageStep_hopen t t' u ht F)
            ⟨Sum.inl (⟨k, hk⟩, b), hne⟩ = ⟨Sum.inl (⟨k, hk⟩, !b), ⟨hni, hnj⟩⟩ :=
          Subtype.ext hrewire_val
        have hflag_rw : (stageStepFlagEquiv t t' u ht F)
            (Fragment.rewire (stageStep_hopen t t' u ht F) ⟨Sum.inl (⟨k, hk⟩,
              b), hne⟩) =
            Sum.inl (⟨k, hlt⟩, !b) := by
          rw [heq_rw]
          have key : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, !b),
            ⟨hni, hnj⟩⟩ =
            if hlt' : k < t' then Sum.inl (⟨k, hlt'⟩, !b)
            else Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := rfl
          rw [key, dif_pos hlt]
        have hflag_f : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, b),
          hne⟩ =
            Sum.inl (⟨k, hlt⟩, b) := by
          have key : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, b),
            hne⟩ =
            if hlt' : k < t' then Sum.inl (⟨k, hlt'⟩, b)
            else Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := rfl
          rw [key, dif_pos hlt]
        rw [hflag_rw, hflag_f]
        rfl
      · -- Case 2: k ≥ t' (must be k = t', b = false)
        have hk_eq : k = t' := by omega
        have hb : b = false := by
          by_contra hbt
          have hbtrue : b = true := by cases b <;> simp_all
          exact hne.1 (by
            rw [stageStep_leftBoundary]
            exact congrArg Sum.inl (Prod.ext (Fin.ext hk_eq) hbtrue))
        have hpair_eq_bdy : (baseFragment t t' u ht F).pairing (Sum.inl (⟨k,
          hk⟩, b)) =
            (baseFragment t t' u ht F).boundaryFlag (Sum.inl ⟨t + t', by omega⟩)
              := by
          change Sum.inl (⟨k, hk⟩, !b) =
            (baseFragment t t' u ht F).boundaryFlag (Sum.inl ⟨t + t', by omega⟩)
          rw [stageStep_leftBoundary]; subst hk_eq; subst hb; rfl
        have hrewire_val : (Fragment.rewire (stageStep_hopen t t' u ht F)
            ⟨Sum.inl (⟨k, hk⟩, b), hne⟩).val =
            Sum.inr (F.pairing (F.boundaryFlag ⟨t', by omega⟩)) := by
          simp only [Fragment.rewire, dif_pos hpair_eq_bdy]
          rw [stageStep_rightBoundary]; rfl
        have hflag_rw : (stageStepFlagEquiv t t' u ht F)
            (Fragment.rewire (stageStep_hopen t t' u ht F) ⟨Sum.inl (⟨k, hk⟩,
              b), hne⟩) =
            Sum.inr (F.pairing (F.boundaryFlag ⟨t', by omega⟩)) := by
          have hprop : Sum.inr (F.pairing (F.boundaryFlag ⟨t', by omega⟩)) ≠
              (baseFragment t t' u ht F).boundaryFlag
                (Sum.inl ⟨t + t', by omega⟩) ∧
              Sum.inr (F.pairing (F.boundaryFlag ⟨t', by omega⟩)) ≠
              (baseFragment t t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩)
                := by
            refine ⟨?_, ?_⟩
            · rw [stageStep_leftBoundary]; exact (nomatch ·)
            · rw [stageStep_rightBoundary]; intro h
              exact F.pairing_ne (F.boundaryFlag ⟨t', by omega⟩) (Sum.inr.inj h)
          have heq : Fragment.rewire (stageStep_hopen t t' u ht F)
              ⟨Sum.inl (⟨k, hk⟩, b), hne⟩ =
              ⟨Sum.inr (F.pairing (F.boundaryFlag ⟨t', by omega⟩)), hprop⟩ :=
            Subtype.ext hrewire_val
          rw [heq]; rfl
        have hflag_f : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, b),
          hne⟩ =
            Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := by
          have key : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inl (⟨k, hk⟩, b),
            hne⟩ =
            if hlt' : k < t' then Sum.inl (⟨k, hlt'⟩, b)
            else Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := rfl
          rw [key, dif_neg hlt]
        rw [hflag_rw, hflag_f]
        rfl
    · -- ═══════ CASE: F-flag g ═══════
      have hg_ne : g ≠ F.boundaryFlag ⟨t', by omega⟩ := by
        intro heq
        exact hne.2
          (by rw [stageStep_rightBoundary]; exact congrArg Sum.inr heq)
      have hni : (baseFragment t t' u ht F).pairing (Sum.inr g) ≠
          (baseFragment t t' u ht F).boundaryFlag (Sum.inl ⟨t + t', by omega⟩)
            := by
        intro h; rw [stageStep_leftBoundary] at h; exact nomatch h
      have hflag_f : (stageStepFlagEquiv t t' u ht F) ⟨Sum.inr g, hne⟩ = Sum.inr
        g := rfl
      by_cases hpg : F.pairing g = F.boundaryFlag ⟨t', by omega⟩
      · -- Sub-case: F.pairing g = F.boundaryFlag ⟨t', _⟩
        have hnj : (baseFragment t t' u ht F).pairing (Sum.inr g) =
            (baseFragment t t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
              by
          rw [show (baseFragment t t' u ht F).pairing (Sum.inr g) =
            Sum.inr (F.pairing g) from rfl, stageStep_rightBoundary, hpg]
        have hrewire_val : (Fragment.rewire (stageStep_hopen t t' u ht F)
            ⟨Sum.inr g, hne⟩).val = Sum.inl (⟨t', by omega⟩, false) := by
          unfold Fragment.rewire
          rw [dif_neg hni, dif_pos hnj]
          show (baseFragment t t' u ht F).pairing
            ((baseFragment t t' u ht F).boundaryFlag
              (Sum.inl ⟨t + t', by omega⟩)) = _
          rw [stageStep_leftBoundary]
          exact stageStep_leftPairing t t' u ht F
        have hne_rw : Sum.inl (⟨t', by omega⟩, false) ≠
            (baseFragment t t' u ht F).boundaryFlag (Sum.inl ⟨t + t', by omega⟩)
              ∧
            Sum.inl (⟨t', by omega⟩, false) ≠
            (baseFragment t t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
              by
          refine ⟨?_, ?_⟩
          · rw [stageStep_leftBoundary]; intro h
            exact absurd (congrArg Prod.snd (Sum.inl.inj h)) Bool.false_ne_true
          · rw [stageStep_rightBoundary]; exact (nomatch ·)
        have heq_rw : Fragment.rewire (stageStep_hopen t t' u ht F)
            ⟨Sum.inr g, hne⟩ = ⟨Sum.inl (⟨t', by omega⟩, false), hne_rw⟩ :=
          Subtype.ext hrewire_val
        have hflag_rw : (stageStepFlagEquiv t t' u ht F)
            (Fragment.rewire (stageStep_hopen t t' u ht F) ⟨Sum.inr g, hne⟩) =
            Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := by
          rw [heq_rw]
          have key : (stageStepFlagEquiv t t' u ht F)
              ⟨Sum.inl (⟨t', by omega⟩, false), hne_rw⟩ =
            if hlt' : t' < t' then Sum.inl (⟨t', hlt'⟩, false)
            else Sum.inr (F.boundaryFlag ⟨t', by omega⟩) := rfl
          rw [key, dif_neg (Nat.lt_irrefl t')]
        rw [hflag_rw, hflag_f]
        show Sum.inr (F.boundaryFlag ⟨t', _⟩) = Sum.inr (F.pairing g)
        exact congrArg Sum.inr hpg.symm
      · -- Sub-case: F.pairing g ≠ F.boundaryFlag ⟨t', _⟩
        have hnj : (baseFragment t t' u ht F).pairing (Sum.inr g) ≠
            (baseFragment t t' u ht F).boundaryFlag (Sum.inr ⟨t', by omega⟩) :=
              by
          intro h; rw [stageStep_rightBoundary] at h; exact hpg (Sum.inr.inj h)
        have hrewire_val : (Fragment.rewire (stageStep_hopen t t' u ht F)
            ⟨Sum.inr g, hne⟩).val = Sum.inr (F.pairing g) := by
          unfold Fragment.rewire
          simp only [show (baseFragment t t' u ht F).pairing (Sum.inr g) =
            Sum.inr (F.pairing g) from rfl]
          rw [dif_neg hni, dif_neg hnj]
        have heq_rw : Fragment.rewire (stageStep_hopen t t' u ht F)
            ⟨Sum.inr g, hne⟩ = ⟨Sum.inr (F.pairing g), ⟨hni, hnj⟩⟩ :=
          Subtype.ext hrewire_val
        have hflag_rw : (stageStepFlagEquiv t t' u ht F)
            (Fragment.rewire (stageStep_hopen t t' u ht F) ⟨Sum.inr g, hne⟩) =
            Sum.inr (F.pairing g) := by
          rw [heq_rw]; rfl
        rw [hflag_rw, hflag_f]
        rfl

/-! ### Assembly: the left identity law -/

/-- The stage equivalence at `t' = t` acts as the identity: every
element is mapped to itself. -/
theorem stageEquiv_self (t u : ℕ) (x : Fin (t + t) ⊕ Fin (t + u)) :
    stageEquiv t t u (le_refl t) x = x := by
  rcases x with a | ℓ
  · rw [stageEquiv_inl]
    split
    · next h => exact congrArg Sum.inl (Fin.ext rfl)
    · next h =>
      have ha_ge : t ≤ a.val := Nat.not_lt.mp h
      exact congrArg Sum.inl
        (Fin.ext (show t + (a.val - t) = a.val from by omega))
  · rw [stageEquiv_inr]
    split
    · next h => exact congrArg Sum.inr (Fin.ext rfl)
    · next h₁ =>
      exact congrArg Sum.inr
        (Fin.ext (show t + (ℓ.val - t) = ℓ.val from by omega))

/-- Relabelling by a pointwise-identity equivalence yields an
equivalent fragment. -/
def Fragment.Equiv.relabelPointwiseId (W : Fragment α) (e : α ≃ α)
    (h : ∀ x, e x = x) :
    (W.relabel e).Equiv W where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm := fun f => by
    show W.attach f = ((W.attach f).map id e).map (_root_.Equiv.refl _) id
    rcases W.attach f with v | ℓ
    · simp
    · simp [h ℓ]
  pairing_comm := fun _ => rfl
  circles_eq := rfl

/-- In the base fragment, the glue is always open, so `gluePair`
coincides with `gluePairOpen`. -/
private theorem baseFragment_gluePair_eq (t t' u : ℕ) (ht : t' + 1 ≤ t)
    (F : Fragment (Fin (t + u))) :
    (baseFragment t t' u ht F).gluePair (Sum.inl ⟨t + t', by omega⟩)
      (Sum.inr ⟨t', by omega⟩) (by simp) =
    (baseFragment t t' u ht F).gluePairOpen (Sum.inl ⟨t + t', by omega⟩)
      (Sum.inr ⟨t', by omega⟩) (by simp) (stageStep_hopen t t' u ht F) := by
  unfold Fragment.gluePair
  exact dif_neg (stageStep_hopen t t' u ht F)

/-- Descending induction: iterating `glueInterface` from stage `t'`
down to zero, with the stage-`t'` fragment, yields a result
equivalent to iterating from stage `t` on the original strand/F
union. -/
private noncomputable def glueInterface_strandBundle_desc
    (t u : ℕ) (F : Fragment (Fin (t + u))) :
    ∀ (t' : ℕ) (ht' : t' ≤ t),
    (glueInterface t t u ((strandBundle t).disjUnion F)).Equiv
    (glueInterface t t' u (((strandBundle t').disjUnion F).relabel
      (stageEquiv t t' u ht')))
  | t', ht' => by
    by_cases htop : t' = t
    · -- Base: t' = t, the stageEquiv is pointwise identity
      cases htop
      exact glueInterfaceCongr _ _ u
        ((Fragment.Equiv.relabelPointwiseId _ _
          (stageEquiv_self _ u)).symm)
    · -- Step: t' < t, use stageStepEquiv to descend one level
      have ht'_lt : t' + 1 ≤ t := by omega
      have ih := glueInterface_strandBundle_desc t u F (t' + 1) ht'_lt
      -- The IH gives equivalence to glueInterface at stage t' + 1.
      -- Unfolding glueInterface at t'+1 applies one gluePair + relabel.
      -- stageStepEquiv shows the result is equivalent to stage t'.
      have step : ((baseFragment t t' u ht'_lt F).gluePair
          (Sum.inl ⟨t + t', by omega⟩) (Sum.inr ⟨t', by omega⟩)
          (by simp)).relabel (interfaceStepEquiv t t' u) =
        sourceFragment t t' u ht'_lt F := by
        unfold sourceFragment
        rw [← baseFragment_gluePair_eq]
      exact ih.trans (glueInterfaceCongr t t' u
        (step ▸ (stageStepEquiv t t' u ht'_lt F)))
termination_by t' _ => t - t'
decreasing_by omega

/-- The left identity law for fragment composition: composing with
the strand bundle on the left yields an equivalent fragment. -/
noncomputable def composeStrandBundleLeft (t u : ℕ)
    (F : Fragment (Fin (t + u))) :
    ((strandBundle t).compose F).Equiv F :=
  (Fragment.Equiv.relabelCongr
    (glueInterface_strandBundle_desc t u F 0 (Nat.zero_le t))
      finSumFinEquiv).trans
    (stageZeroEquiv t u F)

end RS
