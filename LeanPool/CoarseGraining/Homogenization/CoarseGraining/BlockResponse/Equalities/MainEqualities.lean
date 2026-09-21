/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Equalities.Helpers

/-! # Main Equalities -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse Equalities -- blockJ equals half-responseJ-adjoint-sum

blockJ le / eq half responseJ adjoint sum under IsEllipticFieldOn with
hodgeConverseCriterion or IsOpenBoundedConvexDomain, together with the
note-form variants.
-/

theorem blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a ≤
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) := by
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  unfold BlockJ
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    refine ⟨({ potential := 0, flux := 0 } : BlockState d),
      blockResponse_zero_mem_responseSpace a U, blockResponseIntegrabilityData_zero U a, ?_⟩
    rw [blockResponse_integrand_zero]
    simp [volumeAverage]
  · intro m hm
    rcases hm with ⟨X, hX, hIntX, rfl⟩
    have hLowerL2 :
        MemVectorL2 U
          (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
      blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
        hX hIntX.flux_memL2 hEll
    have hLowerPot :
        IsPotentialOn U
          (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
      blockResponse_lowerImage_isPotential_of_mem_responseSpace_of_memVectorL2_of_hodgeConverseCriterion
        (hHodge := hHodge) hX hLowerL2
    rcases
      volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_of_mem_responseSpace_of_lowerImage_isPotential_of_isEllipticFieldOn
        (a := a) hU hX hLowerPot hEll p pStar q qStar with
      ⟨u, v, hsplit⟩
    have hu :
        volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) ≤
          ResponseJ U (p - pStar) (qStar - q) a :=
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn
        hEll hvol (p - pStar) (qStar - q)
        (responseJValueSet_mem U (p - pStar) (qStar - q) a u)
    have hv :
        volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v) ≤
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) :=
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn
        hEllAdj hvol (pStar + p) (qStar + q)
        (responseJValueSet_mem U (pStar + p) (qStar + q)
          (Homogenization.adjointCoeffField a) v)
    linarith [hsplit, hu, hv]

theorem blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a ≤
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) := by
  exact
    blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (a := a) hU hEll hvol
      (HasHodgeConverse.hodgeConverseCriterion (U := U)) p pStar q qStar

theorem blockJ_note_form_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a ≤
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) := by
  simpa using
    blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (a := a) hU hEll hvol hHodge (p := p) (pStar := 0) (q := h) (qStar := q)

theorem blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a ≤
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) := by
  exact
    blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (a := a)
      (hU := hConv.isOpen.measurableSet)
      hEll
      hvol
      (hHodge := hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      p
      pStar
      q
      qStar

theorem blockJ_note_form_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a ≤
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) := by
  simpa using
    blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a) hConv hEll hvol (p := p) (pStar := 0) (q := h) (qStar := q)

theorem half_responseJ_adjoint_sum_le_blockJ_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ≤
      BlockJ U (p, q) (qStar, pStar) a := by
  let J := BlockJ U (p, q) (qStar, pStar) a
  let A := responseJValueSet U (p - pStar) (qStar - q) a
  let B := responseJValueSet U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a)
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  have hpair :
      ∀ m ∈ A, ∀ n ∈ B, (1 / 2 : ℝ) * m + (1 / 2 : ℝ) * n ≤ J := by
    intro m hm n hn
    rcases hm with ⟨u, rfl⟩
    rcases hn with ⟨v, rfl⟩
    dsimp [A, B, J]
    exact blockResponse_half_scalarResponse_sum_le_blockJ_of_isEllipticFieldOn
      (a := a) hU hEll hvol (p := p) (pStar := pStar) (q := q) (qStar := qStar)
      (u := u) (v := v)
  have hresp1 :
      ResponseJ U (p - pStar) (qStar - q) a ≤
        2 * J - ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) := by
    unfold ResponseJ
    refine csSup_le (responseJValueSet_nonempty U (p - pStar) (qStar - q) a) ?_
    intro m hm
    have hresp2 :
        ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ≤
          2 * J - m := by
      unfold ResponseJ
      refine csSup_le
        (responseJValueSet_nonempty U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a)) ?_
      intro n hn
      have hmn := hpair m hm n hn
      linarith
    have hm_le :
        m ≤ 2 * J - ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) := by
      have hsum_le :
          m + ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ≤
            2 * J := by
        have hsum_le' := (le_sub_iff_add_le).mp hresp2
        simpa [add_comm, add_left_comm, add_assoc] using hsum_le'
      exact (le_sub_iff_add_le).mpr hsum_le
    exact hm_le
  have hsum :
      ResponseJ U (p - pStar) (qStar - q) a +
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ≤
        2 * J := by
    have hsum' := (le_sub_iff_add_le).mp hresp1
    simpa [add_comm, add_left_comm, add_assoc] using hsum'
  nlinarith [hsum]

theorem half_responseJ_adjoint_sum_note_form_le_blockJ_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) ≤
      BlockJ U (p, h) (q, 0) a := by
  simpa using
    half_responseJ_adjoint_sum_le_blockJ_of_isEllipticFieldOn
      (a := a) hU hEll hvol (p := p) (pStar := 0) (q := h) (qStar := q)

theorem blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) := by
  apply le_antisymm
  · exact
      blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
        (a := a) hU hEll hvol hHodge p pStar q qStar
  · exact
      half_responseJ_adjoint_sum_le_blockJ_of_isEllipticFieldOn
        (a := a) hU hEll hvol p pStar q qStar

theorem blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) := by
  exact
    blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (a := a) hU hEll hvol (HasHodgeConverse.hodgeConverseCriterion (U := U))
      p pStar q qStar

theorem blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) := by
  simpa using
    blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
      (a := a) hU hEll hvol (p := p) (pStar := 0) (q := h) (qStar := q)

theorem blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) := by
  simpa using
    blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (a := a) hU hEll hvol hHodge (p := p) (pStar := 0) (q := h) (qStar := q)

theorem blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) := by
  exact
    blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (a := a)
      (hU := hConv.isOpen.measurableSet)
      hEll
      hvol
      (hHodge := hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      p
      pStar
      q
      qStar

theorem blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) := by
  simpa using
    blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a) hConv hEll hvol (p := p) (pStar := 0) (q := h) (qStar := q)


end

end Homogenization
