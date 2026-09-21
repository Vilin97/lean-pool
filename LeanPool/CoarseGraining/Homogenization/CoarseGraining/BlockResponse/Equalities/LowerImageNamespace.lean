/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Equalities.MainEqualities

/-! # Lower Image Namespace -/

namespace Homogenization

noncomputable section

/-!
# BlockResponse Equalities -- BlockResponseLowerImageMemVectorL2Data namespace

blockJ le / eq half responseJ adjoint sum in the
BlockResponseLowerImageMemVectorL2Data namespace (with and without
hodgeConverseCriterion / IsOpenBoundedConvexDomain), the blockJ eq
half scalarResponse sum for scalarCanonicalMaximizers, plus the trailing
blockResponse integrand_add / blockJValueSet membership and blockJ_nonneg
lemmas.
-/

namespace BlockResponseLowerImageMemVectorL2Data

/-- Lower-level Hodge-packaged upper bound for the doubled response functional.
For note-facing Chapter 2 statements on bounded open convex domains, prefer
`blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain`.
-/
theorem blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a ≤
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    (a := a) hU hEll hvol p pStar q qStar

theorem blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a ≤
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (a := a) hU hEll hvol hHodge p pStar q qStar

/-- Preferred note-facing lower-image-packaged upper bound for the doubled
response functional on bounded open convex domains. -/
theorem blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a ≤
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (a := a) hConv hEll hvol p pStar q qStar

theorem blockJ_note_form_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a ≤
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_note_form_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (a := a) hU hEll hvol (HasHodgeConverse.hodgeConverseCriterion (U := U)) p q h

theorem blockJ_note_form_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a ≤
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_note_form_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (a := a) hU hEll hvol hHodge p q h

theorem blockJ_note_form_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a ≤
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_note_form_le_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (a := a) hConv hEll hvol p q h

theorem half_responseJ_adjoint_sum_le_blockJ_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ≤
      BlockJ U (p, q) (qStar, pStar) a :=
  Homogenization.half_responseJ_adjoint_sum_le_blockJ_of_isEllipticFieldOn
    (a := a) hU hEll hvol p pStar q qStar

theorem half_responseJ_adjoint_sum_note_form_le_blockJ_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) ≤
      BlockJ U (p, h) (q, 0) a :=
  Homogenization.half_responseJ_adjoint_sum_note_form_le_blockJ_of_isEllipticFieldOn
    (a := a) hU hEll hvol p q h

/-- Lower-level Hodge-packaged equality
`BlockJ = (1/2)(ResponseJ + ResponseJ^*)`. For note-facing Chapter 2
statements on bounded open convex domains, prefer
`blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain`.
-/
theorem blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    (a := a) hU hEll hvol p pStar q qStar

theorem blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (a := a) hU hEll hvol hHodge p pStar q qStar

/-- Preferred note-facing lower-image-packaged equality
`BlockJ = (1/2)(ResponseJ + ResponseJ^*)` on bounded open convex domains. -/
theorem blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (a := a) hConv hEll hvol p pStar q qStar

theorem blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    (a := a) hU hEll hvol p q h

theorem blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (a := a) hU hEll hvol hHodge p q h

theorem blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) :=
  Homogenization.blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (a := a) hConv hEll hvol p q h

theorem blockJ_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d)
    (u : ScalarCanonicalMaximizer U (p - pStar) (qStar - q) a)
    (v : ScalarCanonicalMaximizer U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a)) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) *
        volumeAverage U
          (scalarResponseIntegrand U a (p - pStar) (qStar - q) (u : AHarmonicFunction a U)) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q)
              (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) := by
  rw [blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    hU hEll hvol p pStar q qStar]
  rw [ScalarCanonicalMaximizer.responseJ_eq u, ScalarCanonicalMaximizer.responseJ_eq v]

theorem blockJ_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p pStar q qStar : Vec d)
    (u : ScalarCanonicalMaximizer U (p - pStar) (qStar - q) a)
    (v : ScalarCanonicalMaximizer U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a)) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) *
        volumeAverage U
          (scalarResponseIntegrand U a (p - pStar) (qStar - q) (u : AHarmonicFunction a U)) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q)
              (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) :=
by
  rw [blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    hU hEll hvol hHodge p pStar q qStar]
  rw [ScalarCanonicalMaximizer.responseJ_eq u, ScalarCanonicalMaximizer.responseJ_eq v]

/-- Preferred note-facing scalar-canonical lower-image-packaged equality on
bounded open convex domains. -/
theorem blockJ_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d)
    (u : ScalarCanonicalMaximizer U (p - pStar) (qStar - q) a)
    (v : ScalarCanonicalMaximizer U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a)) :
    BlockJ U (p, q) (qStar, pStar) a =
      (1 / 2 : ℝ) *
        volumeAverage U
          (scalarResponseIntegrand U a (p - pStar) (qStar - q) (u : AHarmonicFunction a U)) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q)
              (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) := by
  rw [blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    hConv hEll hvol p pStar q qStar]
  rw [ScalarCanonicalMaximizer.responseJ_eq u, ScalarCanonicalMaximizer.responseJ_eq v]

/-- Witness-free convex-domain scalar-response equality: the maximizing scalar
states are chosen internally from the direct-method existence theorem. This is
the preferred Chapter-2-facing surface when one wants the scalar-response
decomposition without threading explicit maximizer data through the statement.
-/
theorem blockJ_eq_half_scalarResponse_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    ∃ u : ScalarCanonicalMaximizer U (p - pStar) (qStar - q) a,
      ∃ v : ScalarCanonicalMaximizer U (pStar + p) (qStar + q)
          (Homogenization.adjointCoeffField a),
        BlockJ U (p, q) (qStar, pStar) a =
          (1 / 2 : ℝ) *
            volumeAverage U
              (scalarResponseIntegrand U a (p - pStar) (qStar - q)
                (u : AHarmonicFunction a U)) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q)
                  (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) := by
  classical
  have hne : Set.Nonempty U := by
    by_contra hne
    have hEmpty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact hvol (by simp [hEmpty])
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := a) hne hConv hEll (p - pStar) (qStar - q) with
    ⟨u⟩
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := Homogenization.adjointCoeffField a) hne hConv hEllAdj
        (pStar + p) (qStar + q) with
    ⟨v⟩
  refine ⟨u, v, ?_⟩
  exact
    blockJ_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      hConv hEll hvol p pStar q qStar u v

/-- Explicitly named existential version of the previous theorem. -/
theorem exists_scalarCanonicalMaximizers_blockJ_eq_half_scalarResponse_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d) :
    ∃ u : ScalarCanonicalMaximizer U (p - pStar) (qStar - q) a,
      ∃ v : ScalarCanonicalMaximizer U (pStar + p) (qStar + q)
          (Homogenization.adjointCoeffField a),
        BlockJ U (p, q) (qStar, pStar) a =
          (1 / 2 : ℝ) *
            volumeAverage U
              (scalarResponseIntegrand U a (p - pStar) (qStar - q)
                (u : AHarmonicFunction a U)) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q)
                  (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) := by
  classical
  have hne : Set.Nonempty U := by
    by_contra hne
    have hEmpty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact hvol (by simp [hEmpty])
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := a) hne hConv hEll (p - pStar) (qStar - q) with
    ⟨u⟩
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := Homogenization.adjointCoeffField a) hne hConv hEllAdj
        (pStar + p) (qStar + q) with
    ⟨v⟩
  refine ⟨u, v, ?_⟩
  exact
    blockJ_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      hConv hEll hvol p pStar q qStar u v

theorem blockJ_note_form_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d)
    (u : ScalarCanonicalMaximizer U p (q - h) a)
    (v : ScalarCanonicalMaximizer U p (q + h) (Homogenization.adjointCoeffField a)) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) *
        volumeAverage U (scalarResponseIntegrand U a p (q - h) (u : AHarmonicFunction a U)) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              p (q + h) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) := by
  rw [blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
    hU hEll hvol p q h]
  rw [ScalarCanonicalMaximizer.responseJ_eq u, ScalarCanonicalMaximizer.responseJ_eq v]

theorem blockJ_note_form_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hHodge : HodgeConverseCriterion U)
    (p q h : Vec d)
    (u : ScalarCanonicalMaximizer U p (q - h) a)
    (v : ScalarCanonicalMaximizer U p (q + h) (Homogenization.adjointCoeffField a)) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) *
        volumeAverage U (scalarResponseIntegrand U a p (q - h) (u : AHarmonicFunction a U)) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              p (q + h) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) :=
by
  rw [blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_hodgeConverseCriterion
    hU hEll hvol hHodge p q h]
  rw [ScalarCanonicalMaximizer.responseJ_eq u, ScalarCanonicalMaximizer.responseJ_eq v]

/-- Preferred note-facing scalar-canonical lower-image-packaged equality in
the note form on bounded open convex domains. -/
theorem blockJ_note_form_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d)
    (u : ScalarCanonicalMaximizer U p (q - h) a)
    (v : ScalarCanonicalMaximizer U p (q + h) (Homogenization.adjointCoeffField a)) :
    BlockJ U (p, h) (q, 0) a =
      (1 / 2 : ℝ) *
        volumeAverage U (scalarResponseIntegrand U a p (q - h) (u : AHarmonicFunction a U)) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              p (q + h) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) := by
  rw [blockJ_note_form_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    hConv hEll hvol p q h]
  rw [ScalarCanonicalMaximizer.responseJ_eq u, ScalarCanonicalMaximizer.responseJ_eq v]

/-- Witness-free convex-domain note-form scalar-response equality. The scalar
canonical maximizers are obtained internally, so downstream arguments can
consume the decomposition without packaging explicit maximizer witnesses. -/
theorem blockJ_note_form_eq_half_scalarResponse_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    ∃ u : ScalarCanonicalMaximizer U p (q - h) a,
      ∃ v : ScalarCanonicalMaximizer U p (q + h) (Homogenization.adjointCoeffField a),
        BlockJ U (p, h) (q, 0) a =
          (1 / 2 : ℝ) *
            volumeAverage U
              (scalarResponseIntegrand U a p (q - h) (u : AHarmonicFunction a U)) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  p (q + h) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) := by
  classical
  have hne : Set.Nonempty U := by
    by_contra hne
    have hEmpty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact hvol (by simp [hEmpty])
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := a) hne hConv hEll p (q - h) with
    ⟨u⟩
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := Homogenization.adjointCoeffField a) hne hConv hEllAdj p (q + h) with
    ⟨v⟩
  refine ⟨u, v, ?_⟩
  exact
    blockJ_note_form_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      hConv hEll hvol p q h u v

/-- Explicitly named existential version of the previous theorem. -/
theorem exists_scalarCanonicalMaximizers_blockJ_note_form_eq_half_scalarResponse_sum_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d) :
    ∃ u : ScalarCanonicalMaximizer U p (q - h) a,
      ∃ v : ScalarCanonicalMaximizer U p (q + h) (Homogenization.adjointCoeffField a),
        BlockJ U (p, h) (q, 0) a =
          (1 / 2 : ℝ) *
            volumeAverage U
              (scalarResponseIntegrand U a p (q - h) (u : AHarmonicFunction a U)) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  p (q + h) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) := by
  classical
  have hne : Set.Nonempty U := by
    by_contra hne
    have hEmpty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact hvol (by simp [hEmpty])
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := a) hne hConv hEll p (q - h) with
    ⟨u⟩
  rcases
      ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
        (U := U) (a := Homogenization.adjointCoeffField a) hne hConv hEllAdj p (q + h) with
    ⟨v⟩
  refine ⟨u, v, ?_⟩
  exact
    blockJ_note_form_eq_half_scalarResponse_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      hConv hEll hvol p q h u v

end BlockResponseLowerImageMemVectorL2Data

theorem blockResponse_integrand_add {d : ℕ} (a : CoeffField d) (P Q : BlockVec d)
    (X Y : BlockState d) :
    blockResponseIntegrand a P Q (X + Y) =
      fun x =>
        blockResponseIntegrand a P Q X x
          + blockResponseIntegrand a P Q Y x
          - blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) := by
  funext x
  have hcomm :
      blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (Y.eval x)) =
        blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) := by
    simpa [blockCoeffField] using
      (blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm
        (A := a x) (X := X.eval x) (Y := Y.eval x))
  simp [blockResponseIntegrand, blockEnergyDensity, blockMatVecMul_add, blockVecDot_add_left,
    blockVecDot_add_right]
  rw [hcomm]
  ring

theorem blockResponse_integrand_add_smul {d : ℕ} (a : CoeffField d) (P Q : BlockVec d)
    (X Y : BlockState d) (c : ℝ) :
    blockResponseIntegrand a P Q (X + c • Y) =
      fun x =>
        blockResponseIntegrand a P Q X x
          - (c ^ 2) * blockEnergyDensity a Y x
          - c * blockVecDot P (blockMatVecMul (blockCoeffField a x) (Y.eval x))
          + c * blockVecDot Q (Y.eval x)
          - c * blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) := by
  rw [blockResponse_integrand_add, blockResponse_integrand_smul]
  funext x
  simp [blockVecDot_smul_left]
  ring

theorem blockResponse_mem_blockJValueSet {d : ℕ} {U : Set (Vec d)} {P Q : BlockVec d}
    {a : CoeffField d} {X : BlockState d} (hX : BlockResponseSpace a U X)
    (hInt : BlockResponseIntegrabilityData U a X) :
    volumeAverage U (blockResponseIntegrand a P Q X) ∈ blockJValueSet U P Q a := by
  exact ⟨X, hX, hInt, rfl⟩

theorem blockResponse_blockJValueSet_smul_mem {d : ℕ} {U : Set (Vec d)} {P Q : BlockVec d}
    {a : CoeffField d} {m : ℝ} (hm : m ∈ blockJValueSet U P Q a) (c : ℝ) :
    c ^ 2 * m ∈ blockJValueSet U (c • P) (c • Q) a := by
  rcases hm with ⟨X, hX, hIntX, rfl⟩
  refine ⟨c • X, blockResponse_mem_responseSpace_smul hX c, hIntX.smul c, ?_⟩
  rw [blockResponse_integrand_smul_data_state]
  unfold volumeAverage
  rw [show (fun x => c ^ 2 * blockResponseIntegrand a P Q X x) =
      fun x => (c ^ 2 : ℝ) • blockResponseIntegrand a P Q X x by
        funext x
        simp [smul_eq_mul]]
  rw [MeasureTheory.integral_smul]
  simp [smul_eq_mul, mul_assoc, mul_comm]

theorem blockResponse_zero_mem_blockJValueSet {d : ℕ} (U : Set (Vec d))
    (P Q : BlockVec d) (a : CoeffField d) :
    (0 : ℝ) ∈ blockJValueSet U P Q a := by
  refine ⟨({ potential := 0, flux := 0 } : BlockState d),
    blockResponse_zero_mem_responseSpace a U, blockResponseIntegrabilityData_zero U a, ?_⟩
  rw [blockResponse_integrand_zero]
  simp [volumeAverage]

theorem blockResponse_blockJValueSet_nonempty {d : ℕ} (U : Set (Vec d))
    (P Q : BlockVec d) (a : CoeffField d) :
    (blockJValueSet U P Q a).Nonempty := by
  exact ⟨0, blockResponse_zero_mem_blockJValueSet U P Q a⟩

theorem blockJ_nonneg {d : ℕ} (U : Set (Vec d)) (P Q : BlockVec d) (a : CoeffField d) :
    0 ≤ BlockJ U P Q a := by
  unfold BlockJ
  exact Real.sSup_nonneg' ⟨0, blockResponse_zero_mem_blockJValueSet U P Q a, le_rfl⟩


end

end Homogenization
