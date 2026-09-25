/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse.Perturbation.BlockEnergyFirstVariation

/-! # Response JMu Adjoint -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# BlockResponse perturbation -- responseJ and mu-adjoint-sum family

blockEnergyAverage = responseJ identities under pairingAverage and
firstVariation hypotheses, the half-responseJ-sum reduction for
isResponseMaximizer / scalarCanonicalMaximizer data, the upper bound on
mu_zero_right against the half responseJ adjoint sum, and the corresponding
blockJValueSet / blockJ membership / bound theorems.
-/

/-- Coupling lemma with arbitrary scalar response data. -/
theorem blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_of_pairingAverage_eq_zero_of_firstVariation_eq_zero
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hpair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = 0)
    (hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0) :
    blockEnergyAverage U a (blockResponsePairHalfState a u v) =
      ResponseJ U p q a := by
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  let Eu : ℝ := volumeAverage U (scalarVariationEnergyIntegrand a u)
  let Ev : ℝ :=
    volumeAverage U (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v)
  have hEnergy :
      blockEnergyAverage U a (blockResponsePairHalfState a u v) =
        (1 / 4 : ℝ) * Eu + (1 / 4 : ℝ) * Ev := by
    simpa [Eu, Ev] using
      blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
        (a := a) (measurableSet_of_isEllipticFieldOn hEll) hEll u v
  have hPairSplit :
      (1 / 4 : ℝ) * Eu - (1 / 4 : ℝ) * Ev = 0 := by
    have hsplit :=
      volumeAverage_statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub
        (a := a) hEll u v
    linarith [hpair, hsplit]
  have hmax : IsResponseMaximizer U p q a u :=
    isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
      U a hEll p q u hfirst
  have hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hJ : ResponseJ U p q a = (1 / 2 : ℝ) * Eu := by
    simpa [Eu] using
      responseJ_energy_of_isResponseMaximizer U a p q u hmax
        (hInt.weakFlux u) (hInt.response p q u) (hInt.firstVariation p q u u)
        (hInt.energy u)
  linarith [hEnergy, hPairSplit, hJ]

/-- Coupling lemma with arbitrary scalar response data and nonzero average
state-pairing. The pairing is exactly the correction term between the block
half-pair energy and the scalar response value. -/
theorem blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_sub_pairing_of_pairingAverage_eq_of_firstVariation_eq_zero
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q : Vec d)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (pairing : ℝ)
    (hpair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = pairing)
    (hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a p q u w) = 0) :
    blockEnergyAverage U a (blockResponsePairHalfState a u v) =
      ResponseJ U p q a - pairing := by
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  let Eu : ℝ := volumeAverage U (scalarVariationEnergyIntegrand a u)
  let Ev : ℝ :=
    volumeAverage U (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v)
  have hEnergy :
      blockEnergyAverage U a (blockResponsePairHalfState a u v) =
        (1 / 4 : ℝ) * Eu + (1 / 4 : ℝ) * Ev := by
    simpa [Eu, Ev] using
      blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
        (a := a) (measurableSet_of_isEllipticFieldOn hEll) hEll u v
  have hPairSplit :
      (1 / 4 : ℝ) * Eu - (1 / 4 : ℝ) * Ev = pairing := by
    have hsplit :=
      volumeAverage_statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub
        (a := a) hEll u v
    linarith [hpair, hsplit]
  have hmax : IsResponseMaximizer U p q a u :=
    isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
      U a hEll p q u hfirst
  have hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hJ : ResponseJ U p q a = (1 / 2 : ℝ) * Eu := by
    simpa [Eu] using
      responseJ_energy_of_isResponseMaximizer U a p q u hmax
        (hInt.weakFlux u) (hInt.response p q u) (hInt.firstVariation p q u u)
        (hInt.energy u)
  linarith [hEnergy, hPairSplit, hJ]

/--
Pure-gradient coupling: the recovered first variation appears at `(-p,0)`,
and the final statement uses the quadratic evenness of `ResponseJ` in the
pure-gradient slice.
-/
theorem blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_left_zero_of_pairingAverage_eq_zero_of_firstVariation_neg_left_zero
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p : Vec d)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hpair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = 0)
    (hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a (-p) 0 u w) = 0) :
    blockEnergyAverage U a (blockResponsePairHalfState a u v) =
      ResponseJ U p 0 a := by
  have hneg :
      blockEnergyAverage U a (blockResponsePairHalfState a u v) =
        ResponseJ U (-p) 0 a :=
    blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_of_pairingAverage_eq_zero_of_firstVariation_eq_zero
      (a := a) hEll (-p) 0 u v hpair hfirst
  have heven : ResponseJ U (-p) 0 a = ResponseJ U p 0 a := by
    simpa using
      responseJ_homogeneous_zero_right U p a
        (c := (-1 : ℝ)) (by norm_num)
  exact hneg.trans heven

/-- Coupling lemma for the pure-flux slice: if the half-pair has zero average
state-pairing and its primal scalar component satisfies the Euler-Lagrange
identity for `ResponseJ U 0 q a`, then the block half-pair energy is exactly
that scalar response value. -/
theorem blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_zero_of_pairingAverage_eq_zero_of_firstVariation_eq_zero
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d)
    (u : AHarmonicFunction a U)
    (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hpair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = 0)
    (hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a 0 q u w) = 0) :
    blockEnergyAverage U a (blockResponsePairHalfState a u v) =
      ResponseJ U 0 q a := by
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  let Eu : ℝ := volumeAverage U (scalarVariationEnergyIntegrand a u)
  let Ev : ℝ :=
    volumeAverage U (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v)
  have hEnergy :
      blockEnergyAverage U a (blockResponsePairHalfState a u v) =
        (1 / 4 : ℝ) * Eu + (1 / 4 : ℝ) * Ev := by
    simpa [Eu, Ev] using
      blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
        (a := a) hU hEll u v
  have hPairSplit :
      (1 / 4 : ℝ) * Eu - (1 / 4 : ℝ) * Ev = 0 := by
    have hsplit :=
      volumeAverage_statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub
        (a := a) hEll u v
    linarith [hpair, hsplit]
  have hmax : IsResponseMaximizer U 0 q a u :=
    isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
      U a hEll 0 q u hfirst
  have hInt : ResponseLinearIntegrabilityData U a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hJ : ResponseJ U 0 q a = (1 / 2 : ℝ) * Eu := by
    simpa [Eu] using
      responseJ_energy_of_isResponseMaximizer U a 0 q u hmax
        (hInt.weakFlux u) (hInt.response 0 q u) (hInt.firstVariation 0 q u u)
        (hInt.energy u)
  linarith [hEnergy, hPairSplit, hJ]

/-- If the two scalar inputs are response maximizers, the half-pair witness has
block energy equal to one half of the sum of the corresponding response
values. -/
theorem blockEnergyAverage_blockResponsePairHalfState_eq_half_responseJ_sum_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q p' q' : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hmax : IsResponseMaximizer U p q a u)
    (hmaxAdj :
      IsResponseMaximizer U p' q' (Homogenization.adjointCoeffField a) v) :
    blockEnergyAverage U a (blockResponsePairHalfState a u v) =
      (1 / 2 : ℝ) * ResponseJ U p q a +
        (1 / 2 : ℝ) * ResponseJ U p' q' (Homogenization.adjointCoeffField a) := by
  have hEllAdj : IsEllipticFieldOn lam Lam U (Homogenization.adjointCoeffField a) :=
    isEllipticFieldOn_adjointCoeffField hEll
  have hInt := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hIntAdj := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEllAdj
  have henergy :=
    blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
      (a := a) hU hEll u v
  have hu :
      ResponseJ U p q a = (1 / 2 : ℝ) * volumeAverage U (scalarVariationEnergyIntegrand a u) :=
    responseJ_energy_of_isResponseMaximizer U a p q u hmax
      (hInt.weakFlux u) (hInt.response p q u) (hInt.firstVariation p q u u) (hInt.energy u)
  have hv :
      ResponseJ U p' q' (Homogenization.adjointCoeffField a) =
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarVariationEnergyIntegrand (Homogenization.adjointCoeffField a) v) :=
    responseJ_energy_of_isResponseMaximizer
      U (Homogenization.adjointCoeffField a) p' q' v hmaxAdj
      (hIntAdj.weakFlux v) (hIntAdj.response p' q' v) (hIntAdj.firstVariation p' q' v v)
      (hIntAdj.energy v)
  linarith [henergy, hu, hv]

/-- Scalar canonical maximizers feed the previous half-pair energy identity
without extra bookkeeping. -/
theorem blockEnergyAverage_blockResponsePairHalfState_eq_half_responseJ_sum_of_scalarCanonicalMaximizers_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q p' q' : Vec d)
    (u : ScalarCanonicalMaximizer U p q a)
    (v : ScalarCanonicalMaximizer U p' q' (Homogenization.adjointCoeffField a)) :
    blockEnergyAverage U a
        (blockResponsePairHalfState a
          (u : AHarmonicFunction a U)
          (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)) =
      (1 / 2 : ℝ) * ResponseJ U p q a +
        (1 / 2 : ℝ) * ResponseJ U p' q' (Homogenization.adjointCoeffField a) := by
  exact
    blockEnergyAverage_blockResponsePairHalfState_eq_half_responseJ_sum_of_isResponseMaximizer_of_isEllipticFieldOn
      (a := a) hU hEll p q p' q'
      (u := (u : AHarmonicFunction a U))
      (v := (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U))
      u.isResponseMaximizer v.isResponseMaximizer

theorem blockResponse_half_scalarResponse_sum_mem_blockJValueSet_of_isEllipticFieldOn_of_finiteMeasure
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v) ∈
      blockJValueSet U (p, q) (qStar, pStar) a := by
  exact
    blockResponse_half_scalarResponse_sum_mem_blockJValueSet_of_isEllipticFieldOn
      (a := a) hU hEll p pStar q qStar u v

theorem blockResponse_half_scalarResponse_sum_le_blockJ_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U) :
    (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
        (1 / 2 : ℝ) *
          volumeAverage U
            (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
              (pStar + p) (qStar + q) v) ≤
      BlockJ U (p, q) (qStar, pStar) a := by
  exact
    le_blockJ_of_mem_blockJValueSet_of_isEllipticFieldOn
      hU hEll hvol (p, q) (qStar, pStar)
      (blockResponse_half_scalarResponse_sum_mem_blockJValueSet_of_isEllipticFieldOn_of_finiteMeasure
        (a := a) hU hEll p pStar q qStar u v)

theorem blockResponse_half_responseJ_adjoint_sum_note_form_mem_blockJValueSet_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q h : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hmax : IsResponseMaximizer U p (q - h) a u)
    (hmaxAdj :
      IsResponseMaximizer U p (q + h) (Homogenization.adjointCoeffField a) v) :
    (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) ∈
      blockJValueSet U (p, h) (q, 0) a := by
  exact
    blockResponse_half_responseJ_adjoint_sum_note_form_mem_blockJValueSet_of_isResponseMaximizer
      (a := a) hU hEll p q h u v hmax hmaxAdj

theorem blockResponse_half_responseJ_adjoint_sum_le_blockJ_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hmax : IsResponseMaximizer U (p - pStar) (qStar - q) a u)
    (hmaxAdj :
      IsResponseMaximizer U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) v) :
    (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ≤
      BlockJ U (p, q) (qStar, pStar) a := by
  exact
    le_blockJ_of_mem_blockJValueSet_of_isEllipticFieldOn
      hU hEll hvol (p, q) (qStar, pStar)
      (blockResponse_half_responseJ_adjoint_sum_mem_blockJValueSet_of_isResponseMaximizer
        (a := a) hU hEll p pStar q qStar u v hmax hmaxAdj)

theorem blockResponse_half_responseJ_adjoint_sum_note_form_le_blockJ_of_isResponseMaximizer_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U)
    (hmax : IsResponseMaximizer U p (q - h) a u)
    (hmaxAdj :
      IsResponseMaximizer U p (q + h) (Homogenization.adjointCoeffField a) v) :
    (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) ≤
      BlockJ U (p, h) (q, 0) a := by
  have hmax' : IsResponseMaximizer U (p - 0) (q - h) a u := by
    simpa using hmax
  have hmaxAdj' :
      IsResponseMaximizer U (0 + p) (q + h) (Homogenization.adjointCoeffField a) v := by
    simpa using hmaxAdj
  simpa using
    blockResponse_half_responseJ_adjoint_sum_le_blockJ_of_isResponseMaximizer_of_isEllipticFieldOn
      (a := a) hU hEll hvol (p := p) (pStar := 0) (q := h) (qStar := q) u v
      hmax' hmaxAdj'

theorem blockResponse_half_responseJ_adjoint_sum_mem_blockJValueSet_of_scalarCanonicalMaximizer_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p pStar q qStar : Vec d)
    (u : ScalarCanonicalMaximizer U (p - pStar) (qStar - q) a)
    (v : ScalarCanonicalMaximizer U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a)) :
    (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ∈
      blockJValueSet U (p, q) (qStar, pStar) a := by
  exact
    blockResponse_half_responseJ_adjoint_sum_mem_blockJValueSet_of_isResponseMaximizer
      (a := a) hU hEll p pStar q qStar
      (u := (u : AHarmonicFunction a U))
      (v := (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U))
      u.isResponseMaximizer v.isResponseMaximizer

theorem blockResponse_half_responseJ_adjoint_sum_note_form_mem_blockJValueSet_of_scalarCanonicalMaximizer_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (p q h : Vec d)
    (u : ScalarCanonicalMaximizer U p (q - h) a)
    (v : ScalarCanonicalMaximizer U p (q + h) (Homogenization.adjointCoeffField a)) :
    (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) ∈
      blockJValueSet U (p, h) (q, 0) a := by
  exact
    blockResponse_half_responseJ_adjoint_sum_note_form_mem_blockJValueSet_of_isResponseMaximizer_of_isEllipticFieldOn
      (a := a) hU hEll p q h
      (u := (u : AHarmonicFunction a U))
      (v := (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U))
      u.isResponseMaximizer v.isResponseMaximizer

theorem blockResponse_half_responseJ_adjoint_sum_le_blockJ_of_scalarCanonicalMaximizer_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p pStar q qStar : Vec d)
    (u : ScalarCanonicalMaximizer U (p - pStar) (qStar - q) a)
    (v : ScalarCanonicalMaximizer U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a)) :
    (1 / 2 : ℝ) * ResponseJ U (p - pStar) (qStar - q) a +
        (1 / 2 : ℝ) *
          ResponseJ U (pStar + p) (qStar + q) (Homogenization.adjointCoeffField a) ≤
      BlockJ U (p, q) (qStar, pStar) a := by
  exact
    blockResponse_half_responseJ_adjoint_sum_le_blockJ_of_isResponseMaximizer_of_isEllipticFieldOn
      (a := a) hU hEll hvol p pStar q qStar
      (u := (u : AHarmonicFunction a U))
      (v := (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U))
      u.isResponseMaximizer v.isResponseMaximizer

theorem blockResponse_half_responseJ_adjoint_sum_note_form_le_blockJ_of_scalarCanonicalMaximizer_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} (a : CoeffField d) {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (p q h : Vec d)
    (u : ScalarCanonicalMaximizer U p (q - h) a)
    (v : ScalarCanonicalMaximizer U p (q + h) (Homogenization.adjointCoeffField a)) :
    (1 / 2 : ℝ) * ResponseJ U p (q - h) a +
        (1 / 2 : ℝ) *
          ResponseJ U p (q + h) (Homogenization.adjointCoeffField a) ≤
      BlockJ U (p, h) (q, 0) a := by
  exact
    blockResponse_half_responseJ_adjoint_sum_note_form_le_blockJ_of_isResponseMaximizer_of_isEllipticFieldOn
      (a := a) hU hEll hvol p q h
      (u := (u : AHarmonicFunction a U))
      (v := (v : AHarmonicFunction (Homogenization.adjointCoeffField a) U))
      u.isResponseMaximizer v.isResponseMaximizer


end

end Homogenization
