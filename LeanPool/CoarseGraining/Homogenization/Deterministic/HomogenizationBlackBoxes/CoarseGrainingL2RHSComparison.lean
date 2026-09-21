/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2Response
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization

/-! # Coarse Graining L2RHSComparison -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

private theorem descendantsAverage_sqrt_add_le_of_nonneg {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F G : TriadicCube d → ℝ)
    (hF : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ F R)
    (hG : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ G R) :
    Real.sqrt (descendantsAverage Q j (fun R => (F R + G R) ^ 2)) ≤
      Real.sqrt (descendantsAverage Q j (fun R => (F R) ^ 2)) +
        Real.sqrt (descendantsAverage Q j (fun R => (G R) ^ 2)) := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let c : ℝ := ((D.card : ℝ)⁻¹)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (by positivity)
  have hsumF_nonneg : 0 ≤ ∑ R ∈ D, (F R) ^ 2 :=
    Finset.sum_nonneg fun R _ => sq_nonneg _
  have hsumG_nonneg : 0 ≤ ∑ R ∈ D, (G R) ^ 2 :=
    Finset.sum_nonneg fun R _ => sq_nonneg _
  have hsumFG_nonneg : 0 ≤ ∑ R ∈ D, (F R + G R) ^ 2 :=
    Finset.sum_nonneg fun R _ => sq_nonneg _
  have hLp :
      (∑ R ∈ D, (F R + G R) ^ 2) ^ (1 / 2 : ℝ) ≤
        (∑ R ∈ D, (F R) ^ 2) ^ (1 / 2 : ℝ) +
          (∑ R ∈ D, (G R) ^ 2) ^ (1 / 2 : ℝ) := by
    simpa using
      (Real.Lp_add_le_of_nonneg
        (s := D) (f := F) (g := G) (p := (2 : ℝ))
        (by norm_num)
        (fun R hR => hF R (by simpa [D] using hR))
        (fun R hR => hG R (by simpa [D] using hR)))
  calc
    Real.sqrt (descendantsAverage Q j (fun R => (F R + G R) ^ 2))
        =
          c ^ (1 / 2 : ℝ) *
            (∑ R ∈ D, (F R + G R) ^ 2) ^ (1 / 2 : ℝ) := by
            have hmul :
                (c * ∑ R ∈ D, (F R + G R) ^ 2) ^ (1 / 2 : ℝ) =
                  c ^ (1 / 2 : ℝ) *
                    (∑ R ∈ D, (F R + G R) ^ 2) ^ (1 / 2 : ℝ) :=
              Real.mul_rpow hc hsumFG_nonneg
            simpa [Real.sqrt_eq_rpow, descendantsAverage, D, c] using hmul
    _ ≤
        c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (F R) ^ 2) ^ (1 / 2 : ℝ) +
          c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (G R) ^ 2) ^ (1 / 2 : ℝ) := by
          have hc_rpow : 0 ≤ c ^ (1 / 2 : ℝ) := Real.rpow_nonneg hc _
          simpa [mul_add] using mul_le_mul_of_nonneg_left hLp hc_rpow
    _ =
        Real.sqrt (descendantsAverage Q j (fun R => (F R) ^ 2)) +
          c ^ (1 / 2 : ℝ) * (∑ R ∈ D, (G R) ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← Real.mul_rpow hc hsumF_nonneg]
          simp [Real.sqrt_eq_rpow, descendantsAverage, D, c]
    _ =
        Real.sqrt (descendantsAverage Q j (fun R => (F R) ^ 2)) +
          Real.sqrt (descendantsAverage Q j (fun R => (G R) ^ 2)) := by
          rw [← Real.mul_rpow hc hsumG_nonneg]
          simp [Real.sqrt_eq_rpow, descendantsAverage, D, c]

private theorem sqrt_descendantsAverage_sq_le_mul_of_pointwise_le
    {d : ℕ} (Q : TriadicCube d) (j : ℕ) (F B : TriadicCube d → ℝ)
    {C A : ℝ}
    (hC_nonneg : 0 ≤ C) (hA_nonneg : 0 ≤ A)
    (hF_nonneg : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ F R)
    (hpoint : ∀ R ∈ descendantsAtDepth Q j, F R ≤ C * B R)
    (havg : descendantsAverage Q j (fun R => (B R) ^ 2) ≤ A ^ 2) :
    Real.sqrt (descendantsAverage Q j fun R => (F R) ^ 2) ≤ C * A := by
  have hsq :
      descendantsAverage Q j (fun R => (F R) ^ 2) ≤
        descendantsAverage Q j (fun R => (C * B R) ^ 2) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    exact pow_le_pow_left₀ (hF_nonneg R hR) (hpoint R hR) 2
  have hscaled :
      descendantsAverage Q j (fun R => (C * B R) ^ 2) =
        C ^ 2 * descendantsAverage Q j (fun R => (B R) ^ 2) := by
    calc
      descendantsAverage Q j (fun R => (C * B R) ^ 2)
          = descendantsAverage Q j (fun R => C ^ 2 * (B R) ^ 2) := by
              apply congrArg (descendantsAverage Q j)
              funext R
              ring
      _ = C ^ 2 * descendantsAverage Q j (fun R => (B R) ^ 2) :=
            descendantsAverage_mul_left Q j (C ^ 2) (fun R => (B R) ^ 2)
  have hinside :
      descendantsAverage Q j (fun R => (F R) ^ 2) ≤ C ^ 2 * A ^ 2 := by
    calc
      descendantsAverage Q j (fun R => (F R) ^ 2)
          ≤ descendantsAverage Q j (fun R => (C * B R) ^ 2) := hsq
      _ = C ^ 2 * descendantsAverage Q j (fun R => (B R) ^ 2) := hscaled
      _ ≤ C ^ 2 * A ^ 2 :=
            mul_le_mul_of_nonneg_left havg (sq_nonneg C)
  calc
    Real.sqrt (descendantsAverage Q j fun R => (F R) ^ 2)
        ≤ Real.sqrt (C ^ 2 * A ^ 2) := Real.sqrt_le_sqrt hinside
    _ = C * A := by
          rw [show C ^ 2 * A ^ 2 = (C * A) ^ 2 by ring,
            Real.sqrt_sq (mul_nonneg hC_nonneg hA_nonneg)]

/-- Localized descendant `L²` average of the §3.2.4 energy component. -/
noncomputable def localizedCoarseFluxResponseRHSEnergyBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU : Vec d → Vec d) : ℝ :=
  Real.sqrt
    (descendantsAverage Q j fun R =>
      (coarseFluxResponseRHSEnergyBound R a a0 s gradU) ^ 2)

/-- Localized descendant `L²` average of the §3.2.4 response correction. -/
noncomputable def localizedCoarseFluxResponseRHSResponseCorrectionBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (g : Vec d → Vec d) : ℝ :=
  Real.sqrt
    (descendantsAverage Q j fun R =>
      (coarseFluxResponseRHSResponseCorrectionBound R a a0 s g) ^ 2)

/-- Localized descendant `L²` average of the §3.2.4 weak-flux correction. -/
noncomputable def localizedCoarseFluxResponseRHSWeakFluxCorrectionBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (j : ℕ) (g : Vec d → Vec d) : ℝ :=
  Real.sqrt
    (descendantsAverage Q j fun R =>
      (coarseFluxResponseRHSWeakFluxCorrectionBound R a s g) ^ 2)

/-- Localized descendant `L²` average of the §3.2.4 Poincare correction. -/
noncomputable def localizedCoarseFluxResponseRHSPoincareCorrectionBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (g : Vec d → Vec d) : ℝ :=
  Real.sqrt
    (descendantsAverage Q j fun R =>
      (coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g) ^ 2)

/--
The localized `L²` average of the §3.2.4 RHS energy component is controlled
by the parent-cube energy term in the §3.3.B flux-defect RHS.
-/
theorem localizedCoarseFluxResponseRHSEnergyBound_le_coarseGrainingL2FluxDefectEnergyTerm
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU : Vec d → Vec d)
    (hs : 0 < s)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume)
    (henergy_avg_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ cubeAverage R (coefficientEnergyDensity a gradU)) :
    localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤
      coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU := by
  let energy : Vec d → ℝ := coefficientEnergyDensity a gradU
  let E : ℝ := coarseGrainingHomogenizationErrorAtDepth Q a a0 s j
  let C : ℝ := s⁻¹ * Real.sqrt (matNorm a0) * E
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hsqrt_mat_nonneg : 0 ≤ Real.sqrt (matNorm a0) := Real.sqrt_nonneg _
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 j hs.le
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hs_inv_nonneg hsqrt_mat_nonneg) hE_nonneg
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        (coarseFluxResponseRHSEnergyBound R a a0 s gradU) ^ 2 ≤
          C ^ 2 * cubeAverage R energy := by
    intro R hR
    let ER : ℝ := HomogenizationErrorOnCube R s .infinity (.finite 1) a a0
    have hER_nonneg : 0 ≤ ER := by
      dsimp [ER]
      exact homogenizationErrorOnCube_infinity_one_nonneg R a a0 hs.le
    have hER_le : ER ≤ E := by
      dsimp [ER, E]
      exact homogenizationErrorOnCube_le_coarseGrainingHomogenizationErrorAtDepth hR
    have hA_nonneg : 0 ≤ cubeAverage R energy :=
      henergy_avg_nonneg R hR
    have hsqrtA_nonneg : 0 ≤ Real.sqrt (cubeAverage R energy) :=
      Real.sqrt_nonneg _
    have hbase_nonneg : 0 ≤ s⁻¹ * Real.sqrt (matNorm a0) * ER :=
      mul_nonneg (mul_nonneg hs_inv_nonneg hsqrt_mat_nonneg) hER_nonneg
    have hbase_le : s⁻¹ * Real.sqrt (matNorm a0) * ER ≤ C := by
      have hleft :
          s⁻¹ * Real.sqrt (matNorm a0) * ER ≤
            s⁻¹ * Real.sqrt (matNorm a0) * E := by
        exact mul_le_mul_of_nonneg_left hER_le
          (mul_nonneg hs_inv_nonneg hsqrt_mat_nonneg)
      simpa [C] using hleft
    have hterm_nonneg :
        0 ≤ coarseFluxResponseRHSEnergyBound R a a0 s gradU :=
      coarseFluxResponseRHSEnergyBound_nonneg R a a0 gradU hs
    have hterm_le :
        coarseFluxResponseRHSEnergyBound R a a0 s gradU ≤
          C * Real.sqrt (cubeAverage R energy) := by
      calc
        coarseFluxResponseRHSEnergyBound R a a0 s gradU
            =
          (s⁻¹ * Real.sqrt (matNorm a0) * ER) *
            Real.sqrt (cubeAverage R energy) := by
              unfold coarseFluxResponseRHSEnergyBound
              simp [ER, energy]
        _ ≤ C * Real.sqrt (cubeAverage R energy) := by
              exact mul_le_mul_of_nonneg_right hbase_le hsqrtA_nonneg
    have hsquare := pow_le_pow_left₀ hterm_nonneg hterm_le 2
    calc
      (coarseFluxResponseRHSEnergyBound R a a0 s gradU) ^ 2
          ≤ (C * Real.sqrt (cubeAverage R energy)) ^ 2 := hsquare
      _ = C ^ 2 * cubeAverage R energy := by
            rw [mul_pow, Real.sq_sqrt hA_nonneg]
  have havg_sq :
      descendantsAverage Q j
          (fun R => (coarseFluxResponseRHSEnergyBound R a a0 s gradU) ^ 2) ≤
        descendantsAverage Q j (fun R => C ^ 2 * cubeAverage R energy) := by
    refine descendantsAverage_le_descendantsAverage Q j ?_
    intro R hR
    exact hpoint R hR
  have hconst :
      descendantsAverage Q j (fun R => C ^ 2 * cubeAverage R energy) =
        C ^ 2 * descendantsAverage Q j (fun R => cubeAverage R energy) :=
    descendantsAverage_mul_left Q j (C ^ 2) (fun R => cubeAverage R energy)
  have havg_eq :
      descendantsAverage Q j (fun R => cubeAverage R energy) =
        cubeAverage Q energy := by
    symm
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q j energy henergy_int
  have hinside :
      descendantsAverage Q j
          (fun R => (coarseFluxResponseRHSEnergyBound R a a0 s gradU) ^ 2) ≤
        C ^ 2 * cubeAverage Q energy := by
    calc
      descendantsAverage Q j
          (fun R => (coarseFluxResponseRHSEnergyBound R a a0 s gradU) ^ 2)
          ≤ descendantsAverage Q j (fun R => C ^ 2 * cubeAverage R energy) :=
            havg_sq
      _ = C ^ 2 * descendantsAverage Q j (fun R => cubeAverage R energy) :=
            hconst
      _ = C ^ 2 * cubeAverage Q energy := by rw [havg_eq]
  calc
    localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU
        ≤ Real.sqrt (C ^ 2 * cubeAverage Q energy) := by
          exact Real.sqrt_le_sqrt hinside
    _ = C * Real.sqrt (cubeAverage Q energy) := by
          rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC_nonneg]
    _ = coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU := by
          simp [coarseGrainingL2FluxDefectEnergyTerm, C, E, energy]

/--
Ellipticity-facing version of
`localizedCoarseFluxResponseRHSEnergyBound_le_coarseGrainingL2FluxDefectEnergyTerm`.
-/
theorem localizedCoarseFluxResponseRHSEnergyBound_le_coarseGrainingL2FluxDefectEnergyTerm_of_isEllipticFieldOn
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU : Vec d → Vec d) {lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume) :
    localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤
      coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU :=
  localizedCoarseFluxResponseRHSEnergyBound_le_coarseGrainingL2FluxDefectEnergyTerm
    Q a a0 j gradU hs henergy_int
    (fun R hR =>
      cubeAverage_nonneg_of_nonneg_on (Q := R)
        (fun x hx =>
          coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll gradU x
            (cubeSet_subset_of_mem_descendantsAtDepth hR hx)))

/--
Square-average wrapper for the localized response-correction component.  The
analytic inputs are a pointwise coefficient bound and the parent-scale
localized positive-Besov square estimate.
-/
theorem localizedCoarseFluxResponseRHSResponseCorrectionBound_le_mul_of_pointwise_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d) {C A : ℝ}
    (hC_nonneg : 0 ≤ C) (hA_nonneg : 0 ≤ A)
    (hcomponent_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          C * cubeBesovPositiveVectorSeminormTwo R s g)
    (havg :
      descendantsAverage Q j
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        A ^ 2) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g ≤
      C * A := by
  simpa [localizedCoarseFluxResponseRHSResponseCorrectionBound] using
    sqrt_descendantsAverage_sq_le_mul_of_pointwise_le Q j
      (fun R => coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
      (fun R => cubeBesovPositiveVectorSeminormTwo R s g)
      hC_nonneg hA_nonneg hcomponent_nonneg hpoint havg

/--
Square-average wrapper for the localized weak-flux correction component.
-/
theorem localizedCoarseFluxResponseRHSWeakFluxCorrectionBound_le_mul_of_pointwise_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d) {C A : ℝ}
    (hC_nonneg : 0 ≤ C) (hA_nonneg : 0 ≤ A)
    (hcomponent_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          C * cubeBesovPositiveVectorSeminormTwo R s g)
    (havg :
      descendantsAverage Q j
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        A ^ 2) :
    localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g ≤
      C * A := by
  simpa [localizedCoarseFluxResponseRHSWeakFluxCorrectionBound] using
    sqrt_descendantsAverage_sq_le_mul_of_pointwise_le Q j
      (fun R => coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
      (fun R => cubeBesovPositiveVectorSeminormTwo R s g)
      hC_nonneg hA_nonneg hcomponent_nonneg hpoint havg

/--
Square-average wrapper for the localized Poincare correction component.
-/
theorem localizedCoarseFluxResponseRHSPoincareCorrectionBound_le_mul_of_pointwise_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d) {C A : ℝ}
    (hC_nonneg : 0 ≤ C) (hA_nonneg : 0 ≤ A)
    (hcomponent_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          C * cubeBesovPositiveVectorSeminormTwo R s g)
    (havg :
      descendantsAverage Q j
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        A ^ 2) :
    localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      C * A := by
  simpa [localizedCoarseFluxResponseRHSPoincareCorrectionBound] using
    sqrt_descendantsAverage_sq_le_mul_of_pointwise_le Q j
      (fun R => coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
      (fun R => cubeBesovPositiveVectorSeminormTwo R s g)
      hC_nonneg hA_nonneg hcomponent_nonneg hpoint havg

/--
Component-average forcing correction bound with the descendant-localized
positive-Besov forcing norm kept visible.
-/
theorem localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_localizedPositiveBesovForcing_of_pointwise_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d) {C₁ C₂ C₃ : ℝ}
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hC₃_nonneg : 0 ≤ C₃)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          C₁ * cubeBesovPositiveVectorSeminormTwo R s g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          C₂ * cubeBesovPositiveVectorSeminormTwo R s g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          C₃ * cubeBesovPositiveVectorSeminormTwo R s g) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      (C₁ + C₂ + C₃) *
        localizedPositiveBesovForcingSeminormTwoAtDepth Q s j g := by
  let A : ℝ := localizedPositiveBesovForcingSeminormTwoAtDepth Q s j g
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, localizedPositiveBesovForcingSeminormTwoAtDepth]
    exact Real.sqrt_nonneg _
  have havg_nonneg :
      0 ≤ descendantsAverage Q j
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) :=
    descendantsAverage_nonneg Q j _
      (fun R _ => sq_nonneg (cubeBesovPositiveVectorSeminormTwo R s g))
  have havg :
      descendantsAverage Q j
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        A ^ 2 := by
    dsimp [A, localizedPositiveBesovForcingSeminormTwoAtDepth]
    rw [Real.sq_sqrt havg_nonneg]
  have hresponse :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g ≤
        C₁ * A := by
    exact
      localizedCoarseFluxResponseRHSResponseCorrectionBound_le_mul_of_pointwise_le
        Q a a0 j g hC₁_nonneg hA_nonneg hresponse_nonneg
        hresponse_point havg
  have hweak :
      localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g ≤
        C₂ * A := by
    exact
      localizedCoarseFluxResponseRHSWeakFluxCorrectionBound_le_mul_of_pointwise_le
        Q a j g hC₂_nonneg hA_nonneg hweak_nonneg hweak_point havg
  have hpoincare :
      localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        C₃ * A := by
    exact
      localizedCoarseFluxResponseRHSPoincareCorrectionBound_le_mul_of_pointwise_le
        Q a a0 j g hC₃_nonneg hA_nonneg hpoincare_nonneg
        hpoincare_point havg
  calc
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g
        ≤ C₁ * A + C₂ * A + C₃ * A := by
          linarith
    _ = (C₁ + C₂ + C₃) * A := by ring

/--
Component-average forcing correction bound with the inverse depth weight
exposed after applying positive-Besov localization.
-/
theorem localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_depthWeight_inv_mul_parent_of_pointwise_le_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d) {C₁ C₂ C₃ : ℝ}
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hC₃_nonneg : 0 ≤ C₃)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          C₁ * cubeBesovPositiveVectorSeminormTwo R s g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          C₂ * cubeBesovPositiveVectorSeminormTwo R s g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          C₃ * cubeBesovPositiveVectorSeminormTwo R s g) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      (C₁ + C₂ + C₃) *
        ((Real.rpow (3 : ℝ) (s * (j : ℝ)))⁻¹ *
          cubeBesovPositiveVectorSeminormTwo Q s g) := by
  let A : ℝ := localizedPositiveBesovForcingSeminormTwoAtDepth Q s j g
  have hcoeff_nonneg : 0 ≤ C₁ + C₂ + C₃ := by
    linarith
  have hlocal :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
          localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
          localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        (C₁ + C₂ + C₃) * A :=
    localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_localizedPositiveBesovForcing_of_pointwise_le
      Q a a0 j g hC₁_nonneg hC₂_nonneg hC₃_nonneg hresponse_nonneg
      hweak_nonneg hpoincare_nonneg hresponse_point hweak_point
      hpoincare_point
  have hA :
      A ≤
        (Real.rpow (3 : ℝ) (s * (j : ℝ)))⁻¹ *
          cubeBesovPositiveVectorSeminormTwo Q s g := by
    dsimp [A]
    exact
      localizedPositiveBesovForcingSeminormTwoAtDepth_le_depthWeight_inv_mul_parent_of_bddAbove
        Q g s j hGlobalBdd hLocalBdd
  exact hlocal.trans (mul_le_mul_of_nonneg_left hA hcoeff_nonneg)

/--
Two-exponent component-average forcing correction bound.  The flux-response
components are evaluated at exponent `s`, while the force is measured in the
stronger positive-Besov seminorm at exponent `t`.
-/
theorem localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_localizedPositiveBesovForcing_forceExponent_of_pointwise_le
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s t : ℝ} (j : ℕ) (g : Vec d → Vec d) {C₁ C₂ C₃ : ℝ}
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hC₃_nonneg : 0 ≤ C₃)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          C₁ * cubeBesovPositiveVectorSeminormTwo R t g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          C₂ * cubeBesovPositiveVectorSeminormTwo R t g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          C₃ * cubeBesovPositiveVectorSeminormTwo R t g) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      (C₁ + C₂ + C₃) *
        localizedPositiveBesovForcingSeminormTwoAtDepth Q t j g := by
  let A : ℝ := localizedPositiveBesovForcingSeminormTwoAtDepth Q t j g
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, localizedPositiveBesovForcingSeminormTwoAtDepth]
    exact Real.sqrt_nonneg _
  have havg_nonneg :
      0 ≤ descendantsAverage Q j
        (fun R => (cubeBesovPositiveVectorSeminormTwo R t g) ^ 2) :=
    descendantsAverage_nonneg Q j _
      (fun R _ => sq_nonneg (cubeBesovPositiveVectorSeminormTwo R t g))
  have havg :
      descendantsAverage Q j
          (fun R => (cubeBesovPositiveVectorSeminormTwo R t g) ^ 2) ≤
        A ^ 2 := by
    dsimp [A, localizedPositiveBesovForcingSeminormTwoAtDepth]
    rw [Real.sq_sqrt havg_nonneg]
  have hresponse :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g ≤
        C₁ * A := by
    simpa [localizedCoarseFluxResponseRHSResponseCorrectionBound] using
      sqrt_descendantsAverage_sq_le_mul_of_pointwise_le Q j
        (fun R => coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
        (fun R => cubeBesovPositiveVectorSeminormTwo R t g)
        hC₁_nonneg hA_nonneg hresponse_nonneg hresponse_point havg
  have hweak :
      localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g ≤
        C₂ * A := by
    simpa [localizedCoarseFluxResponseRHSWeakFluxCorrectionBound] using
      sqrt_descendantsAverage_sq_le_mul_of_pointwise_le Q j
        (fun R => coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
        (fun R => cubeBesovPositiveVectorSeminormTwo R t g)
        hC₂_nonneg hA_nonneg hweak_nonneg hweak_point havg
  have hpoincare :
      localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        C₃ * A := by
    simpa [localizedCoarseFluxResponseRHSPoincareCorrectionBound] using
      sqrt_descendantsAverage_sq_le_mul_of_pointwise_le Q j
        (fun R => coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
        (fun R => cubeBesovPositiveVectorSeminormTwo R t g)
        hC₃_nonneg hA_nonneg hpoincare_nonneg hpoincare_point havg
  calc
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g
        ≤ C₁ * A + C₂ * A + C₃ * A := by
          linarith
    _ = (C₁ + C₂ + C₃) * A := by ring

/--
Two-exponent component-average forcing correction bound with the inverse
depth weight exposed at the force exponent.
-/
theorem localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_depthWeight_inv_mul_parent_forceExponent_of_pointwise_le_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s t : ℝ} (j : ℕ) (g : Vec d → Vec d) {C₁ C₂ C₃ : ℝ}
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hC₃_nonneg : 0 ≤ C₃)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q t N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R t N g))
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          C₁ * cubeBesovPositiveVectorSeminormTwo R t g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          C₂ * cubeBesovPositiveVectorSeminormTwo R t g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          C₃ * cubeBesovPositiveVectorSeminormTwo R t g) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      (C₁ + C₂ + C₃) *
        ((Real.rpow (3 : ℝ) (t * (j : ℝ)))⁻¹ *
          cubeBesovPositiveVectorSeminormTwo Q t g) := by
  let A : ℝ := localizedPositiveBesovForcingSeminormTwoAtDepth Q t j g
  have hcoeff_nonneg : 0 ≤ C₁ + C₂ + C₃ := by
    linarith
  have hlocal :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
          localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
          localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        (C₁ + C₂ + C₃) * A :=
    localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_localizedPositiveBesovForcing_forceExponent_of_pointwise_le
      Q a a0 j g hC₁_nonneg hC₂_nonneg hC₃_nonneg hresponse_nonneg
      hweak_nonneg hpoincare_nonneg hresponse_point hweak_point
      hpoincare_point
  have hA :
      A ≤
        (Real.rpow (3 : ℝ) (t * (j : ℝ)))⁻¹ *
          cubeBesovPositiveVectorSeminormTwo Q t g := by
    dsimp [A]
    exact
      localizedPositiveBesovForcingSeminormTwoAtDepth_le_depthWeight_inv_mul_parent_of_bddAbove
        Q g t j hGlobalBdd hLocalBdd
  exact hlocal.trans (mul_le_mul_of_nonneg_left hA hcoeff_nonneg)

/--
The three localized forcing-correction averages are absorbed by the §3.3.B
forcing term once their pointwise descendant coefficients are bounded by the
corresponding parent coefficients and the local positive-Besov squares average
back to the parent seminorm.
-/
theorem localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coarseGrainingL2FluxDefectForcingTerm_of_pointwise_parent_coeff_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d)
    (hs : 0 < s)
    (hB_nonneg : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g)
    (havg :
      descendantsAverage Q j
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
              Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
              Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
              coarseGrainingHomogenizationErrorAtDepth Q a a0 s j) *
            cubeBesovPositiveVectorSeminormTwo R s g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          (Real.rpow s (-(5 / 2 : ℝ)) *
              Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
              Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
            cubeBesovPositiveVectorSeminormTwo R s g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          (Real.rpow s (-3 : ℝ) *
              Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
            cubeBesovPositiveVectorSeminormTwo R s g) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g := by
  let C₁ : ℝ :=
    Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
      Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
      coarseGrainingHomogenizationErrorAtDepth Q a a0 s j
  let C₂ : ℝ :=
    Real.rpow s (-(5 / 2 : ℝ)) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
      Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)
  let C₃ : ℝ :=
    Real.rpow s (-3 : ℝ) *
      Real.rpow (3 : ℝ) (s * (j : ℝ)) *
      matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  have hE_nonneg :
      0 ≤ coarseGrainingHomogenizationErrorAtDepth Q a a0 s j :=
    coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 j hs.le
  have hLambda_nonneg :
      0 ≤ LambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith)
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith)
  have hs_rpow_five_half_nonneg : 0 ≤ Real.rpow s (-(5 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have hs_rpow_three_nonneg : 0 ≤ Real.rpow s (-3 : ℝ) :=
    Real.rpow_nonneg hs.le _
  have hpow_half_nonneg :
      0 ≤ Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hpow_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (s * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hlambda_inv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  have hlambda_inv_sqrt_nonneg :
      0 ≤ Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) :=
    Real.sqrt_nonneg _
  have hC₁_nonneg : 0 ≤ C₁ := by
    dsimp [C₁]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hs_rpow_five_half_nonneg (Real.sqrt_nonneg _))
            hpow_half_nonneg)
          hlambda_inv_sqrt_nonneg)
        hE_nonneg
  have hC₂_nonneg : 0 ≤ C₂ := by
    dsimp [C₂]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg hs_rpow_five_half_nonneg hpow_nonneg)
          (Real.sqrt_nonneg _))
        hlambda_inv_sqrt_nonneg
  have hC₃_nonneg : 0 ≤ C₃ := by
    dsimp [C₃]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg hs_rpow_three_nonneg hpow_nonneg)
          (matNorm_nonneg a0))
        hlambda_inv_nonneg
  have hresponse :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g ≤
        C₁ * cubeBesovPositiveVectorSeminormTwo Q s g := by
    exact
      localizedCoarseFluxResponseRHSResponseCorrectionBound_le_mul_of_pointwise_le
        Q a a0 j g hC₁_nonneg hB_nonneg hresponse_nonneg
        (by simpa [C₁] using hresponse_point) havg
  have hweak :
      localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g ≤
        C₂ * cubeBesovPositiveVectorSeminormTwo Q s g := by
    exact
      localizedCoarseFluxResponseRHSWeakFluxCorrectionBound_le_mul_of_pointwise_le
        Q a j g hC₂_nonneg hB_nonneg hweak_nonneg
        (by simpa [C₂] using hweak_point) havg
  have hpoincare :
      localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        C₃ * cubeBesovPositiveVectorSeminormTwo Q s g := by
    exact
      localizedCoarseFluxResponseRHSPoincareCorrectionBound_le_mul_of_pointwise_le
        Q a a0 j g hC₃_nonneg hB_nonneg hpoincare_nonneg
        (by simpa [C₃] using hpoincare_point) havg
  calc
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g
        ≤
      C₁ * cubeBesovPositiveVectorSeminormTwo Q s g +
        C₂ * cubeBesovPositiveVectorSeminormTwo Q s g +
        C₃ * cubeBesovPositiveVectorSeminormTwo Q s g := by
          linarith
    _ = coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g := by
          simp [coarseGrainingL2FluxDefectForcingTerm, C₁, C₂, C₃]
          ring

/--
Bounded-positive-Besov version of
`localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coarseGrainingL2FluxDefectForcingTerm_of_pointwise_parent_coeff_bounds`.
-/
theorem localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coarseGrainingL2FluxDefectForcingTerm_of_pointwise_parent_coeff_bounds_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (g : Vec d → Vec d)
    (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          (Real.rpow s (-(5 / 2 : ℝ)) * Real.sqrt (matNorm a0) *
              Real.rpow (3 : ℝ) ((s / 2) * (j : ℝ)) *
              Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
              coarseGrainingHomogenizationErrorAtDepth Q a a0 s j) *
            cubeBesovPositiveVectorSeminormTwo R s g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          (Real.rpow s (-(5 / 2 : ℝ)) *
              Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              Real.sqrt (LambdaSq Q (s / 2) (.finite 2) a) *
              Real.sqrt ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
            cubeBesovPositiveVectorSeminormTwo R s g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          (Real.rpow s (-3 : ℝ) *
              Real.rpow (3 : ℝ) (s * (j : ℝ)) *
              matNorm a0 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) *
            cubeBesovPositiveVectorSeminormTwo R s g) :
    localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
      coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g :=
  localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coarseGrainingL2FluxDefectForcingTerm_of_pointwise_parent_coeff_bounds
    Q a a0 j g hs
    (cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hgBdd)
    (descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_parent_of_bddAbove
      Q g j hs.le hgBdd hgBdd_desc)
    (fun R hR =>
      coarseFluxResponseRHSResponseCorrectionBound_nonneg_of_bddAbove
        R a a0 g hs (hgBdd_desc R hR))
    (fun R hR =>
      coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
        R a g hs (hgBdd_desc R hR))
    (fun R hR =>
      coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
        R a a0 g hs (hgBdd_desc R hR))
    hresponse_point hweak_point hpoincare_point

/--
Minkowski split of the localized one-cube §3.2.4 RHS average into its four
component averages.
-/
theorem localizedCoarseFluxResponseRHSBound_le_component_average_sum
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d)
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSEnergyBound R a a0 s gradU)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU +
        localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
        localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g := by
  let E : TriadicCube d → ℝ := fun R =>
    coarseFluxResponseRHSEnergyBound R a a0 s gradU
  let C₁ : TriadicCube d → ℝ := fun R =>
    coarseFluxResponseRHSResponseCorrectionBound R a a0 s g
  let C₂ : TriadicCube d → ℝ := fun R =>
    coarseFluxResponseRHSWeakFluxCorrectionBound R a s g
  let C₃ : TriadicCube d → ℝ := fun R =>
    coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g
  have hRhs_eq :
      localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g =
        Real.sqrt (descendantsAverage Q j fun R => (E R + (C₁ R + (C₂ R + C₃ R))) ^ 2) := by
    unfold localizedCoarseFluxResponseRHSBound
    apply congrArg Real.sqrt
    apply congrArg (descendantsAverage Q j)
    funext R
    rw [coarseFluxResponseRHSBound_eq_component_sum]
    ring
  have htail_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ C₁ R + (C₂ R + C₃ R) := by
    intro R hR
    exact add_nonneg (hresponse_nonneg R hR)
      (add_nonneg (hweak_nonneg R hR) (hpoincare_nonneg R hR))
  have htail₂_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, 0 ≤ C₂ R + C₃ R := by
    intro R hR
    exact add_nonneg (hweak_nonneg R hR) (hpoincare_nonneg R hR)
  have hmain :
      localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
        localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU +
          Real.sqrt (descendantsAverage Q j fun R => (C₁ R + (C₂ R + C₃ R)) ^ 2) := by
    rw [hRhs_eq]
    simpa [localizedCoarseFluxResponseRHSEnergyBound, E] using
      descendantsAverage_sqrt_add_le_of_nonneg Q j E
        (fun R => C₁ R + (C₂ R + C₃ R))
        (by intro R hR; exact henergy_nonneg R hR) htail_nonneg
  have htail :
      Real.sqrt (descendantsAverage Q j fun R => (C₁ R + (C₂ R + C₃ R)) ^ 2) ≤
        localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
          Real.sqrt (descendantsAverage Q j fun R => (C₂ R + C₃ R) ^ 2) := by
    simpa [localizedCoarseFluxResponseRHSResponseCorrectionBound, C₁] using
      descendantsAverage_sqrt_add_le_of_nonneg Q j C₁ (fun R => C₂ R + C₃ R)
        (by intro R hR; exact hresponse_nonneg R hR) htail₂_nonneg
  have htail₂ :
      Real.sqrt (descendantsAverage Q j fun R => (C₂ R + C₃ R) ^ 2) ≤
        localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
          localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g := by
    simpa [localizedCoarseFluxResponseRHSWeakFluxCorrectionBound,
      localizedCoarseFluxResponseRHSPoincareCorrectionBound, C₂, C₃] using
      descendantsAverage_sqrt_add_le_of_nonneg Q j C₂ C₃
        (by intro R hR; exact hweak_nonneg R hR)
        (by intro R hR; exact hpoincare_nonneg R hR)
  linarith

/--
Generic recomposition of the localized one-cube RHS average from an energy
bound and a forcing-correction bound.
-/
theorem localizedCoarseFluxResponseRHSBound_le_energy_add_forcing_of_component_average_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d) {E F : ℝ}
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSEnergyBound R a a0 s gradU)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (henergy :
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤ E)
    (hforcing :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
          localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
          localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤ F) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤ E + F := by
  have hsplit :=
    localizedCoarseFluxResponseRHSBound_le_component_average_sum
      Q a a0 j gradU g henergy_nonneg hresponse_nonneg hweak_nonneg
      hpoincare_nonneg
  linarith

/--
Scale-sharp localized RHS comparison with an arbitrary nonnegative descendant
coefficient envelope for the three forcing correction components.
-/
theorem localizedCoarseFluxResponseRHSBound_le_energy_add_coeffSum_mul_depthWeight_inv_mul_parent_of_pointwise_le_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d) {E C₁ C₂ C₃ : ℝ}
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hC₃_nonneg : 0 ≤ C₃)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSEnergyBound R a a0 s gradU)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (henergy :
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤ E)
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          C₁ * cubeBesovPositiveVectorSeminormTwo R s g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          C₂ * cubeBesovPositiveVectorSeminormTwo R s g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          C₃ * cubeBesovPositiveVectorSeminormTwo R s g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      E +
        (C₁ + C₂ + C₃) *
          ((Real.rpow (3 : ℝ) (s * (j : ℝ)))⁻¹ *
            cubeBesovPositiveVectorSeminormTwo Q s g) := by
  refine
    localizedCoarseFluxResponseRHSBound_le_energy_add_forcing_of_component_average_bounds
      Q a a0 j gradU g henergy_nonneg hresponse_nonneg hweak_nonneg
      hpoincare_nonneg henergy ?_
  exact
    localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_depthWeight_inv_mul_parent_of_pointwise_le_of_bddAbove
      Q a a0 j g hC₁_nonneg hC₂_nonneg hC₃_nonneg hGlobalBdd
      hLocalBdd hresponse_nonneg hweak_nonneg hpoincare_nonneg
      hresponse_point hweak_point hpoincare_point

/--
Two-exponent scale-sharp localized RHS comparison with an arbitrary
nonnegative descendant coefficient envelope for the forcing correction
components.
-/
theorem localizedCoarseFluxResponseRHSBound_le_energy_add_coeffSum_mul_depthWeight_inv_mul_parent_forceExponent_of_pointwise_le_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s t : ℝ} (j : ℕ) (gradU g : Vec d → Vec d) {E C₁ C₂ C₃ : ℝ}
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hC₃_nonneg : 0 ≤ C₃)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q t N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R t N g))
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSEnergyBound R a a0 s gradU)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (henergy :
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤ E)
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          C₁ * cubeBesovPositiveVectorSeminormTwo R t g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          C₂ * cubeBesovPositiveVectorSeminormTwo R t g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          C₃ * cubeBesovPositiveVectorSeminormTwo R t g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      E +
        (C₁ + C₂ + C₃) *
          ((Real.rpow (3 : ℝ) (t * (j : ℝ)))⁻¹ *
            cubeBesovPositiveVectorSeminormTwo Q t g) := by
  refine
    localizedCoarseFluxResponseRHSBound_le_energy_add_forcing_of_component_average_bounds
      Q a a0 j gradU g henergy_nonneg hresponse_nonneg hweak_nonneg
      hpoincare_nonneg henergy ?_
  exact
    localizedCoarseFluxResponseRHSForcingCorrectionBound_le_coeffSum_mul_depthWeight_inv_mul_parent_forceExponent_of_pointwise_le_of_bddAbove
      Q a a0 j g hC₁_nonneg hC₂_nonneg hC₃_nonneg hGlobalBdd
      hLocalBdd hresponse_nonneg hweak_nonneg hpoincare_nonneg
      hresponse_point hweak_point hpoincare_point

/--
End-to-end localized comparison corridor with the scale-sharp forcing
localization kept in the final scalar bound.
-/
theorem solution_diff_l2_le_dualityConstant_mul_energy_add_coeffSum_mul_depthWeight_inv_mul_parent_of_descendant_coarseFluxResponseRHSBound_of_pointwise_le_of_bddAbove
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 E C₁ C₂ C₃ : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (_ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (_ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g)
    (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hC₃_nonneg : 0 ≤ C₃)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (henergy :
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤ E)
    (hresponse_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g ≤
          C₁ * cubeBesovPositiveVectorSeminormTwo R s g)
    (hweak_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSWeakFluxCorrectionBound R a s g ≤
          C₂ * cubeBesovPositiveVectorSeminormTwo R s g)
    (hpoincare_point :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          C₃ * cubeBesovPositiveVectorSeminormTwo R s g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      Cdual * s⁻¹ *
        (E +
          (C₁ + C₂ + C₃) *
            ((Real.rpow (3 : ℝ) (s * (j : ℝ)))⁻¹ *
              cubeBesovPositiveVectorSeminormTwo Q s g)) := by
  subst a0
  have hflux :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j ≤
        E +
          (C₁ + C₂ + C₃) *
            ((Real.rpow (3 : ℝ) (s * (j : ℝ)))⁻¹ *
              cubeBesovPositiveVectorSeminormTwo Q s g) := by
    calc
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j
          ≤ localizedCoarseFluxResponseRHSBound Q a
              (scalarMatrix (d := d) sigma0) s j gradU g :=
            localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_localizedCoarseFluxResponseRHSBound_of_descendant_bounds
              Q a (scalarMatrix (d := d) sigma0) s gradU g j hdefect_bdd hRhs
      _ ≤
        E +
          (C₁ + C₂ + C₃) *
            ((Real.rpow (3 : ℝ) (s * (j : ℝ)))⁻¹ *
              cubeBesovPositiveVectorSeminormTwo Q s g) :=
          localizedCoarseFluxResponseRHSBound_le_energy_add_coeffSum_mul_depthWeight_inv_mul_parent_of_pointwise_le_of_bddAbove
            Q a (scalarMatrix (d := d) sigma0) j gradU g hC₁_nonneg hC₂_nonneg
            hC₃_nonneg hGlobalBdd hLocalBdd
            (fun R _ =>
              coarseFluxResponseRHSEnergyBound_nonneg R a
                (scalarMatrix (d := d) sigma0) gradU hs_pos)
            (fun R hR =>
              coarseFluxResponseRHSResponseCorrectionBound_nonneg_of_bddAbove
                R a (scalarMatrix (d := d) sigma0) g hs_pos (hLocalBdd R hR))
            (fun R hR =>
              coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
                R a g hs_pos (hLocalBdd R hR))
            (fun R hR =>
              coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
                R a (scalarMatrix (d := d) sigma0) g hs_pos (hLocalBdd R hR))
            henergy hresponse_point hweak_point hpoincare_point
  exact
    solution_diff_l2_le_dualityConstant_mul_fluxDefectBound_of_localizedFluxDefect_le
      hdual Q a sigma0 gradU gradV j hsigma0 hs_pos hs_lt_one hEll
      hcomparison hflux

/--
Scalar §3.3 RHS comparison from localized component-average bounds.  This is
the `L²` version of the component-envelope bridge, and is weaker than asking
for pointwise descendant domination.
-/
theorem localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_component_average_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d)
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSEnergyBound R a a0 s gradU)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (henergy :
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤
        coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU)
    (hforcing :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
          localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
          localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g := by
  have hsplit :=
    localizedCoarseFluxResponseRHSBound_le_component_average_sum
      Q a a0 j gradU g henergy_nonneg hresponse_nonneg hweak_nonneg
      hpoincare_nonneg
  rw [coarseGrainingL2FluxDefectBound_eq_energyTerm_add_forcingTerm]
  linarith

/--
Bounded-positive-Besov version of the localized component-average scalar
comparison.
-/
theorem localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_component_average_bounds_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d)
    (hs : 0 < s)
    (hgBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (henergy :
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤
        coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU)
    (hforcing :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
          localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
          localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
  localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_component_average_bounds
    Q a a0 j gradU g
    (fun R _ => coarseFluxResponseRHSEnergyBound_nonneg R a a0 gradU hs)
    (fun R hR =>
      coarseFluxResponseRHSResponseCorrectionBound_nonneg_of_bddAbove
        R a a0 g hs (hgBdd R hR))
    (fun R hR =>
      coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
        R a g hs (hgBdd R hR))
    (fun R hR =>
      coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
        R a a0 g hs (hgBdd R hR))
    henergy hforcing

/--
§3.3 wrapper where the scalar RHS-average comparison is supplied by localized
component-average bounds.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_component_average_bounds
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g)
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSEnergyBound R a a0 s gradU)
    (hresponse_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSResponseCorrectionBound R a a0 s g)
    (hweak_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSWeakFluxCorrectionBound R a s g)
    (hpoincare_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g)
    (henergy :
      localizedCoarseFluxResponseRHSEnergyBound Q a a0 s j gradU ≤
        coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU)
    (hforcing :
      localizedCoarseFluxResponseRHSResponseCorrectionBound Q a a0 s j g +
          localizedCoarseFluxResponseRHSWeakFluxCorrectionBound Q a s j g +
          localizedCoarseFluxResponseRHSPoincareCorrectionBound Q a a0 s j g ≤
        coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j gradU g :=
  solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound
    hdual Q a a0 sigma0 gradU gradV g j hs_pos hs_lt_one hsigma0 ha0eq hEll
    ha0 ha0symm hcomparison
    hdefect_bdd hRhs
    (localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_component_average_bounds
      Q a a0 j gradU g henergy_nonneg hresponse_nonneg hweak_nonneg
      hpoincare_nonneg henergy hforcing)

end

end Homogenization
