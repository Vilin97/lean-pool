/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusWeightedDerivative

/-!
# Ball integral absolute continuity

This module contains thin-shell estimates and the resulting absolute continuity
of scalar ball-integral radius functions.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The difference of two ball integrals is controlled by the `L¹` mass of `f`
on the radial shell between the two radii. -/
theorem dist_ballIntegral_le_radialOpenShell_integral_norm {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {r s R0 : ℝ}
    (hrR0 : r ≤ R0) (hsR0 : s ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    dist
        (∫ x in Metric.ball (0 : Domain n) r, f x)
        (∫ x in Metric.ball (0 : Domain n) s, f x)
      ≤
    ∫ x in Metric.ball (0 : Domain n) R0,
      (Ioo (min r s) (max r s)).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
        |f x| := by
  have hminmax : min r s ≤ max r s := min_le_max
  have hmaxR0 : max r s ≤ R0 := max_le hrR0 hsR0
  have hf_max :
      IntegrableOn f (Metric.ball (0 : Domain n) (max r s)) volume :=
    hf.mono_set (Metric.ball_subset_ball hmaxR0)
  have hann :
      (∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo (min r s) (max r s)).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
            f x)
        =
      (∫ x in Metric.ball (0 : Domain n) (max r s), f x)
        - (∫ x in Metric.ball (0 : Domain n) (min r s), f x) :=
    ball_annulus_indicator_integral_eq_energy_diff
      (n := n) (f := f) (a := min r s) (b := max r s) (R0 := R0)
      hminmax hmaxR0 hf_max
  have hdist :
      dist
          (∫ x in Metric.ball (0 : Domain n) r, f x)
          (∫ x in Metric.ball (0 : Domain n) s, f x)
        =
      abs (
        (∫ x in Metric.ball (0 : Domain n) (max r s), f x)
          - (∫ x in Metric.ball (0 : Domain n) (min r s), f x)
      ) := by
    by_cases hrs : r ≤ s
    · have hmin : min r s = r := min_eq_left hrs
      have hmax : max r s = s := max_eq_right hrs
      simp [Real.dist_eq, hmin, hmax, abs_sub_comm]
    · have hsr : s ≤ r := le_of_not_ge hrs
      have hmin : min r s = s := min_eq_right hsr
      have hmax : max r s = r := max_eq_left hsr
      simp [Real.dist_eq, hmin, hmax]
  calc
    dist
        (∫ x in Metric.ball (0 : Domain n) r, f x)
        (∫ x in Metric.ball (0 : Domain n) s, f x)
        =
      abs (
        (∫ x in Metric.ball (0 : Domain n) (max r s), f x)
          - (∫ x in Metric.ball (0 : Domain n) (min r s), f x)
      ) := hdist
    _ =
      abs (
        ∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo (min r s) (max r s)).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
            f x
      ) := by rw [hann]
    _ ≤
      ∫ x in Metric.ball (0 : Domain n) R0,
        abs (
          (Ioo (min r s) (max r s)).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
            f x
        ) :=
      abs_integral_le_integral_abs
    _ =
      ∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo (min r s) (max r s)).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
          |f x| := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x _hx
      by_cases hx : ‖x‖ ∈ Ioo (min r s) (max r s)
      · simp [hx]
      · simp [hx]

/-- Set-integral form of `dist_ballIntegral_le_radialOpenShell_integral_norm`,
with the ambient measure already restricted to the containing ball. -/
theorem dist_ballIntegral_le_radialOpenShell_setIntegral_norm {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {r s R0 : ℝ}
    (hrR0 : r ≤ R0) (hsR0 : s ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    dist
        (∫ x in Metric.ball (0 : Domain n) r, f x)
        (∫ x in Metric.ball (0 : Domain n) s, f x)
      ≤
    ∫ x in RadialOpenShell (n := n) r s, |f x|
      ∂(volume.restrict (Metric.ball (0 : Domain n) R0)) := by
  have hprev :=
    dist_ballIntegral_le_radialOpenShell_integral_norm
      (n := n) (f := f) (r := r) (s := s) (R0 := R0)
      hrR0 hsR0 hf
  refine hprev.trans_eq ?_
  have hshell : MeasurableSet (RadialOpenShell (n := n) r s) :=
    radialOpenShell_measurable (n := n) r s
  calc
    (∫ x in Metric.ball (0 : Domain n) R0,
      (Ioo (min r s) (max r s)).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
        |f x|)
        =
      ∫ x in Metric.ball (0 : Domain n) R0,
        (RadialOpenShell (n := n) r s).indicator (fun x : Domain n => |f x|) x := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x _hx
        by_cases hx : ‖x‖ ∈ Ioo (min r s) (max r s)
        · have hx' : x ∈ RadialOpenShell (n := n) r s := hx
          simp [hx, hx']
        · have hx' : x ∉ RadialOpenShell (n := n) r s := hx
          simp [hx, hx']
    _ =
      ∫ x in Metric.ball (0 : Domain n) R0 ∩ RadialOpenShell (n := n) r s,
        |f x| := by
        rw [setIntegral_indicator hshell]
    _ =
      ∫ x in RadialOpenShell (n := n) r s, |f x|
        ∂(volume.restrict (Metric.ball (0 : Domain n) R0)) := by
        rw [Measure.restrict_restrict hshell, inter_comm]

/-- Finite disjoint families of radius intervals give the corresponding
absolute-continuity sum estimate for ball integrals. -/
theorem sum_dist_ballIntegral_le_radialOpenShells_integral_norm {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {a b R0 : ℝ} {E : ℕ × (ℕ → ℝ × ℝ)}
    (hab : a ≤ b) (hbR0 : b ≤ R0)
    (hE : E ∈ AbsolutelyContinuousOnInterval.disjWithin a b)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    (∑ i ∈ Finset.range E.1,
      dist
        (∫ x in Metric.ball (0 : Domain n) (E.2 i).1, f x)
        (∫ x in Metric.ball (0 : Domain n) (E.2 i).2, f x))
      ≤
    ∫ x in RadialOpenShells (n := n) E, |f x|
      ∂(volume.restrict (Metric.ball (0 : Domain n) R0)) := by
  let μR : Measure (Domain n) := volume.restrict (Metric.ball (0 : Domain n) R0)
  have hend_left :
      ∀ i ∈ Finset.range E.1, (E.2 i).1 ≤ R0 := by
    intro i hi
    have hmem : (E.2 i).1 ∈ uIcc a b := (hE.1 i hi).1
    have hIcc : (E.2 i).1 ∈ Icc a b := by
      simpa [uIcc_of_le hab] using hmem
    exact hIcc.2.trans hbR0
  have hend_right :
      ∀ i ∈ Finset.range E.1, (E.2 i).2 ≤ R0 := by
    intro i hi
    have hmem : (E.2 i).2 ∈ uIcc a b := (hE.1 i hi).2
    have hIcc : (E.2 i).2 ∈ Icc a b := by
      simpa [uIcc_of_le hab] using hmem
    exact hIcc.2.trans hbR0
  have hf_abs : Integrable (fun x : Domain n => |f x|) μR := by
    simpa [μR, Real.norm_eq_abs] using hf.norm
  calc
    (∑ i ∈ Finset.range E.1,
      dist
        (∫ x in Metric.ball (0 : Domain n) (E.2 i).1, f x)
        (∫ x in Metric.ball (0 : Domain n) (E.2 i).2, f x))
        ≤
      ∑ i ∈ Finset.range E.1,
        ∫ x in RadialOpenShell (n := n) (E.2 i).1 (E.2 i).2, |f x| ∂μR := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact dist_ballIntegral_le_radialOpenShell_setIntegral_norm
          (n := n) (f := f) (r := (E.2 i).1) (s := (E.2 i).2) (R0 := R0)
          (hend_left i hi) (hend_right i hi) hf
    _ =
      ∫ x in RadialOpenShells (n := n) E, |f x| ∂μR := by
        unfold RadialOpenShells
        exact (integral_biUnion_finset
          (μ := μR) (f := fun x : Domain n => |f x|)
          (Finset.range E.1)
          (fun i _hi =>
            radialOpenShell_measurable (n := n) (E.2 i).1 (E.2 i).2)
          (pairwiseDisjoint_radialOpenShell_of_disjWithin (n := n) hE)
          (fun i _hi => by
            change Integrable (fun x : Domain n => |f x|)
              (μR.restrict
                (RadialOpenShell (n := n) (E.2 i).1 (E.2 i).2))
            exact hf_abs.mono_measure Measure.restrict_le_self)).symm

/-- `lintegral` version of the finite shell estimate, convenient for the
absolute-continuity filter argument. -/
theorem sum_dist_ballIntegral_le_radialOpenShells_lintegral_toReal {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {a b R0 : ℝ} {E : ℕ × (ℕ → ℝ × ℝ)}
    (hab : a ≤ b) (hbR0 : b ≤ R0)
    (hE : E ∈ AbsolutelyContinuousOnInterval.disjWithin a b)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    (∑ i ∈ Finset.range E.1,
      dist
        (∫ x in Metric.ball (0 : Domain n) (E.2 i).1, f x)
        (∫ x in Metric.ball (0 : Domain n) (E.2 i).2, f x))
      ≤
    (∫⁻ x in RadialOpenShells (n := n) E, ‖f x‖ₑ
      ∂(volume.restrict (Metric.ball (0 : Domain n) R0))).toReal := by
  let μR : Measure (Domain n) := volume.restrict (Metric.ball (0 : Domain n) R0)
  have hprev :=
    sum_dist_ballIntegral_le_radialOpenShells_integral_norm
      (n := n) (f := f) (a := a) (b := b) (R0 := R0) (E := E)
      hab hbR0 hE hf
  refine hprev.trans_eq ?_
  have hfμ : Integrable f μR := hf
  have hmeas :
      AEStronglyMeasurable f (μR.restrict (RadialOpenShells (n := n) E)) :=
    hfμ.aestronglyMeasurable.restrict
  simpa [μR, Real.norm_eq_abs] using
    (integral_norm_eq_lintegral_enorm
      (μ := μR.restrict (RadialOpenShells (n := n) E))
      (f := f) hmeas)

/-- Thin radial-shell volume control implies absolute continuity of every
`L¹` ball-integral radius function. -/
theorem ballIntegralRadiusAbsolutelyContinuous_of_radialOpenShellsVolumeTendstoZero
    {n : ℕ} [NeZero n] {f : Domain n → ℝ} {R0 : ℝ}
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    BallIntegralRadiusAbsolutelyContinuous f R0 := by
  intro a b ha hab hb
  rw [AbsolutelyContinuousOnInterval]
  have hlinteg :=
    radialOpenShells_lintegral_enorm_tendstoZero
      (n := n) (f := f) (a := a) (b := b) (R0 := R0)
      hthin hf ha hab
  have hreal :
      Filter.Tendsto
        (fun E : ℕ × (ℕ → ℝ × ℝ) =>
          (∫⁻ x in RadialOpenShells (n := n) E, ‖f x‖ₑ
            ∂(volume.restrict (Metric.ball (0 : Domain n) R0))).toReal)
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b))
        (𝓝 0) :=
    ENNReal.toReal_zero ▸
      (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlinteg
  refine squeeze_zero' ?_ ?_ hreal
  · filter_upwards with E
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  · have hdisj_eventually :
        ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in
          AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
            Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b),
          E ∈ AbsolutelyContinuousOnInterval.disjWithin a b := by
        exact Filter.eventually_inf_principal.2 (by
          filter_upwards with E hE
          exact hE)
    filter_upwards [hdisj_eventually] with E hE
    exact sum_dist_ballIntegral_le_radialOpenShells_lintegral_toReal
      (n := n) (f := f) (a := a) (b := b) (R0 := R0) (E := E)
      hab hb hE hf

/-- Packaged form: the thin radial-shell volume theorem supplies the reusable
ball-integral absolute-continuity theorem. -/
theorem ballIntegralRadiusACOfIntegrableOnBall_of_radialOpenShellsVolumeTendstoZero
    {n : ℕ}
    (hthin : RadialOpenShellsVolumeTendstoZero n) :
    BallIntegralRadiusACOfIntegrableOnBall n := by
  intro _inst f R0 hf
  exact ballIntegralRadiusAbsolutelyContinuous_of_radialOpenShellsVolumeTendstoZero
    (n := n) (f := f) (R0 := R0) hthin hf

/-- A packaged radius-derivative formula, together with scalar radius absolute
continuity, yields the unrestricted weighted radial representation by taking
the representing density to be the derivative of the ball-integral radius
function. -/
theorem ballIntegralRadiusWeightedRepresentation_of_ac_derivativeFormula
    {n : ℕ}
    (hac_all : BallIntegralRadiusACOfIntegrableOnBall n)
    (hformula : BallIntegralRadiusDerivativeFormula n) :
    BallIntegralRadiusWeightedRepresentation n := by
  intro hne f R0 hf
  let : NeZero n := hne
  let D : ℝ → ℝ := fun rho : ℝ =>
    deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho
  refine ⟨D, ?_, ?_⟩
  · exact locallyIntegrableOn_deriv_ballIntegral_of_radius_ac
      (n := n) (f := f) (R0 := R0) (hac_all (f := f) (R0 := R0) hf)
  · intro c
    simpa [D] using hformula (f := f) (R0 := R0) hf c

/-- Restricted-weight version of
`ballIntegralRadiusWeightedRepresentation_of_ac_derivativeFormula`. -/
theorem ballIntegralRadiusWeightedRepresentationForWeights_of_ac_derivativeFormulaForWeights
    {n : ℕ}
    (hac_all : BallIntegralRadiusACOfIntegrableOnBall n)
    (hformula : BallIntegralRadiusDerivativeFormulaForWeights n) :
    BallIntegralRadiusWeightedRepresentationForWeights n := by
  intro hne f R0 hf
  let : NeZero n := hne
  let D : ℝ → ℝ := fun rho : ℝ =>
    deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho
  refine ⟨D, ?_, ?_⟩
  · exact locallyIntegrableOn_deriv_ballIntegral_of_radius_ac
      (n := n) (f := f) (R0 := R0) (hac_all (f := f) (R0 := R0) hf)
  · intro c hc
    simpa [D] using hformula (f := f) (R0 := R0) hf c hc

/-- Euclidean thin-shell absolute continuity turns an unrestricted derivative
formula into the unrestricted weighted radial representation. -/
theorem ballIntegralRadiusWeightedRepresentation_of_derivativeFormula_euclidean
    {n : ℕ}
    (hformula : BallIntegralRadiusDerivativeFormula n) :
    BallIntegralRadiusWeightedRepresentation n :=
  ballIntegralRadiusWeightedRepresentation_of_ac_derivativeFormula
    (n := n)
    (ballIntegralRadiusACOfIntegrableOnBall_of_radialOpenShellsVolumeTendstoZero
      (n := n) (radialOpenShellsVolumeTendstoZero_euclidean n))
    hformula

/-- Euclidean thin-shell absolute continuity turns a restricted derivative
formula into the restricted weighted radial representation. -/
theorem ballIntegralRadiusWeightedRepresentationForWeights_of_derivativeFormulaForWeights_euclidean
    {n : ℕ}
    (hformula : BallIntegralRadiusDerivativeFormulaForWeights n) :
    BallIntegralRadiusWeightedRepresentationForWeights n :=
  ballIntegralRadiusWeightedRepresentationForWeights_of_ac_derivativeFormulaForWeights
    (n := n)
    (ballIntegralRadiusACOfIntegrableOnBall_of_radialOpenShellsVolumeTendstoZero
      (n := n) (radialOpenShellsVolumeTendstoZero_euclidean n))
    hformula

/-- Local `L²` radius absolute continuity supplied by the thin radial-shell
volume estimate. -/
theorem weakEnergyAbsolutelyContinuousOnRadii_of_locallyL2_radialShellsVolume
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
  weakEnergyAbsolutelyContinuousOnRadii_of_locallyL2_ballIntegralAC
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    (ballIntegralRadiusACOfIntegrableOnBall_of_radialOpenShellsVolumeTendstoZero
      (n := n) hthin)
    hDu_meas hgrad hclosedBall_subset

/-- `W^{1,2}_{loc}` radius absolute continuity supplied by the thin radial-shell
volume estimate. -/
theorem weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_radialShellsVolume
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
  weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_ballIntegralAC
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    (ballIntegralRadiusACOfIntegrableOnBall_of_radialOpenShellsVolumeTendstoZero
      (n := n) hthin)
    hW hclosedBall_subset

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
