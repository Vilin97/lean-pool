/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.WeakStationarity

/-!
# Energy Quantities
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Energy on a ball. -/
def ballEnergy {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, energyDensity u x

/-- Radial energy on a ball. -/
def ballRadialEnergy {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, radialEnergyDensity u a x

/-- Weak energy on a ball, written in terms of the chosen weak gradient. -/
def weakBallEnergy {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, weakEnergyDensity Du x

/-- Weak radial energy on a ball, written in terms of the chosen weak gradient. -/
def weakBallRadialEnergy {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (r : ℝ) : ℝ :=
  ∫ x in Metric.ball a r, weakRadialEnergyDensity Du a x

/-- The open ball of radius `0` is empty, so its weak energy is zero. -/
theorem weakBallEnergy_zero_radius {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) :
    weakBallEnergy Du a 0 = 0 := by
  simp [weakBallEnergy, Metric.ball_eq_empty.mpr le_rfl]

/-- The open ball of radius `0` is empty, so its weak radial energy is zero. -/
theorem weakBallRadialEnergy_zero_radius {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) :
    weakBallRadialEnergy Du a 0 = 0 := by
  simp [weakBallRadialEnergy, Metric.ball_eq_empty.mpr le_rfl]

/-- The factor `r^(2-n)` as an integer power. -/
def thetaFactor (n : ℕ) (r : ℝ) : ℝ :=
  r ^ (2 - (n : ℤ))

/-- The monotonicity factor is continuous on any closed interval bounded away
from the origin. -/
theorem thetaFactor_continuousOn_Icc {n : ℕ} {s r : ℝ}
    (hs : 0 < s) :
    ContinuousOn (thetaFactor n) (Icc s r) := by
  have hnonzero :
      ∀ z ∈ Icc s r, (id z : ℝ) ≠ 0 ∨ 0 ≤ 2 - (n : ℤ) := by
    intro z hz
    exact Or.inl (ne_of_gt (hs.trans_le hz.1))
  exact continuous_id.continuousOn.zpow₀ (2 - (n : ℤ)) hnonzero

/-- The monotonicity quantity `Theta_u(a,r)`. -/
def theta {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (r : ℝ) : ℝ :=
  thetaFactor n r * ballEnergy u a r

/-- Weak monotonicity quantity, using the weak gradient energy. -/
def weakTheta {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (r : ℝ) : ℝ :=
  thetaFactor n r * weakBallEnergy Du a r

/-- The factor `r^(2-n)` is smooth, hence absolutely continuous, on every
strictly positive radius interval. -/
theorem thetaFactor_absolutelyContinuousOnInterval {n : ℕ} {s r : ℝ}
    (hs : 0 < s) (hsr : s < r) :
    AbsolutelyContinuousOnInterval (thetaFactor n) s r := by
  have hsr_le : s ≤ r := le_of_lt hsr
  have hnonzero : ∀ z ∈ uIcc s r, (id z : ℝ) ≠ 0 := by
    intro z hz
    have hzIcc : z ∈ Icc s r := by
      simpa [uIcc_of_le hsr_le] using hz
    have hzs : s ≤ z := by
      exact hzIcc.1
    exact ne_of_gt (hs.trans_le hzs)
  have han :
      AnalyticOnNhd ℝ (fun z : ℝ => z ^ (2 - (n : ℤ))) (uIcc s r) :=
    (analyticOnNhd_id (𝕜 := ℝ) (E := ℝ) (s := uIcc s r)).zpow hnonzero
  have hud : UniqueDiffOn ℝ (uIcc s r) := by
    rw [uIcc_of_le hsr_le]
    exact uniqueDiffOn_Icc hsr
  have hcontdiff : ContDiffOn ℝ 1 (thetaFactor n) (uIcc s r) := by
    exact han.contDiffOn (n := (1 : ℕ∞)) hud
  exact hcontdiff.absolutelyContinuousOnInterval

/-- Derivative of the monotonicity weight. -/
theorem deriv_thetaFactor {n : ℕ} {rho : ℝ} :
    deriv (thetaFactor n) rho =
      ((2 : ℝ) - (n : ℝ)) * rho ^ (1 - (n : ℤ)) := by
  have hcast : (((2 - (n : ℤ) : ℤ) : ℝ)) = (2 : ℝ) - (n : ℝ) := by
    norm_num
  have hexp : (2 - (n : ℤ) : ℤ) - 1 = 1 - (n : ℤ) := by
    omega
  unfold thetaFactor
  rw [deriv_zpow, hcast, hexp]

/-- Pointwise algebra turning the boundary identity into the derivative of the
monotonicity quantity. -/
theorem thetaFactor_boundary_algebra {n : ℕ} {rho E E' Q' : ℝ}
    (hrho : rho ≠ 0)
    (hboundary : rho * E' - ((n : ℝ) - 2) * E = 2 * rho * Q') :
    deriv (thetaFactor n) rho * E + thetaFactor n rho * E' =
      2 * thetaFactor n rho * Q' := by
  have hpow :
      rho ^ (2 - (n : ℤ)) = rho ^ (1 - (n : ℤ)) * rho := by
    symm
    calc
      rho ^ (1 - (n : ℤ)) * rho =
          rho ^ (1 - (n : ℤ)) * rho ^ (1 : ℤ) := by
            rw [zpow_one]
      _ = rho ^ ((1 - (n : ℤ)) + (1 : ℤ)) := by
            rw [← zpow_add₀ hrho]
      _ = rho ^ (2 - (n : ℤ)) := by
            congr 1
            omega
  rw [deriv_thetaFactor (n := n), thetaFactor, hpow]
  have hscaled :=
    congrArg (fun t : ℝ => rho ^ (1 - (n : ℤ)) * t) hboundary
  nlinarith [hscaled]

/-- The annular weight `|x-a|^(2-n)`. -/
def annulusWeight (n : ℕ) (a x : Domain n) : ℝ :=
  ‖x - a‖ ^ (2 - (n : ℤ))

/-- Right-hand side of the monotonicity formula on `B_r(a) \ B_s(a)`. -/
def monotonicityRhs {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (s r : ℝ) : ℝ :=
  2 * ∫ x in Metric.ball a r \ Metric.ball a s,
    annulusWeight n a x * radialEnergyDensity u a x

/-- Right-hand side of the weak monotonicity formula on `B_r(a) \ B_s(a)`. -/
def weakMonotonicityRhs {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (s r : ℝ) : ℝ :=
  2 * ∫ x in Metric.ball a r \ Metric.ball a s,
    ‖x - a‖ ^ (2 - (n : ℤ)) * weakRadialEnergyDensity Du a x

/-- The weak annular radial-energy term is nonnegative. -/
theorem weakMonotonicityRhs_nonneg {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (s r : ℝ) :
    0 ≤ weakMonotonicityRhs Du a s r := by
  unfold weakMonotonicityRhs weakRadialEnergyDensity
  exact mul_nonneg zero_le_two
    (setIntegral_nonneg
      ((Metric.isOpen_ball : IsOpen (Metric.ball a r)).measurableSet.diff
        (Metric.isOpen_ball : IsOpen (Metric.ball a s)).measurableSet)
      (fun x _hx =>
        mul_nonneg (zpow_nonneg (norm_nonneg (x - a)) _)
          (sq_nonneg ‖weakRadialDerivative Du a x‖)))

/-- Coefficient multiplying the weak energy density in the radial identity. -/
def weakRadialMainCoeff (n : ℕ) (phi : ℝ → ℝ) (x : Domain n) : ℝ :=
  ((n : ℝ) - 2) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖

/-- Coefficient multiplying the weak radial-energy density in the radial identity. -/
def weakRadialRhsCoeff {n : ℕ} (phi : ℝ → ℝ) (x : Domain n) : ℝ :=
  ‖x‖ * deriv phi ‖x‖

/-- Continuity of the main radial cutoff coefficient, assuming `phi` and `phi'`
are continuous. -/
theorem weakRadialMainCoeff_continuous {n : ℕ} {phi : ℝ → ℝ}
    (hphi : Continuous phi) (hdphi : Continuous (deriv phi)) :
    Continuous (fun x : Domain n => weakRadialMainCoeff n phi x) := by
  unfold weakRadialMainCoeff
  fun_prop

/-- Continuity of the radial-energy cutoff coefficient, assuming `phi'` is continuous. -/
theorem weakRadialRhsCoeff_continuous {n : ℕ} {phi : ℝ → ℝ}
    (hdphi : Continuous (deriv phi)) :
    Continuous (fun x : Domain n => weakRadialRhsCoeff phi x) := by
  unfold weakRadialRhsCoeff
  fun_prop

/-- A `C¹` scalar cutoff gives a continuous main radial coefficient. -/
theorem weakRadialMainCoeff_continuous_of_contDiff {n : ℕ} {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi) :
    Continuous (fun x : Domain n => weakRadialMainCoeff n phi x) :=
  weakRadialMainCoeff_continuous
    (n := n) (phi := phi) hphi.continuous hphi.continuous_deriv_one

/-- A `C¹` scalar cutoff gives a continuous radial-energy coefficient. -/
theorem weakRadialRhsCoeff_continuous_of_contDiff {n : ℕ} {phi : ℝ → ℝ}
    (hphi : ContDiff ℝ 1 phi) :
    Continuous (fun x : Domain n => weakRadialRhsCoeff phi x) :=
  weakRadialRhsCoeff_continuous
    (n := n) (phi := phi) hphi.continuous_deriv_one

/-- The main radial cutoff coefficient is a.e. strongly measurable on any set. -/
theorem weakRadialMainCoeff_aestronglyMeasurable {n : ℕ} {Ω : Set (Domain n)}
    {phi : ℝ → ℝ} (hphi : Continuous phi) (hdphi : Continuous (deriv phi)) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
      (volume.restrict Ω) :=
  (weakRadialMainCoeff_continuous (n := n) (phi := phi) hphi hdphi).aestronglyMeasurable

/-- The radial-energy cutoff coefficient is a.e. strongly measurable on any set. -/
theorem weakRadialRhsCoeff_aestronglyMeasurable {n : ℕ} {Ω : Set (Domain n)}
    {phi : ℝ → ℝ} (hdphi : Continuous (deriv phi)) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
      (volume.restrict Ω) :=
  (weakRadialRhsCoeff_continuous (n := n) (phi := phi) hdphi).aestronglyMeasurable

/-- The main radial cutoff coefficient is a.e. strongly measurable for a `C¹`
scalar cutoff. -/
theorem weakRadialMainCoeff_aestronglyMeasurable_of_contDiff {n : ℕ}
    {Ω : Set (Domain n)} {phi : ℝ → ℝ} (hphi : ContDiff ℝ 1 phi) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
      (volume.restrict Ω) :=
  (weakRadialMainCoeff_continuous_of_contDiff (n := n) hphi).aestronglyMeasurable

/-- The radial-energy cutoff coefficient is a.e. strongly measurable for a `C¹`
scalar cutoff. -/
theorem weakRadialRhsCoeff_aestronglyMeasurable_of_contDiff {n : ℕ}
    {Ω : Set (Domain n)} {phi : ℝ → ℝ} (hphi : ContDiff ℝ 1 phi) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
      (volume.restrict Ω) :=
  (weakRadialRhsCoeff_continuous_of_contDiff (n := n) hphi).aestronglyMeasurable

/-- If `phi` and `phi'` are bounded on `[0, R0]`, then the main radial coefficient
is a.e. bounded on `B_R0(0)`. -/
theorem weakRadialMainCoeff_ae_bound_on_ball_of_radius_bounds {n : ℕ}
    {phi : ℝ → ℝ} {R0 M0 M1 : ℝ}
    (hphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖phi t‖ ≤ M0)
    (hdphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1)
    (hR0_nonneg : 0 ≤ R0) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
      ‖weakRadialMainCoeff n phi x‖ ≤ ‖((n : ℝ) - 2)‖ * M0 + R0 * M1 := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hx_lt : ‖x‖ < R0 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hx_le : ‖x‖ ≤ R0 := le_of_lt hx_lt
  have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have hterm₁ :
      ‖((n : ℝ) - 2) * phi ‖x‖‖ ≤ ‖((n : ℝ) - 2)‖ * M0 := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hphi_bound ‖x‖ hnorm_nonneg hx_le) (norm_nonneg _)
  have hterm₂ :
      ‖‖x‖ * deriv phi ‖x‖‖ ≤ R0 * M1 := by
    rw [norm_mul, Real.norm_of_nonneg hnorm_nonneg]
    exact mul_le_mul hx_le (hdphi_bound ‖x‖ hnorm_nonneg hx_le)
      (norm_nonneg _) hR0_nonneg
  have hsum :
      ‖((n : ℝ) - 2) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖‖
        ≤ ‖((n : ℝ) - 2) * phi ‖x‖‖ + ‖‖x‖ * deriv phi ‖x‖‖ :=
    norm_add_le _ _
  calc
    ‖weakRadialMainCoeff n phi x‖
        = ‖((n : ℝ) - 2) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖‖ := rfl
    _ ≤ ‖((n : ℝ) - 2) * phi ‖x‖‖ + ‖‖x‖ * deriv phi ‖x‖‖ := hsum
    _ ≤ ‖((n : ℝ) - 2)‖ * M0 + R0 * M1 := add_le_add hterm₁ hterm₂

/-- If `phi'` is bounded on `[0, R0]`, then the radial-energy coefficient is
a.e. bounded on `B_R0(0)`. -/
theorem weakRadialRhsCoeff_ae_bound_on_ball_of_radius_bound {n : ℕ}
    {phi : ℝ → ℝ} {R0 M1 : ℝ}
    (hdphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1)
    (hR0_nonneg : 0 ≤ R0) :
    ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
      ‖weakRadialRhsCoeff phi x‖ ≤ R0 * M1 := by
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hx_lt : ‖x‖ < R0 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hx_le : ‖x‖ ≤ R0 := le_of_lt hx_lt
  have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
  calc
    ‖weakRadialRhsCoeff phi x‖
        = ‖‖x‖ * deriv phi ‖x‖‖ := rfl
    _ = ‖x‖ * ‖deriv phi ‖x‖‖ := by
          rw [norm_mul, Real.norm_of_nonneg hnorm_nonneg]
    _ ≤ R0 * M1 := by
          exact mul_le_mul hx_le (hdphi_bound ‖x‖ hnorm_nonneg hx_le)
            (norm_nonneg _) hR0_nonneg

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
