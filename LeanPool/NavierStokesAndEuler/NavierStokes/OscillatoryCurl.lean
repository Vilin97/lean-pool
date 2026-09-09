/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualStability
public import LeanPool.NavierStokesAndEuler.NavierStokes.CurlGeometry
public import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Real oscillatory curl realization

The potential and curl below use actual Euclidean spatial derivatives. The
oscillatory carrier is kept separate from the stripped remainder coefficient.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.OscillatoryCurl

open ProblemStatement Set Filter
open scoped Topology BigOperators ContDiff InnerProductSpace


/-- Cross product on the same Euclidean space as the PDE target, as a bounded
bilinear map. -/
def crossLinear : Space →L[ℝ] Space →L[ℝ] Space :=
  (EuclideanSpace.proj 1).smulRight ((EuclideanSpace.proj 2).smulRight (coordinateVector 0)) -
  (EuclideanSpace.proj 2).smulRight ((EuclideanSpace.proj 1).smulRight (coordinateVector 0)) +
  (EuclideanSpace.proj 2).smulRight ((EuclideanSpace.proj 0).smulRight (coordinateVector 1)) -
  (EuclideanSpace.proj 0).smulRight ((EuclideanSpace.proj 2).smulRight (coordinateVector 1)) +
  (EuclideanSpace.proj 0).smulRight ((EuclideanSpace.proj 1).smulRight (coordinateVector 2)) -
  (EuclideanSpace.proj 1).smulRight ((EuclideanSpace.proj 0).smulRight (coordinateVector 2))

/-- Cross, given by `crossLinear u v`. -/
def cross (u v : Space) : Space := crossLinear u v


theorem cross_apply (u v : Space) :
    cross u v =
      u 1 • (v 2 • coordinateVector 0) - u 2 • (v 1 • coordinateVector 0) +
      u 2 • (v 0 • coordinateVector 1) - u 0 • (v 2 • coordinateVector 1) +
      u 0 • (v 1 • coordinateVector 2) - u 1 • (v 0 • coordinateVector 2) := rfl

@[simp] theorem cross_zero (u v : Space) : (cross u v) 0 = u 1 * v 2 - u 2 * v 1 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_one (u v : Space) : (cross u v) 1 = u 2 * v 0 - u 0 * v 2 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_two (u v : Space) : (cross u v) 2 = u 0 * v 1 - u 1 * v 0 := by
  rw [cross_apply]
  simp [coordinateVector]

@[simp] theorem cross_smul_left (c : ℝ) (u v : Space) :
    cross (c • u) v = c • cross u v := by simp [cross]

@[simp] theorem cross_smul_right (c : ℝ) (u v : Space) :
    cross u (c • v) = c • cross u v := by simp [cross]

@[simp] theorem cross_zero_right (u : Space) : cross u 0 = 0 := by simp [cross]

theorem inner_coordinates (u v : Space) :
    ⟪u, v⟫_ℝ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- The Euclidean cross product agrees coordinatewise with the previously
checked symbol algebra. -/
theorem cross_coordinates (u v : Space) :
    (fun i : Fin 3 => (cross u v) i) = CurlGeometry.cross (fun i => u i) (fun i => v i) := by
  ext i
  fin_cases i <;> simp [CurlGeometry.cross]

theorem cross_triple (n a : Space) :
    cross n (cross n a) = ⟪n, a⟫_ℝ • n - ‖n‖ ^ 2 • a := by
  rw [EuclideanSpace.real_norm_sq_eq]
  ext i
  fin_cases i <;> simp [inner_coordinates, Fin.sum_univ_three] <;> ring

/-- The inverse-square-normal coefficient used by the real potential. -/
def normalCoefficient (n a : Space) : Space := (‖n‖ ^ 2)⁻¹ • cross n a

theorem cross_normalCoefficient {n a : Space} (hn : n ≠ 0) (ha : ⟪n, a⟫_ℝ = 0) :
    cross n (normalCoefficient n a) = -a := by
  rw [normalCoefficient, cross_smul_right, cross_triple, ha, zero_smul, zero_sub,
    smul_neg, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn)), one_smul]

/-- The actual Euclidean gradient map applied to a scalar derivative. -/
def gradientLinear : (Space →L[ℝ] ℝ) →L[ℝ] Space :=
  ∑ i : Fin 3, (ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)).smulRight (coordinateVector i)

@[simp] theorem gradientLinear_apply (L : Space →L[ℝ] ℝ) (i : Fin 3) :
    (gradientLinear L) i = L (coordinateVector i) := by
  fin_cases i <;> simp [gradientLinear, Fin.sum_univ_three, coordinateVector]

theorem curlLinear_smulRight (L : Space →L[ℝ] ℝ) (a : Space) :
    SpatialCurl.curlLinear (L.smulRight a) = cross (gradientLinear L) a := by
  ext i
  fin_cases i <;> simp

/-- The genuine spatial curl product rule. -/
theorem curl_smul {f : Space → ℝ} {B : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hB : DifferentiableAt ℝ B x) :
    SpatialCurl.curl (fun y => f y • B y) x =
      cross (gradientLinear (fderiv ℝ f x)) (B x) + f x • SpatialCurl.curl B x := by
  unfold SpatialCurl.curl
  rw [fderiv_fun_smul hf hB, map_add, map_smul, curlLinear_smulRight]
  exact add_comm _ _

/-- Carrier, given by `-Real.sin (k * s) / k`. -/
def carrier (k s : ℝ) : ℝ := -Real.sin (k * s) / k

theorem carrier_hasDerivAt {k : ℝ} (hk : k ≠ 0) (s : ℝ) :
    HasDerivAt (carrier k) (-Real.cos (k * s)) s := by
  have h := ((Real.hasDerivAt_sin (k * s)).comp s
    ((hasDerivAt_id s).const_mul k)).neg.div_const k
  convert! h using 1
  field_simp

theorem carrier_contDiff (k : ℝ) : ContDiff ℝ ∞ (carrier k) :=
  ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).neg).div_const k

/-- Physical spatial phase normal, with time held fixed. -/
def phaseNormal (Φ : PressureField) : VelocityField :=
  fun z => gradientLinear (fderiv ℝ (fun y : Space => Φ (z.1, y)) z.2)

theorem phaseNormal_eq_pressureGradient (Φ : PressureField) (z : SpaceTime) :
    phaseNormal Φ z = pressureGradient Φ z.1 z.2 := by
  simp [phaseNormal, gradientLinear, pressureGradient]

/-- Coefficient, defined pointwise by `normalCoefficient (phaseNormal Φ z) (a z)`. -/
def coefficient (Φ : PressureField) (a : VelocityField) : VelocityField :=
  fun z => normalCoefficient (phaseNormal Φ z) (a z)

/-- `-sin(k Φ) (n × a)/(k |n|²)`, expressed by scalar multiplication. -/
def potential (k : ℝ) (Φ : PressureField) (a : VelocityField) : VelocityField :=
  fun z => carrier k (Φ z) • coefficient Φ a z

/-- Wave, given by `SpatialCurl.spatialCurl (potential k Φ a)`. -/
def wave (k : ℝ) (Φ : PressureField) (a : VelocityField) : VelocityField :=
  SpatialCurl.spatialCurl (potential k Φ a)

theorem phaseNormal_contDiffOn {U : Set SpaceTime} {Φ : PressureField}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) : ContDiffOn ℝ ∞ (phaseNormal Φ) U :=
  (ResidualRegularity.contDiffOn_space_fderiv hU hΦ (m := ∞) (by simp)).continuousLinearMap_comp
    gradientLinear

theorem coefficient_contDiffOn {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0) : ContDiffOn ℝ ∞ (coefficient Φ a) U := by
  have hN := phaseNormal_contDiffOn hU hΦ
  have hnorm : ContDiffOn ℝ ∞ (fun z => ‖phaseNormal Φ z‖ ^ 2) U :=
    (contDiff_norm_sq ℝ).comp_contDiffOn hN
  exact (hnorm.inv (fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hn z hz)))).smul
    ((hN.continuousLinearMap_comp crossLinear).clm_apply ha)

theorem potential_contDiffOn {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0) : ContDiffOn ℝ ∞ (potential k Φ a) U :=
  ((carrier_contDiff k).comp_contDiffOn hΦ).smul (coefficient_contDiffOn hU hΦ ha hn)

/-- Exact real realization: the derivative of the carrier yields the tangent
cosine wave; every coefficient derivative remains in the displayed curl. -/
theorem wave_eq {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    {k : ℝ} (hk : k ≠ 0) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ContDiffOn ℝ ∞ a U) (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0)
    (htangent : ∀ z ∈ U, ⟪phaseNormal Φ z, a z⟫_ℝ = 0) {z : SpaceTime} (hz : z ∈ U) :
    wave k Φ a z = Real.cos (k * Φ z) • a z -
      (Real.sin (k * Φ z) / k) • SpatialCurl.spatialCurl (coefficient Φ a) z := by
  have hΦslice := ResidualStability.spatialSlice_differentiable hU hΦ hz
  have hB := coefficient_contDiffOn hU hΦ ha hn
  have hBslice := ResidualStability.spatialSlice_differentiable hU hB hz
  have hcarrier : HasFDerivAt (fun y : Space => carrier k (Φ (z.1, y)))
      ((-Real.cos (k * Φ z)) • fderiv ℝ (fun y : Space => Φ (z.1, y)) z.2) z.2 := by
    exact (carrier_hasDerivAt hk (Φ z)).comp_hasFDerivAt z.2 hΦslice.hasFDerivAt
  change SpatialCurl.curl (fun y => carrier k (Φ (z.1, y)) • coefficient Φ a (z.1, y)) z.2 = _
  rw [curl_smul hcarrier.differentiableAt hBslice, hcarrier.fderiv, map_smul,
    cross_smul_left]
  change (-Real.cos (k * Φ z)) • cross (phaseNormal Φ z) (normalCoefficient (phaseNormal Φ z) (a
      z)) +
    carrier k (Φ z) • SpatialCurl.spatialCurl (coefficient Φ a) z = _
  rw [cross_normalCoefficient (hn z hz) (htangent z hz)]
  simp only [neg_smul, smul_neg, neg_neg, carrier, neg_div, sub_eq_add_neg]

theorem wave_contDiffOn {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0) : ContDiffOn ℝ ∞ (wave k Φ a) U := by
  intro z hz
  exact (SpatialCurl.contDiffAt_spatialCurl
    ((potential_contDiffOn k hU hΦ ha hn).contDiffAt (hU.mem_nhds hz)) (by simp)).contDiffWithinAt

/-- Divergence vanishes for the full realized wave, including its remainder. -/
theorem wave_divergence_free {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0) {z : SpaceTime} (hz : z ∈ U) :
    spatialDivergence (wave k Φ a) z.1 z.2 = 0 := by
  have hpot : ContDiffAt ℝ ∞ (potential k Φ a) z :=
    (potential_contDiffOn k hU hΦ ha hn).contDiffAt (hU.mem_nhds hz)
  have hslice : ContDiffAt ℝ ∞ (fun y : Space => potential k Φ a (z.1, y)) z.2 :=
    hpot.comp (f := fun y : Space => (z.1, y)) z.2 (contDiffAt_const.prodMk contDiffAt_id)
  exact SpatialCurl.spatialDivergence_spatialCurl (potential k Φ a) z.1 z.2
    (hslice.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)))

theorem coefficient_support_subset (Φ : PressureField) (a : VelocityField) :
    Function.support (coefficient Φ a) ⊆ Function.support a := by
  intro z hz haz
  exact hz (by simp [coefficient, normalCoefficient, haz])

theorem potential_tsupport_subset (k : ℝ) (Φ : PressureField) (a : VelocityField) :
    tsupport (potential k Φ a) ⊆ tsupport a := by
  apply closure_mono
  intro z hz haz
  exact hz (by simp [potential, coefficient, normalCoefficient, haz])

/-- Spatial differentiation cannot create support outside the closed joint
spacetime support, since vanishing on a joint neighborhood implies vanishing
on the spatial slice. -/
theorem spatialCurl_tsupport_subset (A : VelocityField) :
    tsupport (SpatialCurl.spatialCurl A) ⊆ tsupport A := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra hnot
  have heq : A =ᶠ[𝓝 z] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hnot
  apply hz
  change SpatialCurl.curlLinear (fderiv ℝ (fun y : Space => A (z.1, y)) z.2) = 0
  rw [ResidualRegularity.space_fderiv_congr heq]
  simp

theorem wave_tsupport_subset (k : ℝ) (Φ : PressureField) (a : VelocityField) :
    tsupport (wave k Φ a) ⊆ tsupport a :=
  (spatialCurl_tsupport_subset _).trans (potential_tsupport_subset k Φ a)

theorem wave_hasCompactSupport (k : ℝ) (Φ : PressureField) {a : VelocityField}
    (ha : HasCompactSupport a) : HasCompactSupport (wave k Φ a) :=
  ha.of_isClosed_subset isClosed_closure (wave_tsupport_subset k Φ a)

theorem phaseNormal_periodic {times : Set ℝ} {Φ : PressureField}
    (hΦ : UnitSpatialPeriodsOn times Φ) : UnitSpatialPeriodsOn times (phaseNormal Φ) := by
  intro t ht x i
  exact congrArg gradientLinear (ResidualRegularity.space_fderiv_periods hΦ t ht x i)

theorem coefficient_periodic {times : Set ℝ} {Φ : PressureField} {a : VelocityField}
    (hn : UnitSpatialPeriodsOn times (phaseNormal Φ)) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (coefficient Φ a) := by
  intro t ht x i
  unfold coefficient
  rw [hn t ht x i, ha t ht x i]

/-- It suffices for the sine carrier and the normal/amplitude data to be
periodic; a real-valued phase itself may have nonzero winding. -/
theorem potential_periodic {times : Set ℝ} {Φ : PressureField} {a : VelocityField} (k : ℝ)
    (hcarrier : UnitSpatialPeriodsOn times (fun z => Real.sin (k * Φ z)))
    (hn : UnitSpatialPeriodsOn times (phaseNormal Φ)) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (potential k Φ a) := by
  intro t ht x i
  unfold potential carrier
  have hsin := hcarrier t ht x i
  dsimp only at hsin
  rw [hsin, coefficient_periodic hn ha t ht x i]

theorem wave_periodic {times : Set ℝ} {Φ : PressureField} {a : VelocityField} (k : ℝ)
    (hcarrier : UnitSpatialPeriodsOn times (fun z => Real.sin (k * Φ z)))
    (hn : UnitSpatialPeriodsOn times (phaseNormal Φ)) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (wave k Φ a) :=
  SpatialCurl.spatialCurl_periodic (potential_periodic k hcarrier hn ha)

theorem wave_periodic_of_phase {times : Set ℝ} {Φ : PressureField} {a : VelocityField} (k : ℝ)
    (hΦ : UnitSpatialPeriodsOn times Φ) (ha : UnitSpatialPeriodsOn times a) :
    UnitSpatialPeriodsOn times (wave k Φ a) := by
  apply wave_periodic k _ (phaseNormal_periodic hΦ) ha
  intro t ht x i
  change Real.sin (k * Φ (t, x + coordinateVector i)) = Real.sin (k * Φ (t, x))
  rw [hΦ t ht x i]

/-- The coefficient remaining after removing the sine oscillation. -/
def strippedRemainder (k : ℝ) (B : VelocityField) : VelocityField :=
  fun z => (1 / k) • SpatialCurl.spatialCurl B z

theorem wave_eq_stripped {U : Set SpaceTime} {Φ : PressureField} {a : VelocityField}
    {k : ℝ} (hk : k ≠ 0) (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ContDiffOn ℝ ∞ a U) (hn : ∀ z ∈ U, phaseNormal Φ z ≠ 0)
    (htangent : ∀ z ∈ U, ⟪phaseNormal Φ z, a z⟫_ℝ = 0) {z : SpaceTime} (hz : z ∈ U) :
    wave k Φ a z = Real.cos (k * Φ z) • a z -
      Real.sin (k * Φ z) • strippedRemainder k (coefficient Φ a) z := by
  rw [wave_eq hk hU hΦ ha hn htangent hz]
  simp only [strippedRemainder, smul_smul, div_eq_mul_inv, one_mul]

/-- One additional coefficient derivative and one inverse frequency, with
no derivative of the oscillatory carrier hidden in the bound. -/
theorem strippedRemainder_jet_bound {U : Set SpaceTime} {B : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U) {z : SpaceTime} (hz : z ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (strippedRemainder k B) z‖ ≤
      (‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ / |k|) *
        ‖iteratedFDeriv ℝ (m + 1) B z‖ := by
  have hcurl : ContDiffAt ℝ ∞ (SpatialCurl.spatialCurl B) z :=
    SpatialCurl.contDiffAt_spatialCurl (hB.contDiffAt (hU.mem_nhds hz)) (by simp)
  unfold strippedRemainder
  rw [iteratedFDeriv_const_smul_apply' (hcurl.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)), norm_smul, Real.norm_eq_abs, abs_div,
        abs_one]
  calc
    _ ≤ (1 / |k|) * (‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ *
        ‖iteratedFDeriv ℝ (m + 1) B z‖) :=
      mul_le_mul_of_nonneg_left (ResidualStability.norm_iteratedFDeriv_spatialCurl_le hU hB hz m)
        (by positivity)
    _ = _ := by ring

theorem strippedRemainder_finiteJetBound {U : Set SpaceTime} {B : VelocityField}
    (k : ℝ) (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U) {m : ℕ} {C : ℝ}
    (hjet : JetBounds.FiniteJetBound (m + 1) B U C) :
    JetBounds.FiniteJetBound m (strippedRemainder k B) U
      ((‖SpatialCurl.curlLinear.comp (ResidualStability.spaceRestriction Space)‖ / |k|) * C) := by
  intro n hn z hz
  exact (strippedRemainder_jet_bound k hU hB hz n).trans
    (mul_le_mul_of_nonneg_left (hjet (n + 1) (Nat.add_le_add_right hn 1) z hz) (by positivity))

end NavierStokes.OscillatoryCurl
