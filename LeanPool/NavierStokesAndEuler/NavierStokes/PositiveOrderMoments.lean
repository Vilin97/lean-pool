/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveAxisSystem
public import LeanPool.NavierStokesAndEuler.NavierStokes.FiveRowRank
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProfileHistories
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-!
# Actual five-row repair at positive slow order

Only the order-n entries of the histories are changed. Endpoint extraction
proves that all five actual moment increments are linear, including pressure
with the known previous-order radial residual retained.
-/

noncomputable section

open Set Function MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokes.PositiveOrderMoments

abbrev Profile := ℝ → ℝ
abbrev History := ℕ → Profile
abbrev Debt := Fin 5 → ℝ

noncomputable def cauchy (n : ℕ) (u v : History) (R : ℝ) : ℝ :=
  PositiveAxisSystem.convolution n (fun i j => u i R * v j R)

noncomputable def increment (u : History) (n : ℕ) (du : Profile) : History :=
  Function.update u n (fun R => u n R + du R)

theorem increment_lower (u : History) {n j : ℕ} (du : Profile) (hj : j < n) :
    increment u n du j = u j := Function.update_of_ne (Nat.ne_of_lt hj) _ _

theorem cauchy_increment {n : ℕ} (hn : 0 < n) (u v : History) (du dv : Profile) (R : ℝ) :
    cauchy n (increment u n du) (increment v n dv) R =
      cauchy n u v R + u 0 R * dv R + du R * v 0 R := by
  have hl : PositiveAxisSystem.lowerConvolution n
      (fun i j => increment u n du i R * increment v n dv j R) =
      PositiveAxisSystem.lowerConvolution n (fun i j => u i R * v j R) := by
    apply PositiveAxisSystem.lowerConvolution_congr
    intro i hi j hj
    rw [increment_lower u du hi, increment_lower v dv hj]
  unfold cauchy
  rw [PositiveAxisSystem.convolution_split hn, PositiveAxisSystem.convolution_split hn, hl]
  rw [increment_lower u du hn, increment_lower v dv hn]
  simp only [increment, Function.update_self]
  ring

/-- The actual R-pressure equation: Ω is the fixed order-(n-1) source. -/
noncomputable def pressureGradient (n : ℕ) (e : History) (omega : Profile) (R : ℝ) : ℝ :=
  (cauchy n e e R - omega R) / R


/-- The angular similarity coefficient in (22), reconstructed from E. -/
noncomputable def phiHistory (C : ℝ) (e : History) : History :=
  fun j R => C * e j R / R

theorem cauchy_phiHistory (n : ℕ) (C : ℝ) (e : History) (R : ℝ) :
    cauchy n (phiHistory C e) (phiHistory C e) R = (C / R) ^ 2 * cauchy n e e R := by
  unfold cauchy PositiveAxisSystem.convolution phiHistory
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Multiplying the actual X-pressure equation by dX/dR=R gives the pressure
row used here. In particular the preceding Ω term is retained exactly. -/
theorem pressureGradient_eq_X_equation (n : ℕ) (C : ℝ) (e : History) (omega : Profile)
    {R : ℝ} (hC : C ≠ 0) (hR : R ≠ 0) :
    pressureGradient n e omega R = R * ((C ^ 2)⁻¹ *
      cauchy n (phiHistory C e) (phiHistory C e) R - omega R / (2 * (R ^ 2 / 2))) := by
  rw [cauchy_phiHistory]
  unfold pressureGradient
  field_simp

/-- The five densities in (23), in the order printed there. -/
noncomputable def rowDensity (n : ℕ) (u e : History) (omega : Profile) (R : ℝ) : Debt :=
  ![R * u n R, R ^ 2 * e n R, pressureGradient n e omega R,
    R ^ 2 * cauchy n u e R,
    R * cauchy n u u R - R ^ 2 / 2 * pressureGradient n e omega R]

noncomputable def positiveIntegral (f : Profile) : ℝ := ∫ R in Ioi (0 : ℝ), f R

noncomputable def moments (n : ℕ) (u e : History) (omega : Profile) : Debt :=
  fun i => positiveIntegral (fun R => rowDensity n u e omega R i)

noncomputable def linearDensity (u₀ e₀ du de : Profile) (R : ℝ) : Debt :=
  ![R * du R, R ^ 2 * de R, 2 * e₀ R * de R / R,
    R ^ 2 * (u₀ R * de R + du R * e₀ R),
    2 * R * u₀ R * du R - R * e₀ R * de R]

/-- There are no quadratic current-order terms when n>0. -/
theorem rowDensity_increment {n : ℕ} (hn : 0 < n) (u e : History) (omega du de : Profile)
    (R : ℝ) :
    rowDensity n (increment u n du) (increment e n de) omega R =
      rowDensity n u e omega R + linearDensity (u 0) (e 0) du de R := by
  ext i
  fin_cases i <;>
    simp only [rowDensity, pressureGradient, cauchy_increment hn, Pi.add_apply] <;>
    simp [linearDensity, increment, Function.update_self, div_eq_mul_inv]
  all_goals try ring1
  by_cases hR : R = 0
  · simp [hR]
  · field_simp
    ring

noncomputable def weightedDensity (lam A : ℝ) (du de : Profile) (R : ℝ) : Debt :=
  ![R * du R, R ^ 2 * de R, (2 * A) * (R ^ (-2 - 2 * lam) * de R),
    A * (R ^ (1 - 2 * lam) * du R), (-A) * (R ^ (-2 * lam) * de R)]

theorem linearDensity_on_patch (lam A a b : ℝ) (ha : 0 < a)
    (u₀ e₀ du de : Profile)
    (hu : ∀ R ∈ Ioo a b, u₀ R = 0)
    (he : ∀ R ∈ Ioo a b, e₀ R = FiveRowRank.background lam A R)
    (hdu : support du ⊆ Ioo a b) (hde : support de ⊆ Ioo a b) (R : ℝ) :
    linearDensity u₀ e₀ du de R = weightedDensity lam A du de R := by
  by_cases hR : R ∈ Ioo a b
  · have hp : 0 < R := ha.trans hR.1
    ext i
    fin_cases i <;> simp [linearDensity, weightedDensity, hu R hR, he R hR]
    · rw [show 2 * FiveRowRank.background lam A R * de R / R =
        (2 * FiveRowRank.background lam A R / R) * de R by ring,
        FiveRowRank.pressure_weight lam A R hp]
      ring
    · rw [show R ^ 2 * (du R * FiveRowRank.background lam A R) =
        (R ^ 2 * FiveRowRank.background lam A R) * du R by ring,
        FiveRowRank.angular_weight lam A R hp]
      ring
    · have hw := FiveRowRank.axial_weight lam A R hp
      have hw' : R * FiveRowRank.background lam A R = A * R ^ (-2 * lam) := by linarith
      rw [hw']
      ring_nf
  · have hd : du R = 0 := by
      by_contra h
      exact hR (hdu h)
    have he' : de R = 0 := by
      by_contra h
      exact hR (hde h)
    simp [linearDensity, weightedDensity, hd, he']

/-- Axial target moments: physical mass and angular transport. -/
noncomputable def axialDebt (A : ℝ) (d : Debt) : Fin 2 → ℝ := ![d 0, d 3 / A]

/-- Angular target moments: angular mass, pressure, and axial transport. -/
noncomputable def angularDebt (A : ℝ) (d : Debt) : Fin 3 → ℝ :=
  ![d 1, d 2 / (2 * A), -(d 4) / A]

noncomputable def repairU (lam A a b : ℝ) (d : Debt) : Profile :=
  LocalizedMomentRepair.repair (FiveRowRank.axialPowers lam)
    (FiveRowRank.cellLower a b) (FiveRowRank.cellUpper a b) (axialDebt A d)

noncomputable def repairE (lam A a b : ℝ) (d : Debt) : Profile :=
  LocalizedMomentRepair.repair (FiveRowRank.angularPowers lam)
    (FiveRowRank.cellLower a b) (FiveRowRank.cellUpper a b) (angularDebt A d)

theorem repairU_contDiff (lam A a b : ℝ) (d : Debt) : ContDiff ℝ ∞ (repairU lam A a b d) :=
  LocalizedMomentRepair.repair_contDiff _ _ _ _

theorem repairE_contDiff (lam A a b : ℝ) (d : Debt) : ContDiff ℝ ∞ (repairE lam A a b d) :=
  LocalizedMomentRepair.repair_contDiff _ _ _ _

theorem repairU_tsupport (lam A a b : ℝ) (d : Debt) (hab : a < b) :
    tsupport (repairU lam A a b d) ⊆ Ioo a b :=
  (LocalizedMomentRepair.repair_tsupport_subset_open _ _ _ _
    (FiveRowRank.cell_lower_lt_upper a b hab)).trans (FiveRowRank.cell_union_subset a b hab)

theorem repairE_tsupport (lam A a b : ℝ) (d : Debt) (hab : a < b) :
    tsupport (repairE lam A a b d) ⊆ Ioo a b :=
  (LocalizedMomentRepair.repair_tsupport_subset_open _ _ _ _
    (FiveRowRank.cell_lower_lt_upper a b hab)).trans (FiveRowRank.cell_union_subset a b hab)

theorem repairU_moment (lam A a b : ℝ) (d : Debt) (hlam : 0 < lam) (ha : 0 < a)
    (hab : a < b) (i : Fin 2) :
    (∫ R, R ^ FiveRowRank.axialPowers lam i * repairU lam A a b d R) = axialDebt A d i :=
  LocalizedMomentRepair.repair_exact _ _ _ _ (FiveRowRank.axialPowers_injective lam hlam)
    (FiveRowRank.cell_positive a b ha hab) (FiveRowRank.cell_lower_lt_upper a b hab)
    (FiveRowRank.cell_separated a b hab) i

theorem repairE_moment (lam A a b : ℝ) (d : Debt) (hlam : 0 < lam) (ha : 0 < a)
    (hab : a < b) (i : Fin 3) :
    (∫ R, R ^ FiveRowRank.angularPowers lam i * repairE lam A a b d R) = angularDebt A d i :=
  LocalizedMomentRepair.repair_exact _ _ _ _ (FiveRowRank.angularPowers_injective lam hlam)
    (FiveRowRank.cell_positive a b ha hab) (FiveRowRank.cell_lower_lt_upper a b hab)
    (FiveRowRank.cell_separated a b hab) i

theorem positiveIntegral_eq_integral {f : Profile} (hf : ∀ R ≤ 0, f R = 0) :
    positiveIntegral f = ∫ R, f R := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro R hR
  exact hf R (le_of_not_gt hR)

theorem weighted_moments_exact (lam A a b : ℝ) (d : Debt) (hlam : 0 < lam)
    (hA : A ≠ 0) (ha : 0 < a) (hab : a < b) (i : Fin 5) :
    positiveIntegral (fun R => weightedDensity lam A (repairU lam A a b d) (repairE lam A a b d) R
      i) = d i := by
  have hdu := subset_closure.trans (repairU_tsupport lam A a b d hab)
  have hde := subset_closure.trans (repairE_tsupport lam A a b d hab)
  rw [positiveIntegral_eq_integral (by
    intro R hR
    have hu : repairU lam A a b d R = 0 := by
      by_contra h
      exact (not_lt_of_ge hR) (ha.trans (hdu h).1)
    have he : repairE lam A a b d R = 0 := by
      by_contra h
      exact (not_lt_of_ge hR) (ha.trans (hde h).1)
    fin_cases i <;> simp [weightedDensity, hu, he])]
  have hu := repairU_moment lam A a b d hlam ha hab
  have he := repairE_moment lam A a b d hlam ha hab
  fin_cases i
  · simpa [weightedDensity, FiveRowRank.axialPowers, axialDebt] using hu 0
  · simpa [weightedDensity, FiveRowRank.angularPowers, angularDebt] using he 0
  · change (∫ R, (2 * A) * (R ^ (-2 - 2 * lam) * repairE lam A a b d R)) = d 2
    rw [integral_const_mul]
    have hm := he 1
    simp [FiveRowRank.angularPowers, angularDebt] at hm
    rw [hm]
    field_simp
  · change (∫ R, A * (R ^ (1 - 2 * lam) * repairU lam A a b d R)) = d 3
    rw [integral_const_mul]
    have hm := hu 1
    simp [FiveRowRank.axialPowers, axialDebt] at hm
    rw [hm]
    field_simp
  · change (∫ R, (-A) * (R ^ (-2 * lam) * repairE lam A a b d R)) = d 4
    rw [integral_const_mul]
    have hm : (∫ R, R ^ (-2 * lam) * repairE lam A a b d R) = -(d 4) / A := he 2
    rw [hm]
    field_simp


theorem repairU_power_integrable (lam A a b p : ℝ) (d : Debt) (ha : 0 < a) (hab : a < b) :
    Integrable (fun R => R ^ p * repairU lam A a b d R) :=
  FiveRowRank.integrable_power_mul_of_patch p a b _ ha (repairU_contDiff lam A a b d).continuous
    (subset_closure.trans (repairU_tsupport lam A a b d hab))

theorem repairE_power_integrable (lam A a b p : ℝ) (d : Debt) (ha : 0 < a) (hab : a < b) :
    Integrable (fun R => R ^ p * repairE lam A a b d R) :=
  FiveRowRank.integrable_power_mul_of_patch p a b _ ha (repairE_contDiff lam A a b d).continuous
    (subset_closure.trans (repairE_tsupport lam A a b d hab))

theorem weightedDensity_integrable (lam A a b : ℝ) (d : Debt) (ha : 0 < a) (hab : a < b)
    (i : Fin 5) :
    Integrable (fun R => weightedDensity lam A (repairU lam A a b d) (repairE lam A a b d) R i) :=
      by
  fin_cases i
  · simpa [weightedDensity] using repairU_power_integrable lam A a b 1 d ha hab
  · simpa [weightedDensity] using repairE_power_integrable lam A a b 2 d ha hab
  · exact (repairE_power_integrable lam A a b (-2 - 2 * lam) d ha hab).const_mul (2 * A)
  · exact (repairU_power_integrable lam A a b (1 - 2 * lam) d ha hab).const_mul A
  · exact (repairE_power_integrable lam A a b (-2 * lam) d ha hab).const_mul (-A)

/-- Exact affine change of all five actual positive-radius integrals. -/
theorem moments_repair (lam A a b : ℝ) (d : Debt) {n : ℕ} (hn : 0 < n)
    (u e : History) (omega : Profile) (hlam : 0 < lam) (hA : A ≠ 0)
    (ha : 0 < a) (hab : a < b)
    (hu : ∀ R ∈ Ioo a b, u 0 R = 0)
    (he : ∀ R ∈ Ioo a b, e 0 R = FiveRowRank.background lam A R)
    (hint : ∀ i, IntegrableOn (fun R => rowDensity n u e omega R i) (Ioi 0)) :
    moments n (increment u n (repairU lam A a b d))
      (increment e n (repairE lam A a b d)) omega = moments n u e omega + d := by
  have hdu := subset_closure.trans (repairU_tsupport lam A a b d hab)
  have hde := subset_closure.trans (repairE_tsupport lam A a b d hab)
  ext i
  have hf : (fun R => rowDensity n (increment u n (repairU lam A a b d))
      (increment e n (repairE lam A a b d)) omega R i) =
      (fun R => rowDensity n u e omega R i +
        weightedDensity lam A (repairU lam A a b d) (repairE lam A a b d) R i) := by
    funext R
    rw [rowDensity_increment hn, linearDensity_on_patch lam A a b ha _ _ _ _ hu he hdu hde]
    rfl
  change positiveIntegral _ = positiveIntegral _ + d i
  unfold positiveIntegral
  rw [hf, integral_add (hint i) (weightedDensity_integrable lam A a b d ha hab i).integrableOn]
  change _ + positiveIntegral _ = _ + d i
  rw [weighted_moments_exact lam A a b d hlam hA ha hab i]

/-- Arbitrary moment debts are removed, with no size restriction. -/
theorem moments_repair_target (lam A a b : ℝ) (target : Debt) {n : ℕ} (hn : 0 < n)
    (u e : History) (omega : Profile) (hlam : 0 < lam) (hA : A ≠ 0)
    (ha : 0 < a) (hab : a < b)
    (hu : ∀ R ∈ Ioo a b, u 0 R = 0)
    (he : ∀ R ∈ Ioo a b, e 0 R = FiveRowRank.background lam A R)
    (hint : ∀ i, IntegrableOn (fun R => rowDensity n u e omega R i) (Ioi 0)) :
    moments n (increment u n (repairU lam A a b (target - moments n u e omega)))
      (increment e n (repairE lam A a b (target - moments n u e omega))) omega = target := by
  rw [moments_repair lam A a b _ hn u e omega hlam hA ha hab hu he hint]
  abel

theorem exists_smooth_exact_repair (lam A a b : ℝ) (target : Debt) {n : ℕ} (hn : 0 < n)
    (u e : History) (omega : Profile) (hlam : 0 < lam) (hA : A ≠ 0)
    (ha : 0 < a) (hab : a < b)
    (hu : ∀ R ∈ Ioo a b, u 0 R = 0)
    (he : ∀ R ∈ Ioo a b, e 0 R = FiveRowRank.background lam A R)
    (hint : ∀ i, IntegrableOn (fun R => rowDensity n u e omega R i) (Ioi 0)) :
    ∃ du de : Profile, ContDiff ℝ ∞ du ∧ ContDiff ℝ ∞ de ∧
      HasCompactSupport du ∧ HasCompactSupport de ∧
      tsupport du ⊆ Ioo a b ∧ tsupport de ⊆ Ioo a b ∧
      moments n (increment u n du) (increment e n de) omega = target := by
  let d := target - moments n u e omega
  refine ⟨repairU lam A a b d, repairE lam A a b d,
    repairU_contDiff lam A a b d, repairE_contDiff lam A a b d, ?_, ?_,
    repairU_tsupport lam A a b d hab, repairE_tsupport lam A a b d hab,
    moments_repair_target lam A a b target hn u e omega hlam hA ha hab hu he hint⟩
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_closure.trans (repairU_tsupport lam A a b d hab)).trans Ioo_subset_Icc_self)
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_closure.trans (repairE_tsupport lam A a b d hab)).trans Ioo_subset_Icc_self)


theorem repairU_zero_before (lam A a b : ℝ) (d : Debt) (hab : a < b) {R : ℝ} (hR : R ≤ a) :
    repairU lam A a b d R = 0 := by
  by_contra h
  have hm := repairU_tsupport lam A a b d hab (subset_closure h)
  exact (not_lt_of_ge hR) hm.1

theorem repairE_zero_before (lam A a b : ℝ) (d : Debt) (hab : a < b) {R : ℝ} (hR : R ≤ a) :
    repairE lam A a b d R = 0 := by
  by_contra h
  have hm := repairE_tsupport lam A a b d hab (subset_closure h)
  exact (not_lt_of_ge hR) hm.1

theorem repairU_zero_outside (lam A a b : ℝ) (d : Debt) (hab : a < b) {R : ℝ}
    (hR : R ∉ Ioo a b) : repairU lam A a b d R = 0 := by
  by_contra h
  exact hR (repairU_tsupport lam A a b d hab (subset_closure h))

theorem repairE_zero_outside (lam A a b : ℝ) (d : Debt) (hab : a < b) {R : ℝ}
    (hR : R ∉ Ioo a b) : repairE lam A a b d R = 0 := by
  by_contra h
  exact hR (repairE_tsupport lam A a b d hab (subset_closure h))

theorem rowDensity_repair_eq_outside (lam A a b : ℝ) (d : Debt) {n : ℕ} (hn : 0 < n)
    (u e : History) (omega : Profile) (hab : a < b) {R : ℝ} (hR : R ∉ Ioo a b) :
    rowDensity n (increment u n (repairU lam A a b d))
      (increment e n (repairE lam A a b d)) omega R = rowDensity n u e omega R := by
  rw [rowDensity_increment hn]
  ext i
  fin_cases i <;> simp [linearDensity, repairU_zero_outside lam A a b d hab hR,
    repairE_zero_outside lam A a b d hab hR]

theorem rowDensity_repair_exterior (lam A a b : ℝ) (d : Debt) {n : ℕ} (hn : 0 < n)
    (u e : History) (omega : Profile) (hab : a < b) {B R : ℝ}
    (hs : ∀ t, B ≤ t → rowDensity n u e omega t = 0) (hR : max B b ≤ R) :
    rowDensity n (increment u n (repairU lam A a b d))
      (increment e n (repairE lam A a b d)) omega R = 0 := by
  rw [rowDensity_repair_eq_outside lam A a b d hn u e omega hab
    (fun ht => (not_lt_of_ge ((le_max_right B b).trans hR)) ht.2)]
  exact hs R ((le_max_left B b).trans hR)

theorem increment_eq_of_zero (u : History) (n j : ℕ) (du : Profile) (R : ℝ)
    (hd : du R = 0) : increment u n du j R = u j R := by
  by_cases hj : j = n
  · subst j
    simp [increment, hd]
  · simp [increment, hj]

theorem pressureGradient_increment_of_zero {n : ℕ} (hn : 0 < n) (e : History)
    (omega de : Profile) (R : ℝ) (hd : de R = 0) :
    pressureGradient n (increment e n de) omega R = pressureGradient n e omega R := by
  simp only [pressureGradient, cauchy_increment hn, hd, mul_zero, zero_mul, add_zero]

/-- Recomputing pressure does not disturb the already solved inner region:
the complete new pressure source agrees with the old one up to the patch. -/
theorem pressure_primitive_repair_before_patch (lam A a b : ℝ) (d : Debt)
    {n : ℕ} (hn : 0 < n) (e : History) (omega : Profile) (hab : a < b)
    {R : ℝ} (hR0 : 0 ≤ R) (hRa : R ≤ a) :
    (∫ t in (0 : ℝ)..R, pressureGradient n (increment e n (repairE lam A a b d)) omega t) =
      ∫ t in (0 : ℝ)..R, pressureGradient n e omega t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hR0] at ht
  exact pressureGradient_increment_of_zero hn e omega _ t
    (repairE_zero_before lam A a b d hab (ht.2.trans hRa))

/-- The physical mass primitive is likewise preserved before the patch. -/
theorem mass_primitive_repair_before_patch (lam A a b : ℝ) (d : Debt)
    (n : ℕ) (u : History) (hab : a < b) {R : ℝ} (hR0 : 0 ≤ R) (hRa : R ≤ a) :
    (∫ t in (0 : ℝ)..R, t * increment u n (repairU lam A a b d) n t) =
      ∫ t in (0 : ℝ)..R, t * u n t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hR0] at ht
  change t * increment u n (repairU lam A a b d) n t = t * u n t
  rw [increment_eq_of_zero u n n _ t
    (repairU_zero_before lam A a b d hab (ht.2.trans hRa))]

section SmoothParameters

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem axialDebt_contDiffOn {S : Set P} {A : P → ℝ} {d : P → Debt}
    (hA : ContDiffOn ℝ ∞ A S) (hd : ContDiffOn ℝ ∞ d S) (hAn : ∀ p ∈ S, A p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => axialDebt (A p) (d p)) S := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_pi.mp hd 0
  · exact (contDiffOn_pi.mp hd 3).div hA hAn

theorem angularDebt_contDiffOn {S : Set P} {A : P → ℝ} {d : P → Debt}
    (hA : ContDiffOn ℝ ∞ A S) (hd : ContDiffOn ℝ ∞ d S) (hAn : ∀ p ∈ S, A p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => angularDebt (A p) (d p)) S := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_pi.mp hd 1
  · exact (contDiffOn_pi.mp hd 2).div (contDiffOn_const.mul hA)
      (fun p hp => mul_ne_zero (by norm_num) (hAn p hp))
  · exact (contDiffOn_pi.mp hd 4).neg.div hA hAn

theorem repairU_joint_contDiffOn (lam a b : ℝ) {S : Set P} {A : P → ℝ} {d : P → Debt}
    (hA : ContDiffOn ℝ ∞ A S) (hd : ContDiffOn ℝ ∞ d S) (hAn : ∀ p ∈ S, A p ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => repairU lam (A z.1) a b (d z.1) z.2) (S ×ˢ univ) :=
  FiveRowRank.repair_joint_contDiffOn (E := P) (n := 2)
    (FiveRowRank.axialPowers lam) (FiveRowRank.cellLower a b) (FiveRowRank.cellUpper a b)
    (S := S) (d := fun p => axialDebt (A p) (d p)) (axialDebt_contDiffOn hA hd hAn)

theorem repairE_joint_contDiffOn (lam a b : ℝ) {S : Set P} {A : P → ℝ} {d : P → Debt}
    (hA : ContDiffOn ℝ ∞ A S) (hd : ContDiffOn ℝ ∞ d S) (hAn : ∀ p ∈ S, A p ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => repairE lam (A z.1) a b (d z.1) z.2) (S ×ˢ univ) :=
  FiveRowRank.repair_joint_contDiffOn (E := P) (n := 3)
    (FiveRowRank.angularPowers lam) (FiveRowRank.cellLower a b) (FiveRowRank.cellUpper a b)
    (S := S) (d := fun p => angularDebt (A p) (d p)) (angularDebt_contDiffOn hA hd hAn)

end SmoothParameters


section PhysicalHistories

abbrev JointProfile := ℝ × ℝ → ℝ
abbrev JointHistory := ℕ → JointProfile

noncomputable def slice (f : JointHistory) (eta : ℝ) : History := fun j R => f j (R, eta)

noncomputable def jointIncrement (u : JointHistory) (n : ℕ) (du : JointProfile) : JointHistory :=
  Function.update u n (fun w => u n w + du w)

theorem slice_jointIncrement (u : JointHistory) (n : ℕ) (du : JointProfile) (eta : ℝ) :
    slice (jointIncrement u n du) eta = increment (slice u eta) n (fun R => du (R, eta)) := by
  funext j R
  by_cases hj : j = n
  · subst j
    simp [slice, jointIncrement, increment]
  · simp [slice, jointIncrement, increment, hj]

theorem jointIncrement_lower (u : JointHistory) {n j : ℕ} (du : JointProfile) (hj : j < n) :
    jointIncrement u n du j = u j := Function.update_of_ne (Nat.ne_of_lt hj) _ _

theorem jointIncrement_contDiffOn {S : Set (ℝ × ℝ)} {n : ℕ} {u : JointHistory}
    {du : JointProfile} (hu : ∀ j, j ≤ n → ContDiffOn ℝ ∞ (u j) S)
    (hdu : ContDiffOn ℝ ∞ du S) (j : ℕ) (hj : j ≤ n) :
    ContDiffOn ℝ ∞ (jointIncrement u n du j) S := by
  by_cases h : j = n
  · subst j
    simpa only [jointIncrement, Function.update_self] using (hu n le_rfl).add hdu
  · simpa only [jointIncrement, Function.update_of_ne h] using hu j hj

noncomputable def globalDomain : ProfileHistories.RadialDomain where
  carrier := univ
  isOpen := isOpen_univ
  scale_mem := by intro p hp t ht; trivial

theorem primitive_contDiff {F : JointProfile} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (ProfileHistories.primitive F) :=
  contDiffOn_univ.mp (ProfileHistories.primitive_smooth globalDomain hF.contDiffOn)

theorem primitive_hasDerivAt {F : JointProfile} (hF : ContDiff ℝ ∞ F) (w : ℝ × ℝ) :
    HasDerivAt (fun R => ProfileHistories.primitive F (R, w.2)) (F w) w.1 :=
  ProfileHistories.primitive_hasDerivAt globalDomain hF.contDiffOn (mem_univ w)

/-- Compact positive-radius sources identify the actual primitive with the
positive-radius total integral, without imposing values at negative radii. -/
theorem positiveIntegral_eq_primitive {f : Profile} {B R : ℝ} (hB : 0 ≤ B) (hR : B ≤ R)
    (hf : ∀ t, B ≤ t → f t = 0) : positiveIntegral f = ∫ t in (0 : ℝ)..R, f t := by
  rw [intervalIntegral.integral_of_le (hB.trans hR)]
  apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
  · intro t ht
    exact ht.1
  · intro t ht
    have htR : R < t := by
      by_contra h
      exact ht.2 ⟨ht.1, le_of_not_gt h⟩
    exact hf t (hR.trans htR.le)

noncomputable def jointPressureGradient (n : ℕ) (e : JointHistory) (omega : JointProfile)
    (w : ℝ × ℝ) : ℝ := pressureGradient n (slice e w.2) (fun R => omega (R, w.2)) w.1

/-- Pressure is recomputed from its actual radial gradient, with zero axis datum. -/
noncomputable def pressureHistory (n : ℕ) (e : JointHistory) (omega : JointProfile) : JointProfile
  :=
  ProfileHistories.primitive (jointPressureGradient n e omega)

theorem pressureHistory_axis (n : ℕ) (e : JointHistory) (omega : JointProfile) (eta : ℝ) :
    pressureHistory n e omega (0, eta) = 0 := ProfileHistories.primitive_at_axis _ _

theorem pressureHistory_contDiff {n : ℕ} {e : JointHistory} {omega : JointProfile}
    (hq : ContDiff ℝ ∞ (jointPressureGradient n e omega)) :
    ContDiff ℝ ∞ (pressureHistory n e omega) := primitive_contDiff hq

theorem pressureHistory_hasDerivAt {n : ℕ} {e : JointHistory} {omega : JointProfile}
    (hq : ContDiff ℝ ∞ (jointPressureGradient n e omega)) (w : ℝ × ℝ) :
    HasDerivAt (fun R => pressureHistory n e omega (R, w.2))
      (pressureGradient n (slice e w.2) (fun R => omega (R, w.2)) w.1) w.1 :=
  primitive_hasDerivAt hq w

theorem pressureHistory_exterior {n : ℕ} {e : JointHistory} {omega : JointProfile} {B : ℝ}
    (hB : 0 ≤ B) (hs : ∀ eta R, B ≤ R → jointPressureGradient n e omega (R, eta) = 0)
    (hm : ∀ eta, positiveIntegral (fun R => jointPressureGradient n e omega (R, eta)) = 0)
    {R eta : ℝ} (hR : B ≤ R) : pressureHistory n e omega (R, eta) = 0 := by
  rw [pressureHistory, ProfileHistories.primitive,
    ← positiveIntegral_eq_primitive hB hR (hs eta), hm eta]

/-- The third repaired row is the actual pressure-exterior condition. -/
theorem pressureHistory_exterior_of_moments {n : ℕ} {u e : JointHistory} {omega : JointProfile}
    {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta R, B ≤ R → jointPressureGradient n e omega (R, eta) = 0)
    (hm : ∀ eta, moments n (slice u eta) (slice e eta) (fun R => omega (R, eta)) = 0)
    {R eta : ℝ} (hR : B ≤ R) : pressureHistory n e omega (R, eta) = 0 := by
  apply pressureHistory_exterior hB hs _ hR
  intro eta
  exact congrFun (hm eta) 2

noncomputable def weightedAxial (u : JointProfile) (w : ℝ × ℝ) : ℝ := w.1 * u w

noncomputable def massHistory (u : JointProfile) : JointProfile :=
  ProfileHistories.primitive (weightedAxial u)

noncomputable def parameterMassHistory (u : JointProfile) : JointProfile :=
  ProfileHistories.primitive (ProfileHistories.parameterPartial (weightedAxial u))

/-- The R-coordinate version of (21), with both histories given by actual integrals. -/
noncomputable def fluxHistory (h lam : ℝ) (u : JointProfile) (w : ℝ × ℝ) : ℝ :=
  (w.2 * w.1 ^ 2 * u w - 2 * w.2 * (PositiveAxisSystem.dScale h + lam) * massHistory u w -
    PositiveAxisSystem.edge w.2 * parameterMassHistory u w) / PositiveAxisSystem.ell h w.2

noncomputable def radialZ (h power : ℝ) (u : JointProfile) (w : ℝ × ℝ) : ℝ :=
  (2 * w.2 * power * u w + PositiveAxisSystem.edge w.2 * ProfileHistories.parameterPartial u w -
    w.2 * w.1 * ProfileHistories.radialPartial u w) / PositiveAxisSystem.ell h w.2

theorem weightedAxial_contDiff {u : JointProfile} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (weightedAxial u) := contDiff_fst.mul hu

theorem parameterPartial_contDiff {F : JointProfile} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (ProfileHistories.parameterPartial F) :=
  contDiffOn_univ.mp (ProfileHistories.parameterPartial_smooth globalDomain hF.contDiffOn)

theorem weightedAxial_parameterPartial {u : JointProfile} (hu : ContDiff ℝ ∞ u) (w : ℝ × ℝ) :
    ProfileHistories.parameterPartial (weightedAxial u) w =
      w.1 * ProfileHistories.parameterPartial u w := by
  have hd := (ProfileHistories.parameterPartial_hasDerivAt globalDomain hu.contDiffOn (mem_univ
    w)).const_mul w.1
  have he := ProfileHistories.parameterPartial_hasDerivAt globalDomain
    (weightedAxial_contDiff hu).contDiffOn (mem_univ w)
  exact he.unique hd

theorem massHistory_parameterPartial {u : JointProfile} (hu : ContDiff ℝ ∞ u) (w : ℝ × ℝ) :
    ProfileHistories.parameterPartial (massHistory u) w = parameterMassHistory u w :=
  ProfileHistories.parameterPartial_primitive globalDomain (weightedAxial_contDiff hu).contDiffOn
    (mem_univ w)

/-- Genuine radial differentiation of the integral formula gives incompressibility. -/
theorem fluxHistory_hasDerivAt (h lam : ℝ) {u : JointProfile} (hu : ContDiff ℝ ∞ u)
    (w : ℝ × ℝ) :
    HasDerivAt (fun R => fluxHistory h lam u (R, w.2))
      (-w.1 * radialZ h (-PositiveAxisSystem.a h + lam) u w) w.1 := by
  have hdu := ProfileHistories.radialPartial_hasDerivAt globalDomain hu.contDiffOn (mem_univ w)
  have hdm := primitive_hasDerivAt (weightedAxial_contDiff hu) w
  have hdn := primitive_hasDerivAt (parameterPartial_contDiff (weightedAxial_contDiff hu)) w
  have hd := (((((hasDerivAt_id w.1).fun_pow 2).fun_mul hdu).const_mul w.2).sub
    (hdm.const_mul (2 * w.2 * (PositiveAxisSystem.dScale h + lam)))).sub
      (hdn.const_mul (PositiveAxisSystem.edge w.2))
  have he := hd.div_const (PositiveAxisSystem.ell h w.2)
  rw [weightedAxial_parameterPartial hu w] at he
  convert! he using 1
  · funext R
    simp [fluxHistory, massHistory, parameterMassHistory, id_eq]
    ring
  · simp only [weightedAxial, radialZ, PositiveAxisSystem.a, PositiveAxisSystem.dScale,
      id_eq, div_eq_mul_inv]
    ring

/-- The first repaired row is exactly the mass condition making the recomputed
radial flux vanish outside the source. Parameter differentiation is justified
by the actual smooth history theorem. -/
theorem fluxHistory_exterior (h lam : ℝ) {u : JointProfile} (hu : ContDiff ℝ ∞ u) {B : ℝ}
    (hB : 0 ≤ B) (hs : ∀ eta R, B ≤ R → u (R, eta) = 0)
    (hm : ∀ eta, positiveIntegral (fun R => R * u (R, eta)) = 0)
    {R eta : ℝ} (hR : B ≤ R) : fluxHistory h lam u (R, eta) = 0 := by
  have hmass : ∀ z, massHistory u (R, z) = 0 := by
    intro z
    rw [massHistory, ProfileHistories.primitive,
      ← positiveIntegral_eq_primitive hB hR (fun t ht => by
        change t * u (t, z) = 0
        rw [hs z t ht, mul_zero])]
    exact hm z
  have hp : parameterMassHistory u (R, eta) = 0 := by
    rw [← massHistory_parameterPartial hu]
    have hd := ProfileHistories.parameterPartial_hasDerivAt globalDomain
      (primitive_contDiff (weightedAxial_contDiff hu)).contDiffOn (mem_univ (R, eta))
    have he : (fun z => massHistory u (R, z)) = fun _ => (0 : ℝ) := funext hmass
    change HasDerivAt (fun z => massHistory u (R, z)) _ eta at hd
    rw [he] at hd
    exact hd.unique (hasDerivAt_const eta 0)
  simp [fluxHistory, hs eta R hR, hmass eta, hp]


/-- The first row of the actual five-moment system gives the required mass
condition for the recomputed divergence flux. -/
theorem fluxHistory_exterior_of_moments (h lam : ℝ) {n : ℕ} {u e : JointHistory}
    {omega : JointProfile} (hu : ContDiff ℝ ∞ (u n)) {B : ℝ}
    (hB : 0 ≤ B) (hs : ∀ eta R, B ≤ R → u n (R, eta) = 0)
    (hm : ∀ eta, moments n (slice u eta) (slice e eta) (fun R => omega (R, eta)) = 0)
    {R eta : ℝ} (hR : B ≤ R) : fluxHistory h lam (u n) (R, eta) = 0 := by
  apply fluxHistory_exterior h lam hu hB hs _ hR
  intro eta
  exact congrFun (hm eta) 0

/-- The pressure integration-by-parts identity underlying the fifth row is
proved for the actual pressure primitive, including its exterior boundary. -/
theorem pressure_weighted_identity {q : JointProfile} (hq : ContDiff ℝ ∞ q) {B : ℝ}
    (hB : 0 ≤ B) (hs : ∀ eta R, B ≤ R → q (R, eta) = 0)
    (hm : ∀ eta, positiveIntegral (fun R => q (R, eta)) = 0) (eta : ℝ) :
    positiveIntegral (fun R => R * ProfileHistories.primitive q (R, eta)) =
      -(1 / 2 : ℝ) * positiveIntegral (fun R => R ^ 2 * q (R, eta)) := by
  have hPzero : ∀ R, B ≤ R → ProfileHistories.primitive q (R, eta) = 0 := by
    intro R hR
    rw [ProfileHistories.primitive, ← positiveIntegral_eq_primitive hB hR (hs eta), hm eta]
  have hPc : Continuous (fun R => ProfileHistories.primitive q (R, eta)) :=
    (primitive_contDiff hq).continuous.comp (continuous_id.prodMk continuous_const)
  have hqc : Continuous (fun R => q (R, eta)) :=
    hq.continuous.comp (continuous_id.prodMk continuous_const)
  have hpow : ∀ R : ℝ, HasDerivAt (fun t => t ^ 2 / 2) R R := by
    intro R
    convert! ((hasDerivAt_id R).pow 2).div_const 2 using 1
    simp
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := B)
    (u := fun R : ℝ => R ^ 2 / 2) (u' := fun R => R)
    (v := fun R => ProfileHistories.primitive q (R, eta)) (v' := fun R => q (R, eta))
    ((continuous_id.pow 2).div_const 2).continuousOn hPc.continuousOn
    (fun R _ => hpow R) (fun R _ => primitive_hasDerivAt hq (R, eta))
    (continuous_id.intervalIntegrable 0 B) (hqc.intervalIntegrable 0 B)
  have he : (fun R => R ^ 2 / 2 * q (R, eta)) =
      (fun R => (1 / 2 : ℝ) * (R ^ 2 * q (R, eta))) := by funext R; ring
  rw [he, intervalIntegral.integral_const_mul] at hi
  rw [hPzero B le_rfl] at hi
  rw [positiveIntegral_eq_primitive hB le_rfl (fun R hR => by rw [hPzero R hR, mul_zero]),
    positiveIntegral_eq_primitive hB le_rfl (fun R hR => by rw [hs eta R hR, mul_zero])]
  simp only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_sub] at hi
  linarith

/-- Open parameter domains retain all radial histories while keeping the
original parameter domain; no extension across its endpoints is needed. -/
noncomputable def parameterDomain (S : Set ℝ) (hS : IsOpen S) : ProfileHistories.RadialDomain where
  carrier := univ ×ˢ S
  isOpen := isOpen_univ.prod hS
  scale_mem := by intro p hp t ht; exact ⟨mem_univ _, hp.2⟩

/-- The pressure reconstruction needs smoothness only on the working
parameter domain. -/
theorem pressureHistory_contDiffOn {S : Set ℝ} (hS : IsOpen S)
    {n : ℕ} {e : JointHistory} {omega : JointProfile}
    (hq : ContDiffOn ℝ ∞ (jointPressureGradient n e omega) (univ ×ˢ S)) :
    ContDiffOn ℝ ∞ (pressureHistory n e omega) (univ ×ˢ S) :=
  ProfileHistories.primitive_smooth (parameterDomain S hS) hq

theorem pressureHistory_hasDerivAt_on {S : Set ℝ} (hS : IsOpen S)
    {n : ℕ} {e : JointHistory} {omega : JointProfile}
    (hq : ContDiffOn ℝ ∞ (jointPressureGradient n e omega) (univ ×ˢ S))
    {R eta : ℝ} (heta : eta ∈ S) :
    HasDerivAt (fun r => pressureHistory n e omega (r, eta))
      (jointPressureGradient n e omega (R, eta)) R :=
  ProfileHistories.primitive_hasDerivAt (parameterDomain S hS)
    (F := jointPressureGradient n e omega) hq (p := (R, eta)) ⟨mem_univ _, heta⟩

theorem pressureHistory_exterior_on {S : Set ℝ} {n : ℕ}
    {u e : JointHistory} {omega : JointProfile} {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → jointPressureGradient n e omega (R, eta) = 0)
    (hm : ∀ eta ∈ S, moments n (slice u eta) (slice e eta) (fun R => omega (R, eta)) = 0)
    {R eta : ℝ} (hR : B ≤ R) (heta : eta ∈ S) : pressureHistory n e omega (R, eta) = 0 := by
  rw [pressureHistory, ProfileHistories.primitive,
    ← positiveIntegral_eq_primitive hB hR (hs eta heta)]
  exact congrFun (hm eta heta) 2

theorem weightedAxial_parameterPartial_on {S : Set ℝ} (hS : IsOpen S)
    {u : JointProfile} (hu : ContDiffOn ℝ ∞ u (univ ×ˢ S))
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    ProfileHistories.parameterPartial (weightedAxial u) w =
      w.1 * ProfileHistories.parameterPartial u w := by
  have hd := (ProfileHistories.parameterPartial_hasDerivAt (parameterDomain S hS)
    hu (p := w) ⟨mem_univ _, hw⟩).const_mul w.1
  have he := ProfileHistories.parameterPartial_hasDerivAt (parameterDomain S hS)
    (contDiffOn_fst.mul hu) (p := w) ⟨mem_univ _, hw⟩
  exact he.unique hd

theorem massHistory_parameterPartial_on {S : Set ℝ} (hS : IsOpen S)
    {u : JointProfile} (hu : ContDiffOn ℝ ∞ u (univ ×ˢ S))
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    ProfileHistories.parameterPartial (massHistory u) w = parameterMassHistory u w :=
  ProfileHistories.parameterPartial_primitive (parameterDomain S hS)
    (contDiffOn_fst.mul hu) ⟨mem_univ _, hw⟩

theorem fluxHistory_contDiffOn (h lam : ℝ) {S : Set ℝ} (hS : IsOpen S)
    {u : JointProfile} (hu : ContDiffOn ℝ ∞ u (univ ×ˢ S))
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) :
    ContDiffOn ℝ ∞ (fluxHistory h lam u) (univ ×ˢ S) := by
  have hm : ContDiffOn ℝ ∞ (massHistory u) (univ ×ˢ S) :=
    ProfileHistories.primitive_smooth (parameterDomain S hS) (contDiffOn_fst.mul hu)
  have hn : ContDiffOn ℝ ∞ (parameterMassHistory u) (univ ×ˢ S) :=
    ProfileHistories.primitive_smooth (parameterDomain S hS)
      (ProfileHistories.parameterPartial_smooth (parameterDomain S hS) (contDiffOn_fst.mul hu))
  have he : ContDiffOn ℝ ∞ (fun w : ℝ × ℝ => PositiveAxisSystem.edge w.2) (univ ×ˢ S) := by
    exact contDiffOn_const.sub (contDiffOn_snd.pow 2)
  have hl : ContDiffOn ℝ ∞ (fun w : ℝ × ℝ => PositiveAxisSystem.ell h w.2) (univ ×ˢ S) := by
    exact contDiffOn_const.sub (contDiffOn_const.mul (contDiffOn_snd.pow 2))
  exact ((((contDiffOn_snd.mul (contDiffOn_fst.pow 2)).mul hu).sub
    (((contDiffOn_const.mul contDiffOn_snd).mul contDiffOn_const).mul hm)).sub
      (he.mul hn)).div hl (fun w hw => hell w.2 hw.2)

/-- The actual radial divergence equation holds on an open parameter domain,
without any smooth extension past that domain. -/
theorem fluxHistory_hasDerivAt_on (h lam : ℝ) {S : Set ℝ} (hS : IsOpen S)
    {u : JointProfile} (hu : ContDiffOn ℝ ∞ u (univ ×ˢ S))
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    HasDerivAt (fun R => fluxHistory h lam u (R, w.2))
      (-w.1 * radialZ h (-PositiveAxisSystem.a h + lam) u w) w.1 := by
  have huw : ContDiffOn ℝ ∞ (weightedAxial u) (univ ×ˢ S) := contDiffOn_fst.mul hu
  have hdu := ProfileHistories.radialPartial_hasDerivAt (parameterDomain S hS) hu (p := w)
    ⟨mem_univ _, hw⟩
  have hdm := ProfileHistories.primitive_hasDerivAt (parameterDomain S hS)
    huw (p := w) ⟨mem_univ _, hw⟩
  have hdn := ProfileHistories.primitive_hasDerivAt (parameterDomain S hS)
    (ProfileHistories.parameterPartial_smooth (parameterDomain S hS) huw)
    (p := w) ⟨mem_univ _, hw⟩
  have hd := (((((hasDerivAt_id w.1).fun_pow 2).fun_mul hdu).const_mul w.2).sub
    (hdm.const_mul (2 * w.2 * (PositiveAxisSystem.dScale h + lam)))).sub
      (hdn.const_mul (PositiveAxisSystem.edge w.2))
  have he := hd.div_const (PositiveAxisSystem.ell h w.2)
  rw [weightedAxial_parameterPartial_on hS hu hw] at he
  convert! he using 1
  · funext R
    simp [fluxHistory, massHistory, parameterMassHistory, id_eq]
    ring
  · simp only [weightedAxial, radialZ, PositiveAxisSystem.a, PositiveAxisSystem.dScale,
      id_eq, div_eq_mul_inv]
    ring

theorem fluxHistory_exterior_on (h lam : ℝ) {S : Set ℝ} (hS : IsOpen S)
    {u : JointProfile} (hu : ContDiffOn ℝ ∞ u (univ ×ˢ S)) {B : ℝ}
    (hB : 0 ≤ B) (hs : ∀ eta ∈ S, ∀ R, B ≤ R → u (R, eta) = 0)
    (hm : ∀ eta ∈ S, positiveIntegral (fun R => R * u (R, eta)) = 0)
    {R eta : ℝ} (hR : B ≤ R) (heta : eta ∈ S) : fluxHistory h lam u (R, eta) = 0 := by
  have hmass : ∀ z ∈ S, massHistory u (R, z) = 0 := by
    intro z hz
    rw [massHistory, ProfileHistories.primitive,
      ← positiveIntegral_eq_primitive hB hR (fun t ht => by
        change t * u (t, z) = 0
        rw [hs z hz t ht, mul_zero])]
    exact hm z hz
  have hp : parameterMassHistory u (R, eta) = 0 := by
    rw [← massHistory_parameterPartial_on hS hu heta]
    have hd := ProfileHistories.parameterPartial_hasDerivAt (parameterDomain S hS)
      (ProfileHistories.primitive_smooth (parameterDomain S hS) (contDiffOn_fst.mul hu))
      (show (R, eta) ∈ univ ×ˢ S from ⟨mem_univ _, heta⟩)
    have he : (fun z => massHistory u (R, z)) =ᶠ[nhds eta] fun _ => (0 : ℝ) := by
      filter_upwards [hS.mem_nhds heta] with z hz using hmass z hz
    exact hd.unique ((hasDerivAt_const eta 0).congr_of_eventuallyEq he)
  simp [fluxHistory, hs eta heta R hR, hmass eta heta, hp]

/-- Smoothness of the actual total moment follows from common compact radial
support and the proved smooth history theorem. -/
theorem positiveIntegral_contDiffOn {S : Set ℝ} (hS : IsOpen S) {F : JointProfile}
    (hF : ContDiffOn ℝ ∞ F (univ ×ˢ S)) {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → F (R, eta) = 0) :
    ContDiffOn ℝ ∞ (fun eta => positiveIntegral (fun R => F (R, eta))) S := by
  have hp := ProfileHistories.primitive_smooth (parameterDomain S hS) hF
  have hc : ContDiffOn ℝ ∞ (fun eta => ProfileHistories.primitive F (B, eta)) S :=
    hp.comp (contDiffOn_const.prodMk contDiffOn_id) (fun eta heta => ⟨mem_univ _, heta⟩)
  apply hc.congr
  intro eta heta
  exact positiveIntegral_eq_primitive hB le_rfl (hs eta heta)

noncomputable def jointRowDensity (n : ℕ) (u e : JointHistory) (omega : JointProfile)
    (w : ℝ × ℝ) : Debt := rowDensity n (slice u w.2) (slice e w.2) (fun R => omega (R, w.2)) w.1

theorem cauchy_eq_zero_of_left (n : ℕ) (u v : History) (R : ℝ)
    (hu : ∀ j, j ≤ n → u j R = 0) : cauchy n u v R = 0 := by
  unfold cauchy PositiveAxisSystem.convolution
  apply Finset.sum_eq_zero
  intro j hj
  change u j R * v (n - j) R = 0
  rw [hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), zero_mul]

theorem cauchy_self_eq_zero_of_positive {n : ℕ} (hn : 0 < n) (e : History) (R : ℝ)
    (he : ∀ j, 0 < j → j ≤ n → e j R = 0) : cauchy n e e R = 0 := by
  unfold cauchy PositiveAxisSystem.convolution
  apply Finset.sum_eq_zero
  intro j hj
  change e j R * e (n - j) R = 0
  by_cases hj0 : j = 0
  · subst j
    simp only [Nat.sub_zero, he n hn le_rfl, mul_zero]
  · rw [he j (Nat.pos_of_ne_zero hj0) (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), zero_mul]

theorem jointCauchy_contDiffOn {S : Set (ℝ × ℝ)} {n : ℕ} {u v : JointHistory}
    (hu : ∀ j, j ≤ n → ContDiffOn ℝ ∞ (u j) S)
    (hv : ∀ j, j ≤ n → ContDiffOn ℝ ∞ (v j) S) :
    ContDiffOn ℝ ∞ (fun w => cauchy n (slice u w.2) (slice v w.2) w.1) S := by
  change ContDiffOn ℝ ∞ (fun w => ∑ j ∈ Finset.range (n + 1), u j w * v (n - j) w) S
  apply ContDiffOn.sum
  intro j hj
  exact (hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).mul (hv (n - j) (Nat.sub_le _ _))

theorem jointRowDensity_contDiffOn {S : Set (ℝ × ℝ)} {n : ℕ}
    {u e : JointHistory} {omega : JointProfile}
    (hu : ∀ j, j ≤ n → ContDiffOn ℝ ∞ (u j) S)
    (he : ∀ j, j ≤ n → ContDiffOn ℝ ∞ (e j) S)
    (hq : ContDiffOn ℝ ∞ (jointPressureGradient n e omega) S) (i : Fin 5) :
    ContDiffOn ℝ ∞ (fun w => jointRowDensity n u e omega w i) S := by
  fin_cases i
  · exact contDiffOn_fst.mul (hu n le_rfl)
  · exact (contDiffOn_fst.pow 2).mul (he n le_rfl)
  · exact hq
  · exact (contDiffOn_fst.pow 2).mul (jointCauchy_contDiffOn hu he)
  · exact (contDiffOn_fst.mul (jointCauchy_contDiffOn hu hu)).sub
      (((contDiffOn_fst.pow 2).div_const 2).mul hq)

/-- The order-zero angular tail need not be compact: every summand of the
positive-order self-convolution contains a strictly positive index. -/
theorem jointRowDensity_exterior {n : ℕ} (hn : 0 < n) (u e : JointHistory) (omega : JointProfile)
    (w : ℝ × ℝ) (hu : ∀ j, j ≤ n → u j w = 0)
    (he : ∀ j, 0 < j → j ≤ n → e j w = 0) (hw : omega w = 0) :
    jointRowDensity n u e omega w = 0 := by
  have h1 := cauchy_eq_zero_of_left n (slice u w.2) (slice e w.2) w.1 hu
  have h2 := cauchy_eq_zero_of_left n (slice u w.2) (slice u w.2) w.1 hu
  have h3 := cauchy_self_eq_zero_of_positive hn (slice e w.2) w.1 he
  ext i
  fin_cases i <;> simp [jointRowDensity, rowDensity, pressureGradient, h1, h2, h3,
    slice, hu n le_rfl, he n hn le_rfl, hw]

/-- This statement derives smoothness of the five genuine integral debts;
the density hypotheses can be checked componentwise from the known fields. -/
theorem moments_contDiffOn {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {u e : JointHistory} {omega : JointProfile}
    (hd : ∀ i, ContDiffOn ℝ ∞ (fun w => jointRowDensity n u e omega w i) (univ ×ˢ S))
    {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → jointRowDensity n u e omega (R, eta) = 0) :
    ContDiffOn ℝ ∞ (fun eta => moments n (slice u eta) (slice e eta) (fun R => omega (R, eta))) S
      := by
  apply contDiffOn_pi.mpr
  intro i
  exact positiveIntegral_contDiffOn hS (hd i) hB
    (fun eta heta R hR => congrFun (hs eta heta R hR) i)

theorem moments_contDiffOn_of_histories {S : Set ℝ} (hS : IsOpen S) {n : ℕ} (hn : 0 < n)
    {u e : JointHistory} {omega : JointProfile}
    (hu : ∀ j, j ≤ n → ContDiffOn ℝ ∞ (u j) (univ ×ˢ S))
    (he : ∀ j, j ≤ n → ContDiffOn ℝ ∞ (e j) (univ ×ˢ S))
    (hq : ContDiffOn ℝ ∞ (jointPressureGradient n e omega) (univ ×ˢ S))
    {B : ℝ} (hB : 0 ≤ B)
    (hU : ∀ eta ∈ S, ∀ R, B ≤ R → ∀ j, j ≤ n → u j (R, eta) = 0)
    (hE : ∀ eta ∈ S, ∀ R, B ≤ R → ∀ j, 0 < j → j ≤ n → e j (R, eta) = 0)
    (hOmega : ∀ eta ∈ S, ∀ R, B ≤ R → omega (R, eta) = 0) :
    ContDiffOn ℝ ∞ (fun eta => moments n (slice u eta) (slice e eta) (fun R => omega (R, eta))) S
      := by
  apply moments_contDiffOn hS (jointRowDensity_contDiffOn hu he hq) hB
  intro eta heta R hR
  exact jointRowDensity_exterior hn u e omega (R, eta)
    (hU eta heta R hR) (hE eta heta R hR) (hOmega eta heta R hR)

/-- In particular, the exact zero-moment corrections vary smoothly with η
when their debts are the actual profile integrals, not prescribed surrogates. -/
theorem exact_corrections_joint_contDiffOn (lam a b : ℝ) {S : Set ℝ} (hS : IsOpen S)
    {n : ℕ} {u e : JointHistory} {omega : JointProfile} {A : ℝ → ℝ}
    (hA : ContDiffOn ℝ ∞ A S) (hAn : ∀ eta ∈ S, A eta ≠ 0)
    (hd : ∀ i, ContDiffOn ℝ ∞ (fun w => jointRowDensity n u e omega w i) (univ ×ˢ S))
    {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → jointRowDensity n u e omega (R, eta) = 0) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
      (repairU lam (A z.1) a b (-moments n (slice u z.1) (slice e z.1) (fun R => omega (R, z.1)))
        z.2,
       repairE lam (A z.1) a b (-moments n (slice u z.1) (slice e z.1) (fun R => omega (R, z.1)))
         z.2))
      (S ×ˢ univ) :=
  by
    have hm := moments_contDiffOn (S := S) (n := n) (u := u) (e := e)
      (omega := omega) hS hd hB hs
    exact (repairU_joint_contDiffOn (P := ℝ) lam a b (S := S) (A := A)
      (d := fun eta => -moments n (slice u eta) (slice e eta) (fun R => omega (R, eta)))
      hA hm.neg hAn).prodMk
      (repairE_joint_contDiffOn (P := ℝ) lam a b (S := S) (A := A)
        (d := fun eta => -moments n (slice u eta) (slice e eta) (fun R => omega (R, eta)))
        hA hm.neg hAn)


theorem positive_integrableOn_of_compact {f : Profile} {B : ℝ}
    (hf : ContinuousOn f (Icc 0 B)) (hs : ∀ R, B ≤ R → f R = 0) :
    IntegrableOn f (Ioi 0) := by
  have hi : IntegrableOn f (Ioc 0 B) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply hi.of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
  apply Filter.Eventually.of_forall
  intro R hR
  have hBR : B < R := by
    by_contra h
    exact hR.2 ⟨hR.1, le_of_not_gt h⟩
  exact hs R hBR.le

/-- The integrability requirements of the repair theorem follow from the
same common compact support and smoothness used for the parameter jets. -/
theorem jointRowDensity_integrableOn {S : Set ℝ} {n : ℕ}
    {u e : JointHistory} {omega : JointProfile}
    (hd : ∀ i, ContinuousOn (fun w => jointRowDensity n u e omega w i) (univ ×ˢ S))
    {B : ℝ} (hs : ∀ eta ∈ S, ∀ R, B ≤ R → jointRowDensity n u e omega (R, eta) = 0)
    {eta : ℝ} (heta : eta ∈ S) (i : Fin 5) :
    IntegrableOn (fun R => rowDensity n (slice u eta) (slice e eta)
      (fun r => omega (r, eta)) R i) (Ioi 0) := by
  apply positive_integrableOn_of_compact (B := B)
  · exact (hd i).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun R hR => ⟨mem_univ _, heta⟩)
  · intro R hR
    exact congrFun (hs eta heta R hR) i

/-- A single explicit smooth family repairs all five rows on the parameter
domain. Its debts are the actual finite-profile integrals; only order n is
changed, and the known Ω term remains untouched. -/
theorem exists_parameterized_exact_repair (lam a b : ℝ) (hlam : 0 < lam)
    (ha : 0 < a) (hab : a < b) {S : Set ℝ} (hS : IsOpen S)
    {n : ℕ} (hn : 0 < n) (u e : JointHistory) (omega : JointProfile) (A : ℝ → ℝ)
    (hA : ContDiffOn ℝ ∞ A S) (hAn : ∀ eta ∈ S, A eta ≠ 0)
    (hU₀ : ∀ eta ∈ S, ∀ R ∈ Ioo a b, u 0 (R, eta) = 0)
    (hE₀ : ∀ eta ∈ S, ∀ R ∈ Ioo a b, e 0 (R, eta) = FiveRowRank.background lam (A eta) R)
    (hd : ∀ i, ContDiffOn ℝ ∞ (fun w => jointRowDensity n u e omega w i) (univ ×ˢ S))
    {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → jointRowDensity n u e omega (R, eta) = 0) :
    ∃ du de : JointProfile,
      ContDiffOn ℝ ∞ du (univ ×ˢ S) ∧ ContDiffOn ℝ ∞ de (univ ×ˢ S) ∧
      (∀ eta, tsupport (fun R => du (R, eta)) ⊆ Ioo a b) ∧
      (∀ eta, tsupport (fun R => de (R, eta)) ⊆ Ioo a b) ∧
      ∀ eta ∈ S, moments n (increment (slice u eta) n (fun R => du (R, eta)))
        (increment (slice e eta) n (fun R => de (R, eta))) (fun R => omega (R, eta)) = 0 := by
  let debt : ℝ → Debt := fun eta => -moments n (slice u eta) (slice e eta) (fun R => omega (R, eta))
  let du : JointProfile := fun w => repairU lam (A w.2) a b (debt w.2) w.1
  let de : JointProfile := fun w => repairE lam (A w.2) a b (debt w.2) w.1
  have hdebt : ContDiffOn ℝ ∞ debt S :=
    (moments_contDiffOn (S := S) (n := n) (u := u) (e := e) (omega := omega) hS hd hB hs).neg
  have hswap : ContDiffOn ℝ ∞ (fun w : ℝ × ℝ => (w.2, w.1)) (univ ×ˢ S) :=
    contDiffOn_snd.prodMk contDiffOn_fst
  have hswap_mem : MapsTo (fun w : ℝ × ℝ => (w.2, w.1)) (univ ×ˢ S) (S ×ˢ univ) :=
    fun w hw => ⟨hw.2, mem_univ _⟩
  have hdu : ContDiffOn ℝ ∞ du (univ ×ˢ S) :=
    (repairU_joint_contDiffOn (P := ℝ) lam a b (S := S) (A := A) (d := debt) hA hdebt hAn).comp
      (f := fun w : ℝ × ℝ => (w.2, w.1)) hswap hswap_mem
  have hde : ContDiffOn ℝ ∞ de (univ ×ˢ S) :=
    (repairE_joint_contDiffOn (P := ℝ) lam a b (S := S) (A := A) (d := debt) hA hdebt hAn).comp
      (f := fun w : ℝ × ℝ => (w.2, w.1)) hswap hswap_mem
  refine ⟨du, de, hdu, hde, ?_, ?_, ?_⟩
  · intro eta
    exact repairU_tsupport lam (A eta) a b (debt eta) hab
  · intro eta
    exact repairE_tsupport lam (A eta) a b (debt eta) hab
  · intro eta heta
    have hi := jointRowDensity_integrableOn (S := S) (n := n) (u := u) (e := e)
      (omega := omega) (B := B) (fun i => (hd i).continuousOn) hs heta
    simpa only [du, de, debt, zero_sub] using moments_repair_target lam (A eta) a b 0 hn
      (slice u eta) (slice e eta) (fun R => omega (R, eta)) hlam (hAn eta heta) ha hab
      (hU₀ eta heta) (hE₀ eta heta) hi

end PhysicalHistories

end NavierStokes.PositiveOrderMoments
