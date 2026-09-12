/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowExpansionResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveAxisSystem
public import LeanPool.NavierStokesAndEuler.NavierStokes.FiveRowRank

/-!
# Positive slow-order tangential stress support

The moments are actual positive-radius integrals. All radial and parameter
operators use the actual Frechet derivatives. Compact stress support is a
consequence of the repaired moments and the differential equations.
-/

section

/-!
# Actual five-row repair at positive slow order

Only the order-n entries of the histories are changed. Endpoint extraction
proves that all five actual moment increments are linear, including pressure
with the known previous-order radial residual retained.
-/

@[expose] public section

noncomputable section

open Set Function MeasureTheory
open scoped BigOperators ContDiff

namespace NavierStokes.PositiveOrderMoments

/-- Profile: an abbreviation for `ℝ → ℝ`. -/
abbrev Profile := ℝ → ℝ
/-- History: an abbreviation for `ℕ → Profile`. -/
abbrev History := ℕ → Profile
/-- Debt: an abbreviation for `Fin 5 → ℝ`. -/
abbrev Debt := Fin 5 → ℝ

/-- Cauchy, given by `PositiveAxisSystem.convolution n (fun i j => u i R * v j R)`. -/
noncomputable def cauchy (n : ℕ) (u v : History) (R : ℝ) : ℝ :=
  PositiveAxisSystem.convolution n (fun i j => u i R * v j R)

/-- Increment, given by `Function.update u n (fun R => u n R + du R)`. -/
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

/-- Positive integral, given by `∫ R in Ioi (0 : ℝ), f R`. -/
noncomputable def positiveIntegral (f : Profile) : ℝ := ∫ R in Ioi (0 : ℝ), f R

/-- Moments, defined pointwise by `positiveIntegral (fun R => rowDensity n u e omega R i)`. -/
noncomputable def moments (n : ℕ) (u e : History) (omega : Profile) : Debt :=
  fun i => positiveIntegral (fun R => rowDensity n u e omega R i)

/-- Linear density, given by `![R * du R, R ^ 2 * de R, 2 * e₀ R * de R / R, R ^ 2 * (u₀ R * de
R + du R * e₀ R), 2 * R * u₀ R * du R - R * e₀ R * de R]`. -/
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

/-- Weighted density, given by `![R * du R, R ^ 2 * de R, (2 * A) * (R ^ (-2 - 2 * lam) * de R),
A * (R ^ (1 - 2 * lam) * du R), (-A) * (R ^ (-2 * lam) * de R)]`. -/
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
    fin_cases i <;> simp only [linearDensity, he R hR, hu R hR, zero_mul, zero_add, mul_zero,
        zero_sub, Fin.zero_eta, Fin.isValue,
                      Matrix.cons_val_zero, weightedDensity, neg_mul, Fin.mk_one,
                          Matrix.cons_val_one,
                      Fin.reduceFinMk, Matrix.cons_val, neg_inj]
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

/-- Repair U, given by `LocalizedMomentRepair.repair (FiveRowRank.axialPowers lam)
(FiveRowRank.cellLower a b) (FiveRowRank.cellUpper a b) (axialDebt A d)`. -/
noncomputable def repairU (lam A a b : ℝ) (d : Debt) : Profile :=
  LocalizedMomentRepair.repair (FiveRowRank.axialPowers lam)
    (FiveRowRank.cellLower a b) (FiveRowRank.cellUpper a b) (axialDebt A d)

/-- Repair E, constructed using `LocalizedMomentRepair.repair`. -/
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
    simp only [FiveRowRank.angularPowers, neg_mul, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero,
      angularDebt] at hm
    rw [hm]
    field_simp
  · change (∫ R, A * (R ^ (1 - 2 * lam) * repairU lam A a b d R)) = d 3
    rw [integral_const_mul]
    have hm := hu 1
    simp only [FiveRowRank.axialPowers, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      axialDebt] at hm
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

/-- Joint profile: an abbreviation for `ℝ × ℝ → ℝ`. -/
abbrev JointProfile := ℝ × ℝ → ℝ
/-- Joint history: an abbreviation for `ℕ → JointProfile`. -/
abbrev JointHistory := ℕ → JointProfile

/-- Slice, defined pointwise by `f j (R, eta)`. -/
noncomputable def slice (f : JointHistory) (eta : ℝ) : History := fun j R => f j (R, eta)

/-- Joint increment, given by `Function.update u n (fun w => u n w + du w)`. -/
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

/-- Global domain, bundling `carrier`, `isOpen`, `scale_mem`. -/
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

/-- Joint pressure gradient, given by `pressureGradient n (slice e w.2) (fun R => omega (R,
w.2)) w.1`. -/
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

/-- Weighted axial, given by `w.1 * u w`. -/
noncomputable def weightedAxial (u : JointProfile) (w : ℝ × ℝ) : ℝ := w.1 * u w

/-- Mass history, given by `ProfileHistories.primitive (weightedAxial u)`. -/
noncomputable def massHistory (u : JointProfile) : JointProfile :=
  ProfileHistories.primitive (weightedAxial u)

/-- Parameter mass history, given by `ProfileHistories.primitive
(ProfileHistories.parameterPartial (weightedAxial u))`. -/
noncomputable def parameterMassHistory (u : JointProfile) : JointProfile :=
  ProfileHistories.primitive (ProfileHistories.parameterPartial (weightedAxial u))

/-- The R-coordinate version of (21), with both histories given by actual integrals. -/
noncomputable def fluxHistory (h lam : ℝ) (u : JointProfile) (w : ℝ × ℝ) : ℝ :=
  (w.2 * w.1 ^ 2 * u w - 2 * w.2 * (PositiveAxisSystem.dScale h + lam) * massHistory u w -
    PositiveAxisSystem.edge w.2 * parameterMassHistory u w) / PositiveAxisSystem.ell h w.2

/-- Radial Z as an element of `ℝ`. -/
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

/-- Joint row density, given by `rowDensity n (slice u w.2) (slice e w.2) (fun R => omega (R,
w.2)) w.1`. -/
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

end
end

end

@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace NavierStokes.SlowStressSupport

/-- Field: an abbreviation for `ℝ × ℝ → ℝ`. -/
abbrev Field := ℝ × ℝ → ℝ
/-- History: an abbreviation for `ℕ → Field`. -/
abbrev History := ℕ → Field
/-- Dr, given by `ProfileHistories.radialPartial`. -/
noncomputable def dr := ProfileHistories.radialPartial
/-- De, given by `ProfileHistories.parameterPartial`. -/
noncomputable def de := ProfileHistories.parameterPartial
/-- Region: an abbreviation for `(univ : Set ℝ) ×ˢ S`. -/
abbrev region (S : Set ℝ) := (univ : Set ℝ) ×ˢ S
/-- Smooth: an abbreviation for `ContDiffOn ℝ ∞ f (region S)`. -/
abbrev Smooth (S : Set ℝ) (f : Field) := ContDiffOn ℝ ∞ f (region S)

/-- Exterior, given by `∀ eta ∈ S, ∀ R, B ≤ R → f (R, eta) = 0`. -/
noncomputable def exterior (B : ℝ) (S : Set ℝ) (f : Field) : Prop :=
  ∀ eta ∈ S, ∀ R, B ≤ R → f (R, eta) = 0

/-- Weighted, given by `w.1 ^ m * f w`. -/
noncomputable def weighted (m : ℕ) (f : Field) (w : ℝ × ℝ) : ℝ := w.1 ^ m * f w

/-- Moment, given by `∫ R in (0 : ℝ)..B, R ^ m * f (R, eta)`. -/
noncomputable def moment (B : ℝ) (m : ℕ) (f : Field) (eta : ℝ) : ℝ :=
  ∫ R in (0 : ℝ)..B, R ^ m * f (R, eta)

/-- Time op, given by `(-b * f w + PositiveAxisSystem.dScale h * w.2 * de f w + w.1 / 2 * dr f
w) / PositiveAxisSystem.ell h w.2`. -/
noncomputable def timeOp (h b : ℝ) (f : Field) (w : ℝ × ℝ) : ℝ :=
  (-b * f w + PositiveAxisSystem.dScale h * w.2 * de f w + w.1 / 2 * dr f w) /
    PositiveAxisSystem.ell h w.2

/-- Axial op, given by `(2 * w.2 * b * f w + PositiveAxisSystem.edge w.2 * de f w - w.2 * w.1 *
dr f w) / PositiveAxisSystem.ell h w.2`. -/
noncomputable def axialOp (h b : ℝ) (f : Field) (w : ℝ × ℝ) : ℝ :=
  (2 * w.2 * b * f w + PositiveAxisSystem.edge w.2 * de f w - w.2 * w.1 * dr f w) /
    PositiveAxisSystem.ell h w.2

/-- Axial Op2, given by `axialOp h (b - PositiveAxisSystem.dScale h) (axialOp h b f)`. -/
noncomputable def axialOp2 (h b : ℝ) (f : Field) : Field :=
  axialOp h (b - PositiveAxisSystem.dScale h) (axialOp h b f)

theorem smooth_dr {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f) :
    Smooth S (dr f) :=
  ProfileHistories.radialPartial_smooth (PositiveOrderMoments.parameterDomain S hS) hf

theorem smooth_de {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f) :
    Smooth S (de f) :=
  ProfileHistories.parameterPartial_smooth (PositiveOrderMoments.parameterDomain S hS) hf

theorem smooth_weighted {S : Set ℝ} {f : Field} (hf : Smooth S f) (m : ℕ) :
    Smooth S (weighted m f) := (contDiffOn_fst.pow m).mul hf

theorem slice_smooth {S : Set ℝ} {f : Field} (hf : Smooth S f)
    {eta : ℝ} (heta : eta ∈ S) : ContDiff ℝ ∞ (fun R => f (R, eta)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ _ => ⟨mem_univ _, heta⟩)

theorem radial_hasDerivAt {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) : HasDerivAt (fun R => f (R, w.2)) (dr f w) w.1 :=
  ProfileHistories.radialPartial_hasDerivAt (PositiveOrderMoments.parameterDomain S hS)
    hf (p := w) ⟨mem_univ _, hw⟩

theorem parameter_hasDerivAt {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) : HasDerivAt (fun eta => f (w.1, eta)) (de f w) w.2 :=
  ProfileHistories.parameterPartial_hasDerivAt (PositiveOrderMoments.parameterDomain S hS)
    hf (p := w) ⟨mem_univ _, hw⟩

theorem dr_mul {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (fun p => f p * g p) w = dr f w * g w + f w * dr g w :=
  (radial_hasDerivAt hS (hf.mul hg) hw).unique
    ((radial_hasDerivAt hS hf hw).mul (radial_hasDerivAt hS hg hw))

theorem de_mul {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    de (fun p => f p * g p) w = de f w * g w + f w * de g w :=
  (parameter_hasDerivAt hS (hf.mul hg) hw).unique
    ((parameter_hasDerivAt hS hf hw).mul (parameter_hasDerivAt hS hg hw))

theorem de_weighted {S : Set ℝ} (hS : IsOpen S) {f : Field}
    (hf : Smooth S f) (m : ℕ) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    de (weighted m f) w = w.1 ^ m * de f w :=
  (parameter_hasDerivAt hS (smooth_weighted hf m) hw).unique
    ((parameter_hasDerivAt hS hf hw).const_mul (w.1 ^ m))

theorem exterior_partial {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) (v : ℝ × ℝ) :
    exterior B S (fun w => fderiv ℝ f w v) := by
  intro eta heta R hR
  have hg : Smooth S (fun w => fderiv ℝ f w v) :=
    (hf.fderiv_of_isOpen (isOpen_univ.prod hS) (by simp)).clm_apply contDiffOn_const
  have hz : EqOn (fun r => fderiv ℝ f (r, eta) v) (fun _ => 0) (Ioi B) := by
    intro r hr
    have he : f =ᶠ[𝓝 (r, eta)] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_Ioi.prod hS).mem_nhds ⟨hr, heta⟩] with w hw
      exact hs w.2 hw.2 w.1 hw.1.le
    change fderiv ℝ f (r, eta) v = 0
    rw [he.fderiv_eq (𝕜 := ℝ)]
    simp
  have hc := hz.closure (slice_smooth hg heta).continuous continuous_const
  rw [closure_Ioi] at hc
  exact hc hR

theorem exterior_dr {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) : exterior B S (dr f) := exterior_partial hS hf hs (1, 0)

theorem exterior_de {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) : exterior B S (de f) := exterior_partial hS hf hs (0, 1)

theorem moment_eq_positive {S : Set ℝ} {f : Field} {B : ℝ} (hB : 0 ≤ B)
    (hs : exterior B S f) {eta : ℝ} (heta : eta ∈ S) (m : ℕ) :
    moment B m f eta = PositiveOrderMoments.positiveIntegral (fun R => R ^ m * f (R, eta)) := by
  symm
  exact PositiveOrderMoments.positiveIntegral_eq_primitive hB le_rfl
    (fun R hR => by rw [hs eta heta R hR, mul_zero])

theorem moment_hasDerivAt {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    HasDerivAt (moment B m f) (moment B m (de f) eta) eta := by
  let D := PositiveOrderMoments.parameterDomain S hS
  have hp := parameter_hasDerivAt hS
    (ProfileHistories.primitive_smooth D (smooth_weighted hf m))
    (w := (B, eta)) heta
  change HasDerivAt (fun z => ProfileHistories.primitive (weighted m f) (B, z))
    (ProfileHistories.parameterPartial (ProfileHistories.primitive (weighted m f)) (B, eta)) eta
        at hp
  rw [ProfileHistories.parameterPartial_primitive D (smooth_weighted hf m)
    (p := (B, eta)) ⟨mem_univ _, heta⟩] at hp
  have hi : ProfileHistories.primitive (de (weighted m f)) (B, eta) =
      moment B m (de f) eta := by
    apply intervalIntegral.integral_congr
    intro R hR
    exact de_weighted hS hf m (w := (R, eta)) heta
  change ProfileHistories.primitive (ProfileHistories.parameterPartial (weighted m f)) (B, eta) =
    moment B m (de f) eta at hi
  rw [hi] at hp
  exact hp

theorem moment_de_zero {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (B : ℝ) (m : ℕ) (hm : ∀ eta ∈ S, moment B m f eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : moment B m (de f) eta = 0 := by
  have he : moment B m f =ᶠ[𝓝 eta] fun _ => (0 : ℝ) := by
    filter_upwards [hS.mem_nhds heta] with z hz using hm z hz
  exact (moment_hasDerivAt hS hf B m heta).unique
    ((hasDerivAt_const eta 0).congr_of_eventuallyEq he)

/-- Radial integration by parts includes the genuine boundary at the axis. -/
theorem moment_dr {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B (m + 1) (dr f) eta = B ^ (m + 1) * f (B, eta) -
      ((m + 1 : ℕ) : ℝ) * moment B m f eta := by
  have hp : ∀ R : ℝ, HasDerivAt (fun r : ℝ => r ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * R ^ m) R := by
    intro R
    simpa using (hasDerivAt_id R).fun_pow (m + 1)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := B) (u := fun R : ℝ => R ^ (m + 1))
    (u' := fun R => ((m + 1 : ℕ) : ℝ) * R ^ m)
    (v := fun R => f (R, eta)) (v' := fun R => dr f (R, eta))
    (continuous_id.pow (m + 1)).continuousOn (slice_smooth hf heta).continuous.continuousOn
    (fun R _ => hp R) (fun R _ => radial_hasDerivAt hS hf (w := (R, eta)) heta)
    ((continuous_const.mul (continuous_id.pow m)).intervalIntegrable 0 B)
    ((slice_smooth (smooth_dr hS hf) heta).continuous.intervalIntegrable (μ := volume) 0 B)
  simpa only [moment, zero_pow (Nat.succ_ne_zero m), zero_mul, sub_zero,
    mul_assoc, intervalIntegral.integral_const_mul] using hi

theorem moment_add {S : Set ℝ} {f g : Field} (hf : Smooth S f) (hg : Smooth S g)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (fun w => f w + g w) eta = moment B m f eta + moment B m g eta := by
  simp only [moment, mul_add]
  exact intervalIntegral.integral_add
    ((slice_smooth (smooth_weighted hf m) heta).continuous.intervalIntegrable (μ := volume) 0 B)
    ((slice_smooth (smooth_weighted hg m) heta).continuous.intervalIntegrable (μ := volume) 0 B)

theorem moment_sub {S : Set ℝ} {f g : Field} (hf : Smooth S f) (hg : Smooth S g)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (fun w => f w - g w) eta = moment B m f eta - moment B m g eta := by
  simp only [moment, mul_sub]
  exact intervalIntegral.integral_sub
    ((slice_smooth (smooth_weighted hf m) heta).continuous.intervalIntegrable (μ := volume) 0 B)
    ((slice_smooth (smooth_weighted hg m) heta).continuous.intervalIntegrable (μ := volume) 0 B)

theorem smooth_axialOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) :
    Smooth S (axialOp h b f) := by
  have hl : Smooth S (fun w => PositiveAxisSystem.ell h w.2) :=
    contDiffOn_const.sub (contDiffOn_const.mul (contDiffOn_snd.pow 2))
  have he : Smooth S (fun w => PositiveAxisSystem.edge w.2) :=
    contDiffOn_const.sub (contDiffOn_snd.pow 2)
  exact (((((contDiffOn_const.mul contDiffOn_snd).mul contDiffOn_const).mul hf).add
    (he.mul (smooth_de hS hf))).sub ((contDiffOn_snd.mul contDiffOn_fst).mul (smooth_dr hS hf))).div
      hl (fun w hw => hell w.2 hw.2)

theorem exterior_axialOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) (h b : ℝ) : exterior B S (axialOp h b f) := by
  intro eta heta R hR
  simp [axialOp, hs eta heta R hR, exterior_dr hS hf hs eta heta R hR,
    exterior_de hS hf hs eta heta R hR]

theorem axialOp_mul {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) (h b c : ℝ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    axialOp h (b + c) (fun p => f p * g p) w =
      axialOp h b f w * g w + f w * axialOp h c g w := by
  simp only [axialOp, de_mul hS hf hg hw, dr_mul hS hf hg hw]
  ring

/-- The weighted axial derivative is the actual derivative of the weighted
moment, with its exact scaling coefficient and radial boundary term. -/
theorem moment_axialOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (axialOp h b f) eta =
      (2 * eta * b * moment B m f eta + PositiveAxisSystem.edge eta * moment B m (de f) eta -
        eta * (B ^ (m + 1) * f (B, eta) - ((m + 1 : ℕ) : ℝ) * moment B m f eta)) /
        PositiveAxisSystem.ell h eta := by
  have h0 := ((slice_smooth (smooth_weighted hf m) heta).continuous.intervalIntegrable (μ :=
      volume) 0 B)
  have h1 := ((slice_smooth (smooth_weighted (smooth_de hS hf) m)
      heta).continuous.intervalIntegrable (μ := volume) 0 B)
  have h2 := ((slice_smooth (smooth_weighted (smooth_dr hS hf) (m + 1))
      heta).continuous.intervalIntegrable (μ := volume) 0 B)
  dsimp only [weighted] at h0 h1 h2
  have he : (fun R => R ^ m * axialOp h b f (R, eta)) =
      (fun R => (2 * eta * b * (R ^ m * f (R, eta)) +
        PositiveAxisSystem.edge eta * (R ^ m * de f (R, eta)) -
        eta * (R ^ (m + 1) * dr f (R, eta))) / PositiveAxisSystem.ell h eta) := by
    funext R
    simp only [axialOp, pow_succ]
    ring
  unfold moment
  rw [he, intervalIntegral.integral_div,
    intervalIntegral.integral_sub ((h0.const_mul _).add (h1.const_mul _)) (h2.const_mul _),
    intervalIntegral.integral_add (h0.const_mul _) (h1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change (_ + _ - eta * moment B (m + 1) (dr f) eta) / _ = _
  rw [moment_dr hS hf B m heta]
  rfl

theorem moment_timeOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (timeOp h b f) eta =
      (-b * moment B m f eta + PositiveAxisSystem.dScale h * eta * moment B m (de f) eta +
        (B ^ (m + 1) * f (B, eta) - ((m + 1 : ℕ) : ℝ) * moment B m f eta) / 2) /
        PositiveAxisSystem.ell h eta := by
  have h0 := ((slice_smooth (smooth_weighted hf m) heta).continuous.intervalIntegrable (μ :=
      volume) 0 B)
  have h1 := ((slice_smooth (smooth_weighted (smooth_de hS hf) m)
      heta).continuous.intervalIntegrable (μ := volume) 0 B)
  have h2 := ((slice_smooth (smooth_weighted (smooth_dr hS hf) (m + 1))
      heta).continuous.intervalIntegrable (μ := volume) 0 B)
  dsimp only [weighted] at h0 h1 h2
  have he : (fun R => R ^ m * timeOp h b f (R, eta)) =
      (fun R => (-b * (R ^ m * f (R, eta)) +
        PositiveAxisSystem.dScale h * eta * (R ^ m * de f (R, eta)) +
        (1 / 2 : ℝ) * (R ^ (m + 1) * dr f (R, eta))) / PositiveAxisSystem.ell h eta) := by
    funext R
    simp only [timeOp, pow_succ]
    ring
  unfold moment
  rw [he, intervalIntegral.integral_div,
    intervalIntegral.integral_add ((h0.const_mul _).add (h1.const_mul _)) (h2.const_mul _),
    intervalIntegral.integral_add (h0.const_mul _) (h1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change (_ + _ + (1 / 2 : ℝ) * moment B (m + 1) (dr f) eta) / _ = _
  rw [moment_dr hS hf B m heta]
  unfold moment
  ring

theorem moment_axialOp_zero {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) (hb : ∀ eta ∈ S, f (B, eta) = 0)
    (hm : ∀ eta ∈ S, moment B m f eta = 0) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (axialOp h b f) eta = 0 := by
  rw [moment_axialOp hS hf h b B m heta, hb eta heta, hm eta heta,
    moment_de_zero hS hf B m hm heta]
  ring

theorem moment_timeOp_zero {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) (hb : ∀ eta ∈ S, f (B, eta) = 0)
    (hm : ∀ eta ∈ S, moment B m f eta = 0) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (timeOp h b f) eta = 0 := by
  rw [moment_timeOp hS hf h b B m heta, hb eta heta, hm eta heta,
    moment_de_zero hS hf B m hm heta]
  ring

theorem moment_axialOp2_zero {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b B : ℝ) (m : ℕ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hs : exterior B S f) (hm : ∀ eta ∈ S, moment B m f eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : moment B m (axialOp2 h b f) eta = 0 := by
  exact moment_axialOp_zero hS (smooth_axialOp hS hf h b hell)
    h (b - PositiveAxisSystem.dScale h) B m
    (fun z hz => exterior_axialOp hS hf hs h b z hz B le_rfl)
    (fun z hz => moment_axialOp_zero hS hf h b B m
      (fun z hz => hs z hz B le_rfl) hm hz) heta

/-- Order exponent, given by `-PositiveAxisSystem.a h + SlowExpansionResidual.slowOrder h n`. -/
noncomputable def orderExponent (h : ℝ) (n : ℕ) : ℝ :=
  -PositiveAxisSystem.a h + SlowExpansionResidual.slowOrder h n

/-- Pressure exponent, given by `-2 * PositiveAxisSystem.a h + SlowExpansionResidual.slowOrder h
n`. -/
noncomputable def pressureExponent (h : ℝ) (n : ℕ) : ℝ :=
  -2 * PositiveAxisSystem.a h + SlowExpansionResidual.slowOrder h n

theorem orderExponent_pair (h : ℝ) {i j n : ℕ} (hij : i + j = n) :
    orderExponent h i + orderExponent h j = pressureExponent h n := by
  unfold orderExponent pressureExponent
  rw [← hij, SlowExpansionResidual.slowOrder_add]
  ring

/-- At a fixed convolution order the physical power is independent of the split. -/
theorem physical_product_power {q : ℝ} (hq : 0 < q) (h b c : ℝ)
    {i j n : ℕ} (hij : i + j = n) :
    q ^ (b + SlowExpansionResidual.slowOrder h i) * q ^ (c + SlowExpansionResidual.slowOrder h j) =
      q ^ (b + c + SlowExpansionResidual.slowOrder h n) := by
  rw [SlowExpansionResidual.rpow_product_order hq, hij]

/-- Conv, given by `∑ i ∈ Finset.range (n + 1), u i w * v (n - i) w`. -/
noncomputable def conv (n : ℕ) (u v : History) (w : ℝ × ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), u i w * v (n - i) w

theorem conv_eq_actual (n : ℕ) (u v : History) (w : ℝ × ℝ) :
    conv n u v w = PositiveOrderMoments.cauchy n (PositiveOrderMoments.slice u w.2)
      (PositiveOrderMoments.slice v w.2) w.1 := rfl

theorem conv_eq_antidiagonal (n : ℕ) (u v : History) (w : ℝ × ℝ) :
    conv n u v w = SlowExpansionResidual.convolution (fun i j => u i w * v j w) n := by
  symm
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => u i w * v j w) n

theorem smooth_conv {S : Set ℝ} {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hv : ∀ j, j ≤ n → Smooth S (v j)) :
    Smooth S (conv n u v) := by
  apply ContDiffOn.sum
  intro j hj
  exact (hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).mul (hv (n - j) (Nat.sub_le _ _))

theorem dr_conv {S : Set ℝ} (hS : IsOpen S) {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hv : ∀ j, j ≤ n → Smooth S (v j))
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (conv n u v) w = ∑ j ∈ Finset.range (n + 1),
      (dr (u j) w * v (n - j) w + u j w * dr (v (n - j)) w) := by
  apply (radial_hasDerivAt hS (smooth_conv hu hv) hw).unique
  apply HasDerivAt.fun_sum
  intro j hj
  exact (radial_hasDerivAt hS (hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hw).mul
    (radial_hasDerivAt hS (hv (n - j) (Nat.sub_le _ _)) hw)

theorem de_conv {S : Set ℝ} (hS : IsOpen S) {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hv : ∀ j, j ≤ n → Smooth S (v j))
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    de (conv n u v) w = ∑ j ∈ Finset.range (n + 1),
      (de (u j) w * v (n - j) w + u j w * de (v (n - j)) w) := by
  apply (parameter_hasDerivAt hS (smooth_conv hu hv) hw).unique
  apply HasDerivAt.fun_sum
  intro j hj
  exact (parameter_hasDerivAt hS (hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) hw).mul
    (parameter_hasDerivAt hS (hv (n - j) (Nat.sub_le _ _)) hw)

theorem axialOp_conv {S : Set ℝ} (hS : IsOpen S) {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hv : ∀ j, j ≤ n → Smooth S (v j))
    (h : ℝ) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    axialOp h (pressureExponent h n) (conv n u v) w =
      ∑ j ∈ Finset.range (n + 1),
        (axialOp h (orderExponent h j) (u j) w * v (n - j) w +
          u j w * axialOp h (orderExponent h (n - j)) (v (n - j)) w) := by
  unfold axialOp
  rw [de_conv hS hu hv hw, dr_conv hS hu hv hw]
  unfold conv
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have he := orderExponent_pair h (i := j) (j := n - j) (n := n)
    (Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  rw [← he]
  ring

theorem dr_weighted {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (m : ℕ) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (weighted m f) w = (m : ℝ) * w.1 ^ (m - 1) * f w + w.1 ^ m * dr f w := by
  simpa only [id_eq, mul_one, Prod.eta] using
    (radial_hasDerivAt hS (smooth_weighted hf m) hw).unique
      (((hasDerivAt_id w.1).fun_pow m).fun_mul (radial_hasDerivAt hS hf hw))

theorem dr_sub {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (fun p => f p - g p) w = dr f w - dr g w :=
  (radial_hasDerivAt hS (hf.sub hg) hw).unique
    ((radial_hasDerivAt hS hf hw).sub (radial_hasDerivAt hS hg hw))

theorem axialOp_add {S : Set ℝ} (hS : IsOpen S) {f g : Field}
    (hf : Smooth S f) (hg : Smooth S g) (h b : ℝ)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    axialOp h b (fun p => f p + g p) w = axialOp h b f w + axialOp h b g w := by
  have hr := (radial_hasDerivAt hS (hf.add hg) hw).unique
    ((radial_hasDerivAt hS hf hw).add (radial_hasDerivAt hS hg hw))
  have he := (parameter_hasDerivAt hS (hf.add hg) hw).unique
    ((parameter_hasDerivAt hS hf hw).add (parameter_hasDerivAt hS hg hw))
  simp only [axialOp, hr, he]
  ring

/-- Angular viscous flux, given by `w.1 ^ 2 * dr e w - w.1 * e w`. -/
noncomputable def angularViscousFlux (e : Field) (w : ℝ × ℝ) : ℝ :=
  w.1 ^ 2 * dr e w - w.1 * e w

/-- Axial viscous flux, given by `w.1 * dr u w`. -/
noncomputable def axialViscousFlux (u : Field) (w : ℝ × ℝ) : ℝ := w.1 * dr u w

theorem dr_angularViscousFlux {S : Set ℝ} (hS : IsOpen S) {e : Field} (he : Smooth S e)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (angularViscousFlux e) w = w.1 ^ 2 * dr (dr e) w + w.1 * dr e w - e w := by
  have hfun : angularViscousFlux e = fun p => weighted 2 (dr e) p - weighted 1 e p := by
    funext p
    simp [angularViscousFlux, weighted]
  rw [hfun]
  rw [dr_sub hS (smooth_weighted (smooth_dr hS he) 2) (smooth_weighted he 1) hw,
    dr_weighted hS (smooth_dr hS he) 2 hw, dr_weighted hS he 1 hw]
  norm_num
  ring

theorem dr_axialViscousFlux {S : Set ℝ} (hS : IsOpen S) {u : Field} (hu : Smooth S u)
    {w : ℝ × ℝ} (hw : w.2 ∈ S) :
    dr (axialViscousFlux u) w = w.1 * dr (dr u) w + dr u w := by
  have hfun : axialViscousFlux u = weighted 1 (dr u) := by
    funext p
    simp [axialViscousFlux, weighted]
  rw [hfun]
  rw [dr_weighted hS (smooth_dr hS hu) 1 hw]
  norm_num
  ring

/-- Angular weighted, constructed using `w.1`. -/
noncomputable def angularWeighted (h : ℝ) (n : ℕ) (v u e : History) (w : ℝ × ℝ) : ℝ :=
  w.1 ^ 2 * timeOp h (orderExponent h n) (e n) w +
    (∑ j ∈ Finset.range (n + 1),
      (w.1 * v j w * dr (e (n - j)) w + v j w * e (n - j) w +
        w.1 ^ 2 * u j w * axialOp h (orderExponent h (n - j)) (e (n - j)) w)) -
    (w.1 ^ 2 * dr (dr (e n)) w + w.1 * dr (e n) w - e n w) -
    w.1 ^ 2 * axialOp2 h (orderExponent h (n - 1)) (e (n - 1)) w

/-- Axial weighted, constructed using `w.1`. -/
noncomputable def axialWeighted (h : ℝ) (n : ℕ) (v u : History) (p : Field) (w : ℝ × ℝ) : ℝ :=
  w.1 * timeOp h (orderExponent h n) (u n) w +
    (∑ j ∈ Finset.range (n + 1),
      (v j w * dr (u (n - j)) w +
        w.1 * u j w * axialOp h (orderExponent h (n - j)) (u (n - j)) w)) +
    w.1 * axialOp h (pressureExponent h n) p w -
    (w.1 * dr (dr (u n)) w + dr (u n) w) -
    w.1 * axialOp2 h (orderExponent h (n - 1)) (u (n - 1)) w

/-- Angular density, constructed using `w.1`. -/
noncomputable def angularDensity (h : ℝ) (n : ℕ) (v u e : History) (w : ℝ × ℝ) : ℝ :=
  w.1 ^ 2 * timeOp h (orderExponent h n) (e n) w +
    dr (weighted 1 (conv n v e)) w +
    w.1 ^ 2 * axialOp h (pressureExponent h n) (conv n u e) w -
    dr (angularViscousFlux (e n)) w -
    w.1 ^ 2 * axialOp2 h (orderExponent h (n - 1)) (e (n - 1)) w

/-- Axial density, constructed using `w.1`. -/
noncomputable def axialDensity (h : ℝ) (n : ℕ) (v u : History) (p : Field) (w : ℝ × ℝ) : ℝ :=
  w.1 * timeOp h (orderExponent h n) (u n) w + dr (conv n v u) w +
    w.1 * axialOp h (pressureExponent h n) (fun p' => conv n u u p' + p p') w -
    dr (axialViscousFlux (u n)) w -
    w.1 * axialOp2 h (orderExponent h (n - 1)) (u (n - 1)) w

/-- Incompressibility converts the actual angular advection terms to
conservative form; the convolution exponents are checked, not assumed. -/
theorem angularWeighted_eq_density {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h : ℝ) {w : ℝ × ℝ} (hw : w.2 ∈ S)
    (hdiv : ∀ j, j ≤ n → dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w) :
    angularWeighted h n v u e w = angularDensity h n v u e w := by
  unfold angularDensity angularWeighted
  rw [dr_weighted hS (smooth_conv hv he) 1 hw, dr_conv hS hv he hw,
    axialOp_conv hS hu he h hw, dr_angularViscousFlux hS (he n le_rfl) hw]
  norm_num only [Nat.cast_one, pow_zero, pow_one, one_mul, Nat.sub_self]
  unfold conv
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 2
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hdiv j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
  ring

theorem axialWeighted_eq_density {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h : ℝ) {w : ℝ × ℝ} (hw : w.2 ∈ S)
    (hdiv : ∀ j, j ≤ n → dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w) :
    axialWeighted h n v u p w = axialDensity h n v u p w := by
  unfold axialDensity axialWeighted
  rw [dr_conv hS hv hu hw, axialOp_add hS (smooth_conv hu hu) hp h _ hw,
    axialOp_conv hS hu hu h hw, dr_axialViscousFlux hS (hu n le_rfl) hw]
  have hs : (∑ j ∈ Finset.range (n + 1),
      (v j w * dr (u (n - j)) w + w.1 * u j w * axialOp h (orderExponent h (n - j)) (u (n - j)) w))
          =
      (∑ j ∈ Finset.range (n + 1), (dr (v j) w * u (n - j) w + v j w * dr (u (n - j)) w)) +
      w.1 * ∑ j ∈ Finset.range (n + 1),
        (axialOp h (orderExponent h j) (u j) w * u (n - j) w +
          u j w * axialOp h (orderExponent h (n - j)) (u (n - j)) w) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hdiv j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    ring
  rw [hs]
  ring

theorem smooth_timeOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) : Smooth S (timeOp h b f) := by
  have hl : Smooth S (fun w => PositiveAxisSystem.ell h w.2) :=
    contDiffOn_const.sub (contDiffOn_const.mul (contDiffOn_snd.pow 2))
  exact (((contDiffOn_const.mul hf).add
    ((contDiffOn_const.mul contDiffOn_snd).mul (smooth_de hS hf))).add
      ((contDiffOn_fst.div_const 2).mul (smooth_dr hS hf))).div hl
      (fun w hw => hell w.2 hw.2)

theorem smooth_axialOp2 {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (h b : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) : Smooth S (axialOp2 h b f) :=
  smooth_axialOp hS (smooth_axialOp hS hf h b hell) h _ hell

theorem smooth_angularViscousFlux {S : Set ℝ} (hS : IsOpen S) {e : Field} (he : Smooth S e) :
    Smooth S (angularViscousFlux e) :=
  ((contDiffOn_fst.pow 2).mul (smooth_dr hS he)).sub (contDiffOn_fst.mul he)

theorem smooth_axialViscousFlux {S : Set ℝ} (hS : IsOpen S) {u : Field} (hu : Smooth S u) :
    Smooth S (axialViscousFlux u) := contDiffOn_fst.mul (smooth_dr hS hu)

theorem moment_weighted_zero (B : ℝ) (m : ℕ) (f : Field) (eta : ℝ) :
    moment B 0 (weighted m f) eta = moment B m f eta := by simp [moment, weighted]

theorem moment_dr_boundary {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    (B : ℝ) {eta : ℝ} (heta : eta ∈ S) :
    moment B 0 (dr f) eta = f (B, eta) - f (0, eta) := by
  simp only [moment, pow_zero, one_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun R => f (R, eta))
    (fun R _ => radial_hasDerivAt hS hf (w := (R, eta)) heta)
    ((slice_smooth (smooth_dr hS hf) heta).continuous.intervalIntegrable 0 B)

theorem moment_five {S : Set ℝ} {f g k l p : Field}
    (hf : Smooth S f) (hg : Smooth S g) (hk : Smooth S k) (hl : Smooth S l) (hp : Smooth S p)
    (B : ℝ) (m : ℕ) {eta : ℝ} (heta : eta ∈ S) :
    moment B m (fun w => f w + g w + k w - l w - p w) eta =
      moment B m f eta + moment B m g eta + moment B m k eta - moment B m l eta - moment B m p eta
          := by
  rw [moment_sub (((hf.add hg).add hk).sub hl) hp B m heta,
    moment_sub ((hf.add hg).add hk) hl B m heta,
    moment_add (hf.add hg) hk B m heta, moment_add hf hg B m heta]

theorem exterior_conv_left {S : Set ℝ} {B : ℝ} {n : ℕ} {u v : History}
    (hu : ∀ j, j ≤ n → exterior B S (u j)) : exterior B S (conv n u v) := by
  intro eta heta R hR
  unfold conv
  apply Finset.sum_eq_zero
  intro j hj
  rw [hu j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) eta heta R hR, zero_mul]

/-- The integrated angular equation, with the previous axial-viscosity term
still displayed. The other four terms cancel by the repaired moments and
the actual radial boundary terms. -/
theorem angular_integral_balance {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h B : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hev : exterior B S (e n)) (hvv : ∀ j, j ≤ n → exterior B S (v j))
    (hem : ∀ eta ∈ S, moment B 2 (e n) eta = 0)
    (hum : ∀ eta ∈ S, moment B 2 (conv n u e) eta = 0)
    (hug : exterior B S (conv n u e)) {eta : ℝ} (heta : eta ∈ S) :
    moment B 0 (angularDensity h n v u e) eta =
      -moment B 2 (axialOp2 h (orderExponent h (n - 1)) (e (n - 1))) eta := by
  have ht := smooth_weighted (smooth_timeOp hS (he n le_rfl) h (orderExponent h n) hell) 2
  have hr := smooth_weighted (smooth_conv hv he) 1
  have hz := smooth_weighted (smooth_axialOp hS (smooth_conv hu he) h (pressureExponent h n) hell) 2
  have hk := smooth_angularViscousFlux hS (he n le_rfl)
  have hp := smooth_weighted (smooth_axialOp2 hS (he (n - 1) (Nat.sub_le _ _)) h
    (orderExponent h (n - 1)) hell) 2
  have hd : angularDensity h n v u e = fun w =>
      weighted 2 (timeOp h (orderExponent h n) (e n)) w +
      dr (weighted 1 (conv n v e)) w +
      weighted 2 (axialOp h (pressureExponent h n) (conv n u e)) w -
      dr (angularViscousFlux (e n)) w -
      weighted 2 (axialOp2 h (orderExponent h (n - 1)) (e (n - 1))) w := by
    funext w
    rfl
  rw [hd, moment_five ht (smooth_dr hS hr) hz (smooth_dr hS hk) hp B 0 heta,
    moment_weighted_zero, moment_weighted_zero, moment_weighted_zero,
    moment_dr_boundary hS hr B heta, moment_dr_boundary hS hk B heta,
    moment_timeOp_zero hS (he n le_rfl) h _ B 2 (fun z hz => hev z hz B le_rfl) hem heta,
    moment_axialOp_zero hS (smooth_conv hu he) h _ B 2
      (fun z hz => hug z hz B le_rfl) hum heta]
  simp [weighted, angularViscousFlux, exterior_conv_left hvv eta heta B le_rfl,
    hev eta heta B le_rfl, exterior_dr hS (he n le_rfl) hev eta heta B le_rfl]

theorem axial_integral_balance {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h B : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (huv : exterior B S (u n)) (hvv : ∀ j, j ≤ n → exterior B S (v j))
    (haxis : ∀ eta ∈ S, conv n v u (0, eta) = 0)
    (hum : ∀ eta ∈ S, moment B 1 (u n) eta = 0)
    (hflux : ∀ eta ∈ S, moment B 1 (fun w => conv n u u w + p w) eta = 0)
    (hfluxB : ∀ eta ∈ S, conv n u u (B, eta) + p (B, eta) = 0)
    {eta : ℝ} (heta : eta ∈ S) :
    moment B 0 (axialDensity h n v u p) eta =
      -moment B 1 (axialOp2 h (orderExponent h (n - 1)) (u (n - 1))) eta := by
  have ht := smooth_weighted (smooth_timeOp hS (hu n le_rfl) h (orderExponent h n) hell) 1
  have hr := smooth_conv hv hu
  have hz := smooth_weighted (smooth_axialOp hS ((smooth_conv hu hu).add hp) h (pressureExponent h
      n) hell) 1
  have hk := smooth_axialViscousFlux hS (hu n le_rfl)
  have hl := smooth_weighted (smooth_axialOp2 hS (hu (n - 1) (Nat.sub_le _ _)) h
    (orderExponent h (n - 1)) hell) 1
  have hd : axialDensity h n v u p = fun w =>
      weighted 1 (timeOp h (orderExponent h n) (u n)) w + dr (conv n v u) w +
      weighted 1 (axialOp h (pressureExponent h n) (fun w => conv n u u w + p w)) w -
      dr (axialViscousFlux (u n)) w -
      weighted 1 (axialOp2 h (orderExponent h (n - 1)) (u (n - 1))) w := by
    funext w
    simp [axialDensity, weighted]
  rw [hd, moment_five ht (smooth_dr hS hr) hz (smooth_dr hS hk) hl B 0 heta,
    moment_weighted_zero, moment_weighted_zero, moment_weighted_zero,
    moment_dr_boundary hS hr B heta, moment_dr_boundary hS hk B heta,
    moment_timeOp_zero hS (hu n le_rfl) h _ B 1 (fun z hz => huv z hz B le_rfl) hum heta,
    moment_axialOp_zero hS ((smooth_conv hu hu).add hp) h _ B 1 hfluxB hflux heta]
  simp [axialViscousFlux, exterior_conv_left hvv eta heta B le_rfl,
    haxis eta heta, exterior_dr hS (hu n le_rfl) huv eta heta B le_rfl]

/-- Pressure integration by parts turns the fifth repaired row into the
zero total axial momentum flux. The pressure derivative is an actual one. -/
theorem axial_flux_moment_from_fifth {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {u : History} {p : Field} (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (B : ℝ) (hpB : ∀ eta ∈ S, p (B, eta) = 0)
    (hrow : ∀ eta ∈ S, moment B 1 (conv n u u) eta - (1 / 2 : ℝ) * moment B 2 (dr p) eta = 0)
    {eta : ℝ} (heta : eta ∈ S) :
    moment B 1 (fun w => conv n u u w + p w) eta = 0 := by
  have hibp := moment_dr hS hp B 1 heta
  rw [hpB eta heta] at hibp
  norm_num at hibp
  rw [moment_add (smooth_conv hu hu) hp B 1 heta]
  linarith [hrow eta heta]

theorem actual_row_integral_zero {n : ℕ} {u e : History} {omega : Field}
    {S : Set ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → PositiveOrderMoments.jointRowDensity n u e omega (R, eta) = 0)
    (hm : ∀ eta ∈ S, PositiveOrderMoments.moments n (PositiveOrderMoments.slice u eta)
      (PositiveOrderMoments.slice e eta) (fun R => omega (R, eta)) = 0)
    {eta : ℝ} (heta : eta ∈ S) (i : Fin 5) :
    (∫ R in (0 : ℝ)..B, PositiveOrderMoments.jointRowDensity n u e omega (R, eta) i) = 0 := by
  rw [← PositiveOrderMoments.positiveIntegral_eq_primitive hB le_rfl
    (fun R hR => congrFun (hs eta heta R hR) i)]
  exact congrFun (hm eta heta) i

/-- All moment hypotheses used in the integrated balances follow from the
five repaired rows. Pressure is the actual forward primitive of its source. -/
theorem repaired_moment_data {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {u e : History} {omega : Field} (hu : ∀ j, j ≤ n → Smooth S (u j))
    (hq : Smooth S (PositiveOrderMoments.jointPressureGradient n e omega))
    {B : ℝ} (hB : 0 ≤ B)
    (hs : ∀ eta ∈ S, ∀ R, B ≤ R → PositiveOrderMoments.jointRowDensity n u e omega (R, eta) = 0)
    (hm : ∀ eta ∈ S, PositiveOrderMoments.moments n (PositiveOrderMoments.slice u eta)
      (PositiveOrderMoments.slice e eta) (fun R => omega (R, eta)) = 0)
    {eta : ℝ} (heta : eta ∈ S) :
    moment B 1 (u n) eta = 0 ∧ moment B 2 (e n) eta = 0 ∧
      moment B 2 (conv n u e) eta = 0 ∧
      moment B 1 (fun w => conv n u u w + PositiveOrderMoments.pressureHistory n e omega w) eta = 0
          := by
  have hP := PositiveOrderMoments.pressureHistory_contDiffOn hS hq
  have hdP : ∀ w : ℝ × ℝ, w.2 ∈ S →
      dr (PositiveOrderMoments.pressureHistory n e omega) w =
        PositiveOrderMoments.jointPressureGradient n e omega w := by
    intro w hw
    exact ProfileHistories.radialPartial_primitive (PositiveOrderMoments.parameterDomain S hS)
      hq (p := w) ⟨mem_univ _, hw⟩
  have hPB : ∀ z ∈ S, PositiveOrderMoments.pressureHistory n e omega (B, z) = 0 := by
    intro z hz
    exact PositiveOrderMoments.pressureHistory_exterior_on hB
      (fun z hz R hR => congrFun (hs z hz R hR) 2) hm le_rfl hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := actual_row_integral_zero hB hs hm heta 0
    change (∫ R in (0 : ℝ)..B, R * u n (R, eta)) = 0 at hh
    simpa [moment] using hh
  · exact actual_row_integral_zero hB hs hm heta 1
  · exact actual_row_integral_zero hB hs hm heta 3
  · apply axial_flux_moment_from_fifth hS hu hP B hPB _ heta
    intro z hz
    have hh := actual_row_integral_zero hB hs hm hz 4
    have hfun : (fun R => PositiveOrderMoments.jointRowDensity n u e omega (R, z) 4) =
        (fun R => R * conv n u u (R, z) - (1 / 2 : ℝ) *
          (R ^ 2 * dr (PositiveOrderMoments.pressureHistory n e omega) (R, z))) := by
      funext R
      rw [hdP (R, z) hz]
      change R * conv n u u (R, z) - R ^ 2 / 2 *
        PositiveOrderMoments.jointPressureGradient n e omega (R, z) = _
      ring
    have hi0 := (slice_smooth (smooth_weighted (smooth_conv hu hu) 1)
        hz).continuous.intervalIntegrable
      (μ := volume) 0 B
    have hi1 := (slice_smooth (smooth_weighted (smooth_dr hS hP) 2)
        hz).continuous.intervalIntegrable
      (μ := volume) 0 B
    simp only [weighted, pow_one] at hi0 hi1
    rw [hfun, intervalIntegral.integral_sub hi0 (hi1.const_mul (1 / 2)),
      intervalIntegral.integral_const_mul] at hh
    simpa only [moment, pow_one] using hh

theorem angular_integral_zero {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h B : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hev : exterior B S (e n)) (hvv : ∀ j, j ≤ n → exterior B S (v j))
    (hem : ∀ eta ∈ S, moment B 2 (e n) eta = 0)
    (hum : ∀ eta ∈ S, moment B 2 (conv n u e) eta = 0)
    (hug : exterior B S (conv n u e))
    (heprev : exterior B S (e (n - 1)))
    (hmprev : ∀ eta ∈ S, moment B 2 (e (n - 1)) eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : moment B 0 (angularDensity h n v u e) eta = 0 := by
  rw [angular_integral_balance hS hv hu he h B hell hev hvv hem hum hug heta,
    moment_axialOp2_zero hS (he (n - 1) (Nat.sub_le _ _)) h _ B 2 hell heprev hmprev heta,
    neg_zero]

theorem axial_integral_zero {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h B : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (huv : exterior B S (u n)) (hvv : ∀ j, j ≤ n → exterior B S (v j))
    (haxis : ∀ eta ∈ S, conv n v u (0, eta) = 0)
    (hum : ∀ eta ∈ S, moment B 1 (u n) eta = 0)
    (hflux : ∀ eta ∈ S, moment B 1 (fun w => conv n u u w + p w) eta = 0)
    (hfluxB : ∀ eta ∈ S, conv n u u (B, eta) + p (B, eta) = 0)
    (huprev : exterior B S (u (n - 1)))
    (hmprev : ∀ eta ∈ S, moment B 1 (u (n - 1)) eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : moment B 0 (axialDensity h n v u p) eta = 0 := by
  rw [axial_integral_balance hS hv hu hp h B hell huv hvv haxis hum hflux hfluxB heta,
    moment_axialOp2_zero hS (hu (n - 1) (Nat.sub_le _ _)) h _ B 1 hell huprev hmprev heta,
    neg_zero]

/-- The negative weighted radial primitive. The definition is zero on
nonpositive radii; vanishing of the source near the axis makes this smooth. -/
noncomputable def stress (m : ℕ) (F : Field) (w : ℝ × ℝ) : ℝ :=
  if 0 < w.1 then -ProfileHistories.primitive F w / w.1 ^ m else 0

theorem stress_of_pos (m : ℕ) (F : Field) {w : ℝ × ℝ} (hw : 0 < w.1) :
    stress m F w = -ProfileHistories.primitive F w / w.1 ^ m := ite_eq_left hw

theorem stress_inner (m : ℕ) {F : Field} {S : Set ℝ} {a : ℝ}
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    {R eta : ℝ} (hR : R ≤ a) (heta : eta ∈ S) : stress m F (R, eta) = 0 := by
  by_cases hp : 0 < R
  · rw [stress_of_pos m F hp]
    have hi : ProfileHistories.primitive F (R, eta) = 0 := by
      change (∫ r in (0 : ℝ)..R, F (r, eta)) = 0
      have heq : EqOn (fun r => F (r, eta)) (fun _ => (0 : ℝ)) (uIcc 0 R) := by
        intro r hr
        rw [uIcc_of_le hp.le] at hr
        exact hinner eta heta r ⟨hr.1, hr.2.trans hR⟩
      rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_zero]
    simp [hi]
  · simp [stress, hp]

theorem stress_exterior (m : ℕ) {F : Field} {S : Set ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hs : exterior B S F) (hm : ∀ eta ∈ S, moment B 0 F eta = 0)
    {R eta : ℝ} (hR : B ≤ R) (heta : eta ∈ S) : stress m F (R, eta) = 0 := by
  by_cases hp : 0 < R
  · rw [stress_of_pos m F hp]
    have hi : ProfileHistories.primitive F (R, eta) = 0 := by
      change (∫ r in (0 : ℝ)..R, F (r, eta)) = 0
      rw [← PositiveOrderMoments.positiveIntegral_eq_primitive hB hR (hs eta heta)]
      have hh := moment_eq_positive hB hs heta 0
      simpa only [pow_zero, one_mul, hm eta heta] using hh.symm
    simp [hi]
  · simp [stress, hp]

theorem stress_smooth {S : Set ℝ} (hS : IsOpen S) {F : Field} (hF : Smooth S F)
    (m : ℕ) {a : ℝ} (ha : 0 < a)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0) : Smooth S (stress m F) := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  by_cases hR : 0 < w.1
  · have hP := (ProfileHistories.primitive_smooth
      (PositiveOrderMoments.parameterDomain S hS) hF).contDiffAt
        ((isOpen_univ.prod hS).mem_nhds hw)
    have ht : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => -ProfileHistories.primitive F p / p.1 ^ m) w :=
      hP.neg.div (contDiffAt_fst.pow m) (pow_ne_zero m hR.ne')
    apply ht.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt (Ioi_mem_nhds hR)] with p hp
    exact stress_of_pos m F hp
  · have hRa : w.1 < a := (le_of_not_gt hR).trans_lt ha
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_Iio.prod hS).mem_nhds ⟨hRa, hw.2⟩] with p hp
    exact stress_inner m hinner hp.1.le hp.2

/-- The defining primitive has the exact negative weighted derivative. -/
theorem stress_weighted_hasDerivAt {S : Set ℝ} (hS : IsOpen S) {F : Field} (hF : Smooth S F)
    (m : ℕ) {R eta : ℝ} (hR : 0 < R) (heta : eta ∈ S) :
    HasDerivAt (fun r => r ^ m * stress m F (r, eta)) (-F (R, eta)) R := by
  have hp := (ProfileHistories.primitive_hasDerivAt
    (PositiveOrderMoments.parameterDomain S hS) hF (p := (R, eta)) ⟨mem_univ _, heta⟩).fun_neg
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hR] with r hr
  rw [stress_of_pos m F (w := (r, eta)) hr]
  field_simp [pow_ne_zero m (ne_of_gt (show 0 < r from hr))]

theorem stress_radial_identity {S : Set ℝ} (hS : IsOpen S) {F : Field} (hF : Smooth S F)
    (m : ℕ) {a : ℝ} (ha : 0 < a)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    {w : ℝ × ℝ} (hR : 0 < w.1) (heta : w.2 ∈ S) :
    (m : ℝ) * w.1 ^ (m - 1) * stress m F w + w.1 ^ m * dr (stress m F) w = -F w := by
  have ht := stress_smooth hS hF m ha hinner
  have hd := (radial_hasDerivAt hS (smooth_weighted ht m) heta).unique
    (stress_weighted_hasDerivAt hS hF m hR heta)
  rw [dr_weighted hS ht m heta] at hd
  exact hd

theorem stress_slice_support (m : ℕ) {F : Field} {S : Set ℝ} {a B : ℝ} (hB : 0 ≤ B)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    (hs : exterior B S F) (hm : ∀ eta ∈ S, moment B 0 F eta = 0)
    {eta : ℝ} (heta : eta ∈ S) : support (fun R => stress m F (R, eta)) ⊆ Icc a B := by
  intro R hR
  constructor
  · by_contra hh
    exact hR (stress_inner m hinner (le_of_not_ge hh) heta)
  · by_contra hh
    exact hR (stress_exterior m hB hs hm (le_of_not_ge hh) heta)

/-- Radial support, given by `∀ eta ∈ S, ∀ R, R ∉ Icc a b → f (R, eta) = 0`. -/
noncomputable def radialSupport (S : Set ℝ) (a b : ℝ) (f : Field) : Prop :=
  ∀ eta ∈ S, ∀ R, R ∉ Icc a b → f (R, eta) = 0

theorem support_eventually_zero {S : Set ℝ} (hS : IsOpen S) {a b : ℝ} {f : Field}
    (hs : radialSupport S a b f) {w : ℝ × ℝ} (hw : w.2 ∈ S) (hR : w.1 ∉ Icc a b) :
    f =ᶠ[𝓝 w] fun _ => 0 := by
  filter_upwards [(isClosed_Icc.isOpen_compl.prod hS).mem_nhds ⟨hR, hw⟩] with p hp
  exact hs p.2 hp.2 p.1 hp.1

theorem jet_eq_zero_of_eventually {f : Field} {w : ℝ × ℝ}
    (hf : f =ᶠ[𝓝 w] fun _ => 0) (k : ℕ) : iteratedFDeriv ℝ k f w = 0 := by
  have hh : f =ᶠ[𝓝[univ] w] fun _ => (0 : ℝ) := by simpa only [nhdsWithin_univ] using hf
  have he := hh.iteratedFDerivWithin_eq (𝕜 := ℝ) hf.self_of_nhds k
  simpa only [iteratedFDerivWithin_univ, iteratedFDeriv_fun_zero, Pi.zero_apply] using he

theorem interior_quotient_smooth {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {a b l r : ℝ} (hs : radialSupport S a b f) (hab : Icc a b ⊆ Ioo l r)
    {zeta : ℝ → ℝ} (hz : ContDiffOn ℝ ∞ zeta (Ioo l r))
    (hz0 : ∀ R ∈ Ioo l r, zeta R ≠ 0) :
    Smooth S (fun w => f w / zeta w.1) := by
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  by_cases hR : w.1 ∈ Ioo l r
  · exact (hf.contDiffAt ((isOpen_univ.prod hS).mem_nhds hw)).div
      ((hz.contDiffAt (isOpen_Ioo.mem_nhds hR)).comp w contDiffAt_fst) (hz0 w.1 hR)
  · have ho : w.1 ∉ Icc a b := fun hm => hR (hab hm)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [support_eventually_zero hS hs hw.2 ho] with p hp
    simp [hp]

/-- Every actual derivative tensor has a weighted bound because its support
lies in one fixed compact subinterval of the positive-weight region. No
stress norm bound is an input. The constant may depend on the derivative order. -/
theorem interior_weighted_jets {S K : Set ℝ} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {f : Field} (hf : Smooth S f) {a b l r : ℝ}
    (hs : radialSupport S a b f) (hab : Icc a b ⊆ Ioo l r)
    {zeta : ℝ → ℝ} (hz : ContinuousOn zeta (Ioo l r))
    (hz0 : ∀ R ∈ Ioo l r, 0 < zeta R) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Ioo l r, ∀ eta ∈ K,
      ‖iteratedFDeriv ℝ k f (R, eta)‖ ≤ C * zeta R := by
  have hcj : ContinuousOn (iteratedFDeriv ℝ k f) (Icc a b ×ˢ K) := by
    intro w hw
    have hh := hf.contDiffAt ((isOpen_univ.prod hS).mem_nhds ⟨mem_univ _, hKS hw.2⟩)
    exact (hh.iteratedFDeriv_right (m := 0) (by
      simp only [zero_add]
      exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).continuousAt.continuousWithinAt
  have hcz : ContinuousOn (fun w : ℝ × ℝ => zeta w.1) (Icc a b ×ˢ K) :=
    hz.comp continuous_fst.continuousOn (fun w hw => hab hw.1)
  have hc : ContinuousOn (fun w : ℝ × ℝ => ‖iteratedFDeriv ℝ k f w‖ / zeta w.1)
      (Icc a b ×ˢ K) := hcj.norm.div hcz (fun w hw => (hz0 w.1 (hab hw.1)).ne')
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro R hR eta heta
  by_cases hi : R ∈ Icc a b
  · apply (div_le_iff₀ (hz0 R hR)).mp
    exact (le_abs_self _).trans ((hC (R, eta) ⟨hi, heta⟩).trans (le_max_left _ _))
  · have hj := jet_eq_zero_of_eventually (support_eventually_zero hS hs (w := (R, eta)) (hKS heta)
      hi) k
    rw [hj, norm_zero]
    exact mul_nonneg (le_max_right _ _) (hz0 R hR).le

theorem stress_radialSupport (m : ℕ) {F : Field} {S : Set ℝ} {a B : ℝ} (hB : 0 ≤ B)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    (hs : exterior B S F) (hm : ∀ eta ∈ S, moment B 0 F eta = 0) :
    radialSupport S a B (stress m F) := by
  intro eta heta R hR
  by_contra hn
  exact hR (stress_slice_support m hB hinner hs hm heta hn)

/-- A fixed interior support interval gives all weighted stress jets on
every compact parameter subinterval, as well as a smooth normalized stress. -/
theorem stress_weighted_jets {S K : Set ℝ} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {F : Field} (hF : Smooth S F) (m : ℕ) {a B l r : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hab : Icc a B ⊆ Ioo l r)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, F (R, eta) = 0)
    (hs : exterior B S F) (hm : ∀ eta ∈ S, moment B 0 F eta = 0)
    {zeta : ℝ → ℝ} (hz : ContDiffOn ℝ ∞ zeta (Ioo l r))
    (hz0 : ∀ R ∈ Ioo l r, 0 < zeta R) :
    Smooth S (fun w => stress m F w / zeta w.1) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Ioo l r, ∀ eta ∈ K,
        ‖iteratedFDeriv ℝ k (stress m F) (R, eta)‖ ≤ C * zeta R := by
  have ht := stress_smooth hS hF m ha hinner
  have hts := stress_radialSupport m hB hinner hs hm
  exact ⟨interior_quotient_smooth hS ht hts hab hz (fun R hR => (hz0 R hR).ne'),
    interior_weighted_jets hS hK hKS ht hts hab hz.continuousOn hz0⟩

theorem smooth_angularDensity {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) :
    Smooth S (angularDensity h n v u e) :=
  (((((contDiffOn_fst.pow 2).mul (smooth_timeOp hS (he n le_rfl) h _ hell)).add
    (smooth_dr hS (smooth_weighted (smooth_conv hv he) 1))).add
      ((contDiffOn_fst.pow 2).mul (smooth_axialOp hS (smooth_conv hu he) h _ hell))).sub
        (smooth_dr hS (smooth_angularViscousFlux hS (he n le_rfl)))).sub
          ((contDiffOn_fst.pow 2).mul (smooth_axialOp2 hS (he (n - 1) (Nat.sub_le _ _)) h _ hell))

theorem smooth_axialDensity {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h : ℝ) (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) :
    Smooth S (axialDensity h n v u p) :=
  ((((contDiffOn_fst.mul (smooth_timeOp hS (hu n le_rfl) h _ hell)).add
    (smooth_dr hS (smooth_conv hv hu))).add
      (contDiffOn_fst.mul (smooth_axialOp hS ((smooth_conv hu hu).add hp) h _ hell))).sub
        (smooth_dr hS (smooth_axialViscousFlux hS (hu n le_rfl)))).sub
          (contDiffOn_fst.mul (smooth_axialOp2 hS (hu (n - 1) (Nat.sub_le _ _)) h _ hell))

theorem exterior_weighted {S : Set ℝ} {B : ℝ} {f : Field} (hf : exterior B S f) (m : ℕ) :
    exterior B S (weighted m f) := by
  intro eta heta R hR
  simp [weighted, hf eta heta R hR]

theorem exterior_timeOp {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) (h b : ℝ) : exterior B S (timeOp h b f) := by
  intro eta heta R hR
  simp [timeOp, hs eta heta R hR, exterior_dr hS hf hs eta heta R hR,
    exterior_de hS hf hs eta heta R hR]

theorem exterior_axialOp2 {S : Set ℝ} (hS : IsOpen S) {f : Field} (hf : Smooth S f)
    {B : ℝ} (hs : exterior B S f) (h b : ℝ)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0) : exterior B S (axialOp2 h b f) :=
  exterior_axialOp hS (smooth_axialOp hS hf h b hell) (exterior_axialOp hS hf hs h b) h _

theorem exterior_angularDensity {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h B : ℝ) (hV : ∀ j, j ≤ n → exterior B S (v j))
    (hU : ∀ j, j ≤ n → exterior B S (u j)) (hE : exterior B S (e n))
    (hprev : exterior B S (axialOp2 h (orderExponent h (n - 1)) (e (n - 1)))) :
    exterior B S (angularDensity h n v u e) := by
  have hr := exterior_dr hS (smooth_weighted (smooth_conv hv he) 1)
    (exterior_weighted (exterior_conv_left hV) 1)
  have hz := exterior_axialOp hS (smooth_conv hu he) (exterior_conv_left hU) h (pressureExponent h
      n)
  have hvf : exterior B S (angularViscousFlux (e n)) := by
    intro eta heta R hR
    simp [angularViscousFlux, hE eta heta R hR, exterior_dr hS (he n le_rfl) hE eta heta R hR]
  have hk := exterior_dr hS (smooth_angularViscousFlux hS (he n le_rfl)) hvf
  intro eta heta R hR
  simp [angularDensity, exterior_timeOp hS (he n le_rfl) hE h (orderExponent h n) eta heta R hR,
    hr eta heta R hR, hz eta heta R hR, hk eta heta R hR, hprev eta heta R hR]

theorem exterior_axialDensity {S : Set ℝ} (hS : IsOpen S) {n : ℕ}
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h B : ℝ) (hV : ∀ j, j ≤ n → exterior B S (v j))
    (hU : ∀ j, j ≤ n → exterior B S (u j)) (hP : exterior B S p)
    (hprev : exterior B S (axialOp2 h (orderExponent h (n - 1)) (u (n - 1)))) :
    exterior B S (axialDensity h n v u p) := by
  have hr := exterior_dr hS (smooth_conv hv hu) (exterior_conv_left hV)
  have hcp : exterior B S (fun w => conv n u u w + p w) := by
    intro eta heta R hR
    change conv n u u (R, eta) + p (R, eta) = 0
    rw [exterior_conv_left hU eta heta R hR, hP eta heta R hR, add_zero]
  have hz := exterior_axialOp hS ((smooth_conv hu hu).add hp) hcp h (pressureExponent h n)
  have hvf : exterior B S (axialViscousFlux (u n)) := by
    intro eta heta R hR
    simp [axialViscousFlux, exterior_dr hS (hu n le_rfl) (hU n le_rfl) eta heta R hR]
  have hk := exterior_dr hS (smooth_axialViscousFlux hS (hu n le_rfl)) hvf
  intro eta heta R hR
  simp [axialDensity, exterior_timeOp hS (hu n le_rfl) (hU n le_rfl) h (orderExponent h n) eta heta
      R hR,
    hr eta heta R hR, hz eta heta R hR, hk eta heta R hR, hprev eta heta R hR]

/-- Angular stress, given by `stress 2 (angularDensity h n v u e)`. -/
noncomputable def angularStress (h : ℝ) (n : ℕ) (v u e : History) : Field :=
  stress 2 (angularDensity h n v u e)

/-- Axial stress, given by `stress 1 (axialDensity h n v u p)`. -/
noncomputable def axialStress (h : ℝ) (n : ℕ) (v u : History) (p : Field) : Field :=
  stress 1 (axialDensity h n v u p)

/-- For n≥2 all the angular hypotheses below are supplied by ordinary
positive-order moments and compact positive-order profiles. -/
theorem angular_stress_support {S : Set ℝ} (hS : IsOpen S) {n : ℕ} (hn : 2 ≤ n)
    {v u e : History} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (he : ∀ j, j ≤ n → Smooth S (e j))
    (h a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hV : ∀ j, j ≤ n → exterior B S (v j)) (hU : ∀ j, j ≤ n → exterior B S (u j))
    (hE : ∀ j, 0 < j → j ≤ n → exterior B S (e j))
    (hem : ∀ eta ∈ S, moment B 2 (e n) eta = 0)
    (hum : ∀ eta ∈ S, moment B 2 (conv n u e) eta = 0)
    (hprev : ∀ eta ∈ S, moment B 2 (e (n - 1)) eta = 0)
    (hdiv : ∀ w : ℝ × ℝ, w.2 ∈ S → ∀ j, j ≤ n →
      dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, angularWeighted h n v u e (R, eta) = 0) :
    Smooth S (angularStress h n v u e) ∧ radialSupport S a B (angularStress h n v u e) ∧
      ∀ eta ∈ S, ∀ R, 0 < R → HasDerivAt (fun r => r ^ 2 * angularStress h n v u e (r, eta))
        (-angularWeighted h n v u e (R, eta)) R := by
  have hen := hE n (by omega) le_rfl
  have hep := hE (n - 1) (by omega) (Nat.sub_le _ _)
  have hsm := smooth_angularDensity hS hv hu he h hell
  have htotal : ∀ eta ∈ S, moment B 0 (angularDensity h n v u e) eta = 0 :=
    fun eta heta => angular_integral_zero hS hv hu he h B hell hen hV hem hum
      (exterior_conv_left hU) hep hprev heta
  have hout := exterior_angularDensity hS hv hu he h B hV hU hen
    (exterior_axialOp2 hS (he (n - 1) (Nat.sub_le _ _)) hep h _ hell)
  have hin : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, angularDensity h n v u e (R, eta) = 0 := by
    intro eta heta R hR
    rw [← angularWeighted_eq_density hS hv hu he h heta (hdiv _ heta)]
    exact hinner eta heta R hR
  refine ⟨stress_smooth hS hsm 2 ha hin, stress_radialSupport 2 hB hin hout htotal, ?_⟩
  intro eta heta R hR
  rw [angularWeighted_eq_density hS hv hu he h heta (hdiv _ heta)]
  exact stress_weighted_hasDerivAt hS hsm 2 hR heta

theorem axial_stress_support {S : Set ℝ} (hS : IsOpen S) {n : ℕ} (hn : 0 < n)
    {v u : History} {p : Field} (hv : ∀ j, j ≤ n → Smooth S (v j))
    (hu : ∀ j, j ≤ n → Smooth S (u j)) (hp : Smooth S p)
    (h a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hV : ∀ j, j ≤ n → exterior B S (v j)) (hU : ∀ j, j ≤ n → exterior B S (u j))
    (hP : exterior B S p) (haxis : ∀ eta ∈ S, ∀ j, j ≤ n → v j (0, eta) = 0)
    (hum : ∀ eta ∈ S, moment B 1 (u n) eta = 0)
    (hflux : ∀ eta ∈ S, moment B 1 (fun w => conv n u u w + p w) eta = 0)
    (hprev : ∀ eta ∈ S, moment B 1 (u (n - 1)) eta = 0)
    (hdiv : ∀ w : ℝ × ℝ, w.2 ∈ S → ∀ j, j ≤ n →
      dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, axialWeighted h n v u p (R, eta) = 0) :
    Smooth S (axialStress h n v u p) ∧ radialSupport S a B (axialStress h n v u p) ∧
      ∀ eta ∈ S, ∀ R, 0 < R → HasDerivAt (fun r => r * axialStress h n v u p (r, eta))
        (-axialWeighted h n v u p (R, eta)) R := by
  have hprev_le : n - 1 ≤ n := (Nat.sub_lt hn (by decide : 0 < 1)).le
  have hsm := smooth_axialDensity hS hv hu hp h hell
  have hax : ∀ eta ∈ S, conv n v u (0, eta) = 0 := by
    intro eta heta
    unfold conv
    apply Finset.sum_eq_zero
    intro j hj
    rw [haxis eta heta j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), zero_mul]
  have hfB : ∀ eta ∈ S, conv n u u (B, eta) + p (B, eta) = 0 := by
    intro eta heta
    rw [exterior_conv_left hU eta heta B le_rfl, hP eta heta B le_rfl, add_zero]
  have htotal : ∀ eta ∈ S, moment B 0 (axialDensity h n v u p) eta = 0 :=
    fun eta heta => axial_integral_zero hS hv hu hp h B hell (hU n le_rfl) hV hax hum hflux hfB
      (hU (n - 1) hprev_le) hprev heta
  have hout := exterior_axialDensity hS hv hu hp h B hV hU hP
    (exterior_axialOp2 hS (hu (n - 1) (Nat.sub_le _ _)) (hU (n - 1) (Nat.sub_le _ _)) h _ hell)
  have hin : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, axialDensity h n v u p (R, eta) = 0 := by
    intro eta heta R hR
    rw [← axialWeighted_eq_density hS hv hu hp h heta (hdiv _ heta)]
    exact hinner eta heta R hR
  refine ⟨stress_smooth hS hsm 1 ha hin, stress_radialSupport 1 hB hin hout htotal, ?_⟩
  intro eta heta R hR
  rw [axialWeighted_eq_density hS hv hu hp h heta (hdiv _ heta)]
  unfold axialStress
  simpa only [pow_one] using stress_weighted_hasDerivAt hS hsm 1 hR heta

/-- The order-one angular input is a moment of the actual axial viscosity,
not a condition on the total residual. It is supplied by differentiating
the restored renormalized order-zero physical angular moment. -/
noncomputable def LowerAngularViscosityMoment (S : Set ℝ) (B h : ℝ) (e₀ : Field) : Prop :=
  ∀ eta ∈ S, moment B 2 (axialOp2 h (orderExponent h 0) e₀) eta = 0

theorem order_one_angular_stress_support {S : Set ℝ} (hS : IsOpen S)
    {v u e : History} (hv : ∀ j, j ≤ 1 → Smooth S (v j))
    (hu : ∀ j, j ≤ 1 → Smooth S (u j)) (he : ∀ j, j ≤ 1 → Smooth S (e j))
    (h a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hell : ∀ eta ∈ S, PositiveAxisSystem.ell h eta ≠ 0)
    (hV : ∀ j, j ≤ 1 → exterior B S (v j)) (hU : ∀ j, j ≤ 1 → exterior B S (u j))
    (hE : exterior B S (e 1))
    (hem : ∀ eta ∈ S, moment B 2 (e 1) eta = 0)
    (hum : ∀ eta ∈ S, moment B 2 (conv 1 u e) eta = 0)
    (hvisc : LowerAngularViscosityMoment S B h (e 0))
    (hviscExterior : exterior B S (axialOp2 h (orderExponent h 0) (e 0)))
    (hdiv : ∀ w : ℝ × ℝ, w.2 ∈ S → ∀ j, j ≤ 1 →
      dr (v j) w = -w.1 * axialOp h (orderExponent h j) (u j) w)
    (hinner : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, angularWeighted h 1 v u e (R, eta) = 0) :
    Smooth S (angularStress h 1 v u e) ∧ radialSupport S a B (angularStress h 1 v u e) ∧
      ∀ eta ∈ S, ∀ R, 0 < R → HasDerivAt (fun r => r ^ 2 * angularStress h 1 v u e (r, eta))
        (-angularWeighted h 1 v u e (R, eta)) R := by
  have hsm := smooth_angularDensity hS hv hu he h hell
  have htotal : ∀ eta ∈ S, moment B 0 (angularDensity h 1 v u e) eta = 0 := by
    intro eta heta
    rw [angular_integral_balance hS hv hu he h B hell hE hV hem hum (exterior_conv_left hU) heta]
    simp only [Nat.sub_self, hvisc eta heta, neg_zero]
  have hout := exterior_angularDensity hS hv hu he h B hV hU hE hviscExterior
  have hin : ∀ eta ∈ S, ∀ R ∈ Icc 0 a, angularDensity h 1 v u e (R, eta) = 0 := by
    intro eta heta R hR
    rw [← angularWeighted_eq_density hS hv hu he h heta (hdiv _ heta)]
    exact hinner eta heta R hR
  refine ⟨stress_smooth hS hsm 2 ha hin, stress_radialSupport 2 hB hin hout htotal, ?_⟩
  intro eta heta R hR
  rw [angularWeighted_eq_density hS hv hu he h heta (hdiv _ heta)]
  exact stress_weighted_hasDerivAt hS hsm 2 hR heta

/-- A concrete two-edge weight of the form prescribed in (20). -/
noncomputable def logFlatWeight (l r cL cR R : ℝ) : ℝ :=
  if R ∈ Ioo l r then
    FlatCutoff.edge cL (Real.log (R / l)) * FlatCutoff.edge cR (Real.log (r / R))
  else 0

theorem logFlatWeight_pos {l r : ℝ} (hl : 0 < l) (cL cR : ℝ)
    {R : ℝ} (hR : R ∈ Ioo l r) : 0 < logFlatWeight l r cL cR R := by
  rw [logFlatWeight, ite_eq_left hR]
  apply mul_pos
  · exact FlatCutoff.edge_pos cL (Real.log_pos ((one_lt_div hl).mpr hR.1))
  · exact FlatCutoff.edge_pos cR (Real.log_pos ((one_lt_div (hl.trans hR.1)).mpr hR.2))

theorem logFlatWeight_contDiffOn {l r cL cR : ℝ} (hl : 0 < l)
    (hcL : 0 < cL) (hcR : 0 < cR) :
    ContDiffOn ℝ ∞ (logFlatWeight l r cL cR) (Ioo l r) := by
  intro R hR
  apply ContDiffAt.contDiffWithinAt
  have hp := hl.trans hR.1
  have hr := hp.trans hR.2
  have hleft : ContDiffAt ℝ ∞ (fun x : ℝ => Real.log (x / l)) R :=
    (contDiffAt_id.div_const l).log (div_ne_zero hp.ne' hl.ne')
  have hright : ContDiffAt ℝ ∞ (fun x : ℝ => Real.log (r / x)) R :=
    (contDiffAt_const.div contDiffAt_id hp.ne').log (div_ne_zero hr.ne' hp.ne')
  have hs : ContDiffAt ℝ ∞ (fun x =>
      FlatCutoff.edge cL (Real.log (x / l)) * FlatCutoff.edge cR (Real.log (r / x))) R :=
    ((FlatCutoff.edge_contDiff hcL).contDiffAt.comp R hleft).mul
      ((FlatCutoff.edge_contDiff hcR).contDiffAt.comp R hright)
  apply hs.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hR] with x hx
  exact ite_eq_left hx

/-- In particular the prescribed logarithmic Gaussian weight controls every
jet, with inverse-edge loss zero, for a field supported strictly inside both
fixed edges. The constants are obtained from compactness. -/
theorem logarithmic_weighted_jets {S K : Set ℝ} (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S)
    {f : Field} (hf : Smooth S f) {a b l r cL cR : ℝ}
    (hs : radialSupport S a b f) (hab : Icc a b ⊆ Ioo l r)
    (hl : 0 < l) (hcL : 0 < cL) (hcR : 0 < cR) :
    Smooth S (fun w => f w / logFlatWeight l r cL cR w.1) ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Ioo l r, ∀ eta ∈ K,
        ‖iteratedFDeriv ℝ k f (R, eta)‖ ≤ C * logFlatWeight l r cL cR R := by
  have hz := logFlatWeight_contDiffOn (r := r) hl hcL hcR
  have hp : ∀ R ∈ Ioo l r, 0 < logFlatWeight l r cL cR R :=
    fun R hR => logFlatWeight_pos hl cL cR hR
  exact ⟨interior_quotient_smooth hS hf hs hab hz (fun R hR => (hp R hR).ne'),
    interior_weighted_jets hS hK hKS hf hs hab hz.continuousOn hp⟩

end NavierStokes.SlowStressSupport
