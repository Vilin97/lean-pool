/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingTail
import LeanPool.NavierStokesAndEuler.NavierStokes.MomentRepair
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricFlatFactor
import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothMomentRepair
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedMomentRepair
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Uniform applicability of the angular reset

The actual two-bump moment system is uniformly invertible down to `lam = 0`.
The outgoing uniform wait damps the angular-history discrepancy and its
parameter derivatives before this nonlinear repair is applied.
-/

section

/-!
# A pressure-neutral angular-moment reset

Two identical translated smooth relative bumps repair the angular moment while
preserving the pressure integral exactly. The actual two-row derivative matrix
is proved nonsingular, and the small smooth nonlinear branch is constructed.
-/

@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace NavierStokes.AngularMomentReset

/-- Coefficient: an abbreviation for `Fin 2 → ℝ`. -/
abbrev Coeff := Fin 2 → ℝ

/-- Template, given by `LocalizedMomentRepair.bump (-3 / 10) (3 / 10)`. -/
def template : ℝ → ℝ := LocalizedMomentRepair.bump (-3 / 10) (3 / 10)

/-- Bump, given by `template (y - 2 * (j.val : ℝ))`. -/
def bump (j : Fin 2) (y : ℝ) : ℝ := template (y - 2 * (j.val : ℝ))

theorem template_contDiff : ContDiff ℝ ∞ template :=
  LocalizedMomentRepair.bump_contDiff _ _

theorem template_at_zero : template 0 = 1 := by
  have h := LocalizedMomentRepair.bump_at_center (-3 / 10) (3 / 10)
  norm_num at h
  simpa [template, neg_div] using h

theorem template_support : support template ⊆ Icc (-3 / 20 : ℝ) (3 / 20) := by
  have h := LocalizedMomentRepair.bump_support_subset (-3 / 10) (3 / 10) (by norm_num)
  norm_num [LocalizedMomentRepair.innerLower, LocalizedMomentRepair.innerUpper] at h
  simpa [template, neg_div] using h

theorem template_hasCompactSupport : HasCompactSupport template :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc template_support

theorem bump_contDiff (j : Fin 2) : ContDiff ℝ ∞ (bump j) :=
  template_contDiff.comp (contDiff_id.sub contDiff_const)

theorem bump_nonneg (j : Fin 2) (y : ℝ) : 0 ≤ bump j y :=
  LocalizedMomentRepair.bump_nonneg _ _ _

theorem bump_le_one (j : Fin 2) (y : ℝ) : bump j y ≤ 1 :=
  LocalizedMomentRepair.bump_le_one _ _ _

theorem bump_support (j : Fin 2) :
    support (bump j) ⊆ Icc (2 * (j.val : ℝ) - 3 / 20) (2 * (j.val : ℝ) + 3 / 20) := by
  intro y hy
  have h := template_support hy
  change (-3 : ℝ) / 20 ≤ y - 2 * (j.val : ℝ) ∧ y - 2 * (j.val : ℝ) ≤ 3 / 20 at h
  constructor <;> linarith [h.1, h.2]

theorem bump_hasCompactSupport (j : Fin 2) : HasCompactSupport (bump j) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (bump_support j)

theorem bumps_disjoint (y : ℝ) : bump 0 y * bump 1 y = 0 := by
  by_cases h0 : bump 0 y = 0
  · simp [h0]
  by_cases h1 : bump 1 y = 0
  · simp [h1]
  have hs0 := bump_support 0 h0
  have hs1 := bump_support 1 h1
  norm_num at hs0 hs1
  linarith [hs0.2, hs1.1]

/-- Moment, given by `∫ y, Real.exp (s * y) * template y`. -/
def moment (s : ℝ) : ℝ := ∫ y, Real.exp (s * y) * template y

theorem weighted_bump_integrable (s : ℝ) (j : Fin 2) :
    Integrable (fun y => Real.exp (s * y) * bump j y) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (bump_contDiff j).continuous).integrable_of_hasCompactSupport
      (bump_hasCompactSupport j).mul_left

theorem weighted_bump_sq_integrable (s : ℝ) (j : Fin 2) :
    Integrable (fun y => Real.exp (s * y) * (bump j y) ^ 2) := by
  have hc : HasCompactSupport (fun y => (bump j y) ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using (bump_hasCompactSupport j).mul_right (f' := bump j)
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((bump_contDiff j).continuous.pow 2)).integrable_of_hasCompactSupport hc.mul_left

theorem moment_pos (s : ℝ) : 0 < moment s := by
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        template_contDiff.continuous)
    template_hasCompactSupport.mul_left
  · intro y
    exact mul_nonneg (Real.exp_pos _).le (LocalizedMomentRepair.bump_nonneg _ _ _)
  · exact (show Real.exp (s * 0) * template 0 ≠ 0 by simp [template_at_zero])

/-- Translation multiplies an exponential bump moment by its exact exponential factor. -/
theorem bump_moment (s : ℝ) (j : Fin 2) :
    (∫ y, Real.exp (s * y) * bump j y) =
      Real.exp (s * (2 * (j.val : ℝ))) * moment s := by
  rw [← integral_add_right_eq_self (fun y => Real.exp (s * y) * bump j y)
    (2 * (j.val : ℝ))]
  have hf : (fun y => Real.exp (s * (y + 2 * (j.val : ℝ))) * bump j (y + 2 * (j.val : ℝ))) =
      (fun y => Real.exp (s * (2 * (j.val : ℝ))) * (Real.exp (s * y) * template y)) := by
    funext y
    simp only [bump, add_sub_cancel_right, mul_add, Real.exp_add]
    ring
  rw [hf, integral_const_mul]
  rfl

/-- Angular slope, given by `1 - lam`. -/
def angularSlope (lam : ℝ) : ℝ := 1 - lam
/-- Pressure slope, given by `-1 - 2 * lam`. -/
def pressureSlope (lam : ℝ) : ℝ := -1 - 2 * lam

/-- The actual derivative matrix of the two integral changes at zero coefficients. -/
def linearMatrix (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![moment (angularSlope lam), Real.exp (2 * angularSlope lam) * moment (angularSlope lam);
      2 * moment (pressureSlope lam),
        2 * (Real.exp (2 * pressureSlope lam) * moment (pressureSlope lam))]

theorem linearMatrix_det (lam : ℝ) :
    (linearMatrix lam).det = 2 * moment (angularSlope lam) * moment (pressureSlope lam) *
      (Real.exp (2 * pressureSlope lam) - Real.exp (2 * angularSlope lam)) := by
  simp [linearMatrix, Matrix.det_fin_two]
  ring

theorem linearMatrix_det_ne_zero (lam : ℝ) (hlam : 0 < lam) :
    (linearMatrix lam).det ≠ 0 := by
  rw [linearMatrix_det]
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (moment_pos _).ne') (moment_pos _).ne'
  · apply ne_of_lt
    apply sub_neg.mpr
    apply Real.exp_lt_exp.mpr
    unfold angularSlope pressureSlope
    linarith

/-- The integral derivative is an actual continuous linear equivalence. -/
def linearEquiv (lam : ℝ) (hlam : 0 < lam) : Coeff ≃L[ℝ] Coeff :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := (linearMatrix lam).mulVec
      invFun := (linearMatrix lam)⁻¹.mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun r c => Matrix.mulVec_smul _ r c
      left_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero lam hlam)), Matrix.one_mulVec]
      right_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero lam hlam)), Matrix.one_mulVec] }

/-- Relative, given by `c 0 * bump 0 y + c 1 * bump 1 y`. -/
def relative (c : Coeff) (y : ℝ) : ℝ := c 0 * bump 0 y + c 1 * bump 1 y

theorem relative_contDiff (c : Coeff) : ContDiff ℝ ∞ (relative c) :=
  (contDiff_const.mul (bump_contDiff 0)).add (contDiff_const.mul (bump_contDiff 1))

theorem relative_support (c : Coeff) : support (relative c) ⊆ Icc (-3 / 20 : ℝ) (43 / 20) := by
  intro y hy
  by_cases h0 : bump 0 y = 0
  · have h1 : bump 1 y ≠ 0 := by intro h1; exact hy (by simp [relative, h0, h1])
    have hs := bump_support 1 h1
    norm_num at hs
    constructor <;> linarith [hs.1, hs.2]
  · have hs := bump_support 0 h0
    norm_num at hs
    constructor <;> linarith [hs.1, hs.2]

theorem relative_hasCompactSupport (c : Coeff) : HasCompactSupport (relative c) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (relative_support c)

/-- Quadratic moment, given by `∫ y, Real.exp (pressureSlope lam * y) * (bump j y) ^ 2`. -/
def quadraticMoment (lam : ℝ) (j : Fin 2) : ℝ :=
  ∫ y, Real.exp (pressureSlope lam * y) * (bump j y) ^ 2

/-- Quadratic bilin, bundling `toFun`, `map_add`, `map_smul`, `map_add` and the required
compatibility proofs. -/
def quadraticBilin (lam : ℝ) : Coeff →ₗ[ℝ] Coeff →ₗ[ℝ] Coeff where
  toFun c :=
    { toFun := fun d => ![0, quadraticMoment lam 0 * c 0 * d 0 + quadraticMoment lam 1 * c 1 * d 1]
      map_add' := fun d e => by
        ext i
        fin_cases i <;> simp [Pi.add_apply]
        ring
      map_smul' := fun r d => by
        ext i
        fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
        ring }
  map_add' c d := by
    ext e i
    fin_cases i <;> simp [Pi.add_apply]
    ring
  map_smul' r c := by
    ext e i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- Quadratic continuous linear map, constructed using `LinearMap.toContinuousLinearMap`. -/
def quadraticCLM (lam : ℝ) : Coeff →L[ℝ] Coeff →L[ℝ] Coeff :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Coeff) (F' := Coeff)).toLinearMap.comp
      (quadraticBilin lam))

theorem linearEquiv_apply (lam : ℝ) (hlam : 0 < lam) (c : Coeff) :
    linearEquiv lam hlam c = (linearMatrix lam).mulVec c := rfl

theorem quadraticCLM_apply (lam : ℝ) (c d : Coeff) :
    quadraticCLM lam c d =
      ![0, quadraticMoment lam 0 * c 0 * d 0 + quadraticMoment lam 1 * c 1 * d 1] := rfl

theorem weighted_relative_integrable (s : ℝ) (c : Coeff) :
    Integrable (fun y => Real.exp (s * y) * relative c y) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (relative_contDiff c).continuous).integrable_of_hasCompactSupport
      (relative_hasCompactSupport c).mul_left

theorem weighted_relative_sq_integrable (s : ℝ) (c : Coeff) :
    Integrable (fun y => Real.exp (s * y) * (relative c y) ^ 2) := by
  have hc : HasCompactSupport (fun y => (relative c y) ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using (relative_hasCompactSupport c).mul_right (f' := relative
        c)
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    ((relative_contDiff c).continuous.pow 2)).integrable_of_hasCompactSupport hc.mul_left

theorem relative_moment (s : ℝ) (c : Coeff) :
    (∫ y, Real.exp (s * y) * relative c y) =
      moment s * c 0 + Real.exp (2 * s) * moment s * c 1 := by
  have hf : (fun y => Real.exp (s * y) * relative c y) =
      (fun y => c 0 * (Real.exp (s * y) * bump 0 y) +
        c 1 * (Real.exp (s * y) * bump 1 y)) := by
    funext y
    dsimp [relative]
    ring
  rw [hf, integral_add ((weighted_bump_integrable s 0).const_mul _)
    ((weighted_bump_integrable s 1).const_mul _), integral_const_mul, integral_const_mul,
    bump_moment, bump_moment]
  norm_num
  rw [mul_comm s 2]
  ring

theorem relative_square (c : Coeff) (y : ℝ) :
    (relative c y) ^ 2 = (c 0) ^ 2 * (bump 0 y) ^ 2 + (c 1) ^ 2 * (bump 1 y) ^ 2 := by
  calc
    _ = (c 0) ^ 2 * (bump 0 y) ^ 2 + (c 1) ^ 2 * (bump 1 y) ^ 2 +
        2 * c 0 * c 1 * (bump 0 y * bump 1 y) := by dsimp [relative]; ring
    _ = _ := by rw [bumps_disjoint]; ring

theorem relative_square_moment (lam : ℝ) (c : Coeff) :
    (∫ y, Real.exp (pressureSlope lam * y) * (relative c y) ^ 2) =
      quadraticMoment lam 0 * (c 0) ^ 2 + quadraticMoment lam 1 * (c 1) ^ 2 := by
  have hf : (fun y => Real.exp (pressureSlope lam * y) * (relative c y) ^ 2) =
      (fun y => (c 0) ^ 2 * (Real.exp (pressureSlope lam * y) * (bump 0 y) ^ 2) +
        (c 1) ^ 2 * (Real.exp (pressureSlope lam * y) * (bump 1 y) ^ 2)) := by
    funext y
    rw [relative_square]
    ring
  rw [hf, integral_add ((weighted_bump_sq_integrable _ 0).const_mul _)
    ((weighted_bump_sq_integrable _ 1).const_mul _), integral_const_mul, integral_const_mul]
  dsimp [quadraticMoment]
  ring

theorem pressure_change_integrable (lam : ℝ) (c : Coeff) :
    Integrable (fun y => Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1)) := by
  convert! ((weighted_relative_integrable (pressureSlope lam) c).const_mul 2).add
    (weighted_relative_sq_integrable (pressureSlope lam) c) using 1
  ext y
  simp only [Pi.add_apply]
  ring

theorem pressure_change_moment (lam : ℝ) (c : Coeff) :
    (∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1)) =
      2 * (moment (pressureSlope lam) * c 0 +
        Real.exp (2 * pressureSlope lam) * moment (pressureSlope lam) * c 1) +
      quadraticMoment lam 0 * (c 0) ^ 2 + quadraticMoment lam 1 * (c 1) ^ 2 := by
  have hf : (fun y => Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1)) =
      (fun y => 2 * (Real.exp (pressureSlope lam * y) * relative c y) +
        Real.exp (pressureSlope lam * y) * (relative c y) ^ 2) := by funext y; ring
  rw [hf, integral_add ((weighted_relative_integrable _ c).const_mul 2)
    (weighted_relative_sq_integrable _ c), integral_const_mul, relative_moment,
        relative_square_moment]
  ring

/-- The quadratic coefficient map equals the two actual integral changes. -/
theorem moment_map_identity (lam : ℝ) (hlam : 0 < lam) (c : Coeff) :
    linearEquiv lam hlam c + quadraticCLM lam c c =
      ![∫ y, Real.exp (angularSlope lam * y) * relative c y,
        ∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1)] := by
  rw [linearEquiv_apply, quadraticCLM_apply, relative_moment, pressure_change_moment]
  ext i
  fin_cases i <;> simp [linearMatrix, dotProduct, Fin.sum_univ_two]
  ring

/-- Debt, given by `![δ, 0]`. -/
def debt (δ : ℝ) : Coeff := ![δ, 0]

theorem debt_contDiff : ContDiff ℝ ∞ debt := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const

theorem debt_norm_le (δ : ℝ) : ‖debt δ‖ ≤ |δ| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg δ)).mpr
  intro i
  fin_cases i <;> simp [debt]

/-- A smooth small branch is obtained from the proved actual moment derivative,
not from an assumed solution or matrix rank. -/
theorem exists_normalized_branch (lam : ℝ) (hlam : 0 < lam) :
    ∃ (c : ℝ → Coeff) (ε K : ℝ), 0 < ε ∧ 0 < K ∧
      ContDiffOn ℝ ∞ c (Ioo (-ε) ε) ∧ c 0 = 0 ∧
      ∀ δ ∈ Ioo (-ε) ε,
        (∫ y, Real.exp (angularSlope lam * y) * relative (c δ) y) = δ ∧
        (∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative (c δ) y) ^ 2 - 1)) = 0 ∧
        ‖c δ‖ ≤ K * |δ| := by
  obtain ⟨c, U, K, hU, h0, hK, hc, hc0, heq⟩ :=
    SmoothMomentRepair.exists_smooth_parameter_branch (E := Coeff) (P := ℝ) 0
      (fun _ => (linearEquiv lam hlam).toContinuousLinearMap)
      (fun _ => quadraticCLM lam) debt contDiff_const contDiff_const debt_contDiff
      (linearEquiv lam hlam) rfl (by ext i; fin_cases i <;> simp [debt])
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  have hsub : Ioo (-ε) ε ⊆ U := by
    intro δ hδ
    apply hεU
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, Set.mem_Ioo] using hδ
  refine ⟨c, ε, K, hε, hK, hc.mono hsub, hc0, ?_⟩
  intro δ hδ
  obtain ⟨he, hb⟩ := heq δ (hsub hδ)
  change linearEquiv lam hlam (c δ) + quadraticCLM lam (c δ) (c δ) = debt δ at he
  rw [moment_map_identity] at he
  refine ⟨?_, ?_, hb.trans (mul_le_mul_of_nonneg_left (debt_norm_le δ) hK.le)⟩
  · exact congrFun he 0
  · exact congrFun he 1

theorem relative_deriv (c : Coeff) (y : ℝ) :
    deriv (relative c) y = c 0 * deriv (bump 0) y + c 1 * deriv (bump 1) y := by
  have h0 := (bump_contDiff 0).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have h1 := (bump_contDiff 1).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  unfold relative
  rw [deriv_fun_add (h0.differentiableAt.const_mul _) (h1.differentiableAt.const_mul _),
    deriv_const_mul _ h0.differentiableAt, deriv_const_mul _ h1.differentiableAt]

/-- The fixed finite family controls both the relative perturbation and its first derivative. -/
theorem relative_first_jet_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (c : Coeff) (y : ℝ),
      |relative c y| ≤ D * ‖c‖ ∧ |deriv (relative c) y| ≤ D * ‖c‖ := by
  obtain ⟨D0, hD0, hb0⟩ := LocalizedMomentRepair.smooth_compact_derivative_bound
    (bump 0) (bump_contDiff 0) (bump_hasCompactSupport 0) 1
  obtain ⟨D1, hD1, hb1⟩ := LocalizedMomentRepair.smooth_compact_derivative_bound
    (bump 1) (bump_contDiff 1) (bump_hasCompactSupport 1) 1
  simp only [iteratedDeriv_one] at hb0 hb1
  refine ⟨2 + D0 + D1, by linarith, ?_⟩
  intro c y
  have hc0 : |c 0| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 0
  have hc1 : |c 1| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c 1
  have ha0 : |bump 0 y| ≤ 1 := by rw [abs_of_nonneg (bump_nonneg 0 y)]; exact bump_le_one 0 y
  have ha1 : |bump 1 y| ≤ 1 := by rw [abs_of_nonneg (bump_nonneg 1 y)]; exact bump_le_one 1 y
  constructor
  · calc
      |relative c y| ≤ |c 0| * |bump 0 y| + |c 1| * |bump 1 y| := by
        simpa only [relative, abs_mul] using abs_add_le (c 0 * bump 0 y) (c 1 * bump 1 y)
      _ ≤ ‖c‖ * 1 + ‖c‖ * 1 := add_le_add
        (mul_le_mul hc0 ha0 (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul hc1 ha1 (abs_nonneg _) (norm_nonneg _))
      _ ≤ (2 + D0 + D1) * ‖c‖ := by nlinarith [norm_nonneg c]
  · rw [relative_deriv]
    calc
      _ ≤ |c 0| * |deriv (bump 0) y| + |c 1| * |deriv (bump 1) y| := by
        simpa only [abs_mul] using abs_add_le (c 0 * deriv (bump 0) y) (c 1 * deriv (bump 1) y)
      _ ≤ ‖c‖ * D0 + ‖c‖ * D1 := add_le_add
        (mul_le_mul hc0 (hb0 y) (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul hc1 (hb1 y) (abs_nonneg _) (norm_nonneg _))
      _ ≤ (2 + D0 + D1) * ‖c‖ := by nlinarith [norm_nonneg c]

theorem positive_and_slope_of_small (lam : ℝ) (hlam : 0 < lam) (c : Coeff) (y : ℝ)
    (h0 : |relative c y| ≤ 1 / 2) (h1 : |deriv (relative c) y| ≤ lam / 4) :
    0 < 1 + relative c y ∧ -lam + deriv (relative c) y / (1 + relative c y) ≤ -lam / 2 := by
  have hlo : -(1 / 2 : ℝ) ≤ relative c y := (abs_le.mp h0).1
  have hden : 0 < 1 + relative c y := by linarith
  refine ⟨hden, ?_⟩
  have hd : deriv (relative c) y ≤ lam / 4 := (le_abs_self _).trans h1
  have hratio : deriv (relative c) y / (1 + relative c y) ≤ lam / 2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

/-- A constructed branch, with exact normalized integrals and quantitative first-jet control. -/
structure ResetBranch (lam : ℝ) where
  /-- Coefficients of `ResetBranch`, of type `ℝ → Coeff`. -/
  coefficients : ℝ → Coeff
  /-- Radius of `ResetBranch`, of type `ℝ`. -/
  radius : ℝ
  /-- Bound of `ResetBranch`, of type `ℝ`. -/
  bound : ℝ
  radius_pos : 0 < radius
  bound_pos : 0 < bound
  smooth : ContDiffOn ℝ ∞ coefficients (Ioo (-radius) radius)
  at_zero : coefficients 0 = 0
  angular : ∀ δ ∈ Ioo (-radius) radius,
    (∫ y, Real.exp (angularSlope lam * y) * relative (coefficients δ) y) = δ
  pressure : ∀ δ ∈ Ioo (-radius) radius,
    (∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative (coefficients δ) y) ^ 2 - 1)) = 0
  coefficient_bound : ∀ δ ∈ Ioo (-radius) radius, ‖coefficients δ‖ ≤ bound * |δ|
  first_jet_bound : ∀ δ ∈ Ioo (-radius) radius, ∀ y,
    |relative (coefficients δ) y| ≤ bound * |δ| ∧
    |deriv (relative (coefficients δ)) y| ≤ bound * |δ|
  small_jets : ∀ δ ∈ Ioo (-radius) radius, ∀ y,
    |relative (coefficients δ) y| ≤ 1 / 2 ∧
    |deriv (relative (coefficients δ)) y| ≤ lam / 4

/-- No branch fields are hypotheses: all of them are constructed from the explicit bumps. -/
theorem exists_resetBranch (lam : ℝ) (hlam : 0 < lam) : Nonempty (ResetBranch lam) := by
  obtain ⟨c, ε0, K, hε0, hK, hc, hc0, heq⟩ := exists_normalized_branch lam hlam
  obtain ⟨D, hD, hjet⟩ := relative_first_jet_bound
  let b : ℝ := min (1 / 2) (lam / 4)
  let ε : ℝ := min ε0 (b / (D * K))
  let L : ℝ := (1 + D) * K
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hDK : 0 < D * K := mul_pos hD hK
  have hε : 0 < ε := lt_min hε0 (div_pos hb hDK)
  have hL : 0 < L := mul_pos (by linarith) hK
  have hsub : Ioo (-ε) ε ⊆ Ioo (-ε0) ε0 := by
    intro δ hδ
    have he : ε ≤ ε0 := min_le_left _ _
    constructor <;> linarith [hδ.1, hδ.2]
  have htotal : ∀ δ ∈ Ioo (-ε) ε, D * ‖c δ‖ ≤ b := by
    intro δ hδ
    have hnorm := (heq δ (hsub hδ)).2.2
    have habs : |δ| ≤ ε := (abs_lt.mpr hδ).le
    have he : ε ≤ b / (D * K) := min_le_right _ _
    have he' := (le_div_iff₀ hDK).mp he
    nlinarith
  have hcoeff : ∀ δ ∈ Ioo (-ε) ε, ‖c δ‖ ≤ L * |δ| := by
    intro δ hδ
    apply ((heq δ (hsub hδ)).2.2).trans
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg δ)
    dsimp [L]
    nlinarith
  refine ⟨{
    coefficients := c
    radius := ε
    bound := L
    radius_pos := hε
    bound_pos := hL
    smooth := hc.mono hsub
    at_zero := hc0
    angular := fun δ hδ => (heq δ (hsub hδ)).1
    pressure := fun δ hδ => (heq δ (hsub hδ)).2.1
    coefficient_bound := hcoeff
    first_jet_bound := ?_
    small_jets := ?_ }⟩
  · intro δ hδ y
    have hn := (heq δ (hsub hδ)).2.2
    have hL' : D * K ≤ L := by dsimp [L]; nlinarith
    have hbound : D * ‖c δ‖ ≤ L * |δ| :=
      (mul_le_mul_of_nonneg_left hn hD.le).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hL' (abs_nonneg δ))
    exact ⟨(hjet (c δ) y).1.trans hbound, (hjet (c δ) y).2.trans hbound⟩
  · intro δ hδ y
    exact ⟨((hjet (c δ) y).1.trans (htotal δ hδ)).trans (min_le_left _ _),
      ((hjet (c δ) y).2.trans (htotal δ hδ)).trans (min_le_right _ _)⟩

/-- One fixed choice of the proved small branch. -/
def resetBranch (lam : ℝ) (hlam : 0 < lam) : ResetBranch lam :=
  Classical.choice (exists_resetBranch lam hlam)

/-! ## Actual modified angular fields -/

/-- Base E, given by `e0 * Real.exp ((-1 / 2 - lam) * y)`. -/
def baseE (lam e0 y : ℝ) : ℝ := e0 * Real.exp ((-1 / 2 - lam) * y)

/-- The first bump is centered at `y0`, and the second at `y0 + 2`. -/
def modifiedE (lam e0 y0 : ℝ) (c : Coeff) (y : ℝ) : ℝ :=
  baseE lam e0 y * (1 + relative c (y - y0))

/-- Radius X, given by `X0 * Real.exp y`. -/
def radiusX (X0 y : ℝ) : ℝ := X0 * Real.exp y

/-- Base H, given by `Real.sqrt (2 * radiusX X0 y) * baseE lam e0 y`. -/
def baseH (lam e0 X0 y : ℝ) : ℝ := Real.sqrt (2 * radiusX X0 y) * baseE lam e0 y

/-- Modified H, given by `Real.sqrt (2 * radiusX X0 y) * modifiedE lam e0 y0 c y`. -/
def modifiedH (lam e0 X0 y0 : ℝ) (c : Coeff) (y : ℝ) : ℝ :=
  Real.sqrt (2 * radiusX X0 y) * modifiedE lam e0 y0 c y

/-- Angular scale, given by `X0 * Real.sqrt (2 * X0) * e0 * Real.exp (angularSlope lam * y0)`. -/
def angularScale (lam e0 X0 y0 : ℝ) : ℝ :=
  X0 * Real.sqrt (2 * X0) * e0 * Real.exp (angularSlope lam * y0)

/-- Log slope, given by `1 / 2 + deriv E y / E y`. -/
def logSlope (E : ℝ → ℝ) (y : ℝ) : ℝ := 1 / 2 + deriv E y / E y

theorem baseE_contDiff (lam e0 : ℝ) : ContDiff ℝ ∞ (baseE lam e0) :=
  contDiff_const.mul (contDiff_const.mul contDiff_id).exp

theorem modifiedE_contDiff (lam e0 y0 : ℝ) (c : Coeff) :
    ContDiff ℝ ∞ (modifiedE lam e0 y0 c) :=
  (baseE_contDiff lam e0).mul
    (contDiff_const.add ((relative_contDiff c).comp (contDiff_id.sub contDiff_const)))

theorem baseE_pos (lam e0 y : ℝ) (he0 : 0 < e0) : 0 < baseE lam e0 y :=
  mul_pos he0 (Real.exp_pos _)

theorem modifiedE_sub_support (lam e0 y0 : ℝ) (c : Coeff) :
    support (modifiedE lam e0 y0 c - baseE lam e0) ⊆
      Icc (y0 - 3 / 20) (y0 + 43 / 20) := by
  intro y hy
  have hn : relative c (y - y0) ≠ 0 := by
    intro hz
    exact hy (by simp [modifiedE, hz])
  have hs := relative_support c hn
  constructor <;> linarith [hs.1, hs.2]

theorem modifiedE_sub_hasCompactSupport (lam e0 y0 : ℝ) (c : Coeff) :
    HasCompactSupport (modifiedE lam e0 y0 c - baseE lam e0) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (modifiedE_sub_support lam e0 y0 c)

/-- Choosing `y0 = T - 3` places the whole edit strictly inside `(T - 4, T)`. -/
theorem modifiedE_sub_tsupport (lam e0 y0 : ℝ) (c : Coeff) :
    tsupport (modifiedE lam e0 y0 c - baseE lam e0) ⊆ Ioo (y0 - 1) (y0 + 3) := by
  apply (closure_minimal (modifiedE_sub_support lam e0 y0 c) isClosed_Icc).trans
  intro y hy
  constructor <;> linarith [hy.1, hy.2]

theorem modifiedE_unchanged (lam e0 y0 : ℝ) (c : Coeff) {y : ℝ}
    (hy : y ∉ Ioo (y0 - 1) (y0 + 3)) : modifiedE lam e0 y0 c y = baseE lam e0 y := by
  by_contra hn
  apply hy
  apply modifiedE_sub_tsupport lam e0 y0 c
  exact subset_closure (show (modifiedE lam e0 y0 c - baseE lam e0) y ≠ 0 from sub_ne_zero.mpr hn)

theorem baseE_hasDerivAt (lam e0 y : ℝ) :
    HasDerivAt (baseE lam e0) (baseE lam e0 y * (-1 / 2 - lam)) y := by
  convert! (((hasDerivAt_id y).const_mul (-1 / 2 - lam)).exp).const_mul e0 using 1
  simp [baseE]
  ring

theorem modifiedE_hasDerivAt (lam e0 y0 : ℝ) (c : Coeff) (y : ℝ) :
    HasDerivAt (modifiedE lam e0 y0 c)
      (baseE lam e0 y * (-1 / 2 - lam) * (1 + relative c (y - y0)) +
        baseE lam e0 y * deriv (relative c) (y - y0)) y := by
  have hr := (((relative_contDiff c).differentiable (by simp)).differentiableAt.hasDerivAt).comp y
    ((hasDerivAt_id y).sub_const y0)
  convert! (baseE_hasDerivAt lam e0 y).mul (hr.const_add 1) using 1
  simp

theorem modifiedE_logSlope (lam e0 y0 : ℝ) (c : Coeff) (y : ℝ) (he0 : e0 ≠ 0)
    (hpos : 1 + relative c (y - y0) ≠ 0) :
    logSlope (modifiedE lam e0 y0 c) y =
      -lam + deriv (relative c) (y - y0) / (1 + relative c (y - y0)) := by
  have hb : baseE lam e0 y ≠ 0 := mul_ne_zero he0 (Real.exp_ne_zero _)
  unfold logSlope
  rw [(modifiedE_hasDerivAt lam e0 y0 c y).deriv]
  change 1 / 2 +
    (baseE lam e0 y * (-1 / 2 - lam) * (1 + relative c (y - y0)) +
      baseE lam e0 y * deriv (relative c) (y - y0)) /
    (baseE lam e0 y * (1 + relative c (y - y0))) = _
  field_simp; ring

theorem weighted_translate_integral (s y0 : ℝ) (f : ℝ → ℝ) :
    (∫ y, Real.exp (s * y) * f (y - y0)) =
      Real.exp (s * y0) * ∫ y, Real.exp (s * y) * f y := by
  rw [← integral_add_right_eq_self (fun y => Real.exp (s * y) * f (y - y0)) y0]
  have hf : (fun y => Real.exp (s * (y + y0)) * f (y + y0 - y0)) =
      (fun y => Real.exp (s * y0) * (Real.exp (s * y) * f y)) := by
    funext y
    simp only [add_sub_cancel_right, mul_add, Real.exp_add]
    ring
  rw [hf, integral_const_mul]

theorem baseE_square (lam e0 y : ℝ) :
    (baseE lam e0 y) ^ 2 = e0 ^ 2 * Real.exp (pressureSlope lam * y) := by
  unfold baseE
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  unfold pressureSlope
  ring

theorem pressure_integral_formula (lam e0 y0 : ℝ) (c : Coeff) :
    (∫ y, (modifiedE lam e0 y0 c y) ^ 2 - (baseE lam e0 y) ^ 2) =
      e0 ^ 2 * Real.exp (pressureSlope lam * y0) *
        ∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1) := by
  have hf : (fun y => (modifiedE lam e0 y0 c y) ^ 2 - (baseE lam e0 y) ^ 2) =
      (fun y => e0 ^ 2 * (Real.exp (pressureSlope lam * y) * ((1 + relative c (y - y0)) ^ 2 - 1)))
          := by
    funext y
    calc
      _ = (baseE lam e0 y) ^ 2 * ((1 + relative c (y - y0)) ^ 2 - 1) := by
        unfold modifiedE
        ring
      _ = _ := by rw [baseE_square]; ring
  rw [hf, integral_const_mul,
    weighted_translate_integral (pressureSlope lam) y0 (fun y => (1 + relative c y) ^ 2 - 1)]
  ring

theorem sqrt_exp_half (y : ℝ) : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)).mpr
  rw [← Real.exp_add]
  congr 1
  ring

theorem angular_weight_formula (lam e0 X0 y : ℝ) (hX : 0 ≤ X0) :
    radiusX X0 y * baseH lam e0 X0 y =
      X0 * Real.sqrt (2 * X0) * e0 * Real.exp (angularSlope lam * y) := by
  have hs : Real.sqrt (2 * radiusX X0 y) = Real.sqrt (2 * X0) * Real.exp (y / 2) := by
    unfold radiusX
    rw [← mul_assoc, Real.sqrt_mul (by positivity), sqrt_exp_half]
  unfold baseH
  rw [hs]
  unfold radiusX baseE
  calc
    _ = X0 * Real.sqrt (2 * X0) * e0 *
        (Real.exp y * Real.exp (y / 2) * Real.exp ((-1 / 2 - lam) * y)) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      unfold angularSlope
      ring

theorem angular_integral_formula (lam e0 X0 y0 : ℝ) (c : Coeff) (hX : 0 ≤ X0) :
    (∫ y, radiusX X0 y * (modifiedH lam e0 X0 y0 c y - baseH lam e0 X0 y)) =
      angularScale lam e0 X0 y0 * ∫ y, Real.exp (angularSlope lam * y) * relative c y := by
  have hf : (fun y => radiusX X0 y * (modifiedH lam e0 X0 y0 c y - baseH lam e0 X0 y)) =
      (fun y => (X0 * Real.sqrt (2 * X0) * e0) *
        (Real.exp (angularSlope lam * y) * relative c (y - y0))) := by
    funext y
    calc
      _ = (radiusX X0 y * baseH lam e0 X0 y) * relative c (y - y0) := by
        unfold modifiedH modifiedE baseH
        ring
      _ = _ := by rw [angular_weight_formula lam e0 X0 y hX]; ring
  rw [hf, integral_const_mul, weighted_translate_integral]
  unfold angularScale
  ring

theorem angularScale_pos (lam e0 X0 y0 : ℝ) (he0 : 0 < e0) (hX : 0 < X0) :
    0 < angularScale lam e0 X0 y0 := by
  unfold angularScale
  exact mul_pos (mul_pos (mul_pos hX (Real.sqrt_pos.mpr (by positivity))) he0) (Real.exp_pos _)

/-- The pressure change is an integrable compactly supported difference. We do
not subtract divergent integrals of the pure exponential background over `ℝ`. -/
theorem pressure_delta_integrable (lam e0 y0 : ℝ) (c : Coeff) :
    Integrable (fun y => (modifiedE lam e0 y0 c y) ^ 2 - (baseE lam e0 y) ^ 2) := by
  have hf : (fun y => (modifiedE lam e0 y0 c y) ^ 2 - (baseE lam e0 y) ^ 2) =
      (fun y => (modifiedE lam e0 y0 c y + baseE lam e0 y) *
        (modifiedE lam e0 y0 c y - baseE lam e0 y)) := by funext y; ring
  rw [hf]
  exact (((modifiedE_contDiff lam e0 y0 c).continuous.add (baseE_contDiff lam e0).continuous).mul
    ((modifiedE_contDiff lam e0 y0 c).continuous.sub (baseE_contDiff lam
        e0).continuous)).integrable_of_hasCompactSupport
      (modifiedE_sub_hasCompactSupport lam e0 y0 c).mul_left

theorem angular_delta_integrable (lam e0 X0 y0 : ℝ) (c : Coeff) :
    Integrable (fun y => radiusX X0 y * (modifiedH lam e0 X0 y0 c y - baseH lam e0 X0 y)) := by
  have hf : (fun y => radiusX X0 y * (modifiedH lam e0 X0 y0 c y - baseH lam e0 X0 y)) =
      (fun y => (radiusX X0 y * Real.sqrt (2 * radiusX X0 y)) *
        (modifiedE lam e0 y0 c y - baseE lam e0 y)) := by
    funext y
    unfold modifiedH baseH
    ring
  rw [hf]
  have hX : Continuous (radiusX X0) := continuous_const.mul Real.continuous_exp
  have hw : Continuous (fun y => radiusX X0 y * Real.sqrt (2 * radiusX X0 y)) :=
    hX.mul (Real.continuous_sqrt.comp (continuous_const.mul hX))
  exact (hw.mul ((modifiedE_contDiff lam e0 y0 c).continuous.sub
    (baseE_contDiff lam e0).continuous)).integrable_of_hasCompactSupport
      (modifiedE_sub_hasCompactSupport lam e0 y0 c).mul_left

theorem modifiedH_unchanged (lam e0 X0 y0 : ℝ) (c : Coeff) {y : ℝ}
    (hy : y ∉ Ioo (y0 - 1) (y0 + 3)) :
    modifiedH lam e0 X0 y0 c y = baseH lam e0 X0 y := by
  unfold modifiedH baseH
  rw [modifiedE_unchanged lam e0 y0 c hy]

namespace ResetBranch

variable {lam : ℝ} (B : ResetBranch lam)

theorem pressure_neutral (e0 y0 δ : ℝ) (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    (∫ y, (modifiedE lam e0 y0 (B.coefficients δ) y) ^ 2 - (baseE lam e0 y) ^ 2) = 0 := by
  rw [pressure_integral_formula, B.pressure δ hδ, mul_zero]

theorem angular_change (e0 X0 y0 δ : ℝ) (hX : 0 ≤ X0)
    (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    (∫ y, radiusX X0 y *
      (modifiedH lam e0 X0 y0 (B.coefficients δ) y - baseH lam e0 X0 y)) =
      angularScale lam e0 X0 y0 * δ := by
  rw [angular_integral_formula lam e0 X0 y0 (B.coefficients δ) hX, B.angular δ hδ]

theorem positive (hlam : 0 < lam) (e0 y0 δ y : ℝ) (he0 : 0 < e0)
    (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    0 < modifiedE lam e0 y0 (B.coefficients δ) y := by
  apply mul_pos (baseE_pos lam e0 y he0)
  exact (positive_and_slope_of_small lam hlam (B.coefficients δ) (y - y0)
    (B.small_jets δ hδ (y - y0)).1 (B.small_jets δ hδ (y - y0)).2).1

theorem logSlope_le (hlam : 0 < lam) (e0 y0 δ y : ℝ) (he0 : 0 < e0)
    (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    logSlope (modifiedE lam e0 y0 (B.coefficients δ)) y ≤ -lam / 2 := by
  have hp := positive_and_slope_of_small lam hlam (B.coefficients δ) (y - y0)
    (B.small_jets δ hδ (y - y0)).1 (B.small_jets δ hδ (y - y0)).2
  rw [modifiedE_logSlope lam e0 y0 (B.coefficients δ) y he0.ne' hp.1.ne']
  exact hp.2

/-- Any desired angular endpoint moment is reached when its normalized debt
lies in the constructed common small interval. -/
theorem exact_target (e0 X0 y0 Iold Itarget : ℝ) (he0 : 0 < e0) (hX : 0 < X0)
    (hδ : (Itarget - Iold) / angularScale lam e0 X0 y0 ∈ Ioo (-B.radius) B.radius) :
    Iold + (∫ y, radiusX X0 y *
      (modifiedH lam e0 X0 y0
        (B.coefficients ((Itarget - Iold) / angularScale lam e0 X0 y0)) y -
          baseH lam e0 X0 y)) = Itarget := by
  rw [B.angular_change e0 X0 y0 _ hX.le hδ]
  have hs := (angularScale_pos lam e0 X0 y0 he0 hX).ne'
  field_simp
  ring

end ResetBranch

/-! ## Finite-interval moments, including an arbitrary earlier prefix -/

theorem radiusX_continuous (X0 : ℝ) : Continuous (radiusX X0) :=
  continuous_const.mul Real.continuous_exp

theorem baseH_continuous (lam e0 X0 : ℝ) : Continuous (baseH lam e0 X0) :=
  (Real.continuous_sqrt.comp (continuous_const.mul (radiusX_continuous X0))).mul
    (baseE_contDiff lam e0).continuous

theorem modifiedH_continuous (lam e0 X0 y0 : ℝ) (c : Coeff) :
    Continuous (modifiedH lam e0 X0 y0 c) :=
  (Real.continuous_sqrt.comp (continuous_const.mul (radiusX_continuous X0))).mul
    (modifiedE_contDiff lam e0 y0 c).continuous

theorem outside_window {a b y0 y : ℝ} (ha : a ≤ y0 - 1) (hb : y0 + 3 ≤ b)
    (hy : y ∉ Icc a b) : y ∉ Ioo (y0 - 1) (y0 + 3) := by
  intro h
  exact hy ⟨ha.trans h.1.le, h.2.le.trans hb⟩

theorem angular_interval_change (lam e0 X0 y0 a b : ℝ) (c : Coeff)
    (hX : 0 ≤ X0) (ha : a ≤ y0 - 1) (hb : y0 + 3 ≤ b) :
    (∫ y in Icc a b, radiusX X0 y * modifiedH lam e0 X0 y0 c y) -
      (∫ y in Icc a b, radiusX X0 y * baseH lam e0 X0 y) =
      angularScale lam e0 X0 y0 * ∫ y, Real.exp (angularSlope lam * y) * relative c y := by
  have hm : IntegrableOn (fun y => radiusX X0 y * modifiedH lam e0 X0 y0 c y) (Icc a b) :=
    ((radiusX_continuous X0).mul (modifiedH_continuous lam e0 X0 y0
        c)).continuousOn.integrableOn_Icc
  have he : IntegrableOn (fun y => radiusX X0 y * baseH lam e0 X0 y) (Icc a b) :=
    ((radiusX_continuous X0).mul (baseH_continuous lam e0 X0)).continuousOn.integrableOn_Icc
  rw [← integral_sub hm he]
  have hi : (fun y => radiusX X0 y * modifiedH lam e0 X0 y0 c y -
      radiusX X0 y * baseH lam e0 X0 y) =
      (fun y => radiusX X0 y * (modifiedH lam e0 X0 y0 c y - baseH lam e0 X0 y)) := by
    funext y
    ring
  rw [hi, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact angular_integral_formula lam e0 X0 y0 c hX
  · intro y hy
    rw [modifiedH_unchanged lam e0 X0 y0 c (outside_window ha hb hy), sub_self, mul_zero]

theorem pressure_interval_change (lam e0 y0 a b : ℝ) (c : Coeff)
    (ha : a ≤ y0 - 1) (hb : y0 + 3 ≤ b) :
    (∫ y in Icc a b, (modifiedE lam e0 y0 c y) ^ 2) -
      (∫ y in Icc a b, (baseE lam e0 y) ^ 2) =
      e0 ^ 2 * Real.exp (pressureSlope lam * y0) *
        ∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1) := by
  have hm : IntegrableOn (fun y => (modifiedE lam e0 y0 c y) ^ 2) (Icc a b) :=
    ((modifiedE_contDiff lam e0 y0 c).continuous.pow 2).continuousOn.integrableOn_Icc
  have he : IntegrableOn (fun y => (baseE lam e0 y) ^ 2) (Icc a b) :=
    ((baseE_contDiff lam e0).continuous.pow 2).continuousOn.integrableOn_Icc
  rw [← integral_sub hm he, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact pressure_integral_formula lam e0 y0 c
  · intro y hy
    rw [modifiedE_unchanged lam e0 y0 c (outside_window ha hb hy), sub_self]

theorem ResetBranch.pressure_interval_neutral {lam : ℝ} (B : ResetBranch lam)
    (e0 y0 a b δ : ℝ) (ha : a ≤ y0 - 1) (hb : y0 + 3 ≤ b)
    (hδ : δ ∈ Ioo (-B.radius) B.radius) :
    (∫ y in Icc a b, (modifiedE lam e0 y0 (B.coefficients δ) y) ^ 2) =
      ∫ y in Icc a b, (baseE lam e0 y) ^ 2 := by
  apply sub_eq_zero.mp
  rw [pressure_interval_change lam e0 y0 a b (B.coefficients δ) ha hb, B.pressure δ hδ, mul_zero]

/-- Prefix I, given by `Iprior + ∫ y in Icc a b, radiusX X0 y * baseH lam e0 X0 y`. -/
def prefixI (lam e0 X0 a b Iprior : ℝ) : ℝ :=
  Iprior + ∫ y in Icc a b, radiusX X0 y * baseH lam e0 X0 y

theorem ResetBranch.exact_endpoint_moment {lam : ℝ} (B : ResetBranch lam)
    (e0 X0 y0 a b Iprior Itarget : ℝ) (he0 : 0 < e0) (hX : 0 < X0)
    (ha : a ≤ y0 - 1) (hb : y0 + 3 ≤ b)
    (hδ : (Itarget - prefixI lam e0 X0 a b Iprior) / angularScale lam e0 X0 y0 ∈
      Ioo (-B.radius) B.radius) :
    Iprior + (∫ y in Icc a b, radiusX X0 y * modifiedH lam e0 X0 y0
      (B.coefficients ((Itarget - prefixI lam e0 X0 a b Iprior) / angularScale lam e0 X0 y0)) y) =
        Itarget := by
  let δ := (Itarget - prefixI lam e0 X0 a b Iprior) / angularScale lam e0 X0 y0
  have hi := angular_interval_change lam e0 X0 y0 a b (B.coefficients δ) hX.le ha hb
  rw [B.angular δ hδ] at hi
  have hs : angularScale lam e0 X0 y0 ≠ 0 := (angularScale_pos lam e0 X0 y0 he0 hX).ne'
  have hd : angularScale lam e0 X0 y0 * δ = Itarget - prefixI lam e0 X0 a b Iprior := by
    dsimp [δ]
    field_simp
  rw [hd] at hi
  dsimp [prefixI] at hi
  linarith

/-! ## Smooth dependence on the angular parameter -/

theorem relative_joint_contDiff :
    ContDiff ℝ ∞ (fun z : Coeff × ℝ => relative z.1 z.2) := by
  have h0 : ContDiff ℝ ∞ (fun z : Coeff × ℝ => z.1 0) :=
    contDiff_pi.mp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Coeff × ℝ → Coeff)) 0
  have h1 : ContDiff ℝ ∞ (fun z : Coeff × ℝ => z.1 1) :=
    contDiff_pi.mp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Coeff × ℝ → Coeff)) 1
  exact (h0.mul ((bump_contDiff 0).comp contDiff_snd)).add
    (h1.mul ((bump_contDiff 1).comp contDiff_snd))

theorem ResetBranch.joint_contDiffOn {lam : ℝ} (B : ResetBranch lam)
    (e0 y0 : ℝ) {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {S : Set P} {δ : P → ℝ} (hδ : ContDiffOn ℝ ∞ δ S)
    (hsmall : ∀ p ∈ S, δ p ∈ Ioo (-B.radius) B.radius) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => modifiedE lam e0 y0 (B.coefficients (δ z.1)) z.2)
      (S ×ˢ univ) := by
  have hc : ContDiffOn ℝ ∞ (fun p => B.coefficients (δ p)) S :=
    B.smooth.comp hδ hsmall
  have hcz : ContDiffOn ℝ ∞ (fun z : P × ℝ => B.coefficients (δ z.1)) (S ×ˢ univ) :=
    hc.comp contDiffOn_fst (fun _ hz => hz.1)
  have hs : ContDiffOn ℝ ∞ (fun z : P × ℝ => z.2 - y0) (S ×ˢ univ) :=
    contDiffOn_snd.sub contDiffOn_const
  have hr : ContDiffOn ℝ ∞ (fun z : P × ℝ => relative (B.coefficients (δ z.1)) (z.2 - y0))
      (S ×ˢ univ) :=
    relative_joint_contDiff.contDiffOn.comp (hcz.prodMk hs) (mapsTo_univ _ _)
  exact ((baseE_contDiff lam e0).comp contDiff_snd).contDiffOn.mul (contDiffOn_const.add hr)

end NavierStokes.AngularMomentReset

end
end

end

@[expose] public section

noncomputable section

open Set Function Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open NavierStokes.AngularMomentReset

namespace NavierStokes.UniformAngularReset

/-- Lambda range, given by `Icc 0 (1 / 10)`. -/
def lambdaRange : Set ℝ := Icc 0 (1 / 10)

theorem linearMatrix_det_ne_zero_nonneg (lam : ℝ) (hlam : 0 ≤ lam) :
    (linearMatrix lam).det ≠ 0 := by
  rw [AngularMomentReset.linearMatrix_det]
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (moment_pos _).ne') (moment_pos _).ne'
  · apply ne_of_lt
    apply sub_neg.mpr
    apply Real.exp_lt_exp.mpr
    unfold angularSlope pressureSlope
    linarith

theorem continuous_moment : Continuous moment := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support
    (k := Icc (-3 / 20 : ℝ) (3 / 20)) isCompact_Icc
  · exact ((Real.continuous_exp.comp (continuous_fst.mul continuous_snd)).mul
      (template_contDiff.continuous.comp continuous_snd)).continuousOn
  · intro s y _ hy
    have hz : template y = 0 := Classical.byContradiction (fun hn => hy (template_support hn))
    simp [hz]

theorem continuous_quadraticMoment (j : Fin 2) : Continuous (fun lam => quadraticMoment lam j) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support
    (k := Icc (2 * (j.val : ℝ) - 3 / 20) (2 * (j.val : ℝ) + 3 / 20)) isCompact_Icc
  · exact ((Real.continuous_exp.comp ((continuous_const.sub (continuous_const.mul
      continuous_fst)).mul
      continuous_snd)).mul (((bump_contDiff j).continuous.comp continuous_snd).pow 2)).continuousOn
  · intro lam y _ hy
    have hz : bump j y = 0 := Classical.byContradiction (fun hn => hy (bump_support j hn))
    simp [hz]

/-- Linear continuous linear map, constructed using `LinearMap.toContinuousLinearMap`. -/
def linearCLM (lam : ℝ) : Coeff →L[ℝ] Coeff :=
  LinearMap.toContinuousLinearMap
    { toFun := (linearMatrix lam).mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun r c => Matrix.mulVec_smul _ r c }

/-- Linear equiv nonneg, constructed using `LinearEquiv.toContinuousLinearEquiv`. -/
def linearEquivNonneg (lam : ℝ) (hlam : 0 ≤ lam) : Coeff ≃L[ℝ] Coeff :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := (linearMatrix lam).mulVec
      invFun := (linearMatrix lam)⁻¹.mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun r c => Matrix.mulVec_smul _ r c
      left_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero_nonneg lam hlam)), Matrix.one_mulVec]
      right_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero_nonneg lam hlam)), Matrix.one_mulVec] }

theorem linearEquivNonneg_coe (lam : ℝ) (hlam : 0 ≤ lam) :
    (linearEquivNonneg lam hlam).toContinuousLinearMap = linearCLM lam := rfl

theorem continuous_linearCLM : Continuous linearCLM := by
  let L : (Matrix (Fin 2) (Fin 2) ℝ) →ₗ[ℝ] (Coeff →L[ℝ] Coeff) :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Coeff) (F' := Coeff)).toLinearMap.comp
      Matrix.toLin'.toLinearMap
  have hM : Continuous linearMatrix := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;>
      dsimp [linearMatrix, angularSlope, pressureSlope]
    · exact continuous_moment.comp (continuous_const.sub continuous_id)
    · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub
        continuous_id))).mul
        (continuous_moment.comp (continuous_const.sub continuous_id))
    · exact continuous_const.mul
        (continuous_moment.comp (continuous_const.sub (continuous_const.mul continuous_id)))
    · exact continuous_const.mul
        ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub
            (continuous_const.mul continuous_id)))).mul
          (continuous_moment.comp (continuous_const.sub (continuous_const.mul continuous_id))))
  exact L.continuous_of_finiteDimensional.comp hM

/-- Quadratic coefficients bilin, bundling `toFun`, `map_add`, `map_smul`, `map_add` and the
required compatibility proofs. -/
def quadraticCoefficientsBilin (q : Coeff) : Coeff →ₗ[ℝ] Coeff →ₗ[ℝ] Coeff where
  toFun c :=
    { toFun := fun d => ![0, q 0 * c 0 * d 0 + q 1 * c 1 * d 1]
      map_add' := fun d e => by
        ext i
        fin_cases i <;> simp [Pi.add_apply]
        ring
      map_smul' := fun r d => by
        ext i
        fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
        ring }
  map_add' c d := by
    ext e i
    fin_cases i <;> simp [Pi.add_apply]
    ring
  map_smul' r c := by
    ext e i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
    ring

/-- Quadratic coefficient map, bundling `toFun`, `map_add`, `map_smul`. -/
def quadraticCoefficientMap : Coeff →ₗ[ℝ] (Coeff →L[ℝ] Coeff →L[ℝ] Coeff) where
  toFun q := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Coeff) (F' := Coeff)).toLinearMap.comp
      (quadraticCoefficientsBilin q))
  map_add' q p := by
    apply ContinuousLinearMap.ext
    intro c
    apply ContinuousLinearMap.ext
    intro d
    ext i
    fin_cases i <;> simp [quadraticCoefficientsBilin, Pi.add_apply]
    ring
  map_smul' r q := by
    apply ContinuousLinearMap.ext
    intro c
    apply ContinuousLinearMap.ext
    intro d
    ext i
    fin_cases i <;> simp [quadraticCoefficientsBilin, Pi.smul_apply, smul_eq_mul]
    ring

theorem continuous_quadraticCLM : Continuous quadraticCLM := by
  have hL : Continuous (quadraticCoefficientMap : Coeff → (Coeff →L[ℝ] Coeff →L[ℝ] Coeff)) :=
    LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ) (E := Coeff)
      (F' := Coeff →L[ℝ] Coeff →L[ℝ] Coeff) quadraticCoefficientMap
  have heq : quadraticCLM = fun lam => quadraticCoefficientMap (fun j => quadraticMoment lam j) :=
      rfl
  rw [heq]
  exact hL.comp (continuous_pi continuous_quadraticMoment)

/-- Both operator bounds follow from the compact parameter interval and the
proved determinant, including its nonzero value at zero. -/
theorem uniform_operator_bounds :
    ∃ β K : ℝ, 0 < β ∧ 0 < K ∧ ∀ lam ∈ lambdaRange,
      ‖(linearCLM lam).inverse‖ ≤ β ∧ ‖quadraticCLM lam‖ ≤ K := by
  apply SmoothMomentRepair.compact_inverse_quadratic_bounds lambdaRange isCompact_Icc
    linearCLM quadraticCLM continuous_linearCLM.continuousOn continuous_quadraticCLM.continuousOn
  intro lam hlam
  exact ⟨linearEquivNonneg lam hlam.1, linearEquivNonneg_coe lam hlam.1⟩

theorem uniform_small_solutions :
    ∃ β ε : ℝ, 0 < β ∧ 0 < ε ∧ ∀ lam ∈ lambdaRange,
      ∀ d : Coeff, ‖d‖ ≤ ε → ∃! c : Coeff,
        ‖c‖ ≤ 2 * β * ‖d‖ ∧ linearCLM lam c + quadraticCLM lam c c = d := by
  apply SmoothMomentRepair.compact_uniform_small_correction lambdaRange isCompact_Icc
    linearCLM quadraticCLM continuous_linearCLM.continuousOn continuous_quadraticCLM.continuousOn
  intro lam hlam
  exact ⟨linearEquivNonneg lam hlam.1, linearEquivNonneg_coe lam hlam.1⟩

section SmoothUniformInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Quadratic map, given by `B c + A c c`. -/
def quadraticMap (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) (c : E) : E :=
  B c + A c c

/-- Tangent, given by `B.toContinuousLinearMap + A c + A.flip c`. -/
def tangent (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) (c : E) : E →L[ℝ] E :=
  B.toContinuousLinearMap + A c + A.flip c

theorem quadraticMap_contDiff (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ∞ (quadraticMap B A) :=
  B.contDiff.add (A.contDiff.clm_apply contDiff_id)

theorem quadraticMap_hasFDerivAt (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E) (c : E) :
    HasFDerivAt (quadraticMap B A) (tangent B A c) c := by
  convert! B.hasFDerivAt.add (A.hasFDerivAt.clm_apply (hasFDerivAt_id c)) using 1
  apply ContinuousLinearMap.ext
  intro x
  change B x + A c x + A x c = B x + (A c x + A x c)
  abel

theorem tangent_lower_bound (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E)
    (β K r : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hinv : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖) (hA : ‖A‖ ≤ K)
    (hsmall : 4 * β * K * r ≤ 1) (c : E) (hc : ‖c‖ ≤ r) (x : E) :
    ‖x‖ ≤ 2 * β * ‖tangent B A c x‖ := by
  have hrem : ‖A c x + A x c‖ ≤ (2 * K * r) * ‖x‖ := by
    calc
      _ ≤ ‖A c x‖ + ‖A x c‖ := norm_add_le _ _
      _ ≤ (K * r) * ‖x‖ + (K * ‖x‖) * r := by
        apply add_le_add
        · exact (A.le_opNorm₂ c x).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul hA hc (norm_nonneg c) hK) (norm_nonneg x))
        · exact (A.le_opNorm₂ x c).trans
            (mul_le_mul (mul_le_mul_of_nonneg_right hA (norm_nonneg x)) hc
              (norm_nonneg c) (mul_nonneg hK (norm_nonneg x)))
      _ = _ := by ring
  have hid : B x = tangent B A c x - (A c x + A x c) := by
    change B x = B x + A c x + A x c - (A c x + A x c)
    abel
  have hn : ‖x‖ ≤ β * ‖tangent B A c x‖ + (1 / 2 : ℝ) * ‖x‖ := by
    calc
      ‖x‖ = ‖B.symm (B x)‖ := by rw [B.symm_apply_apply]
      _ ≤ β * ‖B x‖ := hinv _
      _ = β * ‖tangent B A c x - (A c x + A x c)‖ := by rw [hid]
      _ ≤ β * (‖tangent B A c x‖ + ‖A c x + A x c‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) hβ
      _ ≤ β * (‖tangent B A c x‖ + (2 * K * r) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hrem _) hβ
      _ ≤ β * ‖tangent B A c x‖ + (1 / 2 : ℝ) * ‖x‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg x)]
  linarith

theorem tangent_invertible [FiniteDimensional ℝ E]
    (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E)
    (β K r : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hinv : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖) (hA : ‖A‖ ≤ K)
    (hsmall : 4 * β * K * r ≤ 1) (c : E) (hc : ‖c‖ ≤ r) :
    (tangent B A c).IsInvertible := by
  have hi : Injective (tangent B A c) := by
    intro x y hxy
    have hz : tangent B A c (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hnorm := tangent_lower_bound B A β K r hβ hK hinv hA hsmall c hc (x - y)
    rw [hz, norm_zero, mul_zero] at hnorm
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))
  let e : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (tangent B A c).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

theorem quadratic_solution_distance (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E)
    (β K r : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (hinv : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖) (hA : ‖A‖ ≤ K)
    (hsmall : 4 * β * K * r ≤ 1) (c e d f : E)
    (hc : ‖c‖ ≤ r) (he : ‖e‖ ≤ r)
    (hceq : quadraticMap B A c = d) (heeq : quadraticMap B A e = f) :
    ‖c - e‖ ≤ 2 * β * ‖d - f‖ := by
  have hr : 0 ≤ r := (norm_nonneg c).trans hc
  have hrem : ‖A c c - A e e‖ ≤ (2 * K * r) * ‖c - e‖ := by
    apply (SmoothMomentRepair.quadratic_sub_le A c e).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖A‖ * (‖c‖ + ‖e‖) ≤ K * (2 * r) :=
        mul_le_mul hA (by linarith) (by positivity) hK
      _ = _ := by ring
  have hid : B (c - e) = (d - f) - (A c c - A e e) := by
    rw [map_sub, ← hceq, ← heeq]
    unfold quadraticMap
    abel
  have hn : ‖c - e‖ ≤ β * ‖d - f‖ + (1 / 2 : ℝ) * ‖c - e‖ := by
    calc
      ‖c - e‖ = ‖B.symm (B (c - e))‖ := by rw [B.symm_apply_apply]
      _ ≤ β * ‖B (c - e)‖ := hinv _
      _ = β * ‖(d - f) - (A c c - A e e)‖ := by rw [hid]
      _ ≤ β * (‖d - f‖ + ‖A c c - A e e‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) hβ
      _ ≤ β * (‖d - f‖ + (2 * K * r) * ‖c - e‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hrem _) hβ
      _ ≤ β * ‖d - f‖ + (1 / 2 : ℝ) * ‖c - e‖ := by
        nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg (c - e))]
  linarith

/-- Contraction uniqueness patches the local smooth inverses throughout one
uniform debt ball. The resulting smoothness radius is quantitative. -/
theorem exists_smooth_solver_on_ball [FiniteDimensional ℝ E] [CompleteSpace E]
    (B : E ≃L[ℝ] E) (A : E →L[ℝ] E →L[ℝ] E)
    (β K r : ℝ) (hβ : 0 < β) (hK : 0 ≤ K) (hr : 0 < r)
    (hinv : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖) (hA : ‖A‖ ≤ K)
    (hsmall : 4 * β * K * r ≤ 1) :
    ∃ g : E → E, ContDiffOn ℝ ∞ g (Metric.ball 0 (r / (4 * β))) ∧
      (∀ d ∈ Metric.ball 0 (r / (4 * β)), quadraticMap B A (g d) = d ∧ ‖g d‖ ≤ 2 * β * ‖d‖) ∧
      ∀ d ∈ Metric.ball 0 (r / (4 * β)), ∀ e ∈ Metric.ball 0 (r / (4 * β)),
        ‖g d - g e‖ ≤ 2 * β * ‖d - e‖ := by
  classical
  let ε : ℝ := r / (4 * β)
  have hε : 0 < ε := div_pos hr (by positivity)
  have hεeq : 2 * β * ε = r / 2 := by dsimp [ε]; field_simp ; ring
  have hex : ∀ d : Metric.ball (0 : E) ε, ∃! c : E,
      ‖c‖ ≤ r ∧ quadraticMap B A c = d := by
    intro d
    apply MomentRepair.exists_unique_small_correction B (fun c => A c c) d β K r hβ.le hK hr.le hinv
    · intro c _
      exact (SmoothMomentRepair.quadratic_norm_le A c).trans
        (mul_le_mul_of_nonneg_right hA (sq_nonneg _))
    · intro c _ e _
      exact (SmoothMomentRepair.quadratic_sub_le A c e).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hA (add_nonneg (norm_nonneg _) (norm_nonneg _)))
          (norm_nonneg _))
    · exact hsmall
    · have hd : ‖(d : E)‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using d.property
      have hb := mul_lt_mul_of_pos_left hd (show 0 < 2 * β by positivity)
      linarith
  choose f hf using hex
  let g : E → E := fun d => if hd : d ∈ Metric.ball (0 : E) ε then f ⟨d, hd⟩ else 0
  have hspec : ∀ d (hd : d ∈ Metric.ball (0 : E) ε),
      (‖g d‖ ≤ r ∧ quadraticMap B A (g d) = d) ∧
      ∀ c, (‖c‖ ≤ r ∧ quadraticMap B A c = d) → c = g d := by
    intro d hd
    simpa only [g, dite_eq_left hd] using hf ⟨d, hd⟩
  have hbound : ∀ d ∈ Metric.ball (0 : E) ε, ‖g d‖ ≤ 2 * β * ‖d‖ := by
    intro d hd
    have hz : quadraticMap B A 0 = 0 := by simp [quadraticMap]
    simpa only [sub_zero] using quadratic_solution_distance B A β K r hβ.le hK hinv hA hsmall
      (g d) 0 d 0 (hspec d hd).1.1 (by simpa using hr.le) (hspec d hd).1.2 hz
  have hinterior : ∀ d ∈ Metric.ball (0 : E) ε, ‖g d‖ < r := by
    intro d hd
    have hd' : ‖d‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using hd
    have ht := mul_lt_mul_of_pos_left hd' (show 0 < 2 * β by positivity)
    linarith [hbound d hd]
  refine ⟨g, ?_, fun d hd => ⟨(hspec d hd).1.2, hbound d hd⟩, ?_⟩
  · intro d hd
    obtain ⟨D, hD⟩ := tangent_invertible B A β K r hβ.le hK hinv hA hsmall
      (g d) (hspec d hd).1.1
    have hderiv : HasFDerivAt (quadraticMap B A) D.toContinuousLinearMap (g d) := by
      rw [hD]
      exact quadraticMap_hasFDerivAt B A (g d)
    have hq : ContDiffAt ℝ ∞ (quadraticMap B A) (g d) :=
      (quadraticMap_contDiff B A).contDiffAt
    let inv : E → E := hq.localInverse hderiv (by simp)
    have hqd : quadraticMap B A (g d) = d := (hspec d hd).1.2
    have hinvsm : ContDiffAt ℝ ∞ inv d := by
      simpa only [hqd] using hq.to_localInverse hderiv (by simp)
    have hinv0 : inv d = g d := by
      simpa only [hqd] using hq.localInverse_apply_image hderiv (by simp)
    have hinvr : ∀ᶠ x in 𝓝 d, ‖inv x‖ < r :=
      hinvsm.continuousAt.norm.eventually
        (eventually_lt_nhds (by simpa only [hinv0] using hinterior d hd))
    have hinveq : ∀ᶠ x in 𝓝 d, quadraticMap B A (inv x) = x := by
      have h := HasStrictFDerivAt.eventually_right_inverse (f' := D)
        (hq.hasStrictFDerivAt' hderiv (by simp))
      change ∀ᶠ x in 𝓝 (quadraticMap B A (g d)), quadraticMap B A (inv x) = x at h
      simpa only [hqd] using h
    have hgeq : g =ᶠ[𝓝 d] inv := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hd, hinvr, hinveq] with x hx hxr hxe
      exact ((hspec x hx).2 (inv x) ⟨hxr.le, hxe⟩).symm
    exact (hinvsm.congr_of_eventuallyEq hgeq).contDiffWithinAt
  · intro d hd e he
    exact quadratic_solution_distance B A β K r hβ.le hK hinv hA hsmall
      (g d) (g e) d e (hspec d hd).1.1 (hspec e he).1.1 (hspec d hd).1.2 (hspec e he).1.2

end SmoothUniformInverse

theorem actual_moment_map (lam : ℝ) (c : Coeff) :
    linearCLM lam c + quadraticCLM lam c c =
      ![∫ y, Real.exp (angularSlope lam * y) * relative c y,
        ∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative c y) ^ 2 - 1)] := by
  rw [quadraticCLM_apply, relative_moment, pressure_change_moment]
  ext i
  fin_cases i <;> simp [linearCLM, linearMatrix, dotProduct, Fin.sum_univ_two]
  ring

/-- A single radius and a single bound work for the actual two-bump system for
every `lam ∈ [0,1/10]`. Smoothness and the derivative bound concern the debt
variable; no smoothness of an arbitrary choice in `lam` is asserted. -/
theorem uniform_reset_branch :
    ∃ ε L : ℝ, 0 < ε ∧ 0 < L ∧ ∀ lam ∈ lambdaRange,
      ∃ c : ℝ → Coeff, ContDiffOn ℝ ∞ c (Ioo (-ε) ε) ∧ c 0 = 0 ∧
        ∀ δ ∈ Ioo (-ε) ε,
          (∫ y, Real.exp (angularSlope lam * y) * relative (c δ) y) = δ ∧
          (∫ y, Real.exp (pressureSlope lam * y) * ((1 + relative (c δ) y) ^ 2 - 1)) = 0 ∧
          ‖c δ‖ ≤ L * |δ| ∧ ‖deriv c δ‖ ≤ L ∧ ∀ y,
            |relative (c δ) y| ≤ L * |δ| ∧ |deriv (relative (c δ)) y| ≤ L * |δ| := by
  obtain ⟨β, K, hβ, hK, hcoeff⟩ := uniform_operator_bounds
  obtain ⟨D, hD, hjet⟩ := relative_first_jet_bound
  let r : ℝ := 1 / (4 * β * K)
  let ε : ℝ := r / (4 * β)
  let L : ℝ := (1 + D) * (2 * β)
  have hr : 0 < r := by dsimp [r]; positivity
  have hε : 0 < ε := div_pos hr (by positivity)
  have hL : 0 < L := mul_pos (by linarith) (by positivity)
  have hLbase : 2 * β ≤ L := by dsimp [L]; nlinarith
  have hLD : D * (2 * β) ≤ L := by dsimp [L]; nlinarith
  have hsmall : 4 * β * K * r ≤ 1 := by dsimp [r]; field_simp ; rfl
  refine ⟨ε, L, hε, hL, ?_⟩
  intro lam hlam
  let B := linearEquivNonneg lam hlam.1
  have hBinv : ‖B.symm.toContinuousLinearMap‖ ≤ β := by
    have h := (hcoeff lam hlam).1
    rw [← linearEquivNonneg_coe lam hlam.1, ContinuousLinearMap.inverse_equiv] at h
    exact h
  have hinv : ∀ x, ‖B.symm x‖ ≤ β * ‖x‖ := fun x =>
    (B.symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hBinv (norm_nonneg x))
  obtain ⟨g, hg, hgeq, hglip⟩ := exists_smooth_solver_on_ball B (quadraticCLM lam)
    β K r hβ hK.le hr hinv (hcoeff lam hlam).2 hsmall
  let c : ℝ → Coeff := fun δ => g (debt δ)
  have hd : ∀ δ ∈ Ioo (-ε) ε, debt δ ∈ Metric.ball (0 : Coeff) ε := by
    intro δ hδ
    simpa only [Metric.mem_ball, dist_zero_right] using (debt_norm_le δ).trans_lt (abs_lt.mpr hδ)
  have hc : ContDiffOn ℝ ∞ c (Ioo (-ε) ε) :=
    hg.comp debt_contDiff.contDiffOn hd
  have hc_norm : ∀ δ ∈ Ioo (-ε) ε, ‖c δ‖ ≤ (2 * β) * |δ| := by
    intro δ hδ
    exact ((hgeq (debt δ) (hd δ hδ)).2).trans
      (mul_le_mul_of_nonneg_left (debt_norm_le δ) (by positivity))
  have hc_zero : c 0 = 0 := by
    have h := hc_norm 0 (by constructor <;> linarith)
    simp only [abs_zero, mul_zero, norm_le_zero_iff] at h
    exact h
  have hclip : ∀ δ ∈ Ioo (-ε) ε, ∀ η ∈ Ioo (-ε) ε,
      ‖c δ - c η‖ ≤ (2 * β) * |δ - η| := by
    intro δ hδ η hη
    have hs : debt δ - debt η = debt (δ - η) := by ext i; fin_cases i <;> simp [debt]
    apply (hglip (debt δ) (hd δ hδ) (debt η) (hd η hη)).trans
    rw [hs]
    exact mul_le_mul_of_nonneg_left (debt_norm_le _) (by positivity)
  refine ⟨c, hc, hc_zero, ?_⟩
  intro δ hδ
  have heq := (hgeq (debt δ) (hd δ hδ)).1
  change linearCLM lam (c δ) + quadraticCLM lam (c δ) (c δ) = debt δ at heq
  rw [actual_moment_map] at heq
  refine ⟨congrFun heq 0, congrFun heq 1,
    (hc_norm δ hδ).trans (mul_le_mul_of_nonneg_right hLbase (abs_nonneg δ)), ?_, ?_⟩
  · apply le_trans _ hLbase
    apply norm_deriv_le_of_lip' (show 0 ≤ 2 * β by positivity)
    filter_upwards [isOpen_Ioo.mem_nhds hδ] with η hη
    simpa only [Real.norm_eq_abs] using hclip η hη δ hδ
  · intro y
    have hb : D * ‖c δ‖ ≤ L * |δ| :=
      (mul_le_mul_of_nonneg_left (hc_norm δ hδ) hD.le).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hLD (abs_nonneg δ))
    exact ⟨(hjet (c δ) y).1.trans hb, (hjet (c δ) y).2.trans hb⟩

section ActualHistory

open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail

/-- The factor `sqrt 2` cancels in every angular-history ratio. -/
def baseWeight (d : TailData) (y : ℝ) : ℝ :=
  Real.exp (3 * y / 2) * radialAmplitude d.core.P d.core.dropLength d.core.lam y

/-- Base history, given by `(5 / 8) * d.core.P + OutgoingSchedule.primitive (baseWeight d) y`. -/
def baseHistory (d : TailData) (y : ℝ) : ℝ :=
  (5 / 8) * d.core.P + OutgoingSchedule.primitive (baseWeight d) y

theorem baseWeight_contDiff (d : TailData) : ContDiff ℝ ∞ (baseWeight d) :=
  ((contDiff_const.mul contDiff_id).div_const 2).exp.mul (radialAmplitude_contDiff _ _ _)

theorem baseWeight_pos (d : TailData) (y : ℝ) : 0 < baseWeight d y :=
  mul_pos (Real.exp_pos _) (mul_pos d.core.P_pos (Real.exp_pos _))

theorem baseWeight_zero (d : TailData) : baseWeight d 0 = d.core.P := by
  simp [baseWeight, radialAmplitude, logAmplitude, OutgoingSchedule.primitive]

theorem core_slope_lower (d : TailData) (y : ℝ) :
    -d.core.lam ≤ slope d.core.dropLength d.core.lam y := by
  unfold OutgoingSchedule.slope
  have h0 := mul_nonneg (show (0 : ℝ) ≤ 3 / 5 by norm_num)
    (sub_nonneg.mpr (sigma_le_one y))
  have h1 := mul_nonneg d.core.lam_pos.le
    (sub_nonneg.mpr (sigma_le_one (y - (d.core.dropLength + 1))))
  linarith

theorem baseWeight_hasDerivAt (d : TailData) (y : ℝ) :
    HasDerivAt (baseWeight d)
      (baseWeight d y * (1 + slope d.core.dropLength d.core.lam y)) y := by
  have he := (((hasDerivAt_id y).const_mul (3 : ℝ)).div_const 2).exp
  convert! he.mul (radialAmplitude_hasDerivAt d.core.P d.core.dropLength d.core.lam y) using 1
  dsimp [baseWeight]
  ring

theorem baseHistory_hasDerivAt (d : TailData) (y : ℝ) :
    HasDerivAt (baseHistory d) (baseWeight d y) y :=
  (OutgoingSchedule.primitive_hasDerivAt (baseWeight_contDiff d).continuous y).const_add _

theorem baseHistory_nonneg (d : TailData) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ baseHistory d y := by
  apply add_nonneg (mul_nonneg (by norm_num) d.core.P_pos.le)
  exact intervalIntegral.integral_nonneg hy (fun t _ => (baseWeight_pos d t).le)

/-- The actual unflattened angular-history ratio is uniformly bounded;
the ideal incoming prefix is included explicitly. -/
theorem baseHistory_le (d : TailData) {y : ℝ} (hy : 0 ≤ y) :
    baseHistory d y ≤ baseWeight d y / (1 - d.core.lam) := by
  have hk : 0 < 1 - d.core.lam := by linarith [d.core.lam_lt]
  let f : ℝ → ℝ := fun y => baseWeight d y / (1 - d.core.lam) - baseHistory d y
  have hf : ∀ y, HasDerivAt f
      (baseWeight d y * (1 + slope d.core.dropLength d.core.lam y) / (1 - d.core.lam) -
        baseWeight d y) y := fun y =>
    ((baseWeight_hasDerivAt d y).div_const _).sub (baseHistory_hasDerivAt d y)
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg (fun y => (hf y).differentiableAt)
    intro y
    rw [(hf y).deriv]
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hk).mpr
    exact mul_le_mul_of_nonneg_left (by linarith [core_slope_lower d y]) (baseWeight_pos d y).le
  have hzero : 0 ≤ f 0 := by
    change 0 ≤ baseWeight d 0 / (1 - d.core.lam) - baseHistory d 0
    rw [baseWeight_zero]
    simp only [baseHistory, OutgoingSchedule.primitive, intervalIntegral.integral_same, add_zero]
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hk).mpr
    nlinarith [d.core.P_pos, d.core.lam_pos]
  have h := hmono hy
  dsimp [f] at h hzero
  linarith

/-- Flatten shape, constructed using `Real.exp`. -/
def flattenShape (d : TailData) (y eta : ℝ) : ℝ :=
  Real.exp ((sigma ((y - d.core.endpoint) / flattenLength) - 1) * logShape eta -
    sigma ((y - d.core.endpoint) / flattenLength) * Real.log 2)

theorem shape_eq_exp (eta : ℝ) : shape eta = Real.exp (-logShape eta) := by
  rw [Real.exp_neg, logShape, Real.exp_log (by positivity)]
  rfl

theorem flattened_eq (d : TailData) (y eta : ℝ) :
    flattened d (y, eta) =
      radialAmplitude d.core.P d.core.dropLength d.core.lam y * flattenShape d y eta := by
  unfold flattened angular flattenFactor flattenShape
  rw [shape_eq_exp]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem flattenShape_pos (d : TailData) (y eta : ℝ) : 0 < flattenShape d y eta := Real.exp_pos _

theorem flattenShape_le_one (d : TailData) (y eta : ℝ) : flattenShape d y eta ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hl : 0 ≤ logShape eta := Real.log_nonneg (by nlinarith [sq_nonneg eta])
  have ha := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (sigma_le_one ((y - d.core.endpoint) / flattenLength))) hl
  have hb := mul_nonneg (sigma_nonneg ((y - d.core.endpoint) / flattenLength))
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  linarith

/-- Flat weight, given by `Real.exp (3 * y / 2) * flattened d (y, eta)`. -/
def flatWeight (d : TailData) (eta y : ℝ) : ℝ :=
  Real.exp (3 * y / 2) * flattened d (y, eta)

/-- Flat history, given by `(5 / 8) * d.core.P * shape eta + OutgoingSchedule.primitive
(flatWeight d eta) y`. -/
def flatHistory (d : TailData) (eta y : ℝ) : ℝ :=
  (5 / 8) * d.core.P * shape eta + OutgoingSchedule.primitive (flatWeight d eta) y

theorem flatWeight_contDiff (d : TailData) (eta : ℝ) : ContDiff ℝ ∞ (flatWeight d eta) :=
  ((contDiff_const.mul contDiff_id).div_const 2).exp.mul
    ((flattened_contDiff d).comp (contDiff_id.prodMk contDiff_const))

theorem flatWeight_pos (d : TailData) (eta y : ℝ) : 0 < flatWeight d eta y :=
  mul_pos (Real.exp_pos _) (flattened_pos d _)

theorem flatWeight_le_base (d : TailData) (eta y : ℝ) : flatWeight d eta y ≤ baseWeight d y := by
  have hf : flatWeight d eta y = baseWeight d y * flattenShape d y eta := by
    unfold flatWeight baseWeight
    rw [flattened_eq]
    ring
  rw [hf]
  exact mul_le_of_le_one_right (baseWeight_pos d y).le (flattenShape_le_one d y eta)

theorem flatHistory_bounds (d : TailData) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ flatHistory d eta y ∧ flatHistory d eta y ≤ baseHistory d y := by
  constructor
  · apply add_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) d.core.P_pos.le) (shape_pos eta).le
    · exact intervalIntegral.integral_nonneg hy (fun t _ => (flatWeight_pos d eta t).le)
  · apply add_le_add
    · have hs : shape eta ≤ 1 := by
        unfold shape
        apply inv_le_one_of_one_le₀
        nlinarith [sq_nonneg eta]
      exact mul_le_of_le_one_right (mul_nonneg (by norm_num) d.core.P_pos.le) hs
    · exact intervalIntegral.integral_mono hy ((flatWeight_contDiff d
        eta).continuous.intervalIntegrable 0 y)
        ((baseWeight_contDiff d).continuous.intervalIntegrable 0 y) (flatWeight_le_base d eta)

theorem compact_integral_contDiff (F : ℝ → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p => ∫ t in a..b, F p t) := by
  apply contDiffOn_univ.mp
  apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet isOpen_univ hab
  · intro t _
    exact (hF.comp (contDiff_id.prodMk contDiff_const)).contDiffOn
  · intro k
    rintro ⟨p, t⟩ _
    have hf : ContDiffAt ℝ ∞ (Function.uncurry (fun t p => F p t)) (t, p) :=
      (hF.comp (contDiff_snd.prodMk contDiff_fst)).contDiffAt
    have hj := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv (fun t p => F p t) k t p hf
    exact (hj.comp (p, t) (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt.continuousWithinAt

theorem flatWeight_joint_contDiff (d : TailData) :
    ContDiff ℝ ∞ (Function.uncurry (flatWeight d)) :=
  ((contDiff_const.mul contDiff_snd).div_const 2).exp.mul
    ((flattened_contDiff d).comp (contDiff_snd.prodMk contDiff_fst))

theorem flatHistory_contDiff (d : TailData) {y : ℝ} (hy : 0 ≤ y) :
    ContDiff ℝ ∞ (fun eta => flatHistory d eta y) :=
  (contDiff_const.mul shape_contDiff).add
    (compact_integral_contDiff (flatWeight d) 0 y hy (flatWeight_joint_contDiff d))

/-- Eta rate, given by `(sigma ((y - d.core.endpoint) / flattenLength) - 1) * (2 * eta / (1 +
eta ^ 2))`. -/
def etaRate (d : TailData) (eta y : ℝ) : ℝ :=
  (sigma ((y - d.core.endpoint) / flattenLength) - 1) * (2 * eta / (1 + eta ^ 2))

theorem logShape_hasDerivAt (eta : ℝ) :
    HasDerivAt logShape (2 * eta / (1 + eta ^ 2)) eta := by
  convert! (((hasDerivAt_id eta).pow 2).const_add 1).log (by positivity : 1 + eta ^ 2 ≠ 0) using 1
  simp []

theorem logShape_deriv_bound (eta : ℝ) : |2 * eta / (1 + eta ^ 2)| ≤ 1 := by
  rw [abs_div, abs_mul, abs_of_pos (by
      positivity : 0 < (2 : ℝ)), abs_of_pos (by positivity : 0 < 1 + eta ^ 2)]
  apply (div_le_one (by positivity : 0 < 1 + eta ^ 2)).mpr
  nlinarith [sq_nonneg (|eta| - 1), sq_abs eta]

theorem etaRate_bound (d : TailData) (eta y : ℝ) : |etaRate d eta y| ≤ 1 := by
  unfold etaRate
  rw [abs_mul]
  have hs : |sigma ((y - d.core.endpoint) / flattenLength) - 1| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (sigma_le_one _))]
    linarith [sigma_nonneg ((y - d.core.endpoint) / flattenLength)]
  exact (mul_le_mul hs (logShape_deriv_bound eta) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem flatWeight_eq (d : TailData) (eta y : ℝ) :
    flatWeight d eta y = baseWeight d y * flattenShape d y eta := by
  unfold flatWeight baseWeight
  rw [flattened_eq]
  ring

theorem flatWeight_eta_hasDerivAt (d : TailData) (eta y : ℝ) :
    HasDerivAt (fun eta => flatWeight d eta y) (flatWeight d eta y * etaRate d eta y) eta := by
  have h := (((logShape_hasDerivAt eta).const_mul
    (sigma ((y - d.core.endpoint) / flattenLength) - 1)).sub_const
      (sigma ((y - d.core.endpoint) / flattenLength) * Real.log 2)).exp
  convert! h.const_mul (baseWeight d y) using 1
  · funext p
    exact flatWeight_eq d p y
  · rw [flatWeight_eq]
    dsimp [flattenShape, etaRate]
    ring

theorem flatWeight_eta_bound (d : TailData) (eta y : ℝ) :
    |flatWeight d eta y * etaRate d eta y| ≤ baseWeight d y := by
  rw [abs_mul, abs_of_pos (flatWeight_pos d eta y)]
  exact (mul_le_of_le_one_right (flatWeight_pos d eta y).le (etaRate_bound d eta y)).trans
    (flatWeight_le_base d eta y)

theorem etaRate_continuous (d : TailData) (eta : ℝ) : Continuous (etaRate d eta) :=
  (sigma_contDiff.continuous.comp ((continuous_id.sub continuous_const).div_const _)
    |>.sub continuous_const).mul continuous_const

theorem shape_hasDerivAt (eta : ℝ) :
    HasDerivAt shape (shape eta * (-(2 * eta / (1 + eta ^ 2)))) eta := by
  have h := (logShape_hasDerivAt eta).fun_neg.exp
  convert! h using 1
  · funext p
    exact shape_eq_exp p
  · rw [← shape_eq_exp]

theorem shape_le_one (eta : ℝ) : shape eta ≤ 1 := by
  unfold shape
  apply inv_le_one_of_one_le₀
  nlinarith [sq_nonneg eta]

theorem flatHistory_hasDerivAt (d : TailData) (eta y : ℝ) :
    HasDerivAt (fun eta => flatHistory d eta y)
      ((5 / 8) * d.core.P * (shape eta * (-(2 * eta / (1 + eta ^ 2)))) +
        ∫ t in (0 : ℝ)..y, flatWeight d eta t * etaRate d eta t) eta := by
  have hint := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := flatWeight d) (F' := fun eta t => flatWeight d eta t * etaRate d eta t)
    (bound := baseWeight d) (s := Metric.ball eta 1) (x₀ := eta) (a := 0) (b := y)
    (Metric.ball_mem_nhds eta (by norm_num))
    (Filter.Eventually.of_forall fun p => (flatWeight_contDiff d p).continuous.aestronglyMeasurable)
    ((flatWeight_contDiff d eta).continuous.intervalIntegrable 0 y)
    (((flatWeight_contDiff d eta).continuous.mul (etaRate_continuous d eta)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t _ p _ => by
      simpa only [Real.norm_eq_abs] using flatWeight_eta_bound d p t)
    ((baseWeight_contDiff d).continuous.intervalIntegrable 0 y)
    (Filter.Eventually.of_forall fun t _ p _ => flatWeight_eta_hasDerivAt d p t)
  exact ((shape_hasDerivAt eta).const_mul ((5 / 8) * d.core.P)).fun_add hint.2

theorem flatHistory_deriv_bound (d : TailData) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |deriv (fun eta => flatHistory d eta y) eta| ≤ baseHistory d y := by
  rw [(flatHistory_hasDerivAt d eta y).deriv]
  have hpre : |(5 / 8 : ℝ) * d.core.P * (shape eta * (-(2 * eta / (1 + eta ^ 2))))| ≤
      (5 / 8 : ℝ) * d.core.P := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) d.core.P_pos.le), abs_mul,
      abs_of_pos (shape_pos eta), abs_neg]
    have hprod := mul_le_mul (shape_le_one eta) (logShape_deriv_bound eta) (abs_nonneg _)
        zero_le_one
    simpa using mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) d.core.P_pos.le)
  have hint : |∫ t in (0 : ℝ)..y, flatWeight d eta t * etaRate d eta t| ≤
      ∫ t in (0 : ℝ)..y, baseWeight d t := by
    apply (intervalIntegral.abs_integral_le_integral_abs hy).trans
    apply intervalIntegral.integral_mono hy
      ((((flatWeight_contDiff d eta).continuous.mul (etaRate_continuous d
          eta)).abs).intervalIntegrable 0 y)
      ((baseWeight_contDiff d).continuous.intervalIntegrable 0 y)
    exact flatWeight_eta_bound d eta
  exact (abs_add_le _ _).trans (add_le_add hpre hint)

theorem flattenEnd_pos (d : TailData) : 0 < d.flattenEnd := by
  exact (d.core.holdStart_pos.trans_le (coreEndpoint_ge_hold d)).trans (flattenEnd_gt_core d)

theorem flatWeight_uniform (d : TailData) (eta : ℝ) {y : ℝ} (hy : d.flattenEnd ≤ y) :
    flatWeight d eta y = baseWeight d y / 2 := by
  unfold flatWeight baseWeight
  rw [flattened_uniform d eta hy]
  ring

theorem baseWeight_hold (d : TailData) {a y : ℝ}
    (ha : d.core.holdStart ≤ a) (hay : a ≤ y) :
    baseWeight d y = baseWeight d a * Real.exp ((1 - d.core.lam) * (y - a)) := by
  have h := radialAmplitude_hold (P := d.core.P) (lam := d.core.lam)
    d.core.dropLength_pos.le ha hay
  unfold baseWeight
  rw [h]
  calc
    _ = radialAmplitude d.core.P d.core.dropLength d.core.lam a *
        (Real.exp (3 * y / 2) * Real.exp (-(1 / 2 + d.core.lam) * (y - a))) := by ring
    _ = radialAmplitude d.core.P d.core.dropLength d.core.lam a *
        (Real.exp (3 * a / 2) * Real.exp ((1 - d.core.lam) * (y - a))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ = _ := by ring

theorem flatHistory_increment (d : TailData) (eta : ℝ) {y : ℝ} (hy : d.flattenEnd ≤ y) :
    flatHistory d eta y = flatHistory d eta d.flattenEnd +
      (baseWeight d y - baseWeight d d.flattenEnd) / (2 * (1 - d.core.lam)) := by
  have hk : 1 - d.core.lam ≠ 0 := by linarith [d.core.lam_lt]
  have hderiv : ∀ t ∈ uIcc d.flattenEnd y,
      HasDerivAt (fun t => baseWeight d t / (2 * (1 - d.core.lam))) (flatWeight d eta t) t := by
    intro t ht
    have htF : d.flattenEnd ≤ t := (uIcc_of_le hy ▸ ht).1
    have htH : d.core.holdStart ≤ t :=
      (coreEndpoint_ge_hold d).trans ((flattenEnd_gt_core d).le.trans htF)
    rw [flatWeight_uniform d eta htF]
    convert! (baseWeight_hasDerivAt d t).div_const (2 * (1 - d.core.lam)) using 1
    rw [slope_hold d.core.dropLength_pos.le htH]
    field_simp; ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((flatWeight_contDiff d eta).continuous.intervalIntegrable d.flattenEnd y)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((flatWeight_contDiff d eta).continuous.intervalIntegrable 0 d.flattenEnd)
    ((flatWeight_contDiff d eta).continuous.intervalIntegrable d.flattenEnd y)
  unfold flatHistory OutgoingSchedule.primitive
  rw [← hadd, hi]
  ring

/-- Flat ratio, given by `flatHistory d eta d.flattenEnd / (baseWeight d d.flattenEnd / 2)`. -/
def flatRatio (d : TailData) (eta : ℝ) : ℝ :=
  flatHistory d eta d.flattenEnd / (baseWeight d d.flattenEnd / 2)

theorem flatRatio_contDiff (d : TailData) : ContDiff ℝ ∞ (flatRatio d) :=
  (flatHistory_contDiff d (flattenEnd_pos d).le).div_const _

theorem flatRatio_bounds (d : TailData) (eta : ℝ) :
    0 ≤ flatRatio d eta ∧ flatRatio d eta ≤ 2 / (1 - d.core.lam) := by
  have hW : 0 < baseWeight d d.flattenEnd := baseWeight_pos d _
  have hI := flatHistory_bounds d eta (flattenEnd_pos d).le
  have hB := baseHistory_le d (flattenEnd_pos d).le
  constructor
  · exact div_nonneg hI.1 (by positivity)
  · calc
      flatRatio d eta ≤ (baseWeight d d.flattenEnd / (1 - d.core.lam)) /
          (baseWeight d d.flattenEnd / 2) :=
        div_le_div_of_nonneg_right (hI.2.trans hB) (by positivity)
      _ = _ := by field_simp [hW.ne', show 1 - d.core.lam ≠ 0 by linarith [d.core.lam_lt]]

theorem flatRatio_deriv_bound (d : TailData) (eta : ℝ) :
    |deriv (flatRatio d) eta| ≤ 2 / (1 - d.core.lam) := by
  have hW : 0 < baseWeight d d.flattenEnd := baseWeight_pos d _
  change |deriv (fun eta => flatHistory d eta d.flattenEnd / (baseWeight d d.flattenEnd / 2)) eta|
      ≤ _
  rw [deriv_div_const, abs_div, abs_of_pos (by positivity : 0 < baseWeight d d.flattenEnd / 2)]
  calc
    _ ≤ baseHistory d d.flattenEnd / (baseWeight d d.flattenEnd / 2) :=
      div_le_div_of_nonneg_right (flatHistory_deriv_bound d eta (flattenEnd_pos d).le) (by
          positivity)
    _ ≤ (baseWeight d d.flattenEnd / (1 - d.core.lam)) / (baseWeight d d.flattenEnd / 2) :=
      div_le_div_of_nonneg_right (baseHistory_le d (flattenEnd_pos d).le) (by positivity)
    _ = _ := by field_simp [hW.ne', show 1 - d.core.lam ≠ 0 by linarith [d.core.lam_lt]]

/-- Decay factor, given by `Real.exp (-(1 - d.core.lam) * (d.uniformWait - 3))`. -/
def decayFactor (d : TailData) : ℝ :=
  Real.exp (-(1 - d.core.lam) * (d.uniformWait - 3))

/-- The actual normalized discrepancy at the first correction center. -/
def normalizedDebt (d : TailData) (eta : ℝ) : ℝ :=
  decayFactor d * (1 / (1 - d.core.lam) - flatRatio d eta)

theorem normalizedDebt_contDiff (d : TailData) : ContDiff ℝ ∞ (normalizedDebt d) :=
  contDiff_const.mul (contDiff_const.sub (flatRatio_contDiff d))

theorem normalizedDebt_bounds (d : TailData) (eta : ℝ) :
    |normalizedDebt d eta| ≤ 3 * decayFactor d ∧
      |deriv (normalizedDebt d) eta| ≤ 3 * decayFactor d := by
  have hk : 0 < 1 - d.core.lam := by linarith [d.core.lam_lt]
  have hinv : 2 / (1 - d.core.lam) ≤ 3 := by
    apply (div_le_iff₀ hk).mpr
    linarith [d.core.lam_lt]
  have hR := flatRatio_bounds d eta
  have he : 0 ≤ decayFactor d := (Real.exp_pos _).le
  constructor
  · unfold normalizedDebt
    rw [abs_mul, abs_of_nonneg he]
    have hsmall : |1 / (1 - d.core.lam) - flatRatio d eta| ≤ 3 := by
      apply abs_le.mpr
      have hpos : 0 ≤ 1 / (1 - d.core.lam) := by positivity
      have htwo : 2 / (1 - d.core.lam) = 2 * (1 / (1 - d.core.lam)) := by ring
      constructor <;> linarith
    calc
      _ ≤ decayFactor d * 3 := mul_le_mul_of_nonneg_left hsmall he
      _ = _ := mul_comm _ _
  · have hd : deriv (normalizedDebt d) eta = -decayFactor d * deriv (flatRatio d) eta := by
      unfold normalizedDebt
      rw [deriv_const_mul_field, deriv_const_sub]
      ring
    rw [hd, abs_mul, abs_neg, abs_of_nonneg he]
    have hbound := (flatRatio_deriv_bound d eta).trans hinv
    calc
      _ ≤ decayFactor d * 3 := mul_le_mul_of_nonneg_left hbound he
      _ = _ := mul_comm _ _

theorem decayFactor_le (d : TailData) (hlam : d.core.lam ≤ 1 / 15) :
    decayFactor d ≤ Real.exp 3 * d.core.lam ^ (28 : ℕ) := by
  have hl1 : d.core.lam ≤ 1 := by linarith [d.core.lam_lt]
  have hlog : Real.log (1 / d.core.lam) = -Real.log d.core.lam := by
    rw [one_div, Real.log_inv]
  have he : decayFactor d = Real.exp (3 * (1 - d.core.lam)) *
      d.core.lam ^ (30 * (1 - d.core.lam)) := by
    rw [decayFactor, TailData.uniformWait, hlog, Real.rpow_def_of_pos d.core.lam_pos, ←
        Real.exp_add]
    congr 1
    ring
  rw [he]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    linarith [d.core.lam_pos]
  · have hp : d.core.lam ^ (30 * (1 - d.core.lam)) ≤ d.core.lam ^ ((28 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge d.core.lam_pos hl1 (by norm_num; linarith)
    simpa only [Real.rpow_natCast] using hp
  · exact Real.rpow_nonneg d.core.lam_pos.le _
  · exact (Real.exp_pos _).le

/-- The normalized debt and its first angular derivative obey the requested
power bound for the actual waiting duration. The constant is universal. -/
theorem actual_debt_first_jet_bound (d : TailData) (hlam : d.core.lam ≤ 1 / 15) (eta : ℝ) :
    |normalizedDebt d eta| ≤ (3 * Real.exp 3) * d.core.lam ^ (28 : ℕ) ∧
    |deriv (normalizedDebt d) eta| ≤ (3 * Real.exp 3) * d.core.lam ^ (28 : ℕ) := by
  have hb := normalizedDebt_bounds d eta
  have he := decayFactor_le d hlam
  have hgrowth : 3 * decayFactor d ≤ (3 * Real.exp 3) * d.core.lam ^ (28 : ℕ) := by
    calc
      _ ≤ 3 * (Real.exp 3 * d.core.lam ^ (28 : ℕ)) :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ = _ := (mul_assoc _ _ _).symm
  exact ⟨hb.1.trans hgrowth, hb.2.trans hgrowth⟩

theorem finalAngular_before_release (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : y ≤ d.releaseStart) : finalAngular d (y, eta) = flattened d (y, eta) := by
  have hrel : y - d.releaseStart ≤ 0 := by linarith
  have htail : y - tailStart d ≤ 1 := by linarith [tailStart_gt_release d]
  have hden : 1 - d.rho ≠ 0 := by linarith [d.rho_lt_half]
  simp [finalAngular, releaseAdjustment_early d hrel, tailShape_early d htail, hden]

/-- The angular history of the actual unedited full outgoing profile, divided
by its common harmless factor `sqrt 2`. -/
def fullHistory (d : TailData) (eta y : ℝ) : ℝ :=
  (5 / 8) * d.core.P * shape eta +
    ∫ t in (0 : ℝ)..y, Real.exp (3 * t / 2) * finalAngular d (t, eta)

theorem fullHistory_eq_flat (d : TailData) (eta : ℝ) {y : ℝ}
    (hy0 : 0 ≤ y) (hyR : y ≤ d.releaseStart) : fullHistory d eta y = flatHistory d eta y := by
  unfold fullHistory flatHistory OutgoingSchedule.primitive
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ≤ y := (uIcc_of_le hy0 ▸ ht).2
  change Real.exp (3 * t / 2) * finalAngular d (t, eta) = flatWeight d eta t
  rw [finalAngular_before_release d eta (ht'.trans hyR)]
  rfl

theorem first_center_after_flatten (d : TailData) : d.flattenEnd ≤ d.releaseStart - 3 := by
  have h := uniformWait_gt_twentyseven d
  dsimp [TailData.releaseStart]
  linarith

/-- Identification with the literal endpoint discrepancy and first-center
normalization of the actual full profile. -/
theorem normalizedDebt_eq_actual (d : TailData) (eta : ℝ) :
    normalizedDebt d eta =
      (baseWeight d d.releaseStart / (2 * (1 - d.core.lam)) - fullHistory d eta d.releaseStart) /
        (baseWeight d (d.releaseStart - 3) / 2) := by
  have hR : 0 ≤ d.releaseStart := (flattenEnd_pos d).le.trans (releaseStart_gt_flattenEnd d).le
  rw [fullHistory_eq_flat d eta hR le_rfl]
  have hI := flatHistory_increment d eta (releaseStart_gt_flattenEnd d).le
  have hconst : baseWeight d d.releaseStart / (2 * (1 - d.core.lam)) -
      flatHistory d eta d.releaseStart =
      baseWeight d d.flattenEnd / (2 * (1 - d.core.lam)) - flatHistory d eta d.flattenEnd := by
    rw [hI]
    ring
  have hcenter : baseWeight d (d.releaseStart - 3) =
      baseWeight d d.flattenEnd * Real.exp ((1 - d.core.lam) * (d.uniformWait - 3)) := by
    rw [baseWeight_hold d ((coreEndpoint_ge_hold d).trans (flattenEnd_gt_core d).le)
      (first_center_after_flatten d)]
    congr 2
    dsimp [TailData.releaseStart]
    ring
  rw [hconst, hcenter]
  unfold normalizedDebt flatRatio decayFactor
  rw [show -(1 - d.core.lam) * (d.uniformWait - 3) = -((1 - d.core.lam) * (d.uniformWait - 3)) by
      ring,
    Real.exp_neg]
  field_simp [(baseWeight_pos d d.flattenEnd).ne', Real.exp_ne_zero,
    show 1 - d.core.lam ≠ 0 by linarith [d.core.lam_lt]]

theorem power28_le_self (d : TailData) : d.core.lam ^ (28 : ℕ) ≤ d.core.lam := by
  have h : d.core.lam ^ ((28 : ℕ) : ℝ) ≤ d.core.lam ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge d.core.lam_pos (by linarith [d.core.lam_lt]) (by norm_num)
  simpa only [Real.rpow_natCast, Real.rpow_one] using h

theorem power28_le_square (d : TailData) : d.core.lam ^ (28 : ℕ) ≤ d.core.lam ^ (2 : ℕ) := by
  have h : d.core.lam ^ ((28 : ℕ) : ℝ) ≤ d.core.lam ^ ((2 : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge d.core.lam_pos (by linarith [d.core.lam_lt]) (by norm_num)
  simpa only [Real.rpow_natCast] using h

/-- Uniform convergence of both actual first jets, with no hypotheses on the
earlier scalar choices or on the angular parameter. -/
theorem actual_debt_tends_to_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.lam < lam0 → ∀ eta : ℝ,
      |normalizedDebt d eta| < ε ∧ |deriv (normalizedDebt d) eta| < ε := by
  let C : ℝ := 3 * Real.exp 3
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min (1 / 15) (ε / C), lt_min (by norm_num) (div_pos hε hC), ?_⟩
  intro d hd eta
  have hsmall : d.core.lam ≤ 1 / 15 := (lt_of_lt_of_le hd (min_le_left _ _)).le
  have hbound : C * d.core.lam ^ (28 : ℕ) < ε := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (power28_le_self d) hC.le)
    have h := lt_of_lt_of_le hd (min_le_right _ _)
    nlinarith [(lt_div_iff₀ hC).mp h]
  have hj := actual_debt_first_jet_bound d hsmall eta
  exact ⟨hj.1.trans_lt hbound, hj.2.trans_lt hbound⟩

/-- A reset for the actual scheduled debt, including the uniform first angular
jet estimate needed for later profile estimates. -/
structure ResetWitness (d : TailData) (K : ℝ) where
  /-- Coefficients of `ResetWitness`, of type `ℝ → Coeff`. -/
  coefficients : ℝ → Coeff
  smooth : ContDiff ℝ ∞ coefficients
  angular : ∀ eta,
    (∫ u, Real.exp (angularSlope d.core.lam * u) * relative (coefficients eta) u) = normalizedDebt
        d eta
  pressure : ∀ eta,
    (∫ u, Real.exp (pressureSlope d.core.lam * u) * ((1 + relative (coefficients eta) u) ^ 2 - 1))
        = 0
  coefficient_bound : ∀ eta, ‖coefficients eta‖ ≤ K * d.core.lam ^ (28 : ℕ)
  eta_derivative_bound : ∀ eta, ‖deriv coefficients eta‖ ≤ K * d.core.lam ^ (28 : ℕ)
  small_jets : ∀ eta u,
    |relative (coefficients eta) u| ≤ 1 / 2 ∧
      |deriv (relative (coefficients eta)) u| ≤ d.core.lam / 4

/-- The complete outgoing data themselves supply a sufficiently small debt.
No small-debt assumption or parameter-derivative assumption remains. -/
theorem exists_scheduled_reset :
    ∃ lam0 K : ℝ, 0 < lam0 ∧ 0 < K ∧ ∀ d : TailData, d.core.lam < lam0 →
      Nonempty (ResetWitness d K) := by
  obtain ⟨ε, L, hε, hL, hsolve⟩ := uniform_reset_branch
  let C : ℝ := 3 * Real.exp 3
  have hC : 0 < C := by dsimp [C]; positivity
  let lam0 : ℝ := min (1 / 15) (min (ε / C) (1 / (4 * L * C)))
  have hlam0 : 0 < lam0 := lt_min (by norm_num) (lt_min (div_pos hε hC) (by positivity))
  refine ⟨lam0, L * C, hlam0, mul_pos hL hC, ?_⟩
  intro d hd
  have hsmall : d.core.lam ≤ 1 / 15 := (lt_of_lt_of_le hd (min_le_left _ _)).le
  have hδε : C * d.core.lam ^ (28 : ℕ) < ε := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (power28_le_self d) hC.le)
    have hlam := lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_left _ _))
    simpa only [mul_comm d.core.lam C] using (lt_div_iff₀ hC).mp hlam
  have hδsmall : L * (C * d.core.lam ^ (28 : ℕ)) ≤ d.core.lam / 4 := by
    have hlam := lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _))
    have hmul := (lt_div_iff₀ (show 0 < 4 * L * C by positivity)).mp hlam
    have hp := mul_le_mul_of_nonneg_left (power28_le_square d) (show 0 ≤ L * C by positivity)
    nlinarith only [hp, mul_lt_mul_of_pos_right hmul d.core.lam_pos]
  have hδ : ∀ eta, normalizedDebt d eta ∈ Ioo (-ε) ε := by
    intro eta
    exact abs_lt.mp ((actual_debt_first_jet_bound d hsmall eta).1.trans_lt hδε)
  obtain ⟨c, hc, _, hceq⟩ := hsolve d.core.lam ⟨d.core.lam_pos.le, d.core.lam_lt.le⟩
  let a : ℝ → Coeff := fun eta => c (normalizedDebt d eta)
  have ha : ContDiff ℝ ∞ a := by
    apply contDiffOn_univ.mp
    exact hc.comp (normalizedDebt_contDiff d).contDiffOn (fun eta _ => hδ eta)
  refine ⟨{
    coefficients := a
    smooth := ha
    angular := fun eta => (hceq _ (hδ eta)).1
    pressure := fun eta => (hceq _ (hδ eta)).2.1
    coefficient_bound := ?_
    eta_derivative_bound := ?_
    small_jets := ?_ }⟩
  · intro eta
    have hb := (hceq _ (hδ eta)).2.2.1
    have hd : |normalizedDebt d eta| ≤ C * d.core.lam ^ (28 : ℕ) :=
      (actual_debt_first_jet_bound d hsmall eta).1
    apply hb.trans
    calc
      _ ≤ L * (C * d.core.lam ^ (28 : ℕ)) := mul_le_mul_of_nonneg_left hd hL.le
      _ = _ := by ring
  · intro eta
    have hcD : HasDerivAt c (deriv c (normalizedDebt d eta)) (normalizedDebt d eta) :=
      ((hc.contDiffAt (isOpen_Ioo.mem_nhds (hδ eta))).differentiableAt (by simp)).hasDerivAt
    have hdD := ((normalizedDebt_contDiff d).differentiable (by simp) eta).hasDerivAt
    have hchain := hcD.scomp eta hdD
    change HasDerivAt a _ eta at hchain
    rw [hchain.deriv, norm_smul, Real.norm_eq_abs]
    have hb := (hceq _ (hδ eta)).2.2.2.1
    have hd := (actual_debt_first_jet_bound d hsmall eta).2
    calc
      _ ≤ (C * d.core.lam ^ (28 : ℕ)) * L :=
        mul_le_mul hd hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · intro eta u
    have hv := (hceq _ (hδ eta)).2.2.2.2 u
    have hb := mul_le_mul_of_nonneg_left (actual_debt_first_jet_bound d hsmall eta).1 hL.le
    constructor
    · exact (hv.1.trans (hb.trans hδsmall)).trans (by linarith only [d.core.lam_lt])
    · exact hv.2.trans (hb.trans hδsmall)

/-- Correction center, given by `d.releaseStart - 3`. -/
def correctionCenter (d : TailData) : ℝ := d.releaseStart - 3

/-- Reference amplitude, given by `(radialAmplitude d.core.P d.core.dropLength d.core.lam
d.flattenEnd / 2) * Real.exp ((1 / 2 + d.core.lam) * d.flattenEnd)`. -/
def referenceAmplitude (d : TailData) : ℝ :=
  (radialAmplitude d.core.P d.core.dropLength d.core.lam d.flattenEnd / 2) *
    Real.exp ((1 / 2 + d.core.lam) * d.flattenEnd)

theorem referenceAmplitude_pos (d : TailData) : 0 < referenceAmplitude d := by
  have hP := d.core.P_pos
  unfold referenceAmplitude radialAmplitude
  positivity

theorem reference_matches (d : TailData) {y : ℝ} (hy : d.flattenEnd ≤ y) :
    baseE d.core.lam (referenceAmplitude d) y =
      radialAmplitude d.core.P d.core.dropLength d.core.lam y / 2 := by
  have hh : d.core.holdStart ≤ d.flattenEnd := (coreEndpoint_ge_hold d).trans (flattenEnd_gt_core
      d).le
  have h := radialAmplitude_hold (P := d.core.P) (lam := d.core.lam)
    d.core.dropLength_pos.le hh hy
  rw [h]
  unfold baseE referenceAmplitude
  rw [mul_assoc, ← Real.exp_add]
  have he : (1 / 2 + d.core.lam) * d.flattenEnd + (-1 / 2 - d.core.lam) * y =
      -(1 / 2 + d.core.lam) * (y - d.flattenEnd) := by ring
  rw [he]
  ring

theorem last_four_after_flatten (d : TailData) : d.flattenEnd < d.releaseStart - 4 := by
  have h := uniformWait_gt_twentyseven d
  dsimp [TailData.releaseStart]
  linarith

theorem original_matches_reference (d : TailData) (eta : ℝ) {y : ℝ}
    (hy : y ∈ Icc (d.releaseStart - 4) d.releaseStart) :
    finalAngular d (y, eta) = baseE d.core.lam (referenceAmplitude d) y := by
  have hf : d.flattenEnd ≤ y := (last_four_after_flatten d).le.trans hy.1
  rw [finalAngular_uniform_wait d eta hf hy.2, reference_matches d hf]

theorem weighted_baseE (lam e0 y : ℝ) :
    Real.exp (3 * y / 2) * baseE lam e0 y = e0 * Real.exp ((1 - lam) * y) := by
  unfold baseE
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem reference_scale (d : TailData) :
    referenceAmplitude d * Real.exp ((1 - d.core.lam) * correctionCenter d) =
      baseWeight d (correctionCenter d) / 2 := by
  rw [← weighted_baseE, reference_matches d (y := correctionCenter d)
    (first_center_after_flatten d)]
  unfold baseWeight
  ring

theorem relative_zero_outside (d : TailData) (c : Coeff) {y : ℝ}
    (hy : y ∉ Ioo (d.releaseStart - 4) d.releaseStart) :
    relative c (y - correctionCenter d) = 0 := by
  apply Classical.byContradiction
  intro hn
  have hs := relative_support c hn
  apply hy
  dsimp [correctionCenter] at hs
  constructor <;> linarith [hs.1, hs.2]

/-- The actual complete outgoing angular field after the two relative bumps. -/
def correctedAngular (d : TailData) (c : ℝ → Coeff) (p : ℝ × ℝ) : ℝ :=
  finalAngular d p * (1 + relative (c p.2) (p.1 - correctionCenter d))

theorem correctedAngular_contDiff (d : TailData) (c : ℝ → Coeff) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (correctedAngular d c) :=
  (finalAngular_contDiff d).mul
    (contDiff_const.add (relative_joint_contDiff.comp
      ((hc.comp contDiff_snd).prodMk (contDiff_fst.sub contDiff_const))))

theorem correctedAngular_unchanged (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : y ∉ Ioo (d.releaseStart - 4) d.releaseStart) :
    correctedAngular d c (y, eta) = finalAngular d (y, eta) := by
  simp [correctedAngular, relative_zero_outside d (c eta) hy]

theorem corrected_matches_reference (d : TailData) (c : ℝ → Coeff) (eta : ℝ) {y : ℝ}
    (hy : y ∈ Ioo (d.releaseStart - 4) d.releaseStart) :
    correctedAngular d c (y, eta) =
      modifiedE d.core.lam (referenceAmplitude d) (correctionCenter d) (c eta) y := by
  unfold correctedAngular modifiedE
  rw [original_matches_reference d eta ⟨hy.1.le, hy.2.le⟩]

theorem corrected_difference_reference (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) :
    correctedAngular d c (y, eta) - finalAngular d (y, eta) =
      modifiedE d.core.lam (referenceAmplitude d) (correctionCenter d) (c eta) y -
        baseE d.core.lam (referenceAmplitude d) y := by
  by_cases hy : y ∈ Ioo (d.releaseStart - 4) d.releaseStart
  · rw [corrected_matches_reference d c eta hy, original_matches_reference d eta ⟨hy.1.le, hy.2.le⟩]
  · rw [correctedAngular_unchanged d c eta hy]
    simp [modifiedE, relative_zero_outside d (c eta) hy]

theorem corrected_pressure_reference (d : TailData) (c : ℝ → Coeff) (eta y : ℝ) :
    (correctedAngular d c (y, eta)) ^ 2 - (finalAngular d (y, eta)) ^ 2 =
      (modifiedE d.core.lam (referenceAmplitude d) (correctionCenter d) (c eta) y) ^ 2 -
        (baseE d.core.lam (referenceAmplitude d) y) ^ 2 := by
  by_cases hy : y ∈ Ioo (d.releaseStart - 4) d.releaseStart
  · rw [corrected_matches_reference d c eta hy, original_matches_reference d eta ⟨hy.1.le, hy.2.le⟩]
  · rw [correctedAngular_unchanged d c eta hy]
    simp [modifiedE, relative_zero_outside d (c eta) hy]

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : ResetWitness d K)

theorem positive (p : ℝ × ℝ) : 0 < correctedAngular d w.coefficients p := by
  apply mul_pos (finalAngular_pos d p)
  have h := (abs_le.mp (w.small_jets p.2 (p.1 - correctionCenter d)).1).1
  linarith

theorem logSlope_le (eta : ℝ) {y : ℝ} (hy : y ∈ Ioo (d.releaseStart - 4) d.releaseStart) :
    logSlope (fun t => correctedAngular d w.coefficients (t, eta)) y ≤ -d.core.lam / 2 := by
  have he : (fun t => correctedAngular d w.coefficients (t, eta)) =ᶠ[𝓝 y]
      modifiedE d.core.lam (referenceAmplitude d) (correctionCenter d) (w.coefficients eta) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with t ht
    exact corrected_matches_reference d w.coefficients eta ht
  have hp := positive_and_slope_of_small d.core.lam d.core.lam_pos (w.coefficients eta)
    (y - correctionCenter d) (w.small_jets eta (y - correctionCenter d)).1
    (w.small_jets eta (y - correctionCenter d)).2
  unfold logSlope
  rw [he.deriv_eq]
  dsimp only
  rw [corrected_matches_reference d w.coefficients eta hy]
  change logSlope (modifiedE d.core.lam (referenceAmplitude d) (correctionCenter d)
    (w.coefficients eta)) y ≤ _
  rw [modifiedE_logSlope d.core.lam (referenceAmplitude d) (correctionCenter d)
    (w.coefficients eta) y (referenceAmplitude_pos d).ne' hp.1.ne']
  exact hp.2

theorem pressure_neutral (eta : ℝ) :
    (∫ y, (correctedAngular d w.coefficients (y, eta)) ^ 2 - (finalAngular d (y, eta)) ^ 2) = 0 :=
        by
  simp_rw [corrected_pressure_reference]
  rw [pressure_integral_formula, w.pressure eta, mul_zero]

theorem angular_change (eta : ℝ) :
    (∫ y, Real.exp (3 * y / 2) *
      (correctedAngular d w.coefficients (y, eta) - finalAngular d (y, eta))) =
      (baseWeight d (correctionCenter d) / 2) * normalizedDebt d eta := by
  simp_rw [corrected_difference_reference]
  have hf : (fun y => Real.exp (3 * y / 2) *
      (modifiedE d.core.lam (referenceAmplitude d) (correctionCenter d) (w.coefficients eta) y -
        baseE d.core.lam (referenceAmplitude d) y)) =
      (fun y => referenceAmplitude d * (Real.exp ((1 - d.core.lam) * y) *
        relative (w.coefficients eta) (y - correctionCenter d))) := by
    funext y
    calc
      _ = (Real.exp (3 * y / 2) * baseE d.core.lam (referenceAmplitude d) y) *
          relative (w.coefficients eta) (y - correctionCenter d) := by unfold modifiedE; ring
      _ = _ := by rw [weighted_baseE]; ring
  have hm : (∫ y, Real.exp ((1 - d.core.lam) * y) * relative (w.coefficients eta) y) =
      normalizedDebt d eta := w.angular eta
  rw [hf, integral_const_mul, weighted_translate_integral, hm, ← mul_assoc, reference_scale]

end ResetWitness

theorem integral_edit_window (d : TailData) (f : ℝ → ℝ)
    (hf : ∀ y, y ∉ Ioo (d.releaseStart - 4) d.releaseStart → f y = 0) :
    (∫ y in (0 : ℝ)..d.releaseStart, f y) = ∫ y, f y := by
  have hR : 0 ≤ d.releaseStart := (flattenEnd_pos d).le.trans (releaseStart_gt_flattenEnd d).le
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  apply hf y
  intro hw
  apply hy
  exact ⟨(flattenEnd_pos d).trans ((last_four_after_flatten d).trans hw.1), hw.2.le⟩

/-- Corrected history, given by `(5 / 8) * d.core.P * shape eta + ∫ t in (0 :
ℝ)..d.releaseStart, Real.exp (3 * t / 2) * correctedAngular d c (t, eta)`. -/
def correctedHistory (d : TailData) (c : ℝ → Coeff) (eta : ℝ) : ℝ :=
  (5 / 8) * d.core.P * shape eta +
    ∫ t in (0 : ℝ)..d.releaseStart, Real.exp (3 * t / 2) * correctedAngular d c (t, eta)

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : ResetWitness d K)

theorem exact_endpoint (eta : ℝ) : correctedHistory d w.coefficients eta =
    baseWeight d d.releaseStart / (2 * (1 - d.core.lam)) := by
  have hm : IntervalIntegrable (fun y => Real.exp (3 * y / 2) *
      correctedAngular d w.coefficients (y, eta)) volume 0 d.releaseStart :=
    (((Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 2))).mul
      ((correctedAngular_contDiff d w.coefficients w.smooth).continuous.comp
        (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  have ho : IntervalIntegrable (fun y => Real.exp (3 * y / 2) * finalAngular d (y, eta))
      volume 0 d.releaseStart :=
    (((Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 2))).mul
      ((finalAngular_contDiff d).continuous.comp (continuous_id.prodMk
          continuous_const))).intervalIntegrable _ _
  have hchange :
      (∫ y in (0 : ℝ)..d.releaseStart, Real.exp (3 * y / 2) * correctedAngular d w.coefficients (y,
          eta)) -
      (∫ y in (0 : ℝ)..d.releaseStart, Real.exp (3 * y / 2) * finalAngular d (y, eta)) =
        (baseWeight d (correctionCenter d) / 2) * normalizedDebt d eta := by
    rw [← intervalIntegral.integral_sub hm ho]
    have hf : (fun y => Real.exp (3 * y / 2) * correctedAngular d w.coefficients (y, eta) -
        Real.exp (3 * y / 2) * finalAngular d (y, eta)) =
        (fun y => Real.exp (3 * y / 2) *
          (correctedAngular d w.coefficients (y, eta) - finalAngular d (y, eta))) := by
              funext y; ring
    rw [hf, integral_edit_window d _ (fun y hy => by
      rw [correctedAngular_unchanged d w.coefficients eta hy, sub_self, mul_zero])]
    exact w.angular_change eta
  have hnorm : (baseWeight d (correctionCenter d) / 2) * normalizedDebt d eta =
      baseWeight d d.releaseStart / (2 * (1 - d.core.lam)) - fullHistory d eta d.releaseStart := by
    rw [normalizedDebt_eq_actual]
    have hz : baseWeight d (correctionCenter d) / 2 ≠ 0 := by
      exact ne_of_gt (div_pos (baseWeight_pos d _) (by norm_num))
    change (baseWeight d (correctionCenter d) / 2) *
      ((baseWeight d d.releaseStart / (2 * (1 - d.core.lam)) - fullHistory d eta d.releaseStart) /
        (baseWeight d (correctionCenter d) / 2)) = _
    field_simp [(baseWeight_pos d (correctionCenter d)).ne']
  rw [hnorm] at hchange
  unfold correctedHistory fullHistory at *
  linarith

theorem pressure_interval_neutral (eta : ℝ) :
    (∫ y in (0 : ℝ)..d.releaseStart, (correctedAngular d w.coefficients (y, eta)) ^ 2) =
      ∫ y in (0 : ℝ)..d.releaseStart, (finalAngular d (y, eta)) ^ 2 := by
  have hm : IntervalIntegrable (fun y => (correctedAngular d w.coefficients (y, eta)) ^ 2)
      volume 0 d.releaseStart :=
    (((correctedAngular_contDiff d w.coefficients w.smooth).continuous.comp
      (continuous_id.prodMk continuous_const)).pow 2).intervalIntegrable _ _
  have ho : IntervalIntegrable (fun y => (finalAngular d (y, eta)) ^ 2)
      volume 0 d.releaseStart :=
    (((finalAngular_contDiff d).continuous.comp (continuous_id.prodMk continuous_const)).pow
        2).intervalIntegrable _ _
  apply sub_eq_zero.mp
  rw [← intervalIntegral.integral_sub hm ho,
    integral_edit_window d _ (fun y hy => by
      rw [correctedAngular_unchanged d w.coefficients eta hy, sub_self])]
  exact w.pressure_neutral eta

theorem physical_endpoint (eta : ℝ) :
    Real.sqrt 2 * correctedHistory d w.coefficients eta =
      (Real.exp d.releaseStart * Real.sqrt (2 * Real.exp d.releaseStart) *
        correctedAngular d w.coefficients (d.releaseStart, eta)) / (1 - d.core.lam) := by
  have hout : d.releaseStart ∉ Ioo (d.releaseStart - 4) d.releaseStart := by simp
  rw [w.exact_endpoint eta, correctedAngular_unchanged d w.coefficients eta hout,
    finalAngular_uniform_wait d eta (releaseStart_gt_flattenEnd d).le le_rfl,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), AngularMomentReset.sqrt_exp_half]
  unfold baseWeight
  have hex : Real.exp d.releaseStart * Real.exp (d.releaseStart / 2) =
      Real.exp (3 * d.releaseStart / 2) := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = (Real.exp d.releaseStart * Real.exp (d.releaseStart / 2)) * Real.sqrt 2 *
        (radialAmplitude d.core.P d.core.dropLength d.core.lam d.releaseStart / 2) /
          (1 - d.core.lam) := by
      rw [hex]
      field_simp [show 1 - d.core.lam ≠ 0 by linarith [d.core.lam_lt]]
    _ = _ := by ring

end ResetWitness

/-- The actual complete outgoing profile allows the pressure-neutral angular
reset for sufficiently small `lam`, with a common scalar threshold. -/
theorem complete_angular_reset :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ d : TailData, d.core.lam < lam0 →
      ∃ c : ℝ → Coeff,
        ContDiff ℝ ∞ (correctedAngular d c) ∧
        (∀ p, 0 < correctedAngular d c p) ∧
        (∀ eta y, y ∉ Ioo (d.releaseStart - 4) d.releaseStart →
          correctedAngular d c (y, eta) = finalAngular d (y, eta)) ∧
        (∀ eta, (∫ y, (correctedAngular d c (y, eta)) ^ 2 - (finalAngular d (y, eta)) ^ 2) = 0 ∧
          Real.sqrt 2 * correctedHistory d c eta =
            (Real.exp d.releaseStart * Real.sqrt (2 * Real.exp d.releaseStart) *
              correctedAngular d c (d.releaseStart, eta)) / (1 - d.core.lam)) ∧
        (∀ eta y, y ∈ Ioo (d.releaseStart - 4) d.releaseStart →
          logSlope (fun t => correctedAngular d c (t, eta)) y ≤ -d.core.lam / 2) := by
  obtain ⟨lam0, K, hlam0, _, hreset⟩ := exists_scheduled_reset
  refine ⟨lam0, hlam0, ?_⟩
  intro d hd
  obtain ⟨w⟩ := hreset d hd
  exact ⟨w.coefficients, correctedAngular_contDiff d w.coefficients w.smooth,
    w.positive, fun eta _ hy => correctedAngular_unchanged d w.coefficients eta hy,
    fun eta => ⟨w.pressure_neutral eta, w.physical_endpoint eta⟩,
    fun eta _ hy => w.logSlope_le eta hy⟩

theorem full_weight_ideal (d : TailData) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    Real.exp (3 * y / 2) * finalAngular d (y, eta) =
      (d.core.P * shape eta) * Real.exp ((8 / 5 : ℝ) * y) := by
  rw [finalAngular_before d eta
    (hy.trans (d.core.holdStart_pos.le.trans (coreEndpoint_ge_hold d))),
    angular_ideal d.core.dropLength_pos.le hy]
  calc
    _ = (d.core.P * shape eta) * (Real.exp (3 * y / 2) * Real.exp (y / 10)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- The ideal incoming segment fixes the prefix as an actual improper integral. -/
theorem history_from_ideal_prefix (d : TailData) (eta : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f)
    (hprefix : ∀ y ≤ 0, f y = (d.core.P * shape eta) * Real.exp ((8 / 5 : ℝ) * y))
    {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn f (Iic y) ∧
      (∫ t in Iic y, f t) = (5 / 8) * d.core.P * shape eta + ∫ t in (0 : ℝ)..y, f t := by
  have hexp : IntegrableOn (fun t => (d.core.P * shape eta) * Real.exp ((8 / 5 : ℝ) * t))
      (Iic (0 : ℝ)) :=
    (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 8 / 5) 0).const_mul (d.core.P * shape eta)
  have h0 : IntegrableOn f (Iic (0 : ℝ)) :=
    IntegrableOn.congr_fun hexp (fun t ht => (hprefix t ht).symm) measurableSet_Iic
  have hi : IntegrableOn f (Iic y) := by
    rw [← Iic_union_Ioc_eq_Iic hy]
    exact h0.union hf.integrableOn_Ioc
  have he : (∫ t in Iic (0 : ℝ), f t) = (5 / 8) * d.core.P * shape eta := by
    calc
      _ = ∫ t in Iic (0 : ℝ), (d.core.P * shape eta) * Real.exp ((8 / 5 : ℝ) * t) :=
        setIntegral_congr_fun measurableSet_Iic (fun t ht => hprefix t ht)
      _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 8 / 5) 0]
        norm_num
        ring
  refine ⟨hi, ?_⟩
  have hdiff := intervalIntegral.integral_Iic_sub_Iic h0 hi
  rw [he] at hdiff
  linarith

theorem fullHistory_eq_integral (d : TailData) (eta : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    fullHistory d eta y = ∫ t in Iic y, Real.exp (3 * t / 2) * finalAngular d (t, eta) := by
  have hc : Continuous (fun t => Real.exp (3 * t / 2) * finalAngular d (t, eta)) :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 2)).mul
      ((finalAngular_contDiff d).continuous.comp (continuous_id.prodMk continuous_const))
  exact (history_from_ideal_prefix d eta _ hc (fun t ht => full_weight_ideal d eta ht) hy).2.symm

namespace ResetWitness

variable {d : TailData} {K : ℝ} (w : ResetWitness d K)

theorem correctedHistory_eq_integral (eta : ℝ) :
    correctedHistory d w.coefficients eta =
      ∫ t in Iic d.releaseStart, Real.exp (3 * t / 2) * correctedAngular d w.coefficients (t, eta)
          := by
  have hc : Continuous (fun t => Real.exp (3 * t / 2) * correctedAngular d w.coefficients (t, eta))
      :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).div_const 2)).mul
      ((correctedAngular_contDiff d w.coefficients w.smooth).continuous.comp
        (continuous_id.prodMk continuous_const))
  have hp : ∀ t ≤ 0, Real.exp (3 * t / 2) * correctedAngular d w.coefficients (t, eta) =
      (d.core.P * shape eta) * Real.exp ((8 / 5 : ℝ) * t) := by
    intro t ht
    have hout : t ∉ Ioo (d.releaseStart - 4) d.releaseStart := by
      intro hw
      linarith [flattenEnd_pos d, last_four_after_flatten d, hw.1]
    rw [correctedAngular_unchanged d w.coefficients eta hout]
    exact full_weight_ideal d eta ht
  exact (history_from_ideal_prefix d eta _ hc hp
    ((flattenEnd_pos d).le.trans (releaseStart_gt_flattenEnd d).le)).2.symm

/-- The reset identity for the full physical angular integral, including the
incoming ideal segment, with `X = exp y` and `H = sqrt (2*X) * E`. -/
theorem physical_integral_endpoint (eta : ℝ) :
    (∫ t in Iic d.releaseStart, Real.exp t * Real.sqrt (2 * Real.exp t) *
      correctedAngular d w.coefficients (t, eta)) =
      (Real.exp d.releaseStart * Real.sqrt (2 * Real.exp d.releaseStart) *
        correctedAngular d w.coefficients (d.releaseStart, eta)) / (1 - d.core.lam) := by
  have hf : (fun t => Real.exp t * Real.sqrt (2 * Real.exp t) *
      correctedAngular d w.coefficients (t, eta)) =
      (fun t => Real.sqrt 2 * (Real.exp (3 * t / 2) * correctedAngular d w.coefficients (t, eta)))
          := by
    funext t
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), AngularMomentReset.sqrt_exp_half]
    have he : Real.exp t * Real.exp (t / 2) = Real.exp (3 * t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = Real.sqrt 2 * ((Real.exp t * Real.exp (t / 2)) * correctedAngular d w.coefficients (t,
          eta)) := by
          ring
      _ = _ := by rw [he]
  rw [hf, integral_const_mul, ← w.correctedHistory_eq_integral eta]
  exact w.physical_endpoint eta

end ResetWitness

end ActualHistory

end NavierStokes.UniformAngularReset
