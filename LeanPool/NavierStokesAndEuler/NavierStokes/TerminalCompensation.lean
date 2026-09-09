/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.UniformAngularReset
public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatTailEdit
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Three exact terminal compensation moments

Three constructed, separated additive bumps in a positive interval repair the
pressure, energy, and angular moments. Factoring out the positive shaped-wait
amplitude leaves one fixed quadratic map, so its smooth inverse and estimates
are uniform in the transverse parameter.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace NavierStokes.TerminalCompensation

abbrev Coeff := Fin 3 → ℝ

/-- An arbitrary reserved interval in the normalized positive radial coordinate. -/
structure Patch where
  left : ℝ
  right : ℝ
  left_pos : 0 < left
  ordered : left < right

noncomputable def lower (P : Patch) (j : Fin 3) : ℝ :=
  P.left + (2 * (j.val : ℝ) + 1) * (P.right - P.left) / 7

noncomputable def upper (P : Patch) (j : Fin 3) : ℝ :=
  P.left + (2 * (j.val : ℝ) + 2) * (P.right - P.left) / 7

theorem lower_gt_left (P : Patch) (j : Fin 3) : P.left < lower P j := by
  fin_cases j <;> simp only [lower] <;>
    norm_num <;> linarith [P.ordered]

theorem lower_lt_upper (P : Patch) (j : Fin 3) : lower P j < upper P j := by
  dsimp [lower, upper]
  nlinarith [P.ordered]

theorem upper_lt_right (P : Patch) (j : Fin 3) : upper P j < P.right := by
  fin_cases j <;> simp only [upper] <;>
    norm_num <;> linarith [P.ordered]

theorem intervals_separated (P : Patch) (i j : Fin 3) (hij : i < j) :
    upper P i ≤ lower P j := by
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num <;>
    dsimp [upper, lower] <;> norm_num <;> linarith [P.ordered]

noncomputable def bump (P : Patch) (j : Fin 3) : ℝ → ℝ :=
  LocalizedMomentRepair.bump (lower P j) (upper P j)

theorem bump_contDiff (P : Patch) (j : Fin 3) : ContDiff ℝ ∞ (bump P j) :=
  LocalizedMomentRepair.bump_contDiff _ _

theorem bump_nonneg (P : Patch) (j : Fin 3) (x : ℝ) : 0 ≤ bump P j x :=
  LocalizedMomentRepair.bump_nonneg _ _ _

theorem bump_le_one (P : Patch) (j : Fin 3) (x : ℝ) : bump P j x ≤ 1 :=
  LocalizedMomentRepair.bump_le_one _ _ _

theorem bump_tsupport (P : Patch) (j : Fin 3) :
    tsupport (bump P j) ⊆ Ioo (lower P j) (upper P j) :=
  LocalizedMomentRepair.bump_tsupport_subset_open _ _ (lower_lt_upper P j)

theorem bump_support_patch (P : Patch) (j : Fin 3) :
    support (bump P j) ⊆ Icc P.left P.right := by
  intro x hx
  have ht := bump_tsupport P j (subset_tsupport _ hx)
  exact ⟨(lower_gt_left P j).le.trans ht.1.le,
    ht.2.le.trans (upper_lt_right P j).le⟩

theorem bumps_disjoint (P : Patch) (i j : Fin 3) (hij : i ≠ j) (x : ℝ) :
    bump P i x * bump P j x = 0 := by
  by_cases hi : bump P i x = 0
  · simp [hi]
  by_cases hj : bump P j x = 0
  · simp [hj]
  have hix := bump_tsupport P i (subset_tsupport _ hi)
  have hjx := bump_tsupport P j (subset_tsupport _ hj)
  rcases lt_or_gt_of_ne hij with h | h
  · have hs := intervals_separated P i j h
    linarith [hix.2, hjx.1]
  · have hs := intervals_separated P j i h
    linarith [hjx.2, hix.1]

noncomputable def correction (P : Patch) (c : Coeff) (x : ℝ) : ℝ :=
  ∑ j, c j * bump P j x

theorem correction_contDiff (P : Patch) (c : Coeff) :
    ContDiff ℝ ∞ (correction P c) :=
  ContDiff.sum (fun j _ => contDiff_const.mul (bump_contDiff P j))

theorem correction_support (P : Patch) (c : Coeff) :
    support (correction P c) ⊆ Icc P.left P.right := by
  intro x hx
  by_contra hnot
  apply hx
  apply Finset.sum_eq_zero
  intro j _
  have hb : bump P j x = 0 := by
    by_contra hn
    exact hnot (bump_support_patch P j hn)
  simp [hb]

theorem correction_tsupport (P : Patch) (c : Coeff) :
    tsupport (correction P c) ⊆ Ioo P.left P.right := by
  have hs : support (correction P c) ⊆ LocalizedMomentRepair.repairRegion (lower P) (upper P) := by
    intro x hx
    by_contra hnot
    apply hx
    apply Finset.sum_eq_zero
    intro j _
    have hb : bump P j x = 0 := by
      by_contra hn
      exact hnot (mem_iUnion.mpr ⟨j,
        LocalizedMomentRepair.bump_support_subset _ _ (lower_lt_upper P j) hn⟩)
    simp [hb]
  have ht := closure_minimal hs
    (LocalizedMomentRepair.repairRegion_isCompact (lower P) (upper P)).isClosed
  intro x hx
  have hm := LocalizedMomentRepair.repairRegion_subset_open (lower P) (upper P)
    (lower_lt_upper P) (ht hx)
  obtain ⟨j, hj⟩ := mem_iUnion.mp hm
  exact ⟨(lower_gt_left P j).trans hj.1, hj.2.trans (upper_lt_right P j)⟩

theorem correction_hasCompactSupport (P : Patch) (c : Coeff) :
    HasCompactSupport (correction P c) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (correction_support P c)

theorem weighted_integrable (P : Patch) (s : ℝ) (g : ℝ → ℝ)
    (hg : Continuous g) (hs : support g ⊆ Icc P.left P.right) :
    Integrable (fun x => x ^ s * g x) := by
  have hsupport : support (fun x => x ^ s * g x) ⊆ Icc P.left P.right := by
    intro x hx
    apply hs
    intro hz
    exact hx (by simp [hz])
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  apply ContinuousOn.integrableOn_Icc
  apply ContinuousOn.mul _ hg.continuousOn
  apply continuousOn_id.rpow_const
  intro x hx
  exact Or.inl (ne_of_gt (P.left_pos.trans_le hx.1))

theorem weighted_bump_integrable (P : Patch) (s : ℝ) (j : Fin 3) :
    Integrable (fun x => x ^ s * bump P j x) :=
  weighted_integrable P s _ (bump_contDiff P j).continuous (bump_support_patch P j)

theorem weighted_bump_sq_integrable (P : Patch) (s : ℝ) (j : Fin 3) :
    Integrable (fun x => x ^ s * (bump P j x) ^ 2) := by
  apply weighted_integrable P s _ ((bump_contDiff P j).continuous.pow 2)
  intro x hx
  apply bump_support_patch P j
  intro hz
  exact hx (by simp [hz])

theorem correction_square (P : Patch) (c : Coeff) (x : ℝ) :
    (correction P c x) ^ 2 = ∑ j, (c j) ^ 2 * (bump P j x) ^ 2 := by
  have h01 := bumps_disjoint P 0 1 (by decide) x
  have h02 := bumps_disjoint P 0 2 (by decide) x
  have h12 := bumps_disjoint P 1 2 (by decide) x
  simp only [correction, Fin.sum_univ_three]
  calc
    _ = c 0 ^ 2 * bump P 0 x ^ 2 + c 1 ^ 2 * bump P 1 x ^ 2 +
        c 2 ^ 2 * bump P 2 x ^ 2 +
        2 * c 0 * c 1 * (bump P 0 x * bump P 1 x) +
        2 * c 0 * c 2 * (bump P 0 x * bump P 2 x) +
        2 * c 1 * c 2 * (bump P 1 x * bump P 2 x) := by ring
    _ = _ := by rw [h01, h02, h12]; ring

noncomputable def bumpMoment (P : Patch) (s : ℝ) (j : Fin 3) : ℝ :=
  ∫ x, x ^ s * bump P j x

noncomputable def squareMoment (P : Patch) (s : ℝ) (j : Fin 3) : ℝ :=
  ∫ x, x ^ s * (bump P j x) ^ 2

theorem correction_moment (P : Patch) (s : ℝ) (c : Coeff) :
    (∫ x, x ^ s * correction P c x) = ∑ j, c j * bumpMoment P s j := by
  have hf : (fun x => x ^ s * correction P c x) =
      (fun x => ∑ j, c j * (x ^ s * bump P j x)) := by
    funext x
    simp only [correction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, bumpMoment]
  · intro j _
    exact (weighted_bump_integrable P s j).const_mul _

theorem correction_square_moment (P : Patch) (s : ℝ) (c : Coeff) :
    (∫ x, x ^ s * (correction P c x) ^ 2) = ∑ j, (c j) ^ 2 * squareMoment P s j := by
  have hf : (fun x => x ^ s * (correction P c x) ^ 2) =
      (fun x => ∑ j, (c j) ^ 2 * (x ^ s * (bump P j x) ^ 2)) := by
    funext x
    rw [correction_square, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hf, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, squareMoment]
  · intro j _
    exact (weighted_bump_sq_integrable P s j).const_mul _

noncomputable def slope (lam : ℝ) : ℝ := -1 / 2 - lam

noncomputable def powers (lam : ℝ) : Coeff := ![-1 + slope lam, slope lam, 1 / 2]

theorem powers_injective (lam : ℝ) (hlam : 0 ≤ lam) : Injective (powers lam) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [powers, slope] at hij <;> norm_num <;> linarith

noncomputable def linearMatrix (P : Patch) (lam : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  LocalizedMomentRepair.matrix (powers lam) (lower P) (upper P)

theorem linearMatrix_entry (P : Patch) (lam : ℝ) (i j : Fin 3) :
    linearMatrix P lam i j = bumpMoment P (powers lam i) j := rfl

/-- The three powers are those of pressure, energy, and angular momentum. -/
theorem linearMatrix_det_ne_zero (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) :
    (linearMatrix P lam).det ≠ 0 :=
  LocalizedMomentRepair.matrix_det_ne_zero (powers lam) (lower P) (upper P)
    (powers_injective lam hlam) (fun j => P.left_pos.trans (lower_gt_left P j))
    (lower_lt_upper P) (intervals_separated P)

noncomputable def linearEquiv (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) :
    Coeff ≃L[ℝ] Coeff :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := (linearMatrix P lam).mulVec
      invFun := (linearMatrix P lam)⁻¹.mulVec
      map_add' := Matrix.mulVec_add _
      map_smul' := fun r c => Matrix.mulVec_smul _ r c
      left_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero P lam hlam)), Matrix.one_mulVec]
      right_inv := fun c => by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero P lam hlam)), Matrix.one_mulVec] }

theorem linearEquiv_apply (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) (c : Coeff) :
    linearEquiv P lam hlam c = (linearMatrix P lam).mulVec c := rfl

noncomputable def quadraticBilin (P : Patch) : Coeff →ₗ[ℝ] Coeff →ₗ[ℝ] Coeff where
  toFun c :=
    { toFun := fun d =>
        ![(1 / 2) * ∑ j, squareMoment P (-1) j * c j * d j,
          (1 / 2) * ∑ j, squareMoment P 0 j * c j * d j, 0]
      map_add' := fun d e => by
        ext i
        fin_cases i <;> simp [Pi.add_apply, Fin.sum_univ_three] <;> ring
      map_smul' := fun r d => by
        ext i
        fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three] <;> ring }
  map_add' c d := by
    ext e i
    fin_cases i <;> simp [Pi.add_apply, Fin.sum_univ_three] <;> ring
  map_smul' r c := by
    ext e i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three] <;> ring

noncomputable def quadraticCLM (P : Patch) : Coeff →L[ℝ] Coeff →L[ℝ] Coeff :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Coeff) (F' := Coeff)).toLinearMap.comp
      (quadraticBilin P))

theorem quadraticCLM_apply (P : Patch) (c d : Coeff) :
    quadraticCLM P c d =
      ![(1 / 2) * ∑ j, squareMoment P (-1) j * c j * d j,
        (1 / 2) * ∑ j, squareMoment P 0 j * c j * d j, 0] := rfl

noncomputable def baseProfile (lam x : ℝ) : ℝ := x ^ slope lam

/-- One half of a squared-profile change, against a power weight. -/
noncomputable def weightedChange (P : Patch) (lam : ℝ) (c : Coeff) (w x : ℝ) : ℝ :=
  x ^ w * ((baseProfile lam x + correction P c x) ^ 2 - (baseProfile lam x) ^ 2) / 2

theorem weightedChange_identity (P : Patch) (lam : ℝ) (c : Coeff) (w x : ℝ) :
    weightedChange P lam c w x =
      x ^ (w + slope lam) * correction P c x + x ^ w * (correction P c x) ^ 2 / 2 := by
  by_cases hc : correction P c x = 0
  · simp [weightedChange, hc]
  have hx : 0 < x := P.left_pos.trans_le (correction_support P c hc).1
  rw [Real.rpow_add hx]
  unfold weightedChange baseProfile
  ring

theorem weighted_correction_integrable (P : Patch) (s : ℝ) (c : Coeff) :
    Integrable (fun x => x ^ s * correction P c x) :=
  weighted_integrable P s _ (correction_contDiff P c).continuous (correction_support P c)

theorem weighted_correction_sq_integrable (P : Patch) (s : ℝ) (c : Coeff) :
    Integrable (fun x => x ^ s * (correction P c x) ^ 2) := by
  apply weighted_integrable P s _ ((correction_contDiff P c).continuous.pow 2)
  intro x hx
  apply correction_support P c
  intro hz
  exact hx (by simp [hz])

theorem weightedChange_integrable (P : Patch) (lam : ℝ) (c : Coeff) (w : ℝ) :
    Integrable (weightedChange P lam c w) := by
  simp only [funext (weightedChange_identity P lam c w)]
  exact (weighted_correction_integrable P (w + slope lam) c).add
    ((weighted_correction_sq_integrable P w c).div_const 2)

theorem weightedChange_integral (P : Patch) (lam : ℝ) (c : Coeff) (w : ℝ) :
    (∫ x, weightedChange P lam c w x) =
      (∑ j, c j * bumpMoment P (w + slope lam) j) +
        (∑ j, (c j) ^ 2 * squareMoment P w j) / 2 := by
  simp only [funext (weightedChange_identity P lam c w)]
  rw [integral_add (weighted_correction_integrable P (w + slope lam) c)
    ((weighted_correction_sq_integrable P w c).div_const 2), integral_div,
    correction_moment, correction_square_moment]

/-- Actual normalized pressure, energy, and angular moment changes. -/
noncomputable def momentMap (P : Patch) (lam : ℝ) (c : Coeff) : Coeff :=
  ![∫ x, weightedChange P lam c (-1) x,
    ∫ x, weightedChange P lam c 0 x,
    ∫ x, x ^ (1 / 2 : ℝ) * correction P c x]

theorem momentMap_identity (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) (c : Coeff) :
    linearEquiv P lam hlam c + quadraticCLM P c c = momentMap P lam c := by
  rw [linearEquiv_apply, quadraticCLM_apply]
  ext i
  fin_cases i <;>
    simp [momentMap, weightedChange_integral, correction_moment, Matrix.mulVec, dotProduct,
      linearMatrix_entry, powers, Fin.sum_univ_three] <;> ring

theorem correction_iteratedDeriv (P : Patch) (c : Coeff) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (correction P c) x = ∑ j, c j * iteratedDeriv k (bump P j) x := by
  change iteratedDeriv k (fun y => ∑ j, c j * bump P j y) x = _
  rw [LocalizedMomentRepair.iteratedDeriv_finite_sum Finset.univ
    (fun j x => c j * bump P j x)
    (fun j => contDiff_const.mul (bump_contDiff P j)) k x]
  apply Finset.sum_congr rfl
  intro j _
  exact iteratedDeriv_const_mul
    (c j) ((bump_contDiff P j).of_le
      (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt

theorem correction_derivative_bound (P : Patch) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Coeff) (x : ℝ),
      |iteratedDeriv k (correction P c) x| ≤ C * ‖c‖ := by
  have hb : ∀ j : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      |iteratedDeriv k (bump P j) x| ≤ C := fun j =>
    LocalizedMomentRepair.smooth_compact_derivative_bound _ (bump_contDiff P j)
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (bump_support_patch P j)) k
  choose C hC hbound using hb
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), fun c x => ?_⟩
  rw [correction_iteratedDeriv]
  calc
    |∑ j, c j * iteratedDeriv k (bump P j) x| ≤
        ∑ j, |c j * iteratedDeriv k (bump P j) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ‖c‖ * C j := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      apply mul_le_mul _ (hbound j x) (abs_nonneg _) (norm_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm c j
    _ = (∑ j, C j) * ‖c‖ := by rw [← Finset.mul_sum, mul_comm]

theorem correction_first_jet_bound (P : Patch) :
    ∃ D : ℝ, 0 < D ∧ ∀ (c : Coeff) (x : ℝ),
      |correction P c x| ≤ D * ‖c‖ ∧ |deriv (correction P c) x| ≤ D * ‖c‖ := by
  obtain ⟨C₀, hC₀, hb₀⟩ := correction_derivative_bound P 0
  obtain ⟨C₁, hC₁, hb₁⟩ := correction_derivative_bound P 1
  refine ⟨C₀ + C₁ + 1, by linarith, fun c x => ⟨?_, ?_⟩⟩
  · exact (hb₀ c x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg c))
  · have ht : |iteratedDeriv 1 (correction P c) x| ≤ (C₀ + C₁ + 1) * ‖c‖ :=
      (hb₁ c x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg c))
    simpa only [iteratedDeriv_one] using ht

theorem baseProfile_positive (lam : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < baseProfile lam x := Real.rpow_pos_of_pos hx _

theorem baseProfile_lower_bound (P : Patch) (lam : ℝ) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Icc P.left P.right, m ≤ baseProfile lam x := by
  apply isCompact_Icc.exists_forall_le'
  · apply continuousOn_id.rpow_const
    intro x hx
    exact Or.inl (ne_of_gt (P.left_pos.trans_le hx.1))
  · intro x hx
    exact baseProfile_positive lam (P.left_pos.trans_le hx.1)

/-- A single smooth inverse repairs all three actual moments and has uniform
value, derivative, and spatial first-jet bounds. Smallness also preserves positivity. -/
theorem exists_normalized_compensation (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ (g : Coeff → Coeff) (ε C : ℝ), 0 < ε ∧ 0 < C ∧
      ContDiffOn ℝ ∞ g (Metric.ball 0 ε) ∧ g 0 = 0 ∧
      ∀ d ∈ Metric.ball (0 : Coeff) ε,
        momentMap P lam (g d) = d ∧ ‖g d‖ ≤ C * ‖d‖ ∧ ‖fderiv ℝ g d‖ ≤ C ∧
        ∀ x : ℝ,
          (|correction P (g d) x| ≤ C * ‖d‖ ∧
            |deriv (correction P (g d)) x| ≤ C * ‖d‖) ∧
          (0 < x → 0 < baseProfile lam x + correction P (g d) x) := by
  let B := linearEquiv P lam hlam
  let A := quadraticCLM P
  let β : ℝ := ‖B.symm.toContinuousLinearMap‖ + 1
  let K : ℝ := ‖A‖ + 1
  let r : ℝ := 1 / (4 * β * K)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hinv : ∀ v, ‖B.symm v‖ ≤ β * ‖v‖ := by
    intro v
    exact (B.symm.toContinuousLinearMap.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (by dsimp [β]; linarith) (norm_nonneg v))
  have hA : ‖A‖ ≤ K := by dsimp [K]; linarith
  have hsmall : 4 * β * K * r ≤ 1 := by dsimp [r]; field_simp ; rfl
  obtain ⟨g, hg, hgeq, hglip⟩ := UniformAngularReset.exists_smooth_solver_on_ball
    B A β K r hβ hK.le hr hinv hA hsmall
  obtain ⟨D, hD, hjet⟩ := correction_first_jet_bound P
  obtain ⟨m, hm, hmin⟩ := baseProfile_lower_bound P lam
  let C : ℝ := (1 + D) * (2 * β)
  let ε : ℝ := min (r / (4 * β)) (m / (2 * C))
  have hC : 0 < C := mul_pos (by linarith) (by positivity)
  have hε : 0 < ε := lt_min (div_pos hr (by positivity)) (div_pos hm (by positivity))
  have hsub : Metric.ball (0 : Coeff) ε ⊆ Metric.ball 0 (r / (4 * β)) :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hC₀ : 2 * β ≤ C := by dsimp [C]; nlinarith
  have hC₁ : D * (2 * β) ≤ C := by dsimp [C]; nlinarith
  have hzero : g 0 = 0 := by
    have hz := (hgeq 0 (Metric.mem_ball_self (div_pos hr (by positivity)))).2
    simpa only [norm_zero, mul_zero, norm_le_zero_iff] using hz
  refine ⟨g, ε, C, hε, hC, hg.mono hsub, hzero, ?_⟩
  intro d hd
  have hnorm : ‖g d‖ ≤ (2 * β) * ‖d‖ := (hgeq d (hsub hd)).2
  have hbound : D * ‖g d‖ ≤ C * ‖d‖ :=
    (mul_le_mul_of_nonneg_left hnorm hD.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC₁ (norm_nonneg d))
  have heq := (hgeq d (hsub hd)).1
  change linearEquiv P lam hlam (g d) + quadraticCLM P (g d) (g d) = d at heq
  rw [momentMap_identity] at heq
  refine ⟨heq, hnorm.trans (mul_le_mul_of_nonneg_right hC₀ (norm_nonneg d)), ?_, ?_⟩
  · apply le_trans _ hC₀
    apply norm_fderiv_le_of_lip' ℝ (by positivity : 0 ≤ 2 * β)
    filter_upwards [Metric.isOpen_ball.mem_nhds (hsub hd)] with e he
    exact hglip e he d (hsub hd)
  · intro x
    have hval := (hjet (g d) x).1.trans hbound
    refine ⟨⟨hval, (hjet (g d) x).2.trans hbound⟩, ?_⟩
    intro hx
    by_cases hc : correction P (g d) x = 0
    · simpa only [hc, add_zero] using baseProfile_positive lam hx
    have hbase := hmin x (correction_support P (g d) hc)
    have hd' : ‖d‖ < ε := by simpa only [Metric.mem_ball, dist_zero_right] using hd
    have hsize : C * ‖d‖ < m / 2 := by
      have ht := mul_lt_mul_of_pos_left (hd'.trans_le (min_le_right _ _)) hC
      have hcancel : C * (m / (2 * C)) = m / 2 := by field_simp
      rwa [hcancel] at ht
    have hlow := neg_abs_le (correction P (g d) x)
    linarith

/-- Evaluation of the finite bump combination is an actual bounded linear map. -/
noncomputable def correctionCLM (P : Patch) (x : ℝ) : Coeff →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => correction P c x
      map_add' := fun c d => by
        simp only [correction, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [correction, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum,
          RingHom.id_apply] }

theorem correctionCLM_apply (P : Patch) (x : ℝ) (c : Coeff) :
    correctionCLM P x c = correction P c x := rfl

theorem correction_parameter_deriv (P : Patch) {c : ℝ → Coeff} {η : ℝ}
    (hc : DifferentiableAt ℝ c η) (x : ℝ) :
    deriv (fun s => correction P (c s) x) η = correction P (deriv c η) x :=
  ((correctionCLM P x).hasFDerivAt.comp_hasDerivAt η hc.hasDerivAt).deriv

theorem correction_family_contDiffOn (P : Patch) {U : Set ℝ} {c : ℝ → Coeff}
    (hc : ContDiffOn ℝ ∞ c U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => correction P (c z.1) z.2) (U ×ˢ univ) := by
  apply ContDiffOn.sum
  intro j _
  exact ((contDiffOn_pi.mp hc j).comp contDiffOn_fst (fun z hz => hz.1)).mul
    ((bump_contDiff P j).comp_contDiffOn contDiffOn_snd)

/-- Composition with the debt gives the true parameter derivative, with no
regularity hypothesis on a previously chosen solution branch. -/
theorem composed_solver_deriv_bound {g : Coeff → Coeff} {ε C : ℝ}
    (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 ε))
    (hbound : ∀ v ∈ Metric.ball (0 : Coeff) ε, ‖fderiv ℝ g v‖ ≤ C)
    {d : ℝ → Coeff} {η : ℝ} (hd : DifferentiableAt ℝ d η)
    (hmem : d η ∈ Metric.ball (0 : Coeff) ε) :
    ‖deriv (g ∘ d) η‖ ≤ C * ‖deriv d η‖ := by
  have hgd := (hg.contDiffAt (Metric.isOpen_ball.mem_nhds hmem)).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  rw [(hgd.hasFDerivAt.comp_hasDerivAt η hd.hasDerivAt).deriv]
  exact ((fderiv ℝ g (d η)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hbound (d η) hmem) (norm_nonneg _))

/-- The physical profile uses the actual additive bumps at scale `R`. -/
noncomputable def physicalProfile (P : Patch) (lam R a : ℝ) (c : Coeff) (X : ℝ) : ℝ :=
  a * (baseProfile lam (X / R) + correction P c (X / R))

noncomputable def cleanProfile (lam R a X : ℝ) : ℝ := a * baseProfile lam (X / R)

noncomputable def physicalMoments (P : Patch) (lam R a : ℝ) (c : Coeff) : Coeff :=
  ![∫ X, ((physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2) / X,
    ∫ X, (physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2,
    ∫ X, Real.sqrt (2 * X) * (physicalProfile P lam R a c X - cleanProfile lam R a X)]

theorem integral_rescale (R : ℝ) (hR : 0 < R) (F : ℝ → ℝ) :
    (∫ X, F X) = R * ∫ x, F (R * x) := by
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hR), smul_eq_mul]
  field_simp

theorem pressure_density_rescale (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) (x : ℝ) :
    ((physicalProfile P lam R a c (R * x)) ^ 2 - (cleanProfile lam R a (R * x)) ^ 2) /
        (R * x) = (2 * a ^ 2 / R) * weightedChange P lam c (-1) x := by
  simp only [physicalProfile, cleanProfile, mul_div_cancel_left₀ x hR.ne',
    weightedChange, Real.rpow_neg_one, div_eq_mul_inv, mul_inv_rev]
  ring

theorem energy_density_rescale (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) (x : ℝ) :
    (physicalProfile P lam R a c (R * x)) ^ 2 - (cleanProfile lam R a (R * x)) ^ 2 =
      (2 * a ^ 2) * weightedChange P lam c 0 x := by
  simp only [physicalProfile, cleanProfile, mul_div_cancel_left₀ x hR.ne',
    weightedChange, Real.rpow_zero]
  ring

theorem angular_density_rescale (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) (x : ℝ) :
    Real.sqrt (2 * (R * x)) *
      (physicalProfile P lam R a c (R * x) - cleanProfile lam R a (R * x)) =
      (Real.sqrt (2 * R) * a) * (x ^ (1 / 2 : ℝ) * correction P c x) := by
  simp only [physicalProfile, cleanProfile, mul_div_cancel_left₀ x hR.ne']
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 2 * R)]
  simp only [Real.sqrt_eq_rpow]
  ring

/-- The normalization constants follow from the actual change of variable `X=R*x`. -/
theorem physicalMoments_eq (P : Patch) (lam R a : ℝ) (hR : 0 < R) (c : Coeff) :
    physicalMoments P lam R a c =
      ![2 * a ^ 2 * momentMap P lam c 0,
        2 * R * a ^ 2 * momentMap P lam c 1,
        R * Real.sqrt (2 * R) * a * momentMap P lam c 2] := by
  ext i
  fin_cases i
  · change (∫ X, ((physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2) / X) =
      2 * a ^ 2 * ∫ x, weightedChange P lam c (-1) x
    rw [integral_rescale R hR]
    simp only [pressure_density_rescale P lam R a hR c, integral_const_mul]
    field_simp
  · change (∫ X, (physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2) =
      2 * R * a ^ 2 * ∫ x, weightedChange P lam c 0 x
    rw [integral_rescale R hR]
    simp only [energy_density_rescale P lam R a hR c, integral_const_mul]
    ring
  · change (∫ X, Real.sqrt (2 * X) *
      (physicalProfile P lam R a c X - cleanProfile lam R a X)) =
      R * Real.sqrt (2 * R) * a * ∫ x, x ^ (1 / 2 : ℝ) * correction P c x
    rw [integral_rescale R hR]
    simp only [angular_density_rescale P lam R a hR c, integral_const_mul]
    ring

noncomputable def normalizationFactors (R a : ℝ) : Coeff :=
  ![(2 * a ^ 2)⁻¹, (2 * R * a ^ 2)⁻¹, (R * Real.sqrt (2 * R) * a)⁻¹]

/-- Signed debts are negated so that their sum with the patch changes is zero. -/
noncomputable def normalizedDebt (R a : ℝ) (d : Coeff) : Coeff :=
  -(normalizationFactors R a * d)

theorem physicalMoments_cancel (P : Patch) (lam R a : ℝ) (hR : 0 < R) (ha : 0 < a)
    (c d : Coeff) (heq : momentMap P lam c = normalizedDebt R a d) :
    physicalMoments P lam R a c + d = 0 := by
  have hs : Real.sqrt (2 * R) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have cancel (t y : ℝ) (ht : t ≠ 0) : t * (-(t⁻¹ * y)) + y = 0 := by
    rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ ht, one_mul, neg_add_cancel]
  rw [physicalMoments_eq P lam R a hR c, heq]
  ext i
  fin_cases i
  · exact cancel (2 * a ^ 2) (d 0) (by positivity)
  · exact cancel (2 * R * a ^ 2) (d 1) (by positivity)
  · exact cancel (R * Real.sqrt (2 * R) * a) (d 2) (by positivity)

/-- Radial normalization, independent of the shaped-wait amplitude. -/
noncomputable def scaledDebt (R : ℝ) (d : Coeff) : Coeff :=
  ![d 0, d 1 / R, d 2 / (R * Real.sqrt (2 * R))]

noncomputable def amplitudeFactors (a : ℝ) : Coeff :=
  ![(2 * a ^ 2)⁻¹, (2 * a ^ 2)⁻¹, a⁻¹]

noncomputable def amplitudeDebt (a : ℝ) (v : Coeff) : Coeff := -(amplitudeFactors a * v)

theorem normalizedDebt_eq (R a : ℝ) (d : Coeff) :
    normalizedDebt R a d = amplitudeDebt a (scaledDebt R d) := by
  ext i
  fin_cases i <;> simp [normalizedDebt, normalizationFactors, amplitudeDebt, amplitudeFactors,
    scaledDebt, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem amplitudeFactors_contDiffOn {U : Set ℝ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ η ∈ U, 0 < a η) :
    ContDiffOn ℝ ∞ (fun η => amplitudeFactors (a η)) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact (contDiffOn_const.mul (ha.pow 2)).inv (fun η hη => by have := hpos η hη; positivity)
  · exact (contDiffOn_const.mul (ha.pow 2)).inv (fun η hη => by have := hpos η hη; positivity)
  · exact ha.inv (fun η hη => (hpos η hη).ne')

theorem amplitudeDebt_contDiffOn {U : Set ℝ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ η ∈ U, 0 < a η) (v : Coeff) :
    ContDiffOn ℝ ∞ (fun η => amplitudeDebt (a η) v) U :=
  ((amplitudeFactors_contDiffOn ha hpos).mul contDiffOn_const).neg

theorem compact_amplitude_bounds {U S : Set ℝ} (hU : IsOpen U) (hS : IsCompact S)
    (hSU : S ⊆ U) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a U)
    (hpos : ∀ η ∈ U, 0 < a η) :
    ∃ D : ℝ, 0 < D ∧ ∀ η ∈ S,
      ‖amplitudeFactors (a η)‖ ≤ D ∧
      ‖deriv (fun θ => amplitudeFactors (a θ)) η‖ ≤ D ∧
      |a η| ≤ D ∧ |deriv a η| ≤ D := by
  have hF := amplitudeFactors_contDiffOn ha hpos
  have hFd : ContDiffOn ℝ ∞ (deriv (fun θ => amplitudeFactors (a θ))) U :=
    hF.deriv_of_isOpen hU (by simp)
  have had : ContDiffOn ℝ ∞ (deriv a) U := ha.deriv_of_isOpen hU (by simp)
  obtain ⟨B₀, hb₀⟩ := hS.exists_bound_of_continuousOn (hF.continuousOn.mono hSU)
  obtain ⟨B₁, hb₁⟩ := hS.exists_bound_of_continuousOn (hFd.continuousOn.mono hSU)
  obtain ⟨B₂, hb₂⟩ := hS.exists_bound_of_continuousOn (ha.continuousOn.mono hSU)
  obtain ⟨B₃, hb₃⟩ := hS.exists_bound_of_continuousOn (had.continuousOn.mono hSU)
  let D : ℝ := 1 + |B₀| + |B₁| + |B₂| + |B₃|
  have hD₀ : B₀ ≤ D := by dsimp [D]; linarith [le_abs_self B₀, abs_nonneg B₁, abs_nonneg B₂,
    abs_nonneg B₃]
  have hD₁ : B₁ ≤ D := by dsimp [D]; linarith [le_abs_self B₁, abs_nonneg B₀, abs_nonneg B₂,
    abs_nonneg B₃]
  have hD₂ : B₂ ≤ D := by dsimp [D]; linarith [le_abs_self B₂, abs_nonneg B₀, abs_nonneg B₁,
    abs_nonneg B₃]
  have hD₃ : B₃ ≤ D := by dsimp [D]; linarith [le_abs_self B₃, abs_nonneg B₀, abs_nonneg B₁,
    abs_nonneg B₂]
  refine ⟨D, by dsimp [D]; positivity, fun η hη => ⟨(hb₀ η hη).trans hD₀,
    (hb₁ η hη).trans hD₁, ?_, ?_⟩⟩
  · exact (hb₂ η hη).trans hD₂
  · exact (hb₃ η hη).trans hD₃

theorem amplitudeDebt_bounds {U S : Set ℝ} (hU : IsOpen U) (hSU : S ⊆ U)
    {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ η ∈ U, 0 < a η)
    {D : ℝ} (hD : ∀ η ∈ S, ‖amplitudeFactors (a η)‖ ≤ D ∧
      ‖deriv (fun θ => amplitudeFactors (a θ)) η‖ ≤ D)
    (v : Coeff) {η : ℝ} (hη : η ∈ S) :
    ‖amplitudeDebt (a η) v‖ ≤ D * ‖v‖ ∧
      ‖deriv (fun θ => amplitudeDebt (a θ) v) η‖ ≤ D * ‖v‖ := by
  have hF : DifferentiableAt ℝ (fun θ => amplitudeFactors (a θ)) η :=
    ((amplitudeFactors_contDiffOn ha hpos).contDiffAt (hU.mem_nhds (hSU hη))).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  constructor
  · dsimp [amplitudeDebt]
    rw [norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hD η hη).1 (norm_nonneg v))
  · simp only [amplitudeDebt]
    rw [((hF.hasDerivAt.mul_const v).fun_neg).deriv]
    rw [norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hD η hη).2 (norm_nonneg v))

/-- The value, normalized radial derivative, and parameter derivative of the
actual additive profile perturbation are all small. -/
noncomputable def FirstJetBound (P : Patch) (a : ℝ → ℝ) (c : ℝ → Coeff)
    (η L : ℝ) : Prop :=
  ∀ x : ℝ, |a η * correction P (c η) x| ≤ L ∧
    |a η * deriv (correction P (c η)) x| ≤ L ∧
    |deriv (fun θ => a θ * correction P (c θ) x) η| ≤ L

/-- One debt threshold and one first-jet constant work on the entire compact
parameter range. Both are independent of the physical radial scale. -/
theorem exists_uniform_parameter_compensation (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam)
    {U S : Set ℝ} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ η ∈ U, 0 < a η) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ v : Coeff, ‖v‖ < ε →
      ∃ (c : ℝ → Coeff) (V : Set ℝ),
        IsOpen V ∧ S ⊆ V ∧ V ⊆ U ∧ ContDiffOn ℝ ∞ c V ∧
        ∀ η ∈ S, momentMap P lam (c η) = amplitudeDebt (a η) v ∧
          ‖c η‖ ≤ C * ‖v‖ ∧ ‖deriv c η‖ ≤ C * ‖v‖ ∧
          FirstJetBound P a c η (C * ‖v‖) ∧
          ∀ x : ℝ, 0 < x → 0 < a η * (baseProfile lam x + correction P (c η) x) := by
  obtain ⟨g, ε₀, C₀, hε₀, hC₀, hg, hg0, hspec⟩ := exists_normalized_compensation P lam hlam
  obtain ⟨D, hD, hbounds⟩ := compact_amplitude_bounds hU hS hSU ha hpos
  obtain ⟨J, hJ, hjet⟩ := correction_first_jet_bound P
  let B : ℝ := C₀ * D
  let T : ℝ := D * B + D * (J * B)
  let C : ℝ := 1 + B + T
  have hB : 0 < B := mul_pos hC₀ hD
  have hT : 0 < T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hTC : T ≤ C := by dsimp [C]; linarith
  have hDBC : D * B ≤ C := by dsimp [T] at hTC; nlinarith [mul_pos hD (mul_pos hJ hB)]
  refine ⟨ε₀ / D, C, div_pos hε₀ hD, hC, ?_⟩
  intro v hv
  let d : ℝ → Coeff := fun η => amplitudeDebt (a η) v
  have hd : ContDiffOn ℝ ∞ d U := amplitudeDebt_contDiffOn ha hpos v
  let V : Set ℝ := U ∩ d ⁻¹' Metric.ball 0 ε₀
  have hV : IsOpen V := hd.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hd_bound : ∀ η ∈ S, ‖d η‖ ≤ D * ‖v‖ ∧ ‖deriv d η‖ ≤ D * ‖v‖ := by
    intro η hη
    exact amplitudeDebt_bounds hU hSU ha hpos
      (fun η hη => ⟨(hbounds η hη).1, (hbounds η hη).2.1⟩) v hη
  have hSV : S ⊆ V := by
    intro η hη
    refine ⟨hSU hη, ?_⟩
    change dist (d η) 0 < ε₀
    rw [dist_zero_right]
    apply (hd_bound η hη).1.trans_lt
    have ht := (lt_div_iff₀ hD).mp hv
    simpa only [mul_comm] using ht
  let c : ℝ → Coeff := g ∘ d
  have hc : ContDiffOn ℝ ∞ c V :=
    hg.comp (hd.mono inter_subset_left) (fun η hη => hη.2)
  refine ⟨c, V, hV, hSV, inter_subset_left, hc, ?_⟩
  intro η hη
  have hηV := hSV hη
  have hηU := hSU hη
  have hm : d η ∈ Metric.ball (0 : Coeff) ε₀ := hηV.2
  have hval : ‖c η‖ ≤ B * ‖v‖ := by
    exact ((hspec (d η) hm).2.1).trans
      (by simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left (hd_bound η hη).1 hC₀.le)
  have hdif : DifferentiableAt ℝ d η :=
    (hd.contDiffAt (hU.mem_nhds hηU)).differentiableAt (by simp)
  have hcdif : DifferentiableAt ℝ c η :=
    (hc.contDiffAt (hV.mem_nhds hηV)).differentiableAt (by simp)
  have hcderiv : ‖deriv c η‖ ≤ B * ‖v‖ := by
    apply (composed_solver_deriv_bound hg (fun w hw => (hspec w hw).2.2.1) hdif hm).trans
    simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left (hd_bound η hη).2 hC₀.le
  have hcorr : ∀ x, |correction P (c η) x| ≤ B * ‖v‖ ∧
      |deriv (correction P (c η)) x| ≤ B * ‖v‖ := by
    intro x
    have hb : C₀ * ‖d η‖ ≤ B * ‖v‖ := by
      simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left (hd_bound η hη).1 hC₀.le
    exact ⟨((hspec (d η) hm).2.2.2 x).1.1.trans hb,
      ((hspec (d η) hm).2.2.2 x).1.2.trans hb⟩
  refine ⟨(hspec (d η) hm).1,
    hval.trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg v)),
    hcderiv.trans (mul_le_mul_of_nonneg_right hBC (norm_nonneg v)), ?_, ?_⟩
  · intro x
    have ha₀ : |a η| ≤ D := (hbounds η hη).2.2.1
    have ha₁ : |deriv a η| ≤ D := (hbounds η hη).2.2.2
    have hparam : |deriv (fun θ => correction P (c θ) x) η| ≤ (J * B) * ‖v‖ := by
      rw [correction_parameter_deriv P hcdif x]
      exact ((hjet (deriv c η) x).1).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcderiv hJ.le)
    have hmul₀ : |a η * correction P (c η) x| ≤ (D * B) * ‖v‖ := by
      rw [abs_mul]
      exact (mul_le_mul ha₀ (hcorr x).1 (abs_nonneg _) hD.le).trans_eq (by ring)
    have hmul₁ : |a η * deriv (correction P (c η)) x| ≤ (D * B) * ‖v‖ := by
      rw [abs_mul]
      exact (mul_le_mul ha₀ (hcorr x).2 (abs_nonneg _) hD.le).trans_eq (by ring)
    refine ⟨hmul₀.trans (mul_le_mul_of_nonneg_right hDBC (norm_nonneg v)),
      hmul₁.trans (mul_le_mul_of_nonneg_right hDBC (norm_nonneg v)), ?_⟩
    have hadif : DifferentiableAt ℝ a η :=
      (ha.contDiffAt (hU.mem_nhds hηU)).differentiableAt (by simp)
    have hfdif : DifferentiableAt ℝ (fun θ => correction P (c θ) x) η :=
      (correctionCLM P x).differentiableAt.comp η hcdif
    rw [(hadif.hasDerivAt.fun_mul hfdif.hasDerivAt).deriv]
    calc
      _ ≤ |deriv a η * correction P (c η) x| +
          |a η * deriv (fun θ => correction P (c θ) x) η| := abs_add_le _ _
      _ ≤ D * (B * ‖v‖) + D * ((J * B) * ‖v‖) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul ha₁ (hcorr x).1 (abs_nonneg _) hD.le)
          (mul_le_mul ha₀ hparam (abs_nonneg _) hD.le)
      _ = T * ‖v‖ := by dsimp [T]; ring
      _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right hTC (norm_nonneg v)
  · intro x hx
    exact mul_pos (hpos η hηU) (((hspec (d η) hm).2.2.2 x).2 hx)

theorem physicalProfile_eq_clean_outside (P : Patch) (lam R a : ℝ) (c : Coeff) (X : ℝ)
    (hX : X / R ∉ Ioo P.left P.right) :
    physicalProfile P lam R a c X = cleanProfile lam R a X := by
  have hz : correction P c (X / R) = 0 := by
    by_contra hn
    exact hX (correction_tsupport P c (subset_tsupport _ hn))
  simp only [physicalProfile, cleanProfile, hz, add_zero]

theorem physicalDifference_hasCompactSupport (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) :
    HasCompactSupport (fun X => physicalProfile P lam R a c X - cleanProfile lam R a X) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (R * P.left) (R * P.right)))
  intro X hX
  have hn : correction P c (X / R) ≠ 0 := by
    intro hz
    apply hX
    simp only [physicalProfile, cleanProfile, hz, add_zero, sub_self]
  have hx := correction_support P c hn
  constructor
  · have h := (le_div_iff₀ hR).mp hx.1
    simpa only [mul_comm] using h
  · have h := (div_le_iff₀ hR).mp hx.2
    simpa only [mul_comm] using h

/-- On the reserved patch `U=0`, so the mixed axial-angular moment is unchanged. -/
theorem mixed_moment_unchanged (P : Patch) (lam R a : ℝ) (c : Coeff) (U : ℝ → ℝ)
    (hU : ∀ X, X / R ∈ Ioo P.left P.right → U X = 0) :
    (∫ X, U X * physicalProfile P lam R a c X) = ∫ X, U X * cleanProfile lam R a X := by
  congr 1
  funext X
  by_cases hX : X / R ∈ Ioo P.left P.right
  · simp [hU X hX]
  · rw [physicalProfile_eq_clean_outside P lam R a c X hX]

theorem angular_scale_eq (R : ℝ) (hR : 0 < R) :
    R * Real.sqrt (2 * R) = Real.sqrt 2 * R ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow R,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR, Real.rpow_one]
  ring

noncomputable def heatDebt (T : OutgoingTail.TailData) (ν K η : ℝ) : Coeff :=
  ![HeatTailEdit.pressureDebt (HeatTailEdit.outgoingProfile T K η) T.h ν K,
    HeatTailEdit.energyDebt (HeatTailEdit.outgoingProfile T K η) T.h ν K,
    HeatTailEdit.angularDebt (HeatTailEdit.outgoingProfile T K η) T.h ν K]

theorem heatDebt_independent (T : OutgoingTail.TailData) (ν : ℝ) {K : ℝ}
    (hK : 0 < K) (η : ℝ) : heatDebt T ν K η = heatDebt T ν K 0 := by
  ext i
  fin_cases i
  · exact (HeatTailEdit.outgoing_pressureDebt_eq T ν η hK).trans
      (HeatTailEdit.outgoing_pressureDebt_eq T ν 0 hK).symm
  · exact (HeatTailEdit.outgoing_energyDebt_eq T ν η hK).trans
      (HeatTailEdit.outgoing_energyDebt_eq T ν 0 hK).symm
  · exact (HeatTailEdit.outgoing_angularDebt_eq T ν η hK).trans
      (HeatTailEdit.outgoing_angularDebt_eq T ν 0 hK).symm

/-- The actual heat-tail debts become uniformly `O(1/K)` in the fixed patch
coordinate when the patch radius is `q*K`. No debt estimate is assumed. -/
theorem scaled_heatDebt_bound (T : OutgoingTail.TailData) (ν q : ℝ)
    (hν : 0 < ν) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 0 < K →
      ‖scaledDebt (q * K) (heatDebt T ν K 0)‖ ≤ C / K := by
  let H := HeatTailEdit.heatConstant T.h ν
  let e := HeatTailEdit.outgoingAmplitude T
  let A := HeatTailEdit.exponent T.h
  have hH : 0 < H := HeatTailEdit.heatConstant_pos T.h_pos hν
  have he : 0 < e := HeatTailEdit.outgoingAmplitude_pos T
  have hA : 0 < A := by dsimp [A, HeatTailEdit.exponent]; linarith [T.h_pos]
  have hh : 0 < T.h := T.h_pos
  let P₀ : ℝ := 2 * H * e ^ 2 / (2 * A + 1)
  let S₀ : ℝ := 2 * H * e ^ 2 / (2 * A)
  let I₀ : ℝ := Real.sqrt 2 * H * e / T.h
  have hP₀ : 0 < P₀ := by dsimp [P₀]; positivity
  have hS₀ : 0 < S₀ := by dsimp [S₀]; positivity
  have hI₀ : 0 < I₀ := by dsimp [I₀]; positivity
  have hsqrt : 0 < Real.sqrt (2 * q) := Real.sqrt_pos.2 (by positivity)
  let C : ℝ := P₀ + S₀ / q + I₀ / (q * Real.sqrt (2 * q))
  have hC : 0 < C := by dsimp [C]; positivity
  have hSq : 0 < S₀ / q := div_pos hS₀ hq
  have hIq : 0 < I₀ / (q * Real.sqrt (2 * q)) := div_pos hI₀ (mul_pos hq hsqrt)
  have hCP : P₀ ≤ C := by dsimp [C]; linarith
  have hCS : S₀ / q ≤ C := by dsimp [C]; linarith
  have hCI : I₀ / (q * Real.sqrt (2 * q)) ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro K hK
  have hqK : 0 < q * K := mul_pos hq hK
  have hrootK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hrootqK : 0 < Real.sqrt (2 * (q * K)) := Real.sqrt_pos.2 (by positivity)
  have hp : |heatDebt T ν K 0 0| ≤ P₀ / K := by
    convert! (HeatTailEdit.outgoing_pressure T hν hK 0).2 using 1
    dsimp [P₀, H, e, A]
    rw [div_div]
    congr 1
    ring
  have hs : |heatDebt T ν K 0 1| ≤ S₀ := (HeatTailEdit.outgoing_energy T hν hK 0).2
  have hi : |heatDebt T ν K 0 2| ≤ I₀ * Real.sqrt K := by
    convert! (HeatTailEdit.outgoing_angular T hν hK 0).2 using 1
    dsimp [I₀, H, e]
    ring
  apply (pi_norm_le_iff_of_nonneg (div_nonneg hC.le hK.le)).mpr
  intro i
  fin_cases i
  · change |heatDebt T ν K 0 0| ≤ C / K
    exact hp.trans (div_le_div_of_nonneg_right hCP hK.le)
  · change |heatDebt T ν K 0 1 / (q * K)| ≤ C / K
    rw [abs_div, abs_of_pos hqK]
    calc
      _ ≤ S₀ / (q * K) := div_le_div_of_nonneg_right hs hqK.le
      _ = (S₀ / q) / K := (div_div S₀ q K).symm
      _ ≤ C / K := div_le_div_of_nonneg_right hCS hK.le
  · change |heatDebt T ν K 0 2 / (q * K * Real.sqrt (2 * (q * K)))| ≤ C / K
    rw [abs_div, abs_of_pos (mul_pos hqK hrootqK)]
    calc
      _ ≤ (I₀ * Real.sqrt K) / (q * K * Real.sqrt (2 * (q * K))) :=
        div_le_div_of_nonneg_right hi (mul_pos hqK hrootqK).le
      _ = (I₀ / (q * Real.sqrt (2 * q))) / K := by
        rw [← mul_assoc 2 q K, Real.sqrt_mul (by positivity : 0 ≤ 2 * q)]
        field_simp
      _ ≤ C / K := div_le_div_of_nonneg_right hCI hK.le

theorem FirstJetBound.mono {P : Patch} {a : ℝ → ℝ} {c : ℝ → Coeff} {η L M : ℝ}
    (h : FirstJetBound P a c η L) (hLM : L ≤ M) : FirstJetBound P a c η M := by
  intro x
  exact ⟨(h x).1.trans hLM, (h x).2.1.trans hLM, (h x).2.2.trans hLM⟩

/-- The actual outgoing heat edit is compensated for every sufficiently large
radius, uniformly on the compact parameter range, with `O(1/K)` first-jet cost. -/
theorem exists_heat_compensation (P : Patch) (lam : ℝ) (hlam : 0 ≤ lam)
    (T : OutgoingTail.TailData) (ν q : ℝ) (hν : 0 < ν) (hq : 0 < q)
    {U S : Set ℝ} (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ η ∈ U, 0 < a η) :
    ∃ K₀ C : ℝ, 0 < K₀ ∧ 0 < C ∧ ∀ K : ℝ, K₀ ≤ K →
      ∃ (c : ℝ → Coeff) (V : Set ℝ),
        IsOpen V ∧ S ⊆ V ∧ V ⊆ U ∧ ContDiffOn ℝ ∞ c V ∧
        ∀ η ∈ S,
          physicalMoments P lam (q * K) (a η) (c η) + heatDebt T ν K η = 0 ∧
          ‖c η‖ ≤ C / K ∧ ‖deriv c η‖ ≤ C / K ∧
          FirstJetBound P a c η (C / K) ∧
          ∀ X : ℝ, 0 < X → 0 < physicalProfile P lam (q * K) (a η) (c η) X := by
  obtain ⟨ε, C₁, hε, hC₁, hsolve⟩ :=
    exists_uniform_parameter_compensation P lam hlam hU hS hSU a ha hpos
  obtain ⟨C₂, hC₂, hdebt⟩ := scaled_heatDebt_bound T ν q hν hq
  let K₀ : ℝ := 1 + C₂ / ε
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨K₀, C₁ * C₂, hK₀, mul_pos hC₁ hC₂, ?_⟩
  intro K hlarge
  have hK : 0 < K := hK₀.trans_le hlarge
  have hqK : 0 < q * K := mul_pos hq hK
  let v := scaledDebt (q * K) (heatDebt T ν K 0)
  have hv : ‖v‖ ≤ C₂ / K := hdebt K hK
  have hvsmall : ‖v‖ < ε := by
    apply hv.trans_lt
    apply (div_lt_iff₀ hK).mpr
    have hk' : C₂ / ε < K := by dsimp [K₀] at hlarge; linarith
    have ht := (div_lt_iff₀ hε).mp hk'
    simpa only [mul_comm] using ht
  obtain ⟨c, V, hV, hSV, hVU, hc, hspec⟩ := hsolve v hvsmall
  refine ⟨c, V, hV, hSV, hVU, hc, ?_⟩
  intro η hη
  have hs := hspec η hη
  have hcost : C₁ * ‖v‖ ≤ C₁ * C₂ / K := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hv hC₁.le
  have hmoment : momentMap P lam (c η) = normalizedDebt (q * K) (a η) (heatDebt T ν K 0) := by
    rw [normalizedDebt_eq]
    exact hs.1
  have hexact := physicalMoments_cancel P lam (q * K) (a η) hqK
    (hpos η (hSU hη)) (c η) (heatDebt T ν K 0) hmoment
  refine ⟨?_, hs.2.1.trans hcost, hs.2.2.1.trans hcost,
    hs.2.2.2.1.mono hcost, ?_⟩
  · rwa [heatDebt_independent T ν hK η]
  · intro X hX
    exact hs.2.2.2.2 (X / (q * K)) (div_pos hX hqK)

/-- All three physical moment changes are genuine integrable functions. -/
theorem physicalMoments_integrable (P : Patch) (lam R a : ℝ) (hR : 0 < R) (c : Coeff) :
    Integrable (fun X => ((physicalProfile P lam R a c X) ^ 2 -
      (cleanProfile lam R a X) ^ 2) / X) ∧
    Integrable (fun X => (physicalProfile P lam R a c X) ^ 2 -
      (cleanProfile lam R a X) ^ 2) ∧
    Integrable (fun X => Real.sqrt (2 * X) *
      (physicalProfile P lam R a c X - cleanProfile lam R a X)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (integrable_comp_mul_left_iff _ hR.ne').mp
    simp only [pressure_density_rescale P lam R a hR c]
    exact (weightedChange_integrable P lam c (-1)).const_mul _
  · apply (integrable_comp_mul_left_iff _ hR.ne').mp
    simp only [energy_density_rescale P lam R a hR c]
    exact (weightedChange_integrable P lam c 0).const_mul _
  · apply (integrable_comp_mul_left_iff _ hR.ne').mp
    simp only [angular_density_rescale P lam R a hR c]
    exact (weighted_correction_integrable P (1 / 2) c).const_mul _

theorem physicalProfile_eq_clean_of_nonpos (P : Patch) (lam R a : ℝ) (hR : 0 < R)
    (c : Coeff) {X : ℝ} (hX : X ≤ 0) :
    physicalProfile P lam R a c X = cleanProfile lam R a X := by
  apply physicalProfile_eq_clean_outside
  intro hx
  have hdiv := div_nonpos_of_nonpos_of_nonneg hX hR.le
  linarith [hx.1, P.left_pos]

/-- The whole-line definitions equal the usual positive-radius moment integrals. -/
theorem physicalMoments_positive_radius (P : Patch) (lam R a : ℝ) (hR : 0 < R) (c : Coeff) :
    physicalMoments P lam R a c =
      ![∫ X in Ioi 0, ((physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2) / X,
        ∫ X in Ioi 0, (physicalProfile P lam R a c X) ^ 2 - (cleanProfile lam R a X) ^ 2,
        ∫ X in Ioi 0, Real.sqrt (2 * X) *
          (physicalProfile P lam R a c X - cleanProfile lam R a X)] := by
  ext i
  fin_cases i <;> symm <;>
    apply setIntegral_eq_integral_of_forall_compl_eq_zero <;>
    intro X hX <;>
    rw [physicalProfile_eq_clean_of_nonpos P lam R a hR c (le_of_not_gt hX)] <;> simp

/-- A reserved patch ending before the heat switch has no overlap with the
actual heat perturbation on positive radii. -/
theorem patch_heat_disjoint (P : Patch) (lam q K a h ν : ℝ)
    (hq : 0 < q) (hK : 0 < K) (hpatch : q * P.right ≤ 1)
    (c : Coeff) (E : ℝ → ℝ) {X : ℝ} (hX : 0 < X) :
    (physicalProfile P lam (q * K) a c X - cleanProfile lam (q * K) a X) *
      HeatTailEdit.change E h ν K X = 0 := by
  by_cases hXK : X ≤ K
  · simp only [HeatTailEdit.change, HeatTailEdit.edit_before E h ν hK hX hXK,
      sub_self, mul_zero]
  · have hout : X / (q * K) ∉ Ioo P.left P.right := by
      intro hx
      have hl := (div_lt_iff₀ (mul_pos hq hK)).mp hx.2
      have hp := mul_le_mul_of_nonneg_right hpatch hK.le
      nlinarith
    rw [physicalProfile_eq_clean_outside P lam (q * K) a c X hout, sub_self, zero_mul]

theorem square_change_add_of_disjoint (b p t : ℝ) (hpt : p * t = 0) :
    (b + p + t) ^ 2 - b ^ 2 = ((b + p) ^ 2 - b ^ 2) + ((b + t) ^ 2 - b ^ 2) := by
  nlinarith

/-- The constructed physical profile is jointly smooth in the parameter and
positive radius, whenever the amplitude and solved coefficients are smooth. -/
theorem physicalProfile_family_contDiffOn (P : Patch) (lam R : ℝ) (hR : 0 < R)
    {U : Set ℝ} {a : ℝ → ℝ} {c : ℝ → Coeff}
    (ha : ContDiffOn ℝ ∞ a U) (hc : ContDiffOn ℝ ∞ c U) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => physicalProfile P lam R (a z.1) (c z.1) z.2) (U ×ˢ Ioi 0) := by
  have ha' : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => a z.1) (U ×ˢ Ioi 0) :=
    ha.comp contDiffOn_fst (fun z hz => hz.1)
  have hb : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => baseProfile lam (z.2 / R)) (U ×ˢ Ioi 0) := by
    intro z hz
    exact ((Real.contDiffAt_rpow_const_of_ne (div_pos hz.2 hR).ne').comp z
      (contDiffAt_snd.div_const R)).contDiffWithinAt
  have hr : ContDiffOn ℝ ∞
      (fun z : ℝ × ℝ => correction P (c z.1) (z.2 / R)) (U ×ˢ Ioi 0) :=
    (correction_family_contDiffOn P hc).comp
      (contDiffOn_fst.prodMk (contDiffOn_snd.div_const R)) (fun z hz => ⟨hz.1, mem_univ _⟩)
  exact ha'.mul (hb.add hr)

end NavierStokes.TerminalCompensation
