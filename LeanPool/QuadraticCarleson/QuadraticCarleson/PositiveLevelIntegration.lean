/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveEndpointOptimization
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Measurable magnitude levels and endpoint-weight integration

This module supplies the measure-theoretic bridge from the scalar estimates
in `PositiveEndpointOptimization` to the sums over the paper's magnitude sets
`F_k`. Extended nonnegative integrals are used throughout, so no integrability
or finiteness hypothesis is needed.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace QuadraticCarleson
namespace PositiveLevelIntegration

open PositiveEndpointOptimization


/-- The paper's magnitude set `F_k`, for an arbitrary threshold sequence. -/
def magnitudeLevelSet {α : Type*} (A : ℕ → ℝ) (f : α → ℂ) (k : ℕ) : Set α :=
  {x | InMagnitudeLevel A k ‖f x‖}

@[simp] theorem mem_magnitudeLevelSet {α : Type*} {A : ℕ → ℝ}
    {f : α → ℂ} {k : ℕ} {x : α} :
    x ∈ magnitudeLevelSet A f k ↔ InMagnitudeLevel A k ‖f x‖ :=
  Iff.rfl

theorem measurableSet_magnitudeLevelSet
    {α : Type*} [MeasurableSpace α] {A : ℕ → ℝ} {f : α → ℂ}
    (hf : Measurable f) (k : ℕ) : MeasurableSet (magnitudeLevelSet A f k) := by
  by_cases hk : k = 0
  · subst k
    simpa [magnitudeLevelSet, InMagnitudeLevel] using
      (measurableSet_le hf.norm (measurable_const : Measurable fun _ : α ↦ A 0))
  · simp only [magnitudeLevelSet, InMagnitudeLevel, hk]
    exact (measurableSet_lt measurable_const hf.norm).inter
      (measurableSet_le hf.norm measurable_const)

/-- Distinct magnitude bands are disjoint when the thresholds are strictly
increasing. -/
theorem magnitudeLevelSet_disjoint
    {α : Type*} {A : ℕ → ℝ} (hA : StrictMono A) (f : α → ℂ)
    {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (magnitudeLevelSet A f k) (magnitudeLevelSet A f l) := by
  apply Set.disjoint_left.2
  intro x hxk hxl
  simp only [mem_magnitudeLevelSet] at hxk hxl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hl0 : l ≠ 0 := by omega
    have hlower := hxl.lower hl0
    by_cases hk0 : k = 0
    · subst k
      simp [InMagnitudeLevel] at hxk
      have hAle : A 0 ≤ A (l - 1) := by
        exact (hA.monotone (by omega : 0 ≤ l - 1))
      linarith
    · have hkupper : ‖f x‖ ≤ A k := by
        have hxk' : A (k - 1) < ‖f x‖ ∧ ‖f x‖ ≤ A k := by
          simpa [InMagnitudeLevel, hk0] using hxk
        exact hxk'.2
      have hAle : A k ≤ A (l - 1) := hA.monotone (by omega)
      linarith
  · have hk0 : k ≠ 0 := by omega
    have hkl' : l ≠ k := Ne.symm hkl
    have hklower := hxk.lower hk0
    by_cases hl0 : l = 0
    · subst l
      simp [InMagnitudeLevel] at hxl
      have hAle : A 0 ≤ A (k - 1) := hA.monotone (by omega)
      linarith
    · have hlupper : ‖f x‖ ≤ A l := by
        have hxl' : A (l - 1) < ‖f x‖ ∧ ‖f x‖ ≤ A l := by
          simpa [InMagnitudeLevel, hl0] using hxl
        exact hxl'.2
      have hAle : A l ≤ A (k - 1) := hA.monotone (by omega)
      linarith

/-- A nonnegative unbounded threshold sequence covers every magnitude by a
unique level. -/
theorem exists_unique_mem_magnitudeLevelSet
    {α : Type*} {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k) (f : α → ℂ) (x : α) :
    ∃! k : ℕ, x ∈ magnitudeLevelSet A f k := by
  let p : ℕ → Prop := fun k ↦ ‖f x‖ ≤ A k
  have hex : ∃ k, p k := hcofinal ‖f x‖ (norm_nonneg _)
  let k := Nat.find hex
  have hkupper : ‖f x‖ ≤ A k := Nat.find_spec hex
  have hkmem : x ∈ magnitudeLevelSet A f k := by
    simp only [mem_magnitudeLevelSet]
    by_cases hk0 : k = 0
    · rw [InMagnitudeLevel, ite_eq_left hk0]
      have hkupper0 : ‖f x‖ ≤ A 0 := by simpa [hk0] using hkupper
      exact ⟨norm_nonneg _, hkupper0⟩
    · rw [InMagnitudeLevel, ite_eq_right hk0]
      refine ⟨lt_of_not_ge ?_, hkupper⟩
      intro hle
      exact Nat.find_min hex (show k - 1 < k by omega) hle
  refine ⟨k, hkmem, ?_⟩
  intro l hlmem
  by_contra hne
  exact Set.disjoint_left.1 (magnitudeLevelSet_disjoint hA f (Ne.symm hne)) hkmem hlmem

theorem iUnion_magnitudeLevelSet_eq_univ
    {α : Type*} {A : ℕ → ℝ} (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k) (f : α → ℂ) :
    ⋃ k : ℕ, magnitudeLevelSet A f k = Set.univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨k, hk, -⟩ := exists_unique_mem_magnitudeLevelSet hA hcofinal f x
  exact ⟨k, hk⟩

theorem strictMono_fullAmplitude : StrictMono fullAmplitude := by
  intro k l hkl
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by norm_num) hkl)
    (by linarith [half_lt_log_two])

theorem strictMono_lacunaryScale : StrictMono lacunaryScale := by
  intro k l hkl
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right₀ (by norm_num) hkl)
    (by linarith [half_lt_log_two])

theorem strictMono_lacunaryAmplitude : StrictMono lacunaryAmplitude := by
  intro k l hkl
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left (strictMono_lacunaryScale hkl)
    (by linarith [half_lt_log_two])

theorem dyadicScale_le_fullAmplitude (k : ℕ) :
    dyadicScale k ≤ fullAmplitude k := by
  rw [fullAmplitude_eq_two_pow, dyadicScale]
  rw [pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  have hk : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
    simpa [dyadicScale] using dyadicScale_ge_nat_succ k
  have hreal : (k : ℝ) ≤ (2 : ℝ) ^ k := by linarith
  exact_mod_cast hreal

theorem fullAmplitude_cofinal (t : ℝ) :
    ∃ k, t ≤ fullAmplitude k := by
  obtain ⟨k, hk⟩ := exists_nat_ge t
  refine ⟨k, hk.trans ?_⟩
  calc
    (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    _ ≤ dyadicScale k := dyadicScale_ge_nat_succ k
    _ ≤ fullAmplitude k := dyadicScale_le_fullAmplitude k

theorem lacunaryScale_le_lacunaryAmplitude (k : ℕ) :
    lacunaryScale k ≤ lacunaryAmplitude k := by
  rw [lacunaryAmplitude]
  rw [← Real.exp_log (lacunaryScale_pos k)]
  apply Real.exp_le_exp.mpr
  simp only [lacunaryScale, Real.log_exp]
  exact mul_le_mul_of_nonneg_left (dyadicScale_le_fullAmplitude k)
    (by linarith [half_lt_log_two])

theorem lacunaryAmplitude_cofinal (t : ℝ) :
    ∃ k, t ≤ lacunaryAmplitude k := by
  obtain ⟨k, hk⟩ := fullAmplitude_cofinal t
  refine ⟨k, hk.trans ?_⟩
  change lacunaryScale k ≤ lacunaryAmplitude k
  exact lacunaryScale_le_lacunaryAmplitude k

theorem fullMagnitudeLevels_cover {α : Type*} (f : α → ℂ) :
    ⋃ k : ℕ, magnitudeLevelSet fullAmplitude f k = Set.univ :=
  iUnion_magnitudeLevelSet_eq_univ
    strictMono_fullAmplitude (fun t _ ↦ fullAmplitude_cofinal t) f

theorem lacunaryMagnitudeLevels_cover {α : Type*} (f : α → ℂ) :
    ⋃ k : ℕ, magnitudeLevelSet lacunaryAmplitude f k = Set.univ :=
  iUnion_magnitudeLevelSet_eq_univ
    strictMono_lacunaryAmplitude (fun t _ ↦ lacunaryAmplitude_cofinal t) f

/-- Actual full-operator magnitude levels for the paper's optimized `A_k`. -/
def fullMagnitudeLevelSet {α : Type*} (f : α → ℂ) (k : ℕ) : Set α :=
  magnitudeLevelSet fullAmplitude f k

/-- Actual lacunary magnitude levels for `A_k = 2^(2^(2^k))`. -/
def lacunaryMagnitudeLevelSet {α : Type*} (f : α → ℂ) (k : ℕ) : Set α :=
  magnitudeLevelSet lacunaryAmplitude f k

theorem measurableSet_fullMagnitudeLevelSet
    {α : Type*} [MeasurableSpace α] {f : α → ℂ} (hf : Measurable f) (k : ℕ) :
    MeasurableSet (fullMagnitudeLevelSet f k) :=
  measurableSet_magnitudeLevelSet hf k

theorem measurableSet_lacunaryMagnitudeLevelSet
    {α : Type*} [MeasurableSpace α] {f : α → ℂ} (hf : Measurable f) (k : ℕ) :
    MeasurableSet (lacunaryMagnitudeLevelSet f k) :=
  measurableSet_magnitudeLevelSet hf k

theorem fullMagnitudeLevelSet_disjoint
    {α : Type*} (f : α → ℂ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (fullMagnitudeLevelSet f k) (fullMagnitudeLevelSet f l) :=
  magnitudeLevelSet_disjoint strictMono_fullAmplitude f hkl

theorem lacunaryMagnitudeLevelSet_disjoint
    {α : Type*} (f : α → ℂ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (lacunaryMagnitudeLevelSet f k) (lacunaryMagnitudeLevelSet f l) :=
  magnitudeLevelSet_disjoint strictMono_lacunaryAmplitude f hkl

theorem iUnion_fullMagnitudeLevelSet_eq_univ {α : Type*} (f : α → ℂ) :
    ⋃ k : ℕ, fullMagnitudeLevelSet f k = Set.univ :=
  fullMagnitudeLevels_cover f

theorem iUnion_lacunaryMagnitudeLevelSet_eq_univ {α : Type*} (f : α → ℂ) :
    ⋃ k : ℕ, lacunaryMagnitudeLevelSet f k = Set.univ :=
  lacunaryMagnitudeLevels_cover f

theorem measurable_paperLog (n : ℕ) : Measurable (paperLog n) := by
  induction n with
  | zero =>
      change Measurable id
      exact measurable_id
  | succ n ih =>
      change Measurable (fun t ↦ Real.log (10 + paperLog n t))
      exact Real.measurable_log.comp (measurable_const.add ih)

/-- The contribution of one magnitude level to an extended integral. -/
noncomputable def levelIntegrand {α : Type*} (A weight : ℕ → ℝ) (f : α → ℂ)
    (k : ℕ) : α → ℝ≥0∞ :=
  (magnitudeLevelSet A f k).indicator
    (fun x ↦ ENNReal.ofReal (weight k * ‖f x‖))

theorem measurable_levelIntegrand
    {α : Type*} [MeasurableSpace α] {A weight : ℕ → ℝ} {f : α → ℂ}
    (hf : Measurable f) (k : ℕ) : Measurable (levelIntegrand A weight f k) := by
  apply Measurable.indicator
  · exact (measurable_const.mul hf.norm).ennreal_ofReal
  · exact measurableSet_magnitudeLevelSet hf k

/-- Extended mass of one level, with its numerical endpoint weight included. -/
noncomputable def levelLIntegral
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A weight : ℕ → ℝ) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, levelIntegrand A weight f k x ∂μ

/-- The unweighted `L¹` mass `∫_{F_k} |f|`, interpreted as an extended
nonnegative integral. -/
noncomputable def magnitudeLevelL1Mass
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : ℕ → ℝ) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖ ∂μ

theorem levelLIntegral_eq_weight_mul_mass
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A weight : ℕ → ℝ} {f : α → ℂ} (hf : Measurable f)
    (hweight : ∀ k, 0 ≤ weight k) (k : ℕ) :
    levelLIntegral μ A weight f k =
      ENNReal.ofReal (weight k) * magnitudeLevelL1Mass μ A f k := by
  rw [levelLIntegral, levelIntegrand,
    lintegral_indicator (measurableSet_magnitudeLevelSet hf k)]
  simp_rw [ENNReal.ofReal_mul (hweight k)]
  rw [lintegral_const_mul]
  · rfl
  exact hf.norm.ennreal_ofReal

/-- Generic disjoint-level integration principle. It is a direct application
of Tonelli's theorem for nonnegative series and therefore needs no finiteness
or integrability assumption. -/
theorem tsum_levelLIntegral_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A weight : ℕ → ℝ} {f : α → ℂ} (hf : Measurable f)
     (hA : StrictMono A)
    (hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ k, t ≤ A k)
    {G : ℝ → ℝ}
    (hpoint : ∀ k t, InMagnitudeLevel A k t → weight k * t ≤ G t) :
    ∑' k : ℕ, levelLIntegral μ A weight f k ≤
      ∫⁻ x, ENNReal.ofReal (G ‖f x‖) ∂μ := by
  change (∑' k : ℕ, ∫⁻ x, levelIntegrand A weight f k x ∂μ) ≤ _
  rw [← lintegral_tsum (fun k ↦ (measurable_levelIntegrand hf k).aemeasurable)]
  apply lintegral_mono
  intro x
  change (∑' i : ℕ, levelIntegrand A weight f i x) ≤ ENNReal.ofReal (G ‖f x‖)
  obtain ⟨k, hk, huniq⟩ :=
    exists_unique_mem_magnitudeLevelSet hA hcofinal f x
  rw [tsum_eq_single k]
  · simp only [levelIntegrand, Set.indicator_of_mem hk]
    exact ENNReal.ofReal_le_ofReal (hpoint k ‖f x‖ hk)
  · intro l hl
    simp only [levelIntegrand]
    rw [Set.indicator_of_notMem]
    intro hlmem
    exact hl (huniq l hlmem)

/-- The weighted extended mass of the full-operator level `F_k`. -/
noncomputable def fullLevelLIntegral
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (C : ℝ) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  levelLIntegral μ fullAmplitude (fullCutoff C) f k

/-- Integrated full-endpoint optimization:
`Σ B_k ∫_{F_k}|f| ≲ ∫ |f| log₁|f|`, in extended-integral form. -/
theorem tsum_fullLevelLIntegral_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) :
    ∑' k : ℕ, fullLevelLIntegral μ C f k ≤
      ∫⁻ x, ENNReal.ofReal (4 * C * (‖f x‖ * paperLog 1 ‖f x‖)) ∂μ := by
  change (∑' k : ℕ, levelLIntegral μ fullAmplitude (fullCutoff C) f k) ≤ _
  exact tsum_levelLIntegral_le (A := fullAmplitude) (weight := fullCutoff C)
      (G := fun t ↦ 4 * C * (t * paperLog 1 t))
      μ hf strictMono_fullAmplitude (fun t _ ↦ fullAmplitude_cofinal t)
      (by
        intro k t ht
        exact fullWeightedLevel_le_orlicz_all hC ht)

theorem tsum_full_weight_mul_levelMass_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) :
    ∑' k : ℕ, ENNReal.ofReal (fullCutoff C k) *
        magnitudeLevelL1Mass μ fullAmplitude f k ≤
      ∫⁻ x, ENNReal.ofReal (4 * C * (‖f x‖ * paperLog 1 ‖f x‖)) ∂μ := by
  have hmain := tsum_fullLevelLIntegral_le_orlicz μ hC hf
  rw [show (∑' k : ℕ, ENNReal.ofReal (fullCutoff C k) *
      magnitudeLevelL1Mass μ fullAmplitude f k) =
      ∑' k : ℕ, fullLevelLIntegral μ C f k by
    apply tsum_congr
    intro k
    symm
    exact levelLIntegral_eq_weight_mul_mass μ hf
      (fun j ↦ mul_nonneg hC (dyadicScale_pos j).le) k]
  exact hmain

theorem one_le_paperLog_succ (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ paperLog (n + 1) t := by
  rw [paperLog_succ, Real.le_log_iff_exp_le
    (by linarith [paperLog_nonnegative n ht])]
  have hexp : Real.exp 1 < 10 := Real.exp_one_lt_d9.trans (by norm_num)
  exact hexp.le.trans (by linarith [paperLog_nonnegative n ht])

/-- The constant controlling the small magnitude levels in the lacunary level decomposition. -/
noncomputable def lacunarySmallLevelConstant (C : ℝ) : ℝ :=
  paperLog 1 7 * (32 * (paperLog 1 C + 1)) ^ 2

/-- The level-integration constant for the lacunary high-frequency contribution. -/
noncomputable def lacunaryHighLevelConstant (C : ℝ) : ℝ :=
  lacunarySmallLevelConstant C + 64 * (paperLog 1 C + 1) ^ 2

/-- The level-integration constant for the lacunary low-frequency contribution. -/
noncomputable def lacunaryLowLevelConstant (C : ℝ) : ℝ :=
  lacunarySmallLevelConstant C + 128 * (paperLog 1 C + 1) ^ 2

theorem lacunarySmallLevelConstant_nonneg {C : ℝ} :
    0 ≤ lacunarySmallLevelConstant C := by
  exact mul_nonneg (paperLog_nonnegative 1 (by norm_num)) (sq_nonneg _)

theorem one_le_lacunaryEndpointFactor {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ paperLog 2 t ^ 2 * paperLog 4 t := by
  have h2 := one_le_paperLog_succ 1 ht
  have h4 := one_le_paperLog_succ 3 ht
  nlinarith [sq_nonneg (paperLog 2 t - 1),
    mul_le_mul_of_nonneg_right (show 1 ≤ paperLog 2 t ^ 2 by nlinarith)
      (zero_le_one.trans h4)]

/-- All lacunary high-level weights, including the first two levels, are
absorbed by `L(log₂ L)^2`. -/
theorem lacunaryHighWeight_le_orlicz_all
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C) (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    paperLog 1 (lacunaryCutoff C k) ^ 2 * t ≤
      lacunaryHighLevelConstant C * (t * paperLog 2 t ^ 2) := by
  have ht0 := ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le)
  by_cases hk : 2 ≤ k
  · have hmain := lacunaryHighWeight_le_orlicz_of_mem hC hk ht
    have hend0 : 0 ≤ t * paperLog 2 t ^ 2 := mul_nonneg ht0 (sq_nonneg _)
    exact hmain.trans (mul_le_mul_of_nonneg_right
      (show 64 * (paperLog 1 C + 1) ^ 2 ≤ lacunaryHighLevelConstant C by
        dsimp [lacunaryHighLevelConstant]
        exact le_add_of_nonneg_left (lacunarySmallLevelConstant_nonneg)) hend0)
  · have hsmall := lacunaryLowWeight_smallLevel_le_L1 (k := k) hC (by omega) ht0
    have hindex := one_le_paperLog_one (by positivity : 0 ≤ (k : ℝ) + 2)
    have hterm0 : 0 ≤ paperLog 1 (lacunaryCutoff C k) ^ 2 * t :=
      mul_nonneg (sq_nonneg _) ht0
    have hdrop : paperLog 1 (lacunaryCutoff C k) ^ 2 * t ≤
        paperLog 1 ((k : ℝ) + 2) * paperLog 1 (lacunaryCutoff C k) ^ 2 * t := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hindex hterm0
    have hfactor : 1 ≤ paperLog 2 t ^ 2 := by
      have := one_le_paperLog_succ 1 ht0
      nlinarith
    calc
      paperLog 1 (lacunaryCutoff C k) ^ 2 * t
          ≤ lacunarySmallLevelConstant C * t := hdrop.trans hsmall
      _ ≤ lacunarySmallLevelConstant C * (t * paperLog 2 t ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor ht0)
          (lacunarySmallLevelConstant_nonneg)
      _ ≤ lacunaryHighLevelConstant C * (t * paperLog 2 t ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg _))
        · positivity

/-- All lacunary low-level weights, including the first six levels, are
absorbed by the paper's complete endpoint weight. -/
theorem lacunaryLowWeight_le_orlicz_all
    {C t : ℝ} {k : ℕ} (hC : 0 ≤ C) (ht : InMagnitudeLevel lacunaryAmplitude k t) :
    paperLog 1 ((k : ℝ) + 2) * paperLog 1 (lacunaryCutoff C k) ^ 2 * t ≤
      lacunaryLowLevelConstant C *
        (t * paperLog 2 t ^ 2 * paperLog 4 t) := by
  have ht0 := ht.nonneg (fun j ↦ (lacunaryAmplitude_pos j).le)
  have hend0 : 0 ≤ t * paperLog 2 t ^ 2 * paperLog 4 t :=
    mul_nonneg (mul_nonneg ht0 (sq_nonneg _)) (paperLog_nonnegative 4 ht0)
  by_cases hk : 6 ≤ k
  · have hmain := lacunaryLowWeight_le_orlicz_of_mem hC hk ht
    exact hmain.trans (mul_le_mul_of_nonneg_right
      (show 128 * (paperLog 1 C + 1) ^ 2 ≤ lacunaryLowLevelConstant C by
        dsimp [lacunaryLowLevelConstant]
        exact le_add_of_nonneg_left (lacunarySmallLevelConstant_nonneg)) hend0)
  · have hsmall := lacunaryLowWeight_smallLevel_le_L1 (k := k) hC (by omega) ht0
    have hfactor := one_le_lacunaryEndpointFactor ht0
    calc
      paperLog 1 ((k : ℝ) + 2) * paperLog 1 (lacunaryCutoff C k) ^ 2 * t
          ≤ lacunarySmallLevelConstant C * t := hsmall
      _ ≤ lacunarySmallLevelConstant C *
          (t * paperLog 2 t ^ 2 * paperLog 4 t) := by
        exact mul_le_mul_of_nonneg_left
          (by
            have := mul_le_mul_of_nonneg_left hfactor ht0
            simpa only [mul_one, mul_assoc] using this)
          (lacunarySmallLevelConstant_nonneg)
      _ ≤ lacunaryLowLevelConstant C *
          (t * paperLog 2 t ^ 2 * paperLog 4 t) := by
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg _))) hend0

/-- The lacunary level integral weighted by the squared logarithm of the high cutoff. -/
noncomputable def lacunaryHighLevelLIntegral
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (C : ℝ) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  levelLIntegral μ lacunaryAmplitude
    (fun k ↦ paperLog 1 (lacunaryCutoff C k) ^ 2) f k

/-- The lacunary level integral with the additional logarithmic weight for the low contribution. -/
noncomputable def lacunaryLowLevelLIntegral
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (C : ℝ) (f : α → ℂ) (k : ℕ) : ℝ≥0∞ :=
  levelLIntegral μ lacunaryAmplitude
    (fun k ↦ paperLog 1 ((k : ℝ) + 2) *
      paperLog 1 (lacunaryCutoff C k) ^ 2) f k

theorem tsum_lacunaryHighLevelLIntegral_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) :
    ∑' k : ℕ, lacunaryHighLevelLIntegral μ C f k ≤
      ∫⁻ x, ENNReal.ofReal
        (lacunaryHighLevelConstant C * (‖f x‖ * paperLog 2 ‖f x‖ ^ 2)) ∂μ := by
  change (∑' k : ℕ, levelLIntegral μ lacunaryAmplitude
    (fun k ↦ paperLog 1 (lacunaryCutoff C k) ^ 2) f k) ≤ _
  exact tsum_levelLIntegral_le (A := lacunaryAmplitude)
      (weight := fun k ↦ paperLog 1 (lacunaryCutoff C k) ^ 2)
      (G := fun t ↦ lacunaryHighLevelConstant C * (t * paperLog 2 t ^ 2))
      μ hf strictMono_lacunaryAmplitude
      (fun t _ ↦ lacunaryAmplitude_cofinal t)
      (by
        intro k t ht
        exact lacunaryHighWeight_le_orlicz_all hC ht)

theorem tsum_lacunaryHighWeight_mul_levelMass_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) :
    ∑' k : ℕ, ENNReal.ofReal (paperLog 1 (lacunaryCutoff C k) ^ 2) *
        magnitudeLevelL1Mass μ lacunaryAmplitude f k ≤
      ∫⁻ x, ENNReal.ofReal
        (lacunaryHighLevelConstant C * (‖f x‖ * paperLog 2 ‖f x‖ ^ 2)) ∂μ := by
  have hmain := tsum_lacunaryHighLevelLIntegral_le_orlicz μ hC hf
  rw [show (∑' k : ℕ, ENNReal.ofReal (paperLog 1 (lacunaryCutoff C k) ^ 2) *
      magnitudeLevelL1Mass μ lacunaryAmplitude f k) =
      ∑' k : ℕ, lacunaryHighLevelLIntegral μ C f k by
    apply tsum_congr
    intro k
    symm
    exact levelLIntegral_eq_weight_mul_mass μ hf (fun _ ↦ sq_nonneg _) k]
  exact hmain

/-- Integrated lacunary low-endpoint optimization, including all initial
levels and requiring no integrability assumption. -/
theorem tsum_lacunaryLowLevelLIntegral_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) :
    ∑' k : ℕ, lacunaryLowLevelLIntegral μ C f k ≤
      ∫⁻ x, ENNReal.ofReal (lacunaryLowLevelConstant C *
        (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖)) ∂μ := by
  change (∑' k : ℕ, levelLIntegral μ lacunaryAmplitude
    (fun k ↦ paperLog 1 ((k : ℝ) + 2) *
      paperLog 1 (lacunaryCutoff C k) ^ 2) f k) ≤ _
  exact tsum_levelLIntegral_le (A := lacunaryAmplitude)
      (weight := fun k ↦ paperLog 1 ((k : ℝ) + 2) *
        paperLog 1 (lacunaryCutoff C k) ^ 2)
      (G := fun t ↦ lacunaryLowLevelConstant C *
        (t * paperLog 2 t ^ 2 * paperLog 4 t))
      μ hf strictMono_lacunaryAmplitude
      (fun t _ ↦ lacunaryAmplitude_cofinal t)
      (by
        intro k t ht
        exact lacunaryLowWeight_le_orlicz_all hC ht)

theorem tsum_lacunaryLowWeight_mul_levelMass_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) :
    ∑' k : ℕ, ENNReal.ofReal (paperLog 1 ((k : ℝ) + 2) *
        paperLog 1 (lacunaryCutoff C k) ^ 2) *
        magnitudeLevelL1Mass μ lacunaryAmplitude f k ≤
      ∫⁻ x, ENNReal.ofReal (lacunaryLowLevelConstant C *
        (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖)) ∂μ := by
  have hmain := tsum_lacunaryLowLevelLIntegral_le_orlicz μ hC hf
  rw [show (∑' k : ℕ, ENNReal.ofReal (paperLog 1 ((k : ℝ) + 2) *
      paperLog 1 (lacunaryCutoff C k) ^ 2) *
      magnitudeLevelL1Mass μ lacunaryAmplitude f k) =
      ∑' k : ℕ, lacunaryLowLevelLIntegral μ C f k by
    apply tsum_congr
    intro k
    symm
    apply levelLIntegral_eq_weight_mul_mass μ hf
    intro j
    exact mul_nonneg
      (paperLog_nonnegative 1 (by positivity : (0 : ℝ) ≤ (j : ℝ) + 2)) (sq_nonneg _)]
  exact hmain

/-- Every finite partial sum is bounded by the same full endpoint integral. -/
theorem sum_range_fullLevelLIntegral_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) (N : ℕ) :
    ∑ k ∈ Finset.range N, fullLevelLIntegral μ C f k ≤
      ∫⁻ x, ENNReal.ofReal (4 * C * (‖f x‖ * paperLog 1 ‖f x‖)) ∂μ := by
  exact (ENNReal.summable.sum_le_tsum (Finset.range N) (fun _ _ ↦ bot_le)).trans
    (tsum_fullLevelLIntegral_le_orlicz μ hC hf)

theorem sum_range_lacunaryHighLevelLIntegral_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) (N : ℕ) :
    ∑ k ∈ Finset.range N, lacunaryHighLevelLIntegral μ C f k ≤
      ∫⁻ x, ENNReal.ofReal
        (lacunaryHighLevelConstant C * (‖f x‖ * paperLog 2 ‖f x‖ ^ 2)) ∂μ := by
  exact (ENNReal.summable.sum_le_tsum (Finset.range N) (fun _ _ ↦ bot_le)).trans
    (tsum_lacunaryHighLevelLIntegral_le_orlicz μ hC hf)

theorem sum_range_lacunaryLowLevelLIntegral_le_orlicz
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {C : ℝ} (hC : 0 ≤ C) {f : α → ℂ} (hf : Measurable f) (N : ℕ) :
    ∑ k ∈ Finset.range N, lacunaryLowLevelLIntegral μ C f k ≤
      ∫⁻ x, ENNReal.ofReal (lacunaryLowLevelConstant C *
        (‖f x‖ * paperLog 2 ‖f x‖ ^ 2 * paperLog 4 ‖f x‖)) ∂μ := by
  exact (ENNReal.summable.sum_le_tsum (Finset.range N) (fun _ _ ↦ bot_le)).trans
    (tsum_lacunaryLowLevelLIntegral_le_orlicz μ hC hf)

end PositiveLevelIntegration
end QuadraticCarleson
