/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ATensorJets
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCoefficientWords
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FiniteSpatialWordBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SMatRegularity
public import Mathlib.Analysis.Matrix.Normed

/-! # TMaterial Spatial Coefficient

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory AVenhance
open AVenhance.Infra.Section4
/-- Equip the spatial matrix space with its coordinate supremum norm. -/
local instance avInfraSection5ContractsTMaterialSpatialCoefficientNormedAddCommGroup1 :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℝ) := Matrix.normedAddCommGroup
/-- Real normed-space structure for spatial matrices with the coordinate supremum norm. -/
local instance avInfraSection5ContractsTMaterialSpatialCoefficientNormedSpace2 : NormedSpace ℝ
    (Matrix (Fin 2) (Fin 2) ℝ) := Matrix.normedSpace
namespace AVenhance.Infra.Section5.Contracts

/-- The all-suborder flow budget `40 n! L^n` used for the quadratic Leibniz estimate. -/
def TMaterialSpatialCoefficient.tMaterialFlowBudget (L : ℝ) (n : ℕ) : ℝ := 40 * (n.factorial : ℝ)
    * L ^ n

theorem TMaterialSpatialCoefficient.tMaterialFlowBudget_le {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : n ≤
    2) :
    TMaterialSpatialCoefficient.tMaterialFlowBudget L n ≤ 80 * L ^ n := by
  unfold TMaterialSpatialCoefficient.tMaterialFlowBudget
  have hf : (n.factorial : ℝ) ≤ 2 := by
    have hh := Nat.factorial_le hn
    norm_num at hh
    exact_mod_cast hh
  have hp : 0 ≤ L ^ n := (pow_pos hL n).le
  nlinarith only [hf, hp]

/-- Every ordered Leibniz term of the quadratic budget is `≤ 6480 L^k`. -/
theorem TMaterialSpatialCoefficient.tMaterial_split_term_le {L : ℝ} (hL : 0 < L) {w : List (Fin 2)}
    (hw : w.length ≤ 2) {p : List (Fin 2) × List (Fin 2)} (hp : p ∈ iterateSpatialSplits w) :
    TMaterialSpatialCoefficient.tMaterialFlowBudget L p.1.length *
      (TMaterialSpatialCoefficient.tMaterialFlowBudget L p.2.length + if p.2 = [] then 1 else 0) ≤
          6480 * L ^ w.length := by
  have hord := iterateSpatialSplits_orders w hp
  have ha : p.1.length ≤ 2 := by omega
  have hb : p.2.length ≤ 2 := by omega
  have hFa := TMaterialSpatialCoefficient.tMaterialFlowBudget_le hL ha
  have hFb := TMaterialSpatialCoefficient.tMaterialFlowBudget_le hL hb
  have hpa : 0 ≤ L ^ p.1.length := (pow_pos hL _).le
  have hpb : 0 ≤ L ^ p.2.length := (pow_pos hL _).le
  have hsum : TMaterialSpatialCoefficient.tMaterialFlowBudget L p.2.length + (if p.2 = [] then 1
      else 0) ≤
      81 * L ^ p.2.length := by
    by_cases h : p.2 = []
    · have hl : p.2.length = 0 := by rw [h]; rfl
      rw [ite_eq_left h, hl]
      simp only [TMaterialSpatialCoefficient.tMaterialFlowBudget, Nat.factorial_zero, pow_zero]
      norm_num
    · rw [ite_eq_right h, add_zero]
      linarith only [hFb, hpb]
  have hnn : 0 ≤ TMaterialSpatialCoefficient.tMaterialFlowBudget L p.1.length := by
    unfold TMaterialSpatialCoefficient.tMaterialFlowBudget; positivity
  calc
    _ ≤ (80 * L ^ p.1.length) * (81 * L ^ p.2.length) :=
      mul_le_mul hFa hsum (by
        by_cases h : p.2 = []
        · simp only [h, ite_true]; unfold TMaterialSpatialCoefficient.tMaterialFlowBudget;
            positivity
        · simp only [h, ite_false, add_zero]; unfold
            TMaterialSpatialCoefficient.tMaterialFlowBudget; positivity)
        (by positivity)
    _ = 6480 * L ^ (p.1.length + p.2.length) := by rw [pow_add]; ring
    _ = _ := by rw [hord]

theorem TMaterialSpatialCoefficient.tMaterial_budget_le {L K κ ν : ℝ} (hL : 0 < L) (hK : 0 ≤ K)
    (hκ : |κ| ≤ ν)
    {w : List (Fin 2)} (hw : w.length ≤ 2) :
    coarseCoeffWordBudget K κ (TMaterialSpatialCoefficient.tMaterialFlowBudget L) w ≤
      (160 * K + 103680 * (K + ν)) * L ^ w.length := by
  unfold coarseCoeffWordBudget
  have hsum : ((iterateSpatialSplits w).map (fun p =>
      TMaterialSpatialCoefficient.tMaterialFlowBudget L p.1.length *
        (TMaterialSpatialCoefficient.tMaterialFlowBudget L p.2.length + if p.2 = [] then 1 else
            0))).sum ≤
      25920 * L ^ w.length := by
    have h := List.sum_le_length_nsmul
      ((iterateSpatialSplits w).map (fun p =>
        TMaterialSpatialCoefficient.tMaterialFlowBudget L p.1.length *
          (TMaterialSpatialCoefficient.tMaterialFlowBudget L p.2.length + if p.2 = [] then 1 else
              0)))
      (6480 * L ^ w.length) (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact TMaterialSpatialCoefficient.tMaterial_split_term_le hL hw hp)
    rw [List.length_map, iterateSpatialSplits_length, nsmul_eq_mul] at h
    have h4 : ((2 ^ w.length : ℕ) : ℝ) ≤ 4 := by
      have : 2 ^ w.length ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hw
      exact_mod_cast this
    have hp : 0 ≤ 6480 * L ^ w.length := by positivity
    calc _ ≤ _ := h
      _ ≤ 4 * (6480 * L ^ w.length) := mul_le_mul_of_nonneg_right h4 hp
      _ = _ := by ring
  have hF := TMaterialSpatialCoefficient.tMaterialFlowBudget_le hL hw
  have hκ' : 4 * (K + |κ|) ≤ 4 * (K + ν) := by linarith only [hκ]
  have hν : 0 ≤ ν := (abs_nonneg _).trans hκ
  have hKν : 0 ≤ 4 * (K + ν) := by positivity
  have hpL : 0 ≤ L ^ w.length := (pow_pos hL _).le
  calc
    _ ≤ 2 * K * (80 * L ^ w.length) + (4 * (K + ν)) * (25920 * L ^ w.length) := by
      refine add_le_add (mul_le_mul_of_nonneg_left hF (by positivity)) ?_
      exact mul_le_mul hκ' hsum (le_trans (by
        have := List.sum_nonneg (l := (iterateSpatialSplits w).map (fun p =>
          TMaterialSpatialCoefficient.tMaterialFlowBudget L p.1.length *
            (TMaterialSpatialCoefficient.tMaterialFlowBudget L p.2.length + if p.2 = [] then 1
                else 0))) (by
          intro x hx
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
          unfold TMaterialSpatialCoefficient.tMaterialFlowBudget
          have h1 : (0 : ℝ) ≤ 40 * (p.1.length.factorial : ℝ) * L ^ p.1.length := by positivity
          have h2 : (0 : ℝ) ≤ 40 * (p.2.length.factorial : ℝ) * L ^ p.2.length +
              (if p.2 = [] then 1 else 0) := by
            split_ifs <;> positivity
          exact mul_nonneg h1 h2)
        exact this) le_rfl) (by positivity)
    _ = _ := by ring

/-- The actual forcing coefficient's spatial orders zero through two from
Kmat size, the molecular comparison `|κm| ≤ ν`, and the proved active flow jets (all suborders,
quadratic Leibniz budget). No time/material coefficient jet enters. -/
theorem tMaterial_coefficient_spatial_two {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m)
    {κm ν Q L : ℝ} (hκm : 0 < κm) (hν : 0 ≤ ν) (hQ : 0 ≤ Q) (hL : 0 < L)
    (hκν : |κm| ≤ ν)
    (hfreq : 2 ^ 10 / epsilon β I.Λ (m - 1) ≤ L)
    (hK : ∀ t i j, |I.Kmat κm m t i j| ≤ Q * ν)
    (i j : Fin 2) (α : List (Fin 2)) (hα : α.length ≤ 2) (z : AmnrSpace) :
    |amnrWord (fun y => streamVel (Φ (m - 1)) y.1 y.2) (α.map some)
      (amnrTemperatureCoefficient I hΦ m κm ν i j) z| ≤
        (200000 * (Q + 1)) * ν * L ^ α.length := by
  have hm1 : 1 ≤ m := by omega
  have hN : α.length ≤ Nstar β := by
    have := Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt; omega
  have hslice := amnrWord_spatial_slice_on_vertical_domain_finite isOpen_univ
    (amnr_temperatureCoefficient_contDiff I hΦ hm1 hκm ν i j).contDiffOn
    (fun y => streamVel (Φ (m - 1)) y.1 y.2) α hN z.1 (fun _ => Set.mem_univ _) z.2
  rw [hslice, ← AVenhance.Infra.Section5.RelativeError.iterateSpatialWord_eq_amnrSpaceWord]
  have hflow : ∀ l : ℤ, ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l z.1) := by
    intro l
    apply contDiff_pi.mpr
    intro q
    apply contDiff_pi.mpr
    intro p
    exact (amnr_flowGrad_joint_contDiff_infty I hΦ m l q p).comp
      (contDiff_const.prodMk contDiff_id)
  have hsMatrix := AVenhance.Infra.Section5.sMat_spatial_contDiff I hΦ m hm1 κm z.1 hflow
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => I.sMat hΦ m κm z.1 y i j) :=
    contDiff_pi.mp (contDiff_pi.mp hsMatrix i) j
  have hfull : (fun y => amnrTemperatureCoefficient I hΦ m κm ν i j (z.1, y)) =
      (fun y => (I.Kmat κm m z.1 i j - ν * (if i = j then 1 else 0)) + I.sMat hΦ m κm z.1 y i j)
          := by
    funext y
    simp only [amnrTemperatureCoefficient, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [hfull]
  have hlinear := congrFun (iterateSpatialWord_linear (f := fun _ : Vec 2 =>
    I.Kmat κm m z.1 i j - ν * (if i = j then 1 else 0)) contDiff_const hs 1 α) z.2
  simp only [one_mul] at hlinear
  rw [hlinear]
  have he : 0 ≤ 2 ^ 10 / epsilon β I.Λ (m - 1) :=
    div_nonneg (by positivity)
      (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le).le
  have hF : ∀ l, I.hatXiML m l z.1 ≠ 0 → ∀ (v : List (Fin 2)) (y : Vec 2) (q p : Fin 2),
      |iterateSpatialWord v (fun y => (I.flowGrad hΦ m l z.1 y - 1) q p) y| ≤
        TMaterialSpatialCoefficient.tMaterialFlowBudget L v.length := by
    intro l hl v y q p
    refine (iterate_flowGrad_word_bound I hΦ hm hl v y q p).trans ?_
    unfold TMaterialSpatialCoefficient.tMaterialFlowBudget
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he hfreq v.length) (by positivity)
  have hKQ : 0 ≤ Q * ν := mul_nonneg hQ hν
  have hsbound := (iterate_sMat_word_entry_bound I hΦ hm1 κm z.1 hflow α z.2 (hK z.1) hF i j).trans
    (TMaterialSpatialCoefficient.tMaterial_budget_le hL hKQ hκν hα)
  have hconstant : |iterateSpatialWord α (fun _ : Vec 2 =>
      I.Kmat κm m z.1 i j - ν * (if i = j then 1 else 0)) z.2| ≤ (Q + 1) * ν * L ^ α.length := by
    by_cases hnil : α = []
    · subst α
      simp only [iterateSpatialWord, List.length_nil, pow_zero, mul_one]
      have hdelta : |ν * (if i = j then 1 else 0)| ≤ ν := by
        by_cases hij : i = j
        · simp only [ite_eq_left hij, mul_one, abs_of_nonneg hν, le_refl]
        · simpa only [ite_eq_right hij, mul_zero, abs_zero] using hν
      calc
        |I.Kmat κm m z.1 i j - ν * (if i = j then 1 else 0)| ≤
            |I.Kmat κm m z.1 i j| + |ν * (if i = j then 1 else 0)| := abs_sub _ _
        _ ≤ Q * ν + ν := add_le_add (hK z.1 i j) hdelta
        _ = (Q + 1) * ν := by ring
    · rw [iterateSpatialWord_const, ite_eq_right hnil]
      change |(0 : ℝ)| ≤ (Q + 1) * ν * L ^ α.length
      rw [abs_zero]
      positivity
  refine (abs_add_le _ _).trans ((add_le_add hconstant hsbound).trans ?_)
  have hp : 0 ≤ L ^ α.length := (pow_pos hL _).le
  have hQν : 0 ≤ Q * ν := hKQ
  nlinarith only [hp, hQν, hν, hQ, mul_nonneg hν hp, mul_nonneg hQν hp]

end AVenhance.Infra.Section5.Contracts
