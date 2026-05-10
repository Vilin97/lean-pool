/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.PNat.Prime
import Mathlib.Data.Rat.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompletePartialOrder

namespace LeanPool.DeadEnds

noncomputable instance decidablePredViolation (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    DecidablePred (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b *
        N + d)) :=
  fun _ => Classical.propDecidable _

/-
MATHLIB COVERAGE:
- Filter.Tendsto uniqueness: tendsto_nhds_unique
- Inclusion-exclusion for finite counting: Finset.sum_powerset_neg_one_pow_card_filter
- Key decomposition: break into (1) joint density for each T, (2) inclusion-exclusion
-/

/-- A positive integer `N` is a *base-`b` dead end*: `N` is square-free, yet `b * N + d`
fails to be square-free for every digit `d ∈ {0, …, b - 1}`. -/
def IsBaseBDeadEnd (b : ℕ) (N : ℕ) : Prop :=
  0 < N ∧ Squarefree N ∧ ∀ d ∈ Finset.range b, ¬Squarefree (b * N + d)

instance (b N : ℕ) : Decidable (IsBaseBDeadEnd b N) := by
  unfold IsBaseBDeadEnd
  infer_instance

/-- The number of base-`b` dead ends in `[1, X]`. -/
def countBaseBDeadEnds (b : ℕ) (X : ℕ) : ℕ :=
  (Finset.filter (fun N => IsBaseBDeadEnd b N) (Finset.Icc 1 X)).card

/-- The asymptotic density of base-`b` dead ends equals `D`, i.e.
`countBaseBDeadEnds b X / X → D` as `X → ∞`. -/
def HasAsymptoticDensity (b : ℕ) (D : ℝ) : Prop :=
  Filter.Tendsto (fun X : ℕ => (countBaseBDeadEnds b X : ℝ) / (X : ℝ))
    Filter.atTop (nhds D)

/-- The local density factor `μ_p(b, T)`: the fraction of residues `r ∈ [0, p²)` with
`p² ∤ r` and `p² ∤ b * r + d` for every `d ∈ T`. -/
noncomputable def localDensityFactor (p : ℕ) (b : ℕ) (T : Finset ℕ) : ℝ :=
  let pSq := p ^ 2
  let validResidues := (Finset.range pSq).filter fun r =>
    ¬(pSq ∣ r) ∧ ∀ d ∈ T, ¬(pSq ∣ (b * r + d))
  (validResidues.card : ℝ) / (pSq : ℝ)

/-- The joint square-free density `α(b, T) = ∏_p μ_p(b, T)`, the infinite product
over all primes. -/
noncomputable def jointSquarefreeDensity (b : ℕ) (T : Finset ℕ) : ℝ :=
  ∏' p : Nat.Primes, localDensityFactor (p : ℕ) b T

/-- The explicit inclusion-exclusion formula `∑_{T ⊆ {0,…,b-1}} (-1)^{|T|} α(b, T)` for `D_b`. -/
noncomputable def explicitDensityFormula (b : ℕ) : ℝ :=
  ∑ T ∈ (Finset.range b).powerset,
    ((-1 : ℝ) ^ T.card) * jointSquarefreeDensity b T

/-! ## Counting functions for joint conditions -/

/-- Count N in [1,X] such that N is squarefree and bN+d is squarefree for all d in T -/
def countJointSquarefree (b : ℕ) (T : Finset ℕ) (X : ℕ) : ℕ :=
  (Finset.Icc 1 X).filter (fun N =>
    Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) |>.card

/-! ## Helper lemmas for summability of local density deviations -/

/-- The residues `r ∈ [0, p²)` divisible by `p²` (just `r = 0`). -/
def typeA (p : ℕ) : Finset ℕ := (Finset.range (p ^ 2)).filter fun r => (p ^ 2) ∣ r

lemma typeA_card_eq_one (p : ℕ) (hp : Nat.Prime p) : (typeA p).card = 1 := by
  have h₁ : (typeA p) = {0} := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_singleton, typeA, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      have h₃ : p ^ 2 ∣ x := by tauto
      have h₄ : x = 0 := by
        have h₇ : p ^ 2 ∣ x := h₃
        have h₈ : x = 0 := by
          by_contra h₉
          have h₁₀ : x > 0 := Nat.pos_of_ne_zero (by intro h₁₁; simp_all)
          have h₁₁ : p ^ 2 ≤ x := Nat.le_of_dvd h₁₀ h₇
          linarith
        exact h₈
      simp [h₄]
    · intro h
      have h₂ : x = 0 := by simp_all
      rw [h₂]
      have h₃ : (0 : ℕ) < p ^ 2 := by
        have h₃₁ : p > 0 := Nat.Prime.pos hp
        have h₃₂ : p ^ 2 > 0 := pow_pos h₃₁ 2
        exact h₃₂
      simp_all
  rw [h₁]
  simp

lemma b_coprime_p_sq (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b) (hbp : b < p) :
    b.Coprime (p ^ 2) := by
  have h : ¬ p ∣ b := by
    intro h_dvd
    have h₁ : p ≤ b := Nat.le_of_dvd (by linarith) h_dvd
    linarith
  have h₂ : b.Coprime (p ^ 2) := Nat.Prime.coprime_pow_of_not_dvd hp (
      by simpa [Nat.Prime.ne_zero hp] using h)
  exact h₂

lemma r_eq_inv_image (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b) (hbp : b < p)
    (r : ℕ) (hr : r < p ^ 2) (d : ℕ) (hd : (p ^ 2) ∣ (b * r + d)) :
    r = ((-((d : ℕ) : ZMod (p ^ 2))) * ((b : ℕ) : ZMod (p ^ 2))⁻¹).val := by
  have hcop : b.Coprime (p ^ 2) := b_coprime_p_sq p hp b hb hbp
  have hbUnit : IsUnit ((b : ℕ) : ZMod (p ^ 2)) := by
    rwa [ZMod.isUnit_iff_coprime]
  have hZero : ((b * r + d : ℕ) : ZMod (p ^ 2)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact hd
  have hEq : (b : ZMod (p ^ 2)) * (r : ZMod (p ^ 2)) = -((d : ℕ) : ZMod (p ^ 2)) := by
    have h1 : ((b * r + d : ℕ) : ZMod (p ^ 2)) = (b : ZMod (p ^ 2)) * (r : ZMod (p ^ 2)) + (
        (d : ℕ) : ZMod (p ^ 2)) := by
      push_cast
      ring
    rw [h1] at hZero
    have h2 : (b : ZMod (p ^ 2)) * (r : ZMod (p ^ 2)) + ((d : ℕ) : ZMod (p ^ 2)) = 0 := hZero
    calc (b : ZMod (p ^ 2)) * (r : ZMod (p ^ 2))
        = (b : ZMod (p ^ 2)) * (r : ZMod (p ^ 2)) + ((d : ℕ) : ZMod (p ^ 2)) - ((d : ℕ) : ZMod (
            p ^ 2)) := by ring
      _ = 0 - ((d : ℕ) : ZMod (p ^ 2)) := by rw [h2]
      _ = -((d : ℕ) : ZMod (p ^ 2)) := by ring
  have hp2_gt_one : 1 < p ^ 2 := by
    have hp2 : 2 ≤ p := hp.two_le
    calc 1 < 2 := by norm_num
      _ ≤ p := hp2
      _ ≤ p * p := Nat.le_mul_self p
      _ = p ^ 2 := by ring
  haveI : Fact (1 < p ^ 2) := ⟨hp2_gt_one⟩
  have hR : (r : ZMod (p ^ 2)) = -((d : ℕ) : ZMod (p ^ 2)) * ((b : ℕ) : ZMod (p ^ 2))⁻¹ := by
    have key : ((b : ℕ) : ZMod (p ^ 2))⁻¹ * ((b : ℕ) : ZMod (p ^ 2)) = 1 := by
      exact ZMod.inv_mul_of_unit _ hbUnit
    calc (r : ZMod (p ^ 2))
        = ((b : ℕ) : ZMod (p ^ 2))⁻¹ * ((b : ℕ) : ZMod (p ^ 2)) * (r : ZMod (p ^ 2)) := by
            rw [key]; ring
      _ = ((b : ℕ) : ZMod (p ^ 2))⁻¹ * ((b : ZMod (p ^ 2)) * (r : ZMod (p ^ 2))) := by ring
      _ = ((b : ℕ) : ZMod (p ^ 2))⁻¹ * (-((d : ℕ) : ZMod (p ^ 2))) := by rw [hEq]
      _ = -((d : ℕ) : ZMod (p ^ 2)) * ((b : ℕ) : ZMod (p ^ 2))⁻¹ := by ring
  have hval : ((r : ℕ) : ZMod (p ^ 2)).val = r := ZMod.val_natCast_of_lt hr
  calc r = ((r : ℕ) : ZMod (p ^ 2)).val := hval.symm
    _ = (-((d : ℕ) : ZMod (p ^ 2)) * ((b : ℕ) : ZMod (p ^ 2))⁻¹).val := by rw [hR]

lemma filtered_subset_image (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b)
    (hbp : b < p) (T : Finset ℕ) (_hT : T ⊆ Finset.range b) :
    ((Finset.range (p ^ 2)).filter fun r => ∃ d ∈ T, (p ^ 2) ∣ (b * r + d)) ⊆
    T.image (fun d : ℕ => ((-((d : ℕ) : ZMod (p ^ 2))) * ((b : ℕ) : ZMod (p ^ 2))⁻¹).val) := by
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_range] at hr
  obtain ⟨hr_range, d, hd_mem, hdiv⟩ := hr
  rw [Finset.mem_image]
  exact ⟨d, hd_mem, (r_eq_inv_image p hp b hb hbp r hr_range d hdiv).symm⟩

lemma bad_residues_type_B_card_le (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b)
    (hbp : b < p) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    ((Finset.range (p ^ 2)).filter fun r => ∃ d ∈ T, (p ^ 2) ∣ (b * r + d)).card ≤ T.card := by
  calc ((Finset.range (p ^ 2)).filter fun r => ∃ d ∈ T, (p ^ 2) ∣ (b * r + d)).card
      ≤ (T.image (fun d : ℕ => ((-((d : ℕ) : ZMod (p ^ 2))) * ((b : ℕ) : ZMod (
          p ^ 2))⁻¹).val)).card :=
        Finset.card_le_card (filtered_subset_image p hp b hb hbp T hT)
    _ ≤ T.card := Finset.card_image_le

/-- The residues `r ∈ [0, p²)` for which `p² ∣ b * r + d` for some `d ∈ T`. -/
def typeB (p b : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.range (p ^ 2)).filter fun r => ∃ d ∈ T, (p ^ 2) ∣ (b * r + d)

lemma bad_residues_card_le (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b)
    (hbp : b < p) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    ((Finset.range (p ^ 2)).filter fun r => (p ^ 2) ∣ r ∨ ∃ d ∈ T, (p ^ 2) ∣ (b * r + d)).card
    ≤ T.card + 1 := by
  have h_eq : (Finset.range (p ^ 2)).filter (fun r => (p ^ 2) ∣ r ∨ ∃ d ∈ T, (p ^ 2) ∣ (b * r + d))
      = typeA p ∪ typeB p b T := Finset.filter_or _ _ _
  rw [h_eq]
  calc (typeA p ∪ typeB p b T).card
      ≤ (typeA p).card + (typeB p b T).card := Finset.card_union_le _ _
    _ = 1 + (typeB p b T).card := by rw [typeA_card_eq_one p hp]
    _ ≤ 1 + T.card := by
        apply Nat.add_le_add_left
        exact bad_residues_type_B_card_le p hp b hb hbp T hT
    _ = T.card + 1 := by ring

lemma valid_residues_card_ge (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b)
    (hbp : b < p) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    (p ^ 2 : ℕ) - (T.card + 1) ≤
    ((Finset.range (p ^ 2)).filter fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))).card :=
        by
  have hbad := bad_residues_card_le p hp b hb hbp T hT
  have hfilter_compl : ∀ r, (¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))) ↔
      ¬((p ^ 2 ∣ r) ∨ ∃ d ∈ T, (p ^ 2 ∣ (b * r + d))) := by
    intro r
    simp only [not_or, not_exists, not_and]
  simp_rw [hfilter_compl]
  have h1 : (Finset.range (p ^ 2)).card = p ^ 2 := Finset.card_range _
  have hcard := @Finset.card_filter_add_card_filter_not ℕ (Finset.range (p ^ 2))
      (fun r => (p ^ 2 ∣ r) ∨ ∃ d ∈ T, (p ^ 2 ∣ (b * r + d))) _ _
  rw [h1] at hcard
  omega

lemma localDensityFactor_le_one (p : ℕ) (b : ℕ) (T : Finset ℕ) :
    localDensityFactor p b T ≤ 1 := by
  unfold localDensityFactor
  simp only []
  set pSq := p ^ 2
  set validResidues := (Finset.range pSq).filter fun r =>
    ¬(pSq ∣ r) ∧ ∀ d ∈ T, ¬(pSq ∣ (b * r + d))
  by_cases hp : pSq = 0
  · simp [hp]
  · have hpSq_pos : (0 : ℝ) < pSq := by
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
    rw [div_le_one₀ hpSq_pos]
    have h1 : validResidues.card ≤ (Finset.range pSq).card := Finset.card_filter_le _ _
    have h2 : (Finset.range pSq).card = pSq := Finset.card_range pSq
    exact Nat.cast_le.mpr (h2 ▸ h1)

lemma localDensityFactor_nonneg (p : ℕ) (b : ℕ) (T : Finset ℕ) :
    0 ≤ localDensityFactor p b T := by
  have h_main : 0 ≤ ((Finset.filter (fun r => (¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d)))) (
      Finset.range (p ^ 2))).card : ℝ) / (p ^ 2 : ℝ) := by
    by_cases h : (p : ℕ) = 0
    · have h₁ : p = 0 := h
      have h₂ : (p ^ 2 : ℕ) = 0 := by
        simp [h₁]
      have h₃ : (Finset.filter (fun r => (¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d)))) (
          Finset.range (p ^ 2))).card = 0 := by
        simp [h₂]
      have h₄ : ((Finset.filter (fun r => (¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d)))) (
          Finset.range (p ^ 2))).card : ℝ) = 0 := by
        norm_cast
      have h₅ : (p ^ 2 : ℝ) = 0 := by
        norm_cast
      have h₆ : ((Finset.filter (fun r => (¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d)))) (
          Finset.range (p ^ 2))).card : ℝ) / (p ^ 2 : ℝ) = 0 := by
        rw [h₄, h₅]; simp
      linarith
    · have h₁ : (p : ℕ) ≠ 0 := h
      have h₂ : (p ^ 2 : ℕ) > 0 := by
        positivity
      have h₃ : (p ^ 2 : ℝ) > 0 := by
        norm_cast
      have h₄ : 0 ≤ ((Finset.filter (fun r => (¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d)))) (
          Finset.range (p ^ 2))).card : ℝ) := by
        exact by positivity
      have h₅ : 0 ≤ ((Finset.filter (fun r => (¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d)))) (
          Finset.range (p ^ 2))).card : ℝ) / (p ^ 2 : ℝ) := by
        exact div_nonneg h₄ (by positivity)
      exact h₅
  simpa [localDensityFactor] using h_main

lemma localDensityFactor_ge_sub (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b)
    (hbp : b < p) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    1 - (T.card + 1 : ℝ) / (p ^ 2 : ℝ) ≤ localDensityFactor p b T := by
  unfold localDensityFactor
  simp only
  have hp2 : 2 ≤ p := hp.two_le
  have hpSq_pos : (0 : ℝ) < (p ^ 2 : ℕ) := by positivity
  have hpSq_ne_zero : ((p : ℝ) ^ 2) ≠ 0 := by positivity
  have hcast : ((p ^ 2 : ℕ) : ℝ) = (p : ℝ) ^ 2 := by norm_cast
  rw [hcast] at hpSq_pos ⊢
  rw [one_sub_div hpSq_ne_zero]
  apply div_le_div_of_nonneg_right _ (le_of_lt hpSq_pos)
  have hcard := valid_residues_card_ge p hp b hb hbp T hT
  have hTcard_bound : T.card + 1 ≤ p ^ 2 := by
    have hT_card : T.card ≤ b := by
      calc T.card ≤ (Finset.range b).card := Finset.card_le_card hT
        _ = b := Finset.card_range b
    have hp_sq_ge : p ^ 2 ≥ p * 2 := by nlinarith
    nlinarith
  have hcast2 : ((p : ℝ) ^ 2) - (↑T.card + 1) = ((p ^ 2 - (T.card + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hTcard_bound]
    push_cast
    ring
  rw [hcast2]
  exact Nat.cast_le.mpr hcard

lemma localDensityFactor_near_one_large_prime (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b)
    (hbp : b < p) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    |localDensityFactor p b T - 1| ≤ (T.card + 1 : ℝ) / (p ^ 2 : ℝ) := by
  have hμ_le : localDensityFactor p b T ≤ 1 := localDensityFactor_le_one p b T
  have hμ_ge : 1 - (T.card + 1 : ℝ) / (p ^ 2 : ℝ) ≤ localDensityFactor p b T :=
    localDensityFactor_ge_sub p hp b hb hbp T hT
  have h_div_nonneg : 0 ≤ (T.card + 1 : ℝ) / (p ^ 2 : ℝ) := by
    apply div_nonneg
    · have : (0 : ℝ) ≤ T.card := by positivity
      linarith
    · have hp_pos : 0 < p := hp.pos
      positivity
  rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 1 - localDensityFactor p b T)]
  linarith

lemma primes_summable_one_div_sq : Summable (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) ^ 2) := by
  have h : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    have h₁ : ((-2 : ℝ) : ℝ) < -1 := by norm_num
    have h₂ : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
      simpa [h₁] using (Nat.Primes.summable_rpow (r := (-2 : ℝ))).mpr (by norm_num)
    exact h₂
  have h₂ : (fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) ^ 2) = (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (
      -2 : ℝ)) := by
    funext p
    have h₃ : (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 = ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
      have h₄ : (p : ℕ) ≥ 2 := p.prop.two_le
      have h₅ : ((p : ℕ) : ℝ) ≠ 0 := by
        norm_cast; linarith
      have h₆ : ((p : ℕ) : ℝ) ^ (-2 : ℝ) = 1 / ((p : ℕ) : ℝ) ^ 2 := by
        rw [Real.rpow_neg (by positivity)]; simp
      rw [h₆]
    rw [h₃]
  rw [h₂] at *
  exact h

lemma bound_summable (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b) :
    Summable (fun p : Nat.Primes => (T.card + 1 : ℝ) / ((p : ℕ) : ℝ) ^ 2) := by
  have h_summable_one_div_p_sq : Summable (fun p : Nat.Primes => (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2) := by
    have h₁ : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) := by
      have h₃ : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) := by
        simpa using Nat.Primes.summable_rpow.mpr (by norm_num : (-2 : ℝ) < -1)
      exact h₃
    have h₂ : (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) = (fun p : Nat.Primes => (1 : ℝ) / (
        (p : ℕ) : ℝ) ^ 2) := by
      funext p
      have h₃ : ((p : ℕ) : ℝ) > 0 := by
        norm_cast
        exact Nat.Prime.pos p.prop
      have h₅ : (p : ℝ) ^ (-2 : ℝ) = (1 : ℝ) / (p : ℝ) ^ 2 := by
        rw [Real.rpow_neg (by positivity)]; simp
      have h₆ : (p : ℝ) = ((p : ℕ) : ℝ) := by norm_cast
      rw [h₅, h₆]
    rw [h₂] at h₁
    exact h₁
  have h_main : Summable (fun p : Nat.Primes => (T.card + 1 : ℝ) / ((p : ℕ) : ℝ) ^ 2) := by
    have h₁ : (fun p : Nat.Primes => (T.card + 1 : ℝ) / ((p : ℕ) : ℝ) ^ 2) = (fun p : Nat.Primes =>
        (T.card + 1 : ℝ) * ((1 : ℝ) / ((p : ℕ) : ℝ) ^ 2)) := by
      funext p
      field_simp [Nat.cast_ne_zero]
    rw [h₁]
    have h₂ : Summable (fun p : Nat.Primes => (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2) :=
        h_summable_one_div_p_sq
    have h₃ : Summable (fun p : Nat.Primes => (T.card + 1 : ℝ) * ((1 : ℝ) / ((p : ℕ) : ℝ) ^ 2)) :=
        by
      exact Summable.mul_left (T.card + 1 : ℝ) h₂
    exact h₃
  exact h_main

theorem deviation_bound_for_large_prime (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b)
    (hbp : b < p) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    ‖|localDensityFactor p b T - 1|‖ ≤ (T.card + 1 : ℝ) / (p : ℝ) ^ 2 := by
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  exact localDensityFactor_near_one_large_prime p hp b hb hbp T hT

lemma finite_primes_le (b : ℕ) : {p : Nat.Primes | (p : ℕ) ≤ b}.Finite := by
  have h₁ : Set.InjOn (fun p : Nat.Primes => (p : ℕ)) Set.univ := by
    exact Set.injOn_of_injective Nat.Primes.coe_nat_injective
  have h₂ : (Set.Iic b : Set ℕ).Finite := by
    exact Set.finite_Iic _
  have h₃ : {p : Nat.Primes | (p : ℕ) ≤ b} = Set.preimage (fun p : Nat.Primes => (p : ℕ)) (
      Set.Iic b) := by
    aesop
  have h₄ : {p : Nat.Primes | (p : ℕ) ≤ b}.Finite := by
    rw [h₃]
    exact h₂.preimage (h₁.mono (Set.subset_univ _))
  aesop

lemma deviation_bounded_eventually (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite,
      ‖|localDensityFactor (p : ℕ) b T - 1|‖ ≤ (T.card + 1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 := by
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (finite_primes_le b)
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  by_contra h
  push Not at h
  exact hp (deviation_bound_for_large_prime p p.prop b hb h T hT)

/-- The sum ∑_p |μ_p(b,T) - 1| converges.
    By localDensityFactor_near_one, |μ_p - 1| ≤ (|T|+1)/p².
    Since ∑_p 1/p² converges (it's bounded by ∑_n 1/n² = π²/6), the sum converges. -/
lemma sum_localDensityFactor_deviation_summable (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) :
    Summable (fun p : Nat.Primes => |localDensityFactor (p : ℕ) b T - 1|) := by
  exact Summable.of_norm_bounded_eventually (bound_summable b hb T hT)
    (deviation_bounded_eventually b hb T hT)

/-- Multipliability from summability of deviations.
    Write μ_p = 1 + (μ_p - 1). If ∑|μ_p - 1| converges, then ∏ μ_p converges.
    Mathlib's `Multipliable.of_norm_bounded` or related lemmas apply when the factors
    are close to 1, which follows from sum_localDensityFactor_deviation_summable. -/
lemma multipliable_of_deviation_summable (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ)
    (_hT : T ⊆ Finset.range b)
    (h_sum : Summable (fun p : Nat.Primes => |localDensityFactor (p : ℕ) b T - 1|)) :
    Multipliable (fun p : Nat.Primes => localDensityFactor (p : ℕ) b T) := by
  -- Step 1: From Summable |f| get Summable f via Summable.of_abs
  have h_summable : Summable (fun p : Nat.Primes => localDensityFactor (p : ℕ) b T - 1) :=
    Summable.of_abs h_sum
  -- Step 2: Apply Real.multipliable_one_add_of_summable
  have h_mult : Multipliable (fun p : Nat.Primes => 1 + (localDensityFactor (p : ℕ) b T - 1)) :=
    Real.multipliable_one_add_of_summable h_summable
  -- Step 3: Simplify 1 + (μ - 1) = μ
  convert h_mult using 1
  ext p
  ring

lemma jointSquarefreeDensity_multipliable (b : ℕ) (hb : 2 ≤ b)
    (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    Multipliable (fun p : Nat.Primes => localDensityFactor (p : ℕ) b T) := by
  exact multipliable_of_deviation_summable b hb T hT (
      sum_localDensityFactor_deviation_summable b hb T hT)

lemma multipliable_of_deviation_summable_subtype
    (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (U : Set Nat.Primes)
    (h_sum : Summable (fun p : U => |localDensityFactor (p : ℕ) b T - 1|)) :
    Multipliable (fun p : U => localDensityFactor (p : ℕ) b T) := by
  have h_sum_abs : Summable (fun p : U => (localDensityFactor (p : ℕ) b T - 1 : ℝ)) :=
    Summable.of_abs h_sum
  have h_main : Multipliable (fun p : U => (1 : ℝ) + (localDensityFactor (p : ℕ) b T - 1 : ℝ)) :=
    Real.multipliable_one_add_of_summable h_sum_abs
  have h_final : Multipliable (fun p : U => localDensityFactor (p : ℕ) b T) := by
    have h₁ : (fun p : U => (1 : ℝ) + (localDensityFactor (p : ℕ) b T - 1 : ℝ)) = (fun p : U =>
        localDensityFactor (p : ℕ) b T) := by
      funext p
      ring
    rw [← h₁]
    exact h_main
  exact h_final

lemma multipliable_compl_of_multipliable (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) (S : Finset Nat.Primes) :
    Multipliable ((fun p : Nat.Primes => localDensityFactor (p : ℕ) b T) ∘
      Subtype.val (p := (· ∉ S))) := by
  have h_full_sum := sum_localDensityFactor_deviation_summable b hb T hT
  have h_compl_sum : Summable ((fun p : Nat.Primes => |localDensityFactor (p : ℕ) b T -
      1|) ∘ Subtype.val (p := (· ∉ S))) :=
    h_full_sum.subtype {p | p ∉ S}
  exact multipliable_of_deviation_summable_subtype b hb T hT {p | p ∉ S} h_compl_sum

lemma tprod_compl_le_one (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) :
    (∏' (x : {p : Nat.Primes // p ∉ S}), localDensityFactor (x : ℕ) b T) ≤ 1 := by
  apply tprod_le_of_prod_le'
  · exact le_refl 1
  · intro s
    apply Finset.prod_le_one
    · intro i _
      exact localDensityFactor_nonneg (i : ℕ) b T
    · intro i _
      exact localDensityFactor_le_one (i : ℕ) b T

/-- The modulus M = ∏_{p ∈ S} p² -/
noncomputable def primeSquareProduct (S : Finset Nat.Primes) : ℕ :=
  ∏ p ∈ S, (p : ℕ) ^ 2

/-- Valid residues mod M: residues r such that for all p ∈ S, r mod p² is valid -/
noncomputable def validResiduesMod (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) : Finset ℕ :=
  (Finset.range (primeSquareProduct S)).filter fun r =>
    ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * r + d))

/-- The product of local density factors L = ∏_{p ∈ S} localDensityFactor p b T -/
noncomputable def localDensityProduct (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ S, localDensityFactor (p : ℕ) b T

/-- The local valid residues for a single prime p: residues r in [0, p²) such that
    p² ∤ r and for all d ∈ T, p² ∤ (b * r + d). -/
def localValidResidues (p : ℕ) (b : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.range (p ^ 2)).filter fun r =>
    ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))

lemma localValidResidues_card_eq (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (T : Finset ℕ) :
    ((localValidResidues p b T).card : ℝ) = (p : ℝ) ^ 2 * localDensityFactor p b T := by
  have h1 : ((localValidResidues p b T).card : ℝ) = ((localValidResidues p b T).card : ℝ) := rfl
  have h2 : localDensityFactor p b T = ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T,
      ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ) / ( (p ^ 2 : ℕ) : ℝ)) := by
    dsimp [localDensityFactor]
  have h3 : ((localValidResidues p b T).card : ℝ) = ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧
      ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ)) := by
    dsimp [localValidResidues]
  have h4 : ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))) (
      Finset.range (p ^ 2))).card : ℝ)) = (p : ℝ) ^ 2 * localDensityFactor p b T := by
    have h5 : localDensityFactor p b T = ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T,
        ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ) / ( (p ^ 2 : ℕ) : ℝ)) := by
      rw [h2]
    have h6 : (p : ℝ) ≠ 0 := by
      norm_cast
      exact Nat.Prime.ne_zero hp
    have h7 : (p : ℝ) ^ 2 ≠ 0 := by
      positivity
    have h8 : ((p : ℝ) ^ 2 : ℝ) = (p ^ 2 : ℕ) := by
      norm_cast
    rw [h5]
    have h9 : (( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ (b * r + d))) (
        Finset.range (p ^ 2))).card : ℝ)) = (( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T,
            ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ)) := rfl
    have h10 : ((p : ℝ) ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp [h7, h10]; ring_nf; field_simp [h7, h10]; norm_cast
  calc
    ((localValidResidues p b T).card : ℝ) = ( ( (Finset.filter (fun r => ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T,
        ¬(p ^ 2 ∣ (b * r + d))) (Finset.range (p ^ 2))).card : ℝ)) := by rw [h3]
    _ = (p : ℝ) ^ 2 * localDensityFactor p b T := by rw [h4]

lemma prime_sq_coprime (p q : Nat.Primes) (hne : p ≠ q) :
    ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2) := by
  have h₁ : p ≠ q := hne
  have h₂ : (p : ℕ).Prime := p.prop
  have h₃ : (q : ℕ).Prime := q.prop
  -- Use the lemma `Nat.coprime_pow_primes` to show that powers of distinct primes are coprime
  have h₄ : ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2) := by
    apply Nat.Coprime.pow_left 2
    apply Nat.Coprime.pow_right 2
    -- Since p and q are distinct primes, they are coprime
    have h₅ : (p : ℕ) ≠ (q : ℕ) := by
      intro h₅
      apply h₁
      -- If their natural number representations are equal, then the primes are equal
      exact Subtype.ext h₅
    -- Use the fact that distinct primes are coprime
    exact Nat.coprime_primes h₂ h₃ |>.mpr h₅
  exact h₄

lemma pairwise_coprime_prime_squares (S : Finset Nat.Primes) :
    (S : Set Nat.Primes).Pairwise (fun p q => ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2)) := by
  intro p _ q _ hpq
  have h_inj : (p : ℕ) ≠ (q : ℕ) := by
    intro h
    apply hpq
    -- If the underlying natural numbers are equal, then the primes are equal
    -- because the coercion from Nat.Primes to ℕ is injective.
    have h₁ : p = q := by
      -- Use the fact that the subtype coercion is injective
      apply Subtype.ext
      simpa using h
    exact h₁
  have h_coprime : (p : ℕ).Coprime (q : ℕ) := by
    have h₁ : Nat.Prime (p : ℕ) := p.prop
    have h₂ : Nat.Prime (q : ℕ) := q.prop
    -- Use the fact that distinct primes are coprime
    have h₃ : (p : ℕ) ≠ (q : ℕ) := h_inj
    have h₄ : (p : ℕ).Coprime (q : ℕ) := by
      apply Nat.coprime_primes h₁ h₂ |>.mpr
      intro h₅
      apply h₃
      simpa using h₅
    exact h₄
  have h_pow_left : ((p : ℕ) ^ 2).Coprime (q : ℕ) := by
    have h₂ : (p : ℕ).Coprime (q : ℕ) := h_coprime
    -- Use the fact that if a and b are coprime, then a ^ 2 and b are coprime.
    have h₃ : ((p : ℕ) ^ 2).Coprime (q : ℕ) := by
      -- Use the property of coprime numbers raised to powers.
      simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using
        Nat.Coprime.pow_left 2 h₂
    exact h₃
  have h_pow_right : ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2) := by
    have h₂ : ((p : ℕ) ^ 2).Coprime (q : ℕ) := h_pow_left
    -- Use the fact that if a and b are coprime, then a and b ^ 2 are coprime.
    have h₃ : ((p : ℕ) ^ 2).Coprime ((q : ℕ) ^ 2) := by
      -- Use the property of coprime numbers raised to powers.
      simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using
        Nat.Coprime.pow_right 2 h₂
    exact h₃
  exact h_pow_right

/-- The list S.toList satisfies pairwise coprimality for the map p ↦ p².
    Uses `pairwise_coprime_prime_squares` and transfers the set pairwise property to the list.
    Mathlib's `List.pairwise_of_reflexive_of_forall_ne` handles this for symmetric reflexive
    relations,
    but coprimality is not reflexive (unless p² = 1). Instead we use the fact that S.toList.Nodup
    and the set pairwise property directly imply the list pairwise property.
    Specifically, uses `List.Nodup.pairwise_of_set_pairwise : l.Nodup → {x | x ∈ l}.Pairwise r →
    List.Pairwise r l`
    together with `Finset.nodup_toList : ∀ (s : Finset α), s.toList.Nodup` and
    `Finset.coe_toList : ↑s.toList = ↑s` (as sets). -/
lemma toList_pairwise_coprime_prime_squares (S : Finset Nat.Primes) :
    List.Pairwise (Function.onFun Nat.Coprime (fun p : Nat.Primes => (p : ℕ) ^ 2)) S.toList := by
  apply List.Nodup.pairwise_of_set_pairwise (Finset.nodup_toList S)
  simp only [Finset.mem_toList]
  exact pairwise_coprime_prime_squares S

lemma list_map_prod_eq_primeSquareProduct (S : Finset Nat.Primes) :
    (List.map (fun p : Nat.Primes => (p : ℕ) ^ 2) S.toList).prod = primeSquareProduct S := by
  aesop

/-- If r₁ ≡ r₂ [MOD p²] for all p ∈ S where the moduli are pairwise coprime,
    then r₁ ≡ r₂ [MOD ∏ p², p ∈ S].
    Uses `Nat.modEq_list_map_prod_iff : ∀ {ι : Type u_1} {a b : ℕ} {s : ι → ℕ} {l : List ι},
      List.Pairwise (Function.onFun Nat.Coprime s) l → (a ≡ b [MOD (List.map s l).prod] ↔ ∀ i ∈ l, a
      ≡ b [MOD s i])`
    by converting the Finset to a list and applying the list-based CRT theorem.
    Requires `toList_pairwise_coprime_prime_squares` and `list_map_prod_eq_primeSquareProduct`. -/
lemma modEq_primeSquareProduct_of_forall_modEq (S : Finset Nat.Primes) (r₁ r₂ : ℕ)
    (h : ∀ p ∈ S, r₁ ≡ r₂ [MOD (p : ℕ) ^ 2]) :
    r₁ ≡ r₂ [MOD primeSquareProduct S] := by
  rw [← list_map_prod_eq_primeSquareProduct]
  rw [Nat.modEq_list_map_prod_iff (toList_pairwise_coprime_prime_squares S)]
  intro p hp
  exact h p (Finset.mem_toList.mp hp)

/-- For r < M (the product of all p² for p ∈ S), the CRT map is injective.
    Two residues in [0, M) with the same tuple of remainders must be equal.
    Proof strategy:
    1. Assume r₁, r₂ < M and the CRT maps are equal
    2. Equal maps means r₁ % p² = r₂ % p² for all p ∈ S
    3. This is equivalent to r₁ ≡ r₂ [MOD p²] by definition of ModEq
    4. By `modEq_primeSquareProduct_of_forall_modEq`, we get r₁ ≡ r₂ [MOD M]
    5. By `Nat.ModEq.eq_of_lt_of_lt`, since both are < M, we get r₁ = r₂ -/
lemma crtMap_injective_on_range (S : Finset Nat.Primes) :
    Set.InjOn (fun r => fun p (_hp : p ∈ S) => r % ((p : ℕ) ^ 2))
      {r | r < primeSquareProduct S} := by
  intro r₁ hr₁ r₂ hr₂ heq
  -- heq : (fun p _hp => r₁ % p²) = (fun p _hp => r₂ % p²)
  -- This means for all p ∈ S, r₁ % p² = r₂ % p²
  have h_modEq : ∀ p ∈ S, r₁ ≡ r₂ [MOD (p : ℕ) ^ 2] := by
    intro p hp
    -- r₁ % p² = r₂ % p² comes from heq
    have h : r₁ % (p : ℕ) ^ 2 = r₂ % (p : ℕ) ^ 2 := congrFun (congrFun heq p) hp
    -- Nat.ModEq is defined as a % n = b % n
    exact h
  -- By CRT, r₁ ≡ r₂ [MOD M]
  have h_modEq_M : r₁ ≡ r₂ [MOD primeSquareProduct S] :=
    modEq_primeSquareProduct_of_forall_modEq S r₁ r₂ h_modEq
  -- Since both are < M, they are equal
  exact Nat.ModEq.eq_of_lt_of_lt h_modEq_M hr₁ hr₂

lemma dvd_iff_mod_dvd (p : ℕ) (_hp : 0 < p ^ 2) (r : ℕ) :
    p ^ 2 ∣ r ↔ r % (p ^ 2) = 0 := by
  have h_main : p ^ 2 ∣ r ↔ r % (p ^ 2) = 0 := Nat.dvd_iff_mod_eq_zero
  aesop

lemma shifted_dvd_iff_mod (p b d r : ℕ) (_hp : 0 < p ^ 2) :
    p ^ 2 ∣ (b * r + d) ↔ p ^ 2 ∣ (b * (r % (p ^ 2)) + d) := by
  have h₁ : b * r + d ≡ b * (r % (p ^ 2)) + d [MOD p ^ 2] := by
    have h₂ : r ≡ r % (p ^ 2) [MOD p ^ 2] := by
      -- Use the property that any number is congruent to its remainder modulo p²
      have h₃ : r % (p ^ 2) = r % (p ^ 2) := rfl
      simp [Nat.ModEq]
    -- Multiply both sides by b and add d to get the desired congruence
    have h₃ : b * r + d ≡ b * (r % (p ^ 2)) + d [MOD p ^ 2] := by
      calc
        b * r + d ≡ b * (r % (p ^ 2)) + d [MOD p ^ 2] := by
          -- Use the fact that multiplication and addition preserve congruence
          have h₄ : b * r ≡ b * (r % (p ^ 2)) [MOD p ^ 2] := by
            -- Multiply both sides of the congruence r ≡ r % (p²) by b
            calc
              b * r ≡ b * (r % (p ^ 2)) [MOD p ^ 2] := by
                -- Use the property of congruence under multiplication
                have h₅ : r ≡ r % (p ^ 2) [MOD p ^ 2] := h₂
                have h₆ : b * r ≡ b * (r % (p ^ 2)) [MOD p ^ 2] := by
                  -- Use the property of congruence under multiplication
                  calc
                    b * r ≡ b * (r % (p ^ 2)) [MOD p ^ 2] := by
                      exact Nat.ModEq.mul_left b h₅
                    _ ≡ b * (r % (p ^ 2)) [MOD p ^ 2] := by rfl
                exact h₆
              _ ≡ b * (r % (p ^ 2)) [MOD p ^ 2] := by rfl
          -- Add d to both sides
          have h₅ : b * r + d ≡ b * (r % (p ^ 2)) + d [MOD p ^ 2] := by
            calc
              b * r + d ≡ b * (r % (p ^ 2)) + d [MOD p ^ 2] := by
                exact Nat.ModEq.add h₄ (Nat.ModEq.refl d)
              _ ≡ b * (r % (p ^ 2)) + d [MOD p ^ 2] := by rfl
          exact h₅
        _ ≡ b * (r % (p ^ 2)) + d [MOD p ^ 2] := by rfl
    exact h₃
  -- Convert the congruence into divisibility conditions
  have h₂ : p ^ 2 ∣ (b * r + d) ↔ p ^ 2 ∣ (b * (r % (p ^ 2)) + d) := by
    constructor
    · -- Prove the forward direction: if p² divides b*r + d, then it divides b*(r % p²) + d
      intro h₃
      have h₄ : p ^ 2 ∣ (b * r + d) := h₃
      have h₅ : p ^ 2 ∣ (b * (r % (p ^ 2)) + d) := by
        -- Use the fact that b*r + d ≡ b*(r % p²) + d [MOD p²]
        have h₆ : (b * r + d) % (p ^ 2) = (b * (r % (p ^ 2)) + d) % (p ^ 2) := by
          rw [Nat.ModEq] at h₁
          exact h₁
        -- Since p² divides b*r + d, (b*r + d) % p² = 0
        have h₈ : (b * (r % (p ^ 2)) + d) % (p ^ 2) = 0 := by
          omega
        -- So p² divides b*(r % p²) + d
        have h₉ : p ^ 2 ∣ (b * (r % (p ^ 2)) + d) := by
          exact Nat.dvd_of_mod_eq_zero h₈
        exact h₉
      exact h₅
    · -- Prove the reverse direction: if p² divides b*(r % p²) + d, then it divides b*r + d
      intro h₃
      have h₄ : p ^ 2 ∣ (b * (r % (p ^ 2)) + d) := h₃
      have h₅ : p ^ 2 ∣ (b * r + d) := by
        -- Use the fact that b*r + d ≡ b*(r % p²) + d [MOD p²]
        have h₆ : (b * r + d) % (p ^ 2) = (b * (r % (p ^ 2)) + d) % (p ^ 2) := by
          rw [Nat.ModEq] at h₁
          exact h₁
        -- Since p² divides b*(r % p²) + d, (b*(r % p²) + d) % p² = 0
        have h₈ : (b * r + d) % (p ^ 2) = 0 := by
          omega
        -- So p² divides b*r + d
        have h₉ : p ^ 2 ∣ (b * r + d) := by
          exact Nat.dvd_of_mod_eq_zero h₈
        exact h₉
      exact h₅
  exact h₂

lemma valid_iff_locally_valid (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (r : ℕ) :
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * r + d))) ↔
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2)) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * (r % (p : ℕ) ^ 2) +
        d))) := by
  apply Iff.intro
  · -- Prove the forward direction: if the original condition holds, then the local condition holds.
    intro h p hp
    have h₁ : ¬((p : ℕ) ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * r + d)) := h p hp
    have h₂ : ¬((p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2)) := by
      have h₄ : (p : ℕ) ^ 2 ∣ r ↔ (p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2) := by
        have h₅ : (p : ℕ) ^ 2 ∣ r ↔ r % (p : ℕ) ^ 2 = 0 := by
          simp [Nat.dvd_iff_mod_eq_zero]
        have h₆ : (p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2) ↔ r % (p : ℕ) ^ 2 = 0 := by
          simp [Nat.dvd_iff_mod_eq_zero]
        simp_all [Nat.pow_succ]
      simp_all
    have h₃ : ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * (r % (p : ℕ) ^ 2) + d)) := by
      intro d hd
      have h₄ : ¬((p : ℕ) ^ 2 ∣ (b * r + d)) := h₁.2 d hd
      have h₅ : (b * r + d) % (p : ℕ) ^ 2 = (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 := by
        have h₆ : (b * r) % (p : ℕ) ^ 2 = (b * (r % (p : ℕ) ^ 2)) % (p : ℕ) ^ 2 := by
          have h₈ : (b * r) % (p : ℕ) ^ 2 = (b * (r % (p : ℕ) ^ 2)) % (p : ℕ) ^ 2 := by
            calc
              (b * r) % (p : ℕ) ^ 2 = (b * r) % (p : ℕ) ^ 2 := rfl
              _ = (b * (r % (p : ℕ) ^ 2)) % (p : ℕ) ^ 2 := by
                simp [Nat.mul_mod]
          exact h₈
        have h₉ : (b * r + d) % (p : ℕ) ^ 2 = ((b * r) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (
            p : ℕ) ^ 2 := by
          simp [Nat.add_mod]
        have h₁₀ : (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 = ((b * (r % (p : ℕ) ^ 2)) % (
            p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 := by
          simp [Nat.add_mod]
        have h₁₁ : ((b * r) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 = ((b * (r % (
            p : ℕ) ^ 2)) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 := by
          rw [h₆]
        calc
          (b * r + d) % (p : ℕ) ^ 2 = ((b * r) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 := by
              rw [h₉]
          _ = ((b * (r % (p : ℕ) ^ 2)) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 := by rw [h₁₁]
          _ = (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 := by rw [h₁₀]
      have h₆ : ¬((p : ℕ) ^ 2 ∣ (b * (r % (p : ℕ) ^ 2) + d)) := by
        intro h₇
        have h₈ : (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 = 0 := by
          exact Nat.mod_eq_zero_of_dvd h₇
        have h₉ : (b * r + d) % (p : ℕ) ^ 2 = 0 := by
          rw [h₅] at *
          exact h₈
        have h₁₀ : (p : ℕ) ^ 2 ∣ (b * r + d) := by
          have h₁₁ : (b * r + d) % (p : ℕ) ^ 2 = 0 := h₉
          exact Nat.dvd_of_mod_eq_zero h₁₁
        exact h₄ h₁₀
      exact h₆
    exact ⟨h₂, h₃⟩
  -- Prove the backward direction: if the local condition holds, then the original condition holds.
  · intro h p hp
    have h₁ : ¬((p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2)) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * (r % (p : ℕ) ^ 2) +
        d)) := h p hp
    have h₂ : ¬((p : ℕ) ^ 2 ∣ r) := by
      have h₄ : (p : ℕ) ^ 2 ∣ r ↔ (p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2) := by
        have h₅ : (p : ℕ) ^ 2 ∣ r ↔ r % (p : ℕ) ^ 2 = 0 := by
          simp [Nat.dvd_iff_mod_eq_zero]
        have h₆ : (p : ℕ) ^ 2 ∣ (r % (p : ℕ) ^ 2) ↔ r % (p : ℕ) ^ 2 = 0 := by
          simp [Nat.dvd_iff_mod_eq_zero]
        simp_all [Nat.pow_succ]
      simp_all
    have h₃ : ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ (b * r + d)) := by
      intro d hd
      have h₄ : ¬((p : ℕ) ^ 2 ∣ (b * (r % (p : ℕ) ^ 2) + d)) := h₁.2 d hd
      have h₅ : (b * r + d) % (p : ℕ) ^ 2 = (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 := by
        have h₆ : (b * r) % (p : ℕ) ^ 2 = (b * (r % (p : ℕ) ^ 2)) % (p : ℕ) ^ 2 := by
          have h₈ : (b * r) % (p : ℕ) ^ 2 = (b * (r % (p : ℕ) ^ 2)) % (p : ℕ) ^ 2 := by
            calc
              (b * r) % (p : ℕ) ^ 2 = (b * r) % (p : ℕ) ^ 2 := rfl
              _ = (b * (r % (p : ℕ) ^ 2)) % (p : ℕ) ^ 2 := by
                simp [Nat.mul_mod]
          exact h₈
        have h₉ : (b * r + d) % (p : ℕ) ^ 2 = ((b * r) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (
            p : ℕ) ^ 2 := by
          simp [Nat.add_mod]
        have h₁₀ : (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 = ((b * (r % (p : ℕ) ^ 2)) % (
            p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 := by
          simp [Nat.add_mod]
        have h₁₁ : ((b * r) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 = ((b * (r % (
            p : ℕ) ^ 2)) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 := by
          rw [h₆]
        calc
          (b * r + d) % (p : ℕ) ^ 2 = ((b * r) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 := by
              rw [h₉]
          _ = ((b * (r % (p : ℕ) ^ 2)) % (p : ℕ) ^ 2 + d % (p : ℕ) ^ 2) % (p : ℕ) ^ 2 := by rw [h₁₁]
          _ = (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 := by rw [h₁₀]
      have h₆ : ¬((p : ℕ) ^ 2 ∣ (b * r + d)) := by
        intro h₇
        have h₈ : (b * r + d) % (p : ℕ) ^ 2 = 0 := by
          exact Nat.mod_eq_zero_of_dvd h₇
        have h₉ : (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 = 0 := by
          rw [h₅] at *
          exact h₈
        have h₁₀ : (p : ℕ) ^ 2 ∣ (b * (r % (p : ℕ) ^ 2) + d) := by
          have h₁₁ : (b * (r % (p : ℕ) ^ 2) + d) % (p : ℕ) ^ 2 = 0 := h₉
          exact Nat.dvd_of_mod_eq_zero h₁₁
        exact h₄ h₁₀
      exact h₆
    exact ⟨h₂, h₃⟩

/-- For any prime p, p² ≠ 0.
    This is needed to apply `Nat.chineseRemainderOfFinset`.
    Uses `Nat.Prime.pos : ∀ {p : ℕ}, Nat.Prime p → 0 < p` and
    `pow_ne_zero : ∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} [NoZeroDivisors M₀] (n :
    ℕ), a ≠ 0 → a ^ n ≠ 0`. -/
lemma prime_sq_ne_zero (p : Nat.Primes) : (p : ℕ) ^ 2 ≠ 0 := by
  have hp : Nat.Prime p := p.2
  exact pow_ne_zero 2 hp.pos.ne'

lemma crt_surjective (S : Finset Nat.Primes) (t : (p : Nat.Primes) → p ∈ S → ℕ)
    (ht : ∀ p (hp : p ∈ S), t p hp < (p : ℕ) ^ 2) :
    ∃ r, r < primeSquareProduct S ∧ ∀ p (hp : p ∈ S), r % ((p : ℕ) ^ 2) = t p hp := by
  -- Define the modulus function and residue function for chineseRemainderOfFinset
  let s : Nat.Primes → ℕ := fun p => (p : ℕ) ^ 2
  let a : Nat.Primes → ℕ := fun p => if h : p ∈ S then t p h else 0
  -- Apply CRT
  have hs : ∀ i ∈ S, s i ≠ 0 := fun p _ => prime_sq_ne_zero p
  have hcoprime : (S : Set Nat.Primes).Pairwise (Function.onFun Nat.Coprime s) :=
    pairwise_coprime_prime_squares S
  let r := Nat.chineseRemainderOfFinset a s S hs hcoprime
  use r
  constructor
  · -- r < primeSquareProduct S
    exact Nat.chineseRemainderOfFinset_lt_prod a s hs hcoprime
  · -- ∀ p (hp : p ∈ S), r % (p : ℕ) ^ 2 = t p hp
    intro p hp
    have hcong : (r : ℕ) ≡ a p [MOD s p] := r.2 p hp
    have ha : a p = t p hp := by simp [a, hp]
    rw [ha] at hcong
    exact Nat.mod_eq_of_modEq hcong (ht p hp)

lemma crtMap_mapsTo_pi (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (r : ℕ)
    (hr : r ∈ validResiduesMod b T S) (p : Nat.Primes) (hp : p ∈ S) :
    r % ((p : ℕ) ^ 2) ∈ localValidResidues (p : ℕ) b T := by
  -- Get the validity condition from hr
  simp only [validResiduesMod, Finset.mem_filter, Finset.mem_range] at hr
  obtain ⟨_, hvalid⟩ := hr
  -- Get the specific condition for our prime p
  have hp_cond := hvalid p hp
  -- Show r % p² is in range
  have hp_sq_pos : 0 < (p : ℕ) ^ 2 := sq_pos_of_pos p.prop.pos
  have hmod_lt : r % ((p : ℕ) ^ 2) < (p : ℕ) ^ 2 := Nat.mod_lt r hp_sq_pos
  -- Show r % p² satisfies the local validity conditions
  simp only [localValidResidues, Finset.mem_filter, Finset.mem_range]
  refine ⟨hmod_lt, ?_, ?_⟩
  · -- Show ¬ p² ∣ r % p²
    intro hdvd
    -- If p² ∣ (r % p²) and r % p² < p², then r % p² = 0
    have h_rmod_eq_zero : r % ((p : ℕ) ^ 2) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hmod_lt
    -- But r % p² = 0 implies p² ∣ r
    have hdvd_r : (p : ℕ) ^ 2 ∣ r := Nat.dvd_of_mod_eq_zero h_rmod_eq_zero
    exact hp_cond.1 hdvd_r
  · -- Show ∀ d ∈ T, ¬ p² ∣ b * (r % p²) + d
    intro d hd hdvd_shifted
    -- From hp_cond we have ¬ p² ∣ b * r + d
    have h_not_dvd := hp_cond.2 d hd
    -- r ≡ r % p² [MOD p²]
    have hmod : (r % ((p : ℕ) ^ 2)) ≡ r [MOD ((p : ℕ) ^ 2)] := Nat.mod_modEq r ((p : ℕ) ^ 2)
    -- so b * (r % p²) ≡ b * r [MOD p²]
    have hmul : b * (r % ((p : ℕ) ^ 2)) ≡ b * r [MOD ((p : ℕ) ^ 2)] := hmod.mul_left b
    -- so b * (r % p²) + d ≡ b * r + d [MOD p²]
    have hadd : b * (r % ((p : ℕ) ^ 2)) + d ≡ b * r + d [MOD ((p : ℕ) ^ 2)] := hmul.add_right d
    -- Apply dvd_iff
    have hdvd_equiv : ((p : ℕ) ^ 2 ∣ b * (r % ((p : ℕ) ^ 2)) + d) ↔ ((p : ℕ) ^ 2 ∣ b * r + d) :=
      hadd.dvd_iff dvd_rfl
    exact h_not_dvd (hdvd_equiv.mp hdvd_shifted)

lemma not_dvd_of_mod_eq_not_dvd (p r f : ℕ) (_hp : 0 < p ^ 2) (hr_eq : r % p ^ 2 = f)
    (hf_ndiv : ¬(p ^ 2 ∣ f)) : ¬(p ^ 2 ∣ r) := by
  intro h_dvd_r
  have h_mod_eq : r % p ^ 2 = 0 := by
    have h₁ : p ^ 2 ∣ r := h_dvd_r
    have h₂ : r % p ^ 2 = 0 := by
      -- If p² divides r, then the remainder when r is divided by p² is 0.
      have h₃ := Nat.mod_eq_zero_of_dvd h₁
      exact h₃
    exact h₂
  -- Since r % p ^ 2 = f and r % p ^ 2 = 0, we have f = 0.
  have h_f_eq_zero : f = 0 := by
    linarith
  -- If f = 0, then p² divides f (since p² is positive).
  have h_p_sq_dvd_f : p ^ 2 ∣ f := by
    have h₁ : f = 0 := h_f_eq_zero
    rw [h₁]
    exact by
      -- p² divides 0 because p² is positive.
      exact ⟨0, by simp⟩
  -- This contradicts the assumption that p² does not divide f.
  exact hf_ndiv h_p_sq_dvd_f

lemma not_dvd_shift_of_mod_eq (p b r f d : ℕ) (_hp : 0 < p ^ 2) (hr_eq : r % p ^ 2 = f)
    (hf_shift : ¬(p ^ 2 ∣ b * f + d)) : ¬(p ^ 2 ∣ b * r + d) := by
  intro h
  have h₁ : p ^ 2 ∣ b * r + d := h
  have h₂ : (b * r + d) % (p ^ 2) = 0 := by
    exact Nat.mod_eq_zero_of_dvd h₁
  have h₃ : (b * r + d) % (p ^ 2) = (b * f + d) % (p ^ 2) := by
    have h₄ : r % p ^ 2 = f := hr_eq
    have h₅ : b * r % (p ^ 2) = b * f % (p ^ 2) := by
      have h₆ : b * r % (p ^ 2) = (b * (r % p ^ 2)) % (p ^ 2) := by
        simp [Nat.mul_mod]
      rw [h₆]
      have h₇ : (b * (r % p ^ 2)) % (p ^ 2) = (b * f) % (p ^ 2) := by
        rw [h₄]
      rw [h₇]
    have h₈ : (b * r + d) % (p ^ 2) = (b * f + d) % (p ^ 2) := by
      have h₉ : (b * r + d) % (p ^ 2) = ((b * r) % (p ^ 2) + d % (p ^ 2)) % (p ^ 2) := by
        simp [Nat.add_mod]
      rw [h₉]
      have h₁₀ : (b * f + d) % (p ^ 2) = ((b * f) % (p ^ 2) + d % (p ^ 2)) % (p ^ 2) := by
        simp [Nat.add_mod]
      rw [h₁₀]
      have h₁₁ : (b * r) % (p ^ 2) = (b * f) % (p ^ 2) := by
        exact h₅
      rw [h₁₁]
    exact h₈
  have h₄ : (b * f + d) % (p ^ 2) = 0 := by
    rw [h₃] at h₂
    exact h₂
  have h₅ : p ^ 2 ∣ b * f + d := by
    have h₆ : (b * f + d) % (p ^ 2) = 0 := h₄
    exact Nat.dvd_of_mod_eq_zero h₆
  exact hf_shift h₅

lemma crt_inverse_mapsTo (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes)
    (f : (p : Nat.Primes) → p ∈ S → ℕ)
    (hf : ∀ p (hp : p ∈ S), f p hp ∈ localValidResidues (p : ℕ) b T) :
    ∃ r ∈ validResiduesMod b T S, ∀ p (hp : p ∈ S), r % ((p : ℕ) ^ 2) = f p hp := by
  -- Extract that f p hp < p ^ 2 from membership in localValidResidues
  have hf_bound : ∀ p (hp : p ∈ S), f p hp < (p : ℕ) ^ 2 := fun p hp => by
    have h := hf p hp
    simp only [localValidResidues, Finset.mem_filter, Finset.mem_range] at h
    exact h.1
  -- Use CRT to get r < M with r % p ^ 2 = f p hp
  obtain ⟨r, hr_lt, hr_mod⟩ := crt_surjective S f hf_bound
  -- Show r ∈ validResiduesMod b T S
  refine ⟨r, ?_, hr_mod⟩
  simp only [validResiduesMod, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact hr_lt
  · intro p hp
    -- We need to show ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^ 2 ∣ b * r + d)
    have hf_valid := hf p hp
    simp only [localValidResidues, Finset.mem_filter, Finset.mem_range] at hf_valid
    obtain ⟨_, hf_ndiv, hf_shift⟩ := hf_valid
    have hr_eq : r % ((p : ℕ) ^ 2) = f p hp := hr_mod p hp
    have hp_pos : 0 < (p : ℕ) ^ 2 := pow_pos (Nat.Prime.pos p.2) 2
    constructor
    · exact not_dvd_of_mod_eq_not_dvd (p : ℕ) r (f p hp) hp_pos hr_eq hf_ndiv
    · intro d hd
      exact not_dvd_shift_of_mod_eq (p : ℕ) b r (f p hp) d hp_pos hr_eq (hf_shift d hd)

lemma validResidues_equiv_pi (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    Nonempty ((validResiduesMod b T S) ≃ (S.pi (fun p => localValidResidues (p : ℕ) b T))) := by
  -- Define the forward map from validResiduesMod to the pi Finset
  have hfwd : ∀ r, r ∈ validResiduesMod b T S →
      (fun p (hp : p ∈ S) => r % ((p : ℕ) ^ 2)) ∈ S.pi (fun p => localValidResidues (p : ℕ) b T) :=
          by
    intro r hr
    rw [Finset.mem_pi]
    intro p hp
    exact crtMap_mapsTo_pi b T S r hr p hp
  let f : (validResiduesMod b T S) → (S.pi (fun p => localValidResidues (p : ℕ) b T)) :=
    fun ⟨r, hr⟩ => ⟨fun p hp => r % ((p : ℕ) ^ 2), hfwd r hr⟩
  -- Prove injectivity
  have hf_inj : Function.Injective f := by
    intro ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ heq
    simp only [Subtype.mk.injEq]
    have hr₁_lt : r₁ < primeSquareProduct S :=
      Finset.mem_filter.mp hr₁ |>.1 |> Finset.mem_range.mp
    have hr₂_lt : r₂ < primeSquareProduct S :=
      Finset.mem_filter.mp hr₂ |>.1 |> Finset.mem_range.mp
    apply crtMap_injective_on_range S hr₁_lt hr₂_lt
    have heq' := Subtype.mk.injEq _ _ _ _ |>.mp heq
    ext p hp
    have := congrFun₂ heq' p hp
    exact this
  -- Prove surjectivity
  have hf_surj : Function.Surjective f := by
    intro ⟨g, hg⟩
    have hg' : ∀ p (hp : p ∈ S), g p hp ∈ localValidResidues (p : ℕ) b T := by
      intro p hp
      rw [Finset.mem_pi] at hg
      exact hg p hp
    obtain ⟨r, hr, hr_eq⟩ := crt_inverse_mapsTo b T S g hg'
    use ⟨r, hr⟩
    apply Subtype.ext
    ext p hp
    exact hr_eq p hp
  -- Construct the equivalence
  exact ⟨Equiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩

lemma validResiduesMod_card_eq_pi_card (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    (validResiduesMod b T S).card =
      (S.pi (fun p => localValidResidues (p : ℕ) b T)).card := by
  exact Finset.card_eq_of_equiv (validResidues_equiv_pi b T S).some

/-- The cardinality of validResiduesMod equals the product of local valid residue cardinalities.

    The proof uses the Chinese Remainder Theorem. Key steps:
    1. The moduli p² for p ∈ S are pairwise coprime. For distinct primes p, q ∈ S, we have
       `(p² : ℕ).Coprime (q² : ℕ)` because distinct primes are coprime and
       `IsCoprime.pow : IsCoprime x y → IsCoprime (x ^ m) (y ^ n)` gives powers coprime.
    2. By CRT (`Nat.chineseRemainderOfFinset`), residues mod M = ∏_{p∈S} p² correspond
       bijectively to tuples (r_p)_{p∈S} where each r_p ∈ [0, p²).
    3. The validity condition factors coordinate-wise: r mod M is valid iff for each p ∈ S,
       - p² ∤ r ↔ (r mod p²) ≢ 0 (mod p²)
       - ∀ d ∈ T, p² ∤ (b*r + d) ↔ (b*(r mod p²) + d) ≢ 0 (mod p²)
    4. Hence validResiduesMod ≅ ∏_{p ∈ S} localValidResidues p b T as sets.
    5. Since the bijection preserves cardinality: |validResiduesMod| = ∏_{p∈S} |localValidResidues|.
    Definitions:
    - `localValidResidues p b T = (Finset.range (p ^ 2)).filter (λ r, ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^
    2 ∣ b*r+d))`
    - `validResiduesMod b T S = (Finset.range M).filter (λ r, ∀ p ∈ S, ¬(p ^ 2 ∣ r) ∧ ∀ d ∈ T, ¬(p ^
    2 ∣ b*r+d))`
      where M = ∏_{p∈S} p²
    Uses Mathlib's `Finset.card_pi : (s.pi t).card = ∏ i ∈ s, (t i).card` -/
lemma validResiduesMod_card_eq_prod (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    ((validResiduesMod b T S).card : ℝ) =
      ∏ p ∈ S, ((localValidResidues (p : ℕ) b T).card : ℝ) := by
  rw [validResiduesMod_card_eq_pi_card]
  rw [Finset.card_pi]
  simp only [Nat.cast_prod]

lemma validResidues_card_eq_mul (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) :
    ((validResiduesMod b T S).card : ℝ) =
      (primeSquareProduct S : ℝ) * localDensityProduct b T S := by
  -- Step 1: |validResiduesMod| = ∏ |localValidResidues|
  rw [validResiduesMod_card_eq_prod]
  -- Step 2: Each |localValidResidues p| = p² × localDensityFactor p
  conv_lhs =>
    arg 2
    ext p
    rw [localValidResidues_card_eq p p.prop b T]
  -- Step 3: ∏ (p² × localDensityFactor) = (∏ p²) × (∏ localDensityFactor)
  rw [Finset.prod_mul_distrib]
  -- Step 4: Simplify using definitions
  simp only [primeSquareProduct, localDensityProduct, Nat.cast_prod, Nat.cast_pow]

/-- Key lemma 3: The product of values in [0,1] is at most 1.
    If each factor ≤ 1 and factors are non-negative, then product ≤ 1.
    Uses: `Finset.prod_le_one` from Mathlib. -/
lemma localDensityProduct_le_one (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    localDensityProduct b T S ≤ 1 := by
  unfold localDensityProduct
  apply Finset.prod_le_one
  · intro p _
    exact localDensityFactor_nonneg p b T
  · intro p _
    exact localDensityFactor_le_one p b T

lemma prime_sq_dvd_primeSquareProduct (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S) :
    (p : ℕ) ^ 2 ∣ primeSquareProduct S := by
  have h₁ : (p : ℕ) ^ 2 ∣ ∏ q ∈ S, (q : ℕ) ^ 2 := by
    apply Finset.dvd_prod_of_mem; simp_all
  simpa [primeSquareProduct] using h₁

lemma dvd_iff_of_mod_eq_primeSquareProduct (S : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ S)
    (N₁ N₂ : ℕ) (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
  have h₁ : (p : ℕ) ^ 2 ∣ primeSquareProduct S := by
    -- Prove that p² divides the product of squares of primes in S
    have h₂ : (p : ℕ) ^ 2 ∣ ∏ q ∈ S, (q : ℕ) ^ 2 := by
      -- Since p is in S, p² is a factor of the product
      have h₃ : p ∈ S := hp
      have h₅ : (p : ℕ) ^ 2 ∣ ∏ q ∈ S, (q : ℕ) ^ 2 := by
        -- Use the fact that if p is in S, then p² divides the product
        apply Finset.dvd_prod_of_mem; simpa using h₃
      exact h₅
    -- Convert the product to the definition of primeSquareProduct
    simpa [primeSquareProduct] using h₂
  -- Use the given congruence and the fact that p² divides the modulus to get the desired
  -- equivalence
  have h₂ : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S := hmod
  have h₃ : N₁ ≡ N₂ [MOD primeSquareProduct S] := by
    -- Convert the modulus equality to congruence
    rw [Nat.ModEq]; simp_all
  -- Apply the theorem that if a ≡ b mod m and d divides m, then d divides a iff d divides b
  have h₄ : ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
    have h₇ : ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
      -- Use the fact that p² divides the modulus to get the equivalence
      have h₉ : ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
        -- Use the theorem Nat.ModEq.dvd_iff
        have h₁₀ : N₁ ≡ N₂ [MOD primeSquareProduct S] := h₃
        have h₁₁ : (p : ℕ) ^ 2 ∣ primeSquareProduct S := h₁
        -- Apply the theorem
        have h₁₂ : ((p : ℕ) ^ 2 ∣ N₁ ↔ (p : ℕ) ^ 2 ∣ N₂) := by
          -- Use the theorem Nat.ModEq.dvd_iff
          apply Nat.ModEq.dvd_iff h₁₀; exact h₁₁
        exact h₁₂
      exact h₉
    exact h₇
  exact h₄

lemma shifted_dvd_iff_of_mod_eq_primeSquareProduct (b d : ℕ) (S : Finset Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ S) (N₁ N₂ : ℕ)
    (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    ((p : ℕ) ^ 2 ∣ b * N₁ + d ↔ (p : ℕ) ^ 2 ∣ b * N₂ + d) := by
  have h₁ : (p : ℕ) ^ 2 ∣ primeSquareProduct S := by
    rw [primeSquareProduct]
    apply Finset.dvd_prod_of_mem; simp_all
  have h₂ : N₁ ≡ N₂ [MOD primeSquareProduct S] := by
    rw [Nat.ModEq]
    exact hmod
  have h₃ : N₁ ≡ N₂ [MOD (p : ℕ) ^ 2] := by
    have h₃ : N₁ ≡ N₂ [MOD primeSquareProduct S] := h₂
    have h₄ : (p : ℕ) ^ 2 ∣ primeSquareProduct S := h₁
    exact h₃.of_dvd h₄
  have h₄ : b * N₁ ≡ b * N₂ [MOD (p : ℕ) ^ 2] := by
    have h₄ : N₁ ≡ N₂ [MOD (p : ℕ) ^ 2] := h₃
    exact h₄.mul_left b
  have h₅ : b * N₁ + d ≡ b * N₂ + d [MOD (p : ℕ) ^ 2] := by
    have h₅ : b * N₁ ≡ b * N₂ [MOD (p : ℕ) ^ 2] := h₄
    exact h₅.add_right d
  have h₆ : ((p : ℕ) ^ 2 ∣ b * N₁ + d ↔ (p : ℕ) ^ 2 ∣ b * N₂ + d) := by
    have h₆ : b * N₁ + d ≡ b * N₂ + d [MOD (p : ℕ) ^ 2] := h₅
    have h₇ : (p : ℕ) ^ 2 ∣ (p : ℕ) ^ 2 := by
      apply Nat.dvd_refl
    have h₈ : ((p : ℕ) ^ 2 ∣ b * N₁ + d ↔ (p : ℕ) ^ 2 ∣ b * N₂ + d) := by
      apply Nat.ModEq.dvd_iff h₆ h₇
    exact h₈
  exact h₆

theorem condition_mod_invariant (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes)
    (N₁ N₂ : ℕ) (hmod : N₁ % primeSquareProduct S = N₂ % primeSquareProduct S) :
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N₁) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N₁ + d)) ↔
    (∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N₂) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N₂ + d)) := by
  constructor <;> intro h p hp
  · constructor
    · rw [← dvd_iff_of_mod_eq_primeSquareProduct S p hp N₁ N₂ hmod]
      exact (h p hp).1
    · intro d hd
      rw [← shifted_dvd_iff_of_mod_eq_primeSquareProduct b d S p hp N₁ N₂ hmod]
      exact (h p hp).2 d hd
  · constructor
    · rw [dvd_iff_of_mod_eq_primeSquareProduct S p hp N₁ N₂ hmod]
      exact (h p hp).1
    · intro d hd
      rw [shifted_dvd_iff_of_mod_eq_primeSquareProduct b d S p hp N₁ N₂ hmod]
      exact (h p hp).2 d hd

/-- The k-th complete block B_k = {kM+1, ..., (k+1)M}.
    For k < X/M, this block is entirely contained in [1, X]. -/
def completeBlock (M k : ℕ) : Finset ℕ := Finset.Icc (k * M + 1) ((k + 1) * M)

lemma primeSquareProduct_pos (S : Finset Nat.Primes) : 0 < primeSquareProduct S := by
  have h₁ : ∀ p : Nat.Primes, 0 < (p : ℕ) ^ 2 := by
    intro p
    have h₂ : (p : ℕ) ≥ 2 := by
      exact Nat.Prime.two_le p.prop
    have h₄ : 0 < (p : ℕ) ^ 2 := by positivity
    exact h₄
  have h₂ : 0 < ∏ p ∈ S, (p : ℕ) ^ 2 := by
    apply Finset.prod_pos
    intro p _
    exact h₁ p
  exact h₂

lemma completeBlocks_subset_Icc (M X : ℕ) (hM : 0 < M) (k : ℕ) (hk : k < X / M) :
    completeBlock M k ⊆ Finset.Icc 1 X := by
  have h₁ : completeBlock M k = Finset.Icc (k * M + 1) ((k + 1) * M) := rfl
  rw [h₁]
  have h₂ : (k + 1) * M ≤ X := by
    have h₄ : (k + 1) * M ≤ X := by
      have h₅ : (X / M) * M ≤ X := by
        apply Nat.div_mul_le_self
      calc
        (k + 1) * M ≤ (X / M) * M := by
          nlinarith
        _ ≤ X := h₅
    exact h₄
  have h₃ : 1 ≤ k * M + 1 := by
    have h₄ : 0 ≤ k * M := by positivity
    omega
  have h₄ : (k + 1) * M ≤ X := h₂
  have h₆ : Finset.Icc (k * M + 1) ((k + 1) * M) ⊆ Finset.Icc 1 X := by
    apply Finset.Icc_subset_Icc
    · -- Prove that 1 ≤ k * M + 1
      omega
    · -- Prove that (k + 1) * M ≤ X
      omega
  exact h₆

lemma completeBlock_card (M k : ℕ) (hM : 0 < M) : (completeBlock M k).card = M := by
  have h₁ : (completeBlock M k) = Finset.Icc (k * M + 1) ((k + 1) * M) := rfl
  rw [h₁]
  have h₂ : (k * M + 1) ≤ ((k + 1) * M) := by
    have h₄ : (k * M + 1) ≤ ((k + 1) * M) := by
      ring_nf at *
      nlinarith
    exact h₄
  rw [Finset.card_eq_sum_ones]
  simp; ring_nf at *; simp_all

lemma completeBlock_mapsTo (M k : ℕ) (hM : 0 < M) :
    Set.MapsTo (· % M) (completeBlock M k : Set ℕ) (Finset.range M : Set ℕ) := by
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_range, completeBlock] at hx ⊢
  have h₄ : x % M < M := Nat.mod_lt x hM
  simp_all

/-- For any x, y in the complete block [kM+1, (k+1)M], we have |y - x| < M.

    This follows because:
    - The block has width (k+1)M - (kM+1) = M - 1
    - So the maximum absolute difference between any two elements is M - 1 < M
    In integers: max(y) - min(x) = (k+1)M - (kM+1) = M - 1
    and min(y) - max(x) = (kM+1) - (k+1)M = 1 - M
    So |y - x| ≤ M - 1 < M.
    Mathlib coverage: This uses `abs_sub_lt_iff` and basic interval arithmetic.
-/
lemma abs_sub_lt_of_mem_completeBlock (M k x y : ℕ) (_hM : 0 < M)
    (hx : x ∈ completeBlock M k) (hy : y ∈ completeBlock M k) :
    |(y : ℤ) - (x : ℤ)| < (M : ℤ) := by
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
  obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
  rw [show (k + 1) * M = k * M + M from by ring] at hx2 hy2
  rw [abs_sub_lt_iff]
  omega

/-- The function N ↦ N % M is injective on the complete block.
    Two numbers in [kM+1, (k+1)M] with the same residue mod M must be equal,
    since they are within distance M of each other.
    The proof uses the fact that if x, y are in [kM+1, (k+1)M], then |x - y| < M.
    If x % M = y % M and |x - y| < M, then x = y (since the only multiple of M
    in (-M, M) is 0). -/
lemma completeBlock_injOn (M k : ℕ) (hM : 0 < M) :
    Set.InjOn (· % M) (completeBlock M k : Set ℕ) := by
  intro x hx y hy hmod
  apply Nat.ModEq.eq_of_abs_lt
  · rw [Nat.ModEq.eq_1]
    exact hmod
  · exact abs_sub_lt_of_mem_completeBlock M k x y hM hx hy

lemma completeBlock_surjOn (M k : ℕ) (hM : 0 < M) :
    Set.SurjOn (· % M) (completeBlock M k : Set ℕ) (Finset.range M : Set ℕ) := by
  have h₁ : ∀ r ∈ (Finset.range M : Set ℕ), ∃ N ∈ (completeBlock M k : Set ℕ), N % M = r := by
    intro r hr
    have h₂ : r < M := Finset.mem_range.mp hr
    have h₃ : r ≤ M := by linarith
    -- Case when r = 0
    by_cases h₄ : r = 0
    · -- If r = 0, we take N = (k + 1) * M
      have h₅ : ((k + 1) * M : ℕ) ∈ (completeBlock M k : Set ℕ) := by
        -- Prove that (k + 1) * M is in the complete block
        simp only [completeBlock, Finset.mem_coe, Finset.mem_Icc]
        constructor <;>
        (try norm_num);
        (try ring_nf);
        (try nlinarith)
      refine ⟨(k + 1) * M, h₅, ?_⟩
      -- Prove that ((k + 1) * M) % M = 0
      have h₆ : ((k + 1) * M : ℕ) % M = 0 := by
        simp
      rw [h₄] at *
      omega
    · -- If r ≠ 0, we take N = k * M + r
      have h₅ : (k * M + r : ℕ) ∈ (completeBlock M k : Set ℕ) := by
        -- Prove that k * M + r is in the complete block
        simp only [completeBlock, Finset.mem_coe, Finset.mem_Icc]
        constructor
        · -- Prove k * M + 1 ≤ k * M + r
          have h₆ : 1 ≤ r := by
            by_contra h₆
            have h₇ : r = 0 := by
              omega
            contradiction
          nlinarith
        · -- Prove k * M + r ≤ (k + 1) * M
          nlinarith
      refine ⟨(k * M + r : ℕ), h₅, ?_⟩
      -- Prove that (k * M + r) % M = r
      have h₆ : (k * M + r : ℕ) % M = r % M := by
        have h₇ : (k * M + r : ℕ) % M = r % M := by
          simp [Nat.add_mod]
        exact h₇
      have h₇ : r % M = r := by
        have h₈ : r < M := by
          exact h₂
        have h₉ : r % M = r := Nat.mod_eq_of_lt h₈
        exact h₉
      omega
  -- Use the previous result to prove that (· % M) is surjective on completeBlock M k onto
  -- Finset.range M
  intro r hr
  have h₂ : r ∈ (Finset.range M : Set ℕ) := hr
  have h₃ : ∃ N ∈ (completeBlock M k : Set ℕ), N % M = r := h₁ r h₂
  obtain ⟨N, hN, hN'⟩ := h₃
  refine ⟨N, hN, ?_⟩; simp_all

/-- For N in the k-th complete block, N mod M takes each value in {0, 1, ..., M-1} exactly once.
    This is because N ranges over kM+1, kM+2, ..., (k+1)M, and:
    - (kM+j) mod M = j for j = 1, ..., M-1
    - (k+1)M mod M = 0
    More precisely: the map N ↦ N % M is a bijection from B_k to {0, 1, ..., M-1}. -/
lemma completeBlock_residues_bijective (M k : ℕ) (hM : 0 < M) :
    Set.BijOn (· % M) (completeBlock M k : Set ℕ) (Finset.range M : Set ℕ) := by
  exact Set.BijOn.mk (completeBlock_mapsTo M k hM) (completeBlock_injOn M k hM) (
      completeBlock_surjOn M k hM)

lemma filter_mapsTo (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.MapsTo (· % M) ((completeBlock M k).filter P : Set ℕ) ((Finset.range M).filter P : Set ℕ) :=
        by
  intro M P N hN
  -- N ∈ (completeBlock M k).filter P means N ∈ completeBlock M k and P N
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hN ⊢
  obtain ⟨hNblock, hPN⟩ := hN
  constructor
  · -- N % M ∈ Finset.range M
    have hM : 0 < M := primeSquareProduct_pos S
    exact (completeBlock_residues_bijective M k hM).mapsTo hNblock
  · -- P (N % M)
    have hM : 0 < M := primeSquareProduct_pos S
    have hmodlt : N % M < M := Nat.mod_lt N hM
    have hmod : N % M % M = N % M := Nat.mod_eq_of_lt hmodlt
    exact (condition_mod_invariant b T S N (N % M) hmod.symm).mp hPN

/-- InjOn: the filter preserves injectivity from the original bijection.

    The proof proceeds as follows:
    1. By `completeBlock_residues_bijective`, N ↦ N % M is a bijection on completeBlock M k.
    2. By `Set.BijOn.injOn`, this means it is injective on completeBlock M k.
    3. Since (completeBlock M k).filter P ⊆ completeBlock M k (filter is a subset),
       by `Set.InjOn.mono`, the function is also injective on the filtered set.
    Uses:
    - `completeBlock_residues_bijective : 0 < M → Set.BijOn (· % M) (completeBlock M k)
    (Finset.range M)`
    - `Set.BijOn.injOn : ∀ {f s t}, Set.BijOn f s t → Set.InjOn f s`
    - `Set.InjOn.mono : ∀ {s₁ s₂ f}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁` -/
lemma filter_injOn (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.InjOn (· % M) ((completeBlock M k).filter P : Set ℕ) := by
  intro M P
  have hM : 0 < M := primeSquareProduct_pos S
  have h_injOn := completeBlock_injOn M k hM
  have h_subset : ((completeBlock M k).filter P : Set ℕ) ⊆ (completeBlock M k : Set ℕ) :=
    Finset.filter_subset P (completeBlock M k)
  exact h_injOn.mono h_subset

/-- SurjOn: for r ∈ range M with P(r), we find N ∈ completeBlock with N % M = r and P(N).

    The proof proceeds as follows:
    1. Take r ∈ (Finset.range M).filter P, so r ∈ Finset.range M and P(r) holds.
    2. By `completeBlock_residues_bijective`, the map is surjective onto Finset.range M.
    3. So there exists N ∈ completeBlock M k with N % M = r.
    4. Since r < M (being in Finset.range M), we have r % M = r, so N % M = r % M.
    5. By `condition_mod_invariant`, since N ≡ r (mod M), we have P(N) ↔ P(r).
    6. Since P(r) holds, P(N) holds.
    7. Therefore N ∈ (completeBlock M k).filter P, and N % M = r.
    Uses:
    - `completeBlock_surjOn : 0 < M → Set.SurjOn (· % M) (completeBlock M k) (Finset.range M)`
    - `Set.SurjOn : ∀ {f s t}, Set.SurjOn f s t ↔ t ⊆ f '' s`
    - `condition_mod_invariant : N₁ % M = N₂ % M → (P N₁ ↔ P N₂)` -/
lemma filter_surjOn (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.SurjOn (· % M) ((completeBlock M k).filter P : Set ℕ) ((Finset.range M).filter P : Set ℕ) :=
        by
  intro M P r hr
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hr
  obtain ⟨hr_range, hr_P⟩ := hr
  -- Get N from surjectivity of base map
  have hM : 0 < M := primeSquareProduct_pos S
  have hsurj := completeBlock_surjOn M k hM
  rw [Set.SurjOn] at hsurj
  have hr_range' : r ∈ (Finset.range M : Set ℕ) := hr_range
  obtain ⟨N, hN_block, hN_mod⟩ := hsurj hr_range'
  -- Show N satisfies P using condition_mod_invariant
  have hr_lt : r < M := Finset.mem_range.mp hr_range
  have hr_mod : r % M = r := Nat.mod_eq_of_lt hr_lt
  have hmod_eq : N % M = r % M := by simp only [hN_mod, hr_mod]
  have hP_equiv := condition_mod_invariant b T S N r hmod_eq
  have hN_P : P N := hP_equiv.mpr hr_P
  -- Construct the witness
  use N
  constructor
  · simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hN_block, hN_P⟩
  · exact hN_mod

lemma filter_card_eq_of_bijOn_filter (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.BijOn (· % M)
      ((completeBlock M k).filter P : Set ℕ)
      ((Finset.range M).filter P : Set ℕ) := by
  intro M P
  exact ⟨filter_mapsTo b T S k, filter_injOn b T S k, filter_surjOn b T S k⟩

/-- Each complete block B_k contributes exactly |A| valid integers.

    Since the map N ↦ N % M is a bijection from B_k to {0, ..., M-1}, and by
    condition_mod_invariant validity depends only on N % M, the count of valid N in B_k
    equals the count of valid residues in {0, ..., M-1}, which is |A|.
    Uses: condition_mod_invariant, completeBlock_residues_bijective -/
lemma completeBlock_valid_count (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (k : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = A.card := by
  intro M A
  -- The filtered block equals the valid residues via bijection
  have hbij := filter_card_eq_of_bijOn_filter b T S k
  exact Set.BijOn.finsetCard_eq _ hbij

lemma completeBlock_disjoint (M : ℕ) (_hM : 0 < M) (i j : ℕ) (hij : i < j) :
    Disjoint (completeBlock M i) (completeBlock M j) := by
  have h₁ : (i + 1) * M < j * M + 1 := by
    have h₃ : (i + 1) * M ≤ j * M := by
      nlinarith
    have h₄ : (i + 1) * M < j * M + 1 := by
      nlinarith
    exact h₄
  have h₂ : ((completeBlock M i) : Set ℕ) ∩ ((completeBlock M j) : Set ℕ) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro x hx
    simp only [Set.mem_inter_iff, completeBlock] at hx
    -- Extract the conditions from hx
    have h₃ : x ∈ (Finset.Icc (i * M + 1) ((i + 1) * M) : Finset ℕ) := hx.1
    have h₄ : x ∈ (Finset.Icc (j * M + 1) ((j + 1) * M) : Finset ℕ) := hx.2
    -- Convert the Finset membership to natural number conditions
    simp only [Finset.mem_Icc] at h₃ h₄
    -- Derive the inequalities
    linarith
  -- Convert the Set disjointness to Finset disjointness
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact_mod_cast h₂

/-- The complete blocks B_0, ..., B_{q-1} are pairwise disjoint.
    Block B_i = {iM+1, ..., (i+1)M} and B_j = {jM+1, ..., (j+1)M} are disjoint for i ≠ j
    because their ranges don't overlap.
    Uses: For i < j, (i+1)M < jM+1 so the intervals are disjoint. -/
lemma completeBlocks_pairwise_disjoint (M : ℕ) (hM : 0 < M) :
    (Set.univ : Set ℕ).PairwiseDisjoint (fun k => (completeBlock M k : Set ℕ)) := by
  intro i _ j _ hij
  rcases hij.lt_or_gt with h | h
  · exact Finset.disjoint_coe.mpr (completeBlock_disjoint M hM i j h)
  · exact (Finset.disjoint_coe.mpr (completeBlock_disjoint M hM j i h)).symm

/-- The sum of valid elements from all complete blocks ≤ count.

    Since blocks are disjoint and contained in [1,X], the union of filtered blocks
    is a subset of the filtered [1,X], so the sum of cardinalities is at most count.
    Uses: completeBlocks_pairwise_disjoint, completeBlocks_subset_Icc, Finset.card_biUnion -/
lemma sum_valid_from_blocks_le_count (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (Finset.range (X / M)).sum (fun k =>
        ((completeBlock M k).filter fun N =>
          ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card) ≤ count := by
  intro M count
  -- The key steps:
  -- 1. Sum of filtered block cards = card of biUnion of filtered blocks (by disjointness)
  -- 2. biUnion of filtered blocks ⊆ filtered [1, X] (each block is subset of [1, X])
  -- 3. So sum ≤ count
  have hM : 0 < M := primeSquareProduct_pos S
  let P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
  -- The disjoint blocks property for the range
  have hdisj : (↑(Finset.range (X / M)) : Set ℕ).PairwiseDisjoint
      (fun k => (completeBlock M k).filter P) := by
    intro i _ j _ hij
    simp only [Function.onFun, Finset.disjoint_iff_ne]
    intro x hxi y hyj
    have hblocks := completeBlocks_pairwise_disjoint M hM
    have hdisj_ij : Disjoint (completeBlock M i : Set ℕ) (completeBlock M j : Set ℕ) :=
      hblocks (Set.mem_univ i) (Set.mem_univ j) hij
    have hxi' : x ∈ completeBlock M i := Finset.mem_of_mem_filter x hxi
    have hyj' : y ∈ completeBlock M j := Finset.mem_of_mem_filter y hyj
    intro heq
    rw [heq] at hxi'
    rw [Set.disjoint_iff] at hdisj_ij
    exact hdisj_ij ⟨hxi', hyj'⟩
  -- The sum equals the cardinality of the biUnion
  have hsum : (Finset.range (X / M)).sum (fun k => ((completeBlock M k).filter P).card)
      = ((Finset.range (X / M)).biUnion (fun k => (completeBlock M k).filter P)).card := by
    rw [Finset.card_biUnion]
    · exact hdisj
  rw [hsum]
  -- The biUnion is a subset of [1, X].filter P
  have hsub : (Finset.range (X / M)).biUnion (fun k => (completeBlock M k).filter P)
      ⊆ (Finset.Icc 1 X).filter P := by
    rw [Finset.biUnion_subset]
    intro k hk
    apply Finset.filter_subset_filter
    exact completeBlocks_subset_Icc M X hM k (Finset.mem_range.mp hk)
  -- Apply card_le_card
  exact Finset.card_le_card hsub

lemma count_lower_bound (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (X / M) * A.card ≤ count := by
  intro M A count
  -- The sum over blocks equals q * |A| since each block contributes |A|
  have blocks_eq : (Finset.range (X / M)).sum (fun k =>
      ((completeBlock M k).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card) =
      (X / M) * A.card := by
    have h : ∀ k ∈ Finset.range (X / M),
        ((completeBlock M k).filter fun N =>
          ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = A.card :=
      fun k _ => completeBlock_valid_count b T S k
    rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc (X / M) * A.card = (Finset.range (X / M)).sum (fun k =>
        ((completeBlock M k).filter fun N =>
          ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card) := blocks_eq.symm
    _ ≤ count := sum_valid_from_blocks_le_count b T S X

/-- The partial block consists of the remaining integers {q*M+1, ..., X} where q = X/M. -/
def partialBlock (M X : ℕ) : Finset ℕ := Finset.Icc (X / M * M + 1) X

-- ==========================================================================
-- Helper lemmas
-- ==========================================================================

lemma partialBlock_subset_Icc (M X : ℕ) (_hM : 0 < M) :
    partialBlock M X ⊆ Finset.Icc 1 X := by
  dsimp [partialBlock]
  apply Finset.Icc_subset_Icc
  <;>
  (try norm_num)

lemma partialBlock_subset_Ico (M X : ℕ) (hM : 0 < M) :
    (partialBlock M X : Set ℕ) ⊆ ↑(Finset.Ico (X / M * M) (X / M * M + M)) := by
  unfold partialBlock
  rw [Finset.coe_Icc, Finset.coe_Ico]
  intro n hn
  simp only [Set.mem_Icc] at hn
  simp only [Set.mem_Ico]
  constructor
  · omega
  · calc n ≤ X := hn.2
      _ < X / M * M + M := Nat.lt_div_mul_add hM

/-- The residue map N ↦ N % M is injective on the partial block {q*M+1, ..., X}.
    This is because for any N in the partial block, N = q*M + k where 1 ≤ k ≤ r < M
    (where r = X % M), so N % M = k. Different elements have different k values.
    The key insight is that all elements lie within a single period of M:
    they are all in [q*M+1, q*M+r] where r < M.
    Uses: `Set.InjOn : ∀ {α : Type u_1} {β : Type u_2}, (α → β) → Set α → Prop`
    which states f is injective on s iff ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y. -/
lemma partialBlock_injOn_mod (M X : ℕ) :
    Set.InjOn (fun x => x % M) ↑(partialBlock M X) := by
  rcases eq_or_lt_of_le (Nat.zero_le M) with rfl | hM
  · -- Case M = 0: x % 0 = x, so the map is identity
    intro x _ y _ hxy
    simp only [Nat.mod_zero] at hxy
    exact hxy
  · -- Case M > 0: use Nat.mod_injOn_Ico via subset
    exact (Nat.mod_injOn_Ico (X / M * M) M).mono (partialBlock_subset_Ico M X hM)

lemma partialBlock_valid_mapsTo (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let validBlock := (partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
    Set.MapsTo (fun x => x % M) ↑validBlock ↑A := by
  intro M A validBlock N hN
  -- hN : N ∈ ↑validBlock, need to show (fun x => x % M) N ∈ ↑A
  rw [Finset.mem_coe] at hN ⊢
  -- hN : N ∈ validBlock, goal : N % M ∈ A
  rw [Finset.mem_filter] at hN
  obtain ⟨_, hvalid⟩ := hN
  -- hvalid : ∀ p ∈ S, ¬↑p ^ 2 ∣ N ∧ ∀ d ∈ T, ¬↑p ^ 2 ∣ b * N + d
  -- Goal: N % M ∈ A = validResiduesMod b T S
  simp only at *
  change N % M ∈ validResiduesMod b T S
  rw [validResiduesMod, Finset.mem_filter, Finset.mem_range]
  constructor
  · -- N % M < M
    exact Nat.mod_lt N (primeSquareProduct_pos S)
  · -- ∀ p ∈ S, ¬↑p ^ 2 ∣ N % M ∧ ∀ d ∈ T, ¬↑p ^ 2 ∣ b * (N % M) + d
    -- From Nat.mod_modEq: (N % M) ≡ N [MOD M]
    -- Using Nat.ModEq.eq_1: this means (N % M) % M = N % M
    have hmodEq : (N % M) ≡ N [MOD M] := Nat.mod_modEq N M
    have hmod : N % M = (N % M) % M := (Nat.ModEq.eq_1 M (N % M) N ▸ hmodEq).symm
    rw [← condition_mod_invariant b T S N (N % M) hmod]
    exact hvalid

lemma partialBlock_valid_count_le (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    ((partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card ≤ A.card := by
  intro M A
  let validBlock := (partialBlock M X).filter fun N =>
    ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)
  apply Finset.card_le_card_of_injOn (fun x => x % M)
  · exact partialBlock_valid_mapsTo b T S X
  · intro x hx y hy hxy
    have hx' : x ∈ partialBlock M X := Finset.mem_filter.mp hx |>.1
    have hy' : y ∈ partialBlock M X := Finset.mem_filter.mp hy |>.1
    exact partialBlock_injOn_mod M X hx' hy' hxy

lemma completeBlock_disjoint_partialBlock (M X : ℕ) (_hM : 0 < M) (k : ℕ) (hk : k < X / M) :
    Disjoint (completeBlock M k) (partialBlock M X) := by
  have h₁ : (completeBlock M k) ∩ (partialBlock M X) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro n hn
    simp only [completeBlock, partialBlock, Finset.mem_inter, Finset.mem_Icc] at hn
    -- Extract the inequalities from the intersection
    have h₈ : (k + 1) * M ≤ (X / M) * M := by
      have h₁₁ : (k + 1) * M ≤ (X / M) * M := by
        nlinarith
      exact h₁₁
    have h₁₁ : n ≤ (X / M) * M := by
      linarith
    omega
  -- Use the empty intersection to conclude disjointness
  exact Finset.disjoint_iff_inter_eq_empty.mpr h₁

lemma biUnion_completeBlocks_disjoint_partialBlock (M X : ℕ) (_hM : 0 < M) :
    Disjoint ((Finset.range (X / M)).biUnion (completeBlock M)) (partialBlock M X) := by
  have h_main : Disjoint ((Finset.range (X / M)).biUnion (completeBlock M)) (partialBlock M X) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    -- Use the property of the biUnion to get a specific k such that x is in completeBlock M k
    have h₁ : ∃ k, k ∈ Finset.range (X / M) ∧ x ∈ completeBlock M k := by
      simpa [Finset.mem_biUnion] using hx₁
    obtain ⟨k, hk₁, hk₂⟩ := h₁
    -- Use the fact that each complete block is disjoint from the partial block to derive a
    -- contradiction
    have h₂ : x ∉ partialBlock M X := by
      have h₃ : k < X / M := Finset.mem_range.mp hk₁
      have h₄ : x ∈ completeBlock M k := hk₂
      have h₅ : x ∈ Finset.Icc (k * M + 1) ((k + 1) * M) := by
        simpa [completeBlock] using h₄
      have h₇ : x ≤ (k + 1) * M := Finset.mem_Icc.mp h₅ |>.2
      have h₈ : x ∉ partialBlock M X := by
        intro h₉
        have h₁₀ : x ∈ Finset.Icc (X / M * M + 1) X := by
          simpa [partialBlock] using h₉
        have h₁₁ : (X / M * M + 1 : ℕ) ≤ x := Finset.mem_Icc.mp h₁₀ |>.1
        have h₁₄ : (k + 1 : ℕ) ≤ X / M := by
          omega
        have h₁₅ : (k + 1) * M ≤ X / M * M := by
          have h₁₆ : (k + 1 : ℕ) ≤ X / M := h₁₄
          have h₁₇ : (k + 1 : ℕ) * M ≤ (X / M) * M := by
            exact Nat.mul_le_mul_right M h₁₆
          exact h₁₇
        have h₁₈ : (X / M * M + 1 : ℕ) ≤ (k + 1) * M := by
          omega
        omega
      exact h₈
    -- Derive the contradiction
    exact h₂ hx₂
  exact h_main

lemma mem_completeBlock_of_div_lt (M X n : ℕ) (hM : 0 < M) (hn_pos : 1 ≤ n) (hn_le : n ≤ X)
    (hk : (n - 1) / M < X / M) : n ∈ completeBlock M ((n - 1) / M) := by
  have h₁ : n - 1 < (n - 1) / M * M + M := by
    have h₂ : (n - 1) % M < M := Nat.mod_lt (n - 1) hM
    have h₃ : (n - 1) = (n - 1) / M * M + (n - 1) % M := by
      have h₄ := Nat.div_add_mod (n - 1) M
      linarith
    linarith
  have h₂ : (n - 1) / M * M + 1 ≤ n := by
    have h₃ : n - 1 ≥ (n - 1) / M * M := by
      have h₄ : (n - 1) / M * M ≤ n - 1 := by
        have h₅ : (n - 1) / M * M ≤ n - 1 := by
          have h₆ := Nat.div_mul_le_self (n - 1) M
          linarith
        exact h₅
      omega
    have h₄ : (n - 1) / M * M + 1 ≤ n := by
      have h₅ : n ≥ 1 := by omega
      have h₆ : (n - 1) / M * M + 1 ≤ n := by
        cases n with
        | zero => omega
        | succ n =>
          cases n with
          | zero => omega
          | succ n =>
            simp at h₃ ⊢; ring_nf at h₃ ⊢; omega
      exact h₆
    exact h₄
  have h₃ : n ≤ ((n - 1) / M + 1) * M := by
    have h₄ : n ≤ ((n - 1) / M + 1) * M := by
      by_cases h₅ : M = 0
      · exfalso
        linarith
      · have h₇ : (n - 1) < ((n - 1) / M + 1) * M := by
          have h₈ : (n - 1) < ((n - 1) / M + 1) * M := by
            linarith
          exact h₈
        have h₈ : n ≤ ((n - 1) / M + 1) * M := by
          have h₁₀ : n ≤ ((n - 1) / M + 1) * M := by
            by_cases h₁₁ : n - 1 + 1 ≤ ((n - 1) / M + 1) * M
            · have h₁₂ : n = n - 1 + 1 := by
                omega
              omega
            · omega
          exact h₁₀
        exact h₈
    exact h₄
  have h₄ : n ∈ Finset.Icc ((n - 1) / M * M + 1) (((n - 1) / M + 1) * M) := by
    rw [Finset.mem_Icc]
    constructor <;>
    (try omega)
  simp only [completeBlock] at *
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add, Nat.add_mul] using h₄

lemma mem_partialBlock_of_div_eq (M X n : ℕ) (_hM : 0 < M) (hn_pos : 1 ≤ n) (hn_le : n ≤ X)
    (hk : (n - 1) / M = X / M) : n ∈ partialBlock M X := by
  have h₁ : X / M * M + 1 ≤ n := by
    have h₂ : (n - 1) / M = X / M := hk
    have h₃ : (n - 1) / M * M ≤ n - 1 := by
      have h₄ : (n - 1) / M * M ≤ n - 1 := by
        have h₅ : (n - 1) / M * M ≤ n - 1 := by
          apply Nat.div_mul_le_self
        exact h₅
      exact h₄
    have h₄ : X / M * M ≤ n - 1 := by
      calc
        X / M * M = (n - 1) / M * M := by rw [h₂]
        _ ≤ n - 1 := h₃
    have h₅ : X / M * M + 1 ≤ n := by
      have h₈ : X / M * M + 1 ≤ n := by
        have h₁₀ : n - 1 + 1 = n := by
          have h₁₂ : n - 1 + 1 = n := by
            omega
          exact h₁₂
        omega
      exact h₈
    exact h₅
  have h₂ : n ≤ X := hn_le
  have h₃ : n ∈ Finset.Icc (X / M * M + 1) X := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact h₁
    · exact h₂
  have h₄ : partialBlock M X = Finset.Icc (X / M * M + 1) X := rfl
  rw [h₄] at *
  exact h₃

lemma div_sub_one_le_div (M X n : ℕ) (hn_pos : 1 ≤ n) (hn_le : n ≤ X) :
    (n - 1) / M ≤ X / M := by
  have h : n - 1 ≤ X := by
    omega
  -- Use the fact that (n - 1) / M ≤ X / M if n - 1 ≤ X
  have h₁ : (n - 1) / M ≤ X / M := by
    apply Nat.div_le_div_right; omega
  exact h₁

/-- The interval [1,X] equals the disjoint union of complete blocks B_0,...,B_{q-1} and
    the partial block V = {qM+1,...,X}.
    Every n ∈ [1,X] falls into exactly one of:
    - Complete block B_k where k = (n-1)/M for k < q
    - Partial block V if (n-1)/M ≥ q
    Conversely, all elements in the blocks are in [1,X] by completeBlocks_subset_Icc
    and partialBlock_subset_Icc.
    Uses the division algorithm: n = (n-1)/M * M + (n-1)%M + 1. -/
theorem Icc_eq_biUnion_union_partialBlock (M X : ℕ) (hM : 0 < M) :
    Finset.Icc 1 X = ((Finset.range (X / M)).biUnion (completeBlock M)) ∪ partialBlock M X := by
  ext n
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_range]
  constructor
  · -- Forward direction: n ∈ [1,X] → n ∈ (⋃ blocks) ∪ V
    intro ⟨hn_pos, hn_le⟩
    have hk_le : (n - 1) / M ≤ X / M := div_sub_one_le_div M X n hn_pos hn_le
    rcases Nat.lt_or_eq_of_le hk_le with hk_lt | hk_eq
    · -- Case 1: k < q, so n ∈ B_k
      left
      exact ⟨(n - 1) / M, hk_lt, mem_completeBlock_of_div_lt M X n hM hn_pos hn_le hk_lt⟩
    · -- Case 2: k = q, so n ∈ V
      right
      exact mem_partialBlock_of_div_eq M X n hM hn_pos hn_le hk_eq
  · -- Backward direction: n ∈ (⋃ blocks) ∪ V → n ∈ [1,X]
    intro h
    rcases h with ⟨k, hk, hn_block⟩ | hn_partial
    · -- n is in some complete block B_k with k < q
      exact Finset.mem_Icc.mp (completeBlocks_subset_Icc M X hM k hk hn_block)
    · -- n is in the partial block V
      exact Finset.mem_Icc.mp (partialBlock_subset_Icc M X hM hn_partial)

lemma filtered_biUnion_disjoint_filtered_partialBlock (M X : ℕ) (_hM : 0 < M)
    (P : ℕ → Prop) [DecidablePred P] :
    Disjoint (((Finset.range (X / M)).biUnion (completeBlock M)).filter P)
             ((partialBlock M X).filter P) := by
  have h_disjoint_unfiltered : Disjoint ((Finset.range (X / M)).biUnion (completeBlock M)) (
      partialBlock M X) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [Finset.mem_biUnion, Finset.mem_range, completeBlock, partialBlock,
        Finset.mem_Icc] at hx₁ hx₂
    obtain ⟨k, hk₁, hk₂⟩ := hx₁
    have h₈ : (k + 1) * M ≤ (X / M) * M := by
      have h₈₂ : (k + 1) * M ≤ (X / M) * M := by
        nlinarith
      exact h₈₂
    have h₉ : x ≤ (X / M) * M := by
      nlinarith
    omega
  have h_main : Disjoint (((Finset.range (X / M)).biUnion (completeBlock M)).filter P) (
      (partialBlock M X).filter P) := by
    apply Finset.disjoint_filter_filter h_disjoint_unfiltered
  exact h_main

/-- Filtering preserves pairwise disjointness of Finsets: if the original Finsets are
    pairwise disjoint, then their filtered versions are too.
    Mathlib has `Finset.pairwiseDisjoint_filter : ∀ {α β : Type*} {s : Finset α} {f : α → Finset β},
      (↑s).PairwiseDisjoint f → ∀ (p : β → Prop), (↑s).PairwiseDisjoint (fun a => Finset.filter p (f
      a))`
    but this only works for Finsets `s`, not arbitrary sets.
    This follows from `Set.PairwiseDisjoint.mono :
      ∀ {s : Set ι} {f g : ι → α}, s.PairwiseDisjoint f → g ≤ f → s.PairwiseDisjoint g`
    combined with `Finset.filter_subset : ∀ (p : α → Prop) [DecidablePred p] (s : Finset α),
      Finset.filter p s ⊆ s` to show that filtering decreases each set.
    Since `(f k).filter P ⊆ f k` for all k, and disjointness is preserved under taking subsets,
    the filtered family inherits pairwise disjointness from the original family. -/
lemma pairwiseDisjoint_filter_of_pairwiseDisjoint {ι : Type*} (s : Set ι)
    (f : ι → Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hpwd : s.PairwiseDisjoint f) :
    s.PairwiseDisjoint (fun k => (f k).filter P) := by
  intro i hi j hj hij
  exact Disjoint.mono (Finset.filter_subset P (f i)) (Finset.filter_subset P (f j)) (hpwd hi hj hij)

lemma filtered_completeBlocks_pairwiseDisjoint (M : ℕ) (hM : 0 < M)
    (P : ℕ → Prop) [DecidablePred P] (s : Finset ℕ) :
    (↑s : Set ℕ).PairwiseDisjoint (fun k => (completeBlock M k).filter P) := by
  apply pairwiseDisjoint_filter_of_pairwiseDisjoint _ _ P
  have h := completeBlocks_pairwise_disjoint M hM
  rw [Finset.pairwiseDisjoint_coe] at h
  exact Set.PairwiseDisjoint.subset h (Set.subset_univ _)

lemma count_eq_sum_blocks (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    let blockCounts := ∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    let partialCount := ((partialBlock M X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    count = blockCounts + partialCount := by
  intro M count blockCounts partialCount
  -- Let P be the filtering predicate
  set P := fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d) with hP
  have hM : 0 < M := primeSquareProduct_pos S
  -- Step 1: Rewrite [1,X] as biUnion of blocks ∪ partial block
  have h_partition := Icc_eq_biUnion_union_partialBlock M X hM
  -- Step 2: The count is the card of filter P over the partition
  calc count
      = ((Finset.Icc 1 X).filter P).card := rfl
    _ = ((((Finset.range (X / M)).biUnion (completeBlock M)) ∪ partialBlock M X).filter P).card :=
        by
        rw [h_partition]
    _ = (((Finset.range (X / M)).biUnion (completeBlock M)).filter P ∪
         (partialBlock M X).filter P).card := by
        rw [Finset.filter_union]
    _ = (((Finset.range (X / M)).biUnion (completeBlock M)).filter P).card +
        ((partialBlock M X).filter P).card := by
        apply Finset.card_union_of_disjoint
        exact filtered_biUnion_disjoint_filtered_partialBlock M X hM P
    _ = ((Finset.range (X / M)).biUnion (fun k => (completeBlock M k).filter P)).card +
        partialCount := by
        rw [Finset.filter_biUnion]
    _ = (∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter P).card) + partialCount := by
        congr 1
        apply Finset.card_biUnion
        exact filtered_completeBlocks_pairwiseDisjoint M hM P (Finset.range (X / M))
    _ = blockCounts + partialCount := rfl

lemma count_upper_bound (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    count ≤ (X / M + 1) * A.card := by
  intro M A count
  -- Unfold count to the explicit formula
  show count ≤ (X / M + 1) * A.card
  -- Rewrite count using the block decomposition
  have hdecomp := count_eq_sum_blocks b T S X
  simp only at hdecomp
  -- count = blockCounts + partialCount
  have hcount_eq : count = ∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card +
      ((partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card := hdecomp
  rw [hcount_eq]
  -- Bound: sum over blocks + partial ≤ (X/M)*|A| + |A| = (X/M + 1)*|A|
  -- Each complete block contributes exactly |A|
  have hblock : ∀ k, ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = A.card :=
    fun k => completeBlock_valid_count b T S k
  -- Sum over blocks = (X/M) * |A|
  have hsum : ∑ k ∈ Finset.range (X / M), ((completeBlock M k).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card = (X / M) * A.card :=
          by
    simp only [hblock]
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hsum]
  -- Partial block contributes at most |A|
  have hpartial : ((partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card ≤ A.card :=
    partialBlock_valid_count_le b T S X
  -- Combine: (X/M)*|A| + partial ≤ (X/M)*|A| + |A| = (X/M + 1)*|A|
  calc X / M * A.card + ((partialBlock M X).filter fun N =>
      ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
      ≤ X / M * A.card + A.card := Nat.add_le_add_left hpartial _
    _ = (X / M + 1) * A.card := by ring

lemma count_bounds (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let A := validResiduesMod b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (X / M) * A.card ≤ count ∧ count ≤ (X / M + 1) * A.card := by
  constructor
  · exact count_lower_bound b T S X
  · exact count_upper_bound b T S X

/-- Helper: localDensityProduct is non-negative (product of non-negative factors). -/
lemma localDensityProduct_nonneg (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) :
    0 ≤ localDensityProduct b T S := by
  rw [localDensityProduct]
  -- Each factor in the product is non-negative
  exact Finset.prod_nonneg fun p _ => localDensityFactor_nonneg _ b T

lemma interval_bound {a b lo hi d : ℝ}
    (ha_lo : lo ≤ a) (ha_hi : a ≤ hi) (hb_lo : lo ≤ b) (hb_hi : b ≤ hi)
    (hd : hi - lo ≤ d) : |a - b| ≤ d := by
  have h₃ : |a - b| ≤ hi - lo := by
    rw [abs_le]
    constructor <;> linarith
  linarith

lemma floor_div_bounds (X M : ℕ) (hM : 0 < M) :
    (X / M) * M ≤ X ∧ X < (X / M + 1) * M := by
  have h_div_add_mod : X = M * (X / M) + (X % M) := (Nat.div_add_mod X M).symm
  have h_mod_lt : X % M < M := Nat.mod_lt X hM
  have h₁ : (X / M) * M ≤ X := Nat.div_mul_le_self X M
  have h₂ : X < (X / M + 1) * M := by nlinarith [h_div_add_mod, h_mod_lt]
  exact ⟨h₁, h₂⟩

/-- Helper: From count_bounds + validResidues_card_eq_mul, get the real-valued bounds. -/
lemma count_real_bounds (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let q := X / M
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    (q : ℝ) * M * L ≤ count ∧ (count : ℝ) ≤ (q + 1) * M * L := by
  intro M L q count
  -- Get integer bounds from count_bounds
  have hbounds := count_bounds b T S X
  simp only at hbounds
  -- Get |A| = M * L
  have hA := validResidues_card_eq_mul b hb T hT S
  -- Lower bound: q * |A| ≤ count
  constructor
  · -- Need: q * M * L ≤ count
    -- From hbounds.1: q * |A| ≤ count (as ℕ)
    -- From hA: |A| = M * L
    calc (q : ℝ) * M * L = q * (M * L) := by ring
      _ = q * (validResiduesMod b T S).card := by rw [← hA]
      _ = (q * (validResiduesMod b T S).card : ℕ) := by simp
      _ ≤ count := by exact Nat.cast_le.mpr hbounds.1
  · -- Upper bound: count ≤ (q + 1) * M * L
    calc (count : ℝ) ≤ ((q + 1) * (validResiduesMod b T S).card : ℕ) := by
           exact Nat.cast_le.mpr hbounds.2
      _ = (q + 1) * (validResiduesMod b T S).card := by simp
      _ = (q + 1) * (M * L) := by rw [← hA]
      _ = (q + 1) * M * L := by ring

lemma xL_real_bounds (X M : ℕ) (L : ℝ) (hL : 0 ≤ L) (hM : 0 < M) :
    let q := X / M
    (q : ℝ) * M * L ≤ (X : ℝ) * L ∧ (X : ℝ) * L ≤ (q + 1) * M * L := by
  intro q
  have h₁ : (q : ℕ) = X / M := rfl
  have h₂ : (q : ℝ) * M * L ≤ (X : ℝ) * L := by
    have h₃ : (q : ℕ) * M ≤ X := by
      have h₄ : (q : ℕ) = X / M := rfl
      have h₅ : (X / M : ℕ) * M ≤ X := by
        have h₆ : (X / M : ℕ) * M ≤ X := Nat.div_mul_le_self X M
        exact h₆
      simpa [h₄] using h₅
    have h₄ : (q : ℝ) * M ≤ (X : ℝ) := by
      have h₅ : (q : ℕ) * M ≤ X := h₃
      have h₇ : ((q : ℕ) * M : ℝ) ≤ (X : ℝ) := by
        norm_cast at h₅ ⊢
      linarith
    have h₅ : (q : ℝ) * M * L ≤ (X : ℝ) * L := by
      nlinarith
    exact h₅
  have h₃ : (X : ℝ) * L ≤ (q + 1) * M * L := by
    have h₄ : X ≤ (q : ℕ) * M + M := by
      have h₅ : (q : ℕ) = X / M := rfl
      have h₆ : X ≤ (X / M : ℕ) * M + M := by
        have h₇ : X < (X / M + 1) * M := by
          have h₈ : X < (X / M + 1) * M := by
            have h₁₀ : X < (X / M + 1) * M := by
              nlinarith [Nat.div_add_mod X M, Nat.mod_lt X (by positivity : 0 < M)]
            exact h₁₀
          exact h₈
        have h₈ : X ≤ (X / M : ℕ) * M + M := by
          have h₉ : X < (X / M + 1) * M := h₇
          have h₁₀ : (X / M + 1) * M = (X / M : ℕ) * M + M := by
            ring_nf
          rw [h₁₀] at h₉
          omega
        exact h₈
      simpa [h₅] using h₆
    have h₅ : (X : ℝ) ≤ ((q : ℕ) * M + M : ℝ) := by
      have h₆ : X ≤ (q : ℕ) * M + M := h₄
      norm_cast at h₆ ⊢
    have h₆ : (X : ℝ) * L ≤ ((q : ℕ) * M + M : ℝ) * L := by
      nlinarith
    have h₇ : ((q : ℕ) * M + M : ℝ) * L = (q + 1 : ℝ) * M * L := by
      have h₉ : ((q : ℕ) * M + M : ℝ) = (q + 1 : ℝ) * M := by
        norm_cast; simp [h₁]; ring_nf
      calc
        ((q : ℕ) * M + M : ℝ) * L = ((q + 1 : ℝ) * M) * L := by rw [h₉]
        _ = (q + 1 : ℝ) * M * L := by ring
    rw [h₇] at h₆
    exact h₆
  exact ⟨h₂, h₃⟩

lemma final_error_bound {count X M : ℕ} {L : ℝ} {q : ℕ}
    (hcount_lo : (q : ℝ) * M * L ≤ count)
    (hcount_hi : (count : ℝ) ≤ (q + 1) * M * L)
    (hxL_lo : (q : ℝ) * M * L ≤ (X : ℝ) * L)
    (hxL_hi : (X : ℝ) * L ≤ (q + 1) * M * L)
    (_hL_nonneg : 0 ≤ L)
    (hL_le_one : L ≤ 1) :
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := by
  have h_upper : (count : ℝ) - (X : ℝ) * L ≤ (M : ℝ) := by nlinarith
  have h_lower : (-(M : ℝ)) ≤ (count : ℝ) - (X : ℝ) * L := by nlinarith
  have h_main : |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := abs_le.mpr ⟨h_lower, h_upper⟩
  exact h_main

lemma error_bound_empty_case (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) (hM : primeSquareProduct S = 0) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := by
  have h_prod_pos : 0 < primeSquareProduct S := by
    have h₁ : ∀ (p : Nat.Primes), 0 < (p : ℕ) ^ 2 := by
      intro p
      have h₂ : 0 < (p : ℕ) := by
        exact Nat.cast_pos.mpr (Nat.Prime.pos p.2)
      positivity
    -- Use the fact that the product of positive numbers is positive
    have h₂ : 0 < ∏ p ∈ S, (p : ℕ) ^ 2 := by
      apply Finset.prod_pos
      intro p _
      exact h₁ p
    -- Since the product is positive, it is greater than 0
    simpa [primeSquareProduct] using h₂
  have h_false : False := by
    linarith
  exfalso
  exact h_false

/-- Key lemma 6: Both the count and X·L lie in the interval [q·M·L, (q+1)·M·L],
    so their difference is at most M·L ≤ M.
    From count_bounds: q·|A_M| ≤ count ≤ (q+1)·|A_M|
    From validResidues_card_eq_mul: |A_M| = M·L
    So: q·M·L ≤ count ≤ (q+1)·M·L
    Also: q ≤ X/M < q+1 (where q = floor(X/M)), so q·M ≤ X < (q+1)·M
    Therefore: q·M·L ≤ X·L ≤ (q+1)·M·L
    Both values in same interval of length M·L, so |count - X·L| ≤ M·L ≤ M. -/
lemma error_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    let M := primeSquareProduct S
    let L := localDensityProduct b T S
    let count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card
    |(count : ℝ) - (X : ℝ) * L| ≤ (M : ℝ) := by
  intro M L count
  -- Step 1: Get the interval bounds for count and X*L
  have hcount := count_real_bounds b hb T hT S X
  have hL_nonneg := localDensityProduct_nonneg b T S
  have hL_le_one := localDensityProduct_le_one b T S
  -- Step 2: Get the bounds for X*L
  -- Need to handle the M = 0 case (empty S)
  by_cases hM : M = 0
  · -- If M = 0, the edge case lemma applies
    exact error_bound_empty_case b hb T hT S X hM
  · -- M > 0
    have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have hxL := xL_real_bounds X M L hL_nonneg hM_pos
    -- Step 3: Apply final_error_bound with the derived bounds
    exact final_error_bound hcount.1 hcount.2 hxL.1 hxL.2 hL_nonneg hL_le_one

lemma count_finite_prime_approx (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    |(((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card : ℝ) -
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T| ≤
      (∏ p ∈ S, (p : ℕ) ^ 2 : ℝ) := by
  have h := error_bound b hb T hT S X
  simp only [primeSquareProduct, localDensityProduct] at h
  convert h using 2
  simp only [Nat.cast_prod, Nat.cast_pow]

lemma hasProd_implies_finite_approx (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Finset Nat.Primes, ∀ S : Finset Nat.Primes, A ⊆ S →
      |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε := by
  -- Step 1: Get multipliability and hasProd
  have h_multi := jointSquarefreeDensity_multipliable b hb T hT
  have h_hasProd := Multipliable.hasProd h_multi
  -- Step 2: Convert HasProd to Tendsto
  rw [HasProd.eq_1] at h_hasProd
  simp only [SummationFilter.unconditional_filter] at h_hasProd
  -- Step 3: Use Metric.tendsto_nhds to get eventually statement
  rw [Metric.tendsto_nhds] at h_hasProd
  specialize h_hasProd ε hε
  -- Step 4: Extract existence from eventually atTop
  rw [Filter.eventually_atTop] at h_hasProd
  obtain ⟨A, hA⟩ := h_hasProd
  use A
  intro S hAS
  specialize hA S hAS
  rwa [Real.dist_eq] at hA

/-- For any ε > 0, the tail contribution from primes p > y to the joint density
    (measuring how much the finite product differs from the infinite product)
    can be made arbitrarily small by choosing y large enough.
    Uses jointSquarefreeDensity_multipliable to ensure convergence. -/
lemma finite_product_converges_to_density (b : ℕ) (hb : 2 ≤ b)
    (T : Finset ℕ) (hT : T ⊆ Finset.range b) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, ∀ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) →
      |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε := by
  -- Get the finite set A that approximates the infinite product within ε
  obtain ⟨A, hA⟩ := hasProd_implies_finite_approx b hb T hT ε hε
  -- Define y as the maximum prime in A (or 0 if A is empty)
  use A.image (fun p : Nat.Primes => (p : ℕ)) |>.sup id
  intro S hS
  apply hA S
  -- Show A ⊆ S: for any p ∈ A, we have (p : ℕ) ≤ y, so p ∈ S by hypothesis
  intro p hp
  apply hS p
  calc (p : ℕ) = id (p : ℕ) := rfl
    _ ≤ (A.image (fun q : Nat.Primes => (q : ℕ))).sup id :=
        Finset.le_sup (Finset.mem_image_of_mem _ hp)

/-- Upper bound: For any S, C(X) ≤ #{N ≤ X : N satisfies S-conditions} since C(X)
    imposes more constraints. Combined with count_finite_prime_approx, this gives
    limsup C(X)/X ≤ D(b,T). -/
lemma count_upper_bound_via_finite (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (countJointSquarefree b T X : ℝ) ≤
      ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card := by
  rw [Nat.cast_le]
  apply Finset.card_le_card
  intro N hN
  simp only [Finset.mem_filter] at hN ⊢
  refine ⟨hN.1, ?_⟩
  intro p _
  obtain ⟨hSqN, hSqAll⟩ := hN.2
  constructor
  · -- Show ¬(p ^ 2 ∣ N)
    rw [Nat.squarefree_iff_prime_squarefree] at hSqN
    rw [sq]
    exact hSqN p p.prop
  · -- Show ∀ d ∈ T, ¬(p ^ 2 ∣ b*N+d)
    intro d hd
    have hSqd := hSqAll d hd
    rw [Nat.squarefree_iff_prime_squarefree] at hSqd
    rw [sq]
    exact hSqd p p.prop

/-- The number of `N ∈ [1, X]` such that for every `p ∈ S` we have `p² ∤ N` and `p² ∤ b * N + d`
for all `d ∈ T` (i.e. the square-free conditions checked only at the primes in `S`). -/
noncomputable def countFinitePrime (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun N =>
    ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card

/-- The primes `p ≤ n`, packaged as a `Finset Nat.Primes`. -/
def primesUpTo (n : ℕ) : Finset Nat.Primes :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).subtype Nat.Prime |>.image (fun ⟨p, hp⟩ => ⟨p,
      hp⟩)

lemma mem_primesUpTo (n : ℕ) (p : Nat.Primes) :
    (p : ℕ) ≤ n → p ∈ primesUpTo n := by
  intro hpn
  have h1 : (p : ℕ) ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) := by
    have h₁ : (p : ℕ) < n + 1 := by omega
    have h₂ : (p : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.mpr h₁
    have h₃ : Nat.Prime (p : ℕ) := p.prop
    exact Finset.mem_filter.mpr ⟨h₂, h₃⟩
  have h2 : (⟨(p : ℕ), p.prop⟩ : { q : ℕ // Nat.Prime q }) ∈ (Finset.filter Nat.Prime (
      Finset.range (n + 1))).subtype Nat.Prime := by
    simp only [Finset.mem_subtype] at h1 ⊢
    exact h1
  have h5 : p ∈ ((Finset.filter Nat.Prime (Finset.range (n + 1))).subtype Nat.Prime).image (fun ⟨q,
      hq⟩ => ⟨q, hq⟩) := by
    apply Finset.mem_image.mpr
    refine ⟨⟨(p : ℕ), p.prop⟩, h2, ?_⟩
    simp
  simpa [primesUpTo] using h5

lemma crt_error_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    |(countFinitePrime b T S X : ℝ) - (X : ℝ) * localDensityProduct b T S| ≤
      (primeSquareProduct S : ℝ) := by
  let M := primeSquareProduct S
  let L := localDensityProduct b T S
  let q := X / M
  let count := countFinitePrime b T S X
  have hM_pos : 0 < M := primeSquareProduct_pos S
  have hL_nonneg : 0 ≤ L := localDensityProduct_nonneg b T S
  have hL_le_one : L ≤ 1 := localDensityProduct_le_one b T S
  have h_count_bounds := count_real_bounds b hb T hT S X
  have h_xL_bounds := xL_real_bounds X M L hL_nonneg hM_pos
  exact final_error_bound h_count_bounds.1 h_count_bounds.2 h_xL_bounds.1 h_xL_bounds.2
    hL_nonneg hL_le_one

lemma count_finite_lower (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (countFinitePrime b T S X : ℝ) ≥ (X : ℝ) * localDensityProduct b T S -
      (primeSquareProduct S : ℝ) := by
  have h := crt_error_bound b hb T hT S X
  have h' := neg_abs_le ((countFinitePrime b T S X : ℝ) - (X : ℝ) * localDensityProduct b T S)
  linarith

lemma finite_product_ge_density (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) :
    localDensityProduct b T S ≥ jointSquarefreeDensity b T := by
  let f := fun p : Nat.Primes => localDensityFactor (p : ℕ) b T
  have hmult := jointSquarefreeDensity_multipliable b hb T hT
  have hmult_S : Multipliable (f ∘ Subtype.val (p := (· ∈ S))) := Finset.multipliable S f
  have hmult_compl : Multipliable (f ∘ Subtype.val (p := (· ∉ S))) :=
    multipliable_compl_of_multipliable b hb T hT S
  have hfactor : (∏' (x : {p : Nat.Primes // p ∈ S}), f x) *
                 (∏' (x : {p : Nat.Primes // p ∉ S}), f x) =
                 (∏' (p : Nat.Primes), f p) :=
    Multipliable.tprod_mul_tprod_compl hmult_S hmult_compl
  have hcompl_le : (∏' (x : {p : Nat.Primes // p ∉ S}), f x) ≤ 1 :=
    tprod_compl_le_one b hb T hT S
  have hS_eq : (∏' (x : {p : Nat.Primes // p ∈ S}), f x) = ∏ p ∈ S, f p :=
    Finset.tprod_subtype S f
  have hS_nonneg : 0 ≤ (∏' (x : {p : Nat.Primes // p ∈ S}), f x) := by
    rw [hS_eq]
    apply Finset.prod_nonneg
    intro p _
    exact localDensityFactor_nonneg p b T
  unfold localDensityProduct jointSquarefreeDensity
  rw [ge_iff_le, ← hfactor, ← hS_eq]
  have h1 : (∏' (x : {p // p ∈ S}), f ↑x) * (∏' (x : {p // p ∉ S}), f ↑x)
          ≤ (∏' (x : {p // p ∈ S}), f ↑x) * 1 := by
    apply mul_le_mul_of_nonneg_left hcompl_le hS_nonneg
  simp only [mul_one] at h1
  exact h1

lemma jointSquarefree_subset_finitePrime (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) ⊆
    (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N +
        d)) := by
  intro N hN
  simp only [Finset.mem_filter] at hN ⊢
  refine ⟨hN.1, ?_⟩
  intro p _
  obtain ⟨hSqN, hSqAll⟩ := hN.2
  constructor
  · rw [Nat.squarefree_iff_prime_squarefree] at hSqN
    rw [sq]
    exact hSqN p p.prop
  · intro d hd
    have hSqd := hSqAll d hd
    rw [Nat.squarefree_iff_prime_squarefree] at hSqd
    rw [sq]
    exact hSqd p p.prop

lemma not_squarefree_has_prime_sq_divisor (n : ℕ) (h : ¬Squarefree n) :
    ∃ p : Nat.Primes, (p : ℕ) ^ 2 ∣ n := by
  have h₁ : ¬ (∀ (x : ℕ), Nat.Prime x → ¬x * x ∣ n) := by
    intro h₂
    have h₃ : Squarefree n := by
      rw [Nat.squarefree_iff_prime_squarefree]
      exact h₂
    contradiction
  have h₂ : ∃ (x : ℕ), Nat.Prime x ∧ x * x ∣ n := by
    by_contra! h₃
    have h₄ : ∀ (x : ℕ), Nat.Prime x → ¬x * x ∣ n := fun x hx => h₃ x hx
    exact h₁ h₄
  obtain ⟨p, hp, hp'⟩ := h₂
  refine ⟨⟨p, hp⟩, ?_⟩
  simpa [pow_two] using hp'

lemma sdiff_subset_violations (b : ℕ) (T : Finset ℕ) (S : Finset Nat.Primes) (X : ℕ) :
    (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N +
        d)) \
    (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) ⊆
    (Finset.Icc 1 X).filter (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (
        q : ℕ) ^ 2 ∣ b * N + d)) := by
  intro N hN
  rw [Finset.mem_sdiff] at hN
  rw [Finset.mem_filter] at hN ⊢
  obtain ⟨⟨hNIcc, hNS⟩, hNotG⟩ := hN
  refine ⟨hNIcc, ?_⟩
  simp only [Finset.mem_filter, not_and] at hNotG
  specialize hNotG hNIcc
  by_cases hSqN : Squarefree N
  · have hNotAll := hNotG hSqN
    push Not at hNotAll
    obtain ⟨d, hd_mem, hd_not_sq⟩ := hNotAll
    obtain ⟨q, hq_dvd⟩ := not_squarefree_has_prime_sq_divisor (b * N + d) hd_not_sq
    refine ⟨q, ?_, Or.inr ⟨d, hd_mem, hq_dvd⟩⟩
    intro hqS
    have := (hNS q hqS).2 d hd_mem
    exact this hq_dvd
  · obtain ⟨q, hq_dvd⟩ := not_squarefree_has_prime_sq_divisor N hSqN
    refine ⟨q, ?_, Or.inl hq_dvd⟩
    intro hqS
    have := (hNS q hqS).1
    exact this hq_dvd

lemma count_ge_finite_minus_violations (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ)
    (_hT : T ⊆ Finset.range b) (S : Finset Nat.Primes) (X : ℕ) :
    (countJointSquarefree b T X : ℝ) ≥ (countFinitePrime b T S X : ℝ) -
      ((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card := by
  let A := (Finset.Icc 1 X).filter (fun N => Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d))
  let B := (Finset.Icc 1 X).filter (fun N => ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣
      b * N + d))
  let V := (Finset.Icc 1 X).filter (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (
      q : ℕ) ^ 2 ∣ b * N + d))
  change (A.card : ℝ) ≥ (B.card : ℝ) - (V.card : ℝ)
  have hAB : A ⊆ B := jointSquarefree_subset_finitePrime b T S X
  have hDiff : B \ A ⊆ V := sdiff_subset_violations b T S X
  have hCard : (B \ A).card + A.card = B.card := Finset.card_sdiff_add_card_eq_card hAB
  have hDiffCard : (B \ A).card ≤ V.card := Finset.card_le_card hDiff
  have h2 : (A.card : ℤ) ≥ B.card - V.card := by omega
  have h3 : (A.card : ℝ) ≥ (B.card : ℤ) - (V.card : ℤ) := by exact_mod_cast h2
  simp only [Int.cast_natCast] at h3
  exact h3

lemma combine_bounds_lower (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) (hX : 0 < X)
    (δ₁ δ₂ : ℝ)
    (hδ₁ : (((Finset.Icc 1 X).filter fun N =>
          ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
              d)).card : ℝ) / X < δ₁)
    (hδ₂ : (primeSquareProduct S : ℝ) / X < δ₂) :
    (countJointSquarefree b T X : ℝ) / X ≥ jointSquarefreeDensity b T - δ₁ - δ₂ := by
  have h1 := count_ge_finite_minus_violations b hb T hT S X
  have h2 := count_finite_lower b hb T hT S X
  have h3 := finite_product_ge_density b hb T hT S
  have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  set V := ((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card with hV
  set M := primeSquareProduct S with hM
  set L := localDensityProduct b T S with hL
  set D := jointSquarefreeDensity b T with hD
  set C := countJointSquarefree b T X with hC
  set Cs := countFinitePrime b T S X with hCs
  have hCbound : (C : ℝ) ≥ (X : ℝ) * L - (M : ℝ) - (V : ℝ) := by linarith
  have hCdiv : (C : ℝ) / (X : ℝ) ≥ L - (M : ℝ) / (X : ℝ) - (V : ℝ) / (X : ℝ) := by
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    rw [ge_iff_le, sub_sub, ← add_div, le_div_iff₀ hXpos]
    have heq : (L - ((M : ℝ) + (V : ℝ)) / (X : ℝ)) * (X : ℝ) = L * (X : ℝ) - (M : ℝ) - (V : ℝ) := by
      field_simp
      ring
    rw [heq]
    linarith
  have hCdiv' : (C : ℝ) / (X : ℝ) ≥ D - (M : ℝ) / (X : ℝ) - (V : ℝ) / (X : ℝ) := by linarith
  linarith

/-- If a prime q is in s, then q.val ≤ s.sup (·.val).

    Uses `Finset.le_sup : ∀ {α β} [SemilatticeSup α] [OrderBot α] {s : Finset β} {f : β → α} {b :
    β},
    b ∈ s → f b ≤ s.sup f`.
    Equivalently, if q.val > s.sup (·.val), then q ∉ s. -/
lemma gt_sup_imp_not_mem (s : Finset Nat.Primes) (q : Nat.Primes) (hq : (q : ℕ) > s.sup (·.val)) :
    q ∉ s := by
  intro hq_mem
  have h := Finset.le_sup (f := fun x : Nat.Primes => (x : ℕ)) hq_mem
  simp only at h
  omega

lemma tsum_primes_gt_le_tsum_compl (f : Nat.Primes → ℝ) (hf : ∀ p, 0 ≤ f p) (hsum : Summable f)
    (s : Finset Nat.Primes) :
    ∑' (p : {q : Nat.Primes // (q : ℕ) > s.sup (·.val)}), f p ≤
    ∑' (p : {q : Nat.Primes // q ∉ s}), f p := by
  apply Summable.tsum_le_tsum_of_inj
    (fun x => ⟨x.val, gt_sup_imp_not_mem s x.val x.property⟩)
  · intro ⟨a, ha⟩ ⟨b, hb⟩ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  · intro c _
    exact hf c.val
  · intro i
    rfl
  · exact hsum.subtype _
  · exact hsum.subtype _

lemma exists_finset_tsum_compl_lt (f : Nat.Primes → ℝ) (_hf : ∀ p, 0 ≤ f p) (_hsum : Summable f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset Nat.Primes, ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
  have h₁ : Filter.Tendsto (fun s : Finset Nat.Primes => ∑' (p : {q : Nat.Primes // q ∉ s}),
      f p) Filter.atTop (nhds 0) := by
    have h₄ : Filter.Tendsto (fun s : Finset Nat.Primes => ∑' (p : {q : Nat.Primes // q ∉ s}),
        f p) Filter.atTop (nhds 0) := by
      -- Use the fact that the sum over the complement tends to 0 as the set grows
      -- This is a lemma in the Lean library, but we need to find the correct application.
      -- We use the fact that the sum over the complement of an increasing sequence of sets tends to
      -- 0.
      -- We can use the fact that the sum over the complement of all finite sets is 0.
      -- We use the fact that the sum over the complement of a finite set is less than the sum over
      -- all primes.
      -- We use the fact that the sum over all primes is finite because f is summable.
      -- We use the fact that the sum over the complement of a finite set is less than the sum over
      -- all primes.
      -- We use the fact that the sum over the complement of a finite set is less than the sum over
      -- all primes.
      -- We can use the fact that the sum over the complement of a finite set is less than the sum
      -- over all primes.
      -- We use the fact that the sum over the complement of a finite set is less than the sum over
      -- all primes.
      -- We use the fact that the sum over the complement of a finite set is less than the sum over
      -- all primes.
      have h₅ : Filter.Tendsto (fun s : Finset Nat.Primes => ∑' (p : {q : Nat.Primes // q ∉ s}),
          f p) Filter.atTop (nhds 0) := by
        -- Use the fact that the sum over the complement tends to 0 as the set grows
        -- This is a lemma in the Lean library, but we need to find the correct application.
        -- We use the fact that the sum over the complement of an increasing sequence of sets tends
        -- to 0.
        -- We can use the fact that the sum over the complement of all finite sets is 0.
        -- We use the fact that the sum over the complement of a finite set is less than the sum
        -- over all primes.
        -- We use the fact that the sum over all primes is finite because f is summable.
        -- We use the fact that the sum over the complement of a finite set is less than the sum
        -- over all primes.
        -- We use the fact that the sum over the complement of a finite set is less than the sum
        -- over all primes.
        -- We can use the fact that the sum over the complement of a finite set is less than the sum
        -- over all primes.
        -- We use the fact that the sum over the complement of a finite set is less than the sum
        -- over all primes.
        -- We use the fact that the sum over the complement of a finite set is less than the sum
        -- over all primes.
        have h₇ : Filter.Tendsto (fun s : Finset (Nat.Primes) => ∑' (a : { q : Nat.Primes // q ∉
            s }), f a) Filter.atTop (nhds 0) := by
          -- Use the fact that the sum over the complement tends to 0 as the set grows
          -- This is a lemma in the Lean library, but we need to find the correct application.
          -- We use the fact that the sum over the complement of an increasing sequence of sets
          -- tends to 0.
          -- We can use the fact that the sum over the complement of all finite sets is 0.
          -- We use the fact that the sum over the complement of a finite set is less than the sum
          -- over all primes.
          -- We use the fact that the sum over all primes is finite because f is summable.
          -- We use the fact that the sum over the complement of a finite set is less than the sum
          -- over all primes.
          -- We use the fact that the sum over the complement of a finite set is less than the sum
          -- over all primes.
          -- We can use the fact that the sum over the complement of a finite set is less than the
          -- sum over all primes.
          -- We use the fact that the sum over the complement of a finite set is less than the sum
          -- over all primes.
          -- We use the fact that the sum over the complement of a finite set is less than the sum
          -- over all primes.
          exact tendsto_tsum_compl_atTop_zero f
        simpa using h₇
      exact h₅
    exact h₄
  have h₂ : ∃ (s : Finset Nat.Primes), ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
    have h₅ : ∃ (s : Finset Nat.Primes), ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
      -- Use the fact that the limit of the tail sums is 0 to find the required finite set s
      have h₆ : ∀ ε > 0, ∃ (s : Finset Nat.Primes), ∀ (s' : Finset Nat.Primes), s ⊆ s' → ∑' (
          p : {q : Nat.Primes // q ∉ s'}), f p < ε := by
        intro ε hε
        -- Use the definition of tendsto to find a finite set s such that the sum over the
        -- complement is less than ε
        have h₈ : ∃ (s : Finset Nat.Primes), ∀ (s' : Finset Nat.Primes), s ⊆ s' → ∑' (
            p : {q : Nat.Primes // q ∉ s'}), f p < ε := by
          -- Use the definition of tendsto to find a finite set s such that the sum over the
          -- complement is less than ε
          have h₉ : ∀ ε > 0, ∃ (s : Finset Nat.Primes), ∀ (s' : Finset Nat.Primes), s ⊆ s' → ∑' (
              p : {q : Nat.Primes // q ∉ s'}), f p < ε := by
            intro ε hε
            -- Use the definition of tendsto to find a finite set s such that the sum over the
            -- complement is less than ε
            have h₁₀ : Filter.Tendsto (fun s : Finset Nat.Primes => ∑' (p : {q : Nat.Primes // q ∉
                s}), f p) Filter.atTop (nhds 0) := h₁
            -- Use the definition of tendsto to find a finite set s such that the sum over the
            -- complement is less than ε
            have h₁₁ : ∃ (s : Finset Nat.Primes), ∀ (s' : Finset Nat.Primes), s ⊆ s' → ∑' (
                p : {q : Nat.Primes // q ∉ s'}), f p < ε := by
              -- Use the definition of tendsto to find a finite set s such that the sum over the
              -- complement is less than ε
              have h₁₂ : ∃ (s : Finset Nat.Primes), ∀ (s' : Finset Nat.Primes), s ⊆ s' → ∑' (
                  p : {q : Nat.Primes // q ∉ s'}), f p < ε := by
                -- Use the definition of tendsto to find a finite set s such that the sum over the
                -- complement is less than ε
                -- This is a placeholder for the actual proof, which would use the definition of
                -- tendsto and properties of filters
                -- to find the required finite set s.
                exact by
                  -- Use the fact that the sum over the complement tends to 0 as the set grows
                  -- to find a finite set s such that the sum over the complement is less than ε.
                  -- This is a placeholder for the actual proof, which would use the definition of
                  -- tendsto and properties of filters
                  -- to find the required finite set s.
                  have h₁₃ := Metric.tendsto_atTop.mp h₁₀ ε hε
                  -- Use the fact that the sum over the complement tends to 0 as the set grows
                  -- to find a finite set s such that the sum over the complement is less than ε.
                  -- This is a placeholder for the actual proof, which would use the definition of
                  -- tendsto and properties of filters
                  -- to find the required finite set s.
                  simp only [Real.dist_eq, abs_lt] at h₁₃
                  -- Use the fact that the sum over the complement tends to 0 as the set grows
                  -- to find a finite set s such that the sum over the complement is less than ε.
                  -- This is a placeholder for the actual proof, which would use the definition of
                  -- tendsto and properties of filters
                  -- to find the required finite set s.
                  obtain ⟨s, hs⟩ := h₁₃
                  -- Use the fact that the sum over the complement tends to 0 as the set grows
                  -- to find a finite set s such that the sum over the complement is less than ε.
                  -- This is a placeholder for the actual proof, which would use the definition of
                  -- tendsto and properties of filters
                  -- to find the required finite set s.
                  refine ⟨s, ?_⟩
                  -- Use the fact that the sum over the complement tends to 0 as the set grows
                  -- to find a finite set s such that the sum over the complement is less than ε.
                  -- This is a placeholder for the actual proof, which would use the definition of
                  -- tendsto and properties of filters
                  -- to find the required finite set s.
                  intro s' hs'
                  -- Use the fact that the sum over the complement tends to 0 as the set grows
                  -- to find a finite set s such that the sum over the complement is less than ε.
                  -- This is a placeholder for the actual proof, which would use the definition of
                  -- tendsto and properties of filters
                  -- to find the required finite set s.
                  simp_all
              -- Use the fact that the sum over the complement tends to 0 as the set grows
              -- to find a finite set s such that the sum over the complement is less than ε.
              -- This is a placeholder for the actual proof, which would use the definition of
              -- tendsto and properties of filters
              -- to find the required finite set s.
              exact h₁₂
            -- Use the fact that the sum over the complement tends to 0 as the set grows
            -- to find a finite set s such that the sum over the complement is less than ε.
            -- This is a placeholder for the actual proof, which would use the definition of tendsto
            -- and properties of filters
            -- to find the required finite set s.
            exact h₁₁
          -- Use the fact that the sum over the complement tends to 0 as the set grows
          -- to find a finite set s such that the sum over the complement is less than ε.
          -- This is a placeholder for the actual proof, which would use the definition of tendsto
          -- and properties of filters
          -- to find the required finite set s.
          exact h₉ ε hε
        -- Use the fact that the sum over the complement tends to 0 as the set grows
        -- to find a finite set s such that the sum over the complement is less than ε.
        -- This is a placeholder for the actual proof, which would use the definition of tendsto and
        -- properties of filters
        -- to find the required finite set s.
        exact h₈
      -- Use the fact that the sum over the complement tends to 0 as the set grows
      -- to find a finite set s such that the sum over the complement is less than ε.
      -- This is a placeholder for the actual proof, which would use the definition of tendsto and
      -- properties of filters
      -- to find the required finite set s.
      have h₇ : ∃ (s : Finset Nat.Primes), ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
        -- Use the fact that the sum over the complement tends to 0 as the set grows
        -- to find a finite set s such that the sum over the complement is less than ε.
        -- This is a placeholder for the actual proof, which would use the definition of tendsto and
        -- properties of filters
        -- to find the required finite set s.
        have h₈ : ∀ ε > 0, ∃ (s : Finset Nat.Primes), ∀ (s' : Finset Nat.Primes), s ⊆ s' → ∑' (
            p : {q : Nat.Primes // q ∉ s'}), f p < ε := h₆
        -- Use the fact that the sum over the complement tends to 0 as the set grows
        -- to find a finite set s such that the sum over the complement is less than ε.
        -- This is a placeholder for the actual proof, which would use the definition of tendsto and
        -- properties of filters
        -- to find the required finite set s.
        have h₉ : ∃ (s : Finset Nat.Primes), ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
          -- Use the fact that the sum over the complement tends to 0 as the set grows
          -- to find a finite set s such that the sum over the complement is less than ε.
          -- This is a placeholder for the actual proof, which would use the definition of tendsto
          -- and properties of filters
          -- to find the required finite set s.
          obtain ⟨s, hs⟩ := h₈ ε hε
          -- Use the fact that the sum over the complement tends to 0 as the set grows
          -- to find a finite set s such that the sum over the complement is less than ε.
          -- This is a placeholder for the actual proof, which would use the definition of tendsto
          -- and properties of filters
          -- to find the required finite set s.
          refine ⟨s, ?_⟩
          -- Use the fact that the sum over the complement tends to 0 as the set grows
          -- to find a finite set s such that the sum over the complement is less than ε.
          -- This is a placeholder for the actual proof, which would use the definition of tendsto
          -- and properties of filters
          -- to find the required finite set s.
          have h₁₀ : ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
            -- Use the fact that the sum over the complement tends to 0 as the set grows
            -- to find a finite set s such that the sum over the complement is less than ε.
            -- This is a placeholder for the actual proof, which would use the definition of tendsto
            -- and properties of filters
            -- to find the required finite set s.
            have h₁₁ : ∀ (s' : Finset Nat.Primes), s ⊆ s' → ∑' (p : {q : Nat.Primes // q ∉ s'}),
                f p < ε := hs
            -- Use the fact that the sum over the complement tends to 0 as the set grows
            -- to find a finite set s such that the sum over the complement is less than ε.
            -- This is a placeholder for the actual proof, which would use the definition of tendsto
            -- and properties of filters
            -- to find the required finite set s.
            have h₁₂ : ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
              -- Use the fact that the sum over the complement tends to 0 as the set grows
              -- to find a finite set s such that the sum over the complement is less than ε.
              -- This is a placeholder for the actual proof, which would use the definition of
              -- tendsto and properties of filters
              -- to find the required finite set s.
              have h₁₃ : ∑' (p : {q : Nat.Primes // q ∉ s}), f p < ε := by
                -- Use the fact that the sum over the complement tends to 0 as the set grows
                -- to find a finite set s such that the sum over the complement is less than ε.
                -- This is a placeholder for the actual proof, which would use the definition of
                -- tendsto and properties of filters
                -- to find the required finite set s.
                have h₁₄ := h₁₁ s (by simp)
                -- Use the fact that the sum over the complement tends to 0 as the set grows
                -- to find a finite set s such that the sum over the complement is less than ε.
                -- This is a placeholder for the actual proof, which would use the definition of
                -- tendsto and properties of filters
                -- to find the required finite set s.
                simpa using h₁₄
              -- Use the fact that the sum over the complement tends to 0 as the set grows
              -- to find a finite set s such that the sum over the complement is less than ε.
              -- This is a placeholder for the actual proof, which would use the definition of
              -- tendsto and properties of filters
              -- to find the required finite set s.
              exact h₁₃
            -- Use the fact that the sum over the complement tends to 0 as the set grows
            -- to find a finite set s such that the sum over the complement is less than ε.
            -- This is a placeholder for the actual proof, which would use the definition of tendsto
            -- and properties of filters
            -- to find the required finite set s.
            exact h₁₂
          -- Use the fact that the sum over the complement tends to 0 as the set grows
          -- to find a finite set s such that the sum over the complement is less than ε.
          -- This is a placeholder for the actual proof, which would use the definition of tendsto
          -- and properties of filters
          -- to find the required finite set s.
          exact h₁₀
        -- Use the fact that the sum over the complement tends to 0 as the set grows
        -- to find a finite set s such that the sum over the complement is less than ε.
        -- This is a placeholder for the actual proof, which would use the definition of tendsto and
        -- properties of filters
        -- to find the required finite set s.
        exact h₉
      -- Use the fact that the sum over the complement tends to 0 as the set grows
      -- to find a finite set s such that the sum over the complement is less than ε.
      -- This is a placeholder for the actual proof, which would use the definition of tendsto and
      -- properties of filters
      -- to find the required finite set s.
      exact h₇
    -- Use the fact that the sum over the complement tends to 0 as the set grows
    -- to find a finite set s such that the sum over the complement is less than ε.
    -- This is a placeholder for the actual proof, which would use the definition of tendsto and
    -- properties of filters
    -- to find the required finite set s.
    exact h₅
  -- Use the fact that the sum over the complement tends to 0 as the set grows
  -- to find a finite set s such that the sum over the complement is less than ε.
  -- This is a placeholder for the actual proof, which would use the definition of tendsto and
  -- properties of filters
  -- to find the required finite set s.
  exact h₂

lemma prime_tail_sum_small (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, ∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 < ε :=
        by
  -- Get a finite set s with small complement sum
  set f : Nat.Primes → ℝ := fun p => 1 / ((p : ℕ) : ℝ) ^ 2 with hf
  have hfnn : ∀ p, 0 ≤ f p := fun p => by simp only [hf]; positivity
  obtain ⟨s, hs⟩ := exists_finset_tsum_compl_lt f hfnn primes_summable_one_div_sq ε hε
  -- Use y = sup of primes in s
  use s.sup (·.val)
  -- Primes > y are not in s, so their sum is bounded by the complement sum
  have h1 : ∑' (p : {q : Nat.Primes // (q : ℕ) > s.sup (·.val)}), f p ≤
            ∑' (p : {q : Nat.Primes // q ∉ s}), f p := by
    apply tsum_primes_gt_le_tsum_compl
    · exact hfnn
    · exact primes_summable_one_div_sq
  simp only [hf] at h1 hs
  exact lt_of_le_of_lt h1 hs

lemma prime_count_le_sqrt (M : ℕ) :
    (M.sqrt.primesBelow).card ≤ Nat.sqrt M := by
  calc (M.sqrt.primesBelow).card ≤ (Finset.range (M.sqrt)).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
    _ = M.sqrt := Finset.card_range _

lemma sqrt_div_X_small (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (Nat.sqrt X : ℝ) / X < ε := by
  have h₁ : 0 < (1 / ε : ℝ) := by positivity
  have h₂ : 0 < (1 / ε : ℝ) ^ 2 := by positivity
  -- Use the Archimedean property to find X₀ : ℕ such that (X₀ : ℝ) > (1 / ε)²
  have h₃ : ∃ (X₀ : ℕ), (1 / ε : ℝ) ^ 2 < (X₀ : ℝ) := by
    obtain ⟨X₀, hX₀⟩ := exists_nat_gt ((1 / ε : ℝ) ^ 2)
    refine ⟨X₀, ?_⟩
    exact_mod_cast hX₀
  obtain ⟨X₀, hX₀⟩ := h₃
  -- We need to show that for all X ≥ X₀, (Nat.sqrt X : ℝ) / X < ε
  refine ⟨X₀, ?_⟩
  intro X hX
  have h₄ : (X : ℝ) ≥ (X₀ : ℝ) := by exact_mod_cast hX
  have h₆ : 0 < (X : ℝ) := by
    by_contra h
    have h₁₀ : (X₀ : ℕ) = 0 := by
      by_contra _
      linarith
    have h₁₁ : (1 / ε : ℝ) ^ 2 < (X₀ : ℝ) := hX₀
    have h₁₂ : (X₀ : ℝ) = 0 := by simp [h₁₀]
    rw [h₁₂] at h₁₁
    norm_num at h₁₁ ⊢; nlinarith [h₂]
  -- Now we know (X : ℝ) > 0, so we can take square roots
  have h₇ : Real.sqrt (X : ℝ) > 1 / ε := by
    have h₈ : Real.sqrt (X : ℝ) > 1 / ε := by
      have h₉ : Real.sqrt (X : ℝ) > 0 := Real.sqrt_pos.mpr (by positivity)
      have h₁₁ : (Real.sqrt (X : ℝ)) ^ 2 = (X : ℝ) := by
        rw [Real.sq_sqrt]; positivity
      nlinarith [Real.sqrt_nonneg (X : ℝ), Real.sq_sqrt (by positivity : 0 ≤ (X : ℝ))]
    exact h₈
  have h₈ : 1 / Real.sqrt (X : ℝ) < ε := by
    have h₁₂ : 1 / Real.sqrt (X : ℝ) < ε := by
      calc
        1 / Real.sqrt (X : ℝ) < 1 / (1 / ε) := by
          apply one_div_lt_one_div_of_lt
          · positivity
          · linarith
        _ = ε := by
          field_simp
    exact h₁₂
  -- Now we need to relate (Nat.sqrt X : ℝ) / X to 1 / Real.sqrt (X : ℝ)
  have h₉ : (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) := by
    have h₁₁ : (Nat.sqrt X : ℝ) ^ 2 ≤ (X : ℝ) := by
      norm_cast
      have h₁₂ : (Nat.sqrt X : ℕ) ^ 2 ≤ X := by
        nlinarith [Nat.sqrt_le X, Nat.lt_succ_sqrt X]
      exact_mod_cast h₁₂
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (X : ℝ)),
      sq_nonneg ((Nat.sqrt X : ℝ) - Real.sqrt (X : ℝ))]
  -- Finally, we can put it all together
  have h₁₀ : (Nat.sqrt X : ℝ) / X ≤ 1 / Real.sqrt (X : ℝ) := by
    have h₁₁ : 0 < (X : ℝ) := by positivity
    calc
      (Nat.sqrt X : ℝ) / X ≤ Real.sqrt (X : ℝ) / X := by
        gcongr
      _ = 1 / Real.sqrt (X : ℝ) := by
        have h₁₄ : Real.sqrt (X : ℝ) > 0 := by positivity
        field_simp [h₁₁.ne', h₁₄.ne'];
        nlinarith [Real.sq_sqrt (by positivity : 0 ≤ (X : ℝ))]
  have h₁₁ : (Nat.sqrt X : ℝ) / X < ε := by
    calc
      (Nat.sqrt X : ℝ) / X ≤ 1 / Real.sqrt (X : ℝ) := h₁₀
      _ < ε := h₈
  exact h₁₁

lemma card_multiples_Icc (q : ℕ) (X : ℕ) :
    ((Finset.Icc 1 X).filter fun N => q ^ 2 ∣ N).card ≤ X / q ^ 2 := by
  have h_subset : ((Finset.Icc 1 X).filter fun N => q ^ 2 ∣ N) ⊆ (Finset.range (X + 1)).filter (
      fun k => k ≠ 0 ∧ q ^ 2 ∣ k) := by
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hN ⊢
    exact ⟨by omega, by omega, hN.2⟩
  have h_card_bound : ((Finset.Icc 1 X).filter fun N => q ^ 2 ∣ N).card ≤ ((Finset.range (X +
      1)).filter (fun k => k ≠ 0 ∧ q ^ 2 ∣ k)).card := Finset.card_le_card h_subset
  have h_card_multiples' : ((Finset.range (X + 1)).filter (fun k => k ≠ 0 ∧ q ^ 2 ∣ k)).card =
      X / q ^ 2 := Nat.card_multiples' X (q ^ 2)
  have h_main : ((Finset.Icc 1 X).filter fun N => q ^ 2 ∣ N).card ≤ X / q ^ 2 := by aesop
  exact h_main
/-- For natural numbers X, v, r with r > 0:
    ⌊(X - v)/r⌋ - ⌊-v/r⌋ ≤ ⌊X/r⌋ + 1  (as integer floor over ℝ).
    The proof uses the general inequality ⌊a⌋ - ⌊b⌋ ≤ ⌊a - b⌋ + 1 for any real a, b.
    Since ⌊x⌋ ≤ x < ⌊x⌋ + 1 and ⌊y⌋ ≤ y < ⌊y⌋ + 1, we have
    ⌊x⌋ - ⌊y⌋ < (x - y) + 1, and as the left side is an integer, ⌊x⌋ - ⌊y⌋ ≤ ⌊x - y⌋ + 1.
    Instantiate with x = (X - v)/r and y = -v/r. Then x - y = X/r.
    Thus ⌊(X - v)/r⌋ - ⌊-v/r⌋ ≤ ⌊X/r⌋ + 1.
    No direct Mathlib theorem found for this floor subtraction inequality.
    Searched: "floor_sub", "Int.floor_sub", "sub_floor". -/
lemma floor_diff_bound (X v r : ℕ) (hr : 0 < r) :
    ⌊((X : ℝ) - v) / r⌋ - ⌊(-(v : ℝ)) / r⌋ ≤ ⌊(X : ℝ) / r⌋ + 1 := by
  have h₁ : ⌊((X : ℝ) - v) / r⌋ - ⌊(-(v : ℝ)) / r⌋ ≤ ⌊(X : ℝ) / r⌋ + 1 := by
    have h₂ : ⌊((X : ℝ) - v) / r⌋ - ⌊(-(v : ℝ)) / r⌋ ≤ ⌊(X : ℝ) / r⌋ + 1 := by
      have h₃ : ((X : ℝ) - v) / r - (-(v : ℝ)) / r = (X : ℝ) / r := by
        have h₄ : (r : ℝ) ≠ 0 := by positivity
        field_simp [h₄]; ring_nf
      have h₄ : ⌊((X : ℝ) - v) / r⌋ - ⌊(-(v : ℝ)) / r⌋ ≤ ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ + 1 :=
          by
        have h₅ : ⌊((X : ℝ) - v) / r⌋ - ⌊(-(v : ℝ)) / r⌋ ≤ ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ +
            1 := by
          -- Use the property of floor functions for subtraction
          have h₆ : (⌊((X : ℝ) - v) / r⌋ : ℝ) ≤ ((X : ℝ) - v) / r := by exact Int.floor_le (
              ((X : ℝ) - v) / r)
          have h₇ : (⌊(-(v : ℝ)) / r⌋ : ℝ) ≤ (-(v : ℝ)) / r := by exact Int.floor_le (
              (-(v : ℝ)) / r)
          have h₉ : (-(v : ℝ)) / r < (⌊(-(v : ℝ)) / r⌋ : ℝ) + 1 := by exact Int.lt_floor_add_one (
              (-(v : ℝ)) / r)
          have h₁₀ : ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ ≥ ⌊((X : ℝ) - v) / r⌋ - ⌊(-(v : ℝ)) / r⌋ -
              1 := by
            -- Use the property of floor functions for subtraction
            have h₁₂ : ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ ≥ ⌊((X : ℝ) - v) / r⌋ -
                ⌊(-(v : ℝ)) / r⌋ - 1 := by
              have h₁₄ : ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ ≥ ⌊((X : ℝ) - v) / r⌋ -
                  ⌊(-(v : ℝ)) / r⌋ - 1 := by
                -- Use the property of floor functions for subtraction
                have h₁₅ : (⌊((X : ℝ) - v) / r⌋ : ℤ) - (⌊(-(v : ℝ)) / r⌋ : ℤ) - 1 ≤ ⌊((X : ℝ) -
                    v) / r - (-(v : ℝ)) / r⌋ := by
                  -- Use the property of floor functions for subtraction
                  have h₁₇ : (⌊((X : ℝ) - v) / r⌋ : ℤ) - (⌊(-(v : ℝ)) / r⌋ : ℤ) - 1 ≤ ⌊((X : ℝ) -
                      v) / r - (-(v : ℝ)) / r⌋ := by
                    -- Use the property of floor functions for subtraction
                    have h₁₈ : (⌊((X : ℝ) - v) / r⌋ : ℝ) - (⌊(-(v : ℝ)) / r⌋ : ℝ) - 1 ≤ ((X : ℝ) -
                        v) / r - (-(v : ℝ)) / r := by
                      linarith [h₆, h₇]
                    have h₁₉ : (⌊((X : ℝ) - v) / r⌋ : ℤ) - (⌊(-(v : ℝ)) / r⌋ : ℤ) - 1 ≤ ⌊((X : ℝ) -
                        v) / r - (-(v : ℝ)) / r⌋ := by
                      -- Use the property of floor functions for subtraction
                      apply Int.le_floor.mpr
                      norm_num at h₁₈ ⊢;
                      (try linarith)
                    exact h₁₉
                  exact h₁₇
                have h₂₁ : ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ ≥ (⌊((X : ℝ) - v) / r⌋ : ℤ) - (
                    ⌊(-(v : ℝ)) / r⌋ : ℤ) - 1 := by
                  linarith
                have h₂₂ : ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ ≥ ⌊((X : ℝ) - v) / r⌋ -
                    ⌊(-(v : ℝ)) / r⌋ - 1 := by
                  norm_num at h₂₁ ⊢;
                  (try simp_all [Int.floor_le, Int.lt_floor_add_one])
                exact h₂₂
              exact h₁₄
            exact h₁₂
          have h₂₃ : (⌊((X : ℝ) - v) / r⌋ : ℤ) - (⌊(-(v : ℝ)) / r⌋ : ℤ) ≤ ⌊((X : ℝ) - v) / r - (
              -(v : ℝ)) / r⌋ + 1 := by
            have h₂₅ : (⌊((X : ℝ) - v) / r⌋ : ℤ) - (⌊(-(v : ℝ)) / r⌋ : ℤ) ≤ ⌊((X : ℝ) - v) / r - (
                -(v : ℝ)) / r⌋ + 1 := by
              linarith
            exact h₂₅
          have h₂₆ : ⌊((X : ℝ) - v) / r⌋ - ⌊(-(v : ℝ)) / r⌋ ≤ ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ +
              1 := by
            norm_cast at h₂₃ ⊢
          exact h₂₆
        exact h₅
      have h₅ : ⌊((X : ℝ) - v) / r - (-(v : ℝ)) / r⌋ = ⌊(X : ℝ) / r⌋ := by
        have h₆ : ((X : ℝ) - v) / r - (-(v : ℝ)) / r = (X : ℝ) / r := by
          have h₇ : (r : ℝ) ≠ 0 := by positivity
          field_simp [h₇]; ring_nf
        rw [h₆]
      have h₆ : ⌊((X : ℝ) - v) / r⌋ - ⌊(-(v : ℝ)) / r⌋ ≤ ⌊(X : ℝ) / r⌋ + 1 := by
        linarith
      exact h₆
    exact h₂
  exact h₁

/-- The number of N ∈ (0, X] satisfying N ≡ v (mod r) is at most X / r + 1.

    The exact count is given by `Nat.Ioc_filter_modEq_card`:
    `{x ∈ Finset.Ioc a b | x ≡ v [MOD r]}.card = max(⌊(b - v)/r⌋ - ⌊(a - v)/r⌋, 0)`
    For a = 0, b = X, the count equals max(⌊(X - v)/r⌋ - ⌊-v/r⌋, 0).
    By `floor_diff_bound`, the expression ⌊(X - v)/r⌋ - ⌊-v/r⌋ ≤ ⌊X/r⌋ + 1.
    Since X, r are naturals, ⌊(X : ℝ)/r⌋ = X / r (integer division).
    The max(..., 0) is at most the upper bound, giving count ≤ X / r + 1. -/
lemma floor_diff_bound_rat (X v r : ℕ) (hr : 0 < r) :
    ⌊((X : ℚ) - v) / r⌋ - ⌊(-(v : ℚ)) / r⌋ ≤ ⌊(X : ℚ) / r⌋ + 1 := by
  have floor_sub_floor_le : ∀ (a b : ℚ), ⌊a⌋ - ⌊b⌋ ≤ ⌊a - b⌋ + 1 := by
    intro a b
    have h₂ : (⌊a⌋ : ℚ) ≤ a := by exact_mod_cast Int.floor_le a
    have h₅ : (b : ℚ) < (⌊b⌋ : ℚ) + 1 := by exact_mod_cast Int.lt_floor_add_one b
    have h₆ : (⌊a⌋ : ℚ) - (⌊b⌋ : ℚ) - 1 < a - b := by linarith
    have h₇ : ((⌊a⌋ : ℤ) - ⌊b⌋ - 1 : ℤ) ≤ ⌊(a - b : ℚ)⌋ := by
      apply Int.le_floor.mpr
      push_cast
      linarith [h₆]
    linarith
  have h := floor_sub_floor_le (((X : ℚ) - v) / r) ((-(v : ℚ)) / r)
  have hr' : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hr)
  have heq : ((X : ℚ) - v) / r - (-(v : ℚ)) / r = (X : ℚ) / r := by field_simp; ring
  rw [heq] at h
  exact h

lemma card_modEq_Icc_bound (v r X : ℕ) (hr : 0 < r) :
    ((Finset.Ioc 0 X).filter fun N => N ≡ v [MOD r]).card ≤ X / r + 1 := by
  have h := Nat.Ioc_filter_modEq_card 0 X hr v
  simp only [Nat.cast_zero, zero_sub] at h
  have hbd := floor_diff_bound_rat X v r hr
  have hfloor : ⌊(X : ℚ) / r⌋ = (X / r : ℕ) := Rat.floor_natCast_div_natCast X r
  rw [hfloor] at hbd
  have hmax : max (⌊((X : ℚ) - v) / r⌋ - ⌊(-(v : ℚ)) / r⌋) 0 ≤ (X / r : ℤ) + 1 := by
    apply max_le hbd
    have : (0 : ℤ) ≤ (X / r : ℕ) := Nat.cast_nonneg _
    omega
  have hcard : ((Finset.Ioc 0 X).filter fun N => N ≡ v [MOD r]).card =
      (max (⌊((X : ℚ) - v) / r⌋ - ⌊(-(v : ℚ)) / r⌋) 0).toNat := by
    have := congrArg Int.toNat h
    simp only [Int.toNat_natCast] at this
    exact this
  rw [hcard]
  omega

lemma gcd_psq_b_eq_one (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b) (hbp : b < p) :
    (p ^ 2).gcd b = 1 := by
  have h₁ : b.Coprime (p ^ 2) := b_coprime_p_sq p hp b hb hbp
  have h₂ : (p ^ 2).gcd b = 1 := h₁.symm
  aesop

/-- p² > 0 when p is prime. -/
lemma prime_sq_pos (p : ℕ) (hp : Nat.Prime p) : 0 < p ^ 2 := by
  exact Nat.pow_pos hp.pos

lemma zmod_mul_inv_add_eq_zero (n b d : ℕ) (_hn : 0 < n) (hb : b.Coprime n) :
    (↑b : ZMod n) * ((-↑d : ZMod n) * (↑b : ZMod n)⁻¹) + ↑d = 0 := by
  have h_unit : IsUnit (↑b : ZMod n) := (ZMod.isUnit_iff_coprime b n).mpr hb
  have h_inv : (↑b : ZMod n) * (↑b : ZMod n)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h_unit
  have h_main : (↑b : ZMod n) * ((-↑d : ZMod n) * (↑b : ZMod n)⁻¹) = (-↑d : ZMod n) := by
    rw [mul_left_comm, h_inv, mul_one]
  have h_final : (↑b : ZMod n) * ((-↑d : ZMod n) * (↑b : ZMod n)⁻¹) + ↑d = 0 := by aesop
  exact h_final

/-- Constructs a unique residue v such that b*v ≡ -d (mod p²) for prime p > b ≥ 2.
    In ZMod (p²), since b is a unit (coprime to p²), we can define v = b⁻¹ * (-d).
    The result is a natural number v < p² such that p² | b*v + d. -/
lemma exists_inverse_residue (p : ℕ) (hp : Nat.Prime p) (b : ℕ) (hb : 2 ≤ b) (hbp : b < p) (d : ℕ) :
    ∃ v : ℕ, v < p ^ 2 ∧ (p ^ 2) ∣ (b * v + d) := by
  -- Get that b is coprime to p²
  have hcop : b.Coprime (p ^ 2) := b_coprime_p_sq p hp b hb hbp
  -- p² > 0
  have hp2_pos : 0 < p ^ 2 := prime_sq_pos p hp
  -- NeZero (p ^ 2) instance
  haveI : NeZero (p ^ 2) := ⟨Nat.pos_iff_ne_zero.mp hp2_pos⟩
  -- Define v as the value of (-d) * b⁻¹ in ZMod (p²)
  let v_zmod : ZMod (p ^ 2) := (-↑d : ZMod (p ^ 2)) * (↑b : ZMod (p ^ 2))⁻¹
  use v_zmod.val
  constructor
  · -- v < p²
    exact ZMod.val_lt v_zmod
  · -- p² | b * v + d
    -- It suffices to show (b * v + d : ZMod (p²)) = 0
    rw [← CharP.cast_eq_zero_iff (ZMod (p ^ 2)) (p ^ 2)]
    -- Push the cast through
    simp only [Nat.cast_add, Nat.cast_mul]
    -- v_zmod.val cast back gives v_zmod
    have hval : (v_zmod.val : ZMod (p ^ 2)) = v_zmod := ZMod.natCast_zmod_val v_zmod
    rw [hval]
    -- Now we need: ↑b * ((-↑d) * (↑b)⁻¹) + ↑d = 0
    exact zmod_mul_inv_add_eq_zero (p ^ 2) b d hp2_pos hcop

lemma dvd_iff_modEq_of_coprime (p b v d N : ℕ) (hcop : (p ^ 2).gcd b = 1)
    (hdvd_v : (p ^ 2) ∣ (b * v + d)) :
    (p ^ 2) ∣ (b * N + d) ↔ N ≡ v [MOD (p ^ 2)] := by
  -- Convert hdvd_v to modular form: b*v + d ≡ 0 [MOD p²]
  have h_v_mod : (b * v + d) ≡ 0 [MOD (p ^ 2)] := Nat.modEq_zero_iff_dvd.mpr hdvd_v
  constructor
  · -- Forward direction: p² | b*N + d → N ≡ v [MOD p²]
    intro hdvd_N
    -- b*N + d ≡ 0 [MOD p²]
    have h_N_mod : (b * N + d) ≡ 0 [MOD (p ^ 2)] := Nat.modEq_zero_iff_dvd.mpr hdvd_N
    -- b*N + d ≡ b*v + d [MOD p²] (both ≡ 0)
    have h_eq : (b * N + d) ≡ (b * v + d) [MOD (p ^ 2)] := h_N_mod.trans h_v_mod.symm
    -- Cancel d: b*N ≡ b*v [MOD p²]
    have h_mul : b * N ≡ b * v [MOD (p ^ 2)] := Nat.ModEq.add_right_cancel' d h_eq
    -- Cancel b: N ≡ v [MOD p²]
    exact Nat.ModEq.cancel_left_of_coprime hcop h_mul
  · -- Backward direction: N ≡ v [MOD p²] → p² | b*N + d
    intro h_modEq
    -- b*N ≡ b*v [MOD p²]
    have h_mul : b * N ≡ b * v [MOD (p ^ 2)] := h_modEq.mul_left b
    -- b*N + d ≡ b*v + d [MOD p²]
    have h_add : (b * N + d) ≡ (b * v + d) [MOD (p ^ 2)] := h_mul.add_right d
    -- b*N + d ≡ 0 [MOD p²]
    have h_zero : (b * N + d) ≡ 0 [MOD (p ^ 2)] := h_add.trans h_v_mod
    -- p² | b*N + d
    exact Nat.modEq_zero_iff_dvd.mp h_zero

lemma dvd_shift_iff_modEq_unique (b : ℕ) (hb : 2 ≤ b) (q : Nat.Primes) (hq : (q : ℕ) > b) (d : ℕ) :
    ∃ v : ℕ, ∀ N : ℕ, (q : ℕ) ^ 2 ∣ b * N + d ↔ N ≡ v [MOD (q : ℕ) ^ 2] := by
  let p := (q : ℕ)
  have hp : Nat.Prime p := q.prop
  have hbp : b < p := hq
  have hcop := gcd_psq_b_eq_one p hp b hb hbp
  obtain ⟨v, _, hdvd_v⟩ := exists_inverse_residue p hp b hb hbp d
  exact ⟨v, fun N => dvd_iff_modEq_of_coprime p b v d N hcop hdvd_v⟩

lemma filter_shifted_dvd_eq_filter_modEq (b : ℕ) (hb : 2 ≤ b) (q : Nat.Primes) (hq : (q : ℕ) > b)
    (d : ℕ) (S : Finset ℕ) :
    ∃ v : ℕ, (S.filter fun N => (q : ℕ) ^ 2 ∣ b * N + d) =
             (S.filter fun N => N ≡ v [MOD (q : ℕ) ^ 2]) := by
  obtain ⟨v, hv⟩ := dvd_shift_iff_modEq_unique b hb q hq d
  exact ⟨v, Finset.filter_congr (fun N _ => hv N)⟩

/-- For a fixed d, the count of N in [1,X] with q²|(bN+d) is at most X/q² + 1.
    Since q > b and q is prime, gcd(b,q²) = 1, so the congruence bN ≡ -d (mod q²) has
    a unique solution mod q². The solutions form an arithmetic progression with common
    difference q², so there are at most ⌊X/q²⌋ + 1 solutions in [1,X]. -/
lemma card_shifted_divisible_bound (b : ℕ) (hb : 2 ≤ b) (q : Nat.Primes) (hq : (q : ℕ) > b)
    (d : ℕ) (X : ℕ) :
    ((Finset.Icc 1 X).filter fun N => (q : ℕ) ^ 2 ∣ b * N + d).card ≤ X / (q : ℕ) ^ 2 + 1 := by
  obtain ⟨v, hv⟩ := filter_shifted_dvd_eq_filter_modEq b hb q hq d (Finset.Icc 1 X)
  rw [hv]
  exact card_modEq_Icc_bound v ((q : ℕ) ^ 2) X (Nat.pow_pos q.prop.pos)

/-- The count of N in [1,X] with ∃d∈T, q²|(bN+d) is at most |T|*(X/q² + 1).
    This follows from the union bound over T applied to card_shifted_divisible_bound.
    Uses `Finset.card_biUnion_le_card_mul : ∀ (s : Finset ι) (f : ι → Finset β) (n : ℕ),
    (∀ a ∈ s, (f a).card ≤ n) → (s.biUnion f).card ≤ s.card * n`. -/
lemma card_union_shifted_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (q : Nat.Primes) (hq : (q : ℕ) > b) (X : ℕ) :
    ((Finset.Icc 1 X).filter fun N => ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card ≤
      T.card * (X / (q : ℕ) ^ 2 + 1) := by
  -- The key insight: {N : ∃ d ∈ T, q²|(bN+d)} = ⋃_{d ∈ T} {N : q²|(bN+d)}
  -- We express this as a biUnion, then apply card_biUnion_le_card_mul
  have h_eq : (Finset.Icc 1 X).filter (fun N => ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d) =
      T.biUnion (fun d => (Finset.Icc 1 X).filter (fun N => (q : ℕ) ^ 2 ∣ b * N + d)) := by
    ext N
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hN, d, hd, hdiv⟩
      exact ⟨d, hd, hN, hdiv⟩
    · rintro ⟨d, hd, hN, hdiv⟩
      exact ⟨hN, d, hd, hdiv⟩
  rw [h_eq]
  apply Finset.card_biUnion_le_card_mul
  intro d _
  exact card_shifted_divisible_bound b hb q hq d X

lemma combined_bound_aux (T : Finset ℕ) (X q_sq : ℕ) :
    X / q_sq + T.card * (X / q_sq + 1) ≤ (T.card + 1) * (X / q_sq + 1) := by
  have h_main : X / q_sq + T.card * (X / q_sq + 1) ≤ (T.card + 1) * (X / q_sq + 1) := by
    rw [add_mul, one_mul]; omega
  aesop

lemma single_prime_violation_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (q : Nat.Primes) (hq : (q : ℕ) > b) (X : ℕ) :
    ((Finset.Icc 1 X).filter fun N =>
      (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card ≤ (T.card + 1) * (X / (q : ℕ) ^ 2 +
          1) := by
  -- The filtered set is ⊆ A ∪ B where A = {q²|N}, B = {∃d∈T, q²|(bN+d)}
  -- By union bound: |A ∪ B| ≤ |A| + |B|
  have hA : ((Finset.Icc 1 X).filter fun N => (q : ℕ) ^ 2 ∣ N).card ≤ X / (q : ℕ) ^ 2 :=
    card_multiples_Icc q X
  have hB : ((Finset.Icc 1 X).filter fun N => ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card ≤
      T.card * (X / (q : ℕ) ^ 2 + 1) := card_union_shifted_bound b hb T hT q hq X
  -- Union bound
  calc ((Finset.Icc 1 X).filter fun N => (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card
      ≤ ((Finset.Icc 1 X).filter fun N => (q : ℕ) ^ 2 ∣ N).card +
        ((Finset.Icc 1 X).filter fun N => ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d).card := by
          rw [Finset.filter_or]
          exact Finset.card_union_le _ _
    _ ≤ X / (q : ℕ) ^ 2 + T.card * (X / (q : ℕ) ^ 2 + 1) := Nat.add_le_add hA hB
    _ ≤ (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) := combined_bound_aux T X ((q : ℕ) ^ 2)

/-- Convert ℕ.primesBelow to Finset Nat.Primes. -/
noncomputable def primesBelow' (n : ℕ) : Finset Nat.Primes :=
  (n.primesBelow).subtype Nat.Prime

/-- The set of primes q with q ≤ √(bX+b) that are not in S.
    Any violation by q ∉ S must have q² ≤ bX+b, so q ≤ √(bX+b) < √(bX+b)+1.
    Either q² | N (so q² ≤ X ≤ bX+b) or q² | bN+d with d < b (so q² ≤ bX + b - 1 < bX+b). -/
noncomputable def relevantNotInS (b X : ℕ) (S : Finset Nat.Primes) : Finset Nat.Primes :=
  (primesBelow' (Nat.sqrt (b * X + b) + 1)).filter (· ∉ S)

lemma primesBelow_succ_card_le (k : ℕ) : (k + 1).primesBelow.card ≤ k := by
  have h₁ : (k + 1).primesBelow.card ≤ k := by
    have h₂ : (k + 1).primesBelow ⊆ Finset.Icc 2 k := by
      intro p hp
      simp only [Finset.mem_Icc,
        Finset.mem_Icc] at hp ⊢
      have h₃ : p < k + 1 := by
        simp_all [Nat.primesBelow]
      have h₄ : Nat.Prime p := by
        simp_all [Nat.primesBelow]
      have h₅ : p ≥ 2 := Nat.Prime.two_le h₄
      have h₆ : p ≤ k := by
        omega
      exact ⟨h₅, h₆⟩
    have h₃ : (k + 1).primesBelow.card ≤ (Finset.Icc 2 k).card := Finset.card_le_card h₂
    have h₄ : (Finset.Icc 2 k).card ≤ k := by
      have h₅ : (Finset.Icc 2 k).card = k + 1 - 2 := by
        simp
      have h₆ : k + 1 - 2 ≤ k := by
        cases k with
        | zero => simp_all
        | succ k' =>
          simp_all [Nat.add_assoc]
      omega
    omega
  exact h₁

lemma primesBelow'_card (n : ℕ) : (primesBelow' n).card = n.primesBelow.card := by
  have h1 : (primesBelow' n).card = ((n.primesBelow).subtype Nat.Prime).card := by rfl
  have h2 : ((n.primesBelow).subtype Nat.Prime).card = (n.primesBelow.filter Nat.Prime).card := by
    rw [Finset.card_subtype]
  have h3 : n.primesBelow.filter Nat.Prime = n.primesBelow := by
    apply Finset.filter_true_of_mem
    intro p hp
    have h₄ : p.Prime := by
      have h₅ : p ∈ n.primesBelow := hp
      have h₆ : p.Prime := by
        -- Prove that if p is in n.primesBelow, then p is prime
        have h₇ : p.Prime := by
          simp only [Nat.mem_primesBelow] at h₅
          -- Use the fact that p is in the list of primes below n to deduce that p is prime
          exact h₅.2
        exact h₇
      exact h₆
    exact h₄
  have h4 : (n.primesBelow.filter Nat.Prime).card = n.primesBelow.card := by
    rw [h3]
  have h5 : (primesBelow' n).card = n.primesBelow.card := by
    calc
      (primesBelow' n).card = ((n.primesBelow).subtype Nat.Prime).card := by rw [h1]
      _ = (n.primesBelow.filter Nat.Prime).card := by rw [h2]
      _ = n.primesBelow.card := by rw [h4]
  apply h5

lemma relevantNotInS_card_le (b X : ℕ) (S : Finset Nat.Primes) :
    (relevantNotInS b X S).card ≤ Nat.sqrt (b * X + b) := by
  calc (relevantNotInS b X S).card
      ≤ (primesBelow' (Nat.sqrt (b * X + b) + 1)).card :=
          Finset.card_filter_le _ _
    _ = (Nat.sqrt (b * X + b) + 1).primesBelow.card := primesBelow'_card _
    _ ≤ Nat.sqrt (b * X + b) := primesBelow_succ_card_le _

lemma not_in_S_implies_gt_y (S : Finset Nat.Primes) (y : ℕ)
    (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (q : Nat.Primes) (hq : q ∉ S) :
    (q : ℕ) > y := by
  have h_main : (q : ℕ) > y := not_le.mp (fun h => hq (hy q h))
  aesop

lemma relevantNotInS_gt_y (b X : ℕ) (S : Finset Nat.Primes) (y : ℕ)
    (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (q : Nat.Primes)
    (hq : q ∈ relevantNotInS b X S) :
    (q : ℕ) > y := by
  have h_main : (q : ℕ) > y := by
    by_contra h
    have h₁ : (q : ℕ) ≤ y := by linarith
    have h₂ : q ∈ S := hy q h₁
    have h₃ : q ∉ S := by
      simp only [relevantNotInS, primesBelow', Finset.mem_filter] at hq
      simp_all
    exact h₃ h₂
  exact h_main

lemma relevantNotInS_gt_b (b X : ℕ) (S : Finset Nat.Primes) (y : ℕ)
    (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b) (q : Nat.Primes)
    (hq : q ∈ relevantNotInS b X S) :
    (q : ℕ) > b := by
  have hq_not_in_S : q ∉ S := by
    simp only [relevantNotInS, Finset.mem_filter] at hq
    have h₁ : q ∉ S := by aesop
    exact h₁
  have h_main : (q : ℕ) > b := by
    by_cases hqy : (q : ℕ) ≤ y
    · -- Case: (q : ℕ) ≤ y
      have hq_in_S : q ∈ S := hy q hqy
      exact absurd hq_in_S hq_not_in_S
    · -- Case: (q : ℕ) > y
      have h₂ : (q : ℕ) > b := by omega
      exact h₂
  exact h_main

lemma prime_sq_bound_from_N_dvd (b X N : ℕ) (hb : 2 ≤ b) (q : Nat.Primes)
    (hN : N ∈ Finset.Icc 1 X) (hdvd : (q : ℕ) ^ 2 ∣ N) : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
  have hN' : N ≤ X := (Finset.mem_Icc.mp hN).2
  have hN'' : 1 ≤ N := (Finset.mem_Icc.mp hN).1
  have hq : (q : ℕ) ^ 2 ≤ N := Nat.le_of_dvd (by positivity) hdvd
  have hq'' : (q : ℕ) ^ 2 ≤ b * X + b := by
    have h₂ : X ≤ b * X := by
      nlinarith
    nlinarith
  have hq''' : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
    have h₁ : (q : ℕ) ^ 2 ≤ b * X + b := hq''
    have h₂ : Nat.sqrt (b * X + b) ≥ q := by
      apply Nat.le_sqrt.mpr;
      (try norm_cast at h₁ ⊢);
      nlinarith [Nat.Prime.two_le q.prop]
    have h₃ : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
      omega
    exact h₃
  exact hq'''

theorem prime_sq_bound_from_shifted_dvd (b X N d : ℕ) (hb : 2 ≤ b) (q : Nat.Primes)
    (hN : N ∈ Finset.Icc 1 X) (hd : d ∈ Finset.range b) (hdvd : (q : ℕ) ^ 2 ∣ b * N + d) :
    (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
  have h₁ : (q : ℕ) ^ 2 ∣ b * N + d := hdvd
  have h₂ : 1 ≤ N := by
    simp [Finset.mem_Icc] at hN
    linarith
  have h₃ : N ≤ X := by
    simp [Finset.mem_Icc] at hN
    linarith
  have h₄ : d < b := by
    simp [Finset.mem_range] at hd
    linarith
  have h₅ : b * N + d < b * X + b := by
    have h₅₁ : b * N ≤ b * X := by
      nlinarith
    nlinarith
  have h₆ : (q : ℕ) ^ 2 ≤ b * N + d := Nat.le_of_dvd (by
    have h₆₁ : 0 < b * N + d := by
      nlinarith
    linarith) h₁
  have h₉ : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
    have h₉₂ : (q : ℕ) ≤ Nat.sqrt (b * X + b) := by
      apply Nat.le_sqrt.mpr; nlinarith
    have h₉₃ : (q : ℕ) < Nat.sqrt (b * X + b) + 1 := by
      omega
    exact h₉₃
  exact h₉

lemma violation_subset_biUnion (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (Finset.Icc 1 X).filter (fun N => ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (
        q : ℕ) ^ 2 ∣ b * N + d))
    ⊆ (relevantNotInS b X S).biUnion
        (fun q => (Finset.Icc 1 X).filter (fun N => (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
            d)) := by
  intro N hN
  simp only [Finset.mem_filter, Finset.mem_biUnion] at hN ⊢
  obtain ⟨hN_Icc, q₀, hq₀_not_S, hq₀_dvd⟩ := hN
  refine ⟨q₀, ?_, hN_Icc, hq₀_dvd⟩
  -- Need to show q₀ ∈ relevantNotInS b X S
  simp only [relevantNotInS, Finset.mem_filter]
  refine ⟨?_, hq₀_not_S⟩
  -- q₀ ∈ primesBelow'(√(bX+b)+1)
  have hq₀_bound : (q₀ : ℕ) < Nat.sqrt (b * X + b) + 1 :=
    hq₀_dvd.elim
      (fun h => prime_sq_bound_from_N_dvd b X N hb q₀ hN_Icc h)
      (fun ⟨d, hd, hdvd⟩ => prime_sq_bound_from_shifted_dvd b X N d hb q₀ hN_Icc (hT hd) hdvd)
  exact Finset.mem_subtype.mpr (Nat.mem_primesBelow.mpr ⟨hq₀_bound, q₀.prop⟩)

/-- Union bound: card(V) ≤ ∑_{q ∈ relevantNotInS} card(V_q).
    Combines violation_subset_biUnion with Finset.card_le_card and Finset.card_biUnion_le.
    Uses `Finset.card_biUnion_le : (s.biUnion t).card ≤ ∑ a ∈ s, (t a).card`. -/
lemma union_card_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (y : ℕ) (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b) (
        X : ℕ) :
    ((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card
    ≤ ∑ q ∈ relevantNotInS b X S, (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) := by
  calc ((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card
      ≤ ((relevantNotInS b X S).biUnion
          (fun q => (Finset.Icc 1 X).filter (fun N => (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b *
              N + d))).card := by
        apply Finset.card_le_card
        exact violation_subset_biUnion b hb T hT S X
    _ ≤ ∑ q ∈ relevantNotInS b X S,
        ((Finset.Icc 1 X).filter (fun N => (q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
            d)).card := by
        apply Finset.card_biUnion_le
    _ ≤ ∑ q ∈ relevantNotInS b X S, (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) := by
        apply Finset.sum_le_sum
        intro q hq
        apply single_prime_violation_bound b hb T hT q
        exact relevantNotInS_gt_b b X S y hy hyb q hq

/-- The finite sum ∑_{q∈Q} 1/q² over primes in Q is ≤ the tsum ∑'_{p>y} 1/p²
    where all primes q in Q satisfy q > y.
    This uses that Q (as a subset of {primes p > y}) contributes to the infinite sum.
    Since 1/q² ≥ 0 for all primes q, and the sum over primes converges,
    the finite partial sum is bounded by the full tail sum.
    Uses `Summable.sum_le_tsum : ∀ {ι : Type*} {f : ι → ℝ} (s : Finset ι),
      (∀ i ∉ s, 0 ≤ f i) → Summable f → ∑ i ∈ s, f i ≤ ∑' i, f i`. -/
lemma finsum_le_tsum_tail (y : ℕ) (Q : Finset Nat.Primes) (hQ : ∀ q ∈ Q, (q : ℕ) > y) :
    (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2))
    ≤ (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2) := by
  -- Define the subtype of primes > y
  let S := {q : Nat.Primes // (q : ℕ) > y}
  -- Define the function on S
  let f : S → ℝ := fun p => 1 / ((((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
  -- Summability: f is summable on S since 1/p² is summable on all primes
  have hf_summable : Summable f := primes_summable_one_div_sq.subtype _
  -- Nonnegativity: f p ≥ 0 for all p
  have hf_nonneg : ∀ p : S, 0 ≤ f p := fun p => by positivity
  -- Map Q into S using the embedding
  let e : Q → S := fun ⟨q, hq⟩ => ⟨q, hQ q hq⟩
  have he_inj : Function.Injective e := fun ⟨q1, hq1⟩ ⟨q2, hq2⟩ h => by
    simp only [e] at h
    exact Subtype.ext (Subtype.mk.injEq _ _ _ _ ▸ h)
  -- Map Q.attach to a Finset in S
  let Q_S : Finset S := Q.attach.map ⟨e, he_inj⟩
  -- The sum over Q equals the sum over Q_S
  have h_sum_eq : ∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2) = ∑ s ∈ Q_S, f s := by
    rw [Finset.sum_map]
    conv_lhs => rw [← Finset.sum_attach]
    rfl
  -- Apply sum_le_tsum
  rw [h_sum_eq]
  exact hf_summable.sum_le_tsum Q_S (fun _ _ => hf_nonneg _)

lemma sum_expand (c : ℝ) (X : ℕ) (Q : Finset Nat.Primes) :
    (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1)))
    = c * X * (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2)) + c * Q.card := by
  have h₁ : (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1))) = (∑ q ∈ Q, (c * ((X : ℝ) / (
      (q : ℕ) : ℝ) ^ 2)) + ∑ _ ∈ Q, c) := by
    calc
      (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1))) = (∑ q ∈ Q, (c * ((X : ℝ) / (
          (q : ℕ) : ℝ) ^ 2) + c)) := by
        -- Distribute c over the sum
        apply Finset.sum_congr rfl
        intro q _
        ring_nf
      _ = (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2)) + ∑ _ ∈ Q, c) := by
        -- Split the sum into two separate sums
        rw [Finset.sum_add_distrib]
  have h₂ : (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2))) = c * X * (∑ q ∈ Q, 1 / (
      ((q : ℕ) : ℝ) ^ 2)) := by
    calc
      (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2))) = c * (∑ q ∈ Q, ((X : ℝ) / (
          (q : ℕ) : ℝ) ^ 2)) := by
        -- Factor out the constant c from the sum
        rw [Finset.mul_sum]
      _ = c * (X * ∑ q ∈ Q, (1 / ((q : ℕ) : ℝ) ^ 2)) := by
        -- Factor out X from the sum
        have h₃ : (∑ q ∈ Q, ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2)) = X * ∑ q ∈ Q, (1 / ((q : ℕ) : ℝ) ^ 2) :=
            by
          calc
            (∑ q ∈ Q, ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2)) = ∑ q ∈ Q, ((X : ℝ) * (1 / (
                (q : ℕ) : ℝ) ^ 2)) := by
              -- Rewrite each term as X * (1 / q ^ 2)
              apply Finset.sum_congr rfl
              intro q _
              field_simp [Nat.cast_ne_zero]
            _ = (X : ℝ) * ∑ q ∈ Q, (1 / ((q : ℕ) : ℝ) ^ 2) := by
              -- Factor out X from the sum
              rw [Finset.mul_sum]
        rw [h₃]
      _ = c * X * (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2)) := by
        -- Rearrange the multiplication for clarity
        ring_nf
  have h₃ : (∑ _ ∈ Q, c : ℝ) = c * Q.card := by
    calc
      (∑ _ ∈ Q, c : ℝ) = (Q.card : ℝ) * c := by
        simp [Finset.sum_const]
      _ = c * Q.card := by ring
  have h₄ : (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1))) = c * X * (∑ q ∈ Q, 1 / (
      ((q : ℕ) : ℝ) ^ 2)) + c * Q.card := by
    calc
      (∑ q ∈ Q, (c * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1))) = (∑ q ∈ Q, (c * ((X : ℝ) / (
          (q : ℕ) : ℝ) ^ 2)) + ∑ _ ∈ Q, c) := by rw [h₁]
      _ = (c * X * (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2)) + ∑ _ ∈ Q, c) := by
        rw [h₂]
      _ = (c * X * (∑ q ∈ Q, 1 / (((q : ℕ) : ℝ) ^ 2)) + c * Q.card) := by
        rw [h₃]
  rw [h₄]

lemma sum_bound_real (T : Finset ℕ) (y : ℕ) (X : ℕ)
    (Q : Finset Nat.Primes) (hQ : ∀ q ∈ Q, (q : ℕ) > y) :
    (∑ q ∈ Q, ((T.card + 1 : ℝ) * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1)))
    ≤ (T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
      + (T.card + 1 : ℝ) * Q.card := by
  rw [sum_expand]
  have h := finsum_le_tsum_tail y Q hQ
  have hc : (0 : ℝ) ≤ (T.card + 1 : ℝ) * X := by positivity
  gcongr

lemma nat_div_floor_le_real_div (X : ℕ) (q : Nat.Primes) :
    ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((q : ℕ) ^ 2 : ℝ) := by
  have h₁ : ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) * ((q : ℕ) ^ 2 : ℝ) ≤ (X : ℝ) := by
    -- Cast the natural number inequality to real numbers
    have h₂ : (X / (q : ℕ) ^ 2 : ℕ) * (q : ℕ) ^ 2 ≤ X := by
      -- Use the property of natural number division: (X / Y) * Y ≤ X
      have h₃ : (X / (q : ℕ) ^ 2 : ℕ) * (q : ℕ) ^ 2 ≤ X := Nat.div_mul_le_self X ((q : ℕ) ^ 2)
      exact h₃
    -- Cast the inequality to real numbers
    norm_cast at h₂ ⊢
  have h₂ : 0 < ((q : ℕ) : ℝ) := by
    -- Prove that q as a real number is positive
    norm_cast
    exact Nat.Prime.pos q.property
  have h₄ : ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / ((q : ℕ) ^ 2 : ℝ) := by
    -- Divide both sides of h₁ by ((q : ℕ) ^ 2 : ℝ)
    have h₆ : 0 < ((q : ℕ) ^ 2 : ℝ) := by positivity
    -- Use the division inequality to get the final result
    calc
      ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) = (((X / (q : ℕ) ^ 2 : ℕ) : ℝ) * ((q : ℕ) ^ 2 : ℝ)) / (
          (q : ℕ) ^ 2 : ℝ) := by
        field_simp [h₆.ne']
      _ ≤ (X : ℝ) / ((q : ℕ) ^ 2 : ℝ) := by
        -- Use the fact that ((X / (q : ℕ) ^ 2 : ℕ) : ℝ) * ((q : ℕ) ^ 2 : ℝ) ≤ (X : ℝ)
        gcongr
  exact h₄

lemma nat_sum_le_real_sum (T : Finset ℕ) (X : ℕ) (Q : Finset Nat.Primes) :
    ((∑ q ∈ Q, (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) : ℕ) : ℝ)
    ≤ ∑ q ∈ Q, ((T.card + 1 : ℝ) * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1)) := by
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro q _
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  apply mul_le_mul_of_nonneg_left
  · have h := nat_div_floor_le_real_div X q
    linarith
  · linarith [T.card.cast_nonneg (α := ℝ)]

/-- Main bound: violation count is at most the tail sum term plus the count term.

    Proof chain:
    1. violation_count ≤ ∑_{q∈Q} (T+1)*(X/q²+1) [union_card_bound, in ℕ]
    2. ↑(ℕ sum) ≤ ∑_{q∈Q} (T+1)*(X/q²+1) [nat_sum_le_real_sum, cast to ℝ]
    3. real sum ≤ (T+1)*X*∑_{q>y} 1/q² + (T+1)*|Q| [sum_bound_real]
    4. |Q| ≤ √(bX+b) [relevantNotInS_card_le]
    The key fix is step 2→3: we bound the REAL-division sum directly,
    not the nat-division sum. This avoids the inequality direction mismatch. -/
lemma violation_count_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (y : ℕ) (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b) (
        X : ℕ) :
    (((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card : ℝ)
    ≤ (T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
      + (T.card + 1 : ℝ) * Nat.sqrt (b * X + b) := by
  have hU := union_card_bound b hb T hT S y hy hyb X
  have hNR := nat_sum_le_real_sum T X (relevantNotInS b X S)
  have hS := sum_bound_real T y X (relevantNotInS b X S)
              (fun q hq => relevantNotInS_gt_y b X S y hy q hq)
  have hC := relevantNotInS_card_le b X S
  calc (((Finset.Icc 1 X).filter fun N =>
        ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card : ℝ)
      ≤ (∑ q ∈ relevantNotInS b X S, (T.card + 1) * (X / (q : ℕ) ^ 2 + 1) : ℕ) := Nat.cast_le.mpr hU
    _ ≤ ∑ q ∈ relevantNotInS b X S, ((T.card + 1 : ℝ) * ((X : ℝ) / ((q : ℕ) : ℝ) ^ 2 + 1)) := hNR
    _ ≤ (T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
        + (T.card + 1 : ℝ) * (relevantNotInS b X S).card := hS
    _ ≤ (T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
        + (T.card + 1 : ℝ) * Nat.sqrt (b * X + b) := by
        have hpos : (0 : ℝ) ≤ (T.card : ℝ) + 1 := by positivity
        have hle : ((relevantNotInS b X S).card : ℝ) ≤ (Nat.sqrt (b * X + b) : ℝ) :=
            Nat.cast_le.mpr hC
        linarith [mul_le_mul_of_nonneg_left hle hpos]

lemma sqrt_bXb_div_X_small (b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (Nat.sqrt (b * X + b) : ℝ) / X < ε := by
  have h₃ : ∃ (X₀ : ℕ), (X₀ : ℝ) > 2 * (b : ℝ) / ε ^ 2 := by
    -- Use the Archimedean property to find X₀ such that X₀ > 2 * b / ε²
    have h₄ : ∃ (n : ℕ), (2 * (b : ℝ) / ε ^ 2 : ℝ) < n := by
      -- Apply the Archimedean property
      obtain ⟨n, hn⟩ := exists_nat_gt (2 * (b : ℝ) / ε ^ 2)
      exact ⟨n, by linarith⟩
    -- Obtain X₀ from the Archimedean property
    obtain ⟨X₀, hX₀⟩ := h₄
    refine ⟨X₀, ?_⟩
    -- Cast X₀ to ℝ and verify the inequality
    norm_cast at hX₀ ⊢
  -- Step 2: Obtain X₀ from the Archimedean property
  obtain ⟨X₀, hX₀⟩ := h₃
  use max 1 X₀
  intro X hX
  have h₄ : X ≥ 1 := by
    -- Prove that X ≥ 1
    have h₅ : max 1 X₀ ≥ 1 := by simp
    linarith
  have h₅ : (X : ℝ) ≥ 1 := by exact_mod_cast h₄
  have h₆ : (X : ℝ) ≥ (X₀ : ℝ) := by
    -- Prove that X ≥ X₀
    have h₇ : (max 1 X₀ : ℕ) ≥ X₀ := by simp
    have h₉ : (X : ℕ) ≥ X₀ := by linarith
    exact_mod_cast h₉
  have h₈ : (ε : ℝ) ^ 2 * (X : ℝ) > 2 * (b : ℝ) := by
    -- Prove that ε² * X > 2 * b
    have h₁₀ : 0 < (ε : ℝ) ^ 2 := by positivity
    have h₁₁ : 0 < (ε : ℝ) ^ 2 := by positivity
    -- Multiply both sides by ε²
    have h₁₂ : (ε : ℝ) ^ 2 * (X : ℝ) > (ε : ℝ) ^ 2 * (2 * (b : ℝ) / ε ^ 2) := by
      nlinarith
    -- Simplify the right side
    have h₁₃ : (ε : ℝ) ^ 2 * (2 * (b : ℝ) / ε ^ 2) = 2 * (b : ℝ) := by
      field_simp [h₁₁.ne']
    -- Combine the inequalities
    linarith
  have h₉ : (b : ℝ) * X + b ≤ 2 * (b : ℝ) * X := by
    -- Prove that b * X + b ≤ 2 * b * X
    have h₁₂ : (b : ℝ) * (X : ℝ) ≥ (b : ℝ) := by
      nlinarith
    have h₁₃ : (b : ℝ) * (X : ℝ) + (b : ℝ) ≤ 2 * (b : ℝ) * (X : ℝ) := by
      nlinarith
    -- Cast back to natural numbers if necessary
    norm_cast at h₁₃ ⊢
  have h₁₀ : (b : ℝ) * X + b < (ε : ℝ) ^ 2 * (X : ℝ) ^ 2 := by
    -- Prove that b * X + b < ε² * X²
    have h₁₆ : (ε : ℝ) ^ 2 * (X : ℝ) ^ 2 > 2 * (b : ℝ) * (X : ℝ) := by
      nlinarith [sq_nonneg ((X : ℝ) - 1)]
    -- Combine the inequalities to get the final result
    nlinarith
  have h₁₁ : (Nat.sqrt (b * X + b) : ℝ) < (ε : ℝ) * X := by
    -- Prove that √(b * X + b) < ε * X
    have h₁₄ : (Nat.sqrt (b * X + b) : ℕ) * (Nat.sqrt (b * X + b) : ℕ) ≤ (b * X + b) := by
      have h₁₅ : (Nat.sqrt (b * X + b)) * (Nat.sqrt (b * X + b)) ≤ (b * X + b) := by
        nlinarith [Nat.sqrt_le (b * X + b), Nat.lt_succ_sqrt (b * X + b)]
      exact h₁₅
    have h₁₈ : (Nat.sqrt (b * X + b) : ℕ) < (ε : ℝ) * X := by
      by_contra h
      -- If √(b * X + b) ≥ ε * X, then (√(b * X + b))² ≥ (ε * X)²
      have h₁₉ : (ε : ℝ) * X ≤ (Nat.sqrt (b * X + b) : ℕ) := by
        norm_num at h ⊢;
        (try linarith)
      have h₂₀ : ((ε : ℝ) * X) ^ 2 ≤ ((Nat.sqrt (b * X + b) : ℕ) : ℝ) ^ 2 := by
        have h₂₂ : ((ε : ℝ) * X) ^ 2 ≤ ((Nat.sqrt (b * X + b) : ℕ) : ℝ) ^ 2 := by
          gcongr
        exact h₂₂
      have h₂₂ : ((Nat.sqrt (b * X + b) : ℕ) : ℝ) * ((Nat.sqrt (b * X + b) : ℕ) : ℝ) ≤ (b * X +
          b : ℝ) := by
        have h₂₃ : (Nat.sqrt (b * X + b) : ℕ) * (Nat.sqrt (b * X + b) : ℕ) ≤ (b * X + b) := h₁₄
        norm_cast at h₂₃ ⊢
      linarith
    -- Cast the result back to ℝ
    have h₁₉ : (Nat.sqrt (b * X + b) : ℝ) < (ε : ℝ) * X := by
      norm_cast at h₁₈ ⊢
    exact h₁₉
  have h₁₂ : (Nat.sqrt (b * X + b) : ℝ) / X < ε := by
    -- Prove that √(b * X + b) / X < ε
    have h₁₃ : 0 < (X : ℝ) := by
      linarith
    have h₁₅ : (Nat.sqrt (b * X + b) : ℝ) / X < ε := by
      calc
        (Nat.sqrt (b * X + b) : ℝ) / X < ((ε : ℝ) * X) / X := by gcongr
        _ = (ε : ℝ) := by
          field_simp [h₁₃.ne']
    exact h₁₅
  exact h₁₂

lemma combine_violation_bounds (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (y : ℕ) (hy : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) (hyb : y ≥ b)
    (X : ℕ) (hX : 0 < X)
    (ε : ℝ) (_hε : 0 < ε)
    (htail : (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) < ε / 2)
    (hsqrt : (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) < ε / 2) :
    (((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
          d)).card : ℝ) / X < ε := by
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  -- Get the bound from violation_count_bound
  have hbound := violation_count_bound b hb T hT S y hy hyb X
  -- We need: V/X < ε where V ≤ (|T|+1)*X*tail + (|T|+1)*sqrt(bX+b)
  -- Dividing by X: V/X ≤ (|T|+1)*tail + (|T|+1)*sqrt(bX+b)/X
  -- Using htail and hsqrt: V/X < ε/2 + ε/2 = ε
  calc (((Finset.Icc 1 X).filter fun N =>
      ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N + d)).card : ℝ) / X
      ≤ ((T.card + 1 : ℝ) * X * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) +
         (T.card + 1 : ℝ) * (Nat.sqrt (b * X + b) : ℝ)) / X := by
        apply div_le_div_of_nonneg_right hbound (le_of_lt hX_pos)
    _ = (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
        ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) +
        (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) := by
        have hXne : (X : ℝ) ≠ 0 := ne_of_gt hX_pos
        field_simp [hXne]
    _ < ε / 2 + ε / 2 := add_lt_add htail hsqrt
    _ = ε := add_halves ε

lemma tail_sum_antitone (y y' : ℕ) (h : y ≤ y') :
    ∑' (p : {q : Nat.Primes // (q : ℕ) > y'}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 ≤
    ∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (((p : Nat.Primes) : ℕ) : ℝ) ^ 2 := by
  -- Define the injection from {p : p > y'} to {p : p > y}
  let e : {q : Nat.Primes // (q : ℕ) > y'} → {q : Nat.Primes // (q : ℕ) > y} :=
    fun ⟨q, hq⟩ => ⟨q, lt_of_le_of_lt h hq⟩
  apply Summable.tsum_le_tsum_of_inj e
  · -- he: e is injective
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have : a = b := by
      have := congrArg Subtype.val hab
      simp only at this
      exact this
    exact Subtype.ext this
  · -- hs: values outside range are non-negative
    intro c _
    positivity
  · -- h: f i ≤ g (e i) (they're equal)
    intro i
    rfl
  · -- hf: Summable f
    exact primes_summable_one_div_sq.subtype _
  · -- hg: Summable g
    exact primes_summable_one_div_sq.subtype _

/-- Choose y large enough that the tail sum is small enough, and y ≥ b.
    Uses prime_tail_sum_small with ε/(2*(|T|+1)). -/
lemma choose_y_for_tail (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, y ≥ b ∧
      (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) < ε / 2 := by
  -- Get small ε' = ε/(2*(T.card+1))
  have hK : (0 : ℝ) < T.card + 1 := by positivity
  have hε' : 0 < ε / (2 * (T.card + 1)) := by positivity
  -- Use prime_tail_sum_small to get y₁ with tail sum < ε'
  obtain ⟨y₁, hy₁⟩ := prime_tail_sum_small (ε / (2 * (T.card + 1))) hε'
  -- Take y = max b y₁
  use max b y₁
  constructor
  · exact le_max_left b y₁
  · calc (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > max b y₁}), 1 / (
      ((p : Nat.Primes) : ℕ) : ℝ) ^ 2)
      ≤ (T.card + 1 : ℝ) * (∑' (p : {q : Nat.Primes // (q : ℕ) > y₁}), 1 / (
          ((p : Nat.Primes) : ℕ) : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left
          · exact tail_sum_antitone y₁ (max b y₁) (le_max_right b y₁)
          · linarith
    _ < (T.card + 1 : ℝ) * (ε / (2 * (T.card + 1))) := by
          apply mul_lt_mul_of_pos_left hy₁ hK
    _ = ε / 2 := by field_simp

/-- Choose X₀ large enough that the √(bX+b)/X term is small and X₀ > 0. -/
lemma choose_X_for_sqrt (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 0 < X₀ ∧ ∀ X ≥ X₀,
      (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X) < ε / 2 := by
  -- Choose ε' = ε / (2 * (T.card + 1))
  have hc : (0 : ℝ) < T.card + 1 := by positivity
  set ε' := ε / (2 * (T.card + 1)) with hε'_def
  have hε' : 0 < ε' := by positivity
  -- Use sqrt_bXb_div_X_small to get X₀' such that for X ≥ X₀', √(bX+b)/X < ε'
  obtain ⟨X₀', hX₀'⟩ := sqrt_bXb_div_X_small b hb ε' hε'
  -- Take X₀ = max X₀' 1 to ensure X₀ > 0
  use max X₀' 1
  constructor
  · omega
  · intro X hX
    have hXge : X ≥ X₀' := le_trans (le_max_left _ _) hX
    have hbound := hX₀' X hXge
    -- We have √(bX+b)/X < ε' = ε / (2 * (T.card + 1))
    -- So (T.card + 1) * √(bX+b)/X < (T.card + 1) * ε / (2 * (T.card + 1)) = ε / 2
    calc (T.card + 1 : ℝ) * ((Nat.sqrt (b * X + b) : ℝ) / X)
        < (T.card + 1) * ε' := by nlinarith [hbound]
      _ = (T.card + 1) * (ε / (2 * (T.card + 1))) := by rfl
      _ = ε / 2 := by field_simp

/-- The "violation count" (N failing for primes outside S) divided by X vanishes
    as S grows and X gets large. -/
lemma error_term_vanishes (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ y : ℕ, ∃ X₁ : ℕ, ∀ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) →
      ∀ X ≥ X₁,
        (((Finset.Icc 1 X).filter fun N =>
          ∃ q : Nat.Primes, q ∉ S ∧ ((q : ℕ) ^ 2 ∣ N ∨ ∃ d ∈ T, (q : ℕ) ^ 2 ∣ b * N +
              d)).card : ℝ) / X < ε := by
  -- Get y with y ≥ b and small tail sum
  obtain ⟨y, hyb, htail⟩ := choose_y_for_tail b hb T ε hε
  -- Get X₀ with 0 < X₀ and small sqrt term
  obtain ⟨X₀, hX₀_pos, hsqrt⟩ := choose_X_for_sqrt b hb T ε hε
  use y, X₀
  intro S hS X hX
  have hX_pos : 0 < X := Nat.lt_of_lt_of_le hX₀_pos hX
  exact combine_violation_bounds b hb T _hT S y hS hyb X hX_pos ε hε htail (hsqrt X hX)


lemma exists_large_for_ratio (M : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (M : ℝ) / X < δ := by
  have h₁ : 0 ≤ (M : ℝ) / δ := by
    positivity
  have h₂ : ∃ X₀ : ℕ, ∀ X ≥ X₀, (M : ℝ) / X < δ := by
    obtain ⟨X₀, hX₀⟩ := exists_nat_gt ((M : ℝ) / δ)
    use X₀
    intro X hX
    have h₃ : (X : ℝ) ≥ (X₀ : ℝ) := by
      exact_mod_cast hX
    have h₅ : 0 < (X : ℝ) := by
      have h₅₅ : (X : ℝ) > 0 := by linarith
      exact h₅₅
    have h₆ : (M : ℝ) / X < δ := by
      have h₆₁ : (M : ℝ) < (X : ℝ) * δ := by
        calc
          (M : ℝ) = ((M : ℝ) / δ) * δ := by
            field_simp [hδ.ne']
          _ < (X : ℝ) * δ := by
            nlinarith
      have h₆₂ : 0 < (X : ℝ) := h₅
      have h₆₃ : (M : ℝ) / X < δ := by
        calc
          (M : ℝ) / X < ((X : ℝ) * δ) / X := by
            gcongr
          _ = δ := by
            field_simp [h₆₂.ne']
      exact h₆₃
    exact h₆
  exact h₂

/-- Lower bound: for large X, C(X)/X ≥ D(b,T) - ε.
    The count equals the count for all primes up to some bound, which is close to X·D(b,T).
    Uses sum of X/p² for primes p > y, which is O(X/y). -/
lemma count_lower_bound_estimate (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (countJointSquarefree b T X : ℝ) / X ≥ jointSquarefreeDensity b T - ε := by
  have hε2 : 0 < ε / 2 := by linarith
  -- Step 1: Choose y and X₁ for error term to be < ε/2
  obtain ⟨y, X₁, hy⟩ := error_term_vanishes b hb T hT (ε / 2) hε2
  -- Step 2: Define S as primes up to y
  let S := primesUpTo y
  -- Step 3: Choose X₂ so that M/X < ε/2 for X ≥ X₂
  obtain ⟨X₂, hX₂⟩ := exists_large_for_ratio (primeSquareProduct S) (ε / 2) hε2
  -- Step 4: Let X₀ = max(X₁, X₂, 1) to ensure X > 0
  use max X₁ (max X₂ 1)
  intro X hX
  have hX1 : X ≥ X₁ := le_trans (le_max_left _ _) hX
  have hX2 : X ≥ X₂ := le_trans (le_trans (le_max_left _ _) (le_max_right X₁ _)) hX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
    (le_trans (le_trans (le_max_right _ _) (le_max_right X₁ _)) hX)
  -- Step 5: Apply combine_bounds_lower
  have hS : ∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S := mem_primesUpTo y
  have hviol := hy S hS X hX1
  have hM := hX₂ X hX2
  have hcomb := combine_bounds_lower b hb T hT S X hXpos (ε / 2) (ε / 2) hviol hM
  linarith

theorem finite_count_upper_bound (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) :
    (countJointSquarefree b T X : ℝ) ≤
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + ∏ p ∈ S, (p : ℕ) ^ 2 := by
  have h1 := count_upper_bound_via_finite b hb T hT S X
  have h2 := count_finite_prime_approx b hb T hT S X
  set count := ((Finset.Icc 1 X).filter fun N =>
        ∀ p ∈ S, ¬((p : ℕ) ^ 2 ∣ N) ∧ ∀ d ∈ T, ¬((p : ℕ) ^ 2 ∣ b * N + d)).card with hcount
  set prodMu := ∏ p ∈ S, localDensityFactor (p : ℕ) b T with hprodMu
  set prodPsq : ℝ := ∏ p ∈ S, (p : ℕ) ^ 2 with hprodPsq
  have h3 : (count : ℝ) ≤ (X : ℝ) * prodMu + prodPsq := by
    have := abs_sub_le_iff.mp h2
    linarith [this.1, this.2]
  have h4 : ((∏ p ∈ S, (p : ℕ) ^ 2 : ℕ) : ℝ) = prodPsq := by
    rw [hprodPsq, Nat.cast_prod]
    congr 1
    ext p
    push_cast
    ring
  calc (countJointSquarefree b T X : ℝ) ≤ (count : ℝ) := h1
    _ ≤ (X : ℝ) * prodMu + prodPsq := h3
    _ = (X : ℝ) * prodMu + (∏ p ∈ S, (p : ℕ) ^ 2 : ℕ) := by rw [h4]

lemma finite_prod_lt_density_add (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (ε : ℝ) (_hε : 0 < ε)
    (h : |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε) :
    ∏ p ∈ S, localDensityFactor (p : ℕ) b T < jointSquarefreeDensity b T + ε := by
  have h₁ : ∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T < ε := by
    exact (abs_lt.mp h).2
  linarith

lemma combine_upper_bounds (b : ℕ) (_hb : 2 ≤ b) (T : Finset ℕ) (_hT : T ⊆ Finset.range b)
    (S : Finset Nat.Primes) (X : ℕ) (ε : ℝ) (_hε : 0 < ε) (hX : 0 < X)
    (M : ℕ) (_hM : M = ∏ p ∈ S, (p : ℕ) ^ 2)
    (hcount : (countJointSquarefree b T X : ℝ) ≤
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M)
    (hprod : ∏ p ∈ S, localDensityFactor (p : ℕ) b T < jointSquarefreeDensity b T + ε / 2)
    (hratio : (M : ℝ) / X < ε / 2) :
    (countJointSquarefree b T X : ℝ) / X ≤ jointSquarefreeDensity b T + ε := by
  have h_div : (countJointSquarefree b T X : ℝ) / X ≤ (∏ p ∈ S, localDensityFactor (p : ℕ) b T) + (
      M : ℝ) / X := by
    have h₁ : 0 < (X : ℝ) := by exact_mod_cast hX
    have h₂ : (countJointSquarefree b T X : ℝ) / X ≤ ((X : ℝ) * ∏ p ∈ S, localDensityFactor (
        p : ℕ) b T + M) / X := by
      have h₄ : (countJointSquarefree b T X : ℝ) / X ≤ ((X : ℝ) * ∏ p ∈ S, localDensityFactor (
          p : ℕ) b T + M) / X := by
        calc
          (countJointSquarefree b T X : ℝ) / X ≤ ((X : ℝ) * ∏ p ∈ S, localDensityFactor (
              p : ℕ) b T + M) / X := by
            gcongr
          _ = ((X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M) / X := by rfl
      exact h₄
    have h₃ : ((X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M) / X = (∏ p ∈ S,
        localDensityFactor (p : ℕ) b T) + (M : ℝ) / X := by
      field_simp [h₁.ne']
    rw [h₃] at h₂
    exact h₂
  have h_final : (countJointSquarefree b T X : ℝ) / X ≤ jointSquarefreeDensity b T + ε := by
    linarith
  exact h_final

lemma exists_finite_prime_set (y : ℕ) :
    ∃ S : Finset Nat.Primes, (∀ p : Nat.Primes, (p : ℕ) ≤ y → p ∈ S) := by
  have hfin : {p : Nat.Primes | (p : ℕ) ≤ y}.Finite := by
    have heq : {p : Nat.Primes | (p : ℕ) ≤ y} = Subtype.val ⁻¹' (Set.Iic y) := rfl
    rw [heq]
    apply Set.Finite.preimage _ (Set.finite_Iic y)
    exact Set.injOn_of_injective Subtype.val_injective
  use hfin.toFinset
  intro p hp
  rw [Set.Finite.mem_toFinset]
  exact hp

/-- Upper bound: for large X, C(X)/X ≤ D(b,T) + ε. -/
lemma count_upper_bound_direct (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀,
      (countJointSquarefree b T X : ℝ) / X ≤ jointSquarefreeDensity b T + ε := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨y, hy⟩ := finite_product_converges_to_density b hb T hT (ε / 2) hε2
  obtain ⟨S, hS⟩ := exists_finite_prime_set y
  have hprod : |∏ p ∈ S, localDensityFactor (p : ℕ) b T - jointSquarefreeDensity b T| < ε / 2 :=
    hy S hS
  let M : ℕ := ∏ p ∈ S, (p : ℕ) ^ 2
  obtain ⟨X₀, hX₀⟩ := exists_large_for_ratio M (ε / 2) hε2
  use max X₀ 1
  intro X hX
  have hX₀' : X ≥ X₀ := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℕ) < X := Nat.one_pos.trans_le hX1
  have hcount : (countJointSquarefree b T X : ℝ) ≤
      (X : ℝ) * ∏ p ∈ S, localDensityFactor (p : ℕ) b T + M :=
    finite_count_upper_bound b hb T hT S X
  have hratio : (M : ℝ) / X < ε / 2 := hX₀ X hX₀'
  have hprod' : ∏ p ∈ S, localDensityFactor (p : ℕ) b T < jointSquarefreeDensity b T + ε / 2 :=
    finite_prod_lt_density_add b hb T hT S (ε / 2) hε2 hprod
  exact combine_upper_bounds b hb T hT S X ε hε hXpos M rfl hcount hprod' hratio

/-- The joint square-free density for subset T equals jointSquarefreeDensity b T.
    Uses Metric.tendsto_atTop: convergence iff for all ε > 0, eventually |f(n) - L| < ε.
    Lower bound: count_lower_bound_estimate.
    Upper bound: count_upper_bound_direct. -/
lemma joint_density_eq_euler_product (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ) (hT : T ⊆ Finset.range b) :
    Filter.Tendsto
      (fun X : ℕ => (countJointSquarefree b T X : ℝ) / (X : ℝ))
      Filter.atTop (nhds (jointSquarefreeDensity b T)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get X₀ for lower bound with ε/2
  obtain ⟨X₁, hX₁⟩ := count_lower_bound_estimate b hb T hT (ε/2) (by linarith)
  -- Get X₀ for upper bound with ε/2
  obtain ⟨X₂, hX₂⟩ := count_upper_bound_direct b hb T hT (ε/2) (by linarith)
  -- Take max
  use max X₁ X₂
  intro X hX
  rw [Real.dist_eq]
  have hX₁' : X ≥ X₁ := le_of_max_le_left hX
  have hX₂' : X ≥ X₂ := le_of_max_le_right hX
  have lower := hX₁ X hX₁'
  have upper := hX₂ X hX₂'
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-! ## Helper lemmas for inclusion-exclusion -/

/-- Indicator function for squarefree: returns 1 if squarefree, 0 otherwise -/
noncomputable def sqfreeIndicator (n : ℕ) : ℝ := if Squarefree n then 1 else 0

/-- Indicator function for "bN+d is squarefree" -/
noncomputable def shiftSqfreeIndicator (b N d : ℕ) : ℝ := if Squarefree (b * N + d) then 1 else 0

lemma sum_over_subsets_containing_x (s : Finset ℕ) (x : ℕ) (hx : x ∉ s) (a : ℕ → ℝ) :
    ∑ T ∈ s.powerset, ((-1 : ℝ) ^ (insert x T).card * ∏ d ∈ (insert x T), a d) =
    - a x * ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card * ∏ d ∈ T, a d := by
  have h₁ : ∀ T : Finset ℕ, T ∈ s.powerset → ((-1 : ℝ) ^ (insert x T).card * ∏ d ∈ (insert x T),
      a d) = (-1 : ℝ) ^ (T.card + 1) * (a x * ∏ d ∈ T, a d) := by
    intro T hT
    have h₂ : x ∉ T := by
      have h₃ : T ⊆ s := Finset.mem_powerset.mp hT
      intro h₄
      have h₅ : x ∈ s := h₃ h₄
      exact hx h₅
    have h₃ : (insert x T).card = T.card + 1 := by
      rw [Finset.card_insert_of_notMem h₂]
    have h₄ : ∏ d ∈ (insert x T), a d = a x * ∏ d ∈ T, a d := by
      rw [Finset.prod_insert h₂]
    calc
      (-1 : ℝ) ^ (insert x T).card * ∏ d ∈ (insert x T), a d
        = (-1 : ℝ) ^ (T.card + 1) * ∏ d ∈ (insert x T), a d := by
          rw [h₃]
        _ = (-1 : ℝ) ^ (T.card + 1) * (a x * ∏ d ∈ T, a d) := by
          rw [h₄]
        _ = (-1 : ℝ) ^ (T.card + 1) * (a x * ∏ d ∈ T, a d) := by rfl
  calc
    ∑ T ∈ s.powerset, ((-1 : ℝ) ^ (insert x T).card * ∏ d ∈ (insert x T), a d)
      = ∑ T ∈ s.powerset, ((-1 : ℝ) ^ (T.card + 1) * (a x * ∏ d ∈ T, a d)) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [h₁ T hT]
      _ = ∑ T ∈ s.powerset, ((-1 : ℝ) * (-1 : ℝ) ^ T.card * (a x * ∏ d ∈ T, a d)) := by
        apply Finset.sum_congr rfl
        intro T _
        have h₂ : (-1 : ℝ) ^ (T.card + 1) = (-1 : ℝ) * (-1 : ℝ) ^ T.card := by
          simp [pow_succ, mul_comm]
        rw [h₂]
      _ = (-1 : ℝ) * a x * ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card * ∏ d ∈ T, a d := by
        calc
          ∑ T ∈ s.powerset, ((-1 : ℝ) * (-1 : ℝ) ^ T.card * (a x * ∏ d ∈ T, a d))
            = ∑ T ∈ s.powerset, (-1 : ℝ) * a x * ((-1 : ℝ) ^ T.card * ∏ d ∈ T, a d) := by
              apply Finset.sum_congr rfl
              intro T _
              ring
            _ = (-1 : ℝ) * a x * ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card * ∏ d ∈ T, a d := by
              calc
                ∑ T ∈ s.powerset, (-1 : ℝ) * a x * ((-1 : ℝ) ^ T.card * ∏ d ∈ T, a d)
                  = (-1 : ℝ) * a x * ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card * ∏ d ∈ T, a d := by
                    simp [Finset.mul_sum]
                  _ = (-1 : ℝ) * a x * ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card * ∏ d ∈ T, a d := by rfl
            _ = (-1 : ℝ) * a x * ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card * ∏ d ∈ T, a d := by rfl
      _ = -a x * ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card * ∏ d ∈ T, a d := by
        ring

lemma prod_one_sub_eq_sum_powerset (U : Finset ℕ) (a : ℕ → ℝ) :
    ∏ d ∈ U, (1 - a d) = ∑ T ∈ U.powerset, (-1 : ℝ) ^ T.card * ∏ d ∈ T, a d := by
  induction U using Finset.induction_on with
  | empty =>
    simp [Finset.powerset_empty]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    rw [ih]
    rw [Finset.sum_powerset_insert hx]
    rw [sum_over_subsets_containing_x s x hx a]
    ring

lemma deadEnd_indicator_eq (b N : ℕ) (hN : 1 ≤ N) :
    (if IsBaseBDeadEnd b N then (1 : ℝ) else 0) =
    sqfreeIndicator N * ∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) := by
  have h₁ : (if IsBaseBDeadEnd b N then (1 : ℝ) else 0) =
    sqfreeIndicator N * ∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) := by
    split_ifs with h
    · have h₃ : Squarefree N := h.2.1
      have h₄ : ∀ d ∈ Finset.range b, ¬Squarefree (b * N + d) := h.2.2
      have h₅ : sqfreeIndicator N = (1 : ℝ) := by
        simp [sqfreeIndicator, h₃]
      have h₆ : (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = 1 := by
        have h₇ : ∀ (d : ℕ), d ∈ Finset.range b → (1 - shiftSqfreeIndicator b N d : ℝ) = 1 := by
          intro d hd
          have h₈ : ¬Squarefree (b * N + d) := h₄ d hd
          have h₉ : shiftSqfreeIndicator b N d = (0 : ℝ) := by
            simp [shiftSqfreeIndicator, h₈]
          rw [h₉]; norm_num
        calc
          (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = ∏ _ ∈ Finset.range b, (
              1 : ℝ) := by
            apply Finset.prod_congr rfl
            intro d hd
            rw [h₇ d hd]
          _ = 1 := by simp
      calc
        (1 : ℝ) = (1 : ℝ) * 1 := by ring
        _ = sqfreeIndicator N * ∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) := by
          rw [h₅, h₆]
    · by_cases h₃ : 0 < N
      · by_cases h₄ : Squarefree N
        · have h₅ : ∃ d ∈ Finset.range b, Squarefree (b * N + d) := by
            by_contra h₅
            have h₆ : ∀ d ∈ Finset.range b, ¬Squarefree (b * N + d) := by
              intro d hd
              by_contra h₆
              have h₇ : Squarefree (b * N + d) := by tauto
              have h₈ : ∃ d ∈ Finset.range b, Squarefree (b * N + d) := ⟨d, hd, h₇⟩
              tauto
            have h₇ : 0 < N ∧ Squarefree N ∧ ∀ d ∈ Finset.range b, ¬Squarefree (b * N + d) := ⟨h₃,
                h₄, h₆⟩
            contradiction
          obtain ⟨d, hd, h₅⟩ := h₅
          have h₆ : (1 - shiftSqfreeIndicator b N d : ℝ) = 0 := by
            have h₇ : shiftSqfreeIndicator b N d = (1 : ℝ) := by
              simp [shiftSqfreeIndicator, h₅]
            rw [h₇]; norm_num
          have h₇ : (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = 0 := by
            have h₈ : d ∈ Finset.range b := hd
            have h₉ : (1 - shiftSqfreeIndicator b N d : ℝ) = 0 := h₆
            have h₁₀ : (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = 0 := by
              calc
                (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = ∏ d ∈ Finset.range b,
                    (1 - shiftSqfreeIndicator b N d : ℝ) := by simp
                _ = 0 := by
                  apply Finset.prod_eq_zero h₈
                  rw [h₉]
            exact h₁₀
          have h₈ : sqfreeIndicator N = (1 : ℝ) := by
            simp [sqfreeIndicator, h₄]
          calc
            (0 : ℝ) = (1 : ℝ) * 0 := by ring
            _ = sqfreeIndicator N * ∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) := by
              rw [h₈, h₇]
        · have h₅ : ¬Squarefree N := h₄
          have h₆ : sqfreeIndicator N = (0 : ℝ) := by
            simp [sqfreeIndicator, h₅]
          calc
            (0 : ℝ) = (0 : ℝ) * ∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) := by
              have h₇ : (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = (∏ d ∈
                  Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) := rfl
              simp
            _ = sqfreeIndicator N * ∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) := by
              rw [h₆]
      · have h₃ : N = 0 := by
          by_contra _
          have h₄ : 0 < N := Nat.pos_of_ne_zero (by intro h₄; simp_all)
          contradiction
        have h₄ : sqfreeIndicator N = (0 : ℝ) := by
          simp [sqfreeIndicator, h₃]
        calc
          (0 : ℝ) = (0 : ℝ) * ∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) := by
            have h₅ : (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = (∏ d ∈
                Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) := rfl
            simp
          _ = sqfreeIndicator N * ∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) := by
            rw [h₄]
  exact h₁

lemma countBaseBDeadEnds_as_sum (b X : ℕ) (_hb : 0 < b) :
    (countBaseBDeadEnds b X : ℝ) =
    ∑ N ∈ Finset.Icc 1 X, sqfreeIndicator N * ∏ d ∈ Finset.range b, (1 -
        shiftSqfreeIndicator b N d) := by
  unfold countBaseBDeadEnds
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.mem_Icc] at hN
  exact deadEnd_indicator_eq b N hN.1

lemma indicator_conjunction_eq_prod (b N : ℕ) (T : Finset ℕ) :
    (if Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d) then (1 : ℝ) else 0) =
    sqfreeIndicator N * ∏ d ∈ T, shiftSqfreeIndicator b N d := by
  by_cases h₁ : Squarefree N
  · have h₂ : sqfreeIndicator N = (1 : ℝ) := by
      simp [sqfreeIndicator, h₁]
    have h₃ : (if Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d) then (1 : ℝ) else 0) = (if ∀ d ∈ T,
        Squarefree (b * N + d) then (1 : ℝ) else 0) := by
      split_ifs <;> simp_all
    rw [h₃]
    have h₄ : (∏ d ∈ T, shiftSqfreeIndicator b N d) = (∏ d ∈ T, if Squarefree (b * N + d) then (
        1 : ℝ) else 0) := by
      simp [shiftSqfreeIndicator]
    rw [h₄]
    have h₅ : (if ∀ d ∈ T, Squarefree (b * N + d) then (1 : ℝ) else 0) = (1 : ℝ) * (∏ d ∈ T,
        if Squarefree (b * N + d) then (1 : ℝ) else 0) := by
      by_cases h₆ : ∀ d ∈ T, Squarefree (b * N + d)
      · simp_all
      · have h₇ : ∃ d ∈ T, ¬Squarefree (b * N + d) := by
          by_contra h₈
          push Not at h₈
          have h₉ : ∀ d ∈ T, Squarefree (b * N + d) := by
            intro d hd
            specialize h₈ d hd
            tauto
          contradiction
        obtain ⟨d, hd, h₈⟩ := h₇
        have h₁₀ : ∏ x ∈ T, (if Squarefree (b * N + x) then (1 : ℝ) else 0) = 0 := by
          have h₁₁ : ∏ x ∈ T, (if Squarefree (b * N + x) then (1 : ℝ) else 0) = 0 := by
            apply Finset.prod_eq_zero hd
            split_ifs; simp_all
          exact h₁₁
        simp_all
    calc
      (if ∀ d ∈ T, Squarefree (b * N + d) then (1 : ℝ) else 0) = (1 : ℝ) * (∏ d ∈ T, if Squarefree (
          b * N + d) then (1 : ℝ) else 0) := by rw [h₅]
      _ = sqfreeIndicator N * ∏ d ∈ T, (if Squarefree (b * N + d) then (1 : ℝ) else 0) := by
        rw [h₂]
      _ = sqfreeIndicator N * ∏ d ∈ T, shiftSqfreeIndicator b N d := by
        simp [shiftSqfreeIndicator]
  · have h₂ : sqfreeIndicator N = (0 : ℝ) := by
      simp [sqfreeIndicator, h₁]
    have h₃ : (if Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d) then (1 : ℝ) else 0) = (0 : ℝ) :=
        by
      split_ifs <;> simp_all
    calc
      (if Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d) then (1 : ℝ) else 0) = (0 : ℝ) := by
          rw [h₃]
      _ = sqfreeIndicator N * ∏ d ∈ T, shiftSqfreeIndicator b N d := by
        rw [h₂]; simp

lemma countJointSquarefree_as_sum (b X : ℕ) (T : Finset ℕ) :
    (countJointSquarefree b T X : ℝ) =
    ∑ N ∈ Finset.Icc 1 X, sqfreeIndicator N * ∏ d ∈ T, shiftSqfreeIndicator b N d := by
  unfold countJointSquarefree
  rw [Finset.natCast_card_filter]
  congr 1
  ext N
  exact indicator_conjunction_eq_prod b N T

/-- Finite inclusion-exclusion for dead end counting.
    For each fixed X, the count of dead ends equals the alternating sum over subsets T:
    #{N ≤ X : dead end} = ∑_{T ⊆ {0,...,b-1}} (-1) ^ |T| · #{N ≤ X : N sf ∧ ∀d∈T, bN+d sf}
    This is the finite Bonferroni identity: for events A_d = "bN+d is squarefree",
    #{sf N : all A_d fail} = ∑_T (-1) ^ |T| #{sf N : ∀d∈T, A_d holds}.
    Mathlib has `Finset.sum_powerset_neg_one_pow_card` for this pattern. -/
lemma dead_end_count_inclusion_exclusion (b : ℕ) (_hb : 2 ≤ b) (X : ℕ) :
    (countBaseBDeadEnds b X : ℝ) =
    ∑ T ∈ (Finset.range b).powerset, ((-1 : ℝ) ^ T.card) * (countJointSquarefree b T X : ℝ) := by
  have hb_pos : 0 < b := by omega
  rw [countBaseBDeadEnds_as_sum b X hb_pos]
  have h1 : ∑ N ∈ Finset.Icc 1 X, sqfreeIndicator N * ∏ d ∈ Finset.range b, (1 -
      shiftSqfreeIndicator b N d) =
            ∑ N ∈ Finset.Icc 1 X, sqfreeIndicator N * ∑ T ∈ (Finset.range b).powerset, (
                -1 : ℝ) ^ T.card * ∏ d ∈ T, shiftSqfreeIndicator b N d := by
    congr 1
    ext N
    congr 1
    exact prod_one_sub_eq_sum_powerset (Finset.range b) (shiftSqfreeIndicator b N)
  rw [h1]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext T
  rw [countJointSquarefree_as_sum b X T]
  have h2 : ∀ N, sqfreeIndicator N * ((-1:ℝ) ^ T.card * ∏ d ∈ T, shiftSqfreeIndicator b N d) =
            (sqfreeIndicator N * ∏ d ∈ T, shiftSqfreeIndicator b N d) * (-1:ℝ) ^ T.card := by
    intro N
    ring
  simp only [h2]
  rw [← Finset.sum_mul]
  ring

/-- Tendsto of alternating sums given Tendsto of each term.
    If for each T ⊆ {0,...,b-1}, the ratio (countJointSquarefree b T X)/X → α(b,T),
    then the alternating sum ∑_T (-1) ^ |T| · (countJointSquarefree b T X)/X
    converges to ∑_T (-1) ^ |T| · α(b,T) = explicitDensityFormula b.
    This uses that Filter.Tendsto is preserved under finite sums:
    `Filter.Tendsto.sum : ∀ (hf : ∀ i ∈ s, Tendsto (f i) l (nhds (a i))),
      Tendsto (fun x => ∑ i ∈ s, f i x) l (nhds (∑ i ∈ s, a i))` -/
lemma alternating_sum_tendsto (b : ℕ) (_hb : 2 ≤ b)
    (h_tendsto : ∀ T ∈ (Finset.range b).powerset,
      Filter.Tendsto (fun X : ℕ => (countJointSquarefree b T X : ℝ) / (X : ℝ))
        Filter.atTop (nhds (jointSquarefreeDensity b T))) :
    Filter.Tendsto
      (fun X : ℕ => ∑ T ∈ (Finset.range b).powerset,
        ((-1 : ℝ) ^ T.card) * ((countJointSquarefree b T X : ℝ) / (X : ℝ)))
      Filter.atTop (nhds (explicitDensityFormula b)) := by
  unfold explicitDensityFormula
  apply tendsto_finset_sum
  intro T hT
  exact (h_tendsto T hT).const_mul _

/-- Rewriting the sum: factor out division by X.
    ∑_T (-1) ^ |T| · count(T,X) / X = (∑_T (-1) ^ |T| · count(T,X)) / X when X ≠ 0.
    Uses basic algebra: ∑_i (a_i / c) = (∑_i a_i) / c for c ≠ 0. -/
lemma sum_div_eq_div_sum (b : ℕ) (X : ℕ) (_hX : 0 < X) :
    ∑ T ∈ (Finset.range b).powerset,
      ((-1 : ℝ) ^ T.card) * ((countJointSquarefree b T X : ℝ) / (X : ℝ)) =
    (∑ T ∈ (Finset.range b).powerset,
      ((-1 : ℝ) ^ T.card) * (countJointSquarefree b T X : ℝ)) / (X : ℝ) := by
  have h_main : ∑ T ∈ (Finset.range b).powerset, ((-1 : ℝ) ^ T.card) * (
      (countJointSquarefree b T X : ℝ) / (X : ℝ)) = ∑ T ∈ (Finset.range b).powerset, (
          ((-1 : ℝ) ^ T.card) * (countJointSquarefree b T X : ℝ)) / (X : ℝ) := by
    apply Finset.sum_congr rfl
    intro T _
    have h₁ : ((-1 : ℝ) ^ T.card) * ((countJointSquarefree b T X : ℝ) / (X : ℝ)) = (
        ((-1 : ℝ) ^ T.card) * (countJointSquarefree b T X : ℝ)) / (X : ℝ) := by
      ring_nf
    rw [h₁]
  have h_sum_div : ∑ T ∈ (Finset.range b).powerset, (((-1 : ℝ) ^ T.card) * (
      countJointSquarefree b T X : ℝ)) / (X : ℝ) = (∑ T ∈ (Finset.range b).powerset, (
          (-1 : ℝ) ^ T.card) * (countJointSquarefree b T X : ℝ)) / (X : ℝ) := by
    have h₁ : ∑ T ∈ (Finset.range b).powerset, (((-1 : ℝ) ^ T.card) * (
        countJointSquarefree b T X : ℝ)) / (X : ℝ) = (∑ T ∈ (Finset.range b).powerset, (
            (-1 : ℝ) ^ T.card) * (countJointSquarefree b T X : ℝ)) / (X : ℝ) := by
      rw [Finset.sum_div]
    exact h₁
  have h_final : ∑ T ∈ (Finset.range b).powerset, ((-1 : ℝ) ^ T.card) * (
      (countJointSquarefree b T X : ℝ) / (X : ℝ)) = (∑ T ∈ (Finset.range b).powerset, (
          (-1 : ℝ) ^ T.card) * (countJointSquarefree b T X : ℝ)) / (X : ℝ) := by
    rw [h_main]
    rw [h_sum_div]
  apply h_final

/-! ## Main theorems -/

/-- Combining inclusion-exclusion and joint densities to get the main density result.
    Uses:
    - joint_density_eq_euler_product for each T (joint density = α(b,T))
    - dead_end_count_inclusion_exclusion (finite IE for counting)
    - alternating_sum_tendsto (Tendsto preserved under finite sums)
    The proof shows countBaseBDeadEnds/X → explicitDensityFormula by:
    1. Rewriting via finite IE
    2. Factoring division
    3. Taking limits term by term -/
lemma dead_end_tendsto_explicit_formula (b : ℕ) (hb : 2 ≤ b) :
    Filter.Tendsto (fun X : ℕ => (countBaseBDeadEnds b X : ℝ) / (X : ℝ))
      Filter.atTop (nhds (explicitDensityFormula b)) := by
  -- Step 1: Get tendsto for each joint density
  have h_joint : ∀ T ∈ (Finset.range b).powerset,
      Filter.Tendsto (fun X : ℕ => (countJointSquarefree b T X : ℝ) / (X : ℝ))
        Filter.atTop (nhds (jointSquarefreeDensity b T)) := by
    intro T hT
    exact joint_density_eq_euler_product b hb T (Finset.mem_powerset.mp hT)
  -- Step 2: Get tendsto for the alternating sum of ratios
  have h_alt := alternating_sum_tendsto b hb h_joint
  -- Step 3: Rewrite dead end count using inclusion-exclusion
  have h_eq : (fun X : ℕ => (countBaseBDeadEnds b X : ℝ) / (X : ℝ)) =ᶠ[Filter.atTop]
      (fun X : ℕ => ∑ T ∈ (Finset.range b).powerset,
        ((-1 : ℝ) ^ T.card) * ((countJointSquarefree b T X : ℝ) / (X : ℝ))) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with X hX
    rw [dead_end_count_inclusion_exclusion b hb X]
    rw [sum_div_eq_div_sum b X hX]
  exact h_alt.congr' h_eq.symm

theorem baseBDeadEnd_density_exists (b : ℕ) (hb : 2 ≤ b) :
    ∃ D : ℝ, HasAsymptoticDensity b D :=
  ⟨explicitDensityFormula b, dead_end_tendsto_explicit_formula b hb⟩

theorem baseBDeadEnd_density_unique (b : ℕ) (D₁ D₂ : ℝ)
    (h₁ : HasAsymptoticDensity b D₁) (h₂ : HasAsymptoticDensity b D₂) :
    D₁ = D₂ := by
  exact tendsto_nhds_unique h₁ h₂

/-- The asymptotic density `D_b` of base-`b` dead ends, defined (when `b ≥ 2`) as the
unique limit guaranteed by `baseBDeadEnd_density_exists`. -/
noncomputable def baseBDeadEndDensity (b : ℕ) (hb : 2 ≤ b) : ℝ :=
  Classical.choose (baseBDeadEnd_density_exists b hb)

theorem baseBDeadEndDensity_spec (b : ℕ) (hb : 2 ≤ b) :
    HasAsymptoticDensity b (baseBDeadEndDensity b hb) :=
  Classical.choose_spec (baseBDeadEnd_density_exists b hb)

theorem jointSquarefreeDensity_convergent (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) :
    Multipliable (fun p : Nat.Primes => localDensityFactor (p : ℕ) b T) := by
  exact multipliable_of_deviation_summable b hb T hT (
      sum_localDensityFactor_deviation_summable b hb T hT)

theorem jointSquarefreeDensity_is_asymptotic_density (b : ℕ) (hb : 2 ≤ b) (T : Finset ℕ)
    (hT : T ⊆ Finset.range b) :
    let countJoint (X : ℕ) : ℕ :=
      (Finset.Icc 1 X).filter (fun N =>
        Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d)) |>.card
    Filter.Tendsto (fun X : ℕ => (countJoint X : ℝ) / (X : ℝ))
      Filter.atTop (nhds (jointSquarefreeDensity b T)) := by
  exact joint_density_eq_euler_product b hb T hT

theorem baseBDeadEnd_density_formula (b : ℕ) (hb : 2 ≤ b) :
    baseBDeadEndDensity b hb = explicitDensityFormula b := by
  have h1 : HasAsymptoticDensity b (baseBDeadEndDensity b hb) := baseBDeadEndDensity_spec b hb
  have h2 : HasAsymptoticDensity b (explicitDensityFormula b) :=
    dead_end_tendsto_explicit_formula b hb
  exact baseBDeadEnd_density_unique b _ _ h1 h2

theorem explicitDensityFormula_correct (b : ℕ) (hb : 2 ≤ b) :
    HasAsymptoticDensity b (explicitDensityFormula b) :=
  dead_end_tendsto_explicit_formula b hb
end LeanPool.DeadEnds
