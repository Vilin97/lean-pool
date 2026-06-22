/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.PNat.Prime
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompletePartialOrder

/-! ## Counting functions for joint conditions -/

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
  have h_summable : Summable (fun p : Nat.Primes => localDensityFactor (p : ℕ) b T - 1) :=
    Summable.of_abs h_sum
  have h_mult : Multipliable (fun p : Nat.Primes => 1 + (localDensityFactor (p : ℕ) b T - 1)) :=
    Real.multipliable_one_add_of_summable h_summable
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


end LeanPool.DeadEnds
