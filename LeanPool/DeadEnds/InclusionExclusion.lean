/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Seewoo Lee, Ken Ono, Jujian Zhang
-/

import LeanPool.DeadEnds.TailEstimates

/-! ## Helper lemmas for inclusion-exclusion -/

namespace LeanPool.DeadEnds


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
  by_cases hsq : Squarefree N
  · by_cases hshift : ∀ d ∈ Finset.range b, ¬Squarefree (b * N + d)
    · have hdead : IsBaseBDeadEnd b N := ⟨by omega, hsq, hshift⟩
      have hprod : (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = 1 := by
        apply Finset.prod_eq_one
        intro d hd
        simp [shiftSqfreeIndicator, hshift d hd]
      simp [hdead, sqfreeIndicator, hsq, hprod]
    · have hnotdead : ¬ IsBaseBDeadEnd b N := by
        intro hdead
        exact hshift hdead.2.2
      push Not at hshift
      obtain ⟨d, hd, hd_sqfree⟩ := hshift
      have hprod : (∏ d ∈ Finset.range b, (1 - shiftSqfreeIndicator b N d) : ℝ) = 0 := by
        apply Finset.prod_eq_zero hd
        simp [shiftSqfreeIndicator, hd_sqfree]
      simp [hnotdead, sqfreeIndicator, hsq, hprod]
  · have hnotdead : ¬ IsBaseBDeadEnd b N := by
      intro hdead
      exact hsq hdead.2.1
    simp [hnotdead, sqfreeIndicator, hsq]

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
  by_cases hsq : Squarefree N
  · by_cases hall : ∀ d ∈ T, Squarefree (b * N + d)
    · have hprod : (∏ d ∈ T, shiftSqfreeIndicator b N d) = 1 := by
        apply Finset.prod_eq_one
        intro d hd
        simp [shiftSqfreeIndicator, hall d hd]
      have hcond : Squarefree N ∧ ∀ d ∈ T, Squarefree (b * N + d) := ⟨hsq, hall⟩
      rw [if_pos hcond, hprod]
      simp [sqfreeIndicator, hsq]
    · push Not at hall
      obtain ⟨d, hd, hd_not_sqfree⟩ := hall
      have hprod : (∏ d ∈ T, shiftSqfreeIndicator b N d) = 0 := by
        apply Finset.prod_eq_zero hd
        simp [shiftSqfreeIndicator, hd_not_sqfree]
      have hnot : ¬(Squarefree N ∧ ∀ x ∈ T, Squarefree (b * N + x)) := by
        rintro ⟨_, hall⟩
        exact hd_not_sqfree (hall d hd)
      rw [if_neg hnot, hprod]
      simp [sqfreeIndicator, hsq]
  · simp [sqfreeIndicator, hsq]

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
    #{N ≤ X : dead end} =
      ∑_{T ⊆ Finset.range b} (-1) ^ |T| · #{N ≤ X : N sf ∧ ∀d∈T, bN+d sf}
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
    If for each T ⊆ Finset.range b, the ratio (countJointSquarefree b T X)/X → α(b,T),
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
  apply tendsto_finsetSum
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
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T _
  ring

/-! ## Main theorems -/

/-- The base-`b` dead-end counting ratios tend to the explicit inclusion-exclusion density. -/
lemma dead_end_tendsto_explicit_formula (b : ℕ) (hb : 2 ≤ b) :
    Filter.Tendsto (fun X : ℕ => (countBaseBDeadEnds b X : ℝ) / (X : ℝ))
      Filter.atTop (nhds (explicitDensityFormula b)) := by
  have h_joint : ∀ T ∈ (Finset.range b).powerset,
      Filter.Tendsto (fun X : ℕ => (countJointSquarefree b T X : ℝ) / (X : ℝ))
        Filter.atTop (nhds (jointSquarefreeDensity b T)) := by
    intro T hT
    exact joint_density_eq_euler_product b hb T (Finset.mem_powerset.mp hT)
  have h_alt := alternating_sum_tendsto b hb h_joint
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
