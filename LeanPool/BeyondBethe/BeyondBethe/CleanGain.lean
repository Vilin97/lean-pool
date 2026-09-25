/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.CleanWitness
public import LeanPool.BeyondBethe.BeyondBethe.PairFactorization
public import Mathlib.Tactic

/-! # Clean Gain -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-- The right-hand side of paper (61), before the final uniform choice of
constants. -/
noncomputable def cleanGainLowerBound
    {ι : Type*} [Fintype ι]
    (κ τ ρ : ℝ) (α : ι → ℝ) : ℝ :=
  (1 - ρ) * Real.log ((2 * (Real.exp (-κ)) ^ 2) / (1 - ρ)) +
    ρ * Real.log (Real.exp (-κ)) + ρ * Real.log ρ - ρ -
    τ * (-(∑ l, α l * Real.log (α l)) + ρ * Real.log 2)

theorem isEmpty_outsideColumn_of_pairAlpha_outsideMass_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r s a b : ι}
    (hzero : outsideMassTwo (pairAlpha X r s) a b = 0) :
    IsEmpty (OutsideColumn a b) := by
  constructor
  intro l
  have hsum : (∑ x : OutsideColumn a b, pairAlpha X r s x.1) = 0 := by
    rw [sum_outsideColumn_eq_outsideMassTwo, hzero]
  have hle : pairAlpha X r s l.1 ≤
      ∑ x : OutsideColumn a b, pairAlpha X r s x.1 :=
    Finset.single_le_sum
      (fun x _ ↦ pairAlpha_nonneg hX r s x.1) (Finset.mem_univ l)
  have hpos : 0 < pairAlpha X r s l.1 :=
    add_pos ((hXint r).2 l.1).1 ((hXint s).2 l.1).1
  linarith

/-- At zero leakage the limiting witness mentioned in paper (52) is the
point mass on the core pair, and it has the required exponent moment. -/
theorem cleanWitness_pairAlpha_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    {r s a b : ι} (hrs : r ≠ s) (hab : a ≠ b)
    (hzero : outsideMassTwo (pairAlpha X r s) a b = 0)
    (hempty : IsEmpty (OutsideColumn a b)) :
    let α := pairAlpha X r s
    let θ := capacityWitnessMass 0 0 0
      (fun l : OutsideColumn a b ↦ α l.1)
    IsProbabilityVector θ ∧
      ∀ j, exponentMoment θ (cleanWitnessExponent a b) j = α j := by
  letI : IsEmpty (OutsideColumn a b) := hempty
  dsimp only
  have ha : pairAlpha X r s a = 1 := by
    have hsplit := twoCore_add_outsideMassTwo_eq_sum
      (pairAlpha X r s) hab
    rw [hzero, sum_pairAlpha hX r s] at hsplit
    have hlea := pairAlpha_le_one hX hrs a
    have hleb := pairAlpha_le_one hX hrs b
    linarith
  have hb : pairAlpha X r s b = 1 := by
    have hsplit := twoCore_add_outsideMassTwo_eq_sum
      (pairAlpha X r s) hab
    rw [hzero, sum_pairAlpha hX r s] at hsplit
    have hlea := pairAlpha_le_one hX hrs a
    have hleb := pairAlpha_le_one hX hrs b
    linarith
  constructor
  · constructor
    · intro e
      rcases e with e | e
      · simp [capacityWitnessMass]
      · exact isEmptyElim e
    · simp [capacityWitnessMass]
  · intro j
    have hj : j = a ∨ j = b := by
      by_contra h
      push Not at h
      let l : OutsideColumn a b := ⟨j, by
        simp [outsideColumnFinset, h.1, h.2]⟩
      exact isEmptyElim l
    rcases hj with rfl | rfl
    · rw [exponentMoment]
      simp [capacityWitnessMass, cleanWitnessExponent, ha]
    · rw [exponentMoment]
      simp [capacityWitnessMass, cleanWitnessExponent, hb]

theorem pairTransferPolynomialCapacity_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} {X : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r s a b : ι} (hrs : r ≠ s) (hab : a ≠ b)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b)
    (hρ1 : outsideMassTwo (pairAlpha X r s) a b ≤ 1) :
    0 < polynomialCapacity (pairAlpha X r s)
      (pairPolynomial (fun j ↦ transferU τ (X r) j)
        (fun j ↦ transferU τ (X s) j)) := by
  let α := pairAlpha X r s
  let ρ := outsideMassTwo α a b
  let δa := 1 - α a
  let δb := 1 - α b
  let Ur : ι → ℝ := fun j ↦ transferU τ (X r) j
  let Us : ι → ℝ := fun j ↦ transferU τ (X s) j
  let θ := capacityWitnessMass ρ δa δb
    (fun l : OutsideColumn a b ↦ α l.1)
  have hprob := cleanWitness_pairAlpha_isProbabilityVector
    hX hrs hab hρ hρ1
  have hmom := cleanWitness_pairAlpha_moment hX hab hρ
  have hcoeff : ∀ e, 0 < cleanWitnessCoefficient Ur Us a b e :=
    cleanWitnessCoefficient_positive
      (fun j ↦ transferU_pos (hXint r) j)
      (fun j ↦ transferU_pos (hXint s) j) a b
  have hexp := exp_entropyCapacityCertificate_le_finitePolynomialCapacity
    hprob.1 hprob.2 hcoeff hmom
  have hcap := cleanWitnessCapacity_le_pairPolynomialCapacity hab
    (u := Ur) (v := Us) (α := α)
    (fun j ↦ (transferU_pos (τ := τ) (hXint r) j).le)
    (fun j ↦ (transferU_pos (τ := τ) (hXint s) j).le)
  dsimp only [α, Ur, Us] at hcap ⊢
  exact (Real.exp_pos _).trans_le (hexp.trans hcap)

/-- Positive-leakage branch of paper Lemma 19 through equation (61).  Every
factor in the pair factorization and every boundary-sensitive logarithm is
accounted for explicitly. -/
theorem log_pairGain_ge_cleanGainLowerBound_of_positiveLeakage
    {n : ℕ} {τ κ : ℝ} (hτ : 0 ≤ τ)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    {rscale cscale : Fin n → ℝ}
    (hApos : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hrscale : ∀ i, 0 < rscale i) (hcscale : ∀ j, 0 < cscale j)
    (hKKT : HasMultiplicativeKKT τ A X rscale cscale)
    {r s a b : Fin n} (hrs : r ≠ s) (hab : a ≠ b)
    (hcost : fourCoreTransferCost τ X r s a b ≤ κ)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b)
    (hρ1 : outsideMassTwo (pairAlpha X r s) a b < 1) :
    cleanGainLowerBound κ τ
        (outsideMassTwo (pairAlpha X r s) a b)
        (fun l : OutsideColumn a b ↦ pairAlpha X r s l.1) ≤
      Real.log (pairGain A X r s) := by
  let α := pairAlpha X r s
  let ρ := outsideMassTwo α a b
  let δa := 1 - α a
  let δb := 1 - α b
  let Ur : Fin n → ℝ := fun j ↦ transferU τ (X r) j
  let Us : Fin n → ℝ := fun j ↦ transferU τ (X s) j
  let cap := polynomialCapacity α (pairPolynomial Ur Us)
  let prodFactor := ∏ j, (1 - α j) ^ (1 - α j)
  let scale := 1 / (rowZeta τ (X r) * rowZeta τ (X s))
  have hfactor := pairGain_factorization hApos hX hXint
    hrscale hcscale hKKT r s
  have hcard := two_lt_card_of_outsideMassTwo_pos hab hρ
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hαlt : ∀ j, α j < 1 := fun j ↦
    pairAlpha_lt_one_of_positive hX hXpos hcard hrs j
  have hcomp : ∀ j, 0 < 1 - α j := fun j ↦ sub_pos.mpr (hαlt j)
  have hprodPos : 0 < prodFactor := by
    dsimp only [prodFactor]
    exact Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hcomp j) _
  have hcapPos : 0 < cap := by
    dsimp only [cap, α, Ur, Us]
    exact pairTransferPolynomialCapacity_pos hX hXint hrs hab hρ hρ1.le
  have hzetaR : 0 < rowZeta τ (X r) :=
    rowZeta_pos (fun j ↦ (hXint r).2 j |>.1)
  have hzetaS : 0 < rowZeta τ (X s) :=
    rowZeta_pos (fun j ↦ (hXint s).2 j |>.1)
  have hzetaRle : rowZeta τ (X r) ≤ 1 :=
    rowZeta_le_one hτ (hX.row_probability r)
  have hzetaSle : rowZeta τ (X s) ≤ 1 :=
    rowZeta_le_one hτ (hX.row_probability s)
  have hdenPos : 0 < rowZeta τ (X r) * rowZeta τ (X s) :=
    mul_pos hzetaR hzetaS
  have hdenLe : rowZeta τ (X r) * rowZeta τ (X s) ≤ 1 :=
    (mul_le_mul hzetaRle hzetaSle hzetaS.le (by norm_num)).trans_eq
      (mul_one 1)
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact one_div_pos.mpr hdenPos
  have hscaleOne : 1 ≤ scale := by
    dsimp only [scale]
    exact (le_div_iff₀ hdenPos).2 (by simpa using hdenLe)
  have hlogScale : 0 ≤ Real.log scale := Real.log_nonneg hscaleOne
  have hlogFactor : Real.log (pairGain A X r s) =
      Real.log scale +
        (∑ j, (1 - α j) * Real.log (1 - α j)) +
        Real.log cap := by
    rw [hfactor]
    dsimp only [scale, prodFactor, cap, α, Ur, Us]
    rw [Real.log_mul (mul_pos hscalePos hprodPos).ne' hcapPos.ne',
      Real.log_mul hscalePos.ne' hprodPos.ne',
      Real.log_prod (fun j _ ↦
        (Real.rpow_pos_of_pos (hcomp j) _).ne')]
    simp_rw [Real.log_rpow (hcomp _)]
    ring
  have hsumDecomp :
      (∑ j, (1 - α j) * Real.log (1 - α j)) =
        δa * Real.log δa + δb * Real.log δb +
          ∑ l : OutsideColumn a b,
            (1 - α l.1) * Real.log (1 - α l.1) := by
    have hsplit := twoCore_add_outsideMassTwo_eq_sum
      (fun j ↦ (1 - α j) * Real.log (1 - α j)) hab
    rw [← sum_outsideColumn_eq_outsideMassTwo] at hsplit
    dsimp only [δa, δb]
    exact hsplit.symm
  have houtsideFactor :
      -ρ ≤ ∑ l : OutsideColumn a b,
        (1 - α l.1) * Real.log (1 - α l.1) := by
    calc
      -ρ = ∑ l : OutsideColumn a b, -α l.1 := by
        rw [Finset.sum_neg_distrib,
          show (∑ l : OutsideColumn a b, α l.1) = ρ by
            exact sum_outsideColumn_eq_outsideMassTwo α a b]
      _ ≤ ∑ l : OutsideColumn a b,
          (1 - α l.1) * Real.log (1 - α l.1) := by
        apply Finset.sum_le_sum
        intro l _
        exact neg_alpha_le_one_sub_mul_log (hαlt l.1)
  have hsumLower :
      δa * Real.log δa + δb * Real.log δb - ρ ≤
        ∑ j, (1 - α j) * Real.log (1 - α j) := by
    rw [hsumDecomp]
    linarith
  have hδpos := pairAlpha_coreDeficit_pos hX hXint hrs hab hρ
  have hδsum : δa + δb = ρ := by
    have hsplit := twoCore_add_outsideMassTwo_eq_sum α hab
    rw [show ∑ j, α j = 2 by
      simpa only [α] using sum_pairAlpha hX r s] at hsplit
    dsimp only [δa, δb, ρ]
    linarith
  have hcancel := core_entropy_cancellation
    hδpos.1 hδpos.2 hρ hδsum
  have hcapLower := pairTransfer_capacity_theta_bound hτ hX hXint
    hrs hab hcost hρ hρ1
  rw [hlogFactor]
  dsimp only [cleanGainLowerBound, α, ρ, δa, δb, Ur, Us, cap] at *
  linarith

/-- Zero-leakage branch of paper Lemma 19.  This formalizes the manuscript's
"limiting distribution concentrated on `{a,b}`" directly, without a limit
argument. -/
theorem log_pairGain_ge_core_of_zeroLeakage
    {n : ℕ} {τ κ : ℝ} (hτ : 0 ≤ τ)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    {rscale cscale : Fin n → ℝ}
    (hApos : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hrscale : ∀ i, 0 < rscale i) (hcscale : ∀ j, 0 < cscale j)
    (hKKT : HasMultiplicativeKKT τ A X rscale cscale)
    {r s a b : Fin n} (hrs : r ≠ s) (hab : a ≠ b)
    (hcost : fourCoreTransferCost τ X r s a b ≤ κ)
    (hzero : outsideMassTwo (pairAlpha X r s) a b = 0) :
    Real.log (2 * (Real.exp (-κ)) ^ 2) ≤
      Real.log (pairGain A X r s) := by
  let α := pairAlpha X r s
  let Ur : Fin n → ℝ := fun j ↦ transferU τ (X r) j
  let Us : Fin n → ℝ := fun j ↦ transferU τ (X s) j
  let cap := polynomialCapacity α (pairPolynomial Ur Us)
  let scale := 1 / (rowZeta τ (X r) * rowZeta τ (X s))
  letI : IsEmpty (OutsideColumn a b) :=
    isEmpty_outsideColumn_of_pairAlpha_outsideMass_eq_zero hX hXint hzero
  let θ := capacityWitnessMass 0 0 0
    (fun l : OutsideColumn a b ↦ α l.1)
  have hzeroWitness := cleanWitness_pairAlpha_zero hX hrs hab hzero
    (inferInstance : IsEmpty (OutsideColumn a b))
  have hcoeff : ∀ e, 0 < cleanWitnessCoefficient Ur Us a b e :=
    cleanWitnessCoefficient_positive
      (fun j ↦ transferU_pos (hXint r) j)
      (fun j ↦ transferU_pos (hXint s) j) a b
  have hcertUpper :=
    cleanWitnessEntropyCertificate_le_log_pairPolynomialCapacity hab
      hzeroWitness.1.1 hzeroWitness.1.2 hcoeff hzeroWitness.2
      (fun j ↦ (transferU_pos (hXint r) j).le)
      (fun j ↦ (transferU_pos (hXint s) j).le)
  have hcertCore : entropyCapacityCertificate θ
      (cleanWitnessCoefficient Ur Us a b) =
        Real.log (cleanWitnessCoefficient Ur Us a b (Sum.inl ())) := by
    dsimp only [θ]
    simp [entropyCapacityCertificate, capacityWitnessMass]
  have hcore := fourCoreTransfer_lower hτ hXint hcost
  have hcoreCoeff := cleanWitnessCoefficient_core_lower
    (Real.exp_pos _).le hcore.1 hcore.2.1 hcore.2.2.1 hcore.2.2.2
  have hcoreBase : 0 < 2 * (Real.exp (-κ)) ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos (Real.exp_pos _))
  have hlogCore : Real.log (2 * (Real.exp (-κ)) ^ 2) ≤
      Real.log (cleanWitnessCoefficient Ur Us a b (Sum.inl ())) :=
    Real.log_le_log hcoreBase hcoreCoeff
  have hcapLower : Real.log (2 * (Real.exp (-κ)) ^ 2) ≤
      Real.log cap := by
    dsimp only [cap]
    exact hlogCore.trans (hcertCore ▸ hcertUpper)
  have hexp := exp_entropyCapacityCertificate_le_finitePolynomialCapacity
    hzeroWitness.1.1 hzeroWitness.1.2 hcoeff hzeroWitness.2
  have hcapFinite := cleanWitnessCapacity_le_pairPolynomialCapacity hab
    (u := Ur) (v := Us) (α := α)
    (fun j ↦ (transferU_pos (hXint r) j).le)
    (fun j ↦ (transferU_pos (hXint s) j).le)
  have hcapPos : 0 < cap := by
    dsimp only [cap]
    exact (Real.exp_pos _).trans_le (hexp.trans hcapFinite)
  have ha : α a = 1 := by
    have hsplit := twoCore_add_outsideMassTwo_eq_sum α hab
    rw [show outsideMassTwo α a b = 0 by simpa only [α] using hzero,
      show ∑ j, α j = 2 by simpa only [α] using sum_pairAlpha hX r s]
      at hsplit
    have hlea := pairAlpha_le_one hX hrs a
    have hleb := pairAlpha_le_one hX hrs b
    dsimp only [α]
    linarith
  have hb : α b = 1 := by
    have hsplit := twoCore_add_outsideMassTwo_eq_sum α hab
    rw [show outsideMassTwo α a b = 0 by simpa only [α] using hzero,
      show ∑ j, α j = 2 by simpa only [α] using sum_pairAlpha hX r s]
      at hsplit
    have hlea := pairAlpha_le_one hX hrs a
    have hleb := pairAlpha_le_one hX hrs b
    dsimp only [α]
    linarith
  have hαone : ∀ j, α j = 1 := by
    intro j
    have hj : j = a ∨ j = b := by
      by_contra h
      push Not at h
      let l : OutsideColumn a b := ⟨j, by
        simp [outsideColumnFinset, h.1, h.2]⟩
      exact isEmptyElim l
    exact hj.elim (fun h ↦ h ▸ ha) (fun h ↦ h ▸ hb)
  have hfactor := pairGain_factorization hApos hX hXint
    hrscale hcscale hKKT r s
  have hgainEq : pairGain A X r s = scale * cap := by
    rw [hfactor]
    simp_rw [show ∀ j, pairAlpha X r s j = 1 by
      simpa only [α] using hαone]
    simp [scale, cap, α, Ur, Us]
  have hzetaR : 0 < rowZeta τ (X r) :=
    rowZeta_pos (fun j ↦ (hXint r).2 j |>.1)
  have hzetaS : 0 < rowZeta τ (X s) :=
    rowZeta_pos (fun j ↦ (hXint s).2 j |>.1)
  have hdenPos : 0 < rowZeta τ (X r) * rowZeta τ (X s) :=
    mul_pos hzetaR hzetaS
  have hdenLe : rowZeta τ (X r) * rowZeta τ (X s) ≤ 1 := by
    have hrle := rowZeta_le_one hτ (hX.row_probability r)
    have hsle := rowZeta_le_one hτ (hX.row_probability s)
    nlinarith [mul_nonneg hzetaR.le hzetaS.le,
      mul_nonneg (sub_nonneg.mpr hrle) (sub_nonneg.mpr hsle)]
  have hscaleOne : 1 ≤ scale := by
    dsimp only [scale]
    exact (le_div_iff₀ hdenPos).2 (by simpa using hdenLe)
  have hcapGain : cap ≤ pairGain A X r s := by
    rw [hgainEq]
    exact le_mul_of_one_le_left hcapPos.le hscaleOne
  exact hcapLower.trans (Real.log_le_log hcapPos hcapGain)

end BeyondBethe
