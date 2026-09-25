/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.CleanGain
public import LeanPool.BeyondBethe.BeyondBethe.NumericalCapacity
public import Mathlib.Tactic

/-! # Numerical Witness -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Explicit finite witnesses for the pair gain

The clean-pair proof already constructs a sparse feasible coefficient
distribution.  Evaluating these distributions for every candidate pair of
core columns removes the need to solve a second convex program for each pair
capacity.  This file records the exact logarithmic witness and its one-sided
comparison with the true pair gain.
-/

/-- The sparse coefficient distribution associated with candidate core
columns `a,b`.  When the outside mass is zero, Lean's totalized division makes
the two arm families vanish and leaves the point mass on the core edge. -/
noncomputable def explicitPairWitness
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (r s a b : Fin n) : CapacityWitnessEdge (OutsideColumn a b) → ℝ :=
  let α := pairAlpha X r s
  let ρ := outsideMassTwo α a b
  let δa := 1 - α a
  let δb := 1 - α b
  capacityWitnessMass ρ δa δb (fun l ↦ α l.1)

/-- Logarithm of the explicit witness lower bound on `pairGain`. -/
noncomputable def explicitPairWitnessLogGain
    {n : ℕ} (τ : ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (r s a b : Fin n) : ℝ :=
  let α := pairAlpha X r s
  let Ur : Fin n → ℝ := fun j ↦ transferU τ (X r) j
  let Us : Fin n → ℝ := fun j ↦ transferU τ (X s) j
  let θ := explicitPairWitness X r s a b
  let coeff := cleanWitnessCoefficient Ur Us a b
  let normalization :=
    -Real.log (rowZeta τ (X r)) - Real.log (rowZeta τ (X s))
  let productTerm := ∑ j, (1 - α j) * Real.log (1 - α j)
  let certificate := entropyCapacityCertificate θ coeff
  normalization + productTerm + certificate

/-- Algorithm-facing form of the clean-pair lemma.  Unlike
`CleanPairGainGuarantee`, this statement does not mention the input matrix or
KKT multipliers: it says that the finite witness computed from `X` already
has the advertised gain.  This is the form needed before directed rational
evaluation and threshold matching are introduced. -/
def ExplicitPairWitnessGainGuarantee (κ₀ ξ₀ γ₀ : ℝ) : Prop :=
  ∀ {n : ℕ} {ell ξ τ : ℝ} {X : Matrix (Fin n) (Fin n) ℝ},
    1 ≤ ell →
    Real.log n ≤ ell * Real.log 2 →
    0 < ξ → ξ ≤ ξ₀ → τ = ξ / (4 * ell) →
    IsDoublyStochastic X →
    (∀ i, IsInteriorProbabilityVector (X i)) →
    ∀ {r s a b : Fin n}, r ≠ s → a ≠ b →
      fourCoreTransferCost τ X r s a b ≤ κ₀ →
      γ₀ ≤ explicitPairWitnessLogGain τ X r s a b

/-- For positive outside mass at most one, the explicit distribution is an
exactly feasible capacity witness. -/
theorem explicitPairWitness_isCapacityDistribution_of_positiveLeakage
    {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X)
    {r s a b : Fin n} (hrs : r ≠ s) (hab : a ≠ b)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b)
    (hρ1 : outsideMassTwo (pairAlpha X r s) a b ≤ 1) :
    IsCapacityDistribution (explicitPairWitness X r s a b)
      (cleanWitnessExponent a b) (pairAlpha X r s) := by
  constructor
  · simpa only [explicitPairWitness] using
      cleanWitness_pairAlpha_isProbabilityVector hX hrs hab hρ hρ1
  · simpa only [explicitPairWitness] using
      cleanWitness_pairAlpha_moment hX hab hρ

/-- The clean-pair analysis lower-bounds the explicit witness itself, not
merely the larger optimized capacity.  This is the formal statement that
justifies replacing the capacity program by finite witness enumeration. -/
theorem cleanGainLowerBound_le_explicitPairWitnessLogGain
    {n : ℕ} {τ κ : ℝ} (hτ : 0 ≤ τ)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r s a b : Fin n} (hrs : r ≠ s) (hab : a ≠ b)
    (hcost : fourCoreTransferCost τ X r s a b ≤ κ)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b)
    (hρ1 : outsideMassTwo (pairAlpha X r s) a b < 1) :
    cleanGainLowerBound κ τ
        (outsideMassTwo (pairAlpha X r s) a b)
        (fun l : OutsideColumn a b ↦ pairAlpha X r s l.1) ≤
      explicitPairWitnessLogGain τ X r s a b := by
  let α := pairAlpha X r s
  let ρ := outsideMassTwo α a b
  let δa := 1 - α a
  let δb := 1 - α b
  let Ur : Fin n → ℝ := fun j ↦ transferU τ (X r) j
  let Us : Fin n → ℝ := fun j ↦ transferU τ (X s) j
  let θ := explicitPairWitness X r s a b
  let coeff := cleanWitnessCoefficient Ur Us a b
  have hcore := fourCoreTransfer_lower hτ hXint hcost
  have hδpos := pairAlpha_coreDeficit_pos hX hXint hrs hab hρ
  have hαpos : ∀ l : OutsideColumn a b, 0 < α l.1 := by
    intro l
    exact add_pos ((hXint r).2 l.1).1 ((hXint s).2 l.1).1
  have hαsum : ∑ l : OutsideColumn a b, α l.1 = ρ :=
    sum_outsideColumn_eq_outsideMassTwo α a b
  have hδsum : δa + δb = ρ := by
    have hsplit := twoCore_add_outsideMassTwo_eq_sum α hab
    rw [show ∑ j, α j = 2 by
      simpa only [α] using sum_pairAlpha hX r s] at hsplit
    dsimp only [δa, δb, ρ]
    linarith
  have houtside :
      -τ * ρ * Real.log 2 +
          (1 + τ) *
            (∑ l : OutsideColumn a b, α l.1 * Real.log (α l.1)) ≤
        ∑ l : OutsideColumn a b,
          α l.1 * Real.log (Ur l.1 + Us l.1) := by
    exact sum_alpha_log_pairTransfer_lower (a := a) (b := b)
      hτ (hXint r) (hXint s)
      (by simpa only [α, ρ, pairAlpha] using hαsum)
  have hUr : ∀ j, 0 < Ur j := fun j ↦ transferU_pos (hXint r) j
  have hUs : ∀ j, 0 < Us j := fun j ↦ transferU_pos (hXint s) j
  have hcertificateLower :
      (1 - ρ) * Real.log ((2 * (Real.exp (-κ)) ^ 2) / (1 - ρ)) +
          ρ * Real.log (Real.exp (-κ)) - τ * ρ * Real.log 2 +
          τ * (∑ l : OutsideColumn a b, α l.1 * Real.log (α l.1)) -
          δa * Real.log (δa / ρ) - δb * Real.log (δb / ρ) ≤
        entropyCapacityCertificate θ coeff := by
    dsimp only [θ, coeff, explicitPairWitness, α, ρ, δa, δb,
      Ur, Us]
    apply cleanWitness_capacity_theta_lower hab (Real.exp_pos _) hρ hρ1
      hδpos.1 hδpos.2 hδsum hαpos hαsum hUr hUs
    · exact hcore.1
    · exact hcore.2.1
    · exact hcore.2.2.1
    · exact hcore.2.2.2
    · exact houtside
  have hcard := two_lt_card_of_outsideMassTwo_pos hab hρ
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hαlt : ∀ j, α j < 1 := fun j ↦
    pairAlpha_lt_one_of_positive hX hXpos hcard hrs j
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
        rw [Finset.sum_neg_distrib, hαsum]
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
  have hcancel := core_entropy_cancellation
    hδpos.1 hδpos.2 hρ hδsum
  have hzetaR : rowZeta τ (X r) ≤ 1 :=
    rowZeta_le_one hτ (hX.row_probability r)
  have hzetaS : rowZeta τ (X s) ≤ 1 :=
    rowZeta_le_one hτ (hX.row_probability s)
  have hzetaRpos : 0 < rowZeta τ (X r) :=
    rowZeta_pos (fun j ↦ (hXint r).2 j |>.1)
  have hzetaSpos : 0 < rowZeta τ (X s) :=
    rowZeta_pos (fun j ↦ (hXint s).2 j |>.1)
  have hlogNormalization :
      0 ≤ -Real.log (rowZeta τ (X r)) - Real.log (rowZeta τ (X s)) := by
    have hrlog : Real.log (rowZeta τ (X r)) ≤ 0 :=
      Real.log_nonpos hzetaRpos.le hzetaR
    have hslog : Real.log (rowZeta τ (X s)) ≤ 0 :=
      Real.log_nonpos hzetaSpos.le hzetaS
    linarith
  dsimp only [cleanGainLowerBound, explicitPairWitnessLogGain, α, ρ,
    δa, δb, Ur, Us, θ, coeff] at *
  linarith

/-- At zero leakage the explicit point-mass witness retains the full core
coefficient.  This is the boundary counterpart of
`cleanGainLowerBound_le_explicitPairWitnessLogGain`. -/
theorem coreLowerBound_le_explicitPairWitnessLogGain_of_zeroLeakage
    {n : ℕ} {τ κ : ℝ} (hτ : 0 ≤ τ)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r s a b : Fin n} (hrs : r ≠ s) (hab : a ≠ b)
    (hcost : fourCoreTransferCost τ X r s a b ≤ κ)
    (hzero : outsideMassTwo (pairAlpha X r s) a b = 0) :
    Real.log (2 * (Real.exp (-κ)) ^ 2) ≤
      explicitPairWitnessLogGain τ X r s a b := by
  let α := pairAlpha X r s
  let Ur : Fin n → ℝ := fun j ↦ transferU τ (X r) j
  let Us : Fin n → ℝ := fun j ↦ transferU τ (X s) j
  letI : IsEmpty (OutsideColumn a b) :=
    isEmpty_outsideColumn_of_pairAlpha_outsideMass_eq_zero hX hXint hzero
  have hzeroWitness := cleanWitness_pairAlpha_zero hX hrs hab hzero
    (inferInstance : IsEmpty (OutsideColumn a b))
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
  have hθ : explicitPairWitness X r s a b =
      capacityWitnessMass 0 0 0 (fun l : OutsideColumn a b ↦ α l.1) := by
    simp only [explicitPairWitness]
    rw [show outsideMassTwo (pairAlpha X r s) a b = 0 from hzero]
    rw [show 1 - pairAlpha X r s a = 0 by
          simpa only [α] using sub_eq_zero.mpr ha.symm,
      show 1 - pairAlpha X r s b = 0 by
          simpa only [α] using sub_eq_zero.mpr hb.symm]
  have hcertificate :
      entropyCapacityCertificate (explicitPairWitness X r s a b)
        (cleanWitnessCoefficient Ur Us a b) =
      Real.log (cleanWitnessCoefficient Ur Us a b (Sum.inl ())) := by
    rw [hθ]
    simp [entropyCapacityCertificate, capacityWitnessMass]
  have hcore := fourCoreTransfer_lower hτ hXint hcost
  have hcoreCoeff := cleanWitnessCoefficient_core_lower
    (Real.exp_pos _).le hcore.1 hcore.2.1 hcore.2.2.1 hcore.2.2.2
  have hcoreBase : 0 < 2 * (Real.exp (-κ)) ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos (Real.exp_pos _))
  have hlogCore : Real.log (2 * (Real.exp (-κ)) ^ 2) ≤
      Real.log (cleanWitnessCoefficient Ur Us a b (Sum.inl ())) :=
    Real.log_le_log hcoreBase hcoreCoeff
  have hzetaR : rowZeta τ (X r) ≤ 1 :=
    rowZeta_le_one hτ (hX.row_probability r)
  have hzetaS : rowZeta τ (X s) ≤ 1 :=
    rowZeta_le_one hτ (hX.row_probability s)
  have hzetaRpos : 0 < rowZeta τ (X r) :=
    rowZeta_pos (fun j ↦ (hXint r).2 j |>.1)
  have hzetaSpos : 0 < rowZeta τ (X s) :=
    rowZeta_pos (fun j ↦ (hXint s).2 j |>.1)
  have hlogNormalization :
      0 ≤ -Real.log (rowZeta τ (X r)) - Real.log (rowZeta τ (X s)) := by
    have hrlog : Real.log (rowZeta τ (X r)) ≤ 0 :=
      Real.log_nonpos hzetaRpos.le hzetaR
    have hslog : Real.log (rowZeta τ (X s)) ≤ 0 :=
      Real.log_nonpos hzetaSpos.le hzetaS
    linarith
  have hproductTerm :
      (∑ j, (1 - α j) * Real.log (1 - α j)) = 0 := by
    simp_rw [hαone]
    simp
  dsimp only [explicitPairWitnessLogGain, α, Ur, Us]
  rw [hproductTerm, hcertificate]
  linarith

/-- Every eligible explicit witness is a rigorous lower bound on the true
pair gain.  Only the log-sum certificate direction of capacity is used. -/
theorem explicitPairWitnessLogGain_le_log_pairGain_of_positiveLeakage
    {n : ℕ} {τ : ℝ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {rscale cscale : Fin n → ℝ}
    (hApos : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hrscale : ∀ i, 0 < rscale i) (hcscale : ∀ j, 0 < cscale j)
    (hKKT : HasMultiplicativeKKT τ A X rscale cscale)
    {r s a b : Fin n} (hrs : r ≠ s) (hab : a ≠ b)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b)
    (hρ1 : outsideMassTwo (pairAlpha X r s) a b ≤ 1) :
    explicitPairWitnessLogGain τ X r s a b ≤
      Real.log (pairGain A X r s) := by
  let α := pairAlpha X r s
  let Ur : Fin n → ℝ := fun j ↦ transferU τ (X r) j
  let Us : Fin n → ℝ := fun j ↦ transferU τ (X s) j
  let cap := polynomialCapacity α (pairPolynomial Ur Us)
  let prodFactor := ∏ j, (1 - α j) ^ (1 - α j)
  let scale := 1 / (rowZeta τ (X r) * rowZeta τ (X s))
  let θ := explicitPairWitness X r s a b
  let coeff := cleanWitnessCoefficient Ur Us a b
  have hfeasible := explicitPairWitness_isCapacityDistribution_of_positiveLeakage
    hX hrs hab hρ hρ1
  have hUr : ∀ j, 0 < Ur j := fun j ↦ transferU_pos (hXint r) j
  have hUs : ∀ j, 0 < Us j := fun j ↦ transferU_pos (hXint s) j
  have hcoeff : ∀ e, 0 < coeff e := by
    simpa only [coeff] using cleanWitnessCoefficient_positive hUr hUs a b
  have hcert : entropyCapacityCertificate θ coeff ≤ Real.log cap := by
    dsimp only [θ, coeff, cap, α, Ur, Us]
    exact cleanWitnessEntropyCertificate_le_log_pairPolynomialCapacity hab
      hfeasible.1.nonnegative hfeasible.1.sum_eq_one
      (by simpa only [coeff, Ur, Us] using hcoeff) hfeasible.2
      (fun j ↦ (hUr j).le) (fun j ↦ (hUs j).le)
  have hcard : 2 < Fintype.card (Fin n) :=
    two_lt_card_of_outsideMassTwo_pos hab hρ
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hαlt : ∀ j, α j < 1 := fun j ↦
    pairAlpha_lt_one_of_positive hX hXpos hcard hrs j
  have hcomp : ∀ j, 0 < 1 - α j := fun j ↦ sub_pos.mpr (hαlt j)
  have hprodPos : 0 < prodFactor := by
    dsimp only [prodFactor]
    exact Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hcomp j) _
  have hcapPos : 0 < cap := by
    dsimp only [cap, α, Ur, Us]
    exact pairTransferPolynomialCapacity_pos hX hXint hrs hab hρ hρ1
  have hzetaR : 0 < rowZeta τ (X r) :=
    rowZeta_pos (fun j ↦ (hXint r).2 j |>.1)
  have hzetaS : 0 < rowZeta τ (X s) :=
    rowZeta_pos (fun j ↦ (hXint s).2 j |>.1)
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact one_div_pos.mpr (mul_pos hzetaR hzetaS)
  have hfactor := pairGain_factorization hApos hX hXint
    hrscale hcscale hKKT r s
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
  rw [hlogFactor]
  dsimp only [explicitPairWitnessLogGain, α, Ur, Us, θ, coeff, scale]
  have hlogScale : Real.log
      (1 / (rowZeta τ (X r) * rowZeta τ (X s))) =
        -Real.log (rowZeta τ (X r)) - Real.log (rowZeta τ (X s)) := by
    rw [one_div, Real.log_inv, Real.log_mul hzetaR.ne' hzetaS.ne']
    ring
  rw [hlogScale]
  linarith

/-- The point-mass witness is also a rigorous lower bound in the exact
zero-leakage boundary case.  This branch is proved directly because the
complement factors are `0^0`, so a positivity argument through their
logarithms would be inappropriate. -/
theorem explicitPairWitnessLogGain_le_log_pairGain_of_zeroLeakage
    {n : ℕ} {τ : ℝ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {rscale cscale : Fin n → ℝ}
    (hApos : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hrscale : ∀ i, 0 < rscale i) (hcscale : ∀ j, 0 < cscale j)
    (hKKT : HasMultiplicativeKKT τ A X rscale cscale)
    {r s a b : Fin n} (hrs : r ≠ s) (hab : a ≠ b)
    (hzero : outsideMassTwo (pairAlpha X r s) a b = 0) :
    explicitPairWitnessLogGain τ X r s a b ≤
      Real.log (pairGain A X r s) := by
  let α := pairAlpha X r s
  let Ur : Fin n → ℝ := fun j ↦ transferU τ (X r) j
  let Us : Fin n → ℝ := fun j ↦ transferU τ (X s) j
  let cap := polynomialCapacity α (pairPolynomial Ur Us)
  let scale := 1 / (rowZeta τ (X r) * rowZeta τ (X s))
  letI : IsEmpty (OutsideColumn a b) :=
    isEmpty_outsideColumn_of_pairAlpha_outsideMass_eq_zero hX hXint hzero
  have hzeroWitness := cleanWitness_pairAlpha_zero hX hrs hab hzero
    (inferInstance : IsEmpty (OutsideColumn a b))
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
  have hθ : explicitPairWitness X r s a b =
      capacityWitnessMass 0 0 0 (fun l : OutsideColumn a b ↦ α l.1) := by
    simp only [explicitPairWitness]
    rw [show outsideMassTwo (pairAlpha X r s) a b = 0 from hzero]
    rw [show 1 - pairAlpha X r s a = 0 by
          simpa only [α] using sub_eq_zero.mpr ha.symm,
      show 1 - pairAlpha X r s b = 0 by
          simpa only [α] using sub_eq_zero.mpr hb.symm]
  have hUr : ∀ j, 0 < Ur j := fun j ↦ transferU_pos (hXint r) j
  have hUs : ∀ j, 0 < Us j := fun j ↦ transferU_pos (hXint s) j
  have hcoeff : ∀ e, 0 < cleanWitnessCoefficient Ur Us a b e :=
    cleanWitnessCoefficient_positive hUr hUs a b
  have hcert : entropyCapacityCertificate (explicitPairWitness X r s a b)
      (cleanWitnessCoefficient Ur Us a b) ≤ Real.log cap := by
    dsimp only [cap, α, Ur, Us]
    exact cleanWitnessEntropyCertificate_le_log_pairPolynomialCapacity hab
      (by simpa only [hθ] using hzeroWitness.1.1)
      (by simpa only [hθ] using hzeroWitness.1.2)
      (by simpa only [Ur, Us] using hcoeff)
      (by simpa only [hθ] using hzeroWitness.2)
      (fun j ↦ (hUr j).le) (fun j ↦ (hUs j).le)
  have hexp := exp_entropyCapacityCertificate_le_finitePolynomialCapacity
    hzeroWitness.1.1 hzeroWitness.1.2 hcoeff hzeroWitness.2
  have hcapFinite := cleanWitnessCapacity_le_pairPolynomialCapacity hab
    (u := Ur) (v := Us) (α := α)
    (fun j ↦ (hUr j).le) (fun j ↦ (hUs j).le)
  have hcapPos : 0 < cap := by
    dsimp only [cap]
    exact (Real.exp_pos _).trans_le (hexp.trans hcapFinite)
  have hzetaR : 0 < rowZeta τ (X r) :=
    rowZeta_pos (fun j ↦ (hXint r).2 j |>.1)
  have hzetaS : 0 < rowZeta τ (X s) :=
    rowZeta_pos (fun j ↦ (hXint s).2 j |>.1)
  have hscalePos : 0 < scale := by
    dsimp only [scale]
    exact one_div_pos.mpr (mul_pos hzetaR hzetaS)
  have hfactor := pairGain_factorization hApos hX hXint
    hrscale hcscale hKKT r s
  have hgainEq : pairGain A X r s = scale * cap := by
    rw [hfactor]
    simp_rw [show ∀ j, pairAlpha X r s j = 1 by
      simpa only [α] using hαone]
    simp [scale, cap, α, Ur, Us]
  have hlogGain : Real.log (pairGain A X r s) =
      Real.log scale + Real.log cap := by
    rw [hgainEq, Real.log_mul hscalePos.ne' hcapPos.ne']
  have hlogScale : Real.log scale =
      -Real.log (rowZeta τ (X r)) - Real.log (rowZeta τ (X s)) := by
    dsimp only [scale]
    rw [one_div, Real.log_inv, Real.log_mul hzetaR.ne' hzetaS.ne']
    ring
  have hproductTerm :
      (∑ j, (1 - α j) * Real.log (1 - α j)) = 0 := by
    simp_rw [hαone]
    simp
  rw [hlogGain, hlogScale]
  dsimp only [explicitPairWitnessLogGain, α, Ur, Us]
  rw [hproductTerm]
  linarith

/-- Unified algorithm-facing form: the sole numerical eligibility test is
that the rational outside mass is at most one.  Nonnegativity is automatic
from double stochasticity, and exact zero is dispatched to the point-mass
branch. -/
theorem explicitPairWitnessLogGain_le_log_pairGain_of_le_one
    {n : ℕ} {τ : ℝ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {rscale cscale : Fin n → ℝ}
    (hApos : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hrscale : ∀ i, 0 < rscale i) (hcscale : ∀ j, 0 < cscale j)
    (hKKT : HasMultiplicativeKKT τ A X rscale cscale)
    {r s a b : Fin n} (hrs : r ≠ s) (hab : a ≠ b)
    (hρ1 : outsideMassTwo (pairAlpha X r s) a b ≤ 1) :
    explicitPairWitnessLogGain τ X r s a b ≤
      Real.log (pairGain A X r s) := by
  have hρnonneg : 0 ≤ outsideMassTwo (pairAlpha X r s) a b := by
    dsimp only [outsideMassTwo]
    exact Finset.sum_nonneg fun j _ ↦ pairAlpha_nonneg hX r s j
  rcases hρnonneg.eq_or_lt with hzero | hpos
  · exact explicitPairWitnessLogGain_le_log_pairGain_of_zeroLeakage
      hApos hX hXint hrscale hcscale hKKT hrs hab hzero.symm
  · exact explicitPairWitnessLogGain_le_log_pairGain_of_positiveLeakage
      hApos hX hXint hrscale hcscale hKKT hrs hab hpos hρ1

end BeyondBethe
