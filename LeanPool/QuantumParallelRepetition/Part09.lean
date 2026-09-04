/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part08

/-! # Quantum parallel repetition, part 09 -/

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part nine. -/
noncomputable local instance matrixComplexContinuousENormPartNine
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem gameQuestionX_nonempty
    (G : Game X Y A B) : Nonempty X := by
  classical
  by_contra empty
  have zero : (∑ x : X, ∑ y : Y, G.questionWeight x y) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact (empty ⟨x⟩).elim
  linarith [G.weight_normalized]

theorem gameQuestionY_nonempty
    (G : Game X Y A B) : Nonempty Y := by
  classical
  by_contra empty
  have zero : (∑ x : X, ∑ y : Y, G.questionWeight x y) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    exact (empty ⟨y⟩).elim
  linarith [G.weight_normalized]

theorem exact_source_equation_twenty_three
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    ExactSourceClassicalInformationBound G n S D base := by
  classical
  exact exact_source_equation_twenty_three_unconditional
    G n S D remaining positive base
    (Classical.choice (gameQuestionY_nonempty G))
    (Classical.choice (gameQuestionX_nonempty G))

theorem
    exact_source_equation_twenty_seven_support_preserving_unconditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base (exactSourcePinskerRate G n S D) gamma := by
  exact
    exact_source_equation_twenty_seven_support_preserving_of_information
      G n S D remaining positive base
      (exact_source_equation_twenty_three
        G n S D remaining positive base)
      gamma_positive

end

section

open Filter
open scoped Topology

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The one-coordinate strategy and error data extracted from an exact source. -/
def ExactSourceOneGameRounding
    (G : Game X Y A B) : Prop :=
  ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (n : ℕ) (S : Strategy (G.repeat n))
      (D : Finset (Fin n)),
      0 < (Finset.univ \ D).card →
      0 < repeatedPostselectionMass G n S D →
      ∀ (α gamma : ℝ),
        0 < α → α ≤ 1 → 0 < gamma →
        uniformRemainingFailure
            (strategyEventLaw (G.repeat n) S)
            (repeatedCoordinateWin G n) D <
          (1 - entangledValue G) / 2 →
        ∃ rounded : Strategy G,
          roundedWinningLowerBound (1 - entangledValue G)
              K₀ α (martingaleRate G n S D)
              (exactSourcePinskerRate G n S D + gamma) ≤
            rounded.winProbability

theorem exact_totalSamplingLoss_mono
    {K₀ α₁ α₂ η₁ η₂ lam₁ lam₂ : ℝ}
    (constant_nonnegative : 0 ≤ K₀)
    (alpha_nonnegative : 0 ≤ α₁)
    (alpha_le : α₁ ≤ α₂)
    (eta_nonnegative : 0 ≤ η₁)
    (eta_le : η₁ ≤ η₂)
    (lam_le : lam₁ ≤ lam₂) :
    totalSamplingLoss K₀ α₁ η₁ lam₁ ≤
      totalSamplingLoss K₀ α₂ η₂ lam₂ := by
  have ceiling_nonnegative : 0 ≤ universalErrorCeiling K₀ := by
    unfold universalErrorCeiling
    positivity
  have alpha_root :
      α₁ ^ (1 / 12 : ℝ) ≤ α₂ ^ (1 / 12 : ℝ) :=
    Real.rpow_le_rpow alpha_nonnegative alpha_le (by norm_num)
  have eta_root :
      (32 * η₁) ^ (1 / 12 : ℝ) ≤
        (32 * η₂) ^ (1 / 12 : ℝ) := by
    apply Real.rpow_le_rpow
    · positivity
    · linarith
    · norm_num
  have eta_sqrt :
      Real.sqrt (8 * η₁) ≤ Real.sqrt (8 * η₂) := by
    apply Real.sqrt_le_sqrt
    linarith
  unfold totalSamplingLoss
  gcongr

theorem exact_standardQuantumParallelRepetition_of_source_rounding
    (G : Game X Y A B)
    (rounding : ExactSourceOneGameRounding G) :
    StandardQuantumParallelRepetition G := by
  intro gap
  by_contra no_exponential_bound
  have witness : HasSubexponentialWitness (repeatedEntangledValue G) :=
    (not_hasExponentialBound_iff (repeatedEntangledValue G)).mp
      no_exponential_bound
  obtain ⟨K₀, constant_nonnegative, construct⟩ := rounding
  let gapValue : ℝ := 1 - entangledValue G
  have gap_positive : 0 < gapValue := by
    dsimp [gapValue]
    linarith
  let failureTolerance : ℝ := min (gapValue / 2) (1 / 2)
  have failure_positive : 0 < failureTolerance := by
    dsimp [failureTolerance]
    exact lt_min (by positivity) (by norm_num)
  have failure_at_most_one : failureTolerance ≤ 1 := by
    have half := min_le_right (gapValue / 2) (1 / 2 : ℝ)
    dsimp [failureTolerance]
    linarith
  let rate : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have rate_positive (k : ℕ) : 0 < rate k := by
    dsimp [rate]
    positivity
  have rate_at_most_one (k : ℕ) : rate k ≤ 1 := by
    dsimp [rate]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
    have nonnegative : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  have rate_tendsto : Tendsto rate atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have martingale_tendsto :
      Tendsto (fun k => rate k ^ 2 / 8) atTop (𝓝 0) := by
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div] using (rate_tendsto.pow 2).div_const (8 : ℝ)
  have sampling_tendsto :
      Tendsto (fun k => rate k / 2 + rate k) atTop (𝓝 0) := by
    simpa only [zero_div, add_zero] using (rate_tendsto.div_const (2 : ℝ)).add rate_tendsto
  have eventually_small :
      ∀ᶠ k : ℕ in atTop,
        totalSamplingLoss K₀ (rate k)
            (rate k ^ 2 / 8) (rate k / 2 + rate k) <
          gapValue / 2 :=
    totalSamplingLoss_eventually_lt K₀
      rate_tendsto martingale_tendsto sampling_tendsto
      (by positivity)
  obtain ⟨k, loss_small⟩ := eventually_small.exists
  obtain ⟨n, _, S, D, _, postselection_positive,
      remaining_positive, failure_small, martingale_small,
      pinsker_small⟩ :=
    exact_arbitrarily_large_conditioning_of_subexponentialWitness
      G witness failure_positive failure_at_most_one
      (rate_positive k) 0
  have failure_gap :
      uniformRemainingFailure
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D < gapValue / 2 :=
    lt_of_lt_of_le failure_small
      (min_le_left (gapValue / 2) (1 / 2 : ℝ))
  obtain ⟨rounded, rounded_bound⟩ :=
    construct n S D remaining_positive postselection_positive
      (rate k) (rate k)
      (rate_positive k) (rate_at_most_one k)
      (rate_positive k) (by simpa only [gapValue] using failure_gap)
  have martingale_nonnegative :=
    martingaleRate_nonneg G n S D
      remaining_positive postselection_positive
  have exact_loss_small :
      totalSamplingLoss K₀ (rate k)
          (martingaleRate G n S D)
          (exactSourcePinskerRate G n S D + rate k) <
        gapValue / 2 := by
    refine lt_of_le_of_lt ?_ loss_small
    apply exact_totalSamplingLoss_mono
      constant_nonnegative (rate_positive k).le (le_refl _)
      martingale_nonnegative martingale_small
    linarith
  exact source_equation_twenty_nine_contradiction G rounded
    K₀ (rate k) (martingaleRate G n S D)
    (exactSourcePinskerRate G n S D + rate k)
    rounded_bound (by simpa only [gapValue] using exact_loss_small)

end

section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The positive operator-valued measurement implementing unitary conjugate. -/
def unitaryConjugatePOVM
    {C d : Type} [Fintype C] [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (P : POVM C d) : POVM C d where
  effect c :=
    (U : Matrix d d ℂ)ᴴ * P.effect c * (U : Matrix d d ℂ)
  positive c := by
    have positive :=
      (P.positive c).mul_mul_conjTranspose_same
        ((U : Matrix d d ℂ)ᴴ)
    simpa only [conjTranspose_conjTranspose] using positive
  complete := by
    classical
    have unitary :
        (U : Matrix d d ℂ)ᴴ * (U : Matrix d d ℂ) = 1 := by
      simpa only [star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff').mp U.property
    calc
      (∑ c : C,
        (U : Matrix d d ℂ)ᴴ * P.effect c * (U : Matrix d d ℂ)) =
          (U : Matrix d d ℂ)ᴴ *
            (∑ c : C, P.effect c) *
            (U : Matrix d d ℂ) := by
              simp only [mul_sum, sum_mul]
      _ = 1 := by rw [P.complete, Matrix.mul_one, unitary]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

theorem residualIdentity_quadratic
    {s t : Type} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (M : Matrix s s ℂ)
    (z : EuclideanSpace ℂ s)
    (κ : EuclideanSpace ℂ t)
    (normalized : ‖κ‖ = 1) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (M ⊗ₖ (1 : Matrix t t ℂ)))
      (toLp 2 (fun q : s × t => z q.1 * κ q.2)) =
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s) (𝕜 := ℂ) M) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  have residual_square :
      (∑ j : t, ‖κ j‖ ^ 2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, normalized]
    norm_num
  have residual_complex :
      (∑ j : t, κ j * star (κ j)) = 1 := by
    calc
      (∑ j : t, κ j * star (κ j)) =
          (↑(∑ j : t, ‖κ j‖ ^ 2) : ℂ) := by
            push_cast
            apply Finset.sum_congr rfl
            intro j _
            simpa only [RCLike.star_def, normSq_eq_norm_sq, ofReal_pow] using
              Complex.mul_conj (κ j)
      _ = 1 := by rw [residual_square]; norm_num
  congr 1
  change
    (∑ i : s × t,
      (∑ j : s × t,
        (M i.1 j.1 * (if i.2 = j.2 then 1 else 0)) *
          (z j.1 * κ j.2)) *
        star (z i.1 * κ i.2)) =
      ∑ i : s, (∑ j : s, M i j * z j) * star (z i)
  rw [Fintype.sum_prod_type]
  calc
    (∑ i : s, ∑ k : t,
      (∑ j : s × t,
        (M i j.1 * (if k = j.2 then 1 else 0)) *
          (z j.1 * κ j.2)) *
        star (z i * κ k)) =
      ∑ i : s, ∑ k : t,
        ((∑ j : s, M i j * z j) * κ k) *
          star (z i * κ k) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            rw [Fintype.sum_prod_type]
            simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ,
              ↓reduceIte, sum_mul, mul_assoc]
    _ = ∑ i : s,
      ((∑ j : s, M i j * z j) * star (z i)) *
        (∑ k : t, κ k * star (κ k)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          simp only [star_mul]
          ring
    _ = ∑ i : s, (∑ j : s, M i j * z j) * star (z i) := by
          rw [residual_complex]
          simp only [RCLike.star_def, mul_one]

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactSourceGlobalCatalystWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (exactSourceGlobalCatalystAlicePOVM
        G n S D e a₀ x).effect a ⊗ₖ
      (exactSourceGlobalCatalystBobPOVM
        G n S D e b₀ y).effect b
    else 0

private def exactSourceGlobalCatalystBasisEquiv
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) :
    ((ExactGlobalHistoryLocalIndex G n S D ×
       ExactGlobalHistoryLocalIndex G n S D) ×
      (Fin e × Fin e)) ≃
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  let localEquiv :
      (ExactGlobalHistoryLocalIndex G n S D × Fin e) ≃
        Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D) * e) :=
    (Equiv.prodCongr
      (Fintype.equivFin
        (ExactGlobalHistoryLocalIndex G n S D))
      (Equiv.refl (Fin e))).trans finProdFinEquiv
  exact
    (Equiv.prodProdProdComm
      (ExactGlobalHistoryLocalIndex G n S D)
      (ExactGlobalHistoryLocalIndex G n S D)
      (Fin e) (Fin e)).trans (Equiv.prodCongr localEquiv localEquiv)

@[simp] theorem exactSourceGlobalCatalystAlicePOVM_effect_global
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (a₀ a : A) (x : X)
    (i j : ExactGlobalHistoryLocalIndex G n S D)
    (k l : Fin e) :
    (exactSourceGlobalCatalystAlicePOVM
      G n S D e a₀ x).effect a
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) i, k))
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) j, l)) =
      (exactSourceGlobalAlicePOVM
        G n S D a₀ x).effect a i j *
        (if k = l then 1 else 0) := by
  classical
  change
    (reindexedPOVM finProdFinEquiv
      (purificationAlicePOVM (k := Fin e)
        (reindexedPOVM
          (Fintype.equivFin
            (ExactGlobalHistoryLocalIndex G n S D))
          (exactSourceGlobalAlicePOVM G n S D a₀ x)))).effect a
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) i, k))
      (finProdFinEquiv
        ((Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D)) j, l)) = _
  exact reindexedCatalystPOVM_effect
    (exactSourceGlobalAlicePOVM G n S D a₀ x)
    e a i j k l

theorem exactSourceGlobalCatalystWinningEffect_compression
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (i j :
      (ExactGlobalHistoryLocalIndex G n S D ×
       ExactGlobalHistoryLocalIndex G n S D) ×
      (Fin e × Fin e)) :
    exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y
      (exactSourceGlobalCatalystBasisEquiv G n S D e i)
      (exactSourceGlobalCatalystBasisEquiv G n S D e j) =
      ((exactSourceGlobalWinningEffect G n S D a₀ b₀ x y) ⊗ₖ
        (1 : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ)) i j := by
  classical
  rcases i with ⟨⟨ia, ib⟩, ⟨ka, kb⟩⟩
  rcases j with ⟨⟨ja, jb⟩, ⟨la, lb⟩⟩
  by_cases alice_residual : ka = la
  · subst la
    by_cases bob_residual : kb = lb
    · subst lb
      simp only [exactSourceGlobalCatalystWinningEffect,
        exactSourceGlobalWinningEffect, Matrix.sum_apply,
        Matrix.kroneckerMap_apply,
        exactSourceGlobalCatalystBasisEquiv,
        Equiv.trans_apply, Equiv.prodCongr_apply,
        Equiv.prodProdProdComm_apply, Matrix.one_apply,
        ite_true, mul_one]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      split_ifs with winning
      · simp only [Equiv.coe_trans, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply,
          Function.comp_apply, id_eq, kroneckerMap_apply,
          exactSourceGlobalCatalystAlicePOVM_effect_global, ↓reduceIte, mul_one,
          exactSourceGlobalCatalystBobPOVM_effect]
      · rfl
    · simp only [exactSourceGlobalCatalystWinningEffect, exactSourceGlobalCatalystBasisEquiv,
        Equiv.trans_apply, Equiv.prodProdProdComm_apply, Equiv.prodCongr_apply, Equiv.coe_trans,
        Equiv.coe_refl, Prod.map_apply, Function.comp_apply, id_eq, Matrix.sum_apply,
        exactSourceGlobalWinningEffect, kroneckerMap_apply, ne_eq, Prod.mk.injEq, bob_residual,
        and_false, not_false_eq_true, one_apply_ne, mul_zero]
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with winning
      · simp only [kroneckerMap_apply, exactSourceGlobalCatalystAlicePOVM_effect_global,
          ↓reduceIte, mul_one, exactSourceGlobalCatalystBobPOVM_effect, bob_residual, mul_zero]
      · rfl
  · simp only [exactSourceGlobalCatalystWinningEffect, exactSourceGlobalCatalystBasisEquiv,
      Equiv.trans_apply, Equiv.prodProdProdComm_apply, Equiv.prodCongr_apply, Equiv.coe_trans,
      Equiv.coe_refl, Prod.map_apply, Function.comp_apply, id_eq, Matrix.sum_apply,
      exactSourceGlobalWinningEffect, kroneckerMap_apply, ne_eq, Prod.mk.injEq, alice_residual,
      false_and, not_false_eq_true, one_apply_ne, mul_zero]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs with winning
    · simp only [kroneckerMap_apply, exactSourceGlobalCatalystAlicePOVM_effect_global,
        alice_residual, ↓reduceIte, mul_zero, exactSourceGlobalCatalystBobPOVM_effect, mul_ite,
        mul_one, zero_mul, ite_self]
    · rfl

theorem exactSourceGlobalCatalystWinningEffect_tensor_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (exactSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y))
      (tensorEmbezzlementTarget (n := e)
        (exactGlobalHistoryFinPsi G n S D r x y)) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          ExactGlobalHistoryLocalIndex G n S D ×
          ExactGlobalHistoryLocalIndex G n S D)
        (𝕜 := ℂ)
        (exactSourceGlobalWinningEffect
          G n S D a₀ b₀ x y))
      (exactGlobalHistoryVector G n S D r
        (exactPsi G n S D r x y)) := by
  classical
  let source := exactGlobalHistoryVector G n S D r
    (exactPsi G n S D r x y)
  let residual := embezzlementState e
  let tensor : EuclideanSpace ℂ
      ((ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ×
       (Fin e × Fin e)) :=
    toLp 2 (fun q => source q.1 * residual q.2)
  let basis := exactSourceGlobalCatalystBasisEquiv G n S D e
  calc
    _ = quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (ExactGlobalHistoryLocalIndex G n S D ×
            ExactGlobalHistoryLocalIndex G n S D) ×
          (Fin e × Fin e))
        (𝕜 := ℂ)
        ((exactSourceGlobalWinningEffect
          G n S D a₀ b₀ x y) ⊗ₖ
          (1 : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ)))
      tensor := by
        apply matrixQuadraticExpectation_injective
          basis basis.injective
        · intro i
          rcases i with ⟨⟨ia, ib⟩, ⟨ka, kb⟩⟩
          have alice_system :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ia, ka)).divNat =
                (Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia := by
            exact congrArg Prod.fst
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia, ka))
          have alice_residual :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ia, ka)).modNat = ka := by
            exact congrArg Prod.snd
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ia, ka))
          have bob_system :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ib, kb)).divNat =
                (Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib := by
            exact congrArg Prod.fst
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib, kb))
          have bob_residual :
              (finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D))
                  ib, kb)).modNat = kb := by
            exact congrArg Prod.snd
              (Equiv.symm_apply_apply finProdFinEquiv
                ((Fintype.equivFin
                  (ExactGlobalHistoryLocalIndex G n S D)) ib, kb))
          simp only [exactSourceGlobalCatalystBasisEquiv, Equiv.trans_apply,
            tensorEmbezzlementTarget, exactGlobalHistoryFinPsi, exactGlobalHistoryFinReindex,
            LinearIsometryEquiv.piLpCongrLeft_apply, finProdFinEquiv_symm_apply,
            Equiv.piCongrLeft'_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
            Equiv.prodProdProdComm_apply, Equiv.coe_trans, Equiv.coe_refl, Function.comp_apply,
            id_eq, alice_system, Equiv.symm_apply_apply, bob_system, alice_residual, bob_residual,
            basis, source, residual, tensor]
        · intro j outside
          exact False.elim
            (outside (basis.symm j) (basis.apply_symm_apply j))
        · exact exactSourceGlobalCatalystWinningEffect_compression
            G n S D e a₀ b₀ x y
    _ = _ := residualIdentity_quadratic
      (exactSourceGlobalWinningEffect G n S D a₀ b₀ x y)
      source residual
      (embezzlementState_norm e residual_positive)

theorem exactPsi_eq_padded_normalizedPureVector_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y)
    (nonzero : exactUnnormalizedPsi G n S D r x y ≠ 0) :
    exactPsi G n S D r x y =
      exactPaddedVector G n S D r
        (normalizedPureVector
          (exactUnnormalizedPsi G n S D r x y)) := by
  classical
  let raw := exactUnnormalizedPsi G n S D r x y
  have padded_nonzero :
      exactPaddedVector G n S D r raw ≠ 0 := by
    intro zero
    apply nonzero
    apply norm_eq_zero.mp
    rw [← exactPaddedVector_norm G n S D r raw, zero]
    exact norm_zero
  unfold exactPsi normalizeOrDefault
  rw [ite_eq_right padded_nonzero, NormedSpace.normalize,
    exactPaddedVector_norm]
  ext q
  rcases q with ⟨i, j⟩
  rcases i with i | (i | i) <;>
    rcases j with j | (j | j) <;>
    simp only [exactPaddedVector, normalizedPureVector, PiLp.smul_apply,
      smul_zero, smul_eq_mul, Complex.real_smul]

theorem exactSourceGlobalCatalystWinningEffect_law_supported_verifier
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B)
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactSourceConditionalWinningProbability G n S D t =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e) ×
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e))
          (𝕜 := ℂ)
          (exactSourceGlobalCatalystWinningEffect
            G n S D e a₀ b₀ t.2.1 t.2.2.1))
        (tensorEmbezzlementTarget (n := e)
          (exactGlobalHistoryFinPsi G n S D t.2.2.2
            t.2.1 t.2.2.1)) := by
  classical
  have coordinate :=
    exactLocallySampleableLaw_coordinate_eq_of_ne_zero
      G n S D t supported
  have accepted :=
    exactLocallySampleableLaw_accepted_of_ne_zero
      G n S D t supported
  have fiber :=
    exactLocallySampleableLaw_fiber_ne_zero_of_ne_zero
      G n S D t supported
  have raw_nonzero :=
    exactLocallySampleableLaw_psi_ne_zero_of_ne_zero
      G n S D t supported
  rw [exactSourceGlobalCatalystWinningEffect_tensor_quadratic
    G n S D t.2.2.2 e residual_positive a₀ b₀ t.2.1 t.2.2.1]
  rw [exactPsi_eq_padded_normalizedPureVector_of_ne_zero
    G n S D t.2.2.2 t.2.1 t.2.2.1 raw_nonzero]
  rw [exactSourceGlobalWinningEffect_quadratic
    G n S D t.2.2.2 a₀ b₀ t.2.1 t.2.2.1]
  have tuple :
      t = (t.2.2.2.seed.coordinate,
        t.2.1, t.2.2.1, t.2.2.2) := by
    rcases t with ⟨i, x, y, r⟩
    simpa only [Prod.mk.injEq, and_true] using coordinate
  conv_lhs => rw [tuple]
  exact
    exactSourceConditionalWinningProbability_eq_normalized_verifier
      G n S D positive t.2.2.2 accepted a₀ b₀
      t.2.1 t.2.2.1 fiber

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/--
The unconditional matched verifier tensor construction used in the quantum parallel-repetition
argument.
-/
def unconditionalMatchedVerifierTensor
    {s t : Type*}
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    EuclideanSpace ℂ (s × t) :=
  toLp 2 (fun q : s × t => target q.1 * work q.2)

theorem unconditionalMatchedVerifierTensor_norm_sq
    {s t : Type*} [Fintype s] [Fintype t]
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    ‖unconditionalMatchedVerifierTensor target work‖ ^ 2 =
      ‖target‖ ^ 2 * ‖work‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  change
    (∑ i : s, ∑ j : t, ‖target i * work j‖ ^ 2) =
      ‖target‖ ^ 2 * ‖work‖ ^ 2
  simp_rw [norm_mul, mul_pow]
  rw [← Fintype.sum_mul_sum, ← EuclideanSpace.norm_sq_eq,
    ← EuclideanSpace.norm_sq_eq]

theorem unconditionalMatchedVerifierTensor_norm
    {s t : Type*} [Fintype s] [Fintype t]
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    ‖unconditionalMatchedVerifierTensor target work‖ =
      ‖target‖ * ‖work‖ := by
  have squared :=
    unconditionalMatchedVerifierTensor_norm_sq target work
  nlinarith [
    norm_nonneg (unconditionalMatchedVerifierTensor target work),
    norm_nonneg target, norm_nonneg work,
    mul_nonneg (norm_nonneg target) (norm_nonneg work)]

theorem unconditionalMatchedVerifierEffect_tensor_complement
    {s t : Type*} [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ) :
    (1 : Matrix (s × t) (s × t) ℂ) -
        (effect ⊗ₖ (1 : Matrix t t ℂ)) =
      (1 - effect) ⊗ₖ (1 : Matrix t t ℂ) := by
  classical
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases same_target : i = j
  · subst j
    by_cases same_work : k = l
    · subst l
      simp only [Matrix.sub_apply, one_apply_eq, kroneckerMap_apply, mul_one]
    · simp only [Matrix.sub_apply, ne_eq, Prod.mk.injEq, same_work, and_false, not_false_eq_true,
        one_apply_ne, kroneckerMap_apply, mul_zero, sub_self, one_apply_eq]
  · by_cases same_work : k = l
    · subst l
      simp only [Matrix.sub_apply, ne_eq, Prod.mk.injEq, same_target, and_true, not_false_eq_true,
        one_apply_ne, kroneckerMap_apply, one_apply_eq, mul_one, zero_sub]
    · simp only [Matrix.sub_apply, ne_eq, Prod.mk.injEq, same_target, same_work, and_self,
        not_false_eq_true, one_apply_ne, kroneckerMap_apply, mul_zero, sub_self, zero_sub]

theorem unconditionalMatchedVerifierEffect_tensor_posSemidef
    {s t : Type*} [Finite s] [Finite t] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (positive : effect.PosSemidef) :
    (effect ⊗ₖ (1 : Matrix t t ℂ)).PosSemidef :=
  positive.kronecker Matrix.PosSemidef.one

theorem unconditionalMatchedVerifierEffect_tensor_complement_posSemidef
    {s t : Type*} [Finite s] [Finite t] [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (complement : (1 - effect).PosSemidef) :
    ((1 : Matrix (s × t) (s × t) ℂ) -
      (effect ⊗ₖ (1 : Matrix t t ℂ))).PosSemidef := by
  rw [unconditionalMatchedVerifierEffect_tensor_complement]
  exact complement.kronecker Matrix.PosSemidef.one

theorem unconditionalMatchedVerifierEffect_tensor_norm_le_one
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (positive : effect.PosSemidef)
    (complement : (1 - effect).PosSemidef) :
    ‖Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (effect ⊗ₖ (1 : Matrix t t ℂ))‖ ≤ 1 := by
  exact matrixEffectCLM_norm_le_one
    (effect ⊗ₖ (1 : Matrix t t ℂ))
    (unconditionalMatchedVerifierEffect_tensor_posSemidef
      effect positive)
    (unconditionalMatchedVerifierEffect_tensor_complement_posSemidef
      effect complement)

theorem unconditionalMatchedVerifierEffect_tensor_quadratic
    {s t : Type*} [Fintype s] [Fintype t]
    [DecidableEq s] [DecidableEq t]
    (effect : Matrix s s ℂ)
    (target : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := s × t) (𝕜 := ℂ)
        (effect ⊗ₖ (1 : Matrix t t ℂ)))
      (unconditionalMatchedVerifierTensor target work) =
      ‖work‖ ^ 2 *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := s) (𝕜 := ℂ) effect)
          target := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  have residual_complex :
      (∑ k : t, work k * star (work k)) =
        (↑(‖work‖ ^ 2) : ℂ) := by
    calc
      (∑ k : t, work k * star (work k)) =
          (↑(∑ k : t, ‖work k‖ ^ 2) : ℂ) := by
            push_cast
            apply Finset.sum_congr rfl
            intro k _
            simpa only [RCLike.star_def, normSq_eq_norm_sq, ofReal_pow] using
              Complex.mul_conj (work k)
      _ = (↑(‖work‖ ^ 2) : ℂ) := by
            rw [← EuclideanSpace.norm_sq_eq]
  change
    (∑ i : s × t,
      (∑ j : s × t,
        (effect i.1 j.1 * (if i.2 = j.2 then 1 else 0)) *
          (target j.1 * work j.2)) *
        star (target i.1 * work i.2)).re =
      ‖work‖ ^ 2 *
        (∑ i : s, (∑ j : s, effect i j * target j) *
          star (target i)).re
  rw [Fintype.sum_prod_type]
  have complex_factor :
      (∑ i : s, ∑ k : t,
        (∑ j : s × t,
          (effect i j.1 * (if k = j.2 then 1 else 0)) *
            (target j.1 * work j.2)) *
          star (target i * work k)) =
        (∑ i : s,
          (∑ j : s, effect i j * target j) * star (target i)) *
          (↑(‖work‖ ^ 2) : ℂ) := by
    calc
      (∑ i : s, ∑ k : t,
        (∑ j : s × t,
          (effect i j.1 * (if k = j.2 then 1 else 0)) *
            (target j.1 * work j.2)) *
          star (target i * work k)) =
        ∑ i : s, ∑ k : t,
          ((∑ j : s, effect i j * target j) * work k) *
            star (target i * work k) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro k _
              congr 1
              rw [Fintype.sum_prod_type]
              simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ,
                ↓reduceIte, sum_mul, mul_assoc]
      _ = ∑ i : s,
        ((∑ j : s, effect i j * target j) * star (target i)) *
          (∑ k : t, work k * star (work k)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            simp only [star_mul]
            ring
      _ = (∑ i : s,
          (∑ j : s, effect i j * target j) * star (target i)) *
          (↑(‖work‖ ^ 2) : ℂ) := by
            rw [residual_complex, Finset.sum_mul]
  rw [complex_factor, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/--
The type used to represent unconditional selected copy local index in the exact sampling
construction.
-/
abbrev UnconditionalSelectedCopyLocalIndex
    (B d N m : ℕ) :=
  Σ _ : Fin B × Fin d, Fin (N * m)

private def unconditionalSelectedCopyCleanedStage
    {d N B m : ℕ}
    (Q : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
    Q w ξ ζ A C
    (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
      (N := N) (B := B) w m ξ ζ)

private def unconditionalSelectedCopyIdealStage
    {d N B m : ℕ}
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  dSVDensityRationalPublicBucketPhysicalCoherentTargetState
    (N := N) (B := B) w m ξ ζ

private def unconditionalSelectedCopyRetainedWork
    {S N d L : ℕ} {τ : Type*}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) × τ) :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
      (N := N) width schedule ξ ζ j)
    rest

/--
The unconditional selected copy cleaned matched branch construction used in the quantum
parallel-repetition argument.
-/
def unconditionalSelectedCopyCleanedMatchedBranch
    {S N d L B m : ℕ} {τ : Type*}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalSelectedCopyLocalIndex B d N m) ×
        ((Fin j.val →
          (DSVUniformDensityThresholdLocalIndex N d ×
            DSVUniformDensityThresholdLocalIndex N d)) × τ)) :=
  unconditionalMatchedVerifierTensor
    (unconditionalSelectedCopyCleanedStage
      (N := N) (B := B) (m := m)
      Q (width (schedule j)) ξ ζ A C)
    (unconditionalSelectedCopyRetainedWork
      (N := N) width schedule ξ ζ j rest)

private def unconditionalSelectedCopyIdealMatchedBranch
    {S N d L B m : ℕ} {τ : Type*}
    (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalSelectedCopyLocalIndex B d N m) ×
        ((Fin j.val →
          (DSVUniformDensityThresholdLocalIndex N d ×
            DSVUniformDensityThresholdLocalIndex N d)) × τ)) :=
  unconditionalMatchedVerifierTensor
    (unconditionalSelectedCopyIdealStage
      (N := N) (B := B) (m := m) (width (schedule j)) ξ ζ)
    (unconditionalSelectedCopyRetainedWork
      (N := N) width schedule ξ ζ j rest)

theorem unconditionalSelectedCopy_tensor_sub
    {s τ : Type*}
    (x y : EuclideanSpace ℂ s) (work : EuclideanSpace ℂ τ) :
    unconditionalMatchedVerifierTensor x work -
        unconditionalMatchedVerifierTensor y work =
      unconditionalMatchedVerifierTensor (x - y) work := by
  ext ⟨i, j⟩
  change x i * work j - y i * work j =
    (x i - y i) * work j
  ring

theorem unconditionalSelectedCopyRetainedWork_norm_sq
    {S N d L : ℕ} {τ : Type*} [Fintype τ]
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ) :
    ‖unconditionalSelectedCopyRetainedWork
        (N := N) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ j.val * ‖rest‖ ^ 2 := by
  unfold unconditionalSelectedCopyRetainedWork
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq]

theorem unconditionalSelectedCopyMatchedBranch_deviation_sq
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyCleanedMatchedBranch
          Q width schedule ξ ζ A C j rest -
        unconditionalSelectedCopyIdealMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
          Q (width (schedule j)) m ξ ζ A C := by
  unfold unconditionalSelectedCopyCleanedMatchedBranch
    unconditionalSelectedCopyIdealMatchedBranch
  rw [unconditionalSelectedCopy_tensor_sub,
    unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  unfold dSVDensityRationalHeterogeneousCommonStopGaugeStageError
    unconditionalSelectedCopyCleanedStage
    unconditionalSelectedCopyIdealStage
  ring

theorem unconditionalSelectedCopy_weightedAffine
    {ι : Type*} [Fintype ι]
    (weight error asynchronous : ι → ℝ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i, weight i) = 1)
    (coefficient residual : ℝ)
    (pointwise : ∀ i, error i ≤ coefficient * asynchronous i + residual) :
    (∑ i, weight i * error i) ≤
      coefficient * (∑ i, weight i * asynchronous i) + residual := by
  classical
  calc
    (∑ i, weight i * error i) ≤
        ∑ i, weight i *
          (coefficient * asynchronous i + residual) := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left
              (pointwise i) (nonnegative i)
    _ = coefficient * (∑ i, weight i * asynchronous i) +
          (∑ i, weight i) * residual := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib,
              Finset.mul_sum, Finset.sum_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = coefficient * (∑ i, weight i * asynchronous i) + residual := by
          rw [normalized]
          ring

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalMatchedVerifierAggregate_dependent_continuity
    {J : Type*} [Fintype J]
    {H : J → Type*}
    [∀ j, NormedAddCommGroup (H j)]
    [∀ j, InnerProductSpace ℂ (H j)]
    (weight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ weight j)
    (effect : (j : J) → (H j →L[ℂ] H j))
    (contraction : ∀ j, ‖effect j‖ ≤ 1)
    (actual ideal : (j : J) → H j) :
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
      (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      (Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2)) *
        Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) := by
  classical
  have point (j : J) :
      |quadraticExpectation (effect j) (actual j) -
        quadraticExpectation (effect j) (ideal j)| ≤
        (‖actual j‖ + ‖ideal j‖) * ‖actual j - ideal j‖ :=
    quadraticExpectation_sub_le
      (effect j) (contraction j) (actual j) (ideal j)
  calc
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
        (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| =
      |∑ j : J, weight j *
        (quadraticExpectation (effect j) (actual j) -
          quadraticExpectation (effect j) (ideal j))| := by
            congr 1
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j : J, |weight j *
      (quadraticExpectation (effect j) (actual j) -
        quadraticExpectation (effect j) (ideal j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : J, weight j *
      |quadraticExpectation (effect j) (actual j) -
        quadraticExpectation (effect j) (ideal j)| := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul, abs_of_nonneg (nonnegative j)]
    _ ≤ ∑ j : J, weight j *
      ((‖actual j‖ + ‖ideal j‖) * ‖actual j - ideal j‖) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (point j) (nonnegative j)
    _ = (∑ j : J, weight j * ‖actual j‖ * ‖actual j - ideal j‖) +
        (∑ j : J, weight j * ‖ideal j‖ * ‖actual j - ideal j‖) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ ≤ Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) *
          Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2) *
          Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) := by
          exact add_le_add
            (weighted_real_cauchy weight
              (fun j => ‖actual j‖)
              (fun j => ‖actual j - ideal j‖) nonnegative)
            (weighted_real_cauchy weight
              (fun j => ‖ideal j‖)
              (fun j => ‖actual j - ideal j‖) nonnegative)
    _ = (Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2)) *
        Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) := by
          ring

theorem unconditionalMatchedVerifierAggregate_dependent_le
    {J : Type*} [Fintype J]
    {H : J → Type*}
    [∀ j, NormedAddCommGroup (H j)]
    [∀ j, InnerProductSpace ℂ (H j)]
    (weight : J → ℝ)
    (nonnegative : ∀ j, 0 ≤ weight j)
    (effect : (j : J) → (H j →L[ℂ] H j))
    (contraction : ∀ j, ‖effect j‖ ≤ 1)
    (actual ideal : (j : J) → H j)
    (actual_mass : (∑ j : J, weight j * ‖actual j‖ ^ 2) ≤ 1)
    (ideal_mass : (∑ j : J, weight j * ‖ideal j‖ ^ 2) ≤ 1)
    (Δ : ℝ)
    (deviation :
      (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) ≤ Δ) :
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
      (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      2 * Real.sqrt Δ := by
  have actual_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖actual j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have ideal_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖ideal j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have error_nonnegative :
      0 ≤ ∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2 :=
    Finset.sum_nonneg
      (fun j _ => mul_nonneg (nonnegative j) (sq_nonneg _))
  have actual_root :
      Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) ≤ 1 := by
    nlinarith [
      Real.sq_sqrt actual_nonnegative,
      Real.sqrt_nonneg (∑ j : J, weight j * ‖actual j‖ ^ 2)]
  have ideal_root :
      Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2) ≤ 1 := by
    nlinarith [
      Real.sq_sqrt ideal_nonnegative,
      Real.sqrt_nonneg (∑ j : J, weight j * ‖ideal j‖ ^ 2)]
  calc
    |(∑ j : J, weight j * quadraticExpectation (effect j) (actual j)) -
        (∑ j : J, weight j * quadraticExpectation (effect j) (ideal j))| ≤
      (Real.sqrt (∑ j : J, weight j * ‖actual j‖ ^ 2) +
        Real.sqrt (∑ j : J, weight j * ‖ideal j‖ ^ 2)) *
        Real.sqrt (∑ j : J, weight j * ‖actual j - ideal j‖ ^ 2) :=
          unconditionalMatchedVerifierAggregate_dependent_continuity
            weight nonnegative effect contraction actual ideal
    _ ≤ 2 * Real.sqrt Δ := by
      apply mul_le_mul
      · linarith
      · exact Real.sqrt_le_sqrt deviation
      · exact Real.sqrt_nonneg _
      · norm_num

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The state vector representing unconditional conjugate pure. -/
def unconditionalConjugatePureVector
    {ι : Type*} (z : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  toLp 2 (fun i : ι => star (z i))

@[simp] theorem unconditionalConjugatePureVector_apply
    {ι : Type*}
    (z : EuclideanSpace ℂ ι) (i : ι) :
    unconditionalConjugatePureVector z i = star (z i) := by
  rfl

theorem unconditionalConjugatePureVector_norm_sq
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, unconditionalConjugatePureVector_apply, RCLike.star_def,
    RCLike.norm_conj]

theorem unconditionalConjugatePureVector_norm
    {ι : Type*} [Fintype ι] (z : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector z‖ = ‖z‖ := by
  have squares := unconditionalConjugatePureVector_norm_sq z
  nlinarith [norm_nonneg (unconditionalConjugatePureVector z),
    norm_nonneg z]

private def unconditionalConjugatePOVM
    {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (P : POVM A ι) : POVM A ι where
  effect a := (P.effect a).transpose
  positive a := (P.positive a).transpose
  complete := by
    classical
    rw [← Matrix.transpose_sum]
    rw [P.complete, Matrix.transpose_one]

theorem unconditionalConjugatePureVector_transpose_quadratic
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M.transpose)
        (unconditionalConjugatePureVector z) =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  congr 1
  simp only [Matrix.transpose_apply,
    unconditionalConjugatePureVector_apply, star_star]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem unconditionalConjugatePOVM_jointEffect
    {A B ι κ : Type*} [Fintype A] [Fintype B]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : POVM A ι) (Q : POVM B κ) (a : A) (b : B) :
    (unconditionalConjugatePOVM P).effect a ⊗ₖ
        (unconditionalConjugatePOVM Q).effect b =
      (P.effect a ⊗ₖ Q.effect b).transpose := by
  exact Matrix.kroneckerMap_transpose (fun x y : ℂ => x * y)
    (P.effect a) (Q.effect b)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def unconditionalConjugateSourceGlobalCatalystWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystAlicePOVM
          G n S D e a₀ x)).effect a ⊗ₖ
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystBobPOVM
          G n S D e b₀ y)).effect b
    else 0

theorem
    unconditionalConjugateSourceGlobalCatalystWinningEffect_eq_transpose
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    unconditionalConjugateSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y =
      (exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y).transpose := by
  classical
  unfold unconditionalConjugateSourceGlobalCatalystWinningEffect
    exactSourceGlobalCatalystWinningEffect
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.transpose_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact unconditionalConjugatePOVM_jointEffect
      (exactSourceGlobalCatalystAlicePOVM G n S D e a₀ x)
      (exactSourceGlobalCatalystBobPOVM G n S D e b₀ y)
      a b
  · exact Matrix.transpose_zero.symm

theorem unconditionalConjugateSourceGlobalCatalystWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e) ×
       Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e))) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y))
      (unconditionalConjugatePureVector z) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (exactSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ x y)) z := by
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e) ×
            Fin (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D) * e))
          (𝕜 := ℂ)
          (exactSourceGlobalCatalystWinningEffect
            G n S D e a₀ b₀ x y).transpose)
        (unconditionalConjugatePureVector z) := by
          exact congrArg
            (fun M =>
              quadraticExpectation
                (Matrix.toEuclideanCLM
                  (n :=
                    Fin (Fintype.card
                      (ExactGlobalHistoryLocalIndex G n S D) * e) ×
                    Fin (Fintype.card
                      (ExactGlobalHistoryLocalIndex G n S D) * e))
                  (𝕜 := ℂ) M)
                (unconditionalConjugatePureVector z))
            (unconditionalConjugateSourceGlobalCatalystWinningEffect_eq_transpose
              G n S D e a₀ b₀ x y)
    _ = _ := unconditionalConjugatePureVector_transpose_quadratic
      (exactSourceGlobalCatalystWinningEffect
        G n S D e a₀ b₀ x y) z

theorem
    unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (e : ℕ) (residual_positive : 0 < e)
    (a₀ : A) (b₀ : B)
    (u : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D u ≠ 0) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e) ×
          Fin (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) * e))
        (𝕜 := ℂ)
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D e a₀ b₀ u.2.1 u.2.2.1))
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := e)
          (exactGlobalHistoryFinPsi G n S D u.2.2.2
            u.2.1 u.2.2.1))) =
    exactSourceConditionalWinningProbability G n S D u := by
  rw [unconditionalConjugateSourceGlobalCatalystWinningEffect_quadratic]
  exact
    (exactSourceGlobalCatalystWinningEffect_law_supported_verifier
      G n S D positive e residual_positive a₀ b₀ u supported).symm

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem unconditionalPublicBucketPhysicalCoherentTarget_apply
    {d N B n : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin (N * n)) :
    dSVDensityRationalPublicBucketPhysicalCoherentTargetState
        (N := N) (B := B) w n ξ ζ
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      (ePRState B (φ, ψ) *
        (((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
          dSVDensityRationalLocalSpectralPairBasisOverlap
            ξ ζ i j)) *
        ((Real.sqrt
            ((dSVDensityRationalPhysicalAcceptedRank
              w N ξ i).val : ℝ) : ℂ) *
          embezzlementState (N * n) (a, b)) := by
  rfl

theorem unconditionalCanonicalAcceptedCoefficient_sourceScale
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) =
      dSVDensityRationalCanonicalAcceptedCoefficient w N ξ i := by
  have d_nonzero : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have n_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt grid)
  have source_positive :
      0 < ‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖ := by
    have source_sq := dSVUniformDensityThresholdRaw_norm_sq N d
    have product_positive : (0 : ℝ) < (d : ℝ) * (N : ℝ) := by
      positivity
    nlinarith [norm_nonneg
      (sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ)))]
  have left_nonnegative :
      0 ≤ Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) := by
    positivity
  have right_nonnegative :=
    dSVDensityRationalCanonicalAcceptedCoefficient_nonneg
      w N ξ i
  have same_square :
      (Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ)) ^ 2 =
        dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i ^ 2 := by
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w * (d : ℝ)),
      inv_pow, dSVUniformDensityThresholdRaw_norm_sq,
      Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤
          (dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val),
      dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
        width N ξ i]
    field_simp
  nlinarith

theorem unconditionalConjugateTranspose_eq_inverse
    {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (conjugateUnitary U : Matrix (Fin d) (Fin d) ℂ).transpose =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) := by
  change U.val.conjTranspose.transpose.transpose =
    ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ)
  rw [Matrix.transpose_transpose]
  change star (U : Matrix (Fin d) (Fin d) ℂ) = _
  exact congrArg
    (fun V : Matrix.unitaryGroup (Fin d) ℂ =>
      (V : Matrix (Fin d) (Fin d) ℂ))
    (Unitary.star_eq_inv U)

theorem unconditionalConjugateBobBasisOverlapCancellation
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitaryBasisOverlap U V : Matrix (Fin d) (Fin d) ℂ) *
        (conjugateUnitary V :
          Matrix (Fin d) (Fin d) ℂ).transpose =
      (conjugateUnitary U :
        Matrix (Fin d) (Fin d) ℂ).transpose := by
  rw [unconditionalConjugateTranspose_eq_inverse,
    unconditionalConjugateTranspose_eq_inverse]
  change
    (((U⁻¹ * V : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ)) *
      ((V⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ)
  change
    (((U⁻¹ * V) * V⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ) =
      ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ)
  simp only [mul_inv_cancel_right, UnitaryGroup.inv_val]

theorem unconditionalConjugateBobBasisOverlap_sum
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (i b : Fin d) :
    (∑ j : Fin d,
      unitaryBasisOverlap U V i j *
        star ((V : Matrix (Fin d) (Fin d) ℂ) b j)) =
      star ((U : Matrix (Fin d) (Fin d) ℂ) b i) := by
  have identity := congrArg
    (fun M : Matrix (Fin d) (Fin d) ℂ => M i b)
    (unconditionalConjugateBobBasisOverlapCancellation U V)
  simpa only [unitaryBasisOverlap_apply, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def,
    transpose_apply, conjugateUnitary_apply] using identity

theorem unconditionalRationalMixedConjugateBobSpectral_sum
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i b : Fin d) :
    (∑ j : Fin d,
      dSVDensityRationalLocalSpectralPairBasisOverlap ξ ζ i j *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ζ :
            Matrix (Fin d) (Fin d) ℂ) b j)) =
      star
        ((dSVUniformDensityThresholdLeftBobBasis ξ :
          Matrix (Fin d) (Fin d) ℂ) b i) := by
  exact unconditionalConjugateBobBasisOverlap_sum
    (dSVUniformDensityThresholdLeftBobBasis ξ)
    (dSVUniformDensityThresholdLeftBobBasis ζ) i b

theorem unconditionalConjugateCanonicalAcceptedTarget_apply
    {d N : ℕ} (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (a b : Fin d) :
    star
        (dSVDensityRationalCanonicalAcceptedTarget w N ξ
          (a, b)) =
      ∑ i : Fin d,
        (dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i : ℂ) *
        star
          ((dSVDensityRationalCanonicalAliceBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) a i) *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) b i) := by
  unfold dSVDensityRationalCanonicalAcceptedTarget
  rw [schmidtVector_apply]
  simp only [star_sum, star_mul', RCLike.star_def, conj_ofReal]

theorem unconditionalMixedConjugateCanonicalAcceptedTarget_sum
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ ζ : BipartiteUnitVector d)
    (a b : Fin d) :
    (∑ i : Fin d, ∑ j : Fin d,
      (Real.sqrt (w * (d : ℝ)) : ℂ) *
        ((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
        (Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) : ℂ) *
        star
          ((dSVDensityRationalCanonicalAliceBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) a i) *
        dSVDensityRationalLocalSpectralPairBasisOverlap
          ξ ζ i j *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ζ :
            Matrix (Fin d) (Fin d) ℂ) b j)) =
      star
        (dSVDensityRationalCanonicalAcceptedTarget
          w N ξ (a, b)) := by
  classical
  calc
    _ =
        ∑ i : Fin d,
          ((Real.sqrt (w * (d : ℝ)) : ℂ) *
            ((‖sharedThresholdResourceRaw (d := Fin d)
              (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
            (Real.sqrt
              ((dSVDensityRationalPhysicalAcceptedRank
                w N ξ i).val : ℝ) : ℂ) *
            star
              ((dSVDensityRationalCanonicalAliceBasis ξ :
                Matrix (Fin d) (Fin d) ℂ) a i)) *
          (∑ j : Fin d,
            dSVDensityRationalLocalSpectralPairBasisOverlap
              ξ ζ i j *
            star
              ((dSVUniformDensityThresholdLeftBobBasis ζ :
                Matrix (Fin d) (Fin d) ℂ) b j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ =
        ∑ i : Fin d,
          (dSVDensityRationalCanonicalAcceptedCoefficient
            w N ξ i : ℂ) *
          star
            ((dSVDensityRationalCanonicalAliceBasis ξ :
              Matrix (Fin d) (Fin d) ℂ) a i) *
          star
            ((dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ) b i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [unconditionalRationalMixedConjugateBobSpectral_sum]
          have coefficient := congrArg (fun x : ℝ => (x : ℂ))
            (unconditionalCanonicalAcceptedCoefficient_sourceScale
              width grid dimension ξ i)
          push_cast at coefficient
          rw [← coefficient]
          push_cast
          ring
    _ = _ :=
      (unconditionalConjugateCanonicalAcceptedTarget_apply
        w ξ a b).symm

/--
The unconditional mixed conjugate sigma atom lift construction used in the quantum parallel-
repetition argument.
-/
def unconditionalMixedConjugateSigmaAtomLift
    {d m : ℕ} (B : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup
      (Σ _ : Fin B × Fin d, Fin m) ℂ := by
  classical
  let e : ((Fin B × Fin d) × Fin m) ≃
      (Σ _ : Fin B × Fin d, Fin m) :=
    (Equiv.sigmaEquivProd (Fin B × Fin d) (Fin m)).symm
  let M : Matrix ((Fin B × Fin d) × Fin m)
      ((Fin B × Fin d) × Fin m) ℂ :=
    ((1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ
      (U : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
      (1 : Matrix (Fin m) (Fin m) ℂ)
  have unitary : M ∈ Matrix.unitaryGroup
      ((Fin B × Fin d) × Fin m) ℂ :=
    Matrix.kronecker_mem_unitary
      (Matrix.kronecker_mem_unitary
        (Matrix.unitaryGroup (Fin B) ℂ).one_mem U.property)
      (Matrix.unitaryGroup (Fin m) ℂ).one_mem
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) =
        Matrix.reindex e e (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp unitary]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

theorem unconditionalMixedConjugateSigmaAtomLift_apply
    {d m : ℕ} (B : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin m) :
    (unconditionalMixedConjugateSigmaAtomLift (m := m) B U :
      Matrix (Σ _ : Fin B × Fin d, Fin m)
        (Σ _ : Fin B × Fin d, Fin m) ℂ)
      ⟨(φ, i), a⟩ ⟨(ψ, j), b⟩ =
      if φ = ψ ∧ a = b then
        (U : Matrix (Fin d) (Fin d) ℂ) i j
      else 0 := by
  classical
  by_cases phase : φ = ψ <;>
    by_cases work : a = b <;>
      simp [unconditionalMixedConjugateSigmaAtomLift,
        Matrix.reindex_apply, Matrix.kroneckerMap_apply, phase, work]

private def unconditionalMixedConjugateSigmaLocalAction
    {d m : ℕ} (B : ℕ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m))) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m)) :=
  toLp 2
    ((((unconditionalMixedConjugateSigmaAtomLift (m := m) B U :
          Matrix (Σ _ : Fin B × Fin d, Fin m)
            (Σ _ : Fin B × Fin d, Fin m) ℂ) ⊗ₖ
        (unconditionalMixedConjugateSigmaAtomLift (m := m) B V :
          Matrix (Σ _ : Fin B × Fin d, Fin m)
            (Σ _ : Fin B × Fin d, Fin m) ℂ)).mulVec
      (ofLp z)))

theorem unconditionalMixedConjugateSigmaLocalAction_apply
    {d m : ℕ} (B : ℕ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
        (Σ _ : Fin B × Fin d, Fin m)))
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin m) :
    unconditionalMixedConjugateSigmaLocalAction B U V z
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      ∑ k : Fin d, ∑ l : Fin d,
        (U : Matrix (Fin d) (Fin d) ℂ) i k *
        (V : Matrix (Fin d) (Fin d) ℂ) j l *
        z (⟨(φ, k), a⟩, ⟨(ψ, l), b⟩) := by
  classical
  simp only [unconditionalMixedConjugateSigmaLocalAction, mulVec, dotProduct, kroneckerMap_apply,
    mul_assoc, Fintype.sum_prod_type, Fintype.sum_sigma,
    unconditionalMixedConjugateSigmaAtomLift_apply, ite_and, ite_mul, zero_mul, mul_ite, mul_zero,
    sum_ite_irrel, sum_ite_eq, mem_univ, ↓reduceIte, sum_const_zero]

private def unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
    {d N B : ℕ} (w : ℝ) (n : ℕ)
    (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
    (unconditionalConjugatePureVector
      (dSVDensityRationalCanonicalAcceptedTarget w N ξ))
    (fun _ _ _ => embezzlementState (N * n))

theorem unconditionalMixedConjugateTargetCovariance
    {d N B n : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ ζ : BipartiteUnitVector d) :
    Real.sqrt (w * (d : ℝ)) •
      unconditionalMixedConjugateSigmaLocalAction
        (m := N * n) B
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis ξ))
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis ζ))
        (dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ) =
    unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
        (B := B) w n ξ := by
  classical
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  change
    (Real.sqrt (w * (d : ℝ)) : ℂ) *
      unconditionalMixedConjugateSigmaLocalAction B
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis ξ))
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis ζ))
        (dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ)
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      (ePRState B (φ, ψ) *
        star (dSVDensityRationalCanonicalAcceptedTarget
          w N ξ (i, j))) *
        embezzlementState (N * n) (a, b)
  rw [unconditionalMixedConjugateSigmaLocalAction_apply]
  simp_rw [conjugateUnitary_apply,
    unconditionalPublicBucketPhysicalCoherentTarget_apply]
  rw [← unconditionalMixedConjugateCanonicalAcceptedTarget_sum
    width grid dimension ξ ζ i j]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalSelectedCopy_coherentPhaseSigma_norm_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (work : H → H → EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B history (fun _ i j => work i j)‖ ^ 2 =
      ‖dSVUniformDensityCorrectedMatchedSigmaWeightedResidual
        history work‖ ^ 2 := by
  classical
  unfold dSVDensityRationalPublicBucketCoherentPhaseSigmaState
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq,
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq]
  simp only [Fintype.sum_prod_type]
  simp_rw [
    dSVDensityRationalPublicBucketCoherentPhaseHistory_apply_norm_sq
      phases]
  have phase_ne : (B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt phases)
  calc
    (∑ φ : Fin B, ∑ i : H, ∑ ψ : Fin B, ∑ j : H,
        (if φ = ψ then (B : ℝ)⁻¹ else 0) *
          ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) =
        ∑ φ : Fin B, ∑ i : H, ∑ j : H,
          (B : ℝ)⁻¹ * ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro φ _
            apply Finset.sum_congr rfl
            intro i _
            simp only [ite_mul, zero_mul, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ,
              ↓reduceIte]
    _ = _ := by
      calc
        (∑ φ : Fin B, ∑ i : H, ∑ j : H,
            (B : ℝ)⁻¹ * ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) =
          ∑ _φ : Fin B, (B : ℝ)⁻¹ *
            (∑ i : H, ∑ j : H,
              ‖history (i, j)‖ ^ 2 * ‖work i j‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro φ _
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp

theorem unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (work : EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B history (fun _ _ _ => work)‖ ^ 2 =
      ‖history‖ ^ 2 * ‖work‖ ^ 2 := by
  rw [unconditionalSelectedCopy_coherentPhaseSigma_norm_sq
    phases history (fun _ _ => work),
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq]
  calc
    (∑ i : H, ∑ j : H, ‖history (i, j)‖ ^ 2 * ‖work‖ ^ 2) =
        (∑ i : H, ∑ j : H, ‖history (i, j)‖ ^ 2) * ‖work‖ ^ 2 := by
          simp_rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]

theorem unconditionalSelectedCopy_conjugateAcceptedTarget_norm_sq
    {d N B m : ℕ} (phases : 0 < B)
    (grid : 0 < N) (harmonic : 0 < m)
    (w : ℝ) (ξ : BipartiteUnitVector d) :
    ‖unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
        (N := N) (B := B) w m ξ‖ ^ 2 =
      ‖dSVDensityRationalCanonicalAcceptedTarget w N ξ‖ ^ 2 := by
  unfold unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
  rw [unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
    phases]
  rw [unconditionalConjugatePureVector_norm_sq,
    embezzlementState_norm (N * m) (Nat.mul_pos grid harmonic)]
  ring

theorem unconditionalSelectedCopy_mixedConjugateLocalAction_norm
    {d B m : ℕ}
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
       (Σ _ : Fin B × Fin d, Fin m))) :
    ‖unconditionalMixedConjugateSigmaLocalAction B U V z‖ = ‖z‖ := by
  simpa only [unconditionalMixedConjugateSigmaLocalAction] using
    dSVUniformDensityMixedProtocolLocalAction_norm
      (unconditionalMixedConjugateSigmaAtomLift (m := m) B U)
      (unconditionalMixedConjugateSigmaAtomLift (m := m) B V) z

theorem unconditionalSelectedCopyIdealStage_norm_sq
    {d N B m : ℕ} {w : ℝ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : 0 < w)
    (ξ ζ : BipartiteUnitVector d) :
    ‖unconditionalSelectedCopyIdealStage
        (N := N) (B := B) (m := m) w ξ ζ‖ ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ := by
  have covariance :=
    unconditionalMixedConjugateTargetCovariance
      (B := B) (n := m) width grid dimension ξ ζ
  have squared := congrArg (fun z => ‖z‖ ^ 2) covariance
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w * (d : ℝ)),
    unconditionalSelectedCopy_mixedConjugateLocalAction_norm,
    unconditionalSelectedCopy_conjugateAcceptedTarget_norm_sq
      phases grid harmonic,
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq width]
    at squared
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have cancelled :
      (d : ℝ) *
          ‖unconditionalSelectedCopyIdealStage
            (N := N) (B := B) (m := m) w ξ ζ‖ ^ 2 =
        dSVDensityRationalLeftProjectiveDiagonalMass w N ξ := by
    apply mul_left_cancel₀ (ne_of_gt width)
    simpa only [unconditionalSelectedCopyIdealStage, mul_eq_mul_left_iff, mul_assoc] using squared
  rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq]
  apply (eq_div_iff (ne_of_gt dimension_real)).2
  simpa only [mul_comm] using cancelled

theorem unconditionalSelectedCopyCleanedStage_norm_sq
    {d N B m : ℕ} {w : ℝ}
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : 0 < w)
    (ξ ζ : BipartiteUnitVector d)
    (Q : ℕ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    ‖unconditionalSelectedCopyCleanedStage
        (N := N) (B := B) (m := m) Q w ξ ζ A C‖ ^ 2 =
      ‖dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ true true‖ ^ 2 := by
  unfold unconditionalSelectedCopyCleanedStage
    dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
  rw [dSVUniformDensityPhysicalAsyncSigmaContinuation_norm]
  unfold dSVDensityRationalPublicBucketPhysicalCoherentMixedState
  rw [unconditionalSelectedCopy_coherentPhaseSigma_norm_sq phases]
  exact
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_norm_sq
      width grid harmonic ξ ζ

theorem unconditionalSelectedCopyCleanedMatchedBranch_norm_sq
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (phases : 0 < B) (grid : 0 < N) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (Q : ℕ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyCleanedMatchedBranch
        Q width schedule ξ ζ A C j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val := by
  unfold unconditionalSelectedCopyCleanedMatchedBranch
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyCleanedStage_norm_sq
      phases grid harmonic (width_positive (schedule j)),
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  simp only [one_pow, mul_comm, one_mul, dSVDensityRationalHeterogeneousPhysicalStageSuccess,
    dSVDensityRationalHeterogeneousPhysicalStageOutcome, j.isLt, ↓reduceDIte, Fin.eta]

theorem unconditionalSelectedCopyIdealMatchedBranch_norm_sq
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ]
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ τ)
    (rest_unit : ‖rest‖ = 1) :
    ‖unconditionalSelectedCopyIdealMatchedBranch
        (N := N) (B := B) (m := m) width schedule ξ ζ j rest‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule j)) ξ := by
  unfold unconditionalSelectedCopyIdealMatchedBranch
  rw [unconditionalMatchedVerifierTensor_norm_sq,
    unconditionalSelectedCopyIdealStage_norm_sq
      phases grid dimension harmonic (width_positive (schedule j)),
    unconditionalSelectedCopyRetainedWork_norm_sq,
    rest_unit]
  ring

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The unitary operator implementing unconditional mixed conjugate selected branch. -/
def unconditionalMixedConjugateSelectedBranchUnitary
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup ((ι × ι) × τ) ℂ := by
  classical
  refine
    ⟨(((U : Matrix ι ι ℂ) ⊗ₖ
        (V : Matrix ι ι ℂ)) ⊗ₖ
        (1 : Matrix τ τ ℂ)), ?_⟩
  exact Matrix.kronecker_mem_unitary
    (Matrix.kronecker_mem_unitary U.property V.property)
    (Matrix.unitaryGroup τ ℂ).one_mem

/-- The operator action for unconditional mixed conjugate selected branch local. -/
def unconditionalMixedConjugateSelectedBranchLocalAction
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    EuclideanSpace ℂ ((ι × ι) × τ) :=
  toLp 2
    ((unconditionalMixedConjugateSelectedBranchUnitary
        (τ := τ) U V :
      Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ).mulVec
      (ofLp z))

theorem unconditionalMixedConjugateSelectedBranch_tensorAction
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (stage : EuclideanSpace ℂ (ι × ι))
    (work : EuclideanSpace ℂ τ) :
    unconditionalMixedConjugateSelectedBranchLocalAction
        U V
        (unconditionalMatchedVerifierTensor stage work) =
      unconditionalMatchedVerifierTensor
        (toLp 2
          ((((U : Matrix ι ι ℂ) ⊗ₖ
              (V : Matrix ι ι ℂ)).mulVec
            (ofLp stage)))) work := by
  classical
  ext ⟨⟨a, b⟩, t⟩
  simp only [unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary, unconditionalMatchedVerifierTensor, mulVec,
    dotProduct, kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul,
    mul_assoc, zero_mul, Fintype.sum_prod_type, sum_ite_eq, mem_univ, ↓reduceIte, sum_mul]

theorem unconditionalMixedConjugateSelectedBranch_tensor_smul
    {s τ : Type*}
    (c : ℝ) (stage : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ τ) :
    c • unconditionalMatchedVerifierTensor stage work =
      unconditionalMatchedVerifierTensor
        (c • stage) work := by
  ext ⟨a, b⟩
  change (c : ℂ) * (stage a * work b) =
    ((c : ℂ) * stage a) * work b
  ring

theorem unconditionalMixedConjugateSelectedBranchCovariance
    {S N d L B m : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (rest : EuclideanSpace ℂ τ) :
    Real.sqrt (width (schedule j) * (d : ℝ)) •
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis ξ)))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ζ)))
        (unconditionalSelectedCopyIdealMatchedBranch
          (N := N) (B := B) (m := m)
          width schedule ξ ζ j rest) =
      unconditionalMatchedVerifierTensor
        (unconditionalMixedConjugateAcceptedPhaseHarmonicTarget
          (N := N) (B := B) (width (schedule j)) m ξ)
        (unconditionalSelectedCopyRetainedWork
          (N := N) width schedule ξ ζ j rest) := by
  classical
  unfold unconditionalSelectedCopyIdealMatchedBranch
    unconditionalSelectedCopyIdealStage
  rw [unconditionalMixedConjugateSelectedBranch_tensorAction,
    unconditionalMixedConjugateSelectedBranch_tensor_smul]
  congr 1
  exact unconditionalMixedConjugateTargetCovariance
    positive grid dimension ξ ζ

theorem unconditionalPhysicalAcceptedCoherentStage_eq_phaseSigma
    {d N B m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d) (a b : Fin (N * m)) :
    dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ
        (⟨(φ, i), a⟩, ⟨(ψ, j), b⟩) =
      ePRState B (φ, ψ) *
        dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState
          w m ξ ζ (⟨i, a⟩, ⟨j, b⟩) := by
  simp only [dSVDensityRationalPublicBucketPhysicalCoherentMixedState,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalPublicBucketCoherentPhaseHistory, mul_assoc,
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState]

theorem unconditionalPhysicalAcceptedCoherentStage_apply
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : Fin B) (i j : Fin d)
    (k l : Fin N) (a b : Fin m) :
    dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ
        (⟨(φ, i), finProdFinEquiv (k, a)⟩,
          ⟨(ψ, j), finProdFinEquiv (l, b)⟩) =
      ePRState B (φ, ψ) *
        dSVDensityRationalCanonicalPrefixSpectralOutcome
          w N ξ ζ (⟨k, i⟩, ⟨l, j⟩) *
        embezzlementState m (a, b) := by
  rw [unconditionalPhysicalAcceptedCoherentStage_eq_phaseSigma,
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_apply
      width grid]
  ring

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

section DependentStoppingBlocks

variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι κ : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
variable [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]

/-- The state vector representing actual stopping branch. -/
def actualStoppingBranchVector
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (r s : R) : EuclideanSpace ℂ (ι r × κ s) :=
  toLp 2 fun q => z (⟨r, q.1⟩, ⟨s, q.2⟩)

/-- The measurement effect for actual stopping branch winning. -/
def actualStoppingBranchWinningEffect
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y) :
    Matrix (ι r × κ s) (ι r × κ s) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (PA r x).effect a ⊗ₖ (PB s y).effect b
    else 0

omit [Fintype R] [DecidableEq R] in
theorem actualStoppingBranchWinningEffect_posSemidef
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y) :
    (actualStoppingBranchWinningEffect
      G PA PB r s x y).PosSemidef := by
  classical
  apply Matrix.nonneg_iff_posSemidef.mp
  unfold actualStoppingBranchWinningEffect
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split
  · exact ((PA r x).positive a).kronecker
      ((PB s y).positive b) |>.nonneg
  · exact le_rfl

omit [Fintype R] [DecidableEq R] in
theorem actualStoppingBranchBorn_nonneg
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (r s : R) (x : X) (y : Y) :
    0 ≤ quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι r × κ s) (𝕜 := ℂ)
        (actualStoppingBranchWinningEffect
          G PA PB r s x y))
      (actualStoppingBranchVector z r s) := by
  apply positive_quadraticExpectation_nonneg
  apply matrixEffectCLM_isPositive
  exact actualStoppingBranchWinningEffect_posSemidef
    G PA PB r s x y

private def actualStoppingGlobalWinningEffect
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (x : X) (y : Y) :
    Matrix ((Σ r, ι r) × (Σ s, κ s))
      ((Σ r, ι r) × (Σ s, κ s)) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (dependentBlockPOVM
        (fun r => PA r x)).effect a ⊗ₖ
        (dependentBlockPOVM
          (fun s => PB s y)).effect b
    else 0

theorem actualStoppingGlobalWinningEffect_same
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s : R) (x : X) (y : Y)
    (i i' : ι r) (j j' : κ s) :
    actualStoppingGlobalWinningEffect G PA PB x y
        (⟨r, i⟩, ⟨s, j⟩) (⟨r, i'⟩, ⟨s, j'⟩) =
      actualStoppingBranchWinningEffect G PA PB r s x y
        (i, j) (i', j') := by
  classical
  unfold actualStoppingGlobalWinningEffect
    actualStoppingBranchWinningEffect
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · simp only [kroneckerMap_apply, dependentBlockPOVM_effect_same]
  · rfl

theorem actualStoppingGlobalWinningEffect_cross_eq_zero
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (r s r' s' : R) (x : X) (y : Y)
    (i : ι r) (j : κ s) (i' : ι r') (j' : κ s')
    (different : r ≠ r' ∨ s ≠ s') :
    actualStoppingGlobalWinningEffect G PA PB x y
        (⟨r, i⟩, ⟨s, j⟩) (⟨r', i'⟩, ⟨s', j'⟩) = 0 := by
  classical
  rcases different with left | right
  · unfold actualStoppingGlobalWinningEffect
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · simp only [dependentBlockPOVM, kroneckerMap_apply, blockDiagonal'_apply, left, ↓reduceDIte,
        mul_dite, zero_mul, mul_zero, dite_eq_ite, ite_self]
    · rfl
  · unfold actualStoppingGlobalWinningEffect
    simp only [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    split_ifs
    · simp only [dependentBlockPOVM, kroneckerMap_apply, blockDiagonal'_apply, right, ↓reduceDIte,
        mul_zero]
    · rfl

theorem actualStoppingGlobalBorn_eq_sum
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (s : R) → Y → POVM B (κ s))
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ s, κ s)))
    (x : X) (y : Y) :
    quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (Σ r, ι r) × (Σ s, κ s)) (𝕜 := ℂ)
          (actualStoppingGlobalWinningEffect G PA PB x y)) z =
      ∑ r : R, ∑ s : R,
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := ι r × κ s) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G PA PB r s x y))
          (actualStoppingBranchVector z r s) := by
  classical
  have collapse (r s : R) (i : ι r) (j : κ s) :
      (∑ r' : R, ∑ i' : ι r', ∑ s' : R, ∑ j' : κ s',
        actualStoppingGlobalWinningEffect G PA PB x y
            (⟨r, i⟩, ⟨s, j⟩) (⟨r', i'⟩, ⟨s', j'⟩) *
          z (⟨r', i'⟩, ⟨s', j'⟩)) =
        ∑ i' : ι r, ∑ j' : κ s,
          actualStoppingBranchWinningEffect G PA PB r s x y
              (i, j) (i', j') * z (⟨r, i'⟩, ⟨s, j'⟩) := by
    rw [Finset.sum_eq_single r]
    · apply Finset.sum_congr rfl
      intro i' _
      rw [Finset.sum_eq_single s]
      · apply Finset.sum_congr rfl
        intro j' _
        rw [actualStoppingGlobalWinningEffect_same]
      · intro s' _ unequal
        apply Finset.sum_eq_zero
        intro j' _
        rw [actualStoppingGlobalWinningEffect_cross_eq_zero
          G PA PB r s r s' x y i j i' j'
            (Or.inr (Ne.symm unequal))]
        simp only [zero_mul]
      · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
    · intro r' _ unequal
      apply Finset.sum_eq_zero
      intro i' _
      apply Finset.sum_eq_zero
      intro s' _
      apply Finset.sum_eq_zero
      intro j' _
      rw [actualStoppingGlobalWinningEffect_cross_eq_zero
        G PA PB r s r' s' x y i j i' j'
          (Or.inl (Ne.symm unequal))]
      simp only [zero_mul]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  rw [matrixQuadraticExpectation_expand]
  simp_rw [matrixQuadraticExpectation_expand]
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [collapse]
  rfl

end DependentStoppingBlocks

end

section

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

theorem unitaryConjugatePOVM_jointEffect
    {A B d : Type} [Fintype A] [Fintype B]
    [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ)
    (P : POVM A d) (Q : POVM B d)
    (a : A) (b : B) :
    (unitaryConjugatePOVM U P).effect a ⊗ₖ
      (unitaryConjugatePOVM V Q).effect b =
      (((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))ᴴ *
        (P.effect a ⊗ₖ Q.effect b) *
        ((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))) := by
  change
    (((U : Matrix d d ℂ)ᴴ * P.effect a * (U : Matrix d d ℂ)) ⊗ₖ
      ((V : Matrix d d ℂ)ᴴ * Q.effect b * (V : Matrix d d ℂ))) =
      (((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ))ᴴ *
        (P.effect a ⊗ₖ Q.effect b) *
        ((U : Matrix d d ℂ) ⊗ₖ (V : Matrix d d ℂ)))
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

section QuestionLocalStopping

variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]

/-- The operator action for actual stopping question local. -/
def actualStoppingQuestionLocalAction
    (U V : Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r))) :
    EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)) :=
  toLp 2
    (((U : Matrix (Σ r, ι r) (Σ r, ι r) ℂ) ⊗ₖ
      (V : Matrix (Σ r, ι r) (Σ r, ι r) ℂ)).mulVec
      (ofLp z))

theorem actualStoppingQuestionLocalWinningEffect_quadratic
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (r : R) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)))
    (normalized : ‖z‖ = 1)
    (x : X) (y : Y) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (pureVerifierEffect G z normalized
          (fun x => unitaryConjugatePOVM (U x)
            (dependentBlockPOVM (fun r => PA r x)))
          (fun y => unitaryConjugatePOVM (V y)
            (dependentBlockPOVM (fun r => PB r y)))
          x y)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
          (actualStoppingGlobalWinningEffect
            G PA PB x y))
        (actualStoppingQuestionLocalAction
          (U x) (V y) z) := by
  classical
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            (unitaryConjugatePOVM (U x)
              (dependentBlockPOVM
                (fun r => PA r x))).effect a ⊗ₖ
            (unitaryConjugatePOVM (V y)
              (dependentBlockPOVM
                (fun r => PB r y))).effect b
          else 0)) z =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := (Σ r, ι r) × (Σ r, ι r)) (𝕜 := ℂ)
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            (dependentBlockPOVM
              (fun r => PA r x)).effect a ⊗ₖ
            (dependentBlockPOVM
              (fun r => PB r y)).effect b
          else 0))
      (actualStoppingQuestionLocalAction
        (U x) (V y) z)
  rw [sourceHistoryQuadraticExpectation_matrix_sum,
    sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceHistoryQuadraticExpectation_matrix_sum,
    sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with accepted
  · rw [unitaryConjugatePOVM_jointEffect]
    exact (rectangular_matrix_quadratic_compression
      (((U x : Matrix (Σ r, ι r) (Σ r, ι r) ℂ) ⊗ₖ
        (V y : Matrix (Σ r, ι r) (Σ r, ι r) ℂ)))
      (((dependentBlockPOVM (fun r => PA r x)).effect a) ⊗ₖ
       ((dependentBlockPOVM (fun r => PB r y)).effect b))
      z).symm
  · simp only [quadraticExpectation, map_zero, _root_.zero_apply, inner_zero_right, zero_re]

theorem actualStoppingQuestionLocalWinningProbability_eq_sum
    (G : Game X Y A B)
    (PA : (r : R) → X → POVM A (ι r))
    (PB : (r : R) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ ((Σ r, ι r) × (Σ r, ι r)))
    (normalized : ‖z‖ = 1) :
    (pureVectorStrategy G z normalized
      (fun x => unitaryConjugatePOVM (U x)
        (dependentBlockPOVM (fun r => PA r x)))
      (fun y => unitaryConjugatePOVM (V y)
        (dependentBlockPOVM (fun r => PB r y)))).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        ∑ r : R, ∑ s : R,
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι s) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r s x y))
            (actualStoppingBranchVector
              (actualStoppingQuestionLocalAction
                (U x) (V y) z) r s) := by
  classical
  rw [pureVectorWinningProbability_eq]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [actualStoppingQuestionLocalWinningEffect_quadratic]
  exact actualStoppingGlobalBorn_eq_sum
    G PA PB (actualStoppingQuestionLocalAction
      (U x) (V y) z) x y

theorem actualStoppingQuestionLocalWinningProbability_ge_matched
    {L : ℕ}
    {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (G : Game X Y A B)
    (PA : (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : X → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (V : Y → Matrix.unitaryGroup (Σ r, ι r) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ r : Fin (L + 1), ι r) ×
       (Σ r : Fin (L + 1), ι r)))
    (normalized : ‖z‖ = 1) :
    (∑ x : X, ∑ y : Y, G.questionWeight x y *
      ∑ j : Fin L,
        quadraticExpectation
          (Matrix.toEuclideanCLM
            (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
            (actualStoppingBranchWinningEffect
              G PA PB j.succ j.succ x y))
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (U x) (V y) z) j.succ j.succ)) ≤
      (pureVectorStrategy G z normalized
        (fun x => unitaryConjugatePOVM (U x)
          (dependentBlockPOVM (fun r => PA r x)))
        (fun y => unitaryConjugatePOVM (V y)
          (dependentBlockPOVM (fun r => PB r y)))).winProbability := by
  classical
  rw [actualStoppingQuestionLocalWinningProbability_eq_sum]
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  apply mul_le_mul_of_nonneg_left _ (G.weight_nonneg x y)
  let stopped := actualStoppingQuestionLocalAction
    (U x) (V y) z
  calc
    (∑ j : Fin L,
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
          (actualStoppingBranchWinningEffect
            G PA PB j.succ j.succ x y))
        (actualStoppingBranchVector stopped
          j.succ j.succ)) ≤
        ∑ r : Fin (L + 1),
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι r) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r r x y))
            (actualStoppingBranchVector stopped r r) := by
          rw [Fin.sum_univ_succ]
          have nonnegative := actualStoppingBranchBorn_nonneg
            G PA PB stopped (0 : Fin (L + 1)) 0 x y
          linarith
    _ ≤ ∑ r : Fin (L + 1), ∑ s : Fin (L + 1),
          quadraticExpectation
            (Matrix.toEuclideanCLM (n := ι r × ι s) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G PA PB r s x y))
            (actualStoppingBranchVector stopped r s) := by
          apply Finset.sum_le_sum
          intro r _
          exact Finset.single_le_sum
            (fun s _ => actualStoppingBranchBorn_nonneg
              G PA PB stopped r s x y)
            (Finset.mem_univ r)

theorem actualStoppingQuestionLocalFlaggedWinningProbability_ge_matched
    {L : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    {ι : Fin (L + 1) → Type}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (G : Game X Y A B)
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j : J, weight j) = 1)
    (PA : J → (r : Fin (L + 1)) → X → POVM A (ι r))
    (PB : J → (r : Fin (L + 1)) → Y → POVM B (ι r))
    (U : J → X → Matrix.unitaryGroup
      (Σ r : Fin (L + 1), ι r) ℂ)
    (V : J → Y → Matrix.unitaryGroup
      (Σ r : Fin (L + 1), ι r) ℂ)
    (z : J → EuclideanSpace ℂ
      ((Σ r : Fin (L + 1), ι r) ×
       (Σ r : Fin (L + 1), ι r)))
    (normalized : ∀ j, ‖z j‖ = 1) :
    (∑ q : J, weight q *
      (∑ x : X, ∑ y : Y, G.questionWeight x y *
        ∑ j : Fin L,
          quadraticExpectation
            (Matrix.toEuclideanCLM
              (n := ι j.succ × ι j.succ) (𝕜 := ℂ)
              (actualStoppingBranchWinningEffect
                G (PA q) (PB q) j.succ j.succ x y))
            (actualStoppingBranchVector
              (actualStoppingQuestionLocalAction
                (U q x) (V q y) (z q)) j.succ j.succ))) ≤
      (pureFlaggedStrategy G weight weight_nonnegative
        weight_normalized z normalized
        (fun q x => unitaryConjugatePOVM (U q x)
          (dependentBlockPOVM (fun r => PA q r x)))
        (fun q y => unitaryConjugatePOVM (V q y)
          (dependentBlockPOVM (fun r => PB q r y)))).winProbability := by
  classical
  rw [pureFlaggedStrategy_winProbability]
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (weight_nonnegative q)
  exact actualStoppingQuestionLocalWinningProbability_ge_matched
    G (PA q) (PB q) (U q) (V q) (z q) (normalized q)

end QuestionLocalStopping

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

private abbrev DSVDensityRationalPublicLogPhaseHistoryFamily
    (B N d L : ℕ) :=
  BipartiteUnitVector d →
    Matrix.unitaryGroup
      (DSVDensityRationalPublicLogPhaseHistoryLocalIndex
        B N d L) ℂ

private def dSVDensityRationalPublicLogPhaseStoppedState
    (B N d L m : ℕ)
    (S T : DSVDensityRationalPublicLogPhaseHistoryFamily
      B N d L)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicLogPhaseResidual
          B N d L m)) :=
  localUnitaryAction
    (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m (S ξ))
    (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
      B N d L m (T ζ))
    (dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
      B N d L m)

private def dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
    (S B N d L m : ℕ) :
    (Σ _ :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L,
      Fin m) ≃
      Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) :=
  (dSVDensityRationalPublicBucketCoherentPhaseSigmaProductEquiv
    (H := DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L)
    (Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B)) m).trans
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m)

private def dSVDensityRationalHeterogeneousOriginalAliceHistoryFamily
    (S B N d L : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S) :
    DSVDensityRationalPublicLogPhaseHistoryFamily
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      N d L :=
  fun ξ =>
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualAliceUnitary
        N width schedule ξ)

private def dSVDensityRationalHeterogeneousOriginalBobHistoryFamily
    (S B N d L : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S) :
    DSVDensityRationalPublicLogPhaseHistoryFamily
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      N d L :=
  fun ζ =>
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
      (Fintype.card
        (DSVDensityRationalPublicMultiscalePhase S B))
      (dSVDensityRationalHeterogeneousActualBobUnitary
        N width schedule ζ)

private def dSVDensityRationalHeterogeneousOriginalStoppedState
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) :=
  dSVDensityRationalPublicLogPhaseStoppedState
    (Fintype.card
      (DSVDensityRationalPublicMultiscalePhase S B))
    N d L m
    (dSVDensityRationalHeterogeneousOriginalAliceHistoryFamily
      S B N d L width schedule)
    (dSVDensityRationalHeterogeneousOriginalBobHistoryFamily
      S B N d L width schedule)
    ξ ζ

private def dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((Σ _ :
        DSVDensityRationalPublicMultiscalePhaseIndex S B ×
          DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
        Fin m) ×
       (Σ _ :
        DSVDensityRationalPublicMultiscalePhaseIndex S B ×
          DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
        Fin m)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m) ×
         Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
        S B N d L m)
      (dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv
        S B N d L m))

private def dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) :=
  dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv
      S B N d L m
    (dSVDensityRationalHeterogeneousPureStoppedSigmaState
      width schedule ξ ζ
      (fun _ _ _ => embezzlementState m))

theorem
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((φ, a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((ψ, b), j)) =
      ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  simp only [dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource,
    dSVDensityRationalHeterogeneousOriginalSameStopStateEquiv,
    dSVDensityRationalPublicMultiscaleOriginalSigmaTargetFirstEquiv,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaProductEquiv,
    dSVDensityRationalHeterogeneousPureStoppedSigmaState,
    dSVDensityRationalPublicMultiscaleBucketCoherentSigmaState,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalPublicBucketCoherentPhaseHistory, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', Equiv.prodCongr_symm, Equiv.symm_trans, Equiv.prodCongr_apply,
    Equiv.coe_trans, Equiv.coe_fn_mk, Prod.map_apply, Function.comp_apply,
    Equiv.symm_apply_apply, Equiv.sigmaEquivProd_symm_apply]

theorem
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
        S B N d L m width schedule ξ ζ =
      dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ := by
  classical
  ext ⟨x, y⟩
  obtain ⟨⟨⟨φ, a⟩, i⟩, rfl⟩ :=
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).surjective x
  obtain ⟨⟨⟨ψ, b⟩, j⟩, rfl⟩ :=
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).surjective y
  obtain ⟨φ', rfl⟩ :=
    (Fintype.equivFin
      (DSVDensityRationalPublicMultiscalePhase S B)).surjective φ
  obtain ⟨ψ', rfl⟩ :=
    (Fintype.equivFin
      (DSVDensityRationalPublicMultiscalePhase S B)).surjective ψ
  rw [dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply]
  change _ =
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
      S B N d L m width schedule ξ ζ
      (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m
        (((Fintype.equivFin
          (DSVDensityRationalPublicMultiscalePhase S B)) φ', a), i),
       dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m
        (((Fintype.equivFin
          (DSVDensityRationalPublicMultiscalePhase S B)) ψ', b), j))
  rw [dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource_apply]
  simp only [ePRState, Fintype.card_pi, Fintype.card_fin, prod_const, card_univ, Nat.cast_pow,
    ofReal_inv, EmbeddingLike.apply_eq_iff_eq, ite_mul, zero_mul]

theorem dSVDensityRationalHeterogeneousOriginalStoppedState_apply
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex N d L)
    (i j : Fin m) :
    dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ
        (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((φ, a), i),
         dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
            S B N d L m ((ψ, b), j)) =
      ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (a, b) *
        embezzlementState m (i, j) := by
  rw [←
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped]
  exact
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply
      S B N d L m width schedule ξ ζ φ ψ a b i j

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

private def directDSVRemainingCopyEquiv
    {L : ℕ} {β : Type*} (j : Fin L) :
    ((Fin j.val → β) × (Fin (L - j.val) → β)) ≃ (Fin L → β) where
  toFun z i :=
    if before : i.val < j.val then z.1 ⟨i.val, before⟩
    else z.2 ⟨i.val - j.val, by omega⟩
  invFun z :=
    (fun i => z ⟨i.val, by omega⟩,
     fun i => z ⟨j.val + i.val, by omega⟩)
  left_inv z := by
    rcases z with ⟨before, after⟩
    apply Prod.ext
    · funext i
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
    · funext i
      simp only [add_lt_iff_neg_left, not_lt_zero, ↓reduceDIte, add_tsub_cancel_left, Fin.eta]
  right_inv z := by
    funext i
    dsimp
    split_ifs with before
    · rfl
    · apply congrArg z
      apply Fin.ext
      change j.val + (i.val - j.val) = i.val
      omega

private def directDSVSelectedCopyLocalHistoryEquiv
    {L : ℕ} {β : Type*} (j : Fin L) :
    (β × ((Fin j.val → β) × (Fin (L - j.val) → β))) ≃
      (Fin (L + 1) → β) :=
  (Equiv.prodCongr (Equiv.refl β)
    (directDSVRemainingCopyEquiv (β := β) j)).trans
    (Fin.insertNthEquiv (fun _ : Fin (L + 1) => β) j.castSucc)

@[simp] theorem directDSVSelectedCopyLocalHistoryEquiv_hit
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after)) j.castSucc = selected := by
  simp only [directDSVSelectedCopyLocalHistoryEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same]

@[simp] theorem directDSVSelectedCopyLocalHistoryEquiv_before
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) (i : Fin j.val) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after))
        ⟨i.val, by omega⟩ = before i := by
  let k : Fin L := ⟨i.val, by omega⟩
  have earlier : k < j := by
    change i.val < j.val
    exact i.isLt
  have selected_index :
      j.castSucc.succAbove k =
        (⟨i.val, by omega⟩ : Fin (L + 1)) := by
    rw [Fin.succAbove_castSucc_of_lt j k earlier]
    rfl
  unfold directDSVSelectedCopyLocalHistoryEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.insertNthEquiv_apply]
  rw [← selected_index, Fin.insertNth_apply_succAbove]
  change
    (if h : k.val < j.val
      then before ⟨k.val, h⟩
      else after ⟨k.val - j.val, by omega⟩) = before i
  simp only [k, i.isLt, ↓reduceDIte]

@[simp] theorem directDSVSelectedCopyLocalHistoryEquiv_after
    {L : ℕ} {β : Type*} (j : Fin L)
    (selected : β) (before : Fin j.val → β)
    (after : Fin (L - j.val) → β) (i : Fin (L - j.val)) :
    directDSVSelectedCopyLocalHistoryEquiv j
        (selected, (before, after))
        ⟨j.val + 1 + i.val, by omega⟩ = after i := by
  let k : Fin L := ⟨j.val + i.val, by omega⟩
  have later : j ≤ k := by
    change j.val ≤ j.val + i.val
    omega
  have selected_index :
      j.castSucc.succAbove k =
        (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)) := by
    rw [Fin.succAbove_castSucc_of_le j k later]
    apply Fin.ext
    change j.val + i.val + 1 = j.val + 1 + i.val
    omega
  unfold directDSVSelectedCopyLocalHistoryEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.insertNthEquiv_apply]
  rw [← selected_index, Fin.insertNth_apply_succAbove]
  change
    (if h : k.val < j.val
      then before ⟨k.val, h⟩
      else after ⟨k.val - j.val, by omega⟩) = after i
  have not_before : ¬ j.val + i.val < j.val := by omega
  simp only [not_before, ↓reduceDIte, add_tsub_cancel_left, Fin.eta, k]

theorem directDSVRemainingCopyProductSplit
    {M : Type*} [CommMonoid M]
    {L : ℕ} (j : Fin L) (f : Fin L → M) :
    (∏ i : Fin L, f i) =
      (∏ i : Fin j.val, f ⟨i.val, by omega⟩) *
      (∏ i : Fin (L - j.val),
        f ⟨j.val + i.val, by omega⟩) := by
  classical
  have length : j.val + (L - j.val) = L := by omega
  calc
    (∏ i : Fin L, f i) =
        ∏ i : Fin (j.val + (L - j.val)), f (i.cast length) :=
      (Fin.prod_congr' f length).symm
    _ =
        (∏ i : Fin j.val, f ⟨i.val, by omega⟩) *
        (∏ i : Fin (L - j.val),
          f ⟨j.val + i.val, by omega⟩) := by
      rw [Fin.prod_univ_add]
      congr 1

theorem directDSVActualStoppingSelectedHistory_sourceProduct
    {S N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (selectedA selectedB : DSVUniformDensityThresholdLocalIndex N d)
    (beforeA beforeB : Fin j.val →
      DSVUniformDensityThresholdLocalIndex N d)
    (afterA afterB : Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ
        (⟨j.succ,
          directDSVSelectedCopyLocalHistoryEquiv j
            (selectedA, (beforeA, afterA))⟩,
         ⟨j.succ,
          directDSVSelectedCopyLocalHistoryEquiv j
            (selectedB, (beforeB, afterB))⟩) =
      dSVDensityRationalCompleteProjectiveOutcome
          (width (schedule j)) N ξ ζ true true
          (selectedA, selectedB) *
        dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j
          (fun i => (beforeA i, beforeB i)) *
        dSVUniformDensityIndependentSharedState
          (L - j.val) N d (afterA, afterB) := by
  classical
  let a := directDSVSelectedCopyLocalHistoryEquiv j
    (selectedA, (beforeA, afterA))
  let b := directDSVSelectedCopyLocalHistoryEquiv j
    (selectedB, (beforeB, afterB))
  rw [dSVDensityRationalHeterogeneousActualCommonStopPhysicalState_eq_outcomeProduct]
  rw [Fin.prod_univ_succAbove _ j.castSucc]
  rw [directDSVRemainingCopyProductSplit j]
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply]
  rw [dSVUniformDensityIndependentSharedState_apply]
  have hitA : a j.castSucc = selectedA :=
    directDSVSelectedCopyLocalHistoryEquiv_hit j
      selectedA beforeA afterA
  have hitB : b j.castSucc = selectedB :=
    directDSVSelectedCopyLocalHistoryEquiv_hit j
      selectedB beforeB afterB
  have selected :
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j j.castSucc
          (a j.castSucc, b j.castSucc) =
        dSVDensityRationalCompleteProjectiveOutcome
          (width (schedule j)) N ξ ζ true true
          (selectedA, selectedB) := by
    rw [dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_hit,
      hitA, hitB]
  rw [selected]
  simp only [mul_assoc]
  apply congrArg (fun t : ℂ =>
    dSVDensityRationalCompleteProjectiveOutcome
      (width (schedule j)) N ξ ζ true true
      (selectedA, selectedB) * t)
  apply congrArg₂ (fun x y : ℂ => x * y)
  · apply Finset.prod_congr rfl
    intro i _
    let k : Fin L := ⟨i.val, by omega⟩
    have earlier : k < j := by
      change i.val < j.val
      exact i.isLt
    have index : j.castSucc.succAbove k =
        (⟨i.val, by omega⟩ : Fin (L + 1)) := by
      rw [Fin.succAbove_castSucc_of_lt j k earlier]
      rfl
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (j.castSucc.succAbove k)
          (a (j.castSucc.succAbove k),
           b (j.castSucc.succAbove k)) = _
    rw [index]
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (⟨i.val, by omega⟩ : Fin (L + 1))
          (a ⟨i.val, by omega⟩,
           b ⟨i.val, by omega⟩) = _
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (⟨i.val, by omega⟩ : Fin (L + 1))
          (directDSVSelectedCopyLocalHistoryEquiv j
             (selectedA, (beforeA, afterA)) ⟨i.val, by omega⟩,
           directDSVSelectedCopyLocalHistoryEquiv j
             (selectedB, (beforeB, afterB)) ⟨i.val, by omega⟩) = _
    rw [directDSVSelectedCopyLocalHistoryEquiv_before,
      directDSVSelectedCopyLocalHistoryEquiv_before]
  · apply Finset.prod_congr rfl
    intro i _
    let k : Fin L := ⟨j.val + i.val, by omega⟩
    have later : j ≤ k := by
      change j.val ≤ j.val + i.val
      omega
    have index : j.castSucc.succAbove k =
        (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)) := by
      rw [Fin.succAbove_castSucc_of_le j k later]
      apply Fin.ext
      change j.val + i.val + 1 = j.val + 1 + i.val
      omega
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (j.castSucc.succAbove k)
          (a (j.castSucc.succAbove k),
           b (j.castSucc.succAbove k)) = _
    rw [index]
    change
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1))
          (directDSVSelectedCopyLocalHistoryEquiv j
             (selectedA, (beforeA, afterA))
               ⟨j.val + 1 + i.val, by omega⟩,
           directDSVSelectedCopyLocalHistoryEquiv j
             (selectedB, (beforeB, afterB))
               ⟨j.val + 1 + i.val, by omega⟩) = _
    rw [directDSVSelectedCopyLocalHistoryEquiv_after,
      directDSVSelectedCopyLocalHistoryEquiv_after]
    have is_after :
        j.val <
          (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)).val := by
      change j.val < j.val + 1 + i.val
      omega
    rw [dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_after
      width schedule ξ ζ j
      (⟨j.val + 1 + i.val, by omega⟩ : Fin (L + 1)) is_after]

/--
The type used to represent unconditional source physical stopping phase fiber in the exact
sampling construction.
-/
abbrev UnconditionalSourcePhysicalStoppingPhaseFiber
    (S B N d L m : ℕ) :=
  Σ _ : DSVDensityRationalPublicMultiscalePhaseIndex S B ×
    DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d, Fin m

private def unconditionalSourcePhysicalStoppingPhaseHarmonicIndexEquiv
    (S B N d L m : ℕ) :
    ((DSVDensityRationalPublicMultiscalePhaseIndex S B ×
        DSVUniformDensityThresholdWholeHistoryLocalIndex N d L) ×
      Fin m) ≃
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber S B N d L m)
    where
  toFun q := ⟨q.1.2.1, ⟨(q.1.1, q.1.2.2), q.2⟩⟩
  invFun q := ((q.2.1.1, ⟨q.1, q.2.1.2⟩), q.2.2)
  left_inv := by
    intro q
    rcases q with ⟨⟨phase, ⟨flag, history⟩⟩, work⟩
    rfl
  right_inv := by
    intro q
    rcases q with ⟨flag, ⟨⟨phase, history⟩, work⟩⟩
    rfl

private def unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
    (S B N d L m : ℕ) :
    Fin (d *
      dSVDensityRationalPublicMultiscalePhaseResidual
        S B N d L m) ≃
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber S B N d L m) :=
  (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).symm.trans
    (unconditionalSourcePhysicalStoppingPhaseHarmonicIndexEquiv
      S B N d L m)

private def unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
        S B N d L m)
      (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
        S B N d L m))

theorem unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (r s : Fin (L + 1))
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d)
    (i k : Fin m) :
    actualStoppingBranchVector
      (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m
        (dSVDensityRationalHeterogeneousOriginalStoppedState
          S B N d L m width schedule ξ ζ)) r s
      (⟨(φ, a), i⟩, ⟨(ψ, b), k⟩) =
        ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ
          (⟨r, a⟩, ⟨s, b⟩) *
        embezzlementState m (i, k) := by
  change
    dSVDensityRationalHeterogeneousOriginalStoppedState
      S B N d L m width schedule ξ ζ
      (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m ((φ, ⟨r, a⟩), i),
       dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m ((ψ, ⟨s, b⟩), k)) = _
  exact dSVDensityRationalHeterogeneousOriginalStoppedState_apply
    S B N d L m width schedule ξ ζ φ ψ ⟨r, a⟩ ⟨s, b⟩ i k

theorem unconditionalSourcePhysicalStoppingBranch_sigmaContinuation
    {R κ : Type} [Fintype R] [DecidableEq R]
    [Fintype κ] [DecidableEq κ]
    (U V : R → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ ((Σ _ : R, κ) × (Σ _ : R, κ)))
    (r s : R) :
    actualStoppingBranchVector
      (dSVUniformDensityPhysicalAsyncSigmaContinuation U V z)
      r s =
      toLp 2
        ((((U r : Matrix κ κ ℂ) ⊗ₖ (V s : Matrix κ κ ℂ)).mulVec
          (ofLp (actualStoppingBranchVector z r s)))) := by
  classical
  ext ⟨i, j⟩
  simp only [actualStoppingBranchVector, dSVUniformDensityPhysicalAsyncSigmaContinuation,
    coherentSharedRandomControlledUnitary, mulVec, dotProduct, kroneckerMap_apply,
    blockDiagonal'_apply, cast_eq, dite_eq_ite, mul_ite, ite_mul, zero_mul, mul_zero,
    Fintype.sum_prod_type, Fintype.sum_sigma, sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ,
    ↓reduceIte]

private def unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) = Matrix.reindex e e (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

private def unconditionalSelectedMultiscalePhaseIndexEquiv
    {S B : ℕ} (scale : Fin (S + 1)) :
    (Fin B × Fin (Fintype.card (Fin S → Fin B))) ≃
      DSVDensityRationalPublicMultiscalePhaseIndex (S + 1) B :=
  ((Equiv.prodCongr (Equiv.refl (Fin B))
      (Fintype.equivFin (Fin S → Fin B)).symm).trans
    (Fin.insertNthEquiv
      (fun _ : Fin (S + 1) => Fin B) scale)).trans
      (Fintype.equivFin (Fin (S + 1) → Fin B))

theorem unconditionalSelectedMultiscalePhase_card
    (S B : ℕ) :
    Fintype.card
        (DSVDensityRationalPublicMultiscalePhase (S + 1) B) =
      B * Fintype.card (Fin S → Fin B) := by
  simp only [DSVDensityRationalPublicMultiscalePhase, Fintype.card_pi, Fintype.card_fin,
    prod_const, card_univ, pow_succ, Nat.mul_comm]

theorem unconditionalSelectedMultiscalePhase_EPR_apply
    {S B : ℕ} (scale : Fin (S + 1))
    (p q : Fin B)
    (r t : Fin (Fintype.card (Fin S → Fin B))) :
    ePRState
        (Fintype.card
          (DSVDensityRationalPublicMultiscalePhase (S + 1) B))
        (unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (p, r),
         unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (q, t)) =
      ePRState B (p, q) *
        ePRState (Fintype.card (Fin S → Fin B)) (r, t) := by
  classical
  by_cases selected : p = q
  · subst q
    by_cases residual : r = t
    · subst t
      simp only [ePRState, ↓reduceIte]
      rw [unconditionalSelectedMultiscalePhase_card,
        Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg B), mul_inv]
      exact Complex.ofReal_mul _ _
    · have different :
          unconditionalSelectedMultiscalePhaseIndexEquiv
              scale (p, r) ≠
            unconditionalSelectedMultiscalePhaseIndexEquiv
              scale (p, t) := by
          intro equal
          exact residual
            (congrArg Prod.snd
              ((unconditionalSelectedMultiscalePhaseIndexEquiv
                scale).injective equal))
      simp only [ePRState, Fintype.card_pi, Fintype.card_fin, prod_const, card_univ, Nat.cast_pow,
        ofReal_inv, different, ↓reduceIte, residual, mul_zero]
  · have different :
        unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (p, r) ≠
          unconditionalSelectedMultiscalePhaseIndexEquiv
            scale (q, t) := by
        intro equal
        exact selected
          (congrArg Prod.fst
            ((unconditionalSelectedMultiscalePhaseIndexEquiv
              scale).injective equal))
    simp only [ePRState, Fintype.card_pi, Fintype.card_fin, prod_const, card_univ, Nat.cast_pow,
      ofReal_inv, different, ↓reduceIte, selected, mul_ite, zero_mul, mul_zero, ite_self]

private def unconditionalActualMultiscalePhaseIndexEquiv
    {S B : ℕ} (scale : Fin S) :
    (Fin B × Fin (Fintype.card (Fin (S - 1) → Fin B))) ≃
      DSVDensityRationalPublicMultiscalePhaseIndex S B := by
  cases S with
  | zero => exact Fin.elim0 scale
  | succ S =>
      exact unconditionalSelectedMultiscalePhaseIndexEquiv
        (S := S) scale

theorem unconditionalActualMultiscalePhase_EPR_apply
    {S B : ℕ} (scale : Fin S)
    (p q : Fin B)
    (r t : Fin (Fintype.card (Fin (S - 1) → Fin B))) :
    ePRState
        (Fintype.card
          (DSVDensityRationalPublicMultiscalePhase S B))
        (unconditionalActualMultiscalePhaseIndexEquiv
            scale (p, r),
         unconditionalActualMultiscalePhaseIndexEquiv
            scale (q, t)) =
      ePRState B (p, q) *
        ePRState (Fintype.card (Fin (S - 1) → Fin B))
          (r, t) := by
  cases S with
  | zero => exact Fin.elim0 scale
  | succ S =>
      exact unconditionalSelectedMultiscalePhase_EPR_apply
        scale p q r t

private def unconditionalSourcePhysicalCleanedReindexedUnitary
    {ι κ : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ)
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ := by
  classical
  let M : Matrix ι ι ℂ := U.val
  refine ⟨Matrix.reindex e e M, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  have compatible :
      star (Matrix.reindex e e M) =
        Matrix.reindex e e (star M) := by
    ext i j
    simp only [reindex_apply, star_apply, submatrix_apply, RCLike.star_def, star_eq_conjTranspose,
      conjTranspose_apply]
  rw [compatible]
  change
    (Matrix.reindexRingEquiv ℂ e) (star M) *
      (Matrix.reindexRingEquiv ℂ e) M = 1
  rw [← (Matrix.reindexRingEquiv ℂ e).map_mul,
    (Matrix.mem_unitaryGroup_iff').mp U.property]
  exact (Matrix.reindexRingEquiv ℂ e).map_one

private def unconditionalSourcePhysicalCleanedTargetFirstUnitary
    (S B N d L m : ℕ)
    (U : Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ) :
    Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) ℂ :=
  unconditionalSourcePhysicalCleanedReindexedUnitary
    (unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
      S B N d L m) U

/-- The source object for unconditional source physical cleaned stopping fixed. -/
def unconditionalSourcePhysicalCleanedStoppingFixedSource
    (S B N d L m : ℕ) :
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m)) :=
  unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
    S B N d L m
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource
      S B N d L m)

theorem unconditionalSourcePhysicalCleanedStoppingFixedSource_norm
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m) :
    ‖unconditionalSourcePhysicalCleanedStoppingFixedSource
      S B N d L m‖ = 1 := by
  unfold unconditionalSourcePhysicalCleanedStoppingFixedSource
  rw [LinearIsometryEquiv.norm_map]
  exact
    dSVDensityRationalPublicMultiscalePhaseTargetFirstPreparedSource_norm
      phases grid dimension harmonic

theorem
    unconditionalSourcePhysicalCleanedStoppingLocalAction_reindex
    {S B N d L m : ℕ}
    (U V : Matrix.unitaryGroup
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m)) ℂ)
    (z : EuclideanSpace ℂ
      (Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m) ×
       Fin (d *
        dSVDensityRationalPublicMultiscalePhaseResidual
          S B N d L m))) :
    actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m U)
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m V)
      (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m z) =
      unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m (localUnitaryAction U V z) := by
  classical
  let e := unconditionalSourcePhysicalStoppingTargetFirstIndexEquiv
    S B N d L m
  ext ⟨a, b⟩
  change
    (∑ q :
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) ×
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m),
      (U : Matrix _ _ ℂ) (e.symm a) (e.symm q.1) *
        (V : Matrix _ _ ℂ) (e.symm b) (e.symm q.2) *
        z (e.symm q.1, e.symm q.2)) =
      ∑ q :
        Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m) ×
        Fin (d *
          dSVDensityRationalPublicMultiscalePhaseResidual
            S B N d L m),
        (U : Matrix _ _ ℂ) (e.symm a) q.1 *
          (V : Matrix _ _ ℂ) (e.symm b) q.2 * z q
  simpa only [Equiv.prodCongr_apply, Prod.map_fst, Equiv.symm_apply_apply, Prod.map_snd,
    Prod.mk.eta] using
    (Equiv.sum_comp (Equiv.prodCongr e e)
      (fun q :
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) ×
        (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            S B N d L m) =>
        (U : Matrix _ _ ℂ) (e.symm a) (e.symm q.1) *
          (V : Matrix _ _ ℂ) (e.symm b) (e.symm q.2) *
          z (e.symm q.1, e.symm q.2))).symm

theorem
    unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          S B N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          S B N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        S B N d L m) =
      unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
        S B N d L m
        (dSVDensityRationalHeterogeneousOriginalStoppedState
          S B N d L m width schedule ξ ζ) := by
  unfold unconditionalSourcePhysicalCleanedStoppingFixedSource
  rw [unconditionalSourcePhysicalCleanedStoppingLocalAction_reindex]
  rfl

theorem
    unconditionalSourcePhysicalCleanedStoppingFixedSource_branch_apply
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (r s : Fin (L + 1))
    (φ ψ : DSVDensityRationalPublicMultiscalePhaseIndex S B)
    (a b : DSVUniformDensityIndependentHistoryLocalIndex
      (L + 1) N d)
    (i k : Fin m) :
    actualStoppingBranchVector
      (actualStoppingQuestionLocalAction
        (unconditionalSourcePhysicalCleanedTargetFirstUnitary
          S B N d L m
          (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
            S B N d L m width schedule ξ))
        (unconditionalSourcePhysicalCleanedTargetFirstUnitary
          S B N d L m
          (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
            S B N d L m width schedule ζ))
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          S B N d L m)) r s
      (⟨(φ, a), i⟩, ⟨(ψ, b), k⟩) =
        ePRState
          (Fintype.card
            (DSVDensityRationalPublicMultiscalePhase S B))
          (φ, ψ) *
        dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ (⟨r, a⟩, ⟨s, b⟩) *
        embezzlementState m (i, k) := by
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction]
  exact
    unconditionalSourcePhysicalStoppingTargetFirst_branch_apply
      width schedule ξ ζ r s φ ψ a b i k

private def unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
    {L : ℕ} (j : Fin L) (β : Type*) :
    (Fin (L + 1) → β) ≃
      β × ((Fin j.val → β) × (Fin (L - j.val) → β)) where
  toFun f :=
    (f j.castSucc,
      (fun i => f ⟨i.val, by omega⟩,
       fun i => f ⟨j.val + 1 + i.val, by omega⟩))
  invFun q i :=
    if before : i.val < j.val then
      q.2.1 ⟨i.val, before⟩
    else if hit : i.val = j.val then q.1
    else q.2.2 ⟨i.val - (j.val + 1), by omega⟩
  left_inv := by
    intro f
    funext i
    dsimp
    split <;> rename_i before
    · apply congrArg f
      apply Fin.ext
      rfl
    · split <;> rename_i hit
      · apply congrArg f
        apply Fin.ext
        exact hit.symm
      · apply congrArg f
        apply Fin.ext
        simp only
        omega
  right_inv := by
    intro q
    rcases q with ⟨selected, before, later⟩
    apply Prod.ext
    · simp only [Fin.val_castSucc, lt_self_iff_false, ↓reduceDIte]
    · apply Prod.ext
      · funext i
        simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
      · funext i
        have not_before : ¬ j.val + 1 + i.val < j.val := by omega
        have not_hit : ¬ j.val + 1 + i.val = j.val := by omega
        simp only [not_before, ↓reduceDIte, not_hit, add_tsub_cancel_left, Fin.eta]

/-- The finite equivalence encoding unconditional source physical cleaned full local index. -/
def unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
    {P R : Type*} {B N d L m : ℕ}
    (phaseSplit : P ≃ Fin B × R) (j : Fin L) :
    (Σ _ : P × (Fin (L + 1) →
        DSVUniformDensityThresholdLocalIndex N d), Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m ×
        ((Fin j.val →
          DSVUniformDensityThresholdLocalIndex N d) ×
         ((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) × R)) where
  toFun q :=
    let phase := phaseSplit q.1.1
    let history :=
      unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
        (DSVUniformDensityThresholdLocalIndex N d) q.1.2
    (⟨(phase.1, history.1.2),
       finProdFinEquiv (history.1.1, q.2)⟩,
      (history.2.1, (history.2.2, phase.2)))
  invFun q :=
    let work := finProdFinEquiv.symm q.1.2
    ⟨(phaseSplit.symm (q.1.1.1, q.2.2.2),
      (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
        (DSVUniformDensityThresholdLocalIndex N d)).symm
        (⟨work.1, q.1.1.2⟩, (q.2.1, q.2.2.1))),
      work.2⟩
  left_inv := by
    rintro ⟨⟨phase, history⟩, work⟩
    simp only [Equiv.symm_apply_apply]
    change
      (⟨(phaseSplit.symm
          ((phaseSplit phase).1, (phaseSplit phase).2),
        (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
          (DSVUniformDensityThresholdLocalIndex N d)).symm
          ((unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
            (DSVUniformDensityThresholdLocalIndex N d) history).1,
           ((unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
             (DSVUniformDensityThresholdLocalIndex N d) history).2.1,
            (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
              (DSVUniformDensityThresholdLocalIndex N d) history).2.2))),
        work⟩ :
        Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m) =
          ⟨(phase, history), work⟩
    simp only [Prod.mk.eta, Equiv.symm_apply_apply,
      unconditionalSourcePhysicalCleanedSelectedHistoryEquiv]
  right_inv := by
    rintro ⟨⟨⟨phase, spectral⟩, packed⟩,
      ⟨before, ⟨later, remainder⟩⟩⟩
    simp only [Equiv.apply_symm_apply, finProdFinEquiv_symm_apply, Prod.mk.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and, and_true]
    exact finProdFinEquiv.apply_symm_apply packed

@[simp] theorem unconditionalSourcePhysicalCleanedSelectedHistoryEquiv_hit
    {L : ℕ} (j : Fin L) (β : Type*) (f : Fin (L + 1) → β) :
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
      j β f).1 = f j.castSucc := by
  rfl

private def unconditionalSourcePhysicalCleanedFullBilateralRegroup
    {R : Type*} {B N d L m : ℕ} (j : Fin L) :
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
       ((Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
        ((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) × R))) ×
     (UnconditionalSelectedCopyLocalIndex B d N m ×
       ((Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
        ((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) × R)))) ≃
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) ×
      ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) ×
       (((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) ×
         (Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d)) ×
        (R × R)))) where
  toFun q :=
    ((q.1.1, q.2.1),
      ((fun i => (q.1.2.1 i, q.2.2.1 i)),
       ((q.1.2.2.1, q.2.2.2.1),
        (q.1.2.2.2, q.2.2.2.2))))
  invFun q :=
    ((q.1.1,
       ((fun i => (q.2.1 i).1),
        (q.2.2.1.1, q.2.2.2.1))),
     (q.1.2,
       ((fun i => (q.2.1 i).2),
        (q.2.2.1.2, q.2.2.2.2))))
  left_inv := by
    rintro ⟨⟨selectedA, beforeA, laterA, phaseA⟩,
      ⟨selectedB, beforeB, laterB, phaseB⟩⟩
    simp only
  right_inv := by
    rintro ⟨⟨selectedA, selectedB⟩,
      ⟨before, ⟨⟨laterA, laterB⟩, ⟨phaseA, phaseB⟩⟩⟩⟩
    simp only [Prod.mk.eta]

/-- The linear isometry implementing unconditional source physical cleaned full bilateral state. -/
def unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
    {P R : Type*} [Fintype P] [Fintype R]
    {B N d L m : ℕ}
    (phaseSplit : P ≃ Fin B × R) (j : Fin L) :
    EuclideanSpace ℂ
      ((Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m) ×
       (Σ _ : P × (Fin (L + 1) →
          DSVUniformDensityThresholdLocalIndex N d), Fin m)) ≃ₗᵢ[ℂ]
    EuclideanSpace ℂ
      ((UnconditionalSelectedCopyLocalIndex B d N m ×
        UnconditionalSelectedCopyLocalIndex B d N m) ×
       ((Fin j.val →
         (DSVUniformDensityThresholdLocalIndex N d ×
          DSVUniformDensityThresholdLocalIndex N d)) ×
        (((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) ×
          (Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d)) ×
         (R × R)))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodCongr
      (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
        phaseSplit j)
      (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
        phaseSplit j)).trans
      (unconditionalSourcePhysicalCleanedFullBilateralRegroup
        (R := R) (B := B) (N := N) (d := d) (m := m) j))

private def unconditionalSourcePhysicalCleanedSelectedStageUnitary
    {B N d m : ℕ}
    (Q : ℕ) (w : ℝ) (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  dSVDensityRationalPublicBucketCoherentPhaseLocalUnitary
    (dSVDensityRationalPhysicalAcceptedRank w N ξ)
    (dSVDensityRationalPublicLogRankBucket Q)
    A

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

private abbrev UnconditionalActualCleanedSelectedRetainedIndex
    {N d L : ℕ} (j : Fin L) (R : Type) :=
  (Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
    ((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) × R)

private def unconditionalActualCleanedSelectedTensorUnitary
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ),
    Matrix.kronecker_mem_unitary U.property V.property⟩

private def unconditionalActualCleanedSelectedStageBucketUnitary
    {B N d m : ℕ} (Q : ℕ) (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourcePhysicalCleanedSelectedStageUnitary Q w ξ A

private def unconditionalActualCleanedSelectedStagePhysicalIndexEquiv
    (B N d m : ℕ) :
    (Σ _ : Fin B,
      DSVUniformDensityThresholdLocalIndex N d × Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m where
  toFun q :=
    ⟨(q.1, q.2.1.2), finProdFinEquiv (q.2.1.1, q.2.2)⟩
  invFun q :=
    let work := finProdFinEquiv.symm q.2
    ⟨q.1.1, (⟨work.1, q.1.2⟩, work.2)⟩
  left_inv := by
    rintro ⟨phase, ⟨⟨threshold, spectral⟩, harmonic⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨phase, spectral⟩, work⟩
    simp only [finProdFinEquiv_symm_apply, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact finProdFinEquiv.apply_symm_apply work

private def unconditionalActualCleanedSelectedStageSpectralUnitary
    {B N d m : ℕ}
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    (unconditionalActualCleanedSelectedStagePhysicalIndexEquiv
      B N d m)
    (coherentSharedRandomControlledUnitary
      (fun _ : Fin B =>
        unconditionalActualCleanedSelectedTensorUnitary
          spectral (1 : Matrix.unitaryGroup (Fin m) ℂ)))

private def unconditionalActualCleanedSelectedFullStageUnitary
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ := by
  let retained :=
    UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R
  let selected := UnconditionalSelectedCopyLocalIndex B d N m
  let regroup :
      UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m ≃ (Σ _ : retained, selected) :=
    (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
      ((Equiv.prodComm selected retained).trans
        (Equiv.sigmaEquivProd retained selected).symm)
  exact
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      regroup.symm
      (coherentSharedRandomControlledUnitary
        (fun _ : retained =>
          unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectral))

private def unconditionalActualCleanedSelectedFiniteStageDecoder
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Fin (L + 1) → Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ :=
  Fin.cases 1 (fun j =>
    unconditionalActualCleanedSelectedFullStageUnitary
      phaseSplit Q width schedule ξ spectral A j)

@[simp] theorem
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    unconditionalActualCleanedSelectedFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A j.succ =
      unconditionalActualCleanedSelectedFullStageUnitary
        phaseSplit Q width schedule ξ spectral A j := by
  simp only [unconditionalActualCleanedSelectedFiniteStageDecoder, Fin.cases_succ]

theorem unconditionalActualCleanedSelectedMatchedStoppingBranch
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    actualStoppingBranchVector
      (dSVUniformDensityPhysicalAsyncSigmaContinuation
        (unconditionalActualCleanedSelectedFiniteStageDecoder
          phaseSplit Q width schedule ξ
          (dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ) A)
        (unconditionalActualCleanedSelectedFiniteStageDecoder
          phaseSplit Q width schedule ζ
          ((dSVUniformDensityBobHistoryCopyBasis (N := N) ζ)⁻¹) C)
        (actualStoppingQuestionLocalAction
          (unconditionalSourcePhysicalCleanedTargetFirstUnitary
            S B N d L m
            (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
              S B N d L m width schedule ξ))
          (unconditionalSourcePhysicalCleanedTargetFirstUnitary
            S B N d L m
            (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
              S B N d L m width schedule ζ))
          (unconditionalSourcePhysicalCleanedStoppingFixedSource
            S B N d L m))) j.succ j.succ =
      toLp 2
        ((((unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ξ
              (dSVUniformDensityAliceHistorySpectralCopy
                (N := N) ξ) A j :
            Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
              S B N d L m)
              (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m) ℂ) ⊗ₖ
          (unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ζ
              ((dSVUniformDensityBobHistoryCopyBasis
                (N := N) ζ)⁻¹) C j :
            Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
              S B N d L m)
              (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m) ℂ)).mulVec
            (ofLp
              (actualStoppingBranchVector
                (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
                  S B N d L m
                  (dSVDensityRationalHeterogeneousOriginalStoppedState
                    S B N d L m width schedule ξ ζ))
                j.succ j.succ)))) := by
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction,
    unconditionalSourcePhysicalStoppingBranch_sigmaContinuation,
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ,
    unconditionalActualCleanedSelectedFiniteStageDecoder_succ]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The type used to represent unconditional source flag controlled retained index in the exact
sampling construction.
-/
abbrev UnconditionalSourceFlagControlledRetainedIndex
    {N d L : ℕ} (j : Fin L) (R : Type) :=
  (Fin j.val → DSVUniformDensityThresholdLocalIndex N d) ×
    ((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) × R)

private def unconditionalSourceFlagControlledTensorUnitary
    {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ),
    Matrix.kronecker_mem_unitary U.property V.property⟩

private def unconditionalSourceFlagControlledStagePhysicalIndexEquiv
    (B N d m : ℕ) :
    (Σ _ : Fin B,
      DSVUniformDensityThresholdLocalIndex N d × Fin m) ≃
      UnconditionalSelectedCopyLocalIndex B d N m where
  toFun q :=
    ⟨(q.1, q.2.1.2), finProdFinEquiv (q.2.1.1, q.2.2)⟩
  invFun q :=
    let work := finProdFinEquiv.symm q.2
    ⟨q.1.1, (⟨work.1, q.1.2⟩, work.2)⟩
  left_inv := by
    rintro ⟨phase, ⟨⟨threshold, spectral⟩, harmonic⟩⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨phase, spectral⟩, work⟩
    simp only [finProdFinEquiv_symm_apply, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact finProdFinEquiv.apply_symm_apply work

private def unconditionalSourceFlagControlledStageSpectralUnitary
    {B N d m : ℕ}
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
    (unconditionalSourceFlagControlledStagePhysicalIndexEquiv
      B N d m)
    (coherentSharedRandomControlledUnitary
      (fun _ : Fin B =>
        unconditionalSourceFlagControlledTensorUnitary
          spectral (1 : Matrix.unitaryGroup (Fin m) ℂ)))

private def unconditionalSourceFlagControlledStageBucketUnitary
    {B N d m : ℕ} (Q : ℕ) (w : ℝ)
    (ξ : BipartiteUnitVector d)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Matrix.unitaryGroup
      (UnconditionalSelectedCopyLocalIndex B d N m) ℂ :=
  coherentSharedRandomControlledUnitary
    (fun q : Fin B × Fin d =>
      A q.1 (dSVDensityRationalPublicLogRankBucket Q q.1
        (dSVDensityRationalPhysicalAcceptedRank w N ξ q.2)))

private def unconditionalSourceFlagControlledFullStageUnitary
    {S B N d L m : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ := by
  let retained :=
    UnconditionalSourceFlagControlledRetainedIndex
      (N := N) (d := d) j R
  let selected := UnconditionalSelectedCopyLocalIndex B d N m
  let regroup :
      UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m ≃ (Σ _ : retained, selected) :=
    (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
      ((Equiv.prodComm selected retained).trans
        (Equiv.sigmaEquivProd retained selected).symm)
  exact
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      regroup.symm
      (coherentSharedRandomControlledUnitary
        (fun _ : retained =>
          unconditionalSourceFlagControlledStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalSourceFlagControlledStageSpectralUnitary
            (B := B) (m := m) spectral))

private def unconditionalSourceFlagControlledFiniteStageDecoder
    {S B N d L m : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    Fin (L + 1) → Matrix.unitaryGroup
      (UnconditionalSourcePhysicalStoppingPhaseFiber
        S B N d L m) ℂ :=
  Fin.cases 1 (fun j =>
    unconditionalSourceFlagControlledFullStageUnitary
      phaseSplit Q width schedule ξ spectral A j)

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

private def unconditionalActualPhysicalMixedAcceptedRawStage
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  toLp 2 fun q =>
    ePRState B (q.1.1.1, q.2.1.1) *
      dSVDensityRationalPhysicalAcceptedOutcome w N ξ ζ
        (⟨(finProdFinEquiv.symm q.1.2).1, q.1.1.2⟩,
         ⟨(finProdFinEquiv.symm q.2.2).1, q.2.1.2⟩) *
      embezzlementState m
        ((finProdFinEquiv.symm q.1.2).2,
         (finProdFinEquiv.symm q.2.2).2)

theorem unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply
    {B N d m : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (φ ψ : Fin B) (i j : Fin d)
    (k l : Fin N) (a b : Fin m) :
    (unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) U :
        Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
          (UnconditionalSelectedCopyLocalIndex B d N m) ℂ)
      ⟨(φ, i), finProdFinEquiv (k, a)⟩
      ⟨(ψ, j), finProdFinEquiv (l, b)⟩ =
        if φ = ψ then
          (U : Matrix
              (DSVUniformDensityThresholdLocalIndex N d)
              (DSVUniformDensityThresholdLocalIndex N d) ℂ)
            ⟨k, i⟩ ⟨l, j⟩ *
            (if a = b then (1 : ℂ) else 0)
        else 0 := by
  classical
  have threshold_a : (finProdFinEquiv (k, a)).divNat = k := by
    change (finProdFinEquiv.symm (finProdFinEquiv (k, a))).1 = k
    rw [Equiv.symm_apply_apply]
  have harmonic_a : (finProdFinEquiv (k, a)).modNat = a := by
    change (finProdFinEquiv.symm (finProdFinEquiv (k, a))).2 = a
    rw [Equiv.symm_apply_apply]
  have threshold_b : (finProdFinEquiv (l, b)).divNat = l := by
    change (finProdFinEquiv.symm (finProdFinEquiv (l, b))).1 = l
    rw [Equiv.symm_apply_apply]
  have harmonic_b : (finProdFinEquiv (l, b)).modNat = b := by
    change (finProdFinEquiv.symm (finProdFinEquiv (l, b))).2 = b
    rw [Equiv.symm_apply_apply]
  simp only [unconditionalActualCleanedSelectedStageSpectralUnitary,
    unconditionalSourceFixedPureStoppedSigmaReindexedUnitary,
    unconditionalActualCleanedSelectedStagePhysicalIndexEquiv, finProdFinEquiv_symm_apply,
    coherentSharedRandomControlledUnitary, unconditionalActualCleanedSelectedTensorUnitary,
    OneMemClass.coe_one, reindex_apply, Equiv.symm_mk, Equiv.coe_fn_mk, submatrix_apply,
    threshold_a, harmonic_a, threshold_b, harmonic_b, blockDiagonal'_apply, cast_eq,
    kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, dite_eq_ite]

theorem
    unconditionalActualPhysicalMixedAcceptedSpectralGauge_sum
    {N d : ℕ}
    (f : DSVUniformDensityThresholdLocalIndex N d →
      DSVUniformDensityThresholdLocalIndex N d → ℂ) :
    (∑ i : Fin d, ∑ k : Fin N,
      ∑ j : Fin d, ∑ l : Fin N,
        f ⟨k, i⟩ ⟨l, j⟩) =
      ∑ x : DSVUniformDensityThresholdLocalIndex N d,
        ∑ y : DSVUniformDensityThresholdLocalIndex N d,
          f x y := by
  classical
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem unconditionalActualPhysicalMixedAcceptedSpectralGauge_stage
    {B N d m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d) :
    toLp 2
      ((((unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m)
            (dSVUniformDensityAliceHistorySpectralCopy
              (N := N) ξ) :
            Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
              (UnconditionalSelectedCopyLocalIndex B d N m) ℂ) ⊗ₖ
          (unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m)
            ((dSVUniformDensityBobHistoryCopyBasis
              (N := N) ζ)⁻¹) :
            Matrix (UnconditionalSelectedCopyLocalIndex B d N m)
              (UnconditionalSelectedCopyLocalIndex B d N m) ℂ)).mulVec
        (ofLp (unconditionalActualPhysicalMixedAcceptedRawStage
          (B := B) (m := m) w ξ ζ)))) =
      dSVDensityRationalPublicBucketPhysicalCoherentMixedState
        (N := N) (B := B) w m ξ ζ := by
  classical
  ext ⟨⟨⟨φ, i⟩, packedA⟩, ⟨⟨ψ, j⟩, packedB⟩⟩
  obtain ⟨⟨k, a⟩, rfl⟩ := finProdFinEquiv.surjective packedA
  obtain ⟨⟨l, b⟩, rfl⟩ := finProdFinEquiv.surjective packedB
  have reindex_packed (f : Fin (N * m) → ℂ) :
      (∑ packed : Fin (N * m), f packed) =
        ∑ packed : Fin N × Fin m, f (finProdFinEquiv packed) :=
    (Equiv.sum_comp finProdFinEquiv f).symm
  rw [unconditionalPhysicalAcceptedCoherentStage_apply
    width grid ξ ζ φ ψ i j k l a b]
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Fintype.sum_sigma]
  simp_rw [reindex_packed]
  simp only [Fintype.sum_prod_type]
  simp_rw [unconditionalActualPhysicalMixedAcceptedSpectralGauge_apply]
  simp only [
    unconditionalActualPhysicalMixedAcceptedRawStage,
    Equiv.symm_apply_apply, ite_mul, mul_ite, zero_mul, mul_zero,
    mul_one]
  simp only [UnitaryGroup.inv_val, star_apply, RCLike.star_def, ePRState, ofReal_inv, ite_mul,
    zero_mul, mul_comm, mul_ite, mul_left_comm, mul_assoc, sum_ite_irrel, sum_ite_eq, mem_univ,
    ↓reduceIte, sum_const_zero, dSVDensityRationalCanonicalPrefixSpectralOutcome, mulVec,
    dotProduct, kroneckerMap_apply, Fintype.sum_prod_type, mul_sum]
  let alice : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityAliceHistorySpectralCopy (N := N) ξ
  let bob : Matrix
      (DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    dSVUniformDensityBobHistoryCopyBasis (N := N) ζ
  let summand :
      DSVUniformDensityThresholdLocalIndex N d →
        DSVUniformDensityThresholdLocalIndex N d → ℂ :=
    fun x y =>
      (↑(Real.sqrt (B : ℝ)) : ℂ)⁻¹ *
        (embezzlementState m (a, b) *
          (dSVDensityRationalPhysicalAcceptedOutcome
            w N ξ ζ (x, y) *
            (alice ⟨k, i⟩ x * (starRingEnd ℂ) (bob y ⟨l, j⟩))))
  by_cases phases : φ = ψ
  · simp only [ite_eq_left phases]
    exact unconditionalActualPhysicalMixedAcceptedSpectralGauge_sum
      summand
  · simp only [ite_eq_right phases]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/--
The type used to represent unconditional actual canonical retained phase index in the exact
sampling construction.
-/
abbrev UnconditionalActualCanonicalRetainedPhaseIndex (S B : ℕ) :=
  Fin (Fintype.card (Fin (S - 1) → Fin B))

/--
The unconditional actual canonical retained phase tail construction used in the quantum
parallel-repetition argument.
-/
def unconditionalActualCanonicalRetainedPhaseTail
    {S B N d L : ℕ} (j : Fin L) :
    EuclideanSpace ℂ
      (((Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d) ×
        (Fin (L - j.val) →
          DSVUniformDensityThresholdLocalIndex N d)) ×
       (UnconditionalActualCanonicalRetainedPhaseIndex S B ×
        UnconditionalActualCanonicalRetainedPhaseIndex S B)) :=
  toLp 2 fun q =>
    dSVUniformDensityIndependentSharedState (L - j.val) N d q.1 *
      ePRState
        (Fintype.card (Fin (S - 1) → Fin B)) q.2

private def unconditionalActualCanonicalFixedSourceMatchedBranch
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ×
       UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m) :=
  actualStoppingBranchVector
    (actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          S B N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        S B N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          S B N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        S B N d L m)) j.succ j.succ

private def unconditionalActualCanonicalRawSelectedPhysicalStage
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      (UnconditionalSelectedCopyLocalIndex B d N m ×
       UnconditionalSelectedCopyLocalIndex B d N m) :=
  toLp 2 fun q =>
    ePRState B (q.1.1.1, q.2.1.1) *
      dSVDensityRationalPhysicalAcceptedOutcome w N ξ ζ
        (⟨(finProdFinEquiv.symm q.1.2).1, q.1.1.2⟩,
         ⟨(finProdFinEquiv.symm q.2.2).1, q.2.1.2⟩) *
      embezzlementState m
        ((finProdFinEquiv.symm q.1.2).2,
         (finProdFinEquiv.symm q.2.2).2)

theorem unconditionalActualCanonicalCleanedHistorySymm_eq_direct
    {L : ℕ} (j : Fin L) (β : Type*)
    (selected : β) (before : Fin j.val → β)
    (later : Fin (L - j.val) → β) :
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
      j β).symm (selected, (before, later)) =
      directDSVSelectedCopyLocalHistoryEquiv
        j (selected, (before, later)) := by
  apply (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv
    j β).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact
      (directDSVSelectedCopyLocalHistoryEquiv_hit
        j selected before later).symm
  · apply Prod.ext
    · funext i
      exact
        (directDSVSelectedCopyLocalHistoryEquiv_before
          j selected before later i).symm
    · funext i
      exact
        (directDSVSelectedCopyLocalHistoryEquiv_after
          j selected before later i).symm

theorem unconditionalActualCanonicalFullSource_eq_rawSelectedStage
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualMultiscalePhaseIndexEquiv
          (schedule j)).symm j
        (unconditionalActualCanonicalFixedSourceMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j) =
      unconditionalMatchedVerifierTensor
        (unconditionalActualCanonicalRawSelectedPhysicalStage
          (B := B) (m := m) (width (schedule j)) ξ ζ)
        (unconditionalSelectedCopyRetainedWork
          (N := N) width schedule ξ ζ j
          (unconditionalActualCanonicalRetainedPhaseTail
            (S := S) (B := B) j)) := by
  classical
  ext ⟨⟨⟨⟨p, i⟩, packedA⟩, ⟨⟨q, k⟩, packedB⟩⟩,
    ⟨before, ⟨⟨afterA, afterB⟩, ⟨tailA, tailB⟩⟩⟩⟩
  let a := finProdFinEquiv.symm packedA
  let b := finProdFinEquiv.symm packedB
  let historyA :=
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
      (DSVUniformDensityThresholdLocalIndex N d)).symm
      (⟨a.1, i⟩,
       ((fun t => (before t).1), afterA))
  let historyB :=
    (unconditionalSourcePhysicalCleanedSelectedHistoryEquiv j
      (DSVUniformDensityThresholdLocalIndex N d)).symm
      (⟨b.1, k⟩,
       ((fun t => (before t).2), afterB))
  change
    unconditionalActualCanonicalFixedSourceMatchedBranch
        width schedule ξ ζ j
        (⟨(unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j) (p, tailA), historyA), a.2⟩,
         ⟨(unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j) (q, tailB), historyB), b.2⟩) =
      unconditionalActualCanonicalRawSelectedPhysicalStage
        (width (schedule j)) ξ ζ
        (⟨(p, i), packedA⟩, ⟨(q, k), packedB⟩) *
      unconditionalSelectedCopyRetainedWork
        width schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail j)
        (before, ((afterA, afterB), (tailA, tailB)))
  unfold unconditionalActualCanonicalFixedSourceMatchedBranch
  rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_branch_apply
    width schedule ξ ζ j.succ j.succ]
  rw [unconditionalActualMultiscalePhase_EPR_apply
    (schedule j) p q tailA tailB]
  change
    (ePRState B (p, q) *
       ePRState (Fintype.card (Fin (S - 1) → Fin B))
         (tailA, tailB)) *
       dSVDensityRationalHeterogeneousActualPhysicalState
         N width schedule ξ ζ
         (⟨j.succ, historyA⟩, ⟨j.succ, historyB⟩) *
       embezzlementState m (a.2, b.2) =
      (ePRState B (p, q) *
        dSVDensityRationalPhysicalAcceptedOutcome
          (width (schedule j)) N ξ ζ (⟨a.1, i⟩, ⟨b.1, k⟩) *
        embezzlementState m (a.2, b.2)) *
        (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j before *
          (dSVUniformDensityIndependentSharedState
             (L - j.val) N d (afterA, afterB) *
           ePRState (Fintype.card (Fin (S - 1) → Fin B))
             (tailA, tailB)))
  rw [show historyA =
    directDSVSelectedCopyLocalHistoryEquiv j
      (⟨a.1, i⟩, ((fun t => (before t).1), afterA)) from
        unconditionalActualCanonicalCleanedHistorySymm_eq_direct
          j _ _ _ _,
    show historyB =
    directDSVSelectedCopyLocalHistoryEquiv j
      (⟨b.1, k⟩, ((fun t => (before t).2), afterB)) from
        unconditionalActualCanonicalCleanedHistorySymm_eq_direct
          j _ _ _ _]
  rw [directDSVActualStoppingSelectedHistory_sourceProduct]
  unfold dSVDensityRationalPhysicalAcceptedOutcome
  ring

theorem unconditionalActualCanonicalRawSelectedPhysicalStage_eq
    {B N d m : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) :
    unconditionalActualCanonicalRawSelectedPhysicalStage
        (B := B) (N := N) (m := m) w ξ ζ =
      unconditionalActualPhysicalMixedAcceptedRawStage
        (B := B) (N := N) (m := m) w ξ ζ := by
  rfl

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The positive operator-valued measurement implementing direct DSV actual reindexed retained. -/
def directDSVActualReindexedRetainedPOVM
    {C s t ι : Type*}
    [Fintype C] [Fintype s] [Fintype t] [Fintype ι]
    [DecidableEq s] [DecidableEq t] [DecidableEq ι]
    (e : ι ≃ s × t)
    (P : POVM C s) : POVM C ι :=
  reindexedPOVM e.symm (purificationAlicePOVM (k := t) P)

@[simp] theorem directDSVActualReindexedRetainedPOVM_effect
    {C s t ι : Type*}
    [Fintype C] [Fintype s] [Fintype t] [Fintype ι]
    [DecidableEq s] [DecidableEq t] [DecidableEq ι]
    (e : ι ≃ s × t)
    (P : POVM C s) (a : C) (i j : ι) :
    (directDSVActualReindexedRetainedPOVM e P).effect a i j =
      P.effect a (e i).1 (e j).1 *
        if (e i).2 = (e j).2 then 1 else 0 := by
  change
    (P.effect a ⊗ₖ (1 : Matrix t t ℂ)) (e i) (e j) = _
  simp only [kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]

/-- The finite equivalence encoding direct DSV actual bilateral retained index. -/
def directDSVActualBilateralRetainedIndexEquiv
    {s t u v ι κ : Type*}
    (eA : ι ≃ s × t) (eB : κ ≃ u × v) :
    (ι × κ) ≃ ((s × u) × (t × v)) :=
  (Equiv.prodCongr eA eB).trans
    (Equiv.prodProdProdComm s t u v)

/-- The measurement effect for direct DSV actual local POVM winning. -/
def directDSVActualLocalPOVMWinningEffect
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B)
    (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) : Matrix (s × t) (s × t) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      PA.effect a ⊗ₖ PB.effect b
    else 0

theorem directDSVActualReindexedRetainedPOVMWinningEffect
    {X Y A B s t u v ι κ : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [Fintype u] [Fintype v]
    [Fintype ι] [Fintype κ]
    [DecidableEq s] [DecidableEq t] [DecidableEq u] [DecidableEq v]
    [DecidableEq ι] [DecidableEq κ]
    (G : Game X Y A B)
    (eA : ι ≃ s × t) (eB : κ ≃ u × v)
    (PA : POVM A s) (PB : POVM B u)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G
        (directDSVActualReindexedRetainedPOVM eA PA)
        (directDSVActualReindexedRetainedPOVM eB PB)
        x y =
      Matrix.reindex
        (directDSVActualBilateralRetainedIndexEquiv eA eB).symm
        (directDSVActualBilateralRetainedIndexEquiv eA eB).symm
        (directDSVActualLocalPOVMWinningEffect G PA PB x y ⊗ₖ
          (1 : Matrix (t × v) (t × v) ℂ)) := by
  classical
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases alice_work : (eA i).2 = (eA j).2 <;>
    by_cases bob_work : (eB k).2 = (eB l).2 <;>
      simp [directDSVActualLocalPOVMWinningEffect,
        directDSVActualReindexedRetainedPOVM,
        reindexedPOVM, purificationAlicePOVM,
        directDSVActualBilateralRetainedIndexEquiv,
        Matrix.reindex_apply, Matrix.sum_apply, Matrix.ite_apply,
        Matrix.submatrix_apply,
        Matrix.kroneckerMap_apply, Matrix.one_apply,
        Equiv.prodProdProdComm_apply, alice_work, bob_work]

theorem directDSVActualReindexedWinningEffect_quadratic
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (winning : Matrix κ κ ℂ)
    (z : EuclideanSpace ℂ ι) :
    quadraticExpectation
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
          (Matrix.reindex e.symm e.symm winning)) z =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) winning)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e z) := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  change
    (∑ i : ι, (∑ j : ι, winning (e i) (e j) * z j) *
      star (z i)).re =
    (∑ i : κ,
      (∑ j : κ, winning i j * z (e.symm j)) *
        star (z (e.symm i))).re
  congr 1
  calc
    (∑ i : ι, (∑ j : ι, winning (e i) (e j) * z j) *
      star (z i)) =
        ∑ i : ι,
          (∑ j : κ, winning (e i) j * z (e.symm j)) *
            star (z i) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          simpa only [Equiv.symm_apply_apply] using
            (Equiv.sum_comp e
              (fun j : κ => winning (e i) j * z (e.symm j)))
    _ = ∑ i : κ,
          (∑ j : κ, winning i j * z (e.symm j)) *
            star (z (e.symm i)) := by
          simpa only [Equiv.symm_apply_apply] using
            (Equiv.sum_comp e
              (fun i : κ =>
                (∑ j : κ, winning i j * z (e.symm j)) *
                  star (z (e.symm i))))

theorem directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
    {X Y A B s t u v ι κ : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [Fintype u] [Fintype v]
    [Fintype ι] [Fintype κ]
    [DecidableEq s] [DecidableEq t] [DecidableEq u] [DecidableEq v]
    [DecidableEq ι] [DecidableEq κ]
    (G : Game X Y A B)
    (eA : ι ≃ s × t) (eB : κ ≃ u × v)
    (PA : POVM A s) (PB : POVM B u)
    (x : X) (y : Y)
    (z : EuclideanSpace ℂ (ι × κ))
    (target : EuclideanSpace ℂ (s × u))
    (work : EuclideanSpace ℂ (t × v))
    (selected :
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (directDSVActualBilateralRetainedIndexEquiv eA eB) z =
          unconditionalMatchedVerifierTensor target work) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := ι × κ) (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM eA PA)
          (directDSVActualReindexedRetainedPOVM eB PB)
          x y)) z =
      ‖work‖ ^ 2 *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := s × u) (𝕜 := ℂ)
            (directDSVActualLocalPOVMWinningEffect G PA PB x y))
          target := by
  rw [directDSVActualReindexedRetainedPOVMWinningEffect,
    directDSVActualReindexedWinningEffect_quadratic,
    selected, unconditionalMatchedVerifierEffect_tensor_quadratic]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem unconditionalSelectedBranchLocalAction_mul
    {s t : Type*} [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t]
    (U₁ U₂ V₁ V₂ : Matrix.unitaryGroup s ℂ)
    (z : EuclideanSpace ℂ ((s × s) × t)) :
    unconditionalMixedConjugateSelectedBranchLocalAction
      (U₁ * U₂) (V₁ * V₂) z =
    unconditionalMixedConjugateSelectedBranchLocalAction U₁ V₁
      (unconditionalMixedConjugateSelectedBranchLocalAction
        U₂ V₂ z) := by
  classical
  simp only [unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary, Submonoid.coe_mul, mul_kronecker_mul,
    mulVec_mulVec, toLp.injEq]
  apply congrArg
    (fun (W : Matrix ((s × s) × t) ((s × s) × t) ℂ) =>
      W.mulVec (ofLp z))
  simpa only [mul_one] using
    (Matrix.mul_kronecker_mul
      ((U₁ : Matrix s s ℂ) ⊗ₖ (V₁ : Matrix s s ℂ))
      ((U₂ : Matrix s s ℂ) ⊗ₖ (V₂ : Matrix s s ℂ))
      (1 : Matrix t t ℂ) (1 : Matrix t t ℂ))

private def unconditionalSelectedRetainedBilateralRegroup
    (ι τ : Type) :
    ((ι × τ) × (ι × τ)) ≃ ((ι × ι) × (τ × τ)) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl
  right_inv := by rintro ⟨⟨_, _⟩, ⟨_, _⟩⟩; rfl

theorem unconditionalRegroupedSelectedRetainedReindexAction
    {κ ι τ δ : Type}
    [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    [Fintype δ] [DecidableEq δ]
    (e : κ ≃ ι × τ)
    (workEquiv : τ × τ ≃ δ)
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ (κ × κ)) :
    let regroup :=
      (unconditionalSelectedRetainedBilateralRegroup ι τ).trans
        (Equiv.prodCongr (Equiv.refl (ι × ι)) workEquiv)
    let sigma :=
      (Equiv.prodComm ι τ).trans (Equiv.sigmaEquivProd τ ι).symm
    let localEquiv := e.trans sigma
    let A := unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      localEquiv.symm (coherentSharedRandomControlledUnitary
        (fun _ : τ => U))
    let B := unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
      localEquiv.symm (coherentSharedRandomControlledUnitary
        (fun _ : τ => V))
    let state := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((Equiv.prodCongr e e).trans regroup)
    state
      (toLp 2
        ((((A : Matrix κ κ ℂ) ⊗ₖ
          (B : Matrix κ κ ℂ)).mulVec (ofLp z)))) =
      unconditionalMixedConjugateSelectedBranchLocalAction U V
        (state z) := by
  classical
  dsimp
  ext ⟨⟨i, j⟩, c⟩
  have reindex (f : κ × κ → ℂ) :
      (∑ p : κ × κ, f p) =
        ∑ p : (ι × τ) × (ι × τ),
          f (e.symm p.1, e.symm p.2) := by
    simpa only [Equiv.prodCongr_apply, Prod.map_fst, Equiv.symm_apply_apply, Prod.map_snd,
      Prod.mk.eta] using
      (Equiv.sum_comp (Equiv.prodCongr e e)
        (fun p : (ι × τ) × (ι × τ) =>
          f (e.symm p.1, e.symm p.2)))
  change
    (∑ p : κ × κ,
      (unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
          (((Equiv.sigmaEquivProd τ ι).trans
            (Equiv.prodComm τ ι)).trans e.symm)
          (coherentSharedRandomControlledUnitary
            (fun _ : τ => U)) : Matrix κ κ ℂ)
          (e.symm (i, (workEquiv.symm c).1)) p.1 *
        (unconditionalSourceFixedPureStoppedSigmaReindexedUnitary
          (((Equiv.sigmaEquivProd τ ι).trans
            (Equiv.prodComm τ ι)).trans e.symm)
          (coherentSharedRandomControlledUnitary
            (fun _ : τ => V)) : Matrix κ κ ℂ)
          (e.symm (j, (workEquiv.symm c).2)) p.2 * z p) = _
  rw [reindex]
  simp only [unconditionalSourceFixedPureStoppedSigmaReindexedUnitary,
    coherentSharedRandomControlledUnitary, reindex_apply, Equiv.symm_trans, Equiv.symm_symm,
    Equiv.prodComm_symm, Equiv.coe_trans, Equiv.coe_prodComm, submatrix_apply,
    Function.comp_apply, Equiv.apply_symm_apply, Prod.swap_prod_mk,
    Equiv.sigmaEquivProd_symm_apply, Prod.fst_swap, Prod.snd_swap, blockDiagonal'_apply, cast_eq,
    dite_eq_ite, mul_ite, ite_mul, zero_mul, mul_zero, mul_assoc, Fintype.sum_prod_type,
    sum_ite_eq, mem_univ, ↓reduceIte, sum_ite_irrel, sum_const_zero,
    unconditionalMixedConjugateSelectedBranchLocalAction,
    unconditionalMixedConjugateSelectedBranchUnitary,
    unconditionalSelectedRetainedBilateralRegroup, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft', Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.symm_mk, Equiv.trans_apply,
    Equiv.coe_fn_mk, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, id_eq, Prod.map_snd,
    Prod.map_apply, mulVec, dotProduct, kroneckerMap_apply, Matrix.one_apply,
    mul_one]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/-- The finite equivalence encoding unconditional actual fixed source retained history pair. -/
def unconditionalActualFixedSourceRetainedHistoryPairEquiv
    {N d L : ℕ} {R : Type} (j : Fin L) :
    (UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R ×
     UnconditionalActualCleanedSelectedRetainedIndex
      (N := N) (d := d) j R) ≃
    ((Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) ×
      (((Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d) ×
        (Fin (L - j.val) →
           DSVUniformDensityThresholdLocalIndex N d)) ×
       (R × R))) where
  toFun p :=
    ((fun i => (p.1.1 i, p.2.1 i)),
      ((p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2)))
  invFun p :=
    ((fun i => (p.1 i).1, (p.2.1.1, p.2.2.1)),
      (fun i => (p.1 i).2, (p.2.1.2, p.2.2.2)))
  left_inv := by
    rintro ⟨⟨beforeA, afterA, phaseA⟩,
      ⟨beforeB, afterB, phaseB⟩⟩
    simp only
  right_inv := by
    rintro ⟨before, ⟨⟨afterA, afterB⟩, ⟨phaseA, phaseB⟩⟩⟩
    simp only [Prod.mk.eta]

theorem unconditionalActualFixedSourceFullBilateralRegroup_eq
    {B N d L m : ℕ} {R : Type} (j : Fin L) :
    unconditionalSourcePhysicalCleanedFullBilateralRegroup
        (R := R) (B := B) (N := N) (d := d) (m := m) j =
      (unconditionalSelectedRetainedBilateralRegroup
        (UnconditionalSelectedCopyLocalIndex B d N m)
        (UnconditionalActualCleanedSelectedRetainedIndex
          (N := N) (d := d) j R)).trans
        (Equiv.prodCongr
          (Equiv.refl
            (UnconditionalSelectedCopyLocalIndex B d N m ×
             UnconditionalSelectedCopyLocalIndex B d N m))
          (unconditionalActualFixedSourceRetainedHistoryPairEquiv
            (N := N) (d := d) (R := R) j)) := by
  apply Equiv.ext
  rintro ⟨⟨selectedA, beforeA, afterA, phaseA⟩,
    ⟨selectedB, beforeB, afterB, phaseB⟩⟩
  rfl

theorem unconditionalActualFixedSourceFullPhysicalBilateralStageTransport
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (spectralA spectralB : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (z : EuclideanSpace ℂ
      (UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ×
       UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m)) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        phaseSplit j
      (toLp 2
        (((unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ξ spectralA A j :
              Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m)
                (UnconditionalSourcePhysicalStoppingPhaseFiber
                  S B N d L m) ℂ) ⊗ₖ
            (unconditionalActualCleanedSelectedFullStageUnitary
              phaseSplit Q width schedule ζ spectralB C j :
              Matrix (UnconditionalSourcePhysicalStoppingPhaseFiber
                S B N d L m)
                (UnconditionalSourcePhysicalStoppingPhaseFiber
                  S B N d L m) ℂ)).mulVec
          (ofLp z))) =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ξ A *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectralA)
        (unconditionalActualCleanedSelectedStageBucketUnitary
            Q (width (schedule j)) ζ C *
          unconditionalActualCleanedSelectedStageSpectralUnitary
            (B := B) (m := m) spectralB)
        (unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
          phaseSplit j z) := by
  classical
  let e :
      UnconditionalSourcePhysicalStoppingPhaseFiber
          S B N d L m ≃
        UnconditionalSelectedCopyLocalIndex B d N m ×
          UnconditionalActualCleanedSelectedRetainedIndex
            (N := N) (d := d) j R :=
    unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      (N := N) (d := d) (m := m) phaseSplit j
  let work :=
    unconditionalActualFixedSourceRetainedHistoryPairEquiv
      (N := N) (d := d) (R := R) j
  let UA :=
    unconditionalActualCleanedSelectedStageBucketUnitary
      Q (width (schedule j)) ξ A *
      unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) spectralA
  let UB :=
    unconditionalActualCleanedSelectedStageBucketUnitary
      Q (width (schedule j)) ζ C *
      unconditionalActualCleanedSelectedStageSpectralUnitary
        (B := B) (m := m) spectralB
  have transport :=
    unconditionalRegroupedSelectedRetainedReindexAction
      e work UA UB z
  simpa only [unconditionalActualCleanedSelectedFullStageUnitary,
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry,
    unconditionalActualFixedSourceFullBilateralRegroup_eq,
    e, work, UA, UB] using transport

theorem unconditionalActualFixedSourceDecodedMatchedBranch
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (positive : 0 < width (schedule j)) (grid : 0 < N) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualMultiscalePhaseIndexEquiv
          (schedule j)).symm j
      (actualStoppingBranchVector
        (dSVUniformDensityPhysicalAsyncSigmaContinuation
          (unconditionalActualCleanedSelectedFiniteStageDecoder
            (unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j)).symm
            Q width schedule ξ
            (dSVUniformDensityAliceHistorySpectralCopy
              (N := N) ξ) A)
          (unconditionalActualCleanedSelectedFiniteStageDecoder
            (unconditionalActualMultiscalePhaseIndexEquiv
              (schedule j)).symm
            Q width schedule ζ
            ((dSVUniformDensityBobHistoryCopyBasis
              (N := N) ζ)⁻¹) C)
          (actualStoppingQuestionLocalAction
            (unconditionalSourcePhysicalCleanedTargetFirstUnitary
              S B N d L m
              (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
                S B N d L m width schedule ξ))
            (unconditionalSourcePhysicalCleanedTargetFirstUnitary
              S B N d L m
              (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
                S B N d L m width schedule ζ))
            (unconditionalSourcePhysicalCleanedStoppingFixedSource
              S B N d L m))) j.succ j.succ) =
      unconditionalSelectedCopyCleanedMatchedBranch
        (N := N) (B := B) (m := m)
        Q width schedule ξ ζ A C j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := S) (B := B) (N := N) (d := d) (L := L) j) := by
  let phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × UnconditionalActualCanonicalRetainedPhaseIndex S B :=
    (unconditionalActualMultiscalePhaseIndexEquiv
      (B := B) (schedule j)).symm
  have sameSource :
      actualStoppingBranchVector
          (unconditionalSourcePhysicalStoppingTargetFirstStateEquiv
            S B N d L m
            (dSVDensityRationalHeterogeneousOriginalStoppedState
              S B N d L m width schedule ξ ζ)) j.succ j.succ =
        unconditionalActualCanonicalFixedSourceMatchedBranch
          (B := B) (m := m) width schedule ξ ζ j := by
    unfold unconditionalActualCanonicalFixedSourceMatchedBranch
    rw [unconditionalSourcePhysicalCleanedStoppingFixedSource_physicalAction]
  change
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        phaseSplit j
      (actualStoppingBranchVector
        (dSVUniformDensityPhysicalAsyncSigmaContinuation
          (unconditionalActualCleanedSelectedFiniteStageDecoder
            phaseSplit Q width schedule ξ
            (dSVUniformDensityAliceHistorySpectralCopy
              (N := N) ξ) A)
          (unconditionalActualCleanedSelectedFiniteStageDecoder
            phaseSplit Q width schedule ζ
            ((dSVUniformDensityBobHistoryCopyBasis
              (N := N) ζ)⁻¹) C)
          (actualStoppingQuestionLocalAction
            (unconditionalSourcePhysicalCleanedTargetFirstUnitary
              S B N d L m
              (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
                S B N d L m width schedule ξ))
            (unconditionalSourcePhysicalCleanedTargetFirstUnitary
              S B N d L m
              (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
                S B N d L m width schedule ζ))
            (unconditionalSourcePhysicalCleanedStoppingFixedSource
              S B N d L m))) j.succ j.succ) = _
  rw [unconditionalActualCleanedSelectedMatchedStoppingBranch
    phaseSplit Q width schedule ξ ζ A C j]
  rw [unconditionalActualFixedSourceFullPhysicalBilateralStageTransport]
  rw [sameSource,
    unconditionalActualCanonicalFullSource_eq_rawSelectedStage]
  rw [unconditionalSelectedBranchLocalAction_mul,
    unconditionalMixedConjugateSelectedBranch_tensorAction,
    unconditionalActualCanonicalRawSelectedPhysicalStage_eq,
    unconditionalActualPhysicalMixedAcceptedSpectralGauge_stage
      positive grid ξ ζ,
    unconditionalMixedConjugateSelectedBranch_tensorAction]
  congr 1

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactSourceHistoryFlag_nonempty_of_positive
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D) :
    Nonempty (ExactHistoryFlag X Y A B D) := by
  classical
  have nonzero :
      (∑ t : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D t) ≠ 0 := by
    rw [exactLocallySampleableLaw_sum
      G n S D remaining positive]
    exact one_ne_zero
  obtain ⟨t, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero nonzero
  exact ⟨t.2.2.2⟩

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

/-- The finite equivalence encoding physical 8 selected global target work. -/
def physical8SelectedGlobalTargetWorkEquiv
    (P N d m : ℕ) :
    UnconditionalSelectedCopyLocalIndex P d N m ≃
      Fin d × (Fin P × Fin (N * m)) where
  toFun q := (q.1.2, (q.1.1, q.2))
  invFun q := ⟨(q.2.1, q.1), q.2.2⟩
  left_inv := by
    rintro ⟨⟨phase, atom⟩, work⟩
    rfl
  right_inv := by
    rintro ⟨atom, phase, work⟩
    rfl

/-- The finite equivalence encoding physical 8 one scale actual global fiber. -/
def physical8OneScaleActualGlobalFiberEquiv
    {P N d L m : ℕ} {R : Type}
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (j : Fin L) :
    UnconditionalSourcePhysicalStoppingPhaseFiber 1 P N d L m ≃
      Fin d ×
        ((Fin P × Fin (N * m)) ×
          UnconditionalSourceFlagControlledRetainedIndex
            (N := N) (d := d) j R) :=
  (unconditionalSourcePhysicalCleanedFullLocalIndexEquiv
      phaseSplit j).trans
    ((Equiv.prodCongr
        (physical8SelectedGlobalTargetWorkEquiv P N d m)
        (Equiv.refl
          (UnconditionalSourceFlagControlledRetainedIndex
            (N := N) (d := d) j R))).trans
      (Equiv.prodAssoc (Fin d) (Fin P × Fin (N * m))
        (UnconditionalSourceFlagControlledRetainedIndex
          (N := N) (d := d) j R)))

/-- The positive operator-valued measurement implementing physical 8 one scale original flag. -/
def physical8OneScaleOriginalFlagPOVM
    {C Z : Type*} [Fintype C] [DecidableEq C]
    {P N d L m : ℕ} {R : Type}
    [Fintype R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (default : C) (sourcePOVM : Z → POVM C (Fin d)) :
    Fin (L + 1) → Z →
      POVM C
        (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) :=
  Fin.cases
    (fun _ => deterministicOutcomePOVM default)
    (fun j x =>
      directDSVActualReindexedRetainedPOVM
        (physical8OneScaleActualGlobalFiberEquiv
          (N := N) (d := d) (m := m) phaseSplit j)
        (sourcePOVM x))

/-- The unitary operator implementing physical 8 one scale actual alice stopping. -/
def physical8OneScaleActualAliceStoppingUnitary
    {F Z : Type*} {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (Q : ℕ) (width : Fin 1 → ℝ)
    (schedule : Fin L → Fin 1)
    (target : F → Z → BipartiteUnitVector d)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    F → Z → Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) ℂ :=
  fun flag x =>
    coherentSharedRandomControlledUnitary
        (unconditionalSourceFlagControlledFiniteStageDecoder
          phaseSplit Q width schedule (target flag x)
          (dSVUniformDensityAliceHistorySpectralCopy
            (N := N) (target flag x)) cleanup) *
      unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          1 P N d L m width schedule (target flag x))

/-- The unitary operator implementing physical 8 one scale actual bob stopping. -/
def physical8OneScaleActualBobStoppingUnitary
    {F Z : Type*} {P N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R)
    (Q : ℕ) (width : Fin 1 → ℝ)
    (schedule : Fin L → Fin 1)
    (target : F → Z → BipartiteUnitVector d)
    (cleanup : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    F → Z → Matrix.unitaryGroup
      (Σ _ : Fin (L + 1),
        UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) ℂ :=
  fun flag y =>
    coherentSharedRandomControlledUnitary
        (unconditionalSourceFlagControlledFiniteStageDecoder
          phaseSplit Q width schedule (target flag y)
          ((dSVUniformDensityBobHistoryCopyBasis
            (N := N) (target flag y))⁻¹) cleanup) *
      unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          1 P N d L m width schedule (target flag y))

theorem exactSourceAnswerTypes_nonempty_of_remaining
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card) :
    Nonempty A ∧ Nonempty B := by
  classical
  let i : Fin n :=
    (Classical.choice (Fintype.card_pos_iff.mp
      (exactRemainingCoordinate_card_pos D remaining))).val
  let xs : Fin n → X :=
    fun _ => Classical.choice (gameQuestionX_nonempty G)
  let ys : Fin n → Y :=
    fun _ => Classical.choice (gameQuestionY_nonempty G)
  have normalized := S.outcomeProbability_normalized xs ys
  constructor
  · by_contra empty
    have zero :
        (∑ a : Fin n → A, ∑ b : Fin n → B,
          S.outcomeProbability xs ys a b) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact (empty ⟨a i⟩).elim
    rw [zero] at normalized
    norm_num at normalized
  · by_contra empty
    have zero :
        (∑ a : Fin n → A, ∑ b : Fin n → B,
          S.outcomeProbability xs ys a b) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      exact (empty ⟨b i⟩).elim
    rw [zero] at normalized
    norm_num at normalized

private def physical8OneScaleActualSourceFlaggedStrategy
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B)
    (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (w : ℝ) (N L P Q m : ℕ)
    (phases : 0 < P) (grid : 0 < N) (harmonic : 0 < m)
    (UA UB : Fin P → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ) : Strategy G := by
  classical
  let d : ℕ := Fintype.card
    (ExactGlobalHistoryLocalIndex G n S D)
  have dimension : 0 < d :=
    exactGlobalHistoryLocalIndex_card_pos G n S D
  let R : Type := Fin (Fintype.card (Fin (1 - 1) → Fin P))
  let phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
        Fin P × R :=
    (unconditionalActualMultiscalePhaseIndexEquiv
      (B := P) (0 : Fin 1)).symm
  let width : Fin 1 → ℝ := fun _ => w
  let schedule : Fin L → Fin 1 := fun _ => 0
  let F : Type := ExactSourceSharedFlag X Y A B D denominator
  let ξ : F → X → BipartiteUnitVector d :=
    fun flag x => exactGlobalHistoryFinGamma G n S D
      (exactSourceAlicePermutationHistory
        D denominator numerator nonempty flag x) x
  let ζ : F → Y → BipartiteUnitVector d :=
    fun flag y => exactGlobalHistoryFinPhi G n S D
      (exactSourceBobPermutationHistory
        D denominator numerator nonempty flag y) y
  let a₀ : A := Classical.choice
    (exactSourceAnswerTypes_nonempty_of_remaining
      G n S D remaining).1
  let b₀ : B := Classical.choice
    (exactSourceAnswerTypes_nonempty_of_remaining
      G n S D remaining).2
  let globalAlice : X → POVM A (Fin d) := fun x =>
    reindexedPOVM (finCongr (Nat.mul_one d))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystAlicePOVM G n S D 1 a₀ x))
  let globalBob : Y → POVM B (Fin d) := fun y =>
    reindexedPOVM (finCongr (Nat.mul_one d))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystBobPOVM G n S D 1 b₀ y))
  let PA : F → Fin (L + 1) → X →
      POVM A
        (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) :=
    fun flag => physical8OneScaleOriginalFlagPOVM
      (N := N) (d := d) (m := m) phaseSplit a₀
      (fun x => unitaryConjugatePOVM
        (conjugateUnitary
          (dSVDensityRationalCanonicalAliceBasis (ξ flag x)))
        (globalAlice x))
  let PB : F → Fin (L + 1) → Y →
      POVM B
        (UnconditionalSourcePhysicalStoppingPhaseFiber
          1 P N d L m) :=
    fun flag => physical8OneScaleOriginalFlagPOVM
      (N := N) (d := d) (m := m) phaseSplit b₀
      (fun y => unitaryConjugatePOVM
        (conjugateUnitary
          (dSVUniformDensityThresholdLeftBobBasis (ζ flag y)))
        (globalBob y))
  let U := physical8OneScaleActualAliceStoppingUnitary
    (P := P) (N := N) (d := d) (L := L) (m := m)
    phaseSplit Q width schedule ξ UA
  let V := physical8OneScaleActualBobStoppingUnitary
    (P := P) (N := N) (d := d) (L := L) (m := m)
    phaseSplit Q width schedule ζ UB
  let prepared : F → EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m)) :=
    fun _ => unconditionalSourcePhysicalCleanedStoppingFixedSource
      1 P N d L m
  have prepared_normalized : ∀ flag : F, ‖prepared flag‖ = 1 := by
    intro flag
    exact unconditionalSourcePhysicalCleanedStoppingFixedSource_norm
      phases grid dimension harmonic
  exact pureFlaggedStrategy G
    (exactSourceSharedFlagWeight D denominator)
    (exactSourceSharedFlagWeight_nonneg D denominator)
    (exactSourceSharedFlagWeight_sum D remaining denominator)
    prepared prepared_normalized
    (fun flag x => unitaryConjugatePOVM (U flag x)
      (dependentBlockPOVM (fun r => PA flag r x)))
    (fun flag y => unitaryConjugatePOVM (V flag y)
      (dependentBlockPOVM (fun r => PB flag r y)))

/--
The type used to represent unconditional one scale actual source flagged strategy in the exact
sampling construction.
-/
abbrev unconditionalOneScaleActualSourceFlaggedStrategy :=
  @physical8OneScaleActualSourceFlaggedStrategy

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The unconditional actual one scale fixed source phase split construction used in the quantum
parallel-repetition argument.
-/
def unconditionalActualOneScaleFixedSourcePhaseSplit (P : ℕ) :
    DSVDensityRationalPublicMultiscalePhaseIndex 1 P ≃
      Fin P × UnconditionalActualCanonicalRetainedPhaseIndex 1 P :=
  (unconditionalActualMultiscalePhaseIndexEquiv
    (B := P) (0 : Fin 1)).symm

theorem unconditionalActualOneScaleFlagControlledFiniteStageDecoder_eq
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    unconditionalSourceFlagControlledFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A =
      unconditionalActualCleanedSelectedFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A := by
  rfl

private def unconditionalActualOneScaleFixedSourceDecodedState
    {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    EuclideanSpace ℂ
      ((Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m) ×
       (Σ _ : Fin (L + 1),
          UnconditionalSourcePhysicalStoppingPhaseFiber
            1 P N d L m)) :=
  dSVUniformDensityPhysicalAsyncSigmaContinuation
    (unconditionalSourceFlagControlledFiniteStageDecoder
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule ξ
      (dSVUniformDensityAliceHistorySpectralCopy
        (N := N) ξ) A)
    (unconditionalSourceFlagControlledFiniteStageDecoder
      (unconditionalActualOneScaleFixedSourcePhaseSplit P)
      Q width schedule ζ
      ((dSVUniformDensityBobHistoryCopyBasis
        (N := N) ζ)⁻¹) C)
    (actualStoppingQuestionLocalAction
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralAlice
          1 P N d L m width schedule ξ))
      (unconditionalSourcePhysicalCleanedTargetFirstUnitary
        1 P N d L m
        (dSVDensityRationalHeterogeneousTargetFirstSpectralBob
          1 P N d L m width schedule ζ))
      (unconditionalSourcePhysicalCleanedStoppingFixedSource
        1 P N d L m))

theorem unconditionalActualOneScaleFixedSourcePhysicalQuestionAction
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (flag : F) (x : X) (y : Y) :
    actualStoppingQuestionLocalAction
        (physical8OneScaleActualAliceStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P)
          Q width schedule ξ A flag x)
        (physical8OneScaleActualBobStoppingUnitary
          (P := P) (N := N) (d := d) (L := L) (m := m)
          (unconditionalActualOneScaleFixedSourcePhaseSplit P)
          Q width schedule ζ C flag y)
        (unconditionalSourcePhysicalCleanedStoppingFixedSource
          1 P N d L m) =
      unconditionalActualOneScaleFixedSourceDecodedState
        Q width schedule (ξ flag x) (ζ flag y) A C := by
  classical
  unfold physical8OneScaleActualAliceStoppingUnitary
    physical8OneScaleActualBobStoppingUnitary
    unconditionalActualOneScaleFixedSourceDecodedState
    actualStoppingQuestionLocalAction
    dSVUniformDensityPhysicalAsyncSigmaContinuation
  simp only []
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul]
  rfl

theorem unconditionalActualOneScaleFixedSourceDecodedMatchedBranch
    {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (positive : 0 < width (schedule j)) (grid : 0 < N) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualOneScaleFixedSourcePhaseSplit P) j
        (actualStoppingBranchVector
          (unconditionalActualOneScaleFixedSourceDecodedState
            Q width schedule ξ ζ A C) j.succ j.succ) =
      unconditionalSelectedCopyCleanedMatchedBranch
        (N := N) (B := P) (m := m)
        Q width schedule ξ ζ A C j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := 1) (B := P) (N := N) (d := d) (L := L) j) := by
  have sameScale : schedule j = (0 : Fin 1) :=
    Subsingleton.elim _ _
  have samePhase :
      (unconditionalActualMultiscalePhaseIndexEquiv
        (B := P) (schedule j)).symm =
        unconditionalActualOneScaleFixedSourcePhaseSplit P := by
    simp only [unconditionalActualOneScaleFixedSourcePhaseSplit]
    rw [sameScale]
  have decoded :=
    unconditionalActualFixedSourceDecodedMatchedBranch
      (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
      Q width schedule ξ ζ A C j positive grid
  rw [samePhase] at decoded
  simpa only [unconditionalActualOneScaleFixedSourceDecodedState,
    unconditionalActualOneScaleFlagControlledFiniteStageDecoder_eq]
    using decoded

theorem
    unconditionalActualOneScalePhysicalQuestionDecodedMatchedBranch
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (flag : F) (x : X) (y : Y) (j : Fin L)
    (positive : 0 < width (schedule j)) :
    unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
        (unconditionalActualOneScaleFixedSourcePhaseSplit P) j
        (actualStoppingBranchVector
          (actualStoppingQuestionLocalAction
            (physical8OneScaleActualAliceStoppingUnitary
              (P := P) (N := N) (d := d) (L := L) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P)
              Q width schedule ξ A flag x)
            (physical8OneScaleActualBobStoppingUnitary
              (P := P) (N := N) (d := d) (L := L) (m := m)
              (unconditionalActualOneScaleFixedSourcePhaseSplit P)
              Q width schedule ζ C flag y)
            (unconditionalSourcePhysicalCleanedStoppingFixedSource
              1 P N d L m)) j.succ j.succ) =
      unconditionalSelectedCopyCleanedMatchedBranch
        (N := N) (B := P) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := 1) (B := P) (N := N) (d := d) (L := L) j) := by
  rw [unconditionalActualOneScaleFixedSourcePhysicalQuestionAction]
  exact unconditionalActualOneScaleFixedSourceDecodedMatchedBranch
    Q width schedule (ξ flag x) (ζ flag y) A C j positive grid

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalConjugatePureVector_sub_norm
    {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) :
    ‖unconditionalConjugatePureVector x -
      unconditionalConjugatePureVector y‖ = ‖x - y‖ := by
  have conjugate_sub :
      unconditionalConjugatePureVector x -
          unconditionalConjugatePureVector y =
        unconditionalConjugatePureVector (x - y) := by
    ext i
    simp only [unconditionalConjugatePureVector, RCLike.star_def, PiLp.sub_apply, star_sub]
  rw [conjugate_sub, unconditionalConjugatePureVector_norm]

theorem unconditionalClippedConjugateUnitTarget_distance_sq_le
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d)
    (psi : EuclideanSpace ℂ (Fin d × Fin d)) :
    ‖unconditionalConjugatePureVector psi -
      unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val‖ ^ 2 ≤
      2 * ‖psi - gamma.val‖ ^ 2 +
        8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  rw [unconditionalConjugatePureVector_sub_norm]
  let accepted : BipartiteUnitVector d :=
    dSVDensityRationalCanonicalAcceptedUnitTarget
      width grid fine gamma
  have triangle : ‖psi - accepted.val‖ ≤
      ‖psi - gamma.val‖ + ‖gamma.val - accepted.val‖ := by
    calc
      ‖psi - accepted.val‖ =
          ‖(psi - gamma.val) + (gamma.val - accepted.val)‖ := by
            congr 1
            abel
      _ ≤ _ := norm_add_le _ _
  have clipping :=
    dSVDensityRationalCanonicalAcceptedUnitTarget_distance_le
      width grid fine gamma
  have clipping_nonnegative :
      0 ≤ 1 / w + (d : ℝ) * w / (N : ℝ) := by
    positivity
  have clipping_squared :
      ‖gamma.val - accepted.val‖ ^ 2 ≤
        4 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
    change
      ‖gamma.val -
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val‖ ^ 2 ≤ _
    nlinarith [
      norm_nonneg
        (gamma.val -
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val),
      Real.sqrt_nonneg (1 / w + (d : ℝ) * w / (N : ℝ)),
      Real.sq_sqrt clipping_nonnegative]
  change ‖psi - accepted.val‖ ^ 2 ≤ _
  nlinarith [norm_nonneg (psi - accepted.val),
    norm_nonneg (psi - gamma.val),
    norm_nonneg (gamma.val - accepted.val),
    sq_nonneg (‖psi - gamma.val‖ - ‖gamma.val - accepted.val‖)]

theorem unconditionalMatchedVerifierTensor_sub_right
    {s t : Type*}
    (x y : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    unconditionalMatchedVerifierTensor x work -
      unconditionalMatchedVerifierTensor y work =
        unconditionalMatchedVerifierTensor (x - y) work := by
  ext q
  change x q.1 * work q.2 - y q.1 * work q.2 =
    (x q.1 - y q.1) * work q.2
  ring

theorem
    unconditionalWeightedClippedConjugateUnitSource_distance_sq_le
    {J : Type*} [Fintype J]
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j, weight j) = 1)
    (gamma : J → BipartiteUnitVector d)
    (psi : J → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : ℝ)
    (energy_bound :
      (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) ≤ energy) :
    (∑ j, weight j *
      ‖unconditionalConjugatePureVector (psi j) -
        unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine (gamma j)).val‖ ^ 2) ≤
      2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  classical
  let clip : ℝ := 1 / w + (d : ℝ) * w / (N : ℝ)
  calc
    _ ≤ ∑ j, weight j *
        (2 * ‖psi j - (gamma j).val‖ ^ 2 + 8 * clip) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (unconditionalClippedConjugateUnitTarget_distance_sq_le
          width grid fine (gamma j) (psi j))
        (weight_nonnegative j)
    _ = 2 * (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) +
        (8 * clip) * (∑ j, weight j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 2 * (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) +
        8 * clip := by
      rw [weight_normalized]
      ring
    _ ≤ 2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
      dsimp [clip]
      linarith

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The unconditional exact fair gamma unit construction used in the quantum parallel-repetition
argument.
-/
def unconditionalExactFairGammaUnit
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (u : ExactLocallySampleableTuple X Y A B D) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactSourceTupleGamma G n S D u,
    exactSourceTupleGamma_norm G n S D u⟩

theorem unconditionalExactFairGammaUnit_eq_global
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (u : ExactLocallySampleableTuple X Y A B D) :
    unconditionalExactFairGammaUnit G n S D u =
      exactGlobalHistoryFinGamma
        G n S D u.2.2.2 u.2.1 := by
  apply Subtype.ext
  rfl

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalCoherentPhaseConstantWork_sub
    {H : Type*} {B m : ℕ}
    (x y : EuclideanSpace ℂ (H × H))
    (work : EuclideanSpace ℂ (Fin m × Fin m)) :
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B x (fun _ _ _ => work) -
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B y (fun _ _ _ => work) =
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B (x - y) (fun _ _ _ => work) := by
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  change
    (ePRState B (φ, ψ) * x (i, j)) * work (a, b) -
      (ePRState B (φ, ψ) * y (i, j)) * work (a, b) =
      (ePRState B (φ, ψ) *
        (x (i, j) - y (i, j))) * work (a, b)
  ring

theorem unconditionalStoppedPhaseHarmonic_distance_sq
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B) (harmonic : 0 < m)
    (x y : EuclideanSpace ℂ (H × H)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B x (fun _ _ _ => embezzlementState m) -
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B y (fun _ _ _ => embezzlementState m)‖ ^ 2 =
      ‖x - y‖ ^ 2 := by
  rw [unconditionalCoherentPhaseConstantWork_sub,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    embezzlementState_norm m harmonic]
  ring

theorem unconditionalStoppedPhaseHarmonicDistance_sum_le
    {J K : Type*} [Fintype K]
    {d B m : ℕ}
    (phases : 0 < B) (harmonic : 0 < m)
    (x y : J → EuclideanSpace ℂ (Fin d × Fin d))
    {T : J × K → Type*} [∀ p, Fintype (T p)]
    (work : (p : J × K) → EuclideanSpace ℂ (T p))
    (work_row : ∀ j : J, (∑ k : K, ‖work (j, k)‖ ^ 2) ≤ 1)
    (j : J) :
    (∑ k : K,
      ‖unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (x j) (fun _ _ _ => embezzlementState m))
          (work (j, k)) -
        unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (y j) (fun _ _ _ => embezzlementState m))
          (work (j, k))‖ ^ 2) ≤
      ‖x j - y j‖ ^ 2 := by
  classical
  let sx := dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    B (x j) (fun _ _ _ => embezzlementState m)
  let sy := dSVDensityRationalPublicBucketCoherentPhaseSigmaState
    B (y j) (fun _ _ _ => embezzlementState m)
  have stage : ‖sx - sy‖ ^ 2 = ‖x j - y j‖ ^ 2 :=
    unconditionalStoppedPhaseHarmonic_distance_sq
      phases harmonic (x j) (y j)
  change
    (∑ k : K,
      ‖unconditionalMatchedVerifierTensor sx (work (j, k)) -
        unconditionalMatchedVerifierTensor sy
          (work (j, k))‖ ^ 2) ≤ _
  calc
    _ = ∑ k : K, ‖sx - sy‖ ^ 2 * ‖work (j, k)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [unconditionalMatchedVerifierTensor_sub_right,
        unconditionalMatchedVerifierTensor_norm_sq]
    _ = ‖sx - sy‖ ^ 2 *
        (∑ k : K, ‖work (j, k)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ‖sx - sy‖ ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg _) (work_row j)
    _ = _ := stage

theorem unconditionalWeightedStoppedPhaseHarmonicClippedUnit_le
    {J K : Type*} [Fintype J] [Fintype K]
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (phases : 0 < B) (harmonic : 0 < m)
    (weight : J → ℝ)
    (weight_nonnegative : ∀ j, 0 ≤ weight j)
    (weight_normalized : (∑ j, weight j) = 1)
    (gamma : J → BipartiteUnitVector d)
    (psi : J → EuclideanSpace ℂ (Fin d × Fin d))
    (energy : ℝ)
    (energy_bound :
      (∑ j, weight j * ‖psi j - (gamma j).val‖ ^ 2) ≤ energy)
    {T : J × K → Type*} [∀ p, Fintype (T p)]
    (work : (p : J × K) → EuclideanSpace ℂ (T p))
    (work_row : ∀ j : J, (∑ k : K, ‖work (j, k)‖ ^ 2) ≤ 1) :
    (∑ j : J, weight j * ∑ k : K,
      ‖unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B (unconditionalConjugatePureVector (psi j))
            (fun _ _ _ => embezzlementState m))
          (work (j, k)) -
        unconditionalMatchedVerifierTensor
          (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
            B
            (unconditionalConjugatePureVector
              (dSVDensityRationalCanonicalAcceptedUnitTarget
                width grid fine (gamma j)).val)
            (fun _ _ _ => embezzlementState m))
          (work (j, k))‖ ^ 2) ≤
      2 * energy + 8 * (1 / w + (d : ℝ) * w / (N : ℝ)) := by
  classical
  calc
    _ ≤ ∑ j : J, weight j *
        ‖unconditionalConjugatePureVector (psi j) -
          unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine (gamma j)).val‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        (unconditionalStoppedPhaseHarmonicDistance_sum_le
          phases harmonic
          (fun i => unconditionalConjugatePureVector (psi i))
          (fun i => unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine (gamma i)).val)
          work work_row j)
        (weight_nonnegative j)
    _ ≤ _ :=
      unconditionalWeightedClippedConjugateUnitSource_distance_sq_le
        width grid fine weight weight_nonnegative weight_normalized
        gamma psi energy energy_bound

theorem unconditionalExactFairStoppedPhaseHarmonicClippedUnit_le
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {w : ℝ} {N P m : ℕ}
    (width : 0 < w) (grid : 0 < N)
    (fine :
      (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) : ℝ) /
        (N : ℝ) < 1 / (w + 1))
    (phases : 0 < P) (harmonic : 0 < m)
    {K : Type*} [Fintype K]
    {T : ExactLocallySampleableTuple X Y A B D × K → Type*}
    [∀ p, Fintype (T p)]
    (work :
      (p : ExactLocallySampleableTuple X Y A B D × K) →
        EuclideanSpace ℂ (T p))
    (work_row :
      ∀ u : ExactLocallySampleableTuple X Y A B D,
        (∑ k : K, ‖work (u, k)‖ ^ 2) ≤ 1) :
    (∑ u : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D u *
        ∑ k : K,
          ‖unconditionalMatchedVerifierTensor
              (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
                P
                (unconditionalConjugatePureVector
                  (exactSourceTuplePsi G n S D u))
                (fun _ _ _ => embezzlementState m))
              (work (u, k)) -
            unconditionalMatchedVerifierTensor
              (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
                P
                (unconditionalConjugatePureVector
                  (dSVDensityRationalCanonicalAcceptedUnitTarget
                    width grid fine
                    (unconditionalExactFairGammaUnit
                      G n S D u)).val)
                (fun _ _ _ => embezzlementState m))
              (work (u, k))‖ ^ 2) ≤
      16 * martingaleRate G n S D +
        8 * (1 / w +
          (Fintype.card
            (ExactGlobalHistoryLocalIndex G n S D) : ℝ) *
            w / (N : ℝ)) := by
  classical
  have source :=
    (exactSourceStateDistanceBound_of_positive
      G n S D remaining positive).1
  have energy :
      (∑ u : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D u *
          ‖exactSourceTuplePsi G n S D u -
            (unconditionalExactFairGammaUnit
              G n S D u).val‖ ^ 2) ≤
        8 * martingaleRate G n S D := by
    simpa only [unconditionalExactFairGammaUnit, norm_sub_rev]
      using source
  have result :=
    unconditionalWeightedStoppedPhaseHarmonicClippedUnit_le
      width grid fine phases harmonic
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableLaw_nonneg G n S D positive)
      (exactLocallySampleableLaw_sum G n S D remaining positive)
      (unconditionalExactFairGammaUnit G n S D)
      (exactSourceTuplePsi G n S D)
      (8 * martingaleRate G n S D) energy work work_row
  convert result using 1
  ring

theorem unconditionalCanonicalRaw_eq_norm_smul_unit
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalAcceptedTarget w N gamma =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val := by
  exact (NormedSpace.norm_smul_normalize
    (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma)).symm

theorem unconditionalConjugateCanonicalRaw_eq_norm_smul_unit
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedTarget
          w N gamma) =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val := by
  have raw := unconditionalCanonicalRaw_eq_norm_smul_unit
    width grid fine gamma
  ext i
  have coefficient := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) => z i) raw
  change
    star (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma i) =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        star
          ((dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val i)
  change
    dSVDensityRationalCanonicalAcceptedTarget
      w N gamma i =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val i at coefficient
  rw [coefficient]
  simp only [star_mul', RCLike.star_def, conj_ofReal]

theorem unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B
        (unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedTarget
            w N gamma))
        (fun _ _ _ => embezzlementState m) =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine gamma).val)
          (fun _ _ _ => embezzlementState m) := by
  have raw :=
    unconditionalConjugateCanonicalRaw_eq_norm_smul_unit
      width grid fine gamma
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  have coefficient := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) => z (i, j)) raw
  change
    (ePRState B (φ, ψ) *
      star (dSVDensityRationalCanonicalAcceptedTarget
        w N gamma (i, j))) *
      embezzlementState m (a, b) =
    (‖dSVDensityRationalCanonicalAcceptedTarget
      w N gamma‖ : ℂ) *
      ((ePRState B (φ, ψ) *
        star ((dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val (i, j))) *
        embezzlementState m (a, b))
  change
    star (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma (i, j)) =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        star ((dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val (i, j)) at coefficient
  rw [coefficient]
  ring

theorem unconditionalMatchedTensor_real_smul_work
    {s t : Type*}
    (c : ℝ)
    (stage : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    c • unconditionalMatchedVerifierTensor stage work =
      unconditionalMatchedVerifierTensor stage (c • work) := by
  ext q
  change (c : ℂ) * (stage q.1 * work q.2) =
    stage q.1 * ((c : ℂ) * work q.2)
  ring

theorem unconditionalPhaseCanonical_sourceScale_absorbed
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d)
    {T : Type*}
    (work : EuclideanSpace ℂ T) :
    Real.sqrt (w * (d : ℝ)) •
      unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine gamma).val)
          (fun _ _ _ => embezzlementState m))
        ((‖dSVDensityRationalCanonicalAcceptedTarget
            w N gamma‖ / Real.sqrt (w * (d : ℝ))) • work) =
      unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedTarget
              w N gamma))
          (fun _ _ _ => embezzlementState m))
        work := by
  let scale : ℝ := Real.sqrt (w * (d : ℝ))
  let mass : ℝ :=
    ‖dSVDensityRationalCanonicalAcceptedTarget w N gamma‖
  let stage :=
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
      B
      (unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val)
      (fun _ _ _ => embezzlementState m)
  have real_dimension : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  have scale_positive : 0 < scale := by
    dsimp [scale]
    positivity
  have scalar : scale * (mass / scale) = mass := by
    field_simp [ne_of_gt scale_positive]
  have factor :=
    unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
      (B := B) (m := m) width grid fine gamma
  change
    scale •
        unconditionalMatchedVerifierTensor
          stage ((mass / scale) • work) = _
  calc
    scale •
        unconditionalMatchedVerifierTensor
          stage ((mass / scale) • work) =
        unconditionalMatchedVerifierTensor
          stage (scale • ((mass / scale) • work)) :=
      unconditionalMatchedTensor_real_smul_work
        scale stage ((mass / scale) • work)
    _ = unconditionalMatchedVerifierTensor
          stage (mass • work) := by
      rw [smul_smul, scalar]
    _ = mass •
          unconditionalMatchedVerifierTensor stage work :=
      (unconditionalMatchedTensor_real_smul_work
        mass stage work).symm
    _ = unconditionalMatchedVerifierTensor
          (mass • stage) work :=
      unconditionalMixedConjugateSelectedBranch_tensor_smul
        mass stage work
    _ = _ := by
      rw [factor]

theorem unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (gamma : BipartiteUnitVector d) :
    (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ / Real.sqrt (w * (d : ℝ))) ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w gamma := by
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  rw [div_pow,
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq
      width N gamma,
    Real.sq_sqrt (by positivity : 0 ≤ w * (d : ℝ)),
    dSVDensityRationalPhysicalDiagonalBornSuccess_eq]
  field_simp [ne_of_gt width, ne_of_gt dimension_real]

theorem unconditionalNormalizedCanonicalRetainedWork_norm_sq
    {S N d L B m : ℕ} {T : Type*} [Fintype T]
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (width_positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (gamma phi : BipartiteUnitVector d)
    (j : Fin L) (rest : EuclideanSpace ℂ T)
    (rest_unit : ‖rest‖ = 1) :
    ‖(‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ))) •
      unconditionalSelectedCopyRetainedWork
        (N := N) width schedule gamma phi j rest‖ ^ 2 =
      ‖unconditionalSelectedCopyIdealMatchedBranch
        (N := N) (B := B) (m := m)
        width schedule gamma phi j rest‖ ^ 2 := by
  have positive := width_positive (schedule j)
  have ratio_nonnegative :
      0 ≤ ‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ)) := by
    exact div_nonneg (norm_nonneg _)
      (Real.sqrt_nonneg _)
  calc
    _ =
      (‖dSVDensityRationalCanonicalAcceptedTarget
          (width (schedule j)) N gamma‖ /
        Real.sqrt ((width (schedule j)) * (d : ℝ))) ^ 2 *
      ‖unconditionalSelectedCopyRetainedWork
        (N := N) width schedule gamma phi j rest‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ratio_nonnegative, mul_pow]
    _ =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule j)) gamma *
      (dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule gamma phi j.val * ‖rest‖ ^ 2) := by
      rw [unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
        positive grid dimension gamma,
        unconditionalSelectedCopyRetainedWork_norm_sq]
    _ =
      dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule gamma phi j.val *
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension (width (schedule j)) gamma := by
      rw [rest_unit]
      ring
    _ = _ :=
      (unconditionalSelectedCopyIdealMatchedBranch_norm_sq
        phases grid dimension harmonic width width_positive schedule
        gamma phi j rest rest_unit).symm

theorem integratorActualCanonicalRetainedPhaseTail_norm
    {S B N d L : ℕ}
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (j : Fin L) :
    ‖unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j‖ = 1 := by
  have residual : 0 < Fintype.card (Fin (S - 1) → Fin B) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ => ⟨0, phases⟩⟩
  change
    ‖unconditionalMatchedVerifierTensor
        (dSVUniformDensityIndependentSharedState
          (L - j.val) N d)
        (ePRState
          (Fintype.card (Fin (S - 1) → Fin B)))‖ = 1
  rw [unconditionalMatchedVerifierTensor_norm,
    dSVUniformDensityIndependentSharedState_norm
      (L - j.val) grid dimension,
    ePRState_norm _ residual]
  norm_num

/--
The type used to represent integrator actual c 485 tail index in the exact sampling
construction.
-/
abbrev IntegratorActualC485TailIndex
    (S B N d L : ℕ) (j : Fin L) :=
  (((Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d) ×
    (Fin (L - j.val) →
      DSVUniformDensityThresholdLocalIndex N d)) ×
   (UnconditionalActualCanonicalRetainedPhaseIndex S B ×
    UnconditionalActualCanonicalRetainedPhaseIndex S B))

/--
The type used to represent integrator actual c 485 retained index in the exact sampling
construction.
-/
abbrev IntegratorActualC485RetainedIndex
    (S B N d L : ℕ) (j : Fin L) :=
  (Fin j.val →
    (DSVUniformDensityThresholdLocalIndex N d ×
     DSVUniformDensityThresholdLocalIndex N d)) ×
    IntegratorActualC485TailIndex S B N d L j

/--
The type used to represent integrator actual c 485 branch space in the exact sampling
construction.
-/
abbrev IntegratorActualC485BranchSpace
    (S B N d L m : ℕ) (j : Fin L) :=
  EuclideanSpace ℂ
    ((UnconditionalSelectedCopyLocalIndex B d N m ×
      UnconditionalSelectedCopyLocalIndex B d N m) ×
     IntegratorActualC485RetainedIndex S B N d L j)

private def integratorActualC485OriginalRetainedWork
    {S B N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (IntegratorActualC485RetainedIndex S B N d L j) :=
  unconditionalSelectedCopyRetainedWork
    (N := N) width schedule ξ ζ j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)

/--
The integrator actual c 485 normalized diagonal work construction used in the quantum parallel-
repetition argument.
-/
def integratorActualC485NormalizedDiagonalWork
    {S B N d L : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    EuclideanSpace ℂ
      (IntegratorActualC485RetainedIndex S B N d L j) :=
  (‖dSVDensityRationalCanonicalAcceptedTarget
      (width (schedule j)) N ξ‖ /
    Real.sqrt (width (schedule j) * (d : ℝ))) •
      integratorActualC485OriginalRetainedWork
        (B := B) width schedule ξ ζ j

open Classical in
/-- The state vector representing integrator actual c 485 cleaned. -/
def integratorActualC485CleanedVector
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMixedConjugateSelectedBranchLocalAction
    (unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) B
      (conjugateUnitary
        (dSVDensityRationalCanonicalAliceBasis ξ)))
    (unconditionalMixedConjugateSigmaAtomLift
      (m := N * m) B
      (conjugateUnitary
        (dSVUniformDensityThresholdLeftBobBasis ζ)))
    (unconditionalSelectedCopyCleanedMatchedBranch
      (N := N) (B := B) (m := m)
      Q width schedule ξ ζ A C j
      (unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j))

/-- The state vector representing integrator actual c 485 canonical. -/
def integratorActualC485CanonicalVector
    {S B N d L m : ℕ}
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
      (unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          positive grid fine ξ).val)
      (fun _ _ _ => embezzlementState (N * m)))
    (integratorActualC485NormalizedDiagonalWork
      (B := B) width schedule ξ ζ j)

/-- The state vector representing integrator actual c 485 source. -/
def integratorActualC485SourceVector
    {S B N d L m : ℕ}
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (j : Fin L) :
    IntegratorActualC485BranchSpace S B N d L m j :=
  unconditionalMatchedVerifierTensor
    (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
      (unconditionalConjugatePureVector ψ)
      (fun _ _ _ => embezzlementState (N * m)))
    (integratorActualC485NormalizedDiagonalWork
      (B := B) width schedule ξ ζ j)

theorem unconditionalActualC485NormalizedDiagonalWork_mass_sum_le_one
    {S B N d L m : ℕ}
    (phases : 0 < B) (grid : 0 < N)
    (dimension : 0 < d) (harmonic : 0 < m)
    (width : Fin S → ℝ) (positive : ∀ s, 0 < width s)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ j : Fin L,
      ‖integratorActualC485NormalizedDiagonalWork
          (S := S) (B := B) (N := N) (d := d) (L := L)
          width schedule ξ ζ j‖ ^ 2) ≤ 1 := by
  classical
  calc
    _ = ∑ j : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule j)) ξ := by
      apply Finset.sum_congr rfl
      intro j _
      unfold integratorActualC485NormalizedDiagonalWork
        integratorActualC485OriginalRetainedWork
      rw [unconditionalNormalizedCanonicalRetainedWork_norm_sq
        (B := B) (m := m) phases grid dimension harmonic
        width positive schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := S) (B := B) (N := N) (d := d) (L := L) j)
        (integratorActualCanonicalRetainedPhaseTail_norm
          phases grid dimension j)]
      exact unconditionalSelectedCopyIdealMatchedBranch_norm_sq
        phases grid dimension harmonic width positive schedule ξ ζ j
        (unconditionalActualCanonicalRetainedPhaseTail
          (S := S) (B := B) (N := N) (d := d) (L := L) j)
        (integratorActualCanonicalRetainedPhaseTail_norm
          phases grid dimension j)
    _ ≤ 1 :=
      dSVDensityRationalHeterogeneousPhysicalDiagonalSurvival_budget
        grid dimension width schedule ξ ζ

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
    {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ]
    (left right : DecidableEq τ)
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    @unconditionalMixedConjugateSelectedBranchLocalAction
      ι τ inferInstance inferInstance inferInstance left U V z =
    @unconditionalMixedConjugateSelectedBranchLocalAction
      ι τ inferInstance inferInstance inferInstance right U V z := by
  have same : left = right := Subsingleton.elim left right
  cases same
  rfl

theorem unconditionalActualC485CanonicalCorrectedIdeal_generic
    {S N d L B m : ℕ} {T : Type*}
    [Fintype T] [DecidableEq T]
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1))
    (rest : EuclideanSpace ℂ T) :
    unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              positive grid fine ξ).val)
          (fun _ _ _ => embezzlementState (N * m)))
        ((‖dSVDensityRationalCanonicalAcceptedTarget
              (width (schedule j)) N ξ‖ /
            Real.sqrt (width (schedule j) * (d : ℝ))) •
          unconditionalSelectedCopyRetainedWork
            (N := N) width schedule ξ ζ j rest) =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis ξ)))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ζ)))
        (unconditionalSelectedCopyIdealMatchedBranch
          (N := N) (B := B) (m := m)
          width schedule ξ ζ j rest) := by
  have scale_positive : 0 < Real.sqrt (width (schedule j) * (d : ℝ)) := by
    positivity
  apply smul_right_injective _ scale_positive.ne'
  exact
    (unconditionalPhaseCanonical_sourceScale_absorbed
      (B := B) (m := N * m) positive grid dimension fine ξ
      (unconditionalSelectedCopyRetainedWork
        (N := N) width schedule ξ ζ j rest)).trans
      (unconditionalMixedConjugateSelectedBranchCovariance
        (B := B) (m := m) grid dimension width schedule ξ ζ j
        positive rest).symm

open Classical in
theorem unconditionalActualC485CanonicalVector_eq_correctedIdeal
    {S B N d L m : ℕ}
    {width : Fin S → ℝ}
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    integratorActualC485CanonicalVector
        (B := B) (m := m) schedule ξ ζ j positive grid fine =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis ξ)))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) B
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis ζ)))
        (unconditionalSelectedCopyIdealMatchedBranch
          (N := N) (B := B) (m := m)
          width schedule ξ ζ j
          (unconditionalActualCanonicalRetainedPhaseTail
            (S := S) (B := B) (N := N) (d := d) (L := L) j)) := by
  change
    unconditionalMatchedVerifierTensor
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              positive grid fine ξ).val)
          (fun _ _ _ => embezzlementState (N * m)))
        ((‖dSVDensityRationalCanonicalAcceptedTarget
              (width (schedule j)) N ξ‖ /
            Real.sqrt (width (schedule j) * (d : ℝ))) •
          unconditionalSelectedCopyRetainedWork
            (N := N) width schedule ξ ζ j
            (unconditionalActualCanonicalRetainedPhaseTail
              (S := S) (B := B) (N := N) (d := d) (L := L) j)) = _
  convert
    (unconditionalActualC485CanonicalCorrectedIdeal_generic
      (B := B) (m := m)
      schedule ξ ζ j positive grid dimension fine
      (unconditionalActualCanonicalRetainedPhaseTail
        (S := S) (B := B) (N := N) (d := d) (L := L) j)) using 1
  exact unconditionalActualSelectedBranchLocalAction_decidableEq_irrel
    _ _ _ _ _

theorem unconditionalActualSelectedBranchLocalAction_norm
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (z : EuclideanSpace ℂ ((ι × ι) × τ)) :
    ‖unconditionalMixedConjugateSelectedBranchLocalAction U V z‖ =
      ‖z‖ := by
  classical
  let M : Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ :=
    (unconditionalMixedConjugateSelectedBranchUnitary
      (τ := τ) U V : Matrix ((ι × ι) × τ) ((ι × ι) × τ) ℂ)
  have gram : M.conjTranspose * M = 1 := by
    simpa only [star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp
        (unconditionalMixedConjugateSelectedBranchUnitary
          (τ := τ) U V).property)
  have squared : ‖toLp 2 (M.mulVec (ofLp z))‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [rectangular_matrix_mulVec_norm_sq, gram]
    simp only [quadraticExpectation, map_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K,
      coe_algebraMap, ← ofReal_pow, ofReal_re]
  change ‖toLp 2 (M.mulVec (ofLp z))‖ = ‖z‖
  nlinarith [norm_nonneg (toLp 2 (M.mulVec (ofLp z))), norm_nonneg z]

theorem unconditionalActualSelectedBranchLocalAction_sub
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (x y : EuclideanSpace ℂ ((ι × ι) × τ)) :
    unconditionalMixedConjugateSelectedBranchLocalAction U V x -
        unconditionalMixedConjugateSelectedBranchLocalAction U V y =
      unconditionalMixedConjugateSelectedBranchLocalAction
        U V (x - y) := by
  classical
  ext i
  simp only [unconditionalMixedConjugateSelectedBranchLocalAction, PiLp.sub_apply, mulVec,
    dotProduct, ofLp_sub, Pi.sub_apply, mul_sub, sum_sub_distrib]

theorem unconditionalActualC485CleanDeviation_sq
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (j : Fin L)
    (positive : 0 < width (schedule j))
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (width (schedule j) + 1)) :
    ‖integratorActualC485CleanedVector
          (B := B) (m := m) Q width schedule ξ ζ A C j -
        integratorActualC485CanonicalVector
          (B := B) (m := m) schedule ξ ζ j positive grid fine‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
          Q (width (schedule j)) m ξ ζ A C := by
  classical
  rw [unconditionalActualC485CanonicalVector_eq_correctedIdeal
    schedule ξ ζ j positive grid dimension fine]
  unfold integratorActualC485CleanedVector
  rw [unconditionalActualSelectedBranchLocalAction_sub,
    unconditionalActualSelectedBranchLocalAction_norm]
  exact unconditionalSelectedCopyMatchedBranch_deviation_sq
    Q width schedule ξ ζ A C j
    (unconditionalActualCanonicalRetainedPhaseTail
      (S := S) (B := B) (N := N) (d := d) (L := L) j)
    (integratorActualCanonicalRetainedPhaseTail_norm
      phases grid dimension j)

theorem unconditionalActualC485CleanDeviation_eq_hazard
    {S B N d L m : ℕ}
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (positive : ∀ s, 0 < width s)
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : ∀ s, (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ j : Fin L,
      ‖integratorActualC485CleanedVector
            (B := B) (m := m) Q width schedule ξ ζ A C j -
          integratorActualC485CanonicalVector
            (B := B) (m := m) schedule ξ ζ j
            (positive (schedule j)) grid (fine (schedule j))‖ ^ 2) =
      dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
        Q m width schedule ξ ζ A C := by
  classical
  simp_rw [unconditionalActualC485CleanDeviation_sq
    Q width schedule ξ ζ A C _ (positive _) phases grid dimension (fine _)]
  unfold dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
  simp_rw [
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq]

theorem unconditionalActualC485WeightedCleanDeviation_eq_hazard
    {ι : Type*} [Fintype ι]
    {S B N d L m : ℕ}
    (law : ι → ℝ)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : ι → BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (positive : ∀ s, 0 < width s)
    (phases : 0 < B) (grid : 0 < N) (dimension : 0 < d)
    (fine : ∀ s, (d : ℝ) / (N : ℝ) < 1 / (width s + 1)) :
    (∑ u : ι, law u *
      ∑ j : Fin L,
        ‖integratorActualC485CleanedVector
              (B := B) (m := m)
              Q width schedule (ξ u) (ζ u) A C j -
            integratorActualC485CanonicalVector
              (B := B) (m := m) schedule (ξ u) (ζ u) j
              (positive (schedule j)) grid (fine (schedule j))‖ ^ 2) =
      ∑ u : ι, law u *
        dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
          Q m width schedule (ξ u) (ζ u) A C := by
  classical
  apply Finset.sum_congr rfl
  intro u _
  rw [unconditionalActualC485CleanDeviation_eq_hazard
    Q width schedule (ξ u) (ζ u) A C positive phases grid dimension fine]

end

section

open scoped BigOperators

open QuantumParallelRepetition.ClassicalSampling

theorem unconditionalFairMatchedFlag_history_eq
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matched :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    exactSourceAlicePermutationHistory
        D denominator numerator nonempty flag x =
      exactSourceBobPermutationHistory
        D denominator numerator nonempty flag y := by
  classical
  change
    decide
      (exactSourceAlicePermutationHistory
          D denominator numerator nonempty flag x =
        exactSourceBobPermutationHistory
          D denominator numerator nonempty flag y) = true at matched
  exact of_decide_eq_true matched

theorem unconditionalFairMatchedFlag_bobTarget_eq_aliceSample
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matched :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    exactGlobalHistoryFinPhi G n S D
        (exactSourceBobPermutationHistory
          D denominator numerator nonempty flag y) y =
      exactGlobalHistoryFinPhi G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))).2.2.2 y := by
  have same := unconditionalFairMatchedFlag_history_eq
    D denominator numerator nonempty flag x y matched
  simp only [exactSourceAliceSampleTuple]
  rw [same]

theorem unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) :
    exactGlobalHistoryFinGamma G n S D
        (exactSourceAlicePermutationHistory
          D denominator numerator nonempty flag x) x =
      exactGlobalHistoryFinGamma G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))).2.2.2 x := by
  rfl

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

open Classical in
theorem unconditionalActualOneScaleDecodedMatchedCleanedVector
    {F X Y : Type} {P N d L m : ℕ}
    (Q : ℕ) (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ : F → X → BipartiteUnitVector d)
    (ζ : F → Y → BipartiteUnitVector d)
    (A C : Fin P → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ)
    (grid : 0 < N)
    (flag : F) (x : X) (y : Y) (j : Fin L)
    (positive : 0 < width (schedule j)) :
    unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        (unconditionalSourcePhysicalCleanedFullBilateralStateIsometry
          (unconditionalActualOneScaleFixedSourcePhaseSplit P) j
          (actualStoppingBranchVector
            (actualStoppingQuestionLocalAction
              (physical8OneScaleActualAliceStoppingUnitary
                (P := P) (N := N) (d := d) (L := L) (m := m)
                (unconditionalActualOneScaleFixedSourcePhaseSplit P)
                Q width schedule ξ A flag x)
              (physical8OneScaleActualBobStoppingUnitary
                (P := P) (N := N) (d := d) (L := L) (m := m)
                (unconditionalActualOneScaleFixedSourcePhaseSplit P)
                Q width schedule ζ C flag y)
              (unconditionalSourcePhysicalCleanedStoppingFixedSource
                1 P N d L m)) j.succ j.succ)) =
      integratorActualC485CleanedVector
        (S := 1) (B := P) (N := N) (d := d) (L := L) (m := m)
        Q width schedule (ξ flag x) (ζ flag y) A C j := by
  classical
  have decoded :=
    unconditionalActualOneScalePhysicalQuestionDecodedMatchedBranch
      Q width schedule ξ ζ A C grid flag x y j positive
  change
    unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        _ =
      unconditionalMixedConjugateSelectedBranchLocalAction
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVDensityRationalCanonicalAliceBasis (ξ flag x))))
        (unconditionalMixedConjugateSigmaAtomLift
          (m := N * m) P
          (conjugateUnitary
            (dSVUniformDensityThresholdLeftBobBasis (ζ flag y))))
        _
  rw [decoded]

/-- The positive operator-valued measurement implementing integrator actual c 485 source alice. -/
def integratorActualC485SourceAlicePOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (x : X) :
    POVM A
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact
    reindexedPOVM
      (finCongr
        (Nat.mul_one
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystAlicePOVM G n S D 1 a₀ x))

/-- The positive operator-valued measurement implementing integrator actual c 485 source bob. -/
def integratorActualC485SourceBobPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B) (y : Y) :
    POVM B
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact
    reindexedPOVM
      (finCongr
        (Nat.mul_one
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
      (unconditionalConjugatePOVM
        (exactSourceGlobalCatalystBobPOVM G n S D 1 b₀ y))

/-- The positive operator-valued measurement implementing integrator actual c 485 selected alice. -/
def integratorActualC485SelectedAlicePOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A)
    (P N m : ℕ) (x : X) :
    POVM A
      (UnconditionalSelectedCopyLocalIndex
        P (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        N m) := by
  classical
  exact
    directDSVActualReindexedRetainedPOVM
      (physical8SelectedGlobalTargetWorkEquiv
        P N (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) m)
      (integratorActualC485SourceAlicePOVM G n S D a₀ x)

/-- The positive operator-valued measurement implementing integrator actual c 485 selected bob. -/
def integratorActualC485SelectedBobPOVM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B)
    (P N m : ℕ) (y : Y) :
    POVM B
      (UnconditionalSelectedCopyLocalIndex
        P (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        N m) := by
  classical
  exact
    directDSVActualReindexedRetainedPOVM
      (physical8SelectedGlobalTargetWorkEquiv
        P N (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) m)
      (integratorActualC485SourceBobPOVM G n S D b₀ y)

/-- The measurement effect for integrator actual c 485 winning. -/
def integratorActualC485WinningEffect
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (j : Fin L) (x : X) (y : Y) :
    IntegratorActualC485BranchSpace
      1 P N
        (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
        L m j →L[ℂ]
      IntegratorActualC485BranchSpace
        1 P N
          (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))
          L m j := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let selected : Type := UnconditionalSelectedCopyLocalIndex
    P d N m
  let retained : Type :=
    IntegratorActualC485RetainedIndex 1 P N d L j
  exact Matrix.toEuclideanCLM
    (n := (selected × selected) × retained) (𝕜 := ℂ)
    (directDSVActualLocalPOVMWinningEffect G
      (integratorActualC485SelectedAlicePOVM
        G n S D a₀ P N m x)
      (integratorActualC485SelectedBobPOVM
        G n S D b₀ P N m y) x y ⊗ₖ
      (1 : Matrix retained retained ℂ))

theorem unconditionalActualFairSourceEmbezzlementOne_apply :
    embezzlementState 1 (0, 0) = 1 := by
  simp only [Fin.isValue, embezzlementState, rawEmbezzlementState, Fin.val_eq_zero,
    CharP.cast_eq_zero, zero_add, Real.sqrt_one, inv_one, ofReal_one, EuclideanSpace.norm_eq,
    Fintype.sum_prod_type, univ_unique, Fin.default_eq_zero, sum_singleton, ↓reduceIte, norm_one,
    one_pow, one_smul]

theorem unconditionalActualFairSourceTensorEmbezzlementOne_reindex
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (finCongr (Nat.mul_one d))
          (finCongr (Nat.mul_one d)))
        (tensorEmbezzlementTarget (n := 1) ξ) = ξ.val := by
  classical
  ext ⟨i, j⟩
  have first :
      (((finCongr (Nat.mul_one d)).symm i).divNat : Fin d) = i := by
    apply Fin.ext
    change i.val / 1 = i.val
    simp only [Nat.div_one]
  have second :
      (((finCongr (Nat.mul_one d)).symm j).divNat : Fin d) = j := by
    apply Fin.ext
    change j.val / 1 = j.val
    simp only [Nat.div_one]
  have first_work :
      (((finCongr (Nat.mul_one d)).symm i).modNat : Fin 1) = 0 :=
    Subsingleton.elim _ _
  have second_work :
      (((finCongr (Nat.mul_one d)).symm j).modNat : Fin 1) = 0 :=
    Subsingleton.elim _ _
  change
    ξ.val
        ((((finCongr (Nat.mul_one d)).symm i).divNat : Fin d),
         (((finCongr (Nat.mul_one d)).symm j).divNat : Fin d)) *
      embezzlementState 1
        ((((finCongr (Nat.mul_one d)).symm i).modNat : Fin 1),
         (((finCongr (Nat.mul_one d)).symm j).modNat : Fin 1)) =
      ξ.val (i, j)
  rw [first, second, first_work, second_work,
    unconditionalActualFairSourceEmbezzlementOne_apply, mul_one]

theorem
    unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (finCongr (Nat.mul_one d)).symm
          (finCongr (Nat.mul_one d)).symm)
        (unconditionalConjugatePureVector ξ.val) =
      unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ) := by
  classical
  ext ⟨i, j⟩
  change
    star (ξ.val
      ((finCongr (Nat.mul_one d)) i,
       (finCongr (Nat.mul_one d)) j)) =
      star (tensorEmbezzlementTarget (n := 1) ξ (i, j))
  congr 1
  have recovered := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) =>
      z ((finCongr (Nat.mul_one d)) i,
         (finCongr (Nat.mul_one d)) j))
    (unconditionalActualFairSourceTensorEmbezzlementOne_reindex ξ)
  simpa only [finCongr_apply, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    Equiv.prodCongr_symm, finCongr_symm, Equiv.prodCongr_apply, Prod.map_apply, Fin.cast_cast,
    Fin.cast_eq_self] using recovered.symm

theorem unconditionalActualFairSourceWinningEffect_reindex
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [decA : DecidableEq A] [decB : DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    (x : X) (y : Y) :
    directDSVActualLocalPOVMWinningEffect G
        (integratorActualC485SourceAlicePOVM G n S D a₀ x)
        (integratorActualC485SourceBobPOVM G n S D b₀ y)
        x y =
      Matrix.reindex
        (Equiv.prodCongr
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D))))
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))))
        (Equiv.prodCongr
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D))))
          (finCongr
            (Nat.mul_one
              (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))))
        (unconditionalConjugateSourceGlobalCatalystWinningEffect
          G n S D 1 a₀ b₀ x y) := by
  classical
  have alice_instance : decA = Classical.decEq A :=
    Subsingleton.elim _ _
  have bob_instance : decB = Classical.decEq B :=
    Subsingleton.elim _ _
  cases alice_instance
  cases bob_instance
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [directDSVActualLocalPOVMWinningEffect,
    integratorActualC485SourceAlicePOVM,
    integratorActualC485SourceBobPOVM,
    unconditionalConjugateSourceGlobalCatalystWinningEffect,
    reindexedPOVM, Matrix.reindex_apply,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map]

private def unconditionalActualFairSourceBaseWinningCLM
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    (x : X) (y : Y) :
    ExactSourceGlobalState G n S D →L[ℂ]
      ExactSourceGlobalState G n S D := by
  classical
  exact Matrix.toEuclideanCLM (𝕜 := ℂ)
    (directDSVActualLocalPOVMWinningEffect G
      (integratorActualC485SourceAlicePOVM G n S D a₀ x)
      (integratorActualC485SourceBobPOVM G n S D b₀ y)
      x y)

theorem unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
    {d : ℕ}
    (winning :
      Matrix (Fin (d * 1) × Fin (d * 1))
        (Fin (d * 1) × Fin (d * 1)) ℂ)
    (ξ : BipartiteUnitVector d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := Fin d × Fin d) (𝕜 := ℂ)
        (Matrix.reindex
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d)))
          (Equiv.prodCongr
            (finCongr (Nat.mul_one d))
            (finCongr (Nat.mul_one d))) winning))
      (unconditionalConjugatePureVector ξ.val) =
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
      (unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ)) := by
  classical
  let e : (Fin (d * 1) × Fin (d * 1)) ≃ (Fin d × Fin d) :=
    Equiv.prodCongr (finCongr (Nat.mul_one d))
      (finCongr (Nat.mul_one d))
  calc
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM
          (n := Fin (d * 1) × Fin (d * 1)) (𝕜 := ℂ) winning)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm
          (unconditionalConjugatePureVector ξ.val)) := by
          exact directDSVActualReindexedWinningEffect_quadratic
            e.symm winning
            (unconditionalConjugatePureVector ξ.val)
    _ = _ := by
          congr 1
          exact
            unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex
              ξ

theorem unconditionalActualFairSourceBaseSupportedBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (a₀ : A) (b₀ : B)
    (h : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D h ≠ 0) :
    quadraticExpectation
      (unconditionalActualFairSourceBaseWinningCLM
        G n S D a₀ b₀ h.2.1 h.2.2.1)
      (unconditionalConjugatePureVector
        (exactSourceTuplePsi G n S D h)) =
      exactSourceConditionalWinningProbability G n S D h := by
  classical
  unfold unconditionalActualFairSourceBaseWinningCLM
  calc
    _ = quadraticExpectation
          (Matrix.toEuclideanCLM
            (n :=
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)) ×
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D)))
            (𝕜 := ℂ)
            (Matrix.reindex
              (Equiv.prodCongr
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D))))
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D)))))
              (Equiv.prodCongr
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D))))
                (finCongr (Nat.mul_one
                  (Fintype.card
                    (ExactGlobalHistoryLocalIndex G n S D)))))
              (unconditionalConjugateSourceGlobalCatalystWinningEffect
                G n S D 1 a₀ b₀ h.2.1 h.2.2.1)))
          (unconditionalConjugatePureVector
            (exactSourceTuplePsi G n S D h)) := by
              congr 2
              exact unconditionalActualFairSourceWinningEffect_reindex
                G n S D a₀ b₀ h.2.1 h.2.2.1
    _ = quadraticExpectation
          (Matrix.toEuclideanCLM
            (n :=
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D) * 1) ×
              Fin (Fintype.card
                (ExactGlobalHistoryLocalIndex G n S D) * 1))
            (𝕜 := ℂ)
            (unconditionalConjugateSourceGlobalCatalystWinningEffect
              G n S D 1 a₀ b₀ h.2.1 h.2.2.1))
          (unconditionalConjugatePureVector
            (tensorEmbezzlementTarget (n := 1)
              (exactGlobalHistoryFinPsi
                G n S D h.2.2.2 h.2.1 h.2.2.1))) := by
              exact unconditionalActualFairSourceEOneReindexedGlobalWinningBorn
                (unconditionalConjugateSourceGlobalCatalystWinningEffect
                  G n S D 1 a₀ b₀ h.2.1 h.2.2.1)
                (exactGlobalHistoryFinPsi
                  G n S D h.2.2.2 h.2.1 h.2.2.1)
    _ = _ :=
      unconditionalConjugateSourceGlobalCatalystWinningEffect_law_supported
        G n S D positive 1 (by norm_num) a₀ b₀ h supported

private def unconditionalActualFairSourcePhaseHarmonicWork
    (P k : ℕ) :
    EuclideanSpace ℂ
      ((Fin P × Fin k) × (Fin P × Fin k)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodProdProdComm
      (Fin P) (Fin P) (Fin k) (Fin k))
    (unconditionalMatchedVerifierTensor
      (ePRState P) (embezzlementState k))

theorem unconditionalActualFairSourcePhaseHarmonicWork_norm
    {P k : ℕ} (phases : 0 < P) (harmonic : 0 < k) :
    ‖unconditionalActualFairSourcePhaseHarmonicWork P k‖ = 1 := by
  unfold unconditionalActualFairSourcePhaseHarmonicWork
  rw [LinearIsometryEquiv.norm_map,
    unconditionalMatchedVerifierTensor_norm,
    ePRState_norm P phases,
    embezzlementState_norm k harmonic]
  norm_num

theorem unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct
    {P N d m : ℕ}
    (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (directDSVActualBilateralRetainedIndexEquiv
          (physical8SelectedGlobalTargetWorkEquiv P N d m)
          (physical8SelectedGlobalTargetWorkEquiv P N d m))
        (dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
          (unconditionalConjugatePureVector ψ)
          (fun _ _ _ => embezzlementState (N * m))) =
      unconditionalMatchedVerifierTensor
        (unconditionalConjugatePureVector ψ)
        (unconditionalActualFairSourcePhaseHarmonicWork
          P (N * m)) := by
  classical
  ext ⟨⟨i, j⟩, ⟨⟨p, a⟩, ⟨q, b⟩⟩⟩
  simp only [directDSVActualBilateralRetainedIndexEquiv, physical8SelectedGlobalTargetWorkEquiv,
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalPublicBucketCoherentPhaseHistory, unconditionalConjugatePureVector_apply,
    RCLike.star_def, mul_comm, mul_left_comm, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_trans, Equiv.prodProdProdComm_symm, Equiv.prodCongr_symm,
    Equiv.symm_mk, Equiv.trans_apply, Equiv.prodProdProdComm_apply, Equiv.prodCongr_apply,
    Equiv.coe_fn_mk, Prod.map_apply, unconditionalMatchedVerifierTensor,
    unconditionalActualFairSourcePhaseHarmonicWork, mul_assoc]

theorem unconditionalActualFairSourceSelectedBorn_of_base
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (x : X) (y : Y)
    (ψ : EuclideanSpace ℂ
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
       Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
    (value : ℝ)
    (base_born :
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          UnconditionalSelectedCopyLocalIndex
            P (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) N m ×
          UnconditionalSelectedCopyLocalIndex
            P (Fintype.card
              (ExactGlobalHistoryLocalIndex G n S D)) N m)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (integratorActualC485SelectedAlicePOVM
            G n S D a₀ P N m x)
          (integratorActualC485SelectedBobPOVM
            G n S D b₀ P N m y) x y))
      (dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
        (unconditionalConjugatePureVector ψ)
        (fun _ _ _ => embezzlementState (N * m))) = value := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let e := physical8SelectedGlobalTargetWorkEquiv P N d m
  let stage := dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
    (unconditionalConjugatePureVector ψ)
    (fun _ _ _ => embezzlementState (N * m))
  let work := unconditionalActualFairSourcePhaseHarmonicWork
    P (N * m)
  have work_unit : ‖work‖ = 1 :=
    unconditionalActualFairSourcePhaseHarmonicWork_norm
      phases (Nat.mul_pos grid harmonic)
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          UnconditionalSelectedCopyLocalIndex P d N m ×
          UnconditionalSelectedCopyLocalIndex P d N m)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (directDSVActualReindexedRetainedPOVM e
            (integratorActualC485SourceAlicePOVM G n S D a₀ x))
          (directDSVActualReindexedRetainedPOVM e
            (integratorActualC485SourceBobPOVM G n S D b₀ y)) x y))
      stage = value
  rw [directDSVActualReindexedRetainedPOVMWinningEffect_tensor_quadratic
    G e e
    (integratorActualC485SourceAlicePOVM G n S D a₀ x)
    (integratorActualC485SourceBobPOVM G n S D b₀ y)
    x y stage (unconditionalConjugatePureVector ψ) work
    (unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct ψ)]
  change
    ‖work‖ ^ 2 *
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value
  rw [work_unit, one_pow, one_mul, base_born]

theorem unconditionalActualFairSourceOuterBorn_of_base
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B)
    {P N L m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (ξ ζ : BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)))
    (ψ : EuclideanSpace ℂ
      (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
       Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D))))
    (ψ_unit : ‖ψ‖ = 1)
    (j : Fin L) (x : X) (y : Y) (value : ℝ)
    (base_born :
      quadraticExpectation
        (unconditionalActualFairSourceBaseWinningCLM
          G n S D a₀ b₀ x y)
        (unconditionalConjugatePureVector ψ) = value) :
    quadraticExpectation
      (integratorActualC485WinningEffect
        G n S D a₀ b₀ (P := P) (N := N) (m := m) j x y)
      (integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule ξ ζ ψ j) =
      ‖integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule ξ ζ ψ j‖ ^ 2 * value := by
  classical
  let d : ℕ :=
    Fintype.card (ExactGlobalHistoryLocalIndex G n S D)
  let stage := dSVDensityRationalPublicBucketCoherentPhaseSigmaState P
    (unconditionalConjugatePureVector ψ)
    (fun _ _ _ => embezzlementState (N * m))
  let retained := integratorActualC485NormalizedDiagonalWork
    (B := P) (N := N) width schedule ξ ζ j
  have selected_born :
      quadraticExpectation
        (Matrix.toEuclideanCLM
          (n :=
            UnconditionalSelectedCopyLocalIndex P d N m ×
            UnconditionalSelectedCopyLocalIndex P d N m)
          (𝕜 := ℂ)
          (directDSVActualLocalPOVMWinningEffect G
            (integratorActualC485SelectedAlicePOVM
              G n S D a₀ P N m x)
            (integratorActualC485SelectedBobPOVM
              G n S D b₀ P N m y) x y))
        stage = value :=
    unconditionalActualFairSourceSelectedBorn_of_base
      G n S D a₀ b₀ phases grid harmonic x y ψ value base_born
  have stage_unit : ‖stage‖ = 1 := by
    calc
      ‖stage‖ =
          ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
            (directDSVActualBilateralRetainedIndexEquiv
              (physical8SelectedGlobalTargetWorkEquiv P N d m)
              (physical8SelectedGlobalTargetWorkEquiv P N d m))
            stage‖ := by rw [LinearIsometryEquiv.norm_map]
      _ = ‖unconditionalMatchedVerifierTensor
            (unconditionalConjugatePureVector ψ)
            (unconditionalActualFairSourcePhaseHarmonicWork
              P (N * m))‖ := by
              rw [unconditionalActualFairSourcePhaseHarmonicStage_sourceProduct]
      _ = 1 := by
            rw [unconditionalMatchedVerifierTensor_norm,
              unconditionalConjugatePureVector_norm, ψ_unit,
              unconditionalActualFairSourcePhaseHarmonicWork_norm
                phases (Nat.mul_pos grid harmonic)]
            norm_num
  change
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n :=
          (UnconditionalSelectedCopyLocalIndex P d N m ×
           UnconditionalSelectedCopyLocalIndex P d N m) ×
          IntegratorActualC485RetainedIndex 1 P N d L j)
        (𝕜 := ℂ)
        (directDSVActualLocalPOVMWinningEffect G
          (integratorActualC485SelectedAlicePOVM
            G n S D a₀ P N m x)
          (integratorActualC485SelectedBobPOVM
            G n S D b₀ P N m y) x y ⊗ₖ
          (1 : Matrix
            (IntegratorActualC485RetainedIndex 1 P N d L j)
            (IntegratorActualC485RetainedIndex 1 P N d L j) ℂ)))
      (unconditionalMatchedVerifierTensor stage retained) =
        ‖unconditionalMatchedVerifierTensor stage retained‖ ^ 2 * value
  rw [unconditionalMatchedVerifierEffect_tensor_quadratic,
    selected_born, unconditionalMatchedVerifierTensor_norm_sq,
    stage_unit]
  ring

theorem unconditionalActualFairSourceSupportedBorn
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (a₀ : A) (b₀ : B)
    (h : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D h ≠ 0)
    {P N L m : ℕ} (phases : 0 < P) (grid : 0 < N)
    (harmonic : 0 < m)
    (width : Fin 1 → ℝ) (schedule : Fin L → Fin 1)
    (j : Fin L) :
    quadraticExpectation
      (integratorActualC485WinningEffect
        G n S D a₀ b₀ (P := P) (N := N) (m := m)
        j h.2.1 h.2.2.1)
      (integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule
        (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        (exactSourceTuplePsi G n S D h) j) =
      ‖integratorActualC485SourceVector
        (B := P) (N := N) (m := m) width schedule
        (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
        (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
        (exactSourceTuplePsi G n S D h) j‖ ^ 2 *
        exactSourceConditionalWinningProbability G n S D h := by
  classical
  exact
    unconditionalActualFairSourceOuterBorn_of_base
      G n S D a₀ b₀ phases grid harmonic width schedule
      (exactGlobalHistoryFinGamma G n S D h.2.2.2 h.2.1)
      (exactGlobalHistoryFinPhi G n S D h.2.2.2 h.2.2.1)
      (exactSourceTuplePsi G n S D h)
      (exactSourceTuplePsi_norm G n S D h)
      j h.2.1 h.2.2.1
      (exactSourceConditionalWinningProbability G n S D h)
      (unconditionalActualFairSourceBaseSupportedBorn
        G n S D positive a₀ b₀ h supported)

end

end QuantumParallelRepetition

end
