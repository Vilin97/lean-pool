/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Quantum parallel repetition, part 01 -/

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part one. -/
noncomputable local instance matrixComplexContinuousENormPartOne
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

/-- The local matrix norm instance used while elaborating part one. -/
noncomputable local instance matrixComplexESeminormedAddCommMonoidPartOne
    {m n : Type*} [Fintype m] [Fintype n] :
    ESeminormedAddCommMonoid (Matrix m n ℂ) :=
  let base := @NormedAddCommGroup.toENormedAddCommMonoid (Matrix m n ℂ)
    Matrix.normedAddCommGroup
  { toContinuousENorm := inferInstance
    toAddCommMonoid := base.toAddCommMonoid
    enorm_zero := base.enorm_zero
    enorm_add_le := base.enorm_add_le }

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*}

/-- A finite two-player nonlocal game with a question distribution and winning predicate. -/
structure Game (X Y A B : Type*)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] where
  /-- The probability weight assigned to a pair of questions. -/
  questionWeight : X → Y → ℝ
  weight_nonneg : ∀ x y, 0 ≤ questionWeight x y
  weight_normalized : (∑ x : X, ∑ y : Y, questionWeight x y) = 1
  /-- The Boolean predicate deciding whether a pair of answers wins. -/
  predicate : X → Y → A → B → Bool

namespace Game

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The first-question marginal of a game. -/
def marginalX (G : Game X Y A B) (x : X) : ℝ :=
  ∑ y : Y, G.questionWeight x y

/-- The second-question marginal of a game. -/
def marginalY (G : Game X Y A B) (y : Y) : ℝ :=
  ∑ x : X, G.questionWeight x y

theorem marginalX_nonneg (G : Game X Y A B) (x : X) :
    0 ≤ G.marginalX x := by
  unfold marginalX
  exact Finset.sum_nonneg fun y _ => G.weight_nonneg x y

theorem marginalY_nonneg (G : Game X Y A B) (y : Y) :
    0 ≤ G.marginalY y := by
  unfold marginalY
  exact Finset.sum_nonneg fun x _ => G.weight_nonneg x y

theorem marginalX_normalized (G : Game X Y A B) :
    (∑ x : X, G.marginalX x) = 1 := by
  simpa only [marginalX] using G.weight_normalized

theorem marginalY_normalized (G : Game X Y A B) :
    (∑ y : Y, G.marginalY y) = 1 := by
  unfold marginalY
  rw [Finset.sum_comm]
  exact G.weight_normalized

/-- The coordinatewise repeated game. -/
def «repeat» (G : Game X Y A B) (n : ℕ) :
    Game (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) where
  questionWeight xs ys := ∏ i : Fin n, G.questionWeight (xs i) (ys i)
  weight_nonneg xs ys :=
    Finset.prod_nonneg fun i _ => G.weight_nonneg (xs i) (ys i)
  weight_normalized := by
    classical
    calc
      (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        ∏ i : Fin n, G.questionWeight (xs i) (ys i)) =
          ∑ xs : Fin n → X, ∏ i : Fin n, ∑ y : Y,
            G.questionWeight (xs i) y := by
              apply Finset.sum_congr rfl
              intro xs _
              exact (Fintype.prod_sum
                (fun i : Fin n => fun y : Y => G.questionWeight (xs i) y)).symm
      _ = ∏ _i : Fin n, ∑ x : X, ∑ y : Y,
            G.questionWeight x y := by
              exact (Fintype.prod_sum
                (fun _i : Fin n => fun x : X => ∑ y : Y,
                  G.questionWeight x y)).symm
      _ = 1 := by simp only [G.weight_normalized, Finset.prod_const_one]
  predicate xs ys as bs :=
    decide (∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true)

@[simp] theorem repeat_questionWeight (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y) :
    (G.repeat n).questionWeight xs ys =
      ∏ i : Fin n, G.questionWeight (xs i) (ys i) := rfl

@[simp] theorem repeat_predicate_eq_true (G : Game X Y A B) (n : ℕ)
    (xs : Fin n → X) (ys : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) :
    (G.repeat n).predicate xs ys as bs = true ↔
      ∀ i : Fin n, G.predicate (xs i) (ys i) (as i) (bs i) = true := by
  simp only [«repeat», decide_eq_true_eq]

end Game

/-- A finite-dimensional positive semidefinite matrix of trace one. -/
structure DensityMatrix (d : Type*) [Fintype d] where
  /-- The matrix underlying a density matrix. -/
  matrix : Matrix d d ℂ
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1

/-- A finite-outcome positive operator-valued measurement. -/
structure POVM (ι d : Type*) [Fintype ι] [Fintype d] [DecidableEq d] where
  /-- The positive operator associated with a measurement outcome. -/
  effect : ι → Matrix d d ℂ
  positive : ∀ i, (effect i).PosSemidef
  complete : (∑ i : ι, effect i) = 1

/-- A finite-dimensional entangled strategy for a nonlocal game. -/
structure Strategy [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (_G : Game X Y A B) where
  /-- Alice's finite Hilbert-space basis type. -/
  Alice : Type
  /-- Bob's finite Hilbert-space basis type. -/
  Bob : Type
  [aliceFintype : Fintype Alice]
  [bobFintype : Fintype Bob]
  [aliceDecidableEq : DecidableEq Alice]
  [bobDecidableEq : DecidableEq Bob]
  /-- The shared bipartite state of the strategy. -/
  state : DensityMatrix (Alice × Bob)
  /-- Alice's measurement for each question. -/
  aliceMeasurement : X → POVM A Alice
  /-- Bob's measurement for each question. -/
  bobMeasurement : Y → POVM B Bob

attribute [instance] Strategy.aliceFintype Strategy.bobFintype
  Strategy.aliceDecidableEq Strategy.bobDecidableEq

theorem trace_mul_posSemidef_nonneg {d : Type*} [Fintype d]
    {R E : Matrix d d ℂ} (hR : R.PosSemidef) (hE : E.PosSemidef) :
    0 ≤ (Matrix.trace (R * E)).re := by
  classical
  obtain ⟨K, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hR.nonneg
  have hpositive : (K * E * star K).PosSemidef := by
    simpa only [star_eq_conjTranspose] using hE.mul_mul_conjTranspose_same K
  have htrace : 0 ≤ (Matrix.trace (K * E * star K)).re :=
    (Complex.nonneg_iff.mp hpositive.trace_nonneg).1
  rw [Matrix.trace_mul_cycle] at htrace
  exact htrace

namespace Strategy

variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

private def jointEffect (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  (S.aliceMeasurement x).effect a ⊗ₖ (S.bobMeasurement y).effect b

theorem jointEffect_positive (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (S.jointEffect x y a b).PosSemidef := by
  exact ((S.aliceMeasurement x).positive a).kronecker
    ((S.bobMeasurement y).positive b)

/-- The Born probability of a question-and-answer outcome. -/
def outcomeProbability (S : Strategy G) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  (Matrix.trace (S.state.matrix * S.jointEffect x y a b)).re

theorem outcomeProbability_nonneg (S : Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.outcomeProbability x y a b := by
  exact trace_mul_posSemidef_nonneg S.state.positive
    (S.jointEffect_positive x y a b)

theorem jointEffect_complete (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.jointEffect x y a b) = 1 := by
  classical
  calc
    (∑ a : A, ∑ b : B, S.jointEffect x y a b) =
        (∑ a : A, (S.aliceMeasurement x).effect a) ⊗ₖ
          (∑ b : B, (S.bobMeasurement y).effect b) := by
            ext ⟨i, j⟩ ⟨k, l⟩
            simp only [jointEffect, Matrix.sum_apply, Matrix.kroneckerMap_apply]
            rw [Finset.sum_mul]
            simp_rw [Finset.mul_sum]
    _ = 1 := by
      rw [(S.aliceMeasurement x).complete, (S.bobMeasurement y).complete]
      exact Matrix.one_kronecker_one

theorem outcomeProbability_normalized (S : Strategy G) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) = 1 := by
  classical
  calc
    (∑ a : A, ∑ b : B, S.outcomeProbability x y a b) =
        (Matrix.trace
          (S.state.matrix * (∑ a : A, ∑ b : B, S.jointEffect x y a b))).re := by
            simp only [outcomeProbability, Matrix.mul_sum, trace_sum, Complex.re_sum]
    _ = (Matrix.trace S.state.matrix).re := by
      rw [S.jointEffect_complete x y]
      simp only [mul_one]
    _ = 1 := by rw [S.state.trace_one]; rfl

/-- The winning probability of the strategy. -/
def winProbability (S : Strategy G) : ℝ :=
  ∑ x : X, ∑ y : Y, G.questionWeight x y *
    ∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then S.outcomeProbability x y a b else 0

theorem winProbability_nonneg (S : Strategy G) : 0 ≤ S.winProbability := by
  unfold winProbability
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  apply mul_nonneg (G.weight_nonneg x y)
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split <;> simp [S.outcomeProbability_nonneg]

theorem winProbability_le_one (S : Strategy G) : S.winProbability ≤ 1 := by
  classical
  have hxy (x : X) (y : Y) :
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then S.outcomeProbability x y a b else 0) ≤ 1 := by
    calc
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then S.outcomeProbability x y a b else 0) ≤
          ∑ a : A, ∑ b : B, S.outcomeProbability x y a b := by
            apply Finset.sum_le_sum
            intro a _
            apply Finset.sum_le_sum
            intro b _
            split
            · exact le_rfl
            · exact S.outcomeProbability_nonneg x y a b
      _ = 1 := S.outcomeProbability_normalized x y
  calc
    S.winProbability =
        ∑ x : X, ∑ y : Y, G.questionWeight x y *
          (∑ a : A, ∑ b : B,
            if G.predicate x y a b = true then S.outcomeProbability x y a b else 0) := rfl
    _ ≤ ∑ x : X, ∑ y : Y, G.questionWeight x y * 1 := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hxy x y) (G.weight_nonneg x y)
    _ = 1 := by simpa only [mul_one] using G.weight_normalized

end Strategy

/-- The supremal winning probability over finite-dimensional entangled strategies. -/
def entangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) : ℝ :=
  sSup (Set.range (Strategy.winProbability (G := G)))

theorem winProbabilities_bddAbove [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : Game X Y A B) :
    BddAbove (Set.range (Strategy.winProbability (G := G))) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨S, rfl⟩
  exact S.winProbability_le_one

theorem entangledValue_le_one [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : Game X Y A B) :
    entangledValue G ≤ 1 := by
  unfold entangledValue
  by_cases h : (Set.range (Strategy.winProbability (G := G))).Nonempty
  · apply csSup_le h
    rintro _ ⟨S, rfl⟩
    exact S.winProbability_le_one
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]
    exact zero_le_one

theorem entangledValue_nonneg [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : Game X Y A B) :
    0 ≤ entangledValue G := by
  unfold entangledValue
  by_cases h : (Set.range (Strategy.winProbability (G := G))).Nonempty
  · rcases h with ⟨_, S, rfl⟩
    exact le_trans S.winProbability_nonneg
      (le_csSup (winProbabilities_bddAbove G) ⟨S, rfl⟩)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]

/-- The entangled value of a coordinatewise repeated game. -/
def repeatedEntangledValue [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) : ℝ :=
  entangledValue (G.repeat n)

end

section

open scoped BigOperators ComplexConjugate InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The quadratic expectation construction used in the quantum parallel-repetition argument. -/
def quadraticExpectation (W : H →L[ℂ] H) (z : H) : ℝ :=
  (⟪z, W z⟫_ℂ).re

theorem positive_quadraticExpectation_nonneg
    (W : H →L[ℂ] H) (hW : W.IsPositive) (z : H) :
    0 ≤ quadraticExpectation W z := by
  exact hW.re_inner_nonneg_right z

theorem positive_complement_quadraticExpectation_le
    (W : H →L[ℂ] H)
    (h_complement : (1 - W).IsPositive) (z : H) :
    quadraticExpectation W z ≤ ‖z‖ ^ 2 := by
  have h := h_complement.re_inner_nonneg_right z
  have hnorm : (⟪z, z⟫_ℂ).re = ‖z‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp only [Complex.coe_algebraMap, pow_two, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  change 0 ≤ (⟪z, z - W z⟫_ℂ).re at h
  rw [inner_sub_right, Complex.sub_re, hnorm] at h
  unfold quadraticExpectation
  exact sub_nonneg.mp h

theorem norm_le_of_operator_contraction
    (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1) (z : H) :
    ‖W z‖ ≤ ‖z‖ := by
  calc
    ‖W z‖ ≤ ‖W‖ * ‖z‖ := W.le_opNorm z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg z)
    _ = ‖z‖ := one_mul _

theorem quadraticExpectation_sub_le
    (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1) (z w : H) :
    |quadraticExpectation W z - quadraticExpectation W w| ≤
      (‖z‖ + ‖w‖) * ‖z - w‖ := by
  have h_expand :
      ⟪z, W z⟫_ℂ - ⟪w, W w⟫_ℂ =
        ⟪z - w, W z⟫_ℂ + ⟪w, W (z - w)⟫_ℂ := by
    simp only [CStarModule.inner_sub_left, map_sub, CStarModule.inner_sub_right,
      sub_add_sub_cancel]
  have hz := norm_le_of_operator_contraction W hW z
  have hdiff := norm_le_of_operator_contraction W hW (z - w)
  unfold quadraticExpectation
  calc
    |(⟪z, W z⟫_ℂ).re - (⟪w, W w⟫_ℂ).re| =
        |(⟪z, W z⟫_ℂ - ⟪w, W w⟫_ℂ).re| := by
          rw [Complex.sub_re]
    _ ≤ ‖⟪z, W z⟫_ℂ - ⟪w, W w⟫_ℂ‖ :=
      Complex.abs_re_le_norm _
    _ = ‖⟪z - w, W z⟫_ℂ + ⟪w, W (z - w)⟫_ℂ‖ := by
      rw [h_expand]
    _ ≤ ‖⟪z - w, W z⟫_ℂ‖ + ‖⟪w, W (z - w)⟫_ℂ‖ :=
      norm_add_le _ _
    _ ≤ ‖z - w‖ * ‖W z‖ + ‖w‖ * ‖W (z - w)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖z - w‖ * ‖z‖ + ‖w‖ * ‖z - w‖ := by
      gcongr
    _ = (‖z‖ + ‖w‖) * ‖z - w‖ := by ring

theorem weighted_real_cauchy
    {ι : Type*} [Fintype ι]
    (weight f g : ι → ℝ)
    (h_weight : ∀ i, 0 ≤ weight i) :
    (∑ i : ι, weight i * f i * g i) ≤
      Real.sqrt (∑ i : ι, weight i * f i ^ 2) *
        Real.sqrt (∑ i : ι, weight i * g i ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i : ι => Real.sqrt (weight i) * f i)
    (fun i : ι => Real.sqrt (weight i) * g i)
  have hsq (i : ι) : Real.sqrt (weight i) ^ 2 = weight i :=
    Real.sq_sqrt (h_weight i)
  have h_left :
      (∑ i : ι,
        (Real.sqrt (weight i) * f i) *
          (Real.sqrt (weight i) * g i)) =
        ∑ i : ι, weight i * f i * g i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      (Real.sqrt (weight i) * f i) *
          (Real.sqrt (weight i) * g i) =
        Real.sqrt (weight i) ^ 2 * f i * g i := by ring
      _ = weight i * f i * g i := by rw [hsq i]
  have h_f :
      (∑ i : ι, (Real.sqrt (weight i) * f i) ^ 2) =
        ∑ i : ι, weight i * f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, hsq i]
  have h_g :
      (∑ i : ι, (Real.sqrt (weight i) * g i) ^ 2) =
        ∑ i : ι, weight i * g i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, hsq i]
  simpa only [ge_iff_le, h_left, h_f, h_g] using h

end

section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem matrixEffectCLM_isPositive
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : E.PosSemidef) :
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E).IsPositive := by
  apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hE

theorem matrixEffectCLM_complement_isPositive
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : (1 - E).PosSemidef) :
    (1 - Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E).IsPositive := by
  simpa only [map_sub, map_one] using matrixEffectCLM_isPositive (1 - E) hE

namespace Strategy

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}

/-- The measurement effect for winning. -/
def winningEffect (S : Strategy G) (x : X) (y : Y) :
    Matrix (S.Alice × S.Bob) (S.Alice × S.Bob) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then S.jointEffect x y a b else 0

theorem winningEffect_born
    (S : Strategy G) (x : X) (y : Y) :
    (Matrix.trace (S.state.matrix * S.winningEffect x y)).re =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          S.outcomeProbability x y a b else 0 := by
  classical
  simp only [winningEffect, Matrix.mul_sum, mul_ite, mul_zero, Matrix.trace_sum, Complex.re_sum,
    outcomeProbability]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp

theorem winProbability_eq_winningEffect_born
    (S : Strategy G) :
    S.winProbability =
      ∑ x : X, ∑ y : Y,
        G.questionWeight x y *
          (Matrix.trace (S.state.matrix * S.winningEffect x y)).re := by
  simp_rw [S.winningEffect_born]
  rfl

end Strategy

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}

theorem posSemidef_blockDiagonal'
    {ι : Type*} [Finite ι] [DecidableEq ι]
    {d : ι → Type*} [∀ j, Finite (d j)]
    (M : ∀ j, Matrix (d j) (d j) ℂ)
    (hM : ∀ j, (M j).PosSemidef) :
    (Matrix.blockDiagonal' M).PosSemidef := by
  classical
  let _ := Fintype.ofFinite ι
  let _ (j : ι) := Fintype.ofFinite (d j)
  choose K hK using fun j =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hM j).nonneg
  apply Matrix.LE.le.posSemidef
  apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
  refine ⟨Matrix.blockDiagonal' K, ?_⟩
  calc
    Matrix.blockDiagonal' M =
        Matrix.blockDiagonal' (fun j => star (K j) * K j) := by
          congr 1
          funext j
          exact hK j
    _ = star (Matrix.blockDiagonal' K) * Matrix.blockDiagonal' K := by
          simp only [star_eq_conjTranspose, blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]

private abbrev mixtureAlice (S : J → Strategy G) := Σ j : J, (S j).Alice

private abbrev mixtureBob (S : J → Strategy G) := Σ j : J, (S j).Bob

private abbrev mixtureMatched (S : J → Strategy G) :=
  Σ j : J, (S j).Alice × (S j).Bob

private def mixtureMatchedIndex (S : J → Strategy G) :
    mixtureMatched S → mixtureAlice S × mixtureBob S
  | ⟨j, (a, b)⟩ => (⟨j, a⟩, ⟨j, b⟩)

omit [Fintype J] [DecidableEq J] in
theorem mixtureMatchedIndex_injective (S : J → Strategy G) :
    Function.Injective (mixtureMatchedIndex S) := by
  rintro ⟨i, a, b⟩ ⟨j, c, d⟩ h
  have hflag : i = j := congrArg (fun q => q.1.1) h
  subst j
  have ha : a = c :=
    eq_of_heq (Sigma.mk.inj (congrArg Prod.fst h)).2
  have hb : b = d :=
    eq_of_heq (Sigma.mk.inj (congrArg Prod.snd h)).2
  subst c
  subst d
  rfl

private def mixtureEmbedding (S : J → Strategy G) :
    Matrix (mixtureAlice S × mixtureBob S) (mixtureMatched S) ℂ := by
  classical
  exact fun q r => if q = mixtureMatchedIndex S r then 1 else 0

theorem mixtureEmbedding_isometry (S : J → Strategy G) :
    (mixtureEmbedding S)ᴴ * mixtureEmbedding S = 1 := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.mul_apply, conjTranspose_apply, mixtureEmbedding, RCLike.star_def,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, one_apply_eq]
  · have hindex : mixtureMatchedIndex S i ≠ mixtureMatchedIndex S j :=
      fun hij => h (mixtureMatchedIndex_injective S hij)
    simp only [Matrix.mul_apply, conjTranspose_apply, mixtureEmbedding, RCLike.star_def,
      MonoidWithZeroHom.map_ite_one_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, hindex.symm, ne_eq, h, not_false_eq_true, one_apply_ne]

theorem mixtureEmbedding_compress (S : J → Strategy G)
    (E : Matrix (mixtureAlice S × mixtureBob S)
      (mixtureAlice S × mixtureBob S) ℂ) :
    (mixtureEmbedding S)ᴴ * E * mixtureEmbedding S =
      E.submatrix (mixtureMatchedIndex S) (mixtureMatchedIndex S) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply, mixtureEmbedding, RCLike.star_def,
    MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, mul_ite, mul_one, mul_zero, submatrix_apply]

private def mixtureBlockMatrix (p : J → ℝ) (S : J → Strategy G) :
    Matrix (mixtureMatched S) (mixtureMatched S) ℂ :=
  Matrix.blockDiagonal' fun j => p j • (S j).state.matrix

omit [Fintype J] in
theorem mixtureBlockMatrix_posSemidef
    [Finite J]
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (S : J → Strategy G) :
    (mixtureBlockMatrix p S).PosSemidef := by
  unfold mixtureBlockMatrix
  apply posSemidef_blockDiagonal'
  intro j
  exact (S j).state.positive.smul (hp j)

theorem mixtureBlockMatrix_trace
    (p : J → ℝ) (S : J → Strategy G) :
    Matrix.trace (mixtureBlockMatrix p S) =
      (↑(∑ j : J, p j) : ℂ) := by
  unfold mixtureBlockMatrix
  rw [Matrix.trace_blockDiagonal']
  simp only [trace_smul, DensityMatrix.trace_one, Complex.real_smul, mul_one, Complex.ofReal_sum]

private def mixtureDensityMatrix (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) :
    DensityMatrix (mixtureAlice S × mixtureBob S) where
  matrix := mixtureEmbedding S * mixtureBlockMatrix p S *
    (mixtureEmbedding S)ᴴ
  positive :=
    (mixtureBlockMatrix_posSemidef p hp S).mul_mul_conjTranspose_same
      (mixtureEmbedding S)
  trace_one := by
    rw [Matrix.trace_mul_cycle, mixtureEmbedding_isometry,
      Matrix.one_mul, mixtureBlockMatrix_trace, h_normalized]
    norm_num

private def mixtureAlicePOVM (S : J → Strategy G) (x : X) :
    POVM A (mixtureAlice S) where
  effect a := Matrix.blockDiagonal' fun j =>
    ((S j).aliceMeasurement x).effect a
  positive a := by
    apply posSemidef_blockDiagonal'
    intro j
    exact ((S j).aliceMeasurement x).positive a
  complete := by
    classical
    ext ⟨i, u⟩ ⟨j, v⟩
    by_cases h : i = j
    · subst j
      have h_complete := congrArg
        (fun M : Matrix (S i).Alice (S i).Alice ℂ => M u v)
        ((S i).aliceMeasurement x).complete
      simpa only [Matrix.sum_apply, blockDiagonal'_apply, ↓reduceDIte, cast_eq, Matrix.one_apply,
        Sigma.mk.injEq, heq_eq_eq, true_and] using h_complete
    · simp only [Matrix.sum_apply, blockDiagonal'_apply, h, ↓reduceDIte, Finset.sum_const_zero,
        ne_eq, Sigma.mk.injEq, false_and, not_false_eq_true, one_apply_ne]

private def mixtureBobPOVM (S : J → Strategy G) (y : Y) :
    POVM B (mixtureBob S) where
  effect b := Matrix.blockDiagonal' fun j =>
    ((S j).bobMeasurement y).effect b
  positive b := by
    apply posSemidef_blockDiagonal'
    intro j
    exact ((S j).bobMeasurement y).positive b
  complete := by
    classical
    ext ⟨i, u⟩ ⟨j, v⟩
    by_cases h : i = j
    · subst j
      have h_complete := congrArg
        (fun M : Matrix (S i).Bob (S i).Bob ℂ => M u v)
        ((S i).bobMeasurement y).complete
      simpa only [Matrix.sum_apply, blockDiagonal'_apply, ↓reduceDIte, cast_eq, Matrix.one_apply,
        Sigma.mk.injEq, heq_eq_eq, true_and] using h_complete
    · simp only [Matrix.sum_apply, blockDiagonal'_apply, h, ↓reduceDIte, Finset.sum_const_zero,
        ne_eq, Sigma.mk.injEq, false_and, not_false_eq_true, one_apply_ne]

private def convexMixtureStrategy (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) : Strategy G where
  Alice := mixtureAlice S
  Bob := mixtureBob S
  aliceFintype := inferInstance
  bobFintype := inferInstance
  aliceDecidableEq := inferInstance
  bobDecidableEq := inferInstance
  state := mixtureDensityMatrix p hp h_normalized S
  aliceMeasurement := mixtureAlicePOVM S
  bobMeasurement := mixtureBobPOVM S

theorem mixtureJointEffect_compress (S : J → Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    (((mixtureAlicePOVM S x).effect a ⊗ₖ
      (mixtureBobPOVM S y).effect b).submatrix
        (mixtureMatchedIndex S) (mixtureMatchedIndex S)) =
      Matrix.blockDiagonal' fun j =>
        (S j).jointEffect x y a b := by
  classical
  ext ⟨i, u, v⟩ ⟨j, u', v'⟩
  by_cases h : i = j
  · subst j
    simp only [mixtureAlicePOVM, mixtureBobPOVM, submatrix_apply, mixtureMatchedIndex,
      kroneckerMap_apply, blockDiagonal'_apply, ↓reduceDIte, cast_eq, Strategy.jointEffect]
  · simp only [mixtureAlicePOVM, mixtureBobPOVM, submatrix_apply, mixtureMatchedIndex,
      kroneckerMap_apply, blockDiagonal'_apply, h, ↓reduceDIte, mul_zero, Strategy.jointEffect]

theorem mixtureEmbedding_trace_mul (S : J → Strategy G)
    (R : Matrix (mixtureMatched S) (mixtureMatched S) ℂ)
    (E : Matrix (mixtureAlice S × mixtureBob S)
      (mixtureAlice S × mixtureBob S) ℂ) :
    Matrix.trace
      ((mixtureEmbedding S * R * (mixtureEmbedding S)ᴴ) * E) =
      Matrix.trace
        (R * E.submatrix (mixtureMatchedIndex S)
          (mixtureMatchedIndex S)) := by
  calc
    Matrix.trace
        ((mixtureEmbedding S * R * (mixtureEmbedding S)ᴴ) * E) =
        Matrix.trace
          ((mixtureEmbedding S * R) * ((mixtureEmbedding S)ᴴ * E)) := by
            congr 1
            simp only [Matrix.mul_assoc]
    _ = Matrix.trace
          (((mixtureEmbedding S)ᴴ * E) * (mixtureEmbedding S * R)) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (((mixtureEmbedding S)ᴴ * E * mixtureEmbedding S) * R) := by
            congr 1
            simp only [Matrix.mul_assoc]
    _ = Matrix.trace
          (R * ((mixtureEmbedding S)ᴴ * E * mixtureEmbedding S)) :=
          Matrix.trace_mul_comm _ _
    _ = Matrix.trace
          (R * E.submatrix (mixtureMatchedIndex S)
            (mixtureMatchedIndex S)) := by
          rw [mixtureEmbedding_compress]

theorem mixtureBlockMatrix_trace_mul
    (p : J → ℝ) (S : J → Strategy G)
    (E : ∀ j : J,
      Matrix ((S j).Alice × (S j).Bob)
        ((S j).Alice × (S j).Bob) ℂ) :
    Matrix.trace (mixtureBlockMatrix p S * Matrix.blockDiagonal' E) =
      ∑ j : J, p j • Matrix.trace ((S j).state.matrix * E j) := by
  unfold mixtureBlockMatrix
  rw [← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']
  simp only [Algebra.smul_mul_assoc, trace_smul, Complex.real_smul]

theorem convexMixtureStrategy_outcomeProbability
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) (x : X) (y : Y) (a : A) (b : B) :
    (convexMixtureStrategy p hp h_normalized S).outcomeProbability
        x y a b =
      ∑ j : J, p j * (S j).outcomeProbability x y a b := by
  change
    (Matrix.trace
      ((mixtureEmbedding S * mixtureBlockMatrix p S *
          (mixtureEmbedding S)ᴴ) *
        ((mixtureAlicePOVM S x).effect a ⊗ₖ
          (mixtureBobPOVM S y).effect b))).re = _
  rw [mixtureEmbedding_trace_mul, mixtureJointEffect_compress,
    mixtureBlockMatrix_trace_mul]
  simp only [Complex.real_smul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Strategy.outcomeProbability]

theorem convexMixtureStrategy_winProbability
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (S : J → Strategy G) :
    (convexMixtureStrategy p hp h_normalized S).winProbability =
      ∑ j : J, p j * (S j).winProbability := by
  classical
  have h_branch (x : X) (y : Y) (a : A) (b : B) :
      (if G.predicate x y a b = true then
        ∑ j : J, p j * (S j).outcomeProbability x y a b
       else 0) =
        ∑ j : J, p j *
          (if G.predicate x y a b = true then
            (S j).outcomeProbability x y a b else 0) := by
    split <;> simp
  have h_swap (f : X → Y → A → B → J → ℝ) :
      (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, ∑ j : J,
        f x y a b j) =
        ∑ j : J, ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
          f x y a b j := by
    calc
      (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B, ∑ j : J,
        f x y a b j) =
          ∑ x : X, ∑ y : Y, ∑ a : A, ∑ j : J, ∑ b : B,
            f x y a b j := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              apply Finset.sum_congr rfl
              intro a _
              exact Finset.sum_comm
      _ = ∑ x : X, ∑ y : Y, ∑ j : J, ∑ a : A, ∑ b : B,
            f x y a b j := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro y _
              exact Finset.sum_comm
      _ = ∑ x : X, ∑ j : J, ∑ y : Y, ∑ a : A, ∑ b : B,
            f x y a b j := by
              apply Finset.sum_congr rfl
              intro x _
              exact Finset.sum_comm
      _ = ∑ j : J, ∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
            f x y a b j := Finset.sum_comm
  unfold Strategy.winProbability
  simp_rw [convexMixtureStrategy_outcomeProbability p hp h_normalized S]
  simp_rw [h_branch]
  simp_rw [Finset.mul_sum]
  rw [h_swap (fun x y a b j =>
    G.questionWeight x y *
      (p j * (if G.predicate x y a b = true then
        (S j).outcomeProbability x y a b else 0)))]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

/-- The matrix representation of pure density. -/
def pureDensityMatrix
    {d : Type*} [Fintype d]
    (z : EuclideanSpace ℂ d) (hz : ‖z‖ = 1) : DensityMatrix d where
  matrix := Matrix.vecMulVec (ofLp z) (star (ofLp z))
  positive := Matrix.posSemidef_vecMulVec_self_star (ofLp z)
  trace_one := by
    rw [Matrix.trace_vecMulVec,
      ← EuclideanSpace.inner_eq_star_dotProduct z z,
      inner_self_eq_norm_sq_to_K, hz]
    norm_num

theorem pureDensityMatrix_trace_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (z : EuclideanSpace ℂ d) (hz : ‖z‖ = 1)
    (E : Matrix d d ℂ) :
    (Matrix.trace ((pureDensityMatrix z hz).matrix * E)).re =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E) z := by
  unfold pureDensityMatrix quadraticExpectation
  congr 1
  calc
    Matrix.trace
        (Matrix.vecMulVec (ofLp z) (star (ofLp z)) * E) =
      Matrix.trace
        (E * Matrix.vecMulVec (ofLp z) (star (ofLp z))) :=
          Matrix.trace_mul_comm _ _
    _ = E.mulVec (ofLp z) ⬝ᵥ star (ofLp z) := by
      rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
    _ = ⟪z, Matrix.toEuclideanCLM
          (n := d) (𝕜 := ℂ) E z⟫_ℂ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      rfl

/-- The strategy implementing pure vector. -/
def pureVectorStrategy
    {X Y A B : Type*} {dA dB : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) : Strategy G where
  Alice := dA
  Bob := dB
  aliceFintype := inferInstance
  bobFintype := inferInstance
  aliceDecidableEq := inferInstance
  bobDecidableEq := inferInstance
  state := pureDensityMatrix z hz
  aliceMeasurement := PA
  bobMeasurement := PB

theorem pureVectorStrategy_outcomeProbability
    {X Y A B : Type*} {dA dB : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB)
    (x : X) (y : Y) (a : A) (b : B) :
    (pureVectorStrategy G z hz PA PB).outcomeProbability x y a b =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
          ((PA x).effect a ⊗ₖ (PB y).effect b)) z := by
  change
    (Matrix.trace
      ((pureDensityMatrix z hz).matrix *
        ((PA x).effect a ⊗ₖ (PB y).effect b))).re = _
  exact pureDensityMatrix_trace_mul z hz
    ((PA x).effect a ⊗ₖ (PB y).effect b)

/-- The strategy implementing pure flagged. -/
def pureFlaggedStrategy
    {X Y A B : Type*} {dA dB J : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    [Fintype J] [DecidableEq J]
    (G : Game X Y A B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (z : J → EuclideanSpace ℂ (dA × dB))
    (hz : ∀ j, ‖z j‖ = 1)
    (PA : J → X → POVM A dA)
    (PB : J → Y → POVM B dB) : Strategy G :=
  convexMixtureStrategy p hp h_normalized
    (fun j => pureVectorStrategy G (z j) (hz j) (PA j) (PB j))

theorem pureFlaggedStrategy_winProbability
    {X Y A B : Type*} {dA dB J : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    [Fintype J] [DecidableEq J]
    (G : Game X Y A B)
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (h_normalized : (∑ j : J, p j) = 1)
    (z : J → EuclideanSpace ℂ (dA × dB))
    (hz : ∀ j, ‖z j‖ = 1)
    (PA : J → X → POVM A dA)
    (PB : J → Y → POVM B dB) :
    (pureFlaggedStrategy G p hp h_normalized z hz PA PB).winProbability =
      ∑ j : J, p j *
        (pureVectorStrategy G (z j) (hz j) (PA j) (PB j)).winProbability := by
  exact convexMixtureStrategy_winProbability p hp h_normalized
    (fun j => pureVectorStrategy G (z j) (hz j) (PA j) (PB j))

end

section

open scoped BigOperators

/-- A normalized nonnegative probability law on a finite sample space. -/
structure FiniteEventLaw (Ω : Type*) [Fintype Ω] where
  /-- The probability weight of a sample point. -/
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : (∑ ω, weight ω) = 1

namespace FiniteEventLaw

variable {Ω ι : Type*} [Fintype Ω]

/-- The probability mass of a finite event. -/
def eventMass (law : FiniteEventLaw Ω) (event : Finset Ω) : ℝ :=
  ∑ ω ∈ event, law.weight ω

theorem eventMass_univ (law : FiniteEventLaw Ω) :
    law.eventMass Finset.univ = 1 := by
  simpa only [eventMass] using law.weight_sum

theorem eventMass_mono
    (law : FiniteEventLaw Ω) {s t : Finset Ω} (h : s ⊆ t) :
    law.eventMass s ≤ law.eventMass t := by
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun ω _ _ => law.weight_nonneg ω)

/-- The event on which every selected coordinate wins. -/
def winEvent
    (wins : ι → Ω → Bool) (D : Finset ι) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ i ∈ D, wins i ω = true)

/-- Membership in a finite-law win event is pointwise winning at every selected index. -/
theorem mem_winEvent_iff
    (wins : ι → Ω → Bool) (D : Finset ι) (ω : Ω) :
    ω ∈ winEvent wins D ↔ ∀ i ∈ D, wins i ω = true := by
  classical
  simp only [winEvent, Finset.mem_filter, Finset.mem_univ, true_and]

theorem winEvent_empty (wins : ι → Ω → Bool) :
    winEvent wins ∅ = Finset.univ := by
  classical
  simp only [winEvent, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true]

theorem winEvent_antitone
    (wins : ι → Ω → Bool) {D E : Finset ι} (h : D ⊆ E) :
    winEvent wins E ⊆ winEvent wins D := by
  classical
  intro ω hω
  have h_all : ∀ i ∈ E, wins i ω = true := by
    simpa only [winEvent, Finset.mem_filter, Finset.mem_univ, true_and] using hω
  simp only [winEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun i hi => h_all i (h hi)

theorem allWinMass_le_partial [Fintype ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (D : Finset ι) :
    law.eventMass (winEvent wins Finset.univ) ≤
      law.eventMass (winEvent wins D) := by
  apply law.eventMass_mono
  exact winEvent_antitone wins (Finset.subset_univ D)

/-- The conditional mass of failure at a selected coordinate. -/
def failureMass [DecidableEq ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    (D : Finset ι) (i : ι) : ℝ :=
  law.eventMass (winEvent wins D) -
    law.eventMass (winEvent wins (insert i D))

theorem exists_greedy_stopping [Fintype ι] [DecidableEq ι]
    (mass : Finset ι → ℝ) {θ η : ℝ} {T : ℕ}
    (hη_one : η ≤ 1)
    (hT : T ≤ Fintype.card ι)
    (hempty : mass ∅ = 1)
    (hfloor : ∀ D : Finset ι, θ ≤ mass D)
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset ι,
      D.card < T ∧
      θ ≤ mass D ∧
      (∑ i ∈ Finset.univ \ D,
        (mass D - mass (insert i D)))
        < ((Finset.univ \ D).card : ℝ) * (η * mass D) := by
  classical
  let candidates : Finset (Finset ι) :=
    Finset.univ.powerset.filter
      (fun D => D.card ≤ T ∧ mass D ≤ (1 - η) ^ D.card)
  have h_candidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [Finset.powerset_univ, Finset.mem_filter, Finset.mem_univ, Finset.card_empty,
      zero_le, hempty, pow_zero, Std.le_refl, and_self, candidates]
  obtain ⟨D, hD, hmax⟩ :=
    Finset.exists_max_image candidates (fun E : Finset ι => E.card)
      h_candidates
  have hD_data : D.card ≤ T ∧ mass D ≤ (1 - η) ^ D.card :=
    (Finset.mem_filter.mp hD).2
  have hD_lt : D.card < T := by
    have hne : D.card ≠ T := by
      intro heq
      have hupper : mass D ≤ (1 - η) ^ T := by
        simpa only [heq] using hD_data.2
      linarith [hfloor D]
    exact lt_of_le_of_ne hD_data.1 hne
  refine ⟨D, hD_lt, hfloor D, ?_⟩
  by_contra h_not_stopped
  have h_sum :
      ((Finset.univ \ D).card : ℝ) * (η * mass D)
        ≤ ∑ i ∈ Finset.univ \ D,
          (mass D - mass (insert i D)) :=
    le_of_not_gt h_not_stopped
  have h_card : D.card < (Finset.univ : Finset ι).card := by
    simpa only [Finset.card_univ] using hD_lt.trans_le hT
  have h_remaining : (Finset.univ \ D).Nonempty :=
    Finset.sdiff_nonempty_of_card_lt_card h_card
  have h_sum_constant :
      (∑ _i ∈ Finset.univ \ D, η * mass D)
        ≤ ∑ i ∈ Finset.univ \ D,
          (mass D - mass (insert i D)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.sum_sub_distrib, Finset.subset_univ,
      Finset.sum_sdiff_eq_sub] using h_sum
  obtain ⟨i, hi, hfailure⟩ :=
    Finset.exists_le_of_sum_le h_remaining h_sum_constant
  have hi_not : i ∉ D := (Finset.mem_sdiff.mp hi).2
  have hnext_card : (insert i D).card ≤ T := by
    rw [Finset.card_insert_of_notMem hi_not]
    omega
  have hshrink :
      mass (insert i D) ≤ (1 - η) * mass D := by
    linarith
  have hnext_bound :
      mass (insert i D) ≤
        (1 - η) ^ (insert i D).card := by
    calc
      mass (insert i D) ≤ (1 - η) * mass D := hshrink
      _ ≤ (1 - η) * (1 - η) ^ D.card :=
        mul_le_mul_of_nonneg_left hD_data.2
          (sub_nonneg.mpr hη_one)
      _ = (1 - η) ^ (insert i D).card := by
        rw [Finset.card_insert_of_notMem hi_not, pow_succ]
        ring
  have hnext_mem : insert i D ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, hnext_card, hnext_bound⟩
  have h_impossible := hmax (insert i D) hnext_mem
  rw [Finset.card_insert_of_notMem hi_not] at h_impossible
  omega

theorem exists_conditioned_win_set [Fintype ι] [DecidableEq ι]
    (law : FiniteEventLaw Ω) (wins : ι → Ω → Bool)
    {θ η : ℝ} {T : ℕ}
    (hη_one : η ≤ 1)
    (hT : T ≤ Fintype.card ι)
    (hwin : θ ≤ law.eventMass (winEvent wins Finset.univ))
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset ι,
      D.card < T ∧
      θ ≤ law.eventMass (winEvent wins D) ∧
      (∑ i ∈ Finset.univ \ D, failureMass law wins D i)
        < ((Finset.univ \ D).card : ℝ) *
          (η * law.eventMass (winEvent wins D)) := by
  let mass : Finset ι → ℝ :=
    fun D => law.eventMass (winEvent wins D)
  have hempty : mass ∅ = 1 := by
    dsimp [mass]
    rw [winEvent_empty]
    exact law.eventMass_univ
  have hfloor : ∀ D : Finset ι, θ ≤ mass D := by
    intro D
    exact hwin.trans (law.allWinMass_le_partial wins D)
  obtain ⟨D, hD, hp, hstop⟩ :=
    exists_greedy_stopping mass hη_one hT hempty hfloor
      h_terminal
  refine ⟨D, hD, hp, ?_⟩
  simpa only [failureMass, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.subset_univ, Finset.sum_sdiff_eq_sub] using hstop

end FiniteEventLaw

section StrategyEventLaw

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent strategy outcome in the exact sampling construction. -/
abbrev StrategyOutcome (X Y A B : Type*) :=
  X × Y × A × B

/-- The finite probability law for strategy event. -/
def strategyEventLaw (G : Game X Y A B) (S : Strategy G) :
    FiniteEventLaw (StrategyOutcome X Y A B) where
  weight ω :=
    G.questionWeight ω.1 ω.2.1 *
      S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
  weight_nonneg ω :=
    mul_nonneg (G.weight_nonneg ω.1 ω.2.1)
      (S.outcomeProbability_nonneg
        ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
  weight_sum := by
    classical
    change
      (∑ ω : X × Y × A × B,
        G.questionWeight ω.1 ω.2.1 *
          S.outcomeProbability
            ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) = 1
    simp_rw [Fintype.sum_prod_type]
    calc
      (∑ x : X, ∑ y : Y, ∑ a : A, ∑ b : B,
        G.questionWeight x y *
          S.outcomeProbability x y a b) =
        ∑ x : X, ∑ y : Y,
          G.questionWeight x y *
            (∑ a : A, ∑ b : B,
              S.outcomeProbability x y a b) := by
                apply Finset.sum_congr rfl
                intro x _
                apply Finset.sum_congr rfl
                intro y _
                simp only [Finset.mul_sum]
      _ = ∑ x : X, ∑ y : Y,
          G.questionWeight x y * 1 := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro y _
            rw [S.outcomeProbability_normalized x y]
      _ = 1 := by
            simpa only [mul_one] using G.weight_normalized

private def strategyWinEvent (G : Game X Y A B) :
    Finset (StrategyOutcome X Y A B) :=
  Finset.univ.filter
    (fun ω =>
      G.predicate ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = true)

theorem strategyEventLaw_winEvent
    (G : Game X Y A B) (S : Strategy G) :
    (strategyEventLaw G S).eventMass (strategyWinEvent G) =
      S.winProbability := by
  classical
  unfold FiniteEventLaw.eventMass strategyWinEvent
  simp only [Finset.sum_filter]
  change
    (∑ ω : X × Y × A × B,
      if G.predicate ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 = true
      then G.questionWeight ω.1 ω.2.1 *
        S.outcomeProbability ω.1 ω.2.1 ω.2.2.1 ω.2.2.2
      else 0) =
      S.winProbability
  simp_rw [Fintype.sum_prod_type]
  unfold Strategy.winProbability
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp

/-- The repeated coordinate win construction used in the quantum parallel-repetition argument. -/
def repeatedCoordinateWin (G : Game X Y A B) (n : ℕ)
    (i : Fin n)
    (ω : StrategyOutcome
      (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B)) : Bool :=
  G.predicate (ω.1 i) (ω.2.1 i)
    (ω.2.2.1 i) (ω.2.2.2 i)

theorem repeated_allWinEvent_eq
    (G : Game X Y A B) (n : ℕ) :
    FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
      (Finset.univ : Finset (Fin n)) =
      strategyWinEvent (G.repeat n) := by
  classical
  ext ω
  simp only [FiniteEventLaw.winEvent, Finset.mem_univ, repeatedCoordinateWin, forall_const,
    Finset.mem_filter, true_and, strategyWinEvent, Game.repeat_predicate_eq_true]

theorem repeated_allWinMass_eq
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) :
    (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
        (Finset.univ : Finset (Fin n))) =
      S.winProbability := by
  rw [repeated_allWinEvent_eq]
  exact strategyEventLaw_winEvent (G.repeat n) S

theorem repeatedStrategy_exists_greedy_conditioning
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {θ η : ℝ} {T : ℕ}
    (hη_one : η ≤ 1)
    (hT : T ≤ n)
    (hwin : θ ≤ S.winProbability)
    (h_terminal : (1 - η) ^ T < θ) :
    ∃ D : Finset (Fin n),
      D.card < T ∧
      θ ≤ (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) ∧
      (∑ i ∈ Finset.univ \ D,
        FiniteEventLaw.failureMass
          (strategyEventLaw (G.repeat n) S)
          (repeatedCoordinateWin G n) D i)
        <
      ((Finset.univ \ D).card : ℝ) *
        (η * (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) D)) := by
  have h_card : T ≤ Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using hT
  have h_full :
      θ ≤ (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n)
          (Finset.univ : Finset (Fin n))) := by
    rw [repeated_allWinMass_eq]
    exact hwin
  exact FiniteEventLaw.exists_conditioned_win_set
    (strategyEventLaw (G.repeat n) S)
    (repeatedCoordinateWin G n)
    hη_one h_card h_full h_terminal

end StrategyEventLaw

end

section

open scoped BigOperators

variable {ι : Type*}

theorem negMulLog_rescale
    {W p : ℝ} (hW : 0 < W) (hp : 0 < p) :
    W * Real.negMulLog (p / W) = p * Real.log (W / p) := by
  unfold Real.negMulLog
  rw [Real.log_div hp.ne' hW.ne', Real.log_div hW.ne' hp.ne']
  field_simp
  ring

theorem finite_weighted_entropy_le
    (s : Finset ι) (w h : ι → ℝ) {W p : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hW : 0 < W)
    (hp : 0 < p)
    (hw_sum : (∑ i ∈ s, w i) = W)
    (hp_sum : (∑ i ∈ s, w i * h i) = p) :
    (∑ i ∈ s, w i * Real.negMulLog (h i))
      ≤ p * Real.log (W / p) := by
  classical
  have h_normalized :
      (∑ i ∈ s, w i / W) = 1 := by
    calc
      (∑ i ∈ s, w i / W) = (∑ i ∈ s, w i) / W := by
        rw [Finset.sum_div]
      _ = W / W := by rw [hw_sum]
      _ = 1 := div_self hW.ne'
  have h_mean :
      (∑ i ∈ s, (w i / W) * h i) = p / W := by
    calc
      (∑ i ∈ s, (w i / W) * h i) =
          ∑ i ∈ s, (w i * h i) / W := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = (∑ i ∈ s, w i * h i) / W := by
            rw [Finset.sum_div]
      _ = p / W := by rw [hp_sum]
  have h_jensen :
      (∑ i ∈ s, (w i / W) * Real.negMulLog (h i))
        ≤ Real.negMulLog (∑ i ∈ s, (w i / W) * h i) := by
    simpa only [smul_eq_mul] using
      (Real.concaveOn_negMulLog.le_map_sum
        (t := s) (w := fun i => w i / W) (p := h)
        (fun i hi => div_nonneg (hw i hi) hW.le)
        h_normalized
        (fun i hi => show h i ∈ Set.Ici (0 : ℝ) from hh i hi))
  calc
    (∑ i ∈ s, w i * Real.negMulLog (h i)) =
        W * (∑ i ∈ s, (w i / W) * Real.negMulLog (h i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          field_simp
    _ ≤ W * Real.negMulLog (∑ i ∈ s, (w i / W) * h i) :=
          mul_le_mul_of_nonneg_left h_jensen hW.le
    _ = W * Real.negMulLog (p / W) := by rw [h_mean]
    _ = p * Real.log (W / p) := negMulLog_rescale hW hp

theorem finite_weighted_entropy_le_of_weight_bound
    (s : Finset ι) (w h : ι → ℝ) {W N p : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hh : ∀ i ∈ s, 0 ≤ h i)
    (hW : 0 < W)
    (hp : 0 < p)
    (hw_sum : (∑ i ∈ s, w i) = W)
    (hp_sum : (∑ i ∈ s, w i * h i) = p)
    (hWN : W ≤ N) :
    (∑ i ∈ s, w i * Real.negMulLog (h i))
      ≤ p * Real.log (N / p) := by
  have hquot : W / p ≤ N / p := by
    exact (div_le_div_iff_of_pos_right hp).mpr hWN
  have hlog : Real.log (W / p) ≤ Real.log (N / p) :=
    Real.log_le_log (div_pos hW hp) hquot
  exact
    (finite_weighted_entropy_le s w h hw hh hW hp hw_sum hp_sum).trans
      (mul_le_mul_of_nonneg_left hlog hp.le)

end

section

open scoped BigOperators

theorem noncommutative_resolvent_identity
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF : RF * (F + S) = 1)
    (hM : (M + S) * RM = 1) :
    RF - RM = RF * (M - F) * RM := by
  calc
    RF - RM = RF * ((M + S) * RM) - (RF * (F + S)) * RM := by
      rw [hM, hF]
      simp only [mul_one, one_mul]
    _ = RF * (M - F) * RM := by
      noncomm_ring

theorem noncommutative_filtered_resolvent_identity
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF_left : (F + S) * RF = 1)
    (hF_right : RF * (F + S) = 1)
    (hM_left : (M + S) * RM = 1) :
    F * RF - M * RM = S * (RF * (F - M) * RM) := by
  have hFR : F * RF = 1 - S * RF := by
    have h : F * RF + S * RF = 1 := by
      simpa only [add_mul] using hF_left
    exact eq_sub_of_add_eq h
  have hMR : M * RM = 1 - S * RM := by
    have h : M * RM + S * RM = 1 := by
      simpa only [add_mul] using hM_left
    exact eq_sub_of_add_eq h
  have hdiff : RM - RF = RF * (F - M) * RM := by
    calc
      RM - RF = -(RF - RM) := by noncomm_ring
      _ = -(RF * (M - F) * RM) := by
        rw [noncommutative_resolvent_identity F M S RF RM hF_right hM_left]
      _ = RF * (F - M) * RM := by noncomm_ring
  rw [hFR, hMR]
  calc
    (1 - S * RF) - (1 - S * RM) = S * (RM - RF) := by
      noncomm_ring
    _ = S * (RF * (F - M) * RM) := by rw [hdiff]

theorem noncommutative_resolvent_second_order
    {R : Type*} [Ring R]
    (F M S RF RM : R)
    (hF_left : (F + S) * RF = 1)
    (hF_right : RF * (F + S) = 1)
    (hM_left : (M + S) * RM = 1)
    (hM_right : RM * (M + S) = 1) :
    RF = RM - RM * (F - M) * RM +
      RM * (F - M) * RF * (F - M) * RM := by
  have hleft : RM - RF = RM * (F - M) * RF :=
    noncommutative_resolvent_identity M F S RM RF hM_right hF_left
  have hright : RF - RM = RF * (M - F) * RM :=
    noncommutative_resolvent_identity F M S RF RM hF_right hM_left
  have hfirst : RF = RM - RM * (F - M) * RF := by
    calc
      RF = RM - (RM - RF) := by noncomm_ring
      _ = RM - RM * (F - M) * RF := by rw [hleft]
  have hsecond : RF = RM - RF * (F - M) * RM := by
    calc
      RF = RM + (RF - RM) := by noncomm_ring
      _ = RM + RF * (M - F) * RM := by rw [hright]
      _ = RM - RF * (F - M) * RM := by noncomm_ring
  calc
    RF = RM - RM * (F - M) * RF := hfirst
    _ = RM - RM * (F - M) *
      (RM - RF * (F - M) * RM) := by rw [← hsecond]
    _ = RM - RM * (F - M) * RM +
      RM * (F - M) * RF * (F - M) * RM := by noncomm_ring

theorem noncommutative_weighted_resolvent_second_order
    {ι R : Type*} [Fintype ι] [Ring R]
    (weight : ι → R) (F : ι → R) (M S : R)
    (RF : ι → R) (RM : R)
    (normalized : (∑ i : ι, weight i) = 1)
    (centered : (∑ i : ι, weight i * (F i - M)) = 0)
    (commute_mean : ∀ i, weight i * RM = RM * weight i)
    (hF_left : ∀ i, (F i + S) * RF i = 1)
    (hF_right : ∀ i, RF i * (F i + S) = 1)
    (hM_left : (M + S) * RM = 1)
    (hM_right : RM * (M + S) = 1) :
    (∑ i : ι, weight i * RF i) - RM =
      RM * (∑ i : ι,
        weight i * ((F i - M) * RF i * (F i - M))) * RM := by
  have hterm (i : ι) :
      weight i * RF i =
        weight i * RM - RM * (weight i * (F i - M)) * RM +
          RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM := by
    nth_rewrite 1 [noncommutative_resolvent_second_order
      (F i) M S (RF i) RM (hF_left i) (hF_right i) hM_left hM_right]
    have hw := commute_mean i
    calc
      weight i *
        (RM - RM * (F i - M) * RM +
          RM * (F i - M) * RF i * (F i - M) * RM) =
        weight i * RM -
          (weight i * RM) * (F i - M) * RM +
          (weight i * RM) * ((F i - M) * RF i * (F i - M)) * RM := by
            noncomm_ring
      _ = weight i * RM -
          (RM * weight i) * (F i - M) * RM +
          (RM * weight i) * ((F i - M) * RF i * (F i - M)) * RM := by
            rw [hw]
      _ = weight i * RM - RM * (weight i * (F i - M)) * RM +
          RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM := by
            noncomm_ring
  calc
    (∑ i : ι, weight i * RF i) - RM =
        (∑ i : ι,
          (weight i * RM - RM * (weight i * (F i - M)) * RM +
            RM * (weight i * ((F i - M) * RF i * (F i - M))) * RM)) - RM := by
              congr 1
              exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i : ι, weight i) * RM -
          RM * (∑ i : ι, weight i * (F i - M)) * RM +
          RM * (∑ i : ι,
            weight i * ((F i - M) * RF i * (F i - M))) * RM - RM := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.sum_mul, ← Finset.mul_sum]
    _ = RM * (∑ i : ι,
          weight i * ((F i - M) * RF i * (F i - M))) * RM := by
            rw [normalized, centered]
            noncomm_ring

end

section

open scoped BigOperators ComplexOrder MatrixOrder

theorem posSemidef_hermitian_sandwich
    {d : Type*} [Fintype d]
    {A D : Matrix d d ℂ}
    (hA : A.PosSemidef) (hD : D.IsHermitian) :
    (D * A * D).PosSemidef := by
  simpa only [hD.eq] using hA.mul_mul_conjTranspose_same D

theorem shifted_posSemidef_matrix_posDef
    {d : Type*} [DecidableEq d]
    {F : Matrix d d ℂ} (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (F + s • (1 : Matrix d d ℂ)).PosDef := by
  have hshift : (s • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.one.smul hs
  exact Matrix.PosDef.posSemidef_add hF hshift

theorem shifted_posSemidef_matrix_inverse_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F : Matrix d d ℂ} (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    ((F + s • (1 : Matrix d d ℂ))⁻¹).PosSemidef :=
  (shifted_posSemidef_matrix_posDef hF hs).posSemidef.inv

theorem matrix_weighted_centered
    {ι d : Type*} [Fintype ι]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M) :
    (∑ i : ι, weight i • (F i - M)) = 0 := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, mean, ← Finset.sum_smul, normalized]
  simp only [one_smul, sub_self]

theorem weighted_positive_matrix_mean
    {ι d : Type*} [Fintype ι]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (positive : ∀ i, (F i).PosSemidef) :
    (∑ i : ι, weight i • F i).PosSemidef := by
  exact Matrix.posSemidef_sum Finset.univ
    (fun i _ => (positive i).smul (nonnegative i))

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology

theorem scalar_resolvent_purification_integrable_of_pos
    {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun s : ℝ => (z / (z + s)) ^ 2) (Ioi 0) := by
  have hpower :
      IntegrableOn (fun s : ℝ => (s + z) ^ (-2 : ℝ)) (Ioi 0) := by
    exact integrableOn_add_rpow_Ioi_of_lt
      (a := (-2 : ℝ)) (c := (0 : ℝ)) (m := z)
      (by norm_num) (by linarith)
  have hscaled :
      IntegrableOn (fun s : ℝ => z ^ 2 * (s + z) ^ (-2 : ℝ))
        (Ioi 0) :=
    hpower.const_mul (z ^ 2)
  refine hscaled.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hspos : 0 < s + z := by
    have : 0 < s := hs
    linarith
  change z ^ 2 * (s + z) ^ (-2 : ℝ) = (z / (z + s)) ^ 2
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
    Real.rpow_neg hspos.le, Real.rpow_two]
  rw [div_pow]
  simp only [add_comm, div_eq_mul_inv]

theorem scalar_resolvent_purification_integrable
    {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun s : ℝ => (z / (z + s)) ^ 2) (Ioi 0) := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp only [zero_add, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      enorm_zero, ENNReal.zero_ne_top, integrableOn_const_iff, Real.volume_Ioi, lt_self_iff_false,
      or_false]
  · exact scalar_resolvent_purification_integrable_of_pos hzpos

theorem scalar_resolvent_purification_integral
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ s in Ioi (0 : ℝ), (z / (z + s)) ^ 2) = z := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp only [zero_add, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      integral_zero]
  · have hderiv :
        ∀ x ∈ Ici (0 : ℝ),
          HasDerivAt (fun t : ℝ => -(z ^ 2) / (z + t))
            ((z / (z + x)) ^ 2) x := by
      intro x hx
      have hden : z + x ≠ 0 := by
        have hx_nonneg : 0 ≤ x := hx
        exact ne_of_gt (by linarith)
      have hd := ((hasDerivAt_const x (-(z ^ 2))).div
        ((hasDerivAt_const x z).add (hasDerivAt_id x)) hden)
      have hfun :
          (fun t : ℝ => -(z ^ 2) / (z + t)) =
            (fun _t : ℝ => -(z ^ 2)) /
              ((fun _t : ℝ => z) + id) := by
        funext t
        rfl
      rw [hfun]
      simpa only [div_pow, Pi.add_apply, id_eq, zero_mul, zero_add, mul_one,
        sub_neg_eq_add] using hd
    have hlimit :
        Tendsto (fun t : ℝ => -(z ^ 2) / (z + t))
          atTop (𝓝 (0 : ℝ)) := by
      have hden : Tendsto (fun t : ℝ => t + z) atTop atTop :=
        tendsto_atTop_add_const_right atTop z tendsto_id
      have hzero : Tendsto (fun t : ℝ => -(z ^ 2) / (t + z))
          atTop (𝓝 (0 : ℝ)) :=
        tendsto_const_nhds.div_atTop hden
      simpa only [add_comm] using hzero
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv (scalar_resolvent_purification_integrable_of_pos hzpos) hlimit
    calc
      (∫ s in Ioi (0 : ℝ), (z / (z + s)) ^ 2) =
          (0 : ℝ) - (-(z ^ 2) / (z + 0)) := hftc
      _ = z := by
        field_simp
        ring

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def diagonalPurificationGram
    {d : Type*} [DecidableEq d]
    (eigenvalue : d → ℝ) (s : ℝ) : Matrix d d ℂ :=
  Matrix.diagonal fun i =>
    (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)

theorem diagonalPurificationGram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (h_nonneg : ∀ i, 0 ≤ eigenvalue i) :
    IntegrableOn (diagonalPurificationGram eigenvalue) (Ioi 0) := by
  apply MeasureTheory.Integrable.of_eval
  intro i
  apply MeasureTheory.Integrable.of_eval
  intro j
  classical
  by_cases h : i = j
  · subst j
    have hcomplex :
        Integrable
          (fun s : ℝ =>
            (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ))
          (volume.restrict (Ioi 0)) :=
      MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
        (scalar_resolvent_purification_integrable (h_nonneg i))
    simpa only [diagonalPurificationGram, Matrix.diagonal_apply_eq] using
      hcomplex
  · simp only [diagonalPurificationGram, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_add, ne_eq, h, not_false_eq_true, Matrix.diagonal_apply_ne,
      integrable_fun_zero]

theorem integral_diagonalPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (h_nonneg : ∀ i, 0 ≤ eigenvalue i) :
    (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s) =
      Matrix.diagonal (fun i => (eigenvalue i : ℂ)) := by
  classical
  have hmatrix := diagonalPurificationGram_integrable eigenvalue h_nonneg
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ => diagonalPurificationGram eigenvalue s i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  have hentry (i : d) :
      ∀ j : d,
        Integrable
          (fun s : ℝ => diagonalPurificationGram eigenvalue s i j)
          (volume.restrict (Ioi 0)) :=
    fun j => (hrows i).eval j
  ext i j
  rw [show
    (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s) i j =
      (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s i) j from
        congrArg (fun row : d → ℂ => row j)
          (MeasureTheory.eval_integral hrows i)]
  rw [show
    (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s i) j =
      ∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s i j from
        MeasureTheory.eval_integral (hentry i) j]
  by_cases h : i = j
  · subst j
    simp only [diagonalPurificationGram, Matrix.diagonal_apply_eq]
    calc
      (∫ s in Ioi (0 : ℝ),
        (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) =
          ((∫ s in Ioi (0 : ℝ),
            (eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ) :=
        integral_ofReal
      _ = (eigenvalue i : ℂ) := by
        rw [scalar_resolvent_purification_integral (h_nonneg i)]
  · simp only [diagonalPurificationGram, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_add, ne_eq, h, not_false_eq_true, Matrix.diagonal_apply_ne, integral_zero]

/-- The continuous linear map implementing spectral conjugation. -/
def spectralConjugationCLM
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    (Unitary.conjStarAlgAut ℝ (Matrix d d ℂ) U).toAlgEquiv.toLinearEquiv.toLinearMap

@[simp] theorem spectralConjugationCLM_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    spectralConjugationCLM U A =
      (U : Matrix d d ℂ) * A * star (U : Matrix d d ℂ) := by
  rfl

private def spectralPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (diagonalPurificationGram hF.isHermitian.eigenvalues s)

theorem spectralPurificationGram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn (spectralPurificationGram F hF) (Ioi 0) := by
  have hdiag := diagonalPurificationGram_integrable
    hF.isHermitian.eigenvalues (fun i => hF.eigenvalues_nonneg i)
  exact (spectralConjugationCLM hF.isHermitian.eigenvectorUnitary).integrable_comp
    hdiag

theorem integral_spectralPurificationGram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ), spectralPurificationGram F hF s) = F := by
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag := diagonalPurificationGram_integrable
    eigenvalue (fun i => hF.eigenvalues_nonneg i)
  calc
    (∫ s in Ioi (0 : ℝ), spectralPurificationGram F hF s) =
        spectralConjugationCLM U
          (∫ s in Ioi (0 : ℝ), diagonalPurificationGram eigenvalue s) := by
            exact ContinuousLinearMap.integral_comp_comm
              (spectralConjugationCLM U) hdiag
    _ = spectralConjugationCLM U
          (Matrix.diagonal (fun i => (eigenvalue i : ℂ))) := by
            rw [integral_diagonalPurificationGram eigenvalue
              (fun i => hF.eigenvalues_nonneg i)]
    _ = F := by
          simpa only [spectralConjugationCLM_apply, Complex.coe_algebraMap, Function.comp_def,
            Unitary.conjStarAlgAut_apply, U, eigenvalue] using
            hF.isHermitian.spectral_theorem.symm

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Kronecker Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The spectral filter for spectral purification. -/
def spectralPurificationFilter
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i =>
      ((hF.isHermitian.eigenvalues i /
        (hF.isHermitian.eigenvalues i + s) : ℝ) : ℂ))

theorem spectralPurificationFilter_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s =
      spectralPurificationGram F hF s := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let D : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U
  have hDhermitian : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ) = _
    simp only [Complex.ofReal_div, Complex.ofReal_add, star_div₀, RCLike.star_def,
      Complex.conj_ofReal, star_add]
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hDhermitian.eq
  have hDsquare : D * D = diagonalPurificationGram eigenvalue s := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [Complex.ofReal_div, Complex.ofReal_add, Matrix.diagonal_apply_eq,
        diagonalPurificationGram, pow_two, Complex.ofReal_mul]
    · simp only [Complex.ofReal_div, Complex.ofReal_add, ne_eq, h, not_false_eq_true,
        Matrix.diagonal_apply_ne, diagonalPurificationGram, Complex.ofReal_pow]
  change star (e D) * e D = e (diagonalPurificationGram eigenvalue s)
  calc
    star (e D) * e D = e (star D) * e D := by rw [map_star]
    _ = e (star D * D) := (map_mul e (star D) D).symm
    _ = e (diagonalPurificationGram eigenvalue s) := by
      rw [hDstar, hDsquare]

theorem integral_spectralPurificationFilter_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ),
      star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s) = F := by
  simp_rw [spectralPurificationFilter_gram]
  exact integral_spectralPurificationGram F hF

theorem spectralPurificationFilter_gram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn
      (fun s : ℝ => star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s) (Ioi 0) := by
  simpa only [spectralPurificationFilter_gram] using
    spectralPurificationGram_integrable F hF

/-- The born trace pairing construction used in the quantum parallel-repetition argument. -/
def bornTracePairing
    {dA dB : Type*} [Fintype dA] [Fintype dB]
    (ρ : Matrix (dA × dB) (dA × dB) ℂ) :
    Matrix dA dA ℂ →ₗ[ℝ] Matrix dB dB ℂ →ₗ[ℝ] ℝ where
  toFun F :=
    { toFun := fun G => (Matrix.trace (ρ * (F ⊗ₖ G))).re
      map_add' := by
        intro G H
        simp only [Matrix.kronecker_add, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := by
        intro r G
        simp only [Matrix.kronecker_smul, mul_smul_comm, Matrix.trace_smul, Complex.real_smul,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Real.ringHom_apply, smul_eq_mul] }
  map_add' := by
    intro F H
    ext G
    simp only [Matrix.add_kronecker, Matrix.mul_add, Matrix.trace_add, Complex.add_re,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  map_smul' := by
    intro r F
    ext G
    simp only [Matrix.smul_kronecker, mul_smul_comm, Matrix.trace_smul, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, LinearMap.coe_mk,
      AddHom.coe_mk, Real.ringHom_apply, LinearMap.smul_apply, smul_eq_mul]

end

section

open scoped BigOperators Kronecker

namespace Game

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem questionWeight_le_marginalX
    (G : Game X Y A B) (x : X) (y : Y) :
    G.questionWeight x y ≤ G.marginalX x := by
  unfold marginalX
  exact Finset.single_le_sum
    (fun y _ => G.weight_nonneg x y)
    (Finset.mem_univ y)

theorem questionWeight_le_marginalY
    (G : Game X Y A B) (x : X) (y : Y) :
    G.questionWeight x y ≤ G.marginalY y := by
  unfold marginalY
  exact Finset.single_le_sum
    (fun x _ => G.weight_nonneg x y)
    (Finset.mem_univ x)

/-- The conditional y given x construction used in the quantum parallel-repetition argument. -/
def conditionalYGivenX (G : Game X Y A B) (x : X) (y : Y) : ℝ :=
  G.questionWeight x y / G.marginalX x

/-- The conditional x given y construction used in the quantum parallel-repetition argument. -/
def conditionalXGivenY (G : Game X Y A B) (y : Y) (x : X) : ℝ :=
  G.questionWeight x y / G.marginalY y

theorem conditionalYGivenX_nonneg
    (G : Game X Y A B) (x : X) (y : Y) :
    0 ≤ G.conditionalYGivenX x y := by
  exact div_nonneg (G.weight_nonneg x y)
    (G.marginalX_nonneg x)

theorem conditionalXGivenY_nonneg
    (G : Game X Y A B) (y : Y) (x : X) :
    0 ≤ G.conditionalXGivenY y x := by
  exact div_nonneg (G.weight_nonneg x y)
    (G.marginalY_nonneg y)

theorem marginalX_mul_conditionalYGivenX
    (G : Game X Y A B) (x : X) (y : Y) :
    G.marginalX x * G.conditionalYGivenX x y =
      G.questionWeight x y := by
  unfold conditionalYGivenX
  by_cases hx : G.marginalX x = 0
  · have hzero : G.questionWeight x y = 0 := by
      have hle := G.questionWeight_le_marginalX x y
      have hnonneg := G.weight_nonneg x y
      rw [hx] at hle
      linarith
    simp only [hx, hzero, div_zero, mul_zero]
  · field_simp

theorem marginalY_mul_conditionalXGivenY
    (G : Game X Y A B) (x : X) (y : Y) :
    G.marginalY y * G.conditionalXGivenY y x =
      G.questionWeight x y := by
  unfold conditionalXGivenY
  by_cases hy : G.marginalY y = 0
  · have hzero : G.questionWeight x y = 0 := by
      have hle := G.questionWeight_le_marginalY x y
      have hnonneg := G.weight_nonneg x y
      rw [hy] at hle
      linarith
    simp only [hy, hzero, div_zero, mul_zero]
  · field_simp

theorem conditionalYGivenX_sum
    (G : Game X Y A B) (x : X)
    (hx : 0 < G.marginalX x) :
    (∑ y : Y, G.conditionalYGivenX x y) = 1 := by
  unfold conditionalYGivenX
  rw [← Finset.sum_div]
  change G.marginalX x / G.marginalX x = 1
  exact div_self hx.ne'

theorem conditionalXGivenY_sum
    (G : Game X Y A B) (y : Y)
    (hy : 0 < G.marginalY y) :
    (∑ x : X, G.conditionalXGivenY y x) = 1 := by
  unfold conditionalXGivenY
  rw [← Finset.sum_div]
  change G.marginalY y / G.marginalY y = 1
  exact div_self hy.ne'

end Game

section MixedHistories

variable {X Y A B U V : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup V] [Module ℝ V]

/-- The finite average of conditional bob. -/
def conditionalBobAverage
    (G : Game X Y A B) (K : Y → V) (x : X) : V :=
  ∑ y : Y, G.conditionalYGivenX x y • K y

/-- The finite average of conditional alice. -/
def conditionalAliceAverage
    (G : Game X Y A B) (H : X → U) (y : Y) : U :=
  ∑ x : X, G.conditionalXGivenY y x • H x

theorem alice_mixed_history_pairing
    (G : Game X Y A B)
    (pair : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H : X → U) (K : Y → V) :
    (∑ x : X,
      G.marginalX x *
        pair (H x) (conditionalBobAverage G K x))
      =
    ∑ x : X, ∑ y : Y,
      G.questionWeight x y * pair (H x) (K y) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  unfold conditionalBobAverage
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [map_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, G.marginalX_mul_conditionalYGivenX x y]

theorem bob_mixed_history_pairing
    (G : Game X Y A B)
    (pair : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H : X → U) (K : Y → V) :
    (∑ y : Y,
      G.marginalY y *
        pair (conditionalAliceAverage G H y) (K y))
      =
    ∑ x : X, ∑ y : Y,
      G.questionWeight x y * pair (H x) (K y) := by
  classical
  calc
    (∑ y : Y,
      G.marginalY y *
        pair (conditionalAliceAverage G H y) (K y))
      =
      ∑ y : Y, ∑ x : X,
        G.questionWeight x y * pair (H x) (K y) := by
        apply Finset.sum_congr rfl
        intro y _
        unfold conditionalAliceAverage
        rw [map_sum]
        simp only [LinearMap.sum_apply, map_smul,
          LinearMap.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [← mul_assoc, G.marginalY_mul_conditionalXGivenY x y]
    _ =
      ∑ x : X, ∑ y : Y,
        G.questionWeight x y * pair (H x) (K y) := by
          rw [Finset.sum_comm]

theorem alice_reveal_increment
    (G : Game X Y A B)
    (pair : U →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (H : X → U) (M : Y → U) (K : Y → V)
    (f : U → U) :
    (∑ x : X,
      G.marginalX x *
        pair (f (H x)) (conditionalBobAverage G K x))
      -
    (∑ y : Y,
      G.marginalY y *
        pair (f (M y)) (K y))
      =
    ∑ y : Y,
      G.marginalY y *
        pair
          (conditionalAliceAverage G (fun x => f (H x)) y -
            f (M y))
          (K y) := by
  classical
  rw [alice_mixed_history_pairing G pair (fun x => f (H x)) K]
  rw [← bob_mixed_history_pairing G pair (fun x => f (H x)) K]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [map_sub]
  simp only [LinearMap.sub_apply]
  ring

end MixedHistories

section RepeatedQuantumFilters

open scoped ComplexOrder MatrixOrder

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The measurement effect for conditioned alice. -/
def conditionedAliceEffect
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    Matrix S.Alice S.Alice ℂ := by
  classical
  exact
    ∑ answers : Fin n → A,
      if ∀ (i : Fin n) (hi : i ∈ D),
        answers i = α ⟨i, hi⟩
      then (S.aliceMeasurement xs).effect answers
      else 0

/-- The measurement effect for conditioned bob. -/
def conditionedBobEffect
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    Matrix S.Bob S.Bob ℂ := by
  classical
  exact
    ∑ answers : Fin n → B,
      if ∀ (i : Fin n) (hi : i ∈ D),
        answers i = β ⟨i, hi⟩
      then (S.bobMeasurement ys).effect answers
      else 0

theorem conditionedAliceEffect_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    (conditionedAliceEffect G n S D α xs).PosSemidef := by
  classical
  unfold conditionedAliceEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.aliceMeasurement xs).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedBobEffect_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    (conditionedBobEffect G n S D β ys).PosSemidef := by
  classical
  unfold conditionedBobEffect
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact (S.bobMeasurement ys).positive answers
  · exact Matrix.PosSemidef.zero

theorem conditionedAliceEffect_complement_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (xs : Fin n → X) :
    (1 - conditionedAliceEffect G n S D α xs).PosSemidef := by
  classical
  have hsplit :
      1 - conditionedAliceEffect G n S D α xs =
        ∑ answers : Fin n → A,
          if ∀ (i : Fin n) (hi : i ∈ D),
            answers i = α ⟨i, hi⟩
          then 0
          else (S.aliceMeasurement xs).effect answers := by
    unfold conditionedAliceEffect
    rw [← (S.aliceMeasurement xs).complete,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro answers _
    split_ifs <;> simp
  rw [hsplit]
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact Matrix.PosSemidef.zero
  · exact (S.aliceMeasurement xs).positive answers

theorem conditionedBobEffect_complement_positive
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (β : {i : Fin n // i ∈ D} → B)
    (ys : Fin n → Y) :
    (1 - conditionedBobEffect G n S D β ys).PosSemidef := by
  classical
  have hsplit :
      1 - conditionedBobEffect G n S D β ys =
        ∑ answers : Fin n → B,
          if ∀ (i : Fin n) (hi : i ∈ D),
            answers i = β ⟨i, hi⟩
          then 0
          else (S.bobMeasurement ys).effect answers := by
    unfold conditionedBobEffect
    rw [← (S.bobMeasurement ys).complete,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro answers _
    split_ifs <;> simp
  rw [hsplit]
  apply Matrix.posSemidef_sum Finset.univ
  intro answers _
  split_ifs
  · exact Matrix.PosSemidef.zero
  · exact (S.bobMeasurement ys).positive answers

end RepeatedQuantumFilters

theorem history_forward_telescope (E : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, (E (k + 1) - E k))
      = E m - E 0 := by
  simpa only [Finset.sum_sub_distrib] using Finset.sum_range_sub E m

end

section

open scoped BigOperators ComplexOrder MatrixOrder

/--
The spectral support functional construction used in the quantum parallel-repetition argument.
-/
def spectralSupportFunctional
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) : Matrix d d ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary)
      (Matrix.diagonal fun i => (f (hF.isHermitian.eigenvalues i) : ℂ))

theorem spectralSupportFunctional_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f g : ℝ → ℝ) :
    spectralSupportFunctional F hF f *
        spectralSupportFunctional F hF g =
      spectralSupportFunctional F hF (fun x => f x * g x) := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  change e _ * e _ = e _
  rw [← map_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  push_cast
  rfl

theorem spectralSupportFunctional_id
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportFunctional F hF (fun x => x) = F := by
  simpa only [spectralSupportFunctional, Unitary.conjStarAlgAut_apply, Complex.coe_algebraMap,
    Function.comp_def] using
    hF.isHermitian.spectral_theorem.symm

theorem spectralSupportFunctional_congr
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {f g : ℝ → ℝ}
    (h : ∀ i : d,
      f (hF.isHermitian.eigenvalues i) =
        g (hF.isHermitian.eigenvalues i)) :
    spectralSupportFunctional F hF f =
      spectralSupportFunctional F hF g := by
  unfold spectralSupportFunctional
  congr 2
  funext i
  exact_mod_cast h i

theorem spectralSupportFunctional_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) :
    (spectralSupportFunctional F hF f).IsHermitian := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  let D : Matrix d d ℂ :=
    Matrix.diagonal fun i => (f (hF.isHermitian.eigenvalues i) : ℂ)
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (f (hF.isHermitian.eigenvalues i) : ℂ) = _
    simp only [RCLike.star_def, Complex.conj_ofReal]
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hD.eq
  change Matrix.conjTranspose (e D) = e D
  simpa only [Matrix.star_eq_conjTranspose] using
    (show star (e D) = e D by rw [← map_star, hDstar])

private def spectralSupportInverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF (fun x => x⁻¹)

private def spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)

/-- The positive square-root construction for spectral support. -/
def spectralSupportSqrt
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) : Matrix d d ℂ :=
  spectralSupportFunctional F hF Real.sqrt

theorem spectralSupportInverse_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (spectralSupportInverse F hF).IsHermitian :=
  spectralSupportFunctional_isHermitian F hF _

theorem spectralSupportProjection_isHermitian
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (spectralSupportProjection F hF).IsHermitian :=
  spectralSupportFunctional_isHermitian F hF _

theorem spectralSupportInverse_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportInverse F hF * F =
      spectralSupportProjection F hF := by
  change spectralSupportFunctional F hF (fun x => x⁻¹) * F =
    spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)
  calc
    spectralSupportFunctional F hF (fun x => x⁻¹) * F =
        spectralSupportFunctional F hF (fun x => x⁻¹) *
          spectralSupportFunctional F hF (fun x => x) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF (fun x => x⁻¹ * x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp only [hi, inv_zero, mul_zero, ↓reduceIte]
      · simp only [ne_eq, hi, not_false_eq_true, inv_mul_cancel₀, ↓reduceIte])

theorem mul_spectralSupportInverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    F * spectralSupportInverse F hF =
      spectralSupportProjection F hF := by
  change F * spectralSupportFunctional F hF (fun x => x⁻¹) =
    spectralSupportFunctional F hF (fun x => if x = 0 then 0 else 1)
  calc
    F * spectralSupportFunctional F hF (fun x => x⁻¹) =
        spectralSupportFunctional F hF (fun x => x) *
          spectralSupportFunctional F hF (fun x => x⁻¹) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF (fun x => x * x⁻¹) :=
      spectralSupportFunctional_mul F hF _ _
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp only [hi, inv_zero, mul_zero, ↓reduceIte]
      · simp only [ne_eq, hi, not_false_eq_true, mul_inv_cancel₀, ↓reduceIte])

theorem spectralSupportProjection_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportProjection F hF * F = F := by
  change spectralSupportFunctional F hF
      (fun x => if x = 0 then 0 else 1) * F = F
  calc
    spectralSupportFunctional F hF
        (fun x => if x = 0 then 0 else 1) * F =
      spectralSupportFunctional F hF
        (fun x => if x = 0 then 0 else 1) *
          spectralSupportFunctional F hF (fun x => x) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF
          (fun x => (if x = 0 then 0 else 1) * x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = spectralSupportFunctional F hF (fun x => x) :=
      spectralSupportFunctional_congr F hF (by
        intro i
        by_cases hi : hF.isHermitian.eigenvalues i = 0 <;> simp [hi])
    _ = F := spectralSupportFunctional_id F hF

theorem spectralSupportInverse_penrose
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportInverse F hF * F *
        spectralSupportInverse F hF =
      spectralSupportInverse F hF := by
  change spectralSupportFunctional F hF (fun x => x⁻¹) * F *
      spectralSupportFunctional F hF (fun x => x⁻¹) =
    spectralSupportFunctional F hF (fun x => x⁻¹)
  calc
    spectralSupportFunctional F hF (fun x => x⁻¹) * F *
        spectralSupportFunctional F hF (fun x => x⁻¹) =
      (spectralSupportFunctional F hF (fun x => x⁻¹) *
        spectralSupportFunctional F hF (fun x => x)) *
          spectralSupportFunctional F hF (fun x => x⁻¹) := by
            rw [spectralSupportFunctional_id]
    _ = spectralSupportFunctional F hF
          (fun x => (x⁻¹ * x) * x⁻¹) := by
      rw [spectralSupportFunctional_mul,
        spectralSupportFunctional_mul]
    _ = _ := spectralSupportFunctional_congr F hF (by
      intro i
      by_cases hi : hF.isHermitian.eigenvalues i = 0
      · simp only [hi, inv_zero, mul_zero]
      · simp only [ne_eq, hi, not_false_eq_true, inv_mul_cancel₀, one_mul])

theorem spectralSupportSqrt_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    spectralSupportSqrt F hF * spectralSupportSqrt F hF = F := by
  change spectralSupportFunctional F hF Real.sqrt *
    spectralSupportFunctional F hF Real.sqrt = F
  calc
    spectralSupportFunctional F hF Real.sqrt *
        spectralSupportFunctional F hF Real.sqrt =
      spectralSupportFunctional F hF
        (fun x => Real.sqrt x * Real.sqrt x) :=
      spectralSupportFunctional_mul F hF _ _
    _ = spectralSupportFunctional F hF (fun x => x) :=
      spectralSupportFunctional_congr F hF (by
        intro i
        exact Real.mul_self_sqrt (hF.eigenvalues_nonneg i))
    _ = F := spectralSupportFunctional_id F hF

end

section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

theorem mul_spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    F * spectralSupportProjection F hF = F := by
  have h := congrArg Matrix.conjTranspose
    (spectralSupportProjection_mul F hF)
  simpa only [conjTranspose_mul, hF.isHermitian.eq,
    (spectralSupportProjection_isHermitian F hF).eq] using h

theorem posSemidef_kernel_of_sub_posSemidef
    {d : Type*} [Fintype d]
    {F A : Matrix d d ℂ}
    (hA : A.PosSemidef) (hsub : (F - A).PosSemidef)
    {x : d → ℂ} (hx : F *ᵥ x = 0) :
    A *ᵥ x = 0 := by
  apply (hA.dotProduct_mulVec_zero_iff x).mp
  have hA_nonneg : 0 ≤ star x ⬝ᵥ (A *ᵥ x) :=
    hA.dotProduct_mulVec_nonneg x
  have hsub_nonneg : 0 ≤ star x ⬝ᵥ ((F - A) *ᵥ x) :=
    hsub.dotProduct_mulVec_nonneg x
  have hzero :
      star x ⬝ᵥ (A *ᵥ x) +
        star x ⬝ᵥ ((F - A) *ᵥ x) = 0 := by
    calc
      star x ⬝ᵥ (A *ᵥ x) +
          star x ⬝ᵥ ((F - A) *ᵥ x) =
        star x ⬝ᵥ ((A + (F - A)) *ᵥ x) := by
          rw [Matrix.add_mulVec, dotProduct_add]
      _ = star x ⬝ᵥ (F *ᵥ x) := by
        have hsum : A + (F - A) = F := by abel
        rw [hsum]
      _ = 0 := by rw [hx]; simp only [dotProduct_zero]
  exact (add_eq_zero_iff_of_nonneg hA_nonneg hsub_nonneg).mp hzero |>.1

theorem posSemidef_mul_spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    A * spectralSupportProjection F hF = A := by
  let P := spectralSupportProjection F hF
  have hFP : F * P = F := mul_spectralSupportProjection F hF
  have hkernel : F * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hFP, sub_self]
  have hAzero : A * (1 - P) = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    have hxi : F *ᵥ ((1 - P) *ᵥ Pi.single i 1) = 0 := by
      have h := congrArg
        (fun M : Matrix d d ℂ => M *ᵥ Pi.single i 1) hkernel
      simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using h
    have hAi := posSemidef_kernel_of_sub_posSemidef hA hsub hxi
    simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using hAi
  have hdiff : A - A * P = 0 := by
    simpa only [mul_sub, mul_one] using hAzero
  exact (sub_eq_zero.mp hdiff).symm

theorem spectralSupportProjection_mul_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    spectralSupportProjection F hF * A = A := by
  have h := congrArg Matrix.conjTranspose
    (posSemidef_mul_spectralSupportProjection hF hA hsub)
  simpa only [conjTranspose_mul, (spectralSupportProjection_isHermitian F hF).eq,
    hA.isHermitian.eq] using h

theorem refinement_complement_posSemidef
    {ι d : Type*} [Fintype ι]
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    ((∑ b : ι, effect b) - effect a).PosSemidef := by
  classical
  have herase : (∑ b ∈ Finset.univ.erase a, effect b).PosSemidef := by
    apply Matrix.posSemidef_sum (Finset.univ.erase a)
    intro c _
    exact hpositive c
  have hsum : effect a +
      (∑ b ∈ Finset.univ.erase a, effect b) =
      ∑ b : ι, effect b := by
    simp only [Finset.mem_univ, Finset.sum_erase_eq_sub, add_sub_cancel]
  rw [← hsum, add_sub_cancel_left]
  exact herase

end

section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder


private def purificationRangeProjection
    {d e : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ) : Matrix e e ℂ :=
  Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ

theorem purificationRangeProjection_isHermitian
    {d e : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ) :
    (purificationRangeProjection F hF Γ).IsHermitian := by
  unfold purificationRangeProjection
  change Matrix.conjTranspose
    (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) = _
  simp only [Matrix.mul_assoc, conjTranspose_mul, conjTranspose_conjTranspose,
    (spectralSupportInverse_isHermitian F hF).eq]

theorem purificationRangeProjection_idempotent
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    purificationRangeProjection F hF Γ *
        purificationRangeProjection F hF Γ =
      purificationRangeProjection F hF Γ := by
  unfold purificationRangeProjection
  calc
    (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) *
        (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) =
      Γ * (spectralSupportInverse F hF *
        (Matrix.conjTranspose Γ * Γ) *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_assoc]
    _ = Γ * (spectralSupportInverse F hF * F *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            rw [hΓ]
    _ = Γ * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            rw [spectralSupportInverse_penrose]

theorem purificationRangeProjection_complement_posSemidef
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    (1 - purificationRangeProjection F hF Γ).PosSemidef := by
  let P := purificationRangeProjection F hF Γ
  have hPstar : Matrix.conjTranspose P = P :=
    (purificationRangeProjection_isHermitian F hF Γ).eq
  have hPsq : P * P = P :=
    purificationRangeProjection_idempotent F hF Γ hΓ
  have hsquare :
      Matrix.conjTranspose (1 - P) * (1 - P) = 1 - P := by
    calc
      Matrix.conjTranspose (1 - P) * (1 - P) =
          (1 - P) * (1 - P) := by
            simp only [conjTranspose_sub, conjTranspose_one, hPstar]
      _ = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPsq]; noncomm_ring
  have hpositive := Matrix.posSemidef_conjTranspose_mul_self
    (1 - P)
  rw [hsquare] at hpositive
  exact hpositive

private def purifiedRefinementCore
    {ι d e : Type*}
    [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ) (a : ι) : Matrix e e ℂ :=
  Γ * spectralSupportInverse F hF * effect a *
    spectralSupportInverse F hF * Matrix.conjTranspose Γ

theorem purifiedRefinementCore_posSemidef
    {ι d e : Type*}
    [Fintype d] [DecidableEq d]
    [Finite e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a : ι) :
    (purifiedRefinementCore F hF Γ effect a).PosSemidef := by
  let _ := Fintype.ofFinite e
  have h := (hpositive a).mul_mul_conjTranspose_same
    (Γ * spectralSupportInverse F hF)
  simpa only [purifiedRefinementCore, Matrix.mul_assoc, conjTranspose_mul,
    (spectralSupportInverse_isHermitian F hF).eq] using h

theorem purifiedRefinementCore_sum
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hsum : (∑ a : ι, effect a) = F) :
    (∑ a : ι, purifiedRefinementCore F hF Γ effect a) =
      purificationRangeProjection F hF Γ := by
  unfold purifiedRefinementCore purificationRangeProjection
  calc
    (∑ a : ι,
      Γ * spectralSupportInverse F hF * effect a *
        spectralSupportInverse F hF * Matrix.conjTranspose Γ) =
      Γ * spectralSupportInverse F hF *
        (∑ a : ι, effect a) * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_sum, Matrix.sum_mul]
    _ = Γ * spectralSupportInverse F hF * F *
          spectralSupportInverse F hF * Matrix.conjTranspose Γ := by
            rw [hsum]
    _ = Γ * (spectralSupportInverse F hF * F *
          spectralSupportInverse F hF) * Matrix.conjTranspose Γ := by
            simp only [Matrix.mul_assoc]
    _ = Γ * spectralSupportInverse F hF *
          Matrix.conjTranspose Γ := by
            rw [spectralSupportInverse_penrose]

private def purifiedRefinedEffect
    {ι d e : Type*} [DecidableEq ι]
    [Fintype d] [DecidableEq d]
     [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (a₀ a : ι) : Matrix e e ℂ :=
  purifiedRefinementCore F hF Γ effect a +
    if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0

theorem purifiedRefinedEffect_posSemidef
    {ι d e : Type*} [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (a₀ a : ι) :
    (purifiedRefinedEffect F hF Γ effect a₀ a).PosSemidef := by
  change (purifiedRefinementCore F hF Γ effect a +
    if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0).PosSemidef
  refine (purifiedRefinementCore_posSemidef F hF Γ effect
    hpositive a).add ?_
  split
  · exact purificationRangeProjection_complement_posSemidef F hF Γ hΓ
  · exact Matrix.PosSemidef.zero

theorem purifiedRefinedEffect_complete
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
     [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (effect : ι → Matrix d d ℂ)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ : ι) :
    (∑ a : ι, purifiedRefinedEffect F hF Γ effect a₀ a) = 1 := by
  classical
  unfold purifiedRefinedEffect
  rw [Finset.sum_add_distrib]
  rw [purifiedRefinementCore_sum F hF Γ effect hsum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, add_sub_cancel]

theorem purificationRangeProjection_compression
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    Matrix.conjTranspose Γ * purificationRangeProjection F hF Γ * Γ = F := by
  unfold purificationRangeProjection
  calc
    Matrix.conjTranspose Γ *
        (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) * Γ =
      (Matrix.conjTranspose Γ * Γ) * spectralSupportInverse F hF *
        (Matrix.conjTranspose Γ * Γ) := by
          simp only [Matrix.mul_assoc]
    _ = F * spectralSupportInverse F hF * F := by rw [hΓ]
    _ = spectralSupportProjection F hF * F := by
      rw [mul_spectralSupportInverse]
    _ = F := spectralSupportProjection_mul F hF

theorem purificationRangeProjection_complement_compression
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ = 0 := by
  calc
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ =
      Matrix.conjTranspose Γ * Γ -
        Matrix.conjTranspose Γ * purificationRangeProjection F hF Γ * Γ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          simp only [Matrix.mul_one]
    _ = F - F := by
      rw [hΓ, purificationRangeProjection_compression F hF Γ hΓ]
    _ = 0 := sub_self F

theorem purifiedRefinementCore_compression
    {ι d e : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    [Fintype e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a : ι) :
    Matrix.conjTranspose Γ *
        purifiedRefinementCore F hF Γ effect a * Γ = effect a := by
  have hsub : (F - effect a).PosSemidef := by
    rw [← hsum]
    exact refinement_complement_posSemidef effect hpositive a
  unfold purifiedRefinementCore
  calc
    Matrix.conjTranspose Γ *
        (Γ * spectralSupportInverse F hF * effect a *
          spectralSupportInverse F hF * Matrix.conjTranspose Γ) * Γ =
      (Matrix.conjTranspose Γ * Γ) * spectralSupportInverse F hF *
        effect a * spectralSupportInverse F hF *
          (Matrix.conjTranspose Γ * Γ) := by
            simp only [Matrix.mul_assoc]
    _ = F * spectralSupportInverse F hF * effect a *
          spectralSupportInverse F hF * F := by
            rw [hΓ]
    _ = (F * spectralSupportInverse F hF) * effect a *
          (spectralSupportInverse F hF * F) := by
            simp only [Matrix.mul_assoc]
    _ = spectralSupportProjection F hF * effect a *
          spectralSupportProjection F hF := by
            rw [mul_spectralSupportInverse, spectralSupportInverse_mul]
    _ = effect a := by
      rw [spectralSupportProjection_mul_posSemidef hF
        (hpositive a) hsub]
      exact posSemidef_mul_spectralSupportProjection hF
        (hpositive a) hsub

theorem purifiedRefinedEffect_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
        purifiedRefinedEffect F hF Γ effect a₀ a * Γ = effect a := by
  have hdefect : Matrix.conjTranspose Γ *
      (if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0) *
        Γ = 0 := by
    split
    · exact purificationRangeProjection_complement_compression F hF Γ hΓ
    · simp only [Matrix.mul_zero, Matrix.zero_mul]
  change Matrix.conjTranspose Γ *
      (purifiedRefinementCore F hF Γ effect a +
        if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0) *
        Γ = effect a
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [purifiedRefinementCore_compression F hF Γ hΓ
    effect hpositive hsum a, hdefect, add_zero]

/-- The positive operator-valued measurement implementing purified refined. -/
def purifiedRefinedPOVM
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ : ι) : POVM ι e where
  effect := purifiedRefinedEffect F hF Γ effect a₀
  positive a := purifiedRefinedEffect_posSemidef F hF Γ hΓ
    effect hpositive a₀ a
  complete := purifiedRefinedEffect_complete F hF Γ effect hsum a₀

theorem purifiedRefinedPOVM_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
      (purifiedRefinedPOVM F hF Γ hΓ effect hpositive hsum a₀).effect a *
        Γ = effect a :=
  purifiedRefinedEffect_compression F hF Γ hΓ effect
    hpositive hsum a₀ a

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


/-- The set of coordinates remaining after full history. -/
def fullHistoryRemaining (n : ℕ)
    (D L : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ D) \ L

/-- A partial transcript split into conditioned, revealed, and remaining coordinates. -/
@[ext (iff := false)] structure FullSubsetHistory
    (X Y : Type*)
    (n : ℕ) (D L : Finset (Fin n)) where
  /-- Alice's questions on conditioned coordinates. -/
  aliceConditioned : {i : Fin n // i ∈ D} → X
  /-- Bob's questions on conditioned coordinates. -/
  bobConditioned : {i : Fin n // i ∈ D} → Y
  /-- Alice's questions on revealed coordinates. -/
  aliceRevealed : {i : Fin n // i ∈ L} → X
  /-- Bob's questions on the remaining coordinates. -/
  bobRemaining : {i : Fin n // i ∈ fullHistoryRemaining n D L} → Y
  deriving Fintype

/--
The full history alice question construction used in the quantum parallel-repetition argument.
-/
def fullHistoryAliceQuestion
    {X Y : Type*}
    {n : ℕ} {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) :
    Fin n → X := fun i =>
  if hiD : i ∈ D then h.aliceConditioned ⟨i, hiD⟩
  else if hiL : i ∈ L then h.aliceRevealed ⟨i, hiL⟩
  else hidden ⟨i, by
    simp only [fullHistoryRemaining, Finset.mem_sdiff, Finset.mem_univ, hiD, not_false_eq_true,
      and_self, hiL]⟩

/-- The full history bob question construction used in the quantum parallel-repetition argument. -/
def fullHistoryBobQuestion
    {X Y : Type*}
    {n : ℕ} {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) :
    Fin n → Y := fun i =>
  if hiD : i ∈ D then h.bobConditioned ⟨i, hiD⟩
  else if hiL : i ∈ L then hidden ⟨i, hiL⟩
  else h.bobRemaining ⟨i, by
    simp only [fullHistoryRemaining, Finset.mem_sdiff, Finset.mem_univ, hiD, not_false_eq_true,
      and_self, hiL]⟩

private def fullHistoryQuestionEquiv
    {X Y : Type*}
    {n : ℕ} (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D) :
    (FullSubsetHistory X Y n D L ×
      ({i : Fin n // i ∈ fullHistoryRemaining n D L} → X) ×
      ({i : Fin n // i ∈ L} → Y)) ≃
      ((Fin n → X) × (Fin n → Y)) where
  toFun t :=
    (fullHistoryAliceQuestion t.1 t.2.1,
      fullHistoryBobQuestion t.1 t.2.2)
  invFun q :=
    (⟨fun i => q.1 i,
      fun i => q.2 i,
      fun i => q.1 i,
      fun i => q.2 i⟩,
      (fun i => q.1 i),
      (fun i => q.2 i))
  left_inv := by
    rintro ⟨h, hx, hy⟩
    apply Prod.ext
    · apply FullSubsetHistory.ext
      · funext i
        simp only [fullHistoryAliceQuestion, i.property, ↓reduceDIte, Subtype.coe_eta]
      · funext i
        simp only [fullHistoryBobQuestion, i.property, ↓reduceDIte, Subtype.coe_eta]
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp (hL i.property)).2
        simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte, i.property, Subtype.coe_eta]
      · funext i
        have hiD : (i : Fin n) ∉ D := by
          have := i.property
          simpa only [fullHistoryRemaining] using
            (Finset.mem_sdiff.mp
              (Finset.mem_sdiff.mp i.property).1).2
        have hiL : (i : Fin n) ∉ L :=
          (Finset.mem_sdiff.mp i.property).2
        simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte, hiL]
    · apply Prod.ext
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp
            (Finset.mem_sdiff.mp i.property).1).2
        have hiL : (i : Fin n) ∉ L :=
          (Finset.mem_sdiff.mp i.property).2
        simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte, hiL]
      · funext i
        have hiD : (i : Fin n) ∉ D :=
          (Finset.mem_sdiff.mp (hL i.property)).2
        simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte, i.property, Subtype.coe_eta]
  right_inv := by
    rintro ⟨xs, ys⟩
    apply Prod.ext
    · funext i
      by_cases hiD : i ∈ D
      · simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte]
      · by_cases hiL : i ∈ L <;>
          simp only [fullHistoryAliceQuestion, hiD, ↓reduceDIte, hiL]
    · funext i
      by_cases hiD : i ∈ D
      · simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte]
      · by_cases hiL : i ∈ L <;>
          simp only [fullHistoryBobQuestion, hiD, ↓reduceDIte, hiL]

section ActualHistoryWeights

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The probability weight for full history. -/
def fullHistoryWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) : ℝ :=
  (∏ i : {i : Fin n // i ∈ D},
    G.questionWeight (h.aliceConditioned i) (h.bobConditioned i)) *
  (∏ i : {i : Fin n // i ∈ L},
    G.marginalX (h.aliceRevealed i)) *
  (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
    G.marginalY (h.bobRemaining i))

/-- The probability weight for full history hidden alice. -/
def fullHistoryHiddenAliceWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) : ℝ :=
  ∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
    G.conditionalXGivenY (h.bobRemaining i) (hidden i)

/-- The probability weight for full history hidden bob. -/
def fullHistoryHiddenBobWeight
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) : ℝ :=
  ∏ i : {i : Fin n // i ∈ L},
    G.conditionalYGivenX (h.aliceRevealed i) (hidden i)

theorem fullHistoryWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) :
    0 ≤ fullHistoryWeight G h := by
  unfold fullHistoryWeight
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun i _ =>
        G.weight_nonneg (h.aliceConditioned i) (h.bobConditioned i)
    · exact Finset.prod_nonneg fun i _ =>
        G.marginalX_nonneg (h.aliceRevealed i)
  · exact Finset.prod_nonneg fun i _ =>
      G.marginalY_nonneg (h.bobRemaining i)

theorem fullHistoryHiddenAliceWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X) :
    0 ≤ fullHistoryHiddenAliceWeight G h hidden := by
  unfold fullHistoryHiddenAliceWeight
  exact Finset.prod_nonneg fun i _ =>
    G.conditionalXGivenY_nonneg (h.bobRemaining i) (hidden i)

theorem fullHistoryHiddenBobWeight_nonneg
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (hidden : {i : Fin n // i ∈ L} → Y) :
    0 ≤ fullHistoryHiddenBobWeight G h hidden := by
  unfold fullHistoryHiddenBobWeight
  exact Finset.prod_nonneg fun i _ =>
    G.conditionalYGivenX_nonneg (h.aliceRevealed i) (hidden i)

theorem fullHistoryWeight_mul_hidden
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D)
    (h : FullSubsetHistory X Y n D L)
    (hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X)
    (hy : {i : Fin n // i ∈ L} → Y) :
    fullHistoryWeight G h *
        fullHistoryHiddenAliceWeight G h hx *
        fullHistoryHiddenBobWeight G h hy =
      (G.repeat n).questionWeight
        (fullHistoryAliceQuestion h hx)
        (fullHistoryBobQuestion h hy) := by
  classical
  let q : Fin n → ℝ := fun i =>
    G.questionWeight
      (fullHistoryAliceQuestion h hx i)
      (fullHistoryBobQuestion h hy i)
  have hDprod :
      (∏ i : {i : Fin n // i ∈ D},
        G.questionWeight
          (h.aliceConditioned i) (h.bobConditioned i)) =
        ∏ i ∈ D, q i := by
    calc
      (∏ i : {i : Fin n // i ∈ D},
        G.questionWeight
          (h.aliceConditioned i) (h.bobConditioned i)) =
        ∏ i : {i : Fin n // i ∈ D}, q i := by
          apply Finset.prod_congr rfl
          intro i _
          simp only [fullHistoryAliceQuestion, fullHistoryBobQuestion, i.property, ↓reduceDIte,
            Subtype.coe_eta, q]
      _ = ∏ i ∈ D, q i := Finset.prod_coe_sort D q
  have hLprod :
      (∏ i : {i : Fin n // i ∈ L},
        G.marginalX (h.aliceRevealed i)) *
      (∏ i : {i : Fin n // i ∈ L},
        G.conditionalYGivenX
          (h.aliceRevealed i) (hy i)) =
        ∏ i ∈ L, q i := by
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ i : {i : Fin n // i ∈ L},
        G.marginalX (h.aliceRevealed i) *
          G.conditionalYGivenX (h.aliceRevealed i) (hy i)) =
        ∏ i : {i : Fin n // i ∈ L}, q i := by
          apply Finset.prod_congr rfl
          intro i _
          have hiD : (i : Fin n) ∉ D :=
            (Finset.mem_sdiff.mp (hL i.property)).2
          simpa only [fullHistoryAliceQuestion, fullHistoryBobQuestion, hiD, ↓reduceDIte,
            i.property, Subtype.coe_eta, q] using
              G.marginalX_mul_conditionalYGivenX
                (h.aliceRevealed i) (hy i)
      _ = ∏ i ∈ L, q i := Finset.prod_coe_sort L q
  have hRprod :
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.marginalY (h.bobRemaining i)) *
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.conditionalXGivenY
          (h.bobRemaining i) (hx i)) =
        ∏ i ∈ fullHistoryRemaining n D L, q i := by
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.marginalY (h.bobRemaining i) *
          G.conditionalXGivenY (h.bobRemaining i) (hx i)) =
        ∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L}, q i := by
          apply Finset.prod_congr rfl
          intro i _
          have hiD : (i : Fin n) ∉ D :=
            (Finset.mem_sdiff.mp
              (Finset.mem_sdiff.mp i.property).1).2
          have hiL : (i : Fin n) ∉ L :=
            (Finset.mem_sdiff.mp i.property).2
          simpa only [fullHistoryAliceQuestion, fullHistoryBobQuestion, hiD, ↓reduceDIte, hiL,
            Subtype.coe_eta, q] using
              G.marginalY_mul_conditionalXGivenY
                (hx i) (h.bobRemaining i)
      _ = ∏ i ∈ fullHistoryRemaining n D L, q i :=
        Finset.prod_coe_sort (fullHistoryRemaining n D L) q
  have hDL : Disjoint D L := by
    apply Finset.disjoint_left.mpr
    intro i hiD hiL
    exact (Finset.mem_sdiff.mp (hL hiL)).2 hiD
  have hDR : Disjoint (D ∪ L) (fullHistoryRemaining n D L) := by
    apply Finset.disjoint_left.mpr
    intro i hiUnion hiR
    have hiD : i ∉ D :=
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hiR).1).2
    have hiL : i ∉ L := (Finset.mem_sdiff.mp hiR).2
    rcases Finset.mem_union.mp hiUnion with hi | hi
    · exact hiD hi
    · exact hiL hi
  have hcover : D ∪ L ∪ fullHistoryRemaining n D L =
      (Finset.univ : Finset (Fin n)) := by
    ext i
    simp only [fullHistoryRemaining, Finset.union_assoc, Finset.union_sdiff_self_eq_union,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    tauto
  rw [Game.repeat_questionWeight]
  change fullHistoryWeight G h *
      fullHistoryHiddenAliceWeight G h hx *
      fullHistoryHiddenBobWeight G h hy =
    ∏ i : Fin n, q i
  unfold fullHistoryWeight fullHistoryHiddenAliceWeight
    fullHistoryHiddenBobWeight
  calc
    ((∏ i : {i : Fin n // i ∈ D},
        G.questionWeight
          (h.aliceConditioned i) (h.bobConditioned i)) *
      (∏ i : {i : Fin n // i ∈ L},
        G.marginalX (h.aliceRevealed i)) *
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.marginalY (h.bobRemaining i))) *
      (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
        G.conditionalXGivenY
          (h.bobRemaining i) (hx i)) *
      (∏ i : {i : Fin n // i ∈ L},
        G.conditionalYGivenX
          (h.aliceRevealed i) (hy i)) =
      (∏ i : {i : Fin n // i ∈ D},
        G.questionWeight
          (h.aliceConditioned i) (h.bobConditioned i)) *
        ((∏ i : {i : Fin n // i ∈ L},
          G.marginalX (h.aliceRevealed i)) *
          (∏ i : {i : Fin n // i ∈ L},
            G.conditionalYGivenX
              (h.aliceRevealed i) (hy i))) *
        ((∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
          G.marginalY (h.bobRemaining i)) *
          (∏ i : {i : Fin n // i ∈ fullHistoryRemaining n D L},
            G.conditionalXGivenY
              (h.bobRemaining i) (hx i))) := by ring
    _ = (∏ i ∈ D, q i) *
          (∏ i ∈ L, q i) *
          (∏ i ∈ fullHistoryRemaining n D L, q i) := by
            rw [hDprod, hLprod, hRprod]
    _ = ∏ i : Fin n, q i := by
      rw [← Finset.prod_union hDL,
        ← Finset.prod_union hDR, hcover]

/-- The spectral filter for full history alice. -/
def fullHistoryAliceFilter
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A) :
    Matrix S.Alice S.Alice ℂ :=
  ∑ hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
    fullHistoryHiddenAliceWeight G h hidden •
      conditionedAliceEffect G n S D α
        (fullHistoryAliceQuestion h hidden)

/-- The spectral filter for full history bob. -/
def fullHistoryBobFilter
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {i : Fin n // i ∈ D} → B) :
    Matrix S.Bob S.Bob ℂ :=
  ∑ hidden : {i : Fin n // i ∈ L} → Y,
    fullHistoryHiddenBobWeight G h hidden •
      conditionedBobEffect G n S D β
        (fullHistoryBobQuestion h hidden)

theorem fullHistoryAliceFilter_posSemidef
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A) :
    (fullHistoryAliceFilter G n S D L h α).PosSemidef := by
  unfold fullHistoryAliceFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro hidden _
  exact (conditionedAliceEffect_positive G n S D α
    (fullHistoryAliceQuestion h hidden)).smul
      (fullHistoryHiddenAliceWeight_nonneg G h hidden)

theorem fullHistoryBobFilter_posSemidef
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {i : Fin n // i ∈ D} → B) :
    (fullHistoryBobFilter G n S D L h β).PosSemidef := by
  unfold fullHistoryBobFilter
  apply Matrix.posSemidef_sum Finset.univ
  intro hidden _
  exact (conditionedBobEffect_positive G n S D β
    (fullHistoryBobQuestion h hidden)).smul
      (fullHistoryHiddenBobWeight_nonneg G h hidden)

/-- The indicator function for full history win. -/
def fullHistoryWinIndicator
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) : ℝ := by
  classical
  exact if ∀ i : {i : Fin n // i ∈ D},
    G.predicate (h.aliceConditioned i) (h.bobConditioned i)
      (α i) (β i) = true then 1 else 0

theorem fullHistoryWinIndicator_nonneg
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) :
    0 ≤ fullHistoryWinIndicator G h α β := by
  classical
  unfold fullHistoryWinIndicator
  split <;> norm_num

theorem conditionedAnswerMatches_iff
    {T : Type*} {n : ℕ}
    (D : Finset (Fin n))
    (answer : Fin n → T)
    (α : {i : Fin n // i ∈ D} → T) :
    (∀ (i : Fin n) (hi : i ∈ D), answer i = α ⟨i, hi⟩) ↔
      α = fun i : {i : Fin n // i ∈ D} => answer (i : Fin n) := by
  constructor
  · intro h
    funext i
    exact (h i i.property).symm
  · intro h i hi
    subst α
    rfl

theorem conditionedEffects_born_expansion
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y) :
    bornTracePairing S.state.matrix
        (conditionedAliceEffect G n S D α xs)
        (conditionedBobEffect G n S D β ys) =
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if ∀ (i : Fin n) (hi : i ∈ D), aa i = α ⟨i, hi⟩ then
          if ∀ (i : Fin n) (hi : i ∈ D), bb i = β ⟨i, hi⟩ then
            S.outcomeProbability xs ys aa bb
          else 0
        else 0 := by
  classical
  simp only [conditionedAliceEffect, conditionedBobEffect,
    map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro aa _
  split_ifs with ha
  · apply Finset.sum_congr rfl
    intro bb _
    split_ifs with hb
    · rfl
    · exact map_zero _
  · simp only [map_zero, LinearMap.zero_apply, Finset.sum_const_zero]

theorem finite_sum_four_swap
    {I J K T : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype T]
    (f : I → J → K → T → ℝ) :
    (∑ i : I, ∑ j : J, ∑ k : K, ∑ t : T, f i j k t) =
      ∑ k : K, ∑ t : T, ∑ i : I, ∑ j : J, f i j k t := by
  classical
  calc
    (∑ i : I, ∑ j : J, ∑ k : K, ∑ t : T, f i j k t) =
      ∑ i : I, ∑ k : K, ∑ j : J, ∑ t : T, f i j k t := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ k : K, ∑ i : I, ∑ j : J, ∑ t : T, f i j k t := by
      rw [Finset.sum_comm]
    _ = ∑ k : K, ∑ i : I, ∑ t : T, ∑ j : J, f i j k t := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k : K, ∑ t : T, ∑ i : I, ∑ j : J, f i j k t := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

private def fullQuestionWinIndicator
    (G : Game X Y A B) {n : ℕ}
    (D : Finset (Fin n))
    (xs : Fin n → X) (ys : Fin n → Y)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) : ℝ := by
  classical
  exact if ∀ i : {i : Fin n // i ∈ D},
    G.predicate (xs i) (ys i) (α i) (β i) = true
    then 1 else 0

theorem fullHistoryWinIndicator_eq_question
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X)
    (hy : {i : Fin n // i ∈ L} → Y)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) :
    fullHistoryWinIndicator G h α β =
      fullQuestionWinIndicator G D
        (fullHistoryAliceQuestion h hx)
        (fullHistoryBobQuestion h hy) α β := by
  classical
  unfold fullHistoryWinIndicator fullQuestionWinIndicator
  congr 1
  apply propext
  constructor
  · intro hw i
    simpa only [fullHistoryAliceQuestion, i.property, ↓reduceDIte, Subtype.coe_eta,
      fullHistoryBobQuestion] using hw i
  · intro hw i
    simpa only [fullHistoryAliceQuestion, i.property, ↓reduceDIte, Subtype.coe_eta,
      fullHistoryBobQuestion] using hw i

theorem conditionedEffects_postselection_sum
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (xs : Fin n → X) (ys : Fin n → Y) :
    (∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullQuestionWinIndicator G D xs ys α β *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α xs)
            (conditionedBobEffect G n S D β ys)) =
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if ∀ i : {i : Fin n // i ∈ D},
          G.predicate (xs i) (ys i) (aa i) (bb i) = true
        then S.outcomeProbability xs ys aa bb else 0 := by
  classical
  simp_rw [conditionedEffects_born_expansion G n S D]
  calc
    (∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullQuestionWinIndicator G D xs ys α β *
          (∑ aa : Fin n → A, ∑ bb : Fin n → B,
            if ∀ (i : Fin n) (hi : i ∈ D), aa i = α ⟨i, hi⟩ then
              if ∀ (i : Fin n) (hi : i ∈ D), bb i = β ⟨i, hi⟩ then
                S.outcomeProbability xs ys aa bb else 0
            else 0)) =
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        fullQuestionWinIndicator G D xs ys α β *
          (if ∀ (i : Fin n) (hi : i ∈ D), aa i = α ⟨i, hi⟩ then
            if ∀ (i : Fin n) (hi : i ∈ D), bb i = β ⟨i, hi⟩ then
              S.outcomeProbability xs ys aa bb else 0
          else 0) := by
            simp only [Finset.mul_sum]
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullQuestionWinIndicator G D xs ys α β *
          (if ∀ (i : Fin n) (hi : i ∈ D), aa i = α ⟨i, hi⟩ then
            if ∀ (i : Fin n) (hi : i ∈ D), bb i = β ⟨i, hi⟩ then
              S.outcomeProbability xs ys aa bb else 0
          else 0) := finite_sum_four_swap _
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if ∀ i : {i : Fin n // i ∈ D},
          G.predicate (xs i) (ys i) (aa i) (bb i) = true
        then S.outcomeProbability xs ys aa bb else 0 := by
      apply Finset.sum_congr rfl
      intro aa _
      apply Finset.sum_congr rfl
      intro bb _
      simp only [fullQuestionWinIndicator, Subtype.forall, conditionedAnswerMatches_iff, mul_ite,
        ite_mul, one_mul, zero_mul, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]

theorem repeated_partialWinMass_expansion
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        (G.repeat n).questionWeight xs ys *
          (if ∀ i : {i : Fin n // i ∈ D},
            G.predicate (xs i) (ys i) (aa i) (bb i) = true
          then S.outcomeProbability xs ys aa bb else 0) := by
  classical
  unfold FiniteEventLaw.eventMass FiniteEventLaw.winEvent
  simp only [Finset.sum_filter]
  simp only [strategyEventLaw]
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  apply Finset.sum_congr rfl
  intro aa _
  apply Finset.sum_congr rfl
  intro bb _
  have hiff :
      (∀ i ∈ D, repeatedCoordinateWin G n i (xs, ys, aa, bb) = true) ↔
        (∀ i : {i : Fin n // i ∈ D},
          G.predicate (xs i) (ys i) (aa i) (bb i) = true) := by
    constructor
    · intro h i
      simpa only [repeatedCoordinateWin] using h i i.property
    · intro h i hi
      simpa only [repeatedCoordinateWin] using h ⟨i, hi⟩
  by_cases hw : ∀ i : {i : Fin n // i ∈ D},
    G.predicate (xs i) (ys i) (aa i) (bb i) = true
  · calc
      (if ∀ i ∈ D, repeatedCoordinateWin G n i (xs, ys, aa, bb) = true then
          (G.repeat n).questionWeight xs ys * S.outcomeProbability xs ys aa bb else 0) =
          (G.repeat n).questionWeight xs ys * S.outcomeProbability xs ys aa bb :=
        ite_eq_left (hiff.mpr hw)
      _ = (G.repeat n).questionWeight xs ys *
          (if ∀ i : {i : Fin n // i ∈ D},
            G.predicate (xs i) (ys i) (aa i) (bb i) = true then
              S.outcomeProbability xs ys aa bb else 0) :=
        congrArg ((G.repeat n).questionWeight xs ys * ·) (ite_eq_left hw).symm
  · calc
      (if ∀ i ∈ D, repeatedCoordinateWin G n i (xs, ys, aa, bb) = true then
          (G.repeat n).questionWeight xs ys * S.outcomeProbability xs ys aa bb else 0) = 0 :=
        ite_eq_right (mt hiff.mp hw)
      _ = (G.repeat n).questionWeight xs ys * 0 := (mul_zero _).symm
      _ = (G.repeat n).questionWeight xs ys *
          (if ∀ i : {i : Fin n // i ∈ D},
            G.predicate (xs i) (ys i) (aa i) (bb i) = true then
              S.outcomeProbability xs ys aa bb else 0) :=
        congrArg ((G.repeat n).questionWeight xs ys * ·) (ite_eq_right hw).symm

theorem fullQuestionConditionedBornMass_eq
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        (G.repeat n).questionWeight xs ys *
          fullQuestionWinIndicator G D xs ys α β *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α xs)
            (conditionedBobEffect G n S D β ys)) =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) := by
  classical
  calc
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        (G.repeat n).questionWeight xs ys *
          fullQuestionWinIndicator G D xs ys α β *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α xs)
            (conditionedBobEffect G n S D β ys)) =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        (G.repeat n).questionWeight xs ys *
          (∑ α : {i : Fin n // i ∈ D} → A,
            ∑ β : {i : Fin n // i ∈ D} → B,
              fullQuestionWinIndicator G D xs ys α β *
                bornTracePairing S.state.matrix
                  (conditionedAliceEffect G n S D α xs)
                  (conditionedBobEffect G n S D β ys)) := by
        apply Finset.sum_congr rfl
        intro xs _
        apply Finset.sum_congr rfl
        intro ys _
        simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ aa : Fin n → A, ∑ bb : Fin n → B,
        (G.repeat n).questionWeight xs ys *
          (if ∀ i : {i : Fin n // i ∈ D},
            G.predicate (xs i) (ys i) (aa i) (bb i) = true
          then S.outcomeProbability xs ys aa bb else 0) := by
        apply Finset.sum_congr rfl
        intro xs _
        apply Finset.sum_congr rfl
        intro ys _
        rw [conditionedEffects_postselection_sum G n S D xs ys]
        simp only [Finset.mul_sum]
    _ = _ := (repeated_partialWinMass_expansion G n S D).symm

theorem fullHistoryFilters_born_expansion
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A)
    (β : {i : Fin n // i ∈ D} → B) :
    bornTracePairing S.state.matrix
        (fullHistoryAliceFilter G n S D L h α)
        (fullHistoryBobFilter G n S D L h β) =
      ∑ hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      ∑ hy : {i : Fin n // i ∈ L} → Y,
        fullHistoryHiddenAliceWeight G h hx *
          fullHistoryHiddenBobWeight G h hy *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α
              (fullHistoryAliceQuestion h hx))
            (conditionedBobEffect G n S D β
              (fullHistoryBobQuestion h hy)) := by
  classical
  unfold fullHistoryAliceFilter fullHistoryBobFilter
  simp only [map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro hx _
  apply Finset.sum_congr rfl
  intro hy _
  ring

theorem fullSubsetHistory_mass_eq_postselection
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (hL : L ⊆ Finset.univ \ D) :
    (∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          bornTracePairing S.state.matrix
            (fullHistoryAliceFilter G n S D L h α)
            (fullHistoryBobFilter G n S D L h β)) =
      (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) D) := by
  classical
  calc
    (∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          bornTracePairing S.state.matrix
            (fullHistoryAliceFilter G n S D L h α)
            (fullHistoryBobFilter G n S D L h β)) =
      ∑ h : FullSubsetHistory X Y n D L,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
      ∑ hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      ∑ hy : {i : Fin n // i ∈ L} → Y,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          fullHistoryHiddenAliceWeight G h hx *
          fullHistoryHiddenBobWeight G h hy *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α
              (fullHistoryAliceQuestion h hx))
            (conditionedBobEffect G n S D β
              (fullHistoryBobQuestion h hy)) := by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        rw [fullHistoryFilters_born_expansion G n S D L h α β]
        simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ h : FullSubsetHistory X Y n D L,
      ∑ hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      ∑ hy : {i : Fin n // i ∈ L} → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
          fullHistoryHiddenAliceWeight G h hx *
          fullHistoryHiddenBobWeight G h hy *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α
              (fullHistoryAliceQuestion h hx))
            (conditionedBobEffect G n S D β
              (fullHistoryBobQuestion h hy)) := by
        apply Finset.sum_congr rfl
        intro h _
        exact finite_sum_four_swap _
    _ = ∑ h : FullSubsetHistory X Y n D L,
      ∑ hx : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      ∑ hy : {i : Fin n // i ∈ L} → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        (G.repeat n).questionWeight
          (fullHistoryAliceQuestion h hx)
          (fullHistoryBobQuestion h hy) *
        fullQuestionWinIndicator G D
          (fullHistoryAliceQuestion h hx)
          (fullHistoryBobQuestion h hy) α β *
        bornTracePairing S.state.matrix
          (conditionedAliceEffect G n S D α
            (fullHistoryAliceQuestion h hx))
          (conditionedBobEffect G n S D β
            (fullHistoryBobQuestion h hy)) := by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro hx _
        apply Finset.sum_congr rfl
        intro hy _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        rw [fullHistoryWinIndicator_eq_question G D L h hx hy α β]
        rw [← fullHistoryWeight_mul_hidden G D L hL h hx hy]
        ring
    _ = ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        (G.repeat n).questionWeight xs ys *
          fullQuestionWinIndicator G D xs ys α β *
          bornTracePairing S.state.matrix
            (conditionedAliceEffect G n S D α xs)
            (conditionedBobEffect G n S D β ys) := by
      let f : ((Fin n → X) × (Fin n → Y)) → ℝ := fun q =>
        ∑ α : {i : Fin n // i ∈ D} → A,
        ∑ β : {i : Fin n // i ∈ D} → B,
          (G.repeat n).questionWeight q.1 q.2 *
            fullQuestionWinIndicator G D q.1 q.2 α β *
            bornTracePairing S.state.matrix
              (conditionedAliceEffect G n S D α q.1)
              (conditionedBobEffect G n S D β q.2)
      simpa only [f, fullHistoryQuestionEquiv, Equiv.coe_fn_mk,
        Fintype.sum_prod_type] using
        (fullHistoryQuestionEquiv
          (X := X) (Y := Y) D L hL).sum_comp f
    _ = _ := fullQuestionConditionedBornMass_eq G n S D

end ActualHistoryWeights

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralPurificationFilter_mul_shift
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s *
        (F + s • (1 : Matrix d d ℂ)) = F := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let D : Matrix d d ℂ :=
    Matrix.diagonal fun i => (eigenvalue i : ℂ)
  let T : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U
  have heigenvalue (i : d) : 0 ≤ eigenvalue i :=
    hF.eigenvalues_nonneg i
  have hden (i : d) : eigenvalue i + s ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (heigenvalue i) hs)
  have hFspec : F = e D := by
    simpa [D, eigenvalue, e, Function.comp_def] using
      hF.isHermitian.spectral_theorem
  have hshift_inner :
      D + s • (1 : Matrix d d ℂ) =
        Matrix.diagonal fun i => ((eigenvalue i + s : ℝ) : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Matrix.one_apply_eq, Complex.real_smul, mul_one, Complex.ofReal_add, D]
    · simp only [Matrix.add_apply, ne_eq, hij, not_false_eq_true, Matrix.diagonal_apply_ne,
        Matrix.smul_apply, Matrix.one_apply_ne, smul_zero, add_zero, Complex.ofReal_add, D]
  have hproduct : T * (D + s • (1 : Matrix d d ℂ)) = D := by
    rw [hshift_inner]
    change
      Matrix.diagonal (fun i =>
        ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)) *
          Matrix.diagonal (fun i => ((eigenvalue i + s : ℝ) : ℂ)) =
        Matrix.diagonal (fun i => (eigenvalue i : ℂ))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    push_cast
    have hden_complex :
        (eigenvalue i : ℂ) + (s : ℂ) ≠ 0 := by
      exact_mod_cast hden i
    rw [div_mul_cancel₀ _ hden_complex]
  have hscalar : e (s • (1 : Matrix d d ℂ)) =
      s • (1 : Matrix d d ℂ) := by
    change
      (U : Matrix d d ℂ) * (s • (1 : Matrix d d ℂ)) *
          star (U : Matrix d d ℂ) = s • (1 : Matrix d d ℂ)
    rw [mul_smul_comm, mul_one, smul_mul_assoc]
    simp only [SetLike.coe_mem, Unitary.mul_star_self_of_mem]
  change e T * (F + s • (1 : Matrix d d ℂ)) = F
  rw [hFspec, ← hscalar, ← map_add, ← map_mul, hproduct]

theorem spectralPurificationFilter_eq_resolvent
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s =
      F * (F + s • (1 : Matrix d d ℂ))⁻¹ := by
  have hdet : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  calc
    spectralPurificationFilter F hF s =
        spectralPurificationFilter F hF s *
          ((F + s • (1 : Matrix d d ℂ)) *
            (F + s • (1 : Matrix d d ℂ))⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, mul_one]
    _ = (spectralPurificationFilter F hF s *
          (F + s • (1 : Matrix d d ℂ))) *
          (F + s • (1 : Matrix d d ℂ))⁻¹ := by
          rw [mul_assoc]
    _ = F * (F + s • (1 : Matrix d d ℂ))⁻¹ := by
          rw [spectralPurificationFilter_mul_shift F hF hs]

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralPurificationFilter_square_contraction
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (spectralPurificationFilter F hF s -
      star (spectralPurificationFilter F hF s) *
        spectralPurificationFilter F hF s).PosSemidef := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let D : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U
  have hDhermitian : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ) = _
    simp only [Complex.ofReal_div, Complex.ofReal_add, star_div₀, RCLike.star_def,
      Complex.conj_ofReal, star_add]
  have hDstar : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using hDhermitian.eq
  have hdiag : (D - D * D).PosSemidef := by
    rw [show D * D = Matrix.diagonal (fun i =>
      (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) by
        dsimp [D]
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        simp only [Complex.ofReal_div, Complex.ofReal_add, pow_two, Complex.ofReal_mul]]
    have hsub : D - Matrix.diagonal (fun i =>
        (((eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) =
        Matrix.diagonal (fun i =>
          ((eigenvalue i / (eigenvalue i + s) -
            (eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow, Matrix.sub_apply,
          Matrix.diagonal_apply_eq, Complex.ofReal_sub, D]
      · simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow, Matrix.sub_apply,
          ne_eq, hij, not_false_eq_true, Matrix.diagonal_apply_ne, sub_self, Complex.ofReal_sub,
          D]
    rw [hsub]
    apply Matrix.PosSemidef.diagonal
    intro i
    change 0 ≤ ((eigenvalue i / (eigenvalue i + s) -
      (eigenvalue i / (eigenvalue i + s)) ^ 2 : ℝ) : ℂ)
    apply Complex.nonneg_iff.mpr
    constructor
    · have hnonneg : 0 ≤ eigenvalue i / (eigenvalue i + s) :=
        div_nonneg (hF.eigenvalues_nonneg i)
          (le_of_lt (add_pos_of_nonneg_of_pos
            (hF.eigenvalues_nonneg i) hs))
      have hle : eigenvalue i / (eigenvalue i + s) ≤ 1 :=
        (div_le_one (add_pos_of_nonneg_of_pos
          (hF.eigenvalues_nonneg i) hs)).mpr (by linarith)
      change 0 ≤ eigenvalue i / (eigenvalue i + s) -
        (eigenvalue i / (eigenvalue i + s)) ^ 2
      nlinarith
    · simp only [Complex.ofReal_im]
  change (e D - star (e D) * e D).PosSemidef
  rw [← map_star, hDstar, ← map_mul, ← map_sub]
  change ((U : Matrix d d ℂ) * (D - D * D) *
    star (U : Matrix d d ℂ)).PosSemidef
  simpa only [Matrix.star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same (U : Matrix d d ℂ)

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def matrixQuadraticCLM
    {d : Type*} [Fintype d]
    (x : d → ℂ) : Matrix d d ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star x ⬝ᵥ A.mulVec x
      map_add' := by
        intro A B
        simp only [dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec, Matrix.add_apply,
          add_mul, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro r A
        change
          (∑ i, star (x i) *
            ∑ j, ((r : ℂ) * A i j) * x j) =
          (r : ℂ) *
            (∑ i, star (x i) * ∑ j, A i j * x j)
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring }

private def matrixAdjointCLM
    {d : Type*} [Fintype d] :
    Matrix d d ℂ →L[ℝ] Matrix d d ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => star A
      map_add' := by
        intro A B
        exact star_add A B
      map_smul' := by
        intro r A
        simp }

theorem bochner_integral_posSemidef
    {α d : Type*} [MeasurableSpace α]
    [Fintype d]
    {μ : Measure α} {f : α → Matrix d d ℂ}
    (hf : Integrable f μ)
    (hpos : ∀ᵐ t ∂μ, (f t).PosSemidef) :
    (∫ t, f t ∂μ).PosSemidef := by
  have hadjoint :
      star (∫ t, f t ∂μ) = ∫ t, star (f t) ∂μ := by
    exact (ContinuousLinearMap.integral_comp_comm
      matrixAdjointCLM hf).symm
  have hadjoint_ae : (fun t => star (f t)) =ᵐ[μ] f := by
    filter_upwards [hpos] with t ht
    simpa only [Matrix.star_eq_conjTranspose] using ht.isHermitian.eq
  have hhermitian : (∫ t, f t ∂μ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    have hstar : star (∫ t, f t ∂μ) = ∫ t, f t ∂μ :=
      hadjoint.trans (integral_congr_ae hadjoint_ae)
    have hentry := congr_fun (congr_fun hstar i) j
    simpa only [RCLike.star_def, Matrix.star_apply] using hentry
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hhermitian
  intro x
  have hcomm :
      (∫ t, matrixQuadraticCLM x (f t) ∂μ) =
        matrixQuadraticCLM x (∫ t, f t ∂μ) :=
    ContinuousLinearMap.integral_comp_comm
      (matrixQuadraticCLM x) hf
  change 0 ≤ matrixQuadraticCLM x (∫ t, f t ∂μ)
  rw [← hcomm]
  apply integral_nonneg_of_ae
  filter_upwards [hpos] with t ht
  exact ht.dotProduct_mulVec_nonneg x

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralPurificationFilter_eq_one_sub_shifted_inverse
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s =
      1 - s • (F + s • (1 : Matrix d d ℂ))⁻¹ := by
  have hdet : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  rw [spectralPurificationFilter_eq_resolvent F hF hs]
  apply eq_sub_of_add_eq
  simpa only [add_mul, Algebra.smul_mul_assoc, one_mul] using
    Matrix.mul_nonsing_inv
      (F + s • (1 : Matrix d d ℂ)) hdet

theorem shifted_inverse_square_contraction
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (s • (F + s • (1 : Matrix d d ℂ))⁻¹ -
      s ^ 2 •
        ((F + s • (1 : Matrix d d ℂ))⁻¹ *
          (F + s • (1 : Matrix d d ℂ))⁻¹)).PosSemidef := by
  let R : Matrix d d ℂ := (F + s • (1 : Matrix d d ℂ))⁻¹
  have hstar : star R = R := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hF hs).isHermitian.eq
  have h := spectralPurificationFilter_square_contraction F hF hs
  rw [spectralPurificationFilter_eq_one_sub_shifted_inverse F hF hs] at h
  change (s • R - s ^ 2 • (R * R)).PosSemidef
  change ((1 - s • R) - star (1 - s • R) *
    (1 - s • R)).PosSemidef at h
  convert h using 1
  simp only [star_sub, star_one, star_smul, star_trivial, hstar,
    sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, pow_two]
  module

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralPurificationFilter_sub_resolvent
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s =
      s • ((F + s • (1 : Matrix d d ℂ))⁻¹ *
        (F - M) * (M + s • (1 : Matrix d d ℂ))⁻¹) := by
  have hdetF : IsUnit (F + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hF hs).isUnit
  have hdetM : IsUnit (M + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hM hs).isUnit
  rw [spectralPurificationFilter_eq_resolvent F hF hs,
    spectralPurificationFilter_eq_resolvent M hM hs]
  simpa only [Algebra.smul_mul_assoc, one_mul] using
    noncommutative_filtered_resolvent_identity
      F M (s • (1 : Matrix d d ℂ))
      (F + s • (1 : Matrix d d ℂ))⁻¹
      (M + s • (1 : Matrix d d ℂ))⁻¹
      (Matrix.mul_nonsing_inv _ hdetF)
      (Matrix.nonsing_inv_mul _ hdetF)
      (Matrix.mul_nonsing_inv _ hdetM)

theorem spectralPurificationFilter_sub_gram
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    star (spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s) *
      (spectralPurificationFilter F hF s -
        spectralPurificationFilter M hM s) =
      s ^ 2 •
        ((M + s • (1 : Matrix d d ℂ))⁻¹ * (F - M) *
          ((F + s • (1 : Matrix d d ℂ))⁻¹ *
            (F + s • (1 : Matrix d d ℂ))⁻¹) *
          (F - M) * (M + s • (1 : Matrix d d ℂ))⁻¹) := by
  let RF : Matrix d d ℂ := (F + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ := (M + s • (1 : Matrix d d ℂ))⁻¹
  let D : Matrix d d ℂ := F - M
  have hRF : star RF = RF := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hF hs).isHermitian.eq
  have hRM : star RM = RM := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (shifted_posSemidef_matrix_inverse_posSemidef hM hs).isHermitian.eq
  have hD : star D = D := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (hF.isHermitian.sub hM.isHermitian).eq
  rw [spectralPurificationFilter_sub_resolvent F M hF hM hs]
  change star (s • (RF * D * RM)) * (s • (RF * D * RM)) =
    s ^ 2 • (RM * D * (RF * RF) * D * RM)
  simp only [star_smul, star_trivial, star_mul, hRF, hRM, hD,
    smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
  congr 1
  noncomm_ring

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem weighted_shifted_inverse_second_order
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    (∑ i : ι, weight i •
      (F i + s • (1 : Matrix d d ℂ))⁻¹) -
        (M + s • (1 : Matrix d d ℂ))⁻¹ =
      (M + s • (1 : Matrix d d ℂ))⁻¹ *
        (∑ i : ι, weight i •
          ((F i - M) * (F i + s • (1 : Matrix d d ℂ))⁻¹ *
            (F i - M))) *
        (M + s • (1 : Matrix d d ℂ))⁻¹ := by
  let W : ι → Matrix d d ℂ := fun i =>
    weight i • (1 : Matrix d d ℂ)
  let RF : ι → Matrix d d ℂ := fun i =>
    (F i + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ :=
    (M + s • (1 : Matrix d d ℂ))⁻¹
  have hW_normalized : (∑ i : ι, W i) = 1 := by
    dsimp [W]
    rw [← Finset.sum_smul, normalized]
    simp only [one_smul]
  have hW_centered : (∑ i : ι, W i * (F i - M)) = 0 := by
    dsimp [W]
    simp_rw [smul_mul_assoc, one_mul]
    exact matrix_weighted_centered weight F M normalized mean
  have hW_commutes (i : ι) : W i * RM = RM * W i := by
    dsimp [W]
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hdetF (i : ι) :
      IsUnit (F i + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef (positive i) hs).isUnit
  have hdetM : IsUnit (M + s • (1 : Matrix d d ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (shifted_posSemidef_matrix_posDef hM hs).isUnit
  have hidentity := noncommutative_weighted_resolvent_second_order
    W F M (s • (1 : Matrix d d ℂ)) RF RM
    hW_normalized hW_centered hW_commutes
    (fun i => Matrix.mul_nonsing_inv _ (hdetF i))
    (fun i => Matrix.nonsing_inv_mul _ (hdetF i))
    (Matrix.mul_nonsing_inv _ hdetM)
    (Matrix.nonsing_inv_mul _ hdetM)
  simpa [W, RF, RM, smul_mul_assoc] using hidentity

theorem weighted_spectralPurificationFilter_variance_le_inverse_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef)
    {s : ℝ} (hs : 0 < s) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    (s •
      ((∑ i : ι, weight i •
        (F i + s • (1 : Matrix d d ℂ))⁻¹) -
        (M + s • (1 : Matrix d d ℂ))⁻¹) -
      ∑ i : ι, weight i •
        (star (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s) *
          (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s))).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  let RF : ι → Matrix d d ℂ := fun i =>
    (F i + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ :=
    (M + s • (1 : Matrix d d ℂ))⁻¹
  let D : ι → Matrix d d ℂ := fun i => F i - M
  let K : ι → Matrix d d ℂ := fun i =>
    s • RF i - s ^ 2 • (RF i * RF i)
  have hK (i : ι) : (K i).PosSemidef :=
    shifted_inverse_square_contraction (F i) (positive i) hs
  have hD (i : ι) : (D i).IsHermitian :=
    (positive i).isHermitian.sub hM.isHermitian
  have hinner :
      (∑ i : ι, weight i • (D i * K i * D i)).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro i _
    exact (posSemidef_hermitian_sandwich (hK i) (hD i)).smul
      (nonnegative i)
  have hRM : RM.IsHermitian :=
    (shifted_posSemidef_matrix_inverse_posSemidef hM hs).isHermitian
  have houter :
      (RM * (∑ i : ι, weight i • (D i * K i * D i)) * RM).PosSemidef :=
    posSemidef_hermitian_sandwich hinner hRM
  have hsecond :
      (∑ i : ι, weight i • RF i) - RM =
        RM * (∑ i : ι, weight i • (D i * RF i * D i)) * RM :=
    weighted_shifted_inverse_second_order
      weight F M normalized mean positive hM hs
  have hgram (i : ι) :
      star (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s) =
        s ^ 2 • (RM * D i * (RF i * RF i) * D i * RM) :=
    spectralPurificationFilter_sub_gram
      (F i) M (positive i) hM hs
  change
    (s • ((∑ i : ι, weight i • RF i) - RM) -
      ∑ i : ι, weight i •
        (star (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s) *
          (spectralPurificationFilter (F i) (positive i) s -
            spectralPurificationFilter M hM s))).PosSemidef
  rw [hsecond]
  simp_rw [hgram]
  convert houter using 1
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.smul_sum,
    mul_smul_comm, smul_mul_assoc,
    smul_smul, mul_sub, sub_mul, K]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_sub, smul_smul, smul_smul, mul_comm s (weight i)]
  simp only [mul_assoc]

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem scalarResolventFilter_memLp_two
    {z : ℝ} (hz : 0 ≤ z) :
    MemLp (fun s : ℝ => z / (z + s)) 2
      (volume.restrict (Ioi 0)) := by
  have hmeas :
      AEStronglyMeasurable (fun s : ℝ => z / (z + s))
        (volume.restrict (Ioi 0)) := by
    exact (measurable_const.div
      (measurable_const.add measurable_id)).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hmeas).mpr
    (scalar_resolvent_purification_integrable hz)

theorem spectralPurificationFilter_memLp_two
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    MemLp (spectralPurificationFilter F hF) 2
      (volume.restrict (Ioi 0)) := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  apply MemLp.of_eval
  intro i
  apply MemLp.of_eval
  intro j
  have hform :
      (fun s : ℝ => spectralPurificationFilter F hF s i j) =
        (fun s : ℝ => ∑ k : d,
          (U : Matrix d d ℂ) i k *
            ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ) *
            star (U : Matrix d d ℂ) k j) := by
    funext s
    change
      ((U : Matrix d d ℂ) *
        Matrix.diagonal (fun k =>
          ((eigenvalue k / (eigenvalue k + s) : ℝ) : ℂ)) *
        star (U : Matrix d d ℂ)) i j = _
    simp only [Matrix.diagonal, Complex.ofReal_div, Complex.ofReal_add, Matrix.mul_apply,
      Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Matrix.star_apply, RCLike.star_def]
  rw [hform]
  apply memLp_finsetSum Finset.univ
  intro k _
  exact ((scalarResolventFilter_memLp_two
    (hF.eigenvalues_nonneg k)).ofReal.const_mul
      ((U : Matrix d d ℂ) i k)).mul_const
        (star (U : Matrix d d ℂ) k j)

theorem matrix_memLp_two_mul_integrable
    {α d : Type*} [MeasurableSpace α]
    [Fintype d] {μ : Measure α}
    {f g : α → Matrix d d ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun t => f t * g t) μ := by
  classical
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  change Integrable (fun t => ∑ k : d, f t i k * g t k j) μ
  apply integrable_finsetSum Finset.univ
  intro k _
  exact ((hf.eval i).eval k).integrable_mul ((hg.eval k).eval j)

theorem spectralPurificationFilter_difference_gram_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F M : Matrix d d ℂ)
    (hF : F.PosSemidef) (hM : M.PosSemidef) :
    IntegrableOn
      (fun s : ℝ =>
        star (spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s))
      (Ioi 0) := by
  have hdelta :
      MemLp (fun s : ℝ =>
        spectralPurificationFilter F hF s -
          spectralPurificationFilter M hM s) 2
        (volume.restrict (Ioi 0)) :=
    (spectralPurificationFilter_memLp_two F hF).sub
      (spectralPurificationFilter_memLp_two M hM)
  exact matrix_memLp_two_mul_integrable hdelta.star hdelta

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem scalar_entropy_resolvent_integrable
    {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn
      (fun s : ℝ => z / (1 + s) - z / (z + s))
      (Ioi 0) := by
  have hone :
      MemLp (fun s : ℝ => 1 / (1 + s)) 2
        (volume.restrict (Ioi 0)) :=
    scalarResolventFilter_memLp_two (z := 1) (by norm_num)
  have hzfilter := scalarResolventFilter_memLp_two hz
  have hproduct :
      Integrable
        (fun s : ℝ =>
          (1 / (1 + s)) * (z / (z + s)))
        (volume.restrict (Ioi 0)) :=
    hone.integrable_mul hzfilter
  have hscaled :
      IntegrableOn
        (fun s : ℝ =>
          (z - 1) * ((1 / (1 + s)) * (z / (z + s))))
        (Ioi 0) := hproduct.const_mul (z - 1)
  refine hscaled.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hspos : 0 < s := hs
  have hzone : 1 + s ≠ 0 := ne_of_gt (by linarith)
  have hzden : z + s ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

private def spectralEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i =>
      ((hF.isHermitian.eigenvalues i / (1 + s) -
        hF.isHermitian.eigenvalues i /
          (hF.isHermitian.eigenvalues i + s) : ℝ) : ℂ))

theorem spectralEntropyKernel_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    IntegrableOn (spectralEntropyKernel F hF) (Ioi 0) := by
  classical
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag :
      IntegrableOn
        (fun s : ℝ => Matrix.diagonal fun i : d =>
          ((eigenvalue i / (1 + s) -
            eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
        (Ioi 0) := by
    apply Integrable.of_eval
    intro i
    apply Integrable.of_eval
    intro j
    by_cases hij : i = j
    · subst j
      have heigenvalue : 0 ≤ eigenvalue i :=
        hF.eigenvalues_nonneg i
      have hcomplex :
          Integrable
            (fun s : ℝ =>
              ((eigenvalue i / (1 + s) -
                eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
            (volume.restrict (Ioi 0)) :=
        MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
          (scalar_entropy_resolvent_integrable heigenvalue)
      simpa only [Matrix.diagonal_apply_eq] using hcomplex
    · simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
        ne_eq, hij, not_false_eq_true, Matrix.diagonal_apply_ne, integrable_fun_zero]
  exact
    (spectralConjugationCLM hF.isHermitian.eigenvectorUnitary).integrable_comp
      hdiag

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectralEntropyKernel_eq_scalar_sub_filter
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (s : ℝ) :
    spectralEntropyKernel F hF s =
      (1 / (1 + s) : ℝ) • F -
        spectralPurificationFilter F hF s := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  let L := spectralConjugationCLM U
  let D : Matrix d d ℂ :=
    Matrix.diagonal fun i => (eigenvalue i : ℂ)
  let G : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  let K : Matrix d d ℂ := Matrix.diagonal fun i =>
    ((eigenvalue i / (1 + s) -
      eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)
  have hFspec : F = L D := by
    simpa [L, U, D, eigenvalue, Function.comp_def,
      Unitary.conjStarAlgAut_apply] using
      hF.isHermitian.spectral_theorem
  have hdiag : K = (1 / (1 + s) : ℝ) • D - G := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [div_eq_mul_inv, mul_comm, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one, Matrix.diagonal_apply_eq,
        one_mul, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul, K, D, G]
    · simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
        ne_eq, hij, not_false_eq_true, Matrix.diagonal_apply_ne, one_div, Matrix.sub_apply,
        Matrix.smul_apply, smul_zero, sub_self, K, D, G]
  change L K = (1 / (1 + s) : ℝ) • F - L G
  rw [hFspec, ← L.map_smul, ← L.map_sub, hdiag]

/--
The weighted spectral filter variance construction used in the quantum parallel-repetition
argument.
-/
def weightedSpectralFilterVariance
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  ∑ i : ι, weight i •
    (star (spectralPurificationFilter (F i) (positive i) s -
        spectralPurificationFilter M hM s) *
      (spectralPurificationFilter (F i) (positive i) s -
        spectralPurificationFilter M hM s))

private def weightedSpectralEntropyJensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) (s : ℝ) : Matrix d d ℂ :=
  (∑ i : ι, weight i • spectralEntropyKernel (F i) (positive i) s) -
    spectralEntropyKernel M hM s

theorem weightedSpectralFilterVariance_integrable
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    IntegrableOn
      (weightedSpectralFilterVariance weight F M positive hM)
      (Ioi 0) := by
  unfold weightedSpectralFilterVariance
  refine integrable_finsetSum (α := ℝ) (ε' := Matrix d d ℂ)
    (f := fun i s => weight i •
      (star (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s))) Finset.univ ?_
  intro i _
  have hintegrable : IntegrableOn
      (fun s : ℝ =>
        star (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s) *
        (spectralPurificationFilter (F i) (positive i) s -
          spectralPurificationFilter M hM s)) (Ioi 0) :=
    spectralPurificationFilter_difference_gram_integrable
      (F i) M (positive i) hM
  have hscaled := MeasureTheory.Integrable.smul
    (α := ℝ) (β := Matrix d d ℂ) (𝕜 := ℝ) (weight i) hintegrable
  apply Integrable.of_eval
  intro j
  apply Integrable.of_eval
  intro k
  simpa only [Pi.smul_apply] using (hscaled.eval j).eval k

theorem weightedSpectralEntropyJensen_integrable
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    IntegrableOn
      (weightedSpectralEntropyJensen weight F M positive hM)
      (Ioi 0) := by
  unfold weightedSpectralEntropyJensen
  apply Integrable.sub
  · apply integrable_finsetSum Finset.univ
    intro i _
    exact (spectralEntropyKernel_integrable
      (F i) (positive i)).smul (weight i)
  · exact spectralEntropyKernel_integrable M hM

theorem weightedSpectralEntropyJensen_eq_shifted_inverse
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    {s : ℝ} (hs : 0 < s) :
    weightedSpectralEntropyJensen weight F M positive hM s =
      s •
        ((∑ i : ι, weight i •
          (F i + s • (1 : Matrix d d ℂ))⁻¹) -
          (M + s • (1 : Matrix d d ℂ))⁻¹) := by
  classical
  let c : ℝ := 1 / (1 + s)
  let RF : ι → Matrix d d ℂ := fun i =>
    (F i + s • (1 : Matrix d d ℂ))⁻¹
  let RM : Matrix d d ℂ :=
    (M + s • (1 : Matrix d d ℂ))⁻¹
  have hscalar :
      (∑ i : ι, weight i • (c • F i)) = c • M := by
    calc
      (∑ i : ι, weight i • (c • F i)) =
          ∑ i : ι, c • (weight i • F i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [smul_smul, mul_comm]
      _ = c • (∑ i : ι, weight i • F i) := by
            rw [Finset.smul_sum]
      _ = c • M := by rw [mean]
  have hscale :
      (∑ i : ι, weight i • (s • RF i)) =
        s • (∑ i : ι, weight i • RF i) := by
    calc
      (∑ i : ι, weight i • (s • RF i)) =
          ∑ i : ι, s • (weight i • RF i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [smul_smul, mul_comm]
      _ = s • (∑ i : ι, weight i • RF i) := by
            rw [Finset.smul_sum]
  have hfilter_sum :
      (∑ i : ι, weight i •
        spectralPurificationFilter (F i) (positive i) s) =
      1 - s • (∑ i : ι, weight i • RF i) := by
    calc
      (∑ i : ι, weight i •
          spectralPurificationFilter (F i) (positive i) s) =
          ∑ i : ι, weight i • (1 - s • RF i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [spectralPurificationFilter_eq_one_sub_shifted_inverse
              (F i) (positive i) hs]
      _ = 1 - s • (∑ i : ι, weight i • RF i) := by
            simp_rw [smul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_smul,
              normalized, hscale]
            simp only [one_smul]
  unfold weightedSpectralEntropyJensen
  simp_rw [spectralEntropyKernel_eq_scalar_sub_filter]
  change
    (∑ i : ι, weight i •
      (c • F i - spectralPurificationFilter (F i) (positive i) s)) -
      (c • M - spectralPurificationFilter M hM s) =
    s • ((∑ i : ι, weight i • RF i) - RM)
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, hscalar, hfilter_sum,
    spectralPurificationFilter_eq_one_sub_shifted_inverse M hM hs]
  module

theorem integrated_weighted_spectralPurificationFilter_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    ((∫ s in Ioi (0 : ℝ),
        weightedSpectralEntropyJensen weight F M positive hM s) -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have hentropy := weightedSpectralEntropyJensen_integrable
    weight F M positive hM
  have hvariance := weightedSpectralFilterVariance_integrable
    weight F M positive hM
  have hremainder :
      Integrable
        (fun s : ℝ =>
          weightedSpectralEntropyJensen weight F M positive hM s -
            weightedSpectralFilterVariance weight F M positive hM s)
        (volume.restrict (Ioi 0)) :=
    hentropy.sub hvariance
  have hpointwise :
      ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        (weightedSpectralEntropyJensen weight F M positive hM s -
          weightedSpectralFilterVariance weight F M positive hM s).PosSemidef := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : 0 < s := hs
    rw [weightedSpectralEntropyJensen_eq_shifted_inverse
      weight F M positive hM normalized mean hspos]
    unfold weightedSpectralFilterVariance
    exact weighted_spectralPurificationFilter_variance_le_inverse_jensen
      weight F M nonnegative normalized mean positive hspos
  have hintegral := bochner_integral_posSemidef hremainder hpointwise
  rw [integral_sub hentropy hvariance] at hintegral
  exact hintegral

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem scalar_entropy_resolvent_integral
    {z : ℝ} (hz : 0 ≤ z) :
    (∫ s in Ioi (0 : ℝ),
      (z / (1 + s) - z / (z + s))) = z * Real.log z := by
  rcases hz.eq_or_lt with rfl | hzpos
  · simp only [zero_div, zero_add, sub_self, integral_zero, Real.log_zero, mul_zero]
  · have hderiv :
        ∀ x ∈ Ici (0 : ℝ),
          HasDerivAt
            (fun t : ℝ => z * Real.log ((1 + t) / (z + t)))
            (z / (1 + x) - z / (z + x)) x := by
      intro x hx
      have hxnonneg : 0 ≤ x := hx
      have hnum : 1 + x ≠ 0 := ne_of_gt (by linarith)
      have hden : z + x ≠ 0 := ne_of_gt (by linarith)
      have hratio : (1 + x) / (z + x) ≠ 0 :=
        div_ne_zero hnum hden
      have hdnum :=
        (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
      have hdden :=
        (hasDerivAt_const x z).add (hasDerivAt_id x)
      have hd :
          HasDerivAt
            (fun t : ℝ => z * Real.log ((1 + t) / (z + t)))
            (z * (((z + x) - (1 + x)) / (z + x) ^ 2 /
              ((1 + x) / (z + x)))) x := by
        simpa only [add_sub_add_right_eq_sub, Pi.div_apply, Pi.add_apply, id_eq, zero_add,
          one_mul, mul_one] using
          ((hdnum.div hdden hden).log hratio).const_mul z
      apply hd.congr_deriv
      field_simp [hnum, hden]
    have hden_top : Tendsto (fun t : ℝ => z + t) atTop atTop := by
      simpa only [id_eq, add_comm] using
        tendsto_atTop_add_const_right atTop z tendsto_id
    have hzero :
        Tendsto (fun t : ℝ => (1 - z) / (z + t))
          atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop hden_top
    have hratio_limit :
        Tendsto (fun t : ℝ => (1 + t) / (z + t))
          atTop (𝓝 (1 : ℝ)) := by
      have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
          atTop (𝓝 (1 : ℝ)) := tendsto_const_nhds
      have h' :
          Tendsto (fun t : ℝ => 1 + (1 - z) / (z + t))
            atTop (𝓝 (1 : ℝ)) := by
        simpa only [add_zero] using hone.add hzero
      apply h'.congr'
      filter_upwards [eventually_gt_atTop (-z)] with t ht
      have hden : z + t ≠ 0 := ne_of_gt (by linarith)
      field_simp
      ring
    have hlog_limit :
        Tendsto (fun t : ℝ =>
          Real.log ((1 + t) / (z + t)))
          atTop (𝓝 (0 : ℝ)) := by
      have hlog :
          Tendsto
            (Real.log ∘ (fun t : ℝ => (1 + t) / (z + t)))
            atTop (𝓝 (Real.log (1 : ℝ))) :=
        (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
          hratio_limit
      change
        Tendsto (fun t : ℝ => Real.log ((1 + t) / (z + t)))
          atTop (𝓝 (Real.log (1 : ℝ))) at hlog
      simpa only [Real.log_one] using hlog
    have hlimit :
        Tendsto (fun t : ℝ =>
          z * Real.log ((1 + t) / (z + t)))
          atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlog_limit
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
      hderiv (scalar_entropy_resolvent_integrable hzpos.le) hlimit
    calc
      (∫ s in Ioi (0 : ℝ),
        (z / (1 + s) - z / (z + s))) =
          0 - z * Real.log ((1 + 0) / (z + 0)) := hftc
      _ = z * Real.log z := by
        simp only [add_zero, one_div, Real.log_inv, mul_neg, sub_neg_eq_add, zero_add]

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private def diagonalEntropyKernel
    {d : Type*} [DecidableEq d]
    (eigenvalue : d → ℝ) (s : ℝ) : Matrix d d ℂ :=
  Matrix.diagonal fun i =>
    ((eigenvalue i / (1 + s) -
      eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)

theorem diagonalEntropyKernel_integrable
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (nonnegative : ∀ i, 0 ≤ eigenvalue i) :
    IntegrableOn (diagonalEntropyKernel eigenvalue) (Ioi 0) := by
  classical
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  by_cases hij : i = j
  · subst j
    have hcomplex :
        Integrable
          (fun s : ℝ =>
            ((eigenvalue i / (1 + s) -
              eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ))
          (volume.restrict (Ioi 0)) :=
      MeasureTheory.Integrable.ofReal (𝕜 := ℂ)
        (scalar_entropy_resolvent_integrable (nonnegative i))
    simpa only [diagonalEntropyKernel,
      Matrix.diagonal_apply_eq] using hcomplex
  · simp only [diagonalEntropyKernel, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_one, ne_eq, hij, not_false_eq_true, Matrix.diagonal_apply_ne,
      integrable_fun_zero]

theorem integral_diagonalEntropyKernel
    {d : Type*} [Fintype d] [DecidableEq d]
    (eigenvalue : d → ℝ)
    (nonnegative : ∀ i, 0 ≤ eigenvalue i) :
    (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s) =
      Matrix.diagonal fun i =>
        ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ) := by
  classical
  have hmatrix := diagonalEntropyKernel_integrable
    eigenvalue nonnegative
  have hrows :
      ∀ i : d,
        Integrable
          (fun s : ℝ => diagonalEntropyKernel eigenvalue s i)
          (volume.restrict (Ioi 0)) :=
    fun i => hmatrix.eval i
  have hentry (i : d) :
      ∀ j : d,
        Integrable
          (fun s : ℝ => diagonalEntropyKernel eigenvalue s i j)
          (volume.restrict (Ioi 0)) :=
    fun j => (hrows i).eval j
  ext i j
  rw [show
    (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s) i j =
      (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s i) j from
        congrArg (fun row : d → ℂ => row j)
          (MeasureTheory.eval_integral hrows i)]
  rw [show
    (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s i) j =
      ∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s i j from
        MeasureTheory.eval_integral (hentry i) j]
  by_cases hij : i = j
  · subst j
    simp only [diagonalEntropyKernel, Matrix.diagonal_apply_eq]
    calc
      (∫ s in Ioi (0 : ℝ),
        ((eigenvalue i / (1 + s) -
          eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ)) =
          ((∫ s in Ioi (0 : ℝ),
            eigenvalue i / (1 + s) -
              eigenvalue i / (eigenvalue i + s) : ℝ) : ℂ) :=
            integral_ofReal
      _ = ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ) := by
            rw [scalar_entropy_resolvent_integral (nonnegative i)]
  · simp only [diagonalEntropyKernel, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_one, ne_eq, hij, not_false_eq_true, Matrix.diagonal_apply_ne, integral_zero,
      Complex.ofReal_mul]

theorem integral_spectralEntropyKernel_eq_cfc
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∫ s in Ioi (0 : ℝ), spectralEntropyKernel F hF s) =
      cfc (fun z : ℝ => z * Real.log z) F := by
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag := diagonalEntropyKernel_integrable
    eigenvalue (fun i => hF.eigenvalues_nonneg i)
  calc
    (∫ s in Ioi (0 : ℝ), spectralEntropyKernel F hF s) =
        spectralConjugationCLM U
          (∫ s in Ioi (0 : ℝ), diagonalEntropyKernel eigenvalue s) := by
            exact ContinuousLinearMap.integral_comp_comm
              (spectralConjugationCLM U) hdiag
    _ = spectralConjugationCLM U
          (Matrix.diagonal fun i =>
            ((eigenvalue i * Real.log (eigenvalue i) : ℝ) : ℂ)) := by
            rw [integral_diagonalEntropyKernel eigenvalue
              (fun i => hF.eigenvalues_nonneg i)]
    _ = cfc (fun z : ℝ => z * Real.log z) F := by
          rw [hF.isHermitian.cfc_eq]
          rfl

end

section

open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem weightedSpectralEntropy_term_integrable
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef) (i : ι) :
    Integrable
      (fun s : ℝ => weight i •
        spectralEntropyKernel (F i) (positive i) s)
      (volume.restrict (Ioi 0)) :=
  (spectralEntropyKernel_integrable (F i) (positive i)).smul (weight i)

private theorem integral_weightedSpectralEntropy_term_eq_cfc
    {ι d : Type*} [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef) (i : ι) :
    (∫ s in Ioi (0 : ℝ),
      weight i • spectralEntropyKernel (F i) (positive i) s) =
      weight i • cfc (fun z : ℝ => z * Real.log z) (F i) := by
  rw [integral_smul, integral_spectralEntropyKernel_eq_cfc]

private theorem weightedSpectralEntropy_sum_integrable
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef) :
    Integrable
      (fun s : ℝ => ∑ i : ι,
        weight i • spectralEntropyKernel (F i) (positive i) s)
      (volume.restrict (Ioi 0)) :=
  integrable_finsetSum Finset.univ fun i _ =>
    weightedSpectralEntropy_term_integrable weight F positive i

private theorem integral_weightedSpectralEntropy_sum_eq_cfc
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef) :
    (∫ s in Ioi (0 : ℝ),
      ∑ i : ι, weight i • spectralEntropyKernel (F i) (positive i) s) =
      ∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i) := by
  have hterm := weightedSpectralEntropy_term_integrable weight F positive
  rw [integral_finsetSum Finset.univ (fun i _ => hterm i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_weightedSpectralEntropy_term_eq_cfc weight F positive i

theorem integral_weightedSpectralEntropyJensen_eq_cfc
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (positive : ∀ i, (F i).PosSemidef)
    (hM : M.PosSemidef) :
    (∫ s in Ioi (0 : ℝ),
      weightedSpectralEntropyJensen weight F M positive hM s) =
      (∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
        cfc (fun z : ℝ => z * Real.log z) M := by
  change (∫ s in Ioi (0 : ℝ),
      (∑ i : ι, weight i • spectralEntropyKernel (F i) (positive i) s) -
        spectralEntropyKernel M hM s) = _
  calc
    _ = (∫ s in Ioi (0 : ℝ), ∑ i : ι,
          weight i • spectralEntropyKernel (F i) (positive i) s) -
        ∫ s in Ioi (0 : ℝ), spectralEntropyKernel M hM s :=
      integral_sub (weightedSpectralEntropy_sum_integrable weight F positive)
        (spectralEntropyKernel_integrable M hM)
    _ = (∑ i : ι, weight i •
          cfc (fun z : ℝ => z * Real.log z) (F i)) -
        ∫ s in Ioi (0 : ℝ), spectralEntropyKernel M hM s :=
      congrArg (· - ∫ s in Ioi (0 : ℝ), spectralEntropyKernel M hM s)
        (integral_weightedSpectralEntropy_sum_eq_cfc weight F positive)
    _ = _ := congrArg ((∑ i : ι, weight i •
          cfc (fun z : ℝ => z * Real.log z) (F i)) - ·)
      (integral_spectralEntropyKernel_eq_cfc M hM)

theorem exact_matrix_log_entropy_filter_jensen
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (weight : ι → ℝ) (F : ι → Matrix d d ℂ)
    (M : Matrix d d ℂ)
    (nonnegative : ∀ i, 0 ≤ weight i)
    (normalized : (∑ i : ι, weight i) = 1)
    (mean : (∑ i : ι, weight i • F i) = M)
    (positive : ∀ i, (F i).PosSemidef) :
    let hM : M.PosSemidef := by
      rw [← mean]
      exact weighted_positive_matrix_mean weight F nonnegative positive
    ((∑ i : ι, weight i •
        cfc (fun z : ℝ => z * Real.log z) (F i)) -
      cfc (fun z : ℝ => z * Real.log z) M -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef := by
  dsimp
  let hM : M.PosSemidef := by
    rw [← mean]
    exact weighted_positive_matrix_mean weight F nonnegative positive
  have h := integrated_weighted_spectralPurificationFilter_jensen
    weight F M nonnegative normalized mean positive
  change
    ((∫ s in Ioi (0 : ℝ),
        weightedSpectralEntropyJensen weight F M positive hM s) -
      (∫ s in Ioi (0 : ℝ),
        weightedSpectralFilterVariance weight F M positive hM s)).PosSemidef at h
  rw [integral_weightedSpectralEntropyJensen_eq_cfc
    weight F M positive hM] at h
  exact h

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder


section HistoryContractions

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem Game.conditionalYGivenX_sum_le_one
    (G : Game X Y A B) (x : X) :
    (∑ y : Y, G.conditionalYGivenX x y) ≤ 1 := by
  by_cases hx : G.marginalX x = 0
  · simp only [conditionalYGivenX, hx, div_zero, Finset.sum_const_zero, zero_le_one]
  · have hpos : 0 < G.marginalX x :=
      lt_of_le_of_ne (G.marginalX_nonneg x) (Ne.symm hx)
    rw [G.conditionalYGivenX_sum x hpos]

theorem Game.conditionalXGivenY_sum_le_one
    (G : Game X Y A B) (y : Y) :
    (∑ x : X, G.conditionalXGivenY y x) ≤ 1 := by
  by_cases hy : G.marginalY y = 0
  · simp only [conditionalXGivenY, hy, div_zero, Finset.sum_const_zero, zero_le_one]
  · have hpos : 0 < G.marginalY y :=
      lt_of_le_of_ne (G.marginalY_nonneg y) (Ne.symm hy)
    rw [G.conditionalXGivenY_sum y hpos]

theorem fullHistoryHiddenAliceWeight_sum_le_one
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) :
    (∑ hidden : {i : Fin n // i ∈ fullHistoryRemaining n D L} → X,
      fullHistoryHiddenAliceWeight G h hidden) ≤ 1 := by
  unfold fullHistoryHiddenAliceWeight
  rw [← Fintype.prod_sum]
  apply Finset.prod_le_one
  · intro i _
    exact Finset.sum_nonneg fun x _ =>
      G.conditionalXGivenY_nonneg (h.bobRemaining i) x
  · intro i _
    exact G.conditionalXGivenY_sum_le_one (h.bobRemaining i)

theorem fullHistoryHiddenBobWeight_sum_le_one
    (G : Game X Y A B) {n : ℕ}
    {D L : Finset (Fin n)}
    (h : FullSubsetHistory X Y n D L) :
    (∑ hidden : {i : Fin n // i ∈ L} → Y,
      fullHistoryHiddenBobWeight G h hidden) ≤ 1 := by
  unfold fullHistoryHiddenBobWeight
  rw [← Fintype.prod_sum]
  apply Finset.prod_le_one
  · intro i _
    exact Finset.sum_nonneg fun y _ =>
      G.conditionalYGivenX_nonneg (h.aliceRevealed i) y
  · intro i _
    exact G.conditionalYGivenX_sum_le_one (h.aliceRevealed i)

theorem fullHistoryAliceFilter_complement_posSemidef
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (α : {i : Fin n // i ∈ D} → A) :
    (1 - fullHistoryAliceFilter G n S D L h α).PosSemidef := by
  classical
  let w : ({i : Fin n // i ∈ fullHistoryRemaining n D L} → X) → ℝ :=
    fullHistoryHiddenAliceWeight G h
  let E : ({i : Fin n // i ∈ fullHistoryRemaining n D L} → X) →
      Matrix S.Alice S.Alice ℂ := fun x =>
    conditionedAliceEffect G n S D α (fullHistoryAliceQuestion h x)
  have hsum : (∑ x, w x) ≤ 1 :=
    fullHistoryHiddenAliceWeight_sum_le_one G h
  have hsplit :
      1 - (∑ x, w x • E x) =
        (1 - (∑ x, w x)) • (1 : Matrix S.Alice S.Alice ℂ) +
          ∑ x, w x • (1 - E x) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    module
  change (1 - ∑ x, w x • E x).PosSemidef
  rw [hsplit]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hsum)
  · apply Matrix.posSemidef_sum Finset.univ
    intro x _
    exact (conditionedAliceEffect_complement_positive G n S D α
      (fullHistoryAliceQuestion h x)).smul
        (fullHistoryHiddenAliceWeight_nonneg G h x)

theorem fullHistoryBobFilter_complement_posSemidef
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n))
    (h : FullSubsetHistory X Y n D L)
    (β : {i : Fin n // i ∈ D} → B) :
    (1 - fullHistoryBobFilter G n S D L h β).PosSemidef := by
  classical
  let w : ({i : Fin n // i ∈ L} → Y) → ℝ :=
    fullHistoryHiddenBobWeight G h
  let E : ({i : Fin n // i ∈ L} → Y) → Matrix S.Bob S.Bob ℂ :=
    fun y => conditionedBobEffect G n S D β (fullHistoryBobQuestion h y)
  have hsum : (∑ y, w y) ≤ 1 :=
    fullHistoryHiddenBobWeight_sum_le_one G h
  have hsplit :
      1 - (∑ y, w y • E y) =
        (1 - (∑ y, w y)) • (1 : Matrix S.Bob S.Bob ℂ) +
          ∑ y, w y • (1 - E y) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    module
  change (1 - ∑ y, w y • E y).PosSemidef
  rw [hsplit]
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hsum)
  · apply Matrix.posSemidef_sum Finset.univ
    intro y _
    exact (conditionedBobEffect_complement_positive G n S D β
      (fullHistoryBobQuestion h y)).smul
        (fullHistoryHiddenBobWeight_nonneg G h y)

theorem matrixLogEntropy_nonpos_of_contraction
    {d : Type*} [Fintype d] [DecidableEq d]
    {F : Matrix d d ℂ}
    (hF : F.PosSemidef)
    (hcomplement : (1 - F).PosSemidef) :
    (-(cfc (fun z : ℝ => z * Real.log z) F)).PosSemidef := by
  have hFle : F ≤ (1 : Matrix d d ℂ) :=
    Matrix.le_iff.mpr hcomplement
  have hupper : ∀ z ∈ spectrum ℝ F, z ≤ 1 :=
    (CFC.le_one_iff (R := ℝ) F hF.isHermitian).mp hFle
  have hlower : ∀ z ∈ spectrum ℝ F, 0 ≤ z := by
    intro z hz
    rw [hF.isHermitian.spectrum_real_eq_range_eigenvalues] at hz
    obtain ⟨i, rfl⟩ := hz
    exact hF.eigenvalues_nonneg i
  have hnonpos : cfc (fun z : ℝ => z * Real.log z) F ≤
      (0 : Matrix d d ℂ) := by
    apply cfc_nonpos
    intro z hz
    exact Real.mul_log_nonpos (hlower z hz) (hupper z hz)
  simpa only [zero_sub] using Matrix.le_iff.mp hnonpos

theorem matrixLogEntropy_born_nonpos_left
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ)
    (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (hG : G.PosSemidef) :
    bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G ≤ 0 := by
  have hneg := matrixLogEntropy_nonpos_of_contraction hF hFcomplement
  have hpair : 0 ≤ bornTracePairing ρ.matrix
      (-(cfc (fun z : ℝ => z * Real.log z) F)) G := by
    exact trace_mul_posSemidef_nonneg ρ.positive (hneg.kronecker hG)
  have hrewrite : bornTracePairing ρ.matrix
      (-(cfc (fun z : ℝ => z * Real.log z) F)) G =
      -bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G := by
    simp only [map_neg, LinearMap.neg_apply]
  rw [hrewrite] at hpair
  exact neg_nonneg.mp hpair

theorem matrixLogEntropy_born_nonpos_right
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ)
    (G : Matrix dB dB ℂ)
    (hF : F.PosSemidef)
    (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) ≤ 0 := by
  have hneg := matrixLogEntropy_nonpos_of_contraction hG hGcomplement
  have hpair : 0 ≤ bornTracePairing ρ.matrix F
      (-(cfc (fun z : ℝ => z * Real.log z) G)) := by
    exact trace_mul_posSemidef_nonneg ρ.positive (hF.kronecker hneg)
  have hrewrite : bornTracePairing ρ.matrix F
      (-(cfc (fun z : ℝ => z * Real.log z) G)) =
      -bornTracePairing ρ.matrix F
        (cfc (fun z : ℝ => z * Real.log z) G) :=
    (bornTracePairing ρ.matrix F).map_neg _
  rw [hrewrite] at hpair
  exact neg_nonneg.mp hpair

/-- The potential function controlling full history alice entropy. -/
def fullHistoryAliceEntropyPotential
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) : ℝ :=
  ∑ h : FullSubsetHistory X Y n D L,
    ∑ α : {i : Fin n // i ∈ D} → A,
    ∑ β : {i : Fin n // i ∈ D} → B,
      fullHistoryWeight G h * fullHistoryWinIndicator G h α β *
        bornTracePairing S.state.matrix
          (cfc (fun z : ℝ => z * Real.log z)
            (fullHistoryAliceFilter G n S D L h α))
          (fullHistoryBobFilter G n S D L h β)

theorem fullHistoryAliceEntropyPotential_nonpos
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    (D L : Finset (Fin n)) :
    fullHistoryAliceEntropyPotential G n S D L ≤ 0 := by
  unfold fullHistoryAliceEntropyPotential
  apply Finset.sum_nonpos
  intro h _
  apply Finset.sum_nonpos
  intro α _
  apply Finset.sum_nonpos
  intro β _
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (fullHistoryWeight_nonneg G h)
      (fullHistoryWinIndicator_nonneg G h α β)
  · exact matrixLogEntropy_born_nonpos_left S.state
      (fullHistoryAliceFilter G n S D L h α)
      (fullHistoryBobFilter G n S D L h β)
      (fullHistoryAliceFilter_posSemidef G n S D L h α)
      (fullHistoryAliceFilter_complement_posSemidef G n S D L h α)
      (fullHistoryBobFilter_posSemidef G n S D L h β)

end HistoryContractions

/-- The finite atom representing positive matrix spectral. -/
def positiveMatrixSpectralAtom
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i : d) :
    Matrix d d ℂ :=
  spectralConjugationCLM hF.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i (1 : ℂ)))

theorem positiveMatrixSpectralAtom_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) (i : d) :
    (positiveMatrixSpectralAtom F hF i).PosSemidef := by
  classical
  have hdiag :
      (Matrix.diagonal (Pi.single i (1 : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro j
    by_cases hij : i = j
    · subst j
      simp only [Pi.zero_apply, Pi.single_eq_same, zero_le_one]
    · simp only [Pi.zero_apply, ne_eq, hij, not_false_eq_true, Pi.single_eq_of_ne', Std.le_refl]
  unfold positiveMatrixSpectralAtom
  rw [spectralConjugationCLM_apply]
  simpa only [star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same
      (hF.isHermitian.eigenvectorUnitary : Matrix d d ℂ)

theorem positiveMatrixSpectralAtom_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef) :
    (∑ i : d, positiveMatrixSpectralAtom F hF i) = 1 := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  have hdiag :
      (∑ i : d, Matrix.diagonal (Pi.single i (1 : ℂ))) =
        (1 : Matrix d d ℂ) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp only [Matrix.sum_apply, diagonal_apply_eq, Pi.single_apply, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte, one_apply_eq]
    · simp only [Matrix.sum_apply, ne_eq, hjk, not_false_eq_true, diagonal_apply_ne,
        Finset.sum_const_zero, one_apply_ne]
  change
    (∑ i : d,
      spectralConjugationCLM U
        (Matrix.diagonal (Pi.single i (1 : ℂ)))) = 1
  rw [← map_sum, hdiag]
  simp only [spectralConjugationCLM_apply, mul_one, SetLike.coe_mem, Unitary.mul_star_self_of_mem]

theorem positiveMatrix_cfc_spectral_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (f : ℝ → ℝ) :
    cfc f F =
      ∑ i : d,
        f (hF.isHermitian.eigenvalues i) •
          positiveMatrixSpectralAtom F hF i := by
  classical
  let U := hF.isHermitian.eigenvectorUnitary
  let eigenvalue := hF.isHermitian.eigenvalues
  have hdiag :
      (∑ i : d,
        f (eigenvalue i) •
          Matrix.diagonal (Pi.single i (1 : ℂ))) =
        Matrix.diagonal fun i => (f (eigenvalue i) : ℂ) := by
    ext j k
    by_cases hjk : j = k
    · subst k
      simp only [Matrix.sum_apply, Matrix.smul_apply, diagonal_apply_eq, Pi.single_apply,
        smul_ite, Complex.real_smul, mul_one, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte]
    · simp only [Matrix.sum_apply, Matrix.smul_apply, ne_eq, hjk, not_false_eq_true,
        diagonal_apply_ne, smul_zero, Finset.sum_const_zero]
  calc
    cfc f F =
        spectralConjugationCLM U
          (Matrix.diagonal fun i => (f (eigenvalue i) : ℂ)) := by
      rw [hF.isHermitian.cfc_eq]
      rfl
    _ = spectralConjugationCLM U
          (∑ i : d,
            f (eigenvalue i) •
              Matrix.diagonal (Pi.single i (1 : ℂ))) := by
      rw [hdiag]
    _ = ∑ i : d,
        f (eigenvalue i) •
          positiveMatrixSpectralAtom F hF i := by
      simp only [map_sum, map_smul, spectralConjugationCLM_apply, positiveMatrixSpectralAtom, U,
        eigenvalue]

private def leftSpectralBornWeight
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ)
    (i : dA) : ℝ :=
  bornTracePairing ρ.matrix
    (positiveMatrixSpectralAtom F hF i) G

theorem leftSpectralBornWeight_nonneg
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (i : dA) :
    0 ≤ leftSpectralBornWeight ρ F hF G i := by
  exact trace_mul_posSemidef_nonneg ρ.positive
    ((positiveMatrixSpectralAtom_posSemidef F hF i).kronecker hG)

theorem leftSpectralBornWeight_sum
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) :
    (∑ i : dA, leftSpectralBornWeight ρ F hF G i) =
      bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G := by
  unfold leftSpectralBornWeight
  calc
    (∑ i : dA,
      bornTracePairing ρ.matrix
        (positiveMatrixSpectralAtom F hF i) G) =
      bornTracePairing ρ.matrix
        (∑ i : dA, positiveMatrixSpectralAtom F hF i) G := by
          simp only [map_sum, LinearMap.sum_apply]
    _ = bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G := by
      rw [positiveMatrixSpectralAtom_sum]

theorem leftSpectralBornWeight_moment
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) :
    (∑ i : dA,
      leftSpectralBornWeight ρ F hF G i *
        hF.isHermitian.eigenvalues i) =
      bornTracePairing ρ.matrix F G := by
  have hspectral : F =
      ∑ i : dA,
        hF.isHermitian.eigenvalues i •
          positiveMatrixSpectralAtom F hF i := by
    calc
      F = cfc (fun z : ℝ => z) F :=
        (cfc_id' ℝ F hF.isHermitian).symm
      _ = _ := positiveMatrix_cfc_spectral_sum F hF (fun z : ℝ => z)
  have h := congrArg
    (fun H : Matrix dA dA ℂ => bornTracePairing ρ.matrix H G)
      hspectral
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul] at h
  calc
    (∑ i : dA,
      leftSpectralBornWeight ρ F hF G i *
        hF.isHermitian.eigenvalues i) =
      ∑ i : dA,
        hF.isHermitian.eigenvalues i *
          bornTracePairing ρ.matrix
            (positiveMatrixSpectralAtom F hF i) G := by
        apply Finset.sum_congr rfl
        intro i _
        unfold leftSpectralBornWeight
        ring
    _ = bornTracePairing ρ.matrix F G := h.symm

theorem leftSpectralBornWeight_entropy
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) :
    bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G =
      ∑ i : dA,
        leftSpectralBornWeight ρ F hF G i *
          (hF.isHermitian.eigenvalues i *
            Real.log (hF.isHermitian.eigenvalues i)) := by
  have hspectral := positiveMatrix_cfc_spectral_sum F hF
    (fun z : ℝ => z * Real.log z)
  have h := congrArg
    (fun H : Matrix dA dA ℂ => bornTracePairing ρ.matrix H G)
      hspectral
  simp only [map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul] at h
  calc
    bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G =
      ∑ i : dA,
        (hF.isHermitian.eigenvalues i *
          Real.log (hF.isHermitian.eigenvalues i)) *
          bornTracePairing ρ.matrix
            (positiveMatrixSpectralAtom F hF i) G := h
    _ = ∑ i : dA,
      leftSpectralBornWeight ρ F hF G i *
        (hF.isHermitian.eigenvalues i *
          Real.log (hF.isHermitian.eigenvalues i)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold leftSpectralBornWeight
      ring

theorem bornTracePairing_one_one
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB)) :
    bornTracePairing ρ.matrix
      (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) = 1 := by
  simp only [bornTracePairing, LinearMap.coe_mk, AddHom.coe_mk, zero_mul, implies_true, mul_zero,
    mul_one, kroneckerMap_one_one, ρ.trace_one, Complex.one_re]

theorem bornTracePairing_one_le_one
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (G : Matrix dB dB ℂ)
    (hGcomplement : (1 - G).PosSemidef) :
    bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G ≤ 1 := by
  have hpositive : 0 ≤ bornTracePairing ρ.matrix
      (1 : Matrix dA dA ℂ) (1 - G) :=
    trace_mul_posSemidef_nonneg ρ.positive
      (Matrix.PosSemidef.one.kronecker hGcomplement)
  have hdiff : bornTracePairing ρ.matrix
      (1 : Matrix dA dA ℂ) (1 - G) =
      bornTracePairing ρ.matrix
        (1 : Matrix dA dA ℂ) (1 : Matrix dB dB ℂ) -
      bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G :=
    (bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ)).map_sub 1 G
  rw [hdiff, bornTracePairing_one_one] at hpositive
  linarith

theorem positiveContraction_eigenvalue_le_one
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (hcomplement : (1 - F).PosSemidef)
    (i : d) :
    hF.isHermitian.eigenvalues i ≤ 1 := by
  have hFle : F ≤ (1 : Matrix d d ℂ) :=
    Matrix.le_iff.mpr hcomplement
  have hspectrum : ∀ z ∈ spectrum ℝ F, z ≤ 1 :=
    (CFC.le_one_iff (R := ℝ) F hF.isHermitian).mp hFle
  exact hspectrum _ (hF.isHermitian.eigenvalues_mem_spectrum_real i)

theorem leftSpectralBornWeight_negEntropy
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (G : Matrix dB dB ℂ) :
    -bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G =
      ∑ i : dA,
        leftSpectralBornWeight ρ F hF G i *
          Real.negMulLog (hF.isHermitian.eigenvalues i) := by
  rw [leftSpectralBornWeight_entropy ρ F hF G,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.negMulLog, neg_mul, mul_neg]

theorem matrixLogEntropy_born_lower_bound_left
    {dA dB : Type*}
    [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ : DensityMatrix (dA × dB))
    (F : Matrix dA dA ℂ) (hF : F.PosSemidef)
    (hFcomplement : (1 - F).PosSemidef)
    (G : Matrix dB dB ℂ) (hG : G.PosSemidef)
    (hGcomplement : (1 - G).PosSemidef) :
    -bornTracePairing ρ.matrix
        (cfc (fun z : ℝ => z * Real.log z) F) G ≤
      Real.negMulLog (bornTracePairing ρ.matrix F G) := by
  classical
  have hp_nonneg : 0 ≤ bornTracePairing ρ.matrix F G :=
    trace_mul_posSemidef_nonneg ρ.positive (hF.kronecker hG)
  have hmass_le :
      bornTracePairing ρ.matrix F G ≤
        bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G := by
    calc
      bornTracePairing ρ.matrix F G =
        ∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            hF.isHermitian.eigenvalues i :=
          (leftSpectralBornWeight_moment ρ F hF G).symm
      _ ≤ ∑ i : dA, leftSpectralBornWeight ρ F hF G i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_right
          (leftSpectralBornWeight_nonneg ρ F hF G hG i)
          (positiveContraction_eigenvalue_le_one F hF hFcomplement i)
      _ = bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G :=
        leftSpectralBornWeight_sum ρ F hF G
  by_cases hp : bornTracePairing ρ.matrix F G = 0
  · have hzero :
        (∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            hF.isHermitian.eigenvalues i) = 0 := by
        rw [leftSpectralBornWeight_moment, hp]
    have hterm (i : dA) :
        leftSpectralBornWeight ρ F hF G i *
          hF.isHermitian.eigenvalues i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg
          (leftSpectralBornWeight_nonneg ρ F hF G hG j)
          (hF.eigenvalues_nonneg j))).mp hzero i (Finset.mem_univ i)
    have hentropy :
        (∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            Real.negMulLog (hF.isHermitian.eigenvalues i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases mul_eq_zero.mp (hterm i) with hw | he
      · simp only [hw, zero_mul]
      · simp only [he, Real.negMulLog_zero, mul_zero]
    calc
      -bornTracePairing ρ.matrix
          (cfc (fun z : ℝ => z * Real.log z) F) G =
        ∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            Real.negMulLog (hF.isHermitian.eigenvalues i) :=
          leftSpectralBornWeight_negEntropy ρ F hF G
      _ = 0 := hentropy
      _ ≤ Real.negMulLog (bornTracePairing ρ.matrix F G) := by
        rw [hp]
        simp only [Real.negMulLog_zero, Std.le_refl]
  · have hp_pos : 0 < bornTracePairing ρ.matrix F G :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hp)
    have hW_pos : 0 <
        bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G :=
      lt_of_lt_of_le hp_pos hmass_le
    have hscalar := finite_weighted_entropy_le_of_weight_bound
      (Finset.univ : Finset dA)
      (leftSpectralBornWeight ρ F hF G)
      hF.isHermitian.eigenvalues
      (W := bornTracePairing ρ.matrix (1 : Matrix dA dA ℂ) G)
      (N := (1 : ℝ))
      (p := bornTracePairing ρ.matrix F G)
      (fun i _ => leftSpectralBornWeight_nonneg ρ F hF G hG i)
      (fun i _ => hF.eigenvalues_nonneg i)
      hW_pos hp_pos
      (leftSpectralBornWeight_sum ρ F hF G)
      (leftSpectralBornWeight_moment ρ F hF G)
      (bornTracePairing_one_le_one ρ G hGcomplement)
    calc
      -bornTracePairing ρ.matrix
          (cfc (fun z : ℝ => z * Real.log z) F) G =
        ∑ i : dA,
          leftSpectralBornWeight ρ F hF G i *
            Real.negMulLog (hF.isHermitian.eigenvalues i) :=
        leftSpectralBornWeight_negEntropy ρ F hF G
      _ ≤ bornTracePairing ρ.matrix F G *
          Real.log (1 / bornTracePairing ρ.matrix F G) := hscalar
      _ = Real.negMulLog (bornTracePairing ρ.matrix F G) := by
        rw [one_div, Real.log_inv]
        simp only [mul_neg, Real.negMulLog, neg_mul]

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

/-- The quantum state representing raw embezzlement. -/
def rawEmbezzlementState (n : ℕ) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2 fun q : Fin n × Fin n =>
    if q.1 = q.2 then
      (↑((Real.sqrt ((q.1.val : ℝ) + 1))⁻¹) : ℂ)
    else
      0

theorem rawEmbezzlementState_ne_zero
    (n : ℕ) (hn : 0 < n) :
    rawEmbezzlementState n ≠ 0 := by
  intro h
  let j : Fin n := ⟨0, hn⟩
  have hj := congrArg
    (fun z : EuclideanSpace ℂ (Fin n × Fin n) => z (j, j)) h
  simp only [rawEmbezzlementState, Complex.ofReal_inv, ↓reduceIte, CharP.cast_eq_zero, zero_add,
    Real.sqrt_one, Complex.ofReal_one, inv_one, PiLp.zero_apply, one_ne_zero, j] at hj

/-- The harmonic number construction used in the quantum parallel-repetition argument. -/
def harmonicNumber (n : ℕ) : ℝ :=
  ∑ j : Fin n, ((j.val : ℝ) + 1)⁻¹

theorem rawEmbezzlementState_norm_sq (n : ℕ) :
    ‖rawEmbezzlementState n‖ ^ 2 =
      harmonicNumber n := by
  classical
  have hamp (j : Fin n) :
      ‖(↑((Real.sqrt ((j.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2 =
        ((j.val : ℝ) + 1)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), inv_pow,
      Real.sq_sqrt (by positivity)]
  have hterm (i j : Fin n) :
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2 =
      if i = j then
        ‖(↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2
      else
        0 := by
    split_ifs <;> simp
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  unfold harmonicNumber
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ j : Fin n,
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2) = ((i.val : ℝ) + 1)⁻¹
  calc
    (∑ j : Fin n,
      ‖if i = j then
        (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
      else
        0‖ ^ 2) =
        ‖(↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)‖ ^ 2 := by
          simp_rw [hterm]
          simp only [Complex.ofReal_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow,
            sq_abs, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    _ = ((i.val : ℝ) + 1)⁻¹ := hamp i

/-- The quantum state representing embezzlement. -/
def embezzlementState (n : ℕ) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  (‖rawEmbezzlementState n‖⁻¹ : ℝ) •
    rawEmbezzlementState n

theorem embezzlementState_norm
    (n : ℕ) (hn : 0 < n) :
    ‖embezzlementState n‖ = 1 := by
  have hraw : ‖rawEmbezzlementState n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (rawEmbezzlementState_ne_zero n hn)
  rw [embezzlementState, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hraw]

theorem embezzlementState_apply
    (n : ℕ) (i j : Fin n) :
    embezzlementState n (i, j) =
      (‖rawEmbezzlementState n‖⁻¹ : ℝ) •
        (if i = j then
          (↑((Real.sqrt ((i.val : ℝ) + 1))⁻¹) : ℂ)
        else
          0) := by
  rfl

/-- The type used to represent bipartite unit vector in the exact sampling construction. -/
abbrev BipartiteUnitVector (d : ℕ) :=
  {ξ : EuclideanSpace ℂ (Fin d × Fin d) // ‖ξ‖ = 1}

/-- The overlap quantity for spectral atom. -/
def spectralAtomOverlap
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i j : d) : ℝ :=
  (Matrix.trace
    (positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom G hG j)).re

theorem spectralAtomOverlap_nonneg
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i j : d) :
    0 ≤ spectralAtomOverlap F G hF hG i j := by
  exact trace_mul_posSemidef_nonneg
    (positiveMatrixSpectralAtom_posSemidef F hF i)
    (positiveMatrixSpectralAtom_posSemidef G hG j)

theorem spectralAtom_trace
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (i : d) :
    Matrix.trace (positiveMatrixSpectralAtom F hF i) = 1 := by
  classical
  unfold positiveMatrixSpectralAtom
  rw [spectralConjugationCLM_apply, Matrix.trace_mul_cycle,
    Matrix.UnitaryGroup.star_mul_self, one_mul,
    Matrix.trace_diagonal]
  simp only [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem spectralAtom_mul
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (i j : d) :
    positiveMatrixSpectralAtom F hF i *
      positiveMatrixSpectralAtom F hF j =
        if i = j then positiveMatrixSpectralAtom F hF i else 0 := by
  classical
  let e := Unitary.conjStarAlgAut ℝ (Matrix d d ℂ)
    hF.isHermitian.eigenvectorUnitary
  change
    e (Matrix.diagonal (Pi.single i (1 : ℂ))) *
      e (Matrix.diagonal (Pi.single j (1 : ℂ))) =
        if i = j then
          e (Matrix.diagonal (Pi.single i (1 : ℂ)))
        else
          0
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    rw [← map_mul, Matrix.diagonal_mul_diagonal]
    congr 1
    ext k l
    simp only [Matrix.diagonal_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · simp only [hij, ite_false]
    rw [← map_mul, Matrix.diagonal_mul_diagonal, ← map_zero e]
    congr 1
    ext k l
    by_cases hik : k = i
    · subst k
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Matrix.diagonal_apply, hij,
        ↓reduceIte, ite_self, Matrix.zero_apply]
    · simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Matrix.diagonal_apply, hik,
        ↓reduceIte, ite_self, Matrix.zero_apply]

theorem spectralAtomSum_mul_self
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (s : Finset d) :
    (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) *
      (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) =
        ∑ i ∈ s, positiveMatrixSpectralAtom F hF i := by
  classical
  calc
    (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) *
        (∑ i ∈ s, positiveMatrixSpectralAtom F hF i) =
      ∑ i ∈ s, ∑ j ∈ s,
        positiveMatrixSpectralAtom F hF i *
          positiveMatrixSpectralAtom F hF j := by
            simp only [Matrix.sum_mul, Matrix.mul_sum]
            rw [Finset.sum_comm]
    _ = ∑ i ∈ s, positiveMatrixSpectralAtom F hF i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [spectralAtom_mul, Finset.sum_ite_eq, hi, ↓reduceIte]

theorem rectangularMatrix_norm_sq
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d]
    (K : Matrix e d ℂ) (z : EuclideanSpace ℂ d) :
    ‖toLp 2 (K.mulVec (ofLp z))‖ ^ 2 =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * K)) z := by
  calc
    ‖toLp 2 (K.mulVec (ofLp z))‖ ^ 2 =
        (inner ℂ (toLp 2 (K.mulVec (ofLp z)))
          (toLp 2 (K.mulVec (ofLp z)))).re :=
            norm_sq_eq_re_inner (𝕜 := ℂ)
              (toLp 2 (K.mulVec (ofLp z)))
    _ = (star (K.mulVec (ofLp z)) ⬝ᵥ
          K.mulVec (ofLp z)).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (K.mulVec (ofLp z) ⬝ᵥ
          star (K.mulVec (ofLp z))).re = _
      rw [dotProduct_comm]
    _ = (star (ofLp z) ⬝ᵥ
        (K.conjTranspose * K).mulVec (ofLp z)).re := by
          rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
            Matrix.mulVec_mulVec]
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)
          (K.conjTranspose * K)) z := by
      unfold quadraticExpectation
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (star (ofLp z) ⬝ᵥ
          (K.conjTranspose * K).mulVec (ofLp z)).re =
        ((K.conjTranspose * K).mulVec (ofLp z) ⬝ᵥ
          star (ofLp z)).re
      rw [dotProduct_comm]

/-- The finite outcome encoding for coherent binary joint. -/
def coherentBinaryJointOutcome
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM Bool d) (Q : POVM Bool e)
    (z : EuclideanSpace ℂ (d × e))
    (a b : Bool) : EuclideanSpace ℂ (d × e) :=
  toLp 2
    (((P.effect a ⊗ₖ Q.effect b)).mulVec (ofLp z))

theorem coherentBinaryJointOutcome_norm_sq
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM Bool d) (Q : POVM Bool e)
    (hP : ∀ c : Bool, P.effect c * P.effect c = P.effect c)
    (hQ : ∀ c : Bool, Q.effect c * Q.effect c = Q.effect c)
    (z : EuclideanSpace ℂ (d × e)) (hz : ‖z‖ = 1)
    (a b : Bool) :
    ‖coherentBinaryJointOutcome P Q z a b‖ ^ 2 =
      (Matrix.trace
        ((pureDensityMatrix z hz).matrix *
          (P.effect a ⊗ₖ Q.effect b))).re := by
  let K : Matrix (d × e) (d × e) ℂ :=
    P.effect a ⊗ₖ Q.effect b
  have hgram : K.conjTranspose * K = K := by
    dsimp [K]
    rw [Matrix.conjTranspose_kronecker,
      (P.positive a).isHermitian.eq,
      (Q.positive b).isHermitian.eq,
      ← Matrix.mul_kronecker_mul,
      hP a, hQ b]
  calc
    ‖coherentBinaryJointOutcome P Q z a b‖ ^ 2 =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := d × e) (𝕜 := ℂ)
          (K.conjTranspose * K)) z :=
        rectangularMatrix_norm_sq K z
    _ = quadraticExpectation
        (Matrix.toEuclideanCLM (n := d × e) (𝕜 := ℂ) K) z := by
      rw [hgram]
    _ = (Matrix.trace ((pureDensityMatrix z hz).matrix * K)).re :=
      (pureDensityMatrix_trace_mul z hz K).symm

/-- The state vector representing finite tensor. -/
def finiteTensorVector
    {ι d : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℂ d) :
    EuclideanSpace ℂ (ι → d) :=
  toLp 2 fun q : ι → d => ∏ i : ι, v i (q i)

theorem finiteTensorVector_norm_sq
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]
    (v : ι → EuclideanSpace ℂ d) :
    ‖finiteTensorVector v‖ ^ 2 =
      ∏ i : ι, ‖v i‖ ^ 2 := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  change
    (∑ q : ι → d, ‖∏ i : ι, v i (q i)‖ ^ 2) =
      ∏ i : ι, ‖v i‖ ^ 2
  calc
    (∑ q : ι → d, ‖∏ i : ι, v i (q i)‖ ^ 2) =
        ∑ q : ι → d, ∏ i : ι, ‖v i (q i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro q _
          rw [norm_prod, ← Finset.prod_pow]
    _ = ∏ i : ι, ∑ a : d, ‖v i a‖ ^ 2 :=
      (Fintype.prod_sum
        (fun i : ι => fun a : d => ‖v i a‖ ^ 2)).symm
    _ = ∏ i : ι, ‖v i‖ ^ 2 := by
      apply Finset.prod_congr rfl
      intro i _
      exact (EuclideanSpace.norm_sq_eq (v i)).symm

theorem finiteTensorVector_norm
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]
    (v : ι → EuclideanSpace ℂ d)
    (hv : ∀ i, ‖v i‖ = 1) :
    ‖finiteTensorVector v‖ = 1 := by
  have hsquare := finiteTensorVector_norm_sq v
  simp_rw [hv, one_pow, Finset.prod_const_one] at hsquare
  nlinarith [norm_nonneg (finiteTensorVector v)]

theorem spectralAtomOverlap_sum_right
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (i : d) :
    (∑ j : d, spectralAtomOverlap F G hF hG i j) = 1 := by
  classical
  calc
    (∑ j : d, spectralAtomOverlap F G hF hG i j) =
        (Matrix.trace
          (positiveMatrixSpectralAtom F hF i *
            (∑ j : d, positiveMatrixSpectralAtom G hG j))).re := by
              simp only [spectralAtomOverlap,
                Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    _ = (Matrix.trace (positiveMatrixSpectralAtom F hF i)).re := by
      rw [positiveMatrixSpectralAtom_sum]
      simp only [mul_one]
    _ = 1 := by
      rw [spectralAtom_trace]
      rfl

theorem spectralAtomOverlap_sum_left
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (j : d) :
    (∑ i : d, spectralAtomOverlap F G hF hG i j) = 1 := by
  classical
  calc
    (∑ i : d, spectralAtomOverlap F G hF hG i j) =
        (Matrix.trace
          ((∑ i : d, positiveMatrixSpectralAtom F hF i) *
            positiveMatrixSpectralAtom G hG j)).re := by
              simp only [spectralAtomOverlap,
                Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
    _ = (Matrix.trace (positiveMatrixSpectralAtom G hG j)).re := by
      rw [positiveMatrixSpectralAtom_sum]
      simp only [one_mul]
    _ = 1 := by
      rw [spectralAtom_trace]
      rfl

theorem positiveDensity_eigenvalues_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (htrace : Matrix.trace F = 1) :
    (∑ i : d, hF.isHermitian.eigenvalues i) = 1 := by
  have hspectral := congrArg Complex.re
    hF.isHermitian.trace_eq_sum_eigenvalues
  simpa only [Complex.coe_algebraMap, Complex.re_sum, Complex.ofReal_re, htrace,
    Complex.one_re] using hspectral.symm

theorem spectralAtomOverlap_schmidtMass_le_one
    {d : Type*} [Fintype d] [DecidableEq d]
    (F G : Matrix d d ℂ)
    (hF : F.PosSemidef) (hG : G.PosSemidef)
    (hFtrace : Matrix.trace F = 1)
    (hGtrace : Matrix.trace G = 1) :
    (∑ i : d, ∑ j : d,
      Real.sqrt (hF.isHermitian.eigenvalues i) *
        Real.sqrt (hG.isHermitian.eigenvalues j) *
          spectralAtomOverlap F G hF hG i j) ≤ 1 := by
  classical
  let w : d × d → ℝ := fun q =>
    spectralAtomOverlap F G hF hG q.1 q.2
  let f : d × d → ℝ := fun q =>
    Real.sqrt (hF.isHermitian.eigenvalues q.1)
  let g : d × d → ℝ := fun q =>
    Real.sqrt (hG.isHermitian.eigenvalues q.2)
  have hf : (∑ q : d × d, w q * f q ^ 2) = 1 := by
    dsimp [w, f]
    rw [Fintype.sum_prod_type]
    simp_rw [Real.sq_sqrt (hF.eigenvalues_nonneg _)]
    calc
      (∑ i : d, ∑ j : d,
        spectralAtomOverlap F G hF hG i j *
          hF.isHermitian.eigenvalues i) =
        ∑ i : d,
          hF.isHermitian.eigenvalues i *
            (∑ j : d,
              spectralAtomOverlap F G hF hG i j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ∑ i : d, hF.isHermitian.eigenvalues i := by
        simp_rw [spectralAtomOverlap_sum_right,
          mul_one]
      _ = 1 := positiveDensity_eigenvalues_sum F hF hFtrace
  have hg : (∑ q : d × d, w q * g q ^ 2) = 1 := by
    dsimp [w, g]
    rw [Fintype.sum_prod_type]
    simp_rw [Real.sq_sqrt (hG.eigenvalues_nonneg _)]
    calc
      (∑ i : d, ∑ j : d,
        spectralAtomOverlap F G hF hG i j *
          hG.isHermitian.eigenvalues j) =
        ∑ j : d,
          hG.isHermitian.eigenvalues j *
            (∑ i : d,
              spectralAtomOverlap F G hF hG i j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = ∑ j : d, hG.isHermitian.eigenvalues j := by
        simp_rw [spectralAtomOverlap_sum_left,
          mul_one]
      _ = 1 := positiveDensity_eigenvalues_sum G hG hGtrace
  calc
    (∑ i : d, ∑ j : d,
      Real.sqrt (hF.isHermitian.eigenvalues i) *
        Real.sqrt (hG.isHermitian.eigenvalues j) *
          spectralAtomOverlap F G hF hG i j) =
      ∑ q : d × d, w q * f q * g q := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp [w, f, g]
        ring
    _ ≤ Real.sqrt (∑ q : d × d, w q * f q ^ 2) *
        Real.sqrt (∑ q : d × d, w q * g q ^ 2) := by
          apply weighted_real_cauchy
          intro q
          exact spectralAtomOverlap_nonneg
            F G hF hG q.1 q.2
    _ = 1 := by rw [hf, hg]; norm_num

/-- The probability of binary born. -/
def binaryBornProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e)
    (a b : Bool) : ℝ :=
  (Matrix.trace
    (ρ.matrix * (P.effect a ⊗ₖ Q.effect b))).re

theorem binaryBornProbability_normalized
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) :
    (∑ a : Bool, ∑ b : Bool,
      binaryBornProbability ρ P Q a b) = 1 := by
  classical
  have hjoint :
      (∑ a : Bool, ∑ b : Bool, P.effect a ⊗ₖ Q.effect b) =
        (1 : Matrix (d × e) (d × e) ℂ) := by
    calc
      (∑ a : Bool, ∑ b : Bool, P.effect a ⊗ₖ Q.effect b) =
          (∑ a : Bool, P.effect a) ⊗ₖ
            (∑ b : Bool, Q.effect b) := by
              ext ⟨i, j⟩ ⟨k, l⟩
              simp only [Matrix.sum_apply,
                Matrix.kroneckerMap_apply]
              rw [Finset.sum_mul]
              simp_rw [Finset.mul_sum]
      _ = 1 := by
        rw [P.complete, Q.complete]
        exact Matrix.one_kronecker_one
  calc
    (∑ a : Bool, ∑ b : Bool,
      binaryBornProbability ρ P Q a b) =
        (Matrix.trace
          (ρ.matrix *
            (∑ a : Bool, ∑ b : Bool,
              P.effect a ⊗ₖ Q.effect b))).re := by
          simp only [Fintype.sum_bool,
            binaryBornProbability, Matrix.mul_add,
            Matrix.trace_add, Complex.add_re]
    _ = (Matrix.trace ρ.matrix).re := by
      rw [hjoint]
      simp only [mul_one]
    _ = 1 := by
      rw [ρ.trace_one]
      rfl

/-- The probability of binary continue. -/
def binaryContinueProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q false false

/-- The probability of binary joint success. -/
def binaryJointSuccessProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q true true

/-- The probability of binary mismatch. -/
def binaryMismatchProbability
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) : ℝ :=
  binaryBornProbability ρ P Q true false +
    binaryBornProbability ρ P Q false true

theorem binaryStoppingPartition
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (ρ : DensityMatrix (d × e))
    (P : POVM Bool d) (Q : POVM Bool e) :
    binaryContinueProbability ρ P Q +
      binaryJointSuccessProbability ρ P Q +
        binaryMismatchProbability ρ P Q = 1 := by
  have hnormalized := binaryBornProbability_normalized ρ P Q
  simp only [Fintype.sum_bool] at hnormalized
  unfold binaryContinueProbability
    binaryJointSuccessProbability
    binaryMismatchProbability
  linarith

theorem unitVector_distance_of_real_overlap
    {ι : Type*} [Fintype ι]
    (z w : EuclideanSpace ℂ ι)
    (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hoverlap : 1 - ε ≤ (inner ℂ z w).re) :
    ‖z - w‖ ≤ Real.sqrt (2 * ε) := by
  have hoverlap' : 1 - ε ≤ RCLike.re (inner ℂ z w) := by
    exact hoverlap
  have hsq : ‖z - w‖ ^ 2 ≤ 2 * ε := by
    rw [@norm_sub_sq ℂ, hz, hw]
    linarith [hoverlap']
  have hsqrt : (Real.sqrt (2 * ε)) ^ 2 = 2 * ε :=
    Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg (z - w), Real.sqrt_nonneg (2 * ε)]

/--
The shared threshold resource raw construction used in the quantum parallel-repetition argument.
-/
def sharedThresholdResourceRaw
    {κ d : Type*}
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    EuclideanSpace ℂ ((Σ _ : κ, d) × (Σ _ : κ, d)) :=
  toLp 2 fun q : (Σ _ : κ, d) × (Σ _ : κ, d) =>
    if q.1.1 = q.2.1 ∧ q.1.2 = q.2.2 then
      (τ q.1.1 : ℂ)
    else
      0

theorem sharedThresholdResourceRaw_norm_sq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    ‖sharedThresholdResourceRaw (d := d) τ‖ ^ 2 =
      (Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2 := by
  classical
  have hterm (k l : κ) (i j : d) :
      ‖if k = l ∧ i = j then (τ k : ℂ) else 0‖ ^ 2 =
        if k = l then if i = j then τ k ^ 2 else 0 else 0 := by
    split_ifs <;>
      simp_all [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sigma]
  change
    (∑ k : κ, ∑ i : d, ∑ l : κ, ∑ j : d,
      ‖if k = l ∧ i = j then (τ k : ℂ) else 0‖ ^ 2) =
        (Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2
  simp_rw [hterm]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

theorem sharedThresholdResourceRaw_ne_zero
    {κ d : Type*}
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k : κ) (i : d) (hk : τ k ≠ 0) :
    sharedThresholdResourceRaw (d := d) τ ≠ 0 := by
  intro hzero
  have hentry := congrArg
    (fun z : EuclideanSpace ℂ
        ((Σ _ : κ, d) × (Σ _ : κ, d)) =>
      z (⟨k, i⟩, ⟨k, i⟩)) hzero
  have hcast : (τ k : ℂ) = 0 := by
    simpa only [Complex.ofReal_eq_zero, sharedThresholdResourceRaw, and_self, ↓reduceIte,
      PiLp.zero_apply] using hentry
  exact hk (by exact_mod_cast hcast)

/-- The auxiliary resource for shared threshold. -/
def sharedThresholdResource
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    EuclideanSpace ℂ ((Σ _ : κ, d) × (Σ _ : κ, d)) :=
  (‖sharedThresholdResourceRaw (d := d) τ‖⁻¹ : ℝ) •
    sharedThresholdResourceRaw (d := d) τ

theorem sharedThresholdResource_norm
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (k : κ) (i : d) (hk : τ k ≠ 0) :
    ‖sharedThresholdResource (d := d) τ‖ = 1 := by
  have hnorm : ‖sharedThresholdResourceRaw (d := d) τ‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (sharedThresholdResourceRaw_ne_zero τ k i hk)
  rw [sharedThresholdResource, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hnorm]

/-- The positive operator-valued measurement implementing transpose. -/
def transposePOVM
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (P : POVM ι d) : POVM ι d where
  effect b := (P.effect b).transpose
  positive b := (P.positive b).transpose
  complete := by
    classical
    ext i j
    have hc := congrArg
      (fun M : Matrix d d ℂ => M j i) P.complete
    simpa only [Matrix.sum_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm] using hc

theorem transposePOVM_projective
    {ι d : Type*} [Fintype ι] [Fintype d] [DecidableEq d]
    (P : POVM ι d)
    (hP : ∀ b : ι, P.effect b * P.effect b = P.effect b)
    (b : ι) :
    (transposePOVM P).effect b *
      (transposePOVM P).effect b =
        (transposePOVM P).effect b := by
  change
    (P.effect b).transpose * (P.effect b).transpose =
      (P.effect b).transpose
  rw [← Matrix.transpose_mul, hP b]

theorem sharedThresholdResourceRaw_eq_vec
    {κ d : Type*}
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    sharedThresholdResourceRaw (d := d) τ =
      toLp 2 (Matrix.vec
        (Matrix.diagonal (fun q : Σ _ : κ, d => (τ q.1 : ℂ)))) := by
  ext ⟨⟨k, i⟩, ⟨l, j⟩⟩
  by_cases h : k = l
  · subst l
    by_cases hij : i = j
    · subst j
      simp only [sharedThresholdResourceRaw, and_self, ↓reduceIte, Matrix.vec,
        Matrix.diagonal_apply_eq]
    · simp only [sharedThresholdResourceRaw, hij, and_false, ↓reduceIte, Matrix.vec, ne_eq,
        Sigma.mk.injEq, heq_eq_eq, Ne.symm hij, not_false_eq_true, Matrix.diagonal_apply_ne]
  · simp only [sharedThresholdResourceRaw, h, false_and, ↓reduceIte, Matrix.vec, ne_eq,
      Sigma.mk.injEq, Ne.symm h, heq_eq_eq, not_false_eq_true, Matrix.diagonal_apply_ne]

theorem sharedThresholdResourceRaw_local_action
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ)
    (A B : Matrix (Σ _ : κ, d) (Σ _ : κ, d) ℂ) :
    toLp 2
      ((A ⊗ₖ B.transpose).mulVec
        (ofLp (sharedThresholdResourceRaw (d := d) τ))) =
      toLp 2
        (Matrix.vec
          (B.transpose *
            Matrix.diagonal
              (fun q : Σ _ : κ, d => (τ q.1 : ℂ)) * A.transpose)) := by
  rw [sharedThresholdResourceRaw_eq_vec]
  apply WithLp.ofLp_injective
  change
    (A ⊗ₖ B.transpose).mulVec
      (Matrix.vec
        (Matrix.diagonal
          (fun q : Σ _ : κ, d => (τ q.1 : ℂ)))) =
      Matrix.vec
        (B.transpose *
          Matrix.diagonal
            (fun q : Σ _ : κ, d => (τ q.1 : ℂ)) * A.transpose)
  exact Matrix.kronecker_mulVec_vec
    B.transpose
    (Matrix.diagonal
      (fun q : Σ _ : κ, d => (τ q.1 : ℂ)))
    A

theorem matrixVectorization_norm_sq
    {d e : Type*} [Fintype d] [Fintype e]
    (K : Matrix d e ℂ) :
    ‖toLp 2 (Matrix.vec K)‖ ^ 2 =
      (Matrix.trace (K.conjTranspose * K)).re := by
  calc
    ‖toLp 2 (Matrix.vec K)‖ ^ 2 =
        (inner ℂ (toLp 2 (Matrix.vec K))
          (toLp 2 (Matrix.vec K))).re :=
            norm_sq_eq_re_inner (𝕜 := ℂ)
              (toLp 2 (Matrix.vec K))
    _ = (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        (Matrix.vec K ⬝ᵥ star (Matrix.vec K)).re =
          (star (Matrix.vec K) ⬝ᵥ Matrix.vec K).re
      rw [dotProduct_comm]
    _ = (Matrix.trace (K.conjTranspose * K)).re := by
      rw [Matrix.star_vec_dotProduct_vec]

theorem sharedThresholdDiagonal_eq_block
    {κ d : Type*}
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) :
    Matrix.diagonal
        (fun q : Σ _ : κ, d => (τ q.1 : ℂ)) =
      Matrix.blockDiagonal' fun k : κ =>
        (τ k : ℂ) • (1 : Matrix d d ℂ) := by
  classical
  ext ⟨k, i⟩ ⟨l, j⟩
  by_cases h : k = l
  · subst l
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Complex.coe_smul, Matrix.blockDiagonal'_apply,
        ↓reduceDIte, cast_eq, Matrix.smul_apply, Matrix.one_apply_eq, Complex.real_smul, mul_one]
    · simp only [ne_eq, Sigma.mk.injEq, heq_eq_eq, hij, and_false, not_false_eq_true,
        Matrix.diagonal_apply_ne, Complex.coe_smul, Matrix.blockDiagonal'_apply, ↓reduceDIte,
        cast_eq, Matrix.smul_apply, Matrix.one_apply_ne, smul_zero]
  · simp only [ne_eq, Sigma.mk.injEq, h, heq_eq_eq, false_and, not_false_eq_true,
      Matrix.diagonal_apply_ne, Complex.coe_smul, Matrix.blockDiagonal'_apply, ↓reduceDIte]

theorem sharedThresholdResourceRaw_block_action
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ) (A B : κ → Matrix d d ℂ) :
    toLp 2
      ((Matrix.blockDiagonal' A ⊗ₖ
          (Matrix.blockDiagonal' B).transpose).mulVec
        (ofLp (sharedThresholdResourceRaw (d := d) τ))) =
      toLp 2
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : κ =>
              (τ k : ℂ) • (A k * B k)).transpose)) := by
  rw [sharedThresholdResourceRaw_local_action]
  congr 2
  rw [sharedThresholdDiagonal_eq_block]
  simp only [Matrix.blockDiagonal'_transpose]
  rw [← Matrix.blockDiagonal'_mul,
    ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  simp only [Complex.coe_smul, Algebra.mul_smul_comm, mul_one, Algebra.smul_mul_assoc,
    Matrix.transpose_smul, Matrix.transpose_mul]

theorem projectorProduct_hilbertSchmidt_trace
    {d : Type*} [Fintype d]
    (A B : Matrix d d ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAA : A * A = A) (hBB : B * B = B) :
    Matrix.trace ((A * B).conjTranspose * (A * B)) =
      Matrix.trace (A * B) := by
  rw [Matrix.conjTranspose_mul,
    hA.isHermitian.eq, hB.isHermitian.eq]
  calc
    Matrix.trace ((B * A) * (A * B)) =
        Matrix.trace (B * (A * A) * B) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (B * A * B) := by rw [hAA]
    _ = Matrix.trace (B * B * A) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (B * A) := by rw [hBB]
    _ = Matrix.trace (A * B) := Matrix.trace_mul_comm B A

theorem weightedProjectorProduct_hilbertSchmidt_trace
    {d : Type*} [Fintype d]
    (t : ℝ) (A B : Matrix d d ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAA : A * A = A) (hBB : B * B = B) :
    (Matrix.trace
      (((t : ℂ) • (A * B)).conjTranspose *
        ((t : ℂ) • (A * B)))).re =
      t ^ 2 * (Matrix.trace (A * B)).re := by
  have hgram := projectorProduct_hilbertSchmidt_trace
    A B hA hB hAA hBB
  rw [Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, Matrix.trace_smul, hgram]
  simp only [RCLike.star_def, Complex.conj_ofReal, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im, add_zero, pow_two, mul_assoc]

theorem sharedThresholdResourceRaw_block_action_norm_sq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ)
    (A B : κ → Matrix d d ℂ)
    (hA : ∀ k, (A k).PosSemidef)
    (hB : ∀ k, (B k).PosSemidef)
    (hAA : ∀ k, A k * A k = A k)
    (hBB : ∀ k, B k * B k = B k) :
    ‖toLp 2
      ((Matrix.blockDiagonal' A ⊗ₖ
          (Matrix.blockDiagonal' B).transpose).mulVec
        (ofLp (sharedThresholdResourceRaw (d := d) τ)))‖ ^ 2 =
      ∑ k : κ, τ k ^ 2 *
        (Matrix.trace (A k * B k)).re := by
  rw [sharedThresholdResourceRaw_block_action,
    matrixVectorization_norm_sq]
  let K : Matrix (Σ _ : κ, d) (Σ _ : κ, d) ℂ :=
    Matrix.blockDiagonal' fun k : κ =>
      (τ k : ℂ) • (A k * B k)
  change
    (Matrix.trace (K.transpose.conjTranspose * K.transpose)).re =
      ∑ k : κ, τ k ^ 2 *
        (Matrix.trace (A k * B k)).re
  rw [Matrix.transpose_conjTranspose,
    ← Matrix.conjTranspose_transpose,
    Matrix.trace_transpose_mul]
  change
    (Matrix.trace
      ((Matrix.blockDiagonal' fun k : κ =>
        (τ k : ℂ) • (A k * B k)).conjTranspose *
        (Matrix.blockDiagonal' fun k : κ =>
          (τ k : ℂ) • (A k * B k)))).re = _
  rw [Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul,
    Matrix.trace_blockDiagonal', Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact weightedProjectorProduct_hilbertSchmidt_trace
    (τ k) (A k) (B k) (hA k) (hB k) (hAA k) (hBB k)

theorem sharedThresholdResource_block_action_norm_sq
    {κ d : Type*} [Fintype κ] [Fintype d]
    [DecidableEq κ] [DecidableEq d]
    (τ : κ → ℝ)
    (A B : κ → Matrix d d ℂ)
    (hA : ∀ k, (A k).PosSemidef)
    (hB : ∀ k, (B k).PosSemidef)
    (hAA : ∀ k, A k * A k = A k)
    (hBB : ∀ k, B k * B k = B k) :
    ‖toLp 2
      ((Matrix.blockDiagonal' A ⊗ₖ
          (Matrix.blockDiagonal' B).transpose).mulVec
        (ofLp (sharedThresholdResource (d := d) τ)))‖ ^ 2 =
      (∑ k : κ, τ k ^ 2 *
        (Matrix.trace (A k * B k)).re) /
        ((Fintype.card d : ℝ) * ∑ k : κ, τ k ^ 2) := by
  let M : Matrix
      ((Σ _ : κ, d) × (Σ _ : κ, d))
      ((Σ _ : κ, d) × (Σ _ : κ, d)) ℂ :=
    Matrix.blockDiagonal' A ⊗ₖ
      (Matrix.blockDiagonal' B).transpose
  change
    ‖Matrix.toEuclideanLin M
      (sharedThresholdResource (d := d) τ)‖ ^ 2 = _
  rw [sharedThresholdResource,
    (Matrix.toEuclideanLin M).map_smul_of_tower,
    norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    mul_pow, inv_pow]
  change
    (‖sharedThresholdResourceRaw (d := d) τ‖ ^ 2)⁻¹ *
      ‖toLp 2
        ((Matrix.blockDiagonal' A ⊗ₖ
            (Matrix.blockDiagonal' B).transpose).mulVec
          (ofLp (sharedThresholdResourceRaw (d := d) τ)))‖ ^ 2 = _
  rw [sharedThresholdResourceRaw_norm_sq,
    sharedThresholdResourceRaw_block_action_norm_sq
      τ A B hA hB hAA hBB]
  simp only [mul_inv_rev, mul_comm, div_eq_mul_inv]

theorem doublyStochasticSchmidtMass_le_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ) (w : ι → κ → ℝ)
    (hσunit : (∑ i : ι, σ i ^ 2) = 1)
    (hμunit : (∑ j : κ, μ j ^ 2) = 1)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, (∑ j : κ, w i j) = 1)
    (hcol : ∀ j, (∑ i : ι, w i j) = 1) :
    (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) ≤ 1 := by
  classical
  let W : ι × κ → ℝ := fun q => w q.1 q.2
  let f : ι × κ → ℝ := fun q => σ q.1
  let g : ι × κ → ℝ := fun q => μ q.2
  have hf : (∑ q : ι × κ, W q * f q ^ 2) = 1 := by
    dsimp [W, f]
    rw [Fintype.sum_prod_type]
    calc
      (∑ i : ι, ∑ j : κ, w i j * σ i ^ 2) =
          ∑ i : ι, σ i ^ 2 * (∑ j : κ, w i j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring_nf
      _ = ∑ i : ι, σ i ^ 2 := by simp_rw [hrow, mul_one]
      _ = 1 := hσunit
  have hg : (∑ q : ι × κ, W q * g q ^ 2) = 1 := by
    dsimp [W, g]
    rw [Fintype.sum_prod_type]
    calc
      (∑ i : ι, ∑ j : κ, w i j * μ j ^ 2) =
          ∑ j : κ, μ j ^ 2 * (∑ i : ι, w i j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = ∑ j : κ, μ j ^ 2 := by simp_rw [hcol, mul_one]
      _ = 1 := hμunit
  calc
    (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) =
        ∑ q : ι × κ, W q * f q * g q := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          dsimp [W, f, g]
          ring
    _ ≤ Real.sqrt (∑ q : ι × κ, W q * f q ^ 2) *
        Real.sqrt (∑ q : ι × κ, W q * g q ^ 2) := by
          apply weighted_real_cauchy
          intro q
          exact hw q.1 q.2
    _ = 1 := by rw [hf, hg]; norm_num

theorem doublyStochasticSchmidtEnergy_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ) (w : ι → κ → ℝ)
    (hσunit : (∑ i : ι, σ i ^ 2) = 1)
    (hμunit : (∑ j : κ, μ j ^ 2) = 1)
    (hrow : ∀ i, (∑ j : κ, w i j) = 1)
    (hcol : ∀ j, (∑ i : ι, w i j) = 1) :
    (∑ i : ι, ∑ j : κ, (σ i - μ j) ^ 2 * w i j) =
      2 - 2 * (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) := by
  classical
  have hfirst :
      (∑ i : ι, ∑ j : κ, σ i ^ 2 * w i j) = 1 := by
    calc
      (∑ i : ι, ∑ j : κ, σ i ^ 2 * w i j) =
          ∑ i : ι, σ i ^ 2 * (∑ j : κ, w i j) := by
            simp_rw [Finset.mul_sum]
      _ = ∑ i : ι, σ i ^ 2 := by simp_rw [hrow, mul_one]
      _ = 1 := hσunit
  have hsecond :
      (∑ i : ι, ∑ j : κ, μ j ^ 2 * w i j) = 1 := by
    calc
      (∑ i : ι, ∑ j : κ, μ j ^ 2 * w i j) =
          ∑ j : κ, μ j ^ 2 * (∑ i : ι, w i j) := by
            rw [Finset.sum_comm]
            simp_rw [Finset.mul_sum]
      _ = ∑ j : κ, μ j ^ 2 := by simp_rw [hcol, mul_one]
      _ = 1 := hμunit
  calc
    (∑ i : ι, ∑ j : κ, (σ i - μ j) ^ 2 * w i j) =
      (∑ i : ι, ∑ j : κ, σ i ^ 2 * w i j) -
        2 * (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) +
          (∑ i : ι, ∑ j : κ, μ j ^ 2 * w i j) := by
            simp_rw [sub_sq]
            simp only [sub_mul, add_mul,
              Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.mul_sum]
            ring_nf
    _ = 2 - 2 * (∑ i : ι, ∑ j : κ, σ i * μ j * w i j) := by
      rw [hfirst, hsecond]
      ring

private def weightedComplexOverlapVector
    {ι κ : Type*}
    (σ : ι → ℝ) (μ : κ → ℝ)
    (L : ι → κ → ℂ) : EuclideanSpace ℂ (ι × κ) :=
  toLp 2 fun q : ι × κ =>
    (Real.sqrt (σ q.1 * μ q.2) : ℂ) * L q.1 q.2

theorem weightedComplexOverlapVector_norm_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hμ : ∀ j, 0 ≤ μ j)
    (L : ι → κ → ℂ) :
    ‖weightedComplexOverlapVector σ μ L‖ ^ 2 =
      ∑ i : ι, ∑ j : κ,
        σ i * μ j * ‖L i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change
    ‖(Real.sqrt (σ i * μ j) : ℂ) * L i j‖ ^ 2 =
      σ i * μ j * ‖L i j‖ ^ 2
  rw [norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (mul_nonneg (hσ i) (hμ j))]

theorem complexInner_norm_sq_le
    {ι : Type*} [Fintype ι]
    (z w : EuclideanSpace ℂ ι) :
    ‖inner ℂ z w‖ ^ 2 ≤ ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
  have hcauchy := @norm_inner_le_norm ℂ _ _ _ _ z w
  nlinarith [norm_nonneg (inner ℂ z w), norm_nonneg z,
    norm_nonneg w, mul_nonneg (norm_nonneg z) (norm_nonneg w)]

theorem twoSidedSchmidtSpectralEnergy_le
    {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (ψ φ : EuclideanSpace ℂ ν)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (σ : ι → ℝ) (μ : κ → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hμ : ∀ j, 0 ≤ μ j)
    (hσunit : (∑ i : ι, σ i ^ 2) = 1)
    (hμunit : (∑ j : κ, μ j ^ 2) = 1)
    (L R : ι → κ → ℂ)
    (hLrow : ∀ i, (∑ j : κ, ‖L i j‖ ^ 2) = 1)
    (hLcol : ∀ j, (∑ i : ι, ‖L i j‖ ^ 2) = 1)
    (hRrow : ∀ i, (∑ j : κ, ‖R i j‖ ^ 2) = 1)
    (hRcol : ∀ j, (∑ i : ι, ‖R i j‖ ^ 2) = 1)
    (hinner :
      inner ℂ ψ φ =
        inner ℂ
          (weightedComplexOverlapVector σ μ L)
          (weightedComplexOverlapVector σ μ R)) :
    (∑ i : ι, ∑ j : κ,
      (σ i - μ j) ^ 2 * ‖L i j‖ ^ 2) ≤
        2 * ‖ψ - φ‖ ^ 2 := by
  classical
  let a : ℝ :=
    ∑ i : ι, ∑ j : κ, σ i * μ j * ‖L i j‖ ^ 2
  let b : ℝ :=
    ∑ i : ι, ∑ j : κ, σ i * μ j * ‖R i j‖ ^ 2
  have ha : 0 ≤ a := by
    dsimp [a]
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg
      (mul_nonneg (hσ i) (hμ j)) (sq_nonneg _)
  have hb : b ≤ 1 := by
    exact doublyStochasticSchmidtMass_le_one
      σ μ (fun i j => ‖R i j‖ ^ 2)
      hσunit hμunit
      (fun i j => sq_nonneg _)
      hRrow hRcol
  have hinnerbound : ‖inner ℂ ψ φ‖ ^ 2 ≤ a := by
    calc
      ‖inner ℂ ψ φ‖ ^ 2 =
          ‖inner ℂ
            (weightedComplexOverlapVector σ μ L)
            (weightedComplexOverlapVector σ μ R)‖ ^ 2 := by
              rw [hinner]
      _ ≤ ‖weightedComplexOverlapVector σ μ L‖ ^ 2 *
          ‖weightedComplexOverlapVector σ μ R‖ ^ 2 :=
            complexInner_norm_sq_le
              (weightedComplexOverlapVector σ μ L)
              (weightedComplexOverlapVector σ μ R)
      _ = a * b := by
            rw [weightedComplexOverlapVector_norm_sq
              σ μ hσ hμ L,
              weightedComplexOverlapVector_norm_sq
                σ μ hσ hμ R]
      _ ≤ a := by nlinarith
  have hre : (inner ℂ ψ φ).re ^ 2 ≤ a := by
    calc
      (inner ℂ ψ φ).re ^ 2 =
          (inner ℂ ψ φ).re * (inner ℂ ψ φ).re := by ring
      _ ≤ Complex.normSq (inner ℂ ψ φ) :=
        Complex.re_sq_le_normSq (inner ℂ ψ φ)
      _ = ‖inner ℂ ψ φ‖ ^ 2 :=
        Complex.normSq_eq_norm_sq (inner ℂ ψ φ)
      _ ≤ a := hinnerbound
  have hdistance :
      ‖ψ - φ‖ ^ 2 = 2 - 2 * (inner ℂ ψ φ).re := by
    rw [@norm_sub_sq ℂ, hψ, hφ]
    change
      1 ^ 2 - 2 * (inner ℂ ψ φ).re + 1 ^ 2 =
        2 - 2 * (inner ℂ ψ φ).re
    ring
  rw [doublyStochasticSchmidtEnergy_eq
    σ μ (fun i j => ‖L i j‖ ^ 2)
    hσunit hμunit hLrow hLcol, hdistance]
  change 2 - 2 * a ≤ 2 *
    (2 - 2 * (inner ℂ ψ φ).re)
  linarith [sq_nonneg ((inner ℂ ψ φ).re - 1)]

/-- The target object for tensor embezzlement. -/
def tensorEmbezzlementTarget
    {d n : ℕ} (ξ : BipartiteUnitVector d) :
    EuclideanSpace ℂ (Fin (d * n) × Fin (d * n)) :=
  toLp 2 fun q : Fin (d * n) × Fin (d * n) =>
    let a : Fin d × Fin n := finProdFinEquiv.symm q.1
    let b : Fin d × Fin n := finProdFinEquiv.symm q.2
    ξ.val (a.1, b.1) * embezzlementState n (a.2, b.2)

theorem tensorEmbezzlementTarget_norm
    {d n : ℕ} (hn : 0 < n)
    (ξ : BipartiteUnitVector d) :
    ‖tensorEmbezzlementTarget (n := n) ξ‖ = 1 := by
  classical
  let e : ((Fin d × Fin d) × (Fin n × Fin n)) ≃
      (Fin (d * n) × Fin (d * n)) :=
    (Equiv.prodProdProdComm (Fin d) (Fin d) (Fin n) (Fin n)).trans
      (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
  have hpoint (p : (Fin d × Fin d) × (Fin n × Fin n)) :
      tensorEmbezzlementTarget (n := n) ξ (e p) =
        ξ.val p.1 * embezzlementState n p.2 := by
    rcases p with ⟨⟨a, b⟩, ⟨c, f⟩⟩
    change
      ξ.val
        ((finProdFinEquiv.symm (finProdFinEquiv (a, c))).1,
          (finProdFinEquiv.symm (finProdFinEquiv (b, f))).1) *
        embezzlementState n
          ((finProdFinEquiv.symm (finProdFinEquiv (a, c))).2,
            (finProdFinEquiv.symm (finProdFinEquiv (b, f))).2) =
        ξ.val (a, b) * embezzlementState n (c, f)
    simp only [Equiv.symm_apply_apply]
  have hsum :
      (∑ q : Fin (d * n) × Fin (d * n),
        ‖tensorEmbezzlementTarget (n := n) ξ q‖ ^ 2) =
      ∑ p : (Fin d × Fin d) × (Fin n × Fin n),
        ‖ξ.val p.1 * embezzlementState n p.2‖ ^ 2 := by
    calc
      (∑ q : Fin (d * n) × Fin (d * n),
        ‖tensorEmbezzlementTarget (n := n) ξ q‖ ^ 2) =
        ∑ p : (Fin d × Fin d) × (Fin n × Fin n),
          ‖tensorEmbezzlementTarget (n := n) ξ (e p)‖ ^ 2 :=
            (Equiv.sum_comp e
              (fun q : Fin (d * n) × Fin (d * n) =>
                ‖tensorEmbezzlementTarget (n := n) ξ q‖ ^ 2)).symm
      _ = ∑ p : (Fin d × Fin d) × (Fin n × Fin n),
          ‖ξ.val p.1 * embezzlementState n p.2‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hpoint p]
  have hfactor :
      (∑ p : (Fin d × Fin d) × (Fin n × Fin n),
        ‖ξ.val p.1 * embezzlementState n p.2‖ ^ 2) =
      (∑ a : Fin d × Fin d, ‖ξ.val a‖ ^ 2) *
        (∑ b : Fin n × Fin n,
          ‖embezzlementState n b‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    simp_rw [norm_mul, mul_pow]
    exact (Fintype.sum_mul_sum
      (fun a : Fin d × Fin d => ‖ξ.val a‖ ^ 2)
      (fun b : Fin n × Fin n =>
        ‖embezzlementState n b‖ ^ 2)).symm
  have hsquare :
      ‖tensorEmbezzlementTarget (n := n) ξ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, hsum, hfactor,
      ← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq,
      ξ.property, embezzlementState_norm n hn]
    norm_num
  nlinarith [norm_nonneg (tensorEmbezzlementTarget (n := n) ξ)]

/-- The operator action for local unitary. -/
def localUnitaryAction {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n × Fin n)) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  toLp 2
    (((U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)).mulVec (ofLp ψ))

theorem localUnitaryAction_matrix_mem_unitary {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    ((U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)) ∈
        Matrix.unitaryGroup (Fin n × Fin n) ℂ := by
  exact Matrix.kronecker_mem_unitary U.property V.property

theorem localUnitaryAction_norm {n : ℕ}
    (U V : Matrix.unitaryGroup (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖localUnitaryAction U V ψ‖ = ‖ψ‖ := by
  let M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
    (U : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (V : Matrix (Fin n) (Fin n) ℂ)
  have hM : M ∈ Matrix.unitaryGroup (Fin n × Fin n) ℂ :=
    localUnitaryAction_matrix_mem_unitary U V
  have hclm : Matrix.toEuclideanCLM
      (n := Fin n × Fin n) (𝕜 := ℂ) M ∈
      unitary
        (EuclideanSpace ℂ (Fin n × Fin n) →L[ℂ]
          EuclideanSpace ℂ (Fin n × Fin n)) :=
    Unitary.map_mem
      (Matrix.toEuclideanCLM (n := Fin n × Fin n) (𝕜 := ℂ)) hM
  exact ContinuousLinearMap.norm_map_of_mem_unitary hclm ψ

theorem unitary_row_norm_sq_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (i : d) :
    (∑ j : d, ‖U i j‖ ^ 2) = 1 := by
  have hnorm (z : ℂ) :
      z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h := congrArg
    (fun M : Matrix d d ℂ => (M i i).re) U.property.2
  simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg,
    sub_neg_eq_add, hnorm, Matrix.one_apply_eq, Complex.one_re] using h

theorem unitary_col_norm_sq_sum
    {d : Type*} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (j : d) :
    (∑ i : d, ‖U i j‖ ^ 2) = 1 := by
  have hnorm (z : ℂ) :
      z.re * z.re + z.im * z.im = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h := congrArg
    (fun M : Matrix d d ℂ => (M j j).re) U.property.1
  simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.re_sum, Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul,
    sub_neg_eq_add, hnorm, Matrix.one_apply_eq, Complex.one_re] using h

/-- The overlap quantity for unitary basis. -/
def unitaryBasisOverlap
    {d : Type*} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) :
    Matrix.unitaryGroup d ℂ := U⁻¹ * V

/-- The quantum state representing diagonal schmidt. -/
def diagonalSchmidtState
    {d : Type*} [DecidableEq d]
    (σ : d → ℝ) : EuclideanSpace ℂ (d × d) :=
  toLp 2 fun q : d × d =>
    if q.1 = q.2 then (σ q.1 : ℂ) else 0

theorem diagonalSchmidtState_norm_sq
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ : d → ℝ) :
    ‖diagonalSchmidtState σ‖ ^ 2 =
      ∑ i : d, σ i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change
    (∑ j : d, ‖if i = j then (σ i : ℂ) else 0‖ ^ 2) =
      σ i ^ 2
  have hterm (j : d) :
      ‖if i = j then (σ i : ℂ) else 0‖ ^ 2 =
        if i = j then σ i ^ 2 else 0 := by
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The state vector representing schmidt. -/
def schmidtVector
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  localUnitaryAction U V
    (diagonalSchmidtState σ)

theorem schmidtVector_norm_sq
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖schmidtVector σ U V‖ ^ 2 =
      ∑ i : Fin d, σ i ^ 2 := by
  rw [schmidtVector,
    localUnitaryAction_norm,
    diagonalSchmidtState_norm_sq]

theorem schmidtVector_apply
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) :
    schmidtVector σ U V (a, b) =
      ∑ i : Fin d, (σ i : ℂ) * U a i * V b i := by
  classical
  simp only [schmidtVector, localUnitaryAction, diagonalSchmidtState, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, mul_comm, ite_mul, zero_mul, Fintype.sum_prod_type,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_assoc]

theorem weightedComplexOverlapVector_inner
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (σ : ι → ℝ) (μ : κ → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hμ : ∀ j, 0 ≤ μ j)
    (L R : ι → κ → ℂ) :
    inner ℂ
      (weightedComplexOverlapVector σ μ
        (fun i j => star (L i j)))
      (weightedComplexOverlapVector σ μ R) =
        ∑ i : ι, ∑ j : κ,
          (σ i : ℂ) * (μ j : ℂ) * L i j * R i j := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    (∑ q : ι × κ,
      ((Real.sqrt (σ q.1 * μ q.2) : ℂ) * R q.1 q.2) *
        star ((Real.sqrt (σ q.1 * μ q.2) : ℂ) *
          star (L q.1 q.2))) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsqrt :
      (Real.sqrt (σ i * μ j) : ℂ) *
        (Real.sqrt (σ i * μ j) : ℂ) =
          (σ i : ℂ) * (μ j : ℂ) := by
    norm_cast
    exact Real.mul_self_sqrt (mul_nonneg (hσ i) (hμ j))
  calc
    ((Real.sqrt (σ i * μ j) : ℂ) * R i j) *
        star ((Real.sqrt (σ i * μ j) : ℂ) * star (L i j)) =
      ((Real.sqrt (σ i * μ j) : ℂ) * R i j) *
        ((Real.sqrt (σ i * μ j) : ℂ) * L i j) := by simp only [RCLike.star_def, star_mul',
                                                      Complex.conj_ofReal,
                                                      RingHomCompTriple.comp_apply,
                                                      RingHom.id_apply]
    _ =
      ((Real.sqrt (σ i * μ j) : ℂ) *
        (Real.sqrt (σ i * μ j) : ℂ)) *
          L i j * R i j := by ring
    _ = (σ i : ℂ) * (μ j : ℂ) * L i j * R i j := by
      rw [hsqrt]

theorem matrixVectorization_inner
    {d e : Type*} [Fintype d] [Fintype e]
    (X Y : Matrix d e ℂ) :
    inner ℂ (toLp 2 (Matrix.vec X))
      (toLp 2 (Matrix.vec Y)) =
        Matrix.trace (X.conjTranspose * Y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change
    Matrix.vec Y ⬝ᵥ star (Matrix.vec X) =
      Matrix.trace (X.conjTranspose * Y)
  rw [dotProduct_comm, Matrix.star_vec_dotProduct_vec]

theorem diagonalSchmidtState_eq_vec
    {d : Type*} [DecidableEq d]
    (σ : d → ℝ) :
    diagonalSchmidtState σ =
      toLp 2 (Matrix.vec (Matrix.diagonal fun i => (σ i : ℂ))) := by
  ext ⟨i, j⟩
  by_cases h : i = j
  · subst j
    simp only [diagonalSchmidtState, ↓reduceIte, Matrix.vec, Matrix.diagonal_apply_eq]
  · simp only [diagonalSchmidtState, h, ↓reduceIte, Matrix.vec, ne_eq, Ne.symm h,
      not_false_eq_true, Matrix.diagonal_apply_ne]

theorem schmidtVector_eq_vec
    {d : ℕ}
    (σ : Fin d → ℝ)
    (U V : Matrix.unitaryGroup (Fin d) ℂ) :
    schmidtVector σ U V =
      toLp 2
        (Matrix.vec
          ((V : Matrix (Fin d) (Fin d) ℂ) *
            Matrix.diagonal (fun i => (σ i : ℂ)) *
            (U : Matrix (Fin d) (Fin d) ℂ).transpose)) := by
  rw [schmidtVector, localUnitaryAction,
    diagonalSchmidtState_eq_vec]
  apply WithLp.ofLp_injective
  exact Matrix.kronecker_mulVec_vec
    (V : Matrix (Fin d) (Fin d) ℂ)
    (Matrix.diagonal (fun i => (σ i : ℂ)))
    (U : Matrix (Fin d) (Fin d) ℂ)

theorem weightedSchmidtMatrixTrace
    {d : Type*} [Fintype d] [DecidableEq d]
    (σ μ : d → ℝ) (L R : Matrix d d ℂ) :
    Matrix.trace
      (L.transpose *
        Matrix.diagonal (fun i => (σ i : ℂ)) *
        R * Matrix.diagonal (fun j => (μ j : ℂ))) =
      ∑ i : d, ∑ j : d,
        (σ i : ℂ) * (μ j : ℂ) * L i j * R i j := by
  classical
  simp only [Matrix.trace, mul_assoc, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    mul_comm, mul_left_comm, Finset.sum_ite_eq]
  rw [Finset.sum_comm]

theorem schmidtVector_inner
    {d : ℕ}
    (σ μ : Fin d → ℝ)
    (U V X Y : Matrix.unitaryGroup (Fin d) ℂ) :
    inner ℂ
      (schmidtVector σ U V)
      (schmidtVector μ X Y) =
        ∑ i : Fin d, ∑ j : Fin d,
          (σ i : ℂ) * (μ j : ℂ) *
            (((U : Matrix (Fin d) (Fin d) ℂ).conjTranspose *
              (X : Matrix (Fin d) (Fin d) ℂ)) i j) *
            (((V : Matrix (Fin d) (Fin d) ℂ).conjTranspose *
              (Y : Matrix (Fin d) (Fin d) ℂ)) i j) := by
  classical
  rw [schmidtVector_eq_vec σ U V,
    schmidtVector_eq_vec μ X Y,
    matrixVectorization_inner]
  let S : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal fun i => (σ i : ℂ)
  let T : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal fun i => (μ i : ℂ)
  let A : Matrix (Fin d) (Fin d) ℂ := U
  let B : Matrix (Fin d) (Fin d) ℂ := V
  let C : Matrix (Fin d) (Fin d) ℂ := X
  let D : Matrix (Fin d) (Fin d) ℂ := Y
  change
    Matrix.trace ((B * S * A.transpose).conjTranspose *
      (D * T * C.transpose)) = _
  calc
    Matrix.trace ((B * S * A.transpose).conjTranspose *
        (D * T * C.transpose)) =
      Matrix.trace
        (((B * S * A.transpose).conjTranspose *
          (D * T)) * C.transpose) := by
            congr 1
            simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul]
    _ = Matrix.trace
        (C.transpose *
          ((B * S * A.transpose).conjTranspose * (D * T))) :=
            Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        ((A.conjTranspose * C).transpose * S *
          (B.conjTranspose * D) * T) := by
            congr 1
            simp only [Matrix.mul_assoc, Matrix.conjTranspose_mul, Matrix.transpose_conjTranspose,
              RCLike.star_def, Matrix.diagonal_conjTranspose, Pi.star_def, Complex.conj_ofReal,
              Matrix.transpose_mul, Matrix.conjTranspose_transpose, S]
    _ = _ := weightedSchmidtMatrixTrace
      σ μ (A.conjTranspose * C) (B.conjTranspose * D)

@[simp] theorem unitaryBasisOverlap_apply
    {d : Type*} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) (i j : d) :
    unitaryBasisOverlap U V i j =
      (((U : Matrix d d ℂ).conjTranspose *
        (V : Matrix d d ℂ)) i j) := by
  rfl

theorem schmidtVector_spectralEnergy_le
    {d : ℕ}
    (σ μ : Fin d → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hμ : ∀ j, 0 ≤ μ j)
    (hσunit : (∑ i : Fin d, σ i ^ 2) = 1)
    (hμunit : (∑ j : Fin d, μ j ^ 2) = 1)
    (U V X Y : Matrix.unitaryGroup (Fin d) ℂ) :
    (∑ i : Fin d, ∑ j : Fin d,
      (σ i - μ j) ^ 2 *
        ‖unitaryBasisOverlap U X i j‖ ^ 2) ≤
      2 * ‖schmidtVector σ U V -
        schmidtVector μ X Y‖ ^ 2 := by
  have hψ : ‖schmidtVector σ U V‖ = 1 := by
    have h := schmidtVector_norm_sq σ U V
    rw [hσunit] at h
    nlinarith [norm_nonneg (schmidtVector σ U V)]
  have hφ : ‖schmidtVector μ X Y‖ = 1 := by
    have h := schmidtVector_norm_sq μ X Y
    rw [hμunit] at h
    nlinarith [norm_nonneg (schmidtVector μ X Y)]
  let L : Fin d → Fin d → ℂ :=
    fun i j => star (unitaryBasisOverlap U X i j)
  let R : Fin d → Fin d → ℂ :=
    fun i j => unitaryBasisOverlap V Y i j
  have hLrow : ∀ i, (∑ j : Fin d, ‖L i j‖ ^ 2) = 1 := by
    intro i
    simpa [L] using
      unitary_row_norm_sq_sum
        (unitaryBasisOverlap U X) i
  have hLcol : ∀ j, (∑ i : Fin d, ‖L i j‖ ^ 2) = 1 := by
    intro j
    simpa [L] using
      unitary_col_norm_sq_sum
        (unitaryBasisOverlap U X) j
  have hRrow : ∀ i, (∑ j : Fin d, ‖R i j‖ ^ 2) = 1 := by
    intro i
    exact unitary_row_norm_sq_sum
      (unitaryBasisOverlap V Y) i
  have hRcol : ∀ j, (∑ i : Fin d, ‖R i j‖ ^ 2) = 1 := by
    intro j
    exact unitary_col_norm_sq_sum
      (unitaryBasisOverlap V Y) j
  have hinner :
      inner ℂ (schmidtVector σ U V)
          (schmidtVector μ X Y) =
        inner ℂ
          (weightedComplexOverlapVector σ μ L)
          (weightedComplexOverlapVector σ μ R) := by
    rw [weightedComplexOverlapVector_inner
      σ μ hσ hμ
      (fun i j => unitaryBasisOverlap U X i j)
      (fun i j => unitaryBasisOverlap V Y i j)]
    simpa only [unitaryBasisOverlap_apply] using
      schmidtVector_inner σ μ U V X Y
  simpa [L] using
    twoSidedSchmidtSpectralEnergy_le
      (schmidtVector σ U V)
      (schmidtVector μ X Y)
      hψ hφ σ μ hσ hμ hσunit hμunit L R
      hLrow hLcol hRrow hRcol hinner

end

section

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

theorem linearMap_exists_singularBases
    {d : ℕ}
    (T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d)) :
    ∃ (σ : Fin d → ℝ)
      (u v : OrthonormalBasis (Fin d) ℂ
        (EuclideanSpace ℂ (Fin d))),
      (∀ i, 0 ≤ σ i) ∧
        (∀ i, T (v i) = (σ i : ℂ) • u i) := by
  classical
  let hT := T.isPositive_adjoint_comp_self
  let v : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)) :=
    hT.isSymmetric.eigenvectorBasis finrank_euclideanSpace_fin
  let σ : Fin d → ℝ := fun i =>
    Real.sqrt
      (hT.isSymmetric.eigenvalues finrank_euclideanSpace_fin i)
  have hσ (i : Fin d) : 0 ≤ σ i := Real.sqrt_nonneg _
  have hσsq (i : Fin d) :
      σ i ^ 2 =
        hT.isSymmetric.eigenvalues finrank_euclideanSpace_fin i := by
    exact Real.sq_sqrt
      (hT.nonneg_eigenvalues finrank_euclideanSpace_fin i)
  have heigen (i : Fin d) :
      (T.adjoint ∘ₗ T) (v i) = ((σ i ^ 2 : ℝ) : ℂ) • v i := by
    rw [hσsq]
    exact hT.isSymmetric.apply_eigenvectorBasis
      finrank_euclideanSpace_fin i
  let s : Set (Fin d) := {i | σ i ≠ 0}
  let f : Fin d → EuclideanSpace ℂ (Fin d) :=
    fun i => ((σ i : ℂ)⁻¹) • T (v i)
  have hGram (i j : Fin d) :
      inner ℂ (T (v i)) (T (v j)) =
        ((σ j ^ 2 : ℝ) : ℂ) *
          inner ℂ (v i) (v j) := by
    calc
      inner ℂ (T (v i)) (T (v j)) =
          inner ℂ (v i) (T.adjoint (T (v j))) :=
        (T.adjoint_inner_right (v i) (T (v j))).symm
      _ = inner ℂ (v i)
          (((σ j ^ 2 : ℝ) : ℂ) • v j) := by
        rw [← heigen j]
        rfl
      _ = ((σ j ^ 2 : ℝ) : ℂ) *
          inner ℂ (v i) (v j) := by
        rw [inner_smul_right]
  have hf : Orthonormal ℂ (s.domRestrict f) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (σ (i : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast i.property
    have hj : (σ (j : Fin d) : ℂ) ≠ 0 := by
      exact_mod_cast j.property
    change inner ℂ
      (((σ (i : Fin d) : ℂ)⁻¹) • T (v i))
      (((σ (j : Fin d) : ℂ)⁻¹) • T (v j)) = _
    rw [inner_smul_left, inner_smul_right, hGram,
      v.inner_eq_ite]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, mul_one]
      have hs :
          starRingEnd ℂ ((σ (i : Fin d) : ℂ)⁻¹) =
            ((σ (i : Fin d) : ℂ)⁻¹) := by
        simp only [map_inv₀, conj_ofReal]
      rw [hs]
      push_cast
      field_simp
    · have hval : (i : Fin d) ≠ (j : Fin d) := by
        intro h
        exact hij (Subtype.ext h)
      simp only [map_inv₀, conj_ofReal, ofReal_pow, hval, ↓reduceIte, mul_zero, hij]
  obtain ⟨u, hu⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (by
        rw [Fintype.card_fin]
        exact finrank_euclideanSpace_fin) hf
  refine ⟨σ, u, v, hσ, ?_⟩
  intro i
  by_cases hi : σ i = 0
  · have hker : (T.adjoint ∘ₗ T) (v i) = 0 := by
      rw [heigen i, hi]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ofReal_zero, zero_smul]
    have hTv : T (v i) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← T.ker_adjoint_comp_self]
      exact LinearMap.mem_ker.mpr hker
    simp only [hTv, hi, ofReal_zero, zero_smul]
  · have hui : u i = f i := hu i hi
    rw [hui]
    change T (v i) =
      (σ i : ℂ) • (((σ i : ℂ)⁻¹) • T (v i))
    rw [smul_smul, mul_inv_cancel₀]
    · simp only [one_smul]
    · exact_mod_cast hi

end

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

/-- The unitary operator implementing orthonormal basis. -/
def orthonormalBasisUnitary
    {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d))) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis,
    (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

@[simp] theorem orthonormalBasisUnitary_apply
    {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ
      (EuclideanSpace ℂ (Fin d)))
    (i j : Fin d) :
    orthonormalBasisUnitary b i j = b j i := by
  rfl

/-- The unitary operator implementing conjugate. -/
def conjugateUnitary
    {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix.unitaryGroup (Fin d) ℂ := by
  refine ⟨(U.val.conjTranspose).transpose, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff']
  change
    ((U.val.conjTranspose).transpose).conjTranspose *
      (U.val.conjTranspose).transpose = 1
  have htranspose :
      ((U.val.conjTranspose).transpose).conjTranspose =
        U.val.transpose := by
    ext i j
    simp only [conjTranspose_apply, transpose_apply, RCLike.star_def,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [htranspose]
  have h := congrArg Matrix.transpose U.property.1
  simpa only [star_eq_conjTranspose, transpose_mul, transpose_one] using h

@[simp] theorem conjugateUnitary_apply
    {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    conjugateUnitary U i j = star (U i j) := by
  rfl

theorem exists_proofSchmidtDecomposition
    {d : ℕ}
    (ξ : EuclideanSpace ℂ (Fin d × Fin d)) :
    ∃ (σ : Fin d → ℝ)
      (U V : Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, 0 ≤ σ i) ∧
        ξ = schmidtVector σ U V := by
  classical
  let C : Matrix (Fin d) (Fin d) ℂ := fun b a => ξ (a, b)
  let T : EuclideanSpace ℂ (Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d) := Matrix.toEuclideanLin C
  obtain ⟨σ, u, v, hσ, hsing⟩ :=
    linearMap_exists_singularBases T
  refine ⟨σ,
    conjugateUnitary (orthonormalBasisUnitary v),
    orthonormalBasisUnitary u, hσ, ?_⟩
  ext ⟨a, b⟩
  rw [schmidtVector_apply]
  have hrepr :
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
        ∑ i : Fin d,
          inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
            T (v i) := by
    calc
      T ((EuclideanSpace.basisFun (Fin d) ℂ) a) =
          T (∑ i : Fin d,
            inner ℂ (v i) ((EuclideanSpace.basisFun (Fin d) ℂ) a) •
              v i) := by
        rw [v.sum_repr']
      _ = _ := by
        simp only [EuclideanSpace.basisFun_apply, map_sum, map_smul]
  have hcoord := congrArg
    (fun z : EuclideanSpace ℂ (Fin d) => z b) hrepr
  change (((Matrix.toLpLin 2 2 C)
    ((EuclideanSpace.basisFun (Fin d) ℂ) a)).ofLp b) = _ at hcoord
  rw [Matrix.ofLp_toLpLin] at hcoord
  rw [EuclideanSpace.basisFun_apply, PiLp.ofLp_single] at hcoord
  rw [Matrix.toLin'_apply] at hcoord
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at hcoord
  simpa [C, EuclideanSpace.basisFun_apply,
    EuclideanSpace.inner_single_right,
    conjugateUnitary_apply,
    orthonormalBasisUnitary_apply, hsing,
    mul_assoc, mul_left_comm, mul_comm] using hcoord

theorem exists_proofUnitSchmidtDecomposition
    {d : ℕ}
    (ξ : BipartiteUnitVector d) :
    ∃ (σ : Fin d → ℝ)
      (U V : Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, 0 ≤ σ i) ∧
        (∑ i : Fin d, σ i ^ 2) = 1 ∧
        ξ.val = schmidtVector σ U V := by
  obtain ⟨σ, U, V, hσ, hξ⟩ :=
    exists_proofSchmidtDecomposition ξ.val
  refine ⟨σ, U, V, hσ, ?_, hξ⟩
  have hnorm : ‖schmidtVector σ U V‖ ^ 2 = 1 := by
    rw [← hξ, ξ.property]
    norm_num
  exact (schmidtVector_norm_sq σ U V).symm.trans hnorm

end

end QuantumParallelRepetition

end
