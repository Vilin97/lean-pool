/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszLinearityDecay
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.FourierTestDerivatives
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureTestBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.R3.RieszPairing

/-!
# The pressure-difference functional on Schwartz tests

The coefficients of the velocity terms belong to ordinary `L²`, and the
tensor coefficients belong to `L¹`. All pairings below are actual Lebesgue
integrals. The final functional uses the spatial Laplacian and coordinate
derivatives from the equation, and the double Riesz test operator.
-/

@[expose] public section



noncomputable section

open MeasureTheory
open scoped BigOperators

namespace NavierStokesR3.PressureFunctionals

open ProblemStatement Comparison HarmonicTestFunctionals PressureTestBounds

/-- Pairing an `L²` coefficient with a Schwartz test is integrable. -/
theorem integrable_l2_pair {W : Space → ℝ} (hW : MemLp W 2) (ψ : ComplexTest) :
    Integrable (fun x : Space => (W x : ℂ) * ψ x) := by
  have hprod : Integrable (fun x : Space => ‖W x‖ * ‖ψ x‖) :=
    hW.norm.integrable_mul (ψ.memLp 2).norm
  apply hprod.mono'
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hW.1).mul
      ψ.continuous.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by simp [Complex.norm_real]

/-- Cauchy--Schwarz for the actual coefficient/test pairing. -/
theorem norm_l2_pair_le {W : Space → ℝ} (hW : MemLp W 2) (ψ : ComplexTest) :
    ‖∫ x : Space, (W x : ℂ) * ψ x‖ ≤
      Real.sqrt (l2Sq W) * Real.sqrt (l2Sq (ψ : Space → ℂ)) := by
  calc
    ‖∫ x : Space, (W x : ℂ) * ψ x‖ ≤ ∫ x : Space, ‖(W x : ℂ) * ψ x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : Space, ‖W x‖ * ‖ψ x‖ := by simp only [norm_mul, Complex.norm_real]
    _ ≤ _ := by
      have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure Space))
        (f := fun x => ‖W x‖) (g := fun x => ‖ψ x‖) Real.HolderConjugate.two_two
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (by simpa using hW.norm) (by simpa using (ψ.memLp 2).norm)
      simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, l2Sq] using h

/-- An `L¹` coefficient may be paired with any Schwartz test. -/
theorem integrable_l1_pair {g : Space → ℝ} (hg : Integrable g) (ψ : ComplexTest) :
    Integrable (fun x : Space => (g x : ℂ) * ψ x) := by
  have hgc : Integrable (fun x : Space => (g x : ℂ)) :=
    Complex.ofRealCLM.integrable_comp hg
  have h := hgc.bdd_mul ψ.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_test_le_integral_fourier ψ))
  simpa only [mul_comm] using h

/-- The canonical pressure pairing is finite for an `L¹` coefficient. -/
theorem integrable_l1_riesz_pair {g : Space → ℝ} (hg : Integrable g)
    (i j : Fin 3) (ψ : ComplexTest) :
    Integrable (fun x : Space => (g x : ℂ) * rieszTest i j ψ x) :=
  RieszTestOperators.integrable_mul_rieszTest i j ψ
    (Complex.ofRealCLM.integrable_comp hg)

/-- A pointwise test bound gives the usual `L¹` pairing estimate. -/
theorem norm_l1_pair_le_of_bound {g : Space → ℝ} (hg : Integrable g)
    {f : Space → ℂ} (hf : Integrable (fun x : Space => (g x : ℂ) * f x))
    {B : ℝ} (hB : ∀ x : Space, ‖f x‖ ≤ B) :
    ‖∫ x : Space, (g x : ℂ) * f x‖ ≤ (∫ x : Space, ‖g x‖) * B := by
  calc
    ‖∫ x : Space, (g x : ℂ) * f x‖ ≤ ∫ x : Space, ‖(g x : ℂ) * f x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Space, ‖g x‖ * B := by
      apply integral_mono hf.norm (hg.norm.mul_const B)
      intro x
      change ‖(g x : ℂ) * f x‖ ≤ ‖g x‖ * B
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
    _ = (∫ x : Space, ‖g x‖) * B := integral_mul_const _ _

/-- The ordinary inclusion of Schwartz tests into complex-valued functions. -/
noncomputable def testValueLinear : ComplexTest →ₗ[ℂ] (Space → ℂ) where
  toFun ψ := ψ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Integrating a linear family of tests against a fixed coefficient is linear
when every displayed integrand is integrable. -/
def integralPairLinear (g : Space → ℝ) (T : ComplexTest →ₗ[ℂ] (Space → ℂ))
    (hint : ∀ ψ : ComplexTest, Integrable (fun x : Space => (g x : ℂ) * T ψ x)) :
    ComplexTest →ₗ[ℂ] ℂ where
  toFun ψ := ∫ x : Space, (g x : ℂ) * T ψ x
  map_add' ψ φ := by
    simp only [map_add, Pi.add_apply, mul_add]
    exact integral_add (hint ψ) (hint φ)
  map_smul' c ψ := by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    calc
      (∫ x : Space, (g x : ℂ) * (c * T ψ x)) =
          ∫ x : Space, c * ((g x : ℂ) * T ψ x) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = c * ∫ x : Space, (g x : ℂ) * T ψ x := integral_const_mul _ _

/-- The linear `L²` coefficient pairing. -/
def l2PairLinear (W : Space → ℝ) (hW : MemLp W 2) : ComplexTest →ₗ[ℂ] ℂ :=
  integralPairLinear W testValueLinear (integrable_l2_pair hW)

/-- The linear `L¹` coefficient pairing. -/
def l1PairLinear (g : Space → ℝ) (hg : Integrable g) : ComplexTest →ₗ[ℂ] ℂ :=
  integralPairLinear g testValueLinear (integrable_l1_pair hg)

@[simp] theorem l2PairLinear_apply (W : Space → ℝ) (hW : MemLp W 2) (ψ : ComplexTest) :
    l2PairLinear W hW ψ = ∫ x : Space, (W x : ℂ) * ψ x := rfl

@[simp] theorem l1PairLinear_apply (g : Space → ℝ) (hg : Integrable g) (ψ : ComplexTest) :
    l1PairLinear g hg ψ = ∫ x : Space, (g x : ℂ) * ψ x := rfl

/-- The coefficients are the two time averages of velocity and the time average
of the quadratic tensor in the conservative pressure equation. -/
def averagedPressureDifferenceValue (W0 W1 : Space → ℝ)
    (G : Fin 3 → Fin 3 → Space → ℝ) (k : Fin 3) (ψ : ComplexTest) : ℂ :=
  (∫ x : Space, (W0 x : ℂ) * laplacianCLM ψ x) +
    (∫ x : Space, (W1 x : ℂ) * ψ x) +
    (∑ i : Fin 3, ∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x) +
    ∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)

/-- Every term of the pressure-difference functional is an integrable pairing. -/
theorem integrable_terms {W0 W1 : Space → ℝ} {G : Fin 3 → Fin 3 → Space → ℝ}
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) (ψ : ComplexTest) :
    Integrable (fun x : Space => (W0 x : ℂ) * laplacianCLM ψ x) ∧
      Integrable (fun x : Space => (W1 x : ℂ) * ψ x) ∧
      (∀ i : Fin 3, Integrable (fun x : Space => (G k i x : ℂ) * partialCLM i ψ x)) ∧
      (∀ i j : Fin 3, Integrable (fun x : Space =>
        (G i j x : ℂ) * rieszTest i j (partialCLM k ψ) x)) := by
  exact ⟨integrable_l2_pair hW0 (laplacianCLM ψ), integrable_l2_pair hW1 ψ,
    fun i => integrable_l1_pair (hG k i) (partialCLM i ψ),
    fun i j => integrable_l1_riesz_pair (hG i j) i j (partialCLM k ψ)⟩

theorem l2_pair_laplacian_eq_sum {W : Space → ℝ} (hW : MemLp W 2)
    (ψ : ComplexTest) :
    (∫ x : Space, (W x : ℂ) * laplacianCLM ψ x) =
      ∑ i : Fin 3, ∫ x : Space, (W x : ℂ) * partialCLM i (partialCLM i ψ) x := by
  change l2PairLinear W hW (laplacianCLM ψ) = _
  simp only [laplacianCLM, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    map_sum, l2PairLinear_apply]

theorem norm_l2_laplacian_pair_le {W : Space → ℝ} (hW : MemLp W 2)
    (ψ : ComplexTest) {B : ℝ}
    (hB : ∀ i : Fin 3,
      Real.sqrt (l2Sq (partialCLM i (partialCLM i ψ) : Space → ℂ)) ≤ B) :
    ‖∫ x : Space, (W x : ℂ) * laplacianCLM ψ x‖ ≤ 3 * Real.sqrt (l2Sq W) * B := by
  rw [l2_pair_laplacian_eq_sum hW ψ]
  calc
    ‖∑ i : Fin 3, ∫ x : Space, (W x : ℂ) * partialCLM i (partialCLM i ψ) x‖ ≤
        ∑ i : Fin 3, ‖∫ x : Space, (W x : ℂ) * partialCLM i (partialCLM i ψ) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, Real.sqrt (l2Sq W) * B := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_l2_pair_le hW (partialCLM i (partialCLM i ψ))).trans
        (mul_le_mul_of_nonneg_left (hB i) (Real.sqrt_nonneg _))
    _ = 3 * Real.sqrt (l2Sq W) * B := by simp [mul_assoc]

/-- The actual pressure-difference expression is bounded by the Fourier `H³`
norm, with a constant depending only on the given coefficients. -/
theorem averagedPressureDifferenceValue_bound {W0 W1 : Space → ℝ}
    {G : Fin 3 → Fin 3 → Space → ℝ}
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ComplexTest,
      ‖averagedPressureDifferenceValue W0 W1 G k ψ‖ ≤ C * Real.sqrt (fourierHNormSq 3 ψ) := by
  obtain ⟨B, hB, htest⟩ := exists_uniform_test_bound
  let M := 3 * Real.sqrt (l2Sq W0) + Real.sqrt (l2Sq W1) +
    (∑ i : Fin 3, ∫ x : Space, ‖G k i x‖) +
    ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space, ‖G i j x‖
  have hmass (i j : Fin 3) : 0 ≤ ∫ x : Space, ‖G i j x‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hrow : 0 ≤ ∑ i : Fin 3, ∫ x : Space, ‖G k i x‖ :=
    Finset.sum_nonneg fun i _ => hmass k i
  have hall : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space, ‖G i j x‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hmass i j
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M * B, mul_nonneg hM hB, ?_⟩
  intro ψ
  obtain ⟨hbase, hsecond, hfirst, hriesz⟩ := htest ψ
  have h0 := norm_l2_laplacian_pair_le hW0 ψ hsecond
  have h1 : ‖∫ x : Space, (W1 x : ℂ) * ψ x‖ ≤
      Real.sqrt (l2Sq W1) * (B * Real.sqrt (fourierHNormSq 3 ψ)) :=
    (norm_l2_pair_le hW1 ψ).trans
      (mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg _))
  have hrow_bound :
      ‖∑ i : Fin 3, ∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x‖ ≤
        (∑ i : Fin 3, ∫ x : Space, ‖G k i x‖) * (B * Real.sqrt (fourierHNormSq 3 ψ)) := by
    calc
      ‖∑ i : Fin 3, ∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x‖ ≤
          ∑ i : Fin 3, ‖∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, (∫ x : Space, ‖G k i x‖) *
          (B * Real.sqrt (fourierHNormSq 3 ψ)) := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_l1_pair_le_of_bound (hG k i)
          (integrable_l1_pair (hG k i) (partialCLM i ψ)) (hfirst i)
      _ = _ := by rw [Finset.sum_mul]
  have hpressure_bound :
      ‖∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)‖ ≤
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space, ‖G i j x‖) *
          (B * Real.sqrt (fourierHNormSq 3 ψ)) := by
    calc
      ‖∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)‖ ≤
          ∑ i : Fin 3, ‖∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖pressurePair i j (G i j) (partialCLM k ψ)‖ :=
        Finset.sum_le_sum fun _ _ => norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, (∫ x : Space, ‖G i j x‖) *
          (B * Real.sqrt (fourierHNormSq 3 ψ)) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact norm_l1_pair_le_of_bound (hG i j)
          (integrable_l1_riesz_pair (hG i j) i j (partialCLM k ψ)) (hriesz i j k)
      _ = _ := by simp only [Finset.sum_mul]
  have htriangle : ‖averagedPressureDifferenceValue W0 W1 G k ψ‖ ≤
      ‖∫ x : Space, (W0 x : ℂ) * laplacianCLM ψ x‖ +
      ‖∫ x : Space, (W1 x : ℂ) * ψ x‖ +
      ‖∑ i : Fin 3, ∫ x : Space, (G k i x : ℂ) * partialCLM i ψ x‖ +
      ‖∑ i : Fin 3, ∑ j : Fin 3, pressurePair i j (G i j) (partialCLM k ψ)‖ := by
    exact (norm_add_le _ _).trans (add_le_add_left
      ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _)
  calc
    ‖averagedPressureDifferenceValue W0 W1 G k ψ‖ ≤ _ := htriangle
    _ ≤ 3 * Real.sqrt (l2Sq W0) * (B * Real.sqrt (fourierHNormSq 3 ψ)) +
        Real.sqrt (l2Sq W1) * (B * Real.sqrt (fourierHNormSq 3 ψ)) +
        (∑ i : Fin 3, ∫ x : Space, ‖G k i x‖) * (B * Real.sqrt (fourierHNormSq 3 ψ)) +
        (∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Space, ‖G i j x‖) *
          (B * Real.sqrt (fourierHNormSq 3 ψ)) :=
      add_le_add (add_le_add (add_le_add h0 h1) hrow_bound) hpressure_bound
    _ = (M * B) * Real.sqrt (fourierHNormSq 3 ψ) := by dsimp [M]; ring

/-- The canonical pressure pairing, as an actual complex-linear map on tests. -/
def pressurePairLinear (i j : Fin 3) (g : Space → ℝ) (hg : Integrable g) :
    ComplexTest →ₗ[ℂ] ℂ :=
  integralPairLinear g (RieszTestOperators.rieszTestLinear i j)
    (integrable_l1_riesz_pair hg i j)

@[simp] theorem pressurePairLinear_apply (i j : Fin 3) (g : Space → ℝ)
    (hg : Integrable g) (ψ : ComplexTest) :
    pressurePairLinear i j g hg ψ = pressurePair i j g ψ := rfl

/-- The averaged pressure-gradient difference determined by the stated
velocity and quadratic-tensor coefficients. -/
def averagedPressureDifference (W0 W1 : Space → ℝ)
    (G : Fin 3 → Fin 3 → Space → ℝ)
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) :
    ComplexTest →ₗ[ℂ] ℂ :=
  (l2PairLinear W0 hW0).comp laplacianCLM.toLinearMap +
    l2PairLinear W1 hW1 +
    (∑ i : Fin 3, (l1PairLinear (G k i) (hG k i)).comp (partialCLM i).toLinearMap) +
    ∑ i : Fin 3, ∑ j : Fin 3,
      (pressurePairLinear i j (G i j) (hG i j)).comp (partialCLM k).toLinearMap

@[simp] theorem averagedPressureDifference_apply (W0 W1 : Space → ℝ)
    (G : Fin 3 → Fin 3 → Space → ℝ)
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) (ψ : ComplexTest) :
    averagedPressureDifference W0 W1 G hW0 hW1 hG k ψ =
      averagedPressureDifferenceValue W0 W1 G k ψ := by
  simp only [averagedPressureDifference, averagedPressureDifferenceValue,
    LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    l2PairLinear_apply, l1PairLinear_apply, pressurePairLinear_apply]
  rfl

/-- The actual complex-linear functional satisfies a uniform `H³` estimate. -/
theorem averagedPressureDifference_bound {W0 W1 : Space → ℝ}
    {G : Fin 3 → Fin 3 → Space → ℝ}
    (hW0 : MemLp W0 2) (hW1 : MemLp W1 2)
    (hG : ∀ i j : Fin 3, Integrable (G i j)) (k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : ComplexTest,
      ‖averagedPressureDifference W0 W1 G hW0 hW1 hG k ψ‖ ≤
        C * Real.sqrt (fourierHNormSq 3 ψ) := by
  simpa only [averagedPressureDifference_apply] using
    averagedPressureDifferenceValue_bound hW0 hW1 hG k

end NavierStokesR3.PressureFunctionals
