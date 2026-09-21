/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.BesovEstimate

/-! # Dual Test Norm -/

namespace Homogenization

open scoped BigOperators ENNReal Topology

/-!
# Positive dual test-norm estimates for Poisson gradients

The endpoint inputs that the full-dual Besov pairing proof actually uses: each
component of the Poisson gradient admits a positive uniform bound for all
finite-depth dual test norms. The L²-facing wrapper combines this with the
Calderon-Zygmund estimate, and the core wrapper packages the epsilon-free clean
componentwise estimate into the positive `B`-bundle used downstream.
-/

/-- Positive-test-norm control for Poisson gradients.

This is the endpoint input that the full-dual Besov pairing proof actually
uses: each component of the Poisson gradient admits a positive uniform bound
for all finite-depth dual test norms, and the sum of those bounds is controlled
by the `B¹_{2,∞}` circ norm of the Poisson gradient up to an arbitrary
epsilon. The epsilon slack keeps the zero-gradient case available while still
implying the exact endpoint duality bound by a limiting argument. -/
def CubePoissonGradientDualTestNormEstimate {d : ℕ} (Q : TriadicCube d) (C : ℝ) :
    Prop :=
  0 ≤ C ∧
    ∀ (F : Vec d → ℝ)
      (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
      (_hmean : cubeAverage Q F = 0)
      (W : MeanZeroNeumannPoissonSolution Q F)
      (ε : ℝ) (_hε : 0 < ε),
      ∃ B : Fin d → ℝ,
        (∀ i : Fin d, 0 < B i) ∧
        (∀ i : Fin d, ∀ N : ℕ,
          cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun x => W.w.toH1Function.grad x i) ≤
            B i) ∧
        (∀ i : Fin d,
          CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
            (fun x => W.w.toH1Function.grad x i)) ∧
        ∑ i : Fin d, B i ≤
          C * ∑ i : Fin d,
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
              (fun x => W.w.toH1Function.grad x i) + ε

/-- L²-facing positive-test-norm control for Poisson gradients.

This is the form obtained after composing the positive-test/circ estimate with
the Neumann Calderon-Zygmund estimate. It is closer to the elliptic regularity
statement that remains to be proved: the admissible positive Besov test bounds
for `∇W` are controlled directly by the normalized `L²` norm of the right-hand
side. -/
def CubePoissonGradientDualTestNormL2Estimate {d : ℕ} (Q : TriadicCube d) (C : ℝ) :
    Prop :=
  0 ≤ C ∧
    ∀ (F : Vec d → ℝ)
      (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
      (_hmean : cubeAverage Q F = 0)
      (W : MeanZeroNeumannPoissonSolution Q F)
      (ε : ℝ) (_hε : 0 < ε),
      ∃ B : Fin d → ℝ,
        (∀ i : Fin d, 0 < B i) ∧
        (∀ i : Fin d, ∀ N : ℕ,
          cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
              (fun x => W.w.toH1Function.grad x i) ≤
            B i) ∧
        (∀ i : Fin d,
          CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
            (fun x => W.w.toH1Function.grad x i)) ∧
        ∑ i : Fin d, B i ≤ C * cubeLpNorm Q (2 : ℝ≥0∞) F + ε

/-- Core direct `L²` positive-test bound for Poisson gradients.

This is the epsilon-free form one expects from Neumann `W^{2,2}`/CZ plus local
Poincare: each component of `∇W` has all finite positive dual test norms
bounded by the same multiple of `‖F‖_{L²(Q)}`. The theorem below turns this
clean componentwise estimate into the positive `B`-package used by the endpoint
duality wrapper. -/
def CubePoissonGradientDualTestNormL2CoreEstimate {d : ℕ}
    (Q : TriadicCube d) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ (F : Vec d → ℝ)
      (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
      (_hmean : cubeAverage Q F = 0)
      (W : MeanZeroNeumannPoissonSolution Q F),
      (∀ i : Fin d, ∀ N : ℕ,
        cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x => W.w.toH1Function.grad x i) ≤
          C * cubeLpNorm Q (2 : ℝ≥0∞) F) ∧
      (∀ i : Fin d,
        CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞)
          (fun x => W.w.toH1Function.grad x i))

theorem CubePoissonGradientDualTestNormL2CoreEstimate.to_l2Estimate
    {d : ℕ} {Q : TriadicCube d} {C : ℝ}
    (h : CubePoissonGradientDualTestNormL2CoreEstimate Q C) :
    CubePoissonGradientDualTestNormL2Estimate Q ((d : ℝ) * C) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg d) h.1, ?_⟩
  intro F hF hmean W ε hε
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  let δ : ℝ := ε / ((d : ℝ) + 1)
  let B : Fin d → ℝ := fun _ => C * L + δ
  have hδ_pos : 0 < δ := by
    exact div_pos hε (by positivity)
  have hCL_nonneg : 0 ≤ C * L := by
    exact mul_nonneg h.1 (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) F)
  rcases h.2 F hF hmean W with ⟨hnorm_core, hmem⟩
  refine ⟨B, ?_, ?_, hmem, ?_⟩
  · intro i
    exact add_pos_of_nonneg_of_pos hCL_nonneg hδ_pos
  · intro i N
    exact (hnorm_core i N).trans (le_add_of_nonneg_right hδ_pos.le)
  · have hdδ_le : (d : ℝ) * δ ≤ ε := by
      have hd1_pos : 0 < (d : ℝ) + 1 := by positivity
      have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
      have hratio : (d : ℝ) / ((d : ℝ) + 1) ≤ 1 := by
        exact (div_le_one hd1_pos).mpr (by linarith)
      calc
        (d : ℝ) * δ = ε * ((d : ℝ) / ((d : ℝ) + 1)) := by
          dsimp [δ]
          field_simp [ne_of_gt hd1_pos]
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
        _ = ε := by ring
    calc
      ∑ i : Fin d, B i
          = (d : ℝ) * (C * L + δ) := by
              simp [B]
              ring
      _ = ((d : ℝ) * C) * L + (d : ℝ) * δ := by ring
      _ ≤ ((d : ℝ) * C) * L + ε := by
            linarith
      _ = ((d : ℝ) * C) * cubeLpNorm Q (2 : ℝ≥0∞) F + ε := by
            simp [L]

theorem CubePoissonGradientDualTestNormEstimate.to_l2Estimate
    {d : ℕ} {Q : TriadicCube d} {Ctest Ccz : ℝ}
    (htest : CubePoissonGradientDualTestNormEstimate Q Ctest)
    (hcz : CubeNeumannPoissonGradientBesovEstimate Q Ccz) :
    CubePoissonGradientDualTestNormL2Estimate Q (Ctest * Ccz) := by
  refine ⟨mul_nonneg htest.1 hcz.1, ?_⟩
  intro F hF hmean W ε hε
  rcases htest.2 F hF hmean W ε hε with ⟨B, hB_pos, hnorm, hmem, hB_sum⟩
  refine ⟨B, hB_pos, hnorm, hmem, ?_⟩
  have hcz_bound :
      ∑ i : Fin d,
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
            (fun x => W.w.toH1Function.grad x i) ≤
        Ccz * cubeLpNorm Q (2 : ℝ≥0∞) F :=
    hcz.2 F hF hmean W
  calc
    ∑ i : Fin d, B i
        ≤ Ctest *
            (∑ i : Fin d,
              cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
                (fun x => W.w.toH1Function.grad x i)) + ε := hB_sum
    _ ≤ Ctest * (Ccz * cubeLpNorm Q (2 : ℝ≥0∞) F) + ε := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (mul_le_mul_of_nonneg_left hcz_bound htest.1) ε
    _ = (Ctest * Ccz) * cubeLpNorm Q (2 : ℝ≥0∞) F + ε := by ring

end Homogenization
