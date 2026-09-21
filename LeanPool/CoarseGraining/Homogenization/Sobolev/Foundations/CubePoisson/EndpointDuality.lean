/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson.DualTestNorm
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliVectorization

/-! # Endpoint Duality -/

namespace Homogenization

open scoped BigOperators ENNReal Topology

/-!
# Endpoint Besov-duality interfaces for Poisson-gradient pairings

The endpoint Besov duality definitions used by the cube-local Poincare
arguments, together with the conversions between projected and full-dual
surfaces. The `to_l2Endpoint` and `of_dualTestNorm…` lemmas wire
these surfaces to the Calderon-Zygmund and dual-test-norm estimates from
sibling files.
-/

/-- Endpoint Besov duality input, specialized to the projected gradient terms
that occur in the one-cube vector Poincare proof. -/
def CubeProjectedGradientEndpointDuality {d : ℕ} (Q : TriadicCube d) (C : ℝ) :
    Prop :=
  0 ≤ C ∧
    ∀ (N : ℕ) (G : Vec d → Vec d) (Ψ : Vec d → Vec d),
      (∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) →
      (∀ i : Fin d,
        MeasureTheory.MemLp (fun x => Ψ x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) →
      ∑ i : Fin d,
          |cubeBesovPairing Q
            (cubeProjection Q N (fun x => G x i))
            (fun x => Ψ x i)| ≤
        C *
          (∑ i : Fin d,
            cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (cubeProjection Q N (fun x => G x i))) *
          (∑ i : Fin d,
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
              (fun x => Ψ x i))

/-- Endpoint Besov duality input for the full, unprojected gradient terms used
by the infinite-depth vector Poincare theorem. -/
def CubeGradientEndpointDuality {d : ℕ} (Q : TriadicCube d) (C : ℝ) :
    Prop :=
  0 ≤ C ∧
    ∀ (G : Vec d → Vec d) (Ψ : Vec d → Vec d),
      (∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) →
      (∀ i : Fin d,
        MeasureTheory.MemLp (fun x => Ψ x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) →
      ∑ i : Fin d,
          |cubeBesovPairing Q
            (fun x => G x i)
            (fun x => Ψ x i)| ≤
        C *
          (∑ i : Fin d,
            cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i)) *
          (∑ i : Fin d,
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
              (fun x => Ψ x i))

/-- Constant-mode-safe endpoint Besov duality input for the Poisson-gradient
test fields that occur in the infinite-depth vector Poincare proof.

This is the corrected replacement surface for arbitrary `H¹` inputs: the first
factor is measured by the full dual norm, so constant gradient modes are not
discarded. -/
def CubePoissonGradientFullEndpointDuality {d : ℕ} (Q : TriadicCube d) (C : ℝ) :
    Prop :=
  0 ≤ C ∧
    ∀ (F : Vec d → ℝ)
      (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
      (_hmean : cubeAverage Q F = 0)
      (W : MeanZeroNeumannPoissonSolution Q F)
      (G : Vec d → Vec d),
      (∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) →
      ∑ i : Fin d,
          |cubeBesovPairing Q
            (fun x => G x i)
            (fun x => W.w.toH1Function.grad x i)| ≤
        C *
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i)) *
          (∑ i : Fin d,
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
              (fun x => W.w.toH1Function.grad x i))

/-- L²-facing full-dual endpoint Besov duality input for Poisson-gradient
test fields.

This packages the combination of full-dual scalar pairing and positive
test-norm control after the Neumann CZ estimate has already converted the
Poisson-gradient side to the normalized `L²` size of the right-hand side. -/
def CubePoissonGradientFullL2EndpointDuality {d : ℕ} (Q : TriadicCube d) (C : ℝ) :
    Prop :=
  0 ≤ C ∧
    ∀ (F : Vec d → ℝ)
      (_hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
      (_hmean : cubeAverage Q F = 0)
      (W : MeanZeroNeumannPoissonSolution Q F)
      (G : Vec d → Vec d),
      (∀ i : Fin d,
        MeasureTheory.MemLp (fun x => G x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) →
      ∑ i : Fin d,
          |cubeBesovPairing Q
            (fun x => G x i)
            (fun x => W.w.toH1Function.grad x i)| ≤
        C *
          (∑ i : Fin d,
            cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => G x i)) *
          cubeLpNorm Q (2 : ℝ≥0∞) F

theorem CubePoissonGradientFullEndpointDuality.to_l2Endpoint
    {d : ℕ} {Q : TriadicCube d} {Cdual Ccz : ℝ}
    (hdual : CubePoissonGradientFullEndpointDuality Q Cdual)
    (hcz : CubeNeumannPoissonGradientBesovEstimate Q Ccz) :
    CubePoissonGradientFullL2EndpointDuality Q (Cdual * Ccz) := by
  refine ⟨mul_nonneg hdual.1 hcz.1, ?_⟩
  intro F hF hmean W G hG
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hp0 : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
    simp [hconj]
  have hpTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    simp [hconj]
  let A : ℝ :=
    ∑ i : Fin d,
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => G x i)
  let S : ℝ :=
    ∑ i : Fin d,
      cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i)
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  have hA_nonneg : 0 ≤ A := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact cubeBesovDualFullNorm_nonneg
      Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i) hp0 hpTop
  have hpair :
      ∑ i : Fin d,
          |cubeBesovPairing Q
            (fun x => G x i)
            (fun x => W.w.toH1Function.grad x i)| ≤
        Cdual * A * S := by
    simpa [A, S] using hdual.2 F hF hmean W G hG
  have hcz_bound : S ≤ Ccz * L := by
    simpa [S, L] using hcz.2 F hF hmean W
  calc
    ∑ i : Fin d,
        |cubeBesovPairing Q
          (fun x => G x i)
          (fun x => W.w.toH1Function.grad x i)|
        ≤ Cdual * A * S := hpair
    _ ≤ Cdual * A * (Ccz * L) := by
          exact mul_le_mul_of_nonneg_left hcz_bound (mul_nonneg hdual.1 hA_nonneg)
    _ = (Cdual * Ccz) * A * L := by ring

theorem CubePoissonGradientFullEndpointDuality.of_dualTestNormEstimate
    {d : ℕ} {Q : TriadicCube d} {C : ℝ}
    (h : CubePoissonGradientDualTestNormEstimate Q C) :
    CubePoissonGradientFullEndpointDuality Q C := by
  refine ⟨h.1, ?_⟩
  intro F hF hmean W G hG
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hp0 : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
    simp [hconj]
  have hpTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    simp [hconj]
  have hdualNonneg :
      ∀ i : Fin d,
        0 ≤ cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
    intro i
    exact cubeBesovDualFullNorm_nonneg
      Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i) hp0 hpTop
  let A : ℝ :=
    ∑ i : Fin d,
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => G x i)
  let S : ℝ :=
    ∑ i : Fin d,
      cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (∞ : ℝ≥0∞)
        (fun x => W.w.toH1Function.grad x i)
  have hA_nonneg : 0 ≤ A := by
    exact Finset.sum_nonneg (fun i _hi => hdualNonneg i)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (A + 1)
  have hA1_pos : 0 < A + 1 := by linarith
  have hδ_pos : 0 < δ := div_pos hε hA1_pos
  rcases h.2 F hF hmean W δ hδ_pos with ⟨B, hB_pos, hnorm, hmem, hB_sum⟩
  have hpair :
      ∑ i : Fin d,
          |cubeBesovPairing Q
            (fun x => G x i)
            (fun x => W.w.toH1Function.grad x i)| ≤
        A * ∑ i : Fin d, B i := by
    simpa [A] using
      sum_abs_cubeBesovPairing_le_sum_dualFullNorm_mul_sum_bounds_two_one
        Q 1 G (fun x => W.w.toH1Function.grad x) B (by norm_num)
        hG hB_pos hnorm hmem hdualNonneg
  have hAδ_le : A * δ ≤ ε := by
    have hratio : A / (A + 1) ≤ 1 := by
      exact (div_le_one hA1_pos).mpr (by linarith)
    calc
      A * δ = ε * (A / (A + 1)) := by
        dsimp [δ]
        field_simp [ne_of_gt hA1_pos]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := by ring
  calc
    ∑ i : Fin d,
        |cubeBesovPairing Q
          (fun x => G x i)
          (fun x => W.w.toH1Function.grad x i)|
        ≤ A * ∑ i : Fin d, B i := hpair
    _ ≤ A * (C * S + δ) := by
          exact mul_le_mul_of_nonneg_left (by simpa [S] using hB_sum) hA_nonneg
    _ = C * A * S + A * δ := by ring
    _ ≤ C * A * S + ε := by linarith

theorem CubePoissonGradientFullL2EndpointDuality.of_dualTestNormL2Estimate
    {d : ℕ} {Q : TriadicCube d} {C : ℝ}
    (h : CubePoissonGradientDualTestNormL2Estimate Q C) :
    CubePoissonGradientFullL2EndpointDuality Q C := by
  refine ⟨h.1, ?_⟩
  intro F hF hmean W G hG
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq
        (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hp0 : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
    simp [hconj]
  have hpTop : cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
    simp [hconj]
  have hdualNonneg :
      ∀ i : Fin d,
        0 ≤ cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
    intro i
    exact cubeBesovDualFullNorm_nonneg
      Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => G x i) hp0 hpTop
  let A : ℝ :=
    ∑ i : Fin d,
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => G x i)
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) F
  have hA_nonneg : 0 ≤ A := by
    exact Finset.sum_nonneg (fun i _hi => hdualNonneg i)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (A + 1)
  have hA1_pos : 0 < A + 1 := by linarith
  have hδ_pos : 0 < δ := div_pos hε hA1_pos
  rcases h.2 F hF hmean W δ hδ_pos with ⟨B, hB_pos, hnorm, hmem, hB_sum⟩
  have hpair :
      ∑ i : Fin d,
          |cubeBesovPairing Q
            (fun x => G x i)
            (fun x => W.w.toH1Function.grad x i)| ≤
        A * ∑ i : Fin d, B i := by
    simpa [A] using
      sum_abs_cubeBesovPairing_le_sum_dualFullNorm_mul_sum_bounds_two_one
        Q 1 G (fun x => W.w.toH1Function.grad x) B (by norm_num)
        hG hB_pos hnorm hmem hdualNonneg
  have hAδ_le : A * δ ≤ ε := by
    have hratio : A / (A + 1) ≤ 1 := by
      exact (div_le_one hA1_pos).mpr (by linarith)
    calc
      A * δ = ε * (A / (A + 1)) := by
        dsimp [δ]
        field_simp [ne_of_gt hA1_pos]
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := by ring
  calc
    ∑ i : Fin d,
        |cubeBesovPairing Q
          (fun x => G x i)
          (fun x => W.w.toH1Function.grad x i)|
        ≤ A * ∑ i : Fin d, B i := hpair
    _ ≤ A * (C * L + δ) := by
          exact mul_le_mul_of_nonneg_left (by simpa [L] using hB_sum) hA_nonneg
    _ = C * A * L + A * δ := by ring
    _ ≤ C * A * L + ε := by linarith

end Homogenization
