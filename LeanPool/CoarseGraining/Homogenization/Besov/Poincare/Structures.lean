/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Negative
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.GlobalComparison
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.MeanInequalities

/-! # Structures -/

@[expose] public section

namespace Homogenization


open scoped BigOperators ENNReal

/-- Descendant-local analytic input for the finite-depth multiscale Poincare corridor. -/
def CubeMultiscalePoincareInput {d : ℕ} (Q : TriadicCube d)
    (C : ℝ) (u g : Vec d → ℝ) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
      C * ∑ n ∈ Finset.range (M - j + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n

theorem CubeMultiscalePoincareInput.bound {d : ℕ} {Q : TriadicCube d}
    {C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hinput : CubeMultiscalePoincareInput Q C u g M) :
    ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
        C * ∑ n ∈ Finset.range (M - j + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n :=
  hinput

/-- Concrete descendant-local multiscale Poincare hypothesis phrased with the
`q = 1` concrete circ norm on each descendant cube. -/
def CubeLocalMultiscalePoincareEstimate {d : ℕ} (Q : TriadicCube d)
    (C : ℝ) (u g : Vec d → ℝ) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
      C * cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) g

theorem CubeLocalMultiscalePoincareEstimate.to_input {d : ℕ} {Q : TriadicCube d}
    {C : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hlocal : CubeLocalMultiscalePoincareEstimate Q C u g M) :
    CubeMultiscalePoincareInput Q C u g M := by
  intro j hj R hR
  calc
    cubeBesovOscillation R (2 : ℝ≥0∞) u
        ≤ C * cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) g :=
          hlocal j hj R hR
    _ = C * ∑ n ∈ Finset.range (M - j + 1), cubeBesovCircDepthSeminorm R 1 (2 : ℝ≥0∞) g n := by
          simp [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm]

/-- Single-cube analytic Poincare estimate phrased with the true dual mean-zero
negative Besov seminorm at the `s = 1`, `p = 2`, `q = 1` endpoint. This is the
black-box form of the note's `l.multiscale.Poincare.function.spaces` before
passing to the concrete circ norm. -/
def CubeDualMeanZeroPoincareEstimate {d : ℕ} (Q : TriadicCube d)
    (C : ℝ) (u g : Vec d → ℝ) : Prop :=
  cubeBesovOscillation Q (2 : ℝ≥0∞) u ≤
    C * cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g

theorem CubeDualMeanZeroPoincareEstimate.to_circNorm {d : ℕ} {Q : TriadicCube d}
    {C : ℝ} {u g : Vec d → ℝ}
    (hdual : CubeDualMeanZeroPoincareEstimate Q C u g)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hC : 0 ≤ C) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) u ≤
      C * (3 : ℝ) ^ ((d : ℝ) + 1) *
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g := by
  have hconj_eq :
      cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hdual_le :
      cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g ≤
        (3 : ℝ) ^ ((d : ℝ) + 1) * cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g := by
    exact cubeBesovDualMeanZeroSeminorm_le_note_constant_mul_cubeBesovCircNorm
      (Q := Q) (s := 1) (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞)) (u := g)
      (by norm_num) hg (by norm_num) (by norm_num)
      (by
        intro htop
        simp [hconj_eq] at htop)
      (by norm_num)
  calc
    cubeBesovOscillation Q (2 : ℝ≥0∞) u
        ≤ C * cubeBesovDualMeanZeroSeminorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g := hdual
    _ ≤ C * ((3 : ℝ) ^ ((d : ℝ) + 1) * cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g) := by
          exact mul_le_mul_of_nonneg_left hdual_le hC
    _ = C * (3 : ℝ) ^ ((d : ℝ) + 1) *
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g := by
          ring

theorem CubeDualMeanZeroPoincareEstimate.fluctuation_le_circNorm
    {d : ℕ} {Q : TriadicCube d} {C : ℝ} {u g : Vec d → ℝ}
    (hdual : CubeDualMeanZeroPoincareEstimate Q C u g)
    (hg : MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hC : 0 ≤ C) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
      C * (3 : ℝ) ^ ((d : ℝ) + 1) *
        cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g := by
  simpa [cubeBesovOscillation] using hdual.to_circNorm hg hC

/-- Descendant-local analytic input packaging the single-cube dual mean-zero
Poincare estimate together with the local `L²` admissibility and the
finite-depth comparison from the full circ norm to the concrete `q = 1`
partial circ norm on each descendant. This is the theorem-surface bridge from
the single-cube analytic lemma to `CubeLocalMultiscalePoincareEstimate`. -/
def CubeDescendantDualMeanZeroPoincareInput {d : ℕ} (Q : TriadicCube d)
    (C K : ℝ) (u g : Vec d → ℝ) (M : ℕ) : Prop :=
  ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
    CubeDualMeanZeroPoincareEstimate R C u g ∧
      MeasureTheory.MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure R) ∧
      cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g ≤
        K * cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) g

theorem CubeDescendantDualMeanZeroPoincareInput.to_localEstimate
    {d : ℕ} {Q : TriadicCube d} {C K : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hinput : CubeDescendantDualMeanZeroPoincareInput Q C K u g M)
    (hC : 0 ≤ C) :
    CubeLocalMultiscalePoincareEstimate Q
      (C * (3 : ℝ) ^ ((d : ℝ) + 1) * K) u g M := by
  intro j hj R hR
  rcases hinput j hj R hR with ⟨hdual, hg, htail⟩
  have hnote_nonneg : 0 ≤ C * (3 : ℝ) ^ ((d : ℝ) + 1) := by
    exact mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  calc
    cubeBesovOscillation R (2 : ℝ≥0∞) u
        ≤ C * (3 : ℝ) ^ ((d : ℝ) + 1) *
            cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) g :=
          hdual.to_circNorm hg hC
    _ ≤ C * (3 : ℝ) ^ ((d : ℝ) + 1) *
          (K * cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) g) := by
          exact mul_le_mul_of_nonneg_left htail hnote_nonneg
    _ = (C * (3 : ℝ) ^ ((d : ℝ) + 1) * K) *
          cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) g := by
          ring

theorem CubeDescendantDualMeanZeroPoincareInput.to_input
    {d : ℕ} {Q : TriadicCube d} {C K : ℝ} {u g : Vec d → ℝ} {M : ℕ}
    (hinput : CubeDescendantDualMeanZeroPoincareInput Q C K u g M)
    (hC : 0 ≤ C) :
    CubeMultiscalePoincareInput Q
      (C * (3 : ℝ) ^ ((d : ℝ) + 1) * K) u g M := by
  exact (hinput.to_localEstimate hC).to_input

end Homogenization
