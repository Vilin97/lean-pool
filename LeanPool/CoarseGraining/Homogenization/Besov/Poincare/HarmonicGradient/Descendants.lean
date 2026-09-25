/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.HarmonicGradient.Definitions

/-! # Descendants -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

variable {d : ℕ}

/-! # Descendant APIs for Vector Poincare Estimates -/

/-- Enlarge the constant in the projected vector Poincare estimate. -/
theorem CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate.mono_C
    {Q : TriadicCube d} {C₁ C₂ : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    {M : ℕ}
    (h :
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C₁ u G M)
    (hC : C₁ ≤ C₂) :
    CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C₂ u G M := by
  intro j hj R hR
  have hsum_nonneg :
      0 ≤
        ∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection R (M - j) (fun x => G x i)) := by
    have hconj_eq :
        cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq
          (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
    refine Finset.sum_nonneg ?_
    intro i _
    exact cubeBesovDualMeanZeroSeminorm_nonneg R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
      (cubeProjection R (M - j) (fun x => G x i))
      (by rw [hconj_eq]; norm_num)
      (by rw [hconj_eq]; norm_num)
  exact le_trans (h j hj R hR)
    (mul_le_mul_of_nonneg_right hC hsum_nonneg)

/-- Assemble descendant projected vector Poincare from one-cube projected
estimates on every descendant. The only rewrite is that subtracting the parent
cube average does not change oscillation on the descendant. -/
theorem CubeProjectedDualMeanZeroVectorPoincareEstimate.to_descendant
    {Q : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d} {M : ℕ}
    (hu :
      ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hlocal :
      ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
        CubeProjectedDualMeanZeroVectorPoincareEstimate R C u G (M - j)) :
    CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C
      (cubeFluctuation Q u) G M := by
  intro j hj R hR
  have hosc :
      cubeBesovOscillation R (2 : ℝ≥0∞) (cubeFluctuation Q u) =
        cubeBesovOscillation R (2 : ℝ≥0∞) u :=
    cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two R Q (hu j hj R hR)
  rw [hosc]
  exact hlocal j hj R hR

/-- Restrict a descendant projected vector Poincare estimate to one of the
parent cube's descendants.  The depth bookkeeping is the same as in the
scalar projected Poincare corridor: a depth-`n` descendant of `R` is a
depth-`j + n` descendant of `Q`. -/
theorem CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate.restrict_to_descendant
    {Q R : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    {M j : ℕ}
    (hproj :
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C u G M)
    (hR : R ∈ descendantsAtDepth Q j) (hj : j ≤ M) :
    CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C u G (M - j) := by
  intro n hn S hS
  have hn_le : n ≤ M - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hjn_le : j + n ≤ M := by
    simpa [Nat.add_sub_of_le hj] using Nat.add_le_add_left hn_le j
  have hSQ : S ∈ descendantsAtDepth Q (j + n) := mem_descendantsAtDepth_add hR hS
  have hmem : j + n ∈ Finset.range (M + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjn_le)
  have hbase := hproj (j + n) hmem S hSQ
  have hsub : M - (j + n) = (M - j) - n := by
    omega
  simpa [hsub] using hbase

/-- Localize a parent cube projected vector Poincare family to a descendant
cube while recentering the fluctuation from the parent average to the local
descendant average. -/
theorem CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate.restrict_fluctuation_to_descendant
    {Q R : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hu :
      ∀ n : ℕ, ∀ S ∈ descendantsAtDepth R n,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure S))
    (hproj : ∀ M : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate Q C
        (cubeFluctuation Q u) G M) :
    ∀ N : ℕ,
      CubeDescendantProjectedDualMeanZeroVectorPoincareEstimate R C
        (cubeFluctuation R u) G N := by
  intro N n hn S hS
  have hn_le : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hSQ : S ∈ descendantsAtDepth Q (j + n) := mem_descendantsAtDepth_add hR hS
  have hmem : j + n ∈ Finset.range (j + N + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.add_le_add_left hn_le j))
  have hbase := hproj (j + N) (j + n) hmem S hSQ
  have huS : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure S) := hu n S hS
  have hoscR :
      cubeBesovOscillation S (2 : ℝ≥0∞) (cubeFluctuation R u) =
        cubeBesovOscillation S (2 : ℝ≥0∞) u :=
    cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two S R huS
  have hoscQ :
      cubeBesovOscillation S (2 : ℝ≥0∞) (cubeFluctuation Q u) =
        cubeBesovOscillation S (2 : ℝ≥0∞) u :=
    cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two S Q huS
  have hsub : j + N - (j + n) = N - n := by
    omega
  calc
    cubeBesovOscillation S (2 : ℝ≥0∞) (cubeFluctuation R u)
        = cubeBesovOscillation S (2 : ℝ≥0∞) u := hoscR
    _ = cubeBesovOscillation S (2 : ℝ≥0∞) (cubeFluctuation Q u) := hoscQ.symm
    _ ≤ C * ∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm S 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection S (j + N - (j + n)) (fun x => G x i)) := hbase
    _ = C * ∑ i : Fin d,
          cubeBesovDualMeanZeroSeminorm S 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (cubeProjection S (N - n) (fun x => G x i)) := by
          rw [hsub]

/-- Assemble the descendant infinite-depth vector Poincare estimate from
one-cube infinite-depth estimates on every descendant. -/
theorem CubeDualMeanZeroVectorPoincareEstimate.to_descendant
    {Q : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d} {M : ℕ}
    (hu :
      ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hlocal :
      ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
        CubeDualMeanZeroVectorPoincareEstimate R C u G) :
    CubeDescendantDualMeanZeroVectorPoincareEstimate Q C
      (cubeFluctuation Q u) G M := by
  intro j hj R hR
  have hosc :
      cubeBesovOscillation R (2 : ℝ≥0∞) (cubeFluctuation Q u) =
        cubeBesovOscillation R (2 : ℝ≥0∞) u :=
    cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two R Q (hu j hj R hR)
  rw [hosc]
  exact hlocal j hj R hR

/-- Assemble the descendant full-dual vector Poincare estimate from one-cube
full-dual estimates on every descendant. -/
theorem CubeDualFullVectorPoincareEstimate.to_descendant
    {Q : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d} {M : ℕ}
    (hu :
      ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hlocal :
      ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
        CubeDualFullVectorPoincareEstimate R C u G) :
    CubeDescendantDualFullVectorPoincareEstimate Q C
      (cubeFluctuation Q u) G M := by
  intro j hj R hR
  have hosc :
      cubeBesovOscillation R (2 : ℝ≥0∞) (cubeFluctuation Q u) =
        cubeBesovOscillation R (2 : ℝ≥0∞) u :=
    cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two R Q (hu j hj R hR)
  rw [hosc]
  exact hlocal j hj R hR

/-- Enlarge the constant in the descendant full-dual vector Poincare estimate. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.mono_C
    {Q : TriadicCube d} {C₁ C₂ : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    {M : ℕ}
    (hfull : CubeDescendantDualFullVectorPoincareEstimate Q C₁ u G M)
    (hC : C₁ ≤ C₂) :
    CubeDescendantDualFullVectorPoincareEstimate Q C₂ u G M := by
  intro j hj R hR
  have hsum_nonneg :
      0 ≤ ∑ i : Fin d,
        cubeBesovDualFullNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => G x i) := by
    have hconj_eq :
        cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
      simpa [cubeBesovConjExponent] using
        (ENNReal.HolderConjugate.conjExponent_eq
          (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
    refine Finset.sum_nonneg ?_
    intro i _
    exact cubeBesovDualFullNorm_nonneg R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
      (fun x => G x i)
      (by rw [hconj_eq]; norm_num)
      (by rw [hconj_eq]; norm_num)
  exact le_trans (hfull j hj R hR)
    (mul_le_mul_of_nonneg_right hC hsum_nonneg)

/-- Restrict a descendant full-dual vector Poincare estimate to one of the
parent cube's descendants. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.restrict_to_descendant
    {Q R : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    {M j : ℕ}
    (hfull : CubeDescendantDualFullVectorPoincareEstimate Q C u G M)
    (hR : R ∈ descendantsAtDepth Q j) (hj : j ≤ M) :
    CubeDescendantDualFullVectorPoincareEstimate R C u G (M - j) := by
  intro n hn S hS
  have hn_le : n ≤ M - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hjn_le : j + n ≤ M := by
    simpa [Nat.add_sub_of_le hj] using Nat.add_le_add_left hn_le j
  have hSQ : S ∈ descendantsAtDepth Q (j + n) := mem_descendantsAtDepth_add hR hS
  have hmem : j + n ∈ Finset.range (M + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjn_le)
  simpa using hfull (j + n) hmem S hSQ

/-- Localize a parent cube full-dual vector Poincare family to a descendant
cube while recentering the fluctuation from the parent average to the local
descendant average. -/
theorem CubeDescendantDualFullVectorPoincareEstimate.restrict_fluctuation_to_descendant
    {Q R : TriadicCube d} {C : ℝ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hu :
      ∀ n : ℕ, ∀ S ∈ descendantsAtDepth R n,
        MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure S))
    (hfull : ∀ M : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q C
        (cubeFluctuation Q u) G M) :
    ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate R C
        (cubeFluctuation R u) G N := by
  intro N n hn S hS
  have hn_le : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have hSQ : S ∈ descendantsAtDepth Q (j + n) := mem_descendantsAtDepth_add hR hS
  have hmem : j + n ∈ Finset.range (j + N + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.add_le_add_left hn_le j))
  have hbase := hfull (j + N) (j + n) hmem S hSQ
  have huS : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure S) := hu n S hS
  have hoscR :
      cubeBesovOscillation S (2 : ℝ≥0∞) (cubeFluctuation R u) =
        cubeBesovOscillation S (2 : ℝ≥0∞) u :=
    cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two S R huS
  have hoscQ :
      cubeBesovOscillation S (2 : ℝ≥0∞) (cubeFluctuation Q u) =
        cubeBesovOscillation S (2 : ℝ≥0∞) u :=
    cubeBesovOscillation_cubeFluctuation_eq_of_memLp_two S Q huS
  calc
    cubeBesovOscillation S (2 : ℝ≥0∞) (cubeFluctuation R u)
        = cubeBesovOscillation S (2 : ℝ≥0∞) u := hoscR
    _ = cubeBesovOscillation S (2 : ℝ≥0∞) (cubeFluctuation Q u) := hoscQ.symm
    _ ≤ C * ∑ i : Fin d,
          cubeBesovDualFullNorm S 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => G x i) := hbase

end Homogenization
