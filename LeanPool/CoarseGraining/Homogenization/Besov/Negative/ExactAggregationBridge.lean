/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Negative.ExactFiniteBridge

/-!
# Finite aggregation transport for exact negative Besov kernels

Source-neutral `ENNReal` transport lemmas for passing from finite real
aggregations to the extended finite and infinite aggregations used by the
exact Chapter 1 kernels.  They retain extended-value behavior without analytic
convergence or real-valued upper-bound hypotheses.
-/

namespace Homogenization

open scoped BigOperators ENNReal

/-- The `ENNReal` embedding of a nonnegative finite real `ℓ^q` expression is
the corresponding finite extended expression. -/
theorem exactAggregation_ofReal_finiteLq (a : ℕ → ℝ) (N : ℕ) (q : ℝ)
    (ha : ∀ i ∈ Finset.range (N + 1), 0 ≤ a i) (hq : 0 ≤ q) :
    ENNReal.ofReal
        ((Finset.sum (Finset.range (N + 1)) fun i => (a i) ^ q) ^ q⁻¹) =
      (Finset.sum (Finset.range (N + 1)) fun i => (ENNReal.ofReal (a i)) ^ q) ^ q⁻¹ := by
  rw [← ENNReal.ofReal_rpow_of_nonneg]
  · rw [ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [(ENNReal.ofReal_rpow_of_nonneg (ha i hi) hq).symm]
    · intro i hi
      exact Real.rpow_nonneg (ha i hi) q
  · exact Finset.sum_nonneg fun i hi => Real.rpow_nonneg (ha i hi) q
  · exact inv_nonneg.mpr hq

/-- A finite extended `ℓ^q` aggregation is bounded by its infinite `tsum`
aggregation.  This deliberately remains valid when the right side is `∞`. -/
theorem exactAggregation_finiteLq_le_tsum (a : ℕ → ℝ≥0∞) (N : ℕ) (q : ℝ)
    (hq : 0 ≤ q) :
    (Finset.sum (Finset.range (N + 1)) fun i => (a i) ^ q) ^ q⁻¹ ≤
      (∑' i : ℕ, (a i) ^ q) ^ q⁻¹ := by
  apply ENNReal.rpow_le_rpow
  · simpa using ENNReal.sum_le_tsum
      (f := fun i : ℕ => (a i) ^ q) (s := Finset.range (N + 1))
  · exact inv_nonneg.mpr hq

private def exactAggregationOfRealSupHom : SupHom ℝ ℝ≥0∞ :=
  ⟨ENNReal.ofReal, ENNReal.ofReal_max⟩

/-- The `ENNReal` embedding of a finite real maximum is bounded by the
extended `iSup` of the embedded terms. -/
theorem exactAggregation_ofReal_finiteSup_le_iSup (a : ℕ → ℝ) (N : ℕ) :
    ENNReal.ofReal ((Finset.range (N + 1)).sup' ⟨0, by simp⟩ a) ≤
      ⨆ i : ℕ, ENNReal.ofReal (a i) := by
  change exactAggregationOfRealSupHom
    ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one a) ≤ _
  rw [map_finset_sup' exactAggregationOfRealSupHom]
  apply Finset.sup'_le
  intro i hi
  simpa [Function.comp_apply] using! le_iSup (fun i : ℕ => ENNReal.ofReal (a i)) i

/-- A pointwise finite-term bridge transports a legacy finite real `ℓ^q`
aggregation directly into an infinite exact `tsum` aggregation. -/
theorem exactAggregation_ofReal_finiteLq_le_tsum_of_term_eq
    (a : ℕ → ℝ) (b : ℕ → ℝ≥0∞) (N : ℕ) (q : ℝ)
    (ha : ∀ i ∈ Finset.range (N + 1), 0 ≤ a i) (hq : 0 ≤ q)
    (hterm : ∀ i ∈ Finset.range (N + 1), ENNReal.ofReal (a i) = b i) :
    ENNReal.ofReal
        ((Finset.sum (Finset.range (N + 1)) fun i => (a i) ^ q) ^ q⁻¹) ≤
      (∑' i : ℕ, (b i) ^ q) ^ q⁻¹ := by
  calc
    ENNReal.ofReal
        ((Finset.sum (Finset.range (N + 1)) fun i => (a i) ^ q) ^ q⁻¹) =
        (Finset.sum (Finset.range (N + 1)) fun i => (ENNReal.ofReal (a i)) ^ q) ^ q⁻¹ :=
      exactAggregation_ofReal_finiteLq a N q ha hq
    _ = (Finset.sum (Finset.range (N + 1)) fun i => (b i) ^ q) ^ q⁻¹ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hterm i hi]
    _ ≤ (∑' i : ℕ, (b i) ^ q) ^ q⁻¹ :=
      exactAggregation_finiteLq_le_tsum b N q hq

/-- A pointwise finite-term bridge transports a legacy finite real maximum
directly into an exact extended `iSup`. -/
theorem exactAggregation_ofReal_finiteSup_le_iSup_of_term_eq
    (a : ℕ → ℝ) (b : ℕ → ℝ≥0∞) (N : ℕ)
    (hterm : ∀ i ∈ Finset.range (N + 1), ENNReal.ofReal (a i) = b i) :
    ENNReal.ofReal ((Finset.range (N + 1)).sup' ⟨0, by simp⟩ a) ≤
      ⨆ i : ℕ, b i := by
  change exactAggregationOfRealSupHom
    ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one a) ≤ _
  rw [map_finset_sup' exactAggregationOfRealSupHom]
  apply Finset.sup'_le
  intro i hi
  change ENNReal.ofReal (a i) ≤ _
  rw [hterm i hi]
  exact le_iSup b i

/-- A finite legacy overlap-positive `ℓ^q` truncation is dominated by the
exact extended overlap seminorm, with the parent `MemLp` data supplying the
canonical local-integrability witness. -/
theorem exactAggregation_overlapPartialSeminorm_le_exactOverlapFiniteSeminorm
    {d : ℕ} (P : ExactOverlapFiniteParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp u (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) (N : ℕ) :
    ENNReal.ofReal
        (cubeBesovOverlapPartialSeminorm Q P.s (ENNReal.ofReal P.p)
          (ENNReal.ofReal P.q) N u) ≤
      exactOverlapFiniteSeminorm P Q u
        (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) := by
  have hq0 : 0 ≤ P.q := zero_le_one.trans P.q_one_le
  simpa [cubeBesovOverlapPartialSeminorm, ENNReal.toReal_ofReal hq0, one_div,
    exactOverlapFiniteSeminorm_eq] using
    exactAggregation_ofReal_finiteLq_le_tsum_of_term_eq
      (a := fun j => cubeBesovOverlapDepthSeminorm Q P.s (ENNReal.ofReal P.p) u j)
      (b := fun j => exactOverlapDepthTerm Q P.s P.p u
        (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) j)
      N P.q
      (fun j _ => cubeBesovOverlapDepthSeminorm_nonneg Q P.s (ENNReal.ofReal P.p) u j)
      hq0
      (fun j _ =>
        (exactOverlapDepthTerm_eq_ofReal_cubeBesovOverlapDepthSeminorm Q P.s P.p
          P.p_one_le u hmem j).symm)

/-- A finite legacy overlap-positive supremum truncation is dominated by the
exact extended overlap endpoint seminorm. -/
theorem exactAggregation_overlapPartialSeminormTop_le_exactOverlapTopSeminorm
    {d : ℕ} (P : ExactOverlapTopParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp u (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) (N : ℕ) :
    ENNReal.ofReal
        (cubeBesovOverlapPartialSeminormTop Q P.s (ENNReal.ofReal P.p) N u) ≤
      exactOverlapTopSeminorm P Q u
        (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) := by
  simpa [cubeBesovOverlapPartialSeminormTop, exactOverlapTopSeminorm_eq] using
    exactAggregation_ofReal_finiteSup_le_iSup_of_term_eq
      (a := fun j => cubeBesovOverlapDepthSeminorm Q P.s (ENNReal.ofReal P.p) u j)
      (b := fun j => exactOverlapDepthTerm Q P.s P.p u
        (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) j)
      N
      (fun j _ =>
        (exactOverlapDepthTerm_eq_ofReal_cubeBesovOverlapDepthSeminorm Q P.s P.p
          P.p_one_le u hmem j).symm)

/-- The finite inhomogeneous overlap-positive truncation is dominated by the
exact extended norm; its root mean transports exactly. -/
theorem exactAggregation_overlapPartialNorm_le_exactOverlapFiniteNorm
    {d : ℕ} (P : ExactOverlapFiniteParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp u (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) (N : ℕ) :
    ENNReal.ofReal
        (cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal P.p)
          (ENNReal.ofReal P.q) N u) ≤
      exactOverlapFiniteNorm P Q u
        (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) := by
  have hsem := exactAggregation_overlapPartialSeminorm_le_exactOverlapFiniteSeminorm
    P Q u hmem N
  have hlegacySem : 0 ≤ cubeBesovOverlapPartialSeminorm Q P.s (ENNReal.ofReal P.p)
      (ENNReal.ofReal P.q) N u :=
    cubeBesovOverlapPartialSeminorm_nonneg Q P.s (ENNReal.ofReal P.p)
      (ENNReal.ofReal P.q) N u
  have hlegacyRoot : 0 ≤ cubeBesovScaleWeight P.s Q * ‖cubeAverage Q u‖ :=
    mul_nonneg (cubeBesovScaleWeight_nonneg P.s Q) (norm_nonneg _)
  calc
    ENNReal.ofReal
        (cubeBesovOverlapPartialNorm Q P.s (ENNReal.ofReal P.p)
          (ENNReal.ofReal P.q) N u) =
        ENNReal.ofReal
          (cubeBesovOverlapPartialSeminorm Q P.s (ENNReal.ofReal P.p)
            (ENNReal.ofReal P.q) N u) +
          exactOverlapRootWeight Q P.s * ENNReal.ofReal |cubeAverage Q u| := by
      rw [cubeBesovOverlapPartialNorm, ENNReal.ofReal_add hlegacySem hlegacyRoot,
        ENNReal.ofReal_mul (cubeBesovScaleWeight_nonneg P.s Q),
        ← exactOverlapRootWeight_eq_ofReal_legacy]
      simp [Real.norm_eq_abs]
    _ ≤ exactOverlapFiniteSeminorm P Q u
          (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) +
          exactOverlapRootWeight Q P.s * ENNReal.ofReal |cubeAverage Q u| :=
      add_le_add hsem le_rfl
    _ = exactOverlapFiniteNorm P Q u
          (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) :=
      (exactOverlapFiniteNorm_eq_rootCubeAverage P Q u
        (exactDualOverlapIntegrable Q P.p P.p_one_le hmem)).symm

/-- The finite inhomogeneous overlap-positive endpoint truncation is dominated
by the exact extended endpoint norm. -/
theorem exactAggregation_overlapPartialNormTop_le_exactOverlapTopNorm
    {d : ℕ} (P : ExactOverlapTopParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp u (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) (N : ℕ) :
    ENNReal.ofReal
        (cubeBesovOverlapPartialNormTop Q P.s (ENNReal.ofReal P.p) N u) ≤
      exactOverlapTopNorm P Q u
        (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) := by
  have hsem := exactAggregation_overlapPartialSeminormTop_le_exactOverlapTopSeminorm
    P Q u hmem N
  have hlegacySem : 0 ≤ cubeBesovOverlapPartialSeminormTop Q P.s
      (ENNReal.ofReal P.p) N u :=
    cubeBesovOverlapPartialSeminormTop_nonneg Q P.s (ENNReal.ofReal P.p) N u
  have hlegacyRoot : 0 ≤ cubeBesovScaleWeight P.s Q * ‖cubeAverage Q u‖ :=
    mul_nonneg (cubeBesovScaleWeight_nonneg P.s Q) (norm_nonneg _)
  calc
    ENNReal.ofReal
        (cubeBesovOverlapPartialNormTop Q P.s (ENNReal.ofReal P.p) N u) =
        ENNReal.ofReal
          (cubeBesovOverlapPartialSeminormTop Q P.s (ENNReal.ofReal P.p) N u) +
          exactOverlapRootWeight Q P.s * ENNReal.ofReal |cubeAverage Q u| := by
      rw [cubeBesovOverlapPartialNormTop, ENNReal.ofReal_add hlegacySem hlegacyRoot,
        ENNReal.ofReal_mul (cubeBesovScaleWeight_nonneg P.s Q),
        ← exactOverlapRootWeight_eq_ofReal_legacy]
      simp [Real.norm_eq_abs]
    _ ≤ exactOverlapTopSeminorm P Q u
          (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) +
          exactOverlapRootWeight Q P.s * ENNReal.ofReal |cubeAverage Q u| :=
      add_le_add hsem le_rfl
    _ = exactOverlapTopNorm P Q u
          (exactDualOverlapIntegrable Q P.p P.p_one_le hmem) :=
      (exactOverlapTopNorm_eq_rootCubeAverage P Q u
        (exactDualOverlapIntegrable Q P.p P.p_one_le hmem)).symm

/-- A finite legacy circ `ℓ^q` truncation is dominated by the exact extended
circ seminorm, under the canonical block-integrability witness. -/
theorem exactAggregation_circPartialNorm_le_exactCircFiniteSeminorm
    {d : ℕ} (P : ExactCircFiniteParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) (N : ℕ) :
    ENNReal.ofReal
        (cubeBesovCircPartialNorm Q P.s (ENNReal.ofReal P.p)
          (ENNReal.ofReal P.q) N f) ≤
      exactCircFiniteSeminorm P Q f
        (exactCircIntegrable_of_memLp Q P.p P.p_one_le hmem) := by
  have hq0 : 0 ≤ P.q := zero_le_one.trans P.q_one_le
  simpa [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm,
    ENNReal.toReal_ofReal hq0, one_div, exactCircFiniteSeminorm_eq] using
    exactAggregation_ofReal_finiteLq_le_tsum_of_term_eq
      (a := fun j => cubeBesovCircDepthSeminorm Q P.s (ENNReal.ofReal P.p) f j)
      (b := fun j => exactCircDepthTerm Q P.s P.p f
        (exactCircIntegrable_of_memLp Q P.p P.p_one_le hmem) j)
      N P.q
      (fun j _ => cubeBesovCircDepthSeminorm_nonneg Q P.s (ENNReal.ofReal P.p) f j)
      hq0
      (fun j _ =>
        (exactCircDepthTerm_eq_ofReal_cubeBesovCircDepthSeminorm Q P.s P.p
          P.p_one_le f hmem j).symm)

/-- A finite legacy circ supremum truncation is dominated by the exact
extended circ endpoint seminorm. -/
theorem exactAggregation_circPartialNormTop_le_exactCircTopSeminorm
    {d : ℕ} (P : ExactCircTopParameters) (Q : TriadicCube d)
    (f : Vec d → ℝ)
    (hmem : MeasureTheory.MemLp f (ENNReal.ofReal P.p)
      (Homogenization.normalizedCubeMeasure Q)) (N : ℕ) :
    ENNReal.ofReal
        (cubeBesovCircPartialNormTop Q P.s (ENNReal.ofReal P.p) N f) ≤
      exactCircTopSeminorm P Q f
        (exactCircIntegrable_of_memLp Q P.p P.p_one_le hmem) := by
  simpa [cubeBesovCircPartialNormTop, cubeBesovCircPartialSeminormTop,
    exactCircTopSeminorm_eq] using
    exactAggregation_ofReal_finiteSup_le_iSup_of_term_eq
      (a := fun j => cubeBesovCircDepthSeminorm Q P.s (ENNReal.ofReal P.p) f j)
      (b := fun j => exactCircDepthTerm Q P.s P.p f
        (exactCircIntegrable_of_memLp Q P.p P.p_one_le hmem) j)
      N
      (fun j _ =>
        (exactCircDepthTerm_eq_ofReal_cubeBesovCircDepthSeminorm Q P.s P.p
          P.p_one_le f hmem j).symm)

end Homogenization
