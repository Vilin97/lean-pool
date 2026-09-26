/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.CircDomination
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.CaccioppoliBridge
public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Projection
public import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectionLimit
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.VectorProduct
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.NoteConstants
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesQTwo

/-! # Projection Tests -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch01
namespace Legacy

noncomputable section

open scoped BigOperators ENNReal

/-!
# Dual-to-circ projection tests

Legacy finite-truncation projection-test scaffolding for the totalized-real,
disjoint/componentwise compatibility lane.  This is distinct from the exact
`ENNReal` overlap/dual/circ kernels.
-/

private theorem cubeBesovConjExponent_two_eq :
    cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

theorem cubeBesovConjExponent_two_ne_zero_dualToCirc :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ 0 := by
  rw [cubeBesovConjExponent_two_eq]
  norm_num

theorem cubeBesovConjExponent_two_ne_top_dualToCirc :
    cubeBesovConjExponent (2 : ℝ≥0∞) ≠ ∞ := by
  rw [cubeBesovConjExponent_two_eq]
  norm_num

private theorem cubeProjection_idempotent_on_cubeSet {d : ℕ}
    (Q : Cube d) (j : ℕ) (f : Vec d → ℝ) :
    ∀ x ∈ cubeSet Q,
      cubeProjection Q j (cubeProjection Q j f) x = cubeProjection Q j f x := by
  intro x hxQ
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := Q) (n := j) hxQ with
    ⟨R, hR, hxR⟩
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (f := cubeProjection Q j f) hR hxR]
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (f := f) hR hxR]
  rw [cubeAverage_cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (g := f) hR]

private theorem cubeProjection_add_self_projection_eq_on_cubeSet {d : ℕ}
    (Q : Cube d) (j n : ℕ) (f : Vec d → ℝ) :
    ∀ x ∈ cubeSet Q,
      cubeProjection Q (j + n) (cubeProjection Q j f) x =
        cubeProjection Q j f x := by
  intro x hxQ
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := Q) (n := j) hxQ with
    ⟨R, hR, hxR⟩
  rw [cubeProjection_add_eq_cubeProjection_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (n := n) (f := cubeProjection Q j f) hR hxR]
  have hcongr :
      cubeProjection R n (cubeProjection Q j f) =
        cubeProjection R n (fun _ : Vec d => cubeAverage R f) := by
    exact cubeProjection_congr_on_cubeSet (Q := R) (j := n)
      (u := cubeProjection Q j f) (v := fun _ : Vec d => cubeAverage R f)
      (by
        intro y hy
        exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
          (Q := Q) (R := R) (j := j) (f := f) hR hy)
  rw [hcongr]
  rw [cubeProjection_const_of_mem_cubeSet R n (cubeAverage R f) hxR]
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (f := f) hR hxR]

private theorem cubeBesovOscillation_cubeProjection_eq_zero_of_le {d : ℕ}
    {Q R : Cube d} {j k : ℕ} (f : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q k) (hjk : j ≤ k) :
    cubeBesovOscillation R (2 : ℝ≥0∞) (cubeProjection Q j f) = 0 := by
  let P : Vec d → ℝ := cubeProjection Q j f
  have hk : k = j + (k - j) := (Nat.add_sub_of_le hjk).symm
  unfold cubeBesovOscillation
  rw [cubeLpNorm_congr_on_cubeSet (Q := R) (p := (2 : ℝ≥0∞))
    (u := cubeFluctuation R P) (v := fun _ : Vec d => (0 : ℝ))]
  · simp
  intro x hxR
  have hxQ : x ∈ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR hxR
  have hproj_to_avg :
      cubeProjection Q k P x = cubeAverage R P := by
    exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := k) (f := P) hR hxR
  have hself :
      cubeProjection Q k P x = P x := by
    change cubeProjection Q k (cubeProjection Q j f) x = cubeProjection Q j f x
    rw [hk]
    exact cubeProjection_add_self_projection_eq_on_cubeSet Q j (k - j) f x hxQ
  simp [cubeFluctuation, P, ← hself, hproj_to_avg]

private theorem cubeProjection_memLp_on_normalizedCubeMeasure {d : ℕ}
    (Q R : Cube d) (j : ℕ) (p : ℝ≥0∞) (f : Vec d → ℝ) :
    MeasureTheory.MemLp (cubeProjection Q j f) p (normalizedCubeMeasure R) := by
  classical
  unfold cubeProjection
  refine MeasureTheory.memLp_finsetSum
    (s := descendantsAtDepth Q j)
    (f := fun S : Cube d => fun x : Vec d =>
      if x ∈ cubeSet S then cubeAverage S f else 0) ?_
  intro S hS
  have hS_ne_top : normalizedCubeMeasure R (cubeSet S) ≠ ∞ := by
    have hS_le : normalizedCubeMeasure R (cubeSet S) ≤ normalizedCubeMeasure R Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ (cubeSet S))
    have hUniv_lt : normalizedCubeMeasure R Set.univ < ∞ := by simp
    exact ne_of_lt (lt_of_le_of_lt hS_le hUniv_lt)
  simpa [Set.indicator] using!
    (MeasureTheory.memLp_indicator_const (μ := normalizedCubeMeasure R)
      (p := p) (s := cubeSet S) (hs := measurableSet_cubeSet S)
      (c := cubeAverage S f) (Or.inr hS_ne_top))

private theorem cubeProjection_dualLocalMemLpGlobal_two {d : ℕ}
    (Q : Cube d) (j : ℕ) (f : Vec d → ℝ) :
    CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
  intro n R hR
  have hproj :
      MeasureTheory.MemLp (cubeProjection Q j f) (2 : ℝ≥0∞)
        (normalizedCubeMeasure R) :=
    cubeProjection_memLp_on_normalizedCubeMeasure Q R j (2 : ℝ≥0∞) f
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => cubeAverage R (cubeProjection Q j f))
        (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    MeasureTheory.memLp_const _
  simpa [cubeBesovConjExponent_two_eq, cubeFluctuation, sub_eq_add_neg] using!
    hproj.sub hconst

private theorem cubeBesovOscillation_two_le_two_mul_cubeLpNorm_two {d : ℕ}
    (Q : Cube d) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) u ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
  unfold cubeBesovOscillation cubeFluctuation
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => -cubeAverage Q u)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const _
  have hadd :
      cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u) ≤
        cubeLpNorm Q (2 : ℝ≥0∞) u +
          cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverage Q u) := by
    have hfun :
        (fun x => u x - cubeAverage Q u) =
          fun x => u x + (fun _ : Vec d => -cubeAverage Q u) x := by
      funext x
      simp [sub_eq_add_neg]
    rw [hfun]
    exact cubeLpNorm_add_le Q (2 : ℝ≥0∞) u (fun _ : Vec d => -cubeAverage Q u)
      hu hconst (by norm_num)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u x - cubeAverage Q u)
        ≤ cubeLpNorm Q (2 : ℝ≥0∞) u +
            cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverage Q u) := hadd
    _ = cubeLpNorm Q (2 : ℝ≥0∞) u + ‖cubeAverage Q u‖ := by
          rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
            (c := -cubeAverage Q u) (by norm_num)]
          simp
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) u + cubeLpNorm Q (2 : ℝ≥0∞) u := by
          gcongr
          exact norm_cubeAverage_le_cubeLpNorm_two Q u hu
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by ring

private theorem cubeBesovDepthAverage_two_le_four_mul_cubeL2ScalarDepthAverage {d : ℕ}
    (Q : Cube d) (u : Vec d → ℝ) (k : ℕ)
    (hu : ∀ R ∈ descendantsAtDepth Q k,
      MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k ≤
      4 * cubeL2ScalarDepthAverage Q u k := by
  have hpoint :
      ∀ R ∈ descendantsAtDepth Q k,
        (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ (2 : ℝ) ≤
          (2 * cubeLpNorm R (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
    intro R hR
    have hosc :
        cubeBesovOscillation R (2 : ℝ≥0∞) u ≤
          2 * cubeLpNorm R (2 : ℝ≥0∞) u :=
      cubeBesovOscillation_two_le_two_mul_cubeLpNorm_two R u (hu R hR)
    have hosc_nonneg :
        0 ≤ cubeBesovOscillation R (2 : ℝ≥0∞) u :=
      cubeBesovOscillation_nonneg R (2 : ℝ≥0∞) u
    have hright_nonneg :
        0 ≤ 2 * cubeLpNorm R (2 : ℝ≥0∞) u :=
      mul_nonneg (by norm_num) (cubeLpNorm_nonneg R (2 : ℝ≥0∞) u)
    have hsquare :
        (cubeBesovOscillation R (2 : ℝ≥0∞) u) ^ (2 : ℕ) ≤
          (2 * cubeLpNorm R (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
      nlinarith
    simpa [Real.rpow_natCast] using hsquare
  calc
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k
        ≤ descendantsAverage Q k
            (fun R => (2 * cubeLpNorm R (2 : ℝ≥0∞) u) ^ (2 : ℕ)) := by
          unfold cubeBesovDepthAverage
          exact descendantsAverage_le_descendantsAverage Q k hpoint
    _ = descendantsAverage Q k
            (fun R => 4 * (cubeLpNorm R (2 : ℝ≥0∞) u) ^ (2 : ℕ)) := by
          refine congrArg (descendantsAverage Q k) ?_
          funext R
          ring
    _ = 4 * cubeL2ScalarDepthAverage Q u k := by
          rw [descendantsAverage_mul_left]
          rfl

private theorem cubeBesovDepthAverage_two_le_four_mul_sq_cubeLpNorm_two {d : ℕ}
    (Q : Cube d) (u : Vec d → ℝ) (k : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k ≤
      4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
  calc
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k
        ≤ 4 * cubeL2ScalarDepthAverage Q u k := by
          exact cubeBesovDepthAverage_two_le_four_mul_cubeL2ScalarDepthAverage Q u k
            (fun R hR => memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := k) hR hu)
    _ = 4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
          rw [cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q u k hu]

private theorem cubeBesovDepthSeminorm_two_le_two_mul_depthWeight_mul_cubeLpNorm_two {d : ℕ}
    (Q : Cube d) (t : ℝ) (u : Vec d → ℝ) (k : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthSeminorm Q t (2 : ℝ≥0∞) u k ≤
      2 * cubeBesovDepthWeight Q t k * cubeLpNorm Q (2 : ℝ≥0∞) u := by
  have hA :
      cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k ≤
        4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) :=
    cubeBesovDepthAverage_two_le_four_mul_sq_cubeLpNorm_two Q u k hu
  have hsqrt :
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k) ≤
        2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    have hright_nonneg :
        0 ≤ 2 * cubeLpNorm Q (2 : ℝ≥0∞) u :=
      mul_nonneg (by norm_num) (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) u)
    calc
      Real.sqrt (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k)
          ≤ Real.sqrt (4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ)) :=
            Real.sqrt_le_sqrt hA
      _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
            have hsq :
                4 * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) =
                  (2 * cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by ring
            rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hright_nonneg]
  have hweight_nonneg : 0 ≤ cubeBesovDepthWeight Q t k :=
    cubeBesovDepthWeight_nonneg Q t k
  have hrpow :
      (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k) ^ (1 / 2 : ℝ) ≤
        2 * cubeLpNorm Q (2 : ℝ≥0∞) u := by
    simpa [Real.sqrt_eq_rpow] using hsqrt
  unfold cubeBesovDepthSeminorm
  norm_num
  calc
    cubeBesovDepthWeight Q t k *
        (cubeBesovDepthAverage Q (2 : ℝ≥0∞) u k) ^ (1 / 2 : ℝ)
        ≤ cubeBesovDepthWeight Q t k *
            (2 * cubeLpNorm Q (2 : ℝ≥0∞) u) :=
          mul_le_mul_of_nonneg_left hrpow hweight_nonneg
    _ = 2 * cubeBesovDepthWeight Q t k *
          cubeLpNorm Q (2 : ℝ≥0∞) u := by ring

private theorem cubeBesovDepthSeminorm_cubeProjection_le {d : ℕ}
    (Q : Cube d) (t : ℝ) (j k : ℕ) (f : Vec d → ℝ) :
    cubeBesovDepthSeminorm Q t (2 : ℝ≥0∞) (cubeProjection Q j f) k ≤
      2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
  calc
    cubeBesovDepthSeminorm Q t (2 : ℝ≥0∞) (cubeProjection Q j f) k
        ≤ 2 * cubeBesovDepthWeight Q t k *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) :=
          cubeBesovDepthSeminorm_two_le_two_mul_depthWeight_mul_cubeLpNorm_two
            Q t (cubeProjection Q j f) k (cubeProjection_memLp Q j (2 : ℝ≥0∞) f)
    _ =
        2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
          rw [cubeBesovDepthWeight_eq_scaleWeight_mul_rpow]
          ring

private theorem cubeBesovDepthAverage_cubeProjection_eq_zero_of_le {d : ℕ}
    {Q : Cube d} {j k : ℕ} (f : Vec d → ℝ) (hjk : j ≤ k) :
    cubeBesovDepthAverage Q (2 : ℝ≥0∞) (cubeProjection Q j f) k = 0 := by
  unfold cubeBesovDepthAverage descendantsAverage
  have hsum :
      ∑ R ∈ descendantsAtDepth Q k,
        (cubeBesovOscillation R (2 : ℝ≥0∞) (cubeProjection Q j f)) ^
          (2 : ℝ) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro R hR
    rw [cubeBesovOscillation_cubeProjection_eq_zero_of_le (Q := Q) (R := R)
      (j := j) (k := k) f hR hjk]
    norm_num
  change ((descendantsAtDepth Q k).card : ℝ)⁻¹ *
      (∑ R ∈ descendantsAtDepth Q k,
        (cubeBesovOscillation R (2 : ℝ≥0∞) (cubeProjection Q j f)) ^
          (2 : ℝ)) = 0
  rw [hsum, mul_zero]

private theorem cubeBesovDepthSeminorm_cubeProjection_eq_zero_of_le {d : ℕ}
    {Q : Cube d} (t : ℝ) {j k : ℕ} (f : Vec d → ℝ) (hjk : j ≤ k) :
    cubeBesovDepthSeminorm Q t (2 : ℝ≥0∞) (cubeProjection Q j f) k = 0 := by
  unfold cubeBesovDepthSeminorm
  rw [cubeBesovDepthAverage_cubeProjection_eq_zero_of_le (Q := Q) (j := j) (k := k) f hjk]
  norm_num

private theorem cubeBesovPartialSeminorm_cubeProjection_le_sum_depth_bounds {d : ℕ}
    (Q : Cube d) (t : ℝ) (j N : ℕ) (f : Vec d → ℝ) :
    cubeBesovPartialSeminorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
        (cubeProjection Q j f) ≤
      ∑ k ∈ Finset.range j,
        2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
  let B : ℕ → ℝ := fun k =>
    2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) *
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)
  have hB_nonneg : ∀ k, 0 ≤ B k := by
    intro k
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (cubeBesovScaleWeight_nonneg t Q))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
      (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (cubeProjection Q j f))
  have hpartial_le_sum :
      cubeBesovPartialSeminorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (cubeProjection Q j f) ≤
        ∑ k ∈ Finset.range (N + 1),
          cubeBesovDepthSeminorm Q t (2 : ℝ≥0∞) (cubeProjection Q j f) k := by
    rw [cubeBesovPartialSeminorm_two_two_eq_sqrt_sum_sq]
    exact sqrt_sum_sq_le_sum (Finset.range (N + 1))
      (fun k => cubeBesovDepthSeminorm Q t (2 : ℝ≥0∞) (cubeProjection Q j f) k)
      (fun k hk => cubeBesovDepthSeminorm_nonneg Q t (2 : ℝ≥0∞) (cubeProjection Q j f) k)
  have hdepth_sum :
      ∑ k ∈ Finset.range (N + 1),
          cubeBesovDepthSeminorm Q t (2 : ℝ≥0∞) (cubeProjection Q j f) k ≤
        ∑ k ∈ Finset.range (N + 1), if k < j then B k else 0 := by
    refine Finset.sum_le_sum ?_
    intro k hk
    by_cases hkj : k < j
    · have hle := cubeBesovDepthSeminorm_cubeProjection_le Q t j k f
      simpa [B, hkj] using hle
    · have hjk : j ≤ k := Nat.le_of_not_gt hkj
      rw [cubeBesovDepthSeminorm_cubeProjection_eq_zero_of_le (Q := Q) t (j := j) (k := k) f hjk]
      simp [hkj]
  have hfilter_subset :
      (Finset.range (N + 1)).filter (fun k => k < j) ⊆ Finset.range j := by
    intro k hk
    exact Finset.mem_range.mpr ((Finset.mem_filter.mp hk).2)
  calc
    cubeBesovPartialSeminorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
        (cubeProjection Q j f)
        ≤ ∑ k ∈ Finset.range (N + 1),
          cubeBesovDepthSeminorm Q t (2 : ℝ≥0∞) (cubeProjection Q j f) k :=
          hpartial_le_sum
    _ ≤ ∑ k ∈ Finset.range (N + 1), if k < j then B k else 0 := hdepth_sum
    _ = ∑ k ∈ (Finset.range (N + 1)).filter (fun k => k < j), B k := by
          rw [Finset.sum_filter]
    _ ≤ ∑ k ∈ Finset.range j, B k := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hfilter_subset
            (by
              intro k hkRange hkFilter
              exact hB_nonneg k)
    _ = ∑ k ∈ Finset.range j,
        2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
          rfl

/-- Uniform positive test bound for the depth-`j` cube projection.  The bound is
independent of the finite test depth `N`; finer scales contribute zero because
the projection is already piecewise constant there. -/
noncomputable def cubeProjectionPositiveTestCoefficientTwo {d : ℕ}
    (Q : Cube d) (t : ℝ) (j : ℕ) : ℝ :=
  (∑ k ∈ Finset.range j,
    2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ))) +
    cubeBesovScaleWeight t Q

noncomputable def cubeProjectionPositiveTestBoundTwo {d : ℕ}
    (Q : Cube d) (t : ℝ) (j : ℕ) (f : Vec d → ℝ) : ℝ :=
  (∑ k ∈ Finset.range j,
    2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) *
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)) +
    cubeBesovScaleWeight t Q *
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)

private theorem cubeBesovScaleWeight_pos {d : ℕ} (s : ℝ) (Q : Cube d) :
    0 < cubeBesovScaleWeight s Q := by
  unfold cubeBesovScaleWeight
  exact Real.rpow_pos_of_pos
    (by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))
    _

theorem cubeProjectionPositiveTestCoefficientTwo_nonneg {d : ℕ}
    (Q : Cube d) (t : ℝ) (j : ℕ) :
    0 ≤ cubeProjectionPositiveTestCoefficientTwo Q t j := by
  unfold cubeProjectionPositiveTestCoefficientTwo
  exact add_nonneg
    (Finset.sum_nonneg fun k hk =>
      mul_nonneg
        (mul_nonneg (by norm_num) (cubeBesovScaleWeight_nonneg t Q))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _))
    (cubeBesovScaleWeight_nonneg t Q)

theorem cubeProjectionPositiveTestCoefficientTwo_pos {d : ℕ}
    (Q : Cube d) (t : ℝ) (j : ℕ) :
    0 < cubeProjectionPositiveTestCoefficientTwo Q t j := by
  unfold cubeProjectionPositiveTestCoefficientTwo
  have hsum_nonneg :
      0 ≤ ∑ k ∈ Finset.range j,
        2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) := by
    exact Finset.sum_nonneg fun k hk =>
      mul_nonneg
        (mul_nonneg (by norm_num) (cubeBesovScaleWeight_nonneg t Q))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  exact add_pos_of_nonneg_of_pos hsum_nonneg (cubeBesovScaleWeight_pos t Q)

theorem cubeProjectionPositiveTestBoundTwo_eq_coefficient_mul_cubeLpNorm {d : ℕ}
    (Q : Cube d) (t : ℝ) (j : ℕ) (f : Vec d → ℝ) :
    cubeProjectionPositiveTestBoundTwo Q t j f =
      cubeProjectionPositiveTestCoefficientTwo Q t j *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
  unfold cubeProjectionPositiveTestBoundTwo cubeProjectionPositiveTestCoefficientTwo
  calc
    (∑ k ∈ Finset.range j,
        2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)) +
        cubeBesovScaleWeight t Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)
        =
      (∑ k ∈ Finset.range j,
        (2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ))) *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)) +
        cubeBesovScaleWeight t Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
          rfl
    _ =
      (∑ k ∈ Finset.range j,
        2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ))) *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) +
        cubeBesovScaleWeight t Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
          rw [Finset.sum_mul]
    _ =
      ((∑ k ∈ Finset.range j,
        2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ))) +
        cubeBesovScaleWeight t Q) *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) := by
          ring

theorem cubeBesovDualTestNorm_cubeProjection_le_positiveTestBound_two {d : ℕ}
    (Q : Cube d) (t : ℝ) (j N : ℕ) (f : Vec d → ℝ) :
    cubeBesovDualTestNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
        (cubeProjection Q j f) ≤
      cubeProjectionPositiveTestBoundTwo Q t j f := by
  let P : Vec d → ℝ := cubeProjection Q j f
  have hsem :
      cubeBesovPartialSeminorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) N P ≤
        ∑ k ∈ Finset.range j,
          2 * cubeBesovScaleWeight t Q * Real.rpow (3 : ℝ) (t * (k : ℝ)) *
            cubeLpNorm Q (2 : ℝ≥0∞) P := by
    simpa [P] using
      cubeBesovPartialSeminorm_cubeProjection_le_sum_depth_bounds Q t j N f
  have hPmem : MeasureTheory.MemLp P (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    cubeProjection_memLp Q j (2 : ℝ≥0∞) f
  have havg :
      cubeBesovScaleWeight t Q * ‖cubeAverage Q P‖ ≤
        cubeBesovScaleWeight t Q * cubeLpNorm Q (2 : ℝ≥0∞) P :=
    mul_le_mul_of_nonneg_left
      (norm_cubeAverage_le_cubeLpNorm_two Q P hPmem)
      (cubeBesovScaleWeight_nonneg t Q)
  rw [cubeBesovDualTestNorm_of_conjExponent_ne_top Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞)
    N P cubeBesovConjExponent_two_ne_top_dualToCirc]
  rw [cubeBesovConjExponent_two_eq]
  unfold cubeBesovPartialNorm cubeProjectionPositiveTestBoundTwo
  exact add_le_add hsem havg

/-- Testing a function against its depth-`j` cube projection returns the
normalized `L²` mass of that projection.  This is the scale-test identity used
in the lossy true-dual-to-circ comparison. -/
theorem cubeBesovPairing_self_projection_eq_sq_cubeLpNorm_two {d : ℕ}
    (Q : Cube d) (j : ℕ) (f : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovPairing Q f (cubeProjection Q j f) =
      (cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)) ^ (2 : ℕ) := by
  let P : Vec d → ℝ := cubeProjection Q j f
  have hfInt : MeasureTheory.IntegrableOn f (cubeSet Q) MeasureTheory.volume :=
    integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) (hf.integrable (by norm_num))
  have hPMem : MeasureTheory.MemLp P (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    cubeProjection_memLp Q j (2 : ℝ≥0∞) f
  have hPInt : MeasureTheory.IntegrableOn P (cubeSet Q) MeasureTheory.volume :=
    integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) (hPMem.integrable (by norm_num))
  have hidem_pair :
      cubeBesovPairing Q f (cubeProjection Q j P) = cubeBesovPairing Q f P := by
    unfold cubeBesovPairing
    apply cubeAverage_congr_on_cubeSet
    intro x hx
    exact congrArg (fun y => f x * y) (cubeProjection_idempotent_on_cubeSet Q j f x hx)
  have hcomm : cubeBesovPairing Q P P = cubeBesovPairing Q f (cubeProjection Q j P) := by
    exact cubeBesovPairing_projection_comm Q j f P hfInt hPInt
  have hpair : cubeBesovPairing Q f P = cubeBesovPairing Q P P := by
    rw [← hidem_pair, ← hcomm]
  rw [hpair]
  have hnorm :
      (cubeLpNorm Q (2 : ℝ≥0∞) P) ^ (2 : ℕ) =
        cubeAverage Q (fun x => ‖P x‖ ^ (2 : ℕ)) := by
    simpa using
      (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
        (Q := Q) (p := (2 : ℝ≥0∞)) (f := P)
        (by norm_num) (by norm_num) hPMem)
  rw [hnorm]
  unfold cubeBesovPairing
  apply cubeAverage_congr_on_cubeSet
  intro x hx
  simp [P, pow_two, Real.norm_eq_abs]

/-- If the depth-`j` projection of `f` has positive dual-test norm bounded by
`B` at every finite depth, then its `L²` mass is controlled by the true dual
negative Besov norm of `f` times `B`.  This is the core lower-bound mechanism
behind the lossy true-dual-to-circ comparison; the remaining analytic estimate
is the explicit positive-Besov test bound for `cubeProjection Q j f`. -/
theorem sq_cubeLpNorm_projection_le_dualFullNorm_mul_testBound_two {d : ℕ}
    (Q : Cube d) (t : ℝ) (j : ℕ) (f : Vec d → ℝ) {B : ℝ}
    (ht : 0 < t)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hB : 0 < B)
    (hbound : ∀ N : ℕ,
      cubeBesovDualTestNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) N
          (cubeProjection Q j f) ≤ B) :
    (cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)) ^ (2 : ℕ) ≤
      cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) f * B := by
  have hpair :=
    abs_cubeBesovPairing_le_mul_cubeBesovDualFullNorm_of_uniform_bound_two_two
      Q t f (cubeProjection Q j f) ht hf hB hbound
      (cubeProjection_dualLocalMemLpGlobal_two Q j f)
  rw [cubeBesovPairing_self_projection_eq_sq_cubeLpNorm_two Q j f hf] at hpair
  simpa [abs_of_nonneg (sq_nonneg (cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)))]
    using hpair

/-- Concrete scale test lower bound with the projection test norm already
estimated. -/
theorem sq_cubeLpNorm_projection_le_dualFullNorm_mul_positiveTestBound_two {d : ℕ}
    (Q : Cube d) (t : ℝ) (j : ℕ) (f : Vec d → ℝ)
    (ht : 0 < t)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hL : 0 < cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)) :
    (cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)) ^ (2 : ℕ) ≤
      cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) f *
        cubeProjectionPositiveTestBoundTwo Q t j f := by
  have hBpos :
      0 < cubeProjectionPositiveTestBoundTwo Q t j f := by
    rw [cubeProjectionPositiveTestBoundTwo_eq_coefficient_mul_cubeLpNorm]
    exact mul_pos (cubeProjectionPositiveTestCoefficientTwo_pos Q t j) hL
  exact sq_cubeLpNorm_projection_le_dualFullNorm_mul_testBound_two Q t j f ht hf hBpos
    (fun N => cubeBesovDualTestNorm_cubeProjection_le_positiveTestBound_two Q t j N f)

/-- Linear scale estimate obtained by cancelling the nonzero projected `L²`
norm from the quadratic testing lower bound. -/
theorem cubeLpNorm_projection_le_dualFullNorm_mul_positiveTestCoefficient_two {d : ℕ}
    (Q : Cube d) (t : ℝ) (j : ℕ) (f : Vec d → ℝ)
    (ht : 0 < t)
    (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f) ≤
      cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) f *
        cubeProjectionPositiveTestCoefficientTwo Q t j := by
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)
  let D : ℝ := cubeBesovDualFullNorm Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) f
  let C : ℝ := cubeProjectionPositiveTestCoefficientTwo Q t j
  have hL_nonneg : 0 ≤ L := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (cubeProjection Q j f)
  by_cases hLzero : L = 0
  · have hD_nonneg : 0 ≤ D := by
      dsimp [D]
      exact cubeBesovDualFullNorm_nonneg Q t (2 : ℝ≥0∞) (2 : ℝ≥0∞) f
        cubeBesovConjExponent_two_ne_zero_dualToCirc cubeBesovConjExponent_two_ne_top_dualToCirc
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      exact cubeProjectionPositiveTestCoefficientTwo_nonneg Q t j
    dsimp [L, D, C] at hLzero ⊢
    rw [hLzero]
    exact mul_nonneg hD_nonneg hC_nonneg
  · have hLpos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hLzero)
    have hsq :
        L ^ (2 : ℕ) ≤ D * (C * L) := by
      dsimp [L, D, C]
      simpa [cubeProjectionPositiveTestBoundTwo_eq_coefficient_mul_cubeLpNorm,
        mul_assoc] using
        sq_cubeLpNorm_projection_le_dualFullNorm_mul_positiveTestBound_two
          Q t j f ht hf hLpos
    have hmul : L * L ≤ (D * C) * L := by
      nlinarith
    have hcancel : L ≤ D * C := le_of_mul_le_mul_right hmul hLpos
    simpa [L, D, C] using hcancel

theorem cubeBesovCircDepthAverage_eq_sq_cubeLpNorm_projection_two {d : ℕ}
    (Q : Cube d) (j : ℕ) (f : Vec d → ℝ) :
    cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) f j =
      (cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q j f)) ^ (2 : ℕ) := by
  rw [cubeBesovCircDepthAverage_eq_descendantsAverage_projection
    (Q := Q) (p := (2 : ℝ≥0∞)) (u := f) (j := j) (by norm_num)]
  simpa [cubeL2ScalarDepthAverage, Real.rpow_natCast] using
    cubeL2ScalarDepthAverage_eq_cubeLpNorm_two_sq Q (cubeProjection Q j f) j
      (cubeProjection_memLp Q j (2 : ℝ≥0∞) f)

end

end Legacy
end Ch01
end Book
end Homogenization
