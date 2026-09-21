/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Intrinsic
public import Mathlib.Analysis.Convex.Combination

/-!
# The affine kernel for Carlson's Dirichlet averages

This file contains the common algebraic kernel used by both the real probability average and
the complex regularized integral.
-/

open Complex
open scoped Classical

@[expose] public noncomputable section CarlsonDirichletKernel

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The affine form on the standard simplex associated with the complex parameters `z`. -/
def carlsonAffineForm (z : ι → ℂ) (u : ι → ℝ) : ℂ :=
  ∑ i, (u i : ℂ) * z i

/-- The affine form associated with `z` is continuous in the simplex variable. -/
theorem continuous_carlsonAffineForm (z : ι → ℂ) :
    Continuous (carlsonAffineForm z) := by
  unfold carlsonAffineForm
  fun_prop

/-- Carlson's affine form, regarded as a continuous complex-linear map in its node variables. -/
noncomputable def carlsonAffineFormCLM (u : ι → ℝ) : (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (u i : ℂ) • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)

/-- Evaluation of the continuous-linear version of Carlson's affine form. -/
lemma carlsonAffineFormCLM_apply (u : ι → ℝ) (z : ι → ℂ) :
    carlsonAffineFormCLM u z = carlsonAffineForm z u := by
  simp [carlsonAffineFormCLM, carlsonAffineForm]

/-- On the standard simplex, the operator norm of Carlson's affine form is at most one. -/
lemma norm_carlsonAffineFormCLM_le_one {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) : ‖carlsonAffineFormCLM u‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [carlsonAffineFormCLM_apply]
  calc
    ‖carlsonAffineForm z u‖ ≤ ∑ i, u i * ‖z i‖ := by
      unfold carlsonAffineForm
      calc
        ‖∑ i, (u i : ℂ) * z i‖ ≤ ∑ i, ‖(u i : ℂ) * z i‖ := norm_sum_le _ _
        _ = ∑ i, u i * ‖z i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          simp [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    _ ≤ ∑ i, u i * ‖z‖ := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (hu.1 i)
    _ = ‖z‖ := by rw [← Finset.sum_mul, hu.2, one_mul]
    _ = 1 * ‖z‖ := by rw [one_mul]

/-- Moving the node vector moves every simplex affine combination by at most the supremum-norm
distance between the node vectors. -/
lemma dist_carlsonAffineForm_le_norm_sub (z w : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    dist (carlsonAffineForm w u) (carlsonAffineForm z u) ≤ ‖w - z‖ := by
  rw [← carlsonAffineFormCLM_apply u w, ← carlsonAffineFormCLM_apply u z]
  rw [dist_eq_norm, ← map_sub]
  calc
    ‖carlsonAffineFormCLM u (w - z)‖ ≤ ‖carlsonAffineFormCLM u‖ * ‖w - z‖ :=
      (carlsonAffineFormCLM u).le_opNorm _
    _ ≤ 1 * ‖w - z‖ := mul_le_mul_of_nonneg_right
      (norm_carlsonAffineFormCLM_le_one hu) (norm_nonneg _)
    _ = ‖w - z‖ := one_mul _

/-- A simplex affine combination is bounded by the supremum norm of its nodes. -/
theorem norm_carlsonAffineForm_le_pi_norm (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    ‖carlsonAffineForm z u‖ ≤ ‖z‖ := by
  simpa only [carlsonAffineFormCLM_apply, one_mul] using
    ((carlsonAffineFormCLM u).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (norm_carlsonAffineFormCLM_le_one hu) (norm_nonneg z))

/-- Carlson's affine form as a real-linear map in its simplex coordinates. -/
def carlsonSimplexCLM (z : ι → ℂ) : (ι → ℝ) →L[ℝ] ℂ :=
  ∑ k, z k • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj k))

/-- Evaluation of the real-linear simplex-coordinate map. -/
lemma carlsonSimplexCLM_apply (z : ι → ℂ) (u : ι → ℝ) :
    carlsonSimplexCLM z u = carlsonAffineForm z u := by
  simp [carlsonSimplexCLM, carlsonAffineForm, mul_comm]

/-- The affine form has its defining real-linear map as its Fréchet derivative. -/
lemma hasFDerivAt_carlsonSimplex (z : ι → ℂ) (u : ι → ℝ) :
    HasFDerivAt (carlsonAffineForm z) (carlsonSimplexCLM z) u := by
  convert! (carlsonSimplexCLM z).hasFDerivAt (x := u) using 1
  funext v
  exact (carlsonSimplexCLM_apply z v).symm

/-- A coordinate tangent vector is sent to the difference of the corresponding nodes. -/
lemma carlsonSimplexCLM_tangent (z : ι → ℂ) (i j : ι) :
    carlsonSimplexCLM z (Pi.single i 1 - Pi.single j 1) = z i - z j := by
  simp [carlsonSimplexCLM, map_sub, Pi.single_apply, apply_ite]

/-- Carlson's affine form lies in the real convex hull of its parameters. -/
theorem carlsonAffineForm_mem_convexHull (z : ι → ℂ) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    carlsonAffineForm z u ∈ convexHull ℝ (Set.range z) := by
  have h := affineCombination_mem_convexHull (s := Finset.univ) (v := z) (w := u)
    (fun i _ ↦ hu.1 i) hu.2
  rw [affineCombination_eq_centerMass hu.2] at h
  simpa [Finset.centerMass, hu.2, carlsonAffineForm, Complex.real_smul, mul_comm] using h

/-- The convex hull of the nodes is exactly the image of the intrinsic simplex
under Carlson's affine form, including for empty index types. -/
theorem mem_convexHull_range_iff_carlsonAffineForm (z : ι → ℂ) (x : ℂ) :
    x ∈ convexHull ℝ (Set.range z) ↔
      ∃ u : Convexity.StdSimplex ℝ ι, carlsonAffineForm z u.coordinates = x := by
  constructor
  · intro hz
    obtain ⟨κ, _, w, y, hw₀, hw₁, hy, hsum⟩ :=
      (mem_convexHull_iff_exists_fintype (R := ℝ) (E := ℂ)).1 hz
    choose i hi using fun k : κ => (hy k)
    let u : ι → ℝ := fun j => ∑ k, if i k = j then w k else 0
    refine ⟨Convexity.StdSimplex.ofCoordinates u ⟨?_, ?_⟩, ?_⟩
    · intro j
      exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hw₀]
    · have hsumu : ∑ j, u j = ∑ k, w k := by
        simp only [u]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [Finset.sum_ite_eq]
      simpa [hsumu] using hw₁
    · change (∑ j, (u j : ℂ) * z j) = x
      have hswap :
          ∑ j, (∑ k, (if i k = j then w k else 0 : ℂ)) * z j =
            ∑ k, (w k : ℂ) * z (i k) := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [Finset.sum_ite_eq]
      calc
        ∑ j, (u j : ℂ) * z j = ∑ j, (∑ k, (if i k = j then w k else 0 : ℂ)) * z j := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          simp only [u, Complex.ofReal_sum, apply_ite Complex.ofReal, ofReal_zero]
        _ = ∑ k, (w k : ℂ) * z (i k) := hswap
        _ = ∑ k, (w k : ℂ) * y k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hi k]
        _ = ∑ k, w k • y k := by
          apply Finset.sum_congr rfl
          intro k _
          simp [Complex.real_smul]
        _ = x := hsum
  · rintro ⟨u, hzero⟩
    rw [← hzero]
    exact carlsonAffineForm_mem_convexHull z u.coordinates_mem

/-- Zero lies in the convex hull precisely when the affine form vanishes at
some simplex point. -/
theorem zero_mem_convexHull_range_iff (z : ι → ℂ) :
    (0 : ℂ) ∈ convexHull ℝ (Set.range z) ↔
      ∃ u : Convexity.StdSimplex ℝ ι, carlsonAffineForm z u.coordinates = 0 :=
  mem_convexHull_range_iff_carlsonAffineForm z 0

end DirichletTransform

end CarlsonDirichletKernel
