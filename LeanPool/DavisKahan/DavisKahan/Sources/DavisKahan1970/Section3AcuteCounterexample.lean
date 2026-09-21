/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.TwoProjections
import Mathlib.Analysis.InnerProductSpace.l2Space
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry

/-!
# Printed acuteness is weaker than a uniform projection gap

This module supplies the infinite-dimensional witness promised after Davis--Kahan
1970, Definition 3.2.  In an orthonormal basis indexed by `ℕ × Bool`, rotate the
two basis vectors in the `n`-th plane through an angle whose cosine is
`1 / (n + 2)`.  Every cosine and sine is nonzero, so both crossed intersections
vanish.  The cosines nevertheless tend to zero, so unit vectors in the first
subspace have projections onto the second subspace of arbitrarily small norm.
Consequently the projection gap is exactly one.

This proves, inside Lean, that the finite-dimensional hypothesis in
`projectionGap_lt_one_of_isAcute` cannot be removed.
-/

open scoped InnerProductSpace
open scoped lp

namespace TauCeti
namespace DavisKahan1970
namespace Section3AcuteCounterexample

open DavisKahan

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- Cosine of the `n`-th model angle. -/
def modelCosine (n : ℕ) : ℝ := ((n : ℝ) + 2)⁻¹

/-- Sine of the `n`-th model angle. -/
def modelSine (n : ℕ) : ℝ := Real.sqrt (1 - modelCosine n ^ 2)

/-- Every model cosine is positive, so no crossed intersection is forced by a
vanishing cosine. -/
theorem modelCosine_pos (n : ℕ) : 0 < modelCosine n := by
  rw [modelCosine]
  positivity

/-- Every model cosine is strictly below one, so no plane is a common part. -/
theorem modelCosine_lt_one (n : ℕ) : modelCosine n < 1 := by
  change ((n : ℝ) + 2)⁻¹ < 1
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  rw [inv_lt_one₀ (by linarith)]
  linarith

/-- The Pythagorean identity for the model angle. -/
theorem modelSine_sq (n : ℕ) : modelSine n ^ 2 = 1 - modelCosine n ^ 2 := by
  rw [modelSine, Real.sq_sqrt]
  nlinarith [modelCosine_pos n, modelCosine_lt_one n]

/-- Every model sine is positive, so no crossed intersection is forced by a
vanishing sine. -/
theorem modelSine_pos (n : ℕ) : 0 < modelSine n := by
  rw [modelSine]
  exact Real.sqrt_pos.2 (by
    nlinarith [modelCosine_pos n, modelCosine_lt_one n])

/-- First vector of the rotated orthonormal pair in the `n`-th coordinate plane. -/
def rotatedVector (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) : H :=
  (modelCosine n : 𝕜) • b (n, false) + (modelSine n : 𝕜) • b (n, true)

/-- Second vector of the rotated orthonormal pair in the `n`-th coordinate plane. -/
def rotatedOrthogonalVector (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) : H :=
  -(modelSine n : 𝕜) • b (n, false) + (modelCosine n : 𝕜) • b (n, true)

omit [CompleteSpace H] in
/-- The two rotated families are mutually orthogonal, across planes as well as
within one. -/
theorem inner_rotatedOrthogonalVector_rotatedVector
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) (m n : ℕ) :
    ⟪rotatedOrthogonalVector b m, rotatedVector b n⟫_𝕜 = 0 := by
  by_cases hmn : m = n
  · subst m
    have hff : ⟪b (n, false), b (n, false)⟫_𝕜 = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1]
      norm_num
    have htt : ⟪b (n, true), b (n, true)⟫_𝕜 = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1]
      norm_num
    simp only [rotatedOrthogonalVector, rotatedVector, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right,
      hff, htt, map_neg, RCLike.conj_ofReal,
      b.orthonormal.2 (by simp : (n, false) ≠ (n, true)),
      b.orthonormal.2 (by simp : (n, true) ≠ (n, false)),
      mul_one, mul_zero, add_zero, zero_add]
    ring
  · have hff : (m, false) ≠ (n, false) := fun h => hmn (Prod.mk.inj h).1
    have hft : (m, false) ≠ (n, true) := by simp
    have htf : (m, true) ≠ (n, false) := by simp
    have htt : (m, true) ≠ (n, true) := fun h => hmn (Prod.mk.inj h).1
    simp only [rotatedOrthogonalVector, rotatedVector, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right,
      b.orthonormal.2 hff, b.orthonormal.2 hft,
      b.orthonormal.2 htf, b.orthonormal.2 htt, mul_zero, add_zero]

omit [CompleteSpace H] in
/-- The rotated vectors are unit vectors. -/
theorem norm_rotatedVector (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) :
    ‖rotatedVector b n‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜)]
  have hff : ⟪b (n, false), b (n, false)⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1]
    norm_num
  have htt : ⟪b (n, true), b (n, true)⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1]
    norm_num
  simp only [rotatedVector, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hff, htt,
    b.orthonormal.2 (by simp : (n, false) ≠ (n, true)),
    b.orthonormal.2 (by simp : (n, true) ≠ (n, false)),
    mul_zero, add_zero, zero_add, mul_one,
    RCLike.conj_ofReal, one_pow]
  norm_cast
  nlinarith [modelSine_sq n]

/-- The first coordinate half of the ambient Hilbert space. -/
def sourceSubspace (b : HilbertBasis (ℕ × Bool) 𝕜 H) : Submodule 𝕜 H :=
  (Submodule.span 𝕜 (b '' {i : ℕ × Bool | i.2 = true}))ᗮ

/-- The closed span of the first rotated vector in every coordinate plane. -/
def targetSubspace (b : HilbertBasis (ℕ × Bool) 𝕜 H) : Submodule 𝕜 H :=
  (Submodule.span 𝕜 (Set.range (rotatedOrthogonalVector b)))ᗮ

/-- The source subspace is an orthogonal complement, hence complemented. -/
theorem sourceSubspace_hasOrthogonalProjection
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) :
    (sourceSubspace b).HasOrthogonalProjection := by
  unfold sourceSubspace
  infer_instance

/-- The target subspace is an orthogonal complement, hence complemented. -/
theorem targetSubspace_hasOrthogonalProjection
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) :
    (targetSubspace b).HasOrthogonalProjection := by
  unfold targetSubspace
  infer_instance

local instance sourceSubspaceProjection
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) :
    (sourceSubspace b).HasOrthogonalProjection :=
  sourceSubspace_hasOrthogonalProjection b

local instance targetSubspaceProjection
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) :
    (targetSubspace b).HasOrthogonalProjection :=
  targetSubspace_hasOrthogonalProjection b

omit [CompleteSpace H] in
/-- The `false` half of each coordinate plane spans the source subspace. -/
theorem basis_false_mem_sourceSubspace
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) :
    b (n, false) ∈ sourceSubspace b := by
  rw [sourceSubspace, mem_orthogonal_span]
  rintro _ ⟨i, hi, rfl⟩
  exact b.orthonormal.2 (by
    intro h
    have := congrArg Prod.snd h
    simp_all)

omit [CompleteSpace H] in
/-- The `true` half of each coordinate plane spans the source complement. -/
theorem basis_true_mem_sourceSubspace_orthogonal
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) :
    b (n, true) ∈ (sourceSubspace b)ᗮ := by
  exact Submodule.le_orthogonal_orthogonal _
    (Submodule.subset_span ⟨(n, true), rfl, rfl⟩)

omit [CompleteSpace H] in
/-- The first rotated vector of each plane lies in the target subspace. -/
theorem rotatedVector_mem_targetSubspace
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) :
    rotatedVector b n ∈ targetSubspace b := by
  rw [targetSubspace, mem_orthogonal_span]
  rintro _ ⟨m, rfl⟩
  exact inner_rotatedOrthogonalVector_rotatedVector b m n

omit [CompleteSpace H] in
/-- The second rotated vector of each plane lies in the target complement. -/
theorem rotatedOrthogonalVector_mem_targetSubspace_orthogonal
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) :
    rotatedOrthogonalVector b n ∈ (targetSubspace b)ᗮ := by
  exact Submodule.le_orthogonal_orthogonal _
    (Submodule.subset_span (Set.mem_range_self n))

/-- The target projection of a source basis vector is the rotated vector scaled
by the model cosine.  This is the computation the gap is read off. -/
theorem starProjection_basis_false
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) :
    (targetSubspace b).starProjection (b (n, false)) =
      (modelCosine n : 𝕜) • rotatedVector b n := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (targetSubspace b).smul_mem _ (rotatedVector_mem_targetSubspace b n)
  · intro y hy
    have hres : b (n, false) - (modelCosine n : 𝕜) • rotatedVector b n =
        -(modelSine n : 𝕜) • rotatedOrthogonalVector b n := by
      have hs : (1 : 𝕜) - (modelCosine n : 𝕜) ^ 2 =
          (modelSine n : 𝕜) ^ 2 := by
        simpa only [RCLike.ofReal_sub, RCLike.ofReal_pow, RCLike.ofReal_one] using
          congrArg (fun r : ℝ => (r : 𝕜)) (modelSine_sq n).symm
      calc
        b (n, false) - (modelCosine n : 𝕜) • rotatedVector b n =
            ((1 : 𝕜) - (modelCosine n : 𝕜) ^ 2) • b (n, false) -
              ((modelCosine n : 𝕜) * modelSine n) • b (n, true) := by
                simp only [rotatedVector]
                module
        _ = ((modelSine n : 𝕜) ^ 2) • b (n, false) -
              ((modelSine n : 𝕜) * modelCosine n) • b (n, true) := by
                rw [hs]
                rw [mul_comm (modelCosine n : 𝕜) (modelSine n : 𝕜)]
        _ = -(modelSine n : 𝕜) • rotatedOrthogonalVector b n := by
              simp only [rotatedOrthogonalVector]
              module
    rw [hres]
    exact Submodule.inner_left_of_mem_orthogonal hy
      ((targetSubspace b)ᗮ.smul_mem _
        (rotatedOrthogonalVector_mem_targetSubspace_orthogonal b n))

/-- The projected source basis vector has norm exactly the model cosine, which
tends to zero. -/
theorem norm_starProjection_basis_false
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) (n : ℕ) :
    ‖(targetSubspace b).starProjection (b (n, false))‖ = modelCosine n := by
  rw [starProjection_basis_false, norm_smul, norm_rotatedVector, mul_one]
  simp [modelCosine_pos n |>.le]

/-- **The pair is acute in the printed sense**: both crossed intersections
vanish, because no model cosine or sine is zero. -/
theorem source_target_isAcute (b : HilbertBasis (ℕ × Bool) 𝕜 H) :
    IsAcute (sourceSubspace b) (targetSubspace b) := by
  constructor
  · intro x hxU hxV
    apply b.repr.injective
    ext i
    simp only [map_zero, b.repr_apply_apply]
    rcases i with ⟨n, q⟩
    cases q
    · change ⟪b (n, false), x⟫_𝕜 = 0
      have hw := Submodule.inner_right_of_mem_orthogonal
          (rotatedVector_mem_targetSubspace b n)
          ((Submodule.starProjection_apply_eq_zero_iff _).mp hxV)
      have ht := Submodule.inner_left_of_mem_orthogonal
          hxU (basis_true_mem_sourceSubspace_orthogonal b n)
      simp only [rotatedVector, inner_add_left, inner_smul_left, ht,
        mul_zero, add_zero, RCLike.conj_ofReal] at hw
      exact (mul_eq_zero.mp hw).resolve_left (by
        exact_mod_cast (modelCosine_pos n).ne')
    · change ⟪b (n, true), x⟫_𝕜 = 0
      exact Submodule.inner_left_of_mem_orthogonal
          hxU (basis_true_mem_sourceSubspace_orthogonal b n)
  · intro y hyV hyU
    apply b.repr.injective
    ext i
    simp only [map_zero, b.repr_apply_apply]
    rcases i with ⟨n, q⟩
    cases q
    · change ⟪b (n, false), y⟫_𝕜 = 0
      exact Submodule.inner_right_of_mem_orthogonal
          (basis_false_mem_sourceSubspace b n)
          ((Submodule.starProjection_apply_eq_zero_iff _).mp hyU)
    · change ⟪b (n, true), y⟫_𝕜 = 0
      have hz := Submodule.inner_left_of_mem_orthogonal hyV
          (rotatedOrthogonalVector_mem_targetSubspace_orthogonal b n)
      have hf := Submodule.inner_right_of_mem_orthogonal
          (basis_false_mem_sourceSubspace b n)
          ((Submodule.starProjection_apply_eq_zero_iff _).mp hyU)
      simp only [rotatedOrthogonalVector, inner_add_left, inner_smul_left,
        hf, mul_zero, zero_add, RCLike.conj_ofReal] at hz
      exact (mul_eq_zero.mp hz).resolve_left (by
        exact_mod_cast (modelCosine_pos n).ne')

/-- **The projection gap is nevertheless one**, because the model cosines tend
to zero.  This is what shows printed acuteness is weaker than a uniform gap. -/
theorem source_target_projectionGap_eq_one
    (b : HilbertBasis (ℕ × Bool) 𝕜 H) :
    (sourceSubspace b).projectionGap (targetSubspace b) = 1 := by
  apply le_antisymm
  · rw [Submodule.projectionGap_eq_max_directedProjectionGap]
    exact max_le (Submodule.directedProjectionGap_le_one _ _)
      (Submodule.directedProjectionGap_le_one _ _)
  · apply one_le_projectionGap_of_forall_exists_unit_lt
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    refine ⟨b (n, false), basis_false_mem_sourceSubspace b n,
      b.orthonormal.1 (n, false), ?_⟩
    rw [norm_starProjection_basis_false, modelCosine]
    have hden : 0 < (n : ℝ) + 2 := by positivity
    simpa only [one_div] using
      (one_div_lt hden hε).2 (hn.trans (by norm_num))

/-- **Infinite-dimensional counterexample to uniform acuteness.**

Over either real or complex scalars there are closed subspaces satisfying the
paper's Definition 3.2 whose projection gap is one. -/
theorem exists_isAcute_projectionGap_eq_one :
    let b : HilbertBasis (ℕ × Bool) 𝕜 (ℓ²(ℕ × Bool, 𝕜)) := default
    IsAcute (sourceSubspace b) (targetSubspace b) ∧
      (sourceSubspace b).projectionGap (targetSubspace b) = 1 := by
  let b : HilbertBasis (ℕ × Bool) 𝕜 (ℓ²(ℕ × Bool, 𝕜)) := default
  exact ⟨source_target_isAcute b, source_target_projectionGap_eq_one b⟩

end

end Section3AcuteCounterexample
end DavisKahan1970
end TauCeti
