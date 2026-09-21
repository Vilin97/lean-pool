/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/

/-
Staged for Tau Ceti, roadmap topic T06.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`AlignedBasis.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

Groundwork for the Yu–Wang–Samworth aligned-basis (orthogonal-Procrustes) bound:
the coordinate isometry `EuclideanSpace 𝕜 (Fin d) →ₗᵢ E` attached to an
orthonormal family, used to build the `d × d` overlap operator whose singular
values are the principal-angle cosines.
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix


/-! # The coordinate isometry of an orthonormal family

An orthonormal family `v : Fin d → E` gives a linear isometry
`familyIsometry hv : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E`, `eⱼ ↦ vⱼ`, onto the
span of the family.  Its adjoint recovers the coordinates `y ↦ (⟪vⱼ, y⟫)ⱼ`, so
the composite `(familyIsometry hu)⋆ ∘ (familyIsometry hv)` is the overlap operator
with matrix `⟪uᵢ, vⱼ⟫` — the object whose singular values are the cosines of the
principal angles between `span u` and `span v`.

## Main results

* `TauCeti.familyMap` and `familyMap_apply`: the linear map `eⱼ ↦ vⱼ`.
* `TauCeti.familyMap_inner_map_map`: it preserves inner products when `v` is
  orthonormal.
* `TauCeti.familyIsometry`: the bundled `EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.AlignedBasis`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `75fdc44`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {d : ℕ}

/-- **An orthonormal family of the right size, lying in `V`, spans `V`.**

Containment gives one inequality and `finrank_span_eq_card` gives equality of
dimensions, which is all `Submodule.eq_of_le_of_finrank_eq` needs.  Written out
four times across `AngleGeometry` and the YWS application statistics layer, once per
subspace in each. -/
theorem span_range_eq_of_orthonormal_of_mem {V : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 V] {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (hmem : ∀ i, v i ∈ V) (hd : d = finrank 𝕜 V) :
    Submodule.span 𝕜 (Set.range v) = V := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact hmem i
  · rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin, hd]

/-- **The span of the family is contained in the isometry's range.**

Immediate from `familyIsometry_single`, and the form the containment is actually
needed in: a vector known to lie in `span (range v)` can be given coordinates. -/
theorem span_range_le_range_familyIsometry {v : Fin d → E} (hv : Orthonormal 𝕜 v) :
    Submodule.span 𝕜 (Set.range v) ≤ LinearMap.range (familyIsometry hv).toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨i, rfl⟩
  exact ⟨EuclideanSpace.single i 1, familyIsometry_single hv i⟩

variable [FiniteDimensional 𝕜 E]

/-- **The overlap operator** of two orthonormal families `u, v`: the compression
`(familyIsometry hu)⋆ ∘ (familyIsometry hv)` on `EuclideanSpace 𝕜 (Fin d)`, with
matrix `⟪uᵢ, vⱼ⟫`.  Its singular values are the cosines of the principal angles
between `span u` and `span v`. -/
@[expose]
noncomputable def overlapOp {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  (familyIsometry hu).toLinearMap.adjoint ∘ₗ (familyIsometry hv).toLinearMap

/-- The overlap operator acts by taking inner products against the first family and re-expanding in
the second. -/
@[simp]
theorem overlapOp_apply {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (x : EuclideanSpace 𝕜 (Fin d)) :
    overlapOp hu hv x = (familyIsometry hu).toLinearMap.adjoint (familyIsometry hv x) := (rfl)

/-- **The overlap operator is a contraction.** `‖overlapOp hu hv x‖ ≤ ‖x‖`, since
`familyIsometry hv` is an isometry and the adjoint of an isometry is a
contraction. -/
theorem overlapOp_contraction {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (x : EuclideanSpace 𝕜 (Fin d)) : ‖overlapOp hu hv x‖ ≤ ‖x‖ := by
  rw [overlapOp_apply]
  have hiso : ∀ y : EuclideanSpace 𝕜 (Fin d), ‖(familyIsometry hu).toLinearMap y‖ ≤ 1 * ‖y‖ :=
    fun y => by
      rw [one_mul, LinearIsometry.coe_toLinearMap]
      exact le_of_eq ((familyIsometry hu).norm_map y)
  calc ‖(familyIsometry hu).toLinearMap.adjoint (familyIsometry hv x)‖
      ≤ 1 * ‖familyIsometry hv x‖ := norm_adjoint_apply_le (by norm_num) hiso _
    _ = ‖x‖ := by rw [one_mul, (familyIsometry hv).norm_map]

/-- **The overlap sum equals `∑ σ²`.** The sum of squared singular values of the
overlap operator is the total squared overlap `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`.  (By Parseval,
`‖overlapOp eⱼ‖² = ‖(familyIsometry hu)⋆ vⱼ‖² = ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²`.) -/
theorem sum_sq_singularValues_overlapOp {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) ^ 2
      = ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2 := by
  rw [sum_sq_singularValues (overlapOp hu hv) finrank_euclideanSpace_fin
    (EuclideanSpace.basisFun (Fin d) 𝕜)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [overlapOp_apply]
  simp only [EuclideanSpace.basisFun_apply, familyIsometry_single]
  rw [← (EuclideanSpace.basisFun (Fin d) 𝕜).sum_sq_norm_inner_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap,
    familyIsometry_single]

/-- **The overlap sum is at most the sum of singular values (cosines).**
`∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖² ≤ ∑ⱼ cos θⱼ`, i.e. `d − ‖sinΘ‖²_F ≤ ∑ cos θ`.  This is the
analytic heart of the Yu–Wang–Samworth aligned-basis (orthogonal-Procrustes)
bound: the overlap operator is a contraction, so `∑σ² ≤ ∑σ`, and its squared
singular values sum to the overlap while its singular values sum to `∑ cos θ`. -/
theorem sum_overlap_le_sum_singularValues {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2 ≤ ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) := by
  -- `∑σ² ≤ ∑σ`, over `Fin d`, from the contraction core lemma (now `hn`-flexible).
  have hcore := sum_sq_norm_le_sum_re_inner_abs_of_contraction (overlapOp_contraction hu hv)
    finrank_euclideanSpace_fin (EuclideanSpace.basisFun (Fin d) 𝕜)
  rw [← sum_sq_singularValues (overlapOp hu hv) finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin d) 𝕜),
    sum_re_inner_abs_self_eq_sum_singularValues (overlapOp hu hv) finrank_euclideanSpace_fin
      (EuclideanSpace.basisFun (Fin d) 𝕜)] at hcore
  calc ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2
      = ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) ^ 2 :=
        (sum_sq_singularValues_overlapOp hu hv).symm
    _ ≤ ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) := hcore

/-- **Cross-term identity** (Procrustes/polar).  With `O = choosePolarUnitary
(overlapOp hu hv)`, the aligned rotation `wⱼ = (familyIsometry hv)(O⁻¹ eⱼ)`
satisfies `⟪uⱼ, wⱼ⟫ = ⟪O⁻¹ eⱼ, |M|(O⁻¹ eⱼ)⟫`, where `M = overlapOp hu hv`.
Moves `familyIsometry hu` to its adjoint (giving `M`), then `M = O|M|` with `O`
unitary. -/
theorem inner_u_aligned_eq {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (j : Fin d) :
    ⟪u j, familyIsometry hv ((choosePolarUnitary (overlapOp hu hv)).symm
          (EuclideanSpace.single j 1))⟫_𝕜
      = ⟪(choosePolarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1),
          operatorAbs (overlapOp hu hv)
            ((choosePolarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1))⟫_𝕜 := by
  set M := overlapOp hu hv with hM
  set O := choosePolarUnitary M with hO
  have hstep : ⟪u j, familyIsometry hv (O.symm (EuclideanSpace.single j 1))⟫_𝕜
      = ⟪EuclideanSpace.single j 1, M (O.symm (EuclideanSpace.single j 1))⟫_𝕜 := by
    rw [← familyIsometry_single hu j, ← LinearIsometry.coe_toLinearMap,
      ← LinearMap.adjoint_inner_right]
    rfl
  rw [hstep]
  -- `M = O ∘ |M|`, then `O` unitary moves across the inner product.
  have hpolar : M (O.symm (EuclideanSpace.single j 1))
      = O (operatorAbs M (O.symm (EuclideanSpace.single j 1))) := by
    have h1 := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary M)
      (O.symm (EuclideanSpace.single j 1))
    rw [LinearMap.comp_apply] at h1
    rw [h1, hO]
    rfl
  rw [hpolar, ← O.apply_symm_apply (EuclideanSpace.single j 1)]
  rw [O.inner_map_map, O.symm_apply_apply]

/-- **Cross-term sum = `∑ cos θ`.** Summing the Procrustes cross-term recovers the
trace of the modulus, `∑ⱼ re⟪uⱼ, wⱼ⟫ = ∑ⱼ σⱼ`, via `W0.1(c)` on the
`O⁻¹`-image orthonormal basis. -/
theorem sum_re_inner_u_aligned {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∑ j, RCLike.re ⟪u j, familyIsometry hv ((choosePolarUnitary (overlapOp hu hv)).symm
          (EuclideanSpace.single j 1))⟫_𝕜
      = ∑ k : Fin d, (overlapOp hu hv).singularValues (k : ℕ) := by
  rw [← sum_re_inner_abs_self_eq_sum_singularValues (overlapOp hu hv) finrank_euclideanSpace_fin
    ((EuclideanSpace.basisFun (Fin d) 𝕜).map (choosePolarUnitary (overlapOp hu hv)).symm)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_u_aligned_eq hu hv j, OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply,
    (isPositive_operatorAbs (overlapOp hu hv)).isSymmetric
      ((choosePolarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1))
      ((choosePolarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1))]

/-- **Yu–Wang–Samworth aligned-basis bound.** For orthonormal families `u, v`
(bases of the two `d`-subspaces), the Procrustes-rotated basis
`wⱼ = (familyIsometry hv)(O⁻¹ eⱼ)` (`O = choosePolarUnitary (overlapOp hu hv)`) obeys
`∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 (d − ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²) = 2 ‖sinΘ‖²_F`.  From
`∑‖wⱼ−uⱼ‖² = 2d − 2∑ cos θ` and the analytic core `overlap ≤ ∑ cos θ`. -/
theorem sum_sq_norm_aligned_le {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∑ j, ‖familyIsometry hv ((choosePolarUnitary (overlapOp hu hv)).symm
          (EuclideanSpace.single j 1)) - u j‖ ^ 2
      ≤ 2 * ((d : ℝ) - ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2) := by
  have hexp : ∀ j, ‖familyIsometry hv ((choosePolarUnitary (overlapOp hu hv)).symm
        (EuclideanSpace.single j 1)) - u j‖ ^ 2
      = 2 - 2 * RCLike.re ⟪u j, familyIsometry hv
          ((choosePolarUnitary (overlapOp hu hv)).symm (EuclideanSpace.single j 1))⟫_𝕜 := by
    intro j
    simp only [norm_sub_sq (𝕜 := 𝕜), (familyIsometry hv).norm_map,
      (choosePolarUnitary (overlapOp hu hv)).symm.norm_map, PiLp.norm_single 2, norm_one,
      hu.1 j, inner_re_symm]
    ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_re_inner_u_aligned hu hv]
  simp
  have hkey := sum_overlap_le_sum_singularValues hu hv
  linarith

end TauCeti
