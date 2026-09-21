/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.TwoProjections
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Orthogonal-summand coordinates

The coordinate chart `H ≃ₗᵢ[ℂ] WithLp 2 (K × Kᗮ)` of an orthogonally complemented
closed subspace is Mathlib's `Submodule.orthogonalDecomposition`.  This file adds
the assembly layer on top of it that the nonacute two-projection classification
needs: once isometries have been constructed on mutually orthogonal summands,
they can be joined into one ambient unitary without repeating projection algebra.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Join two isometries acting on complementary orthogonal summands.

The two coordinate charts are Mathlib's `Submodule.orthogonalDecomposition`; only the
joining of the two factors is new here. -/
noncomputable def orthogonalSumEquiv
    (K L : Submodule ℂ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (eK : K ≃ₗᵢ[ℂ] L) (ePerp : Kᗮ ≃ₗᵢ[ℂ] Lᗮ) :
    H ≃ₗᵢ[ℂ] H :=
  K.orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 eK ePerp) |>.trans
      L.orthogonalDecomposition.symm

omit [CompleteSpace H] in
/-- On the first summand the joined isometry acts by the first factor. -/
@[simp] theorem orthogonalSumEquiv_apply_mem
    (K L : Submodule ℂ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (eK : K ≃ₗᵢ[ℂ] L) (ePerp : Kᗮ ≃ₗᵢ[ℂ] Lᗮ)
    (x : K) :
    orthogonalSumEquiv K L eK ePerp (x : H) = (eK x : H) := by
  simp [orthogonalSumEquiv, LinearIsometryEquiv.trans_apply,
    Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero x.2]

omit [CompleteSpace H] in
/-- On the orthogonal complement it acts by the second factor.  With the previous lemma this
pins the joined isometry down summand-wise. -/
@[simp] theorem orthogonalSumEquiv_apply_mem_orthogonal
    (K L : Submodule ℂ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (eK : K ≃ₗᵢ[ℂ] L) (ePerp : Kᗮ ≃ₗᵢ[ℂ] Lᗮ)
    (x : Kᗮ) :
    orthogonalSumEquiv K L eK ePerp (x : H) = (ePerp x : H) := by
  simp [orthogonalSumEquiv, LinearIsometryEquiv.trans_apply,
    Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr x.2]

omit [CompleteSpace H] in
/-- The joined equivalence conjugates the first orthogonal projection. -/
theorem orthogonalSumEquiv_intertwines_projection
    (K L : Submodule ℂ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (eK : K ≃ₗᵢ[ℂ] L) (ePerp : Kᗮ ≃ₗᵢ[ℂ] Lᗮ) :
    (orthogonalSumEquiv K L eK ePerp : H →L[ℂ] H) ∘L K.starProjection =
      L.starProjection ∘L
        (orthogonalSumEquiv K L eK ePerp : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro x
  have hxK : K.starProjection x ∈ K := K.starProjection_apply_mem x
  have hxP : Kᗮ.starProjection x ∈ Kᗮ := Kᗮ.starProjection_apply_mem x
  have hmemK : orthogonalSumEquiv K L eK ePerp (K.starProjection x)
      = (eK ⟨K.starProjection x, hxK⟩ : H) :=
    orthogonalSumEquiv_apply_mem K L eK ePerp ⟨K.starProjection x, hxK⟩
  have hmemP : orthogonalSumEquiv K L eK ePerp (Kᗮ.starProjection x)
      = (ePerp ⟨Kᗮ.starProjection x, hxP⟩ : H) :=
    orthogonalSumEquiv_apply_mem_orthogonal K L eK ePerp ⟨Kᗮ.starProjection x, hxP⟩
  have hsum : orthogonalSumEquiv K L eK ePerp x
      = (eK ⟨K.starProjection x, hxK⟩ : H)
        + (ePerp ⟨Kᗮ.starProjection x, hxP⟩ : H) := by
    conv_lhs => rw [← K.starProjection_add_starProjection_orthogonal x]
    rw [map_add, hmemK, hmemP]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_coe]
  rw [hmemK, hsum, map_add,
    L.starProjection_eq_self_iff.mpr (eK ⟨K.starProjection x, hxK⟩).2,
    (Submodule.starProjection_apply_eq_zero_iff L).mpr
      (ePerp ⟨Kᗮ.starProjection x, hxP⟩).2,
    add_zero]

end

end DavisKahan
end TauCeti
