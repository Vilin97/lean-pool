/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.BoundedDiagonalization
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Bounded graphs are acute

This leaf module discharges the geometric hypothesis left explicit in
`BoundedDiagonalization`.  The zero graph is the first coordinate subspace.
For a bounded map `X`, the ambient map which sends `(u,v)` to `(0,Xu)` is an
angular operator over that coordinate subspace, and its graph range is exactly
`blockGraph X`.  The general bounded graph representation theorem therefore
places every bounded block graph in the acute case.

The final theorem removes the acuteness hypothesis from the complex bounded
Riccati block diagonalization result.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- The ambient angular operator associated with a bounded block graph. -/
noncomputable def blockAngularOperator (X : E0 →L[𝕜] E1) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
  blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) ∘L X ∘L
    WithLp.fstL 2 𝕜 E0 E1

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The block angular operator sends `z` to `X` of its first coordinate, in the second summand. -/
@[simp]
theorem blockAngularOperator_apply (X : E0 →L[𝕜] E1)
    (z : WithLp 2 (E0 × E1)) :
    blockAngularOperator X z =
      blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1)
        (X (WithLp.fst z)) :=
  rfl

/-- The first coordinate inclusion is the orthogonal projection onto the zero
block graph. -/
theorem blockCoordinate0_eq_zeroGraph_starProjection
    (z : WithLp 2 (E0 × E1)) :
    blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.fst z) =
      (blockGraph (0 : E0 →L[𝕜] E1)).starProjection z := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact blockCoordinate0_mem_zeroGraph
      (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.fst z)
  · intro y hy
    have hy0 : WithLp.snd y = 0 :=
      (mem_blockGraph_zero_iff_snd_eq_zero y).mp hy
    simp only [blockCoordinate0_apply, inner_sub_left,
      WithLp.prod_inner_apply]
    change
      (⟪z.ofLp.1, y.ofLp.1⟫_𝕜 + ⟪z.ofLp.2, y.ofLp.2⟫_𝕜) -
        (⟪z.ofLp.1, y.ofLp.1⟫_𝕜 + ⟪0, y.ofLp.2⟫_𝕜) = 0
    change y.ofLp.2 = 0 at hy0
    rw [hy0]
    simp

/-- The zero-graph projection keeps precisely the first coordinate. -/
theorem zeroGraph_starProjection_apply
    (z : WithLp 2 (E0 × E1)) :
    (blockGraph (0 : E0 →L[𝕜] E1)).starProjection z =
      blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.fst z) :=
  (blockCoordinate0_eq_zeroGraph_starProjection z).symm

/-- The ambient block angular operator is angular over the zero graph. -/
theorem blockAngularOperator_isAngularOperator (X : E0 →L[𝕜] E1) :
    IsAngularOperator (blockGraph (0 : E0 →L[𝕜] E1))
      (blockAngularOperator X) := by
  constructor
  · ext z
    change blockAngularOperator X
        ((blockGraph (0 : E0 →L[𝕜] E1)).starProjection z) =
      blockAngularOperator X z
    rw [zeroGraph_starProjection_apply]
    simp [blockAngularOperator]
  · ext z
    change (blockGraph (0 : E0 →L[𝕜] E1)).starProjection
        (blockAngularOperator X z) = 0
    rw [zeroGraph_starProjection_apply]
    simp [blockAngularOperator]

/-- The graph parametrization produced by the zero-graph projection and the
ambient angular operator has the expected two coordinates. -/
theorem zeroGraph_angularParam_apply (X : E0 →L[𝕜] E1)
    (z : WithLp 2 (E0 × E1)) :
    ((Submodule.starProjection (blockGraph (0 : E0 →L[𝕜] E1)) +
        blockAngularOperator X ∘L
          Submodule.starProjection (blockGraph (0 : E0 →L[𝕜] E1))) z) =
      WithLp.toLp 2 (WithLp.fst z, X (WithLp.fst z)) := by
  rw [add_apply, ContinuousLinearMap.comp_apply,
    zeroGraph_starProjection_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [blockAngularOperator]

/-- The graph range of the ambient block angular operator is exactly the
bounded block graph. -/
theorem blockGraph_eq_range_zeroGraph_angularParam (X : E0 →L[𝕜] E1) :
    blockGraph X = LinearMap.range
      (Submodule.starProjection (blockGraph (0 : E0 →L[𝕜] E1)) +
        blockAngularOperator X ∘L
          Submodule.starProjection (blockGraph (0 : E0 →L[𝕜] E1))).toLinearMap := by
  ext z
  constructor
  · intro hz
    have hzrel : WithLp.snd z = X (WithLp.fst z) := by
      change WithLp.toLp 2 (WithLp.fst z, WithLp.snd z) ∈ blockGraph X at hz
      exact (toLp_mem_blockGraph_iff X (WithLp.fst z) (WithLp.snd z)).mp hz
    refine ⟨z, ?_⟩
    change
      (Submodule.starProjection (blockGraph (0 : E0 →L[𝕜] E1)) +
        blockAngularOperator X ∘L
          Submodule.starProjection (blockGraph (0 : E0 →L[𝕜] E1))) z = z
    rw [zeroGraph_angularParam_apply]
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp
    · simpa using hzrel.symm
  · rintro ⟨w, rfl⟩
    change
      (Submodule.starProjection (blockGraph (0 : E0 →L[𝕜] E1)) +
        blockAngularOperator X ∘L
          Submodule.starProjection (blockGraph (0 : E0 →L[𝕜] E1))) w ∈ blockGraph X
    rw [zeroGraph_angularParam_apply]
    exact (toLp_mem_blockGraph_iff X (WithLp.fst w)
      (X (WithLp.fst w))).mpr rfl

/-- Every bounded block graph is acute to the zero graph. -/
theorem zeroGraph_isUniformlyAcute_blockGraph (X : E0 →L[𝕜] E1) :
    IsUniformlyAcute (blockGraph (0 : E0 →L[𝕜] E1)) (blockGraph X) := by
  apply (acute_iff_exists_bounded_angularOperator
    (blockGraph (0 : E0 →L[𝕜] E1)) (blockGraph X)).2
  exact ⟨blockAngularOperator X,
    blockAngularOperator_isAngularOperator X,
    blockGraph_eq_range_zeroGraph_angularParam X⟩

section Complex

variable {E0c : Type*} [NormedAddCommGroup E0c] [InnerProductSpace ℂ E0c]
  [CompleteSpace E0c]
variable {E1c : Type*} [NormedAddCommGroup E1c] [InnerProductSpace ℂ E1c]
  [CompleteSpace E1c]

/-- Every bounded complex Riccati solution yields a canonical unitary block
 diagonalization, with no additional acuteness hypothesis. -/
theorem complex_blockDiagonalization_of_riccati
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0c) (E1 := E1c))
    {X : E0c →L[ℂ] E1c} (hX : SolvesRiccati H X) :
    ∃ W Winv : WithLp 2 (E0c × E1c) →L[ℂ] WithLp 2 (E0c × E1c),
      ∃ D0 : E0c →L[ℂ] E0c, ∃ D1 : E1c →L[ℂ] E1c,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ TauCeti.LinearPMap.IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id ℂ _ ∧
      W ∘L Winv = ContinuousLinearMap.id ℂ _ ∧
      Winv ∘L blockOperator H ∘L W = blockDiagonalOperator D0 D1 := by
  exact complex_blockDiagonalization_of_riccati_of_acute H hX
    (zeroGraph_isUniformlyAcute_blockGraph X)

end Complex

end DavisKahanExt
end TauCeti
