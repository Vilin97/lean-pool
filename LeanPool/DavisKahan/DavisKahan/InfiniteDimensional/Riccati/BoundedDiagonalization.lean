/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedReduction
public import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SpectraBridge.DirectRotationAPI
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Bounded Riccati block diagonalization

This leaf module separates the algebraic diagonalization step from the
construction of the graph rotation.

First, a bounded operator on the Hilbert direct sum is shown to be block
diagonal whenever it preserves the two coordinate summands.  Next, a unitary
which carries those coordinate summands to a reducing graph and its orthogonal
complement transports the block operator to such a coordinate-preserving
operator.  Finally, the proof-complete complex direct rotation supplies that
unitary for an acute pair consisting of the zero graph and the Riccati graph.

The remaining local geometric input is that every bounded graph is acute to
the zero graph.  It is intentionally left as an explicit hypothesis of the
last theorem so that its proof can be isolated from the block algebra.
-/

@[expose] public section

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

/-- Inclusion of the first coordinate into the Hilbert direct sum. -/
noncomputable def blockCoordinate0 : E0 →L[𝕜] WithLp 2 (E0 × E1) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
      (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
    (ContinuousLinearMap.id 𝕜 E0).prod (0 : E0 →L[𝕜] E1)

/-- Inclusion of the second coordinate into the Hilbert direct sum. -/
noncomputable def blockCoordinate1 : E1 →L[𝕜] WithLp 2 (E0 × E1) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
      (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
    (0 : E1 →L[𝕜] E0).prod (ContinuousLinearMap.id 𝕜 E1)

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The first block coordinate embeds `u` as the pair `(u, 0)`. -/
@[simp]
theorem blockCoordinate0_apply (u : E0) :
    blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) u = WithLp.toLp 2 (u, 0) :=
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The second block coordinate embeds `v` as the pair `(0, v)`. -/
@[simp]
theorem blockCoordinate1_apply (v : E1) :
    blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) v = WithLp.toLp 2 (0, v) :=
  rfl

/-- Every bounded block graph is closed and therefore orthogonally
complemented. -/
noncomputable instance blockGraph_hasOrthogonalProjection
    (X : E0 →L[𝕜] E1) : (blockGraph X).HasOrthogonalProjection := by
  set G : E0 →L[𝕜] WithLp 2 (E0 × E1) :=
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
        (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
      (ContinuousLinearMap.id 𝕜 E0).prod X with hG
  have hGmem : ∀ u : E0, G u ∈ blockGraph X := fun u => ⟨u, rfl⟩
  have hGfix : ∀ z ∈ blockGraph X,
      G (WithLp.fstL 2 𝕜 E0 E1 z) = z := by
    intro z hz
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hz
    rw [← hu]
    rfl
  have hclosed : IsClosed ((blockGraph X : Submodule 𝕜 _) :
      Set (WithLp 2 (E0 × E1))) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq y hseq hlim
    have hfix : ∀ n, seq n = G (WithLp.fstL 2 𝕜 E0 E1 (seq n)) :=
      fun n => (hGfix _ (hseq n)).symm
    have hlim2 : Filter.Tendsto seq Filter.atTop
        (nhds (G (WithLp.fstL 2 𝕜 E0 E1 y))) := by
      refine Filter.Tendsto.congr (fun n => (hfix n).symm) ?_
      exact (((G ∘L WithLp.fstL 2 𝕜 E0 E1)).continuous.tendsto y).comp hlim
    have hy : y = G (WithLp.fstL 2 𝕜 E0 E1 y) :=
      tendsto_nhds_unique hlim hlim2
    rw [hy]
    exact hGmem _
  let : CompleteSpace (blockGraph X) := hclosed.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Membership in the zero graph is exactly vanishing of the second
coordinate. -/
theorem mem_blockGraph_zero_iff_snd_eq_zero
    (z : WithLp 2 (E0 × E1)) :
    z ∈ blockGraph (0 : E0 →L[𝕜] E1) ↔ WithLp.snd z = 0 := by
  change WithLp.toLp 2 (WithLp.fst z, WithLp.snd z) ∈
      blockGraph (0 : E0 →L[𝕜] E1) ↔ WithLp.snd z = 0
  simpa using
    (toLp_mem_blockGraph_iff (0 : E0 →L[𝕜] E1)
      (WithLp.fst z) (WithLp.snd z))

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The first coordinate inclusion lands in the zero graph. -/
theorem blockCoordinate0_mem_zeroGraph (u : E0) :
    blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) u ∈ blockGraph (0 : E0 →L[𝕜] E1) := by
  rw [mem_blockGraph_zero_iff_snd_eq_zero]
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The second coordinate inclusion is orthogonal to the zero graph. -/
theorem blockCoordinate1_mem_zeroGraph_orthogonal (v : E1) :
    blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) v ∈
      (blockGraph (0 : E0 →L[𝕜] E1))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hz0 : WithLp.snd z = 0 :=
    (mem_blockGraph_zero_iff_snd_eq_zero z).mp hz
  simp only [blockCoordinate1_apply, WithLp.prod_inner_apply]
  change z.ofLp.2 = 0 at hz0
  rw [hz0]
  simp only [inner_zero_right, inner_zero_left, add_zero]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A vector in the orthogonal complement of the zero graph has zero first
coordinate. -/
theorem fst_eq_zero_of_mem_zeroGraph_orthogonal
    {z : WithLp 2 (E0 × E1)}
    (hz : z ∈ (blockGraph (0 : E0 →L[𝕜] E1))ᗮ) :
    WithLp.fst z = 0 := by
  have horth := (Submodule.mem_orthogonal _ z).mp hz
    (blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.fst z))
    (blockCoordinate0_mem_zeroGraph (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.fst z))
  simp only [blockCoordinate0_apply, WithLp.prod_inner_apply] at horth
  change ⟪z.ofLp.1, z.ofLp.1⟫_𝕜 + ⟪0, z.ofLp.2⟫_𝕜 = 0 at horth
  simp only [inner_zero_left, add_zero] at horth
  change z.ofLp.1 = 0
  exact inner_self_eq_zero.mp horth

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- The two coordinate inclusions reconstruct every direct-sum vector. -/
theorem blockCoordinate0_add_blockCoordinate1
    (z : WithLp 2 (E0 × E1)) :
    blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.fst z) +
        blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.snd z) = z := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp

/-- Diagonal compression of an operator to the first coordinate. -/
noncomputable def blockCompression0
    (T : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) : E0 →L[𝕜] E0 :=
  WithLp.fstL 2 𝕜 E0 E1 ∘L T ∘L blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1)

/-- Diagonal compression of an operator to the second coordinate. -/
noncomputable def blockCompression1
    (T : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) : E1 →L[𝕜] E1 :=
  WithLp.sndL 2 𝕜 E0 E1 ∘L T ∘L blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1)

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A bounded direct-sum operator which preserves both coordinate summands is
exactly the corresponding block-diagonal operator. -/
theorem eq_blockDiagonalOperator_of_preserves_coordinates
    (T : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1))
    (h0 : ∀ u : E0, WithLp.snd (T (blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) u)) = 0)
    (h1 : ∀ v : E1, WithLp.fst (T (blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) v)) = 0) :
    T = blockDiagonalOperator (blockCompression0 T) (blockCompression1 T) := by
  ext z
  let z0 := blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.fst z)
  let z1 := blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) (WithLp.snd z)
  have hz : z0 + z1 = z :=
    blockCoordinate0_add_blockCoordinate1 (𝕜 := 𝕜) z
  have hz0snd : WithLp.snd (T z0) = 0 := by
    simpa only [z0] using h0 (WithLp.fst z)
  have hz1fst : WithLp.fst (T z1) = 0 := by
    simpa only [z1] using h1 (WithLp.snd z)
  calc
    T z = T (z0 + z1) := congrArg T hz.symm
    _ = T z0 + T z1 := map_add T z0 z1
    _ = WithLp.toLp 2
          (blockCompression0 T (WithLp.fst z),
            blockCompression1 T (WithLp.snd z)) := by
      apply (WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).injective
      ext
      · simp only [map_add]
        change
          WithLp.fst (T z0) + WithLp.fst (T z1) =
            blockCompression0 T (WithLp.fst z)
        rw [hz1fst]
        simp [blockCompression0, z0]
      · simp only [map_add]
        change
          WithLp.snd (T z0) + WithLp.snd (T z1) =
            blockCompression1 T (WithLp.snd z)
        rw [hz0snd]
        simp [blockCompression1, z1]
    _ = blockDiagonalOperator (blockCompression0 T) (blockCompression1 T) z := rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Algebraic block diagonalization from a unitary transport of the coordinate
summands to a reducing graph and its orthogonal complement. -/
theorem blockDiagonalization_of_graph_transport
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hX : SolvesRiccati H X)
    (W Winv : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1))
    (hWunit : TauCeti.LinearPMap.IsUnitaryOperator W) (hWinvunit :
      TauCeti.LinearPMap.IsUnitaryOperator Winv)
    (hleft : Winv ∘L W = ContinuousLinearMap.id 𝕜 _)
    (hright : W ∘L Winv = ContinuousLinearMap.id 𝕜 _)
    (hW0 : ∀ u : E0, W (blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) u) ∈ blockGraph X)
    (hW1 : ∀ v : E1, W (blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) v) ∈ (blockGraph X)ᗮ)
    (hWinv0 : ∀ z ∈ blockGraph X,
      Winv z ∈ blockGraph (0 : E0 →L[𝕜] E1))
    (hWinv1 : ∀ z ∈ (blockGraph X)ᗮ,
      Winv z ∈ (blockGraph (0 : E0 →L[𝕜] E1))ᗮ) :
    ∃ D0 : E0 →L[𝕜] E0, ∃ D1 : E1 →L[𝕜] E1,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ TauCeti.LinearPMap.IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id 𝕜 _ ∧
      W ∘L Winv = ContinuousLinearMap.id 𝕜 _ ∧
      Winv ∘L blockOperator H ∘L W = blockDiagonalOperator D0 D1 := by
  let T := Winv ∘L blockOperator H ∘L W
  have hred : ContinuousLinearMap.Reduces (blockOperator H) (blockGraph X) :=
    (blockGraph_reduces_iff_solvesRiccati H X).2 hX
  have hT0 : ∀ u : E0,
      WithLp.snd (T (blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) u)) = 0 := by
    intro u
    have hHg : blockOperator H (W (blockCoordinate0 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) u)) ∈
        blockGraph X := hred.1 _ (hW0 u)
    have hback := hWinv0 _ hHg
    exact (mem_blockGraph_zero_iff_snd_eq_zero _).mp hback
  have hT1 : ∀ v : E1,
      WithLp.fst (T (blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) v)) = 0 := by
    intro v
    have hHg : blockOperator H (W (blockCoordinate1 (𝕜 := 𝕜) (E0 := E0) (E1 := E1) v)) ∈
        (blockGraph X)ᗮ := hred.2 _ (hW1 v)
    have hback := hWinv1 _ hHg
    exact fst_eq_zero_of_mem_zeroGraph_orthogonal hback
  refine ⟨blockCompression0 T, blockCompression1 T,
    hWunit, hWinvunit, hleft, hright, ?_⟩
  exact eq_blockDiagonalOperator_of_preserves_coordinates T hT0 hT1

section Complex

variable {E0c : Type*} [NormedAddCommGroup E0c] [InnerProductSpace ℂ E0c]
  [CompleteSpace E0c]
variable {E1c : Type*} [NormedAddCommGroup E1c] [InnerProductSpace ℂ E1c]
  [CompleteSpace E1c]

/-- Complex bounded block diagonalization by the canonical direct rotation,
assuming the zero graph and the Riccati graph are acute. -/
theorem complex_blockDiagonalization_of_riccati_of_acute
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0c) (E1 := E1c))
    {X : E0c →L[ℂ] E1c} (hX : SolvesRiccati H X)
    (hacute : IsUniformlyAcute
      (blockGraph (0 : E0c →L[ℂ] E1c)) (blockGraph X)) :
    ∃ W Winv : WithLp 2 (E0c × E1c) →L[ℂ] WithLp 2 (E0c × E1c),
      ∃ D0 : E0c →L[ℂ] E0c, ∃ D1 : E1c →L[ℂ] E1c,
      TauCeti.LinearPMap.IsUnitaryOperator W ∧ TauCeti.LinearPMap.IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id ℂ _ ∧
      W ∘L Winv = ContinuousLinearMap.id ℂ _ ∧
      Winv ∘L blockOperator H ∘L W = blockDiagonalOperator D0 D1 := by
  let U := blockGraph (0 : E0c →L[ℂ] E1c)
  let V := blockGraph X
  let W := complexDirectRotation U V hacute
  let Winv := star W
  have hWinvEq : Winv = complexDirectRotation V U hacute.symm := by
    change star
        (_root_.TauCeti.DavisKahan.spectraDirectRotation
          U V hacute) =
      _root_.TauCeti.DavisKahan.spectraDirectRotation
        V U hacute.symm
    exact (_root_.TauCeti.DavisKahan.spectraDirectRotation_reversal
      U V hacute).symm
  have hWunit : TauCeti.LinearPMap.IsUnitaryOperator W :=
    complexDirectRotation_unitary U V hacute
  have hWinvunit : TauCeti.LinearPMap.IsUnitaryOperator Winv := by
    rw [hWinvEq]
    exact complexDirectRotation_unitary V U hacute.symm
  have hleft : Winv ∘L W = ContinuousLinearMap.id ℂ _ := by
    change star (complexDirectRotation U V hacute) ∘L
      complexDirectRotation U V hacute = _
    simpa only [ContinuousLinearMap.one_def] using star_complexDirectRotation_comp_self U V hacute
  have hright : W ∘L Winv = ContinuousLinearMap.id ℂ _ := by
    change complexDirectRotation U V hacute ∘L
      star (complexDirectRotation U V hacute) = _
    simpa only [ContinuousLinearMap.one_def] using complexDirectRotation_comp_star_self U V hacute
  have hW0 : ∀ u : E0c,
      W (blockCoordinate0 (𝕜 := ℂ) (E0 := E0c) (E1 := E1c) u) ∈ V := by
    intro u
    have hmem : blockCoordinate0 (𝕜 := ℂ) (E0 := E0c) (E1 := E1c) u ∈ U :=
      blockCoordinate0_mem_zeroGraph (𝕜 := ℂ) (E0 := E0c) (E1 := E1c) u
    have hmap := complexDirectRotation_maps_subspace U V hacute
    rw [← hmap]
    exact ⟨blockCoordinate0 (𝕜 := ℂ) (E0 := E0c) (E1 := E1c) u, hmem, rfl⟩
  have hW1 : ∀ v : E1c,
      W (blockCoordinate1 (𝕜 := ℂ) (E0 := E0c) (E1 := E1c) v) ∈ Vᗮ := by
    intro v
    have hmem : blockCoordinate1 (𝕜 := ℂ) (E0 := E0c) (E1 := E1c) v ∈ Uᗮ :=
      blockCoordinate1_mem_zeroGraph_orthogonal (𝕜 := ℂ) (E0 := E0c) (E1 := E1c) v
    have hmap := complexDirectRotation_maps_orthogonalComplement U V hacute
    rw [← hmap]
    exact ⟨blockCoordinate1 (𝕜 := ℂ) (E0 := E0c) (E1 := E1c) v, hmem, rfl⟩
  have hWinv0 : ∀ z ∈ V, Winv z ∈ U := by
    intro z hz
    have hmap := star_complexDirectRotation_maps_subspace U V hacute
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  have hWinv1 : ∀ z ∈ Vᗮ, Winv z ∈ Uᗮ := by
    intro z hz
    have hmap := star_complexDirectRotation_maps_orthogonalComplement U V hacute
    rw [← hmap]
    exact ⟨z, hz, rfl⟩
  obtain ⟨D0, D1, hdiag⟩ := blockDiagonalization_of_graph_transport
    H hX W Winv hWunit hWinvunit hleft hright hW0 hW1 hWinv0 hWinv1
  exact ⟨W, Winv, D0, D1, hdiag⟩

end Complex

end DavisKahanExt
end TauCeti
