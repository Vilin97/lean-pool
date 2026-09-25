/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.BlockSum
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ProjectionBlocks
public import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-!
# Davis--Kahan Lemma 6.1

This is the source-faithful infinite-dimensional form of Lemma 6.1.  The two
summands occupy mutually orthogonal initial and final blocks.  Separate weak
majorization of the blocks therefore combines into weak majorization of their
sum.  The converse follows when the two blocks on each side have matching
singular values, exactly as stated in the paper.

The ambient projection block `Ω.starProjection ∘L K ∘L Γ.starProjection` and its
compression `Γ → Ω` are operators between different Hilbert spaces, so the
identifications are recorded with the heterogeneous relation
`SameApproximationSingularSequence`.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A bounded operator occupying one prescribed projection block. -/
def projectionBlock
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E) : E →L[𝕜] E :=
  Ω.starProjection ∘L K ∘L Γ.starProjection

/-- The compression of `K` to the block coordinates `Γ → Ω`. -/
def blockCompression
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection]
    (K : E →L[𝕜] E) : Γ →L[𝕜] Ω :=
  Ω.subtypeL.adjoint ∘L K ∘L Γ.subtypeL

/-- The ambient projection block is the compression conjugated by the canonical
inclusion and its adjoint. -/
theorem projectionBlock_eq_subtypeL_comp
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    projectionBlock Ω Γ K =
      Ω.subtypeL ∘L blockCompression Ω Γ K ∘L Γ.subtypeL.adjoint := by
  rw [projectionBlock, blockCompression, Submodule.adjoint_subtypeL,
    Submodule.adjoint_subtypeL]
  rfl

/-- The ambient projection block and its compression have the same complete
approximation singular sequence. -/
theorem projectionBlock_same_compression
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E) :
    SameApproximationSingularSequence
      (projectionBlock Ω Γ K) (blockCompression Ω Γ K) := by
  rw [projectionBlock_eq_subtypeL_comp]
  exact sameApproximationSingularValues_ambientSubspaceBlock Γ Ω _

/-- The two complementary blocks are unitarily equivalent to the Hilbert
orthogonal block sum of their compressions. -/
theorem projectionBlockPair_same_blockSum
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[𝕜] E) :
    SameApproximationSingularSequence
      (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ L)
      (continuousOrthogonalBlockSum
        (blockCompression Ω Γ K)
        (blockCompression Ωᗮ Γᗮ L)) := by
  refine SameApproximationSingularValues.of_isometricEquiv_comp
    Ω.orthogonalDecomposition Γ.orthogonalDecomposition ?_
  refine ContinuousLinearMap.ext fun x => ?_
  have hΓfst : Γ.orthogonalProjectionOnto ((x.fst : E) + (x.snd : E)) = x.fst := by
    rw [map_add, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal x.snd.2, add_zero]
  have hΓsnd : Γᗮ.orthogonalProjectionOnto ((x.fst : E) + (x.snd : E)) = x.snd := by
    rw [map_add,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (Submodule.le_orthogonal_orthogonal Γ x.fst.2),
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, zero_add]
  have hz : (projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ L)
      (Γ.orthogonalDecomposition.symm x) =
      Ω.starProjection (K (x.fst : E)) + Ωᗮ.starProjection (L (x.snd : E)) := by
    rw [Submodule.orthogonalDecomposition_symm_apply]
    simp only [add_apply, projectionBlock, ContinuousLinearMap.comp_apply]
    rw [Submodule.starProjection_apply Γ, hΓfst,
      Submodule.starProjection_apply Γᗮ, hΓsnd]
  have hcomp₀ : Ω.orthogonalProjectionOnto
      (Ω.starProjection (K (x.fst : E)) + Ωᗮ.starProjection (L (x.snd : E))) =
      blockCompression Ω Γ K x.fst := by
    rw [map_add,
      Submodule.orthogonalProjectionOnto_starProjection_of_le (le_refl Ω),
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (Ωᗮ.starProjection_apply_mem _),
      add_zero, blockCompression, Submodule.adjoint_subtypeL]
    rfl
  have hcomp₁ : Ωᗮ.orthogonalProjectionOnto
      (Ω.starProjection (K (x.fst : E)) + Ωᗮ.starProjection (L (x.snd : E))) =
      blockCompression Ωᗮ Γᗮ L x.snd := by
    rw [map_add,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
        (Submodule.le_orthogonal_orthogonal Ω (Ω.starProjection_apply_mem _)),
      Submodule.orthogonalProjectionOnto_starProjection_of_le (le_refl Ωᗮ),
      zero_add, blockCompression, Submodule.adjoint_subtypeL]
    rfl
  simp only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    hz, Submodule.orthogonalDecomposition_apply, continuousOrthogonalBlockSum_apply,
    hcomp₀, hcomp₁]

/-- **Davis--Kahan 1970, Lemma 6.1, forward direction.** -/
theorem lemma61_all_kyFan
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[𝕜] E)
    (h₀ : ∀ k,
      kyFanApproximationGauge k (projectionBlock Ω Γ K) ≤
        kyFanApproximationGauge k (projectionBlock Ω Γ L))
    (h₁ : ∀ k,
      kyFanApproximationGauge k (projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        kyFanApproximationGauge k (projectionBlock Ωᗮ Γᗮ Ltilde)) :
    ∀ k,
      kyFanApproximationGauge k
          (projectionBlock Ω Γ K +
            projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        kyFanApproximationGauge k
          (projectionBlock Ω Γ L +
            projectionBlock Ωᗮ Γᗮ Ltilde) := by
  intro k
  rw [(projectionBlockPair_same_blockSum Ω Γ K Ktilde).kyFanApproximationGauge_eq k,
    (projectionBlockPair_same_blockSum Ω Γ L Ltilde).kyFanApproximationGauge_eq k]
  refine kyFanApproximationGauge_blockSum_le (fun j => ?_) (fun j => ?_) k
  · rw [← (projectionBlock_same_compression Ω Γ K).kyFanApproximationGauge_eq j,
      ← (projectionBlock_same_compression Ω Γ L).kyFanApproximationGauge_eq j]
    exact h₀ j
  · rw [← (projectionBlock_same_compression Ωᗮ Γᗮ Ktilde).kyFanApproximationGauge_eq j,
      ← (projectionBlock_same_compression Ωᗮ Γᗮ Ltilde).kyFanApproximationGauge_eq j]
    exact h₁ j

/-- Lemma 6.1 for every source-defined unitarily invariant norm. -/
theorem lemma61_every_unitarilyInvariantNorm
    (N : SymmetricNormingFunction)
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[𝕜] E)
    (h₀ : ∀ k,
      kyFanApproximationGauge k (projectionBlock Ω Γ K) ≤
        kyFanApproximationGauge k (projectionBlock Ω Γ L))
    (h₁ : ∀ k,
      kyFanApproximationGauge k (projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        kyFanApproximationGauge k (projectionBlock Ωᗮ Γᗮ Ltilde)) :
    N.extendedGauge
        (projectionBlock Ω Γ K +
          projectionBlock Ωᗮ Γᗮ Ktilde) ≤
      N.extendedGauge
        (projectionBlock Ω Γ L +
          projectionBlock Ωᗮ Γᗮ Ltilde) :=
  N.extendedGauge_le_of_all_kyFan_le
    (lemma61_all_kyFan Ω Γ K Ktilde L Ltilde h₀ h₁)

section MergeEven

/-- A shifted window of an antitone sequence is dominated by the earlier window
of the same length. -/
private theorem sum_Ico_le_sum_Ico_of_antitone
    {a : ℕ → ℝ} (ha : Antitone a) {p q : ℕ} (hpq : p ≤ q) (m : ℕ) :
    ∑ i ∈ Finset.Ico q (q + m), a i ≤ ∑ i ∈ Finset.Ico p (p + m), a i := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  exact Finset.sum_le_sum fun i _ => ha (by omega)

/-- Balanced splits maximise `S r + S (2k - r)` for an antitone summand. -/
private theorem sum_range_add_sum_range_le_two_mul_of_le
    {a : ℕ → ℝ} (ha : Antitone a) {k r : ℕ} (hrk : r ≤ k) :
    (∑ n ∈ Finset.range r, a n) + ∑ n ∈ Finset.range (2 * k - r), a n ≤
      2 * ∑ n ∈ Finset.range k, a n := by
  obtain ⟨m, rfl⟩ : ∃ m, k = r + m := ⟨k - r, by omega⟩
  have hhigh : 2 * (r + m) - r = r + m + m := by omega
  rw [hhigh]
  have hsplit_high :
      (∑ n ∈ Finset.range (r + m), a n) +
          ∑ n ∈ Finset.Ico (r + m) (r + m + m), a n =
        ∑ n ∈ Finset.range (r + m + m), a n := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (Nat.le_add_right _ _)
  have hsplit_low :
      (∑ n ∈ Finset.range r, a n) + ∑ n ∈ Finset.Ico r (r + m), a n =
        ∑ n ∈ Finset.range (r + m), a n := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) (Nat.le_add_right _ _)
  have hwindow :=
    sum_Ico_le_sum_Ico_of_antitone ha (Nat.le_add_right r m) m
  linarith

/-- Balanced splits maximise `S r + S (2k - r)`, without an ordering
assumption on `r`. -/
private theorem sum_range_add_sum_range_le_two_mul
    {a : ℕ → ℝ} (ha : Antitone a) {k r : ℕ} (hr : r ≤ 2 * k) :
    (∑ n ∈ Finset.range r, a n) + ∑ n ∈ Finset.range (2 * k - r), a n ≤
      2 * ∑ n ∈ Finset.range k, a n := by
  rcases le_total r k with h | h
  · exact sum_range_add_sum_range_le_two_mul_of_le ha h
  · have hle : 2 * k - r ≤ k := by omega
    have hkey := sum_range_add_sum_range_le_two_mul_of_le ha hle
    have hcancel : 2 * k - (2 * k - r) = r := by omega
    rw [hcancel] at hkey
    linarith

variable {E₀ E₁ F₀ F₁ : Type v}
  [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [CompleteSpace F₁]

omit [CompleteSpace E₀] [CompleteSpace F₀] in
/-- Approximation singular values decrease with the index. -/
private theorem antitone_approximationSingularValue (A : E₀ →L[𝕜] F₀) :
    Antitone fun n => approximationSingularValue n A := by
  intro m n hmn
  exact_mod_cast A.approximationNumber_antitone hmn

omit [CompleteSpace E₀] [CompleteSpace E₁] [CompleteSpace F₀] [CompleteSpace F₁] in
/-- When the two blocks have identical singular sequences, the even Ky Fan
prefixes of their orthogonal block sum double the prefixes of one block. -/
theorem splitKyFanGauge_two_mul_of_same
    {A : E₀ →L[𝕜] F₀} {B : E₁ →L[𝕜] F₁}
    (h : SameApproximationSingularSequence A B) (k : ℕ) :
    splitKyFanGauge (2 * k) A B = 2 * kyFanApproximationGauge k A := by
  have hgauge : ∀ m, kyFanApproximationGauge m B = kyFanApproximationGauge m A :=
    fun m => (h.kyFanApproximationGauge_eq m).symm
  unfold splitKyFanGauge
  refine le_antisymm (Finset.sup'_le _ _ fun r hr => ?_) ?_
  · have hr2 : r ≤ 2 * k := by
      have := Finset.mem_range.mp hr
      omega
    rw [hgauge]
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    exact sum_range_add_sum_range_le_two_mul
      (antitone_approximationSingularValue A) hr2
  · have hmem : k ∈ Finset.range (2 * k + 1) := Finset.mem_range.mpr (by omega)
    refine le_trans (le_of_eq ?_)
      (Finset.le_sup'
        (f := fun r => kyFanApproximationGauge r A +
          kyFanApproximationGauge (2 * k - r) B) hmem)
    rw [hgauge]
    have hkk : 2 * k - k = k := by omega
    rw [hkk]
    ring

end MergeEven

/-- If the two complementary projection blocks have the same complete
singular-value sequence, every even Ky Fan prefix of their diagonal pair is
twice the corresponding prefix of either block.  This is the multiplicity
bookkeeping used when a self-adjoint off-diagonal operator is compared with
one rectangular corner. -/
theorem diagonalPair_even_kyFan_eq_two_mul_of_same
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[𝕜] E)
    (h : SameApproximationSingularValues
      (projectionBlock Ω Γ K)
      (projectionBlock Ωᗮ Γᗮ K))
    (k : ℕ) :
    kyFanApproximationGauge (2 * k) (diagonalPair Ω Γ K) =
      2 * kyFanApproximationGauge k (projectionBlock Ω Γ K) := by
  have hc₀ := projectionBlock_same_compression Ω Γ K
  have hc₁ := projectionBlock_same_compression Ωᗮ Γᗮ K
  have hcomp : SameApproximationSingularSequence
      (blockCompression Ω Γ K)
      (blockCompression Ωᗮ Γᗮ K) :=
    (hc₀.symm.trans h).trans hc₁
  have hdiag : diagonalPair Ω Γ K =
      projectionBlock Ω Γ K + projectionBlock Ωᗮ Γᗮ K := by
    rw [diagonalPair, projectionBlock, projectionBlock]
  rw [hdiag,
    (projectionBlockPair_same_blockSum Ω Γ K K).kyFanApproximationGauge_eq
      (2 * k),
    kyFanApproximationGauge_continuousOrthogonalBlockSum,
    splitKyFanGauge_two_mul_of_same hcomp k,
    hc₀.kyFanApproximationGauge_eq k]

/-- The converse in Lemma 6.1 under the source paper's matching-singular-value
hypotheses. -/
theorem lemma61_converse
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[𝕜] E)
    (hK : SameApproximationSingularValues
      (projectionBlock Ω Γ K)
      (projectionBlock Ωᗮ Γᗮ Ktilde))
    (hL : SameApproximationSingularValues
      (projectionBlock Ω Γ L)
      (projectionBlock Ωᗮ Γᗮ Ltilde))
    (hsum : ∀ k,
      kyFanApproximationGauge k
          (projectionBlock Ω Γ K +
            projectionBlock Ωᗮ Γᗮ Ktilde) ≤
        kyFanApproximationGauge k
          (projectionBlock Ω Γ L +
            projectionBlock Ωᗮ Γᗮ Ltilde)) :
    ∀ k,
      kyFanApproximationGauge k (projectionBlock Ω Γ K) ≤
        kyFanApproximationGauge k (projectionBlock Ω Γ L) := by
  intro k
  have hcK := projectionBlock_same_compression Ω Γ K
  have hcKt := projectionBlock_same_compression Ωᗮ Γᗮ Ktilde
  have hcL := projectionBlock_same_compression Ω Γ L
  have hcLt := projectionBlock_same_compression Ωᗮ Γᗮ Ltilde
  have hKcomp : SameApproximationSingularSequence
      (blockCompression Ω Γ K) (blockCompression Ωᗮ Γᗮ Ktilde) :=
    (hcK.symm.trans hK).trans hcKt
  have hLcomp : SameApproximationSingularSequence
      (blockCompression Ω Γ L) (blockCompression Ωᗮ Γᗮ Ltilde) :=
    (hcL.symm.trans hL).trans hcLt
  have htwiceK :
      kyFanApproximationGauge (2 * k)
          (projectionBlock Ω Γ K +
            projectionBlock Ωᗮ Γᗮ Ktilde) =
        2 * kyFanApproximationGauge k (projectionBlock Ω Γ K) := by
    rw [(projectionBlockPair_same_blockSum Ω Γ K Ktilde).kyFanApproximationGauge_eq
        (2 * k),
      kyFanApproximationGauge_continuousOrthogonalBlockSum,
      splitKyFanGauge_two_mul_of_same hKcomp k,
      hcK.kyFanApproximationGauge_eq k]
  have htwiceL :
      kyFanApproximationGauge (2 * k)
          (projectionBlock Ω Γ L +
            projectionBlock Ωᗮ Γᗮ Ltilde) =
        2 * kyFanApproximationGauge k (projectionBlock Ω Γ L) := by
    rw [(projectionBlockPair_same_blockSum Ω Γ L Ltilde).kyFanApproximationGauge_eq
        (2 * k),
      kyFanApproximationGauge_continuousOrthogonalBlockSum,
      splitKyFanGauge_two_mul_of_same hLcomp k,
      hcL.kyFanApproximationGauge_eq k]
  have h := hsum (2 * k)
  rw [htwiceK, htwiceL] at h
  linarith

end

end ExactSinTheta
end DavisKahan
end TauCeti
