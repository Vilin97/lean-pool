/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.DoubleAngleFunctionalCalculus
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.TrialResidual
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.DoubleAngleSpectrum
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.ReflectedDefectDoubling
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative

/-! # Sin Two Theta Ambient -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The whole-space half of the `sin 2Θ` theorem

Section 2 of Davis--Kahan 1970 states the `sin 2Θ` theorem with **two**
conclusions,

`δ ‖sin 2Θ₀‖ ≤ 2‖R‖`  and  `δ ‖sin 2Θ‖ ≤ 2‖H‖`,

for every unitarily invariant norm.  The directed `Θ₀` half is already in the
build.  This module proves the ambient `Θ` half, which is equation (7.5) of the
paper's Section 7 proof.

## The route

Write `X` for the reflection through the second subspace.  `X` is a self-adjoint
unitary, so `X A X` has the *same* compression spectra on the reflected subspace
`X U` that `A` has on `U`, and the `sin Θ` estimate applies verbatim to the pair
`(U, X U)` with perturbation `X A X - A`.  The displacement `X A X - A` equals
`X H X - H` up to sign, hence has gauge at most `2` times that of `H`.  The
geometric input is that the pair `(U, X U)` realises the *doubled* angle,

`|P_{X U} - P_U| = sin 2Θ`,

as an operator identity, proved in
`DavisKahan/Geometry/Angle/DoubleAngleFunctionalCalculus.lean`.  Only the operator-norm form
of that identification was previously available, which is not enough for an
arbitrary unitarily invariant norm.

The two directed estimates are coupled by Lemma 6.1 and contracted by Lemma 6.2,
exactly as in Proposition 6.1 — not by a triangle inequality, so the constant is
the paper's `2` and not `4`.

## Convention

Following the repository's existing `sin 2Θ` development
(`DavisKahan/InfiniteDimensional/DoubleAngleSpectrum.lean`), the internal
spectral gap is carried by `A` on its reducing subspace `U`, and `V` is the
reducing subspace of the comparison operator `B`.  The printed theorem carries
the gap on `A + H` at `QH`; the two readings differ only by exchanging the roles
of the two operators, under which `‖H‖` is unchanged.

## Main results

* `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_kyFan_complex`: the Ky Fan form,
  `δ · kyFan_k (sin 2Θ) ≤ 2 · kyFan_k (B - A)` for every `k`.
* `TauCeti.DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_complex`: the source form,
  `δ · N (sin 2Θ) ≤ 2 · N (B - A)` for every unitarily invariant norm `N` in the
  paper's sense.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: the `sin 2Θ` theorem of Section 2
  and its proof in Section 7, equations (7.1)--(7.5).
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- Equal subspaces have equal orthogonal-projection operators.  Keeping this
as an operator equality avoids dependent rewrites through
`HasOrthogonalProjection`. -/
private theorem starProjection_eq_of_submodule_eq
    {U W : Submodule ℂ E} [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (h : U = W) : U.starProjection = W.starProjection := by
  cases h
  rfl

/-! ### The sharp block form of the bounded `sin Θ` estimate -/

/-- **The bounded `sin Θ` estimate at genuine spectra, before the perturbation
block is contracted.**  `sinTheta_spectrum_gauge` finishes by replacing the
projected perturbation block with the whole perturbation; Lemma 6.1 needs the
estimate one step earlier, block against block, which is what the Sylvester
engine actually produces. -/
theorem sinTheta_spectrum_block_gauge
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    d * N.gaugeReal (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) ≤
      N.gaugeReal (Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL) :=
  (mem_and_gauge_sylvester_le_of_spectrum_intervalExterior N
    (isSelfAdjoint_compressOperator hB Vᗮ)
    (isSelfAdjoint_compressOperator hA U)
    hd hab hUspec hVspec (compress_sylvester_of_reduces hU hV)
    (N.comp_mem _ _ hMem)).2

/-- The scaled identity block, in coordinates. -/
theorem blockCompression_smul_one (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection]  (c : ℂ) :
    blockCompression Ω Γ (c • (1 : E →L[ℂ] E)) =
      c • (Ω.orthogonalProjectionOnto ∘L Γ.subtypeL) := by
  rw [blockCompression, Submodule.adjoint_subtypeL]
  ext x
  simp

/-- A perturbation block, in coordinates. -/
theorem blockCompression_apply (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection]
    (K : E →L[ℂ] E) :
    blockCompression Ω Γ K =
      Ω.orthogonalProjectionOnto ∘L K ∘L Γ.subtypeL := by
  rw [blockCompression, Submodule.adjoint_subtypeL]

/-- **The sharp block estimate, ambient and at every Ky Fan level.**  This is the
hypothesis shape Lemma 6.1 consumes. -/
theorem sinTheta_spectrum_block_all_kyFan
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x) :
    ∀ k : ℕ,
      kyFanApproximationGauge k
          (projectionBlock Vᗮ U (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E))) ≤
        kyFanApproximationGauge k (projectionBlock Vᗮ U (B - A)) := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    have hdnorm : ‖((d : ℝ) : ℂ)‖ = d := by simp [abs_of_pos hd]
    have hraw := sinTheta_spectrum_block_gauge
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk).toSymmetricOperatorIdealFamily
      hA hB hU hV hd hab hUspec hVspec
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hk (B - A))
    rw [FanDominantIdealFamily.toSymmetric_gaugeReal,
      FanDominantIdealFamily.toSymmetric_gaugeReal,
      KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at hraw
    have hone := (projectionBlock_same_compression Vᗮ U
      (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E))).kyFanApproximationGauge_eq k
    have hpert :=
      (projectionBlock_same_compression Vᗮ U (B - A)).kyFanApproximationGauge_eq k
    rw [hone, hpert, blockCompression_smul_one, blockCompression_apply,
      kyFanApproximationGauge_smul, hdnorm]
    exact hraw

/-! ### The sharp symmetric `sin Θ` theorem at genuine spectra -/

section Symmetric

variable {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The symmetric bounded `sin Θ` theorem at genuine spectra, sharp.**  Both
directed spectral configurations give `δ · gauge (sin Θ) ≤ gauge (B - A)` for the
*ambient* sine `|P_V - P_U|`, with constant `1`.

`sinTheta_spectrum_gauge_symmetric` proves the same statement with constant `2`,
by a triangle inequality on the two directed cross blocks.  Here the two blocks
are coupled by Lemma 6.1 and contracted by Lemma 6.2 instead, which is the
paper's argument for Proposition 6.1 and loses nothing. -/
theorem symmetric_sinTheta_spectrum_all_kyFan
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hVspec : spectrum ℝ (compressOperator V B) ⊆ Set.Icc a b)
    (hVspec' : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x) :
    ∀ k : ℕ,
      d * kyFanApproximationGauge k
          ((V.starProjection - U.starProjection).modulus) ≤
        kyFanApproximationGauge k (B - A) := by
  intro k
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  have hdnorm : ‖((d : ℝ) : ℂ)‖ = d := by simp [abs_of_pos hd]
  have hpertsa : IsSelfAdjoint (B - A) := hB.sub hA
  have hforward := sinTheta_spectrum_block_all_kyFan hA hB hU hV hd hab
    hUspec hVspec'
  have hreverse := sinTheta_spectrum_block_all_kyFan hB hA hV hU hd hab
    hVspec hUspec'
  -- the identity blocks, computed
  have hid₁ : projectionBlock Uᗮᗮ Vᗮ (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
      ((d : ℝ) : ℂ) • (U.starProjection ∘L Vᗮ.starProjection) := by
    simp only [hUperp, projectionBlock]
    ext x
    simp
  have hid₂ : projectionBlock Vᗮ U (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
      ((d : ℝ) : ℂ) • (Vᗮ.starProjection ∘L U.starProjection) := by
    simp only [projectionBlock]
    ext x
    simp
  have hswap : U.starProjection ∘L Vᗮ.starProjection =
      (Vᗮ.starProjection ∘L U.starProjection).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection U).adjoint_eq,
      (isSelfAdjoint_starProjection Vᗮ).adjoint_eq]
  have hcombine := lemma61_all_kyFan Uᗮ V
    (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E))
    (B - A) (B - A)
    (fun j => by
      have h := hreverse j
      have hblock : projectionBlock Uᗮ V (A - B) =
          -projectionBlock Uᗮ V (B - A) := by
        rw [projectionBlock, projectionBlock,
          show A - B = -(B - A) from by abel]
        ext x
        simp
      rw [hblock, kyFanApproximationGauge_neg] at h
      exact h)
    (fun j => by
      have h := hforward j
      have hblock : projectionBlock Uᗮᗮ Vᗮ (B - A) =
          (projectionBlock Vᗮ U (B - A)).adjoint := by
        simp only [hUperp, projectionBlock]
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
          (isSelfAdjoint_starProjection U).adjoint_eq,
          (isSelfAdjoint_starProjection Vᗮ).adjoint_eq,
          hpertsa.adjoint_eq]
        rfl
      rw [hblock, kyFanApproximationGauge_adjoint, hid₁, hswap,
        kyFanApproximationGauge_smul, kyFanApproximationGauge_adjoint]
      rw [hid₂, kyFanApproximationGauge_smul] at h
      exact h) k
  -- the two identity blocks add up to the cross sine sum
  have hcross :
      projectionBlock Uᗮ V (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) +
          projectionBlock Uᗮᗮ Vᗮ (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
        ((d : ℝ) : ℂ) • crossSineSum U V := by
    simp only [hUperp]
    ext x
    simp [projectionBlock, crossSineSum, smul_add]
  rw [hcross] at hcombine
  have hpinch := diagonalPair_all_kyFan_le Uᗮ V (B - A) k
  have hsine : kyFanApproximationGauge k (crossSineSum U V) =
      kyFanApproximationGauge k
        ((V.starProjection - U.starProjection).modulus) := by
    rw [(crossSineSum_same_projectionDiff U V).kyFanApproximationGauge_eq k]
    exact ((modulus_hasSameApproximationNumbers
      (V.starProjection - U.starProjection)).kyFanGauge_eq k).symm
  rw [kyFanApproximationGauge_smul, hdnorm, hsine] at hcombine
  exact hcombine.trans hpinch

end Symmetric

/-! ### The whole-space `sin 2Θ` theorem -/

section WholeSpace

variable {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [U.HasOrthogonalProjection] [CompleteSpace E] in
/-- The reflected configuration has the transported compression spectrum. -/
private theorem reflected_spectra (A : E →L[ℂ] E) (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (compressOperator
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))
        (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator U A) :=
  spectrum_compressOperator_map U A V.reflection

omit [U.HasOrthogonalProjection] [CompleteSpace E] in
/-- The reflected configuration on the orthogonal complement. -/
private theorem reflected_spectra_orthogonal (A : E →L[ℂ] E)
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectrum ℝ (compressOperator
        (U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))ᗮ
        (conjByIsometryEquiv V.reflection A)) =
      spectrum ℝ (compressOperator Uᗮ A) :=
  (spectrum_compressOperator_congr
      (Submodule.map_orthogonal_equiv U V.reflection).symm _).trans
    (spectrum_compressOperator_map Uᗮ A V.reflection)

omit [U.HasOrthogonalProjection] in
/-- The reflection displacement is bounded by twice the perturbation, at every
Ky Fan level: `X A X - A = X H X - H` up to sign, and `X` is unitary. -/
private theorem kyFan_reflectionDisplacement_le
    (hV : B.Reduces V) (k : ℕ) :
    kyFanApproximationGauge k (conjByIsometryEquiv V.reflection A - A) ≤
      2 * kyFanApproximationGauge k (B - A) := by
  have hdefect : conjByIsometryEquiv V.reflection A - A =
      V.reflectionOperator ∘L (A - B) ∘L
          V.reflectionOperator - (A - B) := by
    rw [conjByReflection_sub_eq_reflectionDefect,
      reflectionDefect_eq_perturbationDefect A B V hV]
  have hAB : kyFanApproximationGauge k (A - B) =
      kyFanApproximationGauge k (B - A) := by
    rw [show A - B = -(B - A) from by abel, kyFanApproximationGauge_neg]
  have h0 : 0 ≤ kyFanApproximationGauge k (A - B) :=
    kyFanApproximationGauge_nonneg k _
  have h1 : ‖(V.reflectionOperator : E →L[ℂ] E)‖ ≤ 1 := by
    exact_mod_cast Submodule.norm_reflectionOperator_le_one V
  have hconj : kyFanApproximationGauge k
      (V.reflectionOperator ∘L (A - B) ∘L
        V.reflectionOperator) ≤
      kyFanApproximationGauge k (A - B) := by
    refine (kyFanApproximationGauge_comp_le k _ _ _).trans ?_
    calc ‖(V.reflectionOperator : E →L[ℂ] E)‖ *
          kyFanApproximationGauge k (A - B) *
          ‖(V.reflectionOperator : E →L[ℂ] E)‖
        ≤ 1 * kyFanApproximationGauge k (A - B) * 1 := by
          gcongr
      _ = kyFanApproximationGauge k (A - B) := by ring
  have hsplit : kyFanApproximationGauge k
      (V.reflectionOperator ∘L (A - B) ∘L
        V.reflectionOperator - (A - B)) ≤
      kyFanApproximationGauge k
        (V.reflectionOperator ∘L (A - B) ∘L
          V.reflectionOperator) +
        kyFanApproximationGauge k (A - B) := by
    have h := kyFanApproximationGauge_add_le k
      (V.reflectionOperator ∘L (A - B) ∘L
        V.reflectionOperator) (-(A - B))
    rwa [← sub_eq_add_neg, kyFanApproximationGauge_neg] at h
  rw [hdefect]
  rw [hAB] at hconj hsplit
  linarith

/-- **The whole-space `sin 2Θ` theorem, Ky Fan form.**  Equation (7.5) of
Davis--Kahan 1970 at every finite Ky Fan gauge. -/
theorem sinTwoTheta_ambient_bounded_kyFan_complex
    (hA : IsSelfAdjoint A) (_hB : IsSelfAdjoint B)
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x) :
    ∀ k : ℕ,
      d * kyFanApproximationGauge k (sinTwoAngleOperatorC U V) ≤
        2 * kyFanApproximationGauge k (B - A) := by
  intro k
  have hkey := symmetric_sinTheta_spectrum_all_kyFan hA
      (isSelfAdjoint_conjByIsometryEquiv V.reflection hA) hU
      (hU.map_isometryEquiv V.reflection) hd hab hUspec hUspec'
      (by rw [reflected_spectra A U V]; exact hUspec)
      (by rw [reflected_spectra_orthogonal A U V]; exact hUspec') k
  rw [← directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub U V] at hkey
  exact hkey.trans (kyFan_reflectionDisplacement_le hV k)

/-- **The sharp factor two for a reflection defect, at every Ky Fan gauge.**

Read between the exact subspace `U` and the mirror of its complement, the
reflection defect of a bounded self-adjoint `S` through `V` costs at most
*twice* one off-diagonal block of `S`, not four times it.

The two complementary defect blocks have matching singular sequences, so an even
Ky Fan prefix of their pinched sum is exactly twice the odd prefix of one of
them; the same multiplicity identity applied to the trial off-diagonal pair of
`S` removes the second copy.  A triangle inequality on the two off-diagonal
blocks would give four.

This is the geometric half of the directed residual `sin 2Θ₀` estimate; it
mentions no spectral gap, so it serves both the bounded theorem below and the
unbounded directed residual theorem, where `S` is the ambient off-diagonal part
of the trial residual rather than a bounded ambient operator. -/
theorem kyFan_reflectedDefectBlock_le_two_mul_offDiagonalBlock
    {S : E →L[ℂ] E} (hS : IsSelfAdjoint S) (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (k : ℕ) :
    kyFanApproximationGauge k
        ((Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection ∘L
          (conjByIsometryEquiv V.reflection S - S) ∘L U.starProjection) ≤
      2 * kyFanApproximationGauge k
        (Vᗮ.starProjection ∘L S ∘L V.starProjection) := by
  rw [conjByReflection_sub_eq_reflectionDefect]
  exact kyFan_reflectionDefectBlock_le_two_mul hS U V k

/-- **Sharp directed residual `sin 2Θ₀`, Ky Fan form.**

Reflect the exact reducing subspace through the trial subspace.  A one-sided
`sin Θ` spectral estimate bounds one reflected overlap block by one block of
the reflection defect.  The two complementary defect blocks have matching
singular sequences; taking an even Ky Fan prefix, pinching, and then using the
same multiplicity identity for the trial off-diagonal pair removes the second
copy.  The result is the printed factor `2`, rather than the factor `4` from a
triangle inequality on the two off-diagonal blocks. -/
theorem sinTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (M : V →L[ℂ] V) :
    ∀ k : ℕ,
      d * kyFanApproximationGauge k (sinTwoThetaIdealBlock U V) ≤
        2 * kyFanApproximationGauge k (residual A V.subtypeL M) := by
  intro k
  let W := U.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)
  let D := conjByIsometryEquiv V.reflection A - A
  have hB : IsSelfAdjoint (conjByIsometryEquiv V.reflection A) :=
    isSelfAdjoint_conjByIsometryEquiv V.reflection hA
  have hW : ContinuousLinearMap.Reduces (conjByIsometryEquiv V.reflection A) W :=
    hU.map_isometryEquiv V.reflection
  have hWspec : spectrum ℝ (compressOperator W
      (conjByIsometryEquiv V.reflection A)) ⊆ Set.Icc a b := by
    rw [reflected_spectra A U V]
    exact hUspec
  have hWspec' : ∀ x ∈ spectrum ℝ (compressOperator Wᗮ
      (conjByIsometryEquiv V.reflection A)),
      x ≤ a - d ∨ b + d ≤ x := by
    intro x hx
    rw [reflected_spectra_orthogonal A U V] at hx
    exact hUspec' x hx
  have hraw := sinTheta_spectrum_block_all_kyFan hA hB hU hW hd hab
    hUspec hWspec' k
  have hperp : Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E) = Wᗮ := by
    exact Submodule.map_orthogonal_equiv U V.reflection
  have hreflectedPerpProj :
      (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection =
        Wᗮ.starProjection :=
    starProjection_eq_of_submodule_eq hperp
  have hsinAdj : (sinTwoThetaIdealBlock U V).adjoint =
      Wᗮ.starProjection ∘L U.starProjection := by
    rw [sinTwoThetaIdealBlock, ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection
        (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E))).adjoint_eq,
      (isSelfAdjoint_starProjection U).adjoint_eq, hreflectedPerpProj]
  have hleftBlock : projectionBlock Wᗮ U
      (((d : ℝ) : ℂ) • (1 : E →L[ℂ] E)) =
      ((d : ℝ) : ℂ) • (sinTwoThetaIdealBlock U V).adjoint := by
    rw [projectionBlock, hsinAdj]
    ext x
    simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self,
      map_smul]
  have hdnorm : ‖((d : ℝ) : ℂ)‖ = d := by simp [abs_of_pos hd]
  rw [hleftBlock, kyFanApproximationGauge_smul,
    kyFanApproximationGauge_adjoint, hdnorm] at hraw
  have hblockDefect : kyFanApproximationGauge k
      (projectionBlock Wᗮ U D) ≤
      2 * kyFanApproximationGauge k
        (Vᗮ.starProjection ∘L A ∘L V.starProjection) := by
    have hperp : Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E) = Wᗮ :=
      Submodule.map_orthogonal_equiv U V.reflection
    have h := kyFan_reflectedDefectBlock_le_two_mul_offDiagonalBlock hA U V k
    rwa [show (Uᗮ.map (V.reflection.toLinearEquiv : E →ₗ[ℂ] E)).starProjection ∘L
          (conjByIsometryEquiv V.reflection A - A) ∘L U.starProjection =
        projectionBlock Wᗮ U D by
      unfold projectionBlock
      rw [starProjection_eq_of_submodule_eq hperp]] at h
  have hX : IsometricEmbedding (V.subtypeL : V →L[ℂ] E) := fun x => rfl
  have hP : V.subtypeL ∘L V.subtypeL.adjoint = V.starProjection := by
    ext x
    rw [ContinuousLinearMap.comp_apply, Submodule.adjoint_subtypeL]
    rfl
  have hQV : Vᗮ.starProjection ∘L V.subtypeL = 0 := by
    ext v
    change Vᗮ.starProjection (v : E) = 0
    rw [Submodule.starProjection_orthogonal_apply,
      V.starProjection_eq_self_iff.mpr v.property, sub_self]
  have hfactor : Vᗮ.starProjection ∘L A ∘L V.starProjection =
      (Vᗮ.starProjection ∘L residual A V.subtypeL M) ∘L
        V.subtypeL.adjoint := by
    rw [← hP]
    apply ContinuousLinearMap.ext
    intro x
    have hzero :
        Vᗮ.starProjection (V.subtypeL (M (V.subtypeL.adjoint x))) = 0 := by
      have hz := congrArg
        (fun T : V →L[ℂ] E => T (M (V.subtypeL.adjoint x))) hQV
      simpa only [ContinuousLinearMap.comp_apply, zero_apply]
        using hz
    change
      Vᗮ.starProjection (A (V.subtypeL (V.subtypeL.adjoint x))) =
        Vᗮ.starProjection
          ((A ∘L V.subtypeL - V.subtypeL ∘L M) (V.subtypeL.adjoint x))
    rw [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, map_sub, hzero, sub_zero]
  have hcrossKyFan : kyFanApproximationGauge k
      (Vᗮ.starProjection ∘L A ∘L V.starProjection) ≤
      kyFanApproximationGauge k (residual A V.subtypeL M) := by
    have hcomp := kyFanApproximationGauge_comp_le k Vᗮ.starProjection
      (residual A V.subtypeL M) V.subtypeL.adjoint
    calc
      kyFanApproximationGauge k
          (Vᗮ.starProjection ∘L A ∘L V.starProjection) =
          kyFanApproximationGauge k
            ((Vᗮ.starProjection ∘L residual A V.subtypeL M) ∘L
              V.subtypeL.adjoint) := congrArg (kyFanApproximationGauge k) hfactor
      _ ≤ ‖Vᗮ.starProjection‖ *
          kyFanApproximationGauge k (residual A V.subtypeL M) *
          ‖V.subtypeL.adjoint‖ := hcomp
      _ ≤ 1 * kyFanApproximationGauge k (residual A V.subtypeL M) * 1 := by
        have hproj : ‖(Vᗮ.starProjection : E →L[ℂ] E)‖ ≤ 1 :=
          Vᗮ.starProjection_norm_le
        have hadj : ‖V.subtypeL.adjoint‖ ≤ 1 :=
          (TauCeti.DavisKahan.BoundedOperator.isometry_and_adjoint_norm_le_one
            V.subtypeL hX).2
        have hnonneg : 0 ≤ kyFanApproximationGauge k (residual A V.subtypeL M) :=
          kyFanApproximationGauge_nonneg k (residual A V.subtypeL M)
        have hleft :
            ‖(Vᗮ.starProjection : E →L[ℂ] E)‖ *
                kyFanApproximationGauge k (residual A V.subtypeL M) ≤
              1 * kyFanApproximationGauge k (residual A V.subtypeL M) :=
          mul_le_mul_of_nonneg_right hproj hnonneg
        exact mul_le_mul hleft hadj (norm_nonneg _) (by simpa using hnonneg)
      _ = kyFanApproximationGauge k (residual A V.subtypeL M) := by simp
  calc
    d * kyFanApproximationGauge k (sinTwoThetaIdealBlock U V)
        ≤ kyFanApproximationGauge k (projectionBlock Wᗮ U D) := hraw
    _ ≤ 2 * kyFanApproximationGauge k
        (Vᗮ.starProjection ∘L A ∘L V.starProjection) := hblockDefect
    _ ≤ 2 * kyFanApproximationGauge k (residual A V.subtypeL M) := by
      gcongr

/-- **The directed residual `sin 2Θ₀` theorem for every source unitarily
invariant norm.**  This is the paper-norm lift of
`sinTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex`, retaining the sharp factor `2`.

The residual acts from the trial subspace into the ambient space, whereas the
canonical doubled-angle block is ambient-to-ambient.  Before invoking the
homogeneous Fan-dominance adapter, extend the residual by zero on `Vᗮ` using
`V.subtypeL.adjoint`.  This preserves its complete approximation-singular
sequence, hence every paper norm, and keeps the norm comparison within one
operator type. -/
theorem sinTwoTheta_directed_boundedResidual_blockRepresentative_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (M : V →L[ℂ] V)
    (hMem : N.Mem (residual A V.subtypeL M)) :
    N.Mem (sinTwoThetaIdealBlock U V) ∧
      d * N.gauge (sinTwoThetaIdealBlock U V) ≤
        2 * N.gauge (residual A V.subtypeL M) := by
  let R : V →L[ℂ] E := residual A V.subtypeL M
  let R0 : E →L[ℂ] E := R ∘L V.subtypeL.adjoint
  have hsameR : SameApproximationSingularSequence R0 R := by
    exact sameApproximationSingularValues_extendDomainByZero V R
  have htransport := hsameR.normingMem_iff_and_gauge_eq N
  have hMem0 : N.Mem R0 := htransport.1.mpr hMem
  have hgauge : N.gauge R0 = N.gauge R := htransport.2
  have htwo : ‖((2 : ℝ) : ℂ)‖ = 2 := by norm_num
  have hscaled : ∀ k : ℕ,
      d * kyFanApproximationGauge k (sinTwoThetaIdealBlock U V) ≤
        kyFanApproximationGauge k (((2 : ℝ) : ℂ) • R0) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo,
      hsameR.kyFanApproximationGauge_eq k]
    exact sinTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex
      (A := A) (U := U) (V := V) hA hU hd hab hUspec hUspec' M k
  have hMem2 : N.Mem (((2 : ℝ) : ℂ) • R0) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hMem0 h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hd hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rw [N.gauge_smul _ hMem0, htwo, hgauge] at hle
  exact hle

/-- **The whole-space `sin 2Θ` theorem for every source unitarily invariant
norm**: `δ ‖sin 2Θ‖ ≤ 2 ‖H‖`, the second conclusion of the Section 2 `sin 2Θ`
theorem and equation (7.5) of Section 7. -/
theorem sinTwoTheta_ambient_bounded_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (sinTwoAngleOperatorC U V) ∧
      d * N.gauge (sinTwoAngleOperatorC U V) ≤
        2 * N.gauge (B - A) := by
  have htwo : ‖((2 : ℝ) : ℂ)‖ = 2 := by norm_num
  have hscaled : ∀ k : ℕ,
      d * kyFanApproximationGauge k (sinTwoAngleOperatorC U V) ≤
        kyFanApproximationGauge k (((2 : ℝ) : ℂ) • (B - A)) := by
    intro k
    rw [kyFanApproximationGauge_smul, htwo]
    exact sinTwoTheta_ambient_bounded_kyFan_complex hA hB hU hV hd hab hUspec hUspec' k
  have hMem2 : N.Mem (((2 : ℝ) : ℂ) • (B - A)) := by
    intro htop
    rw [N.extendedGauge_smul, htwo] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hMem h
    · exact absurd h (by simp)
  obtain ⟨hmem, hle⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hd hMem2 hscaled
  refine ⟨hmem, ?_⟩
  rwa [N.gauge_smul _ hMem, htwo] at hle

end WholeSpace

end

end DavisKahan1970
end TauCeti
