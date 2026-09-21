/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81Approximation
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.BlockShift
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81Real

/-! # Theorem81Approximation Real -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.1(ii) over a REAL Hilbert space

The printed standing assumption is that `H` is a Hilbert space *real or
complex*, with finite dimension only a special case.  `Section8PartII.lean`
proves part (ii) over `ℂ` at unrestricted dimension; this module carries it to
`ℝ`, also at unrestricted dimension.

## Why this is a descent and not a re-proof

The block algebra of part (ii) is already `RCLike`-generic in
`Section8PartII.lean`, so the *statements* below are the same theorems read at
`𝕜 = ℝ`; nothing is weakened and no constant is lost.  What is genuinely complex
is the branch: `canonicalLowBranch` is the bounded self-adjoint spectral
subspace, built from the complex projection-valued measure.

The real branch is not an arbitrary reducing subspace either.  It is
`realBoundedSpectralSubspaceIicOfGap`, the descent of the *actual* complex
spectral branch across the printed gap, and
`complexifySubmodule_realBoundedSpectralSubspaceIicOfGap` identifies its
complexification with `canonicalLowBranch` on the nose.  That identification is
what makes the transport below exact:

* `complexify_upperBlockShift` and `complexify_cosineBlock` (with their lower
  companions) carry the four block operators across `complexify`;
* `approximationNumber_complexify` and `norm_complexify` are equalities, not
  estimates, so every approximation number and the bound norm `‖C₁‖₁` are
  preserved exactly.

The one thing this module does *not* do is re-elaborate the Weyl step
`approximationNumber_mono_of_form_le` over `ℝ`.  That step squares through
`TauCeti.ApproximationNumber.approximationNumber_gramOperator_complex`, whose whole
layer is defined only over `ℂ` (see the docstring of
`Section8/CompressionApproximation.lean`), and descending the finished
inequality is both shorter and lossless.

## The branch, named without assuming a conclusion

`canonicalLowBranchReal` takes exactly the printed real hypotheses and no more.
In particular the spectral repulsion `realSpectrum (A + K) ⊆ Iic α ∪ Ici (α+δ)`,
which `realBoundedSpectralSubspaceIicOfGap` needs in order to *name* the branch,
is a conclusion of Theorem 8.1 and is proved here
(`theorem8_1_spectralRepulsion_real`) rather than demanded from the caller.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open Set
open scoped InnerProductSpace
open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Foundation
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! ### The real branch -/

/-- **Spectral repulsion over `ℝ`.**  The printed open gap contains no real
spectrum of the perturbed operator.

This is `Theorem81ConclusionReal.spectral_repulsion` isolated, so that the real
branch below can be *named* from the printed hypotheses alone rather than by
taking a conclusion of Theorem 8.1 as a caller-supplied hypothesis. -/
theorem theorem8_1_spectralRepulsion_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    realSpectrum (A + K) ⊆ Set.Iic alpha ∪ Set.Ici (alpha + delta) := by
  obtain ⟨_, _, hconc⟩ :=
    theorem8_1_canonicalBranch_real A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp
  exact hconc.spectral_repulsion

/-- **The real canonical low branch of Theorem 8.1.**

The real descent of the genuine bounded complex spectral subspace of `A + K`
for the closed half-line `Iic α`.  Its arguments are exactly the printed real
hypotheses: the spectral repulsion needed to select the branch is proved, not
assumed. -/
def canonicalLowBranchReal
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Submodule ℝ E :=
  realBoundedSpectralSubspaceIicOfGap (A + K) (hA.add hK) alpha delta hdelta
    (theorem8_1_spectralRepulsion_real A K P hdelta hA hK hAP hPlow hPhigh hKP
      hKPperp)

/-- The real canonical low branch is the range of an idempotent, hence closed,
so it carries its orthogonal projection. -/
instance canonicalLowBranchReal_hasOrthogonalProjection
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
      hKPperp).HasOrthogonalProjection :=
  realBoundedSpectralSubspaceIicOfGap_hasOrthogonalProjection _ _ _ _ _ _

/-- **The real branch is the descent of the complex one.**

Its complexification is exactly `canonicalLowBranch`, the branch Theorem 8.1's
complex existence half selects.  This is the identity that makes the transport
of parts (ii) and (iii) exact rather than approximate. -/
theorem complexifySubmodule_canonicalLowBranchReal
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    complexifySubmodule
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) =
      canonicalLowBranch (complexify A + complexify K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (((complexify_isSelfAdjoint_iff A).2 hA).add
            ((complexify_isSelfAdjoint_iff K).2 hK))) alpha := by
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  unfold canonicalLowBranchReal
  simpa only [canonicalLowBranch, hsum] using
    (complexifySubmodule_realBoundedSpectralSubspaceIicOfGap (A + K) (hA.add hK)
      alpha delta hdelta
      (theorem8_1_spectralRepulsion_real A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp))

/-- Theorem 8.1's complex existence conclusion, read at the complexification of
the real data.  Every real form bound below is read off this. -/
theorem theorem8_1_canonicalBranch_complexified
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Theorem81Conclusion (complexify A) (complexify K) (complexifySubmodule P)
      (canonicalLowBranch (complexify A + complexify K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (((complexify_isSelfAdjoint_iff A).2 hA).add
            ((complexify_isSelfAdjoint_iff K).2 hK))) alpha) alpha delta :=
  theorem8_1_canonicalBranch (E := RealComplexification E)
    (complexify A) (complexify K) (complexifySubmodule P) hdelta
    ((complexify_isSelfAdjoint_iff A).2 hA) ((complexify_isSelfAdjoint_iff K).2 hK)
    (fun z hz => mapsTo_complexifySubmodule hAP hz)
    (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
    (fun z hz => by
      rw [← complexifySubmodule_orthogonal P] at hz
      exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
    (fun z hz => mapsTo_orthogonal_complexifySubmodule P hKP hz)
    (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hKPperp hz)

/-- **Sharp upper form bound on the real branch.**  The form of `A + K` on the
real canonical low branch is at most `α`, with no loss. -/
theorem canonicalLowBranchReal_form_low
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    ∀ x ∈ canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp,
      ⟪(A + K) x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2 := by
  intro x hx
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  have hQc := complexifySubmodule_canonicalLowBranchReal A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp
  have hxC : ofReal x ∈ complexifySubmodule
      (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp) :=
    (ofReal_mem_complexifySubmodule_iff _ x).2 hx
  have hc := (theorem8_1_canonicalBranch_complexified A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp).branch_form_low (ofReal x) (hQc ▸ hxC)
  rw [hsum] at hc
  simpa [re_inner_complexify] using hc

/-- **Sharp lower form bound on the real complementary branch.**  The form of
`A + K` on the orthogonal complement of the real canonical low branch is at
least `α + δ`, with no loss. -/
theorem canonicalLowBranchReal_form_high
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    ∀ x ∈ (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp)ᗮ,
      (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪(A + K) x, x⟫_ℝ := by
  intro x hx
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  have hQc := complexifySubmodule_canonicalLowBranchReal A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp
  have hxC : ofReal x ∈ (complexifySubmodule
      (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp))ᗮ := by
    rw [← complexifySubmodule_orthogonal]
    exact (ofReal_mem_complexifySubmodule_iff _ x).2 hx
  have hc := (theorem8_1_canonicalBranch_complexified A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp).branch_form_high (ofReal x) (by simpa only [hQc] using hxC)
  rw [hsum] at hc
  simpa [re_inner_complexify] using hc

/-- The perturbed upper block of the real canonical branch is positive.

The real mirror of `theorem8_1_perturbedUpperBlockShift_nonneg`; part (iii)
needs it separately, because the weak majorization of a sandwich is stated for a
*positive* middle factor. -/
theorem theorem8_1_perturbedUpperBlockShift_nonneg_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    (0 : E →L[ℝ] E) ≤
      upperBlockShift (A + K)
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
        alpha :=
  upperBlockShift_nonneg (A + K) _ hdelta.le (hA.add hK) fun x hx => by
    simpa only [RCLike.re_to_real] using
      canonicalLowBranchReal_form_high A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp x hx

/-- The perturbed lower block of the real canonical branch is positive. -/
theorem theorem8_1_perturbedLowerBlockShift_nonneg_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    (0 : E →L[ℝ] E) ≤
      lowerBlockShift (A + K)
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp)
        alpha delta :=
  lowerBlockShift_nonneg (A + K) _ hdelta.le (hA.add hK) fun x hx => by
    simpa only [RCLike.re_to_real] using
      canonicalLowBranchReal_form_low A K P hdelta hA hK hAP hPlow hPhigh hKP
        hKPperp x hx

/-! ### Part (i): the printed form repulsion

Part (ii) is a statement about approximation numbers; part (i) is the quadratic
form inequality it is deduced from, and the paper prints it separately.  It is
descended here by the same route: evaluate the complex source-literal statement
on the real copy `ofReal x`, where every projection, every operator and every
inner product is the complexification of its real counterpart. -/

/-- **Davis--Kahan 1970, Theorem 8.1(i), upper block, over a REAL Hilbert
space.**

  `A₁ - α ≤ C₁ (Λ₁ - α) C₁`

read as a quadratic form on `Pᗮ`, with `Q` the real canonical low branch.  As in
the complex statement, the left-hand side is the form of the *unperturbed* `A`
and not of `A + K`, because off-diagonality of `K` kills its cross term on `Pᗮ`.
No dimension hypothesis is introduced. -/
theorem theorem8_1_upperCompressionRepulsion_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    {x : E} (hx : x ∈ Pᗮ) :
    ⟪x, A x⟫_ℝ - alpha * ‖x‖ ^ 2 ≤
      ⟪(canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)ᗮ.starProjection x,
          (A + K) ((canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)ᗮ.starProjection x)⟫_ℝ -
        alpha * ‖(canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
          hKPperp)ᗮ.starProjection x‖ ^ 2 := by
  have hAc : IsSelfAdjoint (complexify A) := (complexify_isSelfAdjoint_iff A).2 hA
  have hKc : IsSelfAdjoint (complexify K) := (complexify_isSelfAdjoint_iff K).2 hK
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  set Q : Submodule ℝ E :=
    canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp with hQdef
  have hQc : complexifySubmodule Q =
      canonicalLowBranch (complexify A + complexify K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc)) alpha :=
    complexifySubmodule_canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
      hKP hKPperp
  have hxC : ofReal x ∈ (complexifySubmodule P)ᗮ := by
    rw [← complexifySubmodule_orthogonal]
    exact (ofReal_mem_complexifySubmodule_iff _ x).2 hx
  have key : ∀ (Qc : Submodule ℂ (RealComplexification E))
      [Qc.HasOrthogonalProjection],
      Qc = canonicalLowBranch (complexify A + complexify K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc))
          alpha →
      RCLike.re ⟪ofReal x, complexify A (ofReal x)⟫_ℂ - alpha * ‖ofReal x‖ ^ 2 ≤
        RCLike.re ⟪Qcᗮ.starProjection (ofReal x),
            (complexify A + complexify K) (Qcᗮ.starProjection (ofReal x))⟫_ℂ -
          alpha * ‖Qcᗮ.starProjection (ofReal x)‖ ^ 2 := by
    rintro Qc _ rfl
    exact DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion
      (complexify A) (complexify K) (complexifySubmodule P) hdelta hAc hKc
      (fun z hz => mapsTo_complexifySubmodule hAP hz)
      (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal P] at hz
        exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
      (fun z hz => mapsTo_orthogonal_complexifySubmodule P hKP hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hKPperp hz) hxC
  have hmain := key (complexifySubmodule Q) hQc
  have hproj : (complexifySubmodule Q)ᗮ.starProjection (ofReal x) =
      ofReal (Qᗮ.starProjection x) := by
    rw [starProjection_complexifySubmodule_orthogonal, complexify_ofReal]
  rw [hproj, hsum] at hmain
  simpa only [complexify_ofReal, inner_ofReal, ofReal.norm_map,
    RCLike.re_to_complex, Complex.ofReal_re] using hmain

/-- **Davis--Kahan 1970, Theorem 8.1(i), lower block, over a REAL Hilbert
space.**

  `(α + δ) - A₀ ≤ C₀ ((α + δ) - Λ₀) C₀`

read as a quadratic form on `P`, the printed lower companion. -/
theorem theorem8_1_lowerCompressionRepulsion_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    {x : E} (hx : x ∈ P) :
    (alpha + delta) * ‖x‖ ^ 2 - ⟪x, A x⟫_ℝ ≤
      (alpha + delta) * ‖(canonicalLowBranchReal A K P hdelta hA hK hAP hPlow
          hPhigh hKP hKPperp).starProjection x‖ ^ 2 -
        ⟪(canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp).starProjection x,
          (A + K) ((canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp).starProjection x)⟫_ℝ := by
  have hAc : IsSelfAdjoint (complexify A) := (complexify_isSelfAdjoint_iff A).2 hA
  have hKc : IsSelfAdjoint (complexify K) := (complexify_isSelfAdjoint_iff K).2 hK
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  set Q : Submodule ℝ E :=
    canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp with hQdef
  have hQc : complexifySubmodule Q =
      canonicalLowBranch (complexify A + complexify K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc)) alpha :=
    complexifySubmodule_canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
      hKP hKPperp
  have hxC : ofReal x ∈ complexifySubmodule P :=
    (ofReal_mem_complexifySubmodule_iff _ x).2 hx
  have key : ∀ (Qc : Submodule ℂ (RealComplexification E))
      [Qc.HasOrthogonalProjection],
      Qc = canonicalLowBranch (complexify A + complexify K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc))
          alpha →
      (alpha + delta) * ‖ofReal x‖ ^ 2 -
          RCLike.re ⟪ofReal x, complexify A (ofReal x)⟫_ℂ ≤
        (alpha + delta) * ‖Qc.starProjection (ofReal x)‖ ^ 2 -
          RCLike.re ⟪Qc.starProjection (ofReal x),
            (complexify A + complexify K) (Qc.starProjection (ofReal x))⟫_ℂ := by
    rintro Qc _ rfl
    exact DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion
      (complexify A) (complexify K) (complexifySubmodule P) hdelta hAc hKc
      (fun z hz => mapsTo_complexifySubmodule hAP hz)
      (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal P] at hz
        exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
      (fun z hz => mapsTo_orthogonal_complexifySubmodule P hKP hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hKPperp hz) hxC
  have hmain := key (complexifySubmodule Q) hQc
  have hproj : (complexifySubmodule Q).starProjection (ofReal x) =
      ofReal (Q.starProjection x) := by
    rw [starProjection_complexifySubmodule, complexify_ofReal]
  rw [hproj, hsum] at hmain
  simpa only [complexify_ofReal, inner_ofReal, ofReal.norm_map,
    RCLike.re_to_complex, Complex.ofReal_re] using hmain

/-! ### The endpoints -/

/-- **The Weyl step of Theorem 8.1 over `ℝ`, upper block.**

  `aₙ(A₁ - α) ≤ aₙ(C₁⋆ (Λ₁ - α) C₁)`,

with `Q` the real canonical low branch.  Descended from
`theorem8_1_upperSandwichApproximation` through the block bridges and the
exact equality `approximationNumber_complexify`; no dimension hypothesis is
introduced. -/
theorem theorem8_1_upperSandwichApproximation_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (upperBlockShift A P alpha).approximationNumber n ≤
      (ContinuousLinearMap.adjoint (cosineBlock P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)) ∘L
        upperBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha ∘L
        cosineBlock P
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)).approximationNumber n := by
  have hAc : IsSelfAdjoint (complexify A) := (complexify_isSelfAdjoint_iff A).2 hA
  have hKc : IsSelfAdjoint (complexify K) := (complexify_isSelfAdjoint_iff K).2 hK
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  set Q : Submodule ℝ E :=
    canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp with hQdef
  have hQc : complexifySubmodule Q =
      canonicalLowBranch (complexify A + complexify K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc)) alpha :=
    complexifySubmodule_canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
      hKP hKPperp
  -- The complex endpoint, stated so that the branch may be substituted.
  have key : ∀ (Qc : Submodule ℂ (RealComplexification E))
      [Qc.HasOrthogonalProjection],
      Qc = canonicalLowBranch (complexify A + complexify K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc))
          alpha →
      (upperBlockShift (complexify A) (complexifySubmodule P) alpha
          ).approximationNumber n ≤
        (ContinuousLinearMap.adjoint (cosineBlock (complexifySubmodule P) Qc) ∘L
          upperBlockShift (complexify A + complexify K) Qc alpha ∘L
          cosineBlock (complexifySubmodule P) Qc).approximationNumber n := by
    rintro Qc _ rfl
    exact theorem8_1_upperSandwichApproximation (complexify A) (complexify K)
      (complexifySubmodule P) hdelta hAc hKc
      (fun z hz => mapsTo_complexifySubmodule hAP hz)
      (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal P] at hz
        exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
      (fun z hz => mapsTo_orthogonal_complexifySubmodule P hKP hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hKPperp hz) n
  have hmain := key (complexifySubmodule Q) hQc
  rw [← complexify_upperBlockShift, ← complexify_cosineBlock, hsum,
    ← complexify_upperBlockShift, ← complexify_adjoint_sandwich,
    approximationNumber_complexify, approximationNumber_complexify] at hmain
  exact hmain

/-- **Davis--Kahan 1970, Theorem 8.1(ii), upper block, over a REAL Hilbert
space.**

  `α_k - α ≤ ‖C₁‖₁² (λ_k - α)`,

at unrestricted dimension.  The printed bound norm `‖C₁‖₁` is the operator norm
of the real cosine block, preserved exactly by `norm_complexify`; the branch is
the real descent of the actual complex spectral branch. -/
theorem theorem8_1_upperApproximationRepulsion_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (upperBlockShift A P alpha).approximationNumber n ≤
      ‖cosineBlock P
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)‖ ^ 2 *
        (upperBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha).approximationNumber n :=
  (theorem8_1_upperSandwichApproximation_real A K P hdelta hA hK hAP hPlow hPhigh
    hKP hKPperp n).trans (approximationNumber_adjoint_sandwich_le _ _ n)

/-- **The Weyl step of Theorem 8.1 over `ℝ`, lower block.**

  `aₙ((α + δ) - A₀) ≤ aₙ(C₀⋆ ((α + δ) - Λ₀) C₀)`,

the printed lower companion, descended in the same way. -/
theorem theorem8_1_lowerSandwichApproximation_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (lowerBlockShift A P alpha delta).approximationNumber n ≤
      (ContinuousLinearMap.adjoint (lowerCosineBlock P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)) ∘L
        lowerBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha delta ∘L
        lowerCosineBlock P
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)).approximationNumber n := by
  have hAc : IsSelfAdjoint (complexify A) := (complexify_isSelfAdjoint_iff A).2 hA
  have hKc : IsSelfAdjoint (complexify K) := (complexify_isSelfAdjoint_iff K).2 hK
  have hsum : complexify A + complexify K = complexify (A + K) :=
    (complexify_add A K).symm
  set Q : Submodule ℝ E :=
    canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP hKPperp with hQdef
  have hQc : complexifySubmodule Q =
      canonicalLowBranch (complexify A + complexify K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc)) alpha :=
    complexifySubmodule_canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh
      hKP hKPperp
  have key : ∀ (Qc : Submodule ℂ (RealComplexification E))
      [Qc.HasOrthogonalProjection],
      Qc = canonicalLowBranch (complexify A + complexify K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hAc.add hKc))
          alpha →
      (lowerBlockShift (complexify A) (complexifySubmodule P) alpha delta
          ).approximationNumber n ≤
        (ContinuousLinearMap.adjoint (lowerCosineBlock (complexifySubmodule P) Qc) ∘L
          lowerBlockShift (complexify A + complexify K) Qc alpha delta ∘L
          lowerCosineBlock (complexifySubmodule P) Qc).approximationNumber n := by
    rintro Qc _ rfl
    exact theorem8_1_lowerSandwichApproximation (complexify A) (complexify K)
      (complexifySubmodule P) hdelta hAc hKc
      (fun z hz => mapsTo_complexifySubmodule hAP hz)
      (fun z hz => re_inner_le_of_mem_complexifySubmodule hPlow hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal P] at hz
        exact le_re_inner_of_mem_complexifySubmodule hPhigh hz)
      (fun z hz => mapsTo_orthogonal_complexifySubmodule P hKP hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule P hKPperp hz) n
  have hmain := key (complexifySubmodule Q) hQc
  rw [← complexify_lowerBlockShift, ← complexify_lowerCosineBlock, hsum,
    ← complexify_lowerBlockShift, ← complexify_adjoint_sandwich,
    approximationNumber_complexify, approximationNumber_complexify] at hmain
  exact hmain

/-- **Davis--Kahan 1970, Theorem 8.1(ii), lower block, over a REAL Hilbert
space.**

  `(α + δ) - α_k ≤ ‖C₀‖₁² ((α + δ) - λ_k)`,

at unrestricted dimension. -/
theorem theorem8_1_lowerApproximationRepulsion_real
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (lowerBlockShift A P alpha delta).approximationNumber n ≤
      ‖lowerCosineBlock P
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)‖ ^ 2 *
        (lowerBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha delta).approximationNumber n :=
  (theorem8_1_lowerSandwichApproximation_real A K P hdelta hA hK hAP hPlow hPhigh
    hKP hKPperp n).trans (approximationNumber_adjoint_sandwich_le _ _ n)

end

end Section8
end DavisKahan1970
end TauCeti
