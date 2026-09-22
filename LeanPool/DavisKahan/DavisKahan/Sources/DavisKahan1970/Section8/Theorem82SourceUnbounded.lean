/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem82UnboundedPath
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaDirectedAngle
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedFromSpectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.RealSpectrum

/-!
# Theorem 8.2 as one source-facing theorem, at unbounded ambient scope

Davis and Kahan state Theorem 8.2 as a single theorem: add to the hypotheses of
the `sin 2θ` theorem either `‖H‖ < δ/2` or `‖R‖ < δ/2`, assume
`spec(A₀) ⊆ [β − δ/2, α + δ/2]`, and then **both** conclusions hold — the
double-angle estimate remains valid, *and* the comparison is on the acute branch.

The four theorems below are that theorem, one per alternative and scalar field,
at the ambient scope Section 8 inherits: `A` is a possibly unbounded self-adjoint
partial map and `H` is a bounded self-adjoint perturbation.  They are façades.
Each conclusion is an existing theorem:

* the retained perturbation estimate is
  `sinTwoTheta_ambient_unbounded_perturbedGap_sourceExact_{complex,real}`, the
  Section 2 endpoint, with the printed spectral placement converted to the
  `FormBoundedSylvesterGap` it takes by `intervalExterior`;
* the retained residual estimate is
  `sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_{complex,real}`
  lifted to an arbitrary normalized unitarily invariant norm the same way the
  Section 2 endpoint is;
* the acute conclusion is
  `theorem8_2_{perturbation,residual}HalfGap_maximalAngle_lt_unbounded_{complex,real}`.

## The residual

In Section 8's context `P` reduces `A`, so the Ritz block of the trial subspace
`P` is `A₀ = A|_P` and Davis--Kahan's residual (1.8) is
`R = (A + H)|_P − A₀ = H|_P`.  `sourceResidual` is that operator, and
`sourceResidual_eq_sub_ritzBlock` certifies the identification rather than
assuming it.

The residual branch therefore takes exactly what the source adds — the
central-spectrum condition and `‖R‖ < δ/2` — and **nothing** about the Ritz
block.  The bounded realization of `A₀`, its full domain on `P`, and the residual
identity are all derived inside, from the central-spectrum condition: a
self-adjoint partial map whose spectrum lies in a compact interval has an
everywhere-defined bounded realization
(`exists_boundedRealization_of_spectrum_subset_Icc`), which is precisely what
`spec(A₀) ⊆ [β − δ/2, α + δ/2]` supplies.
-/

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open TauCeti.DavisKahan.Sylvester
open TauCeti.DavisKahan.ExactSinTheta

noncomputable section

universe v

/-! ### Davis--Kahan's residual, and the Ritz block the source hypothesis supplies -/

section Residual

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Davis--Kahan's residual (1.8) for the trial subspace `P`, in Section 8's
context.**

`P` reduces `A`, so the Ritz block of `P` is `A₀ = A|_P` and the residual of `P`
for `A + H` is `R = (A + H)|_P − A₀ = H|_P`.
`sourceResidual_eq_sub_ritzBlock` certifies that reading; it is not assumed. -/
def sourceResidual (Hop : H →L[𝕜] H) (P : Submodule 𝕜 H)  :
    P →L[𝕜] H :=
  Hop ∘L (P.subtypeL : P →L[𝕜] H)

omit [CompleteSpace H] in
/-- `sourceResidual` is the printed residual: `R = (A + H)|_P − A₀`, for any
bounded realization `M` of the Ritz block `A₀ = A|_P`. -/
theorem sourceResidual_eq_sub_ritzBlock {A : H →ₗ.[𝕜] H} {Hop : H →L[𝕜] H}
    {P : Submodule 𝕜 H}  {M : P →L[𝕜] P}
    (hPdom : ∀ v : P, (v : H) ∈ A.domain)
    (hRitz : ∀ v : P, ((M v : P) : H) = A ⟨(v : H), hPdom v⟩) (v : P) :
    sourceResidual Hop P v
      = TauCeti.LinearPMap.addBounded A Hop ⟨(v : H), hPdom v⟩ - ((M v : P) : H) := by
  rw [TauCeti.LinearPMap.addBounded_apply, hRitz v]
  change Hop (v : H) = A ⟨(v : H), hPdom v⟩ + Hop (v : H) - A ⟨(v : H), hPdom v⟩
  abel

end Residual

/-! ### The Ritz block is derived, not assumed

Davis--Kahan add `spec(A₀) ⊆ [β − δ/2, α + δ/2]` to the `sin 2θ` hypotheses.  For
a self-adjoint operator that is a bounded spectral support, so `A₀` is bounded and
everywhere defined on `P`.  These two lemmas extract exactly that, so the source
façades below need no Ritz data in their signatures. -/

section RitzBlock

/-- **The central-spectrum hypothesis supplies the Ritz block, over `ℂ`.** -/
theorem exists_ritzBlock_of_realSpectrum_subset_Icc_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A) {P : Submodule ℂ Hc}
    [P.HasOrthogonalProjection] (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    {b a : ℝ} (hba : b ≤ a)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred) ⊆ Set.Icc b a) :
    ∃ (hPdom : ∀ v : P, (v : Hc) ∈ A.domain) (M : P →L[ℂ] P),
      ∀ v : P, ((M v : P) : Hc) = A ⟨(v : Hc), hPdom v⟩ := by
  have hblock : IsSelfAdjoint (TauCeti.LinearPMap.reducingRestriction A P hPred) :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A P hPred hA.dense_domain hA
  obtain ⟨Rz, -⟩ := DavisKahan.ExactSinTheta.exists_boundedRealization_of_spectrum_subset_Icc
    hblock hba (by
      rw [← TauCeti.DavisKahan.realSpectrum_eq_spectraSpectrum]
      exact hPspec)
  have hdomP : ∀ v : P, v ∈ (TauCeti.LinearPMap.reducingRestriction A P hPred).domain := by
    intro v
    rw [Rz.domain_eq_top]
    trivial
  have hdom : ∀ v : P, (v : Hc) ∈ A.domain := fun v =>
    (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A P hPred v).mp (hdomP v)
  refine ⟨hdom, Rz.operator, fun v => ?_⟩
  have hag := Rz.agrees ⟨v, hdomP v⟩
  have : ((Rz.operator v : P) : Hc)
      = ((TauCeti.LinearPMap.reducingRestriction A P hPred ⟨v, hdomP v⟩ : P) : Hc) :=
    congrArg _ hag
  rw [this]
  exact TauCeti.LinearPMap.coe_reducingRestriction_apply A P hPred v (hdom v)

open TauCeti.RealComplexification in
/-- **The central-spectrum hypothesis supplies the Ritz block, over `ℝ`.**

The same statement, read through the complexification: the complexified block has
the same real spectrum, so it has a bounded realization, and the real part of that
realization is the real Ritz block. -/
theorem exists_ritzBlock_of_realSpectrum_subset_Icc_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A) {P : Submodule ℝ Er}
    [P.HasOrthogonalProjection] (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    {b a : ℝ} (hba : b ≤ a)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred) ⊆ Set.Icc b a) :
    ∃ (hPdom : ∀ v : P, (v : Er) ∈ A.domain) (M : P →L[ℝ] P),
      ∀ v : P, ((M v : P) : Er) = A ⟨(v : Er), hPdom v⟩ := by
  have hblock : IsSelfAdjoint (TauCeti.LinearPMap.reducingRestriction A P hPred) :=
    TauCeti.LinearPMap.reducingRestriction_isSelfAdjoint A P hPred hA.dense_domain hA
  have hBC : IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal
      (TauCeti.LinearPMap.reducingRestriction A P hPred)) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hblock
  obtain ⟨Rz, -⟩ := DavisKahan.ExactSinTheta.exists_boundedRealization_of_spectrum_subset_Icc
    hBC hba (by
      rw [← TauCeti.DavisKahan.realSpectrum_eq_spectraSpectrum,
        TauCeti.LinearPMap.realSpectrum_complexifyReal]
      exact hPspec)
  have hdomP : ∀ v : P, v ∈ (TauCeti.LinearPMap.reducingRestriction A P hPred).domain := by
    intro v
    have h : (ofReal v : RealComplexification P) ∈
        (TauCeti.LinearPMap.complexifyReal
          (TauCeti.LinearPMap.reducingRestriction A P hPred)).domain := by
      rw [Rz.domain_eq_top]
      trivial
    rw [TauCeti.LinearPMap.mem_complexifyReal_domain_iff] at h
    simpa using h.1
  have hdom : ∀ v : P, (v : Er) ∈ A.domain := fun v =>
    (TauCeti.LinearPMap.mem_reducingRestriction_domain_iff A P hPred v).mp (hdomP v)
  refine ⟨hdom, RealComplexification.realPartOperator Rz.operator, fun v => ?_⟩
  have hag := Rz.agrees (TauCeti.LinearPMap.complexifyRealOfRealDomain _ ⟨v, hdomP v⟩)
  rw [TauCeti.LinearPMap.complexifyRealOfRealDomain_coe,
    TauCeti.LinearPMap.complexifyReal_apply_ofReal] at hag
  have hM : (RealComplexification.realPartOperator Rz.operator) v
      = (TauCeti.LinearPMap.reducingRestriction A P hPred ⟨v, hdomP v⟩ : P) := by
    rw [RealComplexification.realPartOperator_apply, hag, re_ofReal]
  rw [hM]
  exact TauCeti.LinearPMap.coe_reducingRestriction_apply A P hPred v (hdom v)

end RitzBlock

/-! ### The perturbation alternative -/

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, at the printed
source scope over `ℂ`.**

`A` is self-adjoint and possibly unbounded, `H` bounded self-adjoint, `P` reduces
`A`, `Q` reduces `A + H` with the printed spectral placement, `A₀`'s spectrum
lies in the central band `[β − δ/2, α + δ/2]`, and `‖H‖ < δ/2`.  Then the
double-angle estimate is retained and the comparison is on the acute branch. -/
theorem theorem8_2_perturbation_sourceExact_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]

    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2)
    (hHmem : N.Mem Hop) :
    (N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
        delta * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gauge Hop) ∧
      TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  refine ⟨?_, theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_complex hA Hop hHop
    hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall⟩
  exact sinTwoTheta_ambient_unbounded_perturbedGap_normalizedUIN_complex N hA Hop hHop
    hPred hQred hdelta (.intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)) hHmem

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, at the printed
source scope over `ℝ`.** -/
theorem theorem8_2_perturbation_sourceExact_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖Hop‖ < delta / 2)
    (hHmem : N.Mem Hop) :
    (N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
        delta * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gauge Hop) ∧
      TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  refine ⟨?_, theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_real hA Hop hHop
    hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall⟩
  exact sinTwoTheta_ambient_unbounded_perturbedGap_normalizedUIN_real N hA Hop hHop
    hPred hQred hdelta (.intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)) hHmem

/-! ### The residual alternative -/

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, at the printed source
scope over `ℂ`.**

The smallness hypothesis is the printed `‖R‖ < δ/2` on the residual itself, and
does not become `‖H‖ < δ/2`. -/
theorem theorem8_2_residual_sourceExact_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    [TopologicalSpace.SeparableSpace Hc]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖sourceResidual Hop P‖ < delta / 2)
    (hRmem : N.Mem (sourceResidual Hop P)) :
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ∧
        delta * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
          2 * N.gauge (sourceResidual Hop P)) ∧
      TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  have hAH : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop
  have hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) delta :=
    .intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)
  -- the Ritz block is supplied by the central-spectrum hypothesis, not by the caller
  obtain ⟨hPdom, M, hRitz⟩ :=
    exists_ritzBlock_of_realSpectrum_subset_Icc_complex hA hPred (by linarith) hPspec
  have hres : ∀ v : P, TauCeti.LinearPMap.addBounded A Hop ⟨(v : Hc), hPdom v⟩
      = sourceResidual Hop P v + ((M v : P) : Hc) := by
    intro v
    rw [sourceResidual_eq_sub_ritzBlock hPdom hRitz v]
    abel
  refine ⟨?_, ?_⟩
  · exact normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos hRmem
      fun Msnf hM =>
        sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex Msnf
          hAH hQred hPdom hres hdelta hgap hM
  · exact theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_complex hA Hop hHop
      hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, at the printed source
scope over `ℝ`.** -/
theorem theorem8_2_residual_sourceExact_unbounded_real
    {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    [TopologicalSpace.SeparableSpace Er]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    (Hop : Er →L[ℝ] Er) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℝ Er} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    (hQspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      ⊆ Set.Icc beta alpha)
    (hQperp : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) ⊆ bandExterior beta alpha delta)
    (hPspec : TauCeti.LinearPMap.realSpectrum
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      ⊆ Set.Icc (beta - delta / 2) (alpha + delta / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : ‖sourceResidual Hop P‖ < delta / 2)
    (hRmem : N.Mem (sourceResidual Hop P)) :
    (N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ∧
        delta * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
          2 * N.gauge (sourceResidual Hop P)) ∧
      TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  have hAH : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hHop
  have hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction (TauCeti.LinearPMap.addBounded A Hop) Qᗮ
        hQred.orthogonal) delta :=
    .intervalExterior hab (Or.inl ⟨hQspec, hQperp⟩)
  -- the Ritz block is supplied by the central-spectrum hypothesis, not by the caller
  obtain ⟨hPdom, M, hRitz⟩ :=
    exists_ritzBlock_of_realSpectrum_subset_Icc_real hA hPred (by linarith) hPspec
  have hres : ∀ v : P, TauCeti.LinearPMap.addBounded A Hop ⟨(v : Er), hPdom v⟩
      = sourceResidual Hop P v + ((M v : P) : Er) := by
    intro v
    rw [sourceResidual_eq_sub_ritzBlock hPdom hRitz v]
    abel
  refine ⟨?_, ?_⟩
  · exact normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos hRmem
      fun Msnf hM =>
        sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_real Msnf
          hAH hQred hPdom hres hdelta hgap hM
  · exact theorem8_2_residualHalfGap_maximalAngle_lt_unbounded_real hA Hop hHop
      hdelta hab hPred hQred hQspec hQperp hPspec hcross hsmall

end

end Section8
end DavisKahan1970
end TauCeti
