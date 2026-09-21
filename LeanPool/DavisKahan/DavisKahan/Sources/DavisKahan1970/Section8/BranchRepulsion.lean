/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.CircleWitness
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.SelectedBranch
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Smallness
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.CompressionRepulsion
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.CompressionApproximation
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SpectralOrder
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpDiagonalResolvents
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.SharpSchurComplement
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Riccati.ContinuationWitnessOrientedBlocks

/-! # Branch Repulsion -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Section 8: the selected branch and its spectral repulsion

The source-level conclusions of Theorems 8.1 and 8.2 that need the analytic
continuation layer: existence of the selected branch with full spectral
repulsion, the two half-gap bridges that discharge Theorem 8.2's smallness
alternatives, and the printed compression inequalities of Theorem 8.1(i), both
from a target splitting and at the canonical branch.

The machinery is owned upstream.  The circle continuation witness is
`InfiniteDimensional/SinTheta/Continuation/CircleWitness.lean`, the form/spectrum
bridges are `SpectralTheory/SpectralGapFormBounds.lean`, and the branch itself
is `Section8/Theorem81.lean`; this module states the paper's sentences
against them.
-/

open scoped InnerProductSpace
open Set Filter

namespace TauCeti
namespace DavisKahan1970
namespace Section8


open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Foundation
open TauCeti.DavisKahan.RieszCircle

universe u v

section TargetSplittingCompression

/-! The scaffolded statements of this section claimed the compression
inequalities of Theorem 8.1(i) with placeholder identity blocks; as
transcribed they were false (the Pythagorean field demanded
`2 ‖x‖ ^ 2 = ‖x‖ ^ 2`, and the inequalities reduced to a sign condition on
the perturbation).  At the quadratic-form level the paper's cosine-block
inequality needs no direct rotation: the orthogonal splitting through the new
spectral branch supplies the certificate, because the branch reduces the
perturbed operator, so the cross terms of the splitting vanish. -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

omit [CompleteSpace H] in
/-- The quadratic form of an operator splits exactly through a reducing
subspace: the cross terms vanish. -/
theorem re_inner_splitting_of_invariant
    {T : H →L[ℂ] H} {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : InvariantFor T W) (hW' : InvariantFor T Wᗮ) (x : H) :
    RCLike.re ⟪x, T x⟫_ℂ =
      RCLike.re ⟪W.starProjection x, T (W.starProjection x)⟫_ℂ +
        RCLike.re ⟪Wᗮ.starProjection x, T (Wᗮ.starProjection x)⟫_ℂ := by
  set p := W.starProjection x with hp
  set q := Wᗮ.starProjection x with hq
  have hx : p + q = x := W.starProjection_add_starProjection_orthogonal x
  have hpq : ⟪p, T q⟫_ℂ = 0 := by
    have hTq : T q ∈ Wᗮ := hW' q (Wᗮ.starProjection_apply_mem x)
    exact (Submodule.mem_orthogonal W (T q)).mp hTq p (W.starProjection_apply_mem x)
  have hqp : ⟪q, T p⟫_ℂ = 0 := by
    have hTp : T p ∈ W := hW p (W.starProjection_apply_mem x)
    exact (Submodule.mem_orthogonal' W q).mp (Wᗮ.starProjection_apply_mem x)
      (T p) hTp
  have hinner : ⟪x, T x⟫_ℂ = ⟪p, T p⟫_ℂ + ⟪q, T q⟫_ℂ := by
    conv_lhs => rw [← hx]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hpq, hqp]
    ring
  rw [hinner, map_add]

omit [CompleteSpace H] in
/-- The orthogonal splitting through the new spectral branch supplies the
upper compression certificate of Theorem 8.1(i).  The kernel-side form is
shifted by the cut so that its global bound is exactly the branch form
bound. -/
theorem upperCompressionRepulsionData_of_targetSplitting
    {T : H →L[ℂ] H} {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : InvariantFor T W) (hW' : InvariantFor T Wᗮ) (a : ℝ) :
    DavisKahan1970.Section8.UpperCompressionRepulsionData
      (fun x : H => RCLike.re ⟪x, T x⟫_ℂ)
      (fun x : H =>
        RCLike.re ⟪W.starProjection x, T (W.starProjection x)⟫_ℂ +
          (a * ‖x‖ ^ 2 - a * ‖W.starProjection x‖ ^ 2))
      (fun x : H =>
        RCLike.re ⟪Wᗮ.starProjection x, T (Wᗮ.starProjection x)⟫_ℂ)
      W.starProjection Wᗮ.starProjection := by
  have hidem : ∀ x : H, W.starProjection (W.starProjection x) =
      W.starProjection x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem x)
  have hidem' : ∀ x : H, Wᗮ.starProjection (Wᗮ.starProjection x) =
      Wᗮ.starProjection x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (Wᗮ.starProjection_apply_mem x)
  constructor
  · intro x
    rw [hidem x, hidem' x, re_inner_splitting_of_invariant hW hW' x]
    ring
  · intro x
    exact (W.norm_sq_eq_add_norm_sq_starProjection x).symm

omit [CompleteSpace H] in
/-- The orthogonal splitting through the new spectral branch supplies the
lower compression certificate of Theorem 8.1(i). -/
theorem lowerCompressionRepulsionData_of_targetSplitting
    {T : H →L[ℂ] H} {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : InvariantFor T W) (hW' : InvariantFor T Wᗮ) (b : ℝ) :
    DavisKahan1970.Section8.LowerCompressionRepulsionData
      (fun x : H => RCLike.re ⟪x, T x⟫_ℂ)
      (fun x : H =>
        RCLike.re ⟪W.starProjection x, T (W.starProjection x)⟫_ℂ)
      (fun x : H =>
        RCLike.re ⟪Wᗮ.starProjection x, T (Wᗮ.starProjection x)⟫_ℂ +
          (b * ‖x‖ ^ 2 - b * ‖Wᗮ.starProjection x‖ ^ 2))
      W.starProjection Wᗮ.starProjection := by
  have hidem : ∀ x : H, W.starProjection (W.starProjection x) =
      W.starProjection x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem x)
  have hidem' : ∀ x : H, Wᗮ.starProjection (Wᗮ.starProjection x) =
      Wᗮ.starProjection x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (Wᗮ.starProjection_apply_mem x)
  constructor
  · intro x
    rw [hidem x, hidem' x, re_inner_splitting_of_invariant hW hW' x]
    ring
  · intro x
    exact (W.norm_sq_eq_add_norm_sq_starProjection x).symm

/-- Davis--Kahan 1970, Theorem 8.1(i), upper compression inequality, restated
faithfully: the displacement of the perturbed form on the old complement is
controlled by its displacement after the cosine block into the new
complement.  The former placeholder statement compared the unperturbed and
perturbed forms with cancelling cut terms and was false as transcribed. -/
theorem theorem8_1_upperCompressionRepulsion_of_targetSplitting
    (C : SpectralContinuationWitness A E s) {a : ℝ}
    (hsym : (A + E).IsSymmetric)
    (h0 : SpectrumIn (A + E) C.targetSelectedSpectralSubspace (Set.Iic a))
    (h1inv : InvariantFor (A + E) C.targetSelectedSpectralSubspaceᗮ) :
    ∀ x : C.sourceSelectedSpectralSubspaceᗮ,
      RCLike.re ⟪(x : H), (A + E) (x : H)⟫_ℂ - a * ‖(x : H)‖ ^ 2 ≤
        RCLike.re ⟪C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H),
            (A + E) (C.targetSelectedSpectralSubspaceᗮ.starProjection
              (x : H))⟫_ℂ -
          a * ‖C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H)‖ ^ 2 := by
  intro x
  have hdata := upperCompressionRepulsionData_of_targetSplitting
    (T := A + E) (W := C.targetSelectedSpectralSubspace) h0.invariant h1inv a
  have hL0 : ∀ y : H,
      RCLike.re ⟪C.targetSelectedSpectralSubspace.starProjection y,
          (A + E) (C.targetSelectedSpectralSubspace.starProjection y)⟫_ℂ +
        (a * ‖y‖ ^ 2 -
          a * ‖C.targetSelectedSpectralSubspace.starProjection y‖ ^ 2) ≤
      a * ‖y‖ ^ 2 := by
    intro y
    have hform := re_inner_le_of_spectrumIn_Iic hsym h0
      (C.targetSelectedSpectralSubspace.starProjection_apply_mem y)
    linarith
  have hres :=
    DavisKahan1970.Section8.upperCompressionRepulsion_of_data hdata hL0 (x : H)
  have hidem : C.targetSelectedSpectralSubspaceᗮ.starProjection
      (C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H)) =
      C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H) :=
    Submodule.starProjection_eq_self_iff.mpr
      (C.targetSelectedSpectralSubspaceᗮ.starProjection_apply_mem (x : H))
  simp only [hidem] at hres
  exact hres

/-- Davis--Kahan 1970, Theorem 8.1(i), lower compression companion, restated
faithfully over the old selected subspace. -/
theorem theorem8_1_lowerCompressionRepulsion_of_targetSplitting
    (C : SpectralContinuationWitness A E s) {b : ℝ}
    (hsym : (A + E).IsSymmetric)
    (h0inv : InvariantFor (A + E) C.targetSelectedSpectralSubspace)
    (h1 : SpectrumIn (A + E) C.targetSelectedSpectralSubspaceᗮ (Set.Ici b)) :
    ∀ x : C.sourceSelectedSpectralSubspace,
      b * ‖(x : H)‖ ^ 2 - RCLike.re ⟪(x : H), (A + E) (x : H)⟫_ℂ ≤
        b * ‖C.targetSelectedSpectralSubspace.starProjection (x : H)‖ ^ 2 -
          RCLike.re ⟪C.targetSelectedSpectralSubspace.starProjection (x : H),
            (A + E) (C.targetSelectedSpectralSubspace.starProjection
              (x : H))⟫_ℂ := by
  intro x
  have hdata := lowerCompressionRepulsionData_of_targetSplitting
    (T := A + E) (W := C.targetSelectedSpectralSubspace) h0inv h1.invariant b
  have hL1 : ∀ y : H,
      b * ‖y‖ ^ 2 ≤
      RCLike.re ⟪C.targetSelectedSpectralSubspaceᗮ.starProjection y,
          (A + E) (C.targetSelectedSpectralSubspaceᗮ.starProjection y)⟫_ℂ +
        (b * ‖y‖ ^ 2 -
          b * ‖C.targetSelectedSpectralSubspaceᗮ.starProjection y‖ ^ 2) := by
    intro y
    have hform := le_re_inner_of_spectrumIn_Ici hsym h1
      (C.targetSelectedSpectralSubspaceᗮ.starProjection_apply_mem y)
    linarith
  have hres :=
    DavisKahan1970.Section8.lowerCompressionRepulsion_of_data hdata hL1 (x : H)
  have hidem : C.targetSelectedSpectralSubspace.starProjection
      (C.targetSelectedSpectralSubspace.starProjection (x : H)) =
      C.targetSelectedSpectralSubspace.starProjection (x : H) :=
    Submodule.starProjection_eq_self_iff.mpr
      (C.targetSelectedSpectralSubspace.starProjection_apply_mem (x : H))
  simp only [hidem] at hres
  exact hres

end TargetSplittingCompression

section SourceTheorems

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {A E : H →L[ℂ] H} {s : Set ℝ}

/-- Full source-level conclusion currently expected from Davis--Kahan Theorem
8.1.  The compression inequalities are kept explicit rather than hidden behind
an unconstrained certificate.

Restated against the scaffold: the former compression fields compared the
unperturbed and perturbed forms with cancelling cut terms, which is not the
source inequality and is false in general.  The faithful quadratic-form
content of Theorem 8.1(i) compares the perturbed form on the old branch with
its cosine-block compression into the corresponding new branch. -/
structure Theorem81ContinuationConclusion
    (C : SpectralContinuationWitness A E s) (a b delta : ℝ) : Prop where
  core : DavisKahan1970.Section8.Theorem81CoreConclusion C a b delta
  upper_compression :
    ∀ x : C.sourceSelectedSpectralSubspaceᗮ,
      RCLike.re ⟪(x : H), (A + E) (x : H)⟫_ℂ - a * ‖(x : H)‖ ^ 2 ≤
        RCLike.re ⟪C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H),
            (A + E) (C.targetSelectedSpectralSubspaceᗮ.starProjection
              (x : H))⟫_ℂ -
          a * ‖C.targetSelectedSpectralSubspaceᗮ.starProjection (x : H)‖ ^ 2
  lower_compression :
    ∀ x : C.sourceSelectedSpectralSubspace,
      b * ‖(x : H)‖ ^ 2 - RCLike.re ⟪(x : H), (A + E) (x : H)⟫_ℂ ≤
        b * ‖C.targetSelectedSpectralSubspace.starProjection (x : H)‖ ^ 2 -
          RCLike.re ⟪C.targetSelectedSpectralSubspace.starProjection (x : H),
            (A + E) (C.targetSelectedSpectralSubspace.starProjection
              (x : H))⟫_ℂ

/-- Davis--Kahan 1970, Theorem 8.1 assembled from a common-circle
continuation, oriented spectral placement, and the target-splitting
compression algebra. -/
theorem theorem8_1_selectedBranch_and_spectralRepulsion
    (D : CircleContinuationData A E s) {a b delta : ℝ}
    (hsmall : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2)
    (hgap : a + delta ≤ b)
    (h0 : SpectrumIn (A + E)
      (spectralContinuationWitnessOfCircle D).targetSelectedSpectralSubspace
      (Set.Iic a))
    (h1 : SpectrumIn (A + E)
      (spectralContinuationWitnessOfCircle D).targetSelectedSpectralSubspaceᗮ
      (Set.Ici b)) :
    Theorem81ContinuationConclusion
      (spectralContinuationWitnessOfCircle D) a b delta := by
  have hsym : (A + E).IsSymmetric := D.hA.add D.hE
  have hsmallC : selectedBranchProjectionLipschitzConstant
      (spectralContinuationWitnessOfCircle D).contour E D.margin <
        Real.sqrt 2 / 2 :=
    lt_of_le_of_lt (selectedBranchProjectionLipschitzConstant_of_circle D)
      hsmall
  exact
    { core := DavisKahan1970.Section8.theorem81CoreConclusion _
        hsmallC hgap h0 h1
      upper_compression :=
        theorem8_1_upperCompressionRepulsion_of_targetSplitting _
          hsym h0 h1.invariant
      lower_compression :=
        theorem8_1_lowerCompressionRepulsion_of_targetSplitting _
          hsym h0.invariant h1 }

/-- Construct the perturbation half-gap bridge required by Theorem 8.2
from a circle datum and an endpoint-size estimate.

The common circle and its uniform spectral margin are now constructed directly
from the finite-gap, off-diagonal, and perturbation half-gap hypotheses by
`exists_circleContinuationData_of_offDiagonal_halfGap`.  The additional bound
below is a sufficient one-step estimate for locating the endpoint below the
quarter-turn threshold; replacing it by the source continuation/no-crossing
argument is a separate branch-selection step. -/
theorem perturbationHalfGapBridge_of_circleContinuationData
    (D : CircleContinuationData A E s) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖E‖ < delta / 2)
    (hquant : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2) :
    DavisKahan1970.Section8.PerturbationHalfGapBridge
      (spectralContinuationWitnessOfCircle D) delta where
  delta_pos := hdelta
  perturbation_small := hsmall
  contour_selects_quarter_branch :=
    lt_of_le_of_lt (selectedBranchProjectionLipschitzConstant_of_circle D)
      hquant

/-- Construct the residual half-gap bridge.  The same amendment applies; in
the source the quantitative circle input for the residual alternative is
produced by the Krein replacement argument, which remains the open analytic
step. -/
theorem residualHalfGapBridge_of_circleContinuationData
    (D : CircleContinuationData A E s) (R : F →L[ℂ] H) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖R‖ < delta / 2)
    (hquant : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2) :
    DavisKahan1970.Section8.ResidualHalfGapBridge
      (spectralContinuationWitnessOfCircle D) R delta where
  delta_pos := hdelta
  residual_small := hsmall
  contour_selects_quarter_branch :=
    lt_of_le_of_lt (selectedBranchProjectionLipschitzConstant_of_circle D)
      hquant

/-- Davis--Kahan 1970, Theorem 8.2, perturbation-smallness alternative, from
the quantitative circle datum. -/
theorem theorem8_2_perturbationHalfGap_selectedBranch
    (D : CircleContinuationData A E s) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖E‖ < delta / 2)
    (hquant : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2) :
    DavisKahan1970.Section8.SelectedBranchConclusion
      (spectralContinuationWitnessOfCircle D) :=
  DavisKahan1970.Section8.theorem82_branch_of_perturbationHalfGapBridge _
    (perturbationHalfGapBridge_of_circleContinuationData D hdelta hsmall hquant)

/-- Davis--Kahan 1970, Theorem 8.2, residual-smallness alternative, from the
quantitative circle datum. -/
theorem theorem8_2_residualHalfGap_selectedBranch
    (D : CircleContinuationData A E s) (R : F →L[ℂ] H) {delta : ℝ}
    (hdelta : 0 < delta) (hsmall : ‖R‖ < delta / 2)
    (hquant : D.radius * ‖E‖ / D.margin ^ 2 < Real.sqrt 2 / 2) :
    DavisKahan1970.Section8.SelectedBranchConclusion
      (spectralContinuationWitnessOfCircle D) :=
  DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge _ R
    (residualHalfGapBridge_of_circleContinuationData D R hdelta hsmall hquant)

end SourceTheorems

section CanonicalBranchCompression

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Theorem 8.1(i) at the canonical branch, upper compression.**

The abstract compression-repulsion core is instantiated at the branch that
`theorem8_1_canonicalBranch` constructs, so no data record appears in the
hypotheses: the caller supplies only the printed Section 8 configuration. -/
theorem theorem8_1_upperCompressionRepulsion_canonicalBranch
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (x : H) :
    RCLike.re ⟪x, (A + K) x⟫_ℂ - alpha * ‖x‖ ^ 2 ≤
      RCLike.re ⟪(DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)ᗮ.starProjection x,
          (A + K) ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)ᗮ.starProjection x)⟫_ℂ -
        alpha * ‖(DavisKahan1970.Section8.canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)ᗮ.starProjection x‖ ^ 2 := by
  have hconc := DavisKahan1970.Section8.theorem8_1_canonicalBranch A K P hdelta
    hA hK hAP hPlow hPhigh hKP hKPperp
  have hdata := upperCompressionRepulsionData_of_targetSplitting
    (T := A + K)
    (W := DavisKahan1970.Section8.canonicalLowBranch (A + K)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)
    hconc.branch_reduces.1 hconc.branch_reduces.2 alpha
  have hL0 : ∀ y : H,
      RCLike.re ⟪(DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha).starProjection y,
          (A + K) ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha).starProjection y)⟫_ℂ +
        (alpha * ‖y‖ ^ 2 -
          alpha * ‖(DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha).starProjection y‖ ^ 2) ≤
      alpha * ‖y‖ ^ 2 := by
    intro y
    have hmem := (DavisKahan1970.Section8.canonicalLowBranch (A + K)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK))
      alpha).starProjection_apply_mem y
    have hform := hconc.branch_form_low _ hmem
    have hswap := inner_re_symm (𝕜 := ℂ)
      ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK))
        alpha).starProjection y)
      ((A + K) ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK))
        alpha).starProjection y))
    linarith
  have hres := DavisKahan1970.Section8.upperCompressionRepulsion_of_data hdata hL0 x
  have hidem : (DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha)ᗮ.starProjection
      ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha)ᗮ.starProjection x) =
      (DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha)ᗮ.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem _ x)
  simp only [hidem] at hres
  exact hres

/-- **Theorem 8.1(i) at the canonical branch, lower compression companion.** -/
theorem theorem8_1_lowerCompressionRepulsion_canonicalBranch
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (x : H) :
    (alpha + delta) * ‖x‖ ^ 2 - RCLike.re ⟪x, (A + K) x⟫_ℂ ≤
      (alpha + delta) * ‖(DavisKahan1970.Section8.canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha).starProjection x‖ ^ 2 -
        RCLike.re ⟪(DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha).starProjection x,
          (A + K) ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha).starProjection x)⟫_ℂ := by
  have hconc := DavisKahan1970.Section8.theorem8_1_canonicalBranch A K P hdelta
    hA hK hAP hPlow hPhigh hKP hKPperp
  have hdata := lowerCompressionRepulsionData_of_targetSplitting
    (T := A + K)
    (W := DavisKahan1970.Section8.canonicalLowBranch (A + K)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha)
    hconc.branch_reduces.1 hconc.branch_reduces.2 (alpha + delta)
  have hL1 : ∀ y : H,
      (alpha + delta) * ‖y‖ ^ 2 ≤
        RCLike.re ⟪(DavisKahan1970.Section8.canonicalLowBranch (A + K)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
                (hA.add hK)) alpha)ᗮ.starProjection y,
            (A + K) ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
                (hA.add hK)) alpha)ᗮ.starProjection y)⟫_ℂ +
          ((alpha + delta) * ‖y‖ ^ 2 -
            (alpha + delta) * ‖(DavisKahan1970.Section8.canonicalLowBranch (A + K)
              (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
                (hA.add hK)) alpha)ᗮ.starProjection y‖ ^ 2) := by
    intro y
    have hmem := (DavisKahan1970.Section8.canonicalLowBranch (A + K)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK))
      alpha)ᗮ.starProjection_apply_mem y
    have hform := hconc.branch_form_high _ hmem
    have hswap := inner_re_symm (𝕜 := ℂ)
      ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK))
        alpha)ᗮ.starProjection y)
      ((A + K) ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK))
        alpha)ᗮ.starProjection y))
    linarith
  have hres := DavisKahan1970.Section8.lowerCompressionRepulsion_of_data hdata hL1 x
  have hidem : (DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha).starProjection
      ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha).starProjection x) =
      (DavisKahan1970.Section8.canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha).starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr
      (Submodule.starProjection_apply_mem _ x)
  simp only [hidem] at hres
  exact hres

/-- **Theorem 8.1(i), source-literal upper form.**

Restricted to the original `Pᗮ` block, the ambient inequality of
`theorem8_1_upperCompressionRepulsion_canonicalBranch` is exactly the printed

  `A₁ - α ≤ C₁ (Λ₁ - α) C₁`

read as a quadratic form.  The point of restricting is that off-diagonality of
`K` kills its cross term on `Pᗮ`, so the left-hand side is the form of the
*unperturbed* compression `A₁` and not of `A + K`.  The right-hand side is the
form of `Λ₁ - α` evaluated at `C₁ x = P_{Qᗮ} x`, which is the printed
cosine-sandwiched term. -/
theorem theorem8_1_upperCompressionRepulsion
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    {x : H} (hx : x ∈ Pᗮ) :
    RCLike.re ⟪x, A x⟫_ℂ - alpha * ‖x‖ ^ 2 ≤
      RCLike.re ⟪(DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)ᗮ.starProjection x,
          (A + K) ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)ᗮ.starProjection x)⟫_ℂ -
        alpha * ‖(DavisKahan1970.Section8.canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)ᗮ.starProjection x‖ ^ 2 := by
  have hamb := theorem8_1_upperCompressionRepulsion_canonicalBranch A K P hdelta
    hA hK hAP hPlow hPhigh hKP hKPperp x
  have h0 : ⟪K x, x⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (hKPperp x hx) hx
  have hcross : RCLike.re ⟪x, K x⟫_ℂ = 0 := by
    rw [← inner_re_symm (𝕜 := ℂ) (K x) x, h0]
    simp
  have hsplit : RCLike.re ⟪x, (A + K) x⟫_ℂ = RCLike.re ⟪x, A x⟫_ℂ := by
    rw [add_apply, inner_add_right, map_add, hcross,
      add_zero]
  rwa [hsplit] at hamb

/-- **Theorem 8.1(i), source-literal lower form.**

Restricted to the original `P` block, the ambient inequality of
`theorem8_1_lowerCompressionRepulsion_canonicalBranch` is exactly the printed
companion

  `(α + δ) - A₀ ≤ C₀ ((α + δ) - Λ₀) C₀`

read as a quadratic form.  As in the upper case, restricting is what makes the
statement source-literal: off-diagonality of `K` kills its cross term on `P`,
so the left-hand side is the form of the *unperturbed* compression `A₀` and not
of `A + K`.  The right-hand side is the form of `(α + δ) - Λ₀` evaluated at
`C₀ x = P_Q x`, the printed cosine-sandwiched term.

The orientation is the mirror of the upper theorem: there `x ∈ Pᗮ` and
`K x ∈ P`, here `x ∈ P` and `K x ∈ Pᗮ`, so the vanishing inner product is read
off in the other argument order. -/
theorem theorem8_1_lowerCompressionRepulsion
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    {x : H} (hx : x ∈ P) :
    (alpha + delta) * ‖x‖ ^ 2 - RCLike.re ⟪x, A x⟫_ℂ ≤
      (alpha + delta) * ‖(DavisKahan1970.Section8.canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha).starProjection x‖ ^ 2 -
        RCLike.re ⟪(DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha).starProjection x,
          (A + K) ((DavisKahan1970.Section8.canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha).starProjection x)⟫_ℂ := by
  have hamb := theorem8_1_lowerCompressionRepulsion_canonicalBranch A K P hdelta
    hA hK hAP hPlow hPhigh hKP hKPperp x
  have h0 : ⟪x, K x⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hx (hKP x hx)
  have hcross : RCLike.re ⟪x, K x⟫_ℂ = 0 := by
    rw [h0]
    simp
  have hsplit : RCLike.re ⟪x, (A + K) x⟫_ℂ = RCLike.re ⟪x, A x⟫_ℂ := by
    rw [add_apply, inner_add_right, map_add, hcross,
      add_zero]
  rwa [hsplit] at hamb

end CanonicalBranchCompression

end Section8
end DavisKahan1970
end TauCeti
