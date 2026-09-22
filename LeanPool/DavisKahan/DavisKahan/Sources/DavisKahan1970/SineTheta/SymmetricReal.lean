/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Anthropic Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.FullAngleReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Lemma61
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReducingSubspace.RestrictionExtras
import LeanPool.DavisKahan.DavisKahan.Sylvester.RealUnbounded

/-! # Symmetric Real -/


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan Proposition 6.1 over a real Hilbert space

This is the real-scalar sibling of
`DavisKahan.Sources.DavisKahan1970.SineTheta.Symmetric`.  Standing assumption 1
of the transcription allows the ambient space to be real or complex, and
assumption 4 allows infinite dimension; the complex file covers only half of
that scope because its *conclusion* is phrased through
`sinAngleOperatorC`, which is `cfc Real.sin` of the complex operator angle.

The mathematics is not reopened here.  The proof is the paper's, step for step,
and it is the same proof the complex file runs:

1. Apply the one-sided sine theorem to the selected block of `A` and the
   complementary block of `B`.
2. Apply it again with `A` and `B` interchanged.
3. Use Lemma 6.1 to combine the two orthogonal cross blocks sharply.
4. Use Lemma 6.2 to contract the two corresponding perturbation blocks by the
   norm of `H = B - A`.

The one substitution is in step 1--2:
`davisKahan1970_sylvester_complex` becomes `real_unbounded_sylvester_kyFan`.
Everything else -- `lemma61_all_kyFan`, `diagonalPair_all_kyFan_le`,
the ambient/subspace singular-value transport, and `SymmetricNormingFunction`
-- is already `RCLike`-generic and is reused verbatim.

## Why the conclusion is stated on `crossSineSum`

Step 5 of the complex file identifies the cross-block sum with the literal
functional-calculus `sin Theta`.  There is no real continuous functional
calculus in this repository, and building one would be the wrong response: a
unitarily invariant norm sees an operator *only* through its complete
singular-value sequence, so the source statement does not need an operator that
is pointwise the sine of an angle.  It needs an operator carrying the paper's
whole-space sine singular-value sequence.

`crossSineSum U V` is such an operator, and that is compiled rather than
asserted: `crossSineSum_same_projectionDiff` gives it exactly the complete
approximation-singular-value sequence of `P_V - P_U`, which is the paper's
whole-space `sin Theta` sequence.  `crossSineSum_normingMem_iff_and_gauge_eq`
below records the resulting norm identity, and
`result_every_unitarilyInvariantNorm_representative_real` states the theorem for
an arbitrary operator with that sequence, which is the precise sense in which
only the source singular sequence matters.

No complexification, no finite-dimensionality, and no caller-supplied
inequality occurs anywhere below.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open scoped TauCeti.CompleteSubspace

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The source dictionary for the real whole-space sine

`crossSineSum U V` is the operator the real theorem below bounds.  The two
lemmas here are what make that a statement about the paper's `sin Theta` rather
than about an ad hoc projection expression.  Neither is used in the proof of
Proposition 6.1; they exist so the identification is checked by the compiler. -/

/-- The real cross-block sum carries exactly the complete singular-value
sequence of the repository's **literal** real full sine angle
`sourceFullSinR`, the direct sum of the two source-directed angles.

This is the compiled answer to the source-acceptance question: every source
unitarily invariant norm evaluates the operator appearing in
`result_every_unitarilyInvariantNorm_real` exactly as it evaluates the paper's
whole-space `sin Theta` list.  The equality is proved through the projector
difference and exact complexification invariance of the approximation numbers,
and the real theorem's own statement does not mention a complexification.  It was
also proved this way because no real continuous functional calculus existed; one
now does (`ForTauCeti/Analysis/InnerProductSpace/RealContinuousFunctionalCalculus.lean`,
and at every `RCLike` field), so that is history rather than an obstruction.

It is stated as a raw equality of approximation numbers rather than as a
`SameApproximationSingularSequence`, because that relation fixes a single scalar
field for both operands and `sourceFullSinR` is by construction an operator
over `ℂ` on complexified coordinates.  Approximation numbers are real, so the
comparison itself is unproblematic; only the relation's binders are too narrow.
Lifting this to a `SymmetricNormingFunction` equality would need a cross-field
counterpart of `SameApproximationSingularSequence.normingExtendedGauge_eq`, which
is deliberately not added here -- the norm-level dictionary the theorem below
actually uses is `crossSineSum_normingMem_iff_and_gauge_eq`, entirely over `ℝ`. -/
theorem approximationNumber_sourceFullSinR_eq_crossSineSum
    (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ∀ n : ℕ,
      (sourceFullSinR V U).approximationNumber n =
        (crossSineSum U V).approximationNumber n := by
  -- `crossSineSum U V` has the singular values of `P_V - P_U`.
  have hreal : SameApproximationSingularSequence
      (crossSineSum U V) (V.starProjection - U.starProjection) :=
    crossSineSum_same_projectionDiff U V
  -- The literal full sine of the complexified pair has the singular values of
  -- the complexified projector difference.
  have hcomplex : SameApproximationSingularSequence
      (sourceFullSinR V U)
      ((TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule
          V).starProjection -
        (TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule
          U).starProjection) :=
    sourceFullSin_same_projectionDifference _ _
  have hcx :
      (TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule
          V).starProjection -
        (TauCeti.DavisKahan.Foundation.RealComplexification.complexifySubmodule
          U).starProjection =
        TauCeti.RealComplexification.complexify
          (V.starProjection - U.starProjection) := by
    rw [TauCeti.DavisKahan.Foundation.RealComplexification.starProjection_complexifySubmodule,
      TauCeti.DavisKahan.Foundation.RealComplexification.starProjection_complexifySubmodule,
      RealComplexification.complexify_sub]
  rw [hcx] at hcomplex
  intro n
  rw [hcomplex n, ComplexificationApproximation.approximationNumber_complexify,
    (hreal n).symm]

/-- Exact bounded inputs of Proposition 6.1 over a real Hilbert space.  This is
`SymmetricSinThetaProblem` with `ℂ` replaced by `ℝ`: the same printed data
and nothing derived.  The two gap hypotheses are the paper's two applications of
the original sine theorem. -/
structure RealSymmetricSinThetaProblem where
  /-- The first bounded symmetric operator in the real comparison problem. -/
  A : E →L[ℝ] E
  /-- The second bounded symmetric operator in the real comparison problem. -/
  B : E →L[ℝ] E
  selfAdjoint_A : A.IsSymmetric
  selfAdjoint_B : B.IsSymmetric
  /-- The chosen reducing subspace of the first operator. -/
  U : Submodule ℝ E
  /-- The chosen reducing subspace of the second operator. -/
  V : Submodule ℝ E
  proj_U : U.HasOrthogonalProjection
  proj_V : V.HasOrthogonalProjection
  reduces_A_U : A.Reduces U
  reduces_B_V : B.Reduces V
  /-- The common positive form gap for the two opposite subspace comparisons. -/
  gap : ℝ
  gap_pos : 0 < gap
  gap_U_to_Vperp : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction ((A.toLinearMap.toPMap ⊤)) U
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace A U reduces_A_U))
    (TauCeti.LinearPMap.reducingRestriction ((B.toLinearMap.toPMap ⊤)) Vᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace B V reduces_B_V).orthogonal)
    gap
  gap_V_to_Uperp : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction ((B.toLinearMap.toPMap ⊤)) V
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace B V reduces_B_V))
    (TauCeti.LinearPMap.reducingRestriction ((A.toLinearMap.toPMap ⊤)) Uᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace A U reduces_A_U).orthogonal)
    gap

attribute [instance] RealSymmetricSinThetaProblem.proj_U
attribute [instance] RealSymmetricSinThetaProblem.proj_V

namespace RealSymmetricSinThetaProblem

/-- The perturbation `H` of the paper. -/
def perturbation (P : RealSymmetricSinThetaProblem (E := E)) : E →L[ℝ] E :=
  P.B - P.A

/-- Internal data for the first directed application. -/
noncomputable def forwardData
    (P : RealSymmetricSinThetaProblem (E := E)) :
    UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := P.U) (G := P.Vᗮ) where
  A := (P.B.toLinearMap.toPMap ⊤)
  A₀ := TauCeti.LinearPMap.reducingRestriction ((P.A.toLinearMap.toPMap ⊤)) P.U
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U)
  Λ₁ := TauCeti.LinearPMap.reducingRestriction ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal
  X := P.U.subtypeL
  F₁ := P.Vᗮ.subtypeL
  residual := P.perturbation ∘L P.U.subtypeL
  X_maps_domain := by intro x; simp
  F₁_maps_domain := by intro x; simp
  residual_eq := by
    intro x
    rfl
  intertwines :=
    PartialMap.reducingRestriction_inclusion_intertwines
      ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal

/-- Internal data for the reversed application. -/
noncomputable def reverseData
    (P : RealSymmetricSinThetaProblem (E := E)) :
    UnboundedSinThetaData (𝕜 := ℝ) (E := E) (F := P.V) (G := P.Uᗮ) where
  A := (P.A.toLinearMap.toPMap ⊤)
  A₀ := TauCeti.LinearPMap.reducingRestriction ((P.B.toLinearMap.toPMap ⊤)) P.V
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V)
  Λ₁ := TauCeti.LinearPMap.reducingRestriction ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
    (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal
  X := P.V.subtypeL
  F₁ := P.Uᗮ.subtypeL
  residual := (-P.perturbation) ∘L P.V.subtypeL
  X_maps_domain := by intro x; simp
  F₁_maps_domain := by intro x; simp
  residual_eq := by
    intro x
    simp [perturbation]
    rfl
  intertwines :=
    PartialMap.reducingRestriction_inclusion_intertwines
      ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal

/-- The first exact cross-projection block. -/
def forwardSineBlock (P : RealSymmetricSinThetaProblem (E := E)) :
    E →L[ℝ] E :=
  P.Vᗮ.starProjection ∘L P.U.starProjection

/-- The reversed exact cross-projection block. -/
def reverseSineBlock (P : RealSymmetricSinThetaProblem (E := E)) :
    E →L[ℝ] E :=
  P.Uᗮ.starProjection ∘L P.V.starProjection

/-- The first projected perturbation block from the proof of Proposition 6.1. -/
def forwardResidualBlock (P : RealSymmetricSinThetaProblem (E := E)) :
    E →L[ℝ] E :=
  P.Vᗮ.starProjection ∘L P.perturbation ∘L P.U.starProjection

/-- The second projected perturbation block. -/
def reverseResidualBlock (P : RealSymmetricSinThetaProblem (E := E)) :
    E →L[ℝ] E :=
  P.V.starProjection ∘L P.perturbation ∘L P.Uᗮ.starProjection

/-- First one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem forward_all_kyFan
    (P : RealSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.forwardSineBlock ≤
        kyFanApproximationGauge k P.forwardResidualBlock := by
  intro k
  set D := P.forwardData with hD
  have hA0 : _root_.IsSelfAdjoint D.A₀ :=
    PartialMap.reducingRestriction_isSelfAdjoint
      ((P.A.toLinearMap.toPMap ⊤)) P.U
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U)
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_A))
  have hL : _root_.IsSelfAdjoint D.Λ₁ :=
    PartialMap.reducingRestriction_isSelfAdjoint
      ((P.B.toLinearMap.toPMap ⊤)) P.Vᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.B)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_B))
  have hEq := unbounded_adjoint_residual_block_identity D
    (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.B)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_B)) hA0 hL
  -- The only mathematical substitution against the complex file.
  have hraw := real_unbounded_sylvester_kyFan hA0 hL P.gap_pos
    P.gap_U_to_Vperp hEq k
  -- The ambient transport lemma produces the *adjoint* orientation of each
  -- block, so both comparisons are heterogeneous and both pick up one adjoint
  -- step.  Ky Fan gauges are adjoint-invariant, so nothing is lost.
  have hsine : SameApproximationSingularSequence
      (P.U.starProjection ∘L P.Vᗮ.starProjection)
      (D.X.adjoint ∘L D.F₁) := by
    simpa [hD, forwardData, Submodule.adjoint_subtypeL,
      Submodule.starProjection, ContinuousLinearMap.comp_assoc] using
      sameApproximationSingularValues_ambientSubspaceBlock
        P.Vᗮ P.U (D.X.adjoint ∘L D.F₁)
  have hsineAdj : P.forwardSineBlock =
      (P.U.starProjection ∘L P.Vᗮ.starProjection).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection P.U).adjoint_eq,
      (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq]
    rfl
  have hres : SameApproximationSingularSequence
      (-P.forwardResidualBlock.adjoint)
      (-(D.residual.adjoint ∘L D.F₁)) := by
    simpa [hD, forwardData, forwardResidualBlock, perturbation,
      Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
      Submodule.starProjection,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      map_sub, map_neg] using
      sameApproximationSingularValues_ambientSubspaceBlock
        P.Vᗮ P.U (-(D.residual.adjoint ∘L D.F₁))
  have hgaugeSine : kyFanApproximationGauge k P.forwardSineBlock =
      kyFanApproximationGauge k (D.X.adjoint ∘L D.F₁) := by
    rw [hsineAdj, kyFanApproximationGauge_adjoint,
      hsine.kyFanApproximationGauge_eq k]
  have hgaugeRes : kyFanApproximationGauge k P.forwardResidualBlock =
      kyFanApproximationGauge k (-(D.residual.adjoint ∘L D.F₁)) := by
    rw [← kyFanApproximationGauge_adjoint k P.forwardResidualBlock,
      ← kyFanApproximationGauge_neg k P.forwardResidualBlock.adjoint,
      hres.kyFanApproximationGauge_eq k]
  rw [hgaugeSine, hgaugeRes]
  exact hraw

/-- Reversed one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem reverse_all_kyFan
    (P : RealSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.reverseSineBlock ≤
        kyFanApproximationGauge k P.reverseResidualBlock := by
  intro k
  set D := P.reverseData with hD
  have hA0 : _root_.IsSelfAdjoint D.A₀ :=
    PartialMap.reducingRestriction_isSelfAdjoint
      ((P.B.toLinearMap.toPMap ⊤)) P.V
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V)
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.B)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_B))
  have hL : _root_.IsSelfAdjoint D.Λ₁ :=
    PartialMap.reducingRestriction_isSelfAdjoint
      ((P.A.toLinearMap.toPMap ⊤)) P.Uᗮ
      (TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal
      (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_A))
  have hEq := unbounded_adjoint_residual_block_identity D
    (TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_A)) hA0 hL
  have hraw := real_unbounded_sylvester_kyFan hA0 hL P.gap_pos
    P.gap_V_to_Uperp hEq k
  -- Mirror of the forward case: the ambient transport lemma again produces the
  -- adjoint orientation, and Ky Fan gauges are adjoint-invariant.
  have hsine : SameApproximationSingularSequence
      (P.V.starProjection ∘L P.Uᗮ.starProjection)
      (D.X.adjoint ∘L D.F₁) := by
    simpa [hD, reverseData, Submodule.adjoint_subtypeL,
      Submodule.starProjection, ContinuousLinearMap.comp_assoc] using
      sameApproximationSingularValues_ambientSubspaceBlock
        P.Uᗮ P.V (D.X.adjoint ∘L D.F₁)
  have hsineAdj : P.reverseSineBlock =
      (P.V.starProjection ∘L P.Uᗮ.starProjection).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection P.V).adjoint_eq,
      (isSelfAdjoint_starProjection P.Uᗮ).adjoint_eq]
    rfl
  -- Here `A` and `B` are symmetric, so the ambient block comes out in the
  -- original orientation rather than the adjoint one.
  have hadjA : P.A.adjoint = P.A := P.selfAdjoint_A.isSelfAdjoint.adjoint_eq
  have hadjB : P.B.adjoint = P.B := P.selfAdjoint_B.isSelfAdjoint.adjoint_eq
  have hres : SameApproximationSingularSequence
      P.reverseResidualBlock
      (-(D.residual.adjoint ∘L D.F₁)) := by
    simpa [hD, reverseData, reverseResidualBlock, perturbation, hadjA, hadjB,
      Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
      Submodule.starProjection,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      map_sub, map_neg] using
      sameApproximationSingularValues_ambientSubspaceBlock
        P.Uᗮ P.V (-(D.residual.adjoint ∘L D.F₁))
  have hgaugeSine : kyFanApproximationGauge k P.reverseSineBlock =
      kyFanApproximationGauge k (D.X.adjoint ∘L D.F₁) := by
    rw [hsineAdj, kyFanApproximationGauge_adjoint,
      hsine.kyFanApproximationGauge_eq k]
  have hgaugeRes : kyFanApproximationGauge k P.reverseResidualBlock =
      kyFanApproximationGauge k (-(D.residual.adjoint ∘L D.F₁)) :=
    hres.kyFanApproximationGauge_eq k
  rw [hgaugeSine, hgaugeRes]
  exact hraw

/-- Ky Fan form of the real symmetric sine theorem, before universal Fan
dominance.  The left-hand operator is the paper's whole-space sine
representative; see `crossSineSum_normingMem_iff_and_gauge_eq`. -/
theorem symmetric_all_kyFan_real
    (P : RealSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k (crossSineSum P.U P.V) ≤
        kyFanApproximationGauge k P.perturbation := by
  intro k
  have hadjA : P.A.adjoint = P.A := P.selfAdjoint_A.isSelfAdjoint.adjoint_eq
  have hadjB : P.B.adjoint = P.B := P.selfAdjoint_B.isSelfAdjoint.adjoint_eq
  have hadjH : P.perturbation.adjoint = P.perturbation := by
    simp [perturbation, map_sub, hadjA, hadjB]
  have hUperp : P.Uᗮᗮ = P.U := Submodule.orthogonal_orthogonal P.U
  have hgapNorm : ‖P.gap‖ = P.gap := abs_of_pos P.gap_pos
  -- Lemma 6.1 is applied to the *scaled identity*, not to a scaled
  -- perturbation: the two one-sided estimates bound `gap` times a pure
  -- projection product, and `projectionBlock Ω Γ (gap • id)` is exactly
  -- `gap` times that product.  Feeding it `gap • H` would instead demand
  -- `gap * gauge (block H) ≤ gauge (block H)`, which is false for `gap > 1`.
  have hcombine := lemma61_all_kyFan P.Uᗮ P.V
    (P.gap • ContinuousLinearMap.id ℝ E) (P.gap • ContinuousLinearMap.id ℝ E)
    P.perturbation P.perturbation
    (fun j => by
      have hrev := P.reverse_all_kyFan j
      have hblockSine :
          projectionBlock P.Uᗮ P.V (P.gap • ContinuousLinearMap.id ℝ E) =
            P.gap • P.reverseSineBlock := by
        ext x; simp [projectionBlock, reverseSineBlock]
      have hblockRes :
          projectionBlock P.Uᗮ P.V P.perturbation =
            P.reverseResidualBlock.adjoint := by
        simp [projectionBlock, reverseResidualBlock,
          ContinuousLinearMap.adjoint_comp, hadjH,
          (isSelfAdjoint_starProjection P.V).adjoint_eq,
          (isSelfAdjoint_starProjection P.Uᗮ).adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      rw [hblockSine, hblockRes, kyFanApproximationGauge_smul,
        hgapNorm, kyFanApproximationGauge_adjoint]
      exact hrev)
    (fun j => by
      have hfwd := P.forward_all_kyFan j
      have hblockSine :
          projectionBlock P.Uᗮᗮ P.Vᗮ (P.gap • ContinuousLinearMap.id ℝ E) =
            P.gap • P.forwardSineBlock.adjoint := by
        simp only [hUperp]
        ext x
        simp [projectionBlock, forwardSineBlock,
          ContinuousLinearMap.adjoint_comp,
          (isSelfAdjoint_starProjection P.U).adjoint_eq,
          (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq]
      have hblockRes :
          projectionBlock P.Uᗮᗮ P.Vᗮ P.perturbation =
            P.forwardResidualBlock.adjoint := by
        simp only [hUperp]
        simp [projectionBlock, forwardResidualBlock,
          ContinuousLinearMap.adjoint_comp, hadjH,
          (isSelfAdjoint_starProjection P.U).adjoint_eq,
          (isSelfAdjoint_starProjection P.Vᗮ).adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      rw [hblockSine, hblockRes, kyFanApproximationGauge_smul,
        hgapNorm, kyFanApproximationGauge_adjoint,
        kyFanApproximationGauge_adjoint]
      exact hfwd) k
  have hres := diagonalPair_all_kyFan_le P.Uᗮ P.V P.perturbation k
  have hcross :
      projectionBlock P.Uᗮ P.V (P.gap • ContinuousLinearMap.id ℝ E) +
          projectionBlock P.Uᗮᗮ P.Vᗮ (P.gap • ContinuousLinearMap.id ℝ E) =
        P.gap • crossSineSum P.U P.V := by
    simp only [hUperp]
    ext x
    simp [projectionBlock, crossSineSum, smul_add]
  rw [hcross] at hcombine
  calc
    P.gap * kyFanApproximationGauge k (crossSineSum P.U P.V) =
        kyFanApproximationGauge k (P.gap • crossSineSum P.U P.V) := by
      rw [kyFanApproximationGauge_smul, hgapNorm]
    _ ≤ kyFanApproximationGauge k
        (diagonalPair P.Uᗮ P.V P.perturbation) := hcombine
    _ ≤ kyFanApproximationGauge k P.perturbation := hres

/-- **Davis--Kahan 1970, Proposition 6.1 over a real Hilbert space**, for every
normalized unitarily invariant norm in the source sense. -/
theorem result_every_unitarilyInvariantNorm_real
    (P : RealSymmetricSinThetaProblem (E := E))
    (N : SymmetricNormingFunction) (hH : N.Mem P.perturbation) :
    N.Mem (crossSineSum P.U P.V) ∧
      P.gap * N.gauge (crossSineSum P.U P.V) ≤ N.gauge P.perturbation :=
  N.mul_gauge_le_of_all_mul_kyFan_le P.gap_pos hH P.symmetric_all_kyFan_real

omit [CompleteSpace E] in
/-- The compiled source dictionary.  Every source norm evaluates the operator
appearing in `result_every_unitarilyInvariantNorm_real` exactly as it evaluates
the paper's whole-space sine singular-value list, which is the complete
approximation-singular-value sequence of the projector difference
`P_V - P_U`. -/
theorem crossSineSum_normingMem_iff_and_gauge_eq
    (P : RealSymmetricSinThetaProblem (E := E))
    (N : SymmetricNormingFunction) :
    (N.Mem (crossSineSum P.U P.V) ↔
        N.Mem (P.V.starProjection - P.U.starProjection)) ∧
      N.gauge (crossSineSum P.U P.V) =
        N.gauge (P.V.starProjection - P.U.starProjection) :=
  SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N
    (crossSineSum_same_projectionDiff P.U P.V)

/-- Proposition 6.1 for an arbitrary source realization of `sin Theta`: any
operator carrying the paper's whole-space sine singular-value sequence obeys
the same estimate.  This is the exact sense in which the theorem depends only
on the source singular sequence and not on a chosen functional calculus. -/
theorem result_every_unitarilyInvariantNorm_representative_real
    (P : RealSymmetricSinThetaProblem (E := E))
    (S : SinThetaRepresentative (crossSineSum P.U P.V))
    (N : SymmetricNormingFunction) (hH : N.Mem P.perturbation) :
    N.Mem S.operator ∧
      P.gap * N.gauge S.operator ≤ N.gauge P.perturbation := by
  obtain ⟨hmem, hbound⟩ := P.result_every_unitarilyInvariantNorm_real N hH
  obtain ⟨hiff, hgauge⟩ :=
    SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N
      S.same_singular_values
  exact ⟨hiff.mpr hmem, by rw [hgauge]; exact hbound⟩

end RealSymmetricSinThetaProblem

end

end ExactSinTheta
end DavisKahan
end TauCeti
