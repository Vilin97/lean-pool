/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.HeterogeneousRepresentative
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Symmetric
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.SymmetricReal
public import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarGeneric
public import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-! # Common Domain Symmetric -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan Proposition 6.1 on a common dense domain

The Appendix to Section 6 says that "the hypotheses of Proposition 6.1 and Theorem 6.1
may be relaxed similarly".  Theorem 6.1 was relaxed in
`DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomainTheorems`; this module performs
the same relaxation for Proposition 6.1, the *symmetric* sine theorem.

`SymmetricSinThetaProblem` requires two **bounded** self-adjoint operators
`A B : E →L[𝕜] E`.  Here `A` and `B` are two closed densely defined self-adjoint
operators sharing one domain, and the paper's `H = B - A` is the bounded operator that
represents their difference on that common domain.  The bounded problem is the special
case `A.domain = B.domain = ⊤`, recorded as `ofBounded` below.

## What actually has to change

Nothing in the paper's argument.  Both applications of the one-sided sine theorem already
run through `UnboundedSinThetaData`, `unbounded_adjoint_residual_block_identity` and the
Section 5 Sylvester estimate, all of which are stated for closed operators; the bounded
file only reaches them through `(`..toLinearMap.toPMap ⊤)  The combination step
(Lemma 6.1), the perturbation-block contraction (Lemma 6.2) and the identification of the
cross-block sum with the literal functional-calculus `sin Θ` see only bounded projections
and the bounded `H`, so they are reused verbatim.

Exactly one fact has to be re-proved rather than assumed.  In the bounded file
`H.adjoint = H` follows from `A.adjoint = A` and `B.adjoint = B`.  Here `H` is a separate
bounded operator, and its symmetry is a *consequence* of the data rather than a
hypothesis: `⟪H x, y⟫ = ⟪x, H y⟫` holds for `x, y` in the common domain because `A` and
`B` are symmetric there, and both sides are continuous, so density of the domain extends
it to the whole space.  That is `perturbation_isSymmetric`.  It is deliberately not a
structure field: adding it would strengthen the source hypotheses.

## Scalar scope

Standing assumption 1 of the transcription allows the ambient space to be real or complex,
so the whole development below is stated over `[RCLike 𝕜]`.  Two things resisted when this
module was written; both have since been resolved one layer down, and the record of what
they were is kept because it explains the shape of the statements.

*The Sylvester estimate.*  `davisKahan1970_sylvester_complex` is hardwired to `ℂ` at every
level beneath it, and `real_unbounded_sylvester_kyFan` is hardwired to `ℝ`; no
`RCLike`-generic form is proved directly.  The estimate is therefore named as a property of
the scalar field, `HasUnboundedSylvesterKyFan`, exactly as the min--max lower bound already
is.  This file said until 2026-09-03 that the two fixed-field proofs could not be combined
"since `RCLike` offers no discriminator between its two models"; that was wrong.
`RCLike.I_eq_zero_or_im_I_eq_one` is the discriminator, `Sylvester/ScalarTransport.lean`
transports the estimate along the resulting field isomorphism, and the class is an instance
at **every** `RCLike` field.  Nothing below takes it as a binder.

*The conclusion operator.*  `sinAngleOperatorC` was `cfc Real.arcsin` of the **complex**
operator angle, and at the time this repository built no real continuous functional
calculus.  It now does, at every `RCLike` field
(`ForTauCeti/Analysis/RCLike/ScalarTransportFunctionalCalculus.lean`), and
`TauCeti.DavisKahan.Angle.sinAngleOperator` is the scalar-generic angle.  The statements
below still conclude on `crossSineSum U V`, which is not a defect: the two have the same
complete approximation-singular-value sequence, which is all a unitarily invariant norm can
see, and the block form is what the proof produces.  So the
`RCLike`-generic conclusion is carried by `crossSineSum U V`, which
`crossSineSum_same_projectionDiff` gives exactly the complete
approximation-singular-value sequence of `P_V - P_U` -- the paper's whole-space `sin Θ`
sequence, and all a unitarily invariant norm can see.  Over `ℂ` the literal form is then
recovered verbatim through `crossSineSum_same_literalSin`, so `symmetric_all_kyFan`
and `result_every_unitarilyInvariantNorm` keep the statements they always had.

## Main results

* `CommonDomainSymmetricSinThetaProblem`: the common-domain inputs of
  Proposition 6.1, over any `RCLike` field;
* `CommonDomainSymmetricSinThetaProblem.symmetric_all_kyFan_crossSineSum`: the
  estimate for every finite Ky Fan gauge, over any `RCLike` field;
* `CommonDomainSymmetricSinThetaProblem.symmetric_all_kyFan`: the same over `ℂ`, on
  the literal functional-calculus `sin Θ`;
* `CommonDomainSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm`:
  Proposition 6.1 for every normalized unitarily invariant norm in the source sense;
* `CommonDomainSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm_real`:
  the real-scalar form of the same;
* `CommonDomainSymmetricSinThetaProblem.ofBounded` and `.ofBoundedReal`: the bounded
  Proposition 6.1 inputs are an instance of the common-domain ones, over each field.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open TauCeti.DavisKahanExt


open scoped InnerProductSpace

noncomputable section

universe u v

open TauCeti.DavisKahan
open scoped TauCeti.CompleteSubspace

section ScalarGeneric

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Common-domain inputs of Proposition 6.1.

`A` and `B` are closed densely defined self-adjoint operators on one and the same dense
domain, `U` reduces `A`, `V` reduces `B`, and `perturbation` is the paper's bounded `H`,
which represents `B - A` on the common domain.  The two gap hypotheses are the paper's two
applications of the original sine theorem, now between reducing restrictions of *unbounded*
operators. -/
structure CommonDomainSymmetricSinThetaProblem
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] where
  /-- The unperturbed closed self-adjoint operator. -/
  A : E →ₗ.[𝕜] E
  /-- The perturbed closed self-adjoint operator. -/
  B : E →ₗ.[𝕜] E
  /-- `A` is self-adjoint in the domain-aware sense. -/
  selfAdjoint_A : IsSelfAdjoint A
  /-- `B` is self-adjoint in the domain-aware sense. -/
  selfAdjoint_B : IsSelfAdjoint B
  /-- `U` reduces `A`. -/
  reduces_A_U : TauCeti.LinearPMap.ReducesSubspace A U
  /-- `V` reduces `B`. -/
  reduces_B_V : TauCeti.LinearPMap.ReducesSubspace B V
  /-- The paper's bounded perturbation `H`. -/
  perturbation : E →L[𝕜] E
  /-- The two operators share one domain. -/
  domain_eq : A.domain = B.domain
  /-- On the common domain the perturbation represents `B - A`. -/
  perturbation_eq : ∀ (x : E) (hA : x ∈ A.domain) (hB : x ∈ B.domain),
    B ⟨x, hB⟩ - A ⟨x, hA⟩ = perturbation x
  /-- The paper's spectral separation `δ`. -/
  gap : ℝ
  /-- The separation is positive. -/
  gap_pos : 0 < gap
  /-- First application of the one-sided sine theorem. -/
  gap_U_to_Vperp : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction A U reduces_A_U)
    (TauCeti.LinearPMap.reducingRestriction B Vᗮ reduces_B_V.orthogonal)
    gap
  /-- Second application, with `A` and `B` interchanged. -/
  gap_V_to_Uperp : FormBoundedSylvesterGap
    (TauCeti.LinearPMap.reducingRestriction B V reduces_B_V)
    (TauCeti.LinearPMap.reducingRestriction A Uᗮ reduces_A_U.orthogonal)
    gap

namespace CommonDomainSymmetricSinThetaProblem

variable {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- The common domain, read from `A` into `B`. -/
theorem mem_domain_B (P : CommonDomainSymmetricSinThetaProblem U V)
    {x : E} (hx : x ∈ P.A.domain) : x ∈ P.B.domain := by
  rw [← P.domain_eq]; exact hx

/-- The common domain, read from `B` into `A`. -/
theorem mem_domain_A (P : CommonDomainSymmetricSinThetaProblem U V)
    {x : E} (hx : x ∈ P.B.domain) : x ∈ P.A.domain := by
  rw [P.domain_eq]; exact hx

/-- **The perturbation is symmetric**, and this is derived rather than assumed.

On the common domain the identity `⟪H x, y⟫ = ⟪x, H y⟫` is the difference of the symmetry
relations of `B` and of `A`.  Both sides are continuous in each argument separately and
the domain is dense, so the identity extends to the whole space in two steps. -/
theorem perturbation_isSymmetric (P : CommonDomainSymmetricSinThetaProblem U V) :
    P.perturbation.IsSymmetric := by
  have hAs := TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint P.selfAdjoint_A
  have hBs := TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint P.selfAdjoint_B
  have hdense : Dense ((P.A.domain : Submodule 𝕜 E) : Set E) :=
    P.selfAdjoint_A.dense_domain
  have hcore : ∀ x ∈ ((P.A.domain : Submodule 𝕜 E) : Set E),
      ∀ y ∈ ((P.A.domain : Submodule 𝕜 E) : Set E),
      ⟪P.perturbation x, y⟫_𝕜 = ⟪x, P.perturbation y⟫_𝕜 := by
    intro x hx y hy
    have hxB : x ∈ P.B.domain := P.mem_domain_B hx
    have hyB : y ∈ P.B.domain := P.mem_domain_B hy
    rw [← P.perturbation_eq x hx hxB, ← P.perturbation_eq y hy hyB,
      inner_sub_left, inner_sub_right,
      hBs ⟨x, hxB⟩ ⟨y, hyB⟩, hAs ⟨x, hx⟩ ⟨y, hy⟩]
  -- Freeze `x` in the domain and extend in `y`.
  have step : ∀ x ∈ ((P.A.domain : Submodule 𝕜 E) : Set E), ∀ y : E,
      ⟪P.perturbation x, y⟫_𝕜 = ⟪x, P.perturbation y⟫_𝕜 := by
    intro x hx
    have hf : Continuous fun y : E => ⟪P.perturbation x, y⟫_𝕜 :=
      continuous_const.inner continuous_id
    have hg : Continuous fun y : E => ⟪x, P.perturbation y⟫_𝕜 :=
      continuous_const.inner P.perturbation.continuous
    exact fun y => congrFun (Continuous.ext_on hdense hf hg fun y hy => hcore x hx y hy) y
  -- Now extend in `x`.
  intro x y
  have hf : Continuous fun x : E => ⟪P.perturbation x, y⟫_𝕜 :=
    P.perturbation.continuous.inner continuous_const
  have hg : Continuous fun x : E => ⟪x, P.perturbation y⟫_𝕜 :=
    continuous_id.inner continuous_const
  exact congrFun (Continuous.ext_on hdense hf hg fun x hx => step x hx y) x

/-- Internal data for the first directed application: the ambient operator is `B`, the
trial operator is the reducing restriction of `A` to `U`, and the complementary operator
is the reducing restriction of `B` to `Vᗮ`. -/
noncomputable def forwardData
    (P : CommonDomainSymmetricSinThetaProblem U V) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := U) (G := Vᗮ) where
  A := P.B
  A₀ := TauCeti.LinearPMap.reducingRestriction P.A U P.reduces_A_U
  Λ₁ := TauCeti.LinearPMap.reducingRestriction P.B Vᗮ P.reduces_B_V.orthogonal
  X := U.subtypeL
  F₁ := Vᗮ.subtypeL
  residual := P.perturbation ∘L U.subtypeL
  X_maps_domain := fun x =>
    P.mem_domain_B
      (PartialMap.reducingRestriction_inclusion_mem_domain P.A U P.reduces_A_U x)
  F₁_maps_domain := fun y =>
    PartialMap.reducingRestriction_inclusion_mem_domain P.B Vᗮ
      P.reduces_B_V.orthogonal y
  residual_eq := by
    intro x
    have hmemA : ((x : U) : E) ∈ P.A.domain :=
      PartialMap.reducingRestriction_inclusion_mem_domain P.A U P.reduces_A_U x
    have hint :
        (U.subtypeL
            ((TauCeti.LinearPMap.reducingRestriction P.A U P.reduces_A_U) x) : E) =
          P.A ⟨((x : U) : E), hmemA⟩ :=
      (PartialMap.reducingRestriction_inclusion_intertwines P.A U P.reduces_A_U x).symm
    rw [hint]
    exact P.perturbation_eq _ hmemA (P.mem_domain_B hmemA)
  intertwines :=
    PartialMap.reducingRestriction_inclusion_intertwines P.B Vᗮ
      P.reduces_B_V.orthogonal

/-- Internal data for the reversed application, with `A` and `B` interchanged. -/
noncomputable def reverseData
    (P : CommonDomainSymmetricSinThetaProblem U V) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := V) (G := Uᗮ) where
  A := P.A
  A₀ := TauCeti.LinearPMap.reducingRestriction P.B V P.reduces_B_V
  Λ₁ := TauCeti.LinearPMap.reducingRestriction P.A Uᗮ P.reduces_A_U.orthogonal
  X := V.subtypeL
  F₁ := Uᗮ.subtypeL
  residual := (-P.perturbation) ∘L V.subtypeL
  X_maps_domain := fun x =>
    P.mem_domain_A
      (PartialMap.reducingRestriction_inclusion_mem_domain P.B V P.reduces_B_V x)
  F₁_maps_domain := fun y =>
    PartialMap.reducingRestriction_inclusion_mem_domain P.A Uᗮ
      P.reduces_A_U.orthogonal y
  residual_eq := by
    intro x
    have hmemB : ((x : V) : E) ∈ P.B.domain :=
      PartialMap.reducingRestriction_inclusion_mem_domain P.B V P.reduces_B_V x
    have hmemA : ((x : V) : E) ∈ P.A.domain := P.mem_domain_A hmemB
    have hint :
        (V.subtypeL
            ((TauCeti.LinearPMap.reducingRestriction P.B V P.reduces_B_V) x) : E) =
          P.B ⟨((x : V) : E), hmemB⟩ :=
      (PartialMap.reducingRestriction_inclusion_intertwines P.B V P.reduces_B_V x).symm
    rw [hint]
    have hPE := P.perturbation_eq ((x : V) : E) hmemA hmemB
    have : P.A ⟨((x : V) : E), hmemA⟩ -
        P.B ⟨((x : V) : E), hmemB⟩ = -P.perturbation ((x : V) : E) := by
      rw [← hPE]; abel
    exact this
  intertwines :=
    PartialMap.reducingRestriction_inclusion_intertwines P.A Uᗮ
      P.reduces_A_U.orthogonal

/-- The first exact cross-projection block.  It is determined by the two subspaces alone;
the problem argument is carried only so that the estimates below can be stated with the
same field notation as the bounded module. -/
def forwardSineBlock (_P : CommonDomainSymmetricSinThetaProblem U V) :
    E →L[𝕜] E :=
  Vᗮ.starProjection ∘L U.starProjection

/-- The reversed exact cross-projection block, likewise determined by the two subspaces
alone. -/
def reverseSineBlock (_P : CommonDomainSymmetricSinThetaProblem U V) :
    E →L[𝕜] E :=
  Uᗮ.starProjection ∘L V.starProjection

/-- The first projected perturbation block from the proof of Proposition 6.1. -/
def forwardResidualBlock (P : CommonDomainSymmetricSinThetaProblem U V) :
    E →L[𝕜] E :=
  Vᗮ.starProjection ∘L P.perturbation ∘L U.starProjection

/-- The second projected perturbation block. -/
def reverseResidualBlock (P : CommonDomainSymmetricSinThetaProblem U V) :
    E →L[𝕜] E :=
  V.starProjection ∘L P.perturbation ∘L Uᗮ.starProjection

/-- First one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem forward_all_kyFan
    (P : CommonDomainSymmetricSinThetaProblem U V) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.forwardSineBlock ≤
        kyFanApproximationGauge k P.forwardResidualBlock := by
  intro k
  set D := P.forwardData with hD
  have hA0 : _root_.IsSelfAdjoint D.A₀ :=
    PartialMap.reducingRestriction_isSelfAdjoint P.A U P.reduces_A_U P.selfAdjoint_A
  have hL : _root_.IsSelfAdjoint D.Λ₁ :=
    PartialMap.reducingRestriction_isSelfAdjoint P.B Vᗮ
      P.reduces_B_V.orthogonal P.selfAdjoint_B
  have hEq := unbounded_adjoint_residual_block_identity D P.selfAdjoint_B hA0 hL
  -- The only step that is not scalar-generic on its own; see the module docstring.
  have hraw := unbounded_sylvester_kyFan hA0 hL P.gap_pos P.gap_U_to_Vperp hEq k
  -- The ambient transport lemma produces the *adjoint* orientation of each block, so
  -- both comparisons are heterogeneous and both pick up one adjoint step.  Ky Fan
  -- gauges are adjoint-invariant, so nothing is lost.
  have hsine : SameApproximationSingularSequence
      (U.starProjection ∘L Vᗮ.starProjection)
      (D.X.adjoint ∘L D.F₁) := by
    simpa [hD, forwardData, Submodule.adjoint_subtypeL,
      Submodule.starProjection, ContinuousLinearMap.comp_assoc] using
      sameApproximationSingularValues_ambientSubspaceBlock
        Vᗮ U (D.X.adjoint ∘L D.F₁)
  have hsineAdj : P.forwardSineBlock =
      (U.starProjection ∘L Vᗮ.starProjection).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection U).adjoint_eq,
      (isSelfAdjoint_starProjection Vᗮ).adjoint_eq]
    rfl
  have hres : SameApproximationSingularSequence
      (-P.forwardResidualBlock.adjoint)
      (-(D.residual.adjoint ∘L D.F₁)) := by
    simpa [hD, forwardData, forwardResidualBlock,
      Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
      Submodule.starProjection,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      map_neg] using
      sameApproximationSingularValues_ambientSubspaceBlock
        Vᗮ U (-(D.residual.adjoint ∘L D.F₁))
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
    (P : CommonDomainSymmetricSinThetaProblem U V) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.reverseSineBlock ≤
        kyFanApproximationGauge k P.reverseResidualBlock := by
  intro k
  set D := P.reverseData with hD
  have hA0 : _root_.IsSelfAdjoint D.A₀ :=
    PartialMap.reducingRestriction_isSelfAdjoint P.B V P.reduces_B_V P.selfAdjoint_B
  have hL : _root_.IsSelfAdjoint D.Λ₁ :=
    PartialMap.reducingRestriction_isSelfAdjoint P.A Uᗮ
      P.reduces_A_U.orthogonal P.selfAdjoint_A
  have hEq := unbounded_adjoint_residual_block_identity D P.selfAdjoint_A hA0 hL
  have hraw := unbounded_sylvester_kyFan hA0 hL P.gap_pos P.gap_V_to_Uperp hEq k
  -- Mirror of the forward case: the ambient transport lemma again produces the adjoint
  -- orientation, and Ky Fan gauges are adjoint-invariant.
  have hsine : SameApproximationSingularSequence
      (V.starProjection ∘L Uᗮ.starProjection)
      (D.X.adjoint ∘L D.F₁) := by
    simpa [hD, reverseData, Submodule.adjoint_subtypeL,
      Submodule.starProjection, ContinuousLinearMap.comp_assoc] using
      sameApproximationSingularValues_ambientSubspaceBlock
        Uᗮ V (D.X.adjoint ∘L D.F₁)
  have hsineAdj : P.reverseSineBlock =
      (V.starProjection ∘L Uᗮ.starProjection).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection V).adjoint_eq,
      (isSelfAdjoint_starProjection Uᗮ).adjoint_eq]
    rfl
  -- Here the perturbation is symmetric, so the ambient block comes out in the original
  -- orientation rather than the adjoint one.
  have hadjH : P.perturbation.adjoint = P.perturbation :=
    P.perturbation_isSymmetric.isSelfAdjoint.adjoint_eq
  have hres : SameApproximationSingularSequence
      P.reverseResidualBlock
      (-(D.residual.adjoint ∘L D.F₁)) := by
    simpa [hD, reverseData, reverseResidualBlock, hadjH,
      Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
      Submodule.starProjection,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      map_neg] using
      sameApproximationSingularValues_ambientSubspaceBlock
        Uᗮ V (-(D.residual.adjoint ∘L D.F₁))
  have hgaugeSine : kyFanApproximationGauge k P.reverseSineBlock =
      kyFanApproximationGauge k (D.X.adjoint ∘L D.F₁) := by
    rw [hsineAdj, kyFanApproximationGauge_adjoint,
      hsine.kyFanApproximationGauge_eq k]
  have hgaugeRes : kyFanApproximationGauge k P.reverseResidualBlock =
      kyFanApproximationGauge k (-(D.residual.adjoint ∘L D.F₁)) :=
    hres.kyFanApproximationGauge_eq k
  rw [hgaugeSine, hgaugeRes]
  exact hraw

/-- **Ky Fan form of the common-domain symmetric sine theorem over any `RCLike` field**,
before universal Fan dominance.

The left-hand operator is `crossSineSum U V`, the paper's whole-space sine
representative: `crossSineSum_same_projectionDiff` gives it exactly the complete
approximation-singular-value sequence of `P_V - P_U`, which is all a unitarily invariant
norm can see.  Over `ℂ` the literal functional-calculus form is `symmetric_all_kyFan`. -/
theorem symmetric_all_kyFan_crossSineSum
    (P : CommonDomainSymmetricSinThetaProblem U V) :
    ∀ k,
      P.gap * kyFanApproximationGauge k (crossSineSum U V) ≤
        kyFanApproximationGauge k P.perturbation := by
  intro k
  have hadjH : P.perturbation.adjoint = P.perturbation :=
    P.perturbation_isSymmetric.isSelfAdjoint.adjoint_eq
  have hUperp : Uᗮᗮ = U := Submodule.orthogonal_orthogonal U
  have hgapNorm : ‖((P.gap : ℝ) : 𝕜)‖ = P.gap := by
    rw [RCLike.norm_ofReal, abs_of_pos P.gap_pos]
  -- Lemma 6.1 is applied to the *scaled identity*, not to a scaled perturbation: the two
  -- one-sided estimates bound `gap` times a pure projection product, and
  -- `projectionBlock Ω Γ (gap • id)` is exactly `gap` times that product.
  have hcombine := lemma61_all_kyFan Uᗮ V
    (((P.gap : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)
    (((P.gap : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E)
    P.perturbation P.perturbation
    (fun j => by
      have hrev := P.reverse_all_kyFan j
      have hblockSine :
          projectionBlock Uᗮ V (((P.gap : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) =
            ((P.gap : ℝ) : 𝕜) • P.reverseSineBlock := by
        ext x; simp [projectionBlock, reverseSineBlock]
      have hblockRes :
          projectionBlock Uᗮ V P.perturbation =
            P.reverseResidualBlock.adjoint := by
        simp [projectionBlock, reverseResidualBlock,
          ContinuousLinearMap.adjoint_comp, hadjH,
          (isSelfAdjoint_starProjection V).adjoint_eq,
          (isSelfAdjoint_starProjection Uᗮ).adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      rw [hblockSine, hblockRes, kyFanApproximationGauge_smul,
        hgapNorm, kyFanApproximationGauge_adjoint]
      exact hrev)
    (fun j => by
      have hfwd := P.forward_all_kyFan j
      have hblockSine :
          projectionBlock Uᗮᗮ Vᗮ (((P.gap : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) =
            ((P.gap : ℝ) : 𝕜) • P.forwardSineBlock.adjoint := by
        simp only [hUperp]
        ext x
        simp [projectionBlock, forwardSineBlock,
          ContinuousLinearMap.adjoint_comp,
          (isSelfAdjoint_starProjection U).adjoint_eq,
          (isSelfAdjoint_starProjection Vᗮ).adjoint_eq]
      have hblockRes :
          projectionBlock Uᗮᗮ Vᗮ P.perturbation =
            P.forwardResidualBlock.adjoint := by
        simp only [hUperp]
        simp [projectionBlock, forwardResidualBlock,
          ContinuousLinearMap.adjoint_comp, hadjH,
          (isSelfAdjoint_starProjection U).adjoint_eq,
          (isSelfAdjoint_starProjection Vᗮ).adjoint_eq,
          ContinuousLinearMap.comp_assoc]
      rw [hblockSine, hblockRes, kyFanApproximationGauge_smul,
        hgapNorm, kyFanApproximationGauge_adjoint,
        kyFanApproximationGauge_adjoint]
      exact hfwd) k
  have hres := diagonalPair_all_kyFan_le Uᗮ V P.perturbation k
  have hcross :
      projectionBlock Uᗮ V (((P.gap : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) +
          projectionBlock Uᗮᗮ Vᗮ
            (((P.gap : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E) =
        ((P.gap : ℝ) : 𝕜) • crossSineSum U V := by
    simp only [hUperp]
    ext x
    simp [projectionBlock, crossSineSum, smul_add]
  rw [hcross] at hcombine
  calc
    P.gap * kyFanApproximationGauge k (crossSineSum U V) =
        kyFanApproximationGauge k (((P.gap : ℝ) : 𝕜) • crossSineSum U V) := by
      rw [kyFanApproximationGauge_smul, hgapNorm]
    _ ≤ kyFanApproximationGauge k
        (diagonalPair Uᗮ V P.perturbation) := hcombine
    _ ≤ kyFanApproximationGauge k P.perturbation := hres

/-- **Davis--Kahan 1970, Proposition 6.1 on a common dense domain over any `RCLike`
field**, for every normalized unitarily invariant norm in the source sense.

The conclusion is carried by the paper's whole-space sine representative; see
`crossSineSum_normingMem_iff_and_gauge_eq` for the compiled dictionary identifying its
singular-value sequence with the paper's. -/
theorem result_every_unitarilyInvariantNorm_crossSineSum
    (P : CommonDomainSymmetricSinThetaProblem U V)
    (N : SymmetricNormingFunction) (hH : N.Mem P.perturbation) :
    N.Mem (crossSineSum U V) ∧
      P.gap * N.gauge (crossSineSum U V) ≤ N.gauge P.perturbation :=
  N.mul_gauge_le_of_all_mul_kyFan_le P.gap_pos hH P.symmetric_all_kyFan_crossSineSum

/-- The compiled source dictionary.  Every source norm evaluates the operator appearing in
`result_every_unitarilyInvariantNorm_crossSineSum` exactly as it evaluates the paper's
whole-space sine singular-value list, which is the complete approximation-singular-value
sequence of the projector difference `P_V - P_U`. -/
theorem crossSineSum_normingMem_iff_and_gauge_eq
    (_P : CommonDomainSymmetricSinThetaProblem U V)
    (N : SymmetricNormingFunction) :
    (N.Mem (crossSineSum U V) ↔
        N.Mem (V.starProjection - U.starProjection)) ∧
      N.gauge (crossSineSum U V) =
        N.gauge (V.starProjection - U.starProjection) :=
  SameApproximationSingularSequence.normingMem_iff_and_gauge_eq N
    (crossSineSum_same_projectionDiff U V)

end CommonDomainSymmetricSinThetaProblem

end ScalarGeneric

section Complex

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace CommonDomainSymmetricSinThetaProblem

variable {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Ky Fan form of the common-domain symmetric sine theorem, before universal Fan
dominance.

This is `symmetric_all_kyFan_crossSineSum` read through
`crossSineSum_same_literalSin`, which says the cross-block sum and the literal
functional-calculus `sin Θ` have the same complete singular-value sequence. -/
theorem symmetric_all_kyFan
    (P : CommonDomainSymmetricSinThetaProblem U V) :
    ∀ k,
      P.gap * kyFanApproximationGauge k
          (TauCeti.DavisKahan.Angle.sinAngleOperatorC U V) ≤
        kyFanApproximationGauge k P.perturbation := by
  intro k
  have h := P.symmetric_all_kyFan_crossSineSum k
  rwa [(crossSineSum_same_literalSin U V).kyFanApproximationGauge_eq k] at h

/-- **Davis--Kahan 1970, Proposition 6.1 on a common dense domain**, for every normalized
unitarily invariant norm in the source sense.

`A` and `B` are unbounded closed self-adjoint operators sharing one dense domain, and the
paper's `H` is the bounded operator representing `B - A` there.  This is the relaxation
the Appendix to Section 6 licenses when it says the hypotheses of Proposition 6.1 may be
relaxed in the same way as those of Theorem 6.1. -/
theorem result_every_unitarilyInvariantNorm
    (P : CommonDomainSymmetricSinThetaProblem U V)
    (N : SymmetricNormingFunction) (hH : N.Mem P.perturbation) :
    N.Mem (TauCeti.DavisKahan.Angle.sinAngleOperatorC U V) ∧
      P.gap * N.gauge
          (TauCeti.DavisKahan.Angle.sinAngleOperatorC U V) ≤
        N.gauge P.perturbation :=
  N.mul_gauge_le_of_all_mul_kyFan_le P.gap_pos hH P.symmetric_all_kyFan

/-- **The bounded Proposition 6.1 inputs are an instance of the common-domain ones**, at
the full domain.  This is what makes the theorem above a genuine relaxation rather than a
parallel statement: no hypothesis of `SymmetricSinThetaProblem` is dropped, and the
domain hypotheses are discharged by `⊤ = ⊤`. -/
noncomputable def ofBounded (P : SymmetricSinThetaProblem (E := E)) :
    CommonDomainSymmetricSinThetaProblem P.U P.V where
  A := (P.A.toLinearMap.toPMap ⊤)
  B := (P.B.toLinearMap.toPMap ⊤)
  selfAdjoint_A := TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_A)
  selfAdjoint_B := TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.B)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_B)
  reduces_A_U := TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U
  reduces_B_V := TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V
  perturbation := P.perturbation
  domain_eq := rfl
  perturbation_eq := by intro x _ _; rfl
  gap := P.gap
  gap_pos := P.gap_pos
  gap_U_to_Vperp := P.gap_U_to_Vperp
  gap_V_to_Uperp := P.gap_V_to_Uperp

/-- The bounded instance keeps the paper's perturbation `H = B - A`. -/
@[simp] theorem ofBounded_perturbation (P : SymmetricSinThetaProblem (E := E)) :
    (ofBounded P).perturbation = P.perturbation := rfl

/-- The bounded instance keeps the paper's spectral separation. -/
@[simp] theorem ofBounded_gap (P : SymmetricSinThetaProblem (E := E)) :
    (ofBounded P).gap = P.gap := rfl

end CommonDomainSymmetricSinThetaProblem

end Complex

section Real

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace CommonDomainSymmetricSinThetaProblem

variable {U V : Submodule ℝ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Ky Fan form of the common-domain symmetric sine theorem over a **real** Hilbert space.

This is the `RCLike`-generic theorem at `ℝ`, not a second proof.  The left-hand operator is
the paper's whole-space sine representative, for the reason recorded in the module
docstring: a unitarily invariant norm sees only the singular-value sequence, so none of the
statements here needs a functional-calculus sine.  The module docstring used to say that no
real continuous functional calculus is constructed anywhere; one is, at every `RCLike` field,
and that changes what is *possible* here rather than what is *needed*. -/
theorem symmetric_all_kyFan_real
    (P : CommonDomainSymmetricSinThetaProblem U V) :
    ∀ k,
      P.gap * kyFanApproximationGauge k (crossSineSum U V) ≤
        kyFanApproximationGauge k P.perturbation :=
  P.symmetric_all_kyFan_crossSineSum

/-- **Davis--Kahan 1970, Proposition 6.1 on a common dense domain over a real Hilbert
space**, for every normalized unitarily invariant norm in the source sense.

`A` and `B` are unbounded closed self-adjoint operators on one dense real domain, and the
paper's `H` is the bounded operator representing `B - A` there. -/
theorem result_every_unitarilyInvariantNorm_real
    (P : CommonDomainSymmetricSinThetaProblem U V)
    (N : SymmetricNormingFunction) (hH : N.Mem P.perturbation) :
    N.Mem (crossSineSum U V) ∧
      P.gap * N.gauge (crossSineSum U V) ≤ N.gauge P.perturbation :=
  P.result_every_unitarilyInvariantNorm_crossSineSum N hH

/-- **The real bounded Proposition 6.1 inputs are an instance of the common-domain ones**,
at the full domain.  This is the real counterpart of `ofBounded`, and it carries the same
guarantee: no hypothesis of `RealSymmetricSinThetaProblem` is dropped and none is
added, the domain hypotheses being discharged by `⊤ = ⊤`.  Without it the real
common-domain statement would only be parallel to the real bounded one rather than a
relaxation of it. -/
noncomputable def ofBoundedReal (P : RealSymmetricSinThetaProblem (E := E)) :
    CommonDomainSymmetricSinThetaProblem P.U P.V where
  A := (P.A.toLinearMap.toPMap ⊤)
  B := (P.B.toLinearMap.toPMap ⊤)
  selfAdjoint_A := TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.A)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_A)
  selfAdjoint_B := TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := P.B)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr P.selfAdjoint_B)
  reduces_A_U := TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.A P.U P.reduces_A_U
  reduces_B_V := TauCeti.DavisKahanExt.PartialMap.ofBounded_reducesSubspace P.B P.V P.reduces_B_V
  perturbation := P.perturbation
  domain_eq := rfl
  perturbation_eq := by intro x _ _; rfl
  gap := P.gap
  gap_pos := P.gap_pos
  gap_U_to_Vperp := P.gap_U_to_Vperp
  gap_V_to_Uperp := P.gap_V_to_Uperp

/-- The real bounded instance keeps the paper's perturbation `H = B - A`. -/
@[simp] theorem ofBoundedReal_perturbation
    (P : RealSymmetricSinThetaProblem (E := E)) :
    (ofBoundedReal P).perturbation = P.perturbation := rfl

/-- The real bounded instance keeps the paper's spectral separation. -/
@[simp] theorem ofBoundedReal_gap (P : RealSymmetricSinThetaProblem (E := E)) :
    (ofBoundedReal P).gap = P.gap := rfl

end CommonDomainSymmetricSinThetaProblem

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
