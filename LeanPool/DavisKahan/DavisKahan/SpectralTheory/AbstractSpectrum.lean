/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import Mathlib.Analysis.InnerProductSpace.Spectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Operator.Restriction

/-!
# Restricted-operator spectra and provisional embedding interfaces

This module provides the theorem-facing spectrum of a bounded operator and of
its actual restriction to an invariant subspace.  These definitions use the
Banach-algebra spectrum, so continuous spectral components are retained in
infinite dimension.  The double-angle embedding remains a provisional target
and should eventually be built from the closed range of an isometric embedding.
-/


/-! ## Construction plan

* Route inequalities derived from real spectra through `TauCeti.SpectralOrder`;
  the set definitions here are exact, but the real spectral-order theorem is a
  separate analytic obligation.
* Keep spectral separation hypotheses tied to invariant subspaces.  For a
  self-adjoint operator, the reduction hypotheses used by the paper supply the
  required invariance for both the selected subspace and its orthogonal
  complement.
* Build `sinTwoThetaEmbedding` from the sine and cosine blocks of the isometric
  embedding.  In principal coordinates its singular values must be
  `sin (2 * theta_i)`; prove this first on the two-plane decomposition and then
  transport it by unitary invariance.
-/

namespace TauCeti
namespace DavisKahan
namespace Foundation

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- A bounded operator represented as an orthogonal projection. -/
def IsOrthogonalProjection (P : E →L[𝕜] E) : Prop :=
  P ∘L P = P ∧ P.IsSymmetric

/-- Off-diagonal relative to an explicitly supplied projection. -/
def IsOffDiagonalRelativeToProjection (P H : E →L[𝕜] E) : Prop :=
  P ∘L H ∘L P = 0 ∧
    (ContinuousLinearMap.id 𝕜 E - P) ∘L H ∘L
      (ContinuousLinearMap.id 𝕜 E - P) = 0

-- `@[reducible]` for the same reason as `PartialMap.IsSelfAdjoint`: this is the shape
-- `ContinuousLinearMap.restrict` already asks for, and unifiers matching at `instances`
-- transparency have to be able to see that.
/-- A subspace is invariant under a bounded operator. -/
@[reducible] def InvariantFor (A : E →L[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ U, A x ∈ U

/-- `ContinuousLinearMap.coe_restrict_apply`, restated for a hypothesis in `InvariantFor` form.

Mathlib's lemma is stated for `ContinuousLinearMap.restrict`'s own hypothesis shape, and
`InvariantFor A U` is only definitionally that shape.  `simp` and `rw` match at `instances`
transparency and will not bridge the two, so the Mathlib lemma never fires on the `InvariantFor`
restrictions this development actually builds.  Compare
`TauCeti.coe_restrict_apply_of_isInvariant` for the `LinearMap` counterpart. -/
@[simp] theorem coe_restrict_apply_of_invariantFor {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    (hU : InvariantFor A U) (x : U) :
    ((A.restrict hU x : U) : E) = A (x : E) := rfl

/-- Real points in the Banach-algebra spectrum of an `RCLike` operator.

The operator algebra is naturally an algebra over its native scalar field
`𝕜`, not uniformly an algebra over `ℝ`.  We therefore take `spectrum 𝕜 A` and
pull it back along the canonical embedding `ℝ → 𝕜`.  For self-adjoint
operators this captures the full spectrum, while retaining continuous spectral
components in infinite dimension. -/
def realSpectrum (A : E →L[𝕜] E) : Set ℝ :=
  {r | (r : 𝕜) ∈ spectrum 𝕜 A}

/-- Real spectrum of the actual restriction of `A` to an invariant subspace.

The existential packages the invariance proof needed to construct
`A.restrict`.  Proof irrelevance makes the resulting restricted operator
independent of which proof is supplied.  If no invariance proof exists the set
is empty, so theorem-facing containment and separation predicates below also
record invariance explicitly rather than permitting a vacuous gap. -/
def restrictedSpectrum (A : E →L[𝕜] E)
    (U : Submodule 𝕜 E) : Set ℝ :=
  {r | ∃ hU : InvariantFor A U,
    (r : 𝕜) ∈ spectrum 𝕜 (A.restrict hU)}

/-- With a fixed invariance proof, `restrictedSpectrum` is exactly the real
part of the Banach-algebra spectrum of that restriction. -/
theorem restrictedSpectrum_eq_restrictionSpectrum
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (hU : InvariantFor A U) :
    restrictedSpectrum A U = {r : ℝ | (r : 𝕜) ∈ spectrum 𝕜 (A.restrict hU)} := by
  ext r
  constructor
  · rintro ⟨hU', hr⟩
    simpa using hr
  · intro hr
    exact ⟨hU, hr⟩

/-- The restriction to the full subspace has the original real spectrum. -/
theorem restrictedSpectrum_top (A : E →L[𝕜] E) :
    restrictedSpectrum A (⊤ : Submodule 𝕜 E) = realSpectrum A := by
  have hU : InvariantFor A (⊤ : Submodule 𝕜 E) := fun x _ => Submodule.mem_top
  rw [restrictedSpectrum_eq_restrictionSpectrum A ⊤ hU]
  ext r
  simp only [realSpectrum, Set.mem_ofPred_eq, ContinuousLinearMap.spectrum_restrict_top]

/-- The spectrum of the actual restriction to `U` is contained in `s`.

Invariance is part of the predicate, preventing a containment hypothesis from
being discharged merely because no restricted operator was available. -/
def SpectrumIn (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (s : Set ℝ) : Prop :=
  InvariantFor A U ∧ restrictedSpectrum A U ⊆ s

/-- Spectral containment remembers the invariance needed to form the restriction. -/
theorem SpectrumIn.invariant {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {s : Set ℝ} (h : SpectrumIn A U s) : InvariantFor A U := h.1

/-- The restricted spectrum is contained in the declared spectral set. -/
theorem SpectrumIn.subset {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {s : Set ℝ} (h : SpectrumIn A U s) : restrictedSpectrum A U ⊆ s := h.2

/-- Spectral containment is monotone in the containing set. -/
theorem SpectrumIn.mono {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {s t : Set ℝ} (h : SpectrumIn A U s) (hst : s ⊆ t) :
    SpectrumIn A U t :=
  ⟨h.1, h.2.trans hst⟩

/-- A scalar function is uniformly bounded on the real Banach-algebra
spectrum. -/
def BoundedOnSpectrum (A : E →L[𝕜] E) (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ realSpectrum A, |f x| ≤ C

/-- Distance between two real spectral sets. -/
noncomputable def spectralDistance (s t : Set ℝ) : ℝ :=
  sInf {r | ∃ x ∈ s, ∃ y ∈ t, r = |x - y|}

/-- Two actual restricted spectra are separated by at least `d`. -/
def SpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  InvariantFor A U ∧ InvariantFor B V ∧
    ∀ a ∈ restrictedSpectrum A U, ∀ b ∈ restrictedSpectrum B V,
      d ≤ |a - b|

/-- **Separation on `⊤` is separation of the two real spectra**, with the invariance conjuncts
discharged.

This is the consumer-facing form of `restrictedSpectrum_top`: a `SpectraSeparated _ ⊤ _ ⊤`
hypothesis is exactly a statement about `realSpectrum`, so any transport of `realSpectrum` —
complexification, for instance — now applies to it. -/
theorem spectraSeparated_top_iff (A : E →L[𝕜] E) (B : F →L[𝕜] F) (d : ℝ) :
    SpectraSeparated A (⊤ : Submodule 𝕜 E) B (⊤ : Submodule 𝕜 F) d ↔
      ∀ a ∈ realSpectrum A, ∀ b ∈ realSpectrum B, d ≤ |a - b| := by
  have htopA : InvariantFor A (⊤ : Submodule 𝕜 E) := fun x _ => Submodule.mem_top
  have htopB : InvariantFor B (⊤ : Submodule 𝕜 F) := fun x _ => Submodule.mem_top
  constructor
  · rintro ⟨-, -, h⟩ a ha b hb
    exact h a (by rw [restrictedSpectrum_top]; exact ha) b (by rw [restrictedSpectrum_top]; exact hb)
  · intro h
    refine ⟨htopA, htopB, fun a ha b hb => ?_⟩
    rw [restrictedSpectrum_top] at ha hb
    exact h a ha b hb

/-- Spectral separation is symmetric after exchanging the two restricted blocks. -/
theorem SpectraSeparated.symm {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →L[𝕜] F} {V : Submodule 𝕜 F} {d : ℝ}
    (h : SpectraSeparated A U B V d) : SpectraSeparated B V A U d := by
  refine ⟨h.2.1, h.1, ?_⟩
  intro b hb a ha
  simpa [abs_sub_comm] using h.2.2 a ha b hb

/-- Weakening the required gap preserves spectral separation. -/
theorem SpectraSeparated.mono_gap {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →L[𝕜] F} {V : Submodule 𝕜 F} {d e : ℝ}
    (h : SpectraSeparated A U B V d) (hed : e ≤ d) :
    SpectraSeparated A U B V e := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro a ha b hb
  exact hed.trans (h.2.2 a ha b hb)

/-- The selected block of `A` is separated from the complementary block of
`B`. -/
def HybridGap (A B : E →L[𝕜] E) (U V : Submodule 𝕜 E)
    (d : ℝ) : Prop := SpectraSeparated A U B Vᗮ d

/-- Internal spectral gap of an invariant subspace and its invariant
orthogonal complement. -/
def InternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop := SpectraSeparated A U A Uᗮ d

/-- Ordered separation of actual restricted spectra, giving a constant-one
Sylvester estimate. -/
def OrderedSpectraSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F) (d : ℝ) : Prop :=
  InvariantFor A U ∧ InvariantFor B V ∧
    ∀ a ∈ restrictedSpectrum A U, ∀ b ∈ restrictedSpectrum B V,
      a + d ≤ b

/-- Weakening an ordered gap preserves ordered spectral separation. -/
theorem OrderedSpectraSeparated.mono_gap
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →L[𝕜] F} {V : Submodule 𝕜 F} {d e : ℝ}
    (h : OrderedSpectraSeparated A U B V d) (hed : e ≤ d) :
    OrderedSpectraSeparated A U B V e := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro a ha b hb
  exact (add_le_add_right hed a).trans (h.2.2 a ha b hb)

/-- Ordered separation implies absolute spectral separation. -/
theorem OrderedSpectraSeparated.toSpectraSeparated
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →L[𝕜] F} {V : Submodule 𝕜 F} {d : ℝ}
    (h : OrderedSpectraSeparated A U B V d) (hd : 0 ≤ d) :
    SpectraSeparated A U B V d := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro a ha b hb
  have habd := h.2.2 a ha b hb
  have hab : a ≤ b := by linarith
  have hgap : d ≤ b - a := by linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hab)]
  linarith

/-- The reverse ordered orientation also implies the symmetric absolute gap. -/
theorem OrderedSpectraSeparated.toSpectraSeparated_swapped
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →L[𝕜] F} {V : Submodule 𝕜 F} {d : ℝ}
    (h : OrderedSpectraSeparated B V A U d) (hd : 0 ≤ d) :
    SpectraSeparated A U B V d :=
  (h.toSpectraSeparated hd).symm

/-- Interval/exterior separation from the classical `sin Θ` theorem. -/
def IntervalExteriorSeparated (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (B : F →L[𝕜] F) (V : Submodule 𝕜 F)
    (left right d : ℝ) : Prop :=
  SpectrumIn A U (Set.Icc left right) ∧
    SpectrumIn B V {x | x ≤ left - d ∨ right + d ≤ x}

/-- Interval/exterior placement gives the corresponding absolute spectral gap. -/
theorem IntervalExteriorSeparated.toSpectraSeparated
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E}
    {B : F →L[𝕜] F} {V : Submodule 𝕜 F}
    {left right d : ℝ}
    (h : IntervalExteriorSeparated A U B V left right d) :
    SpectraSeparated A U B V d := by
  refine ⟨h.1.1, h.2.1, ?_⟩
  intro a ha b hb
  have haI := h.1.2 ha
  have hbE := h.2.2 hb
  rcases haI with ⟨hla, har⟩
  rcases hbE with hble | hrdb
  · have hgap : d ≤ a - b := by linarith
    exact hgap.trans (le_abs_self (a - b))
  · have hgap : d ≤ b - a := by linarith
    calc
      d ≤ b - a := hgap
      _ ≤ |b - a| := le_abs_self (b - a)
      _ = |a - b| := abs_sub_comm b a

/-- One spectral component lies in a finite gap of the other. -/
def FiniteGapConfiguration (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop :=
  ∃ left right, left ≤ right ∧
    SpectrumIn A U (Set.Icc left right) ∧
    SpectrumIn A Uᗮ {x | x ≤ left - d ∨ right + d ≤ x}

/-- Weakening a finite interval/exterior gap preserves the configuration. -/
theorem FiniteGapConfiguration.mono_gap
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {d e : ℝ}
    (h : FiniteGapConfiguration A U d) (hed : e ≤ d) :
    FiniteGapConfiguration A U e := by
  rcases h with ⟨left, right, hlr, hU, hUc⟩
  refine ⟨left, right, hlr, hU, hUc.mono ?_⟩
  intro x hx
  rcases hx with hx | hx
  · left
    linarith
  · right
    linarith

/-- A finite interval/exterior configuration supplies the internal absolute gap. -/
theorem FiniteGapConfiguration.toInternalGap
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {d : ℝ}
    (h : FiniteGapConfiguration A U d) : InternalGap A U d := by
  rcases h with ⟨left, right, _hlr, hU, hUc⟩
  exact (show IntervalExteriorSeparated A U A Uᗮ left right d from ⟨hU, hUc⟩).toSpectraSeparated

/-- Ordered internal gap, in either orientation. -/
def OrderedInternalGap (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    (d : ℝ) : Prop :=
  OrderedSpectraSeparated A U A Uᗮ d ∨
    OrderedSpectraSeparated A Uᗮ A U d

/-- Weakening an ordered internal gap preserves it. -/
theorem OrderedInternalGap.mono_gap
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {d e : ℝ}
    (h : OrderedInternalGap A U d) (hed : e ≤ d) :
    OrderedInternalGap A U e := by
  rcases h with h | h
  · exact Or.inl (h.mono_gap hed)
  · exact Or.inr (h.mono_gap hed)

/-- Either ordered orientation gives the internal absolute gap. -/
theorem OrderedInternalGap.toInternalGap
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {d : ℝ}
    (h : OrderedInternalGap A U d) (hd : 0 ≤ d) :
    InternalGap A U d := by
  rcases h with h | h
  · exact h.toSpectraSeparated hd
  · exact h.toSpectraSeparated_swapped hd

/-- Weakening an internal gap preserves it. -/
theorem InternalGap.mono_gap
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {d e : ℝ}
    (h : InternalGap A U d) (hed : e ≤ d) :
    InternalGap A U e := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro a ha b hb
  exact hed.trans (h.2.2 a ha b hb)

/-! ## Restriction of scalars to `ℝ`

`realSpectrum` pulls `spectrum 𝕜 A` back along `ℝ → 𝕜`.  The lemma below identifies it with an
honest real spectrum — that of `A` viewed as a continuous `ℝ`-linear map — which is what lets an
`ℝ`-only theorem be applied to an operator over a general `RCLike` field.  `RCLike` admits no case
split into `ℝ` and `ℂ`, so restriction of scalars is the only uniform route.

**The two instances are `scoped`, deliberately.**  Mathlib keeps `NormedSpace.restrictScalars` and
`InnerProductSpace.rclikeToReal` out of the instance graph because a global `Module ℝ E` alongside
`Module 𝕜 E` is a diamond; `local` would work here but would force every consumer to install a
*second* declaration of the same instance, and two defeq-but-distinct instances is what makes
`isDefEq` searches blow up (see lane `{lane:CPLX-DEDUP-3}`, where exactly that timed out a build).
A scope gives every consumer the same declaration. -/

namespace RealScalarRestriction

/-- `E` as a normed space over `ℝ`, by restricting its `𝕜`-structure. -/
noncomputable scoped instance realNormedSpace
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ 𝕜 E

/-- `E` as a *real inner product* space, by taking the real part of the
`𝕜`-inner product.

Mathlib declares `InnerProductSpace.rclikeToReal` as a reducible non-instance on
purpose — installing it globally would clash with the `𝕜`-structure — so it is
`scoped` here alongside the other two.  **`scoped` rather than `local`, and that
is not a style choice**: lanes `{lane:CPLX-DEDUP-3}` and `{lane:CPLX-DEDUP-4}`
measured what happens when the same instance is re-declared `local` in several
files, which is that `isDefEq` has to prove two distinct declarations defeq and
diverges.  One declaration, opened where needed, has nothing to prove. -/
noncomputable scoped instance realInnerProductSpace
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    InnerProductSpace ℝ E :=
  InnerProductSpace.rclikeToReal 𝕜 E

/-- The restricted `ℝ`-action is compatible with the ambient `𝕜`-action. -/
scoped instance realTower
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    IsScalarTower ℝ 𝕜 E :=
  ⟨fun r c x => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩

end RealScalarRestriction

open scoped RealScalarRestriction in
/-- **The real spectrum is the spectrum after restricting scalars to `ℝ`.**

Both sides are the failure of `r - A` to be invertible, and `ContinuousLinearMap.isUnit_iff_bijective`
reduces each to bijectivity of the *same* underlying function: the inverse of a `𝕜`-linear
continuous bijection is automatically `𝕜`-linear, so nothing is lost by forgetting the `𝕜`-structure.

This is the step that lets a theorem proved over `ℝ` reach an operator over a general `RCLike`
field. -/
theorem realSpectrum_eq_spectrum_restrictScalars
    [CompleteSpace E] (A : E →L[𝕜] E) :
    realSpectrum A = spectrum ℝ (A.restrictScalars ℝ) := by
  ext r
  show ((r : 𝕜) ∈ spectrum 𝕜 A) ↔ _
  rw [spectrum.mem_iff, spectrum.mem_iff, not_iff_not,
    ContinuousLinearMap.isUnit_iff_bijective, ContinuousLinearMap.isUnit_iff_bijective]
  have hfun : ⇑((algebraMap ℝ (E →L[ℝ] E)) r - A.restrictScalars ℝ)
      = ⇑((algebraMap 𝕜 (E →L[𝕜] E)) (r : 𝕜) - A) := rfl
  rw [hfun]

end Foundation
end DavisKahan
end TauCeti
