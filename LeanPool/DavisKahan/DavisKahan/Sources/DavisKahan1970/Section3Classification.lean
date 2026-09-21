/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.GenericReconstruction
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.SpectralMultiplicityClassification
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Section3Classification -/
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 3.1 in the paper's multiplicity phrasing

Theorem 3.1 classifies ordered pairs of subspaces up to a unitary of the ambient space.  Its
invariant has two halves: the dimensions of the four elementary Halmos summands, and the *spectral
multiplicity function* of the angle operator on the generic part.  The two source-facing
statements below record exactly that, over `ℂ` and over `ℝ`.

Each is a wrapper over two independently proved theorems and adds no mathematics of its own:

* the operator-level Halmos classification `twoProjection_operator_classification` below, which
  carries the classification *content* with no compactness, no finite dimension and no
  separability; and
* the spectral-multiplicity translation of its generic invariant --
  `TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex` over `ℂ`, and
  `TauCeti.DavisKahan.RealSpectralRestriction.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_real`
  over `ℝ` -- which is Hahn--Hellinger, and which Mathlib has for no scalar field.

## The angle operator is `genericCosineBlock`

The statement compares the `U`-side cosine block on the generic part, not the symmetrized block
`genericHalmosCosineSq`.  On the generic part the symmetrized operator is `A ⊕ A` -- doubled
multiplicity -- and recovering `A` from `A ⊕ A` is multiplicity-halving, which this development
does not have and does not need.  Davis and Kahan state Theorem 3.1 for the angle operator on the
`U`-side, so the block used here is the paper-faithful reading; the docstring at
`SameHalmosCosineBlockInvariant` in `Geometry/Halmos/GenericReconstruction.lean` records the
2026-08-04 decision.

## On separability

Separability is carried on `H₁` only.  It is one of the paper's **standing assumptions**, taken
from the Introduction and Sections 1--2 and so governing Section 3; see
`prose/distilled_literature/DavisKahan1970_part_III.tex`, *Standing assumptions from the
transcription*.  It is needed for `→` alone -- producing a multiplicity model requires the
existence half of Hahn--Hellinger -- and the `←` direction is separability-free.  Nothing already
proved is weakened by it: `twoProjection_operator_classification`, grounded on
`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, remains stated and proved
with no separability at all.

## Note on the relation carrier

The Halmos classification layer still states its generic component with
`TauCeti.DavisKahan.BoundedOperatorsUnitaryEquivalent`, while the promoted
multiplicity theorems are stated with the canonical `TauCeti.OperatorUnitaryEquiv`.  The two are
literally the same existential; `operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent`
below is the one-line bridge, and it is private because the intended long-term outcome is that
the Halmos layer moves to the canonical relation and the bridge disappears.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970


open DavisKahan
open DavisKahan.RealSpectralRestriction

universe u v

section Bridge

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

private theorem operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent
    (A : H₁ →L[𝕜] H₁) (B : H₂ →L[𝕜] H₂) :
    OperatorUnitaryEquiv A B ↔ BoundedOperatorsUnitaryEquivalent A B :=
  Iff.rfl

end Bridge

section OperatorClassification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-! The converse direction reconstructs the pair from the cosine block through the
polar decomposition of the Halmos cross block.  The required real functional calculus on each
complete generic half is supplied by the local `RCLike` operator instances above. -/

/-- **Davis--Kahan 1970, Theorem 3.1: the operator-level classification, both
directions.**

Two ordered pairs of subspaces are unitarily equivalent *as pairs* exactly when
their four elementary Halmos summands are isometric and their angle operators
`cos²Θ` -- read on the `U`-side, as the paper reads them -- are unitarily
equivalent.  This is the constructive spine of the theorem and needs no
direct-integral presentation, no compactness, no finite dimension and no
separability.

Grounded by `:=` on
`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`, so there
is a single source of truth; the two forms differ only in splitting the stable
five-field invariant into the paper's two printed halves.  The forward direction
restricts a pair-equivalence to the `U`-half of the generic part; the converse is
bricks (1) and (2) -- brick (1) reconstructs the generic-part unitary from the
cosine block alone (`Geometry/Halmos/GenericReconstruction`), brick (2) glues it
to the four elementary summand isometries (`Geometry/Halmos/Assembly`). -/
theorem twoProjection_operator_classification :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
        BoundedOperatorsUnitaryEquivalent
          (genericCosineBlock U₁ V₁) (genericCosineBlock U₂ V₂) := by
  rw [pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant
    U₁ V₁ U₂ V₂]
  constructor
  · rintro ⟨hc, hs, ht, he, hg⟩
    exact ⟨⟨hc, hs, ht, he⟩, hg⟩
  · rintro ⟨⟨hc, hs, ht, he⟩, hg⟩
    exact ⟨hc, hs, ht, he, hg⟩

end OperatorClassification

section RealOperatorClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]
/-- **Davis--Kahan 1970, Theorem 3.1, the operator-level classification, over a
real Hilbert space.**

The `𝕜 = ℝ` instance of `twoProjection_operator_classification`.  No
compactness, no finite dimension, no separability. -/
theorem twoProjection_operator_classification_real :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
        BoundedOperatorsUnitaryEquivalent
          (genericCosineBlock U₁ V₁) (genericCosineBlock U₂ V₂) :=
  twoProjection_operator_classification U₁ V₁ U₂ V₂

end RealOperatorClassification

section ComplexClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-! Instantiating the field-generic Halmos classification at `𝕜 = ℂ` asks typeclass
inference for `ContinuousFunctionalCalculus ℝ (M →L[ℂ] M) IsSelfAdjoint` with `M` the
`U`-half of the generic part.  Mathlib supplies it through the C⋆-algebra structure on
bounded operators, but reaching it from a subspace coercion needs one more level of
pending synthesis than the default allows; the instance is found at depth `3`. -/
/-- **Davis--Kahan 1970, Theorem 3.1**, in the paper's own phrasing: the spectral multiplicity
data of the two angle operators, together with the elementary multiplicities, form a complete
invariant for ordered pairs of subspaces of a complex Hilbert space.

See the module docstring for the choice of angle operator and for the status of the separability
hypothesis. -/
theorem theorem3_1_spectralMultiplicity_classification_complex
    [TopologicalSpace.SeparableSpace H₁] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (genericCosineBlock U₁ V₁)
        (genericCosineBlock U₂ V₂) := by
  rw [twoProjection_operator_classification]
  constructor
  · rintro ⟨htriv, hgen⟩
    refine ⟨htriv, sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex _ _ ?_ ?_⟩
    · exact isSelfAdjoint_genericCosineBlock U₁ V₁
    · exact (operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent _ _).2 hgen
  · rintro ⟨htriv, hmult⟩
    exact ⟨htriv, (operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent _ _).1
      (operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex _ _ hmult)⟩

end ComplexClassification

/-! ## The source's own invariant: the angle operators themselves

Theorem 3.1 says that *the spectral multiplicity functions of `Θ₀` and `Θ₁`* are a
complete invariant.  The classifications above are stated on `genericCosineBlock`,
which is Halmos's `cos²Θ` on the generic part, together with the four elementary
multiplicities.  Those are the same data -- on `[0, π/2]` the map `θ ↦ cos²θ` is
injective -- but "the same data" is a theorem, not a spelling, and until it is
proved the source-facing statement is about a different operator from the printed
one.

This section proves it.  `genericAngleBlock` is `Θ` on the generic part, obtained
from `cos²Θ` by the functional calculus of `t ↦ arccos √t`; the classification is
then restated on it.  The transport is
`TauCeti.sameSpectralMultiplicity_cfc_iff`, whose hypotheses are discharged here
by the spectrum bound `spectrum_genericCosineBlock_subset_Icc`.

The four elementary multiplicities stay where they are: they are the multiplicities
at the two endpoints `0` and `π/2`, which the generic part does not see, and the
source counts them separately too. -/

/-- `cos²` undoes `arccos ∘ √` on `[0, 1]`. -/
private theorem cos_sq_arccos_sqrt {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (Real.cos (Real.arccos (Real.sqrt t))) ^ 2 = t := by
  obtain ⟨h0, h1⟩ := ht
  have hs0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h1
  rw [Real.cos_arccos (by linarith) hs1]
  exact Real.sq_sqrt h0

section SourceAngleInvariant

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection] [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]

open scoped Pointwise
/-- Halmos's `cos²Θ` block is a positive operator: its quadratic form is `‖P_V m‖²`. -/
theorem genericCosineBlock_nonneg : 0 ≤ genericCosineBlock U₁ V₁ := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨(isSelfAdjoint_genericCosineBlock U₁ V₁).isSymmetric, fun m => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf, re_inner_genericCosineBlock]
  positivity

/-- Halmos's `cos²Θ` block is a contraction in the order sense: `P_V` is a
projection, so `‖P_V m‖ ≤ ‖m‖`. -/
theorem genericCosineBlock_le_one : genericCosineBlock U₁ V₁ ≤ 1 := by
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨((IsSelfAdjoint.one _).sub (isSelfAdjoint_genericCosineBlock U₁ V₁)).isSymmetric,
    fun m => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf]
  simp only [sub_apply, one_apply_eq_self, inner_sub_left, map_sub]
  rw [re_inner_genericCosineBlock]
  have h1 : RCLike.re (inner ℂ m m) = ‖m‖ ^ 2 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) m
    rw [this, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [h1]
  have hle : ‖V₁.starProjection (m : H₁)‖ ≤ ‖(m : H₁)‖ :=
    V₁.norm_starProjection_apply_le _
  have hm : ‖(m : H₁)‖ = ‖m‖ := rfl
  nlinarith [norm_nonneg (V₁.starProjection (m : H₁)), norm_nonneg (m : H₁)]

/-- **The spectrum of `cos²Θ` lies in `[0, 1]`**, which is what makes
`t ↦ arccos √t` invertible on it. -/
theorem spectrum_genericCosineBlock_subset_Icc :
    spectrum ℝ (genericCosineBlock U₁ V₁) ⊆ Set.Icc 0 1 := by
  intro t ht
  refine ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _
    (isSelfAdjoint_genericCosineBlock U₁ V₁)).mp
    (genericCosineBlock_nonneg U₁ V₁) t ht, ?_⟩
  have hsub : 0 ≤ 1 - genericCosineBlock U₁ V₁ :=
    sub_nonneg.mpr (genericCosineBlock_le_one U₁ V₁)
  have hnn := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _
    ((IsSelfAdjoint.one _).sub (isSelfAdjoint_genericCosineBlock U₁ V₁))).mp hsub
  have hmem : (1 : ℝ) - t ∈ spectrum ℝ (1 - genericCosineBlock U₁ V₁) := by
    have hset := spectrum.singleton_sub_eq (R := ℝ) (genericCosineBlock U₁ V₁) 1
    have hin : (1 : ℝ) - t ∈
        ({(1 : ℝ)} : Set ℝ) - spectrum ℝ (genericCosineBlock U₁ V₁) := ⟨1, rfl, t, ht, rfl⟩
    rw [hset] at hin
    simpa using hin
  linarith [hnn _ hmem]

/-- **The source's angle operator on the generic part.**

`Θ` itself, not `cos²Θ`: the functional calculus of `t ↦ arccos √t` applied to
Halmos's cosine block.  Its spectrum lies in `[0, π/2]`, and applying `t ↦ cos²t`
recovers `genericCosineBlock`. -/
noncomputable def genericAngleBlock : genericLeftHalf U₁ V₁ →L[ℂ] genericLeftHalf U₁ V₁ :=
  cfc (fun t : ℝ => Real.arccos (Real.sqrt t)) (genericCosineBlock U₁ V₁)

/-- **Davis--Kahan 1970, Theorem 3.1, on the source's own invariant.**

The spectral multiplicity data of the *angle operators* `Θ₀`, `Θ₁` -- which is what
the paper names -- together with the four elementary multiplicities, are a complete
invariant for ordered pairs of subspaces.

This is the printed statement.  `theorem3_1_spectralMultiplicity_classification_complex`
above is the same classification carried on `cos²Θ`; the two agree because
`t ↦ arccos √t` is invertible on the spectrum of `cos²Θ`, which is
`spectrum_genericCosineBlock_subset_Icc`.

The only separability hypotheses are the source's own, on the two ambient
spaces.  Separability of the generic halves follows and is derived in the proof;
exposing it as an instance argument would have been an extra public hypothesis
that the paper does not make. -/
theorem theorem3_1_spectralMultiplicity_classification_sourceAngle_complex
    [TopologicalSpace.SeparableSpace H₁] [TopologicalSpace.SeparableSpace H₂] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (genericAngleBlock U₁ V₁)
        (genericAngleBlock U₂ V₂) := by
  -- Separability of the generic halves is a *consequence* of the source's
  -- separability assumption on the ambient spaces, not a hypothesis a caller
  -- supplies: a separable metric space is second countable, and every subspace
  -- of a second countable space is.
  let _ : SecondCountableTopology H₁ := UniformSpace.secondCountable_of_separable H₁
  let _ : SecondCountableTopology H₂ := UniformSpace.secondCountable_of_separable H₂
  have hbridge := TauCeti.sameSpectralMultiplicity_cfc_iff
    (A := genericCosineBlock U₁ V₁) (B := genericCosineBlock U₂ V₂)
    (isSelfAdjoint_genericCosineBlock U₁ V₁) (isSelfAdjoint_genericCosineBlock U₂ V₂)
    (fun t : ℝ => Real.arccos (Real.sqrt t)) (fun t : ℝ => (Real.cos t) ^ 2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun t ht => cos_sq_arccos_sqrt (spectrum_genericCosineBlock_subset_Icc U₁ V₁ ht))
    (fun t ht => cos_sq_arccos_sqrt (spectrum_genericCosineBlock_subset_Icc U₂ V₂ ht))
  rw [theorem3_1_spectralMultiplicity_classification_complex, genericAngleBlock,
    genericAngleBlock, ← hbridge]

end SourceAngleInvariant


section RealClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]
/-- **Davis--Kahan 1970, Theorem 3.1, in the paper's own phrasing, over a real Hilbert space.**

The spectral multiplicity data of the two angle operators, together with the elementary
multiplicities, form a complete invariant for ordered pairs of subspaces of a real Hilbert space.

The classification *content* was already real (`twoProjection_operator_classification_real`, with
no compactness, no finite dimension and no separability); what is added here is the translation of
its invariant into multiplicity language, which is Hahn--Hellinger over `ℝ`.  Separability of
`H₁` is carried for the `→` direction alone, exactly as in the complex statement; the `←`
direction is separability-free. -/
theorem theorem3_1_spectralMultiplicity_classification_real
    [TopologicalSpace.SeparableSpace H₁] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (genericCosineBlock U₁ V₁)
        (genericCosineBlock U₂ V₂) := by
  rw [twoProjection_operator_classification]
  constructor
  · rintro ⟨htriv, hgen⟩
    refine ⟨htriv, sameSpectralMultiplicity_of_operatorUnitaryEquiv_real _ _ ?_ ?_⟩
    · exact isSelfAdjoint_genericCosineBlock U₁ V₁
    · exact (operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent _ _).2 hgen
  · rintro ⟨htriv, hmult⟩
    exact ⟨htriv, (operatorUnitaryEquiv_iff_boundedOperatorsUnitaryEquivalent _ _).1
      (operatorUnitaryEquiv_of_sameSpectralMultiplicity_real _ _ hmult)⟩

end RealClassification

/-! ## The source's own invariant, over a real Hilbert space

The real classification above is stated on `cos²Θ`.  The invariant Davis and
Kahan name is `Θ`, and this section carries the classification onto it, exactly
as `SourceAngleInvariant` does over `ℂ`.

The complex proofs transcribe directly.  The real scalar structure, scalar tower,
self-adjoint continuous functional calculus, and star order on bounded operators are selected
locally from the canonical `ForTauCeti` constructions imported above.  They do not appear as
hypotheses in the classification statements.

`genericAngleBlockReal` remains the source-facing real spelling used by this theorem, while the
scalar-generic operator calculus is available to the reusable geometry layer. -/

section SourceAngleInvariantReal

open scoped Pointwise

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection] [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]
/-- Halmos's `cos²Θ` block is a positive operator over `ℝ` too: its quadratic
form is `‖P_V m‖²`. -/
theorem genericCosineBlock_nonneg_real : 0 ≤ genericCosineBlock U₁ V₁ := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨(isSelfAdjoint_genericCosineBlock U₁ V₁).isSymmetric, fun m => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf, re_inner_genericCosineBlock]
  positivity

/-- Halmos's `cos²Θ` block is an order contraction over `ℝ` too. -/
theorem genericCosineBlock_le_one_real : genericCosineBlock U₁ V₁ ≤ 1 := by
  rw [← sub_nonneg, ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨((IsSelfAdjoint.one _).sub (isSelfAdjoint_genericCosineBlock U₁ V₁)).isSymmetric,
    fun m => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf]
  simp only [sub_apply, one_apply_eq_self, inner_sub_left, map_sub]
  rw [re_inner_genericCosineBlock]
  have h1 : RCLike.re (inner ℝ m m) = ‖m‖ ^ 2 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℝ) m
    rw [this, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [h1]
  have hle : ‖V₁.starProjection (m : H₁)‖ ≤ ‖(m : H₁)‖ :=
    V₁.norm_starProjection_apply_le _
  have hm : ‖(m : H₁)‖ = ‖m‖ := rfl
  nlinarith [norm_nonneg (V₁.starProjection (m : H₁)), norm_nonneg (m : H₁)]

/-- **The spectrum of `cos²Θ` lies in `[0, 1]`, over a real Hilbert space.**

The complex argument, with the real `StarOrderedRing` instance installed
locally. -/
theorem spectrum_genericCosineBlock_subset_Icc_real :
    spectrum ℝ (genericCosineBlock U₁ V₁) ⊆ Set.Icc 0 1 := by
  intro t ht
  refine ⟨(StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _
    (isSelfAdjoint_genericCosineBlock U₁ V₁)).mp
    (genericCosineBlock_nonneg_real U₁ V₁) t ht, ?_⟩
  have hsub : 0 ≤ 1 - genericCosineBlock U₁ V₁ :=
    sub_nonneg.mpr (genericCosineBlock_le_one_real U₁ V₁)
  have hnn := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _
    ((IsSelfAdjoint.one _).sub (isSelfAdjoint_genericCosineBlock U₁ V₁))).mp hsub
  have hmem : (1 : ℝ) - t ∈ spectrum ℝ (1 - genericCosineBlock U₁ V₁) := by
    have hset := spectrum.singleton_sub_eq (R := ℝ) (genericCosineBlock U₁ V₁) 1
    have hin : (1 : ℝ) - t ∈
        ({(1 : ℝ)} : Set ℝ) - spectrum ℝ (genericCosineBlock U₁ V₁) := ⟨1, rfl, t, ht, rfl⟩
    rw [hset] at hin
    simpa using hin
  linarith [hnn _ hmem]

/-- **The source's angle operator on the generic part, over a real Hilbert
space.**  `Θ` itself, not `cos²Θ`. -/
noncomputable def genericAngleBlockReal :
    genericLeftHalf U₁ V₁ →L[ℝ] genericLeftHalf U₁ V₁ :=
  cfc (fun t : ℝ => Real.arccos (Real.sqrt t)) (genericCosineBlock U₁ V₁)

/-- **Davis--Kahan 1970, Theorem 3.1, on the source's own invariant, over a real
Hilbert space.**

The spectral multiplicity data of the *angle operators* `Θ₀`, `Θ₁` -- which is
what the paper names -- together with the four elementary multiplicities, are a
complete invariant for ordered pairs of subspaces.

`theorem3_1_spectralMultiplicity_classification_real` above is the same
classification carried on `cos²Θ`; the two agree because `t ↦ arccos √t` is
invertible on the spectrum of `cos²Θ`, which is
`spectrum_genericCosineBlock_subset_Icc_real`.

The only separability hypotheses are the source's own, on the two ambient
spaces. -/
theorem theorem3_1_spectralMultiplicity_classification_sourceAngle_real
    [TopologicalSpace.SeparableSpace H₁] [TopologicalSpace.SeparableSpace H₂] :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      SameSpectralMultiplicity
        (genericAngleBlockReal U₁ V₁)
        (genericAngleBlockReal U₂ V₂) := by
  have hbridge := DavisKahan.RealSpectralRestriction.sameSpectralMultiplicity_cfc_iff_real
    (A := genericCosineBlock U₁ V₁) (B := genericCosineBlock U₂ V₂)
    (isSelfAdjoint_genericCosineBlock U₁ V₁) (isSelfAdjoint_genericCosineBlock U₂ V₂)
    (fun t : ℝ => Real.arccos (Real.sqrt t)) (fun t : ℝ => (Real.cos t) ^ 2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun t ht => cos_sq_arccos_sqrt (spectrum_genericCosineBlock_subset_Icc_real U₁ V₁ ht))
    (fun t ht => cos_sq_arccos_sqrt (spectrum_genericCosineBlock_subset_Icc_real U₂ V₂ ht))
  rw [theorem3_1_spectralMultiplicity_classification_real, genericAngleBlockReal,
    genericAngleBlockReal, ← hbridge]

end SourceAngleInvariantReal

end DavisKahan1970
end TauCeti
