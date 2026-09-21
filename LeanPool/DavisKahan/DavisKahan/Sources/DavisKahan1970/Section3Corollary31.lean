/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Classification
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section3Theorem31Realization
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.AngleSequenceRealization
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.CompactClassification
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Section3Corollary31 -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Corollary 3.1

Corollary 3.1 replaces the operator invariant of Theorem 3.1 by the *decreasing
eigenvalue list* of the angle operator, under a compactness hypothesis, and then
says that the list is otherwise arbitrary.  This module states both halves and
their composition, over an arbitrary `RCLike` field and then at `ℂ` and `ℝ`.

## Which compact block

Davis and Kahan assume `P tilde(Q) P = P (I - Q) P` compact -- the *defect*
(sine-square) block -- not `P Q P`.  In infinite dimension the two are
incomparable: `P (I - Q) P` compact says the principal angles accumulate only at
`0`, while `P Q P` compact says they accumulate only at `π/2`, and neither
implies the other unless `P` itself is compact.

The repair is exact rather than approximate, because `P (I - Q) P = P P_{Vᗮ} P`:
the defect block of the pair `(U, V)` *is* the cosine block of the pair
`(U, Vᗮ)`.  So the printed corollary is the cosine-block form applied to
`(U, Vᗮ)`, once one knows that complementing the second subspace preserves
pair-equivalence (`pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff`) and
merely permutes the four elementary Halmos summands
(`sameHalmosTrivialDimensions_orthogonal_right_iff`).  Both of those are stable
geometry and live under `Geometry/Halmos/`.

The angle list itself is `compactAngleEigenvalueList`, the approximation-number
sequence, which for a compact positive operator is the ordered eigenvalue list
with multiplicity.  It is `ℝ`-valued over every scalar field.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970


open TauCeti.DavisKahan

universe u v

section CosineBlock

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
/-! The real functional calculus on an operator algebra, and the two scalar-action facts
Mathlib pairs it with, are theorems at every `RCLike` field
(`ContinuousLinearMap.continuousFunctionalCalculusReal`), so they are activated here rather
than quantified over.  Until 2026-09-04 they were section `variable`s on the generic-half
algebras, and the source-facing classification theorems therefore asked their callers for
instances that instance search finds.  `local instance 100` rather than global: a global
`Algebra ℝ (E →L[𝕜] E)` makes Lean's `•` elaborator drop an author-written `((r : ℝ) : 𝕜) •`
coercion. -/
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]


/-- Davis--Kahan 1970, Corollary 3.1: when the cross-projection is compact, the
angle eigenvalue lists and elementary multiplicities classify the pair. -/
theorem corollary3_1_compact_angleList_classification
    (hcompact₁ : IsCompactOperator
      (U₁.starProjection ∘L V₁.starProjection ∘L U₁.starProjection))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L V₂.starProjection ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂) := by
  have hpos₁ : ∀ x, 0 ≤ RCLike.re
      ⟪genericCosineBlock U₁ V₁ x, x⟫_𝕜 := by
    intro x
    rw [re_inner_genericCosineBlock]
    positivity
  have hpos₂ : ∀ x, 0 ≤ RCLike.re
      ⟪genericCosineBlock U₂ V₂ x, x⟫_𝕜 := by
    intro x
    rw [re_inner_genericCosineBlock]
    positivity
  rw [twoProjection_operator_classification U₁ V₁ U₂ V₂]
  constructor
  · rintro ⟨htriv, hgen⟩
    refine ⟨htriv, ?_⟩
    funext n
    exact approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent hgen n
  · rintro ⟨htriv, hlist⟩
    refine ⟨htriv, ?_⟩
    obtain ⟨W, hW⟩ :=
      TauCeti.exists_linearIsometryEquiv_intertwining_of_approximationNumber_eq
        (isCompactOperator_genericCosineBlock U₁ V₁ hcompact₁)
        (isSelfAdjoint_genericCosineBlock U₁ V₁)
        hpos₁
        (eigenspace_genericCosineBlock_zero U₁ V₁)
        (isCompactOperator_genericCosineBlock U₂ V₂ hcompact₂)
        (isSelfAdjoint_genericCosineBlock U₂ V₂)
        hpos₂
        (eigenspace_genericCosineBlock_zero U₂ V₂)
        (fun n => congrFun hlist n)
    exact ⟨W, hW⟩
end CosineBlock

/-! ## Corollary 3.1 with the printed compactness hypothesis, over an arbitrary field

The defect-block form of Corollary 3.1 is the cosine-block form applied to `(U, Vᗮ)`, so it
is field-generic exactly as that form is.  It is separated from `section
OperatorClassification` only because the reconstruction functional calculus it needs is the
one on the generic left half of `(U, Vᗮ)`, while that section's calculus variables are
pinned to `(U, V)`; carrying both would attach four hypotheses that this statement never
uses. -/

section DefectBlockClassification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]


/-- **Davis--Kahan 1970, Corollary 3.1, with the printed hypothesis.**

The compactness assumption is on the *defect* block `P (I - Q) P`, as printed,
and the classifying list is the eigenvalue list of the corresponding
sine-square angle operator. -/
theorem corollary3_1_compact_defectBlock_angleList_classification
    (hcompact₁ : IsCompactOperator
      (U₁.starProjection ∘L
        (ContinuousLinearMap.id 𝕜 H₁ - V₁.starProjection) ∘L U₁.starProjection))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id 𝕜 H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂ᗮ) := by
  have hperp₁ : V₁ᗮ.starProjection =
      ContinuousLinearMap.id 𝕜 H₁ - V₁.starProjection := by
    show V₁ᗮ.starProjection = ContinuousLinearMap.id 𝕜 H₁ - V₁.starProjection
    rw [Submodule.starProjection_orthogonal' V₁]
    rfl
  have hperp₂ : V₂ᗮ.starProjection =
      ContinuousLinearMap.id 𝕜 H₂ - V₂.starProjection := by
    show V₂ᗮ.starProjection = ContinuousLinearMap.id 𝕜 H₂ - V₂.starProjection
    rw [Submodule.starProjection_orthogonal' V₂]
    rfl
  have h₁ : IsCompactOperator (U₁.starProjection ∘L V₁ᗮ.starProjection ∘L U₁.starProjection) := by
    rwa [hperp₁]
  have h₂ : IsCompactOperator (U₂.starProjection ∘L V₂ᗮ.starProjection ∘L U₂.starProjection) := by
    rwa [hperp₂]
  rw [← pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff U₁ V₁ U₂ V₂,
    ← sameHalmosTrivialDimensions_orthogonal_right_iff U₁ V₁ U₂ V₂]
  exact corollary3_1_compact_angleList_classification U₁ V₁ᗮ U₂ V₂ᗮ h₁ h₂

/-! ### The source's own invariant: the angles, not their sines squared

Corollary 3.1 says the complete invariants reduce to *the eigenvalues of `Θ₀` and
`Θ₁`, counted with multiplicity*.  `compactAngleEigenvalueList` is the eigenvalue
list of the sine-square block, so the classification above is stated on `sin²θ`,
not on `θ`.  The two determine each other, because `θ ↦ sin²θ` is injective on
`[0, π/2]` -- that is `angleSequence_eq_of_angleList_eq`, already proved for the
realization half -- but the classification half was never restated on the angles.

`compactAngleList` is the angle list itself, and the theorem below is the printed
statement on it.  The `sin²` form remains as the structural theorem beneath. -/

section SourceAngleList

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K₁ : Type u} [NormedAddCommGroup K₁] [InnerProductSpace 𝕜 K₁] [CompleteSpace K₁]
variable {K₂ : Type v} [NormedAddCommGroup K₂] [InnerProductSpace 𝕜 K₂] [CompleteSpace K₂]

/-- **The source's angle list**: the principal angles themselves, counted with
multiplicity, recovered from the eigenvalue list of the sine-square block by
`θ = arcsin √(sin²θ)`. -/
noncomputable def compactAngleList (A : K₁ →L[𝕜] K₁) : ℕ → ℝ :=
  fun n => Real.arcsin (Real.sqrt (compactAngleEigenvalueList A n))

/-- The angle list lands in the principal-angle range `[0, π/2]`. -/
theorem compactAngleList_mem_Icc (A : K₁ →L[𝕜] K₁) (n : ℕ) :
    compactAngleList A n ∈ Set.Icc 0 (Real.pi / 2) :=
  ⟨Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _), Real.arcsin_le_pi_div_two _⟩

/-- **The angle list determines the sine-square list, and conversely**, given that
the sine-square values lie in `[0, 1]`.

This is the exact sense in which the two spellings of Corollary 3.1's invariant are
the same data. -/
theorem compactAngleList_inj_iff {A : K₁ →L[𝕜] K₁} {B : K₂ →L[𝕜] K₂}
    (hA : ∀ n, compactAngleEigenvalueList A n ≤ 1)
    (hB : ∀ n, compactAngleEigenvalueList B n ≤ 1) :
    compactAngleEigenvalueList A = compactAngleEigenvalueList B ↔
      compactAngleList A = compactAngleList B := by
  constructor
  · intro h; unfold compactAngleList; rw [h]
  · intro h
    funext n
    have hsin : ∀ (x : ℝ), 0 ≤ x → x ≤ 1 →
        Real.sin (Real.arcsin (Real.sqrt x)) ^ 2 = x := by
      intro x h0 h1
      have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      have hs1 : Real.sqrt x ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1
      rw [Real.sin_arcsin (by linarith) hs1]
      exact Real.sq_sqrt h0
    have h0A : 0 ≤ compactAngleEigenvalueList A n :=
      ContinuousLinearMap.approximationNumber_nonneg _ _
    have h0B : 0 ≤ compactAngleEigenvalueList B n :=
      ContinuousLinearMap.approximationNumber_nonneg _ _
    calc compactAngleEigenvalueList A n
        = Real.sin (compactAngleList A n) ^ 2 := (hsin _ h0A (hA n)).symm
      _ = Real.sin (compactAngleList B n) ^ 2 := by rw [h]
      _ = compactAngleEigenvalueList B n := hsin _ h0B (hB n)

/-- **Halmos's cosine block is a contraction.**  It is the compression of the
orthogonal projection `P_V`, and both the compression and `P_V` have norm at most
one. -/
theorem norm_genericCosineBlock_le_one
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖genericCosineBlock U V‖ ≤ 1 := by
  rw [genericCosineBlock, Sylvester.compressOperator]
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  have h1 : ‖(genericLeftHalf U V).orthogonalProjectionOnto‖ ≤ 1 :=
    Submodule.orthogonalProjectionOnto_norm_le _
  have h2 : ‖V.starProjection ∘L (genericLeftHalf U V).subtypeL‖ ≤ 1 := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    have hp : ‖V.starProjection‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
      simpa using V.norm_starProjection_apply_le x
    have hs : ‖(genericLeftHalf U V).subtypeL‖ ≤ 1 := by
      exact_mod_cast (genericLeftHalf U V).norm_subtypeL_le
    nlinarith [norm_nonneg V.starProjection, norm_nonneg (genericLeftHalf U V).subtypeL]
  nlinarith [norm_nonneg ((genericLeftHalf U V).orthogonalProjectionOnto),
    norm_nonneg (V.starProjection ∘L (genericLeftHalf U V).subtypeL)]

/-- The sine-square eigenvalue list of Halmos's block never exceeds `1`, since the
block is a contraction. -/
theorem compactAngleEigenvalueList_genericCosineBlock_le_one
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (n : ℕ) :
    compactAngleEigenvalueList (genericCosineBlock U V) n ≤ 1 :=
  le_trans (ContinuousLinearMap.approximationNumber_le_norm _ n)
    (norm_genericCosineBlock_le_one U V)

/-- **Davis--Kahan 1970, Corollary 3.1, on the source's own invariant.**

The complete invariants reduce to the *eigenvalues of `Θ₀` and `Θ₁`, counted with
multiplicity* -- the angles themselves, which is what the corollary says -- together
with the elementary multiplicities.

`corollary3_1_compact_defectBlock_angleList_classification` is the same
classification carried on the `sin²θ` list; the two agree by
`compactAngleList_inj_iff`, whose hypothesis is discharged here by
`compactAngleEigenvalueList_genericCosineBlock_le_one`. -/
theorem corollary3_1_compact_defectBlock_sourceAngleList_classification
    {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    (W₁ X₁ : Submodule 𝕜 H₁) [W₁.HasOrthogonalProjection] [X₁.HasOrthogonalProjection]
    (W₂ X₂ : Submodule 𝕜 H₂) [W₂.HasOrthogonalProjection] [X₂.HasOrthogonalProjection]
    (hcompact₁ : IsCompactOperator
      (W₁.starProjection ∘L
        (ContinuousLinearMap.id 𝕜 H₁ - X₁.starProjection) ∘L W₁.starProjection))
    (hcompact₂ : IsCompactOperator
      (W₂.starProjection ∘L
        (ContinuousLinearMap.id 𝕜 H₂ - X₂.starProjection) ∘L W₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent W₁ X₁ W₂ X₂ ↔
      SameHalmosTrivialDimensions W₁ X₁ W₂ X₂ ∧
      compactAngleList (genericCosineBlock W₁ X₁ᗮ) =
        compactAngleList (genericCosineBlock W₂ X₂ᗮ) := by
  rw [corollary3_1_compact_defectBlock_angleList_classification
        W₁ X₁ W₂ X₂ hcompact₁ hcompact₂,
    compactAngleList_inj_iff
      (compactAngleEigenvalueList_genericCosineBlock_le_one W₁ X₁ᗮ)
      (compactAngleEigenvalueList_genericCosineBlock_le_one W₂ X₂ᗮ)]

end SourceAngleList

end DefectBlockClassification
section Classification

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
/-! **Davis--Kahan 1970, Theorem 3.1 in the paper's multiplicity phrasing** is
`TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_complex`, in
`DavisKahan/Sources/DavisKahan1970/Section3Classification.lean`, together with its real
analogue.  It is a wrapper over `twoProjection_operator_classification` below and the
promoted spectral-multiplicity classification
`TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex`; it lives with the other
source-facing Section 3 statements rather than here. -/

/-- **Davis--Kahan 1970, Corollary 3.1 with the printed hypothesis, over a complex Hilbert
space.**

The `𝕜 = ℂ` instance of `corollary3_1_compact_defectBlock_angleList_classification`,
grounded on it by `:=`, with no added hypothesis.

It is recorded separately because the generic form *carries* the reconstruction functional
calculus on `↥(genericLeftHalf U Vᗮ)` as a hypothesis, and typeclass inference finds that
instance for an arbitrary pair but not at every concrete one.  A consumer that instantiates
the corollary at a specific pair therefore goes through this form, where the instance was
already discharged. -/
theorem corollary3_1_compact_defectBlock_angleList_classification_complex
    (hcompact₁ : IsCompactOperator
      (U₁.starProjection ∘L
        (ContinuousLinearMap.id ℂ H₁ - V₁.starProjection) ∘L U₁.starProjection))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℂ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂ᗮ) :=
  corollary3_1_compact_defectBlock_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂


end Classification
/-! ## The realization sentence -/

section Realization

/-- **Davis--Kahan 1970, Corollary 3.1, the realization sentence.**

The classification half says that the compactness hypothesis plus the angle
eigenvalue list determines the pair.  This is the sentence that says the list is
otherwise *arbitrary*: given any

`π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0`,

the pair

`U = ` the `E`-factor of `ℓ²(ℕ, 𝕜) ⊕₂ ℓ²(ℕ, 𝕜)`,  `V = (angleSequenceDatum 𝕜 θ).targetSubspace`

realizes it.  The witness is exhibited rather than asserted to exist: `V` is the
image of `U` under the direct rotation built from the diagonal operators
`cos Θ = diag (cos θₙ)` and `sin Θ = diag (sin θₙ)`, so the whole construction is
`theorem3_1_realization` applied to a datum, not a new geometric argument.

The four conclusions are, in order:

1. **the printed compactness hypothesis holds** — what is proved compact is the
   *defect* block `P (1 - Q) P`, which is `sin² Θ` on the `E`-factor, and
   `θₙ → 0` makes its coefficients vanish.  Corollary 3.1 as printed assumes
   exactly this block, and the census records that it is incomparable with
   `P Q P` in infinite dimension, so the choice is stated rather than left
   implicit.  (`P Q P` is `cos² Θ` here, with coefficients tending to `1`; that
   this makes it non-compact is not asserted as proved.);
2. **the angle list is the prescribed one**: the classifying list of the defect
   block, in the sense of `compactAngleEigenvalueList`, is `n ↦ sin² θₙ`.  The
   map `θ ↦ sin² θ` is strictly monotone on `[0, π/2]`, so this carries exactly
   the information of the printed decreasing sequence `θ`;
3. and 4. **the angle-`0` multiplicities**, on the two sides, are the kernels of
   `sin Θ` — here equal, because the datum puts the same diagonal on both sides.

This witness realizes the two sides' angle-`0` multiplicities *equal*, and
realizes only the multiplicities the sequence `θ` itself produces.  An arbitrary
and independently prescribed pair of angle-`0` multiplicities is
`corollary3_1_realization_zeroMultiplicity`, which adds
`trivialHalmosAngleDatum` on two further spaces by `HalmosAngleDatum.prod`. -/
theorem corollary3_1_realization (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0)) :
    IsCompactOperator
        ((sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection ∘L
          (ContinuousLinearMap.id 𝕜 (AngleSequenceAmbient 𝕜) -
            (angleSequenceDatum 𝕜 θ).targetSubspace.starProjection) ∘L
          (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection) ∧
      compactAngleEigenvalueList
          ((sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection ∘L
            (ContinuousLinearMap.id 𝕜 (AngleSequenceAmbient 𝕜) -
              (angleSequenceDatum 𝕜 θ).targetSubspace.starProjection) ∘L
            (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection) =
        (fun n => Real.sin (θ n) ^ 2) ∧
      halmosCommonPart (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          (angleSequenceDatum 𝕜 θ).targetSubspace =
        Submodule.map
          (modelInl 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) :
            AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceAmbient 𝕜)
          (LinearMap.ker (angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          (angleSequenceDatum 𝕜 θ).targetSubspace =
        Submodule.map
          (modelInr 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) :
            AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceAmbient 𝕜)
          (LinearMap.ker (angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜)) :=
  ⟨isCompactOperator_angleSequenceDefectBlock hlim,
    funext fun n => approximationNumber_angleSequenceDefectBlock hθ0 hθ2 hanti n,
    (angleSequenceDatum 𝕜 θ).halmosCommonPart_eq,
    (angleSequenceDatum 𝕜 θ).halmosExteriorPart_eq⟩
/-- **Davis--Kahan 1970, Corollary 3.1, the realization sentence with prescribed
angle-`0` multiplicities.**

The paper's sentence is: the eigenvalues of `Θ₀` are an arbitrary sequence
`π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0` *together with a possible eigenvalue `0`*, and those of
`Θ₁` are the same except perhaps for the multiplicity of `0`.  Here `Z₀` and `Z₁`
are that eigenvalue's two multiplicities: arbitrary Hilbert spaces, chosen
independently of each other and of `θ`.

The pair is again exhibited rather than asserted to exist.  It is
`theorem3_1_realization` applied to
`(angleSequenceDatum 𝕜 θ).prod (trivialHalmosAngleDatum 𝕜 Z₀ Z₁)`: the sequence
on one summand and the all-`0` datum on the other.  The four conclusions are the
printed compactness hypothesis on the *defect* block `P (1 - Q) P` (not on
`P Q P` — see `corollary3_1_realization`), the prescribed angle list, and the two
angle-`0` eigenspaces, which come out as the prescribed `Z₀` and `Z₁`.

`hne` — no prescribed angle is itself `0` — is used only by the last two
conclusions, and is the paper's own reading: the angle `0` is carried by `Z₀` and
`Z₁`, separately from the sequence.  The first two conclusions hold without it. -/
theorem corollary3_1_realization_zeroMultiplicity (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (Z₀ : Type*) [NormedAddCommGroup Z₀] [InnerProductSpace 𝕜 Z₀] [CompleteSpace Z₀]
    (Z₁ : Type*) [NormedAddCommGroup Z₁] [InnerProductSpace 𝕜 Z₁] [CompleteSpace Z₁]
    (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0)) (hne : ∀ n, θ n ≠ 0) :
    IsCompactOperator
        ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
          (ContinuousLinearMap.id 𝕜
              (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
                WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
            (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) ∧
      compactAngleEigenvalueList
          ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
                (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
            (ContinuousLinearMap.id 𝕜
                (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
                  WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
              (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
            (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
                (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) =
        (fun n => Real.sin (θ n) ^ 2) ∧
      halmosCommonPart
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)))
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace =
        Submodule.map
          (modelInl 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :
            WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) →ₗ[𝕜] _)
          (Submodule.map
            (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z₀ :
              Z₀ →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z₀)) ⊤) ∧
      halmosExteriorPart
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)))
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace =
        Submodule.map
          (modelInr 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :
            WithLp 2 (AngleSequenceSpace 𝕜 × Z₁) →ₗ[𝕜] _)
          (Submodule.map
            (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z₁ :
              Z₁ →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) ⊤) := by
  refine ⟨isCompactOperator_angleSequenceZeroDefectBlock 𝕜 θ Z₀ Z₁ hlim,
    funext fun n =>
      approximationNumber_angleSequenceZeroDefectBlock 𝕜 θ Z₀ Z₁ hθ0 hθ2 hanti n,
    ?_, ?_⟩
  · refine (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).halmosCommonPart_eq.trans ?_
    rw [angleSequenceZeroDatum_sin₀, ker_blockMap_angleSinOp 𝕜 θ hθ0 hθ2 hne Z₀]
  · refine (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).halmosExteriorPart_eq.trans ?_
    rw [angleSequenceZeroDatum_sin₁, ker_blockMap_angleSinOp 𝕜 θ hθ0 hθ2 hne Z₁]
/-- **Davis--Kahan 1970, Corollary 3.1's realization clause, at the paper's own
ambient scope.**

Davis and Kahan work throughout on a separable Hilbert space, and the angle-`0`
multiplicity spaces `Z₀`, `Z₁` of the corollary are the null spaces of `Θ₀`,
`Θ₁` *inside* that space, so they are separable.  This is
`corollary3_1_realization_zeroMultiplicity` with that restriction imposed; the
unrestricted statement above is the stronger arbitrary-Hilbert realization and
stays.

The restriction is on the free data of the clause, which is where the source
places it.  Separability of the `ℓ²` model the construction builds from that
data is not itself a Lean instance in the pinned Mathlib — there is no
`SeparableSpace` instance for `lp` — and no statement here asserts it. -/
theorem corollary3_1_realization_zeroMultiplicity_sourceScope (𝕜 : Type*) [RCLike 𝕜]
    (θ : ℕ → ℝ)
    (Z₀ : Type*) [NormedAddCommGroup Z₀] [InnerProductSpace 𝕜 Z₀] [CompleteSpace Z₀]
    [TopologicalSpace.SeparableSpace Z₀]
    (Z₁ : Type*) [NormedAddCommGroup Z₁] [InnerProductSpace 𝕜 Z₁] [CompleteSpace Z₁]
    [TopologicalSpace.SeparableSpace Z₁]
    (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0)) (hne : ∀ n, θ n ≠ 0) :
    IsCompactOperator
        ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
          (ContinuousLinearMap.id 𝕜
              (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
                WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
            (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) ∧
      compactAngleEigenvalueList
          ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
                (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
            (ContinuousLinearMap.id 𝕜
                (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
                  WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
              (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
            (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
                (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) =
        (fun n => Real.sin (θ n) ^ 2) ∧
      halmosCommonPart
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)))
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace =
        Submodule.map
          (modelInl 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :
            WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) →ₗ[𝕜] _)
          (Submodule.map
            (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z₀ :
              Z₀ →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z₀)) ⊤) ∧
      halmosExteriorPart
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)))
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace =
        Submodule.map
          (modelInr 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :
            WithLp 2 (AngleSequenceSpace 𝕜 × Z₁) →ₗ[𝕜] _)
          (Submodule.map
            (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z₁ :
              Z₁ →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) ⊤) :=
  corollary3_1_realization_zeroMultiplicity 𝕜 θ Z₀ Z₁ hθ0 hθ2 hanti hlim hne


end Realization

/-! ## The recorded invariant is the printed one

Corollary 3.1's invariant is printed as the eigenvalues of the angle operators.  Every
statement here records instead the eigenvalue list `n ↦ sin² θₙ` of the defect block, because
that is what an approximation-number sequence of a compact positive block *is*.  The two are
the same information: `θ ↦ sin² θ` is injective on the printed range `[0, π/2]`, so a
recorded list determines the angle sequence it came from and nothing is lost by recording the
transformed one.

This is stated rather than explained, because "these encode the same data" is exactly the
kind of claim a hostile reviewer should be able to check in Lean. -/

section RecordedInvariant

/-- **`sin²` is injective on the printed angle range.**  Two angles in `[0, π/2]` with the
same `sin²` are equal. -/
theorem angle_eq_of_sin_sq_eq {a b : ℝ}
    (ha0 : 0 ≤ a) (ha2 : a ≤ Real.pi / 2) (hb0 : 0 ≤ b) (hb2 : b ≤ Real.pi / 2)
    (h : Real.sin a ^ 2 = Real.sin b ^ 2) : a = b := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith [Real.pi_pos])
  have hsb : 0 ≤ Real.sin b := Real.sin_nonneg_of_nonneg_of_le_pi hb0 (by linarith [Real.pi_pos])
  have hsin : Real.sin a = Real.sin b := by nlinarith [hsa, hsb, h]
  exact Real.injOn_sin ⟨by linarith, ha2⟩ ⟨by linarith, hb2⟩ hsin

/-- **The recorded eigenvalue list determines the printed angle sequence.**

If two admissible angle sequences produce the same recorded list `n ↦ sin² θₙ`, they are the
same sequence.  So recording the list is recording the angles, and the classification and
realization statements above lose nothing by being phrased through it. -/
theorem angleSequence_eq_of_angleList_eq {θ φ : ℕ → ℝ}
    (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2)
    (hφ0 : ∀ n, 0 ≤ φ n) (hφ2 : ∀ n, φ n ≤ Real.pi / 2)
    (h : (fun n => Real.sin (θ n) ^ 2) = fun n => Real.sin (φ n) ^ 2) : θ = φ :=
  funext fun n =>
    angle_eq_of_sin_sq_eq (hθ0 n) (hθ2 n) (hφ0 n) (hφ2 n) (congrFun h n)

end RecordedInvariant

/-! ## Corollary 3.1: realization composed with classification

The realization sentence computes the angle list of the *ambient* defect block
`P (1 - Q) P`, while the classification sentence's invariant is the eigenvalue list of the
*generic* cosine block of the pair `(U, Vᗮ)`.  The realized pair puts no mass on any of the
four elementary Halmos summands once no prescribed angle is `0` or `π/2`, so
`approximationNumber_genericCosineBlock_eq_ambient` identifies the two lists and the two
halves compose.

**Which compact object.**  Both halves here are on the *defect* block `P (1 - Q) P`, as
printed.  Nothing below compares `P (1 - Q) P` with `P Q P`; the census's record that the
two compactness hypotheses are incomparable in infinite dimension is untouched.

**Recorded narrowing.**  The printed sentence allows `π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0`, that is,
angles equal to `π/2` and a possible eigenvalue `0`.  The statements below assume
`0 < θₙ < π/2` strictly.  This is a *narrowing* of the source hypothesis, and it is the
exact hypothesis that makes the four elementary summands vanish, so that the generic
invariant and the ambient list coincide.  The angle-`0` multiplicities are realized
separately and unconstrained by `corollary3_1_realization_zeroMultiplicity`, and the angle
`π/2` is the elementary summand `U ⊓ Vᗮ`, so neither is lost from the paper's picture —
they are carried by `SameHalmosTrivialDimensions` rather than by the list. -/

section RealizationClassification


/-- **Davis--Kahan 1970, Corollary 3.1: the realization sentence composed with the
classification sentence.**

Given a prescribed angle sequence `π/2 > θ₁ ≥ θ₂ ≥ ⋯ → 0` with every `θₙ` strictly between
`0` and `π/2`, an arbitrary pair `(U₂, V₂)` with the printed compact defect block is
unitarily equivalent to the realized pair exactly when its four elementary Halmos
multiplicities are trivial and its angle list is `n ↦ sin² θₙ`.

This is the statement the two halves of Corollary 3.1 were built to meet.  Both hypotheses
and both conclusions are on the *defect* block `P (1 - Q) P`, as printed.  The strict
inequalities `0 < θₙ < π/2` are a recorded narrowing of the printed sequence bound; see the
section note above. -/
theorem corollary3_1_prescribedAngleSequence_classification (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0))
    {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℂ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℂ (AngleSequenceSpace ℂ) (AngleSequenceSpace ℂ))
        (angleSequenceDatum ℂ θ).targetSubspace U₂ V₂ ↔
      SameHalmosTrivialDimensions
        (sourceSubspace ℂ (AngleSequenceSpace ℂ) (AngleSequenceSpace ℂ))
        (angleSequenceDatum ℂ θ).targetSubspace U₂ V₂ ∧
      compactAngleEigenvalueList (genericCosineBlock U₂ V₂ᗮ) =
        fun n => Real.sin (θ n) ^ 2 := by
  rw [corollary3_1_compact_defectBlock_angleList_classification_complex _ _ U₂ V₂
      (isCompactOperator_angleSequenceDefectBlock hlim) hcompact₂,
    compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum ℂ θ hθ0 hθ2 hanti]
  exact and_congr_right fun _ => eq_comm
end RealizationClassification

/-! ## Corollary 3.1 over a real Hilbert space

The statements above are field-generic, so the real forms are instantiations
rather than new theorems.  They are recorded by name because the census tracks
the paper's results at the paper's scope, and because they are the machine check
that the `𝕜 = ℝ` instantiation really is inhabited: each one forces typeclass
inference to find
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`.

Davis and Kahan work on a Hilbert space over `ℝ` or `ℂ` throughout, so the real
scope is the source scope, not an extension of it. -/

section RealScalars

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Corollary 3.1, over a real Hilbert space.**

The `𝕜 = ℝ` instance of
`pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`:
with `P_U P_V P_U` compact on both sides, the four elementary Halmos
multiplicities together with the multiplicity of every angle are a complete
invariant. -/
theorem corollary3_1_compact_classification_real
    (hc₁ : IsCompactOperator (U₁.starProjection ∘L V₁.starProjection ∘L U₁.starProjection))
    (hc₂ : IsCompactOperator (U₂.starProjection ∘L V₂.starProjection ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameCompactAngleData U₁ V₁ U₂ V₂ :=
  pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData
    U₁ V₁ U₂ V₂ hc₁ hc₂

/-- **Davis--Kahan 1970, Corollary 3.1 in the paper's decreasing eigenvalue-list
phrasing, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `corollary3_1_compact_angleList_classification`.

**The angle list stays `ℝ`-valued.**  `compactAngleEigenvalueList` has codomain
`ℕ → ℝ` over every scalar field, because the eigenvalues of a compact positive
self-adjoint operator are real; passing to real scalars changes only how such an
eigenvalue is embedded back into the field, never what the list records.

**The compactness hypothesis is the generic theorem's.**  It is
`P_U P_V P_U` compact, not the printed defect block `P (I - Q) P`.  Those two are
incomparable in infinite dimension; that is a pre-existing question recorded on
this source row, and the real form inherits it unchanged.  The printed
hypothesis is carried by
`corollary3_1_compact_defectBlock_angleList_classification`, which is the same
theorem applied to `(U, Vᗮ)`. -/
theorem corollary3_1_compact_angleList_classification_real
    (hcompact₁ : IsCompactOperator
      (U₁.starProjection ∘L V₁.starProjection ∘L U₁.starProjection))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L V₂.starProjection ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂) :=
  corollary3_1_compact_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂

/-- **Davis--Kahan 1970, Corollary 3.1 with the printed hypothesis, over a real Hilbert
space.**

The `𝕜 = ℝ` instance of `corollary3_1_compact_defectBlock_angleList_classification`,
grounded on it by `:=`, with no added hypothesis: the compactness is of the *defect* block
`P (I - Q) P`, as printed, and the classifying list is the eigenvalue list of the
corresponding sine-square angle operator.

The reconstruction functional calculus that the generic form carries is synthesized here at
`ℝ`, not assumed.  As over `ℂ`, the `PQP` versus `P (I - Q) P` question recorded on this
source row is untouched: this is the printed object on both sides. -/
theorem corollary3_1_compact_defectBlock_angleList_classification_real
    (hcompact₁ : IsCompactOperator
      (U₁.starProjection ∘L
        (ContinuousLinearMap.id ℝ H₁ - V₁.starProjection) ∘L U₁.starProjection))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℝ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂ᗮ) :=
  corollary3_1_compact_defectBlock_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂

/-- **Davis--Kahan 1970, Corollary 3.1: the realization sentence composed with the
classification sentence, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `corollary3_1_prescribedAngleSequence_classification`, assembled
from the same two halves: the realization `corollary3_1_realization` is already
`RCLike`-generic, and the classification half is now
`corollary3_1_compact_defectBlock_angleList_classification_real`.

Both hypotheses and both conclusions are on the *defect* block `P (1 - Q) P`, as printed.
The strict inequalities `0 < θₙ < π/2` are the same **recorded narrowing** of the printed
sequence bound `π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0` that the complex form carries, and for the same
reason: strictness is exactly what makes the four elementary Halmos summands vanish, so
that the generic invariant and the ambient list coincide.  The angle-`0` and angle-`π/2`
data are not lost — they are the elementary summands, carried by
`SameHalmosTrivialDimensions`. -/
theorem corollary3_1_prescribedAngleSequence_classification_real (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℝ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℝ (AngleSequenceSpace ℝ) (AngleSequenceSpace ℝ))
        (angleSequenceDatum ℝ θ).targetSubspace U₂ V₂ ↔
      SameHalmosTrivialDimensions
        (sourceSubspace ℝ (AngleSequenceSpace ℝ) (AngleSequenceSpace ℝ))
        (angleSequenceDatum ℝ θ).targetSubspace U₂ V₂ ∧
      compactAngleEigenvalueList (genericCosineBlock U₂ V₂ᗮ) =
        fun n => Real.sin (θ n) ^ 2 := by
  rw [corollary3_1_compact_defectBlock_angleList_classification_real _ _ U₂ V₂
      (isCompactOperator_angleSequenceDefectBlock hlim) hcompact₂,
    compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum ℝ θ hθ0 hθ2 hanti]
  exact and_congr_right fun _ => eq_comm
end RealScalars

end DavisKahan1970
end TauCeti
