/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.MultiplicityModel
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus

/-!
# Spectral multiplicity data as a complete unitary invariant

`TauCeti.MultiplicityDatum 𝕜` presents an operator as multiplication by the spectral coordinate
on `L²` of a finite base measure on `ℂ` together with an antitone family of measurable level
sets.  This module turns that presentation into a **relation between operators** and proves that,
over `ℂ`, the relation is exactly unitary equivalence.

* `TauCeti.SameSpectralMultiplicity` says that two operators admit multiplicity data whose base
  measures lie in the same measure class and whose level sets agree up to null sets.  It is
  stated over an arbitrary `RCLike` scalar field: the spectral parameter and the base measure
  stay complex, and only the `L²` fibres and the model operator use `𝕜`.
* `TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex` is the complex classification:
  two bounded self-adjoint operators on complex Hilbert spaces, the first separable, have the
  same multiplicity data if and only if they are unitarily equivalent.

## What the relation is, and is not

It is an existential over **presentations**, and that is what makes the classification provable
without a uniqueness theorem for the multiplicity decomposition.  It is **not** a canonical
invariant: nothing here says the datum of an operator is unique.

The cardinal-valued multiplicity function is encoded by its super-level sets: `level k` is
`{z | k < m z}`, so a point of `level k \ level (k + 1)` has multiplicity exactly `k + 1` and a
point of every `level k` has multiplicity `ℵ₀`.  The encoding is not a proxy --
`TauCeti.MultiplicityDatum.multiplicity` is the honest `ℂ → ℕ∞` multiplicity function,
`TauCeti.MultiplicityDatum.mem_level_iff` proves `level k = {z | k < multiplicity z}`, and
`TauCeti.MultiplicityDatum.measurable_multiplicity` proves it measurable.  Level sets are carried
in the structure only because that makes every hypothesis a plain `MeasurableSet`.

## Scope of the classification

Both classification theorems below stay at `𝕜 = ℂ`, for different reasons.

* The direction from multiplicity data to unitary equivalence rests on
  `TauCeti.operatorUnitaryEquiv_of_measureEquiv_complex`, whose Radon--Nikodym unitary is complex.
* The converse rests on `TauCeti.BorelCalculus.exists_hasMultiplicityModel`, complex
  Hahn--Hellinger, and that is where separability of the first space is spent: a model is built
  from a *countable* cyclic decomposition, and countability of the index is what lets the
  level-set normalisation run, since ranks count earlier indices.  A non-separable statement
  would need the uniform-multiplicity form indexed by cardinals, whose measures are not
  σ-finite.

The real analogues of both directions exist and are proved downstream, against
`TauCeti.operatorUnitaryEquiv_of_measureEquiv_real` and the real Hahn--Hellinger existence
theorem; only the *definition* above is shared, and it is already field-generic.

## Main results

* `TauCeti.SameSpectralMultiplicity`: the relation.
* `TauCeti.operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex`: same data implies unitary
  equivalence, with no separability hypothesis on either space.
* `TauCeti.sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex`: unitary equivalence implies
the
  same data, for a self-adjoint operator on a separable space.
* `TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex`: the classification.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

namespace TauCeti

universe u v

section SpectralMultiplicityData

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- **Equality of spectral multiplicity data over an arbitrary `RCLike` scalar field.**

Two operators have the same spectral multiplicity when each is unitarily equivalent to the
multiplication model of a `TauCeti.MultiplicityDatum 𝕜` -- a finite measure on `ℂ` together with
an **antitone** sequence of measurable level sets -- and the two data agree: the base measures
are in the same **measure class**, and the level sets agree up to null sets.  The spectral
parameter and base measure remain complex; only the `L²` fibres and model operator use `𝕜`.

The measure class is `TauCeti.MeasureEquiv`, a named relation proved to be an `Equivalence` at
the point of definition so that the quotient can be formed later.

This is an existential over *presentations*, and it is what
makes
`TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex` provable.  It is **not** a
canonical
invariant: nothing here says the datum of an operator is unique. -/
def SameSpectralMultiplicity (A : H₁ →L[𝕜] H₁) (B : H₂ →L[𝕜] H₂) : Prop :=
  ∃ D E : MultiplicityDatum 𝕜,
    OperatorUnitaryEquiv A D.operator ∧
    OperatorUnitaryEquiv B E.operator ∧
    MeasureEquiv D.base E.base ∧
    ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0

/-- The introduction rule for `TauCeti.SameSpectralMultiplicity`: two models, in the same measure
class, with level sets agreeing up to null sets. -/
theorem sameSpectralMultiplicity_of_models {A : H₁ →L[𝕜] H₁} {B : H₂ →L[𝕜] H₂}
    (D E : MultiplicityDatum 𝕜) (hAD : OperatorUnitaryEquiv A D.operator)
    (hBE : OperatorUnitaryEquiv B E.operator) (hbase : MeasureEquiv D.base E.base)
    (hlevel : ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0) :
    SameSpectralMultiplicity A B :=
  ⟨D, E, hAD, hBE, hbase, hlevel⟩

/-- The elimination rule, dual to `TauCeti.sameSpectralMultiplicity_of_models`.  It exists so
that consumers can destructure the relation without relying on the definition unfolding. -/
theorem SameSpectralMultiplicity.exists_models {A : H₁ →L[𝕜] H₁} {B : H₂ →L[𝕜] H₂}
    (h : SameSpectralMultiplicity A B) :
    ∃ D E : MultiplicityDatum 𝕜,
      OperatorUnitaryEquiv A D.operator ∧
      OperatorUnitaryEquiv B E.operator ∧
      MeasureEquiv D.base E.base ∧
      ∀ k, D.base (symmDiff (D.level k) (E.level k)) = 0 :=
  h

end SpectralMultiplicityData

section ComplexClassification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- **Same multiplicity data implies unitary equivalence**, with no separability hypothesis on
either space.

Chain the two models: `A ≃ D.operator ≃ E.operator ≃ B`.  The statement remains at the complex
specialization because the middle step `TauCeti.operatorUnitaryEquiv_of_measureEquiv_complex` uses
the
complex `rnDerivL2Equiv` API; the real analogue is proved separately from
`TauCeti.operatorUnitaryEquiv_of_measureEquiv_real`. -/
theorem operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (h : SameSpectralMultiplicity A B) : OperatorUnitaryEquiv A B := by
  obtain ⟨D, E, hAD, hBE, hbase, hlevel⟩ := h.exists_models
  exact hAD.trans ((operatorUnitaryEquiv_of_measureEquiv_complex hbase hlevel).trans hBE.symm)

/-- **Unitary equivalence implies the same multiplicity data.**

This is the direction that needs the existence half of Hahn--Hellinger, and therefore the
separability of `H₁`: a model for `A` is built from a *countable* cyclic decomposition, and
countability of the index is what lets the level-set normalisation run, since ranks count
earlier indices.  `H₂` needs nothing -- `B` inherits `A`'s model along the given unitary, so the
same datum serves for both. -/
theorem sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁] (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (hA : IsSelfAdjoint A) (h : OperatorUnitaryEquiv A B) : SameSpectralMultiplicity A B := by
  obtain ⟨D, hAD⟩ := BorelCalculus.exists_hasMultiplicityModel hA.isStarNormal
  refine sameSpectralMultiplicity_of_models D D hAD ?_ (MeasureEquiv.refl _) fun k => ?_
  · exact (OperatorUnitaryEquiv.symm h).trans hAD
  · simp

/-- **Spectral multiplicity data classify bounded self-adjoint operators on a separable complex
Hilbert space up to unitary equivalence.**

Separability is carried on `H₁` only, and is needed for `→` alone; see
`TauCeti.operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex` for the separability-free
converse.
Self-adjointness of `B` is not needed: it follows from that of `A` along the unitary, and in the
`←` direction it is not used at all. -/
theorem sameSpectralMultiplicity_iff_operatorUnitaryEquiv_complex [CompleteSpace H₁]
    [TopologicalSpace.SeparableSpace H₁] (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (hA : IsSelfAdjoint A) :
    SameSpectralMultiplicity A B ↔ OperatorUnitaryEquiv A B :=
  ⟨operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex A B,
    sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex A B hA⟩

end ComplexClassification

/-! ## Transporting the invariant along an invertible functional calculus

A spectral invariant stated on `g(A)` says the same thing as the invariant stated
on `A`, provided `g` is invertible on the spectrum.  This is what lets a
classification proved with one spectral representative -- say `cos²Θ` -- be read
off the representative the source names -- `Θ` itself.

The argument is short because unitary equivalence is the real content:
conjugation by a linear isometric equivalence is a star algebra equivalence, star
algebra homomorphisms commute with the functional calculus, and multiplicity data
classify self-adjoint operators up to unitary equivalence. -/

section FunctionalCalculusTransport

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- Conjugation by a linear isometric equivalence is continuous on operators.

It is `LinearIsometryEquiv.conjStarAlgEquiv`, and its continuity is the side
condition `StarAlgHomClass.map_cfc` needs. -/
theorem continuous_conjStarAlgEquiv (e : H₁ ≃ₗᵢ[ℂ] H₂) :
    Continuous (e.conjStarAlgEquiv : (H₁ →L[ℂ] H₁) → (H₂ →L[ℂ] H₂)) := by
  have hrw : (e.conjStarAlgEquiv : (H₁ →L[ℂ] H₁) → (H₂ →L[ℂ] H₂)) =
      fun x => (e.toContinuousLinearEquiv : H₁ →L[ℂ] H₂) ∘L x ∘L
        (e.symm.toContinuousLinearEquiv : H₂ →L[ℂ] H₁) := rfl
  rw [hrw]
  fun_prop

/-- **Unitary equivalence survives the continuous functional calculus**, by the
same unitary. -/
theorem OperatorUnitaryEquiv.cfc_real {A : H₁ →L[ℂ] H₁} {B : H₂ →L[ℂ] H₂} (f : ℝ → ℝ)
    (h : OperatorUnitaryEquiv A B)
    (hf : ContinuousOn f (spectrum ℝ A) := by cfc_cont_tac)
    (ha : IsSelfAdjoint A := by cfc_tac) :
    OperatorUnitaryEquiv (_root_.cfc f A) (_root_.cfc f B) := by
  obtain ⟨e, he⟩ := h.exists_intertwiner
  have hB : B = e.conjStarAlgEquiv A := by
    ext y
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    rw [he (e.symm y)]
    simp
  refine operatorUnitaryEquiv_of_intertwines e fun x => ?_
  have hmap := StarAlgHomClass.map_cfc e.conjStarAlgEquiv f A hf
    (continuous_conjStarAlgEquiv e)
  rw [hB, ← hmap]
  simp

/-- **The spectral multiplicity invariant transports along a functional calculus
that is invertible on the spectrum.**

`f` carries the invariant forwards and `g` carries it back, so the two statements
of "same spectral multiplicity" -- on `A, B` and on `f A, f B` -- are equivalent.
Both directions need the classification theorem, hence separability, which is the
source's own ambient assumption.

The hypotheses `hgf` say only that `g ∘ f` is the identity *on the spectrum*,
which is all that a functional calculus sees. -/
theorem sameSpectralMultiplicity_cfc_iff
    [TopologicalSpace.SeparableSpace H₁] [TopologicalSpace.SeparableSpace H₂]
    {A : H₁ →L[ℂ] H₁} {B : H₂ →L[ℂ] H₂}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A)) (hf' : ContinuousOn f (spectrum ℝ B))
    (hgA : ContinuousOn g (spectrum ℝ (_root_.cfc f A)))
    (_hgB : ContinuousOn g (spectrum ℝ (_root_.cfc f B)))
    (hgA' : ContinuousOn g (f '' spectrum ℝ A))
    (hgB' : ContinuousOn g (f '' spectrum ℝ B))
    (hgfA : ∀ t ∈ spectrum ℝ A, g (f t) = t)
    (hgfB : ∀ t ∈ spectrum ℝ B, g (f t) = t) :
    SameSpectralMultiplicity A B ↔
      SameSpectralMultiplicity (_root_.cfc f A) (_root_.cfc f B) := by
  have hfA : IsSelfAdjoint (_root_.cfc f A) := cfc_predicate f A
  have hfB : IsSelfAdjoint (_root_.cfc f B) := cfc_predicate f B
  have hbackA : _root_.cfc g (_root_.cfc f A) = A := by
    rw [← cfc_comp g f A hA hgA' hf]
    rw [cfc_congr (f := (g ∘ f : ℝ → ℝ)) (g := (id : ℝ → ℝ)) (fun t ht => hgfA t ht),
      cfc_id ℝ A]
  have hbackB : _root_.cfc g (_root_.cfc f B) = B := by
    rw [← cfc_comp g f B hB hgB' hf']
    rw [cfc_congr (f := (g ∘ f : ℝ → ℝ)) (g := (id : ℝ → ℝ)) (fun t ht => hgfB t ht),
      cfc_id ℝ B]
  constructor
  · intro h
    have hu := operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex A B h
    exact sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex _ _ hfA
      (hu.cfc_real f hf hA)
  · intro h
    have hu := operatorUnitaryEquiv_of_sameSpectralMultiplicity_complex _ _ h
    have := hu.cfc_real g hgA hfA
    rw [hbackA, hbackB] at this
    exact sameSpectralMultiplicity_of_operatorUnitaryEquiv_complex _ _ hA this

/-! ### The real twin

`Algebra ℝ (H →L[𝕜] H)` is not available for a bare `RCLike 𝕜`, so the two
theorems above cannot simply be stated over `𝕜`.  The real statements are the
same proofs with `ℂ` replaced by `ℝ`; they are written out rather than derived
because the only obstruction to sharing them is an instance, not an argument. -/

section RealTransport

variable {G₁ : Type u} [NormedAddCommGroup G₁] [InnerProductSpace ℝ G₁] [CompleteSpace G₁]
variable {G₂ : Type v} [NormedAddCommGroup G₂] [InnerProductSpace ℝ G₂] [CompleteSpace G₂]

/-- Conjugation by a real linear isometric equivalence is continuous on operators. -/
theorem continuous_conjStarAlgEquiv_real (e : G₁ ≃ₗᵢ[ℝ] G₂) :
    Continuous (e.conjStarAlgEquiv : (G₁ →L[ℝ] G₁) → (G₂ →L[ℝ] G₂)) := by
  have hrw : (e.conjStarAlgEquiv : (G₁ →L[ℝ] G₁) → (G₂ →L[ℝ] G₂)) =
      fun x => (e.toContinuousLinearEquiv : G₁ →L[ℝ] G₂) ∘L x ∘L
        (e.symm.toContinuousLinearEquiv : G₂ →L[ℝ] G₁) := rfl
  rw [hrw]
  fun_prop

/-- **Unitary equivalence survives the continuous functional calculus over `ℝ`.** -/
theorem OperatorUnitaryEquiv.cfc_ofReal {A : G₁ →L[ℝ] G₁} {B : G₂ →L[ℝ] G₂} (f : ℝ → ℝ)
    (h : OperatorUnitaryEquiv A B)
    (hf : ContinuousOn f (spectrum ℝ A) := by cfc_cont_tac)
    (ha : IsSelfAdjoint A := by cfc_tac) :
    OperatorUnitaryEquiv (_root_.cfc f A) (_root_.cfc f B) := by
  obtain ⟨e, he⟩ := h.exists_intertwiner
  have hB : B = e.conjStarAlgEquiv A := by
    ext y
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    rw [he (e.symm y)]
    simp
  refine operatorUnitaryEquiv_of_intertwines e fun x => ?_
  have hmap := StarAlgHomClass.map_cfc e.conjStarAlgEquiv f A hf
    (continuous_conjStarAlgEquiv_real e)
  rw [hB, ← hmap]
  simp

/-- **The functional-calculus inverse pair, over `ℝ`.**  `cfc g (cfc f A) = A`
when `g ∘ f` is the identity on the spectrum. -/
theorem cfc_cfc_eq_self_of_leftInverse_real {A : G₁ →L[ℝ] G₁} (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ A))
    (hg : ContinuousOn g (f '' spectrum ℝ A))
    (hgf : ∀ t ∈ spectrum ℝ A, g (f t) = t) :
    _root_.cfc g (_root_.cfc f A) = A := by
  rw [← cfc_comp g f A hA hg hf,
    cfc_congr (f := (g ∘ f : ℝ → ℝ)) (g := (id : ℝ → ℝ)) (fun t ht => hgf t ht),
    cfc_id ℝ A]

end RealTransport

end FunctionalCalculusTransport

end TauCeti
