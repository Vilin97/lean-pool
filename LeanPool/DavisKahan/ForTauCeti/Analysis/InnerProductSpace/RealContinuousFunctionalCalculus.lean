/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Complexification.Spectrum
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Continuous functional calculus over `ℝ` for a real Hilbert space

`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint` registers

```text
ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint
```

for **every** real Hilbert space `E`, at unrestricted dimension.

## Why this is not in Mathlib

Mathlib's only unital real calculus for operators,
`IsSelfAdjoint.instContinuousFunctionalCalculus`, descends by spectrum restriction from a
calculus over `ℂ` for star-normal elements, and `CStarAlgebra (E →L[𝕜] E)` is registered only
at `𝕜 = ℂ`.  `Matrix n n 𝕜` escapes this through a separate spectral-theorem construction in
`Analysis/Matrix/HermitianFunctionalCalculus.lean`, so a real matrix calculus exists while the
operator one does not.  Mathlib records the gap in prose: `Analysis/InnerProductSpace/`
`StarOrder.lean` proves `ContinuousLinearMap.instStarOrderedRingRCLike` for a general `RCLike`
field and declines to register it, because it takes exactly this calculus as an argument and
"for the moment we only have this for `𝕜 := ℂ`".  Registering the instance below supplies the
missing input to `ContinuousLinearMap.instStarOrderedRingRCLike`.  The modulus and polar
factorization consume it downstream rather than being dependencies of this foundational file.

This real instance is the concrete-field base case used by the `RCLike`-generic continuous
functional calculus in `ScalarTransportFunctionalCalculus.lean`.

## The construction

Complexification, as a proof technique rather than as architecture: the missing ingredient is
genuinely complex-only, so the smallest necessary portion is transported and the actual
mathematical object -- `cfcHom` itself -- is descended, not an existential witness.

For `a : E →L[ℝ] E` self-adjoint:

1. `complexify a` is a self-adjoint operator on the complexification, and the complexified
   algebra already carries a real calculus (`realContinuousFunctionalCalculus`);
2. `spectrum_complexify` identifies the two spectra, so the symbol algebras agree
   (`spectrumComplexifyMap`) and `complexifiedCfcHom` is a real `⋆`-algebra map
   `C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] (Eℂ →L[ℂ] Eℂ)`;
3. its whole image is fixed by the canonical conjugation
   (`conjugateOperator_complexifiedCfcHom`, from `conjugateOperator_cfcHom`), and a
   conjugation-fixed operator **is** a complexification (`complexify_realPartOperator`), so the
   map descends to `realCfcHom : C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] (E →L[ℝ] E)`;
4. every field of the calculus is then read off through `complexify`, which is an injective
   isometric unital `⋆`-algebra map (`complexifyStarAlgHom`, `isometry_complexify`).

## Main results

* `TauCeti.RealComplexification.realCfcHom`: the descended calculus;
* `ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`: the real-field instance;
* `TauCeti.RealComplexification.complexify_cfc`: naturality of the calculus under complexification.

## A duplication this file does not resolve

`complexify_mul`, `complexify_one` and `complexify_star` are each declared in two or three
`DavisKahan` modules, in different namespaces, and several consumers use the bare names under an
`open` of `TauCeti.RealComplexification`.  Adding canonical copies here would make those uses
ambiguous, so this file routes through `complexifyStarAlgHom` and `map_mul` / `map_one` /
`map_star` instead.  Consolidating the three copies into `Complexification/Basic.lean` is a
separate, mechanical piece of work.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Transporting the symbol algebra -/

/-- The identity, read as a map from the spectrum of `complexify a` to the spectrum of `a`.
It is a bijection, by `spectrum_complexify`. -/
def spectrumComplexifyMap (a : E →L[ℝ] E) :
    C(spectrum ℝ (complexify a), spectrum ℝ a) :=
  ⟨Set.inclusion (spectrum_complexify a).subset, continuous_inclusion _⟩

omit [CompleteSpace E] in
/-- `spectrumComplexifyMap` does not move points: it is the identity on underlying reals. -/
@[simp]
theorem spectrumComplexifyMap_coe (a : E →L[ℝ] E) (x : spectrum ℝ (complexify a)) :
    ((spectrumComplexifyMap a x : spectrum ℝ a) : ℝ) = (x : ℝ) := rfl

omit [CompleteSpace E] in
/-- `spectrumComplexifyMap` is surjective, the two spectra being equal.  This is what makes
precomposition with it injective on symbols, and what turns `Set.range (f ∘ _)` into
`Set.range f`. -/
theorem spectrumComplexifyMap_surjective (a : E →L[ℝ] E) :
    Function.Surjective (spectrumComplexifyMap a) := fun y =>
  ⟨⟨(y : ℝ), by rw [spectrum_complexify]; exact y.2⟩, Subtype.ext rfl⟩

/-! ## The calculus of `a`, computed in the complexification -/

/-- The real continuous functional calculus of `a`, taken in the complexified operator
algebra: a symbol on `spectrum ℝ a` is read as a symbol on `spectrum ℝ (complexify a)` and fed
to the calculus that `Complexification/FunctionalCalculus.lean` already registers there. -/
def complexifiedCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] (RealComplexification E →L[ℂ] RealComplexification E) :=
  (cfcHom ((complexify_isSelfAdjoint_iff a).2 ha)).comp
    (ContinuousMap.compStarAlgHom' ℝ ℝ (spectrumComplexifyMap a))

/-- `complexifiedCfcHom` unfolded: reindex the symbol, then apply the complex-algebra
calculus. -/
theorem complexifiedCfcHom_apply {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    complexifiedCfcHom ha f =
      cfcHom ((complexify_isSelfAdjoint_iff a).2 ha) (f.comp (spectrumComplexifyMap a)) := rfl

/-- `complexifiedCfcHom` is continuous: `cfcHom` is, and reindexing symbols is. -/
theorem continuous_complexifiedCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    Continuous (complexifiedCfcHom ha) :=
  ((cfcHom_continuous ((complexify_isSelfAdjoint_iff a).2 ha)).comp
    (ContinuousMap.continuous_precomp (spectrumComplexifyMap a))).congr fun f =>
      (complexifiedCfcHom_apply ha f).symm

/-- `complexifiedCfcHom` is injective: `cfcHom` is, and reindexing along a surjection is. -/
theorem complexifiedCfcHom_injective {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    Function.Injective (complexifiedCfcHom ha) := by
  intro f g hfg
  rw [complexifiedCfcHom_apply, complexifiedCfcHom_apply] at hfg
  have h := cfcHom_injective ((complexify_isSelfAdjoint_iff a).2 ha) hfg
  refine ContinuousMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := spectrumComplexifyMap_surjective a x
  exact congrFun (congrArg DFunLike.coe h) y

/-- `complexifiedCfcHom` sends the restricted identity symbol to `complexify a`. -/
theorem complexifiedCfcHom_id {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    complexifiedCfcHom ha ((ContinuousMap.id ℝ).restrict (spectrum ℝ a)) = complexify a := by
  have h : ((ContinuousMap.id ℝ).restrict (spectrum ℝ a)).comp (spectrumComplexifyMap a) =
      (ContinuousMap.id ℝ).restrict (spectrum ℝ (complexify a)) := by
    exact ContinuousMap.ext fun x => rfl
  rw [complexifiedCfcHom_apply, h, cfcHom_id]

/-- The spectral mapping theorem for `complexifiedCfcHom`. -/
theorem complexifiedCfcHom_map_spectrum {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    spectrum ℝ (complexifiedCfcHom ha f) = Set.range f := by
  rw [complexifiedCfcHom_apply, cfcHom_map_spectrum]
  exact (spectrumComplexifyMap_surjective a).range_comp f

/-- `complexifiedCfcHom` produces self-adjoint operators, real symbols being self-adjoint. -/
theorem isSelfAdjoint_complexifiedCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) : IsSelfAdjoint (complexifiedCfcHom ha f) := by
  rw [complexifiedCfcHom_apply]
  exact cfcHom_predicate ((complexify_isSelfAdjoint_iff a).2 ha) _

/-- **The calculus of `complexify a` stays in the fixed-point subalgebra of the canonical
conjugation.**  This is the descent step: by `complexify_realPartOperator` a conjugation-fixed
operator *is* the complexification of a bounded real operator. -/
theorem conjugateOperator_complexifiedCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    conjugateOperator (complexifiedCfcHom ha f) = complexifiedCfcHom ha f := by
  rw [complexifiedCfcHom_apply]
  exact conjugateOperator_cfcHom _ ((complexify_isSelfAdjoint_iff a).2 ha)
    (conjugateOperator_complexify a) _

/-! ## The descended calculus -/

/-- The real continuous functional calculus of a self-adjoint `a : E →L[ℝ] E`, as a function on
symbols: `complexifiedCfcHom` followed by the descent of a conjugation-fixed operator to the
real copy.  `complexifyStarAlgHom_realCfcFun` says the descent is exact. -/
def realCfcFun {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) (f : C(spectrum ℝ a, ℝ)) : E →L[ℝ] E :=
  realPartOperator (complexifiedCfcHom ha f)

/-- **The defining property of the descended calculus.**  Every algebraic law below is this
identity plus injectivity of `complexify`. -/
theorem complexifyStarAlgHom_realCfcFun {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    complexifyStarAlgHom (realCfcFun ha f) = complexifiedCfcHom ha f := by
  rw [complexifyStarAlgHom_apply]
  exact complexify_realPartOperator (conjugateOperator_complexifiedCfcHom ha f)

/-- `complexifyStarAlgHom` is injective; this is `complexify_injective` under the bundling. -/
theorem complexifyStarAlgHom_injective :
    Function.Injective (complexifyStarAlgHom (E := E)) := complexify_injective

/-- **The real continuous functional calculus of a self-adjoint bounded operator on a real
Hilbert space**, bundled as a `⋆`-algebra homomorphism over `ℝ`. -/
def realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    C(spectrum ℝ a, ℝ) →⋆ₐ[ℝ] (E →L[ℝ] E) where
  toFun := realCfcFun ha
  map_one' := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_one, map_one]
  map_mul' f g := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_mul complexifyStarAlgHom,
      complexifyStarAlgHom_realCfcFun, complexifyStarAlgHom_realCfcFun, map_mul]
  map_zero' := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_zero, map_zero]
  map_add' f g := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_add complexifyStarAlgHom,
      complexifyStarAlgHom_realCfcFun, complexifyStarAlgHom_realCfcFun, map_add]
  commutes' r := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, AlgHomClass.commutes, AlgHomClass.commutes]
  map_star' f := complexifyStarAlgHom_injective <| by
    rw [complexifyStarAlgHom_realCfcFun, map_star complexifyStarAlgHom,
      complexifyStarAlgHom_realCfcFun, map_star]

/-- `realCfcHom` acts by `realCfcFun`. -/
@[simp]
theorem realCfcHom_apply {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) (f : C(spectrum ℝ a, ℝ)) :
    realCfcHom ha f = realCfcFun ha f := rfl

/-- **The descent identity for the bundled calculus**: complexifying `realCfcHom` recovers the
calculus computed in the complexification.  Every property of `realCfcHom` below is transported
through this equation. -/
theorem complexify_realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) :
    complexify (realCfcHom ha f) = complexifiedCfcHom ha f :=
  complexifyStarAlgHom_realCfcFun ha f

/-- `realCfcHom` is continuous.  Continuity transports *backwards* along `complexify` because
it is an isometric embedding, not merely norm-preserving; this is what `isometry_complexify`
is for. -/
theorem continuous_realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    Continuous (realCfcHom ha) := by
  refine (isometry_complexify (E := E) (F := E)).isEmbedding.isInducing.continuous_iff.2 ?_
  simpa only [Function.comp_def, complexify_realCfcHom] using continuous_complexifiedCfcHom ha

/-- `realCfcHom` is injective. -/
theorem realCfcHom_injective {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    Function.Injective (realCfcHom ha) := fun f g hfg =>
  complexifiedCfcHom_injective ha <| by
    rw [← complexify_realCfcHom, ← complexify_realCfcHom, hfg]

/-- `realCfcHom` sends the restricted identity symbol to `a`; with continuity and
multiplicativity this is what pins the calculus down uniquely. -/
theorem realCfcHom_id {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    realCfcHom ha ((ContinuousMap.id ℝ).restrict (spectrum ℝ a)) = a :=
  complexify_injective <| by
    rw [complexify_realCfcHom, complexifiedCfcHom_id]

/-- **The spectral mapping theorem over `ℝ`**: the spectrum of `f` applied to `a` is the range
of `f` on the spectrum of `a`. -/
theorem realCfcHom_map_spectrum {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) : spectrum ℝ (realCfcHom ha f) = Set.range f := by
  rw [← spectrum_complexify, complexify_realCfcHom, complexifiedCfcHom_map_spectrum]

/-- `realCfcHom` produces self-adjoint operators, so the calculus is closed on its own
predicate. -/
theorem isSelfAdjoint_realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (f : C(spectrum ℝ a, ℝ)) : IsSelfAdjoint (realCfcHom ha f) :=
  (complexify_isSelfAdjoint_iff _).1 <| by
    rw [complexify_realCfcHom]
    exact isSelfAdjoint_complexifiedCfcHom ha f

/-! ## Nontriviality -/

omit [CompleteSpace E] in
/-- A nontrivial bounded operator algebra forces a nontrivial space. -/
theorem nontrivial_of_nontrivial_operator (h : Nontrivial (E →L[ℝ] E)) : Nontrivial E := by
  by_contra hE
  rw [not_nontrivial_iff_subsingleton] at hE
  exact (not_subsingleton (E →L[ℝ] E))
    ⟨fun S T => ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩

end

end RealComplexification
end TauCeti

/-! ## The instance -/

namespace ContinuousLinearMap

open TauCeti.RealComplexification
open scoped TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The continuous functional calculus over `ℝ` for self-adjoint bounded operators on a real
Hilbert space, in unrestricted dimension.** -/
instance instContinuousFunctionalCalculusRealIsSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint where
  predicate_zero := IsSelfAdjoint.zero _
  compactSpace_spectrum a := isCompact_iff_compactSpace.mp (spectrum.isCompact a)
  spectrum_nonempty a ha := by
    have hE : Nontrivial E := nontrivial_of_nontrivial_operator inferInstance
    have hc : Nontrivial (TauCeti.RealComplexification E) :=
      (ofReal (E := E)).injective.nontrivial
    have : Nontrivial
        (TauCeti.RealComplexification E →L[ℂ] TauCeti.RealComplexification E) :=
      ⟨1, 0, one_ne_zero⟩
    rw [← spectrum_complexify a]
    exact ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (complexify a)
      ((complexify_isSelfAdjoint_iff a).2 ha)
  exists_cfc_of_predicate a ha :=
    ⟨realCfcHom ha, continuous_realCfcHom ha, realCfcHom_injective ha, realCfcHom_id ha,
      realCfcHom_map_spectrum ha, isSelfAdjoint_realCfcHom ha⟩


end ContinuousLinearMap

/-! ## Naturality of the calculus along the complexification

The instance above makes `cfc f a` meaningful for a real self-adjoint `a`, but leaves it
opaque: `cfcHom` is a `choose` against `exists_cfc_of_predicate`, so nothing yet connects it
to `realCfcHom`, which is the map the instance actually supplied.  Uniqueness closes that gap
(`ContinuousMap.UniqueHom ℝ` holds for every T2 real topological `⋆`-algebra), and with it the
calculus commutes with `complexify`.

This is the interface a consumer wants.  A statement proved over `ℂ` for `complexify a`
transfers to `a` itself, and — in the other direction — a real object defined by descent from
the complexification is recognized as a genuine real functional calculus. -/

namespace TauCeti
namespace RealComplexification

open scoped TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `cfcHom`, for a self-adjoint operator on a real Hilbert space, **is** the descended
calculus `realCfcHom`.  Both are continuous `⋆`-algebra maps sending the identity symbol to
`a`, and `ContinuousMap.UniqueHom ℝ` says there is only one such. -/
theorem cfcHom_eq_realCfcHom {a : E →L[ℝ] E} (ha : IsSelfAdjoint a) :
    cfcHom ha = realCfcHom ha :=
  cfcHom_eq_of_continuous_of_map_id ha _ (continuous_realCfcHom ha) (realCfcHom_id ha)

/-- **The continuous functional calculus commutes with complexification.**

The complexification is an injective isometric unital `⋆`-algebra map that preserves spectra,
so this is the naturality one expects; the content is that the *real* calculus on `E →L[ℝ] E`
that this file registers is the one descended from the complex side, which is
`cfcHom_eq_realCfcHom`.

The hypotheses are the ones `cfc` itself requires: without them both sides are `0` by
`cfc_apply_of_not_predicate`, so the statement is not vacuous but is uninteresting. -/
theorem complexify_cfc (f : ℝ → ℝ) {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (hf : ContinuousOn f (spectrum ℝ a)) :
    complexify (cfc f a) = cfc f (complexify a) := by
  have ha' : IsSelfAdjoint (complexify a) := (complexify_isSelfAdjoint_iff a).2 ha
  have hf' : ContinuousOn f (spectrum ℝ (complexify a)) := by
    rw [spectrum_complexify]; exact hf
  rw [cfc_apply f a ha hf, cfc_apply f (complexify a) ha' hf', cfcHom_eq_realCfcHom,
    complexify_realCfcHom, complexifiedCfcHom_apply]
  rfl

/-- The reverse reading of `complexify_cfc`: a real functional calculus may be *computed* in the
complexification.  This is the form the angle operators of the Davis--Kahan development use,
where the real object is defined by descent and has to be recognized as `cfc`. -/
theorem realPartOperator_cfc_complexify (f : ℝ → ℝ) {a : E →L[ℝ] E} (ha : IsSelfAdjoint a)
    (hf : ContinuousOn f (spectrum ℝ a)) :
    realPartOperator (cfc f (complexify a)) = cfc f a := by
  rw [← complexify_cfc f ha hf]
  exact ContinuousLinearMap.ext fun x => by simp

/-! ### Positivity

`complexify` preserves and reflects the order, because it preserves self-adjointness and the
real spectrum, and in a `C⋆`-algebra nonnegativity is exactly a self-adjoint element with
nonnegative spectrum.  Modulus naturality is downstream in
`ForTauCeti.Analysis.InnerProductSpace.ModulusTransport`. -/

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- Complexification preserves and reflects nonnegativity. -/
@[simp] theorem complexify_nonneg_iff {A : E →L[ℝ] E} : 0 ≤ complexify A ↔ 0 ≤ A := by
  constructor
  · intro h
    have hsa : IsSelfAdjoint A := (complexify_isSelfAdjoint_iff A).1 (.of_nonneg h)
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa]
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (.of_nonneg h),
      spectrum_complexify] at h
    exact h
  · intro h
    have hsa : IsSelfAdjoint (complexify A) := (complexify_isSelfAdjoint_iff A).2 (.of_nonneg h)
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa, spectrum_complexify]
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (.of_nonneg h)] at h
    exact h


end RealComplexification
end TauCeti
