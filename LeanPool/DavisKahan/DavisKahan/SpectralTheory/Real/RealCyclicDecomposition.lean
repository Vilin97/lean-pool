/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.BoundedAlmostInvariant
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.SeparableCyclic
import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpStar

/-! # Real Cyclic Decomposition -/

open TauCeti.DavisKahan.Sylvester

/-!
# The conjugation-equivariant cyclic decomposition

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/SeparableCyclic.lean` decomposes a
separable complex Hilbert space into countably many cyclic subspaces of a normal operator,
with the cyclic vectors produced by a Zorn argument that makes no choice about *where* they
sit.  This module re-runs that decomposition for the complexification of a **real** self-adjoint
operator, choosing every cyclic vector inside the real copy.

The payoff is equivariance.  A conjugation-fixed cyclic vector generates a conjugation-invariant
cyclic subspace, and on that subspace the `L²` model carries the canonical conjugation to
*pointwise complex conjugation* on `Lp ℂ 2 μ`.  That is what makes the eventual descent of the
model to a real multiplicity datum sound: the descent of an arbitrary unitary-equivalence
*witness* is genuinely obstructed (the witness is unique only up to the commutant), but the
*model* descends once it is equivariant.

## The load-bearing lemma

`conjugateOperator_borelCalculus`: for a complexified real self-adjoint operator the bounded
Borel calculus is conjugation-equivariant, `conjugation ∘ f(A) ∘ conjugation = f̄(A)`.  It is
the polarisation computation of `conjugateOperator_boundedPVM_proj` run with a general symbol
instead of a real indicator: conjugation permutes the four polarisation vectors, the diagonal
measures are conjugation invariant (`diagMeasure_conjugation_complexify`), and conjugating the
integral conjugates the symbol.

Note that self-adjointness is not decoration.  For a general normal `A` with `conjugateOperator
A = A` the spectrum is only conjugation-*symmetric*, and the transported symbol would be
`λ ↦ conj (f (conj λ))`, a genuine pullback along a nontrivial involution of the spectrum.  It
collapses to plain pointwise conjugation exactly because a self-adjoint operator has real
spectrum, which is also what makes the transported conjugation on `Lp` the honest `star`.

## Main results

* `conjugateOperator_borelCalculus`: conjugation equivariance of the bounded Borel calculus.
* `conjugation_borelCalculus_of_fixed`: its pointwise form at a conjugation-fixed vector.
* `conjugation_mem_cyclicSubspace`: **B1** -- a conjugation-fixed vector generates a
  conjugation-invariant cyclic subspace.
* `cyclicIsometry_star`: **B2** -- the cyclic isometry at a conjugation-fixed vector carries
  `star` on `Lp ℂ 2 μ` to `conjugation`.
* `exists_conjugation_fixed_ne_zero`: a nonzero conjugation-invariant subspace contains a
  nonzero conjugation-fixed vector.  This is the lemma the real exhaustion could have failed
  at, and it holds.
* `topologicalClosure_iSup_cyclicSubspace_of_maximal_fixed`: **B3** -- maximality among
  orthogonal cyclic sets *drawn from the real copy* already gives a dense span.
* `exists_countable_isHilbertSum_lp_diagMeasure_conjugation_fixed` and
  `exists_countable_isHilbertSum_lp_diagMeasure_real`: **B4** -- the real analogue of
  `TauCeti.BorelCalculus.exists_countable_isHilbertSum_lp_diagMeasure_complex`, with the equivariance.

## Hypotheses

The only hypothesis carried by the deliverable is `[TopologicalSpace.SeparableSpace E]`, which
is the complex statement's `[TopologicalSpace.SeparableSpace H]` read on the real space; it
implies the complex one by `separableSpace_realComplexification`, proved here.  No separability,
compactness, or finite-dimensionality hypothesis beyond that was introduced.

## Auxiliary `L²` infrastructure

The pointwise-star API for `Lp` is provided by `ForTauCeti.MeasureTheory.LpStar`.  In particular,
`norm_star_lp`, `star_sub_lp`, `isometry_star_lp`, and `continuous_star_lp` are reusable Tau Ceti
lemmas rather than paper-local infrastructure.
-/

open scoped InnerProductSpace ComplexConjugate

open MeasureTheory

namespace TauCeti
namespace DavisKahan
namespace RealSpectralRestriction


open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Eℂ" => RealComplexification E

variable {T : E →L[ℝ] E}

section Equivariance

/-- **The bounded Borel calculus of a complexified real self-adjoint operator is
conjugation equivariant.**

Conjugating the calculus of a symbol gives the calculus of the conjugate symbol.  The proof is
the polarisation computation of `conjugateOperator_boundedPVM_proj` with a general symbol:
conjugation permutes the four polarisation vectors `ξ ± ψ`, `ξ ± i ψ` among themselves, the
diagonal measures are conjugation invariant, and `integral_conj` moves the outer conjugation
onto the symbol. -/
theorem conjugateOperator_borelCalculus (hT : IsSelfAdjoint T)
    {f : _root_.spectrum ℂ (complexify T) → ℂ}
    (hf : TauCeti.BorelCalculus.IsBddMeasurable f) :
    conjugateOperator (TauCeti.BorelCalculus.borelCalculus
        (isSelfAdjoint_complexify_bounded hT).isStarNormal hf)
      = TauCeti.BorelCalculus.borelCalculus
          (isSelfAdjoint_complexify_bounded hT).isStarNormal hf.conj := by
  refine ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => ?_
  rw [conjugateOperator_apply, inner_conjugation_right, ← inner_conj_symm,
    TauCeti.BorelCalculus.inner_borelCalculus, TauCeti.BorelCalculus.inner_borelCalculus]
  have h1 : conjugation ξ + conjugation ψ = conjugation (ξ + ψ) := (map_add _ _ _).symm
  have h2 : conjugation ξ + Complex.I • conjugation ψ
      = conjugation (ξ - Complex.I • ψ) := by
    rw [map_sub, conjugation_complex_smul, Complex.conj_I]
    module
  have h3 : conjugation ξ - conjugation ψ = conjugation (ξ - ψ) := (map_sub _ _ _).symm
  have h4 : conjugation ξ - Complex.I • conjugation ψ
      = conjugation (ξ + Complex.I • ψ) := by
    rw [map_add, conjugation_complex_smul, Complex.conj_I]
    module
  simp only [TauCeti.BorelCalculus.pair, h1, h2, h3, h4,
    diagMeasure_conjugation_complexify hT]
  simp only [map_mul, map_sub, map_add, map_one, map_div₀, Complex.conj_I,
    Complex.conj_ofNat, integral_conj]
  ring

/-- **Pointwise conjugation equivariance at a conjugation-fixed vector.**

If `conjugation ξ = ξ` then conjugating `f(A) ξ` gives `f̄(A) ξ` -- the vector stays put and only
the symbol is conjugated.  This is the form the cyclic-subspace argument consumes. -/
theorem conjugation_borelCalculus_of_fixed (hT : IsSelfAdjoint T)
    {f : _root_.spectrum ℂ (complexify T) → ℂ}
    (hf : TauCeti.BorelCalculus.IsBddMeasurable f) {ξ : Eℂ} (hξ : conjugation ξ = ξ) :
    conjugation (TauCeti.BorelCalculus.borelCalculus
        (isSelfAdjoint_complexify_bounded hT).isStarNormal hf ξ)
      = TauCeti.BorelCalculus.borelCalculus
          (isSelfAdjoint_complexify_bounded hT).isStarNormal hf.conj ξ := by
  have h := congrArg (fun A : Eℂ →L[ℂ] Eℂ => A ξ) (conjugateOperator_borelCalculus hT hf)
  simpa [conjugateOperator_apply, hξ] using h

end Equivariance

section ConjInvariantSubmodule

/-- **The conjugation preimage of a complex submodule, as a complex submodule.**

Conjugation is only conjugate-linear, so `Submodule.comap` does not apply; but the preimage is
still a `ℂ`-submodule, because a scalar comes back out starred and the starred scalar is again
a scalar. -/
def conjComap (K : Submodule ℂ Eℂ) : Submodule ℂ Eℂ where
  carrier := conjugation ⁻¹' (K : Set Eℂ)
  add_mem' {z w} hz hw := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add] at *
    exact K.add_mem hz hw
  zero_mem' := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_zero]
    exact K.zero_mem
  smul_mem' c z hz := by
    simp only [Set.mem_preimage, SetLike.mem_coe, conjugation_complex_smul] at *
    exact K.smul_mem _ hz

omit [CompleteSpace E] in
/-- Membership in the conjugation preimage is membership of the conjugate. -/
@[simp] theorem mem_conjComap {K : Submodule ℂ Eℂ} {z : Eℂ} :
    z ∈ conjComap K ↔ conjugation z ∈ K := Iff.rfl

omit [CompleteSpace E] in
/-- The conjugation preimage of a closed submodule is closed: conjugation is continuous. -/
theorem isClosed_conjComap {K : Submodule ℂ Eℂ} (hK : IsClosed (K : Set Eℂ)) :
    IsClosed ((conjComap K : Submodule ℂ Eℂ) : Set Eℂ) :=
  hK.preimage (conjugation (E := E)).continuous

end ConjInvariantSubmodule

section CyclicSubspace

/-- **B1: a conjugation-fixed vector generates a conjugation-invariant cyclic subspace.**

By minimality of the cyclic subspace it suffices to check the calculus orbit of `ξ`, where
`conjugation_borelCalculus_of_fixed` replaces conjugation of the value by conjugation of the
symbol -- and the conjugate symbol's calculus value is in the same cyclic subspace. -/
theorem conjugation_mem_cyclicSubspace (hT : IsSelfAdjoint T) {ξ : Eℂ}
    (hξ : conjugation ξ = ξ) {z : Eℂ}
    (hz : z ∈ TauCeti.BorelCalculus.cyclicSubspace
      (isSelfAdjoint_complexify_bounded hT).isStarNormal ξ) :
    conjugation z ∈ TauCeti.BorelCalculus.cyclicSubspace
      (isSelfAdjoint_complexify_bounded hT).isStarNormal ξ := by
  have hle : TauCeti.BorelCalculus.cyclicSubspace
      (isSelfAdjoint_complexify_bounded hT).isStarNormal ξ
        ≤ conjComap (TauCeti.BorelCalculus.cyclicSubspace
          (isSelfAdjoint_complexify_bounded hT).isStarNormal ξ) := by
    refine TauCeti.BorelCalculus.cyclicSubspace_le _
      (isClosed_conjComap (TauCeti.BorelCalculus.isClosed_cyclicSubspace _ ξ)) fun f hf => ?_
    rw [mem_conjComap, conjugation_borelCalculus_of_fixed hT hf hξ]
    exact TauCeti.BorelCalculus.borelCalculus_apply_mem_cyclicSubspace _ hf.conj ξ
  exact hle hz

end CyclicSubspace

section CyclicIsometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H}

/-- The pointwise conjugate of a bounded measurable symbol, as a bounded measurable symbol. -/
def conjSymbol (f : TauCeti.BorelCalculus.bddSymbols A) :
    TauCeti.BorelCalculus.bddSymbols A :=
  ⟨fun x => (starRingEnd ℂ) ((f : _root_.spectrum ℂ A → ℂ) x),
    TauCeti.BorelCalculus.mem_bddSymbols.mpr
      (TauCeti.BorelCalculus.isBddMeasurable_coe f).conj⟩

/-- **Conjugating an `L²` class conjugates the symbol.**  The symbol-to-`L²` map intertwines
`conjSymbol` with `star`. -/
theorem star_symbolToLp (hA : IsStarNormal A) (ξ : H)
    (f : TauCeti.BorelCalculus.bddSymbols A) :
    star (TauCeti.BorelCalculus.symbolToLp hA ξ f)
      = TauCeti.BorelCalculus.symbolToLp hA ξ (conjSymbol f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_star_lp (TauCeti.BorelCalculus.symbolToLp hA ξ f),
    TauCeti.BorelCalculus.coeFn_symbolToLp hA ξ f,
    TauCeti.BorelCalculus.coeFn_symbolToLp hA ξ (conjSymbol f)] with x h1 h2 h3
  rw [h1, h2, h3]
  rfl

end CyclicIsometry

section Equivariance2

/-- **B2: the cyclic isometry at a conjugation-fixed vector is equivariant.**

The `L²` model of the cyclic subspace generated by a conjugation-fixed vector carries pointwise
complex conjugation on `Lp ℂ 2 μ_ξ` to the canonical conjugation on the complexification.

Both sides are continuous in the `L²` variable (`continuous_star_lp`), so it suffices to check
them on the dense set of bounded measurable symbols, where the statement is exactly
`conjugation_borelCalculus_of_fixed`. -/
theorem cyclicIsometry_star (hT : IsSelfAdjoint T) {ξ : Eℂ} (hξ : conjugation ξ = ξ)
    (F : Lp ℂ 2 (TauCeti.BorelCalculus.diagMeasure
      (isSelfAdjoint_complexify_bounded hT).isStarNormal ξ)) :
    TauCeti.BorelCalculus.cyclicIsometry
        (isSelfAdjoint_complexify_bounded hT).isStarNormal ξ (star F)
      = conjugation (TauCeti.BorelCalculus.cyclicIsometry
          (isSelfAdjoint_complexify_bounded hT).isStarNormal ξ F) := by
  refine (TauCeti.BorelCalculus.denseRange_symbolToLp
    (isSelfAdjoint_complexify_bounded hT).isStarNormal ξ).induction_on F
      (isClosed_eq ((TauCeti.BorelCalculus.cyclicIsometry _ ξ).continuous.comp
        continuous_star_lp)
        ((conjugation (E := E)).continuous.comp
          (TauCeti.BorelCalculus.cyclicIsometry _ ξ).continuous)) fun f => ?_
  rw [star_symbolToLp, TauCeti.BorelCalculus.cyclicIsometry_symbolToLp,
    TauCeti.BorelCalculus.cyclicIsometry_symbolToLp,
    conjugation_borelCalculus_of_fixed hT (TauCeti.BorelCalculus.isBddMeasurable_coe f) hξ]
  rfl

end Equivariance2

section RealCopy

omit [CompleteSpace E] in
/-- **The conjugation-fixed vectors are exactly the real copy.**  A vector fixed by the
canonical conjugation is the image under `ofReal` of its own real part. -/
theorem ofReal_re_of_conjugation_fixed {z : Eℂ} (hz : conjugation z = z) :
    ofReal (re z) = z := by
  refine RealComplexification.ext rfl ?_
  have him : -im z = im z := congrArg im hz
  have h2 : (2 : ℝ) • im z = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← him]
    abel
  have h0 : im z = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  rw [im_ofReal, h0]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The complexification of a separable real space is separable: it is `E × E` with the `L²`
product norm, and `WithLp.toLp` is a continuous surjection from the product. -/
theorem separableSpace_realComplexification [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (RealComplexification E) :=
  DenseRange.separableSpace
    (f := (WithLp.toLp 2 : E × E → WithLp 2 (E × E)))
    (Function.Surjective.denseRange fun z => ⟨WithLp.ofLp z, WithLp.toLp_ofLp 2 z⟩)
    (WithLp.prod_continuous_toLp 2 E E)

end RealCopy

section FixedSubspace

omit [CompleteSpace E] in
/-- **A nonzero vector of a conjugation-invariant subspace yields a nonzero conjugation-fixed
vector of the same subspace.**

This is the lemma that makes the real cyclic exhaustion possible, and it is where the
"choose the cyclic vector in the real copy" step could have failed.  It does not: `η` and
`conjugation η` cannot both cancel, because `(η + conjugation η)` and
`i (η - conjugation η)` together recover `2 η`, and both are conjugation fixed. -/
theorem exists_conjugation_fixed_ne_zero {K : Submodule ℂ Eℂ}
    (hK : ∀ z ∈ K, conjugation z ∈ K) {η : Eℂ} (hη : η ∈ K) (hη0 : η ≠ 0) :
    ∃ ζ ∈ K, ζ ≠ 0 ∧ conjugation ζ = ζ := by
  have hcη : conjugation η ∈ K := hK η hη
  by_cases h : η + conjugation η = 0
  · refine ⟨Complex.I • (η - conjugation η), K.smul_mem _ (K.sub_mem hη hcη), ?_, ?_⟩
    · have hcn : conjugation η = -η := eq_neg_of_add_eq_zero_right h
      have hsub : η - conjugation η = (2 : ℂ) • η := by rw [hcn]; module
      rw [hsub, smul_smul]
      exact smul_ne_zero (mul_ne_zero Complex.I_ne_zero two_ne_zero) hη0
    · rw [conjugation_complex_smul, map_sub, conjugation_involutive, Complex.conj_I]
      module
  · refine ⟨η + conjugation η, K.add_mem hη hcη, h, ?_⟩
    rw [map_add, conjugation_involutive]
    abel

end FixedSubspace

section RealZorn

/-- **The condition the real Zorn argument runs on**: an orthogonal cyclic set all of whose
members are fixed by the canonical conjugation, hence lie in the real copy. -/
structure IsFixedOrthogonalCyclicSet (hT : IsSelfAdjoint T) (S : Set Eℂ) : Prop where
  /-- The underlying set is an orthogonal cyclic set for the complexified operator. -/
  toIsOrthogonalCyclicSet : TauCeti.BorelCalculus.IsOrthogonalCyclicSet
    (isSelfAdjoint_complexify_bounded hT).isStarNormal S
  /-- Every member is conjugation fixed. -/
  conjugation_fixed : ∀ x ∈ S, conjugation x = x

/-- The union of a chain of fixed orthogonal cyclic sets is one: both conditions involve at
most two members at a time. -/
theorem isFixedOrthogonalCyclicSet_sUnion (hT : IsSelfAdjoint T) {c : Set (Set Eℂ)}
    (hc : ∀ s ∈ c, IsFixedOrthogonalCyclicSet hT s) (hchain : IsChain (· ⊆ ·) c) :
    IsFixedOrthogonalCyclicSet hT (⋃₀ c) where
  toIsOrthogonalCyclicSet := TauCeti.BorelCalculus.isOrthogonalCyclicSet_sUnion _
    (fun s hs => (hc s hs).toIsOrthogonalCyclicSet) hchain
  conjugation_fixed := by
    rintro x ⟨s, hs, hxs⟩
    exact (hc s hs).conjugation_fixed x hxs

/-- **Zorn's lemma on fixed orthogonal cyclic sets.**  A maximal one exists. -/
theorem exists_maximal_isFixedOrthogonalCyclicSet (hT : IsSelfAdjoint T) :
    ∃ S : Set Eℂ, Maximal (IsFixedOrthogonalCyclicSet hT) S := by
  obtain ⟨m, hm⟩ := zorn_subset {S : Set Eℂ | IsFixedOrthogonalCyclicSet hT S}
    fun c hc hchain =>
      ⟨⋃₀ c, isFixedOrthogonalCyclicSet_sUnion hT (fun s hs => hc hs) hchain,
        fun s hs => Set.subset_sUnion_of_mem hs⟩
  exact ⟨m, hm⟩

/-- **B3: maximality among *real* cyclic sets already gives a dense span.**

This is the real analogue of `topologicalClosure_iSup_cyclicSubspace_of_maximal`, and the one
place where restricting the cyclic vectors to the real copy could have cost something.  It does
not: the supremum of the cyclic subspaces of conjugation-fixed vectors is conjugation invariant
(`conjugation_mem_cyclicSubspace`), hence so is its orthogonal complement, and a nonzero
conjugation-invariant subspace contains a nonzero conjugation-fixed vector
(`exists_conjugation_fixed_ne_zero`).  So a nontrivial complement would supply a new *real*
cyclic vector, contradicting maximality. -/
theorem topologicalClosure_iSup_cyclicSubspace_of_maximal_fixed (hT : IsSelfAdjoint T)
    {S : Set Eℂ} (hS : Maximal (IsFixedOrthogonalCyclicSet hT) S) :
    (⊤ : Submodule ℂ Eℂ) ≤ (⨆ ξ : S, TauCeti.BorelCalculus.cyclicSubspace
      (isSelfAdjoint_complexify_bounded hT).isStarNormal (ξ : Eℂ)).topologicalClosure := by
  set hA := (isSelfAdjoint_complexify_bounded hT).isStarNormal with hAdef
  set K := ⨆ ξ : S, TauCeti.BorelCalculus.cyclicSubspace hA (ξ : Eℂ) with hKdef
  have hle : ∀ v ∈ S, TauCeti.BorelCalculus.cyclicSubspace hA v ≤ K := fun v hv =>
    le_iSup (fun ξ : S => TauCeti.BorelCalculus.cyclicSubspace hA (ξ : Eℂ)) ⟨v, hv⟩
  have hinv : TauCeti.BorelCalculus.IsCalculusInvariant hA K :=
    TauCeti.BorelCalculus.isCalculusInvariant_iSup fun ξ =>
      TauCeti.BorelCalculus.isCalculusInvariant_cyclicSubspace hA (ξ : Eℂ)
  -- `K` is conjugation invariant, summand by summand.
  have hKconj : ∀ z ∈ K, conjugation z ∈ K := by
    have hsub : K ≤ conjComap K := by
      refine iSup_le fun ξ => ?_
      intro z hz
      rw [mem_conjComap]
      exact hle (ξ : Eℂ) ξ.2
        (conjugation_mem_cyclicSubspace hT (hS.prop.conjugation_fixed _ ξ.2) hz)
    exact fun z hz => hsub hz
  -- hence so is `Kᗮ`.
  have hperp : ∀ z ∈ Kᗮ, conjugation z ∈ Kᗮ := by
    intro η hη
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [inner_conjugation_right, ← inner_conj_symm,
      (Submodule.mem_orthogonal K η).mp hη _ (hKconj u hu), map_zero]
  have hbot : Kᗮ = ⊥ := by
    by_contra hne
    obtain ⟨η, hηmem, hη0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨ζ, hζmem, hζ0, hζfix⟩ := exists_conjugation_fixed_ne_zero hperp hηmem hη0
    have hcyc : TauCeti.BorelCalculus.cyclicSubspace hA ζ ≤ Kᗮ :=
      TauCeti.BorelCalculus.cyclicSubspace_le_orthogonal hinv hζmem
    have hins : IsFixedOrthogonalCyclicSet hT (insert ζ S) := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rintro (h | h)
        · exact hζ0 h.symm
        · exact hS.prop.toIsOrthogonalCyclicSet.zero_notMem h
      · rintro x (rfl | hx) y (rfl | hy) hxy
        · exact absurd rfl hxy
        · exact Submodule.isOrtho_iff_le.mpr
            (hcyc.trans (Submodule.orthogonal_le (hle y hy)))
        · exact (Submodule.isOrtho_iff_le.mpr
            (hcyc.trans (Submodule.orthogonal_le (hle x hx)))).symm
        · exact hS.prop.toIsOrthogonalCyclicSet.isOrtho x hx y hy hxy
      · rintro x (rfl | hx)
        · exact hζfix
        · exact hS.prop.conjugation_fixed x hx
    have hζS : ζ ∈ S := hS.mem_of_prop_insert hins
    exact hζ0 (inner_self_eq_zero.mp
      ((Submodule.mem_orthogonal _ ζ).mp hζmem ζ
        (hle ζ hζS (TauCeti.BorelCalculus.mem_cyclicSubspace_self hA ζ))))
  exact (Submodule.topologicalClosure_eq_top_iff.mpr hbot).ge

end RealZorn

section Assembly

/-- **B4, conjugation-fixed form: the `ℕ`-indexed cyclic decomposition with every cyclic
vector fixed by the canonical conjugation.**

This is the real analogue of
`TauCeti.BorelCalculus.exists_countable_isHilbertSum_lp_diagMeasure_complex`.  The enumeration and the
zero-padding are the same as there -- the padding vector `0` is conjugation fixed, so the
`ℕ`-indexed family stays inside the real copy -- and the totality input is
`topologicalClosure_iSup_cyclicSubspace_of_maximal_fixed` instead of its unconstrained
counterpart.

The only hypothesis is `[TopologicalSpace.SeparableSpace E]`, which is the complex statement's
`[TopologicalSpace.SeparableSpace H]` read on the real space: it *implies* separability of the
complexification (`separableSpace_realComplexification`).  Nothing else was added. -/
theorem exists_countable_isHilbertSum_lp_diagMeasure_conjugation_fixed
    [TopologicalSpace.SeparableSpace E] (hT : IsSelfAdjoint T) :
    ∃ ξ : ℕ → Eℂ, (∀ n, conjugation (ξ n) = ξ n) ∧
      IsHilbertSum ℂ (fun n => Lp ℂ 2 (TauCeti.BorelCalculus.diagMeasure
          (isSelfAdjoint_complexify_bounded hT).isStarNormal (ξ n)))
        (fun n => TauCeti.BorelCalculus.cyclicIsometry
          (isSelfAdjoint_complexify_bounded hT).isStarNormal (ξ n)) := by
  classical
  have : TopologicalSpace.SeparableSpace (RealComplexification E) :=
    separableSpace_realComplexification
  set hA := (isSelfAdjoint_complexify_bounded hT).isStarNormal with hAdef
  obtain ⟨S, hSmax⟩ := exists_maximal_isFixedOrthogonalCyclicSet hT
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_injOn.mp
    (TauCeti.BorelCalculus.countable_of_isOrthogonalCyclicSet
      hSmax.prop.toIsOrthogonalCyclicSet)
  set e : ℕ → Eℂ := fun n => if h : ∃ x, x ∈ S ∧ f x = n then h.choose else 0 with hedef
  have hspec : ∀ n, ∀ h : ∃ x, x ∈ S ∧ f x = n, e n ∈ S ∧ f (e n) = n := by
    intro n h
    simp only [hedef, dite_eq_left h]
    exact h.choose_spec
  have hzero : ∀ n, ¬(∃ x, x ∈ S ∧ f x = n) → e n = 0 := by
    intro n h
    simp only [hedef, dite_eq_right h]
  have hemem : ∀ n, e n = 0 ∨ (e n ∈ S ∧ f (e n) = n) := by
    intro n
    by_cases h : ∃ x, x ∈ S ∧ f x = n
    · exact Or.inr (hspec n h)
    · exact Or.inl (hzero n h)
  have heS : ∀ x ∈ S, e (f x) = x := fun x hx =>
    hf (hspec (f x) ⟨x, hx, rfl⟩).1 hx (hspec (f x) ⟨x, hx, rfl⟩).2
  have hfix : ∀ n, conjugation (e n) = e n := by
    intro n
    rcases hemem n with h0 | ⟨hmS, _⟩
    · rw [h0, map_zero]
    · exact hSmax.prop.conjugation_fixed _ hmS
  have horth : ∀ m n : ℕ, m ≠ n →
      ∀ (v : Lp ℂ 2 (TauCeti.BorelCalculus.diagMeasure hA (e m)))
        (w : Lp ℂ 2 (TauCeti.BorelCalculus.diagMeasure hA (e n))),
      ⟪TauCeti.BorelCalculus.cyclicIsometry hA (e m) v,
        TauCeti.BorelCalculus.cyclicIsometry hA (e n) w⟫_ℂ = 0 := by
    intro m n hmn v w
    rcases hemem m with h0 | ⟨hmS, hmf⟩
    · have hbot : TauCeti.BorelCalculus.cyclicSubspace hA (e m) = ⊥ := by
        rw [h0]; exact TauCeti.BorelCalculus.cyclicSubspace_zero hA
      have hzerov : TauCeti.BorelCalculus.cyclicIsometry hA (e m) v = 0 := by
        have hmem := TauCeti.BorelCalculus.cyclicIsometry_mem_cyclicSubspace hA (e m) v
        rw [hbot] at hmem
        simpa using hmem
      rw [hzerov, inner_zero_left]
    · rcases hemem n with h0 | ⟨hnS, hnf⟩
      · have hbot : TauCeti.BorelCalculus.cyclicSubspace hA (e n) = ⊥ := by
          rw [h0]; exact TauCeti.BorelCalculus.cyclicSubspace_zero hA
        have hzerow : TauCeti.BorelCalculus.cyclicIsometry hA (e n) w = 0 := by
          have hmem := TauCeti.BorelCalculus.cyclicIsometry_mem_cyclicSubspace hA (e n) w
          rw [hbot] at hmem
          simpa using hmem
        rw [hzerow, inner_zero_right]
      · have hne : e m ≠ e n := by
          intro hcon
          exact hmn (by rw [← hmf, ← hnf, hcon])
        exact (hSmax.prop.toIsOrthogonalCyclicSet.isOrtho _ hmS _ hnS hne).inner_eq
          (TauCeti.BorelCalculus.cyclicIsometry_mem_cyclicSubspace hA (e m) v)
          (TauCeti.BorelCalculus.cyclicIsometry_mem_cyclicSubspace hA (e n) w)
  refine ⟨e, hfix, IsHilbertSum.mk (𝕜 := ℂ) (fun m n hmn v w => horth m n hmn v w) ?_⟩
  have hle : (⨆ x : S, TauCeti.BorelCalculus.cyclicSubspace hA (x : Eℂ))
      ≤ ⨆ n, TauCeti.BorelCalculus.cyclicSubspace hA (e n) := by
    refine iSup_le fun x => ?_
    have := le_iSup (fun n => TauCeti.BorelCalculus.cyclicSubspace hA (e n)) (f (x : Eℂ))
    rwa [heS (x : Eℂ) x.2] at this
  have htotal := topologicalClosure_iSup_cyclicSubspace_of_maximal_fixed hT hSmax
  refine htotal.trans ((Submodule.topologicalClosure_mono hle).trans ?_)
  simp only [TauCeti.BorelCalculus.range_cyclicIsometry]
  exact le_rfl

/-- **The mission deliverable: the conjugation-equivariant cyclic decomposition.**

Every separable real Hilbert space carrying a bounded self-adjoint operator `T` decomposes its
complexification as a countable Hilbert sum of `L²` models of scalar spectral measures whose
cyclic vectors all lie in the **real copy** `Set.range ofReal`, and each cyclic isometry
intertwines pointwise complex conjugation on `Lp ℂ 2 μ` with the canonical conjugation on the
complexification.

The Hilbert-sum component is the real analogue of
`TauCeti.BorelCalculus.exists_countable_isHilbertSum_lp_diagMeasure_complex`; the equivariance component
is what makes the *model* -- as opposed to an arbitrary unitary-equivalence witness -- descend.

The cyclic vectors are exhibited as elements of the complexification together with the
statement that each lies in the range of `ofReal`, rather than as a family `ℕ → E` fed through
`ofReal`: the measures `diagMeasure ... (ξ n)` occur in the *types* of the summands, so
replacing `ξ n` by `ofReal (re (ξ n))` inside the statement is a dependent rewrite that Lean
does not discharge cheaply.  The two forms carry the same information. -/
theorem exists_countable_isHilbertSum_lp_diagMeasure_real
    [TopologicalSpace.SeparableSpace E] (hT : IsSelfAdjoint T) :
    ∃ ξ : ℕ → Eℂ,
      (∀ n, ξ n ∈ Set.range (ofReal : E → Eℂ)) ∧
      (∀ n, conjugation (ξ n) = ξ n) ∧
      IsHilbertSum ℂ (fun n => Lp ℂ 2 (TauCeti.BorelCalculus.diagMeasure
          (isSelfAdjoint_complexify_bounded hT).isStarNormal (ξ n)))
        (fun n => TauCeti.BorelCalculus.cyclicIsometry
          (isSelfAdjoint_complexify_bounded hT).isStarNormal (ξ n)) ∧
      ∀ (n : ℕ) (F : Lp ℂ 2 (TauCeti.BorelCalculus.diagMeasure
          (isSelfAdjoint_complexify_bounded hT).isStarNormal (ξ n))),
        TauCeti.BorelCalculus.cyclicIsometry
            (isSelfAdjoint_complexify_bounded hT).isStarNormal (ξ n) (star F)
          = conjugation (TauCeti.BorelCalculus.cyclicIsometry
              (isSelfAdjoint_complexify_bounded hT).isStarNormal (ξ n) F) := by
  obtain ⟨ξ, hfix, hsum⟩ :=
    exists_countable_isHilbertSum_lp_diagMeasure_conjugation_fixed (E := E) (T := T) hT
  exact ⟨ξ, fun n => ⟨re (ξ n), ofReal_re_of_conjugation_fixed (hfix n)⟩, hfix, hsum,
    fun n F => cyclicIsometry_star hT (hfix n) F⟩

end Assembly

end

end RealSpectralRestriction
end DavisKahan
end TauCeti
