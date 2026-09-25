/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Adapted from: Spectra (https://github.com/adambornemann-glitch/Spectra),
  `Spectra/Resolvent/Spectrum.lean` at commit
  `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`, Copyright (c) 2026 Spectra
  Formalization Project, Apache 2.0.  See the `## Provenance` section below for
  the declaration-level record and the semantic differences.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Resolvent set and spectrum of an unbounded operator

For a partially defined operator `A : E →ₗ.[𝕜] E`, the **resolvent set**
`TauCeti.LinearPMap.resolventSet` is the set of `z : 𝕜` for which `z • I - A`
has a two-sided *bounded* inverse.  It is defined in
`ForTauCeti.Analysis.Normed.Operator.Resolvent.Unbounded`, which is the
canonical home of the resolvent core; this file adds the **spectrum**, its
complement, which that core does not define.

The set does not depend on the convention: `A - z` is invertible exactly when
`z • I - A` is, the two inverses differing by a sign.  Only the *resolvent
operator* is convention-sensitive, and this file does not define one.

Mathlib's `spectrum R a` is defined for an element of an algebra, via
`¬IsUnit (algebraMap R A z - a)`.  A `LinearPMap` is not an algebra element —
composition is not everywhere defined — so it needs its own definition, and the
bounded two-sided inverse is what replaces `IsUnit`.  For a *bounded* operator
the two agree, which is why the ambient convention matters: this file follows
Mathlib and takes the spectrum in `𝕜`, so that `A.spectrum` and `spectrum 𝕜 T`
can be read side by side.

## Main definitions

* `TauCeti.LinearPMap.spectrum`: the complement of the resolvent set.

## Main results

* the `mem_spectrum_iff` / `notMem_spectrum_iff` complement dictionary.

## Provenance

* **Original repository:** Spectra, `https://github.com/adambornemann-glitch/Spectra`,
  commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
* **Original module:** `Spectra/Resolvent/Spectrum.lean`.
* **Original declarations:** `Spectra.Resolvent.resolventSet`,
  `Spectra.Resolvent.spectrum`.
* **Original authors / copyright / licence:** Copyright (c) 2026 Spectra
  Formalization Project; `Authors: Adam Bornemann`; Apache 2.0 (Spectra's
  `LICENSE`).  Apache 2.0 §4(b): **the definitions below are modified** — see
  "Semantic differences".  Apache 2.0 §4(c): the notices above are retained here
  and in the file header.
* **Extraction class:** *adapted*.  The surrounding API is new and the codomain
  of `spectrum` is changed.
* **Note on scope.**  The `resolventSet` predicate that this file used to define
  (following Spectra, in the `A - z` convention) has been **removed**: the
  canonical `TauCeti.LinearPMap.resolventSet` now lives in
  `ForTauCeti.Analysis.Normed.Operator.Resolvent.Unbounded`, in the `z • I - A`
  convention that agrees with Mathlib's Banach-algebra `resolventSet`.  The two
  predicates define the same set.  What remains here, and what this provenance
  record covers, is the **spectrum** machinery, which the canonical core does not
  provide.
* **Semantic differences from the donor:**
  1. **`spectrum` returns `Set 𝕜`, not `Set ℝ`.**  Spectra defines
     `spectrum (A : H →ₗ.[ℂ] H) : Set ℝ := {lam | (lam : ℂ) ∉ resolventSet A}`,
     which silently assumes self-adjointness — for a general operator that set is
     not the spectrum at all, only its real slice.  Mathlib's convention is
     `spectrum 𝕜 a : Set 𝕜`, and this repository already uses `spectrum ℂ T` for
     bounded operators in `DavisKahan/SpectralTheory/CircleRieszIntegral.lean`,
     so the two were not comparable.  Recorded as a decision in
     the Spectra-removal plan.
  2. **Scalars are a general `NontriviallyNormedField`, not `ℂ`**, and the space
     is a normed space rather than an inner-product space.  Nothing in these
     definitions uses the inner product; requiring one was incidental to
     Spectra's setting.
  3. Spectra's two lemmas placing non-real points in the resolvent set of a
     self-adjoint operator are **not** ported here.  They rest on Spectra's
     resolvent construction and `±i`-surjectivity, which belong to a later phase
     of the removal, and no Davis--Kahan production declaration uses them.
* **Downstream users at extraction time:** 26 `DavisKahan` modules reference
  `spectrum`, 4 reference `resolventSet`.  See
  the Spectra port surface.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **spectrum** of `A`: the complement of the resolvent set.

Unlike Spectra's `Set ℝ` version this makes no self-adjointness assumption; for a
self-adjoint operator the spectrum is real, but that is a theorem rather than
part of the definition. -/
@[expose]
def spectrum (A : E →ₗ.[𝕜] E) : Set 𝕜 :=
  (resolventSet A)ᶜ

/-- Unfolds membership in the spectrum: `z` is spectral exactly when `A - z` fails to have a
bounded two-sided inverse. -/
@[simp]
theorem mem_spectrum_iff {A : E →ₗ.[𝕜] E} {z : 𝕜} :
    z ∈ spectrum A ↔ z ∉ resolventSet A :=
  (Iff.rfl)
/-- The negation of `mem_spectrum_iff`, stated so proofs need not push the negation by hand. -/
theorem notMem_spectrum_iff {A : E →ₗ.[𝕜] E} {z : 𝕜} :
    z ∉ spectrum A ↔ z ∈ resolventSet A :=
  not_not

/-- The spectrum is the complement of the resolvent set -- the definition, as a set equation. -/
theorem spectrum_eq_compl (A : E →ₗ.[𝕜] E) : spectrum A = (resolventSet A)ᶜ := (rfl)
/-- The resolvent set is the complement of the spectrum, the converse reading of
`spectrum_eq_compl`. -/
theorem resolventSet_eq_compl (A : E →ₗ.[𝕜] E) : resolventSet A = (spectrum A)ᶜ :=
  (compl_compl _).symm

/-- Spectrum and resolvent set cover the whole plane. -/
@[simp]
theorem union_spectrum_resolventSet (A : E →ₗ.[𝕜] E) :
    spectrum A ∪ resolventSet A = Set.univ :=
  Set.compl_union_self _

/-- Spectrum and resolvent set are disjoint.  With `union_spectrum_resolventSet` they partition
the plane, which is the form spectral arguments actually use. -/
@[simp]
theorem disjoint_spectrum_resolventSet (A : E →ₗ.[𝕜] E) :
    Disjoint (spectrum A) (resolventSet A) :=
  disjoint_compl_left

section RealInclusion

variable {𝕜' : Type*} [RCLike 𝕜']
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜' E']

/-- **Read a real-set spectral inclusion pointwise.**

Statements about self-adjoint operators constrain the spectrum by a *real* set —
"the spectrum lies in `[β, α]`".  With the spectrum living in `𝕜` the faithful
form of that is `spectrum A ⊆ RCLike.ofReal '' s`, which additionally records
that the spectrum is real.  This is the elimination rule: it recovers the plain
`x ∈ s` that proofs actually use, and it is where the injectivity of the
coercion is discharged once instead of at every call site. -/
theorem mem_of_subset_ofReal_image {A : E' →ₗ.[𝕜'] E'} {s : Set ℝ}
    (h : spectrum A ⊆ (RCLike.ofReal (K := 𝕜') '' s)) {x : ℝ}
    (hx : (RCLike.ofReal (K := 𝕜') x) ∈ spectrum A) : x ∈ s := by
  obtain ⟨y, hy, hxy⟩ := h hx
  rwa [RCLike.ofReal_inj.mp hxy] at hy

/-- The introduction rule paired with `mem_of_subset_ofReal_image`: a spectrum
already known to be real is contained in `s` as soon as its real points are. -/
theorem subset_ofReal_image_of_forall {A : E' →ₗ.[𝕜'] E'} {s : Set ℝ}
    (hreal : spectrum A ⊆ (RCLike.ofReal (K := 𝕜') '' Set.univ))
    (h : ∀ x : ℝ, (RCLike.ofReal (K := 𝕜') x) ∈ spectrum A → x ∈ s) :
    spectrum A ⊆ (RCLike.ofReal (K := 𝕜') '' s) := by
  intro z hz
  obtain ⟨x, -, rfl⟩ := hreal hz
  exact ⟨x, h x hz, rfl⟩

end RealInclusion

end LinearPMap
end TauCeti
