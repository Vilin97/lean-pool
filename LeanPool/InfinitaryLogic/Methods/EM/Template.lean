/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.EM.Indiscernible
/-!
# Ehrenfeucht–Mostowski templates for Lω₁ω

This file introduces the intermediate object that bridges Lω₁ω-indiscernible
sequences and Ehrenfeucht–Mostowski (EM) stretching: a *template* assigns to
each `n` and each formula `φ : L.BoundedFormulaω Empty n` the truth value of
`φ` on increasing `n`-tuples drawn from an indiscernible sequence. A second
sequence `b : J → N` *realizes* the template if its truth values on increasing
tuples agree with the template's.

## Main definitions

- `Lomega1omegaTemplate L`: a template for an Lω₁ω formula language `L`,
  i.e. an assignment `φ ↦ Prop` for every `φ : L.BoundedFormulaω Empty n`.
- `Lomega1omegaTemplate.RealizesOn T b`: a sequence `b : J → N` realizes the
  template `T` if every formula's truth value on every strictly increasing
  tuple from `J` agrees with `T φ`.
- `IsLomega1omegaIndiscernible.template`: the template induced by an
  indiscernible sequence, defined existentially (so well-defined without any
  extra assumption on the index set).

## Main results

- `IsLomega1omegaIndiscernible.template_truth_iff`: well-definedness — the
  template's value at `φ` agrees with `φ.Realize (a ∘ s)` for any strictly
  increasing tuple `s`. Uses `iff_realize` from `Indiscernible.lean`.
- `IsLomega1omegaIndiscernible.realizesTemplate`: an indiscernible sequence
  realizes its own template.
- `IsLomega1omegaIndiscernible.realizesTemplate_restrict`: restricting the
  index set along an order embedding still realizes the *same* template.
- `IsLomega1omegaIndiscernible.template_reindex`: reindexing along an order
  isomorphism produces a definitionally equal template.

This file does **not** prove anything about EM stretching itself; it only sets
up the template object and its basic invariance properties.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

/-- A template for the language `L` of Lω₁ω formulas: an assignment of a truth
value to every Lω₁ω formula in every arity, with no free variables. Intended to
record the "common truth value on increasing `n`-tuples" of an indiscernible
sequence. -/
@[ext]
structure Lomega1omegaTemplate (L : Language.{u, v}) where
  /-- The truth value assigned to a formula. -/
  truth : ∀ {n : ℕ}, L.BoundedFormulaω Empty n → Prop

namespace Lomega1omegaTemplate

variable {N : Type*} [L.Structure N] {J : Type*} [LinearOrder J]

/-- A sequence `b : J → N` realizes a template `T` if for every formula `φ` and
every strictly increasing `n`-tuple `t : Fin n → J`, the truth value of `φ` on
`b ∘ t` agrees with `T.truth φ`. -/
private def RealizesOn (T : Lomega1omegaTemplate L) (b : J → N) : Prop :=
  ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n) {t : Fin n → J} (_ : StrictMono t),
    T.truth φ ↔ φ.Realize (Empty.elim : Empty → N) (b ∘ t)

end Lomega1omegaTemplate

/-- Template associated with a bare sequence `a : I → M` — same body as
`IsLomega1omegaIndiscernible.template` but without the indiscernibility
hypothesis (the existing definition discards that hypothesis in its data
anyway). Used by the restricted-indiscernibility API (`_on` variants). -/
def templateOfSeq {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]
    (a : I → M) : Lomega1omegaTemplate L where
  truth {n} φ :=
    letI := ‹L.Structure M›
    ∃ s : Fin n → I, StrictMono s ∧ φ.Realize (Empty.elim : Empty → M) (a ∘ s)

namespace IsLomega1omegaIndiscernible

variable {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]

/-- The template induced by an indiscernible sequence: the truth value at `φ`
is the existential statement that some strictly increasing `n`-tuple in `I`
makes `φ` true. By indiscernibility (see `template_truth_iff`) this is
equivalent to "every such tuple makes `φ` true", and to "any specific witness
makes `φ` true". -/
def template {a : I → M}
    (_ : IsLomega1omegaIndiscernible (L := L) a) :
    Lomega1omegaTemplate L where
  truth {n} φ :=
    letI := ‹L.Structure M›
    ∃ s : Fin n → I, StrictMono s ∧ φ.Realize (Empty.elim : Empty → M) (a ∘ s)



/-- Well-definedness of `template`: the template's value at `φ` equals the
truth value of `φ` on any specific strictly increasing tuple. This is the
existential-vs-universal collapse provided by indiscernibility. -/
theorem template_truth_iff {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n)
    {s : Fin n → I} (hs : StrictMono s) :
    letI := ‹L.Structure M›
    h.template.truth φ ↔ φ.Realize (Empty.elim : Empty → M) (a ∘ s) := by
  refine ⟨?_, fun hφ => ⟨s, hs, hφ⟩⟩
  rintro ⟨t, ht, hφ⟩
  exact (h.iff_realize φ ht hs).mp hφ

/-- An indiscernible sequence realizes its own template. -/
private theorem realizesTemplate {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a) :
    h.template.RealizesOn a := by
  intro n φ t ht
  exact h.template_truth_iff φ ht

/-- Restricting an indiscernible sequence to a sub-order along an order
embedding `e : J ↪o I` produces a sequence that realizes the **same** template
as the original. (The template object is built from `h`, not `h.restrict e`.) -/
private theorem realizesTemplate_restrict {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type*} [LinearOrder J] (e : J ↪o I) :
    h.template.RealizesOn (a ∘ e) := by
  intro n φ t ht
  -- `e ∘ t : Fin n → I` is strictly increasing, so we can use it as a witness.
  have heT : StrictMono (e ∘ t) := e.strictMono.comp ht
  have := h.template_truth_iff φ heT
  simpa [Function.comp_assoc] using this



/-- Reindexing an indiscernible sequence by an order isomorphism produces a
template equal to the original. (Restricting along a non-surjective order
embedding generally does *not* produce an equal template — only the realisation
direction is preserved; see `realizesTemplate_restrict`.) -/
private theorem template_reindex {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type*} [LinearOrder J] (e : J ≃o I) :
    (h.reindex e).template = h.template := by
  ext n φ
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs, hφ⟩
    refine ⟨e ∘ s, e.strictMono.comp hs, ?_⟩
    simpa [Function.comp_assoc] using hφ
  · rintro ⟨t, ht, hφ⟩
    refine ⟨e.symm ∘ t, e.symm.strictMono.comp ht, ?_⟩
    have hcomp : (a ∘ e) ∘ (e.symm ∘ t) = a ∘ t := by
      funext i
      simp [Function.comp]
    simpa [hcomp] using hφ

end IsLomega1omegaIndiscernible

/-! ### Restricted-indiscernibility API for `templateOfSeq` -/

namespace IsLomega1omegaIndiscernibleOn

variable {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]

/-- Restricted `template_truth_iff`: the `templateOfSeq`'s value at a
formula `φ ∈ Γ` equals the truth value of `φ` on any strictly-increasing
tuple, provided the source sequence is restricted-indiscernible on `Γ`.

This mirrors `IsLomega1omegaIndiscernible.template_truth_iff` but uses the
weaker `IsLomega1omegaIndiscernibleOn` hypothesis and compares against
`templateOfSeq a` (the hypothesis-free template). -/
theorem templateOfSeq_truth_iff {a : I → M}
    {Γ : Set (Σ n, L.BoundedFormulaω Empty n)}
    (h : IsLomega1omegaIndiscernibleOn (L := L) a Γ)
    {n : ℕ} {φ : L.BoundedFormulaω Empty n} (hφ : ⟨n, φ⟩ ∈ Γ)
    {s : Fin n → I} (hs : StrictMono s) :
    (templateOfSeq (L := L) a).truth φ ↔
      φ.Realize (Empty.elim : Empty → M) (a ∘ s) := by
  refine ⟨?_, fun hR => ⟨s, hs, hR⟩⟩
  rintro ⟨t, ht, hR⟩
  exact (h.iff_realize φ hφ ht hs).mp hR

end IsLomega1omegaIndiscernibleOn

end FirstOrder.Language
