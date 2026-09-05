/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.InfinitaryTypes
import LeanPool.InfinitaryLogic.Lomega1omega.CountableIndex
/-!
# Realized-type isolators (issue #17 chunk 1)

The decisive lemma of the small-model → complete-sentence chain, stated LANGUAGE-GENERAL
(independent of fragments, Löwenheim–Skolem, Scott infrastructure, and relationality, per the
frozen audit): in a structure realizing only countably many complete `n`-types, every realized
type `p` is ISOLATED AMONG THE REALIZED TYPES by a single `L_{ω₁ω}`-formula

  `χ_p = ⋀_{q realized} θ_{p,q}`,

where `θ_{p,q}` is an oriented separator (true at realizers of `p`, false at realizers of `q`;
a membership-difference formula or its negation) and the countable conjunction is `ciInf` over
the countable subtype of realized types. Both the language and the structure live in arbitrary
universes: the subtype of realized types lands in `Type (max u v)`, and `ciInf` encodes an index
of any universe into the fixed `ℕ` carrier. "Language-general" means arbitrary function and
relation symbols, no relationality assumption. The characterization:

  `realize_isolatingFormula_iff : χ_p.Realize Empty.elim a ↔ infinitaryType M a = p`.
-/

namespace FirstOrder

namespace Language

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {n : ℕ}

private theorem mem_infinitaryType_iff {φ : L.BoundedFormulaω Empty n} {a : Fin n → M} :
    φ ∈ infinitaryType M a ↔ φ.Realize Empty.elim a :=
  Iff.rfl

/-- **Oriented separators exist** between distinct realized types: a formula true at every
realizer of `p` and false at every realizer of `q`. -/
private theorem exists_separator {p q : Set (L.BoundedFormulaω Empty n)} (hne : p ≠ q) :
    ∃ θ : L.BoundedFormulaω Empty n,
      (∀ a : Fin n → M, infinitaryType M a = p → θ.Realize Empty.elim a) ∧
      (∀ b : Fin n → M, infinitaryType M b = q → ¬θ.Realize Empty.elim b) := by
  have hdiff : ∃ φ : L.BoundedFormulaω Empty n, ¬(φ ∈ p ↔ φ ∈ q) := by
    by_contra hall
    refine hne (Set.ext fun φ => ?_)
    exact not_not.mp fun hne' => hall ⟨φ, hne'⟩
  obtain ⟨φ, hφ⟩ := hdiff
  by_cases hφp : φ ∈ p
  · have hφq : φ ∉ q := fun h => hφ ⟨fun _ => h, fun _ => hφp⟩
    refine ⟨φ, fun a ha => ?_, fun b hb => ?_⟩
    · exact mem_infinitaryType_iff.mp (ha ▸ hφp)
    · exact fun hr => hφq (hb ▸ mem_infinitaryType_iff.mpr hr)
  · have hφq : φ ∈ q := by
      by_contra hφq
      exact hφ ⟨fun h => absurd h hφp, fun h => absurd h hφq⟩
    refine ⟨φ.not, fun a ha => ?_, fun b hb => ?_⟩
    · rw [BoundedFormulaω.realize_not]
      exact fun hr => hφp (ha ▸ mem_infinitaryType_iff.mpr hr)
    · rw [BoundedFormulaω.realize_not, not_not]
      exact mem_infinitaryType_iff.mp (hb ▸ hφq)

open Classical in
/-- **The isolating formula** `χ_p` of a realized type, over a structure with countably many
realized `n`-types: the countable conjunction of the oriented separators against every realized
type (a tautology at `p` itself). -/
noncomputable def isolatingFormula
    (hcount : (RealizedInfinitaryTypes (L := L) M n).Countable)
    (p : Set (L.BoundedFormulaω Empty n)) :
    L.BoundedFormulaω Empty n :=
  haveI := hcount.to_subtype
  BoundedFormulaω.ciInf fun q : RealizedInfinitaryTypes (L := L) M n =>
    if h : q.1 = p then BoundedFormulaω.falsum.imp BoundedFormulaω.falsum
    else (exists_separator (M := M) fun he => h he.symm).choose

/-- **The decisive characterization**: `χ_p` holds at a tuple exactly when its complete type is
`p`. -/
theorem realize_isolatingFormula_iff
    (hcount : (RealizedInfinitaryTypes (L := L) M n).Countable)
    (p : Set (L.BoundedFormulaω Empty n)) (a : Fin n → M) :
    (isolatingFormula hcount p).Realize Empty.elim a ↔ infinitaryType M a = p := by
  have := hcount.to_subtype
  rw [isolatingFormula, BoundedFormulaω.realize_ciInf]
  constructor
  · intro h
    by_contra hne
    have hq : infinitaryType M a ∈ RealizedInfinitaryTypes (L := L) M n := ⟨a, rfl⟩
    have hcomp := h ⟨infinitaryType M a, hq⟩
    rw [dite_eq_right hne] at hcomp
    exact (exists_separator (M := M) fun he => hne he.symm).choose_spec.2 a rfl hcomp
  · intro htp q
    by_cases h : q.1 = p
    · rw [dite_eq_left h]
      show (BoundedFormulaω.falsum.imp BoundedFormulaω.falsum).Realize Empty.elim a
      rw [BoundedFormulaω.realize_imp]
      exact fun hf => hf
    · rw [dite_eq_right h]
      exact (exists_separator (M := M) fun he => h he.symm).choose_spec.1 a htp

/-! ## Universe regression

These instantiate the characterization at a nonzero universe and at universe zero. They are
compiled, so they fail if the development is ever reconstrained; the `variable` block alone
would not catch that, since a `Language.{u, v}` binder can still be silently pinned by a
downstream lemma. -/

example {L' : Language.{1, 1}} {M' : Type 2} [L'.Structure M'] {m : ℕ}
    (hcount : (RealizedInfinitaryTypes (L := L') M' m).Countable)
    (p : Set (L'.BoundedFormulaω Empty m)) (a : Fin m → M') :
    (isolatingFormula hcount p).Realize Empty.elim a ↔ infinitaryType M' a = p :=
  realize_isolatingFormula_iff hcount p a

example {L' : Language.{0, 0}} {M' : Type} [L'.Structure M'] {m : ℕ}
    (hcount : (RealizedInfinitaryTypes (L := L') M' m).Countable)
    (p : Set (L'.BoundedFormulaω Empty m)) (a : Fin m → M') :
    (isolatingFormula hcount p).Realize Empty.elim a ↔ infinitaryType M' a = p :=
  realize_isolatingFormula_iff hcount p a

end Language

end FirstOrder
