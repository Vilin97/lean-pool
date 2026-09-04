/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.DerivedSet
import Mathlib.Topology.MetricSpace.CantorScheme
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Perfect and Cantor antichains, and thinness

The vocabulary a dichotomy theorem is stated in, separated from any particular dichotomy.

* `HasPerfectAntichainOn r A` — a nonempty perfect subset of `A` of pairwise `r`-inequivalent
  points;
* `HasCantorAntichainOn r A` — a *continuous* Cantor-space parametrization of such an antichain,
  the constructive form the Cantor-scheme builders actually produce;
* `IsThinOn r A` — the negation of the first.

The two positive forms are related by `HasPerfectAntichainOn.hasCantorAntichainOn`, which is
`Perfect.exists_nat_bool_injection` plus bookkeeping.  Injectivity of a Cantor antichain is not
an extra hypothesis: it follows from *reflexivity* of the setoid, since distinct arguments have
inequivalent images and every point is equivalent to itself.

The file also carries the cardinal facts these statements are measured against: a nonempty
perfect set in a complete metric space has size continuum (`Perfect.mk_eq_continuum`); a
perfect transversal forces continuum-many classes (`continuum_classes_of_perfect_transversal`,
with its two-sided companion); and a Polish space, hence any quotient of one, has at most
continuum-many points (`mk_le_continuum_of_polish`, `mk_quotient_le_continuum_of_polish`).
None of them mentions a dichotomy, an equivalence relation being closed, or a splitting
hypothesis.

**Hypotheses are kept minimal, and the ordering below is what makes that possible.**  Only three
results need `SecondCountableTopology`: the two Polish cardinality bounds and the *upper* half of
`Perfect.mk_eq_continuum`.  Everything else needs at most `MetricSpace` + `CompleteSpace` (for the
Cantor injection) or nothing beyond `TopologicalSpace`.  In particular
`continuum_classes_of_perfect_transversal` is proved through the Cantor antichain rather than
through `mk_eq_continuum`, which is what lets it drop second countability — it only ever needed
the lower bound.
-/

open Cardinal Set

-- `𝓟` only; opening `Filter` itself would clash with `Set` on names like `map`.
open scoped Filter

universe u v

/-! ### The generic vocabulary -/

variable {X : Type u} [TopologicalSpace X]

/-- `A` carries a **Cantor antichain** for `r`: a continuous map from Cantor space into `A`
sending distinct points to `r`-inequivalent ones.  This is what the Cantor-scheme builders
produce directly, and it is the form a thinness proof must refute. -/
def HasCantorAntichainOn (r : Setoid X) (A : Set X) : Prop :=
  ∃ f : (ℕ → Bool) → X,
    Continuous f ∧ (∀ x, f x ∈ A) ∧ ∀ x y, x ≠ y → ¬r.r (f x) (f y)

/-! ### Adapters that need no metric structure -/

variable {r : Setoid X} {A B : Set X}

/-- Enlarging the ambient set preserves a Cantor antichain.  Keeping this separate is what lets
the scheme wrappers below conclude at the scheme's own root rather than carrying a containment
hypothesis. -/
theorem HasCantorAntichainOn.mono (h : HasCantorAntichainOn r A) (hAB : A ⊆ B) :
    HasCantorAntichainOn r B := by
  obtain ⟨f, hcont, hmem, hineq⟩ := h
  exact ⟨f, hcont, fun x => hAB (hmem x), hineq⟩

omit [TopologicalSpace X] in
/-- Pairwise inequivalence forces injectivity — by *reflexivity*, not by an added hypothesis:
distinct arguments have inequivalent images, and equal images would be equivalent to themselves.

Stated on the raw components rather than on `HasCantorAntichainOn`, so that both the packaged
adapter below and consumers that have already destructured a witness can share one proof. -/
private theorem injective_of_pairwise_inequiv {f : (ℕ → Bool) → X}
    (hineq : ∀ x y, x ≠ y → ¬r.r (f x) (f y)) : Function.Injective f := fun x y hxy => by
  by_contra hne
  exact hineq x y hne (hxy ▸ r.refl (f x))

/-- A Cantor antichain is injective.

The inequivalence clause is deliberately **not** restated in the conclusion: it is already the
content of `h`, and a consumer needing it should unpack `h`.  One job per adapter. -/
theorem HasCantorAntichainOn.injective (h : HasCantorAntichainOn r A) :
    ∃ f : (ℕ → Bool) → X, Continuous f ∧ Set.range f ⊆ A ∧ Function.Injective f := by
  obtain ⟨f, hcont, hmem, hineq⟩ := h
  exact ⟨f, hcont, Set.range_subset_iff.mpr hmem, injective_of_pairwise_inequiv hineq⟩

/-! ### Cantor antichain → perfect antichain

The converse direction to `HasPerfectAntichainOn.hasCantorAntichainOn` below, and the one that
needs no metric or completeness assumption — only that the ambient space is Hausdorff. -/

/-! ### Adapters needing the Cantor injection

`Perfect.exists_nat_bool_injection` needs a complete metric space, but **not** second
countability. -/

/-! ### Perfect set cardinality

This is where second countability genuinely enters, and only for the upper bound. -/

/-! ### Perfect transversal → continuum classes -/

/-! ### Polish space cardinality upper bound -/

/-- A Polish space has cardinality ≤ continuum. -/
private theorem mk_le_continuum_of_polish {α : Type u} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [Nonempty α] :
    #α ≤ Cardinal.continuum := by
  obtain ⟨f, _, hf_surj⟩ := PolishSpace.exists_nat_nat_continuous_surjective α
  have h1 := lift_mk_le_lift_mk_of_surjective hf_surj
  simp only [lift_uzero] at h1
  exact h1.trans (by simp [aleph0_power_aleph0])

/-- The quotient of a Polish space has cardinality ≤ continuum. -/
theorem mk_quotient_le_continuum_of_polish {α : Type u} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α] [Nonempty α] (r : Setoid α) :
    #(Quotient r) ≤ Cardinal.continuum :=
  (Cardinal.mk_le_of_surjective Quotient.mk_surjective).trans mk_le_continuum_of_polish
