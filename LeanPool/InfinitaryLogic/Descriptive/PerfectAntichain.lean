/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.CantorAntichain
import Mathlib.Topology.DerivedSet
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

/-- `A` carries a **perfect antichain** for `r`: a nonempty perfect subset of `A` whose points
are pairwise `r`-inequivalent. -/
private def HasPerfectAntichainOn (r : Setoid X) (A : Set X) : Prop :=
  ∃ P, Perfect P ∧ P.Nonempty ∧ P ⊆ A ∧ ∀ x ∈ P, ∀ y ∈ P, r.r x y → x = y

/-- `A` carries a **Cantor antichain** for `r`: a continuous map from Cantor space into `A`
sending distinct points to `r`-inequivalent ones.  This is what the Cantor-scheme builders
produce directly, and it is the form a thinness proof must refute. -/
def HasCantorAntichainOn (r : Setoid X) (A : Set X) : Prop :=
  ∃ f : (ℕ → Bool) → X,
    Continuous f ∧ (∀ x, f x ∈ A) ∧ ∀ x y, x ≠ y → ¬r.r (f x) (f y)

/-- `A` is **thin** for `r`: no perfect antichain. -/
def IsThinOn (r : Setoid X) (A : Set X) : Prop :=
  ¬HasPerfectAntichainOn r A

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

/-- A Cantor antichain forces continuum-many classes.  No metric or completeness assumption:
the argument is the quotient-map injection, and only `Continuous f` mentions the topology. -/
private theorem HasCantorAntichainOn.continuum_le_quotient (h : HasCantorAntichainOn r A) :
    Cardinal.continuum ≤ #(Quotient r) := by
  -- unpack `h` directly: the inequivalence is its content, and `injective` is a separate job
  obtain ⟨f, -, -, hineq⟩ := h
  have hq : Function.Injective (fun x : ℕ → Bool => Quotient.mk r (f x)) := by
    intro x y hxy
    by_contra hne
    exact hineq x y hne (Quotient.exact hxy)
  have h1 := lift_mk_le_lift_mk_of_injective hq
  simp only [lift_uzero] at h1
  rw [show lift.{u} #(ℕ → Bool) = Cardinal.continuum from by simp] at h1
  exact h1

/-! ### Cantor antichain → perfect antichain

The converse direction to `HasPerfectAntichainOn.hasCantorAntichainOn` below, and the one that
needs no metric or completeness assumption — only that the ambient space is Hausdorff. -/







/-! ### Adapters needing the Cantor injection

`Perfect.exists_nat_bool_injection` needs a complete metric space, but **not** second
countability. -/

/-- A perfect antichain yields a Cantor antichain: `Perfect.exists_nat_bool_injection` together
with the observation that the injection's range lies in the perfect set, hence in `A`. -/
private theorem HasPerfectAntichainOn.hasCantorAntichainOn {α : Type u} [MetricSpace α]
    [CompleteSpace α] {r : Setoid α} {A : Set α}
    (h : HasPerfectAntichainOn r A) : HasCantorAntichainOn r A := by
  obtain ⟨P, hperf, hne, hsub, hanti⟩ := h
  obtain ⟨f, hrange, hcont, hinj⟩ := hperf.exists_nat_bool_injection hne
  refine ⟨f, hcont, fun x => hsub (hrange (mem_range_self x)), fun x y hxy hr => ?_⟩
  exact hxy (hinj (hanti _ (hrange (mem_range_self x)) _ (hrange (mem_range_self y)) hr))



/-! ### Perfect set cardinality

This is where second countability genuinely enters, and only for the upper bound. -/

/-- A nonempty perfect subset of a Polish space has cardinality = continuum.
Lower bound via `Perfect.exists_nat_bool_injection`; upper bound via
second-countability of Polish spaces. -/
theorem Perfect.mk_eq_continuum {α : Type u} [MetricSpace α] [CompleteSpace α]
    [SecondCountableTopology α]
    {C : Set α} (hperf : Perfect C) (hne : C.Nonempty) :
    #C = Cardinal.continuum := by
  apply le_antisymm
  · -- Upper bound: #C ≤ 𝔠
    calc #C ≤ #α := mk_set_le C
      _ ≤ Cardinal.continuum := by
        have : Nonempty α := let ⟨x, _⟩ := hne; ⟨x⟩
        obtain ⟨f, _, hf_surj⟩ := PolishSpace.exists_nat_nat_continuous_surjective α
        have h1 := lift_mk_le_lift_mk_of_surjective hf_surj
        simp only [lift_uzero] at h1
        exact h1.trans (by simp [aleph0_power_aleph0])
  · -- Lower bound: 𝔠 ≤ #C
    obtain ⟨f, hf_range, _, hf_inj⟩ := hperf.exists_nat_bool_injection hne
    let g : (ℕ → Bool) → C := fun x => ⟨f x, hf_range (mem_range_self x)⟩
    have hg_inj : Function.Injective g := fun a b hab => hf_inj (Subtype.mk.inj hab)
    have h1 := lift_mk_le_lift_mk_of_injective hg_inj
    simp only [lift_uzero] at h1
    rw [show lift.{u} #(ℕ → Bool) = Cardinal.continuum from by simp] at h1
    exact h1

/-! ### Perfect transversal → continuum classes -/

/-- If an equivalence relation has a perfect set of pairwise inequivalent elements, it has at
least continuum classes.

No second countability: the route is the Cantor antichain, i.e. only the lower bound of
`Perfect.mk_eq_continuum`, which is exactly the half that does not need it. -/
theorem continuum_classes_of_perfect_transversal {α : Type u}
    [MetricSpace α] [CompleteSpace α]
    (r : Setoid α) {C : Set α} (hperf : Perfect C) (hne : C.Nonempty)
    (hinequiv : ∀ x ∈ C, ∀ y ∈ C, r.r x y → x = y) :
    Cardinal.continuum ≤ #(Quotient r) :=
  (HasPerfectAntichainOn.hasCantorAntichainOn
    (A := C) ⟨C, hperf, hne, subset_rfl, hinequiv⟩).continuum_le_quotient



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

/-! ### Packaging the Cantor-scheme builders

Wrappers only: the existential content is `CantorAntichain.lean`'s, restated in the vocabulary
above so that consumers need not unpack it.  Each concludes at the scheme's own root; use
`HasCantorAntichainOn.mono` to enlarge to an ambient set. -/

/-- `CantorScheme.exists_antichain_map` in antichain vocabulary, concluding at the scheme root
`A []` via branch membership at level zero. -/
private theorem CantorScheme.hasCantorAntichainOn {α : Type u} [PseudoMetricSpace α]
    (r : Setoid α) {A : List Bool → Set α}
    (hlim : ∀ x : ℕ → Bool, (⋂ n, A (PiNat.res x n)).Nonempty)
    (hdiam : CantorScheme.VanishingDiam A)
    (hcross : ∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ r.r x y) :
    HasCantorAntichainOn r (A []) := by
  obtain ⟨f, hcont, -, hmem, hineq⟩ := CantorScheme.exists_antichain_map r hlim hdiam hcross
  exact ⟨f, hcont, fun a => by simpa using hmem a 0, hineq⟩


