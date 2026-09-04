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
def HasPerfectAntichainOn (r : Setoid X) (A : Set X) : Prop :=
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

/-- **A Cantor antichain for a coarser relation is one for a finer relation.**

`hrs` says `r` **refines** `s`: being `r`-related implies being `s`-related, so `r` cuts the space
into the finer classes.  Separating points for the coarser `s` is therefore the *stronger*
requirement, and it survives the passage to `r`.

The direction is easy to reverse mentally, so concretely: with `r := isoSetoid φ` and
`s := bfEquivSetoid φ α`, isomorphic models are back-and-forth equivalent, so a family that is
pairwise BF-**in**equivalent is in particular pairwise non-isomorphic. -/
theorem HasCantorAntichainOn.mono_relation {r s : Setoid X} (hrs : ∀ x y, r.r x y → s.r x y)
    (h : HasCantorAntichainOn s A) : HasCantorAntichainOn r A := by
  obtain ⟨f, hcont, hmem, hineq⟩ := h
  exact ⟨f, hcont, hmem, fun x y hxy hr => hineq x y hxy (hrs _ _ hr)⟩

/-- **A Cantor antichain on a subtype is one on the underlying set.**

The subtype carries `r` pulled back along the inclusion, and it *is* the ambient set seen from
inside, so the containment clause is vacuous there and becomes membership in `A` here.  Only
continuity has to move, and it moves by composing with the inclusion.

This is the return leg for anything proved on the model subtype — where a Polish structure is
available — when the statement to be established is about the ambient space. -/
theorem HasCantorAntichainOn.of_subtype
    (h : HasCantorAntichainOn (r.comap (Subtype.val : ↥A → X)) (Set.univ : Set ↥A)) :
    HasCantorAntichainOn r A := by
  obtain ⟨f, hcont, -, hineq⟩ := h
  exact ⟨fun x => (f x).1, continuous_subtype_val.comp hcont, fun x => (f x).2, hineq⟩

omit [TopologicalSpace X] in
/-- **A Cantor antichain survives coarsening the topology.**

Of the three clauses only continuity is topological, and continuity into a coarser topology is
just composition with the identity.  This is the direction needed to carry a witness built in a
Polish refinement — the kind `PolishSpace.IsClopenable` supplies — back to the ambient space.

It is also why no theorem about *perfectness* surviving coarsening is required: coarsening is
applied to the Cantor antichain, where it is cheap, and perfectness is recovered afterwards in
the ambient space by `HasCantorAntichainOn.hasPerfectAntichainOn`. -/
theorem HasCantorAntichainOn.mono_topology {t t' : TopologicalSpace X} (hle : t' ≤ t)
    (h : @HasCantorAntichainOn X t' r A) : @HasCantorAntichainOn X t r A := by
  obtain ⟨f, hcont, hmem, hineq⟩ := h
  -- `continuous_le_rng` coarsens the codomain directly; going through `id` instead forces the
  -- elaborator to synthesize one `TopologicalSpace X` where two different ones are meant
  exact ⟨f, continuous_le_rng hle hcont, hmem, hineq⟩

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
theorem HasCantorAntichainOn.continuum_le_quotient (h : HasCantorAntichainOn r A) :
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

/-- **Cantor space has no isolated points.**

Stated as the bare accumulation-point fact rather than as a `PerfectSpace (ℕ → Bool)` instance:
this Mathlib pin supplies no such instance (its only ones require `ConnectedSpace`, or a module
over a field), and a global orphan instance here would be liable to collide with one added
upstream later.

A neighbourhood in the product topology constrains only finitely many coordinates, so some
coordinate is left free; flipping it moves the point without leaving the neighbourhood. -/
private theorem accPt_univ_natBool (x : ℕ → Bool) :
    AccPt x (𝓟 (Set.univ : Set (ℕ → Bool))) := by
  rw [accPt_iff_nhds]
  intro U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hIfin, V, hV, hVU⟩ := hU
  obtain ⟨n, -, hn⟩ := Set.infinite_univ.exists_notMem_finite hIfin
  refine ⟨Function.update x n (!x n), ⟨hVU fun i hi => ?_, trivial⟩, fun hEq => ?_⟩
  · -- `i` is constrained by the neighbourhood, so it is not the flipped coordinate
    rw [Function.update_of_ne (fun h : i = n => hn (h ▸ hi))]
    exact mem_of_mem_nhds (hV i)
  · exact Bool.not_ne_self (x n) (Function.update_self n (!x n) x ▸ congrFun hEq n)

/-- **A Cantor antichain is a perfect antichain.**

The range is closed because a continuous injection out of a compact space into a Hausdorff one is
a closed embedding; and it inherits Cantor space's lack of isolated points by transporting
accumulation points along that injection.  No metric, completeness, or second-countability
assumption is needed — only `T2Space`. -/
theorem HasCantorAntichainOn.hasPerfectAntichainOn [T2Space X]
    (h : HasCantorAntichainOn r A) : HasPerfectAntichainOn r A := by
  obtain ⟨f, hcont, hmem, hineq⟩ := h
  have hinj : Function.Injective f := injective_of_pairwise_inequiv hineq
  have hemb := hcont.isClosedEmbedding hinj
  refine ⟨Set.range f, ⟨hemb.isClosed_range, ?_⟩, ⟨f (fun _ => false), ⟨_, rfl⟩⟩,
    Set.range_subset_iff.mpr hmem, ?_⟩
  · rintro _ ⟨x, rfl⟩
    -- spelled out: dot notation on `AccPt` resolves to `Filter.NeBot.map`, which is not this
    simpa [Filter.map_principal] using
      AccPt.map (accPt_univ_natBool x) hcont.continuousAt hinj
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hr
    by_contra hne
    exact hineq a b (fun hab => hne (congrArg f hab)) hr

/-- Thinness rules out a Cantor antichain.  The converse of `IsThinOn.of_no_cantorAntichain`
below, and much cheaper: that direction needs a complete metric space, this one only `T2Space`. -/
theorem IsThinOn.no_cantorAntichain [T2Space X] (h : IsThinOn r A) :
    ¬HasCantorAntichainOn r A :=
  fun hc => h hc.hasPerfectAntichainOn

/-! ### Adapters needing the Cantor injection

`Perfect.exists_nat_bool_injection` needs a complete metric space, but **not** second
countability. -/

/-- A perfect antichain yields a Cantor antichain: `Perfect.exists_nat_bool_injection` together
with the observation that the injection's range lies in the perfect set, hence in `A`. -/
theorem HasPerfectAntichainOn.hasCantorAntichainOn {α : Type u} [MetricSpace α]
    [CompleteSpace α] {r : Setoid α} {A : Set α}
    (h : HasPerfectAntichainOn r A) : HasCantorAntichainOn r A := by
  obtain ⟨P, hperf, hne, hsub, hanti⟩ := h
  obtain ⟨f, hrange, hcont, hinj⟩ := hperf.exists_nat_bool_injection hne
  refine ⟨f, hcont, fun x => hsub (hrange (mem_range_self x)), fun x y hxy hr => ?_⟩
  exact hxy (hinj (hanti _ (hrange (mem_range_self x)) _ (hrange (mem_range_self y)) hr))

/-- Refuting Cantor antichains suffices for thinness. -/
theorem IsThinOn.of_no_cantorAntichain {α : Type u} [MetricSpace α] [CompleteSpace α]
    {r : Setoid α} {A : Set α} (h : ¬HasCantorAntichainOn r A) : IsThinOn r A :=
  fun hp => h hp.hasCantorAntichainOn

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

/-- If an equivalence relation has a perfect set of pairwise inequivalent elements, it has
exactly continuum classes (assuming the ambient space has cardinality ≤ continuum).

No second countability: the upper bound arrives explicitly as `hle`. -/
theorem eq_continuum_classes_of_perfect_transversal {α : Type u}
    [MetricSpace α] [CompleteSpace α]
    (r : Setoid α) {C : Set α} (hperf : Perfect C) (hne : C.Nonempty)
    (hinequiv : ∀ x ∈ C, ∀ y ∈ C, r.r x y → x = y)
    (hle : #α ≤ Cardinal.continuum) :
    #(Quotient r) = Cardinal.continuum := by
  apply le_antisymm
  · calc #(Quotient r) ≤ #α := Cardinal.mk_le_of_surjective (Quotient.mk_surjective)
      _ ≤ Cardinal.continuum := hle
  · exact continuum_classes_of_perfect_transversal r hperf hne hinequiv

/-! ### Polish space cardinality upper bound -/

/-- A Polish space has cardinality ≤ continuum. -/
theorem mk_le_continuum_of_polish {α : Type u} [MetricSpace α] [CompleteSpace α]
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
theorem CantorScheme.hasCantorAntichainOn {α : Type u} [PseudoMetricSpace α]
    (r : Setoid α) {A : List Bool → Set α}
    (hlim : ∀ x : ℕ → Bool, (⋂ n, A (PiNat.res x n)).Nonempty)
    (hdiam : CantorScheme.VanishingDiam A)
    (hcross : ∀ l : List Bool, ∀ x ∈ A (false :: l), ∀ y ∈ A (true :: l), ¬ r.r x y) :
    HasCantorAntichainOn r (A []) := by
  obtain ⟨f, hcont, -, hmem, hineq⟩ := CantorScheme.exists_antichain_map r hlim hdiam hcross
  exact ⟨f, hcont, fun a => by simpa using hmem a 0, hineq⟩

/-- `CantorScheme.exists_antichain_map_of_splitting` in antichain vocabulary. -/
theorem CantorScheme.hasCantorAntichainOn_of_splitting {α : Type u} [MetricSpace α]
    [CompleteSpace α] (r : Setoid α) (P : Set α → Prop)
    (hcl : ∀ F, P F → IsClosed F) (hne : ∀ F, P F → F.Nonempty)
    {E : Set α} (hE : P E)
    (hsplit : ∀ F, P F → ∀ ε : ENNReal, 0 < ε →
      ∃ F₀ F₁ : Set α, P F₀ ∧ P F₁ ∧ F₀ ⊆ F ∧ F₁ ⊆ F ∧
        Metric.ediam F₀ ≤ ε ∧ Metric.ediam F₁ ≤ ε ∧
        ∀ x ∈ F₀, ∀ y ∈ F₁, ¬ r.r x y) :
    HasCantorAntichainOn r E := by
  obtain ⟨f, hcont, -, hmem, hineq⟩ :=
    CantorScheme.exists_antichain_map_of_splitting r P hcl hne hE hsplit
  exact ⟨f, hcont, hmem, hineq⟩
