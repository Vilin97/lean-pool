/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.Mycielski
import LeanPool.InfinitaryLogic.Descriptive.KuratowskiUlam
import LeanPool.InfinitaryLogic.Descriptive.GSGraph
import LeanPool.InfinitaryLogic.Descriptive.G0Fusion
/-!
# Silver via the classical category route (Miller): interface layer

This file holds the route to `gandy_harrington_for_relation` (now fully proved):
Benjamin Miller's classical, forcing-free, effective-DST-free proof of
Silver's theorem ["The graph-theoretic approach to descriptive set theory", BSL 18(4), 2012,
Theorem 11; also "Forceless, ineffective, powerless proofs of descriptive dichotomy theorems,
Lecture I"]. The proof composes:

1. **KST `G₀`-dichotomy** (classical proof via the σ-ideal of Borel `G`-independent sets):
   for the graph `G = ¬E` off the diagonal, either there is a Borel ℵ₀-coloring — giving
   countably many classes — or a continuous homomorphism `φ : 2^ℕ → α` from `G_S(2^ℕ)` to `G`.
2. **Pullback + Kuratowski–Ulam**: every class of `E' = (φ × φ)⁻¹(E)` is `G_S`-independent,
   hence meager (for dense `S`); Kuratowski–Ulam then makes `E'` itself meager.
3. **Mycielski**: a meager equivalence relation on Cantor space admits a continuous map
   `ψ : 2^ℕ → 2^ℕ` with distinct points inequivalent.
4. `f = φ ∘ ψ` is the desired perfect antichain.

Steps 1–2 are packaged here as `CategoryReductionHypothesis`, step 3 as
`MycielskiCantorHypothesis`, and step 4 is **proved**: `gandy_harrington_of_category_route`
derives the exact statement of `gandy_harrington_for_relation` from the two hypotheses.

## Design note (audit outcome)

An earlier candidate design — a Gandy–Harrington-style forcing layer
(`Cond`/`split`/`fusion` on subsets of `α`) feeding `CantorScheme.exists_antichain_map` — does
NOT match this route: in Miller's proof the forcing-style largeness lives on spaces of finite
partial homomorphisms `2^n → α` (the `I_n`-positive sets inside the classical `G₀`-dichotomy
proof), not on subsets of `α`, and the final antichain is a composite `φ ∘ ψ` rather than the
limit of a scheme on `α`. Sibling cross-avoidance at finite stages is impossible for dense
relations (e.g. the pullback of `E₀`), so `exists_antichain_map` is *not* the assembly point
for this route; it remains the assembly point for the closed case (`silver_core_closed`).

## Route decomposition (all classical; no effective DST; all proved)

* `MycielskiCantorHypothesis` — proved as `mycielskiCantorHypothesis_holds`, via
  `mycielski_cantor` in `InfinitaryLogic/Descriptive/Mycielski.lean`.
* `CategoryReductionHypothesis` — decomposes into: Kuratowski–Ulam
  (`isMeagre_of_isMeagre_sections` in `InfinitaryLogic/Descriptive/KuratowskiUlam.lean`);
  the `G_S(2^ℕ)` graphs with the dense-`S` independence lemma
  (`exists_gSGraph_edge_of_not_isMeagre` and `isMeagre_pullback_class_of_gSGraph_hom` in
  `InfinitaryLogic/Descriptive/GSGraph.lean`); and the classical `G₀`-dichotomy (Miller's
  proof of KST via `I_n`-positive sets of partial homomorphisms — the hard core, proved by
  the fusion construction `G0Fusion.exists_gsGraph_hom` over the positivity machinery of
  `InfinitaryLogic/Descriptive/G0Dichotomy.lean`). The wiring
  `categoryReductionHypothesis_of_gSGraphHom` reduces it to the single Prop
  `GSGraphHomHypothesis` — a continuous homomorphism from `GSGraph canonicalS` (dense and
  sparse, see `denseWords_canonicalS` / `sparseWords_canonicalS`) into `¬r` whenever `r` is
  Borel with uncountable quotient — proved below as `gSGraphHomHypothesis_holds`, so the
  whole chain through `gandy_harrington_of_gSGraphHom` is unconditional.
-/

universe u

open Set

/-- **Mycielski's theorem for Cantor space** (hypothesis form). A meager equivalence relation
on `ℕ → Bool` admits a continuous map of Cantor space into it with distinct points pairwise
inequivalent. Classical content: Kechris, CDST 19.1 (specialized); provable by a Cantor scheme
of basic clopen boxes avoiding, at level `n`, the first `n` nowhere dense closed sets covering
the relation. Injectivity is omitted: it follows from the antichain property and reflexivity
(see `gandy_harrington_of_category_route`). -/
def MycielskiCantorHypothesis : Prop :=
  ∀ E : Setoid (ℕ → Bool),
    IsMeagre {p : (ℕ → Bool) × (ℕ → Bool) | E.r p.1 p.2} →
    ∃ ψ : (ℕ → Bool) → (ℕ → Bool), Continuous ψ ∧
      ∀ a b : ℕ → Bool, a ≠ b → ¬ E.r (ψ a) (ψ b)

/-- **Category reduction** (hypothesis form): a Borel equivalence relation with uncountably
many classes on a Polish space admits a continuous `φ : 2^ℕ → α` whose pullback relation is
meager. This packages steps 1–2 of Miller's classical proof of Silver's theorem: the
`G₀`-dichotomy applied to the complement graph `¬r` (the coloring side is impossible with
uncountably many classes), followed by `G_S`-independence of the pullback classes and
Kuratowski–Ulam. -/
def CategoryReductionHypothesis : Prop :=
  ∀ {α : Type u} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α] (r : Setoid α),
    MeasurableSet {p : α × α | r.r p.1 p.2} → ¬ Countable (Quotient r) →
    ∃ φ : (ℕ → Bool) → α, Continuous φ ∧
      IsMeagre {p : (ℕ → Bool) × (ℕ → Bool) | r.r (φ p.1) (φ p.2)}

/-- **Assembly of the category route** (proved): the two hypotheses above compose to give
exactly the statement of `gandy_harrington_for_relation`. Pull `r` back along `φ` to a meager
equivalence relation on Cantor space, apply Mycielski to get `ψ`, and take `f = φ ∘ ψ`;
injectivity follows from the antichain property and reflexivity of `r`. -/
theorem gandy_harrington_of_category_route
    (hred : CategoryReductionHypothesis.{u}) (hmyc : MycielskiCantorHypothesis)
    {α : Type u} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  obtain ⟨φ, hφ_cont, hφ_meager⟩ := hred r hr hunc
  -- Pull r back to Cantor space along φ
  let E : Setoid (ℕ → Bool) :=
    ⟨fun x y => r.r (φ x) (φ y),
      ⟨fun _ => r.iseqv.refl _,
       fun h => r.iseqv.symm h,
       fun h h' => r.iseqv.trans h h'⟩⟩
  obtain ⟨ψ, hψ_cont, hψ_anti⟩ := hmyc E hφ_meager
  refine ⟨φ ∘ ψ, hφ_cont.comp hψ_cont, ?_, fun a b hab => hψ_anti a b hab⟩
  intro a b hfab
  by_contra hne
  apply hψ_anti a b hne
  show r.r (φ (ψ a)) (φ (ψ b))
  rw [show φ (ψ a) = φ (ψ b) from hfab]

/-- `MycielskiCantorHypothesis` holds: proved by the level-scheduled Cantor scheme in
`InfinitaryLogic/Descriptive/Mycielski.lean`. -/
theorem mycielskiCantorHypothesis_holds : MycielskiCantorHypothesis := by
  intro E hE
  obtain ⟨ψ, hψ_cont, hψ_anti⟩ := mycielski_cantor hE
  exact ⟨ψ, hψ_cont, fun a b hab => hψ_anti a b hab⟩

/-- **Assembly, Mycielski discharged**: the category route to
`gandy_harrington_for_relation` now reduces to `CategoryReductionHypothesis` alone
(`G₀`-dichotomy + `G_S`-independence + Kuratowski–Ulam). -/
theorem gandy_harrington_of_categoryReduction
    (hred : CategoryReductionHypothesis.{u})
    {α : Type u} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) :=
  gandy_harrington_of_category_route hred mycielskiCantorHypothesis_holds r hr hunc

/-- **The `G₀`-dichotomy input** (hypothesis form; proved below as
`gSGraphHomHypothesis_holds`): a Borel equivalence relation with uncountably many classes on
a Polish space admits a continuous graph homomorphism from `GSGraph canonicalS` into its
complement. This is the homomorphism half of the Kechris–Solecki–Todorcevic `G₀`-dichotomy
applied to the graph `¬r` (the coloring half is impossible: a Borel ℵ₀-coloring of `¬r`
would make the quotient countable); `canonicalS` is dense (consumed by
`isMeagre_pullback_class_of_gSGraph_hom`) and sparse (required for the dichotomy itself;
see `sparseWords_canonicalS`). -/
def GSGraphHomHypothesis : Prop :=
  ∀ {α : Type u} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α] (r : Setoid α),
    MeasurableSet {p : α × α | r.r p.1 p.2} → ¬ Countable (Quotient r) →
    ∃ φ : (ℕ → Bool) → α, Continuous φ ∧
      ∀ y z : ℕ → Bool, GSGraph canonicalS y z → ¬ r.r (φ y) (φ z)

/-- **2C-a wiring (proved)**: the `G₀`-dichotomy input discharges
`CategoryReductionHypothesis`. Given the homomorphism `φ`, every pullback section is meager
(`isMeagre_pullback_class_of_gSGraph_hom`, density of `canonicalS`), the pullback relation
is Baire measurable (Borel, as a continuous preimage), and Kuratowski–Ulam
(`isMeagre_of_isMeagre_sections`) makes it meager. -/
theorem categoryReductionHypothesis_of_gSGraphHom (h : GSGraphHomHypothesis.{u}) :
    CategoryReductionHypothesis.{u} := by
  intro α _ _ _ _ _ r hr hunc
  obtain ⟨φ, hφ_cont, hhom⟩ := h r hr hunc
  refine ⟨φ, hφ_cont, ?_⟩
  have hsec : ∀ a : ℕ → Bool, IsMeagre {b : ℕ → Bool | r.r (φ a) (φ b)} := fun a =>
    isMeagre_pullback_class_of_gSGraph_hom r hr denseWords_canonicalS hφ_cont hhom a
  have hmeas : Measurable fun p : (ℕ → Bool) × (ℕ → Bool) => (φ p.1, φ p.2) :=
    ((hφ_cont.comp continuous_fst).prodMk (hφ_cont.comp continuous_snd)).measurable
  exact isMeagre_of_isMeagre_sections ((hmeas hr).baireMeasurableSet) hsec

/-- **The full chain**: the `G₀`-dichotomy input alone yields the exact statement of
`gandy_harrington_for_relation`; it is fed `gSGraphHomHypothesis_holds` below. -/
theorem gandy_harrington_of_gSGraphHom (h : GSGraphHomHypothesis.{u})
    {α : Type u} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) :=
  gandy_harrington_of_categoryReduction (categoryReductionHypothesis_of_gSGraphHom h) r hr hunc

/-- **The `G₀`-dichotomy input holds** (2C-b complete): proved by the fusion construction
`G0Fusion.exists_gsGraph_hom` over the positivity machinery of `G0Dichotomy.lean`. The
complement graph is Borel hence analytic, nonempty (else the quotient is a singleton), and
mathlib's `AnalyticSet` definition provides the continuous parametrization `g` whose
witnesses drive the fusion. -/
theorem gSGraphHomHypothesis_holds : GSGraphHomHypothesis.{u} := by
  intro α _ _ _ _ _ r hr hunc
  classical
  set G : Set (α × α) := {p : α × α | ¬ r.r p.1 p.2} with hGdef
  have hGm : MeasurableSet G := hr.compl
  have hGa : MeasureTheory.AnalyticSet G := hGm.analyticSet
  -- G is nonempty: otherwise the quotient is a singleton, hence countable
  have hGne : G.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hunc
    have hall : ∀ a b : α, r.r a b := by
      intro a b
      by_contra hab
      have hmem : (a, b) ∈ G := hab
      rw [h] at hmem
      exact hmem
    have : Subsingleton (Quotient r) :=
      ⟨fun q₁ q₂ => Quotient.inductionOn₂ q₁ q₂ fun a b => Quotient.sound (hall a b)⟩
    infer_instance
  -- the continuous parametrization of G
  have hGa2 := hGa
  rw [MeasureTheory.AnalyticSet_def] at hGa2
  rcases hGa2 with hempty | ⟨g, hgc, hgr⟩
  · exact absurd hempty (Set.nonempty_iff_ne_empty.mp hGne)
  have : Nonempty α := ⟨hGne.some.1⟩
  have hpos := not_smallFam_univ (ι := Fin 0 → Bool) r hunc
  have hsymm : ∀ a b : α, (a, b) ∈ G → (b, a) ∈ G := by
    intro a b hab hba
    exact hab (r.iseqv.symm hba)
  obtain ⟨φ, hφc, hφhom⟩ := G0Fusion.exists_gsGraph_hom hGa hgc hgr hpos hsymm
  exact ⟨φ, hφc, fun y z hyz => hφhom y z hyz⟩
