/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Towards the classical `G₀`-dichotomy: independence and positivity machinery

Foundations for the proof of `GSGraphHomHypothesis` (the KST/Miller `G₀`-dichotomy core;
see `InfinitaryLogic/Conditional/SilverCategoryRoute.lean` and
`docs/silver-phase2-route.md`). This file provides the two pillars of the classical
(forcing-free, effective-DST-free) proof:

* **The separation core** (`exists_measurableSet_relIndependent_superset`): for an analytic
  relation `G` on a Polish space, every analytic `G`-independent set is contained in a
  *Borel* `G`-independent set. This is the Kechris–Solecki–Todorcevic lemma, proved here by
  an ω-recursion of Lusin separations (`AnalyticSet.measurablySeparable`): build a
  decreasing sequence of Borel sets `C n ⊇ A`, each separated from the `G`-neighborhood of
  the previous one; the intersection is Borel and independent.

* **The positivity machinery** (`SmallFam`): a family `Φ` of finite assignments `ι → α` is
  *small* if countably many Borel `G`-independent sets capture a value of every member —
  Miller's ideal `I_n` on partial homomorphisms. Smallness is monotone and countably
  additive (`SmallFam.iUnion_of_forall`), giving the pigeonhole
  (`exists_not_smallFam_inter`) used to refine positive families by vertex-value and
  witness-prefix constraints. For the graph `¬r` of a Borel equivalence relation with
  uncountably many classes, the full family is not small (`not_smallFam_univ`): every
  `¬r`-independent set lies in a single class, so a countable capture family would make the
  quotient countable.

* **Combination positivity** (`not_smallFam_comb_cross`, with `not_smallFam_comb_pairs`
  for levels with no fresh constraint): combining pairs of assignments from a positive
  analytic family across a fresh `G`-edge constraint at a designated index yields a
  positive family. This is Miller's "combining pairs of homomorphisms preserves
  `I_n`-positivity": if a countable Borel independent family captured the combined family,
  the assignments avoiding the capture would form a positive analytic family whose values
  at the cross index are `G`-independent, and the KST superset lemma would capture it —
  contradiction. The analyticity side (`analyticSet_comb_pairs`/`analyticSet_comb_cross`)
  keeps the recursion going; the closure facts needed (`AnalyticSet.inter`,
  `AnalyticSet.inter_measurableSet`, `AnalyticSet.prod`) are proved here.

The level recursion (vertex-shrinking and witness-extension pigeonholes) and the fusion
extracting the continuous homomorphism build on these in
`InfinitaryLogic/Descriptive/G0Fusion.lean`; see `docs/silver-phase2-route.md` for the
completed proof map.
-/

open Set Function MeasureTheory

/-! ### Independent sets and neighborhoods -/

section Independence

variable {α : Type*}

/-- A set is independent for a relation `G` (a set of pairs) if it contains no `G`-edge. -/
def RelIndependent (G : Set (α × α)) (A : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → (a, b) ∉ G

theorem RelIndependent.mono {G : Set (α × α)} {A B : Set α} (hBA : B ⊆ A)
    (hA : RelIndependent G A) : RelIndependent G B :=
  fun _ ha _ hb => hA (hBA ha) (hBA hb)

/-- The set of points `G`-adjacent (in either orientation) to some point of `C`. -/
private def relNbhd (G : Set (α × α)) (C : Set α) : Set α :=
  {x | ∃ y ∈ C, (x, y) ∈ G ∨ (y, x) ∈ G}



private theorem RelIndependent.disjoint_relNbhd {G : Set (α × α)} {A : Set α}
    (hA : RelIndependent G A) : Disjoint A (relNbhd G A) := by
  rw [Set.disjoint_left]
  rintro x hxA ⟨y, hyA, he | he⟩
  · exact hA hxA hyA he
  · exact hA hyA hxA he

end Independence

section Separation

variable {α : Type*} [TopologicalSpace α] [PolishSpace α]

private theorem analyticSet_relNbhd {G : Set (α × α)} (hG : AnalyticSet G)
    {C : Set α} (hC : AnalyticSet C) : AnalyticSet (relNbhd G C) := by
  have hswap : AnalyticSet (Prod.swap ⁻¹' G : Set (α × α)) :=
    hG.preimage continuous_swap
  have hunion : AnalyticSet (G ∪ Prod.swap ⁻¹' G) := by
    rw [Set.union_eq_iUnion]
    exact AnalyticSet.iUnion fun b => by cases b <;> simpa
  have hsnd : AnalyticSet (Prod.snd ⁻¹' C : Set (α × α)) :=
    hC.preimage continuous_snd
  have hinter : AnalyticSet ((G ∪ Prod.swap ⁻¹' G) ∩ Prod.snd ⁻¹' C) := by
    rw [Set.inter_eq_iInter]
    exact AnalyticSet.iInter fun b => by cases b <;> simpa
  have himg := hinter.image_of_continuous continuous_fst
  convert himg using 1
  ext x
  constructor
  · rintro ⟨y, hyC, he⟩
    exact ⟨(x, y), ⟨by simpa using he, hyC⟩, rfl⟩
  · rintro ⟨⟨x', y⟩, ⟨he, hyC⟩, rfl⟩
    exact ⟨y, hyC, by simpa using he⟩

variable [MeasurableSpace α] [BorelSpace α]

/-- **The KST independent-superset lemma**: every analytic independent set for an analytic
relation on a Polish space is contained in a Borel independent set. Proved by an
ω-recursion of Lusin separations. -/
private theorem exists_measurableSet_relIndependent_superset
    {G : Set (α × α)} (hG : AnalyticSet G)
    {A : Set α} (hA : AnalyticSet A) (hAind : RelIndependent G A) :
    ∃ B : Set α, MeasurableSet B ∧ A ⊆ B ∧ RelIndependent G B := by
  classical
  -- Stages: Borel supersets of A disjoint from the G-neighborhood of A
  let T := {C : Set α // MeasurableSet C ∧ A ⊆ C ∧ Disjoint C (relNbhd G A)}
  -- The initial stage, separating A from its own neighborhood
  have h0 : ∃ C : Set α, MeasurableSet C ∧ A ⊆ C ∧ Disjoint C (relNbhd G A) := by
    obtain ⟨u, hAu, hdis, hum⟩ :=
      hA.measurablySeparable (analyticSet_relNbhd hG hA) hAind.disjoint_relNbhd
    exact ⟨u, hum, hAu, hdis.symm⟩
  -- The refinement step, separating A from the neighborhood of the current stage
  have hstep : ∀ t : T, ∃ t' : T, t'.1 ⊆ t.1 ∧ Disjoint t'.1 (relNbhd G t.1) := by
    rintro ⟨C, hCm, hAC, hCd⟩
    have hdisj : Disjoint A (relNbhd G C) := by
      rw [Set.disjoint_left]
      rintro x hxA ⟨y, hyC, he⟩
      have hy : y ∈ relNbhd G A := ⟨x, hxA, he.symm⟩
      exact Set.disjoint_left.mp hCd hyC hy
    obtain ⟨u, hAu, hdis, hum⟩ :=
      hA.measurablySeparable (analyticSet_relNbhd hG hCm.analyticSet) hdisj
    exact ⟨⟨u ∩ C, hum.inter hCm, subset_inter hAu hAC,
      hCd.mono_left inter_subset_right⟩, inter_subset_right,
      hdis.symm.mono_left inter_subset_left⟩
  -- The tower of stages
  let seq : ℕ → T := fun n => Nat.rec ⟨_, h0.choose_spec⟩ (fun _ t => (hstep t).choose) n
  have hseq : ∀ n, (seq (n + 1)).1 ⊆ (seq n).1 ∧
      Disjoint (seq (n + 1)).1 (relNbhd G (seq n).1) :=
    fun n => (hstep (seq n)).choose_spec
  refine ⟨⋂ n, (seq n).1, MeasurableSet.iInter fun n => (seq n).2.1,
    subset_iInter fun n => (seq n).2.2.1, ?_⟩
  -- Independence of the intersection
  rintro a ha b hb hab
  have haB : a ∈ (seq 0).1 := mem_iInter.mp ha 0
  have hbB : b ∈ (seq 1).1 := mem_iInter.mp hb 1
  have hbn : b ∈ relNbhd G (seq 0).1 := ⟨a, haB, Or.inr hab⟩
  exact Set.disjoint_left.mp (hseq 0).2 hbB hbn

end Separation

/-! ### The smallness ideal on families of finite assignments -/

section Smallness

variable {α : Type*} [MeasurableSpace α]

/-- A family `Φ` of assignments `ι → α` is **small** for `G` if countably many Borel
`G`-independent sets capture a value of every member of `Φ`. This is Miller's ideal `I_n`
on the spaces of partial homomorphisms. -/
def SmallFam (G : Set (α × α)) {ι : Type*} (Φ : Set (ι → α)) : Prop :=
  ∃ C : ℕ → Set α, (∀ k, MeasurableSet (C k) ∧ RelIndependent G (C k)) ∧
    ∀ φ ∈ Φ, ∃ i : ι, ∃ k : ℕ, φ i ∈ C k

theorem SmallFam.mono {G : Set (α × α)} {ι : Type*} {Φ Ψ : Set (ι → α)}
    (hΨΦ : Ψ ⊆ Φ) (h : SmallFam G Φ) : SmallFam G Ψ := by
  obtain ⟨C, hC, hcap⟩ := h
  exact ⟨C, hC, fun φ hφ => hcap φ (hΨΦ hφ)⟩

theorem SmallFam.empty {G : Set (α × α)} {ι : Type*} :
    SmallFam G (∅ : Set (ι → α)) :=
  ⟨fun _ => ∅, fun _ => ⟨MeasurableSet.empty, fun _ h => h.elim⟩, fun _ h => h.elim⟩

/-- Smallness is countably additive. -/
private theorem SmallFam.iUnion_of_forall {G : Set (α × α)} {ι : Type*} {Ψ : ℕ → Set (ι → α)}
    (h : ∀ n, SmallFam G (Ψ n)) : SmallFam G (⋃ n, Ψ n) := by
  choose C hC hcap using h
  refine ⟨fun k => C (Nat.unpair k).1 (Nat.unpair k).2, fun k => hC _ _, ?_⟩
  rintro φ hφ
  obtain ⟨n, hn⟩ := mem_iUnion.mp hφ
  obtain ⟨i, k, hik⟩ := hcap n φ hn
  exact ⟨i, Nat.pair n k, by simpa [Nat.unpair_pair] using hik⟩

/-- **Positivity pigeonhole**: a non-small family covered by countably many pieces has a
non-small piece. Used to refine positive families by vertex-value and witness-prefix
constraints. -/
theorem exists_not_smallFam_inter {G : Set (α × α)} {ι : Type*} {Φ : Set (ι → α)}
    (hΦ : ¬ SmallFam G Φ) {Ψ : ℕ → Set (ι → α)} (hcov : Φ ⊆ ⋃ n, Ψ n) :
    ∃ n, ¬ SmallFam G (Φ ∩ Ψ n) := by
  by_contra h
  push Not at h
  apply hΦ
  have hΦeq : Φ = ⋃ n, Φ ∩ Ψ n := by
    ext φ
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hφ => by obtain ⟨n, hn⟩ := mem_iUnion.mp (hcov hφ); exact ⟨n, hφ, hn⟩,
      fun ⟨n, hφ, _⟩ => hφ⟩
  rw [hΦeq]
  exact SmallFam.iUnion_of_forall h

/-- Non-small families are nonempty. -/
theorem nonempty_of_not_smallFam {G : Set (α × α)} {ι : Type*} {Φ : Set (ι → α)}
    (hΦ : ¬ SmallFam G Φ) : Φ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  exact hΦ (h ▸ SmallFam.empty)

/-! ### The seed: positivity of the full family for `¬r` -/

omit [MeasurableSpace α] in
/-- For the complement graph of an equivalence relation, independent sets lie in a single
class. -/
private theorem rel_of_relIndependent_compl (r : Setoid α) {C : Set α}
    (hC : RelIndependent {p : α × α | ¬ r.r p.1 p.2} C) :
    ∀ ⦃a⦄, a ∈ C → ∀ ⦃b⦄, b ∈ C → r.r a b := by
  intro a ha b hb
  by_contra h
  exact hC ha hb h

/-- **The seed**: if a Borel equivalence relation has uncountably many classes, then the
full family of assignments is not small for the complement graph — a countable capture
family of independent (hence single-class) Borel sets would make the quotient countable. -/
theorem not_smallFam_univ {ι : Type*} [Nonempty ι] (r : Setoid α)
    (hunc : ¬ Countable (Quotient r)) :
    ¬ SmallFam {p : α × α | ¬ r.r p.1 p.2} (univ : Set (ι → α)) := by
  rintro ⟨C, hC, hcap⟩
  apply hunc
  -- every point lies in some C k
  have hcov : ∀ x : α, ∃ k, x ∈ C k := by
    intro x
    obtain ⟨_, k, hk⟩ := hcap (fun _ => x) (mem_univ _)
    exact ⟨k, hk⟩
  have : Nonempty α := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : IsEmpty (Quotient r) := ⟨fun q => q.exists_rep.elim fun x _ => hne.false x⟩
    exact hunc inferInstance
  classical
  set f : ℕ → Quotient r := fun k =>
    if h : (C k).Nonempty then Quotient.mk r h.choose
    else Quotient.mk r Classical.ofNonempty
  have hsurj : Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨k, hk⟩ := hcov x
    refine ⟨k, ?_⟩
    have hne : (C k).Nonempty := ⟨x, hk⟩
    simp only [f, dite_eq_left hne]
    exact Quotient.sound (rel_of_relIndependent_compl r (hC k).2 hne.choose_spec hk)
  exact hsurj.countable

/-- Smallness is binary additive. -/
theorem SmallFam.union {G : Set (α × α)} {ι : Type*} {Φ₁ Φ₂ : Set (ι → α)}
    (h₁ : SmallFam G Φ₁) (h₂ : SmallFam G Φ₂) : SmallFam G (Φ₁ ∪ Φ₂) := by
  have hcov : Φ₁ ∪ Φ₂ = ⋃ n : ℕ, if n = 0 then Φ₁ else Φ₂ := by
    ext φ
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (h | h)
      · exact ⟨0, by simpa⟩
      · exact ⟨1, by simpa⟩
    · rintro ⟨n, hn⟩
      by_cases h : n = 0
      · exact Or.inl (by simpa [h] using hn)
      · exact Or.inr (by simpa [h] using hn)
  rw [hcov]
  exact SmallFam.iUnion_of_forall fun n => by
    by_cases h : n = 0 <;> simp [h, h₁, h₂]

end Smallness

/-! ### Analytic-set closure helpers -/

section AnalyticClosure

namespace MeasureTheory

variable {α : Type*} [TopologicalSpace α]

protected theorem AnalyticSet.inter [T2Space α] {A B : Set α}
    (hA : AnalyticSet A) (hB : AnalyticSet B) : AnalyticSet (A ∩ B) := by
  rw [Set.inter_eq_iInter]
  exact AnalyticSet.iInter fun b => by cases b <;> simpa

protected theorem AnalyticSet.inter_measurableSet [PolishSpace α] [MeasurableSpace α]
    [BorelSpace α] {A B : Set α} (hA : AnalyticSet A) (hB : MeasurableSet B) :
    AnalyticSet (A ∩ B) :=
  hA.inter hB.analyticSet

protected theorem AnalyticSet.prod {β : Type*} [TopologicalSpace β] {A : Set α} {B : Set β}
    (hA : AnalyticSet A) (hB : AnalyticSet B) : AnalyticSet (A ×ˢ B) := by
  obtain ⟨X, hXt, hXp, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hA
  obtain ⟨Y, hYt, hYp, g, hg, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hB
  let := hXt; have := hXp; let := hYt; have := hYp
  rw [← Set.range_prodMap]
  exact analyticSet_range_of_polishSpace (hf.prodMap hg)

end MeasureTheory

end AnalyticClosure

/-! ### Combination positivity -/

section Combination

variable {α : Type*} [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
variable {G : Set (α × α)} {ι κ : Type*}

omit [TopologicalSpace α] [PolishSpace α] [BorelSpace α] in
/-- Capture transfer for the plain combination (a level with no fresh cross constraint):
combining pairs from a positive family yields a positive family. -/
theorem not_smallFam_comb_pairs {Φ : Set (ι → α)} (hΦ : ¬ SmallFam G Φ)
    (comb : (ι → α) → (ι → α) → κ → α)
    (hvals : ∀ φ₀ φ₁ : ι → α, ∀ v : κ,
      (∃ i, comb φ₀ φ₁ v = φ₀ i) ∨ (∃ i, comb φ₀ φ₁ v = φ₁ i)) :
    ¬ SmallFam G {ψ : κ → α | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, ψ = comb φ₀ φ₁} := by
  rintro ⟨C, hC, hcap⟩
  refine hΦ ⟨C, hC, fun φ hφ => ?_⟩
  obtain ⟨v, k, hvk⟩ := hcap (comb φ φ) ⟨φ, hφ, φ, hφ, rfl⟩
  rcases hvals φ φ v with ⟨i, hi⟩ | ⟨i, hi⟩ <;> exact ⟨i, k, hi ▸ hvk⟩

/-- **Combination positivity across a fresh edge** (the core lemma of the classical
`G₀`-dichotomy; Miller's "combining pairs of homomorphisms preserves `I_n`-positivity"):
combining pairs of assignments from a positive analytic family subject to a fresh `G`-edge
constraint between the values at `s` yields a positive family.

If a countable Borel independent family captured the combined family, the members of `Φ`
avoiding its union would form a positive analytic subfamily `Φ'` (positivity by additivity,
analyticity since the avoided set is Borel); no two members of `Φ'` can satisfy the cross
constraint (the combination would escape the capture), so the values of `Φ'` at `s` form an
analytic `G`-independent set, and the KST superset lemma yields a single Borel independent
set capturing `Φ'` — contradiction. -/
theorem not_smallFam_comb_cross [Countable ι] (hG : AnalyticSet G)
    {Φ : Set (ι → α)} (hΦa : AnalyticSet Φ) (hΦ : ¬ SmallFam G Φ) (s : ι)
    (comb : (ι → α) → (ι → α) → κ → α)
    (hvals : ∀ φ₀ φ₁ : ι → α, ∀ v : κ,
      (∃ i, comb φ₀ φ₁ v = φ₀ i) ∨ (∃ i, comb φ₀ φ₁ v = φ₁ i)) :
    ¬ SmallFam G {ψ : κ → α | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, (φ₀ s, φ₁ s) ∈ G ∧ ψ = comb φ₀ φ₁} := by
  rintro ⟨C, hC, hcap⟩
  set B : Set α := ⋃ k, C k with hBdef
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun k => (hC k).1
  set Φ' : Set (ι → α) := Φ ∩ {φ | ∀ u, φ u ∉ B} with hΦ'def
  -- Φ' is analytic
  have hΦ'a : AnalyticSet Φ' := by
    refine hΦa.inter_measurableSet ?_
    have h : {φ : ι → α | ∀ u, φ u ∉ B} = ⋂ u, (fun φ : ι → α => φ u) ⁻¹' Bᶜ := by
      ext φ
      simp
    rw [h]
    exact MeasurableSet.iInter fun u => measurable_pi_apply u hBm.compl
  -- Φ' is positive
  have hΦ'pos : ¬ SmallFam G Φ' := by
    intro hsmall
    apply hΦ
    have hsub : Φ ⊆ Φ' ∪ {φ : ι → α | ∃ u, φ u ∈ B} := by
      intro φ hφ
      by_cases h : ∀ u, φ u ∉ B
      · exact Or.inl ⟨hφ, h⟩
      · push Not at h
        exact Or.inr h
    refine SmallFam.mono hsub (hsmall.union ⟨C, hC, ?_⟩)
    rintro φ ⟨u, hu⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp hu
    exact ⟨u, k, hk⟩
  -- the values of Φ' at s form an analytic G-independent set
  have hind : RelIndependent G ((fun φ : ι → α => φ s) '' Φ') := by
    rintro a ⟨φ₀, hφ₀, rfl⟩ b ⟨φ₁, hφ₁, rfl⟩ hab
    obtain ⟨v, k, hvk⟩ := hcap (comb φ₀ φ₁) ⟨φ₀, hφ₀.1, φ₁, hφ₁.1, hab, rfl⟩
    rcases hvals φ₀ φ₁ v with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hφ₀.2 i (mem_iUnion.mpr ⟨k, hi ▸ hvk⟩)
    · exact hφ₁.2 i (mem_iUnion.mpr ⟨k, hi ▸ hvk⟩)
  obtain ⟨B', hB'm, hAB', hB'ind⟩ := exists_measurableSet_relIndependent_superset hG
    (hΦ'a.image_of_continuous (continuous_apply s)) hind
  exact hΦ'pos ⟨fun _ => B', fun _ => ⟨hB'm, hB'ind⟩,
    fun φ hφ => ⟨s, 0, hAB' ⟨φ, hφ, rfl⟩⟩⟩

omit [PolishSpace α] [MeasurableSpace α] [BorelSpace α] in
/-- Analyticity of the plain combined family. -/
theorem analyticSet_comb_pairs {Φ : Set (ι → α)} (hΦa : AnalyticSet Φ)
    (comb : (ι → α) → (ι → α) → κ → α)
    (hcomb : Continuous fun p : (ι → α) × (ι → α) => comb p.1 p.2) :
    AnalyticSet {ψ : κ → α | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, ψ = comb φ₀ φ₁} := by
  have h : {ψ : κ → α | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, ψ = comb φ₀ φ₁} =
      (fun p : (ι → α) × (ι → α) => comb p.1 p.2) '' (Φ ×ˢ Φ) := by
    ext ψ
    constructor
    · rintro ⟨φ₀, h₀, φ₁, h₁, rfl⟩
      exact ⟨(φ₀, φ₁), ⟨h₀, h₁⟩, rfl⟩
    · rintro ⟨⟨φ₀, φ₁⟩, ⟨h₀, h₁⟩, rfl⟩
      exact ⟨φ₀, h₀, φ₁, h₁, rfl⟩
  rw [h]
  exact (hΦa.prod hΦa).image_of_continuous hcomb

omit [MeasurableSpace α] [BorelSpace α] in
/-- Analyticity of the combined family with a fresh edge constraint. -/
theorem analyticSet_comb_cross [Countable ι] (hG : AnalyticSet G)
    {Φ : Set (ι → α)} (hΦa : AnalyticSet Φ) (s : ι)
    (comb : (ι → α) → (ι → α) → κ → α)
    (hcomb : Continuous fun p : (ι → α) × (ι → α) => comb p.1 p.2) :
    AnalyticSet {ψ : κ → α | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, (φ₀ s, φ₁ s) ∈ G ∧ ψ = comb φ₀ φ₁} := by
  have hpre : AnalyticSet ((fun p : (ι → α) × (ι → α) => (p.1 s, p.2 s)) ⁻¹' G) :=
    hG.preimage (((continuous_apply s).comp continuous_fst).prodMk
      ((continuous_apply s).comp continuous_snd))
  have h : {ψ : κ → α | ∃ φ₀ ∈ Φ, ∃ φ₁ ∈ Φ, (φ₀ s, φ₁ s) ∈ G ∧ ψ = comb φ₀ φ₁} =
      (fun p : (ι → α) × (ι → α) => comb p.1 p.2) ''
        ((Φ ×ˢ Φ) ∩ (fun p : (ι → α) × (ι → α) => (p.1 s, p.2 s)) ⁻¹' G) := by
    ext ψ
    constructor
    · rintro ⟨φ₀, h₀, φ₁, h₁, hcr, rfl⟩
      exact ⟨(φ₀, φ₁), ⟨⟨h₀, h₁⟩, hcr⟩, rfl⟩
    · rintro ⟨⟨φ₀, φ₁⟩, ⟨⟨h₀, h₁⟩, hcr⟩, rfl⟩
      exact ⟨φ₀, h₀, φ₁, h₁, hcr, rfl⟩
  rw [h]
  exact ((hΦa.prod hΦa).inter hpre).image_of_continuous hcomb

end Combination
