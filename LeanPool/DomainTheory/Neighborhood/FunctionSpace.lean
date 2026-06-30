/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Product
import LeanPool.DomainTheory.Neighborhood.Exercise127

/-!
# Lecture III (§3) — the function space `(𝒟₀ → 𝒟₁)`: Definitions 3.8, Propositions
3.9,
Theorems 3.10, 3.11, 3.12, 3.13

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19
(1981), Lecture III.
The **function space** `(𝒟₀ → 𝒟₁)` is the neighbourhood system whose *tokens* are
the approximable
maps `𝒟₀ → 𝒟₁` (Definition 2.1), and whose neighbourhoods are the non-empty finite
intersections of
the *step sets*

`[X, Y] = {f ∣ X f Y}`   (`step X Y`),

for `X ∈ 𝒟₀`, `Y ∈ 𝒟₁`. We model a finite intersection by a `List` of `(X, Y)`
pairs, with
`stepFun L = {f ∣ ∀ (X, Y) ∈ L, X f Y}`; the empty list gives the master `Δ = |𝒟₀
→ 𝒟₁|`
(`Set.univ`). The system is **positive**: a neighbourhood is required non-empty,
which is exactly
what makes a filter's induced relation *intersective* (Theorem 3.10).

This file formalizes:

* **Definition 3.8** — `step`, `stepFun`, the system `funSpace V₀ V₁`, with the
basic algebra
  `step_inter_right` (`[X,Y] ∩ [X,Y'] = [X,Y∩Y']`), `step_subset`
  (antitone/monotone),
  `step_master_eq` (`[Δ₀,Δ₁] = univ`), and membership `step_mem`.
* **Theorem 3.10** (the crux) — `funSpaceEquiv : |𝒟₀ → 𝒟₁| ≃o ApproximableMap V₀
V₁`: every filter
  is fixed by a unique approximable map (`toApproxMap`/`toFilter`),
  inclusion-preservingly.
* **Proposition 3.9** — `leastMap` (the least map `f₀` of a consistent
neighbourhood, condition
  (ii) `X f₀ Y ↔ ⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`), `leastMap_mem_stepFun` and `leastMap_le`
  (it is the minimal
  element of `⋂[Xᵢ,Yᵢ]`), and `stepFun_subset_step_iff` (the remark after 3.9).
  The consistency
  hypothesis `hcons` is Scott's condition (i) in operational form.
* **Theorem 3.13** — `le_iff_toElementMap_le` (i);
`mapsBounded_iff_pointwiseBounded` (ii);
  `sSupMaps` with `toElementMap_sSupMaps` (iii).
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-! ### The order on approximable maps (rel-inclusion). -/

/-- Approximable maps are ordered by inclusion of their relations (Scott's
approximation order on
`|𝒟₀ → 𝒟₁|`). Antisymmetry is `ApproximableMap.ext`. -/
instance : PartialOrder (ApproximableMap V₀ V₁) where
  le f g := ∀ X Y, f.rel X Y → g.rel X Y
  le_refl _ _ _ h := h
  le_trans _ _ _ h1 h2 X Y h := h2 X Y (h1 X Y h)
  le_antisymm f g h1 h2 := ApproximableMap.ext fun X Y => ⟨h1 X Y, h2 X Y⟩

theorem ApproximableMap.le_iff {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ X Y, f.rel X Y → g.rel X Y := Iff.rfl

/-! ### Definition 3.8 — step sets and the function space. -/

/-- Scott's step set `[X, Y] = {f ∣ X f Y}`. -/
def step (X : Set α) (Y : Set β) : Set (ApproximableMap V₀ V₁) := {f | f.rel X Y}

@[simp] theorem mem_step {X : Set α} {Y : Set β} {f : ApproximableMap V₀ V₁} :
    f ∈ step X Y ↔ f.rel X Y := Iff.rfl

/-- A finite intersection of step sets, indexed by a list of `(X, Y)` pairs. -/
def stepFun (L : List (Set α × Set β)) : Set (ApproximableMap V₀ V₁) :=
  {f | ∀ p ∈ L, f.rel p.1 p.2}

@[simp] theorem mem_stepFun {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} :
    f ∈ stepFun L ↔ ∀ p ∈ L, f.rel p.1 p.2 := Iff.rfl

@[simp] theorem stepFun_nil : (stepFun [] : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  ext f; simp

theorem stepFun_cons (p : Set α × Set β) (L : List (Set α × Set β)) :
    (stepFun (p :: L) : Set (ApproximableMap V₀ V₁)) = step p.1 p.2 ∩ stepFun L := by
  ext f
  simp only [mem_stepFun, List.mem_cons, Set.mem_inter_iff, mem_step]
  constructor
  · intro h; exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨hp, hrest⟩ q (rfl | hq)
    · exact hp
    · exact hrest q hq

theorem stepFun_append (L L' : List (Set α × Set β)) :
    (stepFun (L ++ L') : Set (ApproximableMap V₀ V₁)) = stepFun L ∩ stepFun L' := by
  ext f
  simp only [mem_stepFun, List.mem_append, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨hL, hL'⟩ p (hp | hp)
    · exact hL p hp
    · exact hL' p hp

theorem stepFun_singleton (X : Set α) (Y : Set β) :
    (stepFun [(X, Y)] : Set (ApproximableMap V₀ V₁)) = step X Y := by
  rw [stepFun_cons, stepFun_nil, Set.inter_univ]

/-- `[Δ₀, Δ₁] = |𝒟₀ → 𝒟₁|`: every map relates the masters. -/
@[simp] theorem step_master_eq : (step V₀.master V₁.master : Set (ApproximableMap V₀ V₁)) =
  Set.univ := by
  ext f; simpa using f.master_rel

/-- `[X, Y] ∩ [X, Y'] = [X, Y ∩ Y']` (intersectivity in the output). -/
theorem step_inter_right {X : Set α} {Y Y' : Set β} (hY : V₁.mem Y) (hY' : V₁.mem Y') :
    (step X Y ∩ step X Y' : Set (ApproximableMap V₀ V₁)) = step X (Y ∩ Y') := by
  ext f
  simp only [Set.mem_inter_iff, mem_step]
  constructor
  · rintro ⟨h, h'⟩; exact f.inter_right h h'
  · intro h
    exact ⟨f.mono h subset_rfl Set.inter_subset_left (f.rel_dom h) hY,
           f.mono h subset_rfl Set.inter_subset_right (f.rel_dom h) hY'⟩

/-- `X' ⊆ X` and `Y ⊆ Y'` imply `[X, Y] ⊆ [X', Y']`. -/
theorem step_subset {X X' : Set α} {Y Y' : Set β} (hX' : V₀.mem X') (hY' : V₁.mem Y')
    (hX'X : X' ⊆ X) (hYY' : Y ⊆ Y') : (step X Y : Set (ApproximableMap V₀ V₁)) ⊆ step X' Y' := by
  intro f hf
  exact f.mono hf hX'X hYY' hX' hY'

/-- **Definition 3.8 (Scott 1981, PRG-19).** The *function space* `(𝒟₀ → 𝒟₁)`:
tokens are
approximable maps, neighbourhoods are non-empty finite intersections of step sets. -/
def funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    NeighborhoodSystem (ApproximableMap V₀ V₁) where
  mem W := (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
    ∧ W.Nonempty
  master := Set.univ
  master_mem := ⟨⟨[], by simp, stepFun_nil.symm⟩, ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩⟩
  inter_mem := by
    rintro W W' Z ⟨⟨L, hL, rfl⟩, _⟩ ⟨⟨L', hL', rfl⟩, _⟩ ⟨_, hZne⟩ hZsub
    refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hZne.mono hZsub⟩
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hL p h
    · exact hL' p h
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem funSpace_master : (funSpace V₀ V₁).master = Set.univ := rfl

theorem funSpace_mem_iff {W : Set (ApproximableMap V₀ V₁)} :
    (funSpace V₀ V₁).mem W ↔
      (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
        ∧ W.Nonempty := Iff.rfl

/-- A step neighbourhood `[X, Y]` is a neighbourhood of the function space
(non-empty: it contains
the constant map `constMap V₀ (↑Y)`). -/
theorem step_mem {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (funSpace V₀ V₁).mem (step X Y) := by
  refine ⟨⟨[(X, Y)], ?_, (stepFun_singleton X Y).symm⟩,
    ⟨constMap V₀ (V₁.principal hY), ?_⟩⟩
  · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hX, hY⟩
  · change (constMap V₀ (V₁.principal hY)).rel X Y
    exact ⟨hX, hY, subset_rfl⟩

/-- The "generation" lemma: a filter contains the intersection `stepFun L` iff it
contains each
step `[Xᵢ, Yᵢ]`. (The step sets `[X, Y] ∈ φ` generate the filter `φ`.) -/
theorem mem_stepFun_iff (φ : (funSpace V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (stepFun L) ↔ ∀ p ∈ L, φ.mem (step p.1 p.2) := by
  induction L with
  | nil => simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hstep : φ.mem (step p.1 p.2) :=
        φ.up_mem hmem (step_mem hp.1 hp.2) Set.inter_subset_left
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (stepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail

/-! ### Theorem 3.10 — the function space is complete. -/

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The relation `X φ̂ Y ↔ [X, Y] ∈ φ` of a
filter `φ`.
Intersectivity is the payoff of positivity (`[X,Y]∩[X,Y'] = [X,Y∩Y']` is
non-empty, so `Y∩Y' ∈ 𝒟₁`). -/
def toApproxMap (φ : (funSpace V₀ V₁).Element) : ApproximableMap V₀ V₁ where
  rel X Y := φ.mem (step X Y)
  rel_dom := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_dom hf
  rel_cod := by intro X Y h; obtain ⟨f, hf⟩ := (φ.sub h).2; exact f.rel_cod hf
  master_rel := by show φ.mem (step V₀.master V₁.master); rw [step_master_eq]; exact φ.master_mem
  inter_right := by
    intro X Y Y' h h'
    obtain ⟨f, hf⟩ := (φ.sub h).2
    obtain ⟨f', hf'⟩ := (φ.sub h').2
    have hY : V₁.mem Y := f.rel_cod hf
    have hY' : V₁.mem Y' := f'.rel_cod hf'
    change φ.mem (step X (Y ∩ Y'))
    rw [← step_inter_right hY hY']
    exact φ.inter_mem h h'
  mono := by
    intro X X' Y Y' h hX'X hYY' hX' hY'
    show φ.mem (step X' Y')
    exact φ.up_mem h (step_mem hX' hY') (step_subset hX' hY' hX'X hYY')

@[simp] theorem toApproxMap_rel {φ : (funSpace V₀ V₁).Element} {X : Set α} {Y : Set β} :
    (toApproxMap φ).rel X Y ↔ φ.mem (step X Y) := Iff.rfl

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The filter `f̂ = {F ∣ f ∈ F}` of an
approximable map. -/
def toFilter (f : ApproximableMap V₀ V₁) : (funSpace V₀ V₁).Element where
  mem W := (funSpace V₀ V₁).mem W ∧ f ∈ W
  sub h := h.1
  master_mem := ⟨(funSpace V₀ V₁).master_mem, Set.mem_univ f⟩
  inter_mem := by
    rintro W W' ⟨hW, hfW⟩ ⟨hW', hfW'⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
    refine ⟨⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, ⟨f, ?_⟩⟩, ?_⟩
    · intro p hp; rcases List.mem_append.mp hp with h | h
      · exact hL p h
      · exact hL' p h
    · exact Set.mem_inter hfW hfW'
    · exact Set.mem_inter hfW hfW'
  up_mem := by rintro W W' ⟨hW, hfW⟩ hW' hWW'; exact ⟨hW', hWW' hfW⟩

@[simp] theorem mem_toFilter {f : ApproximableMap V₀ V₁} {W : Set (ApproximableMap V₀ V₁)} :
    (toFilter f).mem W ↔ (funSpace V₀ V₁).mem W ∧ f ∈ W := Iff.rfl

/-- **Theorem 3.10 (Scott 1981, PRG-19).** The function space is *complete*: every
filter is fixed
by a unique approximable mapping, inclusion-preservingly. -/
def funSpaceEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (funSpace V₀ V₁).Element ≃o ApproximableMap V₀ V₁ where
  toFun := toApproxMap
  invFun := toFilter
  left_inv φ := by
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hWmem, hfW⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hWmem
      exact (mem_stepFun_iff φ hL).mpr (fun p hp => hfW p hp)
    · intro hW
      refine ⟨φ.sub hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      intro p hp
      exact (mem_stepFun_iff φ hL).mp hW p hp
  right_inv f := by
    apply ApproximableMap.ext
    intro X Y
    constructor
    · rintro ⟨_, hf⟩; exact hf
    · intro hf; exact ⟨step_mem (f.rel_dom hf) (f.rel_cod hf), hf⟩
  map_rel_iff' := by
    intro φ φ'
    constructor
    · intro h W hW
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := φ.sub hW
      refine (mem_stepFun_iff φ' hL).mpr (fun p hp => ?_)
      exact h p.1 p.2 ((mem_stepFun_iff φ hL).mp hW p hp)
    · intro h X Y hrel
      exact h _ hrel

@[simp] theorem funSpaceEquiv_apply (φ : (funSpace V₀ V₁).Element) :
    funSpaceEquiv V₀ V₁ φ = toApproxMap φ := rfl

@[simp] theorem funSpaceEquiv_symm_apply (f : ApproximableMap V₀ V₁) :
    (funSpaceEquiv V₀ V₁).symm f = toFilter f := rfl

/-- Intersection of two function-space neighbourhoods, when non-empty, is again
one. -/
theorem funSpace_mem_inter {W W' : Set (ApproximableMap V₀ V₁)}
    (hW : (funSpace V₀ V₁).mem W) (hW' : (funSpace V₀ V₁).mem W') (hne : (W ∩ W').Nonempty) :
    (funSpace V₀ V₁).mem (W ∩ W') := by
  obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
  obtain ⟨⟨L', hL', rfl⟩, _⟩ := hW'
  refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hne⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hL p h
  · exact hL' p h

/-- Step neighbourhoods are *up-closed* under the map order: if `f ∈ stepFun L`
and `f ⊑ f'`, then
`f' ∈ stepFun L`. -/
theorem stepFun_up_closed {L : List (Set α × Set β)} {f f' : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) (hff' : f ≤ f') : f' ∈ stepFun L := by
  intro p hp
  exact hff' p.1 p.2 (hf p hp)

/-- A function-space neighbourhood is up-closed under the map order. -/
theorem funSpace_mem_up_closed {W : Set (ApproximableMap V₀ V₁)} (hW : (funSpace V₀ V₁).mem W)
    {f f' : ApproximableMap V₀ V₁} (hf : f ∈ W) (hff' : f ≤ f') : f' ∈ W := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hW
  exact stepFun_up_closed hf hff'

/-! ### Proposition 3.9 — the least map of a consistent neighbourhood. -/

/-- Scott's intersection `⋂ {Yᵢ ∣ X ⊆ Xᵢ}` of the outputs whose input is coarser
than `X`, taken
inside the master neighbourhood `Δ₁` (so the empty intersection is `Δ₁`, per the
convention 1.1a).
Indexed by the list `L` of `(Xᵢ, Yᵢ)` pairs. -/
def interYs (m : Set β) : List (Set α × Set β) → Set α → Set β
  | [], _ => m
  | p :: L, X => {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X

@[simp] theorem interYs_nil (m : Set β) (X : Set α) : interYs m [] X = m := rfl

theorem interYs_cons (m : Set β) (p : Set α × Set β) (L : List (Set α × Set β)) (X : Set α) :
    interYs m (p :: L) X = {z | X ⊆ p.1 → z ∈ p.2} ∩ interYs m L X := rfl

/-- Membership in `interYs`: `z ∈ ⋂{Yᵢ ∣ X ⊆ Xᵢ}` iff `z ∈ Δ₁` and `z ∈ Yᵢ` for
every `i` with
`X ⊆ Xᵢ`. -/
theorem mem_interYs {m : Set β} {L : List (Set α × Set β)} {X : Set α} {z : β} :
    z ∈ interYs m L X ↔ z ∈ m ∧ ∀ p ∈ L, X ⊆ p.1 → z ∈ p.2 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [interYs_cons]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, ih, List.mem_cons]
    constructor
    · rintro ⟨hp, hm, hL⟩
      refine ⟨hm, ?_⟩
      rintro q (rfl | hq) hXq
      · exact hp hXq
      · exact hL q hq hXq
    · rintro ⟨hm, hall⟩
      exact ⟨fun hXp => hall p (Or.inl rfl) hXp, hm,
        fun q hq hXq => hall q (Or.inr hq) hXq⟩

/-- `interYs` is contained in the master neighbourhood. -/
theorem interYs_subset_master {m : Set β} {L : List (Set α × Set β)} {X : Set α} :
    interYs m L X ⊆ m := fun _ hz => (mem_interYs.mp hz).1

/-- `interYs` is antitone in the input `X`: a sharper input intersects over more
outputs. -/
theorem interYs_antitone {m : Set β} {L : List (Set α × Set β)} {X X' : Set α} (h : X' ⊆ X) :
    interYs m L X' ⊆ interYs m L X := by
  intro z hz
  rw [mem_interYs] at hz ⊢
  exact ⟨hz.1, fun p hp hXp => hz.2 p hp (h.trans hXp)⟩

/-- `interYs` contains `Yⱼ` whenever `Xⱼ ⊆ X`-indexed: in particular `interYs m L
Xⱼ ⊆ Yⱼ` for
`(Xⱼ, Yⱼ) ∈ L`. -/
theorem interYs_subset_of_mem {m : Set β} {L : List (Set α × Set β)} {p : Set α × Set β}
    (hp : p ∈ L) : interYs m L p.1 ⊆ p.2 :=
  fun _ hz => (mem_interYs.mp hz).2 p hp subset_rfl

/-- **Proposition 3.9(ii) (Scott 1981, PRG-19).** The *least* approximable mapping
`f₀` belonging to
the neighbourhood `⋂ [Xᵢ, Yᵢ]`, defined by `X f₀ Y ↔ ⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`.
Well-definedness uses
Scott's condition (i) in the operational form `hcons`: for every neighbourhood
`X`, the outputs
`{Yᵢ ∣ X ⊆ Xᵢ}` (consistent in `𝒟₁`, witnessed by `X` being a common lower bound
of their inputs)
have their intersection again a neighbourhood. -/
def leastMap (L : List (Set α × Set β))
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) : ApproximableMap V₀ V₁ where
  rel X Y := V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, V₁.master_mem, interYs_subset_master⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hX, V₁.inter_mem hY hY' (hcons hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (interYs_antitone hX'X).trans (hsub.trans hYY')⟩

@[simp] theorem leastMap_rel {L : List (Set α × Set β)}
    {hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)} {X : Set α} {Y : Set β} :
    (leastMap L hcons).rel X Y ↔ V₀.mem X ∧ V₁.mem Y ∧ interYs V₁.master L X ⊆ Y := Iff.rfl

/-- **Proposition 3.9 (Scott 1981, PRG-19).** The least map `f₀` belongs to the
neighbourhood:
`Xᵢ f₀ Yᵢ` for every `(Xᵢ, Yᵢ) ∈ L`. -/
theorem leastMap_mem_stepFun {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) :
      leastMap L hcons ∈ stepFun L := by
  intro p hp
  exact ⟨(hL p hp).1, (hL p hp).2, interYs_subset_of_mem hp⟩

/-- The relation `X f Y` holds for `f` in the neighbourhood `stepFun L` at the
master output, and
more importantly `f` relates `X` to the whole intersection `interYs Δ₁ L X`
(finite intersectivity
over the relevant outputs). The case split deciding `X ⊆ Xᵢ` is a documented
classical step. -/
theorem rel_interYs {L : List (Set α × Set β)} {f : ApproximableMap V₀ V₁} (hf : f ∈ stepFun L)
    {X : Set α} (hX : V₀.mem X) : f.rel X (interYs V₁.master L X) := by
  induction L with
  | nil =>
    rw [interYs_nil]
    exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₁.master_mem
  | cons p L ih =>
    have hftail : f ∈ stepFun L := fun q hq => hf q (List.mem_cons.mpr (Or.inr hq))
    have htail := ih hftail
    by_cases hXp : X ⊆ p.1
    · have hp : f.rel p.1 p.2 := hf p (List.mem_cons.mpr (Or.inl rfl))
      have hXp2 : f.rel X p.2 := f.mono hp hXp subset_rfl hX (f.rel_cod hp)
      have heq : interYs V₁.master (p :: L) X = p.2 ∩ interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hXp, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]; exact f.inter_right hXp2 htail
    · have heq : interYs V₁.master (p :: L) X = interYs V₁.master L X := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hXp, h⟩⟩
      rw [heq]; exact htail

/-- **Proposition 3.9 (Scott 1981, PRG-19).** `f₀` is the *minimal* element of the
neighbourhood:
any `f` with `Xᵢ f Yᵢ` for all `i` satisfies `f₀ ⊆ f`. -/
theorem leastMap_le {L : List (Set α × Set β)}
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {f : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) : leastMap L hcons ≤ f := by
  rintro X Y ⟨hX, hY, hsub⟩
  exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

/-- **Remark after Proposition 3.9 (Scott 1981, PRG-19).** When the neighbourhood
is consistent,
`⋂ [Xᵢ, Yᵢ] ⊆ [X, Y]` iff `⋂{Yᵢ ∣ X ⊆ Xᵢ} ⊆ Y`. This is the form used to check
that `curry` is
monotone (and hence approximable). -/
theorem stepFun_subset_step_iff {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {X : Set α} {Y : Set β}
    (hX : V₀.mem X) (hY : V₁.mem Y) :
    (stepFun L : Set (ApproximableMap V₀ V₁)) ⊆ step X Y ↔ interYs V₁.master L X ⊆ Y := by
  constructor
  · intro hsub
    have := hsub (leastMap_mem_stepFun hL hcons)
    exact (mem_step.mp this).2.2
  · intro hsub f hf
    exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

/-! ### Theorem 3.13(i) — the pointwise order. -/

/-- **Theorem 3.13(i) (Scott 1981, PRG-19).** `f ⊑ g ↔ ∀ x, f(x) ⊑ g(x)`. -/
theorem le_iff_toElementMap_le {f g : ApproximableMap V₀ V₁} :
    f ≤ g ↔ ∀ x, f.toElementMap x ≤ g.toElementMap x := by
  constructor
  · intro h x Y ⟨X, hXx, hrel⟩
    exact ⟨X, hXx, h X Y hrel⟩
  · intro h X Y hrel
    have hX : V₀.mem X := f.rel_dom hrel
    rw [f.rel_iff_mem_principal hX] at hrel
    rw [g.rel_iff_mem_principal hX]
    exact h (V₀.principal hX) Y hrel

/-! ### Theorem 3.13(ii)(iii) — pointwise boundedness and sups. -/

/-- A set `F` of approximable maps is *bounded* when it has an upper bound in the
map order. -/
def MapsBounded (F : Set (ApproximableMap V₀ V₁)) : Prop := ∃ h, ∀ f ∈ F, f ≤ h

/-- `F` is *pointwise bounded* when `{f(x) ∣ f ∈ F}` is bounded in `|𝒟₁|` for
every `x`. -/
def PointwiseBounded (F : Set (ApproximableMap V₀ V₁)) : Prop :=
  ∀ x : V₀.Element, V₁.Bounded (Set.image (fun f => f.toElementMap x) F)

theorem toFilter_le_iff {f g : ApproximableMap V₀ V₁} : toFilter f ≤ toFilter g ↔ f ≤ g :=
  (funSpaceEquiv V₀ V₁).symm.map_rel_iff'

theorem mapsBounded_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    V₁.Bounded (Set.image (fun f => f.toElementMap (V₀.principal hX)) F) :=
  hF (V₀.principal hX)

/-- The sup of `{f(↑X) ∣ f ∈ F}` on principal inputs, used to build `sSupMaps`. -/
def supOnPrincipal (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F)
    (X : Set α) (hX : V₀.mem X) : V₁.Element :=
  V₁.sSup (Set.image (fun f => f.toElementMap (V₀.principal hX)) F) (mapsBounded_principal hF hX)

theorem supOnPrincipal_mono (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F)
    (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) :
    supOnPrincipal F hF X hX ≤ supOnPrincipal F hF X' hX' :=
  V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
    obtain ⟨f, hf, rfl⟩ := hs
    exact (toElementMap_mono f ((V₀.principal_le_iff hX hX').mpr hX'X)).trans
      (V₁.le_sSup _ (mapsBounded_principal hF hX') ⟨f, hf, rfl⟩)

theorem mapsBounded_to_filters {F : Set (ApproximableMap V₀ V₁)} (h : MapsBounded F) :
    (funSpace V₀ V₁).Bounded (Set.image toFilter F) := by
  obtain ⟨h, hh⟩ := h
  refine ⟨toFilter h, fun φ hφ => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hφ
  exact (toFilter_le_iff).mpr (hh f hf)

/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** The least upper bound of a
pointwise-bounded set
`F`, defined on principal inputs by `supOnPrincipal` and extended via Exercise 2.8
(`ofMono`). -/
def sSupMaps (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F) : ApproximableMap V₀ V₁ :=
  ofMono (fun X hX => supOnPrincipal F hF X hX) (supOnPrincipal_mono F hF)

theorem toElementMap_sSupMaps_principal {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {X : Set α} (hX : V₀.mem X) :
    (sSupMaps F hF).toElementMap (V₀.principal hX) = supOnPrincipal F hF X hX :=
  toElementMap_ofMono_principal _ (supOnPrincipal_mono F hF) X hX

/-- **Theorem 3.13(ii) (Scott 1981, PRG-19).** `F` is bounded in `|𝒟₀ → 𝒟₁|` iff
`{f(x) ∣ f ∈ F}` is
bounded in `|𝒟₁|` for each `x ∈ |𝒟₀|`. The forward direction is
`le_iff_toElementMap_le` (3.13(i))
applied pointwise; the backward direction builds the bound `sSupMaps F`. -/
theorem mapsBounded_iff_pointwiseBounded {F : Set (ApproximableMap V₀ V₁)} :
    MapsBounded F ↔ PointwiseBounded F := by
  constructor
  · intro ⟨h, hh⟩ x
    refine ⟨h.toElementMap x, fun z hz => ?_⟩
    obtain ⟨f, hf, rfl⟩ := hz
    exact (le_iff_toElementMap_le.mp (hh f hf)) x
  · intro hpb
    refine ⟨sSupMaps F hpb, fun f hf X Y hrel => ?_⟩
    have hX : V₀.mem X := f.rel_dom hrel
    have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
    exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hpb hX) ⟨f, hf, rfl⟩) Y hmem⟩

theorem le_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {f : ApproximableMap V₀ V₁} (hf : f ∈ F) : f ≤ sSupMaps F hF := by
  intro X Y hrel
  have hX : V₀.mem X := f.rel_dom hrel
  have hmem : (f.toElementMap (V₀.principal hX)).mem Y := (f.rel_iff_mem_principal hX).mp hrel
  exact ⟨hX, (V₁.le_sSup _ (mapsBounded_principal hF hX) ⟨f, hf, rfl⟩) Y hmem⟩

theorem sSupMaps_le {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    {h : ApproximableMap V₀ V₁} (hh : ∀ f ∈ F, f ≤ h) : sSupMaps F hF ≤ h := by
  intro X Y hrel
  obtain ⟨hX, hYmem⟩ := hrel
  have hle : supOnPrincipal F hF X hX ≤ h.toElementMap (V₀.principal hX) :=
    V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
      obtain ⟨f, hf, rfl⟩ := hs
      exact (le_iff_toElementMap_le.mp (hh f hf)) (V₀.principal hX)
  exact (h.rel_iff_mem_principal hX).mpr (hle Y hYmem)

theorem toElementMap_sSupMaps {F : Set (ApproximableMap V₀ V₁)} (hF : PointwiseBounded F)
    (x : V₀.Element) :
    (sSupMaps F hF).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F) (hF x) := by
  apply le_antisymm
  · -- `(⊔F)(x) ⊑ ⊔{f(x)}`: read `(⊔F)(x)` off some principal `↑X` (Ex 2.9), where the
    -- principal value `(⊔F)(↑X) = ⊔{f(↑X)}` is bounded above by `⊔{f(x)}`
    -- (monotonicity, `↑X ⊑ x`).
    intro Y hY
    rw [toElementMap_mem_iff_principal (sSupMaps F hF) x] at hY
    obtain ⟨X, hxX, hY'⟩ := hY
    have hX : V₀.mem X := x.sub hxX
    rw [toElementMap_sSupMaps_principal hF] at hY'
    have hprinc : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    have hsub : supOnPrincipal F hF X hX ≤ V₁.sSup (Set.image (fun f => f.toElementMap x) F) (
      hF x) :=
      V₁.sSup_le _ (mapsBounded_principal hF hX) fun s hs => by
        obtain ⟨f, hf, rfl⟩ := hs
        exact (toElementMap_mono f hprinc).trans (V₁.le_sSup _ (hF x) ⟨f, hf, rfl⟩)
    exact hsub Y hY'
  · -- `⊔{f(x)} ⊑ (⊔F)(x)`: `(⊔F)(x)` is an upper bound of every `f(x)` since `f ⊑ ⊔F` (3.13(i)).
    refine V₁.sSup_le _ (hF x) fun s hs => ?_
    obtain ⟨f, hf, rfl⟩ := hs
    exact le_iff_toElementMap_le.mp (le_sSupMaps hF hf) x

/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** When `F` is bounded, `(⊔F)(x) =
⊔{f(x) ∣ f ∈ F}`
(stated with the boundedness hypothesis in Scott's `MapsBounded` form). -/
theorem toElementMap_sSupMaps' {F : Set (ApproximableMap V₀ V₁)} (hF : MapsBounded F)
    (x : V₀.Element) :
    (sSupMaps F (mapsBounded_iff_pointwiseBounded.mp hF)).toElementMap x =
      V₁.sSup (Set.image (fun f => f.toElementMap x) F)
        (mapsBounded_iff_pointwiseBounded.mp hF x) :=
  toElementMap_sSupMaps (mapsBounded_iff_pointwiseBounded.mp hF) x

/-! ### Theorem 3.11 — evaluation. -/

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.11 (Scott 1981, PRG-19).** The two-variable evaluation map
`eval : (𝒟₁ → 𝒟₂) × 𝒟₁ → 𝒟₂`, `F, X eval Y ↔ X f Y for all f ∈ F`. -/
def eval (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap₂ (funSpace V₁ V₂) V₁ V₂ where
  rel F X Y := (funSpace V₁ V₂).mem F ∧ V₁.mem X ∧ V₂.mem Y ∧ ∀ f ∈ F, f.rel X Y
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨(funSpace V₁ V₂).master_mem, V₁.master_mem, V₂.master_mem,
    fun f _ => f.master_rel⟩
  inter_right := by
    rintro F X Y Y' ⟨hF, hX, hY, hrel⟩ ⟨_, _, hY', hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hF).2
    refine ⟨hF, hX, ?_, fun g hg => g.inter_right (hrel g hg) (hrel' g hg)⟩
    exact f.rel_cod (f.inter_right (hrel f hf) (hrel' f hf))
  mono := by
    rintro F F' X X' Y Y' ⟨hF, hX, hY, hrel⟩ hF'F hX'X hYY' hF' hX' hY'
    exact ⟨hF', hX', hY', fun f hf => f.mono (hrel f (hF'F hf)) hX'X hYY' hX' hY'⟩

/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(f, x) = f(x)` (with the filter
`φ` viewed as
the map `toApproxMap φ` via Theorem 3.10). -/
theorem toElementMap₂_eval (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (eval V₁ V₂).toElementMap₂ φ x = (toApproxMap φ).toElementMap x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨F, X, hφF, hxX, _, hX, hY, hrel⟩
    refine ⟨X, hxX, ?_⟩
    change φ.mem (step X Y)
    exact φ.up_mem hφF (step_mem hX hY) (fun f hf => hrel f hf)
  · rintro ⟨X, hxX, hrel⟩
    have hstep : (funSpace V₁ V₂).mem (step X Y) := φ.sub hrel
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp hstep).2
    exact ⟨step X Y, X, hrel, hxX, hstep, f.rel_dom hf, f.rel_cod hf, fun g hg => hg⟩

/-- **Theorem 3.11 (Scott 1981, PRG-19).** Evaluation as a single approximable map
out of the
product `(𝒟₁ → 𝒟₂) × 𝒟₁ → 𝒟₂`. -/
def evalMap (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) V₁) V₂ := ofMap₂ (eval V₁ V₂)

/-- **Theorem 3.11(i) (Scott 1981, PRG-19).** `eval(⟨f, x⟩) = f(x)`. -/
theorem evalMap_apply (φ : (funSpace V₁ V₂).Element) (x : V₁.Element) :
    (evalMap V₁ V₂).toElementMap (pair φ x) = (toApproxMap φ).toElementMap x := by
  rw [evalMap, ← toElementMap₂_toMap₂, toMap₂_ofMap₂, toElementMap₂_eval]

/-! ### Theorem 3.12 — currying. -/

/-- The `X`-section of a two-variable map `g : 𝒟₀ × 𝒟₁ → 𝒟₂`: the map `𝒟₁ → 𝒟₂`
with
`Y (gSection g X) Z ↔ X ∪ Y g Z`. -/
def gSection (g : ApproximableMap (prod V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ where
  rel Y Z := g.rel (prodNbhd X Y) Z
  rel_dom h := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  rel_cod h := g.rel_cod h
  master_rel := g.rel_master (prod_mem_prodNbhd hX V₁.master_mem)
  inter_right h h' := g.inter_right h h'
  mono := by
    intro Y Y' Z Z' h hY'Y hZZ' hY' hZ'
    exact g.mono h (prodNbhd_subset_iff.mpr ⟨subset_rfl, hY'Y⟩) hZZ'
      (prod_mem_prodNbhd hX hY') hZ'

@[simp] theorem gSection_rel {g : ApproximableMap (prod V₀ V₁) V₂} {X : Set α} (hX : V₀.mem X)
    {Y : Set β} {Z : Set γ} : (gSection g hX).rel Y Z ↔ g.rel (prodNbhd X Y) Z := Iff.rfl

theorem gSection_le {g : ApproximableMap (prod V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) : gSection g hX ≤ gSection g hX' := by
  intro Y Z h
  have hY := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  exact g.mono h (prodNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩) subset_rfl
    (prod_mem_prodNbhd hX' hY) (g.rel_cod h)

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry(g) : 𝒟₀ → (𝒟₁ → 𝒟₂)`, where
`X curry(g) W ↔ (the X-section of g) ∈ W` (for `W = [Y, Z]` this is `X ∪ Y g Z`). -/
def curry (g : ApproximableMap (prod V₀ V₁) V₂) : ApproximableMap V₀ (funSpace V₁ V₂) where
  rel X W := ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨_, hW, _⟩ => hW
  master_rel := ⟨V₀.master_mem, (funSpace V₁ V₂).master_mem, Set.mem_univ _⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hmem⟩ ⟨_, hW', hmem'⟩
    exact ⟨hX, funSpace_mem_inter hW hW' ⟨gSection g hX, hmem, hmem'⟩,
      Set.mem_inter hmem hmem'⟩
  mono := by
    rintro X X' W W' ⟨hX, hW, hmem⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', funSpace_mem_up_closed hW' (hWW' hmem) (gSection_le hX hX' hX'X)⟩

@[simp] theorem curry_rel {g : ApproximableMap (prod V₀ V₁) V₂} {X : Set α}
    {W : Set (ApproximableMap V₁ V₂)} :
    (curry g).rel X W ↔ ∃ hX : V₀.mem X, (funSpace V₁ V₂).mem W ∧ gSection g hX ∈ W := Iff.rfl

/-- **Theorem 3.12(i) (Scott 1981, PRG-19).** `curry(g)(x)(y) = g(x, y)`. -/
theorem toElementMap_curry_apply (g : ApproximableMap (prod V₀ V₁) V₂)
    (x : V₀.Element) (y : V₁.Element) :
    (toApproxMap ((curry g).toElementMap x)).toElementMap y = g.toElementMap (pair x y) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hyY, X, hxX, hX, _, hrel⟩
    exact ⟨prodNbhd X Y, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
  · rintro ⟨W, ⟨X, Y, hxX, hyY, rfl⟩, hrel⟩
    exact ⟨Y, hyY, X, hxX, x.sub hxX, step_mem (y.sub hyY) (g.rel_cod hrel), hrel⟩

/-- The relational generation lemma for maps `h : 𝒟₀ → (𝒟₁ → 𝒟₂)`: `X h (⋂ᵢ
[Yᵢ,Zᵢ])` iff
`X h [Yᵢ,Zᵢ]` for all `i`. -/
theorem rel_stepFun_iff (h : ApproximableMap V₀ (funSpace V₁ V₂)) {X : Set α} (hX : V₀.mem X)
    {L : List (Set β × Set γ)} (hL : ∀ p ∈ L, V₁.mem p.1 ∧ V₂.mem p.2) :
    h.rel X (stepFun L) ↔ ∀ p ∈ L, h.rel X (step p.1 p.2) := by
  induction L with
  | nil =>
    simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    change h.rel X (funSpace V₁ V₂).master
    exact h.rel_master hX
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₁.mem q.1 ∧ V₂.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (h.rel_cod hmem).2
      have hstep : h.rel X (step p.1 p.2) :=
        h.mono hmem subset_rfl Set.inter_subset_left hX (step_mem hp.1 hp.2)
      have htail : h.rel X (stepFun L) :=
        h.mono hmem subset_rfl Set.inter_subset_right hX
          ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : h.rel X (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : h.rel X (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact h.inter_right hstep htail

theorem prod_mem_inl {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) : V₀.mem (Sum.inl ⁻¹' W) := by
  obtain ⟨X, Y, hX, _, rfl⟩ := hW; rwa [inl_preimage_prodNbhd]

theorem prod_mem_inr {W : Set (α ⊕ β)} (hW : (prod V₀ V₁).mem W) : V₁.mem (Sum.inr ⁻¹' W) := by
  obtain ⟨X, Y, _, hY, rfl⟩ := hW; rwa [inr_preimage_prodNbhd]

/-- **Theorem 3.12 (Scott 1981, PRG-19).** Uncurrying `h : 𝒟₀ → (𝒟₁ → 𝒟₂)` to `𝒟₀
× 𝒟₁ → 𝒟₂`:
`X ∪ Y (uncurry h) Z ↔ X h [Y, Z]`. -/
def uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : ApproximableMap (prod V₀ V₁) V₂ where
  rel W Z := (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z)
  rel_dom h' := h'.1
  rel_cod := by
    rintro W Z ⟨_, hrel⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    exact f.rel_cod hf
  master_rel := by
    refine ⟨(prod V₀ V₁).master_mem, ?_⟩
    rw [show (prod V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
      inl_preimage_prodNbhd, inr_preimage_prodNbhd, step_master_eq]
    exact h.master_rel
  inter_right := by
    rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
    obtain ⟨f, hf⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel)).2
    obtain ⟨f', hf'⟩ := (funSpace_mem_iff.mp (h.rel_cod hrel')).2
    refine ⟨hW, ?_⟩
    rw [← step_inter_right (f.rel_cod hf) (f'.rel_cod hf')]
    exact h.inter_right hrel hrel'
  mono := by
    rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
    have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
    have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
    obtain ⟨A, B, hA, hB, rfl⟩ := hW₂
    rw [inl_preimage_prodNbhd] at hinl ⊢
    rw [inr_preimage_prodNbhd] at hinr ⊢
    refine ⟨prod_mem_prodNbhd hA hB, ?_⟩
    exact h.mono hrel hinl (step_subset hB hZ' hinr hZZ') hA (step_mem hB hZ')

@[simp] theorem uncurry_rel {h : ApproximableMap V₀ (funSpace V₁ V₂)}
    {W : Set (α ⊕ β)} {Z : Set γ} :
    (uncurry h).rel W Z ↔
      (prod V₀ V₁).mem W ∧ h.rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := Iff.rfl

/-- `uncurry` is the composition `eval ∘ ⟨h ∘ p₀, p₁⟩`. -/
theorem uncurry_eq (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    uncurry h = (evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, evalMap_apply]
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨W₀, hwW₀, hW₀, hrel⟩
    obtain ⟨X, Y, hX, hY, rfl⟩ := hW₀
    rw [inl_preimage_prodNbhd] at hrel
    rw [inr_preimage_prodNbhd] at hrel
    obtain ⟨hwX, hwY⟩ := (prod_mem_split hX hY).mp hwW₀
    exact ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
  · rintro ⟨Y, ⟨hY, hwY⟩, X, ⟨hX, hwX⟩, hrel⟩
    refine ⟨prodNbhd X Y, (prod_mem_split hX hY).mpr ⟨hwX, hwY⟩, prod_mem_prodNbhd hX hY, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact hrel

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `uncurry (curry g) = g`. -/
theorem uncurry_curry (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g := by
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, _, _, hmem⟩
    rw [prodNbhd_preimage hW]; exact hmem
  · intro hrel
    have hW := g.rel_dom hrel
    refine ⟨hW, prod_mem_inl hW, step_mem (prod_mem_inr hW) (g.rel_cod hrel), ?_⟩
    change g.rel (prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W)) Z
    rwa [← prodNbhd_preimage hW]

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry (uncurry h) = h`. -/
theorem curry_uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : curry (uncurry h) = h := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨hX, hW, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    refine (rel_stepFun_iff h hX hL).mpr (fun p hp => ?_)
    have := hmem p hp
    -- `gSection (uncurry h) hX ∈ step p.1 p.2` means `(uncurry h).rel (prodNbhd X
    -- p.1) p.2`
    have hrel : (uncurry h).rel (prodNbhd X p.1) p.2 := this
    obtain ⟨_, hrel'⟩ := hrel
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel'
    exact hrel'
  · intro hrel
    have hX : V₀.mem X := h.rel_dom hrel
    have hW : (funSpace V₁ V₂).mem W := h.rel_cod hrel
    refine ⟨hX, hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    intro p hp
    change (uncurry h).rel (prodNbhd X p.1) p.2
    refine ⟨prod_mem_prodNbhd hX (hL p hp).1, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact (rel_stepFun_iff h hX hL).mp hrel p hp

/-- **Theorem 3.12(ii) (Scott 1981, PRG-19).** `eval ∘ ⟨curry(g) ∘ p₀, p₁⟩ = g`. -/
theorem eval_comp_curry (g : ApproximableMap (prod V₀ V₁) V₂) :
    (evalMap V₁ V₂).comp (paired ((curry g).comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁)) = g := by
  rw [← uncurry_eq]; exact uncurry_curry g

/-- **Theorem 3.12(iii) (Scott 1981, PRG-19).** `curry (eval ∘ ⟨h ∘ p₀, p₁⟩) = h`. -/
theorem curry_eval_comp (h : ApproximableMap V₀ (funSpace V₁ V₂)) :
    curry ((evalMap V₁ V₂).comp (paired (h.comp (proj₀ V₀ V₁)) (proj₁ V₀ V₁))) = h := by
  rw [← uncurry_eq, curry_uncurry]

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry` is an order-isomorphism between
`|𝒟₀ × 𝒟₁ → 𝒟₂|` and `|𝒟₀ → (𝒟₁ → 𝒟₂)|`. -/
def curryEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry
  map_rel_iff' := by
    intro g g'
    constructor
    · intro hcurry W Z hrel
      have h1 : (curry g).rel (Sum.inl ⁻¹' W) (step (Sum.inr ⁻¹' W) Z) := by
        have hu : (uncurry (curry g)).rel W Z := by rw [uncurry_curry]; exact hrel
        exact hu.2
      have h2 := hcurry _ _ h1
      have hu' : (uncurry (curry g')).rel W Z := ⟨g.rel_dom hrel, h2⟩
      rw [uncurry_curry] at hu'
      exact hu'
    · intro hg X W hrel
      obtain ⟨hX, hW, hmem⟩ := hrel
      refine ⟨hX, hW, ?_⟩
      obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
      intro p hp
      have hgrel : g.rel (prodNbhd X p.1) p.2 := hmem p hp
      exact hg _ _ hgrel

end Domain.Neighborhood
