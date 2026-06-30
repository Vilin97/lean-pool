/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Example44
import LeanPool.DomainTheory.Neighborhood.Exercise326

/-!
# Exercise 4.19 (Scott 1981, PRG-19, Lecture IV) — verifying Example 4.4

Example 4.4 leaves many assertions to the reader. This module discharges the two
explicitly
requested ones:

* **"Peano's Axioms" for `{0,1}*`.** The structured set `⟨Σ*, Λ, 0·, 1·⟩` (here
`Σ* = List Bool`,
  `Λ = []`, and the two successors `b ↦ b :: ·`) satisfies the natural
  two-successor analogue of
  Definition 4.5: `Λ` is not a successor (`peano_nil_ne_cons`), each successor is
  injective
  (`peano_cons_injective`), the two successor ranges are disjoint
  (`peano_cons_disjoint`), and the
  *induction* principle holds (`peano_induction`). So `Σ*` is the free monoid on
  two generators —
  the binary-tree analogue of `⟨ℕ, 0, ⁺⟩`.

* **`one : C → T` is definable from the rest of the structure by a fixed-point
equation.** We first
  build the three tests `empty, zero, one : C → T` as honest approximable maps
  (Scott: "it is an
  exercise to show these are approximable"), via a uniform *head-test* combinator
  `liftC`. We then
  show

  `one(x) = cond(empty(x), false, cond(zero(x), false, true))`

  on every generator of `|C|` (`one_def_strElem`, `one_def_strBot`), exhibiting
  `one` as the
  solution of a fixed-point/recursion equation in the remaining structure `⟨C, Λ,
  0, 1, empty,
  zero, cond⟩` (the right-hand side does not mention `one`, so this is the trivial
  fixed point —
  Scott's point that the tests are not independent).

The `liftC` combinator (a map `C → V` determined by its values on the partial
elements `σ⊥` and the
total elements `σ`, subject to two monotonicity conditions) is reusable; with it
one likewise gets
Scott's `tail : C → C` (`tail(bx) = x`, `tail(Λ) = ⊥`), here noted but not needed
for `one`.

The `liftC` *data* is **choice-free**; the truth-domain tests inherit
`Classical.choice`
structurally from `T` (Example 1.2), exactly as `Example23.parityMap` and
`Example43.zeroMap` do.
-/

namespace Domain.Neighborhood.Exercise419

open Domain.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44

/-! ### "Peano's Axioms" for `{0,1}* = List Bool`. -/

/-- **Exercise 4.19 — Peano (i) for `{0,1}*`.** `Λ` is not a successor: `[] ≠ b ::
σ`. -/
theorem peano_nil_ne_cons (b : Bool) (σ : Str) : ([] : Str) ≠ b :: σ := by
  simp

/-- **Exercise 4.19 — Peano (ii) for `{0,1}*`.** Each successor `b ::·` is
injective. -/
theorem peano_cons_injective {b : Bool} {σ τ : Str} (h : b :: σ = b :: τ) : σ = τ :=
  (List.cons.injEq b σ b τ).mp h |>.2

/-- **Exercise 4.19 — Peano (ii′) for `{0,1}*`.** The two successor ranges are
disjoint:
`0σ ≠ 1τ`. -/
theorem peano_cons_disjoint (σ τ : Str) : (false :: σ) ≠ (true :: τ) := by
  simp

/-- **Exercise 4.19 — Peano (iii) for `{0,1}*`.** Induction: a predicate holding
at `Λ` and closed
under both successors holds everywhere. (This is `List.rec`; it is the
two-successor analogue of
Definition 4.5(iii) and the recursion engine behind `tail`/`empty`/`zero`/`one`.) -/
theorem peano_induction (P : Str → Prop) (hnil : P []) (hcons : ∀ b σ, P σ → P (b :: σ)) :
    ∀ σ, P σ := by
  intro σ
  induction σ with
  | nil => exact hnil
  | cons b σ ih => exact hcons b σ ih

/-! ### Disjointness facts for `C`'s neighbourhoods (cones vs singletons). -/

/-- A cone is never contained in a singleton (it has at least two elements). -/
theorem not_cone_subset_singleton (τ σ : Str) : ¬ cone τ ⊆ ({σ} : Set Str) := by
  intro h
  have h1 : τ ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  have h2 : (τ ++ [true]) ∈ ({σ} : Set Str) := h (by simp [mem_cone])
  rw [Set.mem_singleton_iff] at h1 h2
  have : τ = τ ++ [true] := h1.trans h2.symm
  simp at this

/-- A cone is never equal to a singleton. -/
theorem cone_ne_singleton (τ σ : Str) : cone τ ≠ ({σ} : Set Str) := by
  intro h
  exact not_cone_subset_singleton τ σ (h ▸ subset_rfl)

/-! ### The head-test value functions. -/

variable {β : Type*}

/-- The codomain value chosen by inspecting the head of a sequence: `[] ↦ z`, `0σ
↦ a₀`, `1σ ↦ a₁`.
With `z = ⊥` this is the value at the *partial* element `σ⊥`; with `z = vΛ` the
value at the
*total* element `σ`. -/
def headValC (V : NeighborhoodSystem β) (z a0 a1 : V.Element) : Str → V.Element
  | [] => z
  | false :: _ => a0
  | true :: _ => a1

@[simp] theorem headValC_nil (V : NeighborhoodSystem β) (z a0 a1 : V.Element) :
    headValC V z a0 a1 [] = z := rfl
@[simp] theorem headValC_false (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (false :: σ) = a0 := rfl
@[simp] theorem headValC_true (V : NeighborhoodSystem β) (z a0 a1 : V.Element) (σ : Str) :
    headValC V z a0 a1 (true :: σ) = a1 := rfl

/-- Monotonicity of the head value: along a prefix `σ <+: τ`, the *partial* value
(`z = ⊥`) at `σ`
is below *any* head value at `τ` with the same head constants. Covers both
required conditions
(cone→cone with `z' = ⊥`, cone→singleton with `z' = vΛ`). -/
theorem headValC_bot_le (V : NeighborhoodSystem β) (z' a0 a1 : V.Element) {σ τ : Str}
    (h : σ <+: τ) : headValC V V.bot a0 a1 σ ≤ headValC V z' a0 a1 τ := by
  cases σ with
  | nil => exact bot_le
  | cons b σ0 =>
    obtain ⟨s, rfl⟩ := h
    cases b
    · rw [List.cons_append]; exact le_of_eq rfl
    · rw [List.cons_append]; exact le_of_eq rfl

/-! ### The combinator `liftC`: an approximable map out of `C`. -/

/-- A map `C → V` determined by its value `coneVal σ` on each partial element `σ⊥`
and `singVal σ`
on each total element `σ`, provided (a) the partial values are monotone along
prefixes and (b) a
partial value sits below the total value of any extending prefix. The relation
says: a cone `σΣ*`
relates to the neighbourhoods of `coneVal σ`, and a singleton `{σ}` to those of
`singVal σ`. -/
def liftC (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) :
    ApproximableMap C V where
  rel X Y := (∃ σ, X = cone σ ∧ (coneVal σ).mem Y) ∨ (∃ σ, X = {σ} ∧ (singVal σ).mem Y)
  rel_dom := by
    rintro X Y (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_cod := by
    rintro X Y (⟨σ, _, hY⟩ | ⟨σ, _, hY⟩)
    · exact (coneVal σ).sub hY
    · exact (singVal σ).sub hY
  master_rel := by
    refine Or.inl ⟨[], ?_, (coneVal []).master_mem⟩
    rw [C_master]; exact cone_nil.symm
  inter_right := by
    rintro X Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) (⟨σ', hX', hY'⟩ | ⟨σ', hX', hY'⟩)
    · have : σ = σ' := cone_injective hX'
      subst this
      exact Or.inl ⟨σ, rfl, (coneVal σ).inter_mem hY hY'⟩
    · exact absurd hX' (cone_ne_singleton σ σ')
    · exact absurd hX'.symm (cone_ne_singleton σ' σ)
    · have : σ = σ' := by rw [Set.singleton_eq_singleton_iff] at hX'; exact hX'
      subst this
      exact Or.inr ⟨σ, rfl, (singVal σ).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨σ, rfl, hY⟩ | ⟨σ, rfl, hY⟩) hX'X hYY' hX' hY'
    · -- input is the cone `σΣ*`
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · -- `X' = cone τ ⊆ cone σ`, so `σ <+: τ`
        have hpre : σ <+: τ := cone_subset_cone.mp hX'X
        exact Or.inl ⟨τ, rfl, (coneVal τ).up_mem (hcone hpre Y hY) hY' hYY'⟩
      · -- `X' = {τ} ⊆ cone σ`, so `σ <+: τ`
        have hpre : σ <+: τ := singleton_subset_cone.mp hX'X
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem (hsing hpre Y hY) hY' hYY'⟩
    · -- input is the singleton `{σ}`
      rcases hX' with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
      · exact absurd hX'X (not_cone_subset_singleton τ σ)
      · have hτσ : τ = σ := by
          have := Set.singleton_subset_iff.mp hX'X
          rwa [Set.mem_singleton_iff] at this
        subst hτσ
        exact Or.inr ⟨τ, rfl, (singVal τ).up_mem hY hY' hYY'⟩

/-- `liftC` on a partial element: `f(σ⊥) = coneVal σ`. -/
theorem liftC_strBot (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strBot σ) = coneVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := cone_subset_cone.mp (hXcone ▸ hsub)
      exact hcone hpre Y hY
    · exact absurd (hXsing ▸ hsub) (not_cone_subset_singleton σ σ')
  · intro hY
    exact ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, Or.inl ⟨σ, rfl, hY⟩⟩

/-- `liftC` on a total element: `f(σ) = singVal σ`. -/
theorem liftC_strElem (V : NeighborhoodSystem β) (coneVal singVal : Str → V.Element)
    (hcone : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ coneVal τ)
    (hsing : ∀ {σ τ : Str}, σ <+: τ → coneVal σ ≤ singVal τ) (σ : Str) :
    (liftC V coneVal singVal hcone hsing).toElementMap (strElem σ) = singVal σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨_, hsub⟩, hrel⟩
    rcases hrel with ⟨σ', hXcone, hY⟩ | ⟨σ', hXsing, hY⟩
    · have hpre : σ' <+: σ := by
        apply singleton_subset_cone.mp
        rw [← hXcone]; exact hsub
      exact hsing hpre Y hY
    · have hσσ' : σ = σ' := by
        have := Set.singleton_subset_iff.mp (hXsing ▸ hsub)
        rwa [Set.mem_singleton_iff] at this
      subst hσσ'; exact hY
  · intro hY
    exact ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, Or.inr ⟨σ, rfl, hY⟩⟩

/-! ### The three tests `empty, zero, one : C → T`. -/

/-- The truth domain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example23.T

local notation "𝕥" => Example23.trueElt
local notation "𝕗" => Example23.falseElt

/-- **Example 4.4 — `empty`.** `empty(Λ) = true`, `empty(0x) = empty(1x) = false`,
strict. -/
def emptyMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗)

/-- **Example 4.4 — `zero`.** `zero(Λ) = false`, `zero(0x) = true`, `zero(1x) =
false`, strict. -/
def zeroMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗)

/-- **Example 4.4 — `one`.** `one(Λ) = false`, `one(0x) = false`, `one(1x) =
true`, strict. -/
def oneMap : ApproximableMap C T :=
  liftC T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥)

/-! Value equations on total elements `σ` and partial elements `σ⊥`. -/

@[simp] theorem emptyMap_strElem (σ : Str) :
    emptyMap.toElementMap (strElem σ) = headValC T 𝕥 𝕗 𝕗 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗) σ
@[simp] theorem emptyMap_strBot (σ : Str) :
    emptyMap.toElementMap (strBot σ) = headValC T T.bot 𝕗 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕗 𝕗) (headValC T 𝕥 𝕗 𝕗)
    (headValC_bot_le T T.bot 𝕗 𝕗) (headValC_bot_le T 𝕥 𝕗 𝕗) σ
@[simp] theorem zeroMap_strElem (σ : Str) :
    zeroMap.toElementMap (strElem σ) = headValC T 𝕗 𝕥 𝕗 σ :=
  liftC_strElem T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ
@[simp] theorem zeroMap_strBot (σ : Str) :
    zeroMap.toElementMap (strBot σ) = headValC T T.bot 𝕥 𝕗 σ :=
  liftC_strBot T (headValC T T.bot 𝕥 𝕗) (headValC T 𝕗 𝕥 𝕗)
    (headValC_bot_le T T.bot 𝕥 𝕗) (headValC_bot_le T 𝕗 𝕥 𝕗) σ
@[simp] theorem oneMap_strElem (σ : Str) :
    oneMap.toElementMap (strElem σ) = headValC T 𝕗 𝕗 𝕥 σ :=
  liftC_strElem T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ
@[simp] theorem oneMap_strBot (σ : Str) :
    oneMap.toElementMap (strBot σ) = headValC T T.bot 𝕗 𝕥 σ :=
  liftC_strBot T (headValC T T.bot 𝕗 𝕥) (headValC T 𝕗 𝕗 𝕥)
    (headValC_bot_le T T.bot 𝕗 𝕥) (headValC_bot_le T 𝕗 𝕗 𝕥) σ

/-! ### `one` is defined from `empty`, `zero` and `cond` by a fixed-point
equation. -/

/-- `cond(⊥, x, y) = ⊥` in `T`, phrased with `T.bot` (which the head-test
`empty(⊥)` produces)
rather than the syntactically distinct `Example23.botElt` of
`Exercise326.cond_bot`. -/
theorem condT_bot (x y : T.Element) :
    (Exercise326.cond T).toElementMap (pair T.bot (pair x y)) = T.bot := by
  apply Element.ext
  intro Z
  rw [Exercise326.cond_toElementMap_mem]
  constructor
  · rintro (⟨h0, _⟩ | ⟨h1, _⟩ | rfl)
    · rw [NeighborhoodSystem.mem_bot] at h0; exact absurd h0 Exercise326.zero_ne_master
    · rw [NeighborhoodSystem.mem_bot] at h1; exact absurd h1 Exercise326.one_ne_master
    · exact T.bot.master_mem
  · intro h
    rw [NeighborhoodSystem.mem_bot] at h
    exact Or.inr (Or.inr h)

/-- The defining right-hand side: `cond(empty(x), false, cond(zero(x), false,
true))`. It uses only
`empty`, `zero` and the conditional `cond` (Exercise 3.26) — not `one`. -/
def oneDef (x : C.Element) : T.Element :=
  (Exercise326.cond T).toElementMap
    (pair (emptyMap.toElementMap x)
      (pair 𝕗
        ((Exercise326.cond T).toElementMap (pair (zeroMap.toElementMap x) (pair 𝕗 𝕥)))))

/-- **Exercise 4.19 (Scott 1981, PRG-19).** `one` is definable from `empty`,
`zero`, `cond`: the
equation `one(x) = cond(empty(x), false, cond(zero(x), false, true))` holds on
every total element
`σ`. -/
theorem one_def_strElem (σ : Str) : oneMap.toElementMap (strElem σ) = oneDef (strElem σ) := by
  cases σ with
  | nil =>
    -- empty(Λ)=true ⟹ cond picks `false`
    rw [oneDef, emptyMap_strElem, headValC_nil, Exercise326.cond_true,
      oneMap_strElem, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      -- empty=false ⟹ inner cond; zero(0σ)=true ⟹ inner cond picks `false`
      rw [oneDef, emptyMap_strElem, headValC_false, Exercise326.cond_false,
        zeroMap_strElem, headValC_false, Exercise326.cond_true, oneMap_strElem, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strElem, headValC_true, Exercise326.cond_false,
        zeroMap_strElem, headValC_true, Exercise326.cond_false, oneMap_strElem, headValC_true]

/-- **Exercise 4.19 (Scott 1981, PRG-19).** The same defining equation holds on
every partial
element `σ⊥` — including `⊥ = []⊥` where `empty(⊥) = ⊥` forces `cond(⊥, …) = ⊥`. -/
theorem one_def_strBot (σ : Str) : oneMap.toElementMap (strBot σ) = oneDef (strBot σ) := by
  cases σ with
  | nil =>
    rw [oneDef, emptyMap_strBot, headValC_nil, condT_bot, oneMap_strBot, headValC_nil]
  | cons b σ0 =>
    cases b with
    | false =>
      rw [oneDef, emptyMap_strBot, headValC_false, Exercise326.cond_false,
        zeroMap_strBot, headValC_false, Exercise326.cond_true, oneMap_strBot, headValC_false]
    | true =>
      rw [oneDef, emptyMap_strBot, headValC_true, Exercise326.cond_false,
        zeroMap_strBot, headValC_true, Exercise326.cond_false, oneMap_strBot, headValC_true]

end Domain.Neighborhood.Exercise419
