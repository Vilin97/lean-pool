/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Example23
import LeanPool.DomainTheory.Neighborhood.Theorem41

/-!
# Example 4.3 (Scott 1981, PRG-19, §4) — the natural-number domain `N`

Scott's "THE domain of integers" (pages 57–61). The tokens are `ℕ`, and the
neighbourhoods are

`N = {{n} ∣ n ∈ ℕ} ∪ {ℕ}`

— a *flat* domain: the singletons `{n}` are the finite total elements and the
whole space `ℕ`
is the least-informative neighbourhood `Δ = ⊥`. We build `N` by the
nested-or-disjoint criterion
(`ofNestedOrDisjoint`): any two neighbourhoods are nested (one is `ℕ`) or disjoint
(distinct
singletons).

The (ideal) elements of `|N|` are exactly: the bottom `⊥ = {ℕ}` ("undefined"), and
for each `n`
the total element `n̂ = ↑{n} = {{n}, ℕ}` (`natElem n`). Scott then equips `N` with
the structure
maps

* `succ, pred : N → N`     (`succMap`, `predMap`)
* `zero : N → T`           (`zeroMap`, into the truth domain `T` of Example 1.2),

making `⟨N, 0, succ, pred, zero⟩` "THE domain of integers". All three are *strict*
approximable
maps determined by their action on the finite total elements:

* `succ(n̂) = (n+1)^`,            `succ(⊥) = ⊥`;
* `pred((n+1)^) = n̂`, `pred(0̂) = ⊥`, `pred(⊥) = ⊥`;
* `zero(0̂) = true`, `zero((n+1)^) = false`, `zero(⊥) = ⊥`.

We capture the common shape — a map `N → V` sending `n̂ ↦ val n` and `⊥ ↦ ⊥` —
once and for all in
the combinator `constLiftN`, whose computation rules
`constLiftN_natElem`/`constLiftN_bot` give all
of the displayed equations uniformly. The data (`N`, `constLiftN`, `succMap`,
`predMap`) is
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); `zeroMap` inherits
`Classical.choice`
structurally from the truth domain `T` of Example 1.2 exactly as
`Example23.parityMap` does.
-/

namespace Domain.Neighborhood.Example43

open Domain.Neighborhood NeighborhoodSystem ApproximableMap

/-! ### The neighbourhood system `N`. -/

/-- Membership in Scott's natural-number system: a neighbourhood is the whole
space `ℕ` or a
singleton `{n}`. -/
def memN (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

theorem memN_univ : memN (Set.univ : Set ℕ) := Or.inl rfl

theorem memN_singleton (n : ℕ) : memN ({n} : Set ℕ) := Or.inr ⟨n, rfl⟩

/-- `ℕ` is not a singleton (a witness `n+1 ≠ n`). -/
theorem univ_ne_singleton (n : ℕ) : (Set.univ : Set ℕ) ≠ {n} := by
  intro h
  have h1 : (n + 1) ∈ ({n} : Set ℕ) := h ▸ Set.mem_univ (n + 1)
  exact Nat.succ_ne_self n h1

/-- `{n} ≠ ℕ` (the symmetric form). -/
theorem singleton_ne_univ (n : ℕ) : ({n} : Set ℕ) ≠ Set.univ := fun h => univ_ne_singleton n h.symm

/-- Singletons of naturals are one-one as sets. -/
theorem singleton_nat_inj {n m : ℕ} (h : ({n} : Set ℕ) = {m}) : n = m := by
  have h1 : n ∈ ({n} : Set ℕ) := rfl
  rw [h] at h1
  exact h1

/-- Any two neighbourhoods of `N` are nested or disjoint: `ℕ` contains every
singleton, and two
distinct singletons are disjoint. -/
theorem nestedOrDisjoint : NestedOrDisjoint memN := by
  rintro X Y (rfl | ⟨n, rfl⟩) (rfl | ⟨m, rfl⟩)
  · exact Or.inl (Set.Subset.refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · by_cases h : n = m
    · subst h; exact Or.inl (Set.Subset.refl _)
    · refine Or.inr (Or.inr ?_)
      ext k
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl hkm
      exact h hkm

/-- **Example 4.3 (Scott 1981, PRG-19).** The natural-number neighbourhood system
`N` on `Δ = ℕ`. -/
def N : NeighborhoodSystem ℕ :=
  NeighborhoodSystem.ofNestedOrDisjoint memN Set.univ memN_univ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

@[simp] theorem N_mem {X : Set ℕ} : N.mem X ↔ memN X := Iff.rfl

@[simp] theorem N_master : N.master = (Set.univ : Set ℕ) := rfl

/-- `⊥ ∈ N` reads: a neighbourhood lies in `⊥` iff it is the whole space `ℕ`. -/
theorem N_bot_mem {X : Set ℕ} : N.bot.mem X ↔ X = Set.univ := NeighborhoodSystem.mem_bot N

/-! ### The total elements `n̂`. -/

/-- Scott's total element `n̂ = ↑{n} = {{n}, ℕ}`, the principal filter of the
singleton `{n}`. -/
def natElem (n : ℕ) : N.Element := N.principal (memN_singleton n)

/-- A neighbourhood belongs to `n̂` iff it is `ℕ` (the master) or the singleton
`{n}`. -/
theorem mem_natElem_iff {n : ℕ} {Y : Set ℕ} :
    (natElem n).mem Y ↔ Y = Set.univ ∨ Y = {n} := by
  unfold natElem
  rw [mem_principal]
  constructor
  · rintro ⟨hY, hsub⟩
    rcases hY with rfl | ⟨m, rfl⟩
    · exact Or.inl rfl
    · have hnm : n = m := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hsub)
      subst hnm; exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨memN_univ, Set.subset_univ _⟩
    · exact ⟨memN_singleton n, subset_rfl⟩

/-- Scott's `0 ∈ |N|`, the distinguished zero of the structured domain. -/
def zeroElt : N.Element := natElem 0

/-! ### The strict lifting combinator `n̂ ↦ val n`, `⊥ ↦ ⊥`. -/

/-- The *strict* approximable map `N → V` determined by a choice of value `val n ∈
|V|` for each
`n`: it sends the total element `n̂` to `val n` and the bottom `⊥` to `⊥`. The
relation
`X f Y` holds when either `X = Δ_N` forces the blunt output `Y = Δ_V` (the strict
`⊥ ↦ ⊥` clause),
or `X = {n}` and `Y` is a neighbourhood of `val n`.

Definition 2.1 checks uniformly: (i) `Δ_N f Δ_V`; (ii) intersect outputs —
distinct inputs are
impossible (`ℕ ≠ {n}`, singletons are one-one), so both outputs come from the
*same* `val n` and
`inter_mem` of the filter `val n` applies; (iii) sharpening `{n} ⊆ X` keeps the
input a singleton
`{n}`, and `up_mem` of `val n` widens the output, while a blunt input `Δ_N` forces
`Δ_V`. -/
def constLiftN {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) :
    ApproximableMap N V where
  rel X Y := (X = Set.univ ∧ Y = V.master) ∨ (∃ n, X = {n} ∧ (val n).mem Y)
  rel_dom := by
    rintro X Y (⟨rfl, _⟩ | ⟨n, rfl, _⟩)
    · exact memN_univ
    · exact memN_singleton n
  rel_cod := by
    rintro X Y (⟨_, rfl⟩ | ⟨n, _, hY⟩)
    · exact V.master_mem
    · exact (val n).sub hY
  master_rel := Or.inl ⟨rfl, rfl⟩
  inter_right := by
    rintro X Y Y' (⟨rfl, rfl⟩ | ⟨n, rfl, hY⟩) hc'
    · rcases hc' with ⟨_, rfl⟩ | ⟨n, hX, _⟩
      · exact Or.inl ⟨rfl, by rw [Set.inter_self]⟩
      · exact (univ_ne_singleton n hX).elim
    · rcases hc' with ⟨hX, _⟩ | ⟨n', hX', hY'⟩
      · exact (singleton_ne_univ n hX).elim
      · have hnn' : n = n' := singleton_nat_inj hX'
        subst hnn'
        exact Or.inr ⟨n, rfl, (val n).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' (⟨rfl, rfl⟩ | ⟨n, rfl, hY⟩) hX'X hYY' hX' hY'
    · have hY'master : Y' = V.master := Set.Subset.antisymm (V.sub_master hY') hYY'
      subst hY'master
      rcases hX' with rfl | ⟨k, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨k, rfl, (val k).master_mem⟩
    · rcases hX' with rfl | ⟨k, rfl⟩
      · exact (singleton_ne_univ n (Set.univ_subset_iff.mp hX'X)).elim
      · have hkn : k = n := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hX'X)
        subst hkn
        exact Or.inr ⟨k, rfl, (val k).up_mem hY hY' hYY'⟩

/-- **Computation on the total elements.** `f(n̂) = val n`. -/
theorem constLiftN_natElem {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) (n : ℕ) :
    (constLiftN V val).toElementMap (natElem n) = val n := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [mem_natElem_iff] at hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, hY⟩
    · exact (val n).master_mem
    · rcases hXmem with rfl | rfl
      · exact (univ_ne_singleton k hXk).elim
      · have hnk : n = k := singleton_nat_inj hXk
        subst hnk; exact hY
  · intro hY
    exact ⟨{n}, mem_natElem_iff.mpr (Or.inr rfl), Or.inr ⟨n, rfl, hY⟩⟩

/-- **Computation on bottom (strictness).** `f(⊥) = ⊥`. -/
theorem constLiftN_bot {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) :
    (constLiftN V val).toElementMap N.bot = V.bot := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [N_bot_mem] at hXmem
    subst hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, _⟩
    · exact V.mem_bot.mpr rfl
    · exact (univ_ne_singleton k hXk).elim
  · intro hY
    rw [V.mem_bot] at hY
    subst hY
    exact ⟨Set.univ, N_bot_mem.mpr rfl, Or.inl ⟨rfl, rfl⟩⟩

/-! ### The successor map `succ : N → N`. -/

/-- **Example 4.3 — `succ`.** `succ(n) = n + 1`, strict (`succ(⊥) = ⊥`). -/
def succMap : ApproximableMap N N := constLiftN N (fun n => natElem (n + 1))

/-- `succ(n̂) = (n+1)^`. -/
theorem succMap_natElem (n : ℕ) : succMap.toElementMap (natElem n) = natElem (n + 1) :=
  constLiftN_natElem N (fun n => natElem (n + 1)) n

/-- `succ(⊥) = ⊥`. -/
theorem succMap_bot : succMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N (fun n => natElem (n + 1))

/-! ### The predecessor map `pred : N → N`. -/

/-- The value table for `pred`: `pred(0) = ⊥`, `pred(k+1) = k`. -/
def predVal : ℕ → N.Element
  | 0 => N.bot
  | (k + 1) => natElem k

/-- **Example 4.3 — `pred`.** `pred(0) = ⊥`, `pred(n+1) = n`, strict (`pred(⊥) =
⊥`). -/
def predMap : ApproximableMap N N := constLiftN N predVal

/-- `pred((n+1)^) = n̂`. -/
theorem predMap_natElem_succ (k : ℕ) : predMap.toElementMap (natElem (k + 1)) = natElem k :=
  constLiftN_natElem N predVal (k + 1)

/-- `pred(0̂) = ⊥`: predecessor of zero is undefined. -/
theorem predMap_natElem_zero : predMap.toElementMap (natElem 0) = N.bot :=
  constLiftN_natElem N predVal 0

/-- `pred(⊥) = ⊥`. -/
theorem predMap_bot : predMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N predVal

/-! ### The test map `zero : N → T`. -/

/-- The two-token truth domain `T` of Example 1.2 (= `Example23.T`). -/
abbrev T : NeighborhoodSystem Example12.Token := Example23.T

/-- The value table for `zero`: `zero(0) = true`, `zero(n+1) = false`. -/
def zeroVal : ℕ → T.Element
  | 0 => Example23.trueElt
  | (_ + 1) => Example23.falseElt

/-- **Example 4.3 — `zero`.** `zero(0) = true`, `zero(n+1) = false`, strict
(`zero(⊥) = ⊥`). -/
def zeroMap : ApproximableMap N T := constLiftN T zeroVal

/-- `zero(0̂) = true`. -/
theorem zeroMap_natElem_zero : zeroMap.toElementMap (natElem 0) = Example23.trueElt :=
  constLiftN_natElem T zeroVal 0

/-- `zero((n+1)^) = false`. -/
theorem zeroMap_natElem_succ (n : ℕ) : zeroMap.toElementMap (natElem (n +
  1)) = Example23.falseElt :=
  constLiftN_natElem T zeroVal (n + 1)

/-- `zero(⊥) = ⊥`. -/
theorem zeroMap_bot : zeroMap.toElementMap N.bot = T.bot :=
  constLiftN_bot T zeroVal

/-! ### `pred` undoes `succ`. -/

/-- `pred(succ(n̂)) = n̂`: the predecessor undoes the successor on total elements.
(A sample of the
"recursion" reasoning Scott highlights; cf. the iterated-summation example.) -/
theorem predMap_succMap_natElem (n : ℕ) :
    predMap.toElementMap (succMap.toElementMap (natElem n)) = natElem n := by
  rw [succMap_natElem, predMap_natElem_succ]

end Domain.Neighborhood.Example43
