/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise118
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.NormNum

/-!
# Exercise 1.27 (Scott 1981, PRG-19, §1) — bounded sets and least upper bounds

Scott introduces *bounded* sets of elements as the analogue, for `|𝒟|`, of
*consistent*
sequences of neighbourhoods. A set `X ⊆ |𝒟|` is **bounded** iff it has an upper
bound
`y ∈ |𝒟|` (`x ⊑ y` for all `x ∈ X`), and then

`⊔X = ⋂ {y ∣ x ⊑ y for all x ∈ X}`

is its **least upper bound**. This file formalizes:

* `Bounded X` and `sSup X hX := sInf (upper bounds of X)` — the upper-bound family
is non-empty
  exactly because `X` is bounded, so we reuse `sInf` from Exercise 1.18; the lub
  laws
  `le_sSup` / `sSup_le` are then immediate from `le_sInf` / `sInf_le`;
* `consistent_pair_iff_bounded` — for `U, W ∈ 𝒟`, the pair `⟨U, W⟩` is
`Consistent` iff
  `{↑U, ↑W}` is bounded ("boundedness is for elements what consistency is for
  neighbourhoods");
* `bounded_iff_finite_bounded` — **with the aid of Exercise 1.18**, `X` is bounded
iff every
  *finite* subset of `X` is bounded; the hard direction builds the bound as the
  `leastFilter`
  of `C = ⋃_{x∈X} x`, whose finite consistency comes from the finite bounds.

The constructions (`sSup`) are `[propext, Quot.sound]`. The hard direction of
`bounded_iff_finite_bounded` selects a finite witness set via `Classical.choice`;
this is a
*proof*, so the construction stays choice-free.
-/

namespace Domain.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.27 — bounded set of elements.** `X ⊆ |𝒟|` is *bounded* iff it has
an upper
bound `y ∈ |𝒟|`: `x ⊑ y` for all `x ∈ X`. -/
def Bounded (X : Set V.Element) : Prop := ∃ y : V.Element, ∀ x ∈ X, x ≤ y

/-- The family of upper bounds of `X`: `{y ∣ x ⊑ y for all x ∈ X}`. -/
def upperBounds (X : Set V.Element) : Set V.Element := {y | ∀ x ∈ X, x ≤ y}

/-- If `X` is bounded then its upper-bound family is non-empty (it contains the
witness). -/
theorem upperBounds_nonempty {X : Set V.Element} (hX : V.Bounded X) :
    (V.upperBounds X).Nonempty :=
  hX.imp fun _ hy => hy

/-- **Exercise 1.27 — `⊔X`.** The least upper bound of a bounded `X`, defined à la
Scott as the
intersection of all upper bounds: `⊔X = ⋂ {y ∣ x ⊑ y all x∈X}`. Reusing `sInf`
from Exercise
1.18 on the (non-empty, because bounded) family of upper bounds. -/
def sSup (X : Set V.Element) (hX : V.Bounded X) : V.Element :=
  V.sInf (V.upperBounds X) (V.upperBounds_nonempty hX)

/-- **Exercise 1.27 — `⊔X` is an upper bound.** Each `x ∈ X` satisfies `x ⊑ ⊔X`. -/
theorem le_sSup (X : Set V.Element) (hX : V.Bounded X) {x : V.Element} (hx : x ∈ X) :
    x ≤ V.sSup X hX :=
  V.le_sInf (V.upperBounds X) (V.upperBounds_nonempty hX) x (fun _ hy => hy x hx)

/-- **Exercise 1.27 — `⊔X` is least.** Any upper bound `z` of `X` satisfies `⊔X ⊑
z`. -/
theorem sSup_le (X : Set V.Element) (hX : V.Bounded X) {z : V.Element}
    (hz : ∀ x ∈ X, x ≤ z) : V.sSup X hX ≤ z :=
  V.sInf_le (V.upperBounds X) (V.upperBounds_nonempty hX) hz

/-! ### Boundedness of `{↑U, ↑W}` iff consistency of `⟨U, W⟩`. -/

/-- The two-term sequence `⟨U, W⟩` as a function `ℕ → Set α` (used to phrase
`Consistent`). -/
def pairSeq (U W : Set α) : ℕ → Set α := fun i => if i = 0 then U else W

theorem interUpTo_pairSeq (U W : Set α) :
    V.interUpTo (pairSeq U W) 2 = V.master ∩ U ∩ W := by
  simp only [interUpTo_succ, interUpTo_zero, pairSeq]
  norm_num

/-- **Exercise 1.27 — "boundedness is for elements what consistency is for
neighbourhoods".**
For `U, W ∈ 𝒟`, the pair `⟨U, W⟩` is consistent in `𝒟` iff `{↑U, ↑W}` is bounded
in `|𝒟|`.

`→` packages the consistency witness `Z` into the principal filter `↑Z`, which
lies above both
`↑U` and `↑W` (via `principal_le_iff`). `←` uses that any bound `y` contains both
`U` and `W`,
hence `U ∩ W ∈ y ⊆ 𝒟`, giving `U ∩ W` as the consistency witness. -/
theorem consistent_pair_iff_bounded {U W : Set α} (hU : V.mem U) (hW : V.mem W) :
    V.Consistent (pairSeq U W) 2 ↔ V.Bounded {V.principal hU, V.principal hW} := by
  constructor
  · rintro ⟨Z, hZmem, hZsub⟩
    rw [V.interUpTo_pairSeq] at hZsub
    have hZU : Z ⊆ U := hZsub.trans (Set.inter_subset_left.trans Set.inter_subset_right)
    have hZW : Z ⊆ W := hZsub.trans Set.inter_subset_right
    refine ⟨V.principal hZmem, ?_⟩
    intro x hx
    rcases hx with rfl | rfl
    · exact (V.principal_le_iff hU hZmem).mpr hZU
    · exact (V.principal_le_iff hW hZmem).mpr hZW
  · rintro ⟨y, hy⟩
    have hyU : y.mem U :=
      hy _ (Or.inl rfl) U ⟨hU, subset_rfl⟩
    have hyW : y.mem W :=
      hy _ (Or.inr rfl) W ⟨hW, subset_rfl⟩
    have hyUW : y.mem (U ∩ W) := y.inter_mem hyU hyW
    refine ⟨U ∩ W, y.sub hyUW, ?_⟩
    rw [V.interUpTo_pairSeq]
    intro z hz
    exact ⟨⟨V.sub_master hU hz.1, hz.1⟩, hz.2⟩

/-! ### Boundedness is finitary (with the aid of Exercise 1.18). -/

/-- **Exercise 1.27 — boundedness is finitary.** `X ⊆ |𝒟|` is bounded iff every
*finite* subset
of `X` is bounded. The forward direction reuses any global bound. The reverse
direction is the
content: assemble `C = ⋃_{x∈X} x` (the neighbourhoods of all members of `X`); `C`
is finitely
consistent because any finite sequence drawn from `C` comes from finitely many
members of `X`,
which form a finite subset, hence bounded — that bound's filter contains the whole
finite
sequence, so its intersection lies in `𝒟`. The least filter `leastFilter C`
(Exercise 1.18) is
then an upper bound of `X`. -/
theorem bounded_iff_finite_bounded (X : Set V.Element) :
    V.Bounded X ↔ ∀ S : Set V.Element, S ⊆ X → S.Finite → V.Bounded S := by
  constructor
  · rintro ⟨y, hy⟩ S hS _
    exact ⟨y, fun x hx => hy x (hS hx)⟩
  · intro hfin
    set C : Set (Set α) := {Z | ∃ x : V.Element, x ∈ X ∧ x.mem Z} with hCdef
    have hCsub : ∀ Z ∈ C, V.mem Z := by rintro Z ⟨x, _, hxZ⟩; exact x.sub hxZ
    have hCcons : V.FinitelyConsistent C := by
      intro n seq hseqC
      choose g hgX hgmem using hseqC
      set S : Set V.Element := Set.range (fun i : Fin n => g i.1 i.2) with hSdef
      have hSfin : S.Finite := Set.finite_range _
      have hSsub : S ⊆ X := by
        rintro _ ⟨i, rfl⟩
        exact hgX i.1 i.2
      obtain ⟨y, hy⟩ := hfin S hSsub hSfin
      have hseqy : ∀ i, i < n → y.mem (seq i) := by
        intro i hi
        have hle : g i hi ≤ y := hy _ ⟨⟨i, hi⟩, rfl⟩
        exact hle (seq i) (hgmem i hi)
      have hmem : y.mem (V.interUpTo seq n) := y.mem_interUpTo seq hseqy
      exact ⟨V.interUpTo seq n, y.sub hmem, subset_rfl⟩
    refine ⟨V.leastFilter C hCsub hCcons, ?_⟩
    intro x hx Z hZ
    exact V.subset_leastFilter C hCsub hCcons ⟨x, hx, hZ⟩

end NeighborhoodSystem

end Domain.Neighborhood
