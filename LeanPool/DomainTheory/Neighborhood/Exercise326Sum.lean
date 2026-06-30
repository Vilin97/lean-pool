/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise326
import LeanPool.DomainTheory.Neighborhood.Exercise319Sum

/-!
# Exercise 3.26, continued (Scott 1981, PRG-19, §3) — the sum-valued conditional
and `which`

This module completes Exercise 3.26 with the two follow-up operators Scott asks
for:

* the **sum-valued conditional** `condSum : T × D₀ × D₁ → D₀ + D₁`, routing `true
→ in₀`,
  `false → in₁`, `⊥ → ⊥`. It is obtained for free by *composition*: feeding the
  two inputs through
  the injections `in₀, in₁` into the common domain `S = D₀ + D₁` and then applying
  the conditional
  `cond S : T × S × S → S` of Exercise 3.26. The three identities follow from
  `cond_true/false/bot`.

* the discriminator **`which : D₀ + D₁ → T`** reading the tag (`0X ↦ true`, `1Y ↦
false`,
  `Λ ↦ ⊥`), together with Scott's identity

  `cond(which x, in₀(out₀ x), in₁(out₁ x)) = x`   for all `x ∈ |D₀ + D₁|`.

The discriminator is built directly as a neighbourhood relation; its three guards
on the truth
component are mutually exclusive because the three forms of a sum-neighbourhood
(`Λ`-master, left
copy, right copy) are mutually exclusive (Exercise 3.18, using non-emptiness).
-/

namespace Domain.Neighborhood.Exercise326

open Domain.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-! ### The sum-valued conditional `condSum`. -/

/-- The embedding `T × D₀ × D₁ → T × S × S` (`S = D₀ + D₁`) that injects the two
value slots into
the sum via `in₀` and `in₁`, leaving the truth slot fixed. -/
def condSumEmb (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (prod TD (prod (sum V₀ V₁ h₀ h₁) (sum V₀ V₁ h₀ h₁))) :=
  paired (proj₀ TD (prod V₀ V₁))
    (paired ((inMap₀ (h₀ := h₀) (h₁ := h₁)).comp ((proj₀ V₀ V₁).comp (proj₁ TD (prod V₀ V₁))))
      ((inMap₁ (h₀ := h₀) (h₁ := h₁)).comp ((proj₁ V₀ V₁).comp (proj₁ TD (prod V₀ V₁)))))

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The sum-valued conditional `T × D₀ ×
D₁ → D₀ + D₁`. -/
def condSum (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (prod TD (prod V₀ V₁)) (sum V₀ V₁ h₀ h₁) :=
  (cond (sum V₀ V₁ h₀ h₁)).comp (condSumEmb V₀ V₁ h₀ h₁)

theorem condSumEmb_toElementMap (t : TD.Element) (x : V₀.Element) (y : V₁.Element) :
    (condSumEmb V₀ V₁ h₀ h₁).toElementMap (pair t (pair x y))
      = pair t (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)
          ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)) := by
  simp only [condSumEmb, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair]

/-- **Exercise 3.26.** `condSum(true, x, y) = in₀(x)`. -/
theorem condSum_true (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.trueElt (pair x y))
      = (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_true]

/-- **Exercise 3.26.** `condSum(false, x, y) = in₁(y)`. -/
theorem condSum_false (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.falseElt (pair x y))
      = (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_false]

/-- **Exercise 3.26.** `condSum(⊥, x, y) = ⊥`. -/
theorem condSum_bot (x : V₀.Element) (y : V₁.Element) :
    (condSum V₀ V₁ h₀ h₁).toElementMap (pair Example23.botElt (pair x y)) =
      (sum V₀ V₁ h₀ h₁).bot := by
  rw [condSum, toElementMap_comp, condSumEmb_toElementMap, cond_bot]

/-! ### The discriminator `which : D₀ + D₁ → T`. -/

/-- A `T`-neighbourhood containing `Δ` is `Δ`. -/
theorem Tmem_ge_master {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.master ⊆ C) : C = Example12.master :=
  Set.Subset.antisymm (Example12.neighborhoodSystem.sub_master hC) h

/-- A `T`-neighbourhood containing `{0}` is `{0}` or `Δ`. -/
theorem Tmem_ge_zero {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.zero ⊆ C) : C = Example12.zero ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])

/-- A `T`-neighbourhood containing `{1}` is `{1}` or `Δ`. -/
theorem Tmem_ge_one {C : Set Example12.Token} (hC : Example12.mem C)
    (h : Example12.one ⊆ C) : C = Example12.one ∨ C = Example12.master := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact Or.inr rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])
  · exact Or.inl rfl

theorem inter_in_zeroset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C =
  Example12.zero)
    (hc' : C' = Example12.master ∨ C' = Example12.zero) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.zero := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

theorem inter_in_oneset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C = Example12.one)
    (hc' : C' = Example12.master ∨ C' = Example12.one) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.one := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

/-- Scott's guard for `which`: the truth output is `true` (`{0}`/`Δ`) on a left
copy `0X`, `false`
(`{1}`/`Δ`) on a right copy `1Y`, and `⊥` (`Δ`) on the basepoint master. -/
def whichGuard (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (W : Set (Option (α ⊕ β))) (C : Set Example12.Token) : Prop :=
  ((∃ X, V₀.mem X ∧ W = inj₀ X) ∧ (C = Example12.master ∨ C = Example12.zero)) ∨
  ((∃ Y, V₁.mem Y ∧ W = inj₁ Y) ∧ (C = Example12.master ∨ C = Example12.one)) ∨
  (W = sumMaster V₀ V₁ ∧ C = Example12.master)

theorem whichGuard_left {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {X : Set α}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₀ X) (hX : X.Nonempty) :
    C = Example12.master ∨ C = Example12.zero := by
  rcases hg with ⟨_, hc⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨hWsm, _⟩
  · exact hc
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact not_inj₀_subset_inj₁ hX h.subset
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)

theorem whichGuard_right {W : Set (Option (α ⊕ β))} {C : Set Example12.Token} {Y : Set β}
    (hg : whichGuard V₀ V₁ W C) (hW : W = inj₁ Y) (hY : Y.Nonempty) :
    C = Example12.master ∨ C = Example12.one := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨_, hc⟩ | ⟨hWsm, _⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact not_inj₁_subset_inj₀ hY h.subset
  · exact hc
  · refine absurd (hW.symm.trans hWsm) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)

theorem whichGuard_masterC {W : Set (Option (α ⊕ β))} {C : Set Example12.Token}
    (hg : whichGuard V₀ V₁ W C) (hW : W = sumMaster V₀ V₁) : C = Example12.master := by
  rcases hg with ⟨⟨X, _, hWX⟩, _⟩ | ⟨⟨Y, _, hWY⟩, _⟩ | ⟨_, hc⟩
  · refine absurd (hW.symm.trans hWX) ?_
    intro h; exact none_mem_inj₀ (h ▸ none_mem_sumMaster)
  · refine absurd (hW.symm.trans hWY) ?_
    intro h; exact none_mem_inj₁ (h ▸ none_mem_sumMaster)
  · exact hc

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The discriminator `which : D₀ + D₁ →
T`. -/
def whichMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (sum V₀ V₁ h₀ h₁) TD where
  rel W C := (sum V₀ V₁ h₀ h₁).mem W ∧ Example12.mem C ∧ whichGuard V₀ V₁ W C
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  inter_right := by
    rintro W C C' ⟨hW, _, hg⟩ ⟨_, _, hg'⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · have hor := inter_in_zeroset hc (whichGuard_left hg' rfl (h₀ X hX))
      refine ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), ?_, Or.inl ⟨⟨X, hX, rfl⟩, hor⟩⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_zero
    · have hor := inter_in_oneset hc (whichGuard_right hg' rfl (h₁ Y hY))
      refine ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), ?_, Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, hor⟩)⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_one
    · have hc' := whichGuard_masterC hg' rfl
      subst hc; subst hc'
      rw [Set.inter_self]
      exact ⟨Or.inl rfl, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  mono := by
    rintro W W₂ C C₂ ⟨hW, hC, hg⟩ hW₂W hCC₂ hW₂ hC₂
    refine ⟨hW₂, hC₂, ?_⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂ hW₂W
      refine Or.inl ⟨⟨X₂, hX₂, rfl⟩, ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_zero hC₂ hCC₂)
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂ hW₂W
      refine Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, ?_⟩)
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_one hC₂ hCC₂)
    · subst hc
      have hC₂m : C₂ = Example12.master := Tmem_ge_master hC₂ hCC₂
      rcases hW₂ with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
      · exact Or.inr (Or.inr ⟨rfl, hC₂m⟩)
      · exact Or.inl ⟨⟨X₂, hX₂, rfl⟩, Or.inl hC₂m⟩
      · exact Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, Or.inl hC₂m⟩)

/-! ### Membership facts and the composite identity. -/

/-- `∅` is never a sum-neighbourhood (every neighbourhood is non-empty). -/
theorem not_sum_mem_empty : ¬ (sum V₀ V₁ h₀ h₁).mem ∅ := by
  rintro (h | ⟨X, hX, h⟩ | ⟨Y, hY, h⟩)
  · exact absurd (h.symm ▸ none_mem_sumMaster) (Set.notMem_empty _)
  · obtain ⟨a, ha⟩ := inj₀_nonempty (h₀ X hX)
    exact absurd (h ▸ ha) (Set.notMem_empty _)
  · obtain ⟨b, hb⟩ := inj₁_nonempty (h₁ Y hY)
    exact absurd (h ▸ hb) (Set.notMem_empty _)

/-- `which(x)` selects `true` (`{0} ∈ which x`) exactly when `x` reaches into the
left copy. -/
theorem which_mem_zero {x : (sum V₀ V₁ h₀ h₁).Element} :
    ((whichMap V₀ V₁ h₀ h₁).toElementMap x).mem Example12.zero
      ↔ ∃ X, V₀.mem X ∧ x.mem (inj₀ X) := by
  constructor
  · rintro ⟨W, hWx, _, _, hg⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, _⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
    · exact ⟨X, hX, hWx⟩
    · rcases hc with h | h
      · exact absurd h zero_ne_master
      · exact absurd h zero_ne_one
    · exact absurd hc zero_ne_master
  · rintro ⟨X, hX, hWx⟩
    exact ⟨inj₀ X, hWx, Or.inr (Or.inl ⟨X, hX, rfl⟩), Example12.mem_zero,
      Or.inl ⟨⟨X, hX, rfl⟩, Or.inr rfl⟩⟩

/-- `which(x)` selects `false` (`{1} ∈ which x`) exactly when `x` reaches into the
right copy. -/
theorem which_mem_one {x : (sum V₀ V₁ h₀ h₁).Element} :
    ((whichMap V₀ V₁ h₀ h₁).toElementMap x).mem Example12.one
      ↔ ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y) := by
  constructor
  · rintro ⟨W, hWx, _, _, hg⟩
    rcases hg with ⟨_, hc⟩ | ⟨⟨Y, hY, rfl⟩, _⟩ | ⟨_, hc⟩
    · rcases hc with h | h
      · exact absurd h one_ne_master
      · exact absurd h zero_ne_one.symm
    · exact ⟨Y, hY, hWx⟩
    · exact absurd hc one_ne_master
  · rintro ⟨Y, hY, hWx⟩
    exact ⟨inj₁ Y, hWx, Or.inr (Or.inr ⟨Y, hY, rfl⟩), Example12.mem_one,
      Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, Or.inr rfl⟩)⟩

/-- On a "left" element (one reaching into the left copy), the round-trip `in₀ ∘
out₀` is the
identity. -/
theorem inMap₀_outMap₀_eq_of_left {x : (sum V₀ V₁ h₀ h₁).Element}
    (hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)) :
    (inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₀ (h₀ := h₀) (
      h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨X₀, hX₀, hxX₀⟩ := hL
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, ⟨W, hxW, _, _, hLWX⟩, _, hSZ, hinjXZ⟩
    -- W ∩ inj₀ X₀ is a left copy inj₀ X₁ ⊆ Z, and lies in x
    have hxWX₀ : x.mem (W ∩ inj₀ X₀) := x.inter_mem hxW hxX₀
    obtain ⟨X₁, _, hX₁eq⟩ := mem_subset_inj₀ (x.sub hxWX₀) Set.inter_subset_right
    have hX₁X : X₁ ⊆ X := by
      have : leftPart V₀ (W ∩ inj₀ X₀) ⊆ X :=
        (leftPart_mono V₀ Set.inter_subset_left).trans hLWX
      rwa [hX₁eq, leftPart_inj₀] at this
    have : (W ∩ inj₀ X₀) ⊆ Z :=
      hX₁eq ▸ (inj₀_subset_inj₀.mpr hX₁X).trans hinjXZ
    exact x.up_mem hxWX₀ hSZ this
  · intro hxZ
    rcases x.sub hxZ with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · -- Z = sumMaster
      exact ⟨V₀.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩, V₀.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
    · -- Z = inj₀ X'
      exact ⟨X', ⟨inj₀ X', hxZ, Or.inr (Or.inl ⟨X', hX', rfl⟩), hX', (leftPart_inj₀ V₀ X').subset⟩,
        hX', Or.inr (Or.inl ⟨X', hX', rfl⟩), subset_rfl⟩
    · -- Z = inj₁ Y' is impossible for a left element
      have := x.inter_mem hxX₀ hxZ
      rw [inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty

/-- On a "right" element, the round-trip `in₁ ∘ out₁` is the identity. -/
theorem inMap₁_outMap₁_eq_of_right {x : (sum V₀ V₁ h₀ h₁).Element}
    (hR : ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)) :
    (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₁ (h₀ := h₀) (
      h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨Y₀, hY₀, hxY₀⟩ := hR
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, ⟨W, hxW, _, _, hRWY⟩, _, hSZ, hinjYZ⟩
    have hxWY₀ : x.mem (W ∩ inj₁ Y₀) := x.inter_mem hxW hxY₀
    obtain ⟨Y₁, _, hY₁eq⟩ := mem_subset_inj₁ (x.sub hxWY₀) Set.inter_subset_right
    have hY₁Y : Y₁ ⊆ Y := by
      have : rightPart V₁ (W ∩ inj₁ Y₀) ⊆ Y :=
        (rightPart_mono V₁ Set.inter_subset_left).trans hRWY
      rwa [hY₁eq, rightPart_inj₁] at this
    have : (W ∩ inj₁ Y₀) ⊆ Z :=
      hY₁eq ▸ (inj₁_subset_inj₁.mpr hY₁Y).trans hinjYZ
    exact x.up_mem hxWY₀ hSZ this
  · intro hxZ
    rcases x.sub hxZ with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact ⟨V₁.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩, V₁.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
    · have := x.inter_mem hxY₀ hxZ
      rw [Set.inter_comm, inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty
    · exact ⟨Y', ⟨inj₁ Y', hxZ, Or.inr (Or.inr ⟨Y', hY', rfl⟩), hY', (rightPart_inj₁ V₁ Y').subset⟩,
        hY', Or.inr (Or.inr ⟨Y', hY', rfl⟩), subset_rfl⟩

/-- Trichotomy for a sum-element: it reaches the left copy, or the right copy, or
is `⊥`. -/
theorem sum_element_trichotomy (x : (sum V₀ V₁ h₀ h₁).Element) :
    (∃ X, V₀.mem X ∧ x.mem (inj₀ X)) ∨ (∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)) ∨
      (∀ W, x.mem W → W = (sum V₀ V₁ h₀ h₁).master) := by
  by_cases hL : ∃ X, V₀.mem X ∧ x.mem (inj₀ X)
  · exact Or.inl hL
  by_cases hR : ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)
  · exact Or.inr (Or.inl hR)
  refine Or.inr (Or.inr ?_)
  intro W hxW
  rcases x.sub hxW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · rfl
  · exact absurd ⟨X, hX, hxW⟩ hL
  · exact absurd ⟨Y, hY, hxW⟩ hR

/-- **Exercise 3.26 (Scott 1981, PRG-19).** Scott's identity for the
discriminator:
`cond(which x, in₀(out₀ x), in₁(out₁ x)) = x` for every `x ∈ |D₀ + D₁|`. -/
theorem cond_which (x : (sum V₀ V₁ h₀ h₁).Element) :
    (cond (sum V₀ V₁ h₀ h₁)).toElementMap
        (pair ((whichMap V₀ V₁ h₀ h₁).toElementMap x)
          (pair ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap
                  ((outMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x))
                ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap
                  ((outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap x)))) = x := by
  apply Element.ext
  intro Z
  rw [cond_toElementMap_mem, which_mem_zero, which_mem_one]
  constructor
  · rintro (⟨hL, ha⟩ | ⟨hR, hb⟩ | rfl)
    · rwa [inMap₀_outMap₀_eq_of_left hL] at ha
    · rwa [inMap₁_outMap₁_eq_of_right hR] at hb
    · exact x.master_mem
  · intro hxZ
    rcases sum_element_trichotomy x with hL | hR | hN
    · exact Or.inl ⟨hL, by rw [inMap₀_outMap₀_eq_of_left hL]; exact hxZ⟩
    · exact Or.inr (Or.inl ⟨hR, by rw [inMap₁_outMap₁_eq_of_right hR]; exact hxZ⟩)
    · exact Or.inr (Or.inr (hN Z hxZ))

end Domain.Neighborhood.Exercise326
