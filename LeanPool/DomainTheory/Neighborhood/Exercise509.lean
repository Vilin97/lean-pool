/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Exercise407
import Mathlib.Tactic.Ring

/-!
# Exercise 5.9 (Scott 1981, PRG-19, Lecture V)

Suppose `f, g : 𝒟 → 𝒟` are approximable and `f ∘ g = g ∘ f`. Then:

* `f` and `g` have a **least common fixed point** `x = f(x) = g(x)`
(`commuting_least_common_fixed`);
* if in addition `f(⊥) = g(⊥)`, then `fix(f) = fix(g)`
(`fixElement_eq_of_commuting_bot`);
* in particular `fix(f) = fix(f²)` (`fixElement_iterTwice`).

**Construction.** Let `a = fix(f)`. Commutation makes `g(a)` a fixed point of `f`
(`f(g(a)) = g(f(a)) = g(a)`), so `a ⊑ g(a)`, and Exercise 4.7 produces the least
fixed point of `g`
above `a`, namely `x = ⊔ₙ gⁿ(a)`. Each `gⁿ(a)` is again a fixed point of `f`
(induction +
commutation), and `f` preserves the directed union, so `f(x) = x`: `x` is a common
fixed point. Any
common fixed point `w` satisfies `a = fix(f) ⊑ w` and `g(w) ⊑ w`, so `x ⊑ w` by
Exercise 4.7's
leastness.

For the second part, commutation gives `g(fⁿ(⊥)) = fⁿ⁺¹(⊥)` once `g(⊥) = f(⊥)`, so
`g(fix f) =
⊔ₙ fⁿ⁺¹(⊥) = fix f`; symmetrically `f(fix g) = fix g`, whence `fix f = fix g` by
leastness.

All maps and elements are choice-free; the equalities use only the order on `|𝒟|`.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- Commutation `f ∘ g = g ∘ f` read elementwise: `f(g(x)) = g(f(x))`. -/
theorem commute_apply {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f) (x : V.Element) :
    f.toElementMap (g.toElementMap x) = g.toElementMap (f.toElementMap x) := by
  have h1 : (f.comp g).toElementMap x = (g.comp f).toElementMap x := by rw [hcomm]
  rwa [toElementMap_comp, toElementMap_comp] at h1

/-- **Exercise 5.9 (Scott 1981, PRG-19).** Commuting approximable maps have a
*least common fixed
point* `x = f(x) = g(x)`. -/
theorem commuting_least_common_fixed {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f) :
    ∃ x : V.Element, f.toElementMap x = x ∧ g.toElementMap x = x ∧
      ∀ w : V.Element, f.toElementMap w = w → g.toElementMap w = w → x ≤ w := by
  set a := f.fixElement with ha_def
  have hfa : f.toElementMap a = a := toElementMap_fixElement f
  -- `a ⊑ g(a)` since `g(a)` is a fixed point of `f`.
  have ha_le : a ≤ g.toElementMap a := by
    apply fixElement_le_of_toElementMap_le f
    rw [commute_apply hcomm, hfa]
  set x := g.fixAbove ha_le with hx_def
  have hgx : g.toElementMap x = x := fixAbove_isFixed g ha_le
  have hax : a ≤ x := le_fixAbove g ha_le
  -- each `gⁿ(a)` is a fixed point of `f`.
  have hfix_each : ∀ n, f.toElementMap (g.iterFrom a n) = g.iterFrom a n := by
    intro n
    induction n with
    | zero => rw [iterFrom_zero]; exact hfa
    | succ k ih =>
      rw [iterFrom_succ g a k, commute_apply hcomm, ih]
  -- so `f(x) = x` by continuity.
  have hfx : f.toElementMap x = x := by
    apply le_antisymm
    · rw [hx_def, fixAbove, toElementMap_iSupDirected]
      apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hfix_each n]
      exact NeighborhoodSystem.le_iSupDirected (g.iterFrom a) _ n
    · rw [hx_def, fixAbove]
      apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [← hfix_each n]
      exact f.toElementMap_mono (NeighborhoodSystem.le_iSupDirected (g.iterFrom a) _ n)
  refine ⟨x, hfx, hgx, ?_⟩
  intro w hfw hgw
  have haw : a ≤ w := fixElement_le_of_toElementMap_le f (le_of_eq hfw)
  exact fixAbove_least g ha_le haw (le_of_eq hgw)

/-- `f.iterElem (n+1) = f(fⁿ(⊥))`. -/
theorem iterElem_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  rw [iterElem_eq_iterate, iterElem_eq_iterate, Function.iterate_succ', Function.comp_apply]

theorem iterElem_zero' (f : ApproximableMap V V) : f.iterElem 0 = V.bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

/-- **Exercise 5.9 (Scott 1981, PRG-19).** If `f, g` commute and `f(⊥) = g(⊥)`,
then
`fix(f) = fix(g)`. -/
theorem fixElement_eq_of_commuting_bot {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f)
    (hbot : f.toElementMap V.bot = g.toElementMap V.bot) :
    f.fixElement = g.fixElement := by
  -- `g(fⁿ⊥) = fⁿ⁺¹⊥`.
  have hshift : ∀ n, g.toElementMap (f.iterElem n) = f.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', iterElem_succ, iterElem_zero', ← hbot]
    | succ k ih =>
      rw [iterElem_succ, ← commute_apply hcomm, ih]
      exact (iterElem_succ f (k + 1)).symm
  -- `g(fix f) = fix f`.
  have hgfixf : g.toElementMap f.fixElement = f.fixElement := by
    rw [fixElement_eq_iSupDirected f, toElementMap_iSupDirected]
    apply le_antisymm
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hshift n]
      exact NeighborhoodSystem.le_iSupDirected f.iterElem _ (n + 1)
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      calc f.iterElem n ≤ f.iterElem (n + 1) := iterElem_mono f (Nat.le_succ n)
        _ = g.toElementMap (f.iterElem n) := (hshift n).symm
        _ ≤ _ := NeighborhoodSystem.le_iSupDirected (fun m => g.toElementMap (f.iterElem m)) _ n
  -- symmetric: `f(fix g) = fix g`.
  have hshift' : ∀ n, f.toElementMap (g.iterElem n) = g.iterElem (n + 1) := by
    intro n
    induction n with
    | zero =>
      rw [iterElem_zero', iterElem_succ, iterElem_zero', hbot]
    | succ k ih =>
      rw [iterElem_succ, commute_apply hcomm, ih]
      exact (iterElem_succ g (k + 1)).symm
  have hffixg : f.toElementMap g.fixElement = g.fixElement := by
    rw [fixElement_eq_iSupDirected g, toElementMap_iSupDirected]
    apply le_antisymm
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hshift' n]
      exact NeighborhoodSystem.le_iSupDirected g.iterElem _ (n + 1)
    · apply NeighborhoodSystem.iSupDirected_le
      intro n
      calc g.iterElem n ≤ g.iterElem (n + 1) := iterElem_mono g (Nat.le_succ n)
        _ = f.toElementMap (g.iterElem n) := (hshift' n).symm
        _ ≤ _ := NeighborhoodSystem.le_iSupDirected (fun m => f.toElementMap (g.iterElem m)) _ n
  apply le_antisymm
  · exact fixElement_le_of_toElementMap_le f (le_of_eq hffixg)
  · exact fixElement_le_of_toElementMap_le g (le_of_eq hgfixf)

/-- `fⁿ(⊥) ⊑ fix(f)`. -/
theorem iterElem_le_fixElement (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n ≤ f.fixElement := by
  rw [fixElement_eq_iSupDirected f]
  exact NeighborhoodSystem.le_iSupDirected f.iterElem _ n

/-- `(f²)ⁿ(⊥) = f^{2n}(⊥)`. -/
theorem comp_self_iterElem (f : ApproximableMap V V) (n : ℕ) :
    (f.comp f).iterElem n = f.iterElem (2 * n) := by
  induction n with
  | zero => rw [iterElem_zero', Nat.mul_zero, iterElem_zero']
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [iterElem_succ, ih, toElementMap_comp, h2, iterElem_succ, iterElem_succ]

/-- **Exercise 5.9 (Scott 1981, PRG-19).** In particular `fix(f) = fix(f²)`: the
`f²`-chain
`f^{2n}(⊥)` is cofinal in the `f`-chain `fⁿ(⊥)`, so the two least fixed points
coincide. -/
theorem fixElement_iterTwice (f : ApproximableMap V V) :
    f.fixElement = (f.comp f).fixElement := by
  apply le_antisymm
  · -- `fix f ⊑ fix f²`: `fⁿ⊥ ⊑ f^{2n}⊥ = (f²)ⁿ⊥ ⊑ fix f²`.
    rw [fixElement_eq_iSupDirected f]
    apply NeighborhoodSystem.iSupDirected_le
    intro n
    calc f.iterElem n ≤ f.iterElem (2 * n) := iterElem_mono f (by omega)
      _ = (f.comp f).iterElem n := (comp_self_iterElem f n).symm
      _ ≤ (f.comp f).fixElement := iterElem_le_fixElement (f.comp f) n
  · -- `fix f² ⊑ fix f`: `fix f` is a fixed point of `f²`.
    refine fixElement_le_of_toElementMap_le (f.comp f) (le_of_eq ?_)
    rw [toElementMap_comp, toElementMap_fixElement, toElementMap_fixElement]

end ApproximableMap

end Domain.Neighborhood
