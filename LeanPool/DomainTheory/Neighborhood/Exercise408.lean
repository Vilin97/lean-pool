/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Theorem41
import LeanPool.DomainTheory.Neighborhood.ApproximableExercises

/-!
# Exercise 4.8 (Scott 1981, PRG-19, Lecture IV) — the principle of fixed-point
induction

Suppose `f : 𝒟 → 𝒟` and a predicate `S ⊆ |𝒟|` satisfy

  (i)   `⊥ ∈ S`;
  (ii)  `x ∈ S ⟹ f(x) ∈ S`;
  (iii) `S` is closed under sups of increasing sequences.

Then `fix(f) ∈ S`. Since `fix(f) = ⊔ₙ fⁿ(⊥)` (Theorem 4.2(iii)), and `f⁰(⊥) = ⊥ ∈
S` with the
inductive step `fⁿ(⊥) ∈ S ⟹ fⁿ⁺¹(⊥) ∈ S` from (i)/(ii), every approximant lies in
`S`; the
directed union then lies in `S` by (iii). This is **fixed-point induction**
(`fix_induction`).

As Scott suggests, we apply it to `S = {x ∣ a(x) = b(x)}` (`fix_induction_eq`): if
`a, b : 𝒟 → 𝒟`
are approximable with `a(⊥) = b(⊥)`, `f ∘ a = a ∘ f` and `f ∘ b = b ∘ f`, then
`a(fix f) = b(fix f)`. (i) is `a(⊥) = b(⊥)`; (ii) uses the commutation `a(f x) =
f(a x)`,
`b(f x) = f(b x)`; (iii) is continuity (`a`, `b` preserve directed unions,
`toElementMap_iSupDirected`).

The induction principle is **choice-free** (`#print axioms ⊆ {propext,
Quot.sound}`); the equality
corollary inherits `Classical.choice` only through the `Element` extensionality
used to compare the
two directed unions.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The sup of a monotone `ω`-chain, realized as a directed union
(`max`-directedness). -/
def supChain (s : ℕ → V.Element) (hmono : Monotone s) : V.Element :=
  NeighborhoodSystem.iSupDirected s
    (fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)

theorem mem_supChain (s : ℕ → V.Element) (hmono : Monotone s) {Z : Set α} :
    (supChain s hmono).mem Z ↔ ∃ n, (s n).mem Z :=
  NeighborhoodSystem.mem_iSupDirected s _

/-- `fⁿ⁺¹(⊥) = f(fⁿ(⊥))`. -/
theorem iterElem_succ (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem (n + 1) = f.toElementMap (f.iterElem n) := by
  change (f.comp (f.iterMap n)).toElementMap V.bot
      = f.toElementMap ((f.iterMap n).toElementMap V.bot)
  rw [toElementMap_comp]

theorem iterElem_zero (f : ApproximableMap V V) : f.iterElem 0 = V.bot :=
  toElementMap_idMap V.bot

/-- The approximants `fⁿ(⊥)` form a monotone chain whose sup is `fix(f)`. -/
theorem fixElement_eq_supChain (f : ApproximableMap V V) :
    f.fixElement = supChain f.iterElem (fun _ _ hab => iterElem_mono f hab) := by
  apply Element.ext
  intro X
  rw [mem_supChain, mem_fixElement]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mp hn⟩

/-- **Exercise 4.8 (Scott 1981, PRG-19) — fixed-point induction.** If a predicate
`P` holds at `⊥`,
is preserved by `f`, and is closed under sups of monotone chains, then it holds at
`fix(f)`. -/
theorem fix_induction (f : ApproximableMap V V) (P : V.Element → Prop)
    (hbot : P V.bot)
    (hstep : ∀ x, P x → P (f.toElementMap x))
    (hsup : ∀ (s : ℕ → V.Element) (hmono : Monotone s), (∀ n, P (s n)) → P (supChain s hmono)) :
    P f.fixElement := by
  have hmono : Monotone f.iterElem := fun _ _ hab => iterElem_mono f hab
  have hP : ∀ n, P (f.iterElem n) := by
    intro n
    induction n with
    | zero => rw [iterElem_zero]; exact hbot
    | succ k ih => rw [iterElem_succ]; exact hstep _ ih
  rw [fixElement_eq_supChain f]
  exact hsup f.iterElem hmono hP

/-- **Exercise 4.8 (Scott 1981, PRG-19) — application to `S = {x ∣ a(x) =
b(x)}`.** If `a(⊥) = b(⊥)`
and `f` commutes with both `a` and `b` (`f ∘ a = a ∘ f`, `f ∘ b = b ∘ f`), then
`a` and `b` agree at
the least fixed point: `a(fix f) = b(fix f)`. -/
theorem fix_induction_eq (f a b : ApproximableMap V V)
    (hbot : a.toElementMap V.bot = b.toElementMap V.bot)
    (hfa : f.comp a = a.comp f) (hfb : f.comp b = b.comp f) :
    a.toElementMap f.fixElement = b.toElementMap f.fixElement := by
  -- commutation, elementwise: `a(f x) = f(a x)` and `b(f x) = f(b x)`.
  have hca : ∀ x, a.toElementMap (f.toElementMap x) = f.toElementMap (a.toElementMap x) := by
    intro x
    have h1 : (a.comp f).toElementMap x = (f.comp a).toElementMap x := by rw [hfa]
    rwa [toElementMap_comp, toElementMap_comp] at h1
  have hcb : ∀ x, b.toElementMap (f.toElementMap x) = f.toElementMap (b.toElementMap x) := by
    intro x
    have h1 : (b.comp f).toElementMap x = (f.comp b).toElementMap x := by rw [hfb]
    rwa [toElementMap_comp, toElementMap_comp] at h1
  refine fix_induction f (fun x => a.toElementMap x = b.toElementMap x) hbot ?_ ?_
  · intro x hx
    rw [hca, hcb, hx]
  · intro s hmono hs
    -- both sides are directed unions of equal families.
    show a.toElementMap (supChain s hmono) = b.toElementMap (supChain s hmono)
    rw [supChain, toElementMap_iSupDirected, toElementMap_iSupDirected]
    apply Element.ext
    intro Z
    rw [NeighborhoodSystem.mem_iSupDirected, NeighborhoodSystem.mem_iSupDirected]
    constructor
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [← hs n]; exact hn⟩
    · rintro ⟨n, hn⟩; exact ⟨n, by rw [hs n]; exact hn⟩

end ApproximableMap

end Domain.Neighborhood
