/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Theorem110

/-!
# Exercise 1.21 (Scott 1981, PRG-19, §1) — Theorem 1.10 in greater detail

Scott asks to work out the proof of Theorem 1.10 more fully and to observe two
further
properties of the element-token system `{[X]}` over `|𝒟|`:

* it is **positive** (`tokenSystem_isPositive`), giving "in a different way the
same kind of
  conclusion as in 1.20";
* it is **complete** (`tokenSystem_complete`): every filter is *fixed* by a unique
point — the
  point whose filter of containing neighbourhoods it is. We formalize "fixed by a
  point" as
  `IsComplete`, and derive it from the bijection `tokenIso` of Theorem 1.10
  (`tokenSystem_toToken_bijective`). Thus tokens and (partial) elements are
  identified.

Finally, consistency of `{Xᵢ ∣ i < n}` is equivalent to
`⋂_{i<n} [Xᵢ] ≠ ∅` (`consistent_iff_iInter_bracket_nonempty`), the finite
generalization of
Theorem 1.10(2) via Theorem 1.1c.

Everything is `[propext, Quot.sound]` (the corollaries inherit the constructive
proofs of
Theorem 1.10 / Theorem 1.1c).
-/

namespace Domain.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.21 — the token system is positive.** `[X] ∩ [Y] = [X ∩ Y]` is a
neighbourhood
iff non-empty: a common element `x` gives `X ∩ Y ∈ 𝒟` (via `x.sub (x.inter_mem
…)`); conversely
`[W]` always contains the principal filter `↑W`. -/
theorem tokenSystem_isPositive : V.tokenSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.bracket_inter hX hY]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨V.principal hW, V.principal_mem_bracket hW⟩
  · rintro ⟨x, hx⟩
    exact ⟨X ∩ Y, x.sub hx, rfl⟩

/-! ### Completeness: every filter is fixed by a unique point. -/

/-- A neighbourhood system `𝒟'` over `β` is **complete** when every filter `y ∈
|𝒟'|` is *fixed
by a unique point* `b ∈ β`: a neighbourhood `S` lies in `y` iff `b ∈ S`. (Scott:
"*a filter is
fixed by a point iff it is the filter of all neighbourhoods containing that
point*".) -/
def IsComplete {β : Type*} (V' : NeighborhoodSystem β) : Prop :=
  ∀ y : V'.Element, ∃! b : β, ∀ S, V'.mem S → (y.mem S ↔ b ∈ S)

/-- **Exercise 1.21 — the token system is complete.** Every filter `y` of `{[X]}`
is fixed by
the unique point `ofToken y ∈ |𝒟|`: `[W] ∈ y ↔ ofToken y ∈ [W]`. Uniqueness is
`Element.ext`
applied through the brackets. -/
theorem tokenSystem_complete : V.tokenSystem.IsComplete := by
  intro y
  refine ⟨V.ofToken y, ?_, ?_⟩
  · rintro S ⟨W, hW, rfl⟩
    constructor
    · intro hyW; exact ⟨hW, hyW⟩
    · rintro ⟨_, hyW⟩; exact hyW
  · intro b hb
    apply Element.ext
    intro W
    by_cases hW : V.mem W
    · have hb' := hb (V.bracket W) ⟨W, hW, rfl⟩
      constructor
      · intro hbW; exact ⟨hW, hb'.mpr hbW⟩
      · intro hxW; exact hb'.mp hxW.2
    · constructor
      · intro hbW; exact absurd (b.sub hbW) hW
      · intro hxW; exact absurd ((V.ofToken y).sub hxW) hW

/-- The filter of `{[X]}` *fixed by* the point `x ∈ |𝒟|` is `toToken x` (the
filter of all
brackets containing `x`). By Theorem 1.10 this is a bijection `|𝒟| ≃ |{[X]}|`, so
tokens and
(partial) elements are identified. -/
def filterFixedBy (x : V.Element) : V.tokenSystem.Element := V.toToken x

/-- **Exercise 1.21 — tokens ↔ elements.** `toToken : |𝒟| → |{[X]}|` is a
bijection (it is the
underlying map of the order-iso `tokenIso`), so a complete system identifies
tokens with
(partial) elements under a one-one correspondence. -/
theorem tokenSystem_toToken_bijective : Function.Bijective V.toToken :=
  V.tokenIso.bijective

/-! ### Consistency iff non-empty intersection of brackets. -/

/-- `[X] ≠ ∅ iff X ∈ 𝒟`. `→` reads `X ∈ 𝒟` off any element of `[X]`; `←` exhibits
`↑X`. -/
theorem bracket_nonempty_iff {X : Set α} : (V.bracket X).Nonempty ↔ V.mem X := by
  constructor
  · rintro ⟨x, hx⟩; exact x.sub hx
  · intro hX; exact ⟨V.principal hX, V.principal_mem_bracket hX⟩

/-- **Exercise 1.21 — consistency via the intersection `[⋂]`.** For `X₀, …, Xₙ₋₁ ∈
𝒟`,
`⟨Xᵢ⟩` is consistent iff `[⋂_{i<n} Xᵢ] ≠ ∅`. Combines Theorem 1.1c
(`consistent_iff_interUpTo_mem`) with `bracket_nonempty_iff`. -/
theorem consistent_iff_bracket_interUpTo_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ (V.bracket (V.interUpTo X n)).Nonempty := by
  rw [V.consistent_iff_interUpTo_mem X hX]
  exact V.bracket_nonempty_iff.symm

/-- **Exercise 1.21 — consistency `iff ⋂_{i<n} [Xᵢ] ≠ ∅`.** The literal form of
Scott's
equivalence: `⟨Xᵢ⟩` is consistent iff there is a filter lying in every `[Xᵢ]` (`i
< n`). `→`
uses upward closure along `⋂_{i<n} Xᵢ ⊆ Xᵢ`; `←` uses `Element.mem_interUpTo`. -/
theorem consistent_iff_iInter_bracket_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ ∃ x : V.Element, ∀ i, i < n → x ∈ V.bracket (X i) := by
  rw [V.consistent_iff_bracket_interUpTo_nonempty X hX]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i hi => x.up_mem hx (hX i hi) (V.interUpTo_subset X hi)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, x.mem_interUpTo X (fun i hi => hx i hi)⟩

end NeighborhoodSystem

end Domain.Neighborhood
