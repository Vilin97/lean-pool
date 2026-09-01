/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A cardinality criterion for group isomorphism

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

/-- Between finite groups, an injective homomorphism extends to an isomorphism iff the two groups
have the same cardinality. -/
theorem MonoidHom.nonempty_mulEquiv_iff_card_eq {G H : Type*} [Group G] [Group H] [Finite H]
    (φ : G →* H) (hφ : Function.Injective φ) :
    Nonempty (G ≃* H) ↔ Nat.card G = Nat.card H :=
  ⟨fun ⟨e⟩ ↦ Nat.card_congr e.toEquiv,
    fun h ↦ ⟨MulEquiv.ofBijective φ ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hφ, h⟩)⟩⟩
