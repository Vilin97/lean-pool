/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ShapeFintype
public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.SchurPackage

/-!
# The central idempotents, indexed by shapes of a fixed size

`SchurPackage.e μ` lives in the group algebra of `S_{μ.card}`; the
Deligne development sums such idempotents over all shapes of one
size `n`, so it needs them all in the *same* algebra.  `Shape.e`
recasts the idempotent of `μ : Shape n` into `SymGroupAlgebra n`
along the standard embedding at `μ.prop : μ.val.card = n` — an
algebra map, so idempotence and products transport; an injective
one, so nonvanishing transports too.
-/

@[expose] public section

namespace RS

/-- `symCast` along an equality of sizes is injective (it is
`mapDomain` along an injective map). -/
theorem symCast_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (symCast (m := m) (n := n) h) := by
  intro x y hxy
  exact MonoidAlgebra.mapDomain_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb h)) hxy

/-- The central idempotent of a shape of size `n`, recast into the
group algebra of `S_n`. -/
noncomputable def Shape.e (P : SchurPackage.{u}) {n : ℕ}
    (μ : Shape n) : SymGroupAlgebra n :=
  symCast (le_of_eq μ.prop) (P.e μ.val)

/-- The recast idempotent is idempotent. -/
theorem Shape.e_mul_self (P : SchurPackage.{u}) {n : ℕ}
    (μ : Shape n) : Shape.e P μ * Shape.e P μ = Shape.e P μ := by
  rw [Shape.e, ← map_mul]
  exact congrArg _ (P.idem μ.val)

/-- The recast idempotent is nonzero exactly when the original
is. -/
theorem Shape.e_eq_zero_iff (P : SchurPackage.{u}) {n : ℕ}
    (μ : Shape n) : Shape.e P μ = 0 ↔ P.e μ.val = 0 := by
  constructor
  · intro h
    apply symCast_injective (le_of_eq μ.prop)
    rw [map_zero]
    exact h
  · intro h
    rw [Shape.e, h, map_zero]

end RS
