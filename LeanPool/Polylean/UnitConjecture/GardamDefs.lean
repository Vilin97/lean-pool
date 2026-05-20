/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Defs
import LeanPool.Polylean.UnitConjecture.TorsionFree
import LeanPool.Polylean.UnitConjecture.GroupRing

namespace LeanPool.Polylean


/-!

## Definitions for Giles Gardam's result

The data underlying the construction of the non-trivial unit `α` in `𝔽₂[P]`,
plus the proof that this element is non-trivial. The slow `decide +kernel`
verifications that `α · α' = 1` and `α' · α = 1` are factored out into
companion modules so the two heavy kernel reductions can run in parallel.
-/


/-! ### Preliminaries -/

/-- An element of a free module is trivial but not zero if it is supported on one basis vector. -/
def trivialNonZeroElem {R X : Type _} [Ring R] [DecidableEq X] [DecidableEq R]
    (a : FreeModule R X) : Prop :=
  ∃! x : X, FreeModule.coordinates x a ≠ 0

/-- The statement of Kaplansky's Unit Conjecture:
The only units in a group ring, when the group is torsion-free and the ring is a field,
are the trivial units. -/
def UnitConjecture : Prop :=
  ∀ {F : Type _} [Field F] [DecidableEq F]
  {G : Type _} [Group G] [DecidableEq G] [TorsionFree G],
    ∀ u : (F[G])ˣ, trivialNonZeroElem (u : F[G])

/-- The finite field on two elements. -/
abbrev 𝔽₂ := Fin 2

instance : Field 𝔽₂ where
  inv := id
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := fun
    | 0 => by intro; contradiction
    | 1 => by intro; rfl
  inv_zero := rfl
  div_eq_mul_inv := by decide
  qsmul := _
  nnqsmul := _

instance ringElem : Coe P (𝔽₂[P]) where
    coe g := ⟦[(1, g)]⟧

namespace P

/-!
The main constants of the group `P`.
-/

/-- The first kernel generator of the Promislow group. -/
abbrev x : P := (K.x, Q.e)
/-- The second kernel generator of the Promislow group. -/
abbrev y : P := (K.y, Q.e)
/-- The third kernel generator of the Promislow group. -/
abbrev z : P := (K.z, Q.e)
/-- The first nontrivial quotient generator of the Promislow group. -/
abbrev a : P := ((0, 0, 0), Q.a)
/-- The second nontrivial quotient generator of the Promislow group. -/
abbrev b : P := ((0, 0, 0), Q.b)

end P

namespace Gardam

open P

/-- Embed a group element as the corresponding basis element of `𝔽₂[P]`. -/
private abbrev groupRingOf (g : P) : 𝔽₂[P] :=
  ⟦[(1, g)]⟧

/-- The group-ring multiplication, made explicit to avoid the monomial `HMul R G` notation. -/
private abbrev ringMul (u v : 𝔽₂[P]) : 𝔽₂[P] :=
  GroupRing.mul u v

/-- The `p` component of Gardam's non-trivial unit `α`. -/
def p : 𝔽₂[P] :=
  (1 : 𝔽₂[P]) + groupRingOf x + groupRingOf y + groupRingOf (x * y) +
    groupRingOf (z⁻¹) + groupRingOf (x * z⁻¹) + groupRingOf (y * z⁻¹) +
    groupRingOf (x * y * z⁻¹)
/-- The `q` component of Gardam's non-trivial unit `α`. -/
def q : 𝔽₂[P] := groupRingOf (x⁻¹ * y⁻¹) + groupRingOf x + groupRingOf (y⁻¹ * z) +
  groupRingOf z
/-- The `r` component of Gardam's non-trivial unit `α`. -/
def r : 𝔽₂[P] := (1 : 𝔽₂[P]) + groupRingOf x + groupRingOf (y⁻¹ * z) +
  groupRingOf (x * y * z)
/-- The `s` component of Gardam's non-trivial unit `α`. -/
def s : 𝔽₂[P] := (1 : 𝔽₂[P]) + groupRingOf (x * z⁻¹) + groupRingOf (x⁻¹ * z⁻¹) +
  groupRingOf (y * z⁻¹) + groupRingOf (y⁻¹ * z⁻¹)

/-- The non-trivial unit `α`. -/
def α : 𝔽₂[P] :=
  p + ringMul q (groupRingOf a) + ringMul r (groupRingOf b) +
    ringMul (ringMul s (groupRingOf a)) (groupRingOf b)

/-- The `p'` component of the inverse `α'`. -/
def p' : 𝔽₂[P] :=
  ringMul (groupRingOf (x⁻¹))
    (ringMul (ringMul (groupRingOf (a⁻¹)) p) (groupRingOf a))
/-- The `q'` component of the inverse `α'`. -/
def q' : 𝔽₂[P] := -ringMul (groupRingOf (x⁻¹)) q
/-- The `r'` component of the inverse `α'`. -/
def r' : 𝔽₂[P] := -ringMul (groupRingOf (y⁻¹)) r
/-- The `s'` component of the inverse `α'`. -/
def s' : 𝔽₂[P] :=
  ringMul (groupRingOf (z⁻¹))
    (ringMul (ringMul (groupRingOf (a⁻¹)) s) (groupRingOf a))

/-- The inverse `α'` of the non-trivial unit `α`. -/
def α' : 𝔽₂[P] :=
  p' + ringMul q' (groupRingOf a) + ringMul r' (groupRingOf b) +
    ringMul (ringMul s' (groupRingOf a)) (groupRingOf b)

end Gardam

/-!
### Non-triviality of `α`
-/

namespace Gardam

open P

/-- A proof that the unit is non-trivial. -/
theorem α_nonTrivial : ¬ (trivialNonZeroElem α) := by
    intro ⟨g, _, (eqg : ∀ y, α.coordinates y ≠ 0 → y = g)⟩
    have l₁ : z⁻¹ = g := by
      apply eqg; decide
    have l₂ : x * y = g := by
      apply eqg; decide
    have l₃ : z⁻¹ = x * y := by
      exact Eq.trans l₁ l₂.symm
    exact (by decide : z⁻¹ ≠ x * y) l₃

end Gardam

end LeanPool.Polylean
