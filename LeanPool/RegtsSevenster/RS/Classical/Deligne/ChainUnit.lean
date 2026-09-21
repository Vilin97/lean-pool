/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.NatChain
import LeanPool.RegtsSevenster.RS.Classical.Deligne.UnitStage

/-!
# Nonvanishing of the unit along a chain colimit

For a chain of objects of the ind-category with compatible maps
from the monoidal unit, the image of the unit in the colimit
vanishes exactly when it dies at a finite stage.  This is the form
in which the Key Lemma's colimit algebra is shown nonzero: the
δ-transitions carry the unit forward, and stage detection reduces
vanishing in the colimit to vanishing at a stage.  The chain is
indexed by a universe-lifted copy of `ℕ`, the shape at which the
ind-category is known to have filtered colimits.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v

/-- A `v`-small copy of the natural numbers. -/
abbrev SmallNat : Type v := ULiftHom.{v} (ULift.{v} ℕ)

/-- The equivalence between `ℕ` and its `v`-small copy. -/
noncomputable def smallNatEquiv : ℕ ≌ SmallNat.{v} :=
  ULiftHomULiftCategory.equiv ℕ

instance : IsFiltered SmallNat.{v} :=
  IsFiltered.of_equivalence smallNatEquiv

variable {C : Type v}

/-- Compatible unit maps ride along the chain morphisms. -/
theorem unit_chainMap [SmallCategory C] [MonoidalCategory C]
    (B : ℕ → Ind C) (δ : ∀ n, B n ⟶ B (n + 1))
    (u : ∀ n, 𝟙_ (Ind C) ⟶ B n)
    (hu : ∀ n, u n ≫ δ n = u (n + 1)) {m n : ℕ} (h : m ≤ n) :
    u m ≫ chainMap B δ h = u n := by
  induction n, h using Nat.le_induction with
  | base => rw [chainMap_self, Category.comp_id]
  | succ n hmn ih =>
    rw [chainMap_succ_of_le B δ hmn, ← Category.assoc, ih, hu]

/-- The chain functor over the `v`-small copy of `ℕ`. -/
noncomputable def chainFunctorSmall [SmallCategory C]
    (B : ℕ → Ind C)
    (δ : ∀ n, B n ⟶ B (n + 1)) : SmallNat.{v} ⥤ Ind C :=
  smallNatEquiv.inverse ⋙ chainFunctor B δ

/-- **Nonvanishing of the unit in a chain colimit**: with
compatible unit maps along the chain, the image of the unit in the
colimit is zero exactly when the unit dies at some stage. -/
theorem unit_chain_colimit_eq_zero_iff
    [SmallCategory C] [MonoidalCategory C] [Preadditive C]
    [HasFiniteColimits C]
    (B : ℕ → Ind C)
    (δ : ∀ n, B n ⟶ B (n + 1)) (u : ∀ n, 𝟙_ (Ind C) ⟶ B n)
    (hu : ∀ n, u n ≫ δ n = u (n + 1)) (m : ℕ) :
    u m ≫ colimit.ι (chainFunctorSmall B δ)
        (smallNatEquiv.functor.obj m) = 0 ↔ ∃ n, u n = 0 := by
  refine (unit_colimit_eq_zero_iff
    (chainFunctorSmall B δ) (u m)).trans ?_
  constructor
  · rintro ⟨k, α, hk⟩
    refine ⟨smallNatEquiv.inverse.obj k, ?_⟩
    rw [← unit_chainMap B δ u hu
      (leOfHom (smallNatEquiv.inverse.map α))]
    exact hk
  · rintro ⟨n, hn⟩
    rcases le_total m n with h | h
    · refine ⟨smallNatEquiv.functor.obj n,
        smallNatEquiv.functor.map (homOfLE h), ?_⟩
      have : u m ≫ chainMap B δ h = 0 := by
        rw [unit_chainMap B δ u hu h, hn]
      exact this
    · refine ⟨smallNatEquiv.functor.obj m, 𝟙 _, ?_⟩
      have hz : u m = 0 := by
        rw [← unit_chainMap B δ u hu h, hn, Limits.zero_comp]
      have : u m ≫ chainMap B δ (le_refl m) = 0 := by
        rw [chainMap_self, Category.comp_id, hz]
      exact this

end RS
