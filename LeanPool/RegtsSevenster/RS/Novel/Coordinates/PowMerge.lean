/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.CanonColour

/-!
# Merging monoidal powers

The block merge of two monoidal powers into the power of the sum
(right unitor base, associator-threaded step), and its
compatibility with the model transport: transporting blockwise
and merging through the structure map agrees with merging first.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The block merge of monoidal powers. -/
noncomputable def powMerge (V : SuperVect) :
    (a b : ℕ) → (superPow V a ⊗ superPow V b ⟶
      superPow V (a + b))
  | a, 0 => (ρ_ (superPow V a)).hom
  | a, b + 1 =>
      (α_ (superPow V a) (superPow V b) V).inv ≫
        ((powMerge V a b) ▷ V)

variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

-- Raised budget: the block transport is proved by recursion on the
-- second arity, carrying the tensorator and both unitors at every
-- step.
/-- **The block transport**: blockwise transports assembled by
the structure map agree with the merged transport. -/
theorem stdToOmega_merge :
    ∀ (a b : ℕ),
      letI := P.braided
      ((stdToOmega f P e a ⊗ₘ stdToOmega f P e b) ≫
        μ P.ω (SkeinObj.mk a) (SkeinObj.mk b) :
        superPow (stdSuperPair k ℓ) a ⊗ superPow (stdSuperPair k ℓ) b ⟶
          P.ω.obj (SkeinObj.mk (a + b))) =
      powMerge (stdSuperPair k ℓ) a b ≫ stdToOmega f P e (a + b)
  -- ═══════ b = 0: THE RIGHT UNITOR ═══════
  | a, 0 => by
    let := P.braided
    -- The skein right unitor at `a` is the identity.
    have hρ : (ρ_ (SkeinObj.mk a : SkeinObj f)).hom =
        𝟙 (SkeinObj.mk a) := by
      change bundleMapClass f (finCongr _) = _
      rw [show (finCongr (show a + 0 = a by omega) :
          Fin a ≃ Fin a) = _root_.Equiv.refl (Fin a) from
        _root_.Equiv.ext (fun x => Fin.ext rfl)]
      exact bundleMapClass_refl f a
    -- Right unitality with the strict unitor eliminated.
    have hru : (P.ω.obj (SkeinObj.mk a) ◁ ε P.ω) ≫
        μ P.ω (SkeinObj.mk a) (SkeinObj.mk 0) =
        (ρ_ (P.ω.obj (SkeinObj.mk a))).hom := by
      have h0 := Functor.LaxMonoidal.right_unitality
        (F := P.ω) (SkeinObj.mk a)
      rw [hρ] at h0
      rw [show P.ω.map (𝟙 (SkeinObj.mk a : SkeinObj f)) =
          𝟙 (P.ω.obj (SkeinObj.mk a)) from P.ω.map_id _] at h0
      exact h0.symm
    change (stdToOmega f P e a ⊗ₘ ε P.ω) ≫
      μ P.ω (SkeinObj.mk a) (SkeinObj.mk 0) =
      (ρ_ (superPow (stdSuperPair k ℓ) a)).hom ≫
        stdToOmega f P e a
    rw [MonoidalCategory.tensorHom_def]
    rw [Category.assoc, hru]
    exact MonoidalCategory.rightUnitor_naturality _
  -- ═══════ b + 1: PEEL ONE TENSOR FACTOR ═══════
  | a, b + 1 => by
    let := P.braided
    -- Expand the right transport one step.
    change (stdToOmega f P e a ⊗ₘ
        ((stdToOmega f P e b ⊗ₘ e) ≫
          μ P.ω (SkeinObj.mk b) (SkeinObj.mk 1))) ≫
      μ P.ω (SkeinObj.mk a) (SkeinObj.mk (b + 1)) =
      ((α_ (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).inv ≫
        ((powMerge (stdSuperPair k ℓ) a b) ▷ stdSuperPair k ℓ)) ≫
        stdToOmega f P e (a + (b + 1))
    -- Split the nested tensor.
    rw [show (stdToOmega f P e a ⊗ₘ
        ((stdToOmega f P e b ⊗ₘ e) ≫
          μ P.ω (SkeinObj.mk b) (SkeinObj.mk 1))) =
      (stdToOmega f P e a ⊗ₘ
        (stdToOmega f P e b ⊗ₘ e)) ≫
      (P.ω.obj (SkeinObj.mk a) ◁
        μ P.ω (SkeinObj.mk b) (SkeinObj.mk 1)) from by
      rw [← MonoidalCategory.id_tensorHom,
        MonoidalCategory.tensorHom_comp_tensorHom,
        Category.comp_id]]
    -- The associativity square with the strict skein associator.
    have hα : P.ω.map ((α_ (SkeinObj.mk a : SkeinObj f)
        (SkeinObj.mk b) (SkeinObj.mk 1)).inv) =
        𝟙 (P.ω.obj (SkeinObj.mk (a + (b + 1)))) := by
      rw [show (α_ (SkeinObj.mk a : SkeinObj f)
          (SkeinObj.mk b) (SkeinObj.mk 1)).inv =
        𝟙 (SkeinObj.mk (a + (b + 1))) from by
        change bundleMapClass f (finCongr _) = _
        rw [show (finCongr (show a + (b + 1) = a + b + 1
            by omega) : Fin (a + (b + 1)) ≃
            Fin (a + (b + 1))) =
          _root_.Equiv.refl (Fin (a + (b + 1))) from
          _root_.Equiv.ext (fun x => Fin.ext rfl)]
        exact bundleMapClass_refl f (a + (b + 1))]
      exact P.ω.map_id _
    have hassoc : (P.ω.obj (SkeinObj.mk a) ◁
          μ P.ω (SkeinObj.mk b) (SkeinObj.mk 1)) ≫
        μ P.ω (SkeinObj.mk a) (SkeinObj.mk (b + 1)) =
        (α_ (P.ω.obj (SkeinObj.mk a))
          (P.ω.obj (SkeinObj.mk b))
          (P.ω.obj (SkeinObj.mk 1))).inv ≫
        (μ P.ω (SkeinObj.mk a) (SkeinObj.mk b) ▷
          P.ω.obj (SkeinObj.mk 1)) ≫
        μ P.ω (SkeinObj.mk (a + b)) (SkeinObj.mk 1) := by
      have h0 := Functor.LaxMonoidal.associativity_inv
        (F := P.ω) (SkeinObj.mk a) (SkeinObj.mk b)
        (SkeinObj.mk 1)
      rw [hα] at h0
      exact h0
    rw [Category.assoc, hassoc]
    -- Pull the associator across the transports.
    rw [show (stdToOmega f P e a ⊗ₘ
        (stdToOmega f P e b ⊗ₘ e)) ≫
      ((α_ (P.ω.obj (SkeinObj.mk a))
        (P.ω.obj (SkeinObj.mk b))
        (P.ω.obj (SkeinObj.mk 1))).inv ≫
      (μ P.ω (SkeinObj.mk a) (SkeinObj.mk b) ▷
        P.ω.obj (SkeinObj.mk 1)) ≫
      μ P.ω (SkeinObj.mk (a + b)) (SkeinObj.mk 1)) =
      (α_ (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).inv ≫
      (((stdToOmega f P e a ⊗ₘ stdToOmega f P e b) ⊗ₘ e) ≫
      (μ P.ω (SkeinObj.mk a) (SkeinObj.mk b) ▷
        P.ω.obj (SkeinObj.mk 1)) ≫
      μ P.ω (SkeinObj.mk (a + b)) (SkeinObj.mk 1)) from by
      rw [← Category.assoc, ← Category.assoc,
        MonoidalCategory.associator_inv_naturality,
        Category.assoc, Category.assoc]]
    -- Collect the whiskered merge through the induction.
    have htail : ((stdToOmega f P e a ⊗ₘ stdToOmega f P e b)
          ⊗ₘ e) ≫
        (μ P.ω (SkeinObj.mk a) (SkeinObj.mk b) ▷
          P.ω.obj (SkeinObj.mk 1)) ≫
        μ P.ω (SkeinObj.mk (a + b)) (SkeinObj.mk 1) =
        (powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ) ≫
          stdToOmega f P e (a + (b + 1)) := by
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (fun z => z ≫
        μ P.ω (SkeinObj.mk (a + b)) (SkeinObj.mk 1)) (show
          ((stdToOmega f P e a ⊗ₘ stdToOmega f P e b) ⊗ₘ e) ≫
            (μ P.ω (SkeinObj.mk a) (SkeinObj.mk b) ▷
              P.ω.obj (SkeinObj.mk 1)) =
          (((stdToOmega f P e a ⊗ₘ stdToOmega f P e b) ≫
            μ P.ω (SkeinObj.mk a) (SkeinObj.mk b)) ⊗ₘ e)
          from by
        rw [← MonoidalCategory.tensorHom_id,
          MonoidalCategory.tensorHom_comp_tensorHom,
          Category.comp_id])).trans ?_
      refine (congrArg (fun z => (z ⊗ₘ e) ≫
        μ P.ω (SkeinObj.mk (a + b)) (SkeinObj.mk 1))
        (stdToOmega_merge a b)).trans ?_
      refine (congrArg (fun z => z ≫
        μ P.ω (SkeinObj.mk (a + b)) (SkeinObj.mk 1)) (show
          ((powMerge (stdSuperPair k ℓ) a b ≫
            stdToOmega f P e (a + b)) ⊗ₘ e) =
          (powMerge (stdSuperPair k ℓ) a b ▷ stdSuperPair k ℓ) ≫
            (stdToOmega f P e (a + b) ⊗ₘ e) from by
        rw [← MonoidalCategory.tensorHom_id,
          MonoidalCategory.tensorHom_comp_tensorHom,
          Category.id_comp])).trans ?_
      exact Category.assoc _ _ _
    refine (congrArg (fun z =>
      (α_ (superPow (stdSuperPair k ℓ) a)
        (superPow (stdSuperPair k ℓ) b) (stdSuperPair k ℓ)).inv ≫ z)
      htail).trans ?_
    exact (Category.assoc _ _ _).symm

end RS
