/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.StdTransport
import LeanPool.RegtsSevenster.RS.Classical.Super.PowBraid

/-!
# The skein-side adjacent braiding and the transport intertwining

The adjacent braiding of strands in the skein category, mirroring
`powBraid`'s recursion, and the key intertwining: the model
transport `stdToOmega` conjugates the skein braiding into the
model braiding.  The top square is proved abstractly for any
braided monoidal functor — where every rewrite fires — and the
strictness of the skein associator enters only through a small
concrete collapse.
-/

namespace RS

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- **The abstract top braiding square**: for a braided monoidal
functor, transporting two point identifications through the
structure maps intertwines the associator-conjugated braiding of
the last two factors. -/
theorem braid_top_intertwine {C D : Type*} [Category C]
    [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxBraided] {PA PX : D}
    {A X : C} (tA : PA ⟶ F.obj A) (tx : PX ⟶ F.obj X) :
    (((tA ⊗ₘ tx) ≫ μ F A X) ⊗ₘ tx) ≫ μ F (A ⊗ X) X ≫
        F.map ((α_ A X X).hom ≫ (A ◁ (β_ X X).hom) ≫
          (α_ A X X).inv) =
      (α_ PA PX PX).hom ≫ (PA ◁ (β_ PX PX).hom) ≫
        (α_ PA PX PX).inv ≫
        (((tA ⊗ₘ tx) ≫ μ F A X) ⊗ₘ tx) ≫ μ F (A ⊗ X) X := by
  rw [show (((tA ⊗ₘ tx) ≫ μ F A X) ⊗ₘ tx) =
      (((tA ⊗ₘ tx) ⊗ₘ tx) ≫ (μ F A X ▷ F.obj X)) from by
    rw [← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id]]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.LaxMonoidal.associativity_assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [Functor.LaxBraided.braided]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  rw [MonoidalCategory.associator_naturality_assoc]
  have hmove : (tA ⊗ₘ (tx ⊗ₘ tx)) ≫
      (F.obj A ◁ (β_ (F.obj X) (F.obj X)).hom) =
      (PA ◁ (β_ PX PX).hom) ≫ (tA ⊗ₘ (tx ⊗ₘ tx)) := by
    rw [← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id,
      BraidedCategory.braiding_naturality]
    rw [show tA ⊗ₘ ((β_ PX PX).hom ≫ (tx ⊗ₘ tx)) =
        (𝟙 PA ⊗ₘ (β_ PX PX).hom) ≫ (tA ⊗ₘ (tx ⊗ₘ tx)) from by
      rw [MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp]]
    rw [MonoidalCategory.id_tensorHom]
  rw [reassoc_of% hmove]
  rw [Functor.LaxMonoidal.associativity_inv]
  rw [MonoidalCategory.associator_inv_naturality_assoc]

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The skein-side adjacent braiding at position `i`. -/
noncomputable def skeinPowBraid :
    (n : ℕ) → (i : ℕ) → i + 2 ≤ n →
      ((SkeinObj.mk n : SkeinObj f) ⟶ SkeinObj.mk n)
  | 0, _, h => absurd h (by omega)
  | 1, _, h => absurd h (by omega)
  | n + 2, i, h =>
    if hi : i = n then
      (SkeinObj.mk n : SkeinObj f) ◁
        (β_ (SkeinObj.mk 1 : SkeinObj f) (SkeinObj.mk 1)).hom
    else (skeinPowBraid (n + 1) i (by omega)) ▷ SkeinObj.mk 1

/-- The skein associator at concrete arities collapses to the
identity. -/
theorem skein_associator_collapse (n : ℕ) :
    (α_ (SkeinObj.mk n : SkeinObj f) (SkeinObj.mk 1)
      (SkeinObj.mk 1)).hom = 𝟙 (SkeinObj.mk (n + 2)) := by
  change bundleMapClass f (finCongr _) = _
  rw [show (finCongr (show n + 1 + 1 = n + (1 + 1) by omega) :
      Fin (n + 2) ≃ Fin (n + 2)) =
    _root_.Equiv.refl (Fin (n + 2)) from
    _root_.Equiv.ext (fun x => Fin.ext rfl)]
  exact bundleMapClass_refl f (n + 2)

/-- The inverse skein associator at concrete arities collapses to
the identity. -/
theorem skein_associator_inv_collapse (n : ℕ) :
    (α_ (SkeinObj.mk n : SkeinObj f) (SkeinObj.mk 1)
      (SkeinObj.mk 1)).inv = 𝟙 (SkeinObj.mk (n + 2)) := by
  change bundleMapClass f (finCongr _) = _
  rw [show (finCongr (show n + (1 + 1) = n + 1 + 1 by omega) :
      Fin (n + 2) ≃ Fin (n + 2)) =
    _root_.Equiv.refl (Fin (n + 2)) from
    _root_.Equiv.ext (fun x => Fin.ext rfl)]
  exact bundleMapClass_refl f (n + 2)

variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))

-- Raised budget: the intertwining is proved by recursion on the
-- arity with a top and a lower case, each unfolding the transport
-- and the braiding.
/-- **The transport intertwining**: the model transport carries
the skein-side adjacent braiding to the model-side adjacent
braiding. -/
theorem stdToOmega_powBraid :
    ∀ (n i : ℕ) (h : i + 2 ≤ n),
      letI := P.braided
      stdToOmega f P e n ≫ P.ω.map (skeinPowBraid f n i h) =
        powBraid (stdSuperPair k ℓ) n i h ≫ stdToOmega f P e n
  | 0, _, h => absurd h (by omega)
  | 1, _, h => absurd h (by omega)
  | n + 2, i, h => by
    let := P.braided
    by_cases hi : i = n
    · -- ═══════ Top case ═══════
      rw [show skeinPowBraid f (n + 2) i h =
          (SkeinObj.mk n : SkeinObj f) ◁
            (β_ (SkeinObj.mk 1 : SkeinObj f)
              (SkeinObj.mk 1)).hom from dite_eq_left hi]
      rw [show powBraid (stdSuperPair k ℓ) (n + 2) i h =
          topBraid (stdSuperPair k ℓ) n from dite_eq_left hi]
      have hcollapse :
          ((SkeinObj.mk n : SkeinObj f) ◁
            (β_ (SkeinObj.mk 1 : SkeinObj f)
              (SkeinObj.mk 1)).hom) =
          (α_ (SkeinObj.mk n : SkeinObj f) (SkeinObj.mk 1)
            (SkeinObj.mk 1)).hom ≫
          ((SkeinObj.mk n : SkeinObj f) ◁
            (β_ (SkeinObj.mk 1 : SkeinObj f)
              (SkeinObj.mk 1)).hom) ≫
          (α_ (SkeinObj.mk n : SkeinObj f) (SkeinObj.mk 1)
            (SkeinObj.mk 1)).inv := by
        rw [skein_associator_collapse,
          skein_associator_inv_collapse]
        exact ((Category.id_comp _).trans
          (Category.comp_id _)).symm
      have habs := braid_top_intertwine P.ω
        (stdToOmega f P e n) e
      refine Eq.trans ?_ habs
      exact congrArg (fun z =>
        (((stdToOmega f P e n ⊗ₘ e) ≫
          μ P.ω (SkeinObj.mk n) (SkeinObj.mk 1)) ⊗ₘ e) ≫
        μ P.ω (SkeinObj.mk n ⊗ SkeinObj.mk 1)
          (SkeinObj.mk 1) ≫ P.ω.map z) hcollapse
    · -- ═══════ Whisker case ═══════
      have hle : i + 2 ≤ n + 1 := by omega
      rw [show skeinPowBraid f (n + 2) i h =
          (skeinPowBraid f (n + 1) i hle) ▷ SkeinObj.mk 1 from
        dite_eq_right hi]
      rw [show powBraid (stdSuperPair k ℓ) (n + 2) i h =
          (powBraid (stdSuperPair k ℓ) (n + 1) i hle) ▷
            stdSuperPair k ℓ from dite_eq_right hi]
      change ((stdToOmega f P e (n + 1) ⊗ₘ e) ≫
          μ P.ω (SkeinObj.mk (n + 1)) (SkeinObj.mk 1)) ≫
        P.ω.map ((skeinPowBraid f (n + 1) i hle) ▷
          SkeinObj.mk 1) =
        (powBraid (stdSuperPair k ℓ) (n + 1) i hle ▷
          stdSuperPair k ℓ) ≫ stdToOmega f P e (n + 2)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun z =>
        (stdToOmega f P e (n + 1) ⊗ₘ e) ≫ z)
        (Functor.LaxMonoidal.μ_natural_left P.ω
          (skeinPowBraid f (n + 1) i hle)
          (SkeinObj.mk 1)).symm).trans ?_
      refine ((Category.assoc _ _ _).symm).trans ?_
      refine (congrArg (fun z => z ≫
        μ P.ω (SkeinObj.mk (n + 1)) (SkeinObj.mk 1)) (show
          (stdToOmega f P e (n + 1) ⊗ₘ e) ≫
            (P.ω.map (skeinPowBraid f (n + 1) i hle) ▷
              P.ω.obj (SkeinObj.mk 1)) =
          ((stdToOmega f P e (n + 1) ≫
            P.ω.map (skeinPowBraid f (n + 1) i hle)) ⊗ₘ e)
          from by
        rw [← MonoidalCategory.tensorHom_id,
          MonoidalCategory.tensorHom_comp_tensorHom,
          Category.comp_id])).trans ?_
      refine (congrArg (fun z => (z ⊗ₘ e) ≫
        μ P.ω (SkeinObj.mk (n + 1)) (SkeinObj.mk 1))
        (stdToOmega_powBraid (n + 1) i hle)).trans ?_
      refine (congrArg (fun z => z ≫
        μ P.ω (SkeinObj.mk (n + 1)) (SkeinObj.mk 1)) (show
          ((powBraid (stdSuperPair k ℓ) (n + 1) i hle ≫
            stdToOmega f P e (n + 1)) ⊗ₘ e) =
          (powBraid (stdSuperPair k ℓ) (n + 1) i hle ▷
            stdSuperPair k ℓ) ≫ (stdToOmega f P e (n + 1) ⊗ₘ e)
          from by
        rw [← MonoidalCategory.tensorHom_id,
          MonoidalCategory.tensorHom_comp_tensorHom,
          Category.id_comp])).trans ?_
      exact Category.assoc _ _ _

end RS
