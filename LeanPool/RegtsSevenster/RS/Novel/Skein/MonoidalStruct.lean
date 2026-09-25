/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.BundleMapClasses
import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTensor

/-!
# The monoidal structure data of the skein category

Tensor on objects is arity addition, tensor on morphisms is the
descended tensor, and every structural isomorphism — associator,
unitors — is the class of a cast bundle map.  The iso laws and
the coherence lemmas provable without the interchange law
(identity tensoring, pentagon, triangle) all collapse through the
bundle-map calculus.
-/

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The cast isomorphism between equal-arity objects. -/
noncomputable def castIso {n m : ℕ} (h : n = m) :
    (SkeinObj.mk n : SkeinObj f) ≅ SkeinObj.mk m where
  hom := bundleMapClass f (finCongr h)
  inv := bundleMapClass f (finCongr h.symm)
  hom_inv_id := by
    change HomSpace.comp f n m n
      (bundleMapClass f (finCongr h))
      (bundleMapClass f (finCongr h.symm)) =
      HomSpace.ofFragment f.val (strandBundle n)
    rw [bundleMapClass_comp,
      show (finCongr h).trans (finCongr h.symm) =
        _root_.Equiv.refl (Fin n) from
        _root_.Equiv.ext (fun x => Fin.ext rfl)]
    exact bundleMapClass_refl f n
  inv_hom_id := by
    change HomSpace.comp f m n m
      (bundleMapClass f (finCongr h.symm))
      (bundleMapClass f (finCongr h)) =
      HomSpace.ofFragment f.val (strandBundle m)
    rw [bundleMapClass_comp,
      show (finCongr h.symm).trans (finCongr h) =
        _root_.Equiv.refl (Fin m) from
        _root_.Equiv.ext (fun x => Fin.ext rfl)]
    exact bundleMapClass_refl f m

/-- **The monoidal structure** of the skein category. -/
noncomputable instance skeinMonoidalStruct :
    MonoidalCategoryStruct (SkeinObj f) where
  tensorObj X Y := ⟨X.arity + Y.arity⟩
  whiskerLeft X {Y₁ Y₂} p :=
    HomSpace.tensor f X.arity X.arity Y₁.arity Y₂.arity
      (HomSpace.ofFragment f.val (strandBundle X.arity)) p
  whiskerRight {X₁ X₂} p Y :=
    HomSpace.tensor f X₁.arity X₂.arity Y.arity Y.arity p
      (HomSpace.ofFragment f.val (strandBundle Y.arity))
  tensorHom {X₁ Y₁ X₂ Y₂} p q :=
    HomSpace.tensor f X₁.arity Y₁.arity X₂.arity Y₂.arity p q
  tensorUnit := ⟨0⟩
  associator X Y Z := castIso f
    (show (X.arity + Y.arity) + Z.arity =
      X.arity + (Y.arity + Z.arity) by omega)
  leftUnitor X := castIso f
    (show 0 + X.arity = X.arity by omega)
  rightUnitor X := castIso f
    (show X.arity + 0 = X.arity by omega)

/-- Tensoring bundle-map classes is the class of the block
sum. -/
theorem bundleMapClass_tensor {n₁ m₁ n₂ m₂ : ℕ}
    (e₁ : Fin n₁ ≃ Fin m₁) (e₂ : Fin n₂ ≃ Fin m₂) :
    HomSpace.tensor f n₁ m₁ n₂ m₂
        (bundleMapClass f e₁) (bundleMapClass f e₂) =
      bundleMapClass f (tensorMapEquiv e₁ e₂) := by
  rw [bundleMapClass, bundleMapClass,
    HomSpace.tensor_ofFragment]
  exact HomSpace.ofFragment_congr f (bundleMapTensor e₁ e₂)

/-- Tensoring identities is the identity (`tensor_id`). -/
theorem skein_tensor_id (X Y : SkeinObj f) :
    MonoidalCategoryStruct.tensorHom (𝟙 X) (𝟙 Y) =
      𝟙 (MonoidalCategoryStruct.tensorObj X Y) := by
  change HomSpace.tensor f X.arity X.arity Y.arity Y.arity
      (HomSpace.ofFragment f.val (strandBundle X.arity))
      (HomSpace.ofFragment f.val (strandBundle Y.arity)) =
    HomSpace.ofFragment f.val (strandBundle (X.arity + Y.arity))
  rw [HomSpace.tensor_ofFragment]
  exact HomSpace.ofFragment_congr f
    (strandBundleTensor X.arity Y.arity).symm

/-- The identity class is a bundle-map class. -/
theorem id_eq_bundleMapClass (n : ℕ) :
    HomSpace.ofFragment f.val (strandBundle n) =
      bundleMapClass f (_root_.Equiv.refl (Fin n)) :=
  (bundleMapClass_refl f n).symm

/-- Tensoring a bundle-map class with an identity strand on the
right. -/
theorem bundleMapClass_tensor_id_right {n₁ m₁ : ℕ} (k : ℕ)
    (e₁ : Fin n₁ ≃ Fin m₁) :
    HomSpace.tensor f n₁ m₁ k k (bundleMapClass f e₁)
        (HomSpace.ofFragment f.val (strandBundle k)) =
      bundleMapClass f
        (tensorMapEquiv e₁ (_root_.Equiv.refl (Fin k))) := by
  rw [id_eq_bundleMapClass, bundleMapClass_tensor]

/-- Tensoring a bundle-map class with an identity strand on the
left. -/
theorem bundleMapClass_tensor_id_left (k : ℕ) {n₂ m₂ : ℕ}
    (e₂ : Fin n₂ ≃ Fin m₂) :
    HomSpace.tensor f k k n₂ m₂
        (HomSpace.ofFragment f.val (strandBundle k))
        (bundleMapClass f e₂) =
      bundleMapClass f
        (tensorMapEquiv (_root_.Equiv.refl (Fin k)) e₂) := by
  rw [id_eq_bundleMapClass, bundleMapClass_tensor]

/-- The block transposes compose to the identity. -/
theorem transposeEquiv_trans_self (a b : ℕ) :
    (transposeEquiv a b).trans (transposeEquiv b a) =
      _root_.Equiv.refl (Fin (a + b)) := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  rcases Nat.lt_or_ge x.val a with hx | hx
  · rw [_root_.Equiv.trans_apply,
      show x = (⟨x.val, by omega⟩ : Fin (a + b)) from
        Fin.ext rfl,
      transposeEquiv_low a b x.val hx (by omega) (by omega),
      transposeEquiv_high b a x.val hx (by omega) (by omega)]
    rfl
  · rw [_root_.Equiv.trans_apply,
      show x = (⟨a + (x.val - a), by have := x.isLt; omega⟩ :
        Fin (a + b)) from Fin.ext (by
          change x.val = a + (x.val - a)
          omega),
      transposeEquiv_high a b (x.val - a)
        (by have := x.isLt; omega) (by have := x.isLt; omega)
        (by have := x.isLt; omega),
      transposeEquiv_low b a (x.val - a)
        (by have := x.isLt; omega) (by have := x.isLt; omega)
        (by have := x.isLt; omega)]
    rfl

/-- **The braiding isomorphism** of the skein category: the
block-transpose bundle map. -/
noncomputable def skeinBraiding (X Y : SkeinObj f) :
    MonoidalCategoryStruct.tensorObj X Y ≅
      MonoidalCategoryStruct.tensorObj Y X where
  hom := bundleMapClass f (transposeEquiv X.arity Y.arity)
  inv := bundleMapClass f (transposeEquiv Y.arity X.arity)
  hom_inv_id := by
    change HomSpace.comp f _ _ _
      (bundleMapClass f (transposeEquiv X.arity Y.arity))
      (bundleMapClass f (transposeEquiv Y.arity X.arity)) =
      HomSpace.ofFragment f.val
        (strandBundle (X.arity + Y.arity))
    rw [bundleMapClass_comp, transposeEquiv_trans_self]
    exact bundleMapClass_refl f _
  inv_hom_id := by
    change HomSpace.comp f _ _ _
      (bundleMapClass f (transposeEquiv Y.arity X.arity))
      (bundleMapClass f (transposeEquiv X.arity Y.arity)) =
      HomSpace.ofFragment f.val
        (strandBundle (Y.arity + X.arity))
    rw [bundleMapClass_comp, transposeEquiv_trans_self]
    exact bundleMapClass_refl f _

/-- The braiding is symmetric: swapping twice is the identity
(the `symmetry` axiom, at class level). -/
theorem skeinBraiding_symmetry (X Y : SkeinObj f) :
    (skeinBraiding f X Y).hom ≫ (skeinBraiding f Y X).hom =
      𝟙 (MonoidalCategoryStruct.tensorObj X Y) := by
  change HomSpace.comp f _ _ _
    (bundleMapClass f (transposeEquiv X.arity Y.arity))
    (bundleMapClass f (transposeEquiv Y.arity X.arity)) =
    HomSpace.ofFragment f.val (strandBundle (X.arity + Y.arity))
  rw [bundleMapClass_comp, transposeEquiv_trans_self]
  exact bundleMapClass_refl f _

end RS
