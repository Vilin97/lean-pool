/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.MonoidalNat
public import LeanPool.RegtsSevenster.RS.Novel.Skein.MonoidalStruct

/-!
# The monoidal skein category

The `MonoidalCategory` instance on `SkeinObj f`: the interchange
on classes, the identity-strand tensor, the naturality squares,
and the coherence diagrams, all collapsing through the bundle-map
calculus.
-/

@[expose] public section

namespace RS

open CategoryTheory

/-- Block sums of casts are casts. -/
theorem tensorMapEquiv_finCongr {n₁ m₁ n₂ m₂ : ℕ}
    (h₁ : n₁ = m₁) (h₂ : n₂ = m₂) :
    tensorMapEquiv (finCongr h₁) (finCongr h₂) =
      finCongr (by omega) := by
  subst h₁
  subst h₂
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  rcases Nat.lt_or_ge x.val n₁ with hx | hx
  · rw [show x = Fin.castAdd n₂ ⟨x.val, hx⟩ from Fin.ext rfl,
      tensorMapEquiv_castAdd]
    rfl
  · rw [show x = Fin.natAdd n₁ ⟨x.val - n₁, by
        have := x.isLt
        omega⟩ from Fin.ext (by
        change x.val = n₁ + (x.val - n₁)
        omega),
      tensorMapEquiv_natAdd]
    rfl

/-- Tensoring an arity cast with the identity is again a cast. -/
theorem tensorMapEquiv_finCongr_refl_right {n₁ m₁ : ℕ}
    (h₁ : n₁ = m₁) (k : ℕ) :
    tensorMapEquiv (finCongr h₁) (_root_.Equiv.refl (Fin k)) =
      finCongr (by omega) := by
  rw [show (_root_.Equiv.refl (Fin k)) = finCongr rfl from
    _root_.Equiv.ext (fun _ => rfl), tensorMapEquiv_finCongr]

/-- And so is tensoring the identity with one. -/
theorem tensorMapEquiv_refl_finCongr_left (k : ℕ) {n₂ m₂ : ℕ}
    (h₂ : n₂ = m₂) :
    tensorMapEquiv (_root_.Equiv.refl (Fin k)) (finCongr h₂) =
      finCongr (by omega) := by
  rw [show (_root_.Equiv.refl (Fin k)) = finCongr rfl from
    _root_.Equiv.ext (fun _ => rfl), tensorMapEquiv_finCongr]

variable {R : ℕ} (f : EdgeRankParameter R)

/-- **The monoidal skein category.** -/
noncomputable instance skeinMonoidal :
    MonoidalCategory (SkeinObj f) where
  tensorHom_def {X₁ Y₁ X₂ Y₂} p q := by
    change HomSpace.tensor f X₁.arity Y₁.arity X₂.arity Y₂.arity
        p q =
      HomSpace.comp f (X₁.arity + X₂.arity)
        (Y₁.arity + X₂.arity) (Y₁.arity + Y₂.arity)
        (HomSpace.tensor f X₁.arity Y₁.arity X₂.arity X₂.arity
          p (HomSpace.ofFragment f.val (strandBundle X₂.arity)))
        (HomSpace.tensor f Y₁.arity Y₁.arity X₂.arity Y₂.arity
          (HomSpace.ofFragment f.val (strandBundle Y₁.arity)) q)
    rw [← HomSpace.tensor_comp, HomSpace.comp_id_right,
      HomSpace.comp_id_left]
  id_tensorHom_id X₁ X₂ := skein_tensor_id f X₁ X₂
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} p₁ p₂ q₁ q₂ :=
    (HomSpace.tensor_comp f p₁ q₁ p₂ q₂).symm
  whiskerLeft_id X Y := skein_tensor_id f X Y
  id_whiskerRight X Y := skein_tensor_id f X Y
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} p₁ p₂ p₃ :=
    assocNat_class f p₁ p₂ p₃
  leftUnitor_naturality {X Y} p := leftUnitNat_class f p
  rightUnitor_naturality {X Y} p := rightUnitNat_class f p
  pentagon W X Y Z := by
    change HomSpace.comp f _ _ _
        (HomSpace.tensor f _ _ _ _
          (bundleMapClass f (finCongr _))
          (HomSpace.ofFragment f.val (strandBundle Z.arity)))
        (HomSpace.comp f _ _ _
          (bundleMapClass f (finCongr _))
          (HomSpace.tensor f _ _ _ _
            (HomSpace.ofFragment f.val (strandBundle W.arity))
            (bundleMapClass f (finCongr _)))) =
      HomSpace.comp f _ _ _
        (bundleMapClass f (finCongr _))
        (bundleMapClass f (finCongr _))
    rw [bundleMapClass_tensor_id_right,
      tensorMapEquiv_finCongr_refl_right,
      bundleMapClass_tensor_id_left,
      tensorMapEquiv_refl_finCongr_left,
      bundleMapClass_comp, bundleMapClass_comp,
      bundleMapClass_comp]
    exact bundleMapClass_congr f
      (_root_.Equiv.ext (fun x => Fin.ext rfl))
  triangle X Y := by
    change HomSpace.comp f _ _ _
        (bundleMapClass f (finCongr _))
        (HomSpace.tensor f _ _ _ _
          (HomSpace.ofFragment f.val (strandBundle X.arity))
          (bundleMapClass f (finCongr _))) =
      HomSpace.tensor f _ _ _ _
        (bundleMapClass f (finCongr _))
        (HomSpace.ofFragment f.val (strandBundle Y.arity))
    rw [bundleMapClass_tensor_id_left,
      tensorMapEquiv_refl_finCongr_left,
      bundleMapClass_tensor_id_right,
      tensorMapEquiv_finCongr_refl_right,
      bundleMapClass_comp]
    exact bundleMapClass_congr f
      (_root_.Equiv.ext (fun x => Fin.ext rfl))

end RS
