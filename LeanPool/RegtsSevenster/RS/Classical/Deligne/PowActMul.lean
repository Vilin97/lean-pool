/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PowAct

/-!
# Compatibility of the module-power action with the multiplication

Over an internal commutative monoid `A` and a module `X`, the module
powers and symmetric powers carry both a multiplication
(`SymMul.lean`) and an `A`-action (`PowAct.lean`).  This module
proves the two structures compatible: the multiplications are module
maps, in both factors — the statements that make the power algebras
into `A`-module algebras.

* `powTailAct_concat`: on the ambient tensor powers, routing the
  monoid to the tail of the second block and concatenating equals
  concatenating and acting on the tail of the product.  Because the
  concatenation folds on the right, this is a naturality of the
  concatenation against the action through the right factor.
* `modPowMul_actRight`/`symMul_actRight`: acting on the right
  factor, with the monoid carried past the left factor, equals
  multiplying and acting on the product.
* `modPowMul_braiding_exists`: the braiding of two module powers is,
  across the multiplications, the action of a block permutation —
  the descent of `tensorPowConcat_braiding_exists`.
* `modPowMul_actLeft`/`symMul_actLeft`: acting on the left factor
  equals multiplying and acting on the product; proved from the
  right version by braiding the factors, sliding the action across
  the braiding, and absorbing the block permutation through the
  equivariance of the descended action.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The action through the right factor against a concatenation -/

section RawConcat

/-- The action through the right factor of a tensor pair, with the
pair reassociated: carry the monoid past the first factor and act
through the second. -/
theorem actAcross_split_pair
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V₁ V₂ X : D) [ModObj A X] :
    (A ◁ (α_ V₁ V₂ X).inv) ≫ actAcross A (V₁ ⊗ V₂) X =
      (braidPast A V₁ (V₂ ⊗ X)).hom ≫ (V₁ ◁ actAcross A V₂ X) ≫
        (α_ V₁ V₂ X).inv := by
  rw [← cancel_mono (α_ V₁ V₂ X).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [actAcross_context_split A V₁ V₂ X, ← whiskerLeft_comp_assoc,
    Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

/-- **Naturality of a fold-and-collapse against the action**: acting
through the second factor of a pair and collapsing the pair onto a
codomain equals collapsing first and acting through the right factor
of the codomain. -/
theorem actAcross_concat_context
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A]
    (V₁ V₂ Q : D) (c : V₁ ⊗ V₂ ⟶ Q)
    (X : D) [ModObj A X] :
    (braidPast A V₁ (V₂ ⊗ X)).hom ≫ (V₁ ◁ actAcross A V₂ X) ≫
        ((α_ V₁ V₂ X).inv ≫ (c ▷ X)) =
      (A ◁ ((α_ V₁ V₂ X).inv ≫ (c ▷ X))) ≫ actAcross A Q X := by
  have h := whiskerLeft_associator_inv_actAcross A c X (𝟙 (Q ⊗ X))
  simp only [Category.comp_id] at h
  rw [h, reassoc_of% (actAcross_split_pair A V₁ V₂ X)]

/-- **The tail action passes the concatenation**: carrying the
monoid to the tail of the second block and concatenating equals
concatenating and acting on the tail of the product.  The
concatenation folds on the right, so the tail of the product is the
tail of the second block and no arity transport is needed. -/
theorem powTailAct_concat
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X]
    (m n : ℕ) :
    (braidPast A (tensorPow D X (m + 1))
          (tensorPow D X (n + 1))).hom ≫
        (tensorPow D X (m + 1) ◁ powTailAct A X n) ≫
        (tensorPowConcat X (m + 1) (n + 1)).hom =
      (A ◁ (tensorPowConcat X (m + 1) (n + 1)).hom) ≫
        powTailAct A X (m + 1 + n) :=
  actAcross_concat_context A (tensorPow D X (m + 1))
    (tensorPow D X n) (tensorPow D X (m + 1 + n))
    (tensorPowConcat X (m + 1) n).hom X

end RawConcat

/-! ## The multiplication as a module map, right factor -/

section ModLevel

/-- Morphisms out of a whiskered tensor pair of module powers are
determined by their composites with the tensored projections. -/
theorem modPowTensorLeft_hom_ext
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (P : D) (m n : ℕ) {Z : D}
    {k l : P ⊗ (modPow A X m ⊗ modPow A X n) ⟶ Z}
    (h : (P ◁ (modPowπ A X m ⊗ₘ modPowπ A X n)) ≫ k =
      (P ◁ (modPowπ A X m ⊗ₘ modPowπ A X n)) ≫ l) : k = l := by
  simp only [tensorHom_def, whiskerLeft_comp, Category.assoc] at h
  have h₂ := (cancel_epi (P ◁ (modPowπ A X m ▷ tensorPow D X n))).mp h
  rw [← Iso.cancel_iso_hom_left
    (α_ P (modPow A X m) (modPow A X n)) k l]
  apply modPow_whiskerLeft_hom_ext A X (P ⊗ modPow A X m) n
  simp only [associator_naturality_right_assoc]
  rw [h₂]

/-- The descended action passes an arity transport. -/
theorem modPowAct_cast
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    [MonoidalPreadditive D] [IsCommMonObj A]
    {a b : ℕ} (h : a + 1 = b + 1) :
    (A ◁ modPowCast A X h) ≫ modPowAct A X b =
      modPowAct A X a ≫ modPowCast A X h := by
  obtain rfl : a = b := by omega
  rw [modPowCast_irrel A X h rfl, modPowCast_rfl, whiskerLeft_id,
    Category.id_comp, Category.comp_id]

/-- **The raw multiplication is a module map in the right factor**:
acting on the right factor, with the monoid carried past the left
factor, equals multiplying and acting on the product. -/
theorem modPowMul_actRight
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    [MonoidalPreadditive D] [IsCommMonObj A]
    (m n : ℕ) :
    (braidPast A (modPow A X (m + 1)) (modPow A X (n + 1))).hom ≫
        (modPow A X (m + 1) ◁ modPowAct A X n) ≫
        modPowMul A X (m + 1) (n + 1) =
      (A ◁ modPowMul A X (m + 1) (n + 1)) ≫
        modPowAct A X (m + 1 + n) := by
  apply modPowTensorLeft_hom_ext A X A (m + 1) (n + 1)
  have hdef : (A ◁ modPowπ A X (m + 1 + (n + 1))) ≫
      modPowAct A X (m + 1 + n) =
        powTailAct A X (m + 1 + n) ≫
          modPowπ A X (m + 1 + (n + 1)) :=
    whiskerLeft_modPowπ_modPowAct A X (m + 1 + n)
  have hμ : (modPowπ A X (m + 1) ▷ tensorPow D X (n + 1)) ≫
      (modPow A X (m + 1) ◁ modPowπ A X (n + 1)) ≫
        modPowMul A X (m + 1) (n + 1) =
      (tensorPowConcat X (m + 1) (n + 1)).hom ≫
        modPowπ A X (m + 1 + (n + 1)) := by
    rw [← Category.assoc, ← tensorHom_def, modPowπ_tensor_modPowMul]
  conv_lhs => rw [tensorHom_def, whiskerLeft_comp, Category.assoc,
    braidPast_natural_tail_assoc, braidPast_natural_context_assoc,
    ← whiskerLeft_comp_assoc, whiskerLeft_modPowπ_modPowAct,
    whiskerLeft_comp, Category.assoc, ← whisker_exchange_assoc, hμ]
  conv_rhs => rw [← whiskerLeft_comp_assoc, modPowπ_tensor_modPowMul,
    whiskerLeft_comp, Category.assoc, hdef]
  rw [reassoc_of% (powTailAct_concat A X m n)]

end ModLevel

/-! ## Braiding the monoid out of a braided pair -/

section BraidCancel

/-- Braiding a pair with the monoid attached to its first factor,
then carrying the monoid back out of the second factor, is braiding
the bare pair under the monoid. -/
@[reassoc]
theorem associator_inv_braiding_braidPast_inv
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (A V T : D) :
    (α_ A V T).inv ≫ (β_ (A ⊗ V) T).hom ≫ (braidPast A T V).inv =
      A ◁ (β_ V T).hom := by
  rw [← cancel_mono (braidPast A T V).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [braidPast_hom, BraidedCategory.braiding_tensor_left_hom]
  simp only [Iso.inv_hom_id_assoc]

end BraidCancel

/-! ## The multiplication as a module map, left factor -/

section ModLeftLevel

/-- **The braiding of module powers is a block permutation across
the multiplications**: the descent of
`tensorPowConcat_braiding_exists` through the projections. -/
theorem modPowMul_braiding_exists
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    (m n : ℕ) :
    ∃ σ : Equiv.Perm (Fin (n + m)),
      (β_ (modPow A X m) (modPow A X n)).hom ≫ modPowMul A X n m =
        modPowMul A X m n ≫
          modPowCast A X (by omega : m + n = n + m) ≫
            modPowPerm (A := A) (X := X) (n + m) σ := by
  obtain ⟨σ, hσ⟩ := tensorPowConcat_braiding_exists X n m
  refine ⟨σ, ?_⟩
  apply modPowTensor_hom_ext A X m n
  conv_lhs => rw [← Category.assoc,
    BraidedCategory.braiding_naturality, Category.assoc,
    modPowπ_tensor_modPowMul]
  conv_rhs => rw [modPowπ_tensor_modPowMul_assoc, modPowπ_cast_assoc,
    modPowπ_perm]
  rw [reassoc_of% hσ]

/-- **The raw multiplication is a module map in the left factor**:
acting on the left factor equals multiplying and acting on the
product, with no braiding of the monoid past anything.  The action
slides from the tail of the left block to the tail of the product;
the slide is packaged through the braiding of the blocks, the
right-factor statement, and the equivariance of the descended
action. -/
theorem modPowMul_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    [IsCommMonObj A]
    (m n : ℕ) :
    (α_ A (modPow A X (m + 1)) (modPow A X (n + 1))).inv ≫
        (modPowAct A X m ▷ modPow A X (n + 1)) ≫
        modPowMul A X (m + 1) (n + 1) =
      (A ◁ modPowMul A X (m + 1) (n + 1)) ≫
        modPowAct A X (m + 1 + n) := by
  obtain ⟨σ, hσ⟩ := modPowMul_braiding_exists A X (m + 1) (n + 1)
  have hpp : modPowPerm (A := A) (X := X) (n + 1 + (m + 1)) σ ≫
      modPowPerm (A := A) (X := X) (n + 1 + (m + 1)) σ⁻¹ = 𝟙 _ := by
    rw [← modPowPerm_mul, inv_mul_cancel, modPowPerm_one]
  have hcc : ∀ {a b : ℕ} (h : a = b) (h' : b = a),
      modPowCast A X h ≫ modPowCast A X h' = 𝟙 (modPow A X a) := by
    intro a b h h'
    subst h
    rw [modPowCast_irrel A X h' rfl, modPowCast_rfl, Category.comp_id]
  have hA : (β_ (modPow A X (m + 1)) (modPow A X (n + 1))).hom ≫
      modPowMul A X (n + 1) (m + 1) ≫
        modPowPerm (A := A) (X := X) (n + 1 + (m + 1)) σ⁻¹ ≫
        modPowCast A X (by omega : n + 1 + (m + 1) = m + 1 + (n + 1)) =
      modPowMul A X (m + 1) (n + 1) := by
    rw [reassoc_of% hσ, reassoc_of% hpp, hcc, Category.comp_id]
  have hR : (modPow A X (n + 1) ◁ modPowAct A X m) ≫
      modPowMul A X (n + 1) (m + 1) =
        (braidPast A (modPow A X (n + 1)) (modPow A X (m + 1))).inv ≫
          (A ◁ modPowMul A X (n + 1) (m + 1)) ≫
          modPowAct A X (n + 1 + m) := by
    rw [← modPowMul_actRight A X n m, Iso.inv_hom_id_assoc]
  have hperm : (A ◁ modPowPerm (A := A) (X := X)
        (n + 1 + (m + 1)) σ) ≫ modPowAct A X (n + 1 + m) =
      modPowAct A X (n + 1 + m) ≫
        modPowPerm (A := A) (X := X) (n + 1 + (m + 1)) σ :=
    (modPowAct_perm A X (n + 1 + m) σ).symm
  have hac : (A ◁ modPowCast A X
        (by omega : m + 1 + (n + 1) = n + 1 + (m + 1))) ≫
      modPowAct A X (n + 1 + m) =
        modPowAct A X (m + 1 + n) ≫
          modPowCast A X
            (by omega : m + 1 + (n + 1) = n + 1 + (m + 1)) :=
    modPowAct_cast A X _
  conv_lhs => rw [← hA, BraidedCategory.braiding_naturality_left_assoc,
    reassoc_of% hR,
    reassoc_of% (associator_inv_braiding_braidPast_inv A
      (modPow A X (m + 1)) (modPow A X (n + 1))),
    ← whiskerLeft_comp_assoc, hσ]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% hperm, reassoc_of% hpp, reassoc_of% hac, hcc,
    Category.comp_id]

end ModLeftLevel

/-! ## The symmetric multiplication as a module map -/

section SymLevel

/-- Morphisms out of a whiskered tensor pair of symmetric powers
are determined by their composites with the tensored projections,
which are jointly split epi. -/
theorem symPowTensorLeft_hom_ext
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [Linear ℂ D]
    (P : D) (m n : ℕ) {Z : D}
    {k l : P ⊗ (symPow A X m ⊗ symPow A X n) ⟶ Z}
    (h : (P ◁ (symPowπ A X m ⊗ₘ symPowπ A X n)) ≫ k =
      (P ◁ (symPowπ A X m ⊗ₘ symPowπ A X n)) ≫ l) : k = l := by
  have hsec : (P ◁ (symPowσ A X m ⊗ₘ symPowσ A X n)) ≫
      (P ◁ (symPowπ A X m ⊗ₘ symPowπ A X n)) = 𝟙 _ := by
    rw [← whiskerLeft_comp, tensorHom_comp_tensorHom,
      symPowσ_symPowπ, symPowσ_symPowπ, tensorHom_id,
      id_whiskerRight, whiskerLeft_id]
  calc k = ((P ◁ (symPowσ A X m ⊗ₘ symPowσ A X n)) ≫
        (P ◁ (symPowπ A X m ⊗ₘ symPowπ A X n))) ≫ k := by
        rw [hsec, Category.id_comp]
    _ = ((P ◁ (symPowσ A X m ⊗ₘ symPowσ A X n)) ≫
        (P ◁ (symPowπ A X m ⊗ₘ symPowπ A X n))) ≫ l := by
        rw [Category.assoc, Category.assoc, h]
    _ = l := by rw [hsec, Category.id_comp]

/-- **The symmetric multiplication is a module map in the right
factor**: acting on the right factor, with the monoid carried past
the left factor, equals multiplying and acting on the product. -/
theorem symMul_actRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    [IsCommMonObj A]
    (m n : ℕ) :
    (braidPast A (symPow A X (m + 1)) (symPow A X (n + 1))).hom ≫
        (symPow A X (m + 1) ◁ symPowAct A X n) ≫
        symMul A X (m + 1) (n + 1) =
      (A ◁ symMul A X (m + 1) (n + 1)) ≫
        symPowAct A X (m + 1 + n) := by
  apply symPowTensorLeft_hom_ext A X A (m + 1) (n + 1)
  have hdef : (A ◁ symPowπ A X (m + 1 + (n + 1))) ≫
      symPowAct A X (m + 1 + n) =
        modPowAct A X (m + 1 + n) ≫
          symPowπ A X (m + 1 + (n + 1)) :=
    whiskerLeft_symPowπ_symPowAct A X (m + 1 + n)
  have hμ : (symPowπ A X (m + 1) ▷ modPow A X (n + 1)) ≫
      (symPow A X (m + 1) ◁ symPowπ A X (n + 1)) ≫
        symMul A X (m + 1) (n + 1) =
      modPowMul A X (m + 1) (n + 1) ≫
        symPowπ A X (m + 1 + (n + 1)) := by
    rw [← Category.assoc, ← tensorHom_def, symPowπ_tensor_symMul]
  conv_lhs => rw [tensorHom_def, whiskerLeft_comp, Category.assoc,
    braidPast_natural_tail_assoc, braidPast_natural_context_assoc,
    ← whiskerLeft_comp_assoc, whiskerLeft_symPowπ_symPowAct,
    whiskerLeft_comp, Category.assoc, ← whisker_exchange_assoc, hμ]
  conv_rhs => rw [← whiskerLeft_comp_assoc, symPowπ_tensor_symMul,
    whiskerLeft_comp, Category.assoc, hdef]
  rw [reassoc_of% (modPowMul_actRight A X m n)]

/-- **The symmetric multiplication is a module map in the left
factor**: acting on the left factor equals multiplying and acting
on the product, with no braiding of the monoid past anything. -/
theorem symMul_actLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (X : D) [ModObj A X] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Y)]
    [IsCommMonObj A]
    (m n : ℕ) :
    (α_ A (symPow A X (m + 1)) (symPow A X (n + 1))).inv ≫
        (symPowAct A X m ▷ symPow A X (n + 1)) ≫
        symMul A X (m + 1) (n + 1) =
      (A ◁ symMul A X (m + 1) (n + 1)) ≫
        symPowAct A X (m + 1 + n) := by
  apply symPowTensorLeft_hom_ext A X A (m + 1) (n + 1)
  have hdef : (A ◁ symPowπ A X (m + 1 + (n + 1))) ≫
      symPowAct A X (m + 1 + n) =
        modPowAct A X (m + 1 + n) ≫
          symPowπ A X (m + 1 + (n + 1)) :=
    whiskerLeft_symPowπ_symPowAct A X (m + 1 + n)
  have hμ : (symPowπ A X (m + 1) ▷ modPow A X (n + 1)) ≫
      (symPow A X (m + 1) ◁ symPowπ A X (n + 1)) ≫
        symMul A X (m + 1) (n + 1) =
      modPowMul A X (m + 1) (n + 1) ≫
        symPowπ A X (m + 1 + (n + 1)) := by
    rw [← Category.assoc, ← tensorHom_def, symPowπ_tensor_symMul]
  conv_lhs => rw [tensorHom_def, whiskerLeft_comp, Category.assoc,
    associator_inv_naturality_right_assoc,
    associator_inv_naturality_middle_assoc,
    whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    whiskerLeft_symPowπ_symPowAct, comp_whiskerRight,
    Category.assoc, hμ]
  conv_rhs => rw [← whiskerLeft_comp_assoc, symPowπ_tensor_symMul,
    whiskerLeft_comp, Category.assoc, hdef]
  rw [reassoc_of% (modPowMul_actLeft A X m n)]

end SymLevel

end RS
