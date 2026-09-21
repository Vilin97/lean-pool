/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.KaroubiMonoidal

/-!
# Rigidity of the Karoubi envelope

For a right rigid monoidal category `C`, the Karoubi envelope is
right rigid: the dual of an idempotent `(X, p)` is `(Xᘁ, pᘁ)`,
the adjoint mate of `p` being idempotent by contravariant
functoriality of the mate.  The coevaluation and evaluation are
the idempotent-corrected cup and cap; the snake identities reduce
to the base category's by sliding the idempotents around the cup
and cap — the first collapses onto the defining formula of the
adjoint mate, the second onto the base snake identity.

When `C` is moreover braided, `Karoubi C` is rigid.
-/

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents
open CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u}

/-! ### Componentwise access to the Karoubi monoidal data -/

private theorem kwl_f [Category.{v} C] [MonoidalCategory C]
    (P : Karoubi C) {Q R : Karoubi C}
    (g : Q ⟶ R) : (P ◁ g).f = P.p ⊗ₘ g.f := rfl

private theorem kwr_f [Category.{v} C] [MonoidalCategory C]
    {Q R : Karoubi C} (g : Q ⟶ R)
    (P : Karoubi C) : (g ▷ P).f = g.f ⊗ₘ P.p := rfl

private theorem kassoc_inv_f [Category.{v} C] [MonoidalCategory C]
    (P Q R : Karoubi C) :
    (α_ P Q R).inv.f =
      (P.p ⊗ₘ (Q.p ⊗ₘ R.p)) ≫ (α_ P.X Q.X R.X).inv := rfl

private theorem kassoc_hom_f [Category.{v} C] [MonoidalCategory C]
    (P Q R : Karoubi C) :
    (α_ P Q R).hom.f =
      ((P.p ⊗ₘ Q.p) ⊗ₘ R.p) ≫ (α_ P.X Q.X R.X).hom := rfl

private theorem krho_hom_f [Category.{v} C] [MonoidalCategory C]
    (P : Karoubi C) :
    (ρ_ P).hom.f = (P.p ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ P.X).hom := rfl

private theorem krho_inv_f [Category.{v} C] [MonoidalCategory C]
    (P : Karoubi C) :
    (ρ_ P).inv.f = P.p ≫ (ρ_ P.X).inv := rfl

private theorem klam_hom_f [Category.{v} C] [MonoidalCategory C]
    (P : Karoubi C) :
    (λ_ P).hom.f = (𝟙 (𝟙_ C) ⊗ₘ P.p) ≫ (λ_ P.X).hom := rfl

private theorem klam_inv_f [Category.{v} C] [MonoidalCategory C]
    (P : Karoubi C) :
    (λ_ P).inv.f = P.p ≫ (λ_ P.X).inv := rfl

/-! ### The dual idempotent -/

/-- The adjoint mate of an idempotent is idempotent. -/
theorem mate_idem [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    (P.p)ᘁ ≫ (P.p)ᘁ = (P.p)ᘁ := by
  rw [← comp_rightAdjointMate, P.idem]

/-- The right dual object in the Karoubi envelope. -/
noncomputable def karoubiRightDualObj
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    Karoubi C :=
  ⟨(P.X)ᘁ, (P.p)ᘁ, mate_idem P⟩

/-! ### Cup and cap absorption -/

/-- The corrected coevaluation absorbs into a single whisker on
the dual leg. -/
theorem coev_corr_left
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ) =
      η_ P.X (P.X)ᘁ ≫ P.X ◁ (P.p)ᘁ := by
  rw [tensorHom_def, ← assoc, ← coevaluation_comp_rightAdjointMate,
    assoc, ← MonoidalCategory.whiskerLeft_comp, mate_idem]

/-- The corrected coevaluation absorbs into a single whisker on
the primal leg. -/
theorem coev_corr_right
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ) =
      η_ P.X (P.X)ᘁ ≫ P.p ▷ (P.X)ᘁ := by
  rw [coev_corr_left, coevaluation_comp_rightAdjointMate]

/-- The corrected evaluation absorbs into a single whisker on the
primal leg. -/
theorem ev_corr_left
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    ((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ =
      (P.X)ᘁ ◁ P.p ≫ ε_ P.X (P.X)ᘁ := by
  rw [tensorHom_def, assoc, ← rightAdjointMate_comp_evaluation,
    ← assoc, ← comp_whiskerRight, mate_idem,
    rightAdjointMate_comp_evaluation]

/-- The corrected evaluation absorbs into a single whisker on the
dual leg. -/
theorem ev_corr_right
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    ((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ =
      (P.p)ᘁ ▷ P.X ≫ ε_ P.X (P.X)ᘁ := by
  rw [ev_corr_left, ← rightAdjointMate_comp_evaluation]

/-- The corrected coevaluation is stable under the correction. -/
theorem coev_corr_idem
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    (η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ)) ≫ (P.p ⊗ₘ (P.p)ᘁ) =
      η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ) := by
  rw [assoc, tensorHom_comp_tensorHom, P.idem, mate_idem]

/-- The corrected evaluation is stable under the correction. -/
theorem ev_corr_idem
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    ((P.p)ᘁ ⊗ₘ P.p) ≫ (((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ) =
      ((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ := by
  rw [← assoc, tensorHom_comp_tensorHom, P.idem, mate_idem]

/-! ### The snake identities, componentwise -/

/-- **The first snake** in the base category, with corrections:
collapses onto the defining formula of the adjoint mate. -/
theorem karoubi_snake_one
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    ((P.p)ᘁ ⊗ₘ (η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ))) ≫
      (((P.p)ᘁ ⊗ₘ (P.p ⊗ₘ (P.p)ᘁ)) ≫
        (α_ (P.X)ᘁ P.X (P.X)ᘁ).inv) ≫
      ((((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ) ⊗ₘ (P.p)ᘁ) =
    (((P.p)ᘁ ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (P.X)ᘁ).hom) ≫
      ((P.p)ᘁ ≫ (λ_ (P.X)ᘁ).inv) := by
  simp only [assoc]
  -- Merge the first two factors, absorbing the doubled
  -- correction.
  slice_lhs 1 2 =>
    rw [tensorHom_comp_tensorHom, mate_idem, coev_corr_idem]
  -- Single-whisker forms of the cup and cap.
  rw [coev_corr_left, ev_corr_right]
  -- Decompose the tensors into whiskers.
  rw [tensorHom_def' ((P.p)ᘁ)
      (η_ P.X (P.X)ᘁ ≫ P.X ◁ (P.p)ᘁ),
    tensorHom_def ((P.p)ᘁ ▷ P.X ≫ ε_ P.X (P.X)ᘁ) ((P.p)ᘁ),
    MonoidalCategory.whiskerLeft_comp, comp_whiskerRight]
  simp only [assoc]
  -- Chain: Xᘁ◁η ∘ Xᘁ◁(X◁d) ∘ d▷(X⊗Xᘁ) ∘ α⁻¹ ∘ (d▷X)▷Xᘁ
  --        ∘ ε▷Xᘁ ∘ 𝟙◁d.
  slice_lhs 3 4 => rw [associator_inv_naturality_left]
  slice_lhs 4 5 =>
    rw [← comp_whiskerRight, ← comp_whiskerRight, mate_idem]
  slice_lhs 4 5 =>
    rw [← comp_whiskerRight, rightAdjointMate_comp_evaluation,
      comp_whiskerRight]
  slice_lhs 2 3 => rw [associator_inv_naturality_right]
  slice_lhs 3 4 => rw [whisker_exchange]
  slice_lhs 4 5 => rw [whisker_exchange]
  slice_lhs 5 6 =>
    rw [← MonoidalCategory.whiskerLeft_comp, mate_idem]
  slice_lhs 2 3 => rw [← associator_inv_naturality_middle]
  -- The first four factors are the mate's defining composite.
  have hmate : (P.p)ᘁ =
      (ρ_ ((P.X)ᘁ)).inv ≫ ((P.X)ᘁ ◁ η_ P.X (P.X)ᘁ) ≫
        ((P.X)ᘁ ◁ P.p ▷ (P.X)ᘁ) ≫
        (α_ ((P.X)ᘁ) P.X ((P.X)ᘁ)).inv ≫
        (ε_ P.X (P.X)ᘁ ▷ (P.X)ᘁ) ≫ (λ_ ((P.X)ᘁ)).hom := rfl
  have hS : ((P.X)ᘁ ◁ η_ P.X (P.X)ᘁ) ≫
      ((P.X)ᘁ ◁ P.p ▷ (P.X)ᘁ) ≫
      (α_ ((P.X)ᘁ) P.X ((P.X)ᘁ)).inv ≫
      (ε_ P.X (P.X)ᘁ ▷ (P.X)ᘁ) =
      (ρ_ ((P.X)ᘁ)).hom ≫ (P.p)ᘁ ≫ (λ_ ((P.X)ᘁ)).inv := by
    conv_rhs => rw [hmate]
    simp
  simp only [assoc]
  rw [reassoc_of% hS]
  -- Fold the trailing unit-side whisker into the mate.
  rw [← leftUnitor_inv_naturality]
  slice_lhs 2 3 => rw [mate_idem]
  -- Normalize the right-hand side.
  rw [tensorHom_id]
  slice_rhs 1 2 => rw [rightUnitor_naturality]
  slice_rhs 2 3 => rw [mate_idem]

/-- **The second snake** in the base category, with corrections:
collapses onto the base snake identity. -/
theorem karoubi_snake_two
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    ((η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ)) ⊗ₘ P.p) ≫
      (((P.p ⊗ₘ (P.p)ᘁ) ⊗ₘ P.p) ≫
        (α_ P.X (P.X)ᘁ P.X).hom) ≫
      (P.p ⊗ₘ (((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ)) =
    ((𝟙 (𝟙_ C) ⊗ₘ P.p) ≫ (λ_ P.X).hom) ≫
      (P.p ≫ (ρ_ P.X).inv) := by
  simp only [assoc]
  -- Merge the first two factors, absorbing the doubled
  -- correction.
  slice_lhs 1 2 =>
    rw [tensorHom_comp_tensorHom, P.idem, coev_corr_idem]
  -- Single-whisker forms of the cup and cap.
  rw [coev_corr_right, ev_corr_left]
  -- Decompose the tensors into whiskers.
  rw [tensorHom_def (η_ P.X (P.X)ᘁ ≫ P.p ▷ (P.X)ᘁ) P.p,
    tensorHom_def' P.p
      ((P.X)ᘁ ◁ P.p ≫ ε_ P.X (P.X)ᘁ),
    comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  simp only [assoc]
  -- Chain: η▷X ∘ (p▷Xᘁ)▷X ∘ (X⊗Xᘁ)◁p ∘ α ∘ p▷(Xᘁ⊗X)
  --        ∘ X◁(Xᘁ◁p) ∘ X◁ε.
  slice_lhs 3 4 => rw [associator_naturality_right]
  slice_lhs 4 5 =>
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp, P.idem]
  -- Trade the cup correction to the dual leg.
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight, ← coev_corr_right, coev_corr_left,
      comp_whiskerRight]
  slice_lhs 2 3 => rw [associator_naturality_middle]
  -- Absorb the doubled mate into the cap.
  slice_lhs 4 5 =>
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← rightAdjointMate_comp_evaluation]
  slice_lhs 3 4 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← assoc,
      ← comp_whiskerRight, mate_idem]
  rw [rightAdjointMate_comp_evaluation,
    MonoidalCategory.whiskerLeft_comp]
  simp only [assoc]
  -- Slide the cap correction out to the unit edge.
  slice_lhs 2 3 => rw [← associator_naturality_right]
  slice_lhs 1 2 => rw [← whisker_exchange]
  -- The base snake finishes.
  slice_lhs 2 4 => rw [ExactPairing.evaluation_coevaluation]
  slice_lhs 1 2 => rw [leftUnitor_naturality]
  slice_lhs 3 4 => rw [← rightUnitor_inv_naturality]
  slice_lhs 2 3 => rw [P.idem]
  -- Normalize the right-hand side.
  rw [id_tensorHom]
  slice_rhs 1 2 => rw [leftUnitor_naturality]
  slice_rhs 2 3 => rw [P.idem]

/-! ### The exact pairing and rigidity -/

/-- The exact pairing between an idempotent and its mate dual. -/
noncomputable def karoubiExactPairing
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    ExactPairing P (karoubiRightDualObj P) where
  coevaluation' :=
    ⟨η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ), by
      show 𝟙 (𝟙_ C) ≫ (η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ)) ≫
          (P.p ⊗ₘ (P.p)ᘁ) =
        η_ P.X (P.X)ᘁ ≫ (P.p ⊗ₘ (P.p)ᘁ)
      rw [id_comp]
      exact coev_corr_idem P⟩
  evaluation' :=
    ⟨((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ, by
      show ((P.p)ᘁ ⊗ₘ P.p) ≫
          ((((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ) ≫ 𝟙 (𝟙_ C)) =
        ((P.p)ᘁ ⊗ₘ P.p) ≫ ε_ P.X (P.X)ᘁ
      rw [comp_id]
      exact ev_corr_idem P⟩
  coevaluation_evaluation' := by
    apply Karoubi.hom_ext
    simp only [Karoubi.comp_f]
    rw [kwl_f, kwr_f, kassoc_inv_f, krho_hom_f, klam_inv_f]
    exact karoubi_snake_one P
  evaluation_coevaluation' := by
    apply Karoubi.hom_ext
    simp only [Karoubi.comp_f]
    rw [kwr_f, kwl_f, kassoc_hom_f, klam_hom_f, krho_inv_f]
    exact karoubi_snake_two P

/-- Every Karoubi object has a right dual: the ambient dual, cut by
the dual idempotent. -/
noncomputable instance karoubiHasRightDual
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    (P : Karoubi C) :
    HasRightDual P where
  rightDual := karoubiRightDualObj P
  exact := karoubiExactPairing P

/-- **The Karoubi envelope of a right rigid category is right
rigid.** -/
noncomputable instance karoubiRightRigid
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C] :
    RightRigidCategory (Karoubi C) where

/-- **The Karoubi envelope of a braided right rigid category is
rigid.** -/
noncomputable instance karoubiRigid
    [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [BraidedCategory C] :
    RigidCategory (Karoubi C) :=
  BraidedCategory.rigidCategoryOfRightRigidCategory

end RS
