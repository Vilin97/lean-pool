/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorExact

/-!
# Sections through the dual: the reduction of 2.10

Deligne reduces local splitting of a general short exact sequence
to sequences ending at the unit: a section of an epimorphism onto
`C` is the same thing as a unit-side lifting through the left
dual.  This is the pure rigid-adjunction kernel of that reduction;
the splitting-algebra argument then only ever meets maps out of
the unit.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-- The dual-side comparison point: the image of the right unitor
under the duality adjunction — the coevaluation-flavoured map the
liftings are measured against. -/
noncomputable def dualUnitPoint
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    (C : A) : 𝟙_ A ⟶ (ᘁC) ⊗ C :=
  tensorLeftHomEquiv (𝟙_ A) (ᘁC) C C (ρ_ C).hom

/-- **Sections through the dual**: an epimorphism onto `C` admits
a section exactly when the dual-side unit map lifts through it. -/
theorem exists_section_iff_unit_lift
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    {B C : A} (b : B ⟶ C) :
    (∃ t : C ⟶ B, t ≫ b = 𝟙 C) ↔
    (∃ s : 𝟙_ A ⟶ (ᘁC) ⊗ B,
      s ≫ ((ᘁC) ◁ b) = dualUnitPoint C) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨tensorLeftHomEquiv (𝟙_ A) (ᘁC) C B
      ((ρ_ C).hom ≫ t), ?_⟩
    rw [dualUnitPoint, ← tensorLeftHomEquiv_naturality]
    congr 1
    rw [Category.assoc, ht, Category.comp_id]
  · rintro ⟨s, hs⟩
    refine ⟨(ρ_ C).inv ≫
      (tensorLeftHomEquiv (𝟙_ A) (ᘁC) C B).symm s, ?_⟩
    have hnat : (tensorLeftHomEquiv (𝟙_ A) (ᘁC) C B).symm s ≫ b =
        (tensorLeftHomEquiv (𝟙_ A) (ᘁC) C C).symm
          (s ≫ ((ᘁC) ◁ b)) := by
      apply (tensorLeftHomEquiv (𝟙_ A) (ᘁC) C C).injective
      rw [tensorLeftHomEquiv_naturality, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    rw [Category.assoc, hnat, hs, dualUnitPoint,
      Equiv.symm_apply_apply, Iso.inv_hom_id]

section Pullback

open Limits

/-- The unit-ending object of the reduction: the preimage of the
dual-side unit point inside the dual-twisted middle term. -/
noncomputable def unitEnd
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A] [Abelian A]
    {B C : A} (b : B ⟶ C) : A :=
  pullback ((ᘁC) ◁ b) (dualUnitPoint C)

/-- Its projection to the unit. -/
noncomputable def unitEndProj
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A] [Abelian A]
    {B C : A} (b : B ⟶ C) :
    unitEnd b ⟶ 𝟙_ A :=
  pullback.snd _ _

/-- The kernel of the second pullback projection is the kernel of
the first leg. -/
noncomputable def kernelPullbackSndIso [Category.{v} A] [Abelian A]
    {X Y Z : A} (f : X ⟶ Z)
    (g : Y ⟶ Z) :
    kernel (pullback.snd f g) ≅ kernel f := by
  refine ⟨kernel.lift f
      (kernel.ι (pullback.snd f g) ≫ pullback.fst f g) ?_,
    kernel.lift (pullback.snd f g)
      (pullback.lift (kernel.ι f) 0 ?_) ?_, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc,
      kernel.condition, Limits.zero_comp]
  · rw [kernel.condition, Limits.zero_comp]
  · rw [pullback.lift_snd]
  · rw [← cancel_mono (kernel.ι (pullback.snd f g))]
    rw [Category.assoc, kernel.lift_ι, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, kernel.lift_ι]
    · rw [Category.assoc, pullback.lift_snd, Limits.comp_zero,
        kernel.condition]
  · rw [← cancel_mono (kernel.ι f)]
    rw [Category.assoc, kernel.lift_ι, ← Category.assoc,
      kernel.lift_ι, pullback.lift_fst, Category.id_comp]

end Pullback

end RS
