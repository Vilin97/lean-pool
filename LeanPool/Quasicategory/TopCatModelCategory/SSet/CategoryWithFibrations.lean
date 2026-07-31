/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Boundary
import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

open CategoryTheory HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

namespace modelCategoryQuillen

/-def I : MorphismProperty SSet.{u} :=
  .ofHoms (fun (n : ℕ) ↦ (subcomplexBoundary.{u} n).ι)

def J : MorphismProperty SSet.{u} :=
  ⨆ n, .ofHoms (fun i ↦ (subcomplexHorn.{u} (n + 1) i).ι)-/

/-lemma horn_ι_mem_J {n : ℕ} (i : Fin (n + 2)) :
    J (subcomplexHorn.{u} (n + 1) i).ι := by
  simp [J]
  exact ⟨n, ⟨_⟩⟩

lemma I_le_monomorphisms : I.{u} ≤ monomorphisms _ := by
  rintro _ _ _ ⟨n⟩
  simp only [monomorphisms.iff]
  infer_instance

lemma J_le_monomorphisms : J.{u} ≤ monomorphisms _ := by
  rintro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  simp only [monomorphisms.iff]
  infer_instance

instance : CategoryWithCofibrations SSet.{u} where
  cofibrations := .monomorphisms _

instance : CategoryWithFibrations SSet.{u} where
  fibrations := J.rlp

lemma cofibrations_eq : cofibrations SSet.{u} = monomorphisms _ := rfl

lemma fibrations_eq : fibrations SSet.{u} = J.rlp := rfl-/

instance : IsStableUnderBaseChange (fibrations SSet.{u}) := by
  rw [fibrations_eq]
  infer_instance

instance : IsMultiplicative (fibrations SSet.{u}) := by
  rw [fibrations_eq]
  infer_instance

instance : IsStableUnderRetracts (fibrations SSet.{u}) := by
  rw [fibrations_eq]
  infer_instance

instance (X : SSet.{u}) : Fibration (𝟙 X) := by
  rw [fibration_iff]
  exact (fibrations SSet.{u}).id_mem X

section

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-lemma cofibration_iff : Cofibration f ↔ Mono f := by
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

lemma fibration_iff : Fibration f ↔ J.rlp f := by
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

instance (n : ℕ) (i : Fin (n + 2)) [hf : Fibration f] :
    HasLiftingProperty (C := SSet.{u}) (horn (n + 1) i).ι f := by
  rw [fibration_iff] at hf
  exact hf _ (subcomplexHorn_ι_mem_J i)-/

--instance [Mono f] : Cofibration f := by rwa [cofibration_iff]

end

end modelCategoryQuillen

end SSet
