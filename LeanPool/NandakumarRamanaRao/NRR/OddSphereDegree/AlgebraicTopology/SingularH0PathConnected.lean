/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularH0
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SubChainSubspaceBridge
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularHomologyFunctorAPI
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Tactic

/-! # Singular H0Path Connected -/

open CategoryTheory AlgebraicTopology Limits
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

noncomputable section
namespace SphereOddDegree

theorem prev_zero : (ComplexShape.down ℕ).prev 0 = 1 := by
  simp [ComplexShape.prev]

theorem aug_comp_boundary_eq_zero (Y : TopCat.{0}) :
    (singularChainComplex ℤ Y).d 1 0 ≫ aug Y = 0 := by
  ext c
  exact aug_boundary c

/-- The augmentation induced on zeroth singular homology. -/
def H0aug (Y : TopCat.{0}) : (singularChainComplex ℤ Y).homology 0 ⟶ ModuleCat.of ℤ ℤ :=
  (singularChainComplex ℤ Y).homologyι 0 ≫
    (singularChainComplex ℤ Y).descOpcycles (aug Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)

theorem aug_natural {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    singularChainMap ℤ f 0 ≫ aug Z = aug Y := by
  apply Limits.colimit.hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (aug Z).hom ((singularChainMap ℤ f 0).hom (chainGenerator ℤ Y 0 τ.as)) = (aug Y).hom (chainGenerator ℤ Y 0 τ.as)
  rw [singularChainMap_generator, aug_generator, aug_generator]

theorem opcyclesMap_descOpcycles {C : Type*} [Category C] [Abelian C] {K L : HomologicalComplex C (ComplexShape.down ℕ)} (φ : K ⟶ L)
    {A : C} (kL : L.X 0 ⟶ A) (kK : K.X 0 ⟶ A)
    (prev_zero : (ComplexShape.down ℕ).prev 0 = 1)
    (hkL : L.d 1 0 ≫ kL = 0) (hkK : K.d 1 0 ≫ kK = 0)
    (h_comm : φ.f 0 ≫ kL = kK) :
    HomologicalComplex.opcyclesMap φ 0 ≫ L.descOpcycles kL 1 prev_zero hkL =
      K.descOpcycles kK 1 prev_zero hkK := by
  have : Epi (K.pOpcycles 0) := inferInstance
  rw [← cancel_epi (K.pOpcycles 0)]
  rw [← Category.assoc, HomologicalComplex.p_opcyclesMap]
  rw [Category.assoc, HomologicalComplex.p_descOpcycles, h_comm, HomologicalComplex.p_descOpcycles]

theorem H0aug_natural {Y Z : TopCat.{0}} (f : Y ⟶ Z) :
    (singularHomologyℤ 0).map f ≫ H0aug Z = H0aug Y := by
  have h_comm : (singularChainℤ.map f).f 0 ≫ aug Z = aug Y := aug_natural f
  have key : HomologicalComplex.homologyMap (singularChainℤ.map f) 0 ≫ H0aug Z = H0aug Y := by
    unfold H0aug
    have h_nat := HomologicalComplex.homologyι_naturality (singularChainℤ.map f) 0
    rw [← Category.assoc, h_nat, Category.assoc]
    have h_desc := opcyclesMap_descOpcycles (singularChainℤ.map f) (aug Z) (aug Y) prev_zero (aug_comp_boundary_eq_zero Z) (aug_comp_boundary_eq_zero Y) h_comm
    rw [h_desc]
  exact key

instance isIso_homologyι_zero (Y : TopCat.{0}) :
    IsIso ((singularChainComplex ℤ Y).homologyι 0) :=
  HomologicalComplex.isIso_homologyι (singularChainComplex ℤ Y) 0 ((ComplexShape.down ℕ).next 0)
    rfl ((singularChainComplex ℤ Y).shape _ _ (by simp [ComplexShape.next]))

lemma descOpcycles_eval (Y : TopCat.{0}) (c : singularChainGroup ℤ Y 0) :
    (aug Y).hom c = (HomologicalComplex.descOpcycles (singularChainComplex ℤ Y) (aug Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)).hom ((HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0).hom c) := by
  have h_p : HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0 ≫ HomologicalComplex.descOpcycles (singularChainComplex ℤ Y) (aug Y) 1 prev_zero (aug_comp_boundary_eq_zero Y) = aug Y :=
    HomologicalComplex.p_descOpcycles _ _ _ _ _
  have key := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h_p) c
  erw [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  exact key.symm

theorem d_one_comp_pOpcycles (K : HomologicalComplex (ModuleCat ℤ) (ComplexShape.down ℕ)) :
    K.d 1 0 ≫ K.pOpcycles 0 = 0 :=
  Eq.ndrec (motive := fun j => K.d j 0 ≫ K.pOpcycles 0 = 0) (K.sc 0).f_pOpcycles prev_zero

theorem isIso_descOpcycles_aug (Y : TopCat.{0}) [Nonempty ↑Y] [PathConnectedSpace ↑Y] :
    IsIso ((singularChainComplex ℤ Y).descOpcycles (aug Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)) := by
  have h_bijective : Function.Bijective (HomologicalComplex.descOpcycles (singularChainComplex ℤ Y) (aug Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)).hom := by
    constructor
    · intro x y hxy
      have h_surj : Function.Surjective (HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0).hom :=
        (ModuleCat.epi_iff_surjective _).mp inferInstance
      obtain ⟨c, rfl⟩ := h_surj x
      obtain ⟨d, rfl⟩ := h_surj y
      have h_eq : (aug Y).hom c = (aug Y).hom d := by
        rw [descOpcycles_eval, descOpcycles_eval, hxy]
      have h_diff : c - d ∈ LinearMap.range (singularBoundary ℤ Y 0).hom := by
        have := sub_aug_smul_basept_mem_range (Classical.arbitrary ↑Y) (c - d)
        have h_aug_diff : (aug Y).hom (c - d) = 0 := by
          rw [map_sub, h_eq, sub_self]
        rw [h_aug_diff, zero_smul, sub_zero] at this
        exact this
      obtain ⟨e, he⟩ := h_diff
      have h_ker : (HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0).hom (c - d) = 0 := by
        rw [← he]
        have key := congrArg ModuleCat.Hom.hom (d_one_comp_pOpcycles (singularChainComplex ℤ Y))
        have h_eval := DFunLike.congr_fun key (e : (singularChainComplex ℤ Y).X 1)
        erw [ModuleCat.hom_comp, LinearMap.comp_apply] at h_eval
        exact h_eval
      have h_sub : (HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0).hom c - (HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0).hom d = 0 := by
        rw [← map_sub, h_ker]
      exact sub_eq_zero.mp h_sub
    · intro n
      obtain ⟨b⟩ : Nonempty ↑Y := inferInstance
      use (HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0).hom (n • chainGenerator ℤ Y 0 (pointSimplex Y b))
      rw [← descOpcycles_eval, map_zsmul, aug_generator]
      simp
  exact (ConcreteCategory.isIso_iff_bijective _).mpr h_bijective

instance isIso_H0aug (Y : TopCat.{0}) [Nonempty ↑Y] [PathConnectedSpace ↑Y] :
    IsIso (H0aug Y) := by
  have := isIso_descOpcycles_aug Y
  unfold H0aug
  infer_instance

theorem surjective_H0aug (Y : TopCat.{0}) [Nonempty ↑Y] :
    Function.Surjective (H0aug Y).hom := by
  intro n
  obtain ⟨b⟩ : Nonempty ↑Y := inferInstance
  have h_eval : (HomologicalComplex.descOpcycles (singularChainComplex ℤ Y) (aug Y) 1 prev_zero (aug_comp_boundary_eq_zero Y)).hom ((HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0).hom (n • chainGenerator ℤ Y 0 (pointSimplex Y b))) = n := by
    rw [← descOpcycles_eval, map_zsmul, aug_generator]
    simp
  have h_iso : IsIso ((singularChainComplex ℤ Y).homologyι 0) := isIso_homologyι_zero Y
  have h_surj : Function.Surjective ((singularChainComplex ℤ Y).homologyι 0).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp h_iso |>.2
  obtain ⟨x, hx⟩ := h_surj ((HomologicalComplex.pOpcycles (singularChainComplex ℤ Y) 0).hom (n • chainGenerator ℤ Y 0 (pointSimplex Y b)))
  use x
  unfold H0aug
  erw [ModuleCat.hom_comp, LinearMap.comp_apply, hx, h_eval]

/-- The zeroth-homology augmentation for chains supported in a subset. -/
def subH0aug (X : TopCat.{0}) (S : Set X) :
    (subChainComplex ℤ X S).homology 0 ⟶ ModuleCat.of ℤ ℤ :=
  (subspaceHomologyIso S 0).hom ≫ H0aug (TopCat.of S)

instance isIso_subH0aug (X : TopCat.{0}) (S : Set X) [Nonempty S] [PathConnectedSpace S] :
    IsIso (subH0aug X S) := by
  have : IsIso (H0aug (TopCat.of S)) := isIso_H0aug (TopCat.of S)
  unfold subH0aug
  infer_instance

/-- The continuous inclusion between nested subspaces, bundled in `TopCat`. -/
def setInclusionTopCat (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨Set.inclusion h, by fun_prop⟩

theorem setInclusionTopCat_comp_sInclusion (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    setInclusionTopCat X S T h ≫ sInclusion T = sInclusion S := by
  ext x
  rfl

theorem subChainCorestrict_inclusion_square (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    subChainCorestrict ℤ X S ≫ subChainInclusion S T h
      = singularChainℤ.map (setInclusionTopCat X S T h) ≫ subChainCorestrict ℤ X T := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change (singularChainMap ℤ (sInclusion S) n).hom c =
       (singularChainMap ℤ (sInclusion T) n).hom ((singularChainMap ℤ (setInclusionTopCat X S T h) n).hom c)
  have h_comp := singularChainMap_comp ℤ (setInclusionTopCat X S T h) (sInclusion T) n
  have key := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h_comp) c
  erw [ModuleCat.hom_comp, LinearMap.comp_apply] at key
  rw [setInclusionTopCat_comp_sInclusion] at key
  exact key

theorem subH0aug_natural_inclusion (X : TopCat.{0}) (S T : Set X) (h : S ⊆ T) :
    HomologicalComplex.homologyMap (subChainInclusion S T h) 0 ≫ subH0aug X T
      = subH0aug X S := by
  have h_sq := subChainCorestrict_inclusion_square X S T h
  unfold subH0aug
  rw [← cancel_epi (subspaceHomologyIso S 0).inv]
  rw [← Category.assoc (subspaceHomologyIso S 0).inv]
  have h_inv_S : (subspaceHomologyIso S 0).inv = HomologicalComplex.homologyMap (subChainCorestrict ℤ X S) 0 := rfl
  have h_inv_T : (subspaceHomologyIso T 0).inv = HomologicalComplex.homologyMap (subChainCorestrict ℤ X T) 0 := rfl
  rw [h_inv_S, ← HomologicalComplex.homologyMap_comp, h_sq]
  rw [HomologicalComplex.homologyMap_comp, Category.assoc, ← h_inv_T, Iso.inv_hom_id_assoc]
  rw [← h_inv_S, Iso.inv_hom_id_assoc]
  exact H0aug_natural (setInclusionTopCat X S T h)

end SphereOddDegree
