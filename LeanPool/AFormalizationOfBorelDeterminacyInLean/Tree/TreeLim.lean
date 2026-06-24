/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import Mathlib.CategoryTheory.Adjunction.Limits
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.RestrictTree
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.InvLimitNat

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.TreeLim

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace Descriptive.Tree
open CategoryTheory

noncomputable section «Section1»
variable {A B : Type*} {m k n : ℕ}
/-- Object function of adjoint of `res k` -/
def constTreeObj (k : ℕ) (A : Type*) : tree A where
  val := {x | ∃ m ≤ k, x ∈ Set.range (List.replicate m)}
  property := by
    rintro x a ⟨m, hm, ⟨b, h⟩⟩; rcases m with _ | m
    · simp at h
    · rw [List.replicate_succ'] at h
      exact ⟨m, ⟨by omega, ⟨b, List.append_inj_left' h rfl⟩⟩⟩
@[simp] lemma mem_constTree (a : A) (h : m ≤ k) :
  List.replicate m a ∈ constTreeObj k A := by
  use m; simp [h]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def headD (x : constTreeObj k A) : A := x.prop.choose_spec.2.choose
@[simp] lemma eq_replicate_headD (x : constTreeObj k A) :
  List.replicate x.val.length (headD x) = x := by
  nth_rw 2 [← x.prop.choose_spec.2.choose_spec]
  nth_rw 1 [← x.prop.choose_spec.2.choose_spec]
  symm; apply List.eq_replicate_of_mem; intro _; apply List.eq_of_mem_replicate
lemma headD_nonempty (x : constTreeObj k A) (h : x.val ≠ []) : headD x = x.val.head h := by
  rw [← eq_replicate_headD] at h; rw [← List.head_replicate h]; simp
@[simp] lemma constTree_length (x : constTreeObj k A) : x.val.length ≤ k := by
  obtain ⟨_, ⟨_, h, ⟨_, rfl⟩⟩⟩ := x; simp [h]
@[simp] lemma constTree_zero (x : constTreeObj 0 A) : x.val = [] := by
  apply List.eq_nil_of_length_eq_zero; linarith [constTree_length x]
/-- Adjoint of `res k` -/
def constTree (k : ℕ) : Type* ⥤ Trees where
  obj A := ⟨A, constTreeObj k A⟩
  map f := {
    toFun := fun ⟨x, h⟩ ↦ ⟨List.map (ConcreteCategory.hom f) x, by
      obtain ⟨n, hn, ⟨a, rfl⟩⟩ := h
      exact ⟨n, hn, ConcreteCategory.hom f a, by rw [List.map_replicate]⟩⟩
    monotone' := fun _ _ h ↦ List.IsPrefix.map _ h
    h_length := by simp
  }
  map_id X := by
    apply LenHom.ext
    funext x
    apply tree_ext
    change List.map (fun a : X ↦ a) x.val = x.val
    exact List.map_id x.val
  map_comp f g := by
    apply LenHom.ext
    funext x
    apply tree_ext
    change List.map (ConcreteCategory.hom g ∘ ConcreteCategory.hom f) x.val =
      List.map (ConcreteCategory.hom g) (List.map (ConcreteCategory.hom f) x.val)
    exact (List.map_map (f := ConcreteCategory.hom f) (g := ConcreteCategory.hom g)
      (l := x.val)).symm
@[simp] lemma head_constTree_map {B} (k : ℕ) (f : A ⟶ B)
  {x : constTreeObj k A} (h : x.val ≠ []) :
  List.head (((constTree k).map f) x).val (LenHom.map_ne_nil _ h)
  = ConcreteCategory.hom f (List.head x.val h) := by
  change (List.map (ConcreteCategory.hom f) x.val).head _ =
    ConcreteCategory.hom f (List.head x.val h)
  simp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def resEqUnit k : 𝟭 _ ⟶ constTree k ⋙ resEq k where
  app _ := TypeCat.ofHom fun a ↦ ⟨List.replicate k a, by
    constructor
    · exact mem_constTree a le_rfl
    · simp⟩
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact resEq_ext _ _ List.map_replicate.symm
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def resEqCounitComp k T : (constTree k).obj ((resEq k).obj T) ⟶ T where
  toFun := fun x ↦ take x.val.length ⟨(headD x).val, by simp⟩
  monotone' := by
    intro x y h; by_cases hx : x.val = []
    · change List.take x.val.length (headD x).val <+: List.take y.val.length (headD y).val
      rw [hx]
      exact List.nil_prefix
    · have h' : headD x = headD y := by simpa only [← headD_nonempty] using h.head hx
      change List.take x.val.length (headD x).val <+: List.take y.val.length (headD y).val
      rw [h']
      exact List.take_isPrefix_take.mpr (Or.inl (List.IsPrefix.length_le h))
  h_length _ := by simp only [take_coe, List.length_take, resEq_len, constTree_length, min_eq_left]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def resEqCounit k : resEq k ⋙ constTree k ⟶ 𝟭 _ where
  app := resEqCounitComp k
  naturality := by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro x
    apply tree_ext
    change
      (take (((constTree k).map ((resEq k).map f)) x).val.length
        ⟨(headD (((constTree k).map ((resEq k).map f)) x)).val,
          (headD (((constTree k).map ((resEq k).map f)) x)).prop.1⟩).val =
      (f (take x.val.length ⟨(headD x).val, (headD x).prop.1⟩)).val
    rw [LenHom.h_length_simp, take_apply f x.val.length]
    by_cases hxl : x.val = []
    · rw [hxl]
      rfl
    · rw [headD_nonempty]
      · simp_rw [headD_nonempty _ hxl]
        rw [head_constTree_map]
        rfl
      · exact LenHom.map_ne_nil _ hxl
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def resEqAdj (k : ℕ) : constTree k ⊣ resEq k := Adjunction.mkOfUnitCounit {
  unit := resEqUnit k
  counit := resEqCounit k
  left_triangle := by
    apply NatTrans.ext
    funext A
    apply ConcreteCategory.hom_ext
    intro x
    apply tree_ext
    change
      (take (((constTree k).map ((resEqUnit k).app A)) x).val.length
        ⟨(headD (((constTree k).map ((resEqUnit k).app A)) x)).val,
          (headD (((constTree k).map ((resEqUnit k).app A)) x)).prop.1⟩).val =
      x.val
    rw [take_coe]
    by_cases hxl : x.val = []
    · rw [LenHom.h_length_simp, hxl]
      rfl
    · have hmapne :
          (((constTree k).map ((resEqUnit k).app A)) x).val ≠ [] :=
        LenHom.map_ne_nil _ hxl
      have hhead :
          (headD (((constTree k).map ((resEqUnit k).app A)) x)).val =
            List.replicate k (headD x) := by
        calc
          (headD (((constTree k).map ((resEqUnit k).app A)) x)).val =
              (List.head (((constTree k).map ((resEqUnit k).app A)) x).val hmapne).val :=
            congrArg Subtype.val (headD_nonempty _ hmapne)
          _ = (ConcreteCategory.hom ((resEqUnit k).app A) (List.head x.val hxl)).val :=
            congrArg Subtype.val (head_constTree_map k ((resEqUnit k).app A) hxl)
          _ = List.replicate k (List.head x.val hxl) := rfl
          _ = List.replicate k (headD x) := by
            rw [← headD_nonempty x hxl]
      rw [LenHom.h_length_simp, hhead]
      calc
        List.take x.val.length (List.replicate k (headD x)) =
            List.replicate (min x.val.length k) (headD x) := List.take_replicate
        _ = List.replicate x.val.length (headD x) := by
          rw [min_eq_left (constTree_length x)]
        _ = x.val := eq_replicate_headD x
  right_triangle := by
    apply NatTrans.ext
    funext T
    apply ConcreteCategory.hom_ext
    intro x
    apply resEq_ext
    change
      (take (resEq.val' ((resEqUnit k).app ((resEq k).obj T) x)).val.length
        ⟨(headD (resEq.val' ((resEqUnit k).app ((resEq k).obj T) x))).val,
          (headD (resEq.val' ((resEqUnit k).app ((resEq k).obj T) x))).prop.1⟩).val =
      x.val
    rw [take_coe]
    have hxl : x.val.length = k := x.prop.2
    rcases k with _ | k
    · change List.take (List.replicate 0 x).length (headD (resEq.val'
        ((resEqUnit 0).app ((resEq 0).obj T) x))).val = x.val
      rw [List.replicate_zero, List.length_nil, List.take_zero]
      exact (List.eq_nil_of_length_eq_zero hxl).symm
    · let u := resEq.val' ((resEqUnit (k + 1)).app ((resEq (k + 1)).obj T) x)
      have hu : u.val ≠ [] := by
        change (List.replicate (k + 1) x) ≠ []
        exact List.replicate_succ_ne_nil
      have hhead : (headD u).val = x.val := by
        rw [headD_nonempty u hu]
        change ((List.replicate (k + 1) x).head _).val = x.val
        exact congrArg Subtype.val (List.head_replicate _)
      have hlen : u.val.length = k + 1 := by
        change (List.replicate (k + 1) x).length = k + 1
        exact List.length_replicate
      rw [show resEq.val' ((resEqUnit (k + 1)).app ((resEq (k + 1)).obj T) x) = u from rfl]
      rw [hlen, hhead]
      exact List.take_of_length_le (by omega)
}
instance (k : ℕ) : Functor.IsRightAdjoint (Tree.resEq k) :=
  ⟨Tree.constTree k, ⟨Tree.resEqAdj k⟩⟩
instance (k : ℕ) : Limits.PreservesLimitsOfSize (Tree.resEq k) :=
  (Tree.resEqAdj k).rightAdjoint_preservesLimits

section «TreeLimits»
variable {J : Type} [Category J] (F : J ⥤ Trees)
/-- Object function of limit functor in `Trees` -/
def limObj : tree (∀ j, (F.obj j).1) where
  val := { x | ∃ (h : ∀ j, x.mapEval j ∈ (F.obj j).2),
    ∀ ⦃i j⦄ (f : i ⟶ j), (F.map f ⟨_, h i⟩).val = x.mapEval j }
  property := by
    intro x a ⟨h1, h2⟩; use fun j ↦ mem_of_append (y := [a j]) (by
      simpa only [List.map_append, List.map_cons, List.map_nil] using h1 j)
    intro _ _ f; specialize h2 f; apply_fun List.take x.length at h2
    simp_rw [List.map_append, List.map_cons, List.map_nil, ← take_apply_val] at h2
    convert h2 <;> first
      | rfl
      | simp only [List.length_map, le_refl, List.take_append_of_le_length,
          ← List.map_take, List.take_length, take_coe]
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def limCone : Limits.Cone F where
  pt := ⟨_, limObj F⟩
  π := {
    app := fun j ↦ {
      toFun := fun x ↦ ⟨x.val.mapEval j, x.prop.1 j⟩
      monotone' := fun _ _ h ↦ h.map _
      h_length := by
        intro x
        exact List.length_map (f := fun y ↦ y j) (as := x.val)
    }
    naturality := fun _ _ f ↦ ConcreteCategory.hom_ext _ _ fun x ↦ tree_ext (x.prop.2 f).symm
  }
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def coneZip (s : Limits.Cone F) (x : s.pt) : List (∀ j, (F.obj j).1) :=
  List.zipFun (n := x.val.length) (fun j ↦ ((s.π.app j) x).val)
    (fun _ ↦ LenHom.h_length_simp _ x)
@[simp] lemma coneZip_mapEval (s : Limits.Cone F) (x : s.pt) (j : J) :
  (coneZip F s x).mapEval j = ((s.π.app j) x).val :=
  List.mapEval_zip (fun j ↦ ((s.π.app j) x).val) (fun _ ↦ LenHom.h_length_simp _ x)
@[simp, simp_lengths] lemma coneZip_length (s : Limits.Cone F) (x : s.pt) :
  (coneZip F s x).length = x.val.length :=
  List.zipFun_len (fun j ↦ ((s.π.app j) x).val) (fun _ ↦ LenHom.h_length_simp _ x)
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def isLimitLift (s : Limits.Cone F) : s.pt ⟶ (limCone F).pt where
  toFun x := ⟨coneZip F s x, by
    refine ⟨fun j ↦ ?_, ?_⟩
    · rw [coneZip_mapEval]
      exact ((s.π.app j) x).prop
    · intro i j f
      have hi :
          (⟨(coneZip F s x).mapEval i, by
            rw [coneZip_mapEval]
            exact ((s.π.app i) x).prop⟩ : (F.obj i).2) = (s.π.app i) x := by
        apply tree_ext
        exact coneZip_mapEval F s x i
      rw [hi, coneZip_mapEval]
      rw [← s.w f]
      rfl⟩
  monotone' x y h :=
    List.zipFun_mono _ _ _ _ h.length_le (fun j ↦ (s.π.app j).monotone' h)
  h_length x := coneZip_length F s x

/-- Auxiliary declaration for the Borel determinacy formalization. -/
def isLimit : Limits.IsLimit (limCone F) where
  lift := isLimitLift F
  fac := by
    intro s j
    apply LenHom.ext
    funext x
    apply tree_ext
    exact coneZip_mapEval F s x j
  uniq := by
    intro s f h
    apply LenHom.ext
    funext x
    apply tree_ext
    apply List.mapEval_joint_epi
    · exact (LenHom.h_length_simp f x).trans (LenHom.h_length_simp (isLimitLift F s) x).symm
    · intro j
      have hπ := congrArg (fun g : s.pt ⟶ F.obj j ↦ (g x).val) (h j)
      rw [show List.mapEval j ((isLimitLift F s).toFun x).val = ((s.π.app j) x).val from
        coneZip_mapEval F s x j]
      convert hπ using 1
      · simp only [ConcreteCategory.comp_apply]; rfl
      · rfl
end «TreeLimits»

lemma proj_fixing (F : ℕᵒᵖ ⥤ Trees) (k : ℕ)
  (hF : ∀ n, Tree.Fixing (k + n) (F.map (homOfLE (Nat.le_succ n)).op)) n :
  Fixing (k + n) ((limCone F).π.app (Opposite.op n)) :=
  (fixing_iff_fixingEq (k + n) _).mpr (fun m hm ↦
    ⟨nat_add_initial (Limits.isLimitOfPreserves (resEq m) (isLimit F)) n (fun p hp ↦
      ((fixing_iff_fixingEq (k + n) _).mp (by synthFixing) m hm).prop) n le_rfl⟩)

end «Section1»
end Descriptive.Tree
