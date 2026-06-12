/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.TreeBody
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.LenTreeHom

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.BodyFunctor

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace Descriptive.Tree
open CategoryTheory
open Stream'.Discrete

variable {A A' : Type*} {n : ℕ}

noncomputable section «Section1»
variable {S : tree A} {T : tree A'}
/-- The set of points in `body S` where the body map of f is defined -/
def bodyDom (f : OrderHom S T) : Set (Stream' A) := { a | a ∈ body S ∧
  Set.Unbounded Nat.le ((fun (x : S) ↦ (f x).val.length) '' { x | a ∈ principalOpen x }) }
lemma bodyMap_uniq (f : OrderHom S T) {a : Stream' A} {x y : List A}
  {ha : a ∈ body S} (hx : a ∈ principalOpen x) (hy : a ∈ principalOpen y)
  (hlx : n < (f ⟨x, ha x hx⟩).val.length) (hly : n < (f ⟨y, ha y hy⟩).val.length) :
  (f ⟨x, ha x hx⟩).val[n] = (f ⟨y, ha y hy⟩).val[n] := by
  wlog h : x.length ≤ y.length
  · exact (this f hy hx hly hlx <| Nat.le_of_lt (by simpa using h)).symm
  · have hpr : (f ⟨x, ha x hx⟩).val <+: f ⟨y, ha y hy⟩ := by
      apply f.monotone'; change x <+: y
      rw [principalOpen_iff_restrict] at *
      rw [hx, hy]; simp [h]
    simp_rw (config := {singlePass := true}) [List.prefix_iff_eq_take.mp hpr]
    apply List.getElem_take
lemma bodyMap_exists (f : OrderHom S T) (a : bodyDom f) (n : ℕ) :
  ∃ (x : S), (a : Stream' A) ∈ principalOpen x ∧ n < (f x).val.length := by
  obtain ⟨b, ⟨⟨x, hx, rfl⟩, h''⟩⟩ := a.prop.2 n; use x, hx; simpa using h''
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def bodyMapChooseSpec (f : OrderHom S T) (a : bodyDom f) (n : ℕ) : T :=
  let t := bodyMap_exists f a n; f ⟨t.choose, a.prop.1 t.choose t.choose_spec.1⟩
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def bodyMapVal (f : OrderHom S T) (a : bodyDom f) : Stream' A' :=
  fun n ↦ let t := bodyMap_exists f a n; (f t.choose).val[n]
lemma bodyMap_pspec (f : OrderHom S T) (a : bodyDom f) {x}
  (hx : (a : Stream' A) ∈ principalOpen x) (hlx : n < (f ⟨x, a.prop.1 x hx⟩).val.length) :
  (bodyMapVal f a).get n = (f ⟨x, a.prop.1 x hx⟩).val[n] := by
  simp_rw [Stream'.get, bodyMapVal]
  rw [bodyMap_uniq _ _ (bodyMap_exists f a n).choose_spec.1]
  rfl

/-- The induced map on branches -/
def bodyMap (f : OrderHom S T) (a : bodyDom f) : body T :=
  ⟨bodyMapVal f a, by
    intro y hy; apply mem_of_prefix (y := bodyMapChooseSpec f a y.length) _ (SetLike.coe_mem _)
    rw [principalOpen_iff_restrict] at hy; nth_rw 1 [hy]; apply List.prefix_iff_eq_take.mpr
    have ⟨hx, hl⟩ := (bodyMap_exists f a y.length).choose_spec
    apply List.ext_getElem
    · simp [bodyMapChooseSpec, hl.le]
    · intro n hn _; simp only [Stream'.take_get, Stream'.length_take, List.getElem_take]
      rw [(bodyMap_pspec f a hx (lt_trans (by simpa using hn) hl))]; rfl⟩
lemma bodyMap_spec (f : OrderHom S T) (a : bodyDom f) {x}
  (hx : (a : Stream' A) ∈ principalOpen x) (hlx : n < (f ⟨x, a.prop.1 x hx⟩).val.length) :
  (bodyMap f a).val.get n = (f ⟨x, a.prop.1 x hx⟩).val[n] := bodyMap_pspec f a hx hlx
lemma bodyMap_continuous (f : OrderHom S T) : Continuous (bodyMap f) := by
  apply continuous_iff_continuousAt.mpr; intro a
  have h := hasBasis_principalOpen (bodyMap f a : Stream' A')
  have hc := h.comap (fun (x : body T) ↦ x.val)
  rw [← nhds_subtype] at hc; apply hc.tendsto_right_iff.mpr; intro y hy
  have ⟨x, hxa, hxl⟩ := bodyMap_exists f a y.length
  apply Filter.eventually_of_mem (U :=_root_.Subtype.val⁻¹' (principalOpen x))
  · rw [mem_nhds_iff]; use _root_.Subtype.val⁻¹' (principalOpen x)
    constructor
    · exact subset_rfl
    · constructor
      · apply continuous_subtype_val.isOpen_preimage
        apply principalOpen_isOpen
      · exact hxa
  · intro b hb
    simp_rw [Set.mem_preimage, principalOpen_index]; intro n hn
    rw [← ((principalOpen_index _ y).mp hy) n hn,
      bodyMap_spec f b hb (lt_trans hn hxl), bodyMap_spec f a hxa (lt_trans hn hxl)]

variable {S T : Trees}
--also make functor to TopCat?
/-- if f is length-preserving, then its body map is defined everywhere -/
@[simp] lemma bodyDom_univ (f : S ⟶ T) : bodyDom f.toOrderHom = body S.2 := by
  simp only [bodyDom, Set.sep_eq_self_iff_mem_true]
  intro x hx n
  refine ⟨n + 1, ?_, Nat.not_succ_le_self n⟩
  refine ⟨⟨x.take (n + 1), hx _ (extend_sub _ _)⟩, extend_sub _ _, ?_⟩
  simp
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps obj] def bodyPre : Prefunctor Trees (Type*) where
  obj S := body S.2
  map f := TypeCat.ofHom fun a ↦ bodyMap f.toOrderHom ⟨a, by simp⟩
@[ext] lemma bodyPre_obj_ext {x y : bodyPre.obj S} (h : x.val = y.val) : x = y := by
  exact Subtype.ext h
lemma LenHom.bodyMap_spec (f : S ⟶ T) (a : body S.2)
  x (hx : (a : Stream' S.1) ∈ principalOpen x) n (hlx : n < x.length) :
  (bodyPre.map f a).val.get n = (f ⟨x, a.prop x hx⟩).val[n]'(by simpa) := by
  apply Tree.bodyMap_spec f.toOrderHom _ hx
lemma LenHom.bodyMap_spec_res_lt (f : S ⟶ T) (a : body S.2) {m n} (h : m < n) :
  (bodyPre.map f a).val.get m = (f (body.take n a)).val[m]'(by simpa)  :=
  Descriptive.Tree.LenHom.bodyMap_spec f a (a.val.take n) (by simp) m (by simp [h])
lemma LenHom.bodyMap_spec_res (f : S ⟶ T) (a : body S.2) n :
  (bodyPre.map f a).val.get n = (f (body.take (n + 1) a)).val[n]  :=
  Descriptive.Tree.LenHom.bodyMap_spec_res_lt f a (Nat.lt_succ_self n)
lemma LenHom.bodyPre_map_restrict (f : S ⟶ T) (a : body S.2) n :
  (bodyPre.map f a).val.take n = (f (body.take n a)).val := by
  apply List.ext_getElem
  · simp [bodyPre]
  · intro m hm _
    simpa [bodyPre] using LenHom.bodyMap_spec_res_lt f a hm
/-- the body of a tree is functorial -/
@[simps! obj] def bodyFunctor : Trees ⥤ Type* where
  obj S := body S.2
  map f := bodyPre.map f
  map_id _ := by
    ext a n
    change (bodyPre.map (𝟙 _) a).val.get n = a.val.get n
    rw [LenHom.bodyMap_spec_res]
    simp
  map_comp f g := by
    ext x n
    change (bodyPre.map (f ≫ g) x).val.get n =
      (bodyPre.map g (bodyPre.map f x)).val.get n
    rw [LenHom.bodyMap_spec_res, LenHom.bodyMap_spec_res]
    have htake : body.take (n + 1) (bodyPre.map f x) = f (body.take (n + 1) x) := by
      apply tree_ext
      exact LenHom.bodyPre_map_restrict f x (n + 1)
    have htree : g (f (body.take (n + 1) x)) = g (body.take (n + 1) (bodyPre.map f x)) :=
      (congrArg (fun y ↦ g y) htake).symm
    simp [CategoryTheory.comp_apply]
    have hval := congrArg Subtype.val htree
    simp [hval]
instance bodySpace : TopologicalSpace (Tree.bodyFunctor.obj S) :=
  inferInstanceAs (TopologicalSpace (body S.2))
lemma bodyMap_spec' (f : S ⟶ T) (a : body S.2)
  x (hx : (a : Stream' S.1) ∈ principalOpen x) n (hlx : n < x.length) :
  (bodyFunctor.map f a).val.get n = (f ⟨x, a.prop x hx⟩).val[n]'(by simpa) :=
  LenHom.bodyMap_spec f a x hx n hlx
lemma bodyMap_spec_res_lt' (f : S ⟶ T) (a : body S.2) {m n} (h : m < n) :
  (bodyFunctor.map f a).val.get m = (f (body.take n a)).val[m]'(by simpa)  :=
  LenHom.bodyMap_spec_res_lt f a h
lemma bodyMap_spec_res' (f : S ⟶ T) (a : body S.2) n :
  (bodyFunctor.map f a).val.get n = (f ⟨a.val.take (n + 1), a.prop _ (by simp)⟩).val[n]  :=
  LenHom.bodyMap_spec_res f a n
lemma bodyMap_restrict {S T : Trees} (f : S ⟶ T) a n :
  (bodyFunctor.map f a).val.take n = (f (body.take n a)).val :=
  LenHom.bodyPre_map_restrict f a n
lemma LenHom.bodyMap_continuous {S T : Trees} (f : S ⟶ T) :
  Continuous (bodyFunctor.map f) := by
  change Continuous (fun a : body S.2 => bodyMap f.toOrderHom ⟨a.val, by simp [bodyDom_univ]⟩)
  convert Tree.bodyMap_continuous f.toOrderHom <;> simp [bodyDom_univ]

end «Section1»
end Descriptive.Tree
