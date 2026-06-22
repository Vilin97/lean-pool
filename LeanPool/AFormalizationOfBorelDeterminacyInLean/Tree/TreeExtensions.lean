/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/

import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.TreeLim
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.PointedTrees

/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.TreeExtensions

Auxiliary declarations for the Borel determinacy formalization.
-/


namespace Descriptive.Tree
open CategoryTheory Descriptive

noncomputable section «Section1»
variable {k m n : ℕ}
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev mkPointedMor' {S T : Trees} (f : S ⟶ T) (y : T)
  -- TODO: `as_aux_lemma` fails on zero goals.
  (h : Fixing y.val.length f := by all_goals as_aux_lemma => synthFixing) :
  mkPointed (Tree.pInv f y) ⟶ mkPointed y := ⟨f, cancel_pInv_right f y h⟩

/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev pointedResObj (k : ℕ) (T : PointedTrees) : PointedTrees where
  fst := (Tree.res k).obj T.1
  snd := ⟨T.2.val.take k, Tree.take_mem T.2, List.length_take_le k T.2.val⟩
/-- restriction of a pointed tree, obtained by replacing
  the base node by an ancestor if necessary -/
def pointedRes (k : ℕ) : PointedTrees ⥤ PointedTrees where
  obj := pointedResObj k
  map {S T} f := ⟨(forgetPoint ⋙ res k).map f, by
    ext1; change (f.toHom (Tree.take k S.2)).val = _
    change (f.toHom (Tree.take k S.2)).val = (Tree.take k T.2).val
    rw [take_apply_val f.toHom k S.snd]
    exact congrArg (fun x ↦ x.val.take k) f.hp⟩
  map_id _ := rfl
  map_comp _ _ := PointedLenHom.ext rfl
lemma pointedRes_isIso_iff_fixing k {S T : PointedTrees} (f : S ⟶ T) :
  IsIso ((pointedRes k).map f) ↔ Fixing k f.toHom := by
    simp only [pointed_isIso_iff]; use Fixing.mk, fun h ↦ h.prop
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extensionsRes T :
  extensions.obj T ≃ extensions.obj ((pointedRes (T.2.val.length + 1)).obj T) where
  toFun a := ⟨a.val, by
    constructor
    · change T.2.val.take (T.2.val.length + 1) ++ [a.val] ∈ T.1.2
      rw [List.take_of_length_le (Nat.le_succ T.2.val.length)]
      exact a.prop
    · change (T.2.val.take (T.2.val.length + 1) ++ [a.val]).length ≤ T.2.val.length + 1
      rw [List.take_of_length_le (Nat.le_succ T.2.val.length)]
      simp only [List.length_append, List.length_singleton, le_refl]⟩
  invFun a := ⟨a.val, by
    have hbase : ((pointedRes (T.2.val.length + 1)).obj T).2.val = T.2.val := by
      change T.2.val.take (T.2.val.length + 1) = T.2.val
      exact List.take_of_length_le (Nat.le_succ T.2.val.length)
    exact (by
      dsimp only [Set.mem_setOf_eq]
      have hlist := congrArg (fun x ↦ x ++ [a.val]) hbase
      exact hlist ▸ a.prop.1)⟩
  left_inv _ := rfl
  right_inv _ := rfl
@[simp] lemma extensionsRes_val' {T : Trees} {x : T} (a : ExtensionsAt x) :
  extensions.val' (extensionsRes (mkPointed x) a) = a.val' := by
  change x.val.take (x.val.length + 1) ++ [a.val] = x.val ++ [a.val]
  rw [List.take_of_length_le (Nat.le_succ x.val.length)]
@[simp] lemma extensionsRes_res_valT' {T : Trees} {x : T} (a : ExtensionsAt x) :
  res.val' (extensions.valT' (extensionsRes (mkPointed x) a)) = a.valT' :=
  tree_ext (extensionsRes_val' a)
@[simp] lemma extensionsRes_symm_val' {T : Trees} {x : T} a :
  ExtensionsAt.val' (A := no_index _) ((extensionsRes (mkPointed x)).symm a)
  = extensions.val' a := by
  have hbase : ((pointedRes (x.val.length + 1)).obj (mkPointed x)).2.val = x.val := by
    change x.val.take (x.val.length + 1) = x.val
    exact List.take_of_length_le (Nat.le_succ x.val.length)
  exact congrArg (fun u ↦ u ++ [a.val]) hbase.symm
@[simp] lemma cast_val' {S : PointedTrees} (h : k = m)
  (a : extensions.obj ((pointedRes k).obj S)) :
  extensions.val' (cast (by rw [h]) a : extensions.obj ((pointedRes m).obj S))
  = extensions.val' a := by subst h; rfl

variable {S T : Trees} (f : S ⟶ T) (x : S) (y : T)
/-- if f is (|x|+1)-fixing, then it induces a bijection on extensions of x -/
def pointedResIso (hx : Fixing (x.val.length + 1) f := by as_aux_lemma => synthFixing) :
  (pointedRes (x.val.length + 1)).obj (mkPointed x)
  ≅ (pointedRes (x.val.length + 1)).obj (mkPointed (f x)) :=
  have _: IsIso ((pointedRes (x.val.length + 1)).map (mkPointedMor f x)) :=
    (pointedRes_isIso_iff_fixing _ _).mpr hx
  asIso ((pointedRes (x.val.length + 1)).map (mkPointedMor f x))
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extensionsEquiv (hx : Fixing (x.val.length + 1) f := by as_aux_lemma => synthFixing) :
  ExtensionsAt x ≃ ExtensionsAt (f x) := by
  have hlen : x.val.length + 1 = (f x).val.length + 1 := by simp
  exact (extensionsRes (mkPointed x)).trans (
    (Iso.toEquiv (extensions.mapIso (pointedResIso f x))).trans (
    (Equiv.cast (by rw [hlen])).trans (
    extensionsRes (mkPointed (f x))).symm))
@[simp] lemma extensionsEquiv_val' (a : ExtensionsAt x) hx :
  (extensionsEquiv f x hx a).valT' = f a.valT' := by
  have hlen : x.val.length + 1 = (f x).val.length + 1 := by simp
  ext1
  change ExtensionsAt.val' ((extensionsRes (mkPointed (f x))).symm
      (cast (by rw [hlen])
        (extensions.map (pointedResIso f x hx).hom (extensionsRes (mkPointed x) a)))) =
    (f a.valT').val
  rw [extensionsRes_symm_val', cast_val' hlen, extensions_map_val']
  change (f (res.val' (extensions.valT' (extensionsRes (mkPointed x) a)))).val =
    (f a.valT').val
  rw [extensionsRes_res_valT']
@[simp] lemma extensionsEquiv_symm_val'
  (hx : Fixing (x.val.length + 1) f) (a : ExtensionsAt (f x)) :
  ((extensionsEquiv f x hx).symm a).valT' = pInv f a.valT' := by
  obtain ⟨a, rfl⟩ := (extensionsEquiv f x).surjective a
  simp only [Equiv.symm_apply_apply, extensionsEquiv_val', cancel_pInv_left]
@[simp] lemma ExtensionsAt.cast_valT' {A : Type*} {T : tree A} {x y : T}
  (h : x = y) (a : ExtensionsAt x) :
  (cast (congrArg ExtensionsAt h) a).valT' = a.valT' := by
  cases h
  rfl
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def pointedResIso' (hy : Fixing (y.val.length + 1) f := by as_aux_lemma => synthFixing) :
  (pointedRes (y.val.length + 1)).obj (mkPointed y)
  ≅ (pointedRes (y.val.length + 1)).obj (mkPointed (pInv f y)) :=
  have _: IsIso ((pointedRes (y.val.length + 1)).map (mkPointedMor' f y)) :=
    (pointedRes_isIso_iff_fixing _ _).mpr hy
  (asIso ((pointedRes (y.val.length + 1)).map (mkPointedMor' f y))).symm
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extensionsEquiv' (hy : Fixing (y.val.length + 1) f := by as_aux_lemma => synthFixing) :
  ExtensionsAt y ≃ ExtensionsAt (pInv f y) := by
  have hy' : Fixing ((pInv f y).val.length + 1) f := by simpa [h_length_pInv] using hy
  have hnode : f (pInv f y) = y := cancel_pInv_right f y (hy.mon (by simp))
  exact ((extensionsEquiv f (pInv f y) hy').trans
    (Equiv.cast (congrArg ExtensionsAt hnode))).symm
@[simp] lemma extensionsEquiv'_symm_val'
  (hy : Fixing (y.val.length + 1) f) (a : ExtensionsAt (pInv f y)) :
  ((extensionsEquiv' f y hy).symm a).valT' = f a.valT' := by
  have hy' : Fixing ((pInv f y).val.length + 1) f := by simpa [h_length_pInv] using hy
  have hnode : f (pInv f y) = y := cancel_pInv_right f y (hy.mon (by simp))
  change (cast (congrArg ExtensionsAt hnode) (extensionsEquiv f (pInv f y) hy' a)).valT' =
    f a.valT'
  exact (ExtensionsAt.cast_valT' hnode (extensionsEquiv f (pInv f y) hy' a)).trans
    (extensionsEquiv_val' f (pInv f y) a hy')
@[simp] lemma extensionsEquiv'_val' (a : ExtensionsAt y) (hy : Fixing (y.val.length + 1) f) :
  (extensionsEquiv' f y hy a).valT' = pInv f a.valT' := by
  obtain ⟨a, rfl⟩ := (extensionsEquiv' f y).symm.surjective a
  simp only [Equiv.apply_symm_apply, extensionsEquiv'_symm_val', cancel_pInv_left]

@[simp] lemma val_res_zero (x : (res 0).obj S) : x.val = [] :=
  List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (res_len_le x))
lemma zero_fixing : Fixing 0 f ↔ ([] ∈ S.2 ↔ [] ∈ T.2) := by
  rw [fixing_iff_forget_isIso]; constructor
  · intro h; constructor <;> intro hn
    · rw [← LenHom.map_nil f hn]
      exact (SetLike.coe_mem _)
    · obtain ⟨x, _⟩ := surjective_of_epi ((res 0 ⋙ forget Trees).map f) ⟨[], hn, by rfl⟩
      have hxmem := x.prop.1
      rwa [val_res_zero x] at hxmem
  intro ⟨_, h⟩; apply (isIso_iff_bijective _).mpr; constructor
  · intro x y _
    apply res_ext
    rw [val_res_zero x, val_res_zero y]
  · intro y
    have hy : [] ∈ T.2 := by
      have hymem := y.prop.1
      rwa [val_res_zero y] at hymem
    refine ⟨⟨[], h hy, by rfl⟩, ?_⟩
    apply res_ext
    exact (LenHom.map_nil f (h hy)).trans (val_res_zero y).symm

lemma lim_isPruned (F : ℕᵒᵖ ⥤ Trees)
  (hF : ∀ n, Tree.Fixing n (F.map (homOfLE (Nat.le_succ n)).op))
  (h : ∀ n, IsPruned (F.obj (Opposite.op n)).2) :
  IsPruned (limCone F).pt.2 := by
  intro x
  have hp :
      Fixing (x.val.length + 1) ((limCone F).π.app (Opposite.op (x.val.length + 1))) := by
    simpa only [Nat.zero_add] using proj_fixing F 0 (by simpa) (x.val.length + 1)
  exact (extensionsEquiv
    ((limCone F).π.app (Opposite.op (x.val.length + 1))) x hp).nonempty_congr.mpr
    (h (x.val.length + 1)
      (((limCone F).π.app (Opposite.op (x.val.length + 1))) x))
lemma lim_ne (F : ℕᵒᵖ ⥤ Trees) (hF : ∀ n, Tree.Fixing n (F.map (homOfLE (Nat.le_succ n)).op))
  (h : ∀ n, [] ∈ (F.obj (Opposite.op n)).2) : [] ∈ (limCone F).pt.2 :=
  ((zero_fixing _).mp ((proj_fixing F 0 (by simpa) 0).mon (by simp))).mpr (h 0)
end «Section1»
end Descriptive.Tree
