/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.Hom
import LeanPool.QuasiBorelSpaces.Rose.Encoding
import LeanPool.QuasiBorelSpaces.List
import LeanPool.QuasiBorelSpaces.Option
import LeanPool.QuasiBorelSpaces.Nat
import LeanPool.QuasiBorelSpaces.Pi
import LeanPool.QuasiBorelSpaces.ProbabilityMeasure
import LeanPool.QuasiBorelSpaces.Sigma

/-!
# LeanPool.QuasiBorelSpaces.Rose

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Rose`.
-/

variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

namespace Rose.Encoding

open QuasiBorelSpace

@[simp, fun_prop]
lemma isHom_mk : IsHom (fun x : A × List (Rose.Encoding A) ↦ mk x.1 x.2) := by
  unfold mk
  apply isHom_cases (f := fun s (x : A × _) ↦ (⟨s, (mk x.1 x.2).2⟩ : Encoding _))
  · let : QuasiBorelSpace (Rose Unit) := default
    let : MeasurableSpace (Rose Unit) := ⊤
    fun_prop
  · intro t
    simp only [mk]
    apply Sigma.isHom_mk'
    simp only [Pi.isHom_iff]
    intro is
    cases is with
    | nil => simp only [Prod.isHom_fst]
    | cons head tail => fun_prop

@[fun_prop]
lemma isHom_fold
      {mk : A → List B → B} (hmk : IsHom fun (x, y) ↦ mk x y)
    : IsHom (fold mk) := by
  apply Sigma.isHom_elim
  intro t
  induction t with | mk label children ih =>
  have {k : List ℕ → A}
      : fold mk ⟨{ label := label, children := children }, k⟩
      = fold mk (Encoding.mk (k []) (List.ofFn fun i ↦ ⟨children[i], fun is ↦ k (i :: is)⟩)) := by
    simp only [
      Encoding.mk, Fin.getElem_fin, List.map_ofFn, List.getElem?_ofFn,
      Option.map_dif, dite_eq_ite, fold, List.length_ofFn, Fin.val_cast,
      List.getElem_ofFn, Fin.eta, Function.comp_apply, Fin.is_lt, ↓reduceIte,
      Option.getD_some]
    nth_rw 1 [fold]
    simp only [Fin.getElem_fin]
  simp only [this, Fin.getElem_fin, fold_mk, List.map_ofFn]
  have : IsHom fun (x : List ℕ → A) ↦
      (List.ofFn (fold mk ∘ fun i ↦ ⟨children[↑i], fun is ↦ x (↑i :: is)⟩)) := by
    apply List.isHom_ofFn
    simp only [Fin.getElem_fin, Function.comp_apply]
    apply isHom_cases
        (ix := fun x : (List ℕ → A) × Fin children.length ↦ x.2)
        (f := fun n x ↦ fold mk ⟨children[n], fun is ↦ x.1 (↑x.2 :: is)⟩)
    · fun_prop
    · intro n
      specialize ih children[n] (by simp only [Fin.getElem_fin, List.getElem_mem])
      apply isHom_comp' ih
      simp only [Pi.isHom_iff]
      intro i
      apply isHom_cases
          (ix := fun x : (List ℕ → A) × Fin children.length ↦ (↑x.2 :: i))
          (f := fun is x ↦ x.1 is)
      · fun_prop
      · fun_prop
  fun_prop

end Rose.Encoding

namespace QuasiBorelSpace.Rose

instance : QuasiBorelSpace (Rose A) := lift Rose.Encoding.encode

@[simp, fun_prop]
lemma isHom_encode : IsHom (Rose.Encoding.encode (A := A)) := by
  apply isHom_of_lift

@[fun_prop]
lemma isHom_mk : IsHom (fun x : A × List (Rose A) ↦ Rose.mk x.1 x.2) := by
  simp only [isHom_to_lift, Rose.Encoding.encode_mk]
  fun_prop

lemma isHom_cons'
    {f : A → B} (hf : IsHom f)
    {g : A → List (Rose B)} (hg : IsHom g)
    : IsHom (fun x ↦ Rose.mk (f x) (g x)) := by
  fun_prop

@[local fun_prop]
lemma isHom_fold
    {mk : A → List B → B} (hmk : IsHom fun (x, xs) ↦ mk x xs)
    : IsHom (Rose.fold mk) := by
  have : Rose.fold mk = fun xs ↦ Rose.Encoding.fold mk (.encode xs) := by
    ext t
    induction t with | mk label children ih =>
    simp only [Rose.fold.eq_1, Rose.Encoding.encode_mk, Rose.Encoding.fold_mk, List.map_map]
    congr 1
    simp only [List.map_inj_left, Function.comp_apply]
    grind
  rw [this]
  fun_prop

private def foldAlgHom
    (mk : A → B → List C → C)
    (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    : B → List (A →𝒒 C) → A →𝒒 C :=
  fun b ks ↦
    QuasiBorelHom.mk
      (fun a ↦ mk a b (List.map (fun k : A →𝒒 C ↦ k a) ks)) (by
        fun_prop)

private lemma map_congr'
    {α β : Type*} {l : List α} {f g : α → β}
    (h : ∀ x ∈ l, f x = g x) : List.map f l = List.map g l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : f x = g x := by
        exact h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

private lemma fold_pointwise
    (mk : A → B → List C → C)
    (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    (t : Rose B) (a : A)
    : Rose.fold (mk a) t
      =
        (Rose.Encoding.fold
            (A := B)
            (mk := foldAlgHom mk hmk)
            (Rose.Encoding.encode (A := B) t) : A →𝒒 C) a := by
  induction t with
  | mk label children ih =>
      have : List.map (fun child ↦ Rose.fold (mk a) child) children
          = List.map ((fun k : A →𝒒 C ↦ k a) ∘
              Rose.Encoding.fold (A := B) (mk := foldAlgHom mk hmk) ∘
              Rose.Encoding.encode (A := B)) children := by
        simp only [List.map_inj_left, Function.comp_apply]
        intro child hmem
        simpa using ih child hmem
      simp [Rose.fold.eq_1, Rose.Encoding.encode_mk, Rose.Encoding.fold_mk,
        foldAlgHom, List.map_map, this]

private lemma fold_as_quasiBorelHom
    (mk : A → B → List C → C)
    (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    (f : A → Rose B)
    : (fun x ↦ Rose.fold (mk x) (f x))
      =
        (fun x ↦
          (Rose.Encoding.fold
              (A := B)
              (mk := foldAlgHom mk hmk)
              (Rose.Encoding.encode (A := B) (f x)) : A →𝒒 C) x) := by
  funext x
  simpa using fold_pointwise mk hmk (f x) x

@[fun_prop]
lemma isHom_fold'
    {mk : A → B → List C → C} (hmk : IsHom fun (x, y, z) ↦ mk x y z)
    {f : A → Rose B} (hf : IsHom f)
    : IsHom (fun x ↦ Rose.fold (mk x) (f x)) := by
  have hrewrite := fold_as_quasiBorelHom (A := A) (B := B) (C := C) mk hmk f
  have h_fold : IsHom (Rose.Encoding.fold (foldAlgHom mk hmk)) := by
    have : IsHom (fun (b, ks) ↦ foldAlgHom mk hmk b ks) := by
      dsimp [foldAlgHom]; fun_prop
    simpa [foldAlgHom] using Rose.Encoding.isHom_fold (hmk := this)
  simpa [hrewrite] using by fun_prop

@[simp, fun_prop]
lemma isHom_label : IsHom (fun t : Rose A ↦ t.label) := by
  have h : IsHom (fun e : Rose.Encoding A ↦ e.2 []) := by
    fun_prop
  have hencode : IsHom (Rose.Encoding.encode (A := A)) := isHom_encode (A := A)
  have hcomp := isHom_comp' h hencode
  have hfun : (fun t : Rose A ↦ (Rose.Encoding.encode t).2 [])
      = fun t ↦ t.label := by
    funext t
    cases t with
    | mk label children =>
        simp [Rose.Encoding.encode_mk, Rose.Encoding.mk]
  simpa [hfun] using hcomp

private def childrenFoldAlg (x : C) (xs : List (Rose C × List (Rose C)))
    : Rose C × List (Rose C) :=
  let children := List.map Prod.fst xs
  (Rose.mk x children, children)

omit [QuasiBorelSpace C] in
private lemma fold_children_eq
    (t : Rose C)
    : Rose.Encoding.fold (childrenFoldAlg (C := C)) (Rose.Encoding.encode t)
        = (t, t.children) := by
  induction t with
  | mk label children ih =>
      have hxs :
          List.map
              (Rose.Encoding.fold (childrenFoldAlg (C := C))
                ∘ Rose.Encoding.encode (A := C))
              children
            = List.map (fun child ↦ (child, child.children)) children := by
        refine map_congr' ?_
        intro child hmem
        simpa using ih child hmem
      have hchildren :
          List.map (Prod.fst ∘ fun child ↦ (child, child.children)) children
            = children := by
        unfold Function.comp
        simp
      simp [Rose.Encoding.encode_mk, Rose.Encoding.fold_mk, childrenFoldAlg,
        hxs, List.map_map, hchildren]

@[simp, fun_prop]
lemma isHom_children : IsHom (fun t : Rose C ↦ t.children) := by
  have hfold : IsHom (Rose.Encoding.fold (childrenFoldAlg (C := C))) := by
    have : IsHom (fun (x, xs) ↦ childrenFoldAlg (C := C) x xs) := by
      dsimp [childrenFoldAlg]; fun_prop
    simpa [childrenFoldAlg] using Rose.Encoding.isHom_fold (hmk := this)
  have heq : (fun t : Rose C ↦
        (Rose.Encoding.fold (childrenFoldAlg (C := C)) (Rose.Encoding.encode t)).2)
      = fun t ↦ t.children := by
    funext t
    simp [fold_children_eq]
  have : IsHom (fun e ↦ (Rose.Encoding.fold (childrenFoldAlg (C := C)) e).2) :=
    isHom_comp' (by fun_prop) hfold
  simpa [heq] using isHom_comp' this isHom_encode

private def bindFoldAlg (f : B → Rose C) (b : B) (zs : List (Rose C)) : Rose C :=
  let t := f b
  Rose.mk t.label (List.foldr (fun child acc ↦ child :: acc) zs t.children)

lemma isHom_bind
    {f : A → B → Rose C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Rose B} (hg : IsHom g)
    : IsHom (fun x ↦ Rose.bind (f x) (g x)) := by
  let mkBind : A → B → List (Rose C) → Rose C :=
    fun x b zs ↦ bindFoldAlg (f x) b zs
  have hrewrite : (fun x ↦ Rose.bind (f x) (g x))
        = fun x ↦ Rose.fold (mkBind x) (g x) := by
    funext x
    suffices ∀ t : Rose B, Rose.bind (f x) t = Rose.fold (mkBind x) t by
      simpa using this (g x)
    intro t
    induction t with
    | mk label children ih =>
        have : List.map (Rose.fold (mkBind x)) children
            = List.map (Rose.bind (f x)) children := by
          simp only [List.map_inj_left]
          intro child hmem
          simpa [mkBind] using (ih child hmem).symm
        simp [Rose.bind, mkBind, bindFoldAlg]
  have : IsHom fun (x, y, z) ↦ mkBind x y z := by
    dsimp [mkBind, bindFoldAlg]
    fun_prop
  simpa [hrewrite] using isHom_fold' this hg

instance [SeparatesPoints A] : SeparatesPoints (Rose A) where
  separates t u ht := by
    induction t generalizing u with | mk x xs ih =>
    cases u with | mk y ys =>
    simp only [Rose.mk.injEq]
    apply And.intro
    · apply separatesPoints_def
      intro p hp hlabel
      apply ht (p ∘ Rose.label) (by fun_prop) hlabel
    · apply List.ext_get
      · apply ht (fun t ↦ xs.length = t.children.length) ?_ rfl
        apply isHom_cases (f := fun n _ ↦ xs.length = n) <;> fun_prop
      · simp only [List.get_eq_getElem]
        intro n h₁ h₂
        apply ih
        · simp only [List.getElem_mem]
        · intro p hp hxs
          specialize ht (fun t ↦ if h : _ then p (t.children.get ⟨n, h⟩) else False)
          simp only [List.get_eq_getElem, h₁, ↓reduceDIte, h₂] at ht
          apply ht ?_ hxs
          apply Prop.isHom_dite
          · fun_prop
          · apply isHom_comp' hp
            apply List.isHom_get <;> fun_prop
          · fun_prop

end QuasiBorelSpace.Rose
