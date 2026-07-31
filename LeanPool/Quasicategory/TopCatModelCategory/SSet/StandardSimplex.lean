/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.SSet.HasDimensionLT
import LeanPool.Quasicategory.TopCatModelCategory.SSet.StrictSegal
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Degenerate
import LeanPool.Quasicategory.TopCatModelCategory.SSet.SimplexCategory

universe u

open CategoryTheory Opposite Simplicial

theorem Finset.image_comp (f : β → γ) (g : α → β) [DecidableEq β] [DecidableEq γ]
    (a : Finset α) :
    Finset.image (f ∘ g) a = Finset.image f (Finset.image g a) := by aesop

namespace SSet

@[simp]
lemma yonedaEquiv₀ {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv (const x) = x :=
  yonedaEquiv.symm.injective (by simp)

lemma yonedaEquiv_map_comp {n m : SimplexCategory} (f : n ⟶ m) {X : SSet.{u}}
    (g : stdSimplex.obj m ⟶ X) :
    yonedaEquiv (stdSimplex.map f ≫ g) =
      X.map f.op (yonedaEquiv g) := by
  dsimp [yonedaEquiv, yonedaCompUliftFunctorEquiv]
  rw [← NatTrans.naturality_apply]
  rfl

@[simp]
lemma yonedaEquiv_symm_comp {X Y : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
    (f : X ⟶ Y) :
    yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app _ x) := by
  apply yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply, yonedaEquiv_comp]

lemma yonedaEquiv_symm_map {X : SSet.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (x : X.obj (op m)) :
    yonedaEquiv.symm (X.map f.op x) =
      stdSimplex.map f ≫ yonedaEquiv.symm x := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_map_comp, Equiv.apply_symm_apply]

lemma yonedaEquiv_symm_δ {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2)) (x : X _⦋n + 1⦌) :
    yonedaEquiv.symm (X.δ i x) =
      stdSimplex.δ i ≫ yonedaEquiv.symm x := by
  apply yonedaEquiv_symm_map

lemma yonedaEquiv_symm_σ {X : SSet.{u}} {n : ℕ} (i : Fin (n + 1)) (x : X _⦋n⦌) :
    yonedaEquiv.symm (X.σ i x) =
      stdSimplex.σ i ≫ yonedaEquiv.symm x := by
  apply yonedaEquiv_symm_map

@[simp]
lemma yonedaEquiv_symm_app_id {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    (yonedaEquiv.symm x).app _ (yonedaEquiv (𝟙 _)) = x := by
  apply yonedaEquiv.symm.injective
  rw [← yonedaEquiv_symm_comp]
  simp only [Equiv.symm_apply_apply, Category.id_comp]


namespace stdSimplex

instance (n : ℕ) {m : SimplexCategoryᵒᵖ} : Finite ((Δ[n] : SSet.{u}).obj m) := by
  dsimp [stdSimplex, uliftFunctor]
  infer_instance

/-instance (n i : ℕ) : DFunLike (Δ[n] _⦋i⦌) (Fin (i + 1)) (fun _ ↦ Fin (n + 1)) where
  coe x j := (objEquiv _ _ x).toOrderHom j
  coe_injective' j₁ j₂ h := by
    apply (objEquiv _ _).injective
    ext k : 3
    exact congr_fun h k-/

lemma monotone_apply {n i : ℕ} (x : Δ[n] _⦋i⦌) : Monotone (fun (j : Fin (i + 1)) ↦ x j) :=
  (objEquiv x).toOrderHom.monotone

/-@[ext]
lemma ext {n : ℕ} (x y : Δ[n] _[i]) (h : ∀ (i : Fin (i + 1)), x i = y i) : x = y := by
  apply (objEquiv _ _).injective
  ext i : 3
  apply h

@[simp]
lemma objEquiv_symm_apply {n m : ℕ} (f : SimplexCategory.mk m ⟶ [n])
    (i : Fin (m + 1)) :
    (objEquiv.{u} _ (op [m])).symm f i = f.toOrderHom i := rfl-/

@[simp]
lemma yonedaEquiv_id_apply {n : ℕ} (i : Fin (n + 1)) :
    yonedaEquiv.{u} (𝟙 (Δ[n])) i = i := rfl

@[simp]
lemma yonedaEquiv_const_apply {n : ℕ} {m : ℕ}
    (x : Δ[n] _⦋0⦌) (i : Fin (m + 1)) :
    (yonedaEquiv (SSet.const x) : Δ[n] _⦋0⦌) i = x 0 := rfl

/-@[simps]
def obj₀Equiv {n : ℕ} : Δ[n] _[0] ≃ Fin (n + 1) where
  toFun x := x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl
  right_inv _ := rfl-/

@[simp]
lemma map_objMk {n : SimplexCategory} {m m' : SimplexCategoryᵒᵖ}
    (f : Fin (m.unop.len + 1) →o Fin (n.len + 1)) (g : m ⟶ m') :
    (stdSimplex.{u}.obj n).map g (objMk f) =
      objMk (f.comp g.unop.toOrderHom) := rfl

/-@[simp]
lemma objMk_apply {n m : ℕ}
    (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    objMk.{u} (n := .mk n) (m := op (.mk m)) f i = f i :=
  rfl-/

lemma map_op_apply {n m p : ℕ} (x : Δ[n] _⦋m⦌)
    (g : SimplexCategory.mk p ⟶ ⦋m⦌) (i : Fin (p + 1)) :
      Δ[n].map g.op x i = x (g.toOrderHom i) := rfl

lemma map_objEquiv_symm_apply {n : ℕ} {m : SimplexCategory} (f : m ⟶ .mk n)
    {p : ℕ} (g :  .mk p ⟶ m) (i : Fin (p + 1)) :
    Δ[n].map g.op (objEquiv.{u}.symm f) i = f.toOrderHom (g.toOrderHom i) := rfl

lemma map_objEquiv_symm {n : ℕ} {m : SimplexCategory} (f : m ⟶ .mk n)
    {p : ℕ} (g :  .mk p ⟶ m) :
    Δ[n].map g.op (objEquiv.{u}.symm f) = objEquiv.symm (g ≫ f) := rfl

@[simp]
lemma objEquiv_symm_σ_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin (n + 1 + 1)) :
    ((objEquiv.{u}).symm (SimplexCategory.σ i) : Δ[n] _⦋n + 1⦌) j =
      i.predAbove j :=
  rfl

lemma map_yonedaEquiv {X : SSet.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (g : stdSimplex.obj m ⟶ X) :
    X.map f.op (yonedaEquiv g) = g.app _ (yonedaEquiv (stdSimplex.map f)) := by
  dsimp [yonedaEquiv, yonedaCompUliftFunctorEquiv]
  rw [← NatTrans.naturality_apply]
  rfl

instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).StrictSegal where
  spineToSimplex {j v} := objMk
    { toFun i := obj₀Equiv (v.vertex i)
      monotone' := by
        induction' n using SimplexCategory.rec with n
        rw [Fin.monotone_iff]
        intro i
        rw [← v.arrow_src i, ← v.arrow_tgt i]
        exact (monotone_apply (v.arrow i) (Fin.zero_le (1 : Fin 2))) }
  spine_spineToSimplex {i} p := by
    induction' n using SimplexCategory.rec with n
    dsimp
    ext j k : 3
    · fin_cases k
      rfl
    · fin_cases k
      · exact (DFunLike.congr_fun (p.arrow_src j) 0).symm
      · exact (DFunLike.congr_fun (p.arrow_tgt j) 0).symm
  spineToSimplex_spine x := by
    induction' n using SimplexCategory.rec with n
    ext
    rfl

@[ext]
lemma path_ext {n i : ℕ} {x y : Path Δ[n] i} (h : x.vertex = y.vertex) : x = y := by
  obtain ⟨v, a, h₁, h₂⟩ := x
  obtain ⟨w, b, h₃, h₄⟩ := y
  obtain rfl := h
  dsimp at h₃ h₄
  simp only [Path.mk.injEq, true_and]
  ext j k : 2
  fin_cases k
  · exact (DFunLike.congr_fun (h₁ j) 0).trans (DFunLike.congr_fun (h₃ j) 0).symm
  · exact (DFunLike.congr_fun (h₂ j) 0).trans (DFunLike.congr_fun (h₄ j) 0).symm

lemma mono_iff (n : ℕ) (f : Δ[n] ⟶ Y) :
    Mono f ↔ Function.Injective (f.app (op ⦋0⦌)):= by
  constructor
  · intro hf
    rw [NatTrans.mono_iff_mono_app] at hf
    simp only [mono_iff_injective] at hf
    apply hf
  · intro hf
    rw [mono_iff_of_strictSegal]
    intro x₁ x₂ h
    apply StrictSegal.spineInjective
    ext i : 2
    apply hf
    dsimp [StrictSegal.spineEquiv, spine]
    simp only [NatTrans.naturality_apply, h]

variable {n : ℕ}

@[ext]
lemma ext' {j : SimplexCategoryᵒᵖ} {x y : (Δ[n] : SSet.{u}).obj j} -- duplicate?
    (h : objEquiv x = objEquiv y) : x = y :=
  objEquiv.injective h

attribute [local simp] Finset.image_subset_iff

/-@[simps (config := .lemmasOnly)]
def face (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex where
  obj U := setOf (fun f ↦ Finset.image ((objEquiv _ _) f).toOrderHom ⊤ ≤ S)
  map {U V} i := by
    simp
    intro x hx y
    apply hx

@[simp]
lemma mem_face_iff (S : Finset (Fin (n + 1))) {d : ℕ} (x : (Δ[n] : SSet.{u}) _[d]) :
    x ∈ (face S).obj _ ↔ ∀ (i : Fin (d + 1)), x i ∈ S := by
  simp [face]
  rfl-/

--@[deprecated (since := "2025-03-19")]
--alias Subcomplex.inter_obj := Subpresheaf.min_obj

/-@[simp]
lemma Subcomplex.inter_obj {X : SSet.{u}} (A B : X.Subcomplex) (n : SimplexCategoryᵒᵖ) :
    (A ⊓ B).obj n = A.obj n ⊓ B.obj n := by
  rfl

lemma face_inter_face (S₁ S₂ : Finset (Fin (n + 1))) :
    face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂) := by
  dsimp [face]
  aesop

def faceRepresentableBy (S : Finset (Fin (n + 1)))
    (m : ℕ) (e : Fin (m + 1) ≃o S) :
    (face S : SSet.{u}).RepresentableBy (.mk m) where
  homEquiv {j} :=
    { toFun f := ⟨objMk ((OrderHom.Subtype.val S.toSet).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ ↦ by aesop⟩
      invFun := fun ⟨x, hx⟩ ↦ SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv _ _ x).toOrderHom i, hx (by aesop)⟩
          monotone' i₁ i₂ h := e.symm.monotone (by
            simp only [Subtype.mk_le_mk]
            exact OrderHom.monotone _ h) }
      left_inv f := by
        ext i : 3
        apply e.symm_apply_apply
      right_inv := fun ⟨x, hx⟩ ↦ by
        dsimp
        ext i : 5
        exact congr_arg Subtype.val
          (e.apply_symm_apply ⟨(objEquiv _ _ x).toOrderHom i, _⟩) }
  homEquiv_comp f g := by aesop

def isoOfRepresentableBy {X : SSet.{u}} {m : ℕ} (h : X.RepresentableBy (.mk m)) :
    Δ[m] ≅ X :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso ((objEquiv _ _).trans h.homEquiv)) (by
    intros
    ext x
    apply h.homEquiv_comp)-/

@[simp]
lemma yonedaEquiv_isoOfRepresentableBy_hom
    {X : SSet.{u}} {m : ℕ} (h : X.RepresentableBy (.mk m)) :
    yonedaEquiv (isoOfRepresentableBy h).hom = h.homEquiv (𝟙 _) := rfl

lemma obj₀Equiv_symm_mem_face_iff (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    (obj₀Equiv.symm i) ∈ (face S).obj (op (.mk 0)) ↔ i ∈ S := by
  constructor
  · intro h
    simp at h
    exact h 0
  · aesop

lemma face_le_face_iff (S₁ S₂ : Finset (Fin (n + 1))) :
    face.{u} S₁ ≤ face S₂ ↔ S₁ ≤ S₂ := by
  constructor
  · intro h i hi
    simp only [← obj₀Equiv_symm_mem_face_iff.{u}] at hi ⊢
    exact h _ hi
  · intro h d a ha
    dsimp [face] at ha ⊢
    exact ha.trans h

@[simp]
lemma face_emptySet (n : ℕ) : (face (∅ : Finset (Fin (n + 1)))) = ⊥ := by
  ext ⟨k⟩
  simp only [face, SimplexCategory.len_mk, Finset.top_eq_univ, Finset.le_eq_subset,
    Finset.subset_empty, Finset.image_eq_empty, Set.mem_setOf_eq, Subpresheaf.bot_obj,
    Set.bot_eq_empty, Set.mem_empty_iff_false, iff_false]
  intro h
  have := Finset.mem_univ (0 : Fin (k.len + 1))
  simp [h] at this

/-lemma face_eq_ofSimplex (S : Finset (Fin (n + 1))) (m : ℕ) (e : Fin (m + 1) ≃o S) :
    face.{u} S = Subcomplex.ofSimplex (n := m)
        (by exact objMk ((OrderHom.Subtype.val S.toSet).comp e.toOrderEmbedding.toOrderHom)) := by
  apply le_antisymm
  · rintro ⟨k⟩ x hx
    induction' k using SimplexCategory.rec with k
    rw [mem_face_iff] at hx
    let φ : Fin (k + 1) →o S :=
      { toFun i := ⟨x i, hx i⟩
        monotone' := (objEquiv _ _ x).toOrderHom.monotone }
    refine ⟨stdSimplex.objMk
      (e.symm.toOrderEmbedding.toOrderHom.comp φ), ?_⟩
    obtain ⟨f, rfl⟩ := (objEquiv _ _).symm.surjective x
    ext j : 1
    simpa only [Subtype.ext_iff] using e.apply_symm_apply ⟨_, hx j⟩
  · simp [Subcomplex.ofSimplex_le_iff]-/

lemma face_singleton_compl (i : Fin (n + 2)) :
    face.{u} {i}ᶜ =
      Subcomplex.ofSimplex (objEquiv.symm (SimplexCategory.δ i)) := by
  let e : Fin (n + 1) ≃o ({i}ᶜ : Finset _) :=
    { toEquiv := (finSuccAboveEquiv (p := i)).trans
        { toFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
          invFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
          left_inv _ := rfl
          right_inv _ := rfl }
      map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff }
  exact face_eq_ofSimplex _ _ e

def faceSingletonComplIso (i : Fin (n + 2)) :
    Δ[n] ≅ (face {i}ᶜ : SSet.{u}) := by
  apply isoOfRepresentableBy
  apply faceRepresentableBy
  exact
    { toEquiv := (finSuccAboveEquiv (p := i)).trans
        { toFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
          invFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
          left_inv _ := rfl
          right_inv _ := rfl }
      map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff }

@[reassoc (attr := simp)]
lemma faceSingletonComplIso_hom_ι (i : Fin (n + 2)) :
    (faceSingletonComplIso.{u} i).hom ≫ (face {i}ᶜ).ι =
      stdSimplex.δ i := rfl

@[simps! apply]
noncomputable def _root_.Finset.orderIsoOfOrderEmbedding
    {α β : Type*} [Preorder α] [Preorder β] [DecidableEq β] [Fintype α]
    (f : α ↪o β) (S : Finset β) (hS : Finset.image f ⊤ = S) : α ≃o S where
  toEquiv := Equiv.ofBijective (f := fun a ↦ ⟨f a, by simp [← hS]⟩)
    ⟨fun _ _ _ ↦ by aesop, fun _ ↦ by aesop⟩
  map_rel_iff' := by simp

noncomputable def _root_.Fin.orderIsoPairCompl (i j : Fin (n + 3)) (h : i < j) :
    Fin (n + 1) ≃o ({i, j}ᶜ : Finset _) :=
  let φ :=
    (Fin.succAboveOrderEmb (i.castPred (Fin.ne_last_of_lt h))).trans
      (Fin.succAboveOrderEmb j)
  Finset.orderIsoOfOrderEmbedding φ _ (by
    apply Finset.eq_of_subset_of_card_le
    · intro _ h
      simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨x, rfl⟩ := h
      simp only [Finset.compl_insert, Finset.mem_erase, ne_eq, Finset.mem_compl,
        Finset.mem_singleton]
      constructor
      · intro hi
        obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
        dsimp [φ] at hi
        by_cases hx : x.castSucc < i
        · rw [Fin.succAbove_of_castSucc_lt _ _ hx,
            Fin.succAbove_of_castSucc_lt _ _ (lt_trans (by simpa) h),
            Fin.castSucc_inj] at hi
          omega
        · rw [not_lt] at hx
          rw [Fin.succAbove_of_le_castSucc _ _ hx] at hi
          by_cases hx' : x.succ.castSucc < j
          · rw [Fin.succAbove_of_castSucc_lt _ _ hx', Fin.castSucc_inj] at hi
            simp only [← hi, Fin.succ_le_castSucc_iff, lt_self_iff_false] at hx
          · rw [not_lt] at hx'
            rw [Fin.succAbove_of_le_castSucc _ _ hx'] at hi
            rw [← Fin.castSucc_le_castSucc_iff, ← hi,
              Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc,
              Fin.val_succ, Fin.coe_castSucc] at hx
            omega
      · apply Fin.succAbove_ne
    · rw [Finset.card_image_of_injective _ φ.injective,
        Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
        ← Nat.add_le_add_iff_right (n := Finset.card {i, j}),
        Finset.card_compl_add_card,
        Finset.card_pair h.ne, Fintype.card_fin])

noncomputable def facePairComplIso (i j : Fin (n + 3)) (h : i < j) :
    Δ[n] ≅ (face {i, j}ᶜ : SSet.{u}) := by
  apply isoOfRepresentableBy
  apply faceRepresentableBy
  apply Fin.orderIsoPairCompl i j h

@[reassoc]
lemma facePairComplIso_hom_ι (i j : Fin (n + 3)) (h : i < j) :
    (facePairComplIso.{u} i j h).hom ≫ (face {i, j}ᶜ).ι =
      stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) ≫ stdSimplex.δ j :=
  rfl

@[reassoc]
lemma facePairComplIso_hom_ι' (i j : Fin (n + 3)) (h : i < j) :
    (facePairComplIso.{u} i j h).hom ≫ (face {i, j}ᶜ).ι =
      stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) ≫ stdSimplex.δ i := by
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  obtain rfl | ⟨i, rfl⟩ := i.eq_last_or_eq_castSucc
  · have := j.succ.le_last
    omega
  · rw [facePairComplIso_hom_ι,
      Fin.pred_succ, Fin.castPred_castSucc, CosimplicialObject.δ_comp_δ]
    rw [← Fin.succ_le_succ_iff, ← Fin.castSucc_lt_iff_succ_le]
    exact h

lemma face_pair_compl_le₁ (i j : Fin (n + 3)) : face {i, j}ᶜ ≤ face {i}ᶜ := by
  simp [face_le_face_iff]

lemma face_pair_compl_le₂ (i j : Fin (n + 3)) : face {i, j}ᶜ ≤ face {j}ᶜ := by
  simp [face_le_face_iff]

@[reassoc]
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_pred
    (i j : Fin (n + 3)) (h : i < j) :
    Subcomplex.homOfLE (face_pair_compl_le₁ i j) ≫
      (faceSingletonComplIso.{u} i).inv =
        (facePairComplIso i j h).inv ≫ stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) := by
  rw [← cancel_mono (faceSingletonComplIso.{u} i).hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    ← cancel_mono (Subpresheaf.ι _), Category.assoc, Category.assoc,
    Subcomplex.homOfLE_ι, faceSingletonComplIso_hom_ι,
    ← cancel_epi (facePairComplIso i j h).hom,
    Iso.hom_inv_id_assoc, facePairComplIso_hom_ι']

@[reassoc]
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_castPred
    (i j : Fin (n + 3)) (h : i < j) :
    Subcomplex.homOfLE (face_pair_compl_le₂ i j) ≫
      (faceSingletonComplIso.{u} j).inv =
        (facePairComplIso i j h).inv ≫
          stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) := by
  rw [← cancel_mono (faceSingletonComplIso.{u} j).hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    ← cancel_mono (Subpresheaf.ι _), Category.assoc, Category.assoc,
    Subcomplex.homOfLE_ι, faceSingletonComplIso_hom_ι,
    ← cancel_epi (facePairComplIso i j h).hom,
    Iso.hom_inv_id_assoc, facePairComplIso_hom_ι]

noncomputable def faceSingletonIso (i : Fin (n + 1)) :
    Δ[0] ≅ (face {i} : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
      (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoSingleton i))

@[reassoc]
lemma faceSingletonIso_zero_hom_comp_ι_eq_δ :
    (faceSingletonIso.{u} (0 : Fin 2)).hom ≫ (face {0}).ι = stdSimplex.δ 1 := by
  apply yonedaEquiv.injective
  ext i
  fin_cases i
  rfl

@[reassoc]
lemma faceSingletonIso_one_hom_comp_ι_eq_δ :
    (faceSingletonIso.{u} (1 : Fin 2)).hom ≫ (face {1}).ι = stdSimplex.δ 0 := by
  apply yonedaEquiv.injective
  ext i
  fin_cases i
  rfl

noncomputable def facePairIso (i j : Fin (n + 1)) (hij : i < j) :
    Δ[1] ≅ (face {i, j} : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
      (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoPair i j hij))

lemma mem_nonDegenerate_iff_mono {d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ Δ[n].nonDegenerate d ↔ Mono (objEquiv x) := by
  obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
  simp only [Equiv.apply_symm_apply]
  constructor
  · obtain _ | d := d
    · infer_instance
    · obtain ⟨f, rfl⟩ : ∃ (g : Fin (d + 2) →o Fin (n + 1)), SimplexCategory.mkHom g = f :=
        ⟨f.toOrderHom, rfl⟩
      contrapose
      intro hf
      simp only [SimplexCategory.mono_iff_injective, Fin.orderHom_injective_iff,
        not_forall, Decidable.not_not] at hf
      obtain ⟨i, hi⟩ := hf
      dsimp at i f
      simp only [SimplexCategory.len_mk, SimplexCategory.mkHom,
        SimplexCategory.Hom.toOrderHom_mk] at hi
      simp only [← mem_degenerate_iff_not_mem_nonDegenerate, degenerate_eq_iUnion_range_σ,
        Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_range]
      refine ⟨i, objMk (f.comp (SimplexCategory.δ i.castSucc).toOrderHom), ?_⟩
      ext j : 1
      dsimp [SimplicialObject.σ, SimplexCategory.δ, SimplexCategory.σ]
      rw [objEquiv_symm_apply, SimplexCategory.Hom.toOrderHom_mk]
      by_cases hj : j = i.castSucc
      · simpa [hj] using hi.symm
      · exact congr_arg f (Fin.succAbove_predAbove hj)
  · intro
    rw [mem_nonDegenerate_iff_not_mem_degenerate, SSet.mem_degenerate_iff]
    rintro ⟨m, hm, p, _, ⟨g, hg⟩⟩
    obtain ⟨g, rfl⟩ := objEquiv.symm.surjective g
    simp only [map_apply, Quiver.Hom.unop_op, Equiv.apply_symm_apply,
      EmbeddingLike.apply_eq_iff_eq] at hg
    have := SimplexCategory.le_of_mono (mono_of_mono_fac hg)
    omega

variable (n) in
lemma bijective_image_objEquiv_toOrderHom_top (m : ℕ) :
    Function.Bijective (fun (⟨x, hx⟩ : (Δ[n] : SSet.{u}).nonDegenerate m) ↦
      (⟨Finset.image (objEquiv x).toOrderHom ⊤, by
        rw [mem_nonDegenerate_iff_mono, SimplexCategory.mono_iff_injective] at hx
        dsimp
        rw [Finset.card_image_of_injective _ (by exact hx), Finset.card_univ,
          Fintype.card_fin]⟩ : { S : Finset (Fin (n + 1)) | S.card = m + 1 })) := by
  constructor
  · rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h₃
    obtain ⟨f₁, rfl⟩ := objEquiv.symm.surjective x₁
    obtain ⟨f₂, rfl⟩ := objEquiv.symm.surjective x₂
    simp [mem_nonDegenerate_iff_mono, SimplexCategory.mono_iff_injective] at h₁ h₂
    simp at h₃ ⊢
    apply SimplexCategory.Hom.ext
    apply Fin.orderHom_ext_of_injective h₁ h₂ h₃
  · intro ⟨S, hS⟩
    dsimp at hS
    let e := monoEquivOfFin S (k := m + 1) (by simpa using hS)
    refine ⟨⟨objMk ((OrderHom.Subtype.val _).comp (e.toOrderEmbedding.toOrderHom)), ?_⟩, ?_⟩
    · rw [mem_nonDegenerate_iff_mono, SimplexCategory.mono_iff_injective]
      intro a b h
      apply e.injective
      ext : 1
      exact h
    · simp [e, Finset.image_comp, Finset.image_univ_of_surjective e.surjective]

noncomputable def nonDegenerateEquiv {m : ℕ} : (Δ[n] : SSet.{u}).nonDegenerate m ≃
    { S : Finset (Fin (n + 1)) | S.card = m + 1 } :=
  Equiv.ofBijective _ (bijective_image_objEquiv_toOrderHom_top n m)

@[simp]
lemma nonDegenerateEquiv_iff {m : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate m) (j : Fin (n + 1)):
    j ∈ (nonDegenerateEquiv x).1 ↔ ∃ (i : Fin (m + 1)), x.1 i = j := by
  dsimp [nonDegenerateEquiv]
  aesop

noncomputable def orderIsoOfNonDegenerate {m : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate m) :
    Fin (m + 1) ≃o (nonDegenerateEquiv x).1 where
  toEquiv := Equiv.ofBijective (fun i ↦ ⟨x.1 i, Finset.mem_image_of_mem _ (by simp)⟩) (by
    constructor
    · have := (mem_nonDegenerate_iff_mono x.1).1 x.2
      rw [SimplexCategory.mono_iff_injective] at this
      exact fun _ _ h ↦ this (by simpa using h)
    · rintro ⟨j, hj⟩
      rw [nonDegenerateEquiv_iff] at hj
      aesop)
  map_rel_iff' := by
    have := (mem_nonDegenerate_iff_mono x.1).1 x.2
    rw [SimplexCategory.mono_iff_injective] at this
    intro a b
    dsimp
    simp only [Subtype.mk_le_mk]
    constructor
    · rw [← not_lt, ← not_lt]
      intro h h'
      apply h
      obtain h'' | h'' := (monotone_apply x.1 h'.le).lt_or_eq
      · assumption
      · simp only [this h'', lt_self_iff_false] at h'
    · intro h
      exact monotone_apply _ h

lemma face_nonDegenerateEquiv {m : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate m) :
    face (nonDegenerateEquiv x).1 = Subcomplex.ofSimplex x.1 :=
  face_eq_ofSimplex.{u} _ _ (orderIsoOfNonDegenerate x)

lemma nonDegenerateEquiv_symm_apply_mem {m : ℕ}
    (S : { S : Finset (Fin (n + 1)) | S.card = m + 1 }) (i : Fin (m + 1)) :
      (nonDegenerateEquiv.{u}.symm S).1 i ∈ S.1 := by
  obtain ⟨f, rfl⟩ := nonDegenerateEquiv.{u}.surjective S
  dsimp [nonDegenerateEquiv]
  simp only [Equiv.ofBijective_symm_apply_apply, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩

lemma nonDegenerateEquiv_symm_mem_iff_face_le {m : ℕ}
    (S : { S : Finset (Fin (n + 1)) | S.card = m + 1 })
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    (nonDegenerateEquiv.symm S).1 ∈ A.obj _ ↔ face S ≤ A := by
  obtain ⟨x, rfl⟩ := nonDegenerateEquiv.{u}.surjective S
  rw [face_nonDegenerateEquiv x, Equiv.symm_apply_apply, Subcomplex.ofSimplex_le_iff]

lemma nonDegenerate_top_dim :
    (Δ[n] : SSet.{u}).nonDegenerate n = {yonedaEquiv (𝟙 _)} := by
  ext x
  obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
  simp only [Set.mem_singleton_iff, mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply]
  trans f = 𝟙 _
  · constructor
    · intro
      exact SimplexCategory.eq_id_of_mono f
    · rintro rfl
      infer_instance
  · exact (Equiv.apply_eq_iff_eq _).symm

variable (n) in
lemma id_nonDegenerate : yonedaEquiv.{u} (𝟙 _) ∈ Δ[n].nonDegenerate n := by
  simp [nonDegenerate_top_dim]

instance : (Δ[n] : SSet.{u}).HasDimensionLT (n + 1) where
  degenerate_eq_top i hi := by
    ext x
    obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [mem_degenerate_iff_not_mem_nonDegenerate, mem_nonDegenerate_iff_mono,
      Equiv.apply_symm_apply]
    intro hf
    have := SimplexCategory.le_of_mono (f := f) inferInstance
    omega

lemma face_hasDimensionLT (S : Finset (Fin (n + 1))) (k : ℕ)
    (hk : S.card ≤ k) :
    HasDimensionLT (face.{u} S) k := by
  generalize h : S.card = d
  obtain _ | d := d
  · obtain rfl : S = ∅ := by rwa [← Finset.card_eq_zero]
    simp only [face_emptySet]
    infer_instance
  · have pif := isoOfRepresentableBy (faceRepresentableBy.{u} S d (S.orderIsoOfFin h))
    rw [← hasDimensionLT_iff_of_iso pif]
    exact hasDimensionLT_of_le _ (d + 1) _ (by omega)

lemma face_singleton_eq_ofSimplex {n : ℕ} (i : Fin (n + 1)) :
    face.{u} {i} = Subcomplex.ofSimplex (stdSimplex.obj₀Equiv.symm i) :=
  face_nonDegenerateEquiv ⟨(stdSimplex.obj₀Equiv.symm i), by simp⟩

lemma face_singleton_ι_eq_const {n : ℕ} (i : Fin (n + 1)) :
    (face.{u} {i}).ι = SSet.const (stdSimplex.obj₀Equiv.symm i) := by
  ext ⟨d⟩ ⟨x, hx⟩ j
  induction' d using SimplexCategory.rec with d
  aesop

end stdSimplex

namespace Subcomplex

variable {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) [Mono (yonedaEquiv.symm x)]

noncomputable def ofSimplexRepresentableBy :
    (Subcomplex.ofSimplex x : SSet).RepresentableBy ⦋n⦌ :=
  have := (isIso_toOfSimplex_iff x).2 inferInstance
  let e := asIso (toOfSimplex x)
  { homEquiv {m} :=
      ((stdSimplex.objEquiv).symm.trans yonedaEquiv.symm).trans
        ((Iso.homCongr (α := Iso.refl (stdSimplex.obj m)) (β := e)).trans yonedaEquiv)
    homEquiv_comp {m m'} f g := by
      dsimp
      rw [Category.id_comp, Category.id_comp]
      rw [yonedaEquiv_symm_comp]
      erw [Equiv.apply_symm_apply]
      rw [yonedaEquiv_symm_comp]
      conv_rhs => erw [Equiv.apply_symm_apply]
      rw [← NatTrans.naturality_apply]
      rfl }

@[simp]
lemma ofSimplexRepresentableBy_id :
    (ofSimplexRepresentableBy x).homEquiv (𝟙 _) = x := by
  dsimp [ofSimplexRepresentableBy]
  rw [Category.id_comp, yonedaEquiv_symm_comp]
  erw [Equiv.apply_symm_apply]
  apply Functor.map_id_apply

@[simp]
lemma yonedaEquiv_isoOfRepresentableBy_ofSimplexRepresentableBy_hom :
    yonedaEquiv ((stdSimplex.isoOfRepresentableBy (ofSimplexRepresentableBy x)).hom ≫
      (ofSimplex x).ι) = x := by
  rw [yonedaEquiv_comp, stdSimplex.yonedaEquiv_isoOfRepresentableBy_hom,
    Subpresheaf.ι_app, ofSimplexRepresentableBy_id]

lemma isoOfRepresentableBy_ofSimplexRepresentableBy_hom :
    (stdSimplex.isoOfRepresentableBy (ofSimplexRepresentableBy x)).hom ≫
      (ofSimplex x).ι = yonedaEquiv.symm x :=
  yonedaEquiv.injective (by simp)

end Subcomplex

lemma mem_ofSimplex_obj_iff {X : SSet.{u}} {n m : ℕ} (x : X _⦋n⦌)
    (y : X _⦋m⦌) : y ∈ (Subcomplex.ofSimplex x).obj _ ↔
      ∃ (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n), X.map f.op x = y := by
  dsimp [Subcomplex.ofSimplex, Subpresheaf.ofSection]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.unop, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f.op, rfl⟩

lemma mem_ofSimplex_obj_iff' {X : SSet.{u}} {n m : ℕ} (x : X _⦋n⦌)
    (y : X _⦋m⦌) : y ∈ (Subcomplex.ofSimplex x).obj _ ↔
      ∃ (z : Δ[n] _⦋m⦌), y = (yonedaEquiv.symm x).app _ z := by
  dsimp [Subcomplex.ofSimplex, Subpresheaf.ofSection]
  constructor
  · rintro ⟨⟨f⟩, rfl⟩
    exact ⟨stdSimplex.objEquiv.symm f, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(stdSimplex.objEquiv x).op, rfl⟩

end SSet
