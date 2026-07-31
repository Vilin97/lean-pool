/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import LeanPool.Quasicategory.TopCatModelCategory.CommSq
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Boundary

universe u

open CategoryTheory Category Limits Simplicial Opposite

namespace SSet

variable {n : ℕ}

/-lemma horn_eq_iSup (i : Fin (n + 1)) :
    horn.{u} n i =
      ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ := by
  ext m j
  simp [stdSimplex.face, horn]
  change ¬ _ ↔ _
  simp [Set.eq_univ_iff_forall]
  rfl

lemma face_le_horn (i j : Fin (n + 1)) (h : i ≠ j) :
    stdSimplex.face.{u} {i}ᶜ ≤ horn n j := by
  rw [horn_eq_iSup]
  exact le_iSup (fun (k : ({j}ᶜ : Set (Fin (n + 1)))) ↦ stdSimplex.face.{u} {k.1}ᶜ) ⟨i, h⟩-/

lemma horn_le_boundary (i : Fin (n + 1)) :
    horn.{u} n i ≤ boundary n := by
  rw [horn_eq_iSup]
  simp
  intros
  apply face_le_boundary

instance (i : Fin (n + 1)) : HasDimensionLT (horn.{u} n i) n :=
  Subcomplex.hasDimensionLT_of_le
    (horn_le_boundary i) n

lemma horn_obj_eq_top (i : Fin (n + 1)) (m : ℕ) (h : m + 1 < n) :
    (horn.{u} n i).obj (op ⦋m⦌) = ⊤ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  obtain ⟨j, hij, hj⟩ : ∃ (j : Fin (n + 1)), j ≠ i ∧ j ∉ Set.range f.toOrderHom := by
    by_contra!
    have : Finset.image f.toOrderHom ⊤ ∪ {i} = ⊤ := by
      ext k
      simp
      by_cases k = i <;> aesop
    have := (congr_arg Finset.card this).symm.le.trans (Finset.card_union_le _ _)
    simp only [SimplexCategory.len_mk, Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, add_le_add_iff_right] at this
    have := this.trans Finset.card_image_le
    simp at this
    omega
  simp [horn_eq_iSup]
  exact ⟨j, hij, fun k hk ↦ hj ⟨k, hk⟩⟩

lemma stdSimplex.subcomplex_le_horn_iff
    (A : (Δ[n + 1] : SSet.{u}).Subcomplex) (i : Fin (n + 2)) :
    A ≤ horn (n + 1) i ↔ ¬ (face {i}ᶜ ≤ A) := by
  constructor
  · intro hA h
    replace h := h.trans hA
    rw [face_singleton_compl, Subcomplex.ofSimplex_le_iff,
      mem_horn_iff] at h
    apply h
    change Set.range (Fin.succAboveOrderEmb i).toOrderHom ∪ _ = _
    rw [Fin.range_succAboveOrderEmb]
    exact Set.compl_union_self {i}
  · intro h
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    by_cases hd : d < n
    · simp [horn_obj_eq_top i d (by omega)]
    · simp only [not_lt] at hd
      obtain ⟨⟨S, hS⟩, rfl⟩ := stdSimplex.nonDegenerateEquiv.symm.surjective x
      dsimp at hS
      simp only [stdSimplex.nonDegenerateEquiv_symm_mem_iff_face_le] at hx ⊢
      obtain hd | rfl := hd.lt_or_eq
      · obtain rfl : S = Finset.univ := by
          rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
          exact le_antisymm (S.card_le_univ.trans (by simp)) (by omega)
        exfalso
        exact h (le_trans (by simp [face_le_face_iff]) hx)
      · replace hS : Sᶜ.card = 1 := by
          have := S.card_compl_add_card
          rw [Fintype.card_fin] at this
          omega
        obtain ⟨j, rfl⟩ : ∃ j, S = {j}ᶜ := by
          obtain ⟨j, hj⟩ | h :=
            Finset.Nonempty.exists_eq_singleton_or_nontrivial (s := Sᶜ) (by
              rw [← Finset.card_pos]
              omega)
          · exact ⟨j, by simp [← hj]⟩
          · rw [← Finset.one_lt_card_iff_nontrivial] at h
            omega
        apply face_le_horn
        rintro rfl
        exact h hx

namespace horn

def faceι (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j ≠ i) :
    (stdSimplex.face {j}ᶜ : SSet.{u}) ⟶ (horn n i : SSet.{u}) :=
  Subcomplex.homOfLE (face_le_horn j i hij)

@[reassoc (attr := simp)]
lemma faceι_ι (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j ≠ i) :
    faceι i j hij ≫ (horn.{u} n i).ι = (stdSimplex.face {j}ᶜ).ι := by
  simp [faceι]

def ι (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    Δ[n] ⟶ horn.{u} (n + 1) i :=
  Subcomplex.lift ((stdSimplex.{u}.δ j))
    (le_antisymm (by simp) (by
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top]
      simp only [Subcomplex.range_eq_ofSimplex]
      refine le_trans ?_ (face_le_horn j i hij)
      rw [stdSimplex.face_singleton_compl]
      rfl))

@[reassoc (attr := simp)]
lemma ι_ι (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    ι i j hij ≫ (horn.{u} (n + 1) i).ι =
      stdSimplex.{u}.δ j := by simp [ι]

@[reassoc (attr := simp)]
lemma faceSingletonComplIso_inv_ι (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j ≠ i) :
    (stdSimplex.faceSingletonComplIso j).inv ≫ ι i j hij = faceι i j hij := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).hom, Iso.hom_inv_id_assoc]
  rfl

end horn

namespace horn₂₀

lemma sq : Subcomplex.Sq (stdSimplex.face {0}) (stdSimplex.face {0, 1})
    (stdSimplex.face {0, 2}) (horn 2 0) where
  max_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 0 (by simp)
      · exact face_le_horn (1 : Fin 3) 0 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  min_eq := by simp [stdSimplex.face_inter_face]

abbrev ι₀₁ : Δ[1] ⟶ horn.{u} 2 0 := horn.ι 0 2 (by simp)

abbrev ι₀₂ : Δ[1] ⟶ horn.{u} 2 0 := horn.ι 0 1 (by simp)

@[reassoc (attr := simp)]
lemma ι₀₁_ι : ι₀₁ ≫ (horn.{u} 2 0).ι = stdSimplex.δ 2 := rfl

@[reassoc (attr := simp)]
lemma ι₀₂_ι : ι₀₂ ≫ (horn.{u} 2 0).ι = stdSimplex.δ 1 := rfl

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (1 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₀₂ := by
  fapply sq.{u}.isPushout.of_iso'
    (stdSimplex.faceSingletonIso _ )
    (stdSimplex.facePairIso _ _ (by simp))
    (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals
    rw [← cancel_mono (Subpresheaf.ι _)]
    apply yonedaEquiv.injective
    ext i : 1
    fin_cases i <;> rfl

end horn₂₀

namespace horn₂₁

lemma sq : Subcomplex.Sq (stdSimplex.face {1}) (stdSimplex.face {0, 1})
    (stdSimplex.face {1, 2}) (horn 2 1) where
  max_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 1 (by simp)
      · exact face_le_horn (0 : Fin 3) 1 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  min_eq := by simp [stdSimplex.face_inter_face]

abbrev ι₀₁ : Δ[1] ⟶ horn.{u} 2 1 := horn.ι 1 2 (by simp)

abbrev ι₁₂ : Δ[1] ⟶ horn.{u} 2 1 := horn.ι 1 0 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso'
    (stdSimplex.faceSingletonIso _ )
    (stdSimplex.facePairIso _ _ (by simp))
    (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals
    rw [← cancel_mono (Subpresheaf.ι _)]
    apply yonedaEquiv.injective
    ext i : 1
    fin_cases i <;> rfl

end horn₂₁

namespace horn₂₂

lemma sq : Subcomplex.Sq (stdSimplex.face {2}) (stdSimplex.face {0, 2})
    (stdSimplex.face {1, 2}) (horn 2 2) where
  max_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (1 : Fin 3) 2 (by simp)
      · exact face_le_horn (0 : Fin 3) 2 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  min_eq := by simp [stdSimplex.face_inter_face]

abbrev ι₀₂ : Δ[1] ⟶ horn.{u} 2 2 := horn.ι 2 1 (by simp)

abbrev ι₁₂ : Δ[1] ⟶ horn.{u} 2 2 := horn.ι 2 0 (by simp)

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (0 : Fin 2)) ι₀₂ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso'
    (stdSimplex.faceSingletonIso _ )
    (stdSimplex.facePairIso _ _ (by simp))
    (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals
    rw [← cancel_mono (Subpresheaf.ι _)]
    apply yonedaEquiv.injective
    ext i : 1
    fin_cases i <;> rfl

end horn₂₂

namespace horn

section

variable (i : Fin (n + 1))

lemma multicoequalizerDiagram :
  CompleteLattice.MulticoequalizerDiagram (horn n i)
    (ι := ({i}ᶜ : Set (Fin (n +1)))) (fun j ↦ stdSimplex.face {j.1}ᶜ)
    (fun j k ↦ stdSimplex.face {j.1, k.1}ᶜ) where
  iSup_eq := by rw [horn_eq_iSup]
  min_eq j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

noncomputable def isColimit :
    IsColimit ((multicoequalizerDiagram i).multicofork.toLinearOrder.map Subcomplex.toPresheafFunctor) :=
  Subcomplex.multicoforkIsColimit' (multicoequalizerDiagram i)

def exists_desc' {X : SSet.{u}}
    (f : ∀ (j : ({i}ᶜ : Set _)), (stdSimplex.face {j.1}ᶜ : SSet) ⟶ X)
    (hf : ∀ (j k : ({i}ᶜ : Set _)) (_ : j.1 < k.1),
      Subcomplex.homOfLE (show stdSimplex.face {j.1, k.1}ᶜ ≤ _ by
        simp [stdSimplex.face_le_face_iff]) ≫ f j =
      Subcomplex.homOfLE (show stdSimplex.face {j.1, k.1}ᶜ ≤ _ by
        simp [stdSimplex.face_le_face_iff]) ≫ f k) :
    ∃ (φ : (Λ[n, i] : SSet) ⟶ X),
      ∀ j, faceι i j.1 (by simpa only [Finset.mem_compl, Finset.mem_singleton] using j.2) ≫
        φ = f j :=
  ⟨(isColimit i).desc (Multicofork.ofπ _ _ f (fun s ↦ hf _ _ s.2)),
    fun j ↦ (isColimit i).fac _ (.right j)⟩

end

open stdSimplex in
lemma exists_desc {i : Fin (n + 3)} {X : SSet.{u}} (f : ({i}ᶜ : Set _) → ((Δ[n + 1] : SSet) ⟶ X))
    (hf : ∀ (j k : ({i}ᶜ : Set _)) (hjk : j.1 < k.1),
      stdSimplex.δ (k.1.pred (Fin.ne_zero_of_lt hjk)) ≫ f j =
        stdSimplex.δ (j.1.castPred (Fin.ne_last_of_lt hjk)) ≫ f k) :
    ∃ (φ : (Λ[n + 2, i] : SSet) ⟶ X), ∀ j, ι i j.1 j.2 ≫ φ = f j := by
  obtain ⟨φ, hφ⟩ := exists_desc' (i := i)
    (f := fun j ↦
      (faceSingletonComplIso j.1).inv ≫ f j) (fun j k hjk ↦ by
        dsimp
        rw [homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_pred_assoc _ _ hjk,
          homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_castPred_assoc _ _ hjk,
          hf _ _ hjk])
  exact ⟨φ, fun j ↦ by
    rw [← cancel_epi (faceSingletonComplIso j.1).inv, ← hφ,
      faceSingletonComplIso_inv_ι_assoc]⟩

end horn

namespace horn₃₁

abbrev ι₀ : Δ[2] ⟶ horn.{u} 3 1 := horn.ι 1 0 (by simp)
abbrev ι₂ : Δ[2] ⟶ horn.{u} 3 1 := horn.ι 1 2 (by simp)
abbrev ι₃ : Δ[2] ⟶ horn.{u} 3 1 := horn.ι 1 3 (by simp)

variable {X : SSet.{u}} (f₀ f₂ f₃ : Δ[2] ⟶ X)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂)
  (h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃)

namespace desc

@[simps!]
def multicofork :
    Multicofork ((horn.multicoequalizerDiagram (1 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toPresheafFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => by simp at hi
    | 2 => (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (by
      dsimp
      intro x
      fin_cases x
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 3 (by simp)).hom,
          ← assoc]
        convert h₁₃
        all_goals apply yonedaEquiv.injective; ext i; fin_cases i <;> rfl
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← assoc]
        convert h₁₂
        all_goals apply yonedaEquiv.injective; ext i; fin_cases i <;> rfl
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 0 1 (by simp)).hom,
          ← assoc]
        convert h₂₃
        all_goals apply yonedaEquiv.injective; ext i; fin_cases i <;> rfl)

end desc

noncomputable def desc : (horn 3 1 : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 1).desc (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)

@[reassoc (attr := simp)]
lemma ι₀_desc : ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 0).inv, ← assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₂_desc : ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 2).inv, ← assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨2, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₃_desc : ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 3).inv, ← assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨3, by simp⟩)

include h₁₂ h₁₃ h₂₃ in
lemma exists_desc : ∃ (φ : (horn 3 1 : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₂ ≫ φ = f₂ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃, by simp⟩

end horn₃₁

namespace horn₃₂

abbrev ι₀ : Δ[2] ⟶ horn.{u} 3 2 := horn.ι 2 0 (by simp)
abbrev ι₁ : Δ[2] ⟶ horn.{u} 3 2 := horn.ι 2 1 (by simp)
abbrev ι₃ : Δ[2] ⟶ horn.{u} 3 2 := horn.ι 2 3 (by simp)

variable {X : SSet.{u}} (f₀ f₁ f₃ : Δ[2] ⟶ X)
  (h₀₂ : stdSimplex.δ 2 ≫ f₁ = stdSimplex.δ 1 ≫ f₃)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₂₃ : stdSimplex.δ 0 ≫ f₀ = stdSimplex.δ 0 ≫ f₁)

namespace desc

@[simps!]
def multicofork :
    Multicofork ((horn.multicoequalizerDiagram (2 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toPresheafFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ ↦ match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁
    | 2 => by simp at hi
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (by
      dsimp
      intro x
      fin_cases x
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 2 3 (by simp)).hom,
          ← assoc]
        convert h₂₃
        all_goals apply yonedaEquiv.injective; ext i; fin_cases i <;> rfl
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← assoc]
        convert h₁₂
        all_goals apply yonedaEquiv.injective; ext i; fin_cases i <;> rfl
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 0 2 (by simp)).hom,
          ← assoc]
        convert h₀₂
        all_goals apply yonedaEquiv.injective; ext i; fin_cases i <;> rfl)

end desc

noncomputable def desc : (horn 3 2 : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 2).desc (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)

@[reassoc (attr := simp)]
lemma ι₀_desc : ι₀ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 0).inv, ← assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₁_desc : ι₁ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₁ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 1).inv, ← assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨1, by simp⟩)

@[reassoc (attr := simp)]
lemma ι₃_desc : ι₃ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso 3).inv, ← assoc,
    horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨3, by simp⟩)

include h₀₂ h₁₂ h₂₃ in
lemma exists_desc : ∃ (φ : (horn 3 2 : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₁ ≫ φ = f₁ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃, by simp⟩

end horn₃₂

namespace horn₁

variable (i : Fin 2)

lemma eq_face : horn.{u} 1 i = stdSimplex.face {i} := by
  rw [horn_eq_iSup]
  fin_cases i
  · letI : Unique ({0}ᶜ : Set (Fin 2)) :=
      { default := ⟨1, by simp⟩
        uniq := by rintro ⟨a, _⟩; fin_cases a <;> aesop }
    dsimp
    rw [iSup_unique]
    rfl
  · letI : Unique ({1}ᶜ : Set (Fin 2)) :=
      { default := ⟨0, by simp⟩
        uniq := by rintro ⟨a, _⟩; fin_cases a <;> aesop }
    dsimp
    rw [iSup_unique]
    rfl

lemma ι_eq : (horn.{u} 1 i).ι = const.{u} (stdSimplex.obj₀Equiv.{u}.symm i) := by
  rw [← Subcomplex.isoOfEq_hom_ι (eq_face i), stdSimplex.face_singleton_ι_eq_const, comp_const]

noncomputable def iso : Δ[0] ≅ (horn 1 i : SSet.{u}) :=
  stdSimplex.faceSingletonIso _ ≪≫ Subcomplex.isoOfEq (eq_face i).symm

@[reassoc (attr := simp)]
lemma iso₁_hom_ι : (iso.{u} 1).hom ≫ Λ[1, 1].ι = stdSimplex.δ 0 := by
  rw [ι_eq, comp_const]
  apply yonedaEquiv.injective
  ext j
  fin_cases j
  rfl

@[reassoc (attr := simp)]
lemma iso₀_hom_ι : (iso.{u} 0).hom ≫ Λ[1, 0].ι = stdSimplex.δ 1 := by
  rw [ι_eq, comp_const]
  apply yonedaEquiv.injective
  ext j
  fin_cases j
  rfl

lemma eq_ofSimplex : Λ[1, i] = Subcomplex.ofSimplex.{u} (stdSimplex.obj₀Equiv.symm i) := by
  rw [eq_face, stdSimplex.face_singleton_eq_ofSimplex]

lemma eq_objMk_const {d : ℕ} (x : Δ[1] _⦋d⦌) (hx : x ∈ Λ[1, i].obj _) :
    x = stdSimplex.objMk (n := .mk 1) (OrderHom.const _ i) := by
  rw [eq_ofSimplex] at hx
  obtain ⟨⟨f⟩, rfl⟩ := hx
  obtain rfl : f = SimplexCategory.const _ _ 0 := Subsingleton.elim _ _
  rfl

end horn₁

end SSet
