/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory._007F.Filtration
import LeanPool.Quasicategory._007F.Order

namespace SSet.σ

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ} (b : Fin (n + 1)) (i : Σₗ (b : Fin (n + 1)), Fin b.succ)

/-- the image of `Λ[n + 2, i.snd + 1]` under `s i`. -/
@[simp]
noncomputable
abbrev innerHornImage : (Δ[n + 1] ⊗ Δ[2]).Subcomplex :=
  Λ[n + 2, ⟨i.snd.succ, by omega⟩].image (s i)

lemma innerHornImage_eq_iSup : innerHornImage i =
    ⨆ (j : ({⟨i.snd.succ, by omega⟩}ᶜ : Set (Fin (n + 3)))), (face {j.1}ᶜ).image (s i) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup]

-- ofSimplex ((s i).app (Opposite.op ⦋n + 1⦌) (objEquiv.symm (δ j)))
open SimplexCategory in
lemma face_image_eq_range_comp (j : Fin (n + 3)) :
    (face {j}ᶜ).image (s i) = range (stdSimplex.δ j ≫ s i) := by
  rw [face_singleton_compl, ofSimplex_eq_range, ← range_comp]
  congr

-- ofSimplex ((s i).app (Opposite.op ⦋n + 1⦌) (objEquiv.symm (δ j)))
open SimplexCategory in
lemma face_image_eq_ofSimplex (j : Fin (n + 3)) :
    (face {j}ᶜ).image (s i) = ofSimplex (SSet.yonedaEquiv (stdSimplex.δ j ≫ s i)) := by
  rw [ofSimplex_eq_range, face_image_eq_range_comp]
  rfl

/-- each face of `σ b a` except the `a`-th and `a + 1`-th is
  contained in `∂Δ[n + 1] ⊗ Δ[2]`. -/
lemma face_ne_snd_succ_image_le_boundary_prod_top (a : Fin b.succ) (j : Fin (n + 3))
    (hj : ¬j = ⟨a, by omega⟩) (hj' : ¬j = ⟨a.succ, by omega⟩) :
    (face {j}ᶜ).image (s ⟨b, a⟩) ≤ ∂Δ[n + 1].prod ⊤ := by
  rw [face_image_eq_ofSimplex, ofSimplex_le_iff]
  refine ⟨?_, Set.mem_univ _⟩
  change ¬Function.Surjective (Fin.predAbove _ ∘ j.succAbove)
  intro h
  have : j < ⟨a, by omega⟩ ∨ ⟨a.succ, by omega⟩ < j := by
    cases Fin.lt_or_lt_of_ne hj'
    all_goals cases Fin.lt_or_lt_of_ne hj; try omega
    any_goals omega
    · next q q' =>
      exfalso
      apply not_lt.2 q' q
  cases this
  · next hj =>
    obtain ⟨i, hi⟩ := h ⟨j, lt_trans hj (by simp; omega)⟩
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj
    split at hi
    · next h' =>
      simp [show ¬a.1 < i.1 by omega, Fin.eq_mk_iff_val_eq] at hi
      omega
    · next h' =>
      split at hi
      all_goals simp [Fin.eq_mk_iff_val_eq] at hi
      · next h'' =>
        simp at h''
        omega
      · next h'' => omega
  · next hj =>
    obtain ⟨i, hi⟩ := h (j.pred (Fin.ne_zero_of_lt hj))
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj
    split at hi
    · next h' =>
      split at hi
      · next => aesop
      · next h'' =>
        simp at h''
        simp_all
        omega
    · next h'' =>
      simp [show a.1 < i + 1 by omega] at hi
      aesop

/-- the `0`-th face of `σ b 0` is contained in `Δ[n] ⊗ Λ[2, 1]`. -/
lemma face_zero_image_le_top_prod_horn :
    (face {0}ᶜ).image (s ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩) ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (simplex₂' ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩ ∘ Fin.succ) ∪ {1} ≠ Set.univ
  intro h
  rw [Set.eq_univ_iff_forall] at h
  have h := h 0
  simp at h
  obtain ⟨e, h⟩ := h
  have := h (Fin.succ_ne_zero e)
  split at this
  all_goals omega

/-- for `0 ≤ a < b ≤ n` the `(a + 1)`-th face of `σ b (a + 1)` is the `(a + 1)`-th face of
  `σ b a`. -/
lemma face_snd_succ_image_eq (a : Fin b) :
    (face {⟨a.succ, by omega⟩}ᶜ).image (s ⟨b, a.succ⟩) =
      (face {⟨a.succ, by omega⟩}ᶜ).image (s ⟨b, a.castSucc⟩) := by
  rw [face_image_eq_range_comp, face_image_eq_range_comp]
  apply congr_arg
  ext1
  all_goals
    apply_fun (fun f ↦ SSet.yonedaEquiv f)
    apply_fun (fun f ↦ stdSimplex.objEquiv f)
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
  · change Fin.predAbove _ ∘ Fin.succAboveOrderEmb _ = Fin.predAbove _ ∘ Fin.succAboveOrderEmb _
    ext k
    simp only [SimplexCategory.len_mk, Fin.val_succ, Sigma.Lex.Fin.fst_eq, Function.comp_apply,
      Fin.predAbove, Fin.castSucc_mk, Fin.succAboveOrderEmb_apply, Fin.succAbove,
      Fin.lt_iff_val_lt_val, Fin.coe_castSucc]
    split_ifs
    · next h =>
      dsimp at h
      omega
    · simp only [Fin.castPred_castSucc, Fin.coe_castSucc, show ¬a.1 < k by omega, ↓reduceDIte]
    · simp only [Fin.pred_succ, Fin.val_succ, show a.1 < k + 1 by omega, ↓reduceDIte]
    · next h =>
      dsimp at h
      omega
  · change simplex₂' _ ∘ Fin.succAboveOrderEmb _ = simplex₂' _ ∘ Fin.succAboveOrderEmb _
    ext k
    simp [Fin.succAbove, Fin.lt_iff_val_lt_val]
    split_ifs
    all_goals
      simp only [not_lt, Fin.le_iff_val_le_val, Fin.val_succ, add_le_add_iff_right, not_le,
        Fin.isValue, Fin.val_zero, Fin.val_one, zero_ne_one, Fin.coe_castSucc] at *
      try omega

/-- for `0 ≤ a < b ≤ n`, the `(a + 1)`-th face of `σ b (a + 1)` is contained in `σ b a`. -/
lemma face_snd_succ_image_le (a : Fin b) :
    (face {⟨a.succ, by omega⟩}ᶜ).image (s ⟨b, a.succ⟩) ≤ σ.subcomplex ⟨b, a.castSucc⟩ := by
  rw [face_snd_succ_image_eq, σ.subcomplex, ofSimplex_eq_range]
  exact image_le_range _ _

/-- for `0 ≤ a < b ≤ n`, the image of `Λ[n + 2, a + 2]` under `s b (a + 1)` is contained
  in `S(b, a)`. -/
lemma innerHornImage_intermediate_le_filtration (a : Fin b) :
    innerHornImage ⟨b, a.succ⟩ ≤ filtration ⟨b, a.castSucc⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a.succ, by omega⟩ -- check whether the face is the (a + 1)-th
  · subst h
    refine le_sup_of_le_right (le_iSup_of_le ⟨b, a.castSucc⟩ ?_)
    simp only [Fin.val_succ, le_refl, iSup_pos]
    exact face_snd_succ_image_le b a
  · exact le_sup_of_le_left
      (le_sup_of_le_right (face_ne_snd_succ_image_le_boundary_prod_top b a.succ j h hj))

/-- for `0 ≤ b < n`, the image of `Λ[n + 2, 1]` under `s b 0` is contained in `S(b, b)`. -/
lemma innerHornImage_join_le_filtration (b : Fin n) :
    innerHornImage ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩ ≤
      filtration ⟨b.castSucc, ⟨b, Nat.lt_add_one _⟩⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  by_cases h : j = 0
  · subst h
    exact le_sup_of_le_left
      ((face_zero_image_le_top_prod_horn b.succ).trans (top_prod_le_unionProd _ _))
  · exact le_sup_of_le_left
      ((face_ne_snd_succ_image_le_boundary_prod_top _ _ j h hj).trans (prod_top_le_unionProd _ _))

open Sigma.Lex in
lemma innerHornImage_succ_le_filtration :
    innerHornImage (succ i) ≤ filtration i := by
  obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
  · rw [Fin.succ_last_eq_last]
    apply le_sup_of_le_right (le_iSup_of_le ⟨Fin.last n, Fin.last n⟩ _)
    simp only [innerHornImage, Fin.val_succ, Fin.fst_eq, Fin.succ_last, Nat.succ_eq_add_one,
      Fin.val_last, le_refl, σ.subcomplex, ofSimplex_eq_range, iSup_pos]
    exact image_le_range _ _
  · rw [Fin.succ_eq₁]
    exact innerHornImage_intermediate_le_filtration b a
  · rw [Fin.succ_eq₂]
    exact innerHornImage_join_le_filtration b

lemma innerHornImage_bot_le_unionProd : innerHornImage ⊥ ≤ ∂Δ[n + 1].unionProd Λ[2, 1] := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  obtain rfl | ⟨j, rfl⟩ := (Fin.eq_zero_or_eq_succ j)
  · dsimp at hj
    exact le_sup_of_le_left
      (face_zero_image_le_top_prod_horn 0)
  · dsimp at hj
    exact le_sup_of_le_right
      (face_ne_snd_succ_image_le_boundary_prod_top _ _ j.succ (Fin.succ_ne_zero _) hj)

/-- for `0 ≤ a < b ≤ n`, the `a + 2`-th face of `σ b (a + 1)` is not contained in
  `Δ[n + 1] ⊗ Λ[2, 1]`. -/
lemma face_snd_succ_succ_image_not_le_top_prod_horn (a : Fin b) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (s ⟨b, a.succ⟩)
      ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  rw [mem_horn_iff]
  simp
  change insert 1 (Set.range (simplex₂' _ ∘ Fin.succAbove _)) = Set.univ
  ext i
  fin_cases i
  all_goals simp [Fin.succAbove]
  · use ⟨a.succ, by omega⟩
    simp [Fin.lt_iff_val_lt_val]
  · use b.succ
    simp [Fin.lt_iff_val_lt_val, show ¬b.1 < a.1 + 1 by omega]
    split
    · next h =>
      simp [Fin.le_iff_val_le_val] at h
      omega
    · simp [Fin.le_iff_val_le_val]

/-- for `0 ≤ b < n`, the first face of `s (b + 1) 0` is not contained in `Δ[n + 1] ⊗ Λ[2, 1]`. -/
lemma face_one_image_not_le_top_prod_horn (b : Fin n) :
    ¬ (face {1}ᶜ).image (s ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl, filtration, unionProd]
  refine Set.nmem_setOf_iff.2 ?_
  simp [mem_horn_iff]
  change insert 1 (Set.range ((simplex₂' ⟨b.succ, _⟩) ∘ Fin.succAbove _)) = Set.univ
  ext i
  fin_cases i
  all_goals simp [Fin.succAbove, objMk]
  · use 0
    aesop
  · use b.succ.succ
    simp [Fin.lt_iff_val_lt_val, Fin.ext_iff]

/-- for `0 ≤ a < b ≤ n`, the `a + 2`-th face of `σ b (a + 1)` is not contained in
  `∂Δ[n + 1] ⊗ Δ[2]`. -/
lemma face_snd_succ_succ_image_not_le_boundary_prod_top (a : Fin b) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (s ⟨b, a.succ⟩)
      ≤ ∂Δ[n + 1].prod ⊤ := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary]
  change Function.Surjective (Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
  intro i
  use i
  dsimp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp [Fin.lt_iff_val_lt_val]
  split
  all_goals
    simp
    omega

/-- for `0 ≤ b < n`, the first face of `σ (b + 1) 0` is not contained in
  `∂Δ[n + 1] ⊗ Δ[2]`. -/
lemma face_one_image_not_le_boundary_prod_top (b : Fin n) :
    ¬ (face {1}ᶜ).image (s ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ ∂Δ[n + 1].prod ⊤ := by
  simp [face_singleton_compl, filtration, unionProd]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary, s]
  change Function.Surjective (Fin.predAbove 0 ∘ (Fin.succ 0).succAboveOrderEmb)
  intro i
  use i
  simp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp_rw [Fin.lt_iff_val_lt_val]
  aesop

/-- for `0 ≤ a < b ≤ n`, the `a + 2`-th face of `σ b (a + 1)` is not contained in
  `σ j i` for any `0 ≤ i ≤ j < b`. -/
lemma face_snd_succ_succ_image_not_le_σ (a j : Fin b) (i : Fin j.succ) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (s ⟨b, a.succ⟩)
      ≤ σ.subcomplex ⟨⟨j, by omega⟩, ⟨i, by dsimp; omega⟩⟩ := by
  dsimp [σ.subcomplex]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [s, simplex, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ.subcomplex, objMk] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  simp  at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  cases lt_or_eq_of_le (show a.1 + 1 ≤ b.1 from a.2)
  all_goals
    replace h₁ := congr_fun h₁ b.castSucc
    replace h₂ := congr_fun h₂ b.castSucc
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
  · next h =>
    simp [show ¬b.1 < a.1 + 1 + 1 by omega, show ¬b.1 ≤ a.1 by omega] at h₁ h₂
    split at h₂
    · next h' =>
      simp [h'.not_lt, Fin.ext_iff] at h₁
      omega
    · next h' =>
      simp [h', Fin.ext_iff] at h₁
      split at h₂
      · next h'' =>
        simp_all [Fin.ext_iff]
        omega
      · next h'' =>
        omega
  · next h =>
    simp_rw [← h] at h₁ h₂
    simp [show a.1 + 1 < a.1 + 1 + 1 by omega, h.symm.le, show ¬a.1 + 1 < b by omega] at h₁ h₂
    split at h₁
    · next h' =>
      simp [Fin.ext_iff, h.not_lt] at h₁
      split at h₂
      · next h'' =>
        omega
      · omega
    · next h' =>
      simp [Fin.ext_iff] at h₁
      omega

/-- for `0 ≤ a < b ≤ n`, the `a + 2`-th face of `σ b (a + 1)` is not contained in
  `σ b i` for any `0 ≤ i ≤ a`. -/
lemma face_snd_succ_succ_image_not_le_σ' (a : Fin b) (i : Fin a.succ) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (s ⟨b, a.succ⟩)
      ≤ σ.subcomplex ⟨b, ⟨i, by simp; omega⟩⟩ := by
  dsimp [σ.subcomplex]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [s, simplex, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ.subcomplex, objMk] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  dsimp at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  replace h₁ := congr_fun h₁ ⟨a.succ, by omega⟩
  replace h₂ := congr_fun h₂ ⟨a.succ, by omega⟩
  simp [Fin.succAbove, Fin.predAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
  split at h₁
  · next h =>
    simp [Fin.ext_iff] at h₁
    split at h₂
    · next h =>
      omega
    · omega
  · next h =>
    simp [Fin.ext_iff] at h₁
    omega

open Sigma.Lex in
lemma face_snd_succ_succ_image_not_le_σ_le (j : Σₗ (b : Fin (n + 1)), Fin b.succ) (h : j ≤ i) (hn : i < ⊤) :
    ¬ (face {⟨(succ i).2.succ, by omega⟩}ᶜ).image (s (succ i)) ≤ σ.subcomplex j := by
  obtain ⟨b', a'⟩ := j
  obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := (Sigma.Lex.Fin.cases i)
  · exfalso
    rwa [top_eq_last, lt_self_iff_false] at hn
  · rw [Fin.succ_eq₁]
    cases h
    · next h =>
      exact face_snd_succ_succ_image_not_le_σ b a ⟨b', h⟩ ⟨a', by simp⟩
    · next h =>
      simp [Fin.le_iff_val_le_val] at h
      exact face_snd_succ_succ_image_not_le_σ' b' a ⟨a', by simp; omega⟩
  · rw [Fin.succ_eq₂]
    simp
    dsimp [σ.subcomplex]
    rw [ofSimplex_eq_range]
    simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
      Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
    intro x h'
    simp [s, simplex, nonDegenerateEquiv.toFun] at h'
    have h₁ := congr_arg Prod.fst h'
    have h₂ := congr_arg Prod.snd h'
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ.subcomplex, objMk] at h₁ h₂
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
    dsimp at h₁ h₂
    change _ ∘ x = _ at h₁ h₂
    replace h₁ := congr_fun h₁ ⟨b.succ, by omega⟩
    replace h₂ := congr_fun h₂ ⟨b.succ, by omega⟩
    simp [Fin.succAbove, Fin.predAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
    split at h₂
    · aesop
    · next h'' =>
      rw [not_le] at h''
      simp [h'', Fin.ext_iff] at h₁
      rw [h₁] at h₂
      split at h₂
      · simp [Fin.le_iff_val_le_val] at h
        cases h
        · next h =>
          simp [Fin.lt_iff_val_lt_val] at h
          omega
        · aesop
      · simp at h₂

open Sigma.Lex in
lemma face_snd_succ_succ_image_succ_not_le_filtration (hn : i < ⊤) :
    ¬ (face {⟨(succ i).snd.succ, by omega⟩}ᶜ).image (s (succ i))
      ≤ filtration i := by
  simp only [Fin.val_succ, face_singleton_compl, Subpresheaf.ofSection_image,
    filtration, unionProd, Fin.isValue, Subpresheaf.ofSection_le_iff, Subpresheaf.max_obj,
    prod_obj, Subpresheaf.top_obj, Set.top_eq_univ, Subpresheaf.iSup_obj, iSup_obj, Set.mem_union,
    Set.mem_iUnion, exists_prop, not_or, not_exists, not_and]
  constructor
  · obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
    · exfalso
      rwa [top_eq_last, lt_self_iff_false] at hn
    · rw [Fin.succ_eq₁]
      refine ⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩
      · have := face_snd_succ_succ_image_not_le_top_prod_horn b a
        simp [face_singleton_compl] at this
        exact this
      · have := face_snd_succ_succ_image_not_le_boundary_prod_top b a
        simp [face_singleton_compl] at this
        exact this
    · rw [Fin.succ_eq₂]
      refine ⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩
      · have := face_one_image_not_le_top_prod_horn b
        simp [face_singleton_compl] at this
        exact this
      · have := face_one_image_not_le_boundary_prod_top b
        simp [face_singleton_compl] at this
        exact this
  · intro j hj
    simpa only [face_singleton_compl, Subpresheaf.ofSection_image,
      Subpresheaf.ofSection_le_iff] using face_snd_succ_succ_image_not_le_σ_le i j hj hn

open Sigma.Lex in
/-- the first face of `s 0 0` is not contained in `∂Δ[n + 1].unionProd Λ[2, 1]`. -/
lemma face_one_image_not_le_unionProd :
    ¬ (face {1}ᶜ).image (s ⊥) ≤ ∂Δ[n + 1].unionProd Λ[2, 1] := by
  simp [face_singleton_compl, filtration, unionProd, bot_eq_zero]
  refine ⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩
  · simp [mem_horn_iff]
    change insert 1 (Set.range ((simplex₂' _) ∘ Fin.succAbove _)) = Set.univ
    ext i
    fin_cases i
    · simp
      use 0
      simp
    · simp
    · simp
      use 1
      rfl
  · simp [boundary]
    change Function.Surjective (Fin.predAbove 0 ∘ (Fin.succ 0).succAboveOrderEmb)
    intro i
    use i
    simp [Fin.predAbove, Fin.succAbove]
    simp_rw [Fin.lt_iff_val_lt_val]
    aesop

open Sigma.Lex in
lemma innerHornImage_succ_le_inf :
    innerHornImage (succ i) ≤
      σ.subcomplex (succ i) ⊓ filtration i := by
  apply le_inf
  · rw [σ.subcomplex, ofSimplex_eq_range]
    exact image_le_range _ _
  · exact innerHornImage_succ_le_filtration i

open Sigma.Lex in
lemma inf_le_innerHornImage_succ (hn : i < ⊤) :
    σ.subcomplex (succ i) ⊓ filtration i ≤
      innerHornImage (succ i) := by
  rw [σ.subcomplex, ofSimplex_eq_range, subcomplex_le_horn_image_iff _ _ inf_le_left, le_inf_iff, not_and]
  exact fun _ ↦ face_snd_succ_succ_image_succ_not_le_filtration i hn

open Sigma.Lex in
def filtrationPushout_intermediate (hn : i < ⊤) :
    Sq
      (innerHornImage (succ i))
      (σ.subcomplex (succ i))
      (filtration i)
      (filtration (succ i))
      where
  max_eq := by rw [filtration_succ, sup_comm]
  min_eq := le_antisymm (inf_le_innerHornImage_succ i hn) (innerHornImage_succ_le_inf i)

open Sigma.Lex in
def filtrationPushout_zero :
    Sq
      (innerHornImage ⊥)
      (σ.subcomplex ⊥)
      (∂Δ[n + 1].unionProd Λ[2, 1])
      (filtration ⊥) where
  max_eq := by simp [σ.subcomplex, filtration, sup_comm]
  min_eq := by
    rw [σ.subcomplex, ofSimplex_eq_range]
    apply le_antisymm
    · rw [subcomplex_le_horn_image_iff, le_inf_iff, not_and]
      · exact fun _ ↦ face_one_image_not_le_unionProd
      · exact inf_le_left
    · exact le_inf (image_le_range _ _) (innerHornImage_bot_le_unionProd)

end σ
