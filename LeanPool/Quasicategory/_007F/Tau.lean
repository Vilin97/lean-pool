/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import LeanPool.Quasicategory._007F.Filtration
import LeanPool.Quasicategory._007F.Order

namespace SSet.τ

open CategoryTheory Simplicial MorphismProperty MonoidalCategory SSet

open Subcomplex stdSimplex

variable {n : ℕ}

variable (b : Fin (n + 2)) (i : Σₗ (b : Fin (n + 2)), Fin b.succ)

/-- the image of `Λ[n + 3, i.snd + 1]` under `t i`. -/
@[simp]
noncomputable
abbrev innerHornImage : (Δ[n + 1] ⊗ Δ[2]).Subcomplex :=
  Λ[n + 3, ⟨i.snd.succ, by omega⟩].image (t i)

open SimplexCategory in
lemma face_image_eq_range_comp (j : Fin (n + 4)) :
    (face {j}ᶜ).image (t i) = range (stdSimplex.δ j ≫ t i) := by
  rw [face_singleton_compl, ofSimplex_eq_range, ← range_comp]
  congr

lemma innerHornImage_eq_iSup : innerHornImage i =
    ⨆ (j : ({⟨i.snd.succ, by omega⟩}ᶜ : Set (Fin (n + 4)))), (face {j.1}ᶜ).image (t i) := by
  simp only [innerHornImage, horn_eq_iSup, image_iSup]

/-- for `0 ≤ a ≤ b ≤ n + 1`, each face of `τ b a` except the `a`-th, `a + 1`-th, `b + 1`-th, and
  `b + 2`-th is contained in `∂Δ[n + 1] ⊗ Δ[2]`. -/
lemma face_ne_fst_snd_succ_image_le_boundary_prod_top (a : Fin b.succ) (j : Fin (n + 4))
    (ha : ¬j = ⟨a, by omega⟩) (ha' : ¬j = ⟨a + 1, by omega⟩)
    (hb : ¬j = b.succ.castSucc) (hb' : ¬j = b.succ.succ) :
      (face {j}ᶜ).image (t ⟨b, a⟩) ≤ ∂Δ[n + 1].prod ⊤ := by
  simp [face_singleton_compl]
  refine ⟨?_, Set.mem_univ _⟩
  change ¬ Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAbove _)
  intro h
  have : j < ⟨a, by omega⟩ ∨ ⟨a + 1, by omega⟩ < j := by
    cases Fin.lt_or_lt_of_ne ha
    all_goals cases Fin.lt_or_lt_of_ne ha'; try omega
    any_goals omega
    · next q q' =>
      exfalso
      exact not_le.2 q' q
  cases this
  · next hj =>
    obtain ⟨i, hi⟩ := h ⟨j, by simp [Fin.lt_iff_val_lt_val] at hj ⊢; omega⟩
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj
    split at hi
    · next h' =>
      simp [show ¬a.1 < i.1 by omega, show ¬b.1 < i by omega, Fin.eq_mk_iff_val_eq] at hi
      omega
    · next h' =>
      split at hi
      all_goals
        simp [Fin.eq_mk_iff_val_eq] at hi
        · next h'' =>
          split at hi
          all_goals
            simp at hi h''
            omega
  · next hj =>
    have : j < b.succ.castSucc ∨ b.succ.succ < j := by
      cases Fin.lt_or_lt_of_ne hb'
      all_goals cases Fin.lt_or_lt_of_ne hb; try omega
      any_goals omega
      · next q q' =>
        exfalso
        exact not_lt.2 q' q
    cases this
    . next hj' =>
      simp [Fin.lt_iff_val_lt_val] at hj hj'
      obtain ⟨i, hi⟩ := h ⟨j - 1, by dsimp; omega⟩
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj hj'
      split at hi
      · next h' =>
        split at hi
        · next =>
          simp [show ¬b.1 < i - 1 by omega, Fin.eq_mk_iff_val_eq] at hi
          omega
        · next h'' =>
          simp [show ¬b.1 < i by omega, Fin.eq_mk_iff_val_eq] at hi
          simp_all
          omega
      · next h'' =>
        simp [show a.1 < i + 1 by omega] at hi
        split at hi
        all_goals
          simp [Fin.eq_mk_iff_val_eq] at hi
          omega
    · next hj' =>
      simp [Fin.lt_iff_val_lt_val] at hj hj'
      obtain ⟨i, hi⟩ := h ⟨j - 2, by dsimp; omega⟩
      simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val] at hi hj hj'
      split at hi
      · next h' =>
        split at hi
        · next h'' =>
          split at hi
          all_goals
            simp [Fin.eq_mk_iff_val_eq] at hi
            simp_all
            omega
        · next h'' =>
          split at hi
          all_goals
            simp [Fin.eq_mk_iff_val_eq] at hi
            simp_all
          simp_all
          omega
          omega
      · next h'' =>
        simp [show a.1 < i + 1 by omega] at hi
        split at hi
        all_goals
          simp [Fin.eq_mk_iff_val_eq] at hi
          omega

/-- for `0 ≤ b ≤ n`, the `0`-th face of `τ b 0` is contained in `Δ[n + 1] ⊗ Λ[2, 1]`. -/
lemma face_zero_image_le_top_prod_horn :
    (face {0}ᶜ).image (t ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩) ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (simplex₂' ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩ ∘ Fin.succ) ∪ {1} ≠ Set.univ
  rw [ne_eq, Set.union_singleton, Set.eq_univ_iff_forall, not_forall]
  use 0
  simp
  intro ⟨e, he⟩
  aesop

/-- for `0 ≤ a ≤ n` the `n + 2`-th face of `τ n a` is contained in `Δ[n + 1] ⊗ Λ[2, 1]`. -/
lemma face_last_image_le_top_prod_horn (a : Fin (n + 1)) :
    (face {Fin.last (n + 2)}ᶜ).image (t ⟨Fin.last n, a⟩) ≤ prod ⊤ Λ[2, 1] := by
  simp [face_singleton_compl, SimplexCategory.δ, Fin.succAboveOrderEmb]
  refine ⟨Set.mem_univ _, ?_⟩
  change Set.range (simplex₂' _ ∘ Fin.castSucc) ∪ {1} ≠ Set.univ
  rw [ne_eq, Set.eq_univ_iff_forall, not_forall]
  use 2
  simp
  intro e he
  split at he
  · omega
  · simp [Fin.lt_iff_val_lt_val] at he
    omega

/-- for `0 ≤ a ≤ b ≤ n` the `b + 2`-th face of `τ b a` is `σ b a`. -/
lemma face_fst_succ_succ_image_eq (b : Fin (n + 1)) (a : Fin b.succ) :
    (face {⟨b + 2, by omega⟩}ᶜ).image (t ⟨b.castSucc, a⟩) = σ.subcomplex ⟨b, a⟩ := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk, t,
      simplex, nonDegenerateEquiv.toFun, σ.simplex, nonDegenerateEquiv,
      σ.nonDegenerateEquiv.toFun, Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split
    · next h' =>
      simp
      split
      · next h'' => simp [show ¬b.1 < e - 1 by omega, h'']
      · next h'' => simp [h'', ((not_lt.1 h'').trans a.is_le).not_lt]
    · next h' =>
      have := a.is_le
      simp [show a.1 < e + 1 by omega, show b.1 < e by omega, show a.1 < e by omega]
  · simp
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · rfl
    · have := a.is_le
      simp [show ¬e.1 + 1 ≤ a by omega, show ¬e.1 ≤ b by omega, show ¬e.1 ≤ a by omega,
        show ¬e.1 ≤ b + 1 by omega]

/-- for `0 ≤ a ≤ b ≤ n` the `b + 2`-th face of `τ (b + 1) a` is `σ b a`. -/
lemma face_fst_succ_succ_image_succ_eq (b : Fin (n + 1)) (a : Fin b.succ) :
    (face {⟨b + 2, by omega⟩}ᶜ).image (t ⟨b.succ, a.castSucc⟩) = σ.subcomplex ⟨b, a⟩ := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk, t,
      simplex, nonDegenerateEquiv.toFun, nonDegenerateEquiv, τ.simplex, σ.simplex,
      σ.nonDegenerateEquiv.toFun, Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
  · ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split
    · next h =>
      simp
      split
      · simp [show ¬b.1 + 1 < e - 1 by omega]
      · simp [show ¬b.1 + 1 < e by omega]
    · next h =>
      simp [show a.1 < e + 1 by dsimp; omega, show a.1 < e by dsimp; omega]
      split
      · simp
      · omega
  · ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split
    · next h =>
      simp [h.le, show e.1 ≤ b + 1 by omega]
    · next h =>
      rw [not_lt] at h
      simp [show ¬e.1 + 1 ≤ a by dsimp; omega, show ¬e.1 ≤ a by dsimp; omega]

/-- for `0 ≤ a < b ≤ n` the `a + 1`-th face of `τ b (a + 1)` is the `a + 1`-th face of
  `τ b a`. -/
lemma face_snd_succ_image_eq (a : Fin b) :
    (face {⟨a + 1, by omega⟩}ᶜ).image (t ⟨b, a.succ⟩) =
      (face {⟨a + 1, by omega⟩}ᶜ).image (t ⟨b, a.castSucc⟩) := by
  simp [face_singleton_compl]
  congr
  apply Prod.ext
  all_goals
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk, t,
      simplex, nonDegenerateEquiv.toFun, nonDegenerateEquiv, σ.simplex,
      σ.nonDegenerateEquiv.toFun, Equiv.ulift]
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff]
    ext e
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
  · split
    · next h => simp [h.le.not_lt, show (¬ a.1 < e) by omega]
    · next => simp [show (a.1 < e) by omega, show (a.1 < e + 1) by omega]
  · split
    · next h => simp [h.le, show e.1 ≤ a by omega]
    · next =>
      simp [show ¬e.1 ≤ a by omega]
      split
      all_goals simp [show ¬e.1 + 1 ≤ a by omega]

/-- for `0 ≤ a < b ≤ n + 1`, the image of `Λ[n + 3, a + 2]` under `t b (a + 1)` is contained
  in `T(b, a)`. -/
lemma innerHornImage_intermediate_le_filtration (b : Fin (n + 2)) (a : Fin b) :
    innerHornImage ⟨b, a.succ⟩ ≤ filtration ⟨b, a.castSucc⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  rintro ⟨j, hj⟩
  by_cases h : j = ⟨a + 1, by omega⟩
  · subst h
    apply le_sup_of_le_right (le_iSup_of_le ⟨b, a.castSucc⟩ _)
    simp only [Fin.val_succ, face_snd_succ_image_eq, le_refl, ofSimplex_eq_range, iSup_pos, τ.subcomplex]
    exact image_le_range _ _
  · by_cases h' : j = b.succ.castSucc
    · subst h'
      have : b ≠ 0 := by
        by_contra h'
        rw [h'] at a
        exact Nat.not_lt_zero _ a.2
      obtain ⟨b, rfl⟩ := Fin.eq_succ_of_ne_zero this
      have : a.1 < b := by
        apply Nat.lt_of_le_of_ne a.is_le
        simp only [Fin.val_succ, Sigma.Lex.Fin.fst_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
          Fin.ext_iff, Fin.coe_castSucc, add_left_inj] at hj
        omega
      apply le_sup_of_le_left (le_sup_of_le_right _)
      have := face_fst_succ_succ_image_succ_eq b ⟨a.succ, by dsimp; omega⟩
      simp [Fin.succ] at this ⊢
      rw [this]
      exact le_iSup_of_le ⟨b, ⟨a.succ, by dsimp; omega⟩⟩ le_rfl
    by_cases h'' : j = b.succ.succ
    · subst h''
      obtain rfl | ⟨b , rfl⟩ := Fin.eq_last_or_eq_castSucc b
      · exact
        le_sup_of_le_left
          (le_sup_of_le_left (le_sup_of_le_left (face_last_image_le_top_prod_horn a.succ)))
      · have := face_fst_succ_succ_image_eq b a.succ
        simp [Fin.succ] at this ⊢
        rw [this]
        apply le_sup_of_le_left (le_sup_of_le_right _)
        simp only [σ.subcomplex, Fin.val_succ, Fin.coe_castSucc, le_top, iSup_pos, ofSimplex_eq_range]
        exact le_iSup_of_le ⟨b, a.succ⟩ le_rfl
    exact
      le_sup_of_le_left
        (le_sup_of_le_left
          (le_sup_of_le_right
            (face_ne_fst_snd_succ_image_le_boundary_prod_top b a.succ j h hj h' h'')))

/-- for `0 ≤ b ≤ n`, the image of `Λ[n + 3, 1]` under `t (b + 1) 0` is contained in `T(b, b)`. -/
lemma innerHornImage_join_le_filtration (b : Fin (n + 1)) :
    innerHornImage ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩ ≤
      filtration ⟨b.castSucc, ⟨b, Nat.lt_add_one _⟩⟩ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  apply le_sup_of_le_left
  by_cases h : j = 0 -- case for the `0`-th face
  · subst h
    exact (le_sup_of_le_left (le_sup_of_le_left (face_zero_image_le_top_prod_horn b.succ)))
  · by_cases h' : j = b.succ.succ.castSucc -- case for the `(b + 1)`-th face
    subst h'
    apply le_sup_of_le_right (le_iSup_of_le ⟨b, ⟨0, Nat.zero_lt_succ _⟩⟩ _)
    have := face_fst_succ_succ_image_succ_eq b ⟨0, Nat.zero_lt_succ _⟩
    simp [Fin.succ] at this ⊢
    rw [this]
    by_cases h'' : j = b.succ.succ.succ
    · subst h''
      obtain rfl | ⟨b , rfl⟩ := Fin.eq_last_or_eq_castSucc b
      · exact (le_sup_of_le_left (le_sup_of_le_left (face_last_image_le_top_prod_horn 0)))
      · apply (le_sup_of_le_right _)
        apply le_iSup₂_of_le ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩ le_top
        exact (face_fst_succ_succ_image_eq b.succ ⟨0, Nat.zero_lt_succ _⟩).le
    exact
      le_sup_of_le_left
        (le_sup_of_le_right
          (face_ne_fst_snd_succ_image_le_boundary_prod_top b.succ ⟨0, Nat.zero_lt_succ _⟩ j h hj h' h''))

open Sigma.Lex in
lemma innerHornImage_succ_le_filtration :
    innerHornImage (succ i) ≤ filtration i := by
  obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
  · rw [Fin.succ_last_eq_last]
    apply le_sup_of_le_right (le_iSup_of_le ⟨Fin.last _, Fin.last _⟩ _)
    simp [ofSimplex_eq_range, image_le_range, τ.subcomplex]
  · rw [Fin.succ_eq₁]
    exact innerHornImage_intermediate_le_filtration b a
  · rw [Fin.succ_eq₂]
    exact innerHornImage_join_le_filtration b

lemma innerHornImage_bot_le_filtration : innerHornImage (⊥ : Σₗ (b : Fin (n + 2)), Fin ↑b.succ) ≤ σ.filtration ⊤ := by
  rw [innerHornImage_eq_iSup]
  apply iSup_le
  intro ⟨j, hj⟩
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · exact le_sup_of_le_left (le_sup_of_le_left (face_zero_image_le_top_prod_horn 0))
  · by_cases h : j = 1
    · subst h
      have := face_fst_succ_succ_image_eq (n := n) ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩
      change (face {2}ᶜ).image (t ⊥) = _ at this
      dsimp
      rw [this]
      apply le_sup_of_le_right
      apply le_iSup_of_le ⟨0, ⟨0, Nat.zero_lt_succ _⟩⟩
      simp
    · exact le_sup_of_le_left (le_sup_of_le_right
        (face_ne_fst_snd_succ_image_le_boundary_prod_top _ _ j.succ (ne_of_beq_false rfl) hj hj (by simpa [Fin.succ, Fin.ext_iff] using h)))

/-- for `0 ≤ a < b ≤ n + 1`, the `a + 2`-th face of `τ b (a + 1)` is not contained in
  `Δ[n + 1] ⊗ Λ[2, 1]`. -/
lemma face_snd_succ_succ_image_not_le_top_prod_horn (a : Fin b) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (t ⟨b, a.succ⟩)
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
    simp [Fin.lt_iff_val_lt_val, show ¬b.1 < a.1 + 1 by omega, Fin.le_iff_val_le_val]
    omega

lemma face_one_image_not_le_top_prod_horn (b : Fin (n + 1)) :
    ¬ (face {1}ᶜ).image (t ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
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
    simp [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    exact Fin.succ_ne_zero _

/-- for `0 ≤ a < b ≤ n + 1`, the `a + 2`-th face of `τ b (a + 1)` is not contained in
  `∂Δ[n + 1] ⊗ Δ[2]`. -/
lemma face_snd_succ_succ_image_not_le_boundary_prod_top (a : Fin b) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (t ⟨b, a.succ⟩)
      ≤ ∂Δ[n + 1].prod ⊤ := by
  simp [face_singleton_compl]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary]
  change Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
  intro i
  dsimp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp [Fin.lt_iff_val_lt_val]
  by_cases h : b.1 < i
  · use i.succ
    rw [Fin.eq_mk_iff_val_eq]
    simp [show ¬i.1 < a + 1 by omega, show a.1 < i + 1 by omega, show b.1 < i + 1 by omega]
  · use i.castSucc
    simp
    split
    · simp [show ¬ a.1 + 1 < i by omega]
      omega
    · simp [show a.1 < i by omega]
      omega

/-- for `0 ≤ b ≤ n`, the first face of `τ (b + 1) 0` is not contained in `∂Δ[n + 1].prod ⊤`. -/
lemma face_one_image_not_le_boundary_prod_top (b : Fin (n + 1)) :
    ¬ (face {1}ᶜ).image (t ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ ∂Δ[n + 1].prod ⊤ := by
  simp [face_singleton_compl, filtration, unionProd]
  refine Set.nmem_setOf_iff.2 ?_
  simp [boundary]
  change Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
  intro i
  dsimp
  simp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove]
  simp_rw [Fin.lt_iff_val_lt_val]
  by_cases h : b.succ.1 < i
  · use i.succ
    simp
    intro h'
    exfalso
    exact h'.not_lt (Nat.lt_of_succ_lt h)
  · use i.castSucc
    split
    next h_1 =>
      simp at h_1
      subst h_1
      simp [Fin.ext_iff]
    next h_1 =>
      simp
      intro h'
      exfalso
      exact h h'

/-- for `0 ≤ a < b ≤ n + 1`, the `a + 2`-th face of `τ b (a + 1)` is not contained in
  `σ j i` for any `0 ≤ i ≤ j ≤ n`. -/
lemma face_snd_succ_succ_image_not_le_σ (a : Fin b) (j : Fin (n + 1)) (i : Fin j.succ) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (t ⟨b, a.succ⟩)
      ≤ σ.subcomplex ⟨j, i⟩ := by
  dsimp [τ.subcomplex, σ.subcomplex]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [t, simplex, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, objMk,
    σ.nonDegenerateEquiv.toFun, τ.nonDegenerateEquiv,
    τ.nonDegenerateEquiv.toFun, τ.simplex, σ.simplex] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  dsimp at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  obtain hj | (hj : b ≤ j.castSucc) := Fin.lt_or_le j.castSucc b
  · replace h₁' := congr_fun h₁ b.castSucc
    replace h₂' := congr_fun h₂ b.castSucc
    simp only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at hj
    have : a.1 + 1 ≤ b := a.2
    obtain ha | ha := Nat.lt_or_eq_of_le this
    · simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val,
        show ¬ b.1 < ↑a + 1 + 1 by omega,
        show a.1 < b + 1 by omega, show ¬ b.1 ≤ a by omega] at h₁' h₂'
      simp [Fin.ext_iff] at h₁' h₂'
      split at h₁'
      · next h =>
        simp [h.not_le] at h₂'
        simp at h₁'
        simp [show ¬ (x b.castSucc).1 ≤ j.1 + 1 by omega] at h₂'
      · aesop
    · simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
      simp_rw [← ha] at h₁' h₂'
      simp [Fin.ext_iff] at h₁' h₂'
      simp_rw [← ha] at h₁' h₂'
      simp at h₁' h₂'
      split at h₁'
      · aesop
      · next h =>
        simp [show ¬ a.1 + 1 < b by omega] at h₁'
        omega
  · replace h₁' := congr_fun h₁ b.succ
    replace h₂' := congr_fun h₂ b.succ
    simp [Fin.predAbove, Fin.succAbove, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
    simp [show ¬ b.1 < a + 1 by omega, show ¬ b.1 + 1 ≤ a by omega, show a.1 < b + 1 by omega] at h₁' h₂'
    split at h₁'
    · next h =>
      simp [h.not_le] at h₂'
      simp [Fin.ext_iff] at h₁'
      simp [Fin.le_iff_val_le_val] at hj
      omega
    · aesop

/-- for `0 ≤ b ≤ n`, the first face of `τ (b + 1) 0` is not contained in
  `σ j i` for any `0 ≤ i ≤ j ≤ n`. -/
lemma face_one_image_not_le_σ (b : Fin (n + 1)) (j : Fin (n + 1)) (i : Fin j.succ) :
    ¬ (face {1}ᶜ).image (t ⟨b.succ, ⟨0, Nat.zero_lt_succ _⟩⟩)
      ≤ σ.subcomplex ⟨j, i⟩ := by
  dsimp [τ.subcomplex, σ.subcomplex]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [t, simplex, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ.simplex, objMk,
    σ.nonDegenerateEquiv.toFun, τ.nonDegenerateEquiv,
    τ.nonDegenerateEquiv.toFun, τ.simplex] at h₁ h₂
  rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  dsimp at h₁ h₂
  change _ ∘ x = _ at h₁ h₂
  obtain hj | (hj : b.succ ≤ j.castSucc) := Fin.lt_or_le j.castSucc b.succ
  · let h₁' := congr_fun h₁ b.succ.castSucc
    let h₂' := congr_fun h₂ b.succ.castSucc
    simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
    simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.ext_iff] at h₁' h₂'
    split at h₁'
    · next h =>
      simp [h.not_le] at h₂'
      simp [Fin.lt_iff_val_lt_val] at hj
      simp at h₁'
      rw [h₁'] at h₂'
      simp [show ¬ b.1 + 2 ≤ j + 1 by omega] at h₂'
    · next h =>
      aesop
  · let h₁' := congr_fun h₁ b.succ.succ
    let h₂' := congr_fun h₂ b.succ.succ
    simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
    simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.ext_iff] at h₁' h₂'
    simp [Fin.le_iff_val_le_val] at hj
    aesop

/-- for `0 ≤ a < b ≤ n + 1`, the `a + 2`-th face of `τ b (a + 1)` is not contained in
  `τ j i` for any `0 ≤ i ≤ j < b`. -/
lemma face_snd_succ_succ_image_not_le_τ (a j : Fin b) (i : Fin j.succ) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (t ⟨b, a.succ⟩)
      ≤ τ.subcomplex ⟨⟨j, by omega⟩, ⟨i, by simp⟩⟩ := by
  dsimp [τ.subcomplex]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [t, simplex, nonDegenerateEquiv, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, τ.simplex, objMk] at h₁ h₂
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
      rw [not_le] at h'
      simp [h', Fin.ext_iff] at h₁
      simp_all only [Int.reduceNeg, Fin.isValue, ite_eq_left_iff, not_le, Fin.reduceEq, imp_false, not_lt]
      split at h₁
      next h_2 =>
        simp_all only [Int.reduceNeg, Fin.coe_pred]
        omega
      next h_2 =>
        simp_all only [Int.reduceNeg, Fin.coe_castPred, Fin.coe_pred]
        simp_all only [Int.reduceNeg, Fin.is_lt, not_true_eq_false]
  · next h =>
    simp_rw [← h] at h₁ h₂
    simp [h.not_lt, h.symm.le] at h₁ h₂
    split at h₂
    · next h' =>
      simp at h₂
      simp_all only [Int.reduceNeg]
      simp_all only [Int.reduceNeg]
      split at h₁
      next h_2 =>
        split at h₁
        next h_3 => omega
        next h_3 => omega
      next h_2 =>
        split at h₁
        next h_3 =>
          simp [Fin.ext_iff] at h₁
          omega
        next h_3 =>
          simp [Fin.ext_iff] at h₁
          omega
    · omega

/-- for `0 ≤ a < b ≤ n`, the `a + 2`-th face of `τ b (a + 1)` is not contained in
  `τ b i` for any `0 ≤ i ≤ a`. -/
lemma face_snd_succ_succ_image_not_le_τ' (a : Fin b) (i : Fin a.succ) :
    ¬ (face {⟨a.succ.succ, by omega⟩}ᶜ).image (t ⟨b, a.succ⟩)
      ≤ τ.subcomplex ⟨b, ⟨i, by simp; omega⟩⟩ := by
  dsimp [τ.subcomplex]
  rw [ofSimplex_eq_range]
  simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
    Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
  intro x h
  simp [t, simplex, nonDegenerateEquiv, nonDegenerateEquiv.toFun] at h
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
    objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, τ.simplex, objMk] at h₁ h₂
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
    · aesop
  · next h =>
    simp [Fin.ext_iff] at h₁
    split at h₁
    · omega
    · split at h₁
      · omega
      · simp [Fin.ext_iff] at h₁
        omega

open Sigma.Lex in
lemma face_snd_succ_succ_image_not_le_τ_le (j : Σₗ (b : Fin (n + 2)), Fin b.succ) (h : j ≤ i) (hn : i < ⊤) :
    ¬ (face {⟨(succ i).2.succ, by omega⟩}ᶜ).image (t (succ i)) ≤ τ.subcomplex j := by
  obtain ⟨b', a'⟩ := j
  obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := (Sigma.Lex.Fin.cases i)
  · exfalso
    rwa [top_eq_last, lt_self_iff_false] at hn
  · rw [Fin.succ_eq₁]
    cases h
    · next h =>
      exact face_snd_succ_succ_image_not_le_τ b a ⟨b', h⟩ ⟨a', by simp⟩
    · next h =>
      simp [Fin.le_iff_val_le_val] at h
      exact face_snd_succ_succ_image_not_le_τ' b' a ⟨a', by simp; omega⟩
  · rw [Fin.succ_eq₂]
    dsimp [τ.subcomplex]
    rw [ofSimplex_eq_range]
    simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
      Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
    intro x h'
    simp [t, simplex, nonDegenerateEquiv, nonDegenerateEquiv.toFun] at h'
    have h₁ := congr_arg Prod.fst h'
    have h₂ := congr_arg Prod.snd h'
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, τ.simplex, objMk] at h₁ h₂
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
    dsimp at h₁ h₂
    change _ ∘ x = _ at h₁ h₂
    replace h₁ := congr_fun h₁ ⟨b.succ, by omega⟩
    replace h₂ := congr_fun h₂ ⟨b.succ, by omega⟩
    simp [Fin.succAbove, Fin.predAbove] at h₁ h₂
    simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
    simp at h₁ h₂
    split at h₂
    · omega
    · next h'' =>
      rw [not_le] at h''
      simp at h₂
      simp [h'', Fin.ext_iff, show ¬ ↑b' < ↑(x ⟨b + 1, _⟩) - 1 by omega] at h₁
      rw [h₁] at h₂
      cases h
      · next h =>
        simp [Fin.lt_iff_val_lt_val] at h
        omega
      · next h =>
        simp at h₂

open Sigma.Lex in
lemma face_snd_succ_succ_image_succ_not_le_filtration (hn : i < ⊤) :
    ¬ (face {⟨(succ i).snd.succ, by omega⟩}ᶜ).image (t (succ i))
      ≤ filtration i := by
  simp only [Fin.val_succ, face_singleton_compl, Subpresheaf.ofSection_image,
    filtration, σ.filtration, unionProd, Fin.isValue, Subpresheaf.ofSection_le_iff, Subpresheaf.max_obj,
    prod_obj, Subpresheaf.top_obj, Set.top_eq_univ, Subpresheaf.iSup_obj, iSup_obj, Set.mem_union,
    Set.mem_iUnion, exists_prop, not_or, not_exists, not_and]
  constructor
  · obtain rfl | ⟨b, a, rfl⟩ | ⟨b, rfl⟩ := Sigma.Lex.Fin.cases i
    · exfalso
      rwa [top_eq_last, lt_self_iff_false] at hn
    · rw [Fin.succ_eq₁]
      refine ⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩
      · have := face_snd_succ_succ_image_not_le_top_prod_horn b a
        simp [face_singleton_compl] at this
        exact this
      · have := face_snd_succ_succ_image_not_le_boundary_prod_top b a
        simp [face_singleton_compl] at this
        exact this
      · intro ⟨j, i⟩ _
        have := face_snd_succ_succ_image_not_le_σ b a j i
        simp [face_singleton_compl] at this
        exact this
    · rw [Fin.succ_eq₂]
      refine ⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩
      · have := face_one_image_not_le_top_prod_horn b
        simp [face_singleton_compl] at this
        exact this
      · have := face_one_image_not_le_boundary_prod_top b
        simp [face_singleton_compl] at this
        exact this
      · intro ⟨j, i⟩ hij
        have := face_one_image_not_le_σ b j i
        simp [face_singleton_compl] at this
        exact this
  · intro j h
    have := face_snd_succ_succ_image_not_le_τ_le _ _ h hn
    simp [face_singleton_compl] at this
    exact this

/-- the first face of `τ 0 0` is not contained in `S(n,n)`. -/
lemma face_one_image_not_le_σ_filtration_top :
  ¬ (face {(1 : Fin (n + 4))}ᶜ).image (t ⊥) ≤ σ.filtration ⊤ := by
  simp [face_singleton_compl, σ.filtration, unionProd]
  refine ⟨⟨Set.nmem_setOf_iff.2 ?_, Set.nmem_setOf_iff.2 ?_⟩, ?_⟩
  · simp [mem_horn_iff]
    change insert 1 (Set.range (simplex₂' _ ∘ Fin.succAbove _)) = Set.univ
    ext i
    fin_cases i
    all_goals simp [Fin.succAbove, Sigma.Lex.bot_eq_zero, SimplexCategory.Hom.toOrderHom,
        SimplexCategory.Hom.mk, objMk, objEquiv, Equiv.ulift]
    · use 0
      aesop
    · use 1
      aesop
  · simp [boundary]
    change Function.Surjective (Fin.predAbove _ ∘ Fin.predAbove _ ∘ Fin.succAboveOrderEmb _)
    intro i
    dsimp
    simp [Fin.succAboveOrderEmb, Fin.predAbove, Fin.succAbove, Sigma.Lex.bot_eq_zero]
    simp_rw [Fin.lt_iff_val_lt_val]
    by_cases h : 0 < i.1
    · use i.succ
      simp
    · use i.castSucc
      aesop
  · intro j i
    rw [σ.subcomplex, ofSimplex_eq_range, Sigma.Lex.bot_eq_zero]
    simp only [face_singleton_compl, ofSimplex, Subpresheaf.ofSection_image,
      Subpresheaf.ofSection_le_iff, Subpresheaf.range_obj, Set.mem_range, not_exists]
    intro x h
    simp [t, simplex, nonDegenerateEquiv.toFun] at h
    have h₁ := congr_arg Prod.fst h
    have h₂ := congr_arg Prod.snd h
    simp [SSet.yonedaEquiv, SSet.uliftFunctor, yonedaCompUliftFunctorEquiv, stdSimplex,
      objEquiv, SimplexCategory.σ, SimplexCategory.δ, Fin.succAboveOrderEmb, σ.simplex, objMk,
      σ.nonDegenerateEquiv.toFun, τ.nonDegenerateEquiv,
      τ.nonDegenerateEquiv.toFun, τ.simplex] at h₁ h₂
    rw [SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
    dsimp at h₁ h₂
    change _ ∘ x = _ at h₁ h₂
    let h₁' := congr_fun h₁ 1
    let h₂' := congr_fun h₂ 1
    simp [Fin.predAbove, Fin.succAbove] at h₁' h₂'
    simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁' h₂'
    have fst : (toLex (⟨j, i⟩ : (a : Fin (n + 1)) × Fin (↑a + 1))).fst = j := rfl
    have snd : (toLex (⟨j, i⟩ : (a : Fin (n + 1)) × Fin (↑a + 1))).snd = i := rfl
    simp_rw [fst, snd] at h₁' h₂'
    split at h₁'
    · next h' =>
      dsimp [Fin.succ] at h₂'
      simp [h'.not_le] at h₂'
      rw [Fin.eq_mk_iff_val_eq] at h₁'
      dsimp at h₁'
      split at h₂'
      · simp [Fin.ext_iff] at h₂'
      · omega
    · next h' =>
      rw [Fin.ext_iff] at h₁'
      dsimp at h₁'
      rw [h₁'] at h₂'
      simp [show ¬ (2 : Fin (n + 4)) = 0 by simp [Fin.ext_iff]] at h₂'

open Sigma.Lex in
lemma innerHornImage_succ_le_inf :
    innerHornImage (succ i) ≤
      τ.subcomplex (succ i) ⊓ filtration i := by
  apply le_inf
  · rw [τ.subcomplex, ofSimplex_eq_range]
    exact image_le_range _ _
  · exact innerHornImage_succ_le_filtration i

open Sigma.Lex in
lemma inf_le_innerHornImage_succ (hn : i < ⊤) :
    τ.subcomplex (succ i) ⊓ filtration i ≤
      innerHornImage (succ i) := by
  rw [τ.subcomplex, ofSimplex_eq_range, subcomplex_le_horn_image_iff _ _ inf_le_left, le_inf_iff, not_and]
  exact fun _ ↦ face_snd_succ_succ_image_succ_not_le_filtration i hn

open Sigma.Lex in
def filtrationPushout_intermediate (hn : i < ⊤) :
    Sq
      (innerHornImage (succ i))
      (τ.subcomplex (succ i))
      (filtration i)
      (filtration (succ i))
      where
  max_eq := by rw [filtration_succ, sup_comm]
  min_eq := le_antisymm (inf_le_innerHornImage_succ i hn) (innerHornImage_succ_le_inf i)

open Sigma.Lex in
def filtrationPushout_zero :
    Sq
      (innerHornImage (⊥ : Σₗ (b : Fin (n + 2)), Fin b.succ))
      (τ.subcomplex ⊥)
      (σ.filtration ⊤)
      (filtration ⊥) where
  max_eq := by rw [filtration_bot, sup_comm]
  min_eq := by
    rw [τ.subcomplex, ofSimplex_eq_range]
    apply le_antisymm
    · rw [subcomplex_le_horn_image_iff, le_inf_iff, not_and]
      · exact fun _ ↦ face_one_image_not_le_σ_filtration_top
      · exact inf_le_left
    · exact le_inf (image_le_range _ _) (innerHornImage_bot_le_filtration)

end τ
