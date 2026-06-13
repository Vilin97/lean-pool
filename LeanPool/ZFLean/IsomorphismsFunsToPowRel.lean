/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import LeanPool.ZFLean.Isomorphisms

/-!
# LeanPool.ZFLean.IsomorphismsFunsToPowRel

Imported Lean Pool material for `LeanPool.ZFLean.IsomorphismsFunsToPowRel`.
-/

namespace ZFSet

open Classical in
/-- Sends a function `A → 𝒫 B` to the corresponding relation on `A × B`. -/
noncomputable abbrev funsToPowRelF (A B : ZFSet) : ZFSet :=
  λᶻ : (A.funs B.powerset) → (A.prod B).powerset
    | f ↦ if hf : A.IsFunc B.powerset f then
      A.prod B |>.sep fun z ↦
        if hz : z ∈ A.prod B then
          have : z.π₁ ∈ A := by
            rw [mem_prod] at hz
            obtain ⟨_, _, _, _, rfl⟩ := hz
            rwa [π₁_pair]
          z.π₂ ∈ (@ᶻf ⟨z.π₁, by rwa [is_func_dom_eq hf]⟩).val
        else False
      else ∅

open Classical in
/-- Sends a relation on `A × B` to the corresponding function `A → 𝒫 B`. -/
noncomputable abbrev funsToPowRelG (A B : ZFSet) : ZFSet :=
  λᶻ : (A.prod B).powerset → (A.funs B.powerset)
    | R ↦ λᶻ: A → B.powerset
      | a ↦ if _ha : a ∈ A then B.sep fun b ↦ a.pair b ∈ R else ∅

@[zfun]
theorem funsToPowRelF_isFunc {A B : ZFSet} :
    (A.funs B.powerset).IsFunc (A.prod B).powerset (funsToPowRelF A B) := by
  classical
  apply lambda_isFunc
  intro f hf
  rw [mem_funs] at hf
  rw [dite_cond_eq_true (eq_true hf)]
  apply sep_mem_powerset
  rw [mem_powerset]

@[zfun]
theorem funsToPowRelG_isFunc {A B : ZFSet} :
    (A.prod B).powerset.IsFunc (A.funs B.powerset) (funsToPowRelG A B) := by
  classical
  apply lambda_isFunc
  intro R hR
  rw [mem_powerset] at hR
  apply mem_funs_of_lambda
  intro a ha
  rw [dite_cond_eq_true (eq_true ha)]
  apply sep_mem_powerset
  rw [mem_powerset]

theorem funsToPowRel_left_inverse {A B : ZFSet} :
    funsToPowRelG A B ∘ᶻ funsToPowRelF A B = 𝟙(A.funs B.powerset) := by
  classical
  let F := funsToPowRelF A B
  let G := funsToPowRelG A B
  have hF : (A.funs B.powerset).IsFunc (A.prod B).powerset F := funsToPowRelF_isFunc
  ext1 f
  simp only [mem_composition, mem_funs, mem_powerset, mem_Id_iff]
  constructor
  · rintro ⟨f, R, g, rfl, hf, hg, hR, fR_F, Rg_G⟩
    use f, hf
    rw [pair_inj, eq_self, true_and]
    rw [lambda_spec] at fR_F Rg_G
    obtain ⟨_, _, rfl⟩ := fR_F
    obtain ⟨_, _, rfl⟩ := Rg_G
    rw [dite_cond_eq_true (eq_true hf)]
    conv_rhs => rw [lambda_eta hf]
    rw [lambda_ext_iff ?_]
    · intro a ha
      rw [dite_cond_eq_true (eq_true ha), dite_cond_eq_true (eq_true ha)]
      ext1 X
      simp only [mem_prod, dite_else_false, mem_sep, pair_inj, exists_eq_right_right', π₁_pair,
        π₂_pair, and_exists_self]
      constructor
      · rintro ⟨_, _, hX⟩
        exact hX
      · intro hX
        obtain ⟨Y, Y_def, X_unq⟩ := hf.2 a ha
        have YB := hf.1 Y_def |> pair_mem_prod.mp |>.2
        rw [Image_of_singleton_pair_mem_iff hf] at Y_def
        simp_rw [fapply_eq_Image_singleton hf ha, Y_def, sInter_singleton] at hX ⊢
        rw [mem_powerset] at YB
        and_intros
        · exact YB hX
        · exact ⟨⟨ha, YB hX⟩, hX⟩
    · intro a ha
      rw [dite_cond_eq_true (eq_true ha)]
      apply sep_mem_powerset
      rw [mem_powerset]
  · rintro ⟨f, hf, rfl⟩
    use f, @ᶻF ⟨f, by rwa [is_func_dom_eq hF, mem_funs]⟩, f
    · rw [eq_self, true_and, ←and_assoc, and_self]
      and_intros
      · exact hf.1
      · exact hf.2
      · rw [←mem_powerset]
        apply fapply_mem_range
      · apply fapply.def
      · rw [lambda_spec]
        refine ⟨fapply_mem_range _ _, mem_funs.mpr hf, ?_⟩
        · conv_lhs => rw [lambda_eta hf]
          rw [lambda_ext_iff ?_]
          · intro a ha
            generalize_proofs _ _ ha_f_dom Fpfunc f_Fdom
            rw [fapply_lambda (ha := by rwa [mem_funs]), dite_cond_eq_true (eq_true ha),
              dite_cond_eq_true (eq_true ha), dite_cond_eq_true (eq_true hf)]
            · ext1 z
              constructor
              · intro hz
                simp only [mem_prod, dite_else_false, mem_sep, pair_inj, exists_eq_right_right',
                  π₁_pair, π₂_pair, and_exists_self]
                have zB : z ∈ B := mem_powerset.mp (fapply_mem_range _ (ha_f_dom ha)) hz
                exact ⟨zB, ⟨ha, zB⟩, hz⟩
              · intro hz
                simp only [mem_prod, dite_else_false, mem_sep, pair_inj, exists_eq_right_right',
                  π₁_pair, π₂_pair, and_exists_self] at hz
                obtain ⟨-, _, z_mem⟩ := hz
                exact z_mem
            · intro X hX
              rw [dite_cond_eq_true (eq_true <| mem_funs.mp hX)]
              apply sep_mem_powerset
              rw [mem_powerset]
          · intro a ha
            rw [dite_cond_eq_true (eq_true ha)]
            apply fapply_mem_range

theorem funsToPowRel_right_inverse {A B : ZFSet} :
    funsToPowRelF A B ∘ᶻ funsToPowRelG A B = 𝟙((A.prod B).powerset) := by
  classical
  let F := funsToPowRelF A B
  let G := funsToPowRelG A B
  have hG : (A.prod B).powerset.IsFunc (A.funs B.powerset) G := funsToPowRelG_isFunc
  ext1 R
  simp only [mem_composition, mem_powerset, mem_funs, mem_Id_iff]
  constructor
  · rintro ⟨R, f, S, rfl, hR, hf, hS, Rf_G, fS_F⟩
    use R, hR
    rw [pair_inj, eq_self, true_and]
    rw [lambda_spec] at Rf_G fS_F
    obtain ⟨_, _, rfl⟩ := Rf_G
    obtain ⟨_, _, rfl⟩ := fS_F
    rw [dite_cond_eq_true (eq_true hS)]
    ext1 ab
    simp only [mem_prod, dite_eq_ite, dite_else_false, mem_sep, and_exists_self]
    constructor
    · rintro ⟨⟨a, ha, b, hb, rfl⟩, b_mem⟩
      simp only [π₁_pair, π₂_pair] at b_mem
      rw [fapply_lambda] at b_mem
      · rw [ite_cond_eq_true (h := eq_true ha), mem_sep] at b_mem
        exact b_mem.2
      · intro x hx
        rw [ite_cond_eq_true (h := eq_true hx)]
        apply sep_mem_powerset
        rw [mem_powerset]
      · exact ha
    · intro hab
      obtain ⟨a, ha, b, hb, rfl⟩ := hR hab |> mem_prod.mp
      simp only [π₁_pair, π₂_pair, pair_inj, exists_eq_right_right']
      use ⟨ha, hb⟩
      rw [fapply_lambda]
      · rw [ite_cond_eq_true (h := eq_true ha), mem_sep]
        exact ⟨hb, hab⟩
      · intro x hx
        rw [ite_cond_eq_true (h := eq_true hx)]
        apply sep_mem_powerset
        rw [mem_powerset]
      · exact ha
  · rintro ⟨S, hS, rfl⟩
    simp only [pair_inj, existsAndEq, and_true, exists_and_left, exists_eq_left', and_self_left]
    and_intros
    · exact hS
    · use @ᶻG ⟨S, by rwa [is_func_dom_eq hG, mem_powerset]⟩
      and_intros
      · exact fapply_mem_range _ _ |> mem_funs.mp |>.1
      · intro a ha
        rw [fapply_lambda]
        · simp only [ha, true_and, dite_true, lambda_spec, mem_powerset]
          use B.sep fun b ↦ (a.pair b ∈ S)
          and_intros
          · exact sep_subset_self
          · rfl
          · rintro _ ⟨_, rfl⟩
            rfl
        · intros
          apply mem_funs_of_lambda
          intro _ ha
          rw [dite_cond_eq_true (eq_true ha)]
          apply sep_mem_powerset
          rw [mem_powerset]
        · rwa [mem_powerset]
      · apply fapply.def
      · rw [lambda_spec]
        refine ⟨fapply_mem_range _ _, by rwa [mem_powerset], ?_⟩
        · rw [dite_cond_eq_true (eq_true ?_)]
          · ext1 ab
            simp only [mem_prod, dite_else_false, mem_sep, and_exists_self]
            generalize_proofs G_pfunc _ S_Gdom fapply_pfunc a_dom
            have fapp_eq :
              ↑(@ᶻG ⟨S, S_Gdom⟩) =
              (λᶻ : A → B.powerset
                  | a ↦ if ha : a ∈ A then B.sep (fun b => a.pair b ∈ S) else ∅)
                := by
              rw [fapply_lambda]
              · intros
                apply mem_funs_of_lambda
                intro _ ha
                rw [dite_cond_eq_true (eq_true ha)]
                apply sep_mem_powerset
                rw [mem_powerset]
              · rwa [mem_powerset]
            constructor
            · intro hab
              obtain ⟨a, ha, b, hb, rfl⟩ := hS hab |> mem_prod.mp
              simp only [π₁_pair, π₂_pair, pair_inj, exists_eq_right_right']
              use ⟨ha, hb⟩
              rw [fapply]
              generalize_proofs choose₁ choose₂
              simp only [fapp_eq, mem_powerset] at *
              clear fapp_eq
              generalize_proofs choose₃
              have choose₃_spec := Classical.choose_spec choose₃
              rw [lambda_spec] at choose₃_spec
              rw [choose₃_spec.2.2.2, dite_cond_eq_true (eq_true ha), mem_sep]
              exact ⟨hb, hab⟩
            · rintro ⟨⟨a, ha, b, hb, rfl⟩, h⟩
              simp only [π₁_pair, π₂_pair] at h
              simp only [fapply, mem_powerset, mem_funs] at h
              generalize_proofs choose₁ choose₂ at h
              have choose₁_spec := Classical.choose_spec choose₁
              have choose₂_spec := Classical.choose_spec choose₂
              have choose₁_eq := choose₁_spec.2 |> lambda_spec.mp |>.2.2
              conv at choose₂_spec =>
                enter [2,1]
                rw [choose₁_eq]
              rw [lambda_spec, dite_cond_eq_true (eq_true ha)] at choose₂_spec
              rw [choose₂_spec.2.2.2, mem_sep] at h
              exact h.2
          · rw [fapply_lambda]
            · apply lambda_isFunc
              intro a ha
              rw [dite_cond_eq_true (eq_true ha)]
              apply sep_mem_powerset
              rw [mem_powerset]
            · intros
              apply mem_funs_of_lambda
              intro a ha
              rw [dite_cond_eq_true (eq_true ha)]
              apply sep_mem_powerset
              rw [mem_powerset]
            · rwa [mem_powerset]

theorem isIso_funs_to_pow_rel {A B : ZFSet} : A.funs B.powerset ≅ᶻ (A.prod B).powerset :=
  isIso_of_two_sided_inverse funsToPowRel_left_inverse funsToPowRel_right_inverse

end ZFSet
