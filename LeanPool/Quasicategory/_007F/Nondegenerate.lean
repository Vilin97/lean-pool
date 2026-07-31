/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.Data.Sigma.Order
import LeanPool.Quasicategory.TopCatModelCategory.SSet.NonDegenerateProdSimplex

namespace SSet

open CategoryTheory MonoidalCategory SSet Simplicial SimplexCategory prodStdSimplex

variable {n : ℕ}

@[simp]
def simplex₂' (i : Σₗ (b : Fin n), Fin b.succ) : Fin (n + 2) →o Fin 3 where
  toFun k :=
    if k ≤ ⟨i.2, by omega⟩ then 0
    else if k ≤ ⟨i.1 + 1, by omega⟩ then 1
    else 2
  monotone' := by
    refine Fin.monotone_iff_le_succ.mpr ?_
    intro j
    simp_rw [Fin.le_iff_val_le_val]
    simp_all only [Nat.reduceAdd, Fin.coe_castSucc, Fin.val_succ, Fin.isValue, add_le_add_iff_right, Fin.val_fin_le]
    split
    next => omega
    next =>
      split
      next h_1 =>
        split
        next =>omega
        next =>
          split
          all_goals omega
      next =>
        split
        next => omega
        next =>
          split
          all_goals omega

@[simp]
def τ.simplex₂ (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : Δ[2] _⦋n + 2⦌  :=
  stdSimplex.objEquiv.symm (mkHom (simplex₂' i))

@[simp]
def σ.simplex₂ (i : Σₗ (b : Fin n), Fin b.succ) : Δ[2] _⦋n + 1⦌  :=
  stdSimplex.objEquiv.symm (mkHom (simplex₂' i))

lemma σ.simplex₂_injective : Function.Injective (σ.simplex₂ (n := n)) := by
  intro i j h
  rcases i with ⟨b, a⟩
  rcases j with ⟨b', a'⟩
  dsimp at h
  wlog hb : b < b' generalizing b b'
  · simp only [not_lt] at hb
    obtain hb | rfl := hb.lt_or_eq
    · exact (this _ _ _ _ h.symm hb).symm
    · clear hb
      wlog ha : a < a' generalizing a a'
      · simp only [not_lt] at ha
        obtain ha | rfl := ha.lt_or_eq
        · exact (this _ _ h.symm ha).symm
        · rfl
      have := stdSimplex.objMk_injective h
      simp at this
      have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨a', by dsimp; omega⟩
      simp_rw [Fin.le_iff_val_le_val] at this
      simp [ha.not_le] at this
  exfalso
  have := stdSimplex.objMk_injective h
  simp at this
  have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨b'.succ, by dsimp; omega⟩
  simp at this
  have p : ¬ b'.1 + 1 ≤ a.1 := by
    simp only [Fin.val_succ, not_le]
    rw [Fin.lt_iff_val_lt_val] at hb
    omega
  have p' : ¬ b'.1 + 1 ≤ a'.1 := by dsimp; omega
  have p'' : ⟨b'.1 + 1, by omega⟩ ≤ b'.castSucc.succ := by
    rw [Fin.le_iff_val_le_val]
    simp
  simp [p, p', p''] at this
  omega

lemma τ.simplex₂_injective : Function.Injective (τ.simplex₂ (n := n)) := by
  intro i j h
  rcases i with ⟨b, a⟩
  rcases j with ⟨b', a'⟩
  dsimp [τ.simplex₂] at h
  wlog hb : b < b' generalizing b b'
  · simp only [not_lt] at hb
    obtain hb | rfl := hb.lt_or_eq
    · exact (this _ _ _ _ h.symm hb).symm
    · clear hb
      wlog ha : a < a' generalizing a a'
      · simp only [not_lt] at ha
        obtain ha | rfl := ha.lt_or_eq
        · exact (this _ _ h.symm ha).symm
        · rfl
      have := stdSimplex.objMk_injective h
      simp at this
      have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨a', by dsimp; omega⟩
      simp [ha] at this
  exfalso
  have := stdSimplex.objMk_injective h
  simp at this
  have := DFunLike.congr_fun (stdSimplex.objMk_injective h) ⟨b'.succ, by dsimp; omega⟩
  simp at this
  have p : ¬ b'.1 + 1 ≤ a.1 := by
    simp only [Fin.val_succ, not_le]
    rw [Fin.lt_iff_val_lt_val] at hb
    omega
  have p' : ¬ b'.1 + 1 ≤ a'.1 := by dsimp; omega
  have p'' : ⟨b'.1 + 1, by omega⟩ ≤ b'.castSucc.succ := by
    rw [Fin.le_iff_val_le_val]
    simp
  simp [p, p', p''] at this
  rw [Fin.le_iff_val_le_val] at this
  simp at this
  omega

open stdSimplex in
def τ.simplex (i : Σₗ (b : Fin (n + 1)), Fin b.succ) : (Δ[n] ⊗ Δ[2] : SSet) _⦋n + 2⦌ :=
  (objEquiv.symm (σ ⟨i.2, by omega⟩ ≫ σ i.1), objEquiv.symm (mkHom (simplex₂' i)))

open stdSimplex in
def σ.simplex (i : Σₗ (b : Fin n), Fin b.succ) : (Δ[n] ⊗ Δ[2] : SSet) _⦋n + 1⦌ :=
  (objEquiv.symm (σ ⟨i.2, by omega⟩), objEquiv.symm (mkHom (simplex₂' i)))

/-- `σ b a = (Δ[n] ⊗ Δ[2]).δ (b + 2) (τ b a) `-/
lemma simplex_eq_δ_simplex (i : Σₗ (b : Fin n), Fin b.succ) : (σ.simplex i) =
    (Δ[n] ⊗ Δ[2]).δ ⟨i.1 + 2, by omega⟩ (τ.simplex ⟨i.1.castSucc, i.2⟩) := by
  dsimp [SimplicialObject.δ]
  apply Prod.ext
  · apply_fun (fun f ↦ stdSimplex.objEquiv f)
    change _ = δ _ ≫ σ _ ≫ σ _
    dsimp [σ.simplex, SimplicialObject.σ]
    rw [Equiv.apply_symm_apply]
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    ext k
    simp [σ, Fin.predAbove, δ, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split_ifs
    all_goals try omega
    · next h h' h'' =>
      simp [show ¬ i.fst.1 < k - 1 by omega]
    · next h h' h'' =>
      simp at h h' h''
      omega
    · split
      · simp only [Fin.coe_pred, Fin.pred_succ]
      · next h h' h'' h''' =>
        simp at h h' h'' h'''
        omega
    · next h h' h'' =>
      simp at h h' h''
      omega
    · next h h' h'' =>
      simp at h h' h''
      omega
    · simp [show ¬ i.1.1 < k by omega]
  · apply_fun (fun f ↦ stdSimplex.objEquiv f)
    change mkHom (simplex₂' _) = δ _ ≫ mkHom (simplex₂' _)
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    ext k
    simp [δ, Fin.succAboveOrderEmb, Fin.succAbove, Fin.lt_iff_val_lt_val]
    split_ifs
    all_goals
      simp [Fin.le_iff_val_le_val] at *
      try omega

/-- for all `0 ≤ a ≤ b < n`, we get a nondegenerate `(n+1)`-simplex. -/
def σ.nonDegenerateEquiv.toFun (i : Σₗ (b : Fin n), Fin b.succ) :
    (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 1) := by
  refine ⟨σ.simplex i, ?_⟩
  rcases i with ⟨b, a⟩
  rw [prodStdSimplex.nonDegenerate_iff']
  simp [σ.simplex]
  simp [SSet.yonedaEquiv, yonedaCompUliftFunctorEquiv, stdSimplex.objEquiv, Equiv.ulift]
  intro x y h
  simp at h
  ext i
  fin_cases i
  have h₁ := congr_arg Prod.fst h
  have h₂ := congr_arg Prod.snd h
  rw [stdSimplex.ext'_iff, SimplexCategory.Hom.ext_iff, OrderHom.ext_iff] at h₁ h₂
  simp [stdSimplex, σ, SSet.uliftFunctor, stdSimplex.objEquiv, stdSimplex.objMk] at h₁ h₂
  replace h₁ := congr_fun h₁ 0
  replace h₂ := congr_fun h₂ 0
  simp [Hom.toOrderHom, Fin.predAbove] at h₁ h₂
  simp_rw [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.ext_iff] at h₁ h₂
  simp
  split at h₂
  · next h =>
    simp_all only [Fin.isValue, Fin.val_zero, Fin.val_natCast]
    split at h₁
    next h_2 =>
      split at h₂
      next h_3 =>
        split at h₁
        next h_4 =>
          simp_all only [Fin.isValue, Fin.val_zero, Fin.coe_pred]
          change (x 0).1.pred = (y 0).1.pred at h₁
          refine Nat.pred_inj ?_ ?_ h₁
          · change _ < (x 0).1 at h_2
            omega
          · change _ < (y 0).1 at h_4
            omega
        omega
      omega
    next h_2 =>
      split at h₂
      next h_3 =>
        split at h₁
        next h_4 =>
          omega
        simpa
      next h_3 =>
        split at h₁
        all_goals
          split at h₂
          all_goals omega
  · next h =>
    simp at h
    simp [h] at h₁
    split at h₁
    · next h' =>
      change (x 0).1.pred = (y 0).1.pred at h₁
      refine Nat.pred_inj ?_ ?_ h₁
      · change _ < (x 0).1 at h
        omega
      · change _ < (y 0).1 at h'
        omega
    · next h' =>
      exfalso
      simp at h₁
      simp_all only [Fin.isValue, Fin.val_natCast, not_lt]
      split at h₂
      next h_2 =>
        split at h₂
        next h_3 => simp_all only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero]
        next h_3 =>
          split at h₂
          next h_4 =>
            simp_all only [Fin.isValue, not_le, Fin.val_one]
          omega
      next h_2 => omega

/-- for all `0 ≤ a ≤ b ≤ n`, we get a nondegenerate `(n+2)`-simplex. -/
def τ.nonDegenerateEquiv.toFun (i : Σₗ (b : Fin (n + 1)), Fin b.succ) :
    (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 2) := by
  refine ⟨τ.simplex i, ?_⟩
  rcases i with ⟨b, a⟩
  rw [nonDegenerate_iff _ rfl]
  ext x
  change (((Fin.predAbove b) ∘ (Fin.predAbove ⟨a, _⟩)) x).1 + (simplex₂' ⟨b, a⟩ x) = x
  simp [Fin.predAbove, τ.simplex, simplex₂]
  split
  · next h =>
    simp_rw [Fin.lt_pred_iff]
    simp [h.not_le]
    split
    · next h' =>
      simp [Fin.lt_iff_val_lt_val] at h'
      simp [h'.not_le, Fin.le_iff_val_le_val]
      omega
    · next h' =>
      simp [Fin.lt_iff_val_lt_val] at h'
      simp [h', Fin.le_iff_val_le_val]
      omega
  · next h =>
    simp_rw [Fin.lt_castPred_iff]
    simp [not_lt.1 h]
    simp at h
    have : ⟨a, by omega⟩ ≤ b.castSucc.castSucc := by
      simp [Fin.le_iff_val_le_val]
      omega
    simp [(h.trans this).not_lt]

-- `σab = ⟨(0, 0),..., (0, a), (1, a),..., (1, b), (2, b + 1),..., (2, n)⟩`
-- `τab = ⟨(0, 0),..., (0, a), (1, a),..., (1, b), (2, b), (2, b + 1),..., (2, n)⟩`
/-- There is a bijection (via `σ`) between pairs `0 ≤ a ≤ b < n` and nondegenerate
  `(n + 1)`-simplices. -/
noncomputable
def σ.nonDegenerateEquiv :
    (Σₗ (b : Fin n), Fin b.succ) ≃ (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 1) := by
  refine Equiv.ofBijective (σ.nonDegenerateEquiv.toFun) ?_
  constructor
  · exact fun _ _ h ↦ σ.simplex₂_injective (congr_arg (Prod.snd ∘ Subtype.val) h)
  · -- `(Δ[n] ⊗ Δ[2]).δ (b + 2) y` is nd for all `0 ≤ a ≤ b < n` corresponding to `y ∈ nd_(n + 2)`
    sorry

/-- There is a bijection (via `τ`) between pairs `0 ≤ a ≤ b ≤ n` and nondegenerate
  `(n + 2)`-simplices. -/
noncomputable
def τ.nonDegenerateEquiv :
    (Σₗ (b : Fin (n + 1)), Fin b.succ) ≃ (Δ[n] ⊗ Δ[2] : SSet).nonDegenerate (n + 2) := by
  refine Equiv.ofBijective (τ.nonDegenerateEquiv.toFun) ?_
  constructor
  · intro i j h
    simpa using τ.simplex₂_injective (congr_arg (Prod.snd ∘ Subtype.val) h)
  · intro x
    have α := (prodStdSimplex.nonDegenerate_iff _ rfl).1 x.2
    let f := x.1.2
    let g := x.1.1
    let S : Finset (Fin (n + 3)) := { i | f i = 1} -- min will be a+1, max will be b+1
    have thm : ∀ (i : Fin (n + 3)), (g i).1 + (f i).1 = i.1 := fun i ↦
      Fin.eq_mk_iff_val_eq.1 (DFunLike.congr_fun α i)
    by_cases hS : S.Nonempty
    · let asucc := (S.min' hS) -- a+1
      let bsucc := (S.max' hS) -- b+1
      let a := g asucc
      let b := g bsucc

      have ha : asucc ∈ S := S.min'_mem hS
      have hb : bsucc ∈ S := S.max'_mem hS
      have Ha : ⟨a + (f asucc), _⟩ = asucc := DFunLike.congr_fun α asucc
      have Hb : ⟨b + (f bsucc), _⟩ = bsucc := DFunLike.congr_fun α bsucc
      have Ha' : f asucc = 1 := by simpa [S] using (S.min'_mem hS)
      have Hb' : f bsucc = 1 := by simpa [S] using (S.max'_mem hS)
      simp_rw [Ha'] at Ha -- shows that (g asucc) = a
      simp_rw [Hb'] at Hb -- shows that (g bsucc) = b

      have haa : ⟨a, by omega⟩ < asucc := by simp only [← Ha, Nat.reduceAdd, Fin.isValue,
        Fin.val_one, Fin.mk_lt_mk, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, S]
      have hbb : ⟨b, by omega⟩ < bsucc := by simp only [← Hb, Nat.reduceAdd, Fin.isValue,
        Fin.val_one, Fin.mk_lt_mk, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt, S]
      have hab : a ≤ b := by
        have : asucc ≤ bsucc := Finset.min'_le S bsucc hb
        rw [← Ha, ← Hb, Fin.le_iff_val_le_val] at this
        simpa only [Nat.reduceAdd, Fin.isValue, Fin.val_one, add_le_add_iff_right, Fin.val_fin_le]

      use ⟨b, ⟨a, Nat.lt_add_one_of_le hab⟩⟩
      apply nonDegenerate_ext rfl
      ext i
      change (((Fin.predAbove b) ∘ (Fin.predAbove ⟨a, _⟩)) i).1 = (g i).1
      simp only [Function.comp_apply, Fin.predAbove, Fin.castSucc_mk, Fin.val_succ, len_mk,
        OrderHom.toFun_eq_coe, stdSimplex.objEquiv_toOrderHom_apply]
      split
      ·
        next h =>
        simp_rw [Fin.lt_pred_iff]
        replace h : asucc ≤ i := by
          rw [← Ha]
          exact Fin.le_iff_val_le_val.1 h
        split
        · next h' =>
          -- f i = 2, so g i = i - 2
          suffices (f i).1 = 2 by
            rw [Fin.coe_pred, Fin.coe_pred, ← thm, this]
            rfl
          have h' : bsucc < i := by rwa [← Hb]
          have ne_one : ¬1 = (f i) := by
            intro h
            apply Finset.not_mem_of_max_lt h' (Finset.coe_max' hS).symm
            simpa [S] using h.symm
          rw [Fin.eq_mk_iff_val_eq] at ne_one
          have : (f bsucc).1 ≤ (f i).1 := (stdSimplex.asOrderHom f).monotone' h'.le
          rw [Hb'] at this
          have := Nat.lt_of_le_of_ne this ne_one
          rw [← Fin.eq_mk_iff_val_eq]
          swap; omega
          apply Fin.eq_last_of_not_lt
          rw [not_lt]
          exact this
        · next h' =>
          -- f i = 1, so g i = i - 1
          suffices (f i).1 = 1 by
            rw [Fin.coe_castPred, Fin.coe_pred, ← thm, this]
            rfl
          have h' : i ≤ bsucc := by
            rw [← Hb]
            rwa [not_lt] at h'
          have ge_one : (f asucc).1 ≤ (f i).1 := (stdSimplex.asOrderHom f).monotone' h
          have le_one : (f i).1 ≤ (f bsucc).1 := (stdSimplex.asOrderHom f).monotone' h'
          rw [Ha'] at ge_one
          rw [Hb'] at le_one
          exact Eq.symm (Nat.le_antisymm ge_one le_one)
      · next h' =>
        -- f i = 0, so g i = i
        simp_rw [Fin.lt_castPred_iff]
        have : ¬ b.castSucc.castSucc < i := fun p ↦ h' (lt_of_le_of_lt hab p)
        simp only [this, ↓reduceDIte, Fin.coe_castPred]
        rw [← thm, Nat.add_right_eq_self, ← Nat.lt_one_iff]
        rw [not_lt] at h'
        have ne_one : ¬(f i) = 1 := by
          intro h
          apply Finset.not_mem_of_lt_min (lt_of_le_of_lt h' haa) (Finset.coe_min' hS).symm
          simpa [S]
        rw [Fin.eq_mk_iff_val_eq] at ne_one
        have : (f i).1 ≤ (f asucc).1 := (stdSimplex.asOrderHom f).monotone' (h'.trans haa.le)
        rw [Ha'] at this
        exact Nat.lt_of_le_of_ne this ne_one
    · --if the set is empty, then 1 is not in the image. contradiction somewhere
      exfalso
      let T : Finset (Fin (n + 3)) := { i | f i = 2}
      by_cases hT : T.Nonempty
      · let a := (T.min' hT)
        have hfa : f a = 2 := by simpa [T] using (T.min'_mem hT)
        cases (Fin.eq_zero_or_eq_succ a)
        · next h =>
          have hfa' := congr_arg f h
          rw [hfa] at hfa'
          have := thm 0
          rw [← hfa'] at this
          simp at this
        · next h =>
          obtain ⟨a1, ha⟩ := h
          cases (Fin.eq_zero_or_eq_succ a1)
          · next h' =>
            subst h'
            have hfa' : f a = f 1 := congr_arg f ha
            rw [hfa] at hfa'
            have := thm 1
            rw [← hfa'] at this
            simp only [Nat.reduceAdd, Fin.isValue, Fin.val_two, Fin.val_one, Nat.reduceEqDiff, T,
              S] at this
          . next h' =>
            obtain ⟨a2, haa⟩ := h'
            have p : (f a1.castSucc).1 = 0 := by
              have p : ¬(f a1.castSucc) = 2 := by
                intro h
                apply Finset.not_mem_of_lt_min (Fin.castSucc_lt_succ a1) (by
                  rw [← ha]
                  exact (Finset.coe_min' hT).symm)
                simpa [T]
              have : (f a1.castSucc).1 ≤ (f a1.succ).1 := (stdSimplex.asOrderHom f).monotone' (Fin.castSucc_le_succ a1)
              rw [← ha, hfa] at this
              cases (lt_or_eq_of_le this)
              · next h'' =>
                cases (lt_or_eq_of_le (Nat.le_of_lt_succ h''))
                · next h''' => exact Nat.lt_one_iff.mp h'''
                · next h''' =>
                  exfalso
                  apply hS
                  refine ⟨a1.castSucc, ?_⟩
                  simp [S]
                  rwa [Fin.eq_mk_iff_val_eq]
              · next h'' => exfalso; omega
            have p' : (f a2.castSucc.castSucc).1 = 0 := by
              have : (f a2.castSucc.castSucc).1 ≤ (f a1.castSucc).1 := by
                rw [haa, ← Fin.succ_castSucc]
                exact (stdSimplex.asOrderHom f).monotone' (Fin.castSucc_le_succ a2.castSucc)
              rw [p] at this
              exact Nat.eq_zero_of_le_zero this
            have p'' : (g a1.castSucc).1 = (a1.castSucc).1 := by
              rw [← thm, p]
              simp
            have p''' : (g a1.succ).1 = (a2.castSucc.castSucc).1 := by
              have := thm a1.succ
              rw [← ha, hfa] at this
              rcases a with ⟨a, pa⟩
              rcases a1 with ⟨a1, pa1⟩
              rcases a2 with ⟨a2, pa2⟩
              simp_all
            have hyp : (g a1.castSucc).1 ≤ (g a1.succ).1 := (stdSimplex.asOrderHom g).monotone' (Fin.castSucc_le_succ a1)
            rw [p'', p'''] at hyp
            simp only [Fin.coe_castSucc, Fin.val_natCast, Fin.cast_val_eq_self, T, S] at hyp
            simp_all
      · -- if the set is empty, then f is constant 0, which is not nondegenerate
        have thm1 : ∀ (i : Fin (n + 3)), ¬(f i) = 1 := by
          intro i hi
          apply hS
          refine ⟨i, ?_⟩
          simpa [S]
        have thm2 : ∀ (i : Fin (n + 3)), ¬(f i) = 2 := by
          intro i hi
          apply hT
          refine ⟨i, ?_⟩
          simpa [T]
        have thm0 : ∀ (i : Fin (n + 3)), (f i) = 0 := by
          intro i
          have thm1 := thm1 i
          have thm2 := thm2 i
          cases Fin.eq_zero_or_eq_succ (f i)
          · next h => exact h
          · next h =>
            obtain ⟨j, hj⟩ := h
            fin_cases j
            · exfalso
              exact thm1 hj
            · exfalso
              exact thm2 hj
        have := thm (Fin.last _)
        rw [thm0] at this
        simp at this
        omega
