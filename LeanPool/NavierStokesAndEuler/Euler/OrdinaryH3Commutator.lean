/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Products

/-! The actual ordinary H³ transport commutator, without derivative loss. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerTransportDerivatives Finset
open scoped ContDiff

theorem advection_directional (A B : SmoothL2Field Space) (v : Space) :
    (advectionField A B).directionalField v =
      addField (advectionField A (B.directionalField v))
        (advectionField (A.directionalField v) B) := by
  apply field_ext
  funext x
  have he : (advectionField A B).field=transport A.field B.field :=
    funext (advectionField_field A B)
  rw [directionalField_field,he,addField_field,advectionField_field,advectionField_field]
  exact directional_transport_commutator v A.field B.field A.smooth B.smooth x

/-- Transport commutator, given by `fieldSub (wordField (advectionField A B) w) (advectionField
A (wordField B w))`. -/
def transportCommutator (A B : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) : SmoothL2Field
    Space :=
  fieldSub (wordField (advectionField A B) w) (advectionField A (wordField B w))

theorem transportCommutator_zero (A B : SmoothL2Field Space) (w : Fin 0 → Fin 3) :
    (transportCommutator A B w).toLp=0 := by
  rw [transportCommutator,toLp_fieldSub,wordField_zero,wordField_zero,sub_self]

theorem transportCommutator_snoc (A B : SmoothL2Field Space)
    {n : ℕ} (w : Fin n → Fin 3) (j : Fin 3) :
    transportCommutator A B (Fin.snoc w j) =
      addField (wordField (advectionField (A.directionalField (axis j)) B) w)
        (transportCommutator A (B.directionalField (axis j)) w) := by
  apply field_ext
  funext x
  simp only [transportCommutator,wordField_snoc,advection_directional,wordField_add,
    fieldSub_field,addField_field]
  abel

theorem gradient_advection_outer (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 3 M A) (hB : WordBound 3 N B)
    {n k l : ℕ} (hk : 1 ≤ k) (horder : n + k + l ≤ 3)
    (a : Fin n → Fin 3) (w : Fin k → Fin 3) (v : Fin l → Fin 3) :
    ‖(wordField (advectionField (wordField A w) (wordField B v)) a).toLp‖ ≤
      3*(2 : ℝ)^n*h3ProductConstant*M*N := by
  rw [advectionField,wordField_sum,toLp_sumField]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, (2 : ℝ)^n*h3ProductConstant*M*N := by
      apply sum_le_sum
      intro i _
      simpa only [wordField_cons] using gradient_outer_product A B M N hA hB hk
        (by omega : 1 ≤ l+1) (by omega : n+k+(l+1) ≤ 4) a w (Fin.cons i v) i
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem source_advection_outer (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 3 M A) (hB : WordBound 4 N B)
    {n : ℕ} (hn : n ≤ 3) (a : Fin n → Fin 3) :
    ‖(wordField (advectionField A B) a).toLp‖ ≤
      3*(2 : ℝ)^n*h3ProductConstant*M*N := by
  rw [advectionField,wordField_sum,toLp_sumField]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, (2 : ℝ)^n*h3ProductConstant*M*N := by
      apply sum_le_sum
      intro i _
      simpa only [wordField_cons,wordField_zero] using source_outer_product A B M N hA hB
        (by omega : n+0 ≤ 3) (by norm_num : 1 ≤ 1) (by omega : n+0+1 ≤ 4)
        a Fin.elim0 (Fin.cons i Fin.elim0) i
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem transportCommutator_word_bound (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 3 M A) (hB : WordBound 3 N B)
    {n l : ℕ} (horder : n + l ≤ 3) (a : Fin n → Fin 3) (v : Fin l → Fin 3) :
    ‖(transportCommutator A (wordField B v) a).toLp‖ ≤
      3*((2 : ℝ)^n-1)*h3ProductConstant*M*N := by
  induction n generalizing l with
  | zero =>
      simp only [transportCommutator_zero,norm_zero,pow_zero,sub_self,mul_zero,zero_mul,le_refl]
  | succ n ih =>
    have he : transportCommutator A (wordField B v) a =
        addField
          (wordField (advectionField (A.directionalField (axis (a (Fin.last n)))) (wordField B v))
              (Fin.init a))
          (transportCommutator A (wordField B (Fin.cons (a (Fin.last n)) v)) (Fin.init a)) := by
      simpa only [Fin.snoc_init_self,wordField_cons] using
        transportCommutator_snoc A (wordField B v) (Fin.init a) (a (Fin.last n))
    rw [he,toLp_addField]
    apply (norm_add_le _ _).trans
    have h1 := gradient_advection_outer A B M N hA hB (by norm_num : 1 ≤ 1)
      (by omega : n+1+l ≤ 3) (Fin.init a) (Fin.cons (a (Fin.last n)) Fin.elim0) v
    have h2 := ih (by omega : n+(l+1) ≤ 3) (Fin.init a) (Fin.cons (a (Fin.last n)) v)
    simp only [wordField_cons,wordField_zero] at h1
    exact (add_le_add h1 h2).trans_eq (by rw [pow_succ]; ring)

theorem transportCommutator_bound (A B : SmoothL2Field Space) (M N : ℝ)
    (hA : WordBound 3 M A) (hB : WordBound 3 N B)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → Fin 3) :
    ‖(transportCommutator A B w).toLp‖ ≤ 3*((2 : ℝ)^n-1)*h3ProductConstant*M*N := by
  simpa only [wordField_zero] using transportCommutator_word_bound A B M N hA hB
    (by simpa only [Nat.add_zero] using hn) w Fin.elim0

end EulerOrdinarySobolev
