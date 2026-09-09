/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.GevreyProductLp
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryGradientInterpolation
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Products
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds

/-! Sharp H³ products controlled by the actual velocity gradient.
The only middle product is D²u D²u, handled by cubic testing. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerGevreyProductLp Finset

theorem firstWord_pointwise_gradient (A : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (w : Fin 1 → Fin 3) (x : Space) :
    ‖(wordField A w).field x‖ ≤ K := by
  change ‖fderiv ℝ A.field x (axis (w 0))‖ ≤ K
  exact ((fderiv ℝ A.field x).le_opNorm _).trans
    (by simpa only [axis_norm,mul_one] using hK x)

theorem secondWord_square_gradient (A : SmoothL2Field Space) (K N : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hN : WordBound 3 N A)
    (w : Fin 2 → Fin 3) (i : Fin 3) :
    ‖(scalarProduct (wordField (mapField (EuclideanSpace.proj i) A) w)
      (wordField (mapField (EuclideanSpace.proj i) A) w)).toLp‖ ≤ 3*K*N := by
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ A.field 0)).trans (hK 0)
  have hb (x : Space) :
      ‖(wordField (mapField (EuclideanSpace.proj i) A) (Fin.tail w)).field x‖ ≤ K := by
    rw [wordField_map,mapField_field]
    exact (PiLp.norm_apply_le _ i).trans
      (firstWord_pointwise_gradient A K hK (Fin.tail w) x)
  have hs := directional_square_norm
    (wordField (mapField (EuclideanSpace.proj i) A) (Fin.tail w)) (axis (w 0)) K hb
  change ‖(scalarProduct (wordField (mapField (EuclideanSpace.proj i) A) w)
      (wordField (mapField (EuclideanSpace.proj i) A) w)).toLp‖ ≤
    3*K*‖((wordField (mapField (EuclideanSpace.proj i) A) w).directionalField (axis (w 0))).toLp‖
        at hs
  apply hs.trans
  have hn := (wordBound_coordinate hN i) 3 le_rfl (Fin.cons (w 0) w)
  rw [wordField_cons] at hn
  exact mul_le_mul_of_nonneg_left hn (by positivity)

theorem scalar_secondWord_product_gradient (A : SmoothL2Field Space) (K N : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hN : WordBound 3 N A)
    (w v : Fin 2 → Fin 3) (i j : Fin 3) :
    ‖(scalarProduct (wordField (mapField (EuclideanSpace.proj i) A) w)
      (wordField (mapField (EuclideanSpace.proj j) A) v)).toLp‖ ≤ 3*K*N := by
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ A.field 0)).trans (hK 0)
  have hN0 := wordBound_nonneg hN
  exact scalarProduct_norm_of_square_bounds _ _ _ (by positivity)
    (secondWord_square_gradient A K N hK hN w i)
    (secondWord_square_gradient A K N hK hN v j)

theorem norm_le_sum_coordinates (x : Space) : ‖x‖ ≤ ∑ i : Fin 3, ‖x i‖ := by
  have hx : (∑ i : Fin 3, x i • axis i)=x := by
    ext j
    simp [axis,Pi.single_apply,mul_ite]
  calc
    _ = ‖∑ i : Fin 3, x i • axis i‖ := congrArg norm hx.symm
    _ ≤ ∑ i : Fin 3, ‖x i • axis i‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul,axis_norm,mul_one]

theorem secondWord_product_gradient (A : SmoothL2Field Space) (K N : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hN : WordBound 3 N A)
    (w v : Fin 2 → Fin 3) (i : Fin 3) :
    ‖(coordinateProduct i (wordField A w) (wordField A v)).toLp‖ ≤ 9*K*N := by
  let B := coordinateProduct i (wordField A w) (wordField A v)
  let C := fun j : Fin 3 => scalarProduct
    (wordField (mapField (EuclideanSpace.proj i) A) w)
    (wordField (mapField (EuclideanSpace.proj j) A) v)
  have hc (j : Fin 3) (x : Space) : (C j).field x=(B.field x) j := by
    simp only [C,B,wordField_map,mapField_field,scalarProduct_field,
      coordinateProduct_field,PiLp.smul_apply,smul_eq_mul]
    rfl
  have hn (j : Fin 3) :
      (eLpNorm (fun x => ‖(C j).field x‖) 2 volume).toReal = ‖(C j).toLp‖ := by
    rw [field_norm,eLpNorm_norm]
  have h := (finite_domination (volume : Measure Space) univ B.field
    B.memLp.aestronglyMeasurable (fun j x => ‖(C j).field x‖)
    (fun j _ => (C j).memLp.norm) (fun x => by
      simp only [hc]
      exact norm_le_sum_coordinates (B.field x))).2
  change ‖B.toLp‖ ≤ 9*K*N
  rw [field_norm]
  apply h.trans
  simp only [hn]
  calc
    _ ≤ ∑ _j : Fin 3, 3*K*N := sum_le_sum (fun j _ =>
      scalar_secondWord_product_gradient A K N hK hN w v i j)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem coordinateProduct_gradient (A : SmoothL2Field Space) (K N : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hN : WordBound 3 N A)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l ≤ 4)
    (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    ‖(coordinateProduct i (wordField A w) (wordField A v)).toLp‖ ≤ 9*K*N := by
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ A.field 0)).trans (hK 0)
  have hN0 := wordBound_nonneg hN
  have hc : K*N ≤ 9*K*N := by nlinarith [mul_nonneg hK0 hN0]
  by_cases hk1 : k=1
  · subst k
    have hs (x : Space) :
        ‖(mapField (EuclideanSpace.proj i) (wordField A w)).field x‖ ≤ K :=
      (PiLp.norm_apply_le _ i).trans (firstWord_pointwise_gradient A K hK w x)
    exact ((scalarProduct_norm_left _ _ K hs).trans
      (mul_le_mul_of_nonneg_left (hN l (by omega) v) hK0)).trans hc
  by_cases hl1 : l=1
  · subst l
    have hs := scalarProduct_norm_right
      (mapField (EuclideanSpace.proj i) (wordField A w)) (wordField A v) K
      (firstWord_pointwise_gradient A K hK v)
    have hn := (wordBound_coordinate hN i) k (by omega) w
    rw [wordField_map] at hn
    exact (hs.trans (mul_le_mul_of_nonneg_left hn hK0)).trans hc
  have hk2 : k=2 := by omega
  have hl2 : l=2 := by omega
  subst k
  subst l
  exact secondWord_product_gradient A K N hK hN w v i

theorem gradient_tame_outer_product (A : SmoothL2Field Space) (K N : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hN : WordBound 3 N A)
    {n k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (horder : n + k + l ≤ 4)
    (a : Fin n → Fin 3) (w : Fin k → Fin 3) (v : Fin l → Fin 3) (i : Fin 3) :
    ‖(wordField (coordinateProduct i (wordField A w) (wordField A v)) a).toLp‖ ≤
      (2 : ℝ)^n*9*K*N := by
  induction n generalizing k l with
  | zero =>
    simpa only [wordField_zero,pow_zero,one_mul] using
      coordinateProduct_gradient A K N hK hN hk hl (by omega) w v i
  | succ n ih =>
    rw [word_coordinateProduct_recurrence,toLp_addField]
    apply (norm_add_le _ _).trans
    have h1 := ih (k := k+1) (l := l) (by omega) hl (by omega)
      (Fin.init a) (Fin.cons (a (Fin.last n)) w) v
    have h2 := ih (k := k) (l := l+1) hk (by omega) (by omega)
      (Fin.init a) w (Fin.cons (a (Fin.last n)) v)
    exact (add_le_add h1 h2).trans_eq (by rw [pow_succ]; ring)

end EulerOrdinarySobolev
