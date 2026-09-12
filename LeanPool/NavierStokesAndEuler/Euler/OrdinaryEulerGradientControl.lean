/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerHigherEnergy
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryVariableGronwall
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTameEnergy
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.GevreyProductLp
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Products
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryL2Integration
import Mathlib.Algebra.Order.Star.Real

/-! Actual gradient-supremum control of Euler Sobolev norms.  The
gradient norm is a constructed continuous path, its time integral
controls H³, and the checked H³-tame estimate then propagates every
higher order on the same time interval. -/

section

/-! Sharp H³ products controlled by the actual velocity gradient.
The only middle product is D²u D²u, handled by cubic testing. -/

section

/-! The sharp middle-derivative interpolation needed by H³ Euler
energy.  Everything is an actual smooth L² field.  Cubic testing and
noncompact integration by parts prove the L⁴ inequality without a
support or interpolation hypothesis. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field

theorem scalarProduct_norm_square (A B : SmoothL2Field ℝ) :
    ‖(scalarProduct A B).toLp‖^2 =
      ⟪(scalarProduct A A).toLp,(scalarProduct B B).toLp⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq,field_inner,field_inner]
  apply integral_congr_ae
  filter_upwards with x
  simp only [scalarProduct_field,RCLike.inner_apply,conj_trivial,smul_eq_mul]
  ring

theorem directional_square_identity (A : SmoothL2Field ℝ) (v : Space) :
    ‖(scalarProduct (A.directionalField v) (A.directionalField v)).toLp‖^2 =
      -3*⟪(scalarProduct A
        (scalarProduct (A.directionalField v) (A.directionalField v))).toLp,
        ((A.directionalField v).directionalField v).toLp⟫_ℝ := by
  let B := A.directionalField v
  let S := scalarProduct B B
  let C := scalarProduct B S
  have hs : ⟪B.toLp,C.toLp⟫_ℝ = ‖S.toLp‖^2 := by
    rw [← real_inner_self_eq_norm_sq,field_inner,field_inner]
    apply integral_congr_ae
    filter_upwards with x
    simp only [C,S,scalarProduct_field,RCLike.inner_apply,conj_trivial,smul_eq_mul]
    ring
  have hd : ⟪A.toLp,(C.directionalField v).toLp⟫_ℝ =
      3*⟪(scalarProduct A S).toLp,(B.directionalField v).toLp⟫_ℝ := by
    rw [field_inner,field_inner,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [C,S,scalarProduct_directional,addField_field,scalarProduct_field,
      RCLike.inner_apply,conj_trivial,smul_eq_mul]
    ring
  have hi := field_directional_inner A C v
  change ⟪B.toLp,C.toLp⟫_ℝ = -⟪A.toLp,(C.directionalField v).toLp⟫_ℝ at hi
  rw [hs,hd] at hi
  change ‖S.toLp‖^2 = -3*⟪(scalarProduct A S).toLp,(B.directionalField v).toLp⟫_ℝ
  linarith

theorem directional_square_norm (A : SmoothL2Field ℝ) (v : Space)
    (K : ℝ) (hK : ∀ x, ‖A.field x‖ ≤ K) :
    ‖(scalarProduct (A.directionalField v) (A.directionalField v)).toLp‖ ≤
      3*K*‖((A.directionalField v).directionalField v).toLp‖ := by
  let S := scalarProduct (A.directionalField v) (A.directionalField v)
  let Z := (A.directionalField v).directionalField v
  have hK0 : 0 ≤ K := (norm_nonneg (A.field 0)).trans (hK 0)
  have hb := scalarProduct_norm_left A S K hK
  have hi := directional_square_identity A v
  change ‖S.toLp‖^2 = -3*⟪(scalarProduct A S).toLp,Z.toLp⟫_ℝ at hi
  have hs : ‖S.toLp‖^2 ≤ (3*K*‖Z.toLp‖)*‖S.toLp‖ := by
    calc
      _ ≤ 3*|⟪(scalarProduct A S).toLp,Z.toLp⟫_ℝ| := by
        rw [hi]
        have h := neg_le_abs ⟪(scalarProduct A S).toLp,Z.toLp⟫_ℝ
        linarith
      _ ≤ 3*(‖(scalarProduct A S).toLp‖*‖Z.toLp‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ 3*((K*‖S.toLp‖)*‖Z.toLp‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (by norm_num)
      _ = _ := by ring
  change ‖S.toLp‖ ≤ 3*K*‖Z.toLp‖
  have hc : 0 ≤ 3*K*‖Z.toLp‖ := by positivity
  nlinarith [norm_nonneg S.toLp]

theorem scalarProduct_norm_of_square_bounds (A B : SmoothL2Field ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ‖(scalarProduct A A).toLp‖ ≤ C)
    (hB : ‖(scalarProduct B B).toLp‖ ≤ C) :
    ‖(scalarProduct A B).toLp‖ ≤ C := by
  have hs : ‖(scalarProduct A B).toLp‖^2 ≤ C^2 := by
    rw [scalarProduct_norm_square]
    exact (real_inner_le_norm _ _).trans
      ((mul_le_mul hA hB (norm_nonneg _) hC).trans_eq (by ring))
  nlinarith [norm_nonneg (scalarProduct A B).toLp]

end EulerOrdinarySobolev

end
end

end

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
  have hc : K*N ≤ 9*K*N := by linarith [mul_nonneg hK0 hN0]
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

end
end

end

section

/-! Sharp H³ transport energy with the actual L-infinity norm of the
velocity gradient.  The pressure and undifferentiated transport cancel
before the cubic-test interpolation estimate is used. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal Finset

theorem gradientSup_advection_outer (A : SmoothL2Field Space) (K N : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hN : WordBound 3 N A)
    {n k l : ℕ} (hk : 1 ≤ k) (horder : n + k + l ≤ 3)
    (a : Fin n → Fin 3) (w : Fin k → Fin 3) (v : Fin l → Fin 3) :
    ‖(wordField (advectionField (wordField A w) (wordField A v)) a).toLp‖ ≤
      27*(2 : ℝ)^n*K*N := by
  rw [advectionField,wordField_sum,toLp_sumField]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, (2 : ℝ)^n*9*K*N := by
      apply sum_le_sum
      intro i _
      simpa only [wordField_cons] using gradient_tame_outer_product A K N hK hN hk
        (by omega : 1 ≤ l+1) (by omega : n+k+(l+1) ≤ 4) a w (Fin.cons i v) i
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem gradient_transportCommutator_word (A : SmoothL2Field Space) (K N : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hN : WordBound 3 N A)
    {n l : ℕ} (horder : n + l ≤ 3) (a : Fin n → Fin 3) (v : Fin l → Fin 3) :
    ‖(transportCommutator A (wordField A v) a).toLp‖ ≤
      27*((2 : ℝ)^n-1)*K*N := by
  induction n generalizing l with
  | zero =>
      simp only [transportCommutator_zero,norm_zero,pow_zero,sub_self,mul_zero,zero_mul,le_refl]
  | succ n ih =>
    have he : transportCommutator A (wordField A v) a =
        addField
          (wordField (advectionField (A.directionalField (axis (a (Fin.last n)))) (wordField A v))
              (Fin.init a))
          (transportCommutator A (wordField A (Fin.cons (a (Fin.last n)) v)) (Fin.init a)) := by
      simpa only [Fin.snoc_init_self,wordField_cons] using
        transportCommutator_snoc A (wordField A v) (Fin.init a) (a (Fin.last n))
    rw [he,toLp_addField]
    apply (norm_add_le _ _).trans
    have h1 := gradientSup_advection_outer A K N hK hN (by norm_num : 1 ≤ 1)
      (by omega : n+1+l ≤ 3) (Fin.init a) (Fin.cons (a (Fin.last n)) Fin.elim0) v
    have h2 := ih (by omega : n+(l+1) ≤ 3) (Fin.init a) (Fin.cons (a (Fin.last n)) v)
    simp only [wordField_cons,wordField_zero] at h1
    exact (add_le_add h1 h2).trans_eq (by rw [pow_succ]; ring)

theorem gradient_transportCommutator (A : SmoothL2Field Space) (K N : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hN : WordBound 3 N A)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → Fin 3) :
    ‖(transportCommutator A A w).toLp‖ ≤ 27*((2 : ℝ)^n-1)*K*N := by
  simpa only [wordField_zero] using gradient_transportCommutator_word A K N hK hN
    (by simpa only [Nat.add_zero] using hn) w Fin.elim0

/-- Gradient energy constant, given by `54*(∑ n ∈ range 4, (6 : ℝ)^n)`. -/
def gradientEnergyConstant : ℝ := 54*(∑ n ∈ range 4, (6 : ℝ)^n)

theorem gradientEnergyConstant_nonneg : 0 ≤ gradientEnergyConstant := by
  exact mul_nonneg (by norm_num) (sum_nonneg (fun _ _ => by positivity))

theorem gradientEnergyConstant_eq : gradientEnergyConstant=13986 := by
  norm_num [gradientEnergyConstant,sum_range_succ]

theorem eulerRhs_word_gradient (A P : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hdiv : ∀ x, divergence A.field x = 0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → Fin 3) :
    ⟪(wordField A w).toLp,(wordField (eulerRhs A P) w).toLp⟫_ℝ ≤
      27*(2 : ℝ)^n*K*wordEnergy 3 A := by
  let X := Real.sqrt (wordEnergy 3 A)
  have hx : X^2=wordEnergy 3 A := Real.sq_sqrt (wordEnergy_nonneg 3 A)
  have hN : WordBound 3 X A := wordBound_sqrt_energy 3 A
  have hb := gradient_transportCommutator A K X hK hN hn w
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ A.field 0)).trans (hK 0)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hb' : ‖(transportCommutator A A w).toLp‖ ≤ 27*(2 : ℝ)^n*K*X := by
    apply hb.trans
    have hcoef : 27*((2 : ℝ)^n-1) ≤ 27*(2 : ℝ)^n := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hK0) hX
  rw [eulerRhs_pairing A P hdiv hA hP w]
  calc
    _ ≤ |⟪(transportCommutator A A w).toLp,(wordField A w).toLp⟫_ℝ| := neg_le_abs _
    _ ≤ ‖(transportCommutator A A w).toLp‖*‖(wordField A w).toLp‖ := abs_real_inner_le_norm _ _
    _ ≤ (27*(2 : ℝ)^n*K*X)*X :=
      mul_le_mul hb' (hN n hn w) (norm_nonneg _) (by positivity)
    _ = 27*(2 : ℝ)^n*K*wordEnergy 3 A := by rw [← hx]; ring

theorem h3_energy_gradient (A P : SmoothL2Field Space) (K : ℝ)
    (hK : ∀ x, ‖fderiv ℝ A.field x‖ ≤ K) (hdiv : ∀ x, divergence A.field x = 0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    integerEnergyProduction 3 A (eulerRhs A P) ≤
      gradientEnergyConstant*K*wordEnergy 3 A := by
  have hs : (∑ n ∈ range 4, ∑ w : Fin n → Fin 3,
      ⟪(wordField A w).toLp,(wordField (eulerRhs A P) w).toLp⟫_ℝ) ≤
        ∑ n ∈ range 4, (3 : ℝ)^n*(27*(2 : ℝ)^n*K*wordEnergy 3 A) := by
    apply sum_le_sum
    intro n hn
    calc
      _ ≤ ∑ _w : Fin n → Fin 3, 27*(2 : ℝ)^n*K*wordEnergy 3 A :=
        sum_le_sum (fun w _ => eulerRhs_word_gradient A P K hK hdiv hA hP
          (by have := mem_range.mp hn; omega) w)
      _ = _ := by simp
  have hp (n : ℕ) : (3 : ℝ)^n*(27*(2 : ℝ)^n*K*wordEnergy 3 A) =
      (6 : ℝ)^n*(27*K*wordEnergy 3 A) := by
    rw [show (6 : ℝ)=3*2 by norm_num,mul_pow]
    ring
  simp_rw [hp] at hs
  rw [← sum_mul] at hs
  exact (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    (by unfold gradientEnergyConstant; ring)

end EulerOrdinarySobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerMeanSobolevBoundedField EulerVolterraConvolution EulerContinuousTimeIntegral

variable {T : ℝ} {hT : 0 ≤ T}

/-- Gradient norm path as an element of `C(Icc (0 : ℝ) T,ℝ)`. -/
def gradientNormPath (U : Evolution T hT) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => ‖finiteField (U.velocity t).derivative‖,
    (continuous_finiteField (fun t => (U.velocity t).derivative)
      (continuous_jetLp_derivative U.velocity U.velocity_continuous)).norm⟩

theorem gradientNormPath_nonneg (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    0 ≤ U.gradientNormPath t := by
  change 0 ≤ ‖finiteField (U.velocity t).derivative‖
  exact norm_nonneg _

theorem gradientNormPath_le_iff (U : Evolution T hT) (t : Icc (0 : ℝ) T) (K : ℝ) :
    U.gradientNormPath t ≤ K ↔ ∀ x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K := by
  change ‖finiteField (U.velocity t).derivative‖ ≤ K ↔ _
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply]
  rfl

theorem pointwise_gradient_le (U : Evolution T hT) (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ (U.velocity t).field x‖ ≤ U.gradientNormPath t :=
  (U.gradientNormPath_le_iff t _).mp le_rfl x

/-- Gradient integral, given by `realIntegral T hT U.gradientNormPath t`. -/
def gradientIntegral (U : Evolution T hT) (t : Icc (0 : ℝ) T) : ℝ :=
  realIntegral T hT U.gradientNormPath t

theorem gradientIntegral_nonneg (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    0 ≤ U.gradientIntegral t :=
  intervalIntegral.integral_nonneg_of_forall t.property.1
    (fun r => U.gradientNormPath_nonneg (projIcc 0 T hT r))

theorem gradientIntegral_le_const (U : Evolution T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    U.gradientIntegral t ≤ K*(t : ℝ) := by
  have hc := extendPath_continuous T hT U.gradientNormPath
  calc
    _ ≤ ∫ _r in (0 : ℝ)..(t : ℝ), K :=
      intervalIntegral.integral_mono_on t.property.1 (hc.intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t) (fun r _ =>
          (U.gradientNormPath_le_iff (projIcc 0 T hT r) K).mpr (hK _))
    _ = _ := by simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]; ring

theorem integerEnergyDerivative_gradient (U : Evolution T hT) (K : ℝ)
    (t : Icc (0 : ℝ) T) (hK : ∀ x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) :
    U.integerEnergyDerivative 3 t ≤ gradientEnergyConstant*K*U.integerEnergyPath 3 t := by
  rw [integerEnergyDerivative,derivative_eq_eulerRhs]
  apply h3_energy_gradient _ _ K hK _ (U.solenoidal t) (U.gradient t)
  exact solenoidal_representative_divergence _ (U.solenoidal t) _ (U.velocity t).smooth
    (U.velocity t).toLp_ae

theorem h3_energy_gradientIntegral (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    wordEnergy 3 (U.velocity t) ≤ wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩) *
      Real.exp (gradientEnergyConstant*U.gradientIntegral t) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.integerEnergyPath 3))
        (U.integerEnergyDerivative 3 (projIcc 0 T hT r)) (Icc 0 T) r := by
    have h := U.integerEnergy_hasDerivWithinAt 3 ⟨r,hr.1,hr.2.le⟩
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1,hr.2.le⟩)] using h
  have hb (r : ℝ) (_hr : r ∈ Ico 0 T) :
      U.integerEnergyDerivative 3 (projIcc 0 T hT r) ≤
        gradientEnergyConstant*extendPath T hT U.gradientNormPath r *
          extendPath T hT (U.integerEnergyPath 3) r :=
    U.integerEnergyDerivative_gradient _ _ (U.pointwise_gradient_le _)
  have h := variable_linear_stability T hT
    (extendPath T hT (U.integerEnergyPath 3))
    (fun r => U.integerEnergyDerivative 3 (projIcc 0 T hT r))
    gradientEnergyConstant U.gradientNormPath
    ((U.integerEnergyPath 3).continuous.comp continuous_projIcc).continuousOn hd hb t
  simpa only [extendPath,projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    integerEnergyPath,ContinuousMap.coe_mk,gradientIntegral] using h

theorem h3_energy_gradient_bound (U : Evolution T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    wordEnergy 3 (U.velocity t) ≤ wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩) *
      Real.exp (gradientEnergyConstant*K*(t : ℝ)) := by
  apply (U.h3_energy_gradientIntegral t).trans
  apply mul_le_mul_of_nonneg_left _ (wordEnergy_nonneg _ _)
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left (U.gradientIntegral_le_const K hK t)
    gradientEnergyConstant_nonneg).trans_eq (by ring)

/-- Gradient H3 bound, given by `Real.sqrt (wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩)*Real.exp
(gradientEnergyConstant*G))`. -/
def gradientH3Bound (U : Evolution T hT) (G : ℝ) : ℝ :=
  Real.sqrt (wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩)*Real.exp (gradientEnergyConstant*G))

theorem wordBound_of_gradientIntegral (U : Evolution T hT) (G : ℝ)
    (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    WordBound 3 (U.gradientH3Bound G) (U.velocity t) := by
  intro n hn w
  apply (wordBound_sqrt_energy 3 (U.velocity t) n hn w).trans
  apply Real.sqrt_le_sqrt
  exact (U.h3_energy_gradientIntegral t).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hG t) gradientEnergyConstant_nonneg))
      (wordEnergy_nonneg _ _))

theorem h3_tensorNorm_of_gradientIntegral (U : Evolution T hT) (G : ℝ)
    (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    tensorNorm 3 (U.velocity t) ≤ wordCount 3*U.gradientH3Bound G :=
  tensorNorm_le_wordCount _ 3 _ (U.wordBound_of_gradientIntegral G hG t)

theorem higher_energy_of_gradientIntegral (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (G : ℝ) (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩) *
      Real.exp (tameEnergyConstant m*U.gradientH3Bound G*T) :=
  U.integer_energy_uniform m hm _ (U.wordBound_of_gradientIntegral G hG) t

theorem higher_tensorNorm_of_gradientIntegral (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (G : ℝ) (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    tensorNorm m (U.velocity t) ≤ wordCount m *
      Real.sqrt (wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩) *
        Real.exp (tameEnergyConstant m*U.gradientH3Bound G*T)) :=
  U.tensorNorm_uniform m hm _ (U.wordBound_of_gradientIntegral G hG) t

theorem higher_tensorNorm_of_gradientBound (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (K : ℝ) (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K)
    (t : Icc (0 : ℝ) T) :
    tensorNorm m (U.velocity t) ≤ wordCount m *
      Real.sqrt (wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩) *
        Real.exp (tameEnergyConstant m*U.gradientH3Bound (K*T)*T)) := by
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ (U.velocity t).field 0)).trans (hK t 0)
  exact U.higher_tensorNorm_of_gradientIntegral m hm (K*T)
    (fun s => (U.gradientIntegral_le_const K hK s).trans
      (mul_le_mul_of_nonneg_left s.property.2 hK0)) t

end EulerOrdinarySobolev.Evolution
