/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Commutator
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Energy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTameProduct
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTransportCancellation
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordConstraints

/-! Integer-order Euler transport energy with a genuine H³ coefficient.
The pressure and top transport term cancel. All remaining products
are controlled by the proved L² interpolation of derivative words. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal Finset
open scoped ContDiff

theorem tame_advection_outer (A : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m) (M N : ℝ)
    (hM : WordBound 3 M A) (hN : WordBound m N A)
    {n k l : ℕ} (hk : 1 ≤ k) (horder : n + k + l ≤ m)
    (a : Fin n → Fin 3) (w : Fin k → Fin 3) (v : Fin l → Fin 3) :
    ‖(wordField (advectionField (wordField A w) (wordField A v)) a).toLp‖ ≤
      3*(2 : ℝ)^n*h3ProductConstant*M*N := by
  rw [advectionField,wordField_sum,toLp_sumField]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, (2 : ℝ)^n*h3ProductConstant*M*N := by
      apply sum_le_sum
      intro i _
      simpa only [wordField_cons] using tame_outer_product A m hm M N hM hN hk
        (by omega : 1 ≤ l+1) (by omega : n+k+(l+1) ≤ m+1) a w (Fin.cons i v) i
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem tame_transportCommutator_word (A : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m)
    (M N : ℝ) (hM : WordBound 3 M A) (hN : WordBound m N A)
    {n l : ℕ} (horder : n + l ≤ m) (a : Fin n → Fin 3) (v : Fin l → Fin 3) :
    ‖(transportCommutator A (wordField A v) a).toLp‖ ≤
      3*((2 : ℝ)^n-1)*h3ProductConstant*M*N := by
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
    have h1 := tame_advection_outer A m hm M N hM hN (by norm_num : 1 ≤ 1)
      (by omega : n+1+l ≤ m) (Fin.init a) (Fin.cons (a (Fin.last n)) Fin.elim0) v
    have h2 := ih (by omega : n+(l+1) ≤ m) (Fin.init a) (Fin.cons (a (Fin.last n)) v)
    simp only [wordField_cons,wordField_zero] at h1
    exact (add_le_add h1 h2).trans_eq (by rw [pow_succ]; ring)

theorem tame_transportCommutator (A : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m)
    (M N : ℝ) (hM : WordBound 3 M A) (hN : WordBound m N A)
    {n : ℕ} (hn : n ≤ m) (w : Fin n → Fin 3) :
    ‖(transportCommutator A A w).toLp‖ ≤
      3*((2 : ℝ)^n-1)*h3ProductConstant*M*N := by
  simpa only [wordField_zero] using tame_transportCommutator_word A m hm M N hM hN
    (by simpa only [Nat.add_zero] using hn) w Fin.elim0

/-- Euler rhs, given by `fieldNeg (addField (advectionField A A) P)`. -/
def eulerRhs (A P : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldNeg (addField (advectionField A A) P)

theorem eulerRhs_field (A P : SmoothL2Field Space) (x : Space) :
    (eulerRhs A P).field x = -fderiv ℝ A.field x (A.field x)-P.field x := by
  simp only [eulerRhs,fieldNeg_field,addField_field,advectionField_field]
  abel

theorem eulerRhs_pairing (A P : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    {n : ℕ} (w : Fin n → Fin 3) :
    ⟪(wordField A w).toLp,(wordField (eulerRhs A P) w).toLp⟫_ℝ =
      -⟪(transportCommutator A A w).toLp,(wordField A w).toLp⟫_ℝ := by
  have ht : ⟪(wordField A w).toLp,(wordField (advectionField A A) w).toLp⟫_ℝ =
      ⟪(transportCommutator A A w).toLp,(wordField A w).toLp⟫_ℝ := by
    rw [real_inner_comm,transportCommutator,toLp_fieldSub,inner_sub_left,
      advection_inner_zero A (wordField A w) hdiv,sub_zero]
  have hp : ⟪(wordField A w).toLp,(wordField P w).toLp⟫_ℝ=0 := by
    rw [real_inner_comm]
    exact word_pressure_pairing_zero P A hP hA w
  simp only [eulerRhs,wordField_neg,wordField_add,toLp_fieldNeg,toLp_addField,
    inner_neg_right,inner_add_right,ht,hp,add_zero]

/-- Tame energy constant, given by `6*h3ProductConstant*(∑ n ∈ range (m+1), (6 : ℝ)^n)`. -/
def tameEnergyConstant (m : ℕ) : ℝ :=
  6*h3ProductConstant*(∑ n ∈ range (m+1), (6 : ℝ)^n)

theorem tameEnergyConstant_nonneg (m : ℕ) : 0 ≤ tameEnergyConstant m :=
  mul_nonneg (mul_nonneg (by norm_num) h3ProductConstant_nonneg)
    (sum_nonneg (fun _ _ => by positivity))

/-- Integer energy production, given by `2*(∑ n ∈ range (m+1), ∑ w : Fin n → Fin 3, ⟪(wordField
A w).toLp,(wordField Q w).toLp⟫_ℝ)`. -/
def integerEnergyProduction (m : ℕ) (A Q : SmoothL2Field Space) : ℝ :=
  2*(∑ n ∈ range (m+1), ∑ w : Fin n → Fin 3,
    ⟪(wordField A w).toLp,(wordField Q w).toLp⟫_ℝ)

theorem eulerRhs_word_tame (A P : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : WordBound 3 M A) (hdiv : ∀ x, divergence A.field x = 0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace)
    {n : ℕ} (hn : n ≤ m) (w : Fin n → Fin 3) :
    ⟪(wordField A w).toLp,(wordField (eulerRhs A P) w).toLp⟫_ℝ ≤
      3*(2 : ℝ)^n*h3ProductConstant*M*wordEnergy m A := by
  let X := Real.sqrt (wordEnergy m A)
  have hx : X^2=wordEnergy m A := Real.sq_sqrt (wordEnergy_nonneg m A)
  have hN : WordBound m X A := wordBound_sqrt_energy m A
  have hb := tame_transportCommutator A m hm M X hM hN hn w
  have hM0 := wordBound_nonneg hM
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hc := h3ProductConstant_nonneg
  have hb' : ‖(transportCommutator A A w).toLp‖ ≤ 3*(2 : ℝ)^n*h3ProductConstant*M*X := by
    apply hb.trans
    have hcoef : 3*((2 : ℝ)^n-1) ≤ 3*(2 : ℝ)^n := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef hc) hM0) hX
  rw [eulerRhs_pairing A P hdiv hA hP w]
  calc
    _ ≤ |⟪(transportCommutator A A w).toLp,(wordField A w).toLp⟫_ℝ| := neg_le_abs _
    _ ≤ ‖(transportCommutator A A w).toLp‖*‖(wordField A w).toLp‖ := abs_real_inner_le_norm _ _
    _ ≤ (3*(2 : ℝ)^n*h3ProductConstant*M*X)*X :=
      mul_le_mul hb' (hN n hn w) (norm_nonneg _) (by positivity)
    _ = 3*(2 : ℝ)^n*h3ProductConstant*M*wordEnergy m A := by rw [← hx]; ring

theorem integer_energy_tame (A P : SmoothL2Field Space) (m : ℕ) (hm : 3 ≤ m)
    (M : ℝ) (hM : WordBound 3 M A) (hdiv : ∀ x, divergence A.field x = 0)
    (hA : A.toLp ∈ solenoidalSpace) (hP : P.toLp ∈ gradientSpace) :
    integerEnergyProduction m A (eulerRhs A P) ≤ tameEnergyConstant m*M*wordEnergy m A := by
  have hs : (∑ n ∈ range (m+1), ∑ w : Fin n → Fin 3,
      ⟪(wordField A w).toLp,(wordField (eulerRhs A P) w).toLp⟫_ℝ) ≤
        ∑ n ∈ range (m+1), (3 : ℝ)^n*(3*(2 : ℝ)^n*h3ProductConstant*M*wordEnergy m A) := by
    apply sum_le_sum
    intro n hn
    calc
      _ ≤ ∑ _w : Fin n → Fin 3, 3*(2 : ℝ)^n*h3ProductConstant*M*wordEnergy m A :=
        sum_le_sum (fun w _ => eulerRhs_word_tame A P m hm M hM hdiv hA hP
          (by have := mem_range.mp hn; omega) w)
      _ = _ := by simp
  have hp (n : ℕ) : (3 : ℝ)^n*(3*(2 : ℝ)^n*h3ProductConstant*M*wordEnergy m A) =
      (6 : ℝ)^n*(3*h3ProductConstant*M*wordEnergy m A) := by
    rw [show (6 : ℝ)=3*2 by norm_num,mul_pow]
    ring
  simp_rw [hp] at hs
  rw [← sum_mul] at hs
  exact (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    (by unfold tameEnergyConstant; ring)

end EulerOrdinarySobolev
