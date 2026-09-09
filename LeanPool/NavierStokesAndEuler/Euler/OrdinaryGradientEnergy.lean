/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryTameEnergy
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryGradientProducts

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
