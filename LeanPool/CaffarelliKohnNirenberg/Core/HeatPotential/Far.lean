/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.MorreySources
public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Campanato
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Far

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric
open Filter


noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem measurable_heatPotentialKernel_translate (w : ParabolicPoint) :
    Measurable (fun v : ParabolicPoint => heatPotentialKernel w v) := by
  rw [show (fun v : ParabolicPoint => heatPotentialKernel w v) =
      (fun v => heatKernel (w.1 - v.1) (w.2 - v.2)) by
      funext v
      unfold heatPotentialKernel pointSub
      exact heatKernelPlus_eq_heatKernel _]
  unfold heatKernel
  apply Measurable.ite
  · measurability
  · measurability
  · exact measurable_const

private lemma coord_fderiv_heatKernel {x : Vec3} {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    (fderiv ℝ (fun y : Vec3 => heatKernel y t) x) (CKN.basisVec i) =
      heatKernelSpaceDerivative x t i := by
  have hdiff : DifferentiableAt ℝ (fun y : Vec3 => heatKernel y t) x := by
    rw [show (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, y j ^ 2) / (4 * t)) by
      funext y
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  have hcomp := HasFDerivAt.comp (x i)
    (by simpa only [Function.update_eq_self] using hdiff.hasFDerivAt)
    (hasFDerivAt_update (𝕜 := ℝ) (i := i) x (x i))
  have hderiv := hcomp.hasDerivAt
  have hderiv' : HasDerivAt (fun s : ℝ => heatKernel (Function.update x i s) t)
      ((fderiv ℝ (fun y : Vec3 => heatKernel y t) x ∘SL
        ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1) (x i) := by
    simpa only [Function.comp_def] using hderiv
  have hval := hderiv'.deriv
  have hb : ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1 =
      CKN.basisVec i := by
    ext j
    by_cases hji : j = i <;> simp [CKN.basisVec, hji]
  calc
    (fderiv ℝ (fun y : Vec3 => heatKernel y t) x) (CKN.basisVec i) =
        (fderiv ℝ (fun y : Vec3 => heatKernel y t) x ∘SL
          ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1 := by
      rw [show (fderiv ℝ (fun y : Vec3 => heatKernel y t) x ∘SL
          ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1 =
          (fderiv ℝ (fun y : Vec3 => heatKernel y t) x) (ContinuousLinearMap.pi
            (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1) by rfl, hb]
    _ = deriv (fun s : ℝ => heatKernel (Function.update x i s) t) (x i) := hval.symm
    _ = heatKernelSpaceDerivative x t i := heatKernel_space_deriv ht i
theorem heatKernel_fderiv_bound {x : Vec3} {t R : ℝ} (ht : 0 < t)
    (hR : 0 < R) (hsep : R ≤ rhoTwo x t) :
    ‖fderiv ℝ (fun y : Vec3 => heatKernel y t) x‖ ≤ 900000 / R ^ 4 := by
  rw [CKN.opNorm_eq_sum_abs_basis]
  calc
    ∑ i, |(fderiv ℝ (fun y : Vec3 => heatKernel y t) x) (CKN.basisVec i)| =
        ∑ i, |heatKernelSpaceDerivative x t i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coord_fderiv_heatKernel ht i]
    _ ≤ ∑ _i : Fin 3, 300000 / R ^ 4 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := heatKernelSpaceDerivative_abs_le_rho_inv_four
        (x := x) (t := t) ht i
      exact h.trans (by gcongr)
    _ = 900000 / R ^ 4 := by norm_num; ring

private lemma heatPotential_exp_poly_bound {k : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    a ^ k * Real.exp (-a) ≤ (k.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp a ha k
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hmul : a ^ k ≤ Real.exp a * (k.factorial : ℝ) := by
    exact (div_le_iff₀ hfac).mp h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos a)).2
  calc
    a ^ k ≤ Real.exp a * (k.factorial : ℝ) := hmul
    _ = (k.factorial : ℝ) * Real.exp a := by ring

private lemma heatPotential_one_add_pow_exp_neg_le {n : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    (1 + a) ^ n * Real.exp (-a) ≤
      (2 : ℝ) ^ (n - 1) * (1 + (n.factorial : ℝ)) := by
  have hp := add_pow_le (zero_le_one : (0 : ℝ) ≤ 1) ha n
  have h0 : Real.exp (-a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr ha
  have hn' := heatPotential_exp_poly_bound (k := n) ha
  have hsum : (1 + a ^ n) * Real.exp (-a) ≤
      1 + (n.factorial : ℝ) := by
    calc
      (1 + a ^ n) * Real.exp (-a) = Real.exp (-a) + a ^ n * Real.exp (-a) := by ring
      _ ≤ 1 + (n.factorial : ℝ) := add_le_add h0 hn'
  have hp' : (1 + a) ^ n ≤ 2 ^ (n - 1) * (1 + a ^ n) := by
    simpa only [one_pow] using hp
  calc
    (1 + a) ^ n * Real.exp (-a) ≤
        2 ^ (n - 1) * (1 + a ^ n) * Real.exp (-a) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_nonneg _)
    _ = 2 ^ (n - 1) * ((1 + a ^ n) * Real.exp (-a)) := by ring
    _ ≤ 2 ^ (n - 1) * (1 + (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)

private lemma heatPotential_heat_prefactor_le {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) ≤ (Real.sqrt t) ^ (-(3 : ℝ)) := by
  have hbase : t ≤ 4 * Real.pi * t := by
    have hpi : (1 : ℝ) ≤ 4 * Real.pi := by
      nlinarith only [Real.two_le_pi]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi ht.le
  have hpow : t ^ ((3 : ℝ) / 2) ≤ (4 * Real.pi * t) ^ ((3 : ℝ) / 2) := by
    exact Real.rpow_le_rpow ht.le hbase (by positivity)
  have hsqrt : (Real.sqrt t) ^ (3 : ℕ) = t ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  calc
    (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) =
        ((4 * Real.pi * t) ^ ((3 : ℝ) / 2))⁻¹ := by
      rw [show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
        Real.rpow_neg (by positivity)]
    _ ≤ (t ^ ((3 : ℝ) / 2))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
    _ = (Real.sqrt t) ^ (-(3 : ℝ)) := by
      rw [← hsqrt, Real.rpow_neg (by positivity)]
      exact congrArg Inv.inv (Real.rpow_natCast (Real.sqrt t) 3).symm

private lemma heatPotential_heat_rpow_neg_three (z : ℝ) (hz : 0 < z) :
    z ^ (-(3 : ℝ)) = (z ^ (3 : ℕ))⁻¹ := by
  rw [Real.rpow_neg hz.le]
  exact congrArg Inv.inv (Real.rpow_natCast z 3)

private lemma heatPotential_mixed_deriv_formula {x : Vec3} {t : ℝ} (ht : 0 < t)
    (i j : Fin 3) :
    deriv (fun s : ℝ => heatKernelSpaceDerivative (Function.update x j s) t i)
      (x j) = heatKernelSpaceMixedSecondDerivative x t i j := by
  have hg : HasDerivAt (fun s : ℝ => heatKernel (Function.update x j s) t)
      (heatKernelSpaceDerivative x t j) (x j) := by
    have houter : DifferentiableAt ℝ
        (fun y : Vec3 => heatKernel y t) (Function.update x j (x j)) := by
      rw [show (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
          (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ k, y k ^ 2) / (4 * t)) by
          funext y
          rw [heatKernel_eq_formula_sum ht]]
      fun_prop (disch := positivity)
    have hinner := hasFDerivAt_update (𝕜 := ℝ) (i := j) x (x j)
    have hd := (houter.hasFDerivAt.comp (x j) hinner).differentiableAt
    have hd' : DifferentiableAt ℝ
        (fun s : ℝ => heatKernel (Function.update x j s) t) (x j) := by
      simpa only [Function.comp_def] using hd
    have hg' := hd'.hasDerivAt
    rw [heatKernel_space_deriv ht j] at hg'
    exact hg'
  have ha : HasDerivAt (fun s : ℝ => Function.update x j s i)
      (if i = j then 1 else 0) (x j) := by
    by_cases hij : i = j
    · subst i
      have heq : (fun s : ℝ => Function.update x j s j) = fun s => s := by
        funext s
        simp
      rw [heq]
      rw [ite_eq_left (rfl : j = j)]
      exact hasDerivAt_id' (x j)
    · have heq : (fun s : ℝ => Function.update x j s i) = fun _ : ℝ => x i := by
        funext s
        simp [hij]
      rw [heq]
      rw [ite_eq_right hij]
      exact hasDerivAt_const (x j) (x i)
  have hc := (ha.const_mul (-1 / (2 * t))).mul hg
  have heq : (fun s => heatKernelSpaceDerivative
      (Function.update x j s) t i) =
      (fun s => -(Function.update x j s i) / (2 * t) *
        heatKernel (Function.update x j s) t) := by
    funext s
    rw [heatKernelSpaceDerivative, ite_eq_left ht]
  rw [heq]
  have hc' : deriv (fun s : ℝ => -Function.update x j s i / (2 * t) *
      heatKernel (Function.update x j s) t) (x j) =
      (-1 / (2 * t) * (if i = j then 1 else 0) * heatKernel (Function.update x j (x j)) t +
        -1 / (2 * t) * Function.update x j (x j) i * heatKernelSpaceDerivative x t j) := by
    have hfun : (fun s : ℝ => -Function.update x j s i / (2 * t) *
        heatKernel (Function.update x j s) t) =
        ((fun y => -1 / (2 * t) * Function.update x j y i) *
          (fun s => heatKernel (Function.update x j s) t)) := by
      funext s
      dsimp
      ring
    rw [hfun]
    exact hc.deriv
  rw [hc']
  rw [heatKernelSpaceMixedSecondDerivative, ite_eq_left ht]
  rw [heatKernel_eq_formula_sum ht]
  have hupd : Function.update x j (x j) = x := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [hkj]
  rw [hupd]
  rw [heatKernelSpaceDerivative, ite_eq_left ht, heatKernel_eq_formula_sum ht]
  by_cases hij : i = j
  · subst i
    rw [ite_eq_left (rfl : j = j)]
    simp
    field_simp [ht.ne']
    ring
  · rw [ite_eq_right hij]
    simp [hij]
    field_simp [ht.ne']
    ring

private lemma heatPotential_coord_fderiv_eq_deriv_update {f : Vec3 → ℝ} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    (fderiv ℝ f x) (CKN.basisVec i) =
      deriv (fun s => f (Function.update x i s)) (x i) := by
  have hcomp := HasFDerivAt.comp (x i)
    (by simpa only [Function.update_eq_self] using hf.hasFDerivAt)
    (hasFDerivAt_update (𝕜 := ℝ) (i := i) x (x i))
  have hderiv := hcomp.hasDerivAt
  have hderiv' : HasDerivAt (fun s : ℝ => f (Function.update x i s))
      ((fderiv ℝ f x ∘SL
        ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1) (x i) := by
    simpa only [Function.comp_def] using hderiv
  rw [hderiv'.deriv]
  have hb : ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1 =
      CKN.basisVec i := by
    ext j
    by_cases hji : j = i <;> simp [CKN.basisVec, hji]
  rw [show (fderiv ℝ f x ∘SL
      ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ))) 1 =
      (fderiv ℝ f x) (ContinuousLinearMap.pi
      (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) 1) by rfl, hb]

private lemma heatKernelSpaceMixedSecondDerivative_abs_le_rho_inv_five
    {x : Vec3} {t : ℝ} (ht : 0 < t) (i j : Fin 3) :
    |heatKernelSpaceMixedSecondDerivative x t i j| ≤
      20000000 / rhoTwo x t ^ 5 := by
  let s : ℝ := vec3EuclideanNorm x
  let z : ℝ := Real.sqrt t
  let a : ℝ := (∑ k, x k ^ 2) / (4 * t)
  let u : ℝ := s / z
  have hs : 0 ≤ s := vec3EuclideanNorm_nonneg x
  have hz : 0 < z := Real.sqrt_pos.2 ht
  have htz : z ^ 2 = t := Real.sq_sqrt ht.le
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hu : 0 ≤ u := by
    dsimp [u]
    positivity
  have hsu : s = z * u := by
    dsimp [u]
    field_simp
  have hua : u ^ 2 = 4 * a := by
    dsimp [u, a, s]
    rw [div_pow, vec3EuclideanNorm_sq, htz]
    field_simp [htz]
  have h1u : 1 + u ≤ 3 * (1 + a) := by
    have hu_le : u ≤ 2 * (1 + a) := by
      nlinarith only [hua, sq_nonneg (u - 1)]
    nlinarith only [ha, hu_le]
  have hG : heatKernel x t ≤ z ^ (-(3 : ℝ)) * Real.exp (-a) := by
    rw [heatKernel_eq_formula_sum ht]
    have harg : -(∑ k, x k ^ 2) / (4 * t) = -a := by
      dsimp [a]
      ring
    rw [harg]
    exact mul_le_mul_of_nonneg_right
      (heatPotential_heat_prefactor_le ht) (Real.exp_nonneg _)
  have hrho : rhoTwo x t = z * (1 + u) := by
    change s + z = z * (1 + u)
    rw [hsu]
    ring
  have hcomp :
      |heatKernelSpaceMixedSecondDerivative x t i j| ≤
        heatKernel x t * ((a + (1 : ℝ) / 2) / t) := by
    rw [heatKernelSpaceMixedSecondDerivative, ite_eq_left ht, abs_mul,
      abs_of_nonneg (heatKernel_nonneg x t)]
    have hcomponent : ∀ k : Fin 3, |x k| ≤ s := by
      intro k
      dsimp [s]
      unfold vec3EuclideanNorm
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum
        (fun q _hq => sq_nonneg (x q)) (Finset.mem_univ k)
    have hxi : |x i| ≤ s := hcomponent i
    have hxj : |x j| ≤ s := hcomponent j
    have hprod : |x i * x j / (4 * t ^ 2)| ≤ s ^ 2 / (4 * t ^ 2) := by
      rw [abs_div, abs_of_pos (by positivity : 0 < (4 * t ^ 2 : ℝ)), abs_mul]
      apply div_le_div_of_nonneg_right
      calc
        |x i| * |x j| ≤ s * s := mul_le_mul hxi hxj (abs_nonneg _) hs
        _ = s ^ 2 := by ring
      positivity
    have hdiag : |(if i = j then (1 : ℝ) / (2 * t) else 0)| ≤
        (1 : ℝ) / (2 * t) := by
      split_ifs
      · rw [abs_of_pos (by positivity)]
      · simp
        positivity
    calc
      |x i * x j / (4 * t ^ 2) - (if i = j then (1 : ℝ) / (2 * t) else 0)| *
          heatKernel x t ≤
        (|x i * x j / (4 * t ^ 2)| +
          |(if i = j then (1 : ℝ) / (2 * t) else 0)|) * heatKernel x t := by
        exact mul_le_mul_of_nonneg_right (abs_sub _ _)
          (heatKernel_nonneg x t)
      _ ≤ (s ^ 2 / (4 * t ^ 2) + (1 : ℝ) / (2 * t)) * heatKernel x t := by
        exact mul_le_mul_of_nonneg_right (add_le_add hprod hdiag)
          (heatKernel_nonneg x t)
      _ = heatKernel x t * ((a + (1 : ℝ) / 2) / t) := by
        dsimp [a, s]
        rw [vec3EuclideanNorm_sq]
        ring
  have hscaled : rhoTwo x t ^ 5 *
      |heatKernelSpaceMixedSecondDerivative x t i j| ≤
      (1 + u) ^ 5 * (1 + a) * Real.exp (-a) := by
    rw [hrho]
    calc
      (z * (1 + u)) ^ 5 *
          |heatKernelSpaceMixedSecondDerivative x t i j| ≤
          (z * (1 + u)) ^ 5 *
            (heatKernel x t * ((a + (1 : ℝ) / 2) / t)) :=
        mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ (z * (1 + u)) ^ 5 *
          ((z ^ (-(3 : ℝ)) * Real.exp (-a)) *
            ((a + (1 : ℝ) / 2) / t)) := by
        gcongr
      _ ≤ (1 + u) ^ 5 * (1 + a) * Real.exp (-a) := by
        have ha1 : a + (1 : ℝ) / 2 ≤ 1 + a := by nlinarith only
        rw [← htz, heatPotential_heat_rpow_neg_three z hz]
        field_simp [hz.ne']
        nlinarith only [ha1]
  have hscaled' : rhoTwo x t ^ 5 *
      |heatKernelSpaceMixedSecondDerivative x t i j| ≤
      3 * (3 * (1 + a)) ^ 5 * (1 + a) * Real.exp (-a) := by
    calc
      _ ≤ (1 + u) ^ 5 * (1 + a) * Real.exp (-a) := hscaled
      _ ≤ 3 * (3 * (1 + a)) ^ 5 * (1 + a) * Real.exp (-a) := by
        calc
          (1 + u) ^ 5 * (1 + a) * Real.exp (-a) ≤
              (3 * (1 + a)) ^ 5 * (1 + a) * Real.exp (-a) := by
            gcongr
          _ ≤ 3 * (3 * (1 + a)) ^ 5 * (1 + a) * Real.exp (-a) := by
            have hnonneg : 0 ≤ (3 * (1 + a)) ^ 5 *
                (1 + a) * Real.exp (-a) := by positivity
            nlinarith only [hnonneg]
  have hρ : 0 < rhoTwo x t := by
    unfold rhoTwo
    exact add_pos_of_nonneg_of_pos (vec3EuclideanNorm_nonneg _)
      (Real.sqrt_pos.2 ht)
  apply (le_div_iff₀ (pow_pos hρ 5)).2
  calc
    |heatKernelSpaceMixedSecondDerivative x t i j| * rhoTwo x t ^ 5 =
        rhoTwo x t ^ 5 * |heatKernelSpaceMixedSecondDerivative x t i j| := by ring
    _ ≤ 3 * (3 * (1 + a)) ^ 5 * (1 + a) * Real.exp (-a) := hscaled'
    _ ≤ 20000000 := by
      calc
        3 * (3 * (1 + a)) ^ 5 * (1 + a) * Real.exp (-a) =
            3 * 243 * ((1 + a) ^ 6 * Real.exp (-a)) := by ring
        _ ≤ 3 * 243 * ((2 : ℝ) ^ (6 - 1) *
            (1 + (Nat.factorial 6 : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (heatPotential_one_add_pow_exp_neg_le (n := 6) ha) (by positivity)
        _ ≤ 20000000 := by norm_num

private lemma heatPotential_spatial_fderiv_bound {x : Vec3} {t R : ℝ}
    (ht : 0 < t) (hR : 0 < R) (hsep : R ≤ rhoTwo x t) (i : Fin 3) :
    ‖fderiv ℝ (fun y : Vec3 => heatKernelSpaceDerivative y t i) x‖ ≤
      60000000 / R ^ 5 := by
  have hdiff : DifferentiableAt ℝ
      (fun y : Vec3 => heatKernelSpaceDerivative y t i) x := by
    rw [show (fun y : Vec3 => heatKernelSpaceDerivative y t i) =
        fun y : Vec3 => -(y i) / (2 * t) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ k, y k ^ 2) / (4 * t))) by
        funext y
        rw [heatKernelSpaceDerivative, ite_eq_left ht,
          heatKernel_eq_formula_sum ht]]
    fun_prop (disch := positivity)
  rw [CKN.opNorm_eq_sum_abs_basis]
  calc
    ∑ k, |(fderiv ℝ (fun y : Vec3 => heatKernelSpaceDerivative y t i) x)
        (CKN.basisVec k)| =
        ∑ k, |heatKernelSpaceMixedSecondDerivative x t i k| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [heatPotential_coord_fderiv_eq_deriv_update hdiff k,
        heatPotential_mixed_deriv_formula ht i k]
    _ ≤ ∑ _k : Fin 3, 20000000 / R ^ 5 := by
      apply Finset.sum_le_sum
      intro k hk
      exact (heatKernelSpaceMixedSecondDerivative_abs_le_rho_inv_five ht i k).trans
        (by gcongr)
    _ = 60000000 / R ^ 5 := by norm_num; ring

theorem heatPotential_spatial_derivative_kernel_difference_abs_le
    {i : Fin 3} {p p' v : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (ht : 0 < p.2 - v.2)
    (hsep : ∀ y ∈ segment ℝ p.1 p'.1,
      R ≤ rhoTwo (y - v.1) (p.2 - v.2)) :
    |heatPotentialSpatialKernel i p v -
        heatPotentialSpatialKernel i (p'.1, p.2) v| ≤
      (60000000 / R ^ 5) * vec3EuclideanNorm (p.1 - p'.1) := by
  let f : Vec3 → ℝ := fun y =>
    heatKernelSpaceDerivative (y - v.1) (p.2 - v.2) i
  have hf : ∀ y ∈ segment ℝ p.1 p'.1, DifferentiableAt ℝ f y := by
    intro y hy
    have hinner : HasFDerivAt (fun x : Vec3 => x - v.1)
        (ContinuousLinearMap.id ℝ Vec3) y := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) y).sub_const v.1
    have houter_diff : DifferentiableAt ℝ
        (fun x : Vec3 => heatKernelSpaceDerivative x (p.2 - v.2) i)
        (y - v.1) := by
      rw [show (fun x : Vec3 => heatKernelSpaceDerivative x (p.2 - v.2) i) =
          fun x : Vec3 => -(x i) / (2 * (p.2 - v.2)) *
            ((4 * Real.pi * (p.2 - v.2)) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(∑ k, x k ^ 2) / (4 * (p.2 - v.2)))) by
          funext x
          rw [heatKernelSpaceDerivative, ite_eq_left ht,
            heatKernel_eq_formula_sum ht]]
      fun_prop (disch := positivity)
    exact (houter_diff.hasFDerivAt.comp y hinner).differentiableAt
  have hbound : ∀ y ∈ segment ℝ p.1 p'.1,
      ‖fderiv ℝ f y‖ ≤ 60000000 / R ^ 5 := by
    intro y hy
    have hinner : HasFDerivAt (fun x : Vec3 => x - v.1)
        (ContinuousLinearMap.id ℝ Vec3) y := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) y).sub_const v.1
    have houter_diff : DifferentiableAt ℝ
        (fun x : Vec3 => heatKernelSpaceDerivative x (p.2 - v.2) i)
        (y - v.1) := by
      rw [show (fun x : Vec3 => heatKernelSpaceDerivative x (p.2 - v.2) i) =
          fun x : Vec3 => -(x i) / (2 * (p.2 - v.2)) *
            ((4 * Real.pi * (p.2 - v.2)) ^ (-(3 : ℝ) / 2) *
              Real.exp (-(∑ k, x k ^ 2) / (4 * (p.2 - v.2)))) by
          funext x
          rw [heatKernelSpaceDerivative, ite_eq_left ht,
            heatKernel_eq_formula_sum ht]]
      fun_prop (disch := positivity)
    have hcomp := houter_diff.hasFDerivAt.comp y hinner
    rw [show f = fun y =>
        heatKernelSpaceDerivative (y - v.1) (p.2 - v.2) i by rfl,
      show fderiv ℝ (fun y : Vec3 =>
        heatKernelSpaceDerivative (y - v.1) (p.2 - v.2) i) y =
        fderiv ℝ (fun x : Vec3 => heatKernelSpaceDerivative x
          (p.2 - v.2) i) (y - v.1) ∘L
          ContinuousLinearMap.id ℝ Vec3 by exact hcomp.fderiv]
    simpa using heatPotential_spatial_fderiv_bound ht hR (hsep y hy) i
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le hf hbound
    (convex_segment p.1 p'.1) (left_mem_segment ℝ p.1 p'.1)
      (right_mem_segment ℝ p.1 p'.1)
  have hmean' : |heatKernelSpaceDerivative (p.1 - v.1) (p.2 - v.2) i -
      heatKernelSpaceDerivative (p'.1 - v.1) (p.2 - v.2) i| ≤
      (60000000 / R ^ 5) * ‖p.1 - p'.1‖ := by
    simpa [f, Real.norm_eq_abs, norm_sub_rev, dist_eq_norm] using hmean
  have hnorm : ‖p.1 - p'.1‖ ≤ vec3EuclideanNorm (p.1 - p'.1) := by
    rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
    intro k
    change |(p.1 - p'.1) k| ≤ vec3EuclideanNorm (p.1 - p'.1)
    unfold vec3EuclideanNorm
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum
      (fun q _hq => sq_nonneg ((p.1 - p'.1) q)) (Finset.mem_univ k)
  have hcoef : 0 ≤ 60000000 / R ^ 5 := by positivity
  have hfinal := hmean'.trans
    (mul_le_mul_of_nonneg_left hnorm hcoef)
  simpa [heatPotentialSpatialKernel] using hfinal

theorem vec3_norm_le_euclidean_norm (x : Vec3) :
    ‖x‖ ≤ vec3EuclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (vec3EuclideanNorm_nonneg _)]
  intro i
  change |x i| ≤ vec3EuclideanNorm x
  unfold vec3EuclideanNorm
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum
    (fun j _hj => sq_nonneg (x j)) (Finset.mem_univ i)
theorem vec3EuclideanNorm_add_le (x y : Vec3) :
    vec3EuclideanNorm (x + y) ≤ vec3EuclideanNorm x + vec3EuclideanNorm y := by
  rw [vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2]
  simpa only [WithLp.toLp_add] using norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)
theorem parabolic_ball_segment_mem
    {z p p' y : ParabolicPoint} {r : ℝ}
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hy : y.1 ∈ segment ℝ p.1 p'.1) (hytime : y.2 = p.2) :
    y ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r := by
  rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp hp' ⊢
  have hps : vec3EuclideanNorm (p.1 - z.1) ≤ r :=
    (le_max_left _ _).trans hp
  have hps' : vec3EuclideanNorm (p'.1 - z.1) ≤ r :=
    (le_max_left _ _).trans hp'
  have hpt : Real.sqrt |p.2 - z.2| ≤ r := (le_max_right _ _).trans hp
  have hyt : Real.sqrt |y.2 - z.2| ≤ r := by simpa [hytime] using hpt
  rcases hy with ⟨a, b, ha, hb, hab, hy⟩
  have hspace : vec3EuclideanNorm (y.1 - z.1) ≤ r := by
    rw [← hy]
    have heq : a • p.1 + b • p'.1 - z.1 =
        a • (p.1 - z.1) + b • (p'.1 - z.1) := by
      rw [smul_sub, smul_sub]
      have hz : -(z.1) = (a + b) • (-(z.1)) := by
        rw [hab, one_smul]
      rw [sub_eq_add_neg, hz]
      module
    rw [heq]
    calc
      vec3EuclideanNorm (a • (p.1 - z.1) + b • (p'.1 - z.1)) ≤
          vec3EuclideanNorm (a • (p.1 - z.1)) +
            vec3EuclideanNorm (b • (p'.1 - z.1)) :=
        vec3EuclideanNorm_add_le _ _
      _ = a * vec3EuclideanNorm (p.1 - z.1) +
            b * vec3EuclideanNorm (p'.1 - z.1) := by
        rw [vec3EuclideanNorm_smul, vec3EuclideanNorm_smul,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * r + b * r := add_le_add
        (mul_le_mul_of_nonneg_left hps ha)
        (mul_le_mul_of_nonneg_left hps' hb)
      _ = r := by rw [← add_mul, hab, one_mul]
  exact max_le hspace hyt
theorem parabolic_ball_time_segment_mem
    {z p p' : ParabolicPoint} {x : Vec3} {r s : ℝ}
    (hr : 0 ≤ r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hx : vec3EuclideanNorm (x - z.1) ≤ r)
    (hs : s ∈ Set.Icc p.2 p'.2) :
    (let q : ParabolicPoint := (x, s); q) ∈
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r := by
  rw [Metric.mem_closedBall, dist_eq_parabolicDist] at hp hp'
  change dist (let q : ParabolicPoint := (x, s); q) z ≤ r
  rw [dist_eq_parabolicDist]
  have htp : Real.sqrt |p.2 - z.2| ≤ r := (le_max_right _ _).trans hp
  have htp' : Real.sqrt |p'.2 - z.2| ≤ r := (le_max_right _ _).trans hp'
  have habsp : |p.2 - z.2| ≤ r ^ 2 := by
    have hsq := Real.sq_sqrt (abs_nonneg (p.2 - z.2))
    nlinarith only [hsq, htp, hr, Real.sqrt_nonneg (|p.2 - z.2|)]
  have habsp' : |p'.2 - z.2| ≤ r ^ 2 := by
    have hsq := Real.sq_sqrt (abs_nonneg (p'.2 - z.2))
    nlinarith only [hsq, htp', hr, Real.sqrt_nonneg (|p'.2 - z.2|)]
  have hlow : -(r ^ 2) ≤ s - z.2 := by
    have hlowp : -(r ^ 2) ≤ p.2 - z.2 := (abs_le.mp habsp).1
    linarith only [hlowp, hs.1]
  have hhigh : s - z.2 ≤ r ^ 2 := by
    have hhighp : p'.2 - z.2 ≤ r ^ 2 := (abs_le.mp habsp').2
    linarith only [hhighp, hs.2]
  apply max_le hx
  rw [Real.sqrt_le_iff]
  exact ⟨hr, (abs_le.mpr ⟨hlow, hhigh⟩).trans_eq rfl⟩
/-! The source shells used by the far part start six dyadic scales outside the
    observation ball.  The larger gap makes the causal kernel separation
    uniform after moving the observation point inside its ball. -/
end CKN.Core.HeatPotential
