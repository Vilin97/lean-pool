/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.HeatPotential.Far

/-!
# Far Shell

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric
open Filter


noncomputable section

namespace CKN.Core.HeatPotential

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey

theorem measurable_heatPotentialSpatialKernel_translate (i : Fin 3) (w : ParabolicPoint) :
    Measurable (fun v : ParabolicPoint => heatPotentialSpatialKernel i w v) := by
  unfold heatPotentialSpatialKernel
  unfold heatKernelSpaceDerivative
  apply Measurable.ite
  · measurability
  · have hheat : Measurable (fun v : ParabolicPoint =>
        heatKernel (w.1 - v.1) (w.2 - v.2)) := by
      unfold heatKernel
      apply Measurable.ite
      · measurability
      · measurability
      · exact measurable_const
    have hcoef : Measurable (fun v : ParabolicPoint =>
        -(w.1 - v.1) i / (2 * (w.2 - v.2))) := by
      measurability
    exact hcoef.mul hheat
  · exact measurable_const

/-- Far parabolic shell with the six-scale separation used in heat-kernel difference estimates. -/
@[expose] def heatPotentialFarShellSet (z : ParabolicPoint) (r : ℝ) (j : ℕ) :
    Set ParabolicPoint :=
  parabolicRieszShell r (j + 6 : ℤ) z
theorem measurableSet_heatPotentialFarShellSet (z : ParabolicPoint) (r : ℝ)
    (j : ℕ) : MeasurableSet (heatPotentialFarShellSet z r j) := by
  exact measurableSet_parabolicRieszShell r (j + 6 : ℤ) z
theorem heatPotential_far_shell_source_l1_bound
    {F : ParabolicPoint → ℝ} {z : ParabolicPoint} {r P θ : ℝ}
    (hr : 0 < r) (hP : 1 ≤ P) (hPθ : P ≤ θ)
    (hF : AEMeasurable F volume) (j : ℕ) :
    (∫⁻ w in heatPotentialFarShellSet z r j, ENNReal.ofReal |F w|) ≤
      (ENNReal.ofReal
          (2 * ((2 : ℝ) ^ (((j + 6 : ℤ) : ℝ) + 1) * r))) ^
          (5 * (1 - 1 / θ)) *
        (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P) *
        morreyNorm P θ F := by
  unfold heatPotentialFarShellSet
  exact heatPotential_shell_source_l1_bound (z := z) hr hP hPθ hF
    (j + 6 : ℤ)



private lemma parabolicRho₂_symm (z w : ParabolicPoint) :
    parabolicRho₂ z w = parabolicRho₂ w z := by
  unfold parabolicRho₂
  rw [abs_sub_comm]
  congr 1
  have hneg : z.1 - w.1 = -(w.1 - z.1) := by abel
  calc
    vec3EuclideanNorm (z.1 - w.1) =
        vec3EuclideanNorm (-(w.1 - z.1)) := by rw [hneg]
    _ = vec3EuclideanNorm (w.1 - z.1) := by
      unfold vec3EuclideanNorm
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      change (-(w.1 i - z.1 i)) ^ 2 = (w.1 i - z.1 i) ^ 2
      ring

private lemma parabolicRho₂_le_two_parabolicDist (z w : ParabolicPoint) :
    parabolicRho₂ z w ≤ 2 * parabolicDist z w := by
  unfold parabolicRho₂ parabolicDist
  have hs : vec3EuclideanNorm (z.1 - w.1) ≤
      max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
    le_max_left _ _
  have ht : Real.sqrt |z.2 - w.2| ≤
      max (vec3EuclideanNorm (z.1 - w.1)) (Real.sqrt |z.2 - w.2|) :=
    le_max_right _ _
  linarith only [hs, ht]

private lemma parabolicRho₂_quasi_triangle (a b c : ParabolicPoint) :
    parabolicRho₂ a c ≤
      2 * parabolicRho₂ a b + 2 * parabolicRho₂ b c := by
  have hdist : parabolicDist a c ≤ parabolicDist a b + parabolicDist b c := by
    rw [← dist_eq_parabolicDist a c, ← dist_eq_parabolicDist a b,
      ← dist_eq_parabolicDist b c]
    exact dist_triangle _ _ _
  have hab : parabolicDist a b ≤ parabolicRho₂ a b :=
    parabolicDist_le_parabolicRho₂ _ _
  have hbc : parabolicDist b c ≤ parabolicRho₂ b c :=
    parabolicDist_le_parabolicRho₂ _ _
  calc
    parabolicRho₂ a c ≤ 2 * parabolicDist a c :=
      parabolicRho₂_le_two_parabolicDist _ _
    _ ≤ 2 * (parabolicDist a b + parabolicDist b c) :=
      mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ = 2 * parabolicDist a b + 2 * parabolicDist b c := by ring
    _ ≤ 2 * parabolicRho₂ a b + 2 * parabolicRho₂ b c := by
      exact add_le_add (mul_le_mul_of_nonneg_left hab (by norm_num))
        (mul_le_mul_of_nonneg_left hbc (by norm_num))

theorem heatPotential_far_shell_kernel_separation
    {z w v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hw : w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    w.2 - v.2 ≤ 0 ∨
      (2 : ℝ) ^ ((j : ℝ) + 4) * r ≤
        rhoTwo (w.1 - v.1) (w.2 - v.2) := by
  by_cases ht : w.2 - v.2 ≤ 0
  · exact Or.inl ht
  · right
    have htpos : 0 < w.2 - v.2 := lt_of_not_ge ht
    have hdist : parabolicDist w z ≤ r := by
      rw [← dist_eq_parabolicDist]
      simpa [dist_comm] using hw
    have hrhowz : parabolicRho₂ w z ≤ 2 * r := by
      exact (parabolicRho₂_le_two_parabolicDist w z).trans
        (mul_le_mul_of_nonneg_left hdist (by norm_num))
    have hsource : (2 : ℝ) ^ ((j : ℝ) + 6) * r ≤
        parabolicRho₂ z v := by
      simpa [heatPotentialFarShellSet, Nat.cast_add, Int.cast_ofNat,
        add_assoc, add_comm, add_left_comm] using hv.1
    have hquasi := parabolicRho₂_quasi_triangle z w v
    have hlow : 2 ^ ((j : ℝ) + 5) * r - 2 * r ≤ parabolicRho₂ w v := by
      have hq : 2 * parabolicRho₂ z w + 2 * parabolicRho₂ w v ≥
          parabolicRho₂ z v := by linarith only [hquasi]
      have hsym : parabolicRho₂ z w = parabolicRho₂ w z :=
        parabolicRho₂_symm _ _
      have hq' : 2 * parabolicRho₂ w v ≥
          parabolicRho₂ z v - 2 * (2 * r) := by
        rw [hsym] at hq
        linarith only [hq, hrhowz]
      have hpow : 2 ^ ((j : ℝ) + 5) * r ≤ parabolicRho₂ z v / 2 := by
        have hpow' : 2 ^ ((j : ℝ) + 6) * r =
            2 * (2 ^ ((j : ℝ) + 5) * r) := by
          rw [show (j : ℝ) + 6 = ((j : ℝ) + 5) + 1 by ring,
            Real.rpow_add (by norm_num)]
          ring
        rw [hpow'] at hsource
        linarith only [hsource]
      linarith only [hq', hpow]
    rw [show rhoTwo (w.1 - v.1) (w.2 - v.2) = parabolicRho₂ w v by
      unfold rhoTwo parabolicRho₂
      rw [abs_of_pos htpos]
      exact add_comm _ _]
    have hpow : 2 ≤ (2 : ℝ) ^ ((j : ℝ) + 4) := by
      have hone : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num
      have hj : (1 : ℝ) ≤ (j : ℝ) + 4 := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith only [hj0]
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := hone.symm
        _ ≤ (2 : ℝ) ^ ((j : ℝ) + 4) :=
          Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hj
    have hrpow : 2 * r ≤ (2 : ℝ) ^ ((j : ℝ) + 4) * r :=
      mul_le_mul_of_nonneg_right hpow hr.le
    have hpow' : (2 : ℝ) ^ ((j : ℝ) + 5) =
        2 * ((2 : ℝ) ^ ((j : ℝ) + 4)) := by
      calc
        (2 : ℝ) ^ ((j : ℝ) + 5) =
            (2 : ℝ) ^ (((j : ℝ) + 4) + 1) := by congr 1; ring
        _ = (2 : ℝ) ^ ((j : ℝ) + 4) * (2 : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_add (by norm_num)]
        _ = 2 * ((2 : ℝ) ^ ((j : ℝ) + 4)) := by norm_num; ring
    rw [hpow'] at hlow
    linarith only [hlow, hrpow]
theorem heatPotential_far_shell_rho_separation
    {z w v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hw : w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    (2 : ℝ) ^ ((j : ℝ) + 4) * r ≤ parabolicRho₂ w v := by
  have hdist : parabolicDist w z ≤ r := by
    rw [← dist_eq_parabolicDist]
    simpa [dist_comm] using hw
  have hrhowz : parabolicRho₂ w z ≤ 2 * r := by
    exact (parabolicRho₂_le_two_parabolicDist w z).trans
      (mul_le_mul_of_nonneg_left hdist (by norm_num))
  have hsource : (2 : ℝ) ^ ((j : ℝ) + 6) * r ≤ parabolicRho₂ z v := by
    simpa [heatPotentialFarShellSet, Nat.cast_add, Int.cast_ofNat,
      add_assoc, add_comm, add_left_comm] using hv.1
  have hquasi := parabolicRho₂_quasi_triangle z w v
  have hq : 2 * parabolicRho₂ z w + 2 * parabolicRho₂ w v ≥
      parabolicRho₂ z v := by linarith only [hquasi]
  have hsym : parabolicRho₂ z w = parabolicRho₂ w z :=
    parabolicRho₂_symm _ _
  have hq' : 2 * parabolicRho₂ w v ≥
      parabolicRho₂ z v - 2 * (2 * r) := by
    rw [hsym] at hq
    linarith only [hq, hrhowz]
  have hpow : 2 ^ ((j : ℝ) + 5) * r ≤ parabolicRho₂ z v / 2 := by
    have hpow' : 2 ^ ((j : ℝ) + 6) * r =
        2 * (2 ^ ((j : ℝ) + 5) * r) := by
      rw [show (j : ℝ) + 6 = ((j : ℝ) + 5) + 1 by ring,
        Real.rpow_add (by norm_num)]
      ring
    rw [hpow'] at hsource
    linarith only [hsource]
  have hlow : 2 ^ ((j : ℝ) + 5) * r - 2 * r ≤ parabolicRho₂ w v := by
    linarith only [hq', hpow]
  have hpow2 : 2 ≤ (2 : ℝ) ^ ((j : ℝ) + 4) := by
    have hone : (2 : ℝ) ^ (1 : ℝ) = 2 := by norm_num
    have hj : (1 : ℝ) ≤ (j : ℝ) + 4 := by
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith only [hj0]
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := hone.symm
      _ ≤ (2 : ℝ) ^ ((j : ℝ) + 4) :=
        Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hj
  have hrpow : 2 * r ≤ (2 : ℝ) ^ ((j : ℝ) + 4) * r :=
    mul_le_mul_of_nonneg_right hpow2 hr.le
  have hpow' : (2 : ℝ) ^ ((j : ℝ) + 5) =
      2 * ((2 : ℝ) ^ ((j : ℝ) + 4)) := by
    calc
      (2 : ℝ) ^ ((j : ℝ) + 5) =
          (2 : ℝ) ^ (((j : ℝ) + 4) + 1) := by congr 1; ring
      _ = (2 : ℝ) ^ ((j : ℝ) + 4) * (2 : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_add (by norm_num)]
      _ = 2 * ((2 : ℝ) ^ ((j : ℝ) + 4)) := by norm_num; ring
  rw [hpow'] at hlow
  linarith only [hlow, hrpow]
theorem heatPotential_spatial_kernel_difference_abs_le
    {p p' v : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (ht : 0 < p.2 - v.2)
    (hsep : ∀ y ∈ segment ℝ p.1 p'.1,
      R ≤ rhoTwo (y - v.1) (p.2 - v.2)) :
    |heatPotentialKernel p v - heatPotentialKernel (p'.1, p.2) v| ≤
      (900000 / R ^ 4) * vec3EuclideanNorm (p.1 - p'.1) := by
  let f : Vec3 → ℝ := fun y => heatKernel (y - v.1) (p.2 - v.2)
  have hf : ∀ y ∈ segment ℝ p.1 p'.1, DifferentiableAt ℝ f y := by
    intro y hy
    have hinner : HasFDerivAt (fun x : Vec3 => x - v.1)
        (ContinuousLinearMap.id ℝ Vec3) y := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) y).sub_const v.1
    have houter_diff : DifferentiableAt ℝ
        (fun x : Vec3 => heatKernel x (p.2 - v.2)) (y - v.1) := by
      rw [show (fun x : Vec3 => heatKernel x (p.2 - v.2)) = fun x : Vec3 =>
          (4 * Real.pi * (p.2 - v.2)) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, x j ^ 2) / (4 * (p.2 - v.2))) by
        funext x
        exact heatKernel_eq_formula_sum ht]
      fun_prop (disch := positivity)
    exact (houter_diff.hasFDerivAt.comp y hinner).differentiableAt
  have hbound : ∀ y ∈ segment ℝ p.1 p'.1,
      ‖fderiv ℝ f y‖ ≤ 900000 / R ^ 4 := by
    intro y hy
    have hinner : HasFDerivAt (fun x : Vec3 => x - v.1)
        (ContinuousLinearMap.id ℝ Vec3) y := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) y).sub_const v.1
    have houter_diff : DifferentiableAt ℝ
        (fun x : Vec3 => heatKernel x (p.2 - v.2)) (y - v.1) := by
      rw [show (fun x : Vec3 => heatKernel x (p.2 - v.2)) = fun x : Vec3 =>
          (4 * Real.pi * (p.2 - v.2)) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, x j ^ 2) / (4 * (p.2 - v.2))) by
        funext x
        exact heatKernel_eq_formula_sum ht]
      fun_prop (disch := positivity)
    have hcomp := houter_diff.hasFDerivAt.comp y hinner
    rw [show f = fun y => heatKernel (y - v.1) (p.2 - v.2) by rfl,
      show fderiv ℝ (fun y : Vec3 => heatKernel (y - v.1) (p.2 - v.2)) y =
        fderiv ℝ (fun x : Vec3 => heatKernel x (p.2 - v.2)) (y - v.1) ∘L
          ContinuousLinearMap.id ℝ Vec3 by exact hcomp.fderiv]
    simpa using heatKernel_fderiv_bound ht hR (hsep y hy)
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le hf hbound
    (convex_segment p.1 p'.1) (left_mem_segment ℝ p.1 p'.1)
      (right_mem_segment ℝ p.1 p'.1)
  have hmean' : |heatKernel (p.1 - v.1) (p.2 - v.2) -
      heatKernel (p'.1 - v.1) (p.2 - v.2)| ≤
      (900000 / R ^ 4) * ‖p.1 - p'.1‖ := by
    simpa [f, Real.norm_eq_abs, norm_sub_rev, dist_eq_norm] using hmean
  have hnorm : ‖p.1 - p'.1‖ ≤ vec3EuclideanNorm (p.1 - p'.1) :=
    vec3_norm_le_euclidean_norm _
  have hcoef : 0 ≤ 900000 / R ^ 4 := by positivity
  have hfinal := hmean'.trans
    (mul_le_mul_of_nonneg_left hnorm hcoef)
  simpa [heatPotentialKernel, pointSub, heatKernelPlus, ht] using hfinal

theorem heatPotential_spatial_kernel_spatial_difference_abs_le
    {i : Fin 3} {p p' v : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (ht : 0 < p.2 - v.2)
    (hsep : ∀ y ∈ segment ℝ p.1 p'.1,
      R ≤ rhoTwo (y - v.1) (p.2 - v.2)) :
    |heatPotentialSpatialKernel i p v -
        heatPotentialSpatialKernel i (p'.1, p.2) v| ≤
      (60000000 / R ^ 5) * vec3EuclideanNorm (p.1 - p'.1) := by
  exact heatPotential_spatial_derivative_kernel_difference_abs_le hR ht hsep

private lemma heatKernel_hasDerivWithinAt_zero_right {x : Vec3}
    (hx : 0 < vec3EuclideanNorm x) :
    HasDerivWithinAt (fun t : ℝ => heatKernel x t) 0 (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hq : 0 < (vec3EuclideanNorm x) ^ 2 / 4 := by positivity
  have hu : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (5 / 2 : ℝ) ((vec3EuclideanNorm x) ^ 2 / 4) hq
  have hlim := hbase.comp hu
  have hlim' : Tendsto (fun t : ℝ => t⁻¹ * heatKernel x t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => (4 * Real.pi) ^ (-(3 : ℝ) / 2))
        (𝓝[>] (0 : ℝ)) (𝓝 ((4 * Real.pi) ^ (-(3 : ℝ) / 2))) := tendsto_const_nhds
    have hprod := hconst.mul hlim
    have heq : (fun t : ℝ => t⁻¹ * heatKernel x t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
          ((t⁻¹) ^ ((5 : ℝ) / 2) *
            Real.exp (-((vec3EuclideanNorm x) ^ 2 / 4) * t⁻¹))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      rw [heatKernel_eq_formula ht]
      have hbasecoef : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) =
          (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (t⁻¹) ^ ((3 : ℝ) / 2) := by
        rw [Real.mul_rpow (by positivity) ht.le,
          show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
          Real.rpow_neg (by positivity), Real.rpow_neg (by positivity : 0 ≤ t),
          Real.inv_rpow (by positivity : 0 ≤ t)]
      rw [hbasecoef]
      have hpow : t⁻¹ * (t⁻¹) ^ ((3 : ℝ) / 2) =
          (t⁻¹) ^ ((5 : ℝ) / 2) := by
        calc
          t⁻¹ * (t⁻¹) ^ ((3 : ℝ) / 2) =
              (t⁻¹) ^ (1 : ℝ) * (t⁻¹) ^ ((3 : ℝ) / 2) := by rw [Real.rpow_one]
          _ = (t⁻¹) ^ ((5 : ℝ) / 2) := by
            rw [← Real.rpow_add (by positivity : 0 < t⁻¹)]
            congr 1; ring
      calc
        t⁻¹ * ((4 * Real.pi) ^ (-(3 : ℝ) / 2) * (t⁻¹) ^ ((3 : ℝ) / 2) *
            Real.exp (-(vec3EuclideanNorm x) ^ 2 / (4 * t))) =
            (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
              ((t⁻¹ * (t⁻¹) ^ ((3 : ℝ) / 2)) *
                Real.exp (-(vec3EuclideanNorm x) ^ 2 / (4 * t))) := by ring
        _ = (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
              ((t⁻¹) ^ ((5 : ℝ) / 2) *
                Real.exp (-(vec3EuclideanNorm x) ^ 2 / (4 * t))) := by rw [hpow]
        _ = (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
              ((t⁻¹) ^ ((5 : ℝ) / 2) *
                Real.exp (-((vec3EuclideanNorm x) ^ 2 / 4) * t⁻¹)) := by
          congr 2
          field_simp
    simpa using hprod.congr' heq.symm
  have hslope : (fun t : ℝ => slope (fun s => heatKernel x s) 0 t) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => t⁻¹ * heatKernel x t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    simp [slope, heatKernel_eq_zero_of_nonpos (le_rfl), smul_eq_mul]
  have hlim'' : Tendsto (fun t : ℝ => slope (fun s => heatKernel x s) 0 t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := hlim'.congr' hslope.symm
  simpa [show Ici (0 : ℝ) \ {0} = Ioi 0 by ext t; simp] using hlim''

private lemma heatPotential_spatial_time_deriv {x : Vec3} {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    deriv (fun s : ℝ => heatKernelSpaceDerivative x s i) t =
      heatKernelTimeGradientDerivative x t i := by
  have ha : HasDerivAt (fun s : ℝ => -(x i) / (2 * s))
      ((x i) / (2 * t ^ 2)) t := by
    have hden : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      convert (hasDerivAt_const t (2 : ℝ)).mul (hasDerivAt_id' t) using 1; ring
    have hinv := (hasDerivAt_inv (by positivity : 2 * t ≠ 0)).comp t hden
    convert (hasDerivAt_const t (-(x i))).mul hinv using 1
    · funext s
      dsimp
      ring
    · field_simp [ht.ne']
      ring
  have hg := (heatKernel_time_differentiableAt (x := x) ht).hasDerivAt
  have hc := ha.mul hg
  have hc0 : HasDerivAt (fun s : ℝ => heatKernelSpaceDerivative x s i)
      (x i / (2 * t ^ 2) * heatKernel x t +
        (-(x i) / (2 * t)) * deriv (fun s : ℝ => heatKernel x s) t) t := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [heatKernelSpaceDerivative, ite_eq_left hs]
    rfl
  have hcs : HasDerivAt (fun s : ℝ => heatKernelSpaceDerivative x s i)
      ((x i) / (2 * t ^ 2) * heatKernel x t +
        (-(x i) / (2 * t)) * heatKernelTimeDerivative x t) t := by
    convert hc0 using 1
    rw [heatKernel_time_deriv ht]
  rw [heatKernelTimeGradientDerivative, ite_eq_left ht]
  exact hcs.deriv

private lemma heatKernelSpaceDerivative_hasDerivWithinAt_zero_right {x : Vec3} (hx : 0 <
  vec3EuclideanNorm x)
    (i : Fin 3) :
    HasDerivWithinAt (fun t : ℝ => heatKernelSpaceDerivative x t i)
      0 (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hq : 0 < (vec3EuclideanNorm x) ^ 2 / 4 := by positivity
  have hu : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (7 / 2 : ℝ) ((vec3EuclideanNorm x) ^ 2 / 4) hq
  have hlim := hbase.comp hu
  have hlim' : Tendsto
      (fun t : ℝ => t⁻¹ * heatKernelSpaceDerivative x t i)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ =>
        (-(x i) / 2) * (4 * Real.pi) ^ (-(3 : ℝ) / 2))
        (𝓝[>] (0 : ℝ)) (𝓝 ((-(x i) / 2) * (4 * Real.pi) ^ (-(3 : ℝ) / 2))) :=
      tendsto_const_nhds
    have hprod := hconst.mul hlim
    have heq : (fun t : ℝ => t⁻¹ * heatKernelSpaceDerivative x t i) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t => ((-(x i) / 2) * (4 * Real.pi) ^ (-(3 : ℝ) / 2)) *
          ((t⁻¹) ^ ((7 : ℝ) / 2) *
            Real.exp (-((vec3EuclideanNorm x) ^ 2 / 4) * t⁻¹))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      rw [heatKernelSpaceDerivative, ite_eq_left ht,
        heatKernel_eq_formula_sum ht]
      have hbasecoef : (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) =
          (4 * Real.pi) ^ (-(3 : ℝ) / 2) * (t⁻¹) ^ ((3 : ℝ) / 2) := by
        rw [Real.mul_rpow (by positivity) ht.le,
          show -(3 : ℝ) / 2 = -((3 : ℝ) / 2) by ring,
          Real.rpow_neg (by positivity), Real.rpow_neg (by positivity : 0 ≤ t),
          Real.inv_rpow (by positivity : 0 ≤ t)]
      rw [hbasecoef]
      rw [← vec3EuclideanNorm_sq]
      have hpow : t⁻¹ * (t⁻¹ * (t⁻¹) ^ ((3 : ℝ) / 2)) =
          (t⁻¹) ^ ((7 : ℝ) / 2) := by
        calc
          t⁻¹ * (t⁻¹ * (t⁻¹) ^ ((3 : ℝ) / 2)) =
              (t⁻¹) ^ (1 : ℝ) * ((t⁻¹) ^ (1 : ℝ) *
                (t⁻¹) ^ ((3 : ℝ) / 2)) := by rw [Real.rpow_one]
          _ = (t⁻¹) ^ ((7 : ℝ) / 2) := by
            rw [← Real.rpow_add (by positivity : 0 < t⁻¹),
              ← Real.rpow_add (by positivity : 0 < t⁻¹)]
            congr 1; ring
      calc
        t⁻¹ * (-(x i) / (2 * t) *
            ((4 * Real.pi) ^ (-(3 : ℝ) / 2) *
              (t⁻¹) ^ ((3 : ℝ) / 2) *
              Real.exp (-(vec3EuclideanNorm x) ^ 2 / (4 * t)))) =
            ((-(x i) / 2) * (4 * Real.pi) ^ (-(3 : ℝ) / 2)) *
              ((t⁻¹ * (t⁻¹ * (t⁻¹) ^ ((3 : ℝ) / 2))) *
                Real.exp (-(vec3EuclideanNorm x) ^ 2 / (4 * t))) := by ring
        _ = ((-(x i) / 2) * (4 * Real.pi) ^ (-(3 : ℝ) / 2)) *
              ((t⁻¹) ^ ((7 : ℝ) / 2) *
                Real.exp (-((vec3EuclideanNorm x) ^ 2 / 4) * t⁻¹)) := by
          rw [hpow]
          congr 2
          field_simp
    simpa using hprod.congr' heq.symm
  have hslope : (fun t : ℝ => slope
      (fun s => heatKernelSpaceDerivative x s i) 0 t) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => t⁻¹ * heatKernelSpaceDerivative x t i) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    simp [slope, heatKernelSpaceDerivative, ite_eq_left ht, smul_eq_mul]
  have hlim'' := hlim'.congr' hslope.symm
  simpa [show Ici (0 : ℝ) \ {0} = Ioi 0 by ext t; simp] using hlim''


theorem heatPotential_time_kernel_difference_abs_le
    {p p' v : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hp : p.2 ≤ p'.2) (ht : 0 ≤ p.2 - v.2)
    (hsep : ∀ s ∈ Set.Icc p.2 p'.2,
      R ≤ rhoTwo (p'.1 - v.1) (s - v.2)) :
    |heatPotentialKernel (p'.1, p.2) v - heatPotentialKernel p' v| ≤
      (10000000 / R ^ 5) * |p.2 - p'.2| := by
  let f : ℝ → ℝ := fun s => heatKernel (p'.1 - v.1) (s - v.2)
  have hderiv : ∀ s ∈ Set.Icc p.2 p'.2,
      HasDerivWithinAt f (heatKernelTimeDerivative (p'.1 - v.1) (s - v.2))
        (Set.Icc p.2 p'.2) s := by
    intro s hs
    by_cases hts : 0 < s - v.2
    · have hinner : HasDerivAt (fun s : ℝ => s - v.2) 1 s := by
        simpa using (hasDerivAt_id s).sub_const v.2
      have houter := (heatKernel_time_differentiableAt
        (x := p'.1 - v.1) hts).hasDerivAt
      have hcomp := houter.comp s hinner
      have hcomp' : HasDerivAt
          (fun s : ℝ => heatKernel (p'.1 - v.1) (s - v.2))
          (heatKernelTimeDerivative (p'.1 - v.1) (s - v.2)) s := by
        simpa [Function.comp_def, heatKernel_time_deriv hts] using hcomp
      simpa [f] using hcomp'.hasDerivWithinAt
    · have hsnonneg : 0 ≤ s - v.2 := by linarith only [ht, hs.1]
      have hszero : s - v.2 = 0 := le_antisymm
        (le_of_not_gt hts) hsnonneg
      have hx : 0 < vec3EuclideanNorm (p'.1 - v.1) := by
        have hpos := lt_of_lt_of_le hR (hsep s hs)
        simpa [rhoTwo, hszero] using hpos
      have hzero := heatKernel_hasDerivWithinAt_zero_right hx
      have hinner : HasDerivAt (fun s : ℝ => s - v.2) 1 s := by
        simpa using (hasDerivAt_id s).sub_const v.2
      have hmaps : MapsTo (fun y : ℝ => y - v.2)
          (Set.Icc p.2 p'.2) (Set.Ici 0) := by
        intro y hy
        change 0 ≤ y - v.2
        linarith only [ht, hy.1]
      have hcomp := hzero.comp_of_eq s hinner.hasDerivWithinAt hmaps hszero.symm
      simpa [f, Function.comp_def, heatKernelTimeDerivative, hts] using hcomp
  have hbound : ∀ s ∈ Set.Ico p.2 p'.2,
      |heatKernelTimeDerivative (p'.1 - v.1) (s - v.2)| ≤
        10000000 / R ^ 5 := by
    intro s hs
    by_cases hts : 0 < s - v.2
    · have hkernel := heatKernelTimeDerivative_le_rho_inv_five
        (x := p'.1 - v.1) (t := s - v.2) hts
      exact hkernel.trans (by gcongr; exact hsep s (Ico_subset_Icc_self hs))
    · simp only [heatKernelTimeDerivative, hts, ↓reduceIte, abs_zero]
      positivity
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    p'.2 (right_mem_Icc.2 hp)
  have hmean' : |heatKernel (p'.1 - v.1) (p'.2 - v.2) -
      heatKernel (p'.1 - v.1) (p.2 - v.2)| ≤
      (10000000 / R ^ 5) * (p'.2 - p.2) := by
    simpa [f, Real.norm_eq_abs] using hmean
  have htime : |p.2 - p'.2| = p'.2 - p.2 := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hp)]
  rw [htime]
  rw [abs_sub_comm] at hmean'
  change |heatKernelPlus (p'.1 - v.1, p.2 - v.2) -
      heatKernelPlus (p'.1 - v.1, p'.2 - v.2)| ≤
    (10000000 / R ^ 5) * (p'.2 - p.2)
  have hk := heatKernelPlus_eq_heatKernel (p'.1 - v.1, p.2 - v.2)
  have hk' := heatKernelPlus_eq_heatKernel (p'.1 - v.1, p'.2 - v.2)
  rw [hk, hk']
  exact hmean'
theorem heatPotential_far_shell_spatial_kernel_difference_abs_le
    {z p p' v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    |heatPotentialKernel p v - heatPotentialKernel (p'.1, p.2) v| ≤
      (900000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4) *
        vec3EuclideanNorm (p.1 - p'.1) := by
  by_cases ht : 0 < p.2 - v.2
  · apply heatPotential_spatial_kernel_difference_abs_le (by positivity) ht
    intro y hy
    rcases heatPotential_far_shell_kernel_separation hr
      (parabolic_ball_segment_mem hp hp'
        (y := (show ParabolicPoint from (y, p.2))) hy rfl) hv with hzero | hsep
    · exact False.elim ((not_le_of_gt ht) hzero)
    · exact hsep
  · have hzero : p.2 - v.2 ≤ 0 := le_of_not_gt ht
    simp only [heatPotentialKernel, pointSub, heatKernelPlus_eq_zero_of_nonpos hzero, sub_self,
      abs_zero,
    ge_iff_le]
    have hRj : 0 < (2 : ℝ) ^ ((j : ℝ) + 4) * r := by positivity
    exact mul_nonneg
      (div_nonneg (by norm_num) (pow_nonneg hRj.le _))
      (vec3EuclideanNorm_nonneg _)

theorem heatPotential_far_shell_spatial_kernel_spatial_difference_abs_le
    {i : Fin 3} {z p p' v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r)
    (hp : p ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hp' : p' ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    |heatPotentialSpatialKernel i p v -
        heatPotentialSpatialKernel i (p'.1, p.2) v| ≤
      (60000000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 5) *
        vec3EuclideanNorm (p.1 - p'.1) := by
  by_cases ht : 0 < p.2 - v.2
  · apply heatPotential_spatial_kernel_spatial_difference_abs_le (by positivity) ht
    intro y hy
    rcases heatPotential_far_shell_kernel_separation hr
      (parabolic_ball_segment_mem hp hp'
        (y := (show ParabolicPoint from (y, p.2))) hy rfl) hv with hzero | hsep
    · exact False.elim ((not_le_of_gt ht) hzero)
    · exact hsep
  · have hzero : p.2 - v.2 ≤ 0 := le_of_not_gt ht
    have hnot : ¬ v.2 < p.2 := by linarith only [hzero]
    simp only [heatPotentialSpatialKernel, heatKernelSpaceDerivative, sub_pos, hnot, ↓reduceIte,
      sub_self,
    abs_zero, ge_iff_le]
    have hRj : 0 < (2 : ℝ) ^ ((j : ℝ) + 4) * r := by positivity
    exact mul_nonneg
      (div_nonneg (by norm_num) (pow_nonneg hRj.le 5))
      (vec3EuclideanNorm_nonneg _)

theorem heatPotential_far_shell_kernel_abs_le
    {z w v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hw : w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    |heatPotentialKernel w v| ≤
        1000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 3 := by
  rcases heatPotential_far_shell_kernel_separation hr hw hv with ht | hsep
  · change |heatKernelPlus (w.1 - v.1, w.2 - v.2)| ≤
      1000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 3
    rw [heatKernelPlus_eq_zero_of_nonpos ht, abs_zero]
    positivity
  · exact heatPotentialKernel_abs_le (by positivity) hsep

theorem heatPotential_far_shell_spatial_kernel_abs_le
    {i : Fin 3} {z w v : ParabolicPoint} {r : ℝ} {j : ℕ}
    (hr : 0 < r) (hw : w ∈ @Metric.closedBall ParabolicPoint
      parabolicPseudoMetricSpace z r)
    (hv : v ∈ heatPotentialFarShellSet z r j) :
    |heatPotentialSpatialKernel i w v| ≤
        300000 / ((2 : ℝ) ^ ((j : ℝ) + 4) * r) ^ 4 := by
  rcases heatPotential_far_shell_kernel_separation hr hw hv with ht | hsep
  · rw [heatPotentialSpatialKernel, heatKernelSpaceDerivative,
      ite_eq_right (not_lt.mpr ht), abs_zero]
    positivity
  · exact heatPotentialSpatialKernel_abs_le (by positivity) hsep

theorem heatPotential_spatial_time_kernel_difference_abs_le
    {i : Fin 3} {p p' v : ParabolicPoint} {R : ℝ}
    (hR : 0 < R) (hp : p.2 ≤ p'.2) (ht : 0 ≤ p.2 - v.2)
    (hsep : ∀ s ∈ Set.Icc p.2 p'.2,
      R ≤ rhoTwo (p'.1 - v.1) (s - v.2)) :
    |heatPotentialSpatialKernel i (p'.1, p.2) v -
        heatPotentialSpatialKernel i p' v| ≤
      (30000000000 / R ^ 6) * |p.2 - p'.2| := by
  let f : ℝ → ℝ := fun s =>
    heatKernelSpaceDerivative (p'.1 - v.1) (s - v.2) i
  have hderiv : ∀ s ∈ Set.Icc p.2 p'.2,
      HasDerivWithinAt f
        (heatKernelTimeGradientDerivative (p'.1 - v.1) (s - v.2) i)
        (Set.Icc p.2 p'.2) s := by
    intro s hs
    by_cases hts : 0 < s - v.2
    · have hinner : HasDerivAt (fun s : ℝ => s - v.2) 1 s := by
        simpa using (hasDerivAt_id' s).sub_const v.2
      have houter_diff : DifferentiableAt ℝ
          (fun τ : ℝ => heatKernelSpaceDerivative (p'.1 - v.1) τ i)
          (s - v.2) := by
        have hformula : DifferentiableAt ℝ
            (fun τ : ℝ => -((p'.1 - v.1) i) / (2 * τ) *
              ((4 * Real.pi * τ) ^ (-(3 : ℝ) / 2) *
                Real.exp (-(∑ k, (p'.1 - v.1) k ^ 2) / (4 * τ))))
            (s - v.2) := by
          fun_prop (disch := positivity)
        apply hformula.congr_of_eventuallyEq
        filter_upwards [eventually_gt_nhds hts] with τ hτ
        rw [heatKernelSpaceDerivative, ite_eq_left hτ,
          heatKernel_eq_formula_sum hτ]
      have houter := houter_diff.hasDerivAt
      rw [heatPotential_spatial_time_deriv hts i
        (x := p'.1 - v.1) (t := s - v.2)] at houter
      have hcomp := houter.comp s hinner
      have hcomp' : HasDerivAt
          (fun s : ℝ => heatKernelSpaceDerivative (p'.1 - v.1) (s - v.2) i)
          (heatKernelTimeGradientDerivative (p'.1 - v.1) (s - v.2) i) s := by
        simpa [Function.comp_def] using hcomp
      simpa [f] using hcomp'.hasDerivWithinAt
    · have hsnonneg : 0 ≤ s - v.2 := by linarith only [ht, hs.1]
      have hszero : s - v.2 = 0 := le_antisymm
        (le_of_not_gt hts) hsnonneg
      have hx : 0 < vec3EuclideanNorm (p'.1 - v.1) := by
        have hpos := lt_of_lt_of_le hR (hsep s hs)
        simpa [rhoTwo, hszero] using hpos
      have hzero := heatKernelSpaceDerivative_hasDerivWithinAt_zero_right hx i
      have hinner : HasDerivAt (fun s : ℝ => s - v.2) 1 s := by
        simpa using (hasDerivAt_id' s).sub_const v.2
      have hmaps : MapsTo (fun y : ℝ => y - v.2)
          (Set.Icc p.2 p'.2) (Set.Ici 0) := by
        intro y hy
        change 0 ≤ y - v.2
        linarith only [ht, hy.1]
      have hcomp := hzero.comp_of_eq s hinner.hasDerivWithinAt hmaps hszero.symm
      simpa [f, Function.comp_def, heatKernelSpaceDerivative, hts,
        heatKernelTimeGradientDerivative, hszero] using hcomp
  have hbound : ∀ s ∈ Set.Ico p.2 p'.2,
      |heatKernelTimeGradientDerivative (p'.1 - v.1) (s - v.2) i| ≤
        30000000000 / R ^ 6 := by
    intro s hs
    by_cases hts : 0 < s - v.2
    · exact (heatPotentialSpatialTimeKernel_abs_le (i := i)
        (w := (p'.1, s)) (v := v) hR (hsep s
          (Ico_subset_Icc_self hs))).trans (by gcongr)
    · simp only [heatKernelTimeGradientDerivative, hts, ↓reduceIte, abs_zero]
      positivity
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    p'.2 (right_mem_Icc.2 hp)
  have hmean' : |heatKernelSpaceDerivative (p'.1 - v.1) (p'.2 - v.2) i -
      heatKernelSpaceDerivative (p'.1 - v.1) (p.2 - v.2) i| ≤
      (30000000000 / R ^ 6) * (p'.2 - p.2) := by
    simpa [f, Real.norm_eq_abs] using hmean
  have htime : |p.2 - p'.2| = p'.2 - p.2 := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hp)]
  rw [htime]
  rw [abs_sub_comm] at hmean'
  change |heatKernelSpaceDerivative (p'.1 - v.1) (p.2 - v.2) i -
      heatKernelSpaceDerivative (p'.1 - v.1) (p'.2 - v.2) i| ≤
    (30000000000 / R ^ 6) * (p'.2 - p.2)
  exact hmean'

end CKN.Core.HeatPotential
