/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecond
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Commutator.Kernels
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Interior
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrders

/-!
# Riesz Second Bad Part

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- Explicit coefficient controlling the second Riesz kernel's size estimates. -/
@[expose] def rieszSecondKernelC₂ : ℝ := 72 / (4 * Real.pi)

/-- Second spatial derivative of the Newtonian kernel in the chosen coordinates. -/
@[expose]
def rieszSecondKernel (i j : Fin 3) (z : Vec3) : ℝ :=
  CKN.spatialDeriv (CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i) j z

/-- Algebraic Hessian formula for the inverse Euclidean radius, before Newtonian normalization. -/
def heatSecondFormula (i j : Fin 3) (z : Vec3) : ℝ :=
  3 * z i * z j * CKN.Foundation.Heat.q z ^ (-(5 : ℝ) / 2) -
    (if i = j then 1 else 0) * CKN.Foundation.Heat.q z ^ (-(3 : ℝ) / 2)

/-- Continuous linear differential of the power of the squared Euclidean norm. -/
def heatQDerivative (p : ℝ) (x : Vec3) : Vec3 →L[ℝ] ℝ :=
  (p * CKN.Foundation.Heat.q x ^ (p - 1)) •
    ∑ k : Fin 3, (2 * x k) •
      (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)

/-- Continuous linear differential of the algebraic Newtonian Hessian formula. -/
def heatSecondDerivative (i j : Fin 3) (x : Vec3) : Vec3 →L[ℝ] ℝ :=
  3 • ((x i * x j) • heatQDerivative (-(5 : ℝ) / 2) x +
    (CKN.Foundation.Heat.q x ^ (-(5 : ℝ) / 2)) •
      (x i • (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ) +
        x j • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))) -
    (if i = j then 1 else 0) • heatQDerivative (-(3 : ℝ) / 2) x

private lemma hasFDerivAt_heatQ (x : Vec3) :
    HasFDerivAt CKN.Foundation.Heat.q
      (∑ k : Fin 3, (2 * x k) •
        (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)) x := by
  have hfun : CKN.Foundation.Heat.q = ∑ k : Fin 3,
      (fun y : Vec3 => y k * y k) := by
    funext y
    simp [CKN.Foundation.Heat.q, pow_two]
  have hsum : HasFDerivAt
      (∑ k : Fin 3, (fun y : Vec3 => y k * y k))
      (∑ k : Fin 3, (2 * x k) •
        (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)) x := by
    apply HasFDerivAt.sum
    intro k _hk
    have hprod := (hasFDerivAt_apply (𝕜 := ℝ) k x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) k x)
    convert hprod using 1
    ext v
    simp [smul_eq_mul]
    ring
  rw [hfun]
  exact hsum

private lemma hasFDerivAt_heatSecondFormula {x : Vec3} (hx : x ≠ 0)
    (i j : Fin 3) :
    HasFDerivAt (heatSecondFormula i j)
      (heatSecondDerivative i j x) x := by
  have hq := hasFDerivAt_heatQ x
  have hq5 := hq.rpow_const (p := -(5 : ℝ) / 2)
    (Or.inl (CKN.Foundation.Heat.q_pos hx).ne')
  have hq3 := hq.rpow_const (p := -(3 : ℝ) / 2)
    (Or.inl (CKN.Foundation.Heat.q_pos hx).ne')
  have hi : HasFDerivAt (fun y : Vec3 => y i)
      (ContinuousLinearMap.proj i) x := hasFDerivAt_apply (𝕜 := ℝ) i x
  have hj : HasFDerivAt (fun y : Vec3 => y j)
      (ContinuousLinearMap.proj j) x := hasFDerivAt_apply (𝕜 := ℝ) j x
  have hprod := (hi.mul hj).mul hq5
  have hterm := hprod.const_mul (3 : ℝ)
  have hdelta := hq3.const_mul (if i = j then (1 : ℝ) else 0)
  have htotal := hterm.sub hdelta
  convert htotal using 1
  · funext y
    simp [heatSecondFormula]
    ring
  · ext v
    simp [heatSecondDerivative, heatQDerivative,
      ContinuousLinearMap.proj_apply, smul_eq_mul]

private lemma heat_second_component_formula {x : Vec3} (hx : x ≠ 0)
    (i j m : Fin 3) :
    (fderiv ℝ (fun z : Vec3 => rieszSecondKernel i j z) x)
        (CKN.basisVec m) =
      (4 * Real.pi)⁻¹ *
        (3 * (if m = i then 1 else 0) * x j * CKN.Foundation.Heat.q x ^ (-(5 : ℝ) / 2) +
        3 * x i * (if m = j then 1 else 0) * CKN.Foundation.Heat.q x ^ (-(5 : ℝ) / 2) -
        15 * x i * x j * x m * CKN.Foundation.Heat.q x ^ (-(7 : ℝ) / 2) +
        3 * (if i = j then 1 else 0) * x m * CKN.Foundation.Heat.q x ^ (-(5 : ℝ) / 2)) := by
  let H : Vec3 → ℝ := fun z => rieszSecondKernel i j z
  have hEq : H =ᶠ[𝓝 x]
      (fun z => (4 * Real.pi)⁻¹ * heatSecondFormula i j z) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with z hz
    change CKN.spatialDeriv
      (CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i) j z = _
    rw [CKN.Foundation.Heat.newtonianKernel_spatialDeriv_second_formula hz i j]
    simp [heatSecondFormula,
      show -(3 : ℝ) / 2 - 1 = -(5 : ℝ) / 2 by ring]
    ring
  have hfd := (hasFDerivAt_heatSecondFormula (x := x) hx i j).const_mul
    ((4 * Real.pi)⁻¹)
  have hfd' := hfd.congr_of_eventuallyEq hEq
  have hm := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec m)) hfd'.fderiv
  change (fderiv ℝ H x) (CKN.basisVec m) = _
  rw [hm]
  by_cases hij : i = j
  · subst j
    by_cases hmi : m = i
    · subst m
      simp [heatSecondDerivative, heatQDerivative, _root_.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul,
        show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by ring,
        show -(3 : ℝ) / 2 - 1 = -(5 : ℝ) / 2 by ring]
      ring
    · have him : ¬i = m := by exact fun h => hmi h.symm
      simp [heatSecondDerivative, heatQDerivative, _root_.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, hmi, him,
        show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by ring,
        show -(3 : ℝ) / 2 - 1 = -(5 : ℝ) / 2 by ring]
      ring
  · by_cases hmi : m = i
    · subst m
      have hji : ¬j = i := by exact fun h => hij h.symm
      simp [heatSecondDerivative, heatQDerivative, _root_.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul, hij, hji,
        show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by ring,
        show -(3 : ℝ) / 2 - 1 = -(5 : ℝ) / 2 by ring]
      ring
    · have him : ¬i = m := by exact fun h => hmi h.symm
      by_cases hmj : m = j
      · subst m
        simp [heatSecondDerivative, heatQDerivative, _root_.smul_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, hij, hmi,
          show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by ring,
          show -(3 : ℝ) / 2 - 1 = -(5 : ℝ) / 2 by ring]
        ring
      · have hjm : ¬j = m := by exact fun h => hmj h.symm
        simp [heatSecondDerivative, heatQDerivative, _root_.smul_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, hij, hmi, him, hmj, hjm,
          show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by ring,
          show -(3 : ℝ) / 2 - 1 = -(5 : ℝ) / 2 by ring]
        ring

private lemma second_component_eq_neg_third {x : Vec3} (hx : x ≠ 0)
    (i j m : Fin 3) :
    (fderiv ℝ (fun z : Vec3 => rieszSecondKernel i j z) x)
        (CKN.basisVec m) =
      -CKN.Foundation.Harmonic.Commutator.newtonianKernel m j i x := by
  have h5 : CKN.Foundation.Heat.q x ^ (-(5 : ℝ) / 2) =
      (vec3EuclideanNorm x ^ 5)⁻¹ := by
    rw [CKN.Foundation.Heat.q_eq_vec3Norm_sq,
      show -(5 : ℝ) / 2 = -(5 / 2 : ℝ) by ring,
      show vec3EuclideanNorm x ^ 2 = vec3EuclideanNorm x ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg x)]
    ring_nf
    rw [Real.rpow_neg (vec3EuclideanNorm_nonneg x)]
    norm_num
  have h7 : CKN.Foundation.Heat.q x ^ (-(7 : ℝ) / 2) =
      (vec3EuclideanNorm x ^ 7)⁻¹ := by
    rw [CKN.Foundation.Heat.q_eq_vec3Norm_sq,
      show -(7 : ℝ) / 2 = -(7 / 2 : ℝ) by ring,
      show vec3EuclideanNorm x ^ 2 = vec3EuclideanNorm x ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg x)]
    ring_nf
    rw [Real.rpow_neg (vec3EuclideanNorm_nonneg x)]
    norm_num
  have hcomp := heat_second_component_formula hx i j m
  rw [h5, h7] at hcomp
  calc
    (fderiv ℝ (fun z : Vec3 => rieszSecondKernel i j z) x)
        (CKN.basisVec m) =
        (4 * Real.pi)⁻¹ *
          (3 * (if m = i then 1 else 0) * x j * (vec3EuclideanNorm x ^ 5)⁻¹ +
          3 * x i * (if m = j then 1 else 0) * (vec3EuclideanNorm x ^ 5)⁻¹ -
          15 * x i * x j * x m * (vec3EuclideanNorm x ^ 7)⁻¹ +
          3 * (if i = j then 1 else 0) * x m * (vec3EuclideanNorm x ^ 5)⁻¹) := hcomp
    _ = -CKN.Foundation.Harmonic.Commutator.newtonianKernel m j i x := by
      rw [CKN.Foundation.Harmonic.Commutator.newtonianKernel_eq_scaled]
      have hnorm : vec3EuclideanNorm x = CKN.vecEuclideanNorm x := by
        simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
          CKN.vecDot, pow_two]
      rw [hnorm]
      simp only [mul_inv_rev, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Harmonic.Commutator.inverseThirdFormula, neg_mul, one_mul, neg_neg, mul_eq_mul_left_iff,
      mul_eq_zero, inv_eq_zero,
    Real.pi_ne_zero, OfNat.ofNat_ne_zero, or_self, or_false]
      rw [← inv_pow, ← inv_pow]
      simp only [eq_comm]
      split_ifs <;> ring

private lemma opNorm_le_sum_components (L : Vec3 →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ m : Fin 3, ‖L (CKN.basisVec m)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound L
    (Finset.sum_nonneg fun m _hm => norm_nonneg _)
  intro v
  calc
    ‖L v‖ = ‖L (∑ m : Fin 3, v m • CKN.basisVec m)‖ := by
      rw [sum_smul_basisVec]
    _ = ‖∑ m : Fin 3, v m • L (CKN.basisVec m)‖ := by
      rw [_root_.map_sum]
      simp only [map_smul]
    _ ≤ ∑ m : Fin 3, ‖v m • L (CKN.basisVec m)‖ := norm_sum_le _ _
    _ = ∑ m : Fin 3, ‖v m‖ * ‖L (CKN.basisVec m)‖ := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [norm_smul]
    _ ≤ ∑ m : Fin 3, ‖v‖ * ‖L (CKN.basisVec m)‖ := by
      apply Finset.sum_le_sum
      intro m _hm
      gcongr
      exact norm_le_pi_norm v m
    _ = (∑ m : Fin 3, ‖L (CKN.basisVec m)‖) * ‖v‖ := by
      calc
        _ = ∑ m : Fin 3, ‖L (CKN.basisVec m)‖ * ‖v‖ := by
          apply Finset.sum_congr rfl
          intro m _hm
          ring
        _ = _ := (Finset.sum_mul _ _ _).symm

private lemma fderiv_bound {x : Vec3} (hx : x ≠ 0) (i j : Fin 3) :
    ‖fderiv ℝ (fun z : Vec3 => rieszSecondKernel i j z) x‖ ≤
      rieszSecondKernelC₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)) := by
  let L : Vec3 →L[ℝ] ℝ := fderiv ℝ (fun z : Vec3 => rieszSecondKernel i j z) x
  have hcomp (m : Fin 3) : ‖L (CKN.basisVec m)‖ ≤
      (24 / (4 * Real.pi)) * (vec3EuclideanNorm x) ^ (-(4 : ℝ)) := by
    change ‖(fderiv ℝ (fun z : Vec3 => rieszSecondKernel i j z) x)
        (CKN.basisVec m)‖ ≤ _
    rw [Real.norm_eq_abs, second_component_eq_neg_third hx i j m, abs_neg]
    have hnorm : vec3EuclideanNorm x = CKN.vecEuclideanNorm x := by
      simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
        CKN.vecDot, pow_two]
    rw [hnorm]
    exact CKN.Foundation.Harmonic.Commutator.newtonianKernel_size_bound hx m j i
  have hsum : ∑ m : Fin 3, ‖L (CKN.basisVec m)‖ ≤
      ∑ _m : Fin 3, (24 / (4 * Real.pi)) *
        (vec3EuclideanNorm x) ^ (-(4 : ℝ)) := by
    apply Finset.sum_le_sum
    intro m _hm
    exact hcomp m
  calc
    ‖fderiv ℝ (fun z : Vec3 => rieszSecondKernel i j z) x‖ = ‖L‖ := by rfl
    _ ≤ ∑ m : Fin 3, ‖L (CKN.basisVec m)‖ := opNorm_le_sum_components L
    _ ≤ ∑ _m : Fin 3, (24 / (4 * Real.pi)) *
        (vec3EuclideanNorm x) ^ (-(4 : ℝ)) := hsum
    _ = rieszSecondKernelC₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)) := by
      simp [rieszSecondKernelC₂, Finset.sum_const, nsmul_eq_mul]
      ring

private lemma kernel_differentiableAt {x : Vec3} (hx : x ≠ 0) (i j : Fin 3) :
    DifferentiableAt ℝ (rieszSecondKernel i j) x := by
  have hfd : ContDiffAt ℝ (1 : ℕ)
      (fderiv ℝ (CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i)) x :=
    (CKN.Foundation.Heat.contDiffAt_newtonianKernel_spatialDeriv i 2 x hx).fderiv_right
      (m := (1 : ℕ)) (by norm_num)
  have hj : ContDiffAt ℝ (1 : ℕ) (rieszSecondKernel i j) x := by
    change ContDiffAt ℝ (1 : ℕ) (fun w : Vec3 =>
      (fderiv ℝ (CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i) w)
        (CKN.basisVec j)) x
    exact hfd.clm_apply contDiffAt_const
  exact hj.differentiableAt (by norm_num)

private lemma vec3EuclideanNorm_le_sqrt_three_mul_norm (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    have hv : vec3EuclideanNorm v ^ 2 = ∑ k : Fin 3, v k ^ 2 := by
      unfold vec3EuclideanNorm
      exact Real.sq_sqrt (Finset.sum_nonneg (fun k _hk => sq_nonneg (v k)))
    rw [hv, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ∑ k : Fin 3, v k ^ 2 ≤ ∑ _k : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _hk
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v k) 2
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2

theorem rieszSecondKernelC₂_nonneg : 0 ≤ rieszSecondKernelC₂ := by
  dsimp [rieszSecondKernelC₂]
  positivity

theorem rieszSecondKernel_measurable (i j : Fin 3) :
    Measurable (rieszSecondKernel i j) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  exact (CKN.Foundation.Heat.newtonianKernel_spatialDeriv_second_continuousAt hx i j)
    |>.continuousWithinAt

theorem rieszSecondKernel_differentiableAt {x : Vec3} (hx : x ≠ 0)
    (i j : Fin 3) :
    DifferentiableAt ℝ (rieszSecondKernel i j) x :=
  kernel_differentiableAt hx i j

theorem rieszSecondKernel_fderiv_bound {x : Vec3} (hx : x ≠ 0)
    (i j : Fin 3) :
    ‖fderiv ℝ (rieszSecondKernel i j) x‖ ≤
      rieszSecondKernelC₂ * (vec3EuclideanNorm x) ^ (-(4 : ℝ)) :=
  fderiv_bound hx i j

theorem rieszSecond_cube_star_exterior_geometry {Q : DyadicIndex}
    {x y : Vec3} (hx : x ∈ (rieszSecondCubeStar Q)ᶜ)
    (hy : y ∈ dyadicCubeSet Q) :
    2 * vec3EuclideanNorm (y - dyadicCubeCenter Q.scale Q.corner) <
      vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner) := by
  let c : Vec3 := dyadicCubeCenter Q.scale Q.corner
  let s : ℝ := dyadicScale Q.scale / 2
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (dyadicScale_pos Q.scale) (by norm_num)
  have hyc : vec3EuclideanNorm (y - c) ≤ Real.sqrt 3 * s := by
    dsimp [c, s]
    have hsup : ‖y - dyadicCubeCenter Q.scale Q.corner‖ ≤
        dyadicScale Q.scale / 2 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro k
      have hy' := (mem_dyadicCube.mp hy) k
      change |y k - dyadicCubeCenter Q.scale Q.corner k| ≤
        dyadicScale Q.scale / 2
      dsimp [dyadicCubeCenter]
      rw [abs_le]
      constructor <;> nlinarith only [hy'.1, hy'.2, dyadicScale_pos Q.scale]
    exact (vec3EuclideanNorm_le_sqrt_three_mul_norm _).trans
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg 3))
  have hstar : 2 * Real.sqrt 3 * s < vec3EuclideanNorm (x - c) := by
    exact lt_of_not_ge (by simpa [rieszSecondCubeStar, c, s] using hx)
  change 2 * vec3EuclideanNorm (y - c) < vec3EuclideanNorm (x - c)
  have hstar' : 2 * (Real.sqrt 3 * s) < vec3EuclideanNorm (x - c) := by
    simpa [mul_assoc] using hstar
  exact (mul_le_mul_of_nonneg_left hyc (by norm_num : (0 : ℝ) ≤ 2)).trans_lt hstar'

theorem rieszSecond_bad_cube_mean_zero {Q : DyadicIndex} {b : Vec3 → ℝ}
    (i j : Fin 3)
    (hmean : ∫ y in dyadicCubeSet Q, b y = 0)
    (hb : IntegrableOn b (dyadicCubeSet Q) volume)
    (hterm : ∀ x ∈ (rieszSecondCubeStar Q)ᶜ,
      IntegrableOn (fun y => rieszSecondKernel i j (x - y) * b y)
        (dyadicCubeSet Q) volume)
    {x : Vec3} (hx : x ∈ (rieszSecondCubeStar Q)ᶜ) :
    (∫ y in dyadicCubeSet Q, rieszSecondKernel i j (x - y) * b y) =
      ∫ y in dyadicCubeSet Q,
        (rieszSecondKernel i j (x - y) -
          rieszSecondKernel i j (x - dyadicCubeCenter Q.scale Q.corner)) * b y := by
  have hterm' := hterm x hx
  have hconst : IntegrableOn
      (fun y => rieszSecondKernel i j (x - dyadicCubeCenter Q.scale Q.corner) * b y)
      (dyadicCubeSet Q) volume := hb.const_mul _
  have hdiff : IntegrableOn
      (fun y => (rieszSecondKernel i j (x - y) -
        rieszSecondKernel i j (x - dyadicCubeCenter Q.scale Q.corner)) * b y)
      (dyadicCubeSet Q) volume := by
    have hsub := hterm'.sub hconst
    convert hsub using 1
    funext y
    simp only [Pi.sub_apply]
    ring
  have hzero : ∫ y in dyadicCubeSet Q,
      rieszSecondKernel i j (x - dyadicCubeCenter Q.scale Q.corner) * b y = 0 := by
    rw [integral_const_mul, hmean, mul_zero]
  calc
    ∫ y in dyadicCubeSet Q, rieszSecondKernel i j (x - y) * b y =
        ∫ y in dyadicCubeSet Q,
          (rieszSecondKernel i j (x - y) * b y -
            rieszSecondKernel i j (x - dyadicCubeCenter Q.scale Q.corner) * b y) := by
      rw [integral_sub hterm' hconst, hzero]
      simp
    _ = ∫ y in dyadicCubeSet Q,
        (rieszSecondKernel i j (x - y) -
          rieszSecondKernel i j (x - dyadicCubeCenter Q.scale Q.corner)) * b y := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring_nf

theorem rieszSecond_bad_cube_hormander {Q : DyadicIndex} {b : Vec3 → ℝ}
    (i j : Fin 3)
    (hmean : ∫ y in dyadicCubeSet Q, b y = 0)
    (hb : IntegrableOn b (dyadicCubeSet Q) volume)
    (hterm : ∀ x ∈ (rieszSecondCubeStar Q)ᶜ,
      IntegrableOn (fun y => rieszSecondKernel i j (x - y) * b y)
        (dyadicCubeSet Q) volume)
    (hjoint : AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(rieszSecondKernel i j (z.1 - z.2) -
          rieszSecondKernel i j (z.1 - dyadicCubeCenter Q.scale Q.corner)) * b z.2|
        ) ((volume.restrict (rieszSecondCubeStar Q)ᶜ).prod
          (volume.restrict (dyadicCubeSet Q))))
    (hjointSwap : AEMeasurable (fun z : Vec3 × Vec3 =>
        ENNReal.ofReal |(rieszSecondKernel i j (z.2 - z.1) -
          rieszSecondKernel i j (z.2 - dyadicCubeCenter Q.scale Q.corner)) * b z.1|
        ) ((volume.restrict (dyadicCubeSet Q)).prod
          (volume.restrict (rieszSecondCubeStar Q)ᶜ))) :
    ∃ Tbad : Vec3 → ℝ,
      AEMeasurable (fun x => ENNReal.ofReal |Tbad x|)
        (volume.restrict (rieszSecondCubeStar Q)ᶜ) ∧
      IntegrableOn Tbad (rieszSecondCubeStar Q)ᶜ volume ∧
      (∫⁻ x in (rieszSecondCubeStar Q)ᶜ,
        ENNReal.ofReal |Tbad x|) ≤
        ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
          ∫⁻ y in dyadicCubeSet Q, ENNReal.ofReal |b y| := by
  let K : Vec3 → ℝ := rieszSecondKernel i j
  let S : Set Vec3 := dyadicCubeSet Q
  let E : Set Vec3 := (rieszSecondCubeStar Q)ᶜ
  let Tbad : Vec3 → ℝ := fun x => ∫ y in S, K (x - y) * b y
  have hS : MeasurableSet S := by
    exact dyadicCube_measurable Q.scale Q.corner
  have hKmeas : Measurable K := by
    dsimp [K]
    exact rieszSecondKernel_measurable i j
  have hKdiff : ∀ x, x ≠ 0 → DifferentiableAt ℝ K x := by
    intro x hx
    exact rieszSecondKernel_differentiableAt hx i j
  have hKgrad : ∀ x, x ≠ 0 →
      ‖fderiv ℝ K x‖ ≤ rieszSecondKernelC₂ *
        (vec3EuclideanNorm x) ^ (-(4 : ℝ)) := by
    intro x hx
    exact rieszSecondKernel_fderiv_bound hx i j
  have hBint : Integrable (S.indicator b) volume := hb.integrable_indicator hS
  have hBae : AEStronglyMeasurable (S.indicator b) volume :=
    hBint.aestronglyMeasurable
  have hKprod : AEStronglyMeasurable (fun z : Vec3 × Vec3 => K (z.1 - z.2))
      (volume.prod volume) := by
    exact (hKmeas.stronglyMeasurable.comp_measurable
      (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have hBprod : AEStronglyMeasurable (fun z : Vec3 × Vec3 =>
      (S.indicator b) z.2) (volume.prod volume) := by
    exact hBae.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hTglobal : AEMeasurable (fun x : Vec3 =>
      ∫ y : Vec3, K (x - y) * (S.indicator b) y) volume := by
    have hprod := hKprod.mul hBprod
    exact hprod.integral_prod_right'.aemeasurable
  have hTeq : Tbad =ᵐ[volume] (fun x : Vec3 =>
      ∫ y : Vec3, K (x - y) * (S.indicator b) y) := by
    filter_upwards [] with x
    dsimp [Tbad]
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ S <;> simp [Set.indicator, hy]
  have hTbad_ae : AEMeasurable Tbad volume := hTglobal.congr hTeq.symm
  have hTmeas : AEMeasurable (fun x => ENNReal.ofReal |Tbad x|)
      (volume.restrict E) := by
    exact (AEMeasurable.ennreal_ofReal hTbad_ae.norm).mono_measure
      Measure.restrict_le_self
  have hterm' : ∀ x ∈ E, IntegrableOn (fun y => K (x - y) * b y) S volume := by
    simpa [K, E, S] using hterm
  have hjoint' : AEMeasurable (fun z : Vec3 × Vec3 =>
      ENNReal.ofReal |(K (z.1 - z.2) - K (z.1 -
        dyadicCubeCenter Q.scale Q.corner)) * b z.2|)
        ((volume.restrict E).prod (volume.restrict S)) := by
    simpa [K, E, S] using hjoint
  have hjointSwap' : AEMeasurable (fun z : Vec3 × Vec3 =>
      ENNReal.ofReal |(K (z.2 - z.1) - K (z.2 -
        dyadicCubeCenter Q.scale Q.corner)) * b z.1|)
        ((volume.restrict S).prod (volume.restrict E)) := by
    simpa [K, E, S] using hjointSwap
  have hbridge : (∫⁻ x in E, ENNReal.ofReal |Tbad x|) ≤
      ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
        ∫⁻ y in S, ENNReal.ofReal |b y| := by
    simpa [Tbad, E, S] using (rieszSecond_bad_cube_bridge_of_kernel
      (K := K) (Q := Q) (C₂ := rieszSecondKernelC₂) (b := b)
      rieszSecondKernelC₂_nonneg hKmeas hKdiff hKgrad hmean hb hterm'
      hjoint' hjointSwap')
  have hbtop : (∫⁻ y in S, ENNReal.ofReal |b y|) ≠ ∞ := by
    have hiff := lintegral_ofReal_ne_top_iff_integrable
      (μ := volume.restrict S) (f := fun y => |b y|)
      hb.norm.aestronglyMeasurable
      (ae_of_all _ (fun y => abs_nonneg (b y)))
    apply hiff.mpr
    simpa [Real.norm_eq_abs] using hb.norm
  have hrighttop : ENNReal.ofReal (64 * Real.pi * rieszSecondKernelC₂) *
        ∫⁻ y in S, ENNReal.ofReal |b y| ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbtop
  have hfin : (∫⁻ x in E, ENNReal.ofReal |Tbad x|) < ∞ :=
    lt_of_le_of_lt hbridge ((lt_top_iff_ne_top).mpr hrighttop)
  have hTabs : Integrable (fun x => |Tbad x|) (volume.restrict E) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (μ := volume.restrict E) (f := fun x => |Tbad x|)
      (hTbad_ae.norm.aestronglyMeasurable.restrict)
      (ae_of_all _ (fun x => abs_nonneg (Tbad x)))).mp
    exact hfin.ne
  have hTint : IntegrableOn Tbad E volume := by
    apply hTabs.mono' hTbad_ae.aestronglyMeasurable.restrict
    exact ae_of_all _ (fun x => le_rfl)
  exact ⟨Tbad, hTmeas, hTint, hbridge⟩

end CKN.Foundation.Euclidean
