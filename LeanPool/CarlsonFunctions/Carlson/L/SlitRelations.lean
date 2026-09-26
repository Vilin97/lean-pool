/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.L.SlitContinuation
public import LeanPool.CarlsonFunctions.Carlson.L.Associated

/-!
# Associated relations for L on the full product slit plane

Carlson (1987), (2.6), (3.1)–(3.4), and (3.7), for arbitrary complex exponents
and Dirichlet parameters. The identities are regularized and have no exceptional
parameter hyperplanes. Euler inversion retains the minus sign from the reflected
exponent, and the lowering and tangent identities retain their inhomogeneous R-terms.
-/

open Complex
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Equation (3.1) on slit-plane nodes. -/
theorem regCarlsonLSlit_eq_sum_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonLSlit t b z = ∑ i, b i * regCarlsonLSlit t (addDirichletUnit b i) z := by
  have h := hasDerivAt_regCarlsonRSlit_L t b hz
  have heq : (fun s => regCarlsonRSlit s b z) =
      (fun s => ∑ i, b i * regCarlsonRSlit s (addDirichletUnit b i) z) :=
    funext fun s => regCarlsonRSlit_eq_sum_addDirichletUnit s b hz
  rw [heq] at h
  exact h.unique (HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_regCarlsonRSlit_L t (addDirichletUnit b i) hz).const_mul (b i))

/-- Equation (3.2) on slit-plane nodes. -/
theorem regCarlsonLSlit_add_one_eq_sum_mul_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonLSlit (t + 1) b z =
      ∑ i, b i * z i * regCarlsonLSlit t (addDirichletUnit b i) z := by
  have h := (hasDerivAt_regCarlsonRSlit_L (t + 1) b hz).comp t ((hasDerivAt_id t).add_const 1)
  simp only [mul_one, Function.comp_def, id_eq] at h
  have heq : (fun s => regCarlsonRSlit (s + 1) b z) =
      (fun s => ∑ i, b i * z i * regCarlsonRSlit s (addDirichletUnit b i) z) :=
    funext fun s => regCarlsonRSlit_add_one_eq_sum_mul_addDirichletUnit s b hz
  rw [heq] at h
  exact h.unique (HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_regCarlsonRSlit_L t (addDirichletUnit b i) hz).const_mul (b i * z i))

/-- Equation (3.4), in its division-free parameter-raised form. -/
theorem regCarlsonLSlit_eq_addDirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    regCarlsonLSlit t b z =
      ((∑ j, b j) + t) * regCarlsonLSlit t (addDirichletUnit b i) z -
        t * z i * regCarlsonLSlit (t - 1) (addDirichletUnit b i) z +
        regCarlsonRSlit t (addDirichletUnit b i) z -
        z i * regCarlsonRSlit (t - 1) (addDirichletUnit b i) z := by
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane (analyticOnNhd_regCarlsonLSlit t b) ?_ ?_ hz
  · intro w hw
    have hcoord := (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w
    exact (((analyticAt_const.mul (analyticOnNhd_regCarlsonLSlit t _ w hw)).sub
      ((analyticAt_const.mul hcoord).mul (analyticOnNhd_regCarlsonLSlit (t - 1) _ w hw))).add
      (analyticOnNhd_regCarlsonRSlit t _ w hw)).sub
        (hcoord.mul (analyticOnNhd_regCarlsonRSlit (t - 1) _ w hw))
  · intro w hw
    change regCarlsonLSlit t b w =
      ((∑ j, b j) + t) * regCarlsonLSlit t (addDirichletUnit b i) w -
        t * w i * regCarlsonLSlit (t - 1) (addDirichletUnit b i) w +
        regCarlsonRSlit t (addDirichletUnit b i) w -
        w i * regCarlsonRSlit (t - 1) (addDirichletUnit b i) w
    simp_rw [regCarlsonLSlit_eq_continued _ _ hw, regCarlsonRSlit_eq_continued _ _ hw]
    exact regCarlsonLContinued_eq_addDirichletUnit t b hw i

/-- Equation (2.6): Euler inversion on the full slit domain. -/
theorem regCarlsonLSlit_euler (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonLSlit t b z =
      -(∏ i, z i ^ (-b i)) * regCarlsonLSlit (-(∑ i, b i) - t) b (fun i => (z i)⁻¹) := by
  have h := hasDerivAt_regCarlsonRSlit_L t b hz
  have heq : (fun s => regCarlsonRSlit s b z) =
      (fun s => (∏ i, z i ^ (-b i)) *
        regCarlsonRSlit (-(∑ i, b i) - s) b (fun i => (z i)⁻¹)) :=
    funext fun s => regCarlsonRSlit_euler s b hz
  rw [heq] at h
  have hd := ((hasDerivAt_regCarlsonRSlit_L (-(∑ i, b i) - t) b
    (carlsonRSlitDomain_inv hz)).comp t
      ((hasDerivAt_id t).const_sub (-(∑ i, b i)))).const_mul (∏ i, z i ^ (-b i))
  convert h.unique hd using 1
  ring

open scoped Classical in
/-- Equation (3.3), allowing coincident indices and nodes. -/
theorem regCarlsonLSlit_three_node (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j k : ι) :
    (z i - z j) * regCarlsonLSlit t (b - Pi.single k 1) z +
      (z j - z k) * regCarlsonLSlit t (b - Pi.single i 1) z +
      (z k - z i) * regCarlsonLSlit t (b - Pi.single j 1) z = 0 := by
  have hterm (i j k : ι) : AnalyticOnNhd ℂ
      (fun w => (w i - w j) * regCarlsonLSlit t (b - Pi.single k 1) w) carlsonRSlitDomain := by
    intro w hw
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w).sub
      ((ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)).mul
        (analyticOnNhd_regCarlsonLSlit t _ w hw)
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane
    (((hterm i j k).add (hterm j k i)).add (hterm k i j)) analyticOnNhd_const ?_ hz
  intro w hw
  change (w i - w j) * regCarlsonLSlit t (b - Pi.single k 1) w +
    (w j - w k) * regCarlsonLSlit t (b - Pi.single i 1) w +
    (w k - w i) * regCarlsonLSlit t (b - Pi.single j 1) w = 0
  simp_rw [regCarlsonLSlit_eq_continued _ _ hw]
  exact regCarlsonLContinued_three_node t b hw i j k

open scoped Classical in
/-- Equation (3.7), with its R-term and without parameter restrictions. -/
theorem regCarlsonLSlit_tangent_sub (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    (z i - z j) * (t * regCarlsonLSlit (t - 1) b z + regCarlsonRSlit (t - 1) b z) =
      regCarlsonLSlit t (b - Pi.single j 1) z - regCarlsonLSlit t (b - Pi.single i 1) z := by
  have hleft : AnalyticOnNhd ℂ (fun w : ι → ℂ =>
      (w i - w j) * (t * regCarlsonLSlit (t - 1) b w + regCarlsonRSlit (t - 1) b w))
      carlsonRSlitDomain := by
    intro w hw
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt w).sub
      ((ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).analyticAt w)).mul
        ((analyticAt_const.mul (analyticOnNhd_regCarlsonLSlit (t - 1) b w hw)).add
          (analyticOnNhd_regCarlsonRSlit (t - 1) b w hw))
  apply eqOn_carlsonRSlitDomain_of_eqOn_rightHalfPlane hleft
    ((analyticOnNhd_regCarlsonLSlit t _).sub (analyticOnNhd_regCarlsonLSlit t _)) ?_ hz
  intro w hw
  change (w i - w j) * (t * regCarlsonLSlit (t - 1) b w + regCarlsonRSlit (t - 1) b w) =
    regCarlsonLSlit t (b - Pi.single j 1) w - regCarlsonLSlit t (b - Pi.single i 1) w
  simp_rw [regCarlsonLSlit_eq_continued _ _ hw, regCarlsonRSlit_eq_continued _ _ hw]
  exact regCarlsonLContinued_tangent_sub t b hw i j

open scoped Classical in
/-- Equation (3.4) in parameter-lowered form. Regularization eliminates the
ordinary normalization's factor `c - 1`, so no exceptional parameter is excluded. -/
theorem regCarlsonLSlit_sub_dirichletUnit (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i : ι) :
    regCarlsonLSlit t (b - Pi.single i 1) z =
      ((∑ j, b j) + t - 1) * regCarlsonLSlit t b z -
        t * z i * regCarlsonLSlit (t - 1) b z +
        regCarlsonRSlit t b z - z i * regCarlsonRSlit (t - 1) b z := by
  have hunit : addDirichletUnit (b - Pi.single i 1) i = b := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [addDirichletUnit]
    · simp [addDirichletUnit, hji]
  have hsum : (∑ j, ((b - Pi.single i (1 : ℂ)) : ι → ℂ) j) = (∑ j, b j) - 1 := by
    simp [Pi.sub_apply, Finset.sum_sub_distrib]
  have h := regCarlsonLSlit_eq_addDirichletUnit t (b - Pi.single i 1) hz i
  rw [hunit, hsum] at h
  convert h using 1
  ring

open scoped Classical in
/-- Carlson (1987), (3.8), on the full slit domain. The undivided identity
includes coincident nodes and equal indices. -/
theorem regCarlsonLSlit_weighted_tangent_sub (t : ℂ) (b : ι → ℂ)
    {z : ι → ℂ} (hz : z ∈ carlsonRSlitDomain) (i j : ι) :
    ((∑ k, b k) + t - 1) * (z i - z j) * regCarlsonLSlit t b z +
      z j * regCarlsonLSlit t (b - Pi.single i 1) z -
      z i * regCarlsonLSlit t (b - Pi.single j 1) z +
      (z i - z j) * regCarlsonRSlit t b z = 0 := by
  linear_combination z j * regCarlsonLSlit_sub_dirichletUnit t b hz i -
    z i * regCarlsonLSlit_sub_dirichletUnit t b hz j

end DirichletTransform
