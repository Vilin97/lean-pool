/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersShift
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersOpen
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Kernel All Orders Potential

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

universe u

open scoped BigOperators Topology
open MeasureTheory
open CKN.Foundation.Parabolic


/-!
# Potentials of singular kernels away from the support of their density

Let `K` be a kernel that is of every finite differentiability order away from
the origin and whose `j`-th derivative is bounded by `C j ‖z‖₂^{-(m + j)}`, and
let `g` be an integrable density vanishing outside a set `A` separated from an
open set `U` by a distance `δ > 0`.  Then the potential

  `P x = ∫ y, g y • K (x - y)`

is of every finite differentiability order on `U`, its derivative on `U` is the
potential of `fderiv K`, and

  `‖D^k P x‖ ≤ C k δ^{-(m + k)} ‖g‖₁`  for `x ∈ U`.

These are the smooth-off-the-support statements `eq:har-Ck` used by the local
pressure decomposition of `cor:CZ-harmonic`.
-/

noncomputable section

namespace CKN.Foundation.Heat

/-- The potential of a kernel `K` against a density `g`. -/
@[expose] def kernelPotential {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Vec3 → F) (g : Vec3 → ℝ) (x : Vec3) : F :=
  ∫ y : Vec3, g y • K (x - y)

/-- Integrability of the potential integrand under a uniform bound on the density support. -/
theorem integrable_smul_kernel_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Vec3 → F} {g : Vec3 → ℝ} {A : Set Vec3} {M : ℝ} {x : Vec3}
    (hKc : ContinuousOn K {z : Vec3 | z ≠ 0}) (hg : Integrable g volume)
    (hg0 : ∀ y : Vec3, y ∉ A → g y = 0)
    (hbd : ∀ y ∈ A, ‖K (x - y)‖ ≤ M) :
    Integrable (fun y : Vec3 => g y • K (x - y)) volume := by
  refine Integrable.mono' (hg.norm.mul_const M)
    (aestronglyMeasurable_smul_kernel_shift hKc hg.aestronglyMeasurable x) ?_
  filter_upwards [] with y
  by_cases hy : y ∈ A
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbd y hy) (abs_nonneg _)
  · rw [hg0 y hy]
    simp

/-- Differentiation under the integral sign for a potential, away from the density support. -/
theorem hasFDerivAt_kernelPotential {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Vec3 → F} {g : Vec3 → ℝ} {A U : Set Vec3} {δ M₀ M₁ : ℝ}
    (hKdiff : ∀ z : Vec3, z ≠ 0 → DifferentiableAt ℝ K z)
    (hKc : ContinuousOn K {z : Vec3 | z ≠ 0})
    (hK'c : ContinuousOn (fderiv ℝ K) {z : Vec3 | z ≠ 0})
    (hKb : ∀ z : Vec3, δ ≤ vec3EuclideanNorm z → ‖K z‖ ≤ M₀)
    (hK'b : ∀ z : Vec3, δ / 2 ≤ vec3EuclideanNorm z → ‖fderiv ℝ K z‖ ≤ M₁)
    (hg : Integrable g volume) (hg0 : ∀ y : Vec3, y ∉ A → g y = 0)
    (hδ : 0 < δ) (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y))
    {x : Vec3} (hx : x ∈ U) :
    HasFDerivAt (kernelPotential K g) (kernelPotential (fderiv ℝ K) g x) x := by
  have hsepx : ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y) := hsep x hx
  have hsep2 : ∀ z ∈ Metric.ball x (δ / 6), ∀ y ∈ A,
      δ / 2 ≤ vec3EuclideanNorm (z - y) := by
    intro z hz y hy
    have hzx : ‖z - x‖ < δ / 6 := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact hz
    exact half_le_vec3EuclideanNorm_sub hδ hzx (hsepx y hy)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun z y : Vec3 => g y • K (z - y))
    (F' := fun z y : Vec3 => g y • fderiv ℝ K (z - y))
    (bound := fun y : Vec3 => ‖g y‖ * M₁) (s := Metric.ball x (δ / 6))
    (Metric.ball_mem_nhds x (by positivity)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun z =>
      aestronglyMeasurable_smul_kernel_shift hKc hg.aestronglyMeasurable z
  · exact integrable_smul_kernel_shift hKc hg hg0 (fun y hy => hKb _ (hsepx y hy))
  · exact aestronglyMeasurable_smul_kernel_shift hK'c hg.aestronglyMeasurable x
  · filter_upwards [] with y z hz
    by_cases hy : y ∈ A
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hK'b _ (hsep2 z hz y hy)) (abs_nonneg _)
    · rw [hg0 y hy]
      simp
  · exact hg.norm.mul_const M₁
  · filter_upwards [] with y z hz
    by_cases hy : y ∈ A
    · have hne : z - y ≠ 0 := by
        refine ne_zero_of_vec3EuclideanNorm_pos ?_
        exact lt_of_lt_of_le (by positivity) (hsep2 z hz y hy)
      have hcomp : HasFDerivAt (fun w : Vec3 => K (w - y)) (fderiv ℝ K (z - y)) z := by
        have hsub : HasFDerivAt (fun w : Vec3 => w - y)
            (ContinuousLinearMap.id ℝ Vec3) z := hasFDerivAt_sub_const (𝕜 := ℝ) y
        have h := (hKdiff _ hne).hasFDerivAt.comp z hsub
        rw [ContinuousLinearMap.comp_id] at h
        exact h
      exact hcomp.const_smul (g y)
    · rw [hg0 y hy]
      simpa using (hasFDerivAt_const (0 : F) z)

/-! ### Consequences of the all-order kernel hypotheses -/

section KernelData

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Vec3 → F}

/-- A kernel of every finite order off the origin is differentiable there. -/
theorem differentiableAt_of_kernelSmooth
    (hsmooth : ∀ (n : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ n K z)
    (z : Vec3) (hz : z ≠ 0) : DifferentiableAt ℝ K z :=
  (hsmooth 1 z hz).differentiableAt (by simp)

/-- A kernel of every finite order off the origin is continuous there. -/
theorem continuousOn_of_kernelSmooth
    (hsmooth : ∀ (n : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ n K z) :
    ContinuousOn K {z : Vec3 | z ≠ 0} := fun z hz =>
  (hsmooth 0 z hz).continuousAt.continuousWithinAt

/-- The derivative of a kernel of every finite order off the origin has the same property. -/
theorem contDiffAt_fderiv_of_kernelSmooth
    (hsmooth : ∀ (n : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ n K z)
    (n : ℕ) (z : Vec3) (hz : z ≠ 0) : ContDiffAt ℝ n (fderiv ℝ K) z := by
  have hcast : ((n : ℕ) : WithTop ℕ∞) + 1 = ((n + 1 : ℕ) : WithTop ℕ∞) := by
    push_cast
    ring
  have h : ContDiffAt ℝ (((n : ℕ) : WithTop ℕ∞) + 1) K z := by
    rw [hcast]
    exact hsmooth (n + 1) z hz
  exact h.fderiv_right_succ

/-- The zeroth-order kernel bound at Euclidean distance at least `δ`. -/
theorem kernelBound_zero {C : ℕ → ℝ} {m : ℕ} {δ : ℝ} (hC : ∀ j, 0 ≤ C j)
    (hbound : ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹)
    (hδ : 0 < δ) :
    ∀ z : Vec3, δ ≤ vec3EuclideanNorm z → ‖K z‖ ≤ C 0 * (δ ^ m)⁻¹ := by
  intro z hz
  have hzne : z ≠ 0 := ne_zero_of_vec3EuclideanNorm_pos (lt_of_lt_of_le hδ hz)
  have h := hbound 0 z hzne
  rw [norm_iteratedFDeriv_zero] at h
  refine h.trans ?_
  have hmono : (vec3EuclideanNorm z ^ (m + 0))⁻¹ ≤ (δ ^ m)⁻¹ := by
    rw [Nat.add_zero]
    exact inv_pow_le_inv_pow_of_le hδ hz m
  exact mul_le_mul_of_nonneg_left hmono (hC 0)

/-- The first-order kernel bound at Euclidean distance at least `δ / 2`. -/
theorem kernelBound_one {C : ℕ → ℝ} {m : ℕ} {δ : ℝ} (hC : ∀ j, 0 ≤ C j)
    (hbound : ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹)
    (hδ : 0 < δ) :
    ∀ z : Vec3, δ / 2 ≤ vec3EuclideanNorm z →
      ‖fderiv ℝ K z‖ ≤ C 1 * ((δ / 2) ^ (m + 1))⁻¹ := by
  intro z hz
  have hhalf : 0 < δ / 2 := by positivity
  have hzne : z ≠ 0 := ne_zero_of_vec3EuclideanNorm_pos (lt_of_lt_of_le hhalf hz)
  have h := hbound 1 z hzne
  rw [norm_iteratedFDeriv_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (inv_pow_le_inv_pow_of_le hhalf hz (m + 1)) (hC 1))

/-- The all-order bounds pass from a kernel to its derivative, with the exponent shifted. -/
theorem iteratedFDeriv_fderiv_bound {C : ℕ → ℝ} {m : ℕ}
    (hbound : ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹) :
    ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j (fderiv ℝ K) z‖ ≤
        C (j + 1) * (vec3EuclideanNorm z ^ (m + 1 + j))⁻¹ := by
  intro j z hz
  rw [norm_iteratedFDeriv_fderiv, show m + 1 + j = m + (j + 1) by ring]
  exact hbound (j + 1) z hz

end KernelData

/-! ### Smoothness and all-order bounds for the potential -/

section Potential

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Vec3 → F}
  {C : ℕ → ℝ} {m : ℕ} {g : Vec3 → ℝ} {A U : Set Vec3} {δ : ℝ}

/-- The potential differentiates under the integral sign at every point of `U`. -/
theorem hasFDerivAt_kernelPotential_of_data (hC : ∀ j, 0 ≤ C j)
    (hsmooth : ∀ (i : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ i K z)
    (hbound : ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹)
    (hg : Integrable g volume) (hg0 : ∀ y : Vec3, y ∉ A → g y = 0) (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y))
    {x : Vec3} (hx : x ∈ U) :
    HasFDerivAt (kernelPotential K g) (kernelPotential (fderiv ℝ K) g x) x :=
  hasFDerivAt_kernelPotential (differentiableAt_of_kernelSmooth hsmooth)
    (continuousOn_of_kernelSmooth hsmooth)
    (continuousOn_of_kernelSmooth (contDiffAt_fderiv_of_kernelSmooth hsmooth))
    (kernelBound_zero hC hbound hδ) (kernelBound_one hC hbound hδ) hg hg0 hδ hsep hx

/-- The potential is differentiable on `U`. -/
theorem differentiableOn_kernelPotential (hC : ∀ j, 0 ≤ C j)
    (hsmooth : ∀ (i : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ i K z)
    (hbound : ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹)
    (hg : Integrable g volume) (hg0 : ∀ y : Vec3, y ∉ A → g y = 0) (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    DifferentiableOn ℝ (kernelPotential K g) U := fun _z hz =>
  (hasFDerivAt_kernelPotential_of_data hC hsmooth hbound hg hg0 hδ hsep
    hz).differentiableAt.differentiableWithinAt

/-- On `U` the derivative of the potential is the potential of the differentiated kernel. -/
theorem fderiv_kernelPotential_eqOn (hC : ∀ j, 0 ≤ C j)
    (hsmooth : ∀ (i : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ i K z)
    (hbound : ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹)
    (hg : Integrable g volume) (hg0 : ∀ y : Vec3, y ∉ A → g y = 0) (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    Set.EqOn (fderiv ℝ (kernelPotential K g)) (kernelPotential (fderiv ℝ K) g) U := fun _z hz =>
  (hasFDerivAt_kernelPotential_of_data hC hsmooth hbound hg hg0 hδ hsep hz).fderiv

end Potential

private theorem contDiffOn_kernelPotential_aux
    {g : Vec3 → ℝ} {A U : Set Vec3} {δ : ℝ}
    (hg : Integrable g volume) (hU : IsOpen U)
    (hg0 : ∀ y : Vec3, y ∉ A → g y = 0) (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Vec3 → F}
      {C : ℕ → ℝ} {m : ℕ}, (∀ j, 0 ≤ C j) →
      (∀ (i : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ i K z) →
      (∀ (j : ℕ) (z : Vec3), z ≠ 0 →
        ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹) →
      ContDiffOn ℝ (n : ℕ) (kernelPotential K g) U := by
  induction n with
  | zero =>
      intro F _ _ K C m hC hsmooth hbound
      rw [Nat.cast_zero, contDiffOn_zero]
      exact (differentiableOn_kernelPotential hC hsmooth hbound hg hg0 hδ hsep).continuousOn
  | succ n ih =>
      intro F _ _ K C m hC hsmooth hbound
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 := by
        push_cast
        ring
      rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨differentiableOn_kernelPotential hC hsmooth hbound hg hg0 hδ hsep, ?_, ?_⟩
      · simp
      · exact ContDiffOn.congr
          (ih (K := fderiv ℝ K) (C := fun j => C (j + 1)) (m := m + 1)
            (fun j => hC (j + 1)) (contDiffAt_fderiv_of_kernelSmooth hsmooth)
            (iteratedFDeriv_fderiv_bound hbound))
          (fderiv_kernelPotential_eqOn hC hsmooth hbound hg hg0 hδ hsep)

private theorem norm_iteratedFDeriv_kernelPotential_le_aux
    {g : Vec3 → ℝ} {A U : Set Vec3} {δ : ℝ}
    (hg : Integrable g volume) (hU : IsOpen U)
    (hg0 : ∀ y : Vec3, y ∉ A → g y = 0) (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) (k : ℕ)
    {x : Vec3} (hx : x ∈ U) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Vec3 → F}
      {C : ℕ → ℝ} {m : ℕ}, (∀ j, 0 ≤ C j) →
      (∀ (i : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ i K z) →
      (∀ (j : ℕ) (z : Vec3), z ≠ 0 →
        ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹) →
      ‖iteratedFDeriv ℝ k (kernelPotential K g) x‖ ≤
        C k * (δ ^ (m + k))⁻¹ * ∫ y : Vec3, ‖g y‖ := by
  induction k with
  | zero =>
      intro F _ _ K C m hC hsmooth hbound
      have hKc := continuousOn_of_kernelSmooth hsmooth
      have hM := kernelBound_zero hC hbound hδ
      have hint : Integrable (fun y : Vec3 => g y • K (x - y)) volume :=
        integrable_smul_kernel_shift hKc hg hg0 (fun y hy => hM _ (hsep x hx y hy))
      have hpt : ∀ y : Vec3, ‖g y • K (x - y)‖ ≤ ‖g y‖ * (C 0 * (δ ^ m)⁻¹) := by
        intro y
        by_cases hy : y ∈ A
        · rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hM _ (hsep x hx y hy)) (norm_nonneg _)
        · rw [hg0 y hy]
          simp
      rw [norm_iteratedFDeriv_zero]
      calc ‖kernelPotential K g x‖ ≤ ∫ y : Vec3, ‖g y • K (x - y)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ y : Vec3, ‖g y‖ * (C 0 * (δ ^ m)⁻¹) :=
            integral_mono hint.norm (hg.norm.mul_const _) hpt
        _ = C 0 * (δ ^ (m + 0))⁻¹ * ∫ y : Vec3, ‖g y‖ := by
            rw [integral_mul_const, Nat.add_zero]
            ring
  | succ k ih =>
      intro F _ _ K C m hC hsmooth hbound
      have hfd := fderiv_kernelPotential_eqOn hC hsmooth hbound hg hg0 hδ hsep
      calc ‖iteratedFDeriv ℝ (k + 1) (kernelPotential K g) x‖
          = ‖iteratedFDeriv ℝ k (fderiv ℝ (kernelPotential K g)) x‖ :=
            norm_iteratedFDeriv_fderiv.symm
        _ = ‖iteratedFDeriv ℝ k (kernelPotential (fderiv ℝ K) g) x‖ := by
            rw [iteratedFDeriv_eq_of_eqOn_isOpen hU hfd k hx]
        _ ≤ C (k + 1) * (δ ^ (m + 1 + k))⁻¹ * ∫ y : Vec3, ‖g y‖ :=
            ih (K := fderiv ℝ K) (C := fun j => C (j + 1)) (m := m + 1)
              (fun j => hC (j + 1)) (contDiffAt_fderiv_of_kernelSmooth hsmooth)
              (iteratedFDeriv_fderiv_bound hbound)
        _ = C (k + 1) * (δ ^ (m + (k + 1)))⁻¹ * ∫ y : Vec3, ‖g y‖ := by
            rw [show m + 1 + k = m + (k + 1) by ring]

/-- A real-valued potential written with the kernel on the left, as in the pressure terms. -/
theorem kernelPotential_real_eq (K : Vec3 → ℝ) (g : Vec3 → ℝ) (x : Vec3) :
    kernelPotential K g x = ∫ y : Vec3, K (x - y) * g y := by
  rw [kernelPotential]
  congr 1
  funext y
  rw [smul_eq_mul, mul_comm]

/-- The potential of a separated density has every finite differentiability order on `U`;
this is the smoothness half of `eq:har-Ck`. -/
theorem contDiffOn_kernelPotential {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Vec3 → F} {C : ℕ → ℝ} {m : ℕ} {g : Vec3 → ℝ} {A U : Set Vec3} {δ : ℝ}
    (hC : ∀ j, 0 ≤ C j)
    (hsmooth : ∀ (i : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ i K z)
    (hbound : ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹)
    (hg : Integrable g volume) (hU : IsOpen U) (hg0 : ∀ y : Vec3, y ∉ A → g y = 0)
    (hδ : 0 < δ) (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) (n : ℕ) :
    ContDiffOn ℝ (n : ℕ) (kernelPotential K g) U :=
  contDiffOn_kernelPotential_aux hg hU hg0 hδ hsep n hC hsmooth hbound

/-- The all-order size of the potential of a separated density; this is the bound half of
`eq:har-Ck`. -/
theorem norm_iteratedFDeriv_kernelPotential_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Vec3 → F} {C : ℕ → ℝ} {m : ℕ} {g : Vec3 → ℝ} {A U : Set Vec3}
    {δ : ℝ} (hC : ∀ j, 0 ≤ C j)
    (hsmooth : ∀ (i : ℕ) (z : Vec3), z ≠ 0 → ContDiffAt ℝ i K z)
    (hbound : ∀ (j : ℕ) (z : Vec3), z ≠ 0 →
      ‖iteratedFDeriv ℝ j K z‖ ≤ C j * (vec3EuclideanNorm z ^ (m + j))⁻¹)
    (hg : Integrable g volume) (hU : IsOpen U) (hg0 : ∀ y : Vec3, y ∉ A → g y = 0)
    (hδ : 0 < δ) (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) (k : ℕ)
    {x : Vec3} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ k (kernelPotential K g) x‖ ≤
      C k * (δ ^ (m + k))⁻¹ * ∫ y : Vec3, ‖g y‖ :=
  norm_iteratedFDeriv_kernelPotential_le_aux hg hU hg0 hδ hsep k hx hC hsmooth hbound

end CKN.Foundation.Heat
