/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Complex
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Kernel
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Complex.Convex

/-!
# Carlson's Dirichlet averages: basic definitions

This file specializes the regularized Dirichlet integral to a univariate function evaluated
at the affine form `∑ i, u i * z i`.  It contains the algebraic and convex-geometric material
used by both the native integral theory of Carlson's Chapter 5 and its analytic continuation
in Chapter 6.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Chapters 5 and 6,
  Academic Press, 1977.
-/

open Complex MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section CarlsonDirichletAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The multivariate polynomial whose value is Carlson's affine form. -/
def carlsonAffinePolynomial (z : ι → ℂ) : MvPolynomial ι ℂ :=
  ∑ i, MvPolynomial.C (z i) * MvPolynomial.X i

/-- Evaluation of `carlsonAffinePolynomial` gives the corresponding affine form. -/
@[simp] theorem eval_carlsonAffinePolynomial (z x : ι → ℂ) :
    (carlsonAffinePolynomial z).eval x = ∑ i, x i * z i := by
  simp [carlsonAffinePolynomial, mul_comm]

/-- The polynomial representing the `n`th power of Carlson's affine form. -/
def carlsonPowerPolynomial (n : ℕ) (z : ι → ℂ) : MvPolynomial ι ℂ :=
  (carlsonAffinePolynomial z) ^ n

/-- Evaluation of `carlsonPowerPolynomial` gives the corresponding power of the affine form. -/
@[simp] theorem eval_carlsonPowerPolynomial (n : ℕ) (z : ι → ℂ) (u : ι → ℝ) :
    (carlsonPowerPolynomial n z).eval (fun i ↦ (u i : ℂ)) =
      carlsonAffineForm z u ^ n := by
  simp [carlsonPowerPolynomial, carlsonAffineForm]

/-- Carlson's Dirichlet average divided by `Γ(∑ i, b i)`, on the native integral domain.

The function supplied to the simplex integral is `u ↦ f (∑ i, u i * z i)`. -/
def regCarlsonDirichletAverage (b z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  regDirichletIntegral b (fun u ↦ f (carlsonAffineForm z u))

/-- Carlson's native (unregularized) Dirichlet average on the convergence region. -/
def carlsonDirichletAverage (b z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonDirichletAverage b z f

/-! ## The native averaging process -/

/-- Simultaneously permuting the simplex coordinates and the parameters of the affine form
does not change that affine form. -/
@[simp] theorem carlsonAffineForm_perm (z : ι → ℂ) (σ : Equiv.Perm ι) (u : ι → ℝ) :
    carlsonAffineForm (z ∘ σ) (u ∘ σ) = carlsonAffineForm z u := by
  unfold carlsonAffineForm
  simpa only [Function.comp_apply] using
    Equiv.sum_comp σ (fun i ↦ (u i : ℂ) * z i)

/-- The affine form of a constant parameter vector is constant on the standard simplex. -/
theorem carlsonAffineForm_const {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) (w : ℂ) :
    carlsonAffineForm (fun _ ↦ w) u = w := by
  rw [carlsonAffineForm, ← Finset.sum_mul]
  have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
  rw [hsum, one_mul]

/-- Simultaneous permutation of the Dirichlet parameters and the variables leaves the native
regularized Carlson average unchanged.  This is the regularized form of Carlson's
Theorem 5.2-3. -/
theorem regCarlsonDirichletAverage_perm (b z : ι → ℂ) (f : ℂ → ℂ)
    (σ : Equiv.Perm ι) :
    regCarlsonDirichletAverage (b ∘ σ) (z ∘ σ) f =
      regCarlsonDirichletAverage b z f := by
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_stdSimplex_comp_perm σ
    (fun u ↦ regDirichletDensity (b ∘ σ) u * f (carlsonAffineForm (z ∘ σ) u))]
  congr 1
  funext u
  rw [regDirichletDensity_perm, carlsonAffineForm_perm]

/-- On the diagonal, the native regularized Carlson average is `f(w) / Γ(∑ i, b i)`.
This is the regularized form of Carlson's equation (5.2-2). -/
theorem regCarlsonDirichletAverage_const (f : ℂ → ℂ) (w : ℂ)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonDirichletAverage b (fun _ ↦ w) f =
      f w / Gamma (∑ i, b i) := by
  unfold regCarlsonDirichletAverage
  rw [regDirichletIntegral_congr b
    (g := fun _ ↦ f w) (fun u hu ↦ congrArg f (carlsonAffineForm_const hu w))]
  have hsmul := regDirichletIntegral_smul b (fun _ ↦ (1 : ℂ)) (f w)
  simp only [mul_one] at hsmul
  rw [hsmul]
  rw [show regDirichletIntegral b (fun _ ↦ (1 : ℂ)) =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, regDirichletDensity b u ∂stdSimplexMeasure by
    simp [regDirichletIntegral]]
  rw [regDirichletIntegral_normalization b hb]
  simp [div_eq_mul_inv]

/-- Affine changes in the variables commute with Carlson's affine form on the standard
simplex. -/
theorem carlsonAffineForm_affine {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι)
    (a t : ℂ) (z : ι → ℂ) :
    carlsonAffineForm (fun i ↦ a * z i + t) u = a * carlsonAffineForm z u + t := by
  have hsum : ∑ i, (u i : ℂ) = 1 := by exact_mod_cast hu.2
  unfold carlsonAffineForm
  calc
    ∑ i, (u i : ℂ) * (a * z i + t) =
        ∑ i, (a * ((u i : ℂ) * z i) + (u i : ℂ) * t) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * ∑ i, (u i : ℂ) * z i + (∑ i, (u i : ℂ)) * t := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = a * ∑ i, (u i : ℂ) * z i + t := by rw [hsum, one_mul]

/-- Precomposing the averaged function by an affine map is equivalent to applying the same
affine map to every variable.  This is Carlson's Theorem 5.2-6. -/
theorem regCarlsonDirichletAverage_comp_affine (b z : ι → ℂ) (f : ℂ → ℂ) (a t : ℂ) :
    regCarlsonDirichletAverage b z (fun w ↦ f (a * w + t)) =
      regCarlsonDirichletAverage b (fun i ↦ a * z i + t) f := by
  unfold regCarlsonDirichletAverage
  apply regDirichletIntegral_congr
  intro u hu
  change f (a * carlsonAffineForm z u + t) =
    f (carlsonAffineForm (fun i ↦ a * z i + t) u)
  rw [carlsonAffineForm_affine hu]



/-- On the standard simplex, Carlson's affine form is bounded by the sum of the norms of
its variables. -/
theorem norm_carlsonAffineForm_le_sum_norm (z : ι → ℂ) {u : ι → ℝ}
    (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    ‖carlsonAffineForm z u‖ ≤ ∑ i, ‖z i‖ := by
  unfold carlsonAffineForm
  calc
    ‖∑ i, (u i : ℂ) * z i‖ ≤ ∑ i, ‖(u i : ℂ) * z i‖ := norm_sum_le _ _
    _ = ∑ i, u i * ‖z i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    _ ≤ ∑ i, ‖z i‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hui : u i ≤ 1 := by
        calc
          u i ≤ ∑ j, u j :=
            Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i)
          _ = 1 := hu.2
      exact mul_le_of_le_one_left (norm_nonneg _) hui

/-- The denominator in Carlson's resolvent is nonzero off the convex hull of `z`. -/
theorem sub_carlsonAffineForm_ne_zero {s : ℂ} {z : ι → ℂ} {u : ι → ℝ}
    (hs : s ∉ convexHull ℝ (Set.range z)) (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    s - carlsonAffineForm z u ≠ 0 := by
  intro h
  apply hs
  rw [sub_eq_zero.mp h]
  exact carlsonAffineForm_mem_convexHull z hu

/-- The open right half-plane, an important domain for Carlson's power and resolvent
constructions. -/
def carlsonRightHalfPlane : Set ℂ :=
  {w | 0 < w.re}

/-- The right half-plane is open. -/
theorem isOpen_carlsonRightHalfPlane : IsOpen carlsonRightHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- The right half-plane is convex over the real scalars. -/
theorem convex_carlsonRightHalfPlane : Convex ℝ carlsonRightHalfPlane := by
  exact convex_halfSpace_re_gt 0

/-- A convenient name for the hypothesis that a univariate function is holomorphic on the
right half-plane. -/
def HolomorphicOnCarlsonRightHalfPlane (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f carlsonRightHalfPlane

/-- A complex scalar can be pulled through a regularized Carlson average. -/
theorem regCarlsonDirichletAverage_const_mul (b z : ι → ℂ) (c : ℂ) (f : ℂ → ℂ) :
    regCarlsonDirichletAverage b z (fun w => c * f w) =
      c * regCarlsonDirichletAverage b z f := by
  unfold regCarlsonDirichletAverage
  exact regDirichletIntegral_smul b _ c

/-- A finite sum can be passed through a regularized Carlson average on the native convergence
domain. -/
theorem regCarlsonDirichletAverage_finsetSum {κ : Type*} {s : Finset κ}
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (f : κ → ℂ → ℂ)
    (hf : ∀ k ∈ s, ContinuousOn (fun u : ι → ℝ => f k (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    regCarlsonDirichletAverage b z (fun w => ∑ k ∈ s, f k w) =
      ∑ k ∈ s, regCarlsonDirichletAverage b z (f k) := by
  unfold regCarlsonDirichletAverage regDirichletIntegral
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  intro k hk
  exact integrableOn_regDirichletDensity_mul b hb (hf k hk)

end DirichletTransform

end CarlsonDirichletAverage
