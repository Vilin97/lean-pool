/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Code4me2
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProblemStatement
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Differential identities for Navier–Stokes solution differences

Subtraction of the physical differential operators, the difference equation, and pointwise
energy identities are independent of boundary conditions and integration domains. This module
provides that common API for periodic and whole-space energy estimates. Spatial and temporal
slice regularity works over arbitrary real normed spaces, and the nonlinear energy bound works
in any real inner product space.

This separation of the common differential API follows
[Code4me2's refactor](https://github.com/Code4me2/NavierStokesAndEuler/blob/26e896edbdbe1215c0d50ddba24b2b6453646f5f/NavierStokes/SolutionDifference.lean).
The original periodic names remain available as compatibility lemmas.
-/

public section

open Set Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

namespace NavierStokes.SolutionDifference

open ProblemStatement

private theorem infty_add_one_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  simpa only [ENat.coe_top_add_one] using (le_rfl : (∞ : WithTop ℕ∞) ≤ ∞)

/-- The closed time interval `[a, b]` with unrestricted spatial coordinates. -/
@[expose] def slab {X : Type*} (a b : ℝ) : Set (ℝ × X) := Icc a b ×ˢ univ

@[simp] theorem mem_slab {X : Type*} {a b : ℝ} {z : ℝ × X} :
    z ∈ slab a b ↔ z.1 ∈ Icc a b := by
  simp only [slab, mem_prod, mem_univ, and_true]

/-- Enlarging the time interval enlarges its slab. -/
theorem slab_mono {X : Type*} {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    slab (X := X) a b ⊆ slab c d := by
  intro z hz
  exact ⟨⟨hca.trans hz.1.1, hz.1.2.trans hbd⟩, mem_univ _⟩

/-- Differentiate a spatial field in the `i`th standard coordinate direction. -/
@[expose] noncomputable def spatialPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (f : Space → E) (x : Space) : E :=
  fderiv ℝ f x (coordinateVector i)

/-- Coordinate partial derivatives of a continuously differentiable field are continuous. -/
theorem continuous_partial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} (hf : ContDiff ℝ 1 f) (i : Fin 3) : Continuous (spatialPartial i f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem spatial_smooth {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : (ℝ × X) → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (fun x : X => u (t, x)) :=
  hu.comp_contDiff (contDiff_const.prodMk contDiff_id)
    (fun x => show (t, x) ∈ slab a b from ⟨ht, mem_univ x⟩)

theorem smooth_at_interior {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : (ℝ × X) → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Ioo a b) (x : X) : ContDiffAt ℝ ∞ u (t, x) :=
  hu.contDiffAt (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) Filter.univ_mem)

theorem spatialDerivative_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialDerivative (u - v) t x = spatialDerivative u t x - spatialDerivative v t x :=
  fderiv_fun_sub (hu.differentiable (by simp) x)
    (hv.differentiable (by simp) x)

theorem spatialDivergence_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialDivergence (u - v) t x = spatialDivergence u t x - spatialDivergence v t x := by
  simp only [spatialDivergence, spatialDerivative_sub hu hv,
    _root_.sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]

theorem advection_difference {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    advection u t x - advection v t x =
      spatialDerivative u t x ((u - v) (t, x)) +
        spatialDerivative (u - v) t x (v (t, x)) := by
  simp only [advection, spatialDerivative_sub hu hv, Pi.sub_apply,
    map_sub, _root_.sub_apply]
  abel

theorem spatialLaplacian_sub {u v : VelocityField} {t : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x))) (x : Space) :
    spatialLaplacian (u - v) t x = spatialLaplacian u t x - spatialLaplacian v t x := by
  unfold spatialLaplacian
  simp_rw [spatialDerivative_sub hu hv, _root_.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hdu := ((hu.fderiv_right infty_add_one_le).clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => coordinateVector i))).differentiable
      (by simp) x
  have hdv := ((hv.fderiv_right infty_add_one_le).clm_apply
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space => coordinateVector i))).differentiable
      (by simp) x
  dsimp only [spatialDerivative]
  rw [fderiv_fun_sub hdu hdv]
  rfl

theorem pressureGradient_sub {p q : PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x))) (x : Space) :
    pressureGradient (p - q) t x = pressureGradient p t x - pressureGradient q t x := by
  unfold pressureGradient
  have hderiv := fderiv_fun_sub (hp.differentiable (by simp) x)
    (hq.differentiable (by simp) x)
  simp only [Pi.sub_apply, hderiv, _root_.sub_apply, sub_smul,
    Finset.sum_sub_distrib]

theorem temporalDerivative_sub {u v : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (hv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t) :
    temporalDerivative (u - v) t x = temporalDerivative u t x - temporalDerivative v t x := by
  unfold temporalDerivative
  rw [show (fun s => (u - v) (s, x)) = (fun s => u (s, x) - v (s, x)) from rfl,
    fderiv_fun_sub hu hv]
  rfl

/-- Subtract the actual Navier--Stokes residuals, retaining the favorable
transport decomposition `Du(w) + Dw(v)`. -/
theorem difference_equation {u v : VelocityField} {p q : PressureField} {t : ℝ} {x : Space}
    (hu : ContDiff ℝ ∞ (fun y : Space => u (t, y)))
    (hv : ContDiff ℝ ∞ (fun y : Space => v (t, y)))
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y)))
    (hq : ContDiff ℝ ∞ (fun y : Space => q (t, y)))
    (htu : DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t)
    (htv : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t)
    (hNS : navierStokesResidual u p t x = navierStokesResidual v q t x) :
    temporalDerivative (u - v) t x = spatialLaplacian (u - v) t x -
      spatialDerivative u t x ((u - v) (t, x)) -
      spatialDerivative (u - v) t x (v (t, x)) - pressureGradient (p - q) t x := by
  have ha := advection_difference hu hv x
  rw [temporalDerivative_sub htu htv, spatialLaplacian_sub hu hv,
    pressureGradient_sub hp hq]
  unfold navierStokesResidual at hNS
  have heq := sub_eq_zero.mpr hNS
  rw [show temporalDerivative u t x + advection u t x - spatialLaplacian u t x +
      pressureGradient p t x -
      (temporalDerivative v t x + advection v t x - spatialLaplacian v t x +
        pressureGradient q t x) =
      temporalDerivative u t x - temporalDerivative v t x +
        (advection u t x - advection v t x) -
        (spatialLaplacian u t x - spatialLaplacian v t x) +
        (pressureGradient p t x - pressureGradient q t x) by abel, ha] at heq
  apply sub_eq_zero.mp
  convert! heq using 1
  abel

/-- The adverse quadratic energy term is bounded by an operator norm bound in any
real inner product space. -/
theorem nonlinear_energy_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (A : V →L[ℝ] V) (w : V) {B : ℝ}
    (hB : ‖A‖ ≤ B) : -⟪w, A w⟫_ℝ ≤ B * ‖w‖ ^ 2 := by
  calc
    -⟪w, A w⟫_ℝ ≤ |⟪w, A w⟫_ℝ| := neg_le_abs _
    _ ≤ ‖w‖ * ‖A w‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖A‖ * ‖w‖) := mul_le_mul_of_nonneg_left (A.le_opNorm w) (norm_nonneg w)
    _ ≤ ‖w‖ * (B * ‖w‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hB (norm_nonneg w)) (norm_nonneg w)
    _ = B * ‖w‖ ^ 2 := by ring

/-- The ordinary spatial derivative at a time endpoint is the restriction
of the joint within-derivative to spatial directions. -/
theorem spatialDerivative_eq_within_comp {a b t : ℝ} {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) (ht : t ∈ Icc a b) (x : Space) :
    spatialDerivative u t x =
      (fderivWithin ℝ u (slab a b) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd := (hu.differentiableOn (by simp) (t, x) ⟨ht, mem_univ x⟩).hasFDerivWithinAt
  have hs := hd.comp x (s := univ) (hasFDerivAt_prodMk_right t x).hasFDerivWithinAt
    (fun y _ => show (t, y) ∈ slab a b from ⟨ht, mem_univ y⟩)
  have hs' : HasFDerivAt (fun y : Space => u (t, y))
      ((fderivWithin ℝ u (slab a b) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
    simpa only [Function.comp_def, hasFDerivWithinAt_univ] using hs
  exact hs'.fderiv

/-- Compactness supplies the spatial-gradient bound used by the energy
estimate; it is a conclusion from smoothness, not an input to uniqueness. -/
theorem exists_gradient_bound {a b : ℝ} (hab : a < b) {u : VelocityField}
    (hu : ContDiffOn ℝ ∞ u (slab a b)) {K : Set Space} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x ∈ K, ‖spatialDerivative u t x‖ ≤ B := by
  have hs : UniqueDiffOn ℝ (slab (X := Space) a b) :=
    (uniqueDiffOn_Icc hab).prod uniqueDiffOn_univ
  have hD := (hu.fderivWithin hs infty_add_one_le).continuousOn
  have hDK : ContinuousOn (fderivWithin ℝ u (slab a b)) (Icc a b ×ˢ K) :=
    hD.mono (fun z hz => ⟨hz.1, mem_univ z.2⟩)
  obtain ⟨B, hBpos, hB⟩ := ((isCompact_Icc.prod hK).image_of_continuousOn
      hDK).isBounded.exists_pos_norm_le
  refine ⟨B, hBpos, ?_⟩
  intro t ht x hx
  apply ContinuousLinearMap.opNorm_le_bound _ hBpos.le
  intro w
  rw [spatialDerivative_eq_within_comp hu ht x, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  calc
    ‖(fderivWithin ℝ u (slab a b) (t, x)) (0, w)‖ ≤
        ‖fderivWithin ℝ u (slab a b) (t, x)‖ * ‖((0 : ℝ), w)‖ :=
      (fderivWithin ℝ u (slab a b) (t, x)).le_opNorm _
    _ ≤ B * ‖((0 : ℝ), w)‖ := mul_le_mul_of_nonneg_right
      (hB _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩) (norm_nonneg _)
    _ = B * ‖w‖ := by simp

/-- Reconstruction in the standard Euclidean coordinate basis. -/
theorem sum_coordinates (x : Space) :
    (∑ i : Fin 3, x i • coordinateVector i) = x := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  ext j
  change (EuclideanSpace.proj j) (∑ i : Fin 3, x i • coordinateVector i) = x j
  simp only [map_sum, map_smul]
  simp [coordinateVector]

theorem spatial_partial_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Space → V} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x (coordinateVector i)) :=
  (hf.fderiv_right infty_add_one_le).clm_apply contDiff_const

theorem component_contDiff {f : Space → Space} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => f x j) :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hf

theorem fderiv_component {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (j : Fin 3) (x v : Space) :
    fderiv ℝ (fun y => f y j) x v = fderiv ℝ f x v j := by
  have h := ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
    (hf.differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun A : Space →L[ℝ] ℝ => A v) h

theorem fderiv_apply_eq_sum (f : Space → ℝ) (x v : Space) :
    fderiv ℝ f x v = ∑ i : Fin 3, v i * fderiv ℝ f x (coordinateVector i) := by
  conv_lhs => rw [← sum_coordinates v]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem fderiv_normsq {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : X → V} (hf : ContDiff ℝ ∞ f) (x v : X) :
    fderiv ℝ (fun y => ‖f y‖ ^ 2) x v = 2 * ⟪f x, fderiv ℝ f x v⟫_ℝ := by
  rw [((hf.differentiable (by simp) x).hasFDerivAt.norm_sq).fderiv]
  simp

theorem fderiv_inner {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f g : X → V} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x v : X) :
    fderiv ℝ (fun y => ⟪f y, g y⟫_ℝ) x v =
      ⟪f x, fderiv ℝ g x v⟫_ℝ + ⟪fderiv ℝ f x v, g x⟫_ℝ := by
  rw [((hf.differentiable (by simp) x).hasFDerivAt.inner ℝ
    (hg.differentiable (by simp) x).hasFDerivAt).fderiv]
  rfl

/-- The pressure term paired with a vector is its scalar directional
derivative. This uses exactly the gradient definition in the target. -/
theorem inner_pressureGradient (p : PressureField) (t : ℝ) (x w : Space) :
    ⟪w, pressureGradient p t x⟫_ℝ = fderiv ℝ (fun y => p (t, y)) x w := by
  rw [fderiv_apply_eq_sum]
  simp only [pressureGradient, inner_sum, inner_smul_right, coordinateVector,
    EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem energy_density_derivative {u : VelocityField} {t : ℝ} {x : Space}
    (hu : DifferentiableAt ℝ (fun s => u (s, x)) t) :
    HasDerivAt (fun s : ℝ => ‖u (s, x)‖ ^ 2)
      (2 * ⟪u (t, x), temporalDerivative u t x⟫_ℝ) t :=
  hu.hasDerivAt.norm_sq

theorem spatialLaplacian_contDiff {w : VelocityField} {t : ℝ}
    (hw : ContDiff ℝ ∞ (fun x : Space => w (t, x))) :
    ContDiff ℝ ∞ (spatialLaplacian w t) := by
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ (fun y => w (t, y)) y (coordinateVector i)) x
      (coordinateVector i))
  exact ContDiff.sum fun i _ => spatial_partial_contDiff (spatial_partial_contDiff hw i) i

theorem pressureGradient_contDiff {p : PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x))) :
    ContDiff ℝ ∞ (pressureGradient p t) := by
  change ContDiff ℝ ∞ (fun x => ∑ i : Fin 3,
    fderiv ℝ (fun y => p (t, y)) x (coordinateVector i) • coordinateVector i)
  exact ContDiff.sum fun i _ => (spatial_partial_contDiff hp i).smul contDiff_const

theorem time_differentiable_at_interior {X V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b t : ℝ} {u : (ℝ × X) → V} (hu : ContDiffOn ℝ ∞ u (slab a b))
    (ht : t ∈ Ioo a b) (x : X) :
    DifferentiableAt ℝ (fun s : ℝ => u (s, x)) t :=
  ((smooth_at_interior hu ht x).comp t
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

end NavierStokes.SolutionDifference
