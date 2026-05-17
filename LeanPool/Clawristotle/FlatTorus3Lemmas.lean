/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs

/-!
# Derived Lemmas for the FlatTorus3 Typeclass

Lemmas derived from the `FlatTorus3` axioms: spatial multiplication, gradient vanishing,
chain rules for log, integration by parts consequences, Laplacian sign at extrema,
and Maxwellian parameter regularity.
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

namespace FlatTorus3

variable {X : Type*} [FlatTorus3 X]

lemma _root_.VML.FlatTorus3.IsSpatiallySmooth.of_le {n m : ℕ∞} {f : X → ℝ}
    (h : IsSpatiallySmooth n f) (hle : m ≤ n) : IsSpatiallySmooth m f :=
  hDiff_of_le f hle h

/-- Scalar multiplication: ∫ g(x) * c = (∫ g) * c.
    Proved from Mathlib's `integral_mul_const`. -/
lemma hSpatialMul (g : X → ℝ) (c : ℝ) :
    spatialIntegral (fun x => g x * c) = spatialIntegral g * c := by
  simp [spatialIntegral, integral_mul_const]

/-- Zero gradient implies spatially constant (derived from hHarmonic_const + hDivLinear). -/
lemma hGradZeroConst (φ : X → ℝ) (hd : IsSpatiallySmooth 2 φ) (h : ∀ x, gradX φ x = 0) :
    ∀ x y, φ x = φ y := by
  apply hHarmonic_const _ hd
  intro x
  have h1 := hDivLinear (X := X) 0 (gradX φ) x
  have hg : (fun y : X => (0 : ℝ) • gradX φ y) = gradX φ := by
    ext y; simp [h y]
  rw [hg, zero_mul] at h1; exact h1

/-- Chain rule for log: gradX(log ∘ g) = (1/g) · gradX(g) when g > 0.
    Derived from hGradChainExp: gradX(exp(log g)) = g · gradX(log g) = gradX(g). -/
lemma hGradChainLog (g : X → ℝ) (hg_diff : IsSpatiallySmooth 1 g) (hg : ∀ x, 0 < g x) :
    ∀ x i, gradX (fun y => Real.log (g y)) x i = (1 / g x) * gradX g x i := by
  intro x i
  have key := hGradChainExp (fun y => Real.log (g y)) (hDiff_log 1 g hg_diff hg) x i
  have hexplog : (fun y => Real.exp (Real.log (g y))) = g := by
    ext y; exact Real.exp_log (hg y)
  rw [hexplog, Real.exp_log (hg x)] at key
  have hgx_ne : g x ≠ 0 := ne_of_gt (hg x)
  field_simp at key ⊢; linarith

/-- Integral of a single gradient component vanishes (from IBP with φ=1). -/
private lemma gradIntZero_component (g : X → ℝ) (hg : IsSpatiallySmooth 1 g) (i : Fin 3) :
    ∫ x, gradX g x i = 0 := by
  have h := hIBP_spatial (fun _ => 1) g i (hDiff_const 1 1) hg
  simp only [one_mul] at h
  have hc : ∀ x : X, gradX (fun _ : X => (1 : ℝ)) x = 0 :=
    hGradConst (fun _ : X => (1 : ℝ)) (fun _ _ => rfl)
  simp only [hc, Pi.zero_apply, mul_zero, integral_zero, neg_zero] at h
  linarith

/-- Gradient integral vanishes (Stokes for 0-forms: ∫_M dg = 0).
    Derived from hIBP_spatial + hGradConst + hGradIntegrable. -/
lemma hGradIntZero (g : X → ℝ) (hg : IsSpatiallySmooth 1 g) (u : Fin 3 → ℝ) :
    ∫ x, dotProduct u (gradX g x) = 0 := by
  simp only [dotProduct, Fin.sum_univ_three]
  have hint : ∀ i : Fin 3, MeasureTheory.Integrable (fun x : X => gradX g x i) :=
    hGradIntegrable g hg
  have h0 : ∫ x : X, u 0 * gradX g x 0 = 0 := by
    rw [integral_const_mul, gradIntZero_component g hg 0, mul_zero]
  have h1 : ∫ x : X, u 1 * gradX g x 1 = 0 := by
    rw [integral_const_mul, gradIntZero_component g hg 1, mul_zero]
  have h2 : ∫ x : X, u 2 * gradX g x 2 = 0 := by
    rw [integral_const_mul, gradIntZero_component g hg 2, mul_zero]
  have h01 := MeasureTheory.integral_add ((hint 0).const_mul (u 0)) ((hint 1).const_mul (u 1))
  have h012 : ∫ (a : X), u 0 * gradX g a 0 + u 1 * gradX g a 1 + u 2 * gradX g a 2 =
      (∫ (a : X), u 0 * gradX g a 0 + u 1 * gradX g a 1) + ∫ (a : X), u 2 * gradX g a 2 := by
    have := MeasureTheory.integral_add
      (((hint 0).const_mul (u 0)).add ((hint 1).const_mul (u 1))) ((hint 2).const_mul (u 2))
    simp only [Pi.add_apply] at this; exact this
  linarith

/-- Adding a constant doesn't change the gradient.
    Derived from hGradChainExp + hGradScalarMul via the exp trick:
    exp(f+c) = exp(c)*exp(f), so by the chain rule and scalar multiplication,
    exp(f(x)+c) * gradX(f+c)(x) = exp(c) * exp(f(x)) * gradX(f)(x).
    Cancelling exp(f(x)+c) > 0 gives gradX(f+c) = gradX(f). -/
lemma hGradAddConst (f : X → ℝ) (hf : IsSpatiallySmooth 1 f) (c : ℝ) :
    ∀ x, gradX (fun y => f y + c) x = gradX f x := by
  intro x; ext i
  have h1 := hGradChainExp (X := X) (fun y => f y + c)
    (hDiff_add 1 _ _ hf (hDiff_const 1 c)) x i
  have h2 := hGradChainExp (X := X) f hf x i
  -- exp(f+c) = exp(c) * exp(f)
  have hfun_eq : (fun y => Real.exp (f y + c)) = (fun y => Real.exp c * Real.exp (f y)) :=
    funext (fun y => by rw [Real.exp_add]; ring)
  rw [hfun_eq] at h1
  -- gradX(exp(c) * exp(f)) = exp(c) • gradX(exp(f)) by hGradScalarMul
  have h3 := congr_fun (hGradScalarMul (X := X) (Real.exp c) (fun y => Real.exp (f y)) x) i
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  rw [h3, h2] at h1
  -- h1: exp(c) * (exp(f x) * gradX f x i) = exp(f x + c) * gradX(f+c) x i
  rw [Real.exp_add] at h1
  -- h1: exp(c) * (exp(f x) * gradX f x i) = exp(f x) * exp(c) * gradX(f+c) x i
  have hne : Real.exp c * Real.exp (f x) ≠ 0 :=
    ne_of_gt (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  have h4 : Real.exp c * Real.exp (f x) * gradX f x i =
      Real.exp c * Real.exp (f x) * gradX (fun y => f y + c) x i := by linarith
  exact mul_left_cancel₀ hne h4.symm

/-- Second derivative test: Laplacian ≥ 0 at a minimum.
    Derived from hLaplacianMaxNonpos applied to -φ, using linearity of grad and div. -/
lemma hLaplacianMinNonneg (φ : X → ℝ) (hφ : IsSpatiallySmooth 2 φ) (x₀ : X)
    (hmin : ∀ x, φ x₀ ≤ φ x) : 0 ≤ divX (gradX φ) x₀ := by
  have hmax : ∀ x, (fun y => (-1) * φ y) x ≤ (fun y => (-1) * φ y) x₀ := by
    intro x
    simp
    linarith [hmin x]
  have h := hLaplacianMaxNonpos (fun y => (-1) * φ y) x₀ (hDiff_smul 2 (-1) φ hφ) hmax
  have h2 : divX (gradX (fun y => (-1) * φ y)) x₀ =
      (-1) * divX (gradX φ) x₀ := by
    have hg : gradX (fun y => (-1) * φ y) = fun x => (-1 : ℝ) • gradX φ x := by
      funext x; exact hGradScalarMul (-1) φ x
    change divX (gradX (fun y => (-1) * φ y)) x₀ = _
    conv_lhs => rw [hg]
    exact hDivLinear (-1) (gradX φ) x₀
  linarith

/-- Maxwellian regularity: if f(x,v) = exp(a(x) + b(x)·v + c(x)|v|²) with f > 0 and
    f(·,v) spatially differentiable for each v, then a, bⱼ, c are spatially differentiable.

    Proof: Evaluate log f at v = 0, eⱼ, 2e₀ to extract the coefficients as linear combinations
    of the spatially differentiable functions x ↦ log f(x, v). -/
lemma maxwellian_params_isSpatiallySmooth
    (f : X → (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hDiff_fv : ∀ v, IsSpatiallySmooth n (fun x => f x v))
    (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ)
    (hform : ∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) :
    IsSpatiallySmooth n a ∧
    (∀ j, IsSpatiallySmooth n (fun x => b x j)) ∧
    IsSpatiallySmooth n c := by
  -- log f(x, v) = a x + b x · v + c x * |v|² for all x, v
  have hDiff_lf : ∀ v, IsSpatiallySmooth n (fun x => Real.log (f x v)) := fun v =>
    hDiff_log n _ (hDiff_fv v) (fun x => hf_pos x v)
  have hlogform : ∀ x v, Real.log (f x v) = a x + dotProduct (b x) v + c x * normSq v := by
    intros x v; rw [hform x v, Real.log_exp]
  -- At v = 0: log f(x, 0) = a x
  have ha_val : ∀ x, a x = Real.log (f x 0) := by
    intro x
    have := hlogform x 0
    simp [normSq_zero, dotProduct] at this
    linarith
  -- At v = eⱼ: log f(x, eⱼ) = a x + b x j + c x
  have hform_single : ∀ x (j : Fin 3), Real.log (f x (Pi.single j 1)) = a x + b x j + c x := by
    intros x j; have h := hlogform x (Pi.single j 1)
    have h_dot : dotProduct (b x) (Pi.single j (1:ℝ)) = b x j := by
      simp [dotProduct, Pi.single_apply]
    have h_ns : normSq (Pi.single j (1:ℝ)) = 1 := by
      simp [normSq, dotProduct, Pi.single_apply]
    rw [h_dot, h_ns, mul_one] at h; linarith
  -- At v = 2e₀: log f(x, 2e₀) = a x + 2*(b x 0) + 4*(c x)
  have hform_2e₀ : ∀ x, Real.log (f x (2 • Pi.single 0 1)) = a x + 2 * b x 0 + 4 * c x := by
    intro x; have h := hlogform x (2 • Pi.single 0 (1:ℝ))
    have h_dot : dotProduct (b x) (2 • Pi.single 0 (1:ℝ)) = 2 * b x 0 := by
      simp [dotProduct, Pi.smul_apply, Pi.single_apply]
      ring
    have h_ns : normSq (2 • Pi.single 0 (1:ℝ)) = 4 := by
      simp [normSq, dotProduct, Pi.smul_apply, Pi.single_apply]
      ring
    rw [h_dot, h_ns] at h; linarith
  -- c formula: 2 * c x = log f(2e₀) - 2*log f(e₀) + log f(0)
  have hc_val : ∀ x, 2 * c x = Real.log (f x (2 • Pi.single 0 1)) -
      2 * Real.log (f x (Pi.single 0 1)) + Real.log (f x 0) := by
    intro x; linarith [hform_single x 0, hform_2e₀ x, ha_val x]
  -- bⱼ formula: b x j = log f(eⱼ) - log f(0) - c x
  have hbj_val : ∀ x (j : Fin 3), b x j = Real.log (f x (Pi.single j 1)) -
      Real.log (f x 0) - c x := by
    intros x j; linarith [hform_single x j, ha_val x]
  -- IsSpatiallySmooth ⊤ of c
  have hc_diff : IsSpatiallySmooth n c := by
    have hc_eq : c = fun x => (1/2 : ℝ) * (Real.log (f x (2 • Pi.single 0 1)) +
        (-2) * Real.log (f x (Pi.single 0 1)) + Real.log (f x 0)) := by
      funext x
      have := hc_val x
      field_simp
      linarith
    rw [hc_eq]
    exact hDiff_smul n _ _ (hDiff_add n _ _ (hDiff_add n _ _ (hDiff_lf _)
      (hDiff_smul n _ _ (hDiff_lf _))) (hDiff_lf _))
  refine ⟨?_, ?_, hc_diff⟩
  · -- IsSpatiallySmooth n a: a x = log f(x, 0)
    have : a = fun x => Real.log (f x 0) := funext (fun x => ha_val x)
    rw [this]; exact hDiff_lf 0
  · -- IsSpatiallySmooth ⊤ (b · j): b x j = log f(eⱼ) - log f(0) - c x
    intro j
    have hbj_eq : (fun x => b x j) = fun x =>
        Real.log (f x (Pi.single j 1)) + (-1) * Real.log (f x 0) + (-1) * c x := by
      funext x
      have := hbj_val x j
      linarith
    rw [hbj_eq]
    exact hDiff_add n _ _ (hDiff_add n _ _ (hDiff_lf _) (hDiff_smul n _ _ (hDiff_lf _)))
      (hDiff_smul n _ _ hc_diff)

end FlatTorus3

end VML
