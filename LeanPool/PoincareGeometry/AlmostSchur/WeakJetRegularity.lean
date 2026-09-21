/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.PostH2Bootstrap
public import LeanPool.PoincareGeometry.AlmostSchur.WeakDerivativeMollification
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! # Interior mollification of compatible weak L² jets

Pinned Mathlib db584cd6d46c92f209a44c0f1c829460d327499d:
* Distribution/Sobolev: `MemSobolev.fourier_memL1` proves Fourier L¹
  representability above half the dimension, but uses Bessel-potential Sobolev
  membership of a tempered distribution, not the local weak jets here.
* FunctionalSpaces/SobolevInequality: Gagliardo-Nirenberg-Sobolev estimates
  require classical C¹ compactly supported inputs.
* Calculus/ContDiff/Convolution supplies classical derivatives of mollifications.

This module proves the analytic transfer from weak jet derivatives to classical
derivatives of their interior mollifications. It does not claim that a limit
has a continuous or smooth representative. That requires a local embedding/
uniform convergence argument (or a jet-to-Bessel-potential Fourier bridge).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Convolution
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An interior convolution differentiates to the convolution of the genuine
weak derivative. The support condition prevents any boundary contribution. -/
theorem fderiv_convolution_eq_weakDerivative_convolution
    {K : Set E} (u du : Lp ℝ 2 (volume : Measure E)) (v : E)
    (hw : HasWeakDirectionalDerivativeOn K v u du)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (x : E) (hs : tsupport (fun y => ρ (x - y)) ⊆ K) :
    fderiv ℝ ((u : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) x v =
      ((du : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) x := by
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
  let φ : E → ℝ := fun y => ρ (x - y)
  have hφ : ContDiff ℝ ∞ φ :=
    hρ.comp (contDiff_const.sub contDiff_id : ContDiff ℝ ∞ (fun y : E => x - y))
  have hcφ : HasCompactSupport φ := hcρ.comp_homeomorph (Homeomorph.subLeft x)
  have hsφ : tsupport φ ⊆ K := hs
  have hdφ (y : E) : fderiv ℝ φ y v = -(fderiv ℝ ρ (x - y) v) := by
    have hd := (hρ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    simpa [φ, Function.comp_def, Pi.sub_def] using
      congrArg (fun T : E →L[ℝ] ℝ => T v) hd.fderiv
  have hl : ∀ y ∉ K, u y * fderiv ℝ φ y v = 0 := by
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hy (hsφ hh))]
    simp
  have hr : ∀ y ∉ K, du y * φ y = 0 := by
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hy (hsφ hh))]
    simp
  have he := hw φ hφ hcφ hs
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hl,
    setIntegral_eq_integral_of_forall_compl_eq_zero hr] at he
  simp_rw [hdφ, mul_neg] at he
  rw [integral_neg] at he
  have he' : (∫ y, u y * fderiv ℝ ρ (x - y) v) = ∫ y, du y * φ y := by
    linarith
  rw [(hcρ.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hu (hρ.of_le (by simp)) x).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hu (hcρ.fderiv ℝ)
    ((hρ.of_le (by simp) : ContDiff ℝ 1 ρ).continuous_fderiv (by simp))]
  exact he'

/-- Every L² lift has a smooth convolution with a smooth compact kernel. -/
theorem contDiff_L2_convolution (u : Lp ℝ 2 (volume : Measure E))
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) :
    ContDiff ℝ ∞ ((u : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) :=
  hcρ.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    ((Lp.memLp u).locallyIntegrable (by norm_num)) hρ

/-- Every valid word in a finite weak jet becomes the corresponding classical
iterated directional derivative of the mollified zeroth field, on any open
region where the translated kernels remain inside the weak-identity domain. -/
theorem LocalL2DerivativeJet.localDirectionalIterate_convolution
    {ι : Type*} {b : ι → E} {K O : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) (hO : IsOpen O)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hs : ∀ x ∈ O, tsupport (fun y => ρ (x - y)) ⊆ K)
    (w : List ι) (hw : w.length ≤ n) (x : E) (hx : x ∈ O) :
    localDirectionalIterate b
      ((J.value [] : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) w x =
      ((J.value w : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    have hwl : w.length < n := by simp only [List.length_cons] at hw; omega
    have he : localDirectionalIterate b
        ((J.value [] : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) w =ᶠ[𝓝 x]
        ((J.value w : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact ih hwl.le y hy
    change fderiv ℝ _ x (b i) = _
    rw [he.fderiv_eq]
    exact fderiv_convolution_eq_weakDerivative_convolution _ _ (b i)
      (J.weak w hwl i) hρ hcρ x (hs x hx)

/-- Concrete nested-ball version: each derivative of the mollified solution
equals the mollification of the matching weak jet field, strictly inside the
larger ball. Kernel normalization is unnecessary for this identity. -/
theorem LocalL2DerivativeJet.localDirectionalIterate_convolution_on_ball
    {ι : Type*} {b : ι → E} {K : Set E} {n : ℕ}
    (J : LocalL2DerivativeJet b K n) {a : E} {R r ε : ℝ}
    (hK : closedBall a R ⊆ K) {ρ : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hsρ : tsupport ρ ⊆ closedBall 0 ε) (hε : ε < R - r)
    (w : List ι) (hw : w.length ≤ n) (x : E) (hx : x ∈ ball a r) :
    localDirectionalIterate b
      ((J.value [] : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) w x =
      ((J.value w : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ) x :=
  J.localDirectionalIterate_convolution isOpen_ball hρ hcρ
    (fun _ hy => (translated_kernel_tsupport_subset hsρ hy hε).trans hK) w hw x hx

/-- Normalized shrinking bump convolutions recover an L² field almost
everywhere. This is Lebesgue differentiation, not uniform convergence. -/
theorem ae_tendsto_L2_bump_convolution
    {α : Type*} {l : Filter α} (u : Lp ℝ 2 (volume : Measure E))
    (ρ : α → ContDiffBump (0 : E)) {C : ℝ}
    (hρ : Tendsto (fun j => (ρ j).rOut) l (𝓝 0))
    (hratio : ∀ᶠ j in l, (ρ j).rOut ≤ C * (ρ j).rIn) :
    ∀ᵐ x ∂(volume : Measure E), Tendsto (fun j =>
      ((u : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (ρ j).normed volume) x)
      l (𝓝 (u x)) := by
  have ht := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    hρ hratio ((Lp.memLp u).locallyIntegrable (by norm_num))
  filter_upwards [ht] with x hx
  apply hx.congr
  intro j
  rw [convolution_eq_swap]
  change (∫ t, (ρ j).normed volume (x - t) * u t) =
    ∫ t, u t * (ρ j).normed volume (x - t)
  congr 1
  funext t
  exact mul_comm _ _

/-- On strictly nested balls, the classical derivatives of smooth normalized
mollifications recover every valid weak jet field almost everywhere.
No smoothness of the recovered field, nor uniform convergence, is asserted. -/
theorem LocalL2DerivativeJet.ae_tendsto_localDirectionalIterate_bump_convolution
    {ι α : Type*} {b : ι → E} {K : Set E} {n : ℕ} {l : Filter α}
    (J : LocalL2DerivativeJet b K n) {a : E} {R r : ℝ}
    (hK : closedBall a R ⊆ K) (hrR : r < R)
    (ρ : α → ContDiffBump (0 : E)) {C : ℝ}
    (hρ : Tendsto (fun j => (ρ j).rOut) l (𝓝 0))
    (hratio : ∀ᶠ j in l, (ρ j).rOut ≤ C * (ρ j).rIn)
    (w : List ι) (hw : w.length ≤ n) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ ball a r → Tendsto (fun j =>
      localDirectionalIterate b
        ((J.value [] : E → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
          (ρ j).normed volume) w x) l (𝓝 (J.value w x)) := by
  have ht := ae_tendsto_L2_bump_convolution (J.value w) ρ hρ hratio
  have hsmall : ∀ᶠ j in l, (ρ j).rOut < R - r :=
    hρ.eventually (gt_mem_nhds (sub_pos.mpr hrR))
  filter_upwards [ht] with x hx
  intro hxb
  apply hx.congr'
  filter_upwards [hsmall] with j hj
  symm
  exact J.localDirectionalIterate_convolution_on_ball hK (ρ j).contDiff_normed
    (ρ j).hasCompactSupport_normed (by rw [(ρ j).tsupport_normed_eq]) hj w hw x hxb

end AlmostSchur
