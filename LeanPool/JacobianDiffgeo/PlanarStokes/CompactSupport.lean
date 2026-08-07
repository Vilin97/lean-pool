/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PlanarStokes.Compat

/-!
# Atom 1: compact-support planar Stokes for `dbar`

Unit: planar-stokes-atoms (`docs/design/planar-stokes.md` §6). Proves the honest 2-D Stokes
theorem this unit exists to supply: a compactly-supported `C¹` function's `dbar` integrates to zero
over the whole plane (`integral_wirtingerDbar_eq_zero`), by picking a rectangle strictly
containing the support and invoking `Complex.integral_boundary_rect_of_differentiableOn_real`
(mathlib's rectangle divergence theorem, specialized to `ℂ`) — the boundary terms vanish since `g`
is `≡ 0` there, leaving exactly the `wirtingerDbar`-area identity. The holomorphic-multiplier
corollary (`integral_wirtingerDbar_mul_eq_zero_of_differentiableOn`, Atom 1b) is the "no pole in
this chart" case residue-theorem needs for every PoU piece that misses every pole.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RS

variable {g f : ℂ → ℂ} {U : Set ℂ}

/-- **Atom 1** (compact-support planar Stokes for `dbar`): the `dbar` of a compactly-supported `C¹`
function integrates to zero over the whole plane. -/
theorem integral_wirtingerDbar_eq_zero (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U) :
    ∫ w : ℂ, wirtingerDbar g w = 0 := by
  -- Step 1: upgrade to global `ContDiff`.
  have hg' : ContDiff ℝ 1 g := ContDiffOn.contDiff_of_hasCompactSupport hU hg hcs hsub
  have hgdiff : Differentiable ℝ g := hg'.differentiable (by norm_num)
  have hfc : Continuous (fderiv ℝ g) := hg'.continuous_fderiv (by norm_num)
  -- Step 2: pick a rectangle strictly containing the support.
  obtain ⟨M0, hM0⟩ := hcs.isBounded.subset_closedBall (0 : ℂ)
  set M : ℝ := max M0 0 with hM_def
  have hMnn : (0 : ℝ) ≤ M := le_max_right _ _
  have hM : tsupport g ⊆ Metric.closedBall (0 : ℂ) M :=
    hM0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  set z : ℂ := (⟨-(M + 1), -(M + 1)⟩ : ℂ) with hz_def
  set w : ℂ := (⟨M + 1, M + 1⟩ : ℂ) with hw_def
  have hzre : z.re = -(M + 1) := rfl
  have hzim : z.im = -(M + 1) := rfl
  have hwre : w.re = M + 1 := rfl
  have hwim : w.im = M + 1 := rfl
  have hzw_re : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have hzw_im : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  have hsub2 : tsupport g ⊆ Complex.reProdIm (Set.Ioo z.re w.re) (Set.Ioo z.im w.im) := by
    intro ζ hζ
    have hball : ‖ζ‖ ≤ M := by
      have hζ' := hM hζ
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hζ'
    have hre : |ζ.re| ≤ M := (Complex.abs_re_le_norm ζ).trans hball
    have him : |ζ.im| ≤ M := (Complex.abs_im_le_norm ζ).trans hball
    rw [abs_le] at hre him
    rw [Complex.mem_reProdIm, hzre, hwre, hzim, hwim, Set.mem_Ioo, Set.mem_Ioo]
    exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, ⟨by linarith [him.1], by linarith [him.2]⟩⟩
  -- Step 3: apply the rectangle lemma.
  have hDon : DifferentiableOn ℝ g (Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)) :=
    hgdiff.differentiableOn
  have hIntegrand_cont : Continuous (fun ζ : ℂ => I • fderiv ℝ g ζ 1 - fderiv ℝ g ζ I) := by
    have h1 : Continuous (fun ζ : ℂ => fderiv ℝ g ζ 1) := hfc.clm_apply continuous_const
    have hI : Continuous (fun ζ : ℂ => fderiv ℝ g ζ I) := hfc.clm_apply continuous_const
    have hsmul : Continuous (fun ζ : ℂ => I • fderiv ℝ g ζ 1) := h1.const_smul I
    exact hsmul.sub hI
  have hcompactRect : IsCompact
      (Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)) :=
    IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
  have hInt : IntegrableOn (fun ζ : ℂ => I • fderiv ℝ g ζ 1 - fderiv ℝ g ζ I)
      (Complex.reProdIm (Set.uIcc z.re w.re) (Set.uIcc z.im w.im)) :=
    hIntegrand_cont.continuousOn.integrableOn_compact hcompactRect
  have hrect := Complex.integral_boundary_rect_of_differentiableOn_real g z w hDon hInt
  -- The four boundary integrals vanish: each segment lies entirely outside the open rectangle.
  have hvanish : ∀ ζ : ℂ, ζ.re ∉ Set.Ioo z.re w.re ∨ ζ.im ∉ Set.Ioo z.im w.im → g ζ = 0 := by
    intro ζ hζ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hsub2 hmem
    rw [Complex.mem_reProdIm] at this
    rcases hζ with h | h
    · exact h this.1
    · exact h this.2
  have hbottom : (fun x : ℝ => g (x + z.im * I)) = fun _ => (0 : ℂ) := by
    funext x
    apply hvanish
    right
    rw [show ((x : ℂ) + z.im * I).im = z.im by simp]
    exact fun h => (lt_irrefl _ h.1)
  have htop : (fun x : ℝ => g (x + w.im * I)) = fun _ => (0 : ℂ) := by
    funext x
    apply hvanish
    right
    rw [show ((x : ℂ) + w.im * I).im = w.im by simp]
    exact fun h => (lt_irrefl _ h.2)
  have hleft : (fun y : ℝ => g (z.re + y * I)) = fun _ => (0 : ℂ) := by
    funext y
    apply hvanish
    left
    rw [show ((z.re : ℂ) + y * I).re = z.re by simp]
    exact fun h => (lt_irrefl _ h.1)
  have hright : (fun y : ℝ => g (w.re + y * I)) = fun _ => (0 : ℂ) := by
    funext y
    apply hvanish
    left
    rw [show ((w.re : ℂ) + y * I).re = w.re by simp]
    exact fun h => (lt_irrefl _ h.2)
  rw [hbottom, htop, hleft, hright] at hrect
  simp only [intervalIntegral.integral_zero, sub_zero, smul_zero, add_zero] at hrect
  -- Rewrite the RHS integrand via the `2i·wirtingerDbar` identity.
  have hpt : ∀ x y : ℝ, I • fderiv ℝ g (x + y * I) 1 - fderiv ℝ g (x + y * I) I
      = 2 * I * wirtingerDbar g (x + y * I) := by
    intro x y
    simp only [wirtingerDbar, smul_eq_mul]
    have hI2 : I * I = -1 := Complex.I_mul_I
    linear_combination (-(fderiv ℝ g (x + y * I) I)) * hI2
  simp_rw [hpt] at hrect
  have hpull : ∀ x : ℝ, ∫ y : ℝ in z.im..w.im, 2 * I * wirtingerDbar g (x + y * I)
      = 2 * I * ∫ y : ℝ in z.im..w.im, wirtingerDbar g (x + y * I) := fun x =>
    intervalIntegral.integral_const_mul _ _
  simp_rw [hpull] at hrect
  rw [intervalIntegral.integral_const_mul] at hrect
  have hIne : (2 : ℂ) * I ≠ 0 := by simp [Complex.I_ne_zero]
  have hiter0 : ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, wirtingerDbar g (x + y * I) = 0 := by
    rcases mul_eq_zero.mp hrect.symm with h | h
    · exact absurd h hIne
    · exact h
  -- Step 4/5: bridge back to the global integral via `Compat`.
  have hFc : Continuous (wirtingerDbar g) := continuous_wirtingerDbar_of_contDiff_one hg'
  have hFsub : tsupport (wirtingerDbar g) ⊆ Complex.reProdIm (Set.Ioo z.re w.re)
      (Set.Ioo z.im w.im) :=
    (tsupport_wirtingerDbar_subset).trans hsub2
  rw [integral_eq_intervalIntegral_of_tsupport_subset_reProdIm hFc hFsub]
  exact hiter0

/-- **Atom 1b** (immediate corollary, the "no pole in this chart" case residue-theorem needs for
every PoU piece that does not touch a pole): if `f` is holomorphic throughout `U`, the
`dbar`-weighted integral against `f` also vanishes. -/
theorem integral_wirtingerDbar_mul_eq_zero_of_differentiableOn (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    ∫ w : ℂ, wirtingerDbar g w * f w = 0 := by
  -- `fun w => g w * f w` is `ContDiffOn ℝ 1` on `U` (product of `ContDiffOn` and a differentiable
  -- — hence `ContDiffOn ℝ 1` — holomorphic factor), has compact support `⊆ tsupport g ⊆ U`, and
  -- its `wirtingerDbar` agrees pointwise with `wirtingerDbar g * f`. Apply Atom 1 to it.
  have hfAn : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hfCD : ContDiffOn ℂ 1 f U := hfAn.contDiffOn hU.uniqueDiffOn
  have hfC1 : ContDiffOn ℝ 1 f U := hfCD.restrict_scalars ℝ
  have hprodC1 : ContDiffOn ℝ 1 (fun w => g w * f w) U := hg.mul hfC1
  have hprodcs : HasCompactSupport (fun w => g w * f w) := by
    apply hcs.mono'
    intro x hx
    simp only [Function.mem_support] at hx
    exact subset_tsupport g (by simpa [Function.mem_support] using left_ne_zero_of_mul hx)
  have hprodsub : tsupport (fun w => g w * f w) ⊆ U := by
    have hsupp : Function.support (fun w => g w * f w) ⊆ tsupport g := by
      intro x hx
      simp only [Function.mem_support] at hx
      exact subset_tsupport g (by simpa [Function.mem_support] using left_ne_zero_of_mul hx)
    calc tsupport (fun w => g w * f w) = closure (Function.support (fun w => g w * f w)) := rfl
      _ ⊆ closure (tsupport g) := closure_mono hsupp
      _ = tsupport g := (isClosed_tsupport g).closure_eq
      _ ⊆ U := hsub
  have hkey : ∫ w : ℂ, wirtingerDbar (fun w => g w * f w) w = 0 :=
    integral_wirtingerDbar_eq_zero hU hprodC1 hprodcs hprodsub
  have hpt : ∀ w : ℂ, wirtingerDbar (fun w => g w * f w) w = wirtingerDbar g w * f w := by
    intro w
    by_cases hw : w ∈ U
    · have hgd : DifferentiableAt ℝ g w :=
        (hg.contDiffAt (hU.mem_nhds hw)).differentiableAt (by norm_num)
      have hfd : DifferentiableAt ℂ f w := (hf w hw).differentiableAt (hU.mem_nhds hw)
      exact wirtingerDbar_mul_of_differentiableAt hgd hfd
    · have hwt : w ∉ tsupport g := fun h => hw (hsub h)
      rw [wirtingerDbar_mul_eq_zero_of_notMem_tsupport hwt]
      have hgw0 : wirtingerDbar g w = 0 := by
        have hg0 : g =ᶠ[nhds w] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hwt
        rw [wirtingerDbar_congr_nhds _ _ w hg0]
        simp [wirtingerDbar]
      rw [hgw0, zero_mul]
  simp_rw [hpt] at hkey
  exact hkey

end RS
