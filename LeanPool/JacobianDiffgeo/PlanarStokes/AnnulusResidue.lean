/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.PlanarStokes.CompactSupport
import LeanPool.JacobianDiffgeo.ResidueCalculus.IntegralBridge
import LeanPool.JacobianDiffgeo.ResidueCalculus.Residue
import LeanPool.JacobianDiffgeo.ResidueCalculus.PrincipalPart
import LeanPool.JacobianDiffgeo.Dbar.CauchyKernel
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# The annulus Stokes identity and the smeared residue theorem

Unit: planar-stokes-atoms (`docs/design/planar-stokes.md` §7–§8). Two theorems:

* `circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` (Atom 1′): the
  area-to-boundary identity for the `dbar` of an arbitrary `C¹` function on a closed annulus, proved
  by the exponential substitution `w = c + exp ζ` mapping a rectangle onto the annulus. No
  meromorphy, no residues.
* `integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt` (Atom 2, the smeared residue theorem) and its
  model-case regression check `integral_wirtingerDbar_mul_inv_sub_eq` (`f = 1/(z-p)`, proved a
  second, independent way via `RS.cauchyPompeiu`).

Deviation from the design's §7 proof sketch: instead of routing the area term through
`Complex.polarCoord` (whose target `Ioi 0 ×ˢ Ioo(-π,π)` forces a periodicity-shift reconciliation
against the `[0,2π]` circle parametrization), we apply
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` directly to the substitution
`τ ζ = c + exp ζ` on the half-open-in-angle rectangle `Icc a b ×ℂ Ico 0 (2π)` (`a = log r`,
`b = log R`), which `τ` maps *bijectively* onto the annulus (no missing ray, unlike the open
rectangle) — a shorter route to the same identity, using the same mathlib machinery flagged as
the design's own R2 fallback.
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real

noncomputable section

namespace RS

/-! ## Helper facts -/

section Helpers

variable {u : ℂ → ℂ}

/-- The determinant (as a real-linear self-map of `ℂ`) of the real differential of a
holomorphic map, in closed form: `|det| = normSq (deriv)`. -/
private theorem det_fderiv_of_differentiableAt {τ : ℂ → ℂ} {ζ : ℂ}
    (hτ : DifferentiableAt ℂ τ ζ) :
    (fderiv ℝ τ ζ).det = Complex.normSq (deriv τ ζ) := by
  have hr : fderiv ℝ τ ζ = (fderiv ℂ τ ζ).restrictScalars ℝ := hτ.fderiv_restrictScalars ℝ
  have hspan : fderiv ℂ τ ζ = ContinuousLinearMap.toSpanSingleton ℂ (deriv τ ζ) := by
    ext
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, fderiv_eq_deriv_mul]
    ring
  rw [hr, hspan]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

/-- A horizontal segment (fixed imaginary part, real part ranging over any set) is Lebesgue-null
in `ℂ`. -/
private theorem measure_reProdIm_im_singleton (y0 : ℝ) (s : Set ℝ) :
    volume (Complex.reProdIm s {y0}) = 0 := by
  have heq : (Complex.reProdIm s {y0} : Set ℂ)
      = Complex.measurableEquivRealProd ⁻¹' (s ×ˢ ({y0} : Set ℝ)) := by
    ext w; simp [Complex.reProdIm, Complex.measurableEquivRealProd_apply]
  rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    MeasureTheory.Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- A vertical segment (fixed real part, imaginary part ranging over any set) is Lebesgue-null
in `ℂ`. -/
private theorem measure_reProdIm_re_singleton (x0 : ℝ) (t : Set ℝ) :
    volume (Complex.reProdIm ({x0} : Set ℝ) t) = 0 := by
  have heq : (Complex.reProdIm ({x0} : Set ℝ) t : Set ℂ)
      = Complex.measurableEquivRealProd ⁻¹' (({x0} : Set ℝ) ×ˢ t) := by
    ext w; simp [Complex.reProdIm, Complex.measurableEquivRealProd_apply]
  rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    MeasureTheory.Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem measure_reProdIm_pair_re (x0 x1 : ℝ) (t : Set ℝ) :
    volume (Complex.reProdIm ({x0, x1} : Set ℝ) t) = 0 := by
  have hset : (Complex.reProdIm ({x0, x1} : Set ℝ) t : Set ℂ)
      = Complex.reProdIm {x0} t ∪ Complex.reProdIm {x1} t := by
    ext w; simp [Complex.reProdIm, or_and_right]
  rw [hset]
  exact measure_union_null (measure_reProdIm_re_singleton x0 t) (measure_reProdIm_re_singleton x1 t)

private theorem measure_reProdIm_pair_im (s : Set ℝ) (y0 y1 : ℝ) :
    volume (Complex.reProdIm s ({y0, y1} : Set ℝ)) = 0 := by
  have hset : (Complex.reProdIm s ({y0, y1} : Set ℝ) : Set ℂ)
      = Complex.reProdIm s {y0} ∪ Complex.reProdIm s {y1} := by
    ext w; simp [Complex.reProdIm, and_or_left]
  rw [hset]
  exact measure_union_null (measure_reProdIm_im_singleton y0 s) (measure_reProdIm_im_singleton y1 s)

/-- The frame (closed rectangle minus open rectangle) is Lebesgue-null. -/
private theorem measure_frame_null (a b lo hi : ℝ) (hab : a ≤ b) (hlohi : lo ≤ hi) :
    volume (Complex.reProdIm (Set.Icc a b) (Set.Icc lo hi)
      \ Complex.reProdIm (Set.Ioo a b) (Set.Ioo lo hi)) = 0 := by
  have hsub : Complex.reProdIm (Set.Icc a b) (Set.Icc lo hi)
      \ Complex.reProdIm (Set.Ioo a b) (Set.Ioo lo hi)
      ⊆ Complex.reProdIm ({a, b} : Set ℝ) (Set.Icc lo hi)
        ∪ Complex.reProdIm (Set.Icc a b) ({lo, hi} : Set ℝ) := by
    rintro w ⟨hw, hw'⟩
    rw [Complex.mem_reProdIm] at hw
    by_cases hre : w.re ∈ Set.Ioo a b
    · right
      rw [Complex.mem_reProdIm]
      refine ⟨hw.1, ?_⟩
      have hnotim : w.im ∉ Set.Ioo lo hi := fun h => hw' (Complex.mem_reProdIm.mpr ⟨hre, h⟩)
      have hmem : w.im ∈ Set.Icc lo hi \ Set.Ioo lo hi := ⟨hw.2, hnotim⟩
      rwa [Icc_sdiff_Ioo_same hlohi] at hmem
    · left
      rw [Complex.mem_reProdIm]
      refine ⟨?_, hw.2⟩
      have hmem : w.re ∈ Set.Icc a b \ Set.Ioo a b := ⟨hw.1, hre⟩
      rwa [Icc_sdiff_Ioo_same hab] at hmem
  have hbound : volume (Complex.reProdIm ({a, b} : Set ℝ) (Set.Icc lo hi)
      ∪ Complex.reProdIm (Set.Icc a b) ({lo, hi} : Set ℝ)) = 0 :=
    measure_union_null (measure_reProdIm_pair_re a b (Set.Icc lo hi))
      (measure_reProdIm_pair_im (Set.Icc a b) lo hi)
  exact measure_mono_null hsub hbound

/-- The exp-substitution algebraic core (de-risked in the design's spike, §9): the `dbar` of the
transported function `u(c + exp ·) * exp` sees `u`'s `dbar` scaled by `‖exp ζ‖²`. -/
private theorem wirtingerDbar_expSubst_eq {c ζ : ℂ}
    (hu : DifferentiableAt ℝ u (c + Complex.exp ζ)) :
    wirtingerDbar (fun w => u (c + Complex.exp w) * Complex.exp w) ζ =
      Complex.exp ζ * (starRingEnd ℂ) (Complex.exp ζ) * wirtingerDbar u (c + Complex.exp ζ) := by
  have hexp : DifferentiableAt ℂ Complex.exp ζ := Complex.differentiableAt_exp
  have hexpR : DifferentiableAt ℝ Complex.exp ζ := hexp.restrictScalars ℝ
  have hcexp : DifferentiableAt ℝ (fun w => c + Complex.exp w) ζ :=
    (differentiableAt_const c).add hexpR
  have hcomp : DifferentiableAt ℝ (fun w => u (c + Complex.exp w)) ζ := hu.comp ζ hcexp
  rw [wirtingerDbar_mul hcomp hexpR]
  have hchain : wirtingerDbar (fun w => u (c + Complex.exp w)) ζ =
      (starRingEnd ℂ) (deriv (fun w => c + Complex.exp w) ζ)
        * wirtingerDbar u (c + Complex.exp ζ) :=
    wirtingerDbar_comp_differentiableAt (τ := fun w => c + Complex.exp w) u ζ hu
      (hexp.const_add c)
  have hderivexp : deriv (fun w => c + Complex.exp w) ζ = Complex.exp ζ := by
    rw [deriv_const_add, congrFun Complex.deriv_exp ζ]
  have hbar0 : wirtingerDbar Complex.exp ζ = 0 :=
    wirtingerDbar_eq_zero_of_differentiableAt Complex.exp ζ hexp
  rw [hchain, hderivexp, hbar0]
  ring

end Helpers

/-! ## The annulus identity (Atom 1′) -/

/-- The polar-log change of variables `τ ζ = c + exp ζ` carries the rectangle onto the annulus:
it maps `Rec` into `A`, is injective on the half-open `s`, and has image exactly `A`. Split out of
`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` for the 200-line proof
size we hold ourselves to; the abbreviations are rebuilt here so the arguments read as inline. -/
private theorem polarLog_mapsTo_injOn_image {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hRpos : 0 < R)
    (hRr : r < R) :
    Set.MapsTo (fun ζ : ℂ => c + Complex.exp ζ)
        (Complex.reProdIm (Set.Icc (Real.log r) (Real.log R)) (Set.Icc (0 : ℝ) (2 * π)))
        (Metric.closedBall c R \ Metric.ball c r) ∧
      Set.InjOn (fun ζ : ℂ => c + Complex.exp ζ)
        (Complex.reProdIm (Set.Icc (Real.log r) (Real.log R)) (Set.Ico (0 : ℝ) (2 * π))) ∧
      (fun ζ : ℂ => c + Complex.exp ζ) ''
          (Complex.reProdIm (Set.Icc (Real.log r) (Real.log R)) (Set.Ico (0 : ℝ) (2 * π))) =
        Metric.closedBall c R \ Metric.ball c r := by
  set a : ℝ := Real.log r with ha_def
  set b : ℝ := Real.log R with hb_def
  have hea : Real.exp a = r := Real.exp_log h0
  have heb : Real.exp b = R := Real.exp_log hRpos
  have hab : a < b := (Real.log_lt_log_iff h0 hRpos).mpr hRr
  set τ : ℂ → ℂ := fun ζ => c + Complex.exp ζ with hτ_def
  set A : Set ℂ := Metric.closedBall c R \ Metric.ball c r with hA_def
  set Rec : Set ℂ := Complex.reProdIm (Set.Icc a b) (Set.Icc (0 : ℝ) (2 * π)) with hRec_def
  set s : Set ℂ := Complex.reProdIm (Set.Icc a b) (Set.Ico (0 : ℝ) (2 * π)) with hs_def
  have hs_sub_Rec : s ⊆ Rec := by
    intro ζ hζ
    rw [hs_def, Complex.mem_reProdIm] at hζ
    rw [hRec_def, Complex.mem_reProdIm]
    exact ⟨hζ.1, ⟨hζ.2.1, hζ.2.2.le⟩⟩
  have hτ_maps : Set.MapsTo τ Rec A := by
    intro ζ hζ
    rw [hRec_def, Complex.mem_reProdIm] at hζ
    have hdist : dist (τ ζ) c = Real.exp ζ.re := by
      rw [hτ_def, dist_eq_norm, show c + Complex.exp ζ - c = Complex.exp ζ from by ring,
        Complex.norm_exp]
    have hlow : r ≤ Real.exp ζ.re := by
      rw [← hea]; exact Real.exp_le_exp.mpr hζ.1.1
    have hhigh : Real.exp ζ.re ≤ R := by
      rw [← heb]; exact Real.exp_le_exp.mpr hζ.1.2
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, hdist]; exact hhigh
    · rw [Metric.mem_ball, not_lt, hdist] at *; exact hlow
  have hs_maps : Set.MapsTo τ s A := hτ_maps.mono_left hs_sub_Rec
  refine ⟨hτ_maps, ?_, ?_⟩
  · show Set.InjOn τ s
    intro ζ1 hζ1 ζ2 hζ2 heq
    rw [hs_def, Complex.mem_reProdIm] at hζ1 hζ2
    have heq' : Complex.exp ζ1 = Complex.exp ζ2 := by
      have hh : c + Complex.exp ζ1 = c + Complex.exp ζ2 := by simpa [hτ_def] using heq
      exact add_left_cancel hh
    rw [Complex.exp_eq_exp_iff_exists_int] at heq'
    obtain ⟨n, hn⟩ := heq'
    have hre : ζ1.re = ζ2.re := by
      have := congrArg Complex.re hn; simpa using this
    have him : ζ1.im = ζ2.im + n * (2 * π) := by
      have := congrArg Complex.im hn; simpa using this
    have hn0 : n = 0 := by
      have hb1 := hζ1.2.1; have hb2 := hζ1.2.2
      have hc1 := hζ2.2.1; have hc2 := hζ2.2.2
      have hbound1 : -(2 * π) < (n : ℝ) * (2 * π) := by nlinarith
      have hbound2 : (n : ℝ) * (2 * π) < 2 * π := by nlinarith
      have hpi : (0 : ℝ) < 2 * π := Real.two_pi_pos
      have hn1 : (-1 : ℝ) < (n : ℝ) := by nlinarith
      have hn2 : (n : ℝ) < 1 := by nlinarith
      have h1' : (-1 : ℤ) < n := by exact_mod_cast hn1
      have h2' : n < (1 : ℤ) := by exact_mod_cast hn2
      omega
    rw [hn0] at him
    simp only [Int.cast_zero, zero_mul, add_zero] at him
    exact Complex.ext hre him
  · show τ '' s = A
    apply Set.Subset.antisymm (Set.image_subset_iff.mpr hs_maps)
    intro w hw
    set ρ : ℝ := ‖w - c‖ with hρ_def
    have hρpos : 0 < ρ := by
      rw [hρ_def, norm_pos_iff, sub_ne_zero]
      rintro rfl
      exact hw.2 (Metric.mem_ball_self h0)
    have hρr : r ≤ ρ := by
      have hh := hw.2
      rw [Metric.mem_ball, not_lt] at hh
      rwa [hρ_def, ← dist_eq_norm]
    have hρR : ρ ≤ R := by
      have hh := hw.1
      rw [Metric.mem_closedBall] at hh
      rwa [hρ_def, ← dist_eq_norm]
    set θ₀ : ℝ := Complex.arg (w - c) with hθ₀_def
    have hθ₀range := Complex.arg_mem_Ioc (w - c)
    set y : ℝ := if θ₀ < 0 then θ₀ + 2 * π else θ₀ with hy_def
    have hyrange : y ∈ Set.Ico (0 : ℝ) (2 * π) := by
      rw [hy_def]
      split_ifs with hneg
      · exact ⟨by linarith [hθ₀range.1], by linarith [hθ₀range.2]⟩
      · push Not at hneg
        exact ⟨hneg, by linarith [hθ₀range.2, Real.pi_pos]⟩
    have hexpy : Complex.exp (y * I) = Complex.exp (θ₀ * I) := by
      rw [hy_def]
      split_ifs with hneg
      · rw [show ((θ₀ + 2 * π : ℝ) : ℂ) * I = θ₀ * I + 2 * π * I by push_cast; ring,
          Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      · rfl
    set x : ℝ := Real.log ρ with hx_def
    have hxrange : x ∈ Set.Icc a b := by
      rw [hx_def, ha_def, hb_def]
      exact ⟨(Real.log_le_log_iff h0 hρpos).mpr hρr, (Real.log_le_log_iff hρpos hRpos).mpr hρR⟩
    refine ⟨x + y * I, ?_, ?_⟩
    · rw [hs_def, Complex.mem_reProdIm]
      simpa using ⟨hxrange, hyrange⟩
    · rw [hτ_def]
      simp only
      rw [Complex.exp_add, ← Complex.ofReal_exp, hx_def, Real.exp_log hρpos, hexpy,
        Complex.norm_mul_exp_arg_mul_I]
      ring

/-- On the open rectangle the pulled-back function is real-differentiable: its image sits in the
interior of the annulus. Split out of
`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` for the 200-line proof
size we hold ourselves to. -/
private theorem differentiableAt_comp_polarLog {u : ℂ → ℂ} {c : ℂ} {r R : ℝ} (h0 : 0 < r)
    (hRpos : 0 < R)
    (hu : ContDiffOn ℝ 1 u (Metric.closedBall c R \ Metric.ball c r)) :
    ∀ ζ ∈ Complex.reProdIm (Set.Ioo (Real.log r) (Real.log R)) (Set.Ioo (0 : ℝ) (2 * π)),
      DifferentiableAt ℝ u (c + Complex.exp ζ) := by
  set a : ℝ := Real.log r with ha_def
  set b : ℝ := Real.log R with hb_def
  have hea : Real.exp a = r := Real.exp_log h0
  have heb : Real.exp b = R := Real.exp_log hRpos
  set τ : ℂ → ℂ := fun ζ => c + Complex.exp ζ with hτ_def
  set A : Set ℂ := Metric.closedBall c R \ Metric.ball c r with hA_def
  set RecOpen : Set ℂ := Complex.reProdIm (Set.Ioo a b) (Set.Ioo (0 : ℝ) (2 * π)) with
    hRecOpen_def
  change ∀ ζ ∈ RecOpen, DifferentiableAt ℝ u (τ ζ)
  intro ζ hζ
  rw [hRecOpen_def, Complex.mem_reProdIm] at hζ
  have hτζ_int : τ ζ ∈ Metric.ball c R \ Metric.closedBall c r := by
    have hdist : dist (τ ζ) c = Real.exp ζ.re := by
      rw [hτ_def, dist_eq_norm, show c + Complex.exp ζ - c = Complex.exp ζ from by ring,
        Complex.norm_exp]
    have hlt1 : Real.exp ζ.re < R := by rw [← heb]; exact Real.exp_lt_exp.mpr hζ.1.2
    have hlt2 : r < Real.exp ζ.re := by rw [← hea]; exact Real.exp_lt_exp.mpr hζ.1.1
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, hdist]; exact hlt1
    · rw [Metric.mem_closedBall, not_le, hdist]; exact hlt2
  have hAmem : A ∈ nhds (τ ζ) := by
    have hopenset : IsOpen (Metric.ball c R \ Metric.closedBall c r) :=
      Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
    have hsub2 : Metric.ball c R \ Metric.closedBall c r ⊆ A := by
      rw [hA_def]
      rintro x ⟨hx1, hx2⟩
      rw [Metric.mem_ball] at hx1
      rw [Metric.mem_closedBall, not_le] at hx2
      exact ⟨by rw [Metric.mem_closedBall]; linarith, by rw [Metric.mem_ball, not_lt]; linarith⟩
    exact Filter.mem_of_superset (hopenset.mem_nhds hτζ_int) hsub2
  exact (hu.contDiffAt hAmem).differentiableAt (by norm_num)

/-- The integrand is `2π`-periodic in the imaginary direction. Split out of
`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` for the 200-line proof
size we hold ourselves to. -/
private theorem polarLog_integrand_periodic {u : ℂ → ℂ} {c : ℂ} :
    ∀ x : ℝ, (fun ζ : ℂ => u (c + Complex.exp ζ) * Complex.exp ζ) ((x : ℂ) + (0 : ℝ) * I) =
      (fun ζ : ℂ => u (c + Complex.exp ζ) * Complex.exp ζ) ((x : ℂ) + (2 * π : ℝ) * I) := by
  set τ : ℂ → ℂ := fun ζ => c + Complex.exp ζ with hτ_def
  set F : ℂ → ℂ := fun ζ => u (τ ζ) * Complex.exp ζ with hF_def
  change ∀ x : ℝ, F ((x : ℂ) + (0 : ℝ) * I) = F ((x : ℂ) + (2 * π : ℝ) * I)
  intro x
  have hx0 : (x : ℂ) + (0 : ℝ) * I = (x : ℂ) := by push_cast; ring
  have hx2pi : (x : ℂ) + (2 * π : ℝ) * I = (x : ℂ) + 2 * π * I := by push_cast; ring
  have hexp_eq : Complex.exp ((x : ℂ) + 2 * π * I) = Complex.exp (x : ℂ) :=
    Complex.exp_periodic x
  have hτ_eq : τ ((x : ℂ) + 2 * π * I) = τ (x : ℂ) := by
    rw [hτ_def]; simp only; rw [hexp_eq]
  rw [hF_def, hx0, hx2pi]
  simp only
  rw [hτ_eq, hexp_eq]

/-- On the open rectangle the integrand has the within-derivative as an honest Fréchet derivative.
Split out of `circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` for the
200-line proof size we hold ourselves to. -/
private theorem hasFDerivAt_polarLog_integrand {u : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hInterior_diff : ∀ ζ ∈ Complex.reProdIm (Set.Ioo (Real.log r) (Real.log R))
        (Set.Ioo (0 : ℝ) (2 * π)), DifferentiableAt ℝ u (c + Complex.exp ζ)) :
    ∀ ζ ∈ Complex.reProdIm (Set.Ioo (Real.log r) (Real.log R)) (Set.Ioo (0 : ℝ) (2 * π)),
      HasFDerivAt (fun ζ : ℂ => u (c + Complex.exp ζ) * Complex.exp ζ)
        (fderivWithin ℝ (fun ζ : ℂ => u (c + Complex.exp ζ) * Complex.exp ζ)
          (Complex.reProdIm (Set.Icc (Real.log r) (Real.log R))
            (Set.Icc (0 : ℝ) (2 * π))) ζ) ζ := by
  set a : ℝ := Real.log r with ha_def
  set b : ℝ := Real.log R with hb_def
  set τ : ℂ → ℂ := fun ζ => c + Complex.exp ζ with hτ_def
  set Rec : Set ℂ := Complex.reProdIm (Set.Icc a b) (Set.Icc (0 : ℝ) (2 * π)) with hRec_def
  set F : ℂ → ℂ := fun ζ => u (τ ζ) * Complex.exp ζ with hF_def
  set RecOpen : Set ℂ := Complex.reProdIm (Set.Ioo a b) (Set.Ioo (0 : ℝ) (2 * π)) with
    hRecOpen_def
  set f' : ℂ → (ℂ →L[ℝ] ℂ) := fderivWithin ℝ F Rec with hf'_def
  have hτ_diffC : ∀ ζ, DifferentiableAt ℂ τ ζ := fun ζ =>
    (Complex.differentiableAt_exp).const_add c
  have hτ_diffR : ∀ ζ, DifferentiableAt ℝ τ ζ := fun ζ => (hτ_diffC ζ).restrictScalars ℝ
  have hRecOpen_isOpen : IsOpen RecOpen := by
    rw [hRecOpen_def, Complex.reProdIm]
    exact (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  have hRecOpen_sub : RecOpen ⊆ Rec := by
    rw [hRecOpen_def, hRec_def]
    intro ζ hζ
    rw [Complex.mem_reProdIm] at hζ ⊢
    exact ⟨⟨hζ.1.1.le, hζ.1.2.le⟩, ⟨hζ.2.1.le, hζ.2.2.le⟩⟩
  change ∀ ζ ∈ RecOpen, HasFDerivAt F (f' ζ) ζ
  intro ζ hζ
  have hud : DifferentiableAt ℝ u (τ ζ) := hInterior_diff ζ hζ
  have hτd : DifferentiableAt ℝ τ ζ := hτ_diffR ζ
  have hexpd : DifferentiableAt ℝ Complex.exp ζ := Complex.differentiableAt_exp (𝕜 := ℝ)
  have hFd : DifferentiableAt ℝ F ζ := by
    have h1 : DifferentiableAt ℝ (u ∘ τ) ζ := hud.comp ζ hτd
    have h2 : DifferentiableAt ℝ (fun ζ => (u ∘ τ) ζ * Complex.exp ζ) ζ := h1.mul hexpd
    simpa [hF_def, Function.comp] using h2
  have hnhds : Rec ∈ nhds ζ :=
    Filter.mem_of_superset (hRecOpen_isOpen.mem_nhds hζ) hRecOpen_sub
  rw [hf'_def, fderivWithin_of_mem_nhds hnhds]
  exact hFd.hasFDerivAt

/-- Pointwise, the Stokes integrand equals `2i` times the Jacobian-weighted Wirtinger derivative.
Split out of `circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` for the
200-line proof size we hold ourselves to. -/
private theorem stokes_integrand_eq {u : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hInterior_diff : ∀ ζ ∈ Complex.reProdIm (Set.Ioo (Real.log r) (Real.log R))
        (Set.Ioo (0 : ℝ) (2 * π)), DifferentiableAt ℝ u (c + Complex.exp ζ)) :
    ∀ ζ ∈ Complex.reProdIm (Set.Ioo (Real.log r) (Real.log R)) (Set.Ioo (0 : ℝ) (2 * π)),
      I • (fderivWithin ℝ (fun ζ : ℂ => u (c + Complex.exp ζ) * Complex.exp ζ)
            (Complex.reProdIm (Set.Icc (Real.log r) (Real.log R))
              (Set.Icc (0 : ℝ) (2 * π))) ζ) 1 -
          (fderivWithin ℝ (fun ζ : ℂ => u (c + Complex.exp ζ) * Complex.exp ζ)
            (Complex.reProdIm (Set.Icc (Real.log r) (Real.log R))
              (Set.Icc (0 : ℝ) (2 * π))) ζ) I
        = 2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) •
            wirtingerDbar u (c + Complex.exp ζ)) := by
  set a : ℝ := Real.log r with ha_def
  set b : ℝ := Real.log R with hb_def
  set τ : ℂ → ℂ := fun ζ => c + Complex.exp ζ with hτ_def
  set Rec : Set ℂ := Complex.reProdIm (Set.Icc a b) (Set.Icc (0 : ℝ) (2 * π)) with hRec_def
  set F : ℂ → ℂ := fun ζ => u (τ ζ) * Complex.exp ζ with hF_def
  set RecOpen : Set ℂ := Complex.reProdIm (Set.Ioo a b) (Set.Ioo (0 : ℝ) (2 * π)) with
    hRecOpen_def
  set f' : ℂ → (ℂ →L[ℝ] ℂ) := fderivWithin ℝ F Rec with hf'_def
  have hRecOpen_isOpen : IsOpen RecOpen := by
    rw [hRecOpen_def, Complex.reProdIm]
    exact (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  have hRecOpen_sub : RecOpen ⊆ Rec := by
    rw [hRecOpen_def, hRec_def]
    intro ζ hζ
    rw [Complex.mem_reProdIm] at hζ ⊢
    exact ⟨⟨hζ.1.1.le, hζ.1.2.le⟩, ⟨hζ.2.1.le, hζ.2.2.le⟩⟩
  change ∀ ζ ∈ RecOpen, I • f' ζ 1 - f' ζ I
    = 2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ))
  intro ζ hζ
  have hFderiv_eq : f' ζ = fderiv ℝ F ζ := by
    rw [hf'_def]
    exact fderivWithin_of_mem_nhds
      (Filter.mem_of_superset (hRecOpen_isOpen.mem_nhds hζ) hRecOpen_sub)
  rw [hFderiv_eq]
  have hud : DifferentiableAt ℝ u (τ ζ) := hInterior_diff ζ hζ
  have hFeq : F = fun w => u (c + Complex.exp w) * Complex.exp w := by rw [hF_def, hτ_def]
  have hwF : wirtingerDbar F ζ
      = Complex.exp ζ * (starRingEnd ℂ) (Complex.exp ζ) * wirtingerDbar u (τ ζ) := by
    rw [hFeq]
    exact wirtingerDbar_expSubst_eq (u := u) (c := c) (ζ := ζ) (by rwa [hτ_def] at hud)
  have h2i : I • fderiv ℝ F ζ 1 - fderiv ℝ F ζ I = 2 * I * wirtingerDbar F ζ := by
    simp only [wirtingerDbar, smul_eq_mul]
    have hI2 : I * I = -1 := Complex.I_mul_I
    linear_combination (-(fderiv ℝ F ζ I)) * hI2
  rw [h2i, hwF, Complex.mul_conj, Complex.real_smul]

/-- Each horizontal boundary of the rectangle integrates to the corresponding circle integral.
Split out of `circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` for the
200-line proof size we hold ourselves to. -/
private theorem smul_intervalIntegral_eq_circleIntegral {u : ℂ → ℂ} {c : ℂ} {t ρ : ℝ}
    (heρ : Real.exp t = ρ) :
    I • (∫ y : ℝ in (0 : ℝ)..(2 * π),
        (fun ζ : ℂ => u (c + Complex.exp ζ) * Complex.exp ζ) ((t : ℂ) + y * I))
      = ∮ w in C(c, ρ), u w := by
  set τ : ℂ → ℂ := fun ζ => c + Complex.exp ζ with hτ_def
  set F : ℂ → ℂ := fun ζ => u (τ ζ) * Complex.exp ζ with hF_def
  have hFexp : ∀ (x0 ρ0 y : ℝ), Real.exp x0 = ρ0 →
      F ((x0 : ℂ) + y * I) = u (c + ρ0 * Complex.exp (y * I)) * (ρ0 * Complex.exp (y * I)) := by
    intro x0 ρ0 y hx0
    rw [hF_def, hτ_def]
    simp only
    have hexp_split : Complex.exp ((x0 : ℂ) + y * I) = ρ0 * Complex.exp (y * I) := by
      rw [Complex.exp_add, ← Complex.ofReal_exp, hx0]
    rw [hexp_split]
  change I • (∫ y : ℝ in (0 : ℝ)..(2 * π), F ((t : ℂ) + y * I)) = ∮ w in C(c, ρ), u w
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro y _
  change I • F ((t : ℂ) + y * I) = deriv (circleMap c ρ) y • u (circleMap c ρ y)
  rw [hFexp t ρ y heρ, deriv_circleMap, circleMap, circleMap]
  simp only [zero_add, smul_eq_mul]
  ring

/-- The open rectangle is nonempty when `a < b`. Split out of
`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` for the 200-line proof
size we hold ourselves to. -/
private theorem reProdIm_Ioo_nonempty {a b : ℝ} (hab : a < b) :
    (Complex.reProdIm (Set.Ioo a b) (Set.Ioo (0 : ℝ) (2 * π))).Nonempty := by
  refine ⟨⟨(a + b) / 2, π⟩, ?_⟩
  rw [Complex.mem_reProdIm]
  refine ⟨?_, ?_⟩
  · change (a + b) / 2 ∈ Set.Ioo a b
    constructor <;> linarith
  · change π ∈ Set.Ioo (0 : ℝ) (2 * π)
    constructor <;> linarith [Real.pi_pos]

/-- The iterated interval integral over the rectangle is the set integral over it. Split out of
`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` for the 200-line proof
size we hold ourselves to. -/
private theorem iterated_eq_setIntegral_reProdIm {a b : ℝ} (hab : a < b)
    {G : ℂ → ℂ} (hHi : IntegrableOn G
      (Complex.reProdIm (Set.Icc a b) (Set.Icc (0 : ℝ) (2 * π)))) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in (0 : ℝ)..(2 * π), G ((x : ℂ) + y * I)) =
      ∫ ζ in Complex.reProdIm (Set.Icc a b) (Set.Icc (0 : ℝ) (2 * π)), G ζ :=
  (setIntegral_reProdIm_eq_intervalIntegral
    (z := (⟨a, 0⟩ : ℂ)) (w := (⟨b, 2 * π⟩ : ℂ)) hab.le Real.two_pi_pos.le hHi).symm

/-- **Atom 1′** (annulus Stokes, general — no meromorphy, no residue): area-to-boundary identity
for the `dbar` of an arbitrary `C¹` function on a closed annulus. -/
theorem circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar
    {u : ℂ → ℂ} {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R)
    (hu : ContDiffOn ℝ 1 u (Metric.closedBall c R \ Metric.ball c r)) :
    (∮ w in C(c, R), u w) - (∮ w in C(c, r), u w) =
      2 * I * ∫ w in (Metric.closedBall c R \ Metric.ball c r), wirtingerDbar u w := by
  rcases hle.lt_or_eq with hRr | hRr
  swap
  · -- Degenerate case `r = R`: the annulus collapses to a circle (measure zero).
    subst hRr
    have hAeq : Metric.closedBall c r \ Metric.ball c r = Metric.sphere c r := by
      ext w
      simp only [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere, Set.mem_sdiff, not_lt]
      exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
    rw [hAeq, MeasureTheory.setIntegral_measure_zero _ (Measure.addHaar_sphere volume c r),
      mul_zero, sub_self]
  · -- Main case `r < R`.
    have hRpos : 0 < R := h0.trans hRr
    set a : ℝ := Real.log r with ha_def
    set b : ℝ := Real.log R with hb_def
    have hea : Real.exp a = r := Real.exp_log h0
    have heb : Real.exp b = R := Real.exp_log hRpos
    have hab : a < b := (Real.log_lt_log_iff h0 hRpos).mpr hRr
    set τ : ℂ → ℂ := fun ζ => c + Complex.exp ζ with hτ_def
    set A : Set ℂ := Metric.closedBall c R \ Metric.ball c r with hA_def
    set Rec : Set ℂ := Complex.reProdIm (Set.Icc a b) (Set.Icc (0 : ℝ) (2 * π)) with hRec_def
    set F : ℂ → ℂ := fun ζ => u (τ ζ) * Complex.exp ζ with hF_def
    -- `τ` is entire.
    have hτ_diffC : ∀ ζ, DifferentiableAt ℂ τ ζ := fun ζ =>
      (Complex.differentiableAt_exp).const_add c
    have hτ_diffR : ∀ ζ, DifferentiableAt ℝ τ ζ := fun ζ => (hτ_diffC ζ).restrictScalars ℝ
    have hderivτ : ∀ ζ, deriv τ ζ = Complex.exp ζ := by
      intro ζ
      rw [hτ_def, deriv_const_add, congrFun Complex.deriv_exp ζ]
    -- `τ` maps `Rec` into `A`.
    obtain ⟨hτ_maps, -, -⟩ := polarLog_mapsTo_injOn_image h0 hRpos hRr
    -- The half-open-in-angle domain, on which `τ` is a genuine bijection onto `A`.
    set s : Set ℂ := Complex.reProdIm (Set.Icc a b) (Set.Ico (0 : ℝ) (2 * π)) with hs_def
    have hs_sub_Rec : s ⊆ Rec := by
      intro ζ hζ
      rw [hs_def, Complex.mem_reProdIm] at hζ
      rw [hRec_def, Complex.mem_reProdIm]
      exact ⟨hζ.1, ⟨hζ.2.1, hζ.2.2.le⟩⟩
    have hs_maps : Set.MapsTo τ s A := hτ_maps.mono_left hs_sub_Rec
    -- Injectivity of `τ` on `s`.
    obtain ⟨-, hτ_inj, -⟩ := polarLog_mapsTo_injOn_image h0 hRpos hRr
    -- `τ '' s = A` exactly.
    obtain ⟨-, -, hτ_image⟩ := polarLog_mapsTo_injOn_image h0 hRpos hRr
    -- `Rec` is convex with nonempty interior, hence a set of unique differentiability.
    have hRe_lin : IsLinearMap ℝ Complex.re := ⟨Complex.add_re, fun t v => by
      simp [Complex.real_smul, Complex.mul_re]⟩
    have hIm_lin : IsLinearMap ℝ Complex.im := ⟨Complex.add_im, fun t v => by
      simp [Complex.real_smul, Complex.mul_im]⟩
    have hRec_convex : Convex ℝ Rec := by
      rw [hRec_def, Complex.reProdIm]
      exact ((convex_Icc a b).is_linear_preimage hRe_lin).inter
        ((convex_Icc 0 (2 * π)).is_linear_preimage hIm_lin)
    set RecOpen : Set ℂ := Complex.reProdIm (Set.Ioo a b) (Set.Ioo (0 : ℝ) (2 * π)) with
      hRecOpen_def
    have hRecOpen_isOpen : IsOpen RecOpen := by
      rw [hRecOpen_def, Complex.reProdIm]
      exact (isOpen_Ioo.preimage Complex.continuous_re).inter
        (isOpen_Ioo.preimage Complex.continuous_im)
    have hRecOpen_sub : RecOpen ⊆ Rec := by
      rw [hRecOpen_def, hRec_def]
      exact Complex.reProdIm_subset_iff.mpr
        (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
    have hRecOpen_nonempty : RecOpen.Nonempty := reProdIm_Ioo_nonempty hab
    have hRec_int : (interior Rec).Nonempty :=
      hRecOpen_nonempty.mono (interior_maximal hRecOpen_sub hRecOpen_isOpen)
    have hRec_uniqueDiff : UniqueDiffOn ℝ Rec := uniqueDiffOn_convex hRec_convex hRec_int
    -- Regularity of `τ`, `exp`, and `F` on `Rec`.
    have hτ_CD : ContDiff ℝ 1 τ := by
      rw [hτ_def]; exact contDiff_const.add (Complex.contDiff_exp (𝕜 := ℝ))
    have hexp_CD : ContDiff ℝ 1 Complex.exp := Complex.contDiff_exp (𝕜 := ℝ)
    have hu_CDRec : ContDiffOn ℝ 1 (u ∘ τ) Rec := ContDiffOn.comp hu hτ_CD.contDiffOn hτ_maps
    have hF_CDRec : ContDiffOn ℝ 1 F Rec := by
      have h1 : ContDiffOn ℝ 1 (fun ζ => (u ∘ τ) ζ * Complex.exp ζ) Rec :=
        hu_CDRec.mul hexp_CD.contDiffOn
      simpa [hF_def, Function.comp] using h1
    -- The explicit derivative candidate `f'`, continuous on all of `Rec`.
    set f' : ℂ → (ℂ →L[ℝ] ℂ) := fderivWithin ℝ F Rec with hf'_def
    have hf'_cont : ContinuousOn f' Rec :=
      hF_CDRec.continuousOn_fderivWithin hRec_uniqueDiff (le_refl 1)
    have hu_contOn : ContinuousOn u A := hu.continuousOn
    have hHc : ContinuousOn F Rec := by
      have h1 : ContinuousOn (u ∘ τ) Rec := hu_contOn.comp (hτ_CD.continuous.continuousOn) hτ_maps
      have h2 : ContinuousOn (fun ζ => (u ∘ τ) ζ * Complex.exp ζ) Rec :=
        h1.mul (hexp_CD.continuous.continuousOn)
      simpa [hF_def, Function.comp] using h2
    have hHi : IntegrableOn (fun ζ => I • f' ζ 1 - f' ζ I) Rec := by
      have hcont : ContinuousOn (fun ζ => I • f' ζ 1 - f' ζ I) Rec := by
        have h1 : ContinuousOn (fun ζ => f' ζ 1) Rec := hf'_cont.clm_apply continuousOn_const
        have h2 : ContinuousOn (fun ζ => f' ζ I) Rec := hf'_cont.clm_apply continuousOn_const
        exact (h1.const_smul I).sub h2
      have hcompact : IsCompact Rec := by
        rw [hRec_def]; exact IsCompact.reProdIm isCompact_Icc isCompact_Icc
      exact hcont.integrableOn_compact hcompact
    -- Interior points of `Rec` (in the `ζ`-rectangle) map to interior points of `A`.
    have hInterior_diff := differentiableAt_comp_polarLog h0 hRpos hu
    have hHd := hasFDerivAt_polarLog_integrand hInterior_diff
    -- Apply the rectangle Stokes lemma with corners `z0 = a`, `w0 = b + 2πi`.
    set z0 : ℂ := (⟨a, 0⟩ : ℂ) with hz0_def
    set w0 : ℂ := (⟨b, 2 * π⟩ : ℂ) with hw0_def
    have hz0re : z0.re = a := rfl
    have hz0im : z0.im = 0 := rfl
    have hw0re : w0.re = b := rfl
    have hw0im : w0.im = 2 * π := rfl
    have hRec_eq : Complex.reProdIm (Set.uIcc z0.re w0.re) (Set.uIcc z0.im w0.im) = Rec := by
      rw [hz0re, hw0re, hz0im, hw0im, Set.uIcc_of_le hab.le, Set.uIcc_of_le Real.two_pi_pos.le]
    have hHc' : ContinuousOn F (Complex.reProdIm (Set.uIcc z0.re w0.re) (Set.uIcc z0.im w0.im)) :=
        by
      rw [hRec_eq]; exact hHc
    have hHd' : ∀ x ∈ Set.Ioo (min z0.re w0.re) (max z0.re w0.re) ×ℂ
        Set.Ioo (min z0.im w0.im) (max z0.im w0.im), HasFDerivAt F (f' x) x := by
      rw [hz0re, hw0re, hz0im, hw0im, min_eq_left hab.le, max_eq_right hab.le,
        min_eq_left Real.two_pi_pos.le, max_eq_right Real.two_pi_pos.le]
      exact hHd
    have hHi' : IntegrableOn (fun ζ => I • f' ζ 1 - f' ζ I)
        (Complex.reProdIm (Set.uIcc z0.re w0.re) (Set.uIcc z0.im w0.im)) := by
      rw [hRec_eq]; exact hHi
    have hrect := Complex.integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real F f' z0 w0
      hHc' hHd' hHi'
    rw [hz0re, hw0re, hz0im, hw0im] at hrect
    -- The `y`-boundary cancels by periodicity of `exp`.
    have hperiod := polarLog_integrand_periodic (u := u) (c := c)
    have hLHS_yb : (∫ x : ℝ in a..b, F ((x : ℂ) + (0 : ℝ) * I))
        - (∫ x : ℝ in a..b, F ((x : ℂ) + (2 * π : ℝ) * I)) = 0 :=
      sub_eq_zero.mpr (intervalIntegral.integral_congr (fun x _ => hperiod x))
    -- The `x`-boundary identifies with the two circle integrals.
    have hFexp : ∀ (x0 ρ0 y : ℝ), Real.exp x0 = ρ0 →
        F ((x0 : ℂ) + y * I) = u (c + ρ0 * Complex.exp (y * I)) * (ρ0 * Complex.exp (y * I)) := by
      intro x0 ρ0 y hx0
      rw [hF_def, hτ_def]
      simp only
      have hexp_split : Complex.exp ((x0 : ℂ) + y * I) = ρ0 * Complex.exp (y * I) := by
        rw [Complex.exp_add, ← Complex.ofReal_exp, hx0]
      rw [hexp_split]
    have hcircleR := smul_intervalIntegral_eq_circleIntegral (u := u) (c := c) heb
    have hcircler := smul_intervalIntegral_eq_circleIntegral (u := u) (c := c) hea
    rw [hLHS_yb, zero_add, hcircleR, hcircler] at hrect
    clear hHc hHd hHc' hHd' hf'_cont hF_CDRec hu_CDRec hRec_convex hRec_uniqueDiff
      hRec_int hτ_CD hexp_CD hRec_eq hperiod hLHS_yb hFexp hcircleR hcircler
    -- Convert the RHS iterated integral to a set integral over `Rec`.
    have hiter_to_set := iterated_eq_setIntegral_reProdIm hab (G := fun ζ => I • f' ζ 1 - f' ζ I)
      (by rw [← hRec_def]; exact hHi)
    rw [hiter_to_set] at hrect
    -- Pointwise, on `RecOpen`, the integrand matches `2i·normSq(exp ζ)·wirtingerDbar u (τ ζ)`.
    have hpt := stokes_integrand_eq hInterior_diff
    have hRecOpen_null_diff : volume (Rec \ RecOpen) = 0 := by
      rw [hRec_def, hRecOpen_def]
      exact measure_frame_null a b 0 (2 * π) hab.le Real.two_pi_pos.le
    have hae : ∀ᵐ ζ ∂volume, ζ ∈ Rec →
        I • f' ζ 1 - f' ζ I
          = 2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ)) := by
      have hnmem : ∀ᵐ ζ ∂volume, ζ ∉ Rec \ RecOpen := by
        rw [MeasureTheory.ae_iff]
        simp only [not_not]
        exact hRecOpen_null_diff
      filter_upwards [hnmem] with ζ hζ hζRec
      by_contra hne
      exact hζ ⟨hζRec, fun hop => hne (hpt ζ hop)⟩
    have hRec_meas : MeasurableSet Rec := by
      rw [hRec_def, Complex.reProdIm]
      exact (measurableSet_Icc.preimage Complex.measurable_re).inter
        (measurableSet_Icc.preimage Complex.measurable_im)
    have hset_eq : (∫ ζ in Rec, I • f' ζ 1 - f' ζ I)
        = ∫ ζ in Rec, 2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ)) :=
      MeasureTheory.setIntegral_congr_ae hRec_meas hae
    rw [hset_eq] at hrect
    have hpull : (∫ ζ in Rec,
          2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ)))
        = 2 * I * ∫ ζ in Rec, (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ) :=
      MeasureTheory.integral_const_mul _ _
    rw [hpull] at hrect
    -- Restrict from `Rec` to `s` (differ by the one null edge `im = 2π`).
    have hs_meas : MeasurableSet s := by
      rw [hs_def, Complex.reProdIm]
      exact (measurableSet_Icc.preimage Complex.measurable_re).inter
        (measurableSet_Ico.preimage Complex.measurable_im)
    have hRecs_null_diff : volume (Rec \ s) = 0 := by
      have heq : Rec \ s = Complex.reProdIm (Set.Icc a b) ({2 * π} : Set ℝ) := by
        rw [hRec_def, hs_def, ← Icc_sdiff_Ico_same Real.two_pi_pos.le]
        ext w
        simp only [Complex.mem_reProdIm, Set.mem_sdiff]
        tauto
      rw [heq]
      exact measure_reProdIm_im_singleton (2 * π) (Set.Icc a b)
    have hRec_ae_s : Rec =ᵐ[volume] s := by
      rw [ae_eq_set]
      refine ⟨hRecs_null_diff, ?_⟩
      rw [Set.sdiff_eq_empty.mpr hs_sub_Rec]
      exact measure_empty
    have hRec_to_s : (∫ ζ in Rec, (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ))
        = ∫ ζ in s, (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ) :=
      MeasureTheory.setIntegral_congr_set hRec_ae_s
    rw [hRec_to_s] at hrect
    -- The Jacobian change of variables transports this to the area integral over `A`.
    have hJacobian : (∫ ζ in s, (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ))
        = ∫ w in A, wirtingerDbar u w := by
      have hderiv_eq : ∀ ζ ∈ s, HasFDerivWithinAt τ (fderiv ℝ τ ζ) s ζ :=
        fun ζ _ => (hτ_diffR ζ).hasFDerivAt.hasFDerivWithinAt
      have hjac := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume hs_meas
        hderiv_eq hτ_inj (wirtingerDbar u)
      rw [hτ_image] at hjac
      rw [hjac]
      apply MeasureTheory.setIntegral_congr_fun hs_meas
      intro ζ _
      change (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ)
          = |(fderiv ℝ τ ζ).det| • wirtingerDbar u (τ ζ)
      congr 1
      rw [det_fderiv_of_differentiableAt (hτ_diffC ζ), hderivτ,
        abs_of_nonneg (Complex.normSq_nonneg _)]
    rw [hJacobian] at hrect
    exact hrect

/-! ## The smeared residue theorem (Atom 2) -/

/-- **Atom 2** (the smeared residue theorem — the "one honest integration atom" routing decision
#2 budgets for): `g` compactly supported in `U`, locally CONSTANT near the puncture `p` (§D4),
`f` holomorphic on `U \ {p}` and meromorphic at `p`. -/
theorem integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt {g f : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hU : IsOpen U) (_hpU : p ∈ U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U)
    (hconst : g =ᶠ[nhds p] Function.const ℂ (g p))
    (hf : DifferentiableOn ℂ f (U \ {p})) (hfp : MeromorphicAt f p) :
    ∫ w : ℂ, wirtingerDbar g w * f w = -π * g p * resAt f p := by
  -- Step 1: `g ≡ g p` on some `ball p δ`, hence `wirtingerDbar g ≡ 0` there.
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hconst
  have hwbar0 : ∀ w ∈ Metric.ball p δ, wirtingerDbar g w = 0 := by
    intro w hw
    have hgnh : g =ᶠ[nhds w] Function.const ℂ (g p) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw] with x hx using hδ x hx
    rw [wirtingerDbar_congr_nhds g (Function.const ℂ (g p)) w hgnh]
    exact wirtingerDbar_const w (g p)
  -- Choose `R` with `tsupport g ⊆ ball p R` and `δ ≤ R`.
  obtain ⟨R0, hR0⟩ := hcs.isBounded.subset_ball p
  set R : ℝ := max R0 (max δ 1) with hR_def
  have hRpos : 0 < R :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right δ 1) (le_max_right R0 (max δ 1)))
  have hRδ : δ ≤ R := le_trans (le_max_left δ 1) (le_max_right R0 (max δ 1))
  have htsub_ballR : tsupport g ⊆ Metric.ball p R :=
    hR0.trans (Metric.ball_subset_ball (le_max_left _ _))
  -- Choose `ε ∈ (0, δ)` in the eventual set of the residue bridge.
  obtain ⟨ε, hε_res, hε_mem⟩ :=
    ((MeromorphicAt.eventually_circleIntegral_eq_two_pi_I_mul_resAt hfp).and
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hδpos) (fun ρ hρ => hρ))).exists
  have hεpos : 0 < ε := hε_mem.1
  have hεδ : ε < δ := hε_mem.2
  have hεR : ε ≤ R := le_of_lt (lt_of_lt_of_le hεδ hRδ)
  -- `v := g * f` is `ContDiffOn ℝ 1` on the annulus `closedBall p R \ ball p ε`.
  set v : ℂ → ℂ := fun w => g w * f w with hv_def
  have hUp_open : IsOpen (U \ {p}) := hU.sdiff isClosed_singleton
  have hf_CD : ContDiffOn ℝ 1 f (U \ {p}) := by
    have hfAn : AnalyticOnNhd ℂ f (U \ {p}) := hf.analyticOnNhd hUp_open
    have hfCD : ContDiffOn ℂ 1 f (U \ {p}) := hfAn.contDiffOn hUp_open.uniqueDiffOn
    exact hfCD.restrict_scalars ℝ
  have hwp_ne : ∀ w, w ∈ Metric.closedBall p R \ Metric.ball p ε → w ∈ tsupport g → w ≠ p := by
    intro w hw _ hcontra
    rw [hcontra] at hw
    exact hw.2 (Metric.mem_ball_self hεpos)
  have hv_ContDiffAt : ∀ w ∈ Metric.closedBall p R \ Metric.ball p ε, ContDiffAt ℝ 1 v w := by
    intro w hw
    by_cases hwt : w ∈ tsupport g
    · have hwU : w ∈ U := hsub hwt
      have hwne : w ≠ p := hwp_ne w hw hwt
      have hwUp : w ∈ U \ {p} := ⟨hwU, hwne⟩
      have hgAt : ContDiffAt ℝ 1 g w := hg.contDiffAt (hU.mem_nhds hwU)
      have hfAt : ContDiffAt ℝ 1 f w := hf_CD.contDiffAt (hUp_open.mem_nhds hwUp)
      exact hgAt.mul hfAt
    · have hg0 : g =ᶠ[nhds w] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hwt
      have hv0 : v =ᶠ[nhds w] (fun _ => (0 : ℂ)) := by
        filter_upwards [hg0] with x hx
        change g x * f x = 0
        rw [hx]; ring
      exact contDiffAt_const.congr_of_eventuallyEq hv0
  have hv_ContDiffOn : ContDiffOn ℝ 1 v (Metric.closedBall p R \ Metric.ball p ε) :=
    fun w hw => (hv_ContDiffAt w hw).contDiffWithinAt
  have hannulus := circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar
    hεpos hεR hv_ContDiffOn
  -- The outer circle integral vanishes (`g ≡ 0` there, `R` chosen `⊇ tsupport g`).
  have hgouter0 : ∀ w ∈ Metric.sphere p R, g w = 0 := by
    intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hwt
    have hlt := htsub_ballR hwt
    rw [Metric.mem_ball] at hlt
    rw [Metric.mem_sphere] at hw
    exact absurd hw (ne_of_lt hlt)
  have hoq : (∮ w in C(p, R), v w) = 0 := by
    have heq0 : Set.EqOn v (fun _ => (0 : ℂ)) (Metric.sphere p R) := by
      intro w hw
      change g w * f w = 0
      rw [hgouter0 w hw, zero_mul]
    rw [circleIntegral.integral_congr hRpos.le heq0]
    simp [circleIntegral]
  -- The inner circle integral is `g p * (2πi · resAt f p)` (`g ≡ g p` exactly there, `ε < δ`).
  have hgε : Set.EqOn g (Function.const ℂ (g p)) (Metric.sphere p ε) := by
    intro w hw
    rw [Metric.mem_sphere] at hw
    exact hδ w (by rw [Metric.mem_ball, hw]; exact hεδ)
  have hvε : Set.EqOn v (fun w => g p * f w) (Metric.sphere p ε) := by
    intro w hw
    change g w * f w = g p * f w
    rw [hgε hw]
    rfl
  have hcircleε : (∮ w in C(p, ε), v w) = g p * (2 * π * I * resAt f p) := by
    rw [circleIntegral.integral_congr hεpos.le hvε, circleIntegral.integral_const_mul, hε_res]
  -- Assemble and divide by `2i`.
  have hεeq : (∮ w in C(p, ε), v w)
      = -(2 * I * ∫ w in (Metric.closedBall p R \ Metric.ball p ε), wirtingerDbar v w) := by
    have h2 := hannulus
    rw [hoq] at h2
    linear_combination -h2
  have hfinal_annulus : g p * (2 * π * I * resAt f p)
      = -(2 * I * ∫ w in (Metric.closedBall p R \ Metric.ball p ε), wirtingerDbar v w) := by
    rw [← hcircleε]; exact hεeq
  have h2Ine : (2 : ℂ) * I ≠ 0 := by simp [Complex.I_ne_zero]
  have harea : (∫ w in (Metric.closedBall p R \ Metric.ball p ε), wirtingerDbar v w)
      = -π * g p * resAt f p := by
    have hmul : 2 * I * (∫ w in (Metric.closedBall p R \ Metric.ball p ε), wirtingerDbar v w)
        = 2 * I * (-π * g p * resAt f p) := by
      linear_combination hfinal_annulus
    exact mul_left_cancel₀ h2Ine hmul
  -- On the annulus (`w ≠ p`), `wirtingerDbar v w = wirtingerDbar g w * f w`.
  have hv_eq_gf : ∀ w ∈ Metric.closedBall p R \ Metric.ball p ε,
      wirtingerDbar v w = wirtingerDbar g w * f w := by
    intro w hw
    by_cases hwt : w ∈ tsupport g
    · have hwU : w ∈ U := hsub hwt
      have hwne : w ≠ p := hwp_ne w hw hwt
      have hwUp : w ∈ U \ {p} := ⟨hwU, hwne⟩
      have hgd : DifferentiableAt ℝ g w := (hg.contDiffAt (hU.mem_nhds hwU)).differentiableAt
        (by norm_num)
      have hfd : DifferentiableAt ℂ f w := (hf w hwUp).differentiableAt (hUp_open.mem_nhds hwUp)
      rw [hv_def]
      exact wirtingerDbar_mul_of_differentiableAt hgd hfd
    · have hg0 : g =ᶠ[nhds w] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hwt
      have hgbar0 : wirtingerDbar g w = 0 := by
        rw [wirtingerDbar_congr_nhds g (fun _ => (0 : ℂ)) w hg0]
        simp [wirtingerDbar]
      rw [hgbar0, zero_mul, hv_def]
      exact wirtingerDbar_mul_eq_zero_of_notMem_tsupport hwt
  have harea_gf : (∫ w in (Metric.closedBall p R \ Metric.ball p ε), wirtingerDbar g w * f w)
      = -π * g p * resAt f p := by
    rw [← harea]
    exact MeasureTheory.setIntegral_congr_fun
      (measurableSet_closedBall.diff measurableSet_ball) (fun w hw => (hv_eq_gf w hw).symm)
  -- The area integral over the annulus equals the global integral (the rest vanishes).
  have hglobal_eq_annulus : (∫ w : ℂ, wirtingerDbar g w * f w)
      = ∫ w in (Metric.closedBall p R \ Metric.ball p ε), wirtingerDbar g w * f w := by
    apply (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro w hw
    rw [Set.mem_sdiff, not_and, not_not] at hw
    by_cases hw1 : w ∈ Metric.closedBall p R
    · have hw2 : w ∈ Metric.ball p ε := hw hw1
      have hwδ : w ∈ Metric.ball p δ := Metric.ball_subset_ball hεδ.le hw2
      rw [hwbar0 w hwδ, zero_mul]
    · have hwt : w ∉ tsupport g := fun h => hw1 (Metric.ball_subset_closedBall (htsub_ballR h))
      have hg0 : g =ᶠ[nhds w] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hwt
      have hgbar0 : wirtingerDbar g w = 0 := by
        rw [wirtingerDbar_congr_nhds g (fun _ => (0 : ℂ)) w hg0]
        simp [wirtingerDbar]
      rw [hgbar0, zero_mul]
  rw [hglobal_eq_annulus]
  exact harea_gf

/-! ## Model-case regression check (`f = (·-p)⁻¹`, §8.4), and the abel-weak-solutions refinement -/

/-- Model-case corollary (the verification the task asked for, `f = 1/(z-p)`, kept as a named
sanity lemma / regression test on Atom 2's `-π` normalization constant) — proved a *second*,
independent way, translating `RS.cauchyPompeiu` (dbar-solvability) through the measure-preserving
involution `w ↦ p - w`, NOT as a corollary of Atom 2 itself.

**Deviation from the design's §5.3 signature**: the frozen design states this lemma with the same
`hpU`/`hconst` hypotheses as Atom 2, "for signature parity" only. Both are provably UNUSED in this
proof (neither name appears in the tactic block below) — exactly as the design's own §8.4 already
observes ("a simple pole is exactly the borderline order where the general-`g` and locally-
constant-`g` formulas coincide... with no local-constancy hypothesis on `g` needed at all in this
special case"). Dropped here because `abel-weak-solutions` (this unit's downstream consumer,
`docs/design/abel-weak-solutions.md` §7.3/§10/§11 risk R1) needs *exactly* this hypothesis-free
form: its `g` is a genuine holomorphic primitive, not locally constant near its punctures, so it
cannot supply `hconst`. See `integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq` below for the exact
two-puncture shape that unit's Lemma 20.3 step assembles. -/
theorem integral_wirtingerDbar_mul_inv_sub_eq {g : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U) :
    ∫ w : ℂ, wirtingerDbar g w * (w - p)⁻¹ = -π * g p := by
  have hg' : ContDiff ℝ 1 g := ContDiffOn.contDiff_of_hasCompactSupport hU hg hcs hsub
  have hcp : ∫ w : ℂ, cauchyKernel w * wirtingerDbar g (p - w) = g p :=
    cauchyPompeiu g hg' hcs p
  have hme : MeasurableEmbedding (fun w : ℂ => p - w) := measurableEmbedding_subLeft p
  have hmp : MeasureTheory.MeasurePreserving (fun w : ℂ => p - w)
      (volume : Measure ℂ) volume := MeasureTheory.Measure.measurePreserving_sub_left volume p
  have hpp : ∀ x : ℂ, p - (p - x) = x := fun x => by ring
  -- Substitute `w ↦ p - w` (a measure-preserving involution of `ℂ`) in `hcp`.
  have hcomp : ∫ x : ℂ, cauchyKernel (p - x) * wirtingerDbar g (p - (p - x))
      = ∫ w : ℂ, cauchyKernel w * wirtingerDbar g (p - w) :=
    hmp.integral_comp hme (fun w => cauchyKernel w * wirtingerDbar g (p - w))
  rw [hcp] at hcomp
  simp only [hpp] at hcomp
  -- `hcomp : ∫ x, cauchyKernel (p - x) * wirtingerDbar g x = g p`
  have hπne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hker : ∀ x : ℂ, cauchyKernel (p - x) * wirtingerDbar g x
      = (-(Real.pi : ℂ)⁻¹) * (wirtingerDbar g x * (x - p)⁻¹) := by
    intro x
    have hxp : (p - x : ℂ) = -(x - p) := by ring
    simp only [cauchyKernel, hxp]
    rw [show (Real.pi : ℂ) * -(x - p) = -(Real.pi * (x - p)) by ring, inv_neg, mul_inv]
    ring
  simp_rw [hker] at hcomp
  rw [MeasureTheory.integral_const_mul] at hcomp
  -- `hcomp : -(π⁻¹) * ∫ x, wirtingerDbar g x * (x - p)⁻¹ = g p`
  have hfin : (Real.pi : ℂ) * (-(Real.pi : ℂ)⁻¹ * ∫ x : ℂ, wirtingerDbar g x * (x - p)⁻¹)
      = Real.pi * g p := by rw [hcomp]
  rw [show (Real.pi : ℂ) * (-(Real.pi : ℂ)⁻¹ * ∫ x : ℂ, wirtingerDbar g x * (x - p)⁻¹)
      = -(Real.pi * (Real.pi : ℂ)⁻¹) * ∫ x : ℂ, wirtingerDbar g x * (x - p)⁻¹ by ring,
    mul_inv_cancel₀ hπne] at hfin
  linear_combination -hfin

/-- The `wirtingerDbar g · (·-p)⁻¹` integrand of the model-case identity above is integrable
(needed to combine several single-puncture instances of `integral_wirtingerDbar_mul_inv_sub_eq`
into one multi-puncture identity — `integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq` below).
Proved the same way: transport the convolution-integrability fact already available for
`cauchyKernel * wirtingerDbar g (p - ·)` (`HasCompactSupport.convolutionExists_right`, the same
mathlib fact `RS.cauchyPompeiu`'s own proof relies on) through the measure-preserving substitution
`w ↦ p - w`. -/
theorem integrable_wirtingerDbar_mul_inv_sub {g : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U) :
    Integrable (fun w : ℂ => wirtingerDbar g w * (w - p)⁻¹) := by
  have hg' : ContDiff ℝ 1 g := ContDiffOn.contDiff_of_hasCompactSupport hU hg hcs hsub
  have hcs_dbar : HasCompactSupport (wirtingerDbar g) := hasCompactSupport_wirtingerDbar g hcs
  have hcont_dbar : Continuous (wirtingerDbar g) := continuous_wirtingerDbar_of_contDiff_one hg'
  have hIntF : Integrable (fun w : ℂ => cauchyKernel w * wirtingerDbar g (p - w)) :=
    hcs_dbar.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_cauchyKernel
      hcont_dbar p
  have hme : MeasurableEmbedding (fun w : ℂ => p - w) := measurableEmbedding_subLeft p
  have hmp : MeasureTheory.MeasurePreserving (fun w : ℂ => p - w)
      (volume : Measure ℂ) volume := MeasureTheory.Measure.measurePreserving_sub_left volume p
  have hpp : ∀ x : ℂ, p - (p - x) = x := fun x => by ring
  have hIntComp : Integrable (fun x : ℂ => cauchyKernel (p - x) * wirtingerDbar g (p - (p - x))) :=
    hmp.integrable_comp_of_integrable hIntF
  simp only [hpp] at hIntComp
  -- `hIntComp : Integrable (fun x, cauchyKernel (p - x) * wirtingerDbar g x)`
  have hker : ∀ x : ℂ, cauchyKernel (p - x) * wirtingerDbar g x
      = (-(Real.pi : ℂ)⁻¹) * (wirtingerDbar g x * (x - p)⁻¹) := by
    intro x
    have hxp : (p - x : ℂ) = -(x - p) := by ring
    simp only [cauchyKernel, hxp]
    rw [show (Real.pi : ℂ) * -(x - p) = -(Real.pi * (x - p)) by ring, inv_neg, mul_inv]
    ring
  have hIntConst : Integrable
      (fun x : ℂ => (-(Real.pi : ℂ)⁻¹) * (wirtingerDbar g x * (x - p)⁻¹)) := by
    have heq : (fun x : ℂ => cauchyKernel (p - x) * wirtingerDbar g x)
        = (fun x : ℂ => (-(Real.pi : ℂ)⁻¹) * (wirtingerDbar g x * (x - p)⁻¹)) := funext hker
    rwa [heq] at hIntComp
  have hπne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hunit : IsUnit (-(Real.pi : ℂ)⁻¹) :=
    isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (inv_ne_zero hπne))
  exact (integrable_const_mul_iff hunit _).mp hIntConst

/-- The exact two-puncture shape `abel-weak-solutions` assembles in its Lemma-20.3-specialized
step (`docs/design/abel-weak-solutions.md` §7.3 step 3): the smeared residue identity for
`f := (·-b)⁻¹ - (·-a)⁻¹` (simple poles of residue `+1` at `b`, `-1` at `a`), matching `g b - g a`
directly, for **any** `C¹` compactly-supported `g` — no local constancy needed at either puncture,
since both poles are simple (the same reasoning as `integral_wirtingerDbar_mul_inv_sub_eq`).
Assembled from two instances of that lemma plus linearity of the Bochner integral
(`integrable_wirtingerDbar_mul_inv_sub` supplies the integrability `MeasureTheory.integral_sub`
needs). -/
theorem integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq {g : ℂ → ℂ} {U : Set ℂ} {a b : ℂ}
    (hU : IsOpen U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U) :
    ∫ w : ℂ, wirtingerDbar g w * ((w - b)⁻¹ - (w - a)⁻¹) = -π * (g b - g a) := by
  have hb := integral_wirtingerDbar_mul_inv_sub_eq (p := b) hU hg hcs hsub
  have ha := integral_wirtingerDbar_mul_inv_sub_eq (p := a) hU hg hcs hsub
  have hIntb : Integrable (fun w : ℂ => wirtingerDbar g w * (w - b)⁻¹) :=
    integrable_wirtingerDbar_mul_inv_sub (p := b) hU hg hcs hsub
  have hInta : Integrable (fun w : ℂ => wirtingerDbar g w * (w - a)⁻¹) :=
    integrable_wirtingerDbar_mul_inv_sub (p := a) hU hg hcs hsub
  have heq : (fun w : ℂ => wirtingerDbar g w * ((w - b)⁻¹ - (w - a)⁻¹))
      = (fun w : ℂ => wirtingerDbar g w * (w - b)⁻¹ - wirtingerDbar g w * (w - a)⁻¹) := by
    funext w; ring
  rw [heq, MeasureTheory.integral_sub hIntb hInta, hb, ha]
  ring

end RS

