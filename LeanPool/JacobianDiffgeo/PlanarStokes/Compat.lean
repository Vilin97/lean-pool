/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import LeanPool.JacobianDiffgeo.Dbar.Wirtinger

/-!
# Compat: Leibniz rule, `ContDiffOn` gluing, and the rectangle ↔ iterated-integral bridge

Unit: planar-stokes-atoms (`docs/design/planar-stokes.md` §5.1). Mathlib-only (plus
`Jacobian.Dbar.Wirtinger`, D10-compliant, no manifold imports). Three groups of facts:

* The Leibniz rule for `wirtingerDbar` (`wirtingerDbar_mul` and its two specializations), not
  present in `Jacobian/Dbar/Wirtinger.lean` — proved here exactly as de-risked in the design's
  spike (`scratch_stokes.lean`); flagged for upstreaming in `docs/requests/dbar-solvability.md`.
* `ContDiffOn.contDiff_of_hasCompactSupport`: the two-piece gluing argument that upgrades a
  `ContDiffOn U` function of compact support `⊆ U` to a globally `ContDiff` function.
* The `ℂ`-rectangle ↔ iterated-real-integral bridge, both as a general (no support hypothesis)
  internal building block `setIntegral_reProdIm_eq_intervalIntegral` (reused by
  `AnnulusResidue.lean`'s Step 3) and as the exported compact-support corollary
  `integral_eq_intervalIntegral_of_tsupport_subset_reProdIm`.
-/

open Complex MeasureTheory Set Filter

noncomputable section

namespace RS

variable {g f : ℂ → ℂ} {z : ℂ}

/-! ## The Leibniz rule -/

/-- Leibniz rule for the Wirtinger `dbar` (requested for upstreaming to
`Jacobian/Dbar/Wirtinger.lean` — see `docs/requests/dbar-solvability.md`; proved locally here
meanwhile, exactly as compiled in the design's spike). -/
theorem wirtingerDbar_mul (hg : DifferentiableAt ℝ g z) (hf : DifferentiableAt ℝ f z) :
    wirtingerDbar (fun w => g w * f w) z
      = wirtingerDbar g z * f z + g z * wirtingerDbar f z := by
  simp only [wirtingerDbar, fderiv_fun_mul hg hf]
  simp
  ring

/-- The `f`-holomorphic specialization: the `dbar` of a product with a holomorphic factor sees only
the other factor's `dbar`. -/
theorem wirtingerDbar_mul_of_differentiableAt (hg : DifferentiableAt ℝ g z)
    (hf : DifferentiableAt ℂ f z) :
    wirtingerDbar (fun w => g w * f w) z = wirtingerDbar g z * f z := by
  rw [wirtingerDbar_mul hg (hf.restrictScalars ℝ),
    wirtingerDbar_eq_zero_of_differentiableAt f z hf, mul_zero, add_zero]

/-- `g` vanishes identically on a whole neighborhood of any point outside `tsupport g`, so a
product with an arbitrary (possibly non-differentiable/junk) `f` is still `dbar`-trivial there. -/
theorem wirtingerDbar_mul_eq_zero_of_notMem_tsupport (hz : z ∉ tsupport g) :
    wirtingerDbar (fun w => g w * f w) z = 0 := by
  have hg0 : g =ᶠ[nhds z] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hz
  have hprod : (fun w => g w * f w) =ᶠ[nhds z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hg0] with w hw
    simp [hw]
  rw [wirtingerDbar_congr_nhds _ _ z hprod]
  simp [wirtingerDbar]

/-! ## The `ContDiffOn` → `ContDiff` gluing lemma -/

/-- Upgrade a `ContDiffOn` function with compact support strictly inside an open set to a
globally `ContDiff` function (two-piece gluing: locally `g` on `U`, locally `0` on
`(tsupport g)ᶜ`, these two opens cover `ℂ`). -/
theorem ContDiffOn.contDiff_of_hasCompactSupport {U : Set ℂ} {n : ℕ∞} (hU : IsOpen U)
    (hg : ContDiffOn ℝ n g U) (_hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U) :
    ContDiff ℝ n g := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hxU : x ∈ U
  · exact hg.contDiffAt (hU.mem_nhds hxU)
  · have hxt : x ∉ tsupport g := fun h => hxU (hsub h)
    have hg0 : g =ᶠ[nhds x] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hxt
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hg0

/-- Continuity of `wirtingerDbar g` from `ContDiff ℝ 1 g` alone (Dbar's own
`continuous_wirtingerDbar` needs `ContDiff ℝ ∞`; this unit only ever has regularity `1` in hand,
per D1 — R1 in the design's risk list, resolved by the same two-line argument one level down). -/
theorem continuous_wirtingerDbar_of_contDiff_one (hg : ContDiff ℝ 1 g) :
    Continuous (wirtingerDbar g) := by
  have hfc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have h1 : Continuous (fun z => fderiv ℝ g z 1) := hfc.clm_apply continuous_const
  have hI : Continuous (fun z => fderiv ℝ g z Complex.I) := hfc.clm_apply continuous_const
  exact (h1.add (continuous_const.mul hI)).div_const 2

/-- `tsupport (wirtingerDbar g) ⊆ tsupport g` (a sharper, closure-level companion to Dbar's own
`hasCompactSupport_wirtingerDbar`, which only extracts compactness). -/
theorem tsupport_wirtingerDbar_subset : tsupport (wirtingerDbar g) ⊆ tsupport g := by
  have hsupp : Function.support (wirtingerDbar g) ⊆ tsupport g := by
    intro x hx
    by_contra hxt
    exact hx (by simp [wirtingerDbar, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt])
  calc tsupport (wirtingerDbar g) = closure (Function.support (wirtingerDbar g)) := rfl
    _ ⊆ closure (tsupport g) := closure_mono hsupp
    _ = tsupport g := (isClosed_tsupport g).closure_eq

/-! ## The rectangle ↔ iterated-real-integral bridge -/

/-- Internal building block (no support/vanishing hypothesis): the `ℂ`-set integral over a closed
rectangle equals the iterated real interval integral, given integrability on the rectangle and
`z.re ≤ w.re`, `z.im ≤ w.im`. Reused both for the exported compact-support corollary below and by
`AnnulusResidue.lean`'s Step 3. -/
theorem setIntegral_reProdIm_eq_intervalIntegral {F : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im)
    (hF : IntegrableOn F (Complex.reProdIm (Set.Icc z.re w.re) (Set.Icc z.im w.im))) :
    ∫ ζ in Complex.reProdIm (Set.Icc z.re w.re) (Set.Icc z.im w.im), F ζ
      = ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, F (x + y * I) := by
  set s := Set.Icc z.re w.re with hs_def
  set t := Set.Icc z.im w.im with ht_def
  have hset : (Complex.reProdIm s t : Set ℂ) = Complex.measurableEquivRealProd ⁻¹' (s ×ˢ t) := by
    ext ζ
    simp [Complex.reProdIm, Complex.measurableEquivRealProd_apply]
  rw [hset] at hF
  have hFeq : F = (fun p : ℝ × ℝ => F (p.1 + p.2 * I)) ∘ Complex.measurableEquivRealProd := by
    funext ζ
    simp [Complex.measurableEquivRealProd_apply]
  have hF' : IntegrableOn (fun p : ℝ × ℝ => F (p.1 + p.2 * I)) (s ×ˢ t) volume := by
    rw [← Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      (MeasurableEquiv.measurableEmbedding _), ← hFeq]
    exact hF
  calc ∫ ζ in Complex.reProdIm s t, F ζ
      = ∫ ζ in Complex.measurableEquivRealProd ⁻¹' (s ×ˢ t), F ζ := by rw [hset]
    _ = ∫ ζ in Complex.measurableEquivRealProd ⁻¹' (s ×ˢ t),
          (fun p : ℝ × ℝ => F (p.1 + p.2 * I)) (Complex.measurableEquivRealProd ζ) := by
        apply MeasureTheory.setIntegral_congr_fun
          (MeasurableSet.preimage (measurableSet_Icc.prod measurableSet_Icc)
            Complex.measurableEquivRealProd.measurable)
        intro ζ _
        simp [Complex.measurableEquivRealProd_apply]
    _ = ∫ p in s ×ˢ t, F (p.1 + p.2 * I) :=
        Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
          (MeasurableEquiv.measurableEmbedding _) (fun p : ℝ × ℝ => F (p.1 + p.2 * I)) (s ×ˢ t)
    _ = ∫ x in s, ∫ y in t, F (x + y * I) := MeasureTheory.setIntegral_prod _ hF'
    _ = ∫ x in s, ∫ y : ℝ in z.im..w.im, F (x + y * I) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro x _
        dsimp only
        rw [intervalIntegral.integral_of_le him]
        exact setIntegral_congr_set Ioc_ae_eq_Icc.symm
    _ = ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, F (x + y * I) := by
        rw [intervalIntegral.integral_of_le hre]
        exact setIntegral_congr_set Ioc_ae_eq_Icc.symm

/-- The `ℂ`-rectangle ↔ iterated-real-integral bridge: a function vanishing off an open rectangle
has the same global `ℂ`-integral as its iterated real double integral over (any closed rectangle
containing) that open rectangle. -/
theorem integral_eq_intervalIntegral_of_tsupport_subset_reProdIm {F : ℂ → ℂ} {z w : ℂ}
    (hFc : Continuous F)
    (hsub : tsupport F ⊆ Complex.reProdIm (Set.Ioo z.re w.re) (Set.Ioo z.im w.im)) :
    ∫ ζ : ℂ, F ζ = ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, F (x + y * I) := by
  by_cases hcase : z.re < w.re ∧ z.im < w.im
  · obtain ⟨hre, him⟩ := hcase
    have hsub' : tsupport F ⊆ Complex.reProdIm (Set.Icc z.re w.re) (Set.Icc z.im w.im) :=
      hsub.trans (Complex.reProdIm_subset_iff.mpr
        (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self))
    have hvanish : ∀ ζ, ζ ∉ Complex.reProdIm (Set.Icc z.re w.re) (Set.Icc z.im w.im) → F ζ = 0 :=
      fun ζ hζ => image_eq_zero_of_notMem_tsupport (fun h => hζ (hsub' h))
    have hcompact : IsCompact (Complex.reProdIm (Set.Icc z.re w.re) (Set.Icc z.im w.im)) :=
      IsCompact.reProdIm isCompact_Icc isCompact_Icc
    have hF : IntegrableOn F (Complex.reProdIm (Set.Icc z.re w.re) (Set.Icc z.im w.im)) :=
      hFc.continuousOn.integrableOn_compact hcompact
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hvanish]
    exact setIntegral_reProdIm_eq_intervalIntegral hre.le him.le hF
  · have hF0 : F = fun _ => (0 : ℂ) := by
      have hempty : Complex.reProdIm (Set.Ioo z.re w.re) (Set.Ioo z.im w.im) = ∅ := by
        rw [not_and_or] at hcase
        rcases hcase with h | h
        · rw [Set.Ioo_eq_empty (fun hlt => h hlt), Complex.reProdIm]; simp
        · rw [Set.Ioo_eq_empty (fun hlt => h hlt), Complex.reProdIm]; simp
      have htsupp : tsupport F = ∅ := Set.subset_empty_iff.mp (hempty ▸ hsub)
      funext ζ
      exact image_eq_zero_of_notMem_tsupport (htsupp ▸ Set.notMem_empty ζ)
    rw [hF0]
    simp

end RS
