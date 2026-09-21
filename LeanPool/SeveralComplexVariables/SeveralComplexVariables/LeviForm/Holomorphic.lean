/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LeviForm

/-!
# The Levi form under holomorphic maps

The Levi form transforms under a holomorphic map `Φ` by the chain rule `Lev (g ∘ Φ) (a, w) = Lev
g (Φ a, Φ'(a) w)`: the second derivative of `Φ` contributes `Dg (D²Φ (w, w) + D²Φ (I • w, I •
w))`, which vanishes because the second derivative of a holomorphic map is complex bilinear.
Consequently `C²` plurisubharmonic functions compose with holomorphic maps to `C²`
plurisubharmonic functions.

References: [Fritzsche–Grauert][FritzscheGrauert2002] (2002), Chapter II, Section 2, Example 4
after the definition of the Levi form; [Hörmander][Hormander1973] (1973), Theorem 2.6.4 (smooth
case).

## Main results

* `leviForm_comp_analytic`: **Chain rule for the Levi form.** For a `C²` function `g` and a
  holomorphic map `Φ`, `Lev (g ∘ Φ) (a, w) = Lev g (Φ a, Φ'(a) w)`.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The real second derivative of a holomorphic map is complex bilinear: it changes sign when both
arguments are multiplied by `I`. -/
theorem fderiv_fderiv_smul_I_smul_I {Φ : E → F} {a : E} (hΦ : AnalyticAt ℂ Φ a) (s t : E) :
    fderiv ℝ (fderiv ℝ Φ) a (I • s) (I • t) = -fderiv ℝ (fderiv ℝ Φ) a s t := by
  have hc : ContDiffAt ℂ 2 Φ a := hΦ.contDiffAt
  have hr := hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ) (n := 2)
  have h1 : fderiv ℝ (fderiv ℝ Φ) a (I • s) (I • t) = iteratedFDeriv ℝ 2 Φ a ![I • s, I • t] := by
    rw [iteratedFDeriv_two_apply]; rfl
  have h2 : fderiv ℝ (fderiv ℝ Φ) a s t = iteratedFDeriv ℝ 2 Φ a ![s, t] := by
    rw [iteratedFDeriv_two_apply]; rfl
  have hv : (![I • s, I • t] : Fin 2 → E) = fun i => I • (![s, t] : Fin 2 → E) i := by
    funext i; fin_cases i <;> rfl
  rw [h1, h2, ← hr, hv]
  change (iteratedFDeriv ℂ 2 Φ a) (fun i => I • (![s, t] : Fin 2 → E) i) =
    -(iteratedFDeriv ℂ 2 Φ a) ![s, t]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

/-- **Chain rule for the Levi form.** For a `C²` function `g` and a holomorphic map `Φ`,
`Lev (g ∘ Φ) (a, w) = Lev g (Φ a, Φ'(a) w)`. -/
theorem leviForm_comp_analytic {g : F → ℝ} {Φ : E → F} {a : E} (hg : ContDiffAt ℝ 2 g (Φ a))
    (hΦ : AnalyticAt ℂ Φ a) (w : E) :
    leviForm (g ∘ Φ) a w = leviForm g (Φ a) (fderiv ℂ Φ a w) := by
  have hΦc : ContDiffAt ℝ 2 Φ a := (hΦ.contDiffAt (n := 2)).restrict_scalars ℝ
  -- first derivatives near `a`
  have hΦev : ∀ᶠ x in 𝓝 a, HasFDerivAt Φ (fderiv ℝ Φ x) x := by
    filter_upwards [hΦc.eventually (by simp)] with x hx
    exact (hx.differentiableAt (by norm_num)).hasFDerivAt
  have hgev : ∀ᶠ x in 𝓝 a, HasFDerivAt g (fderiv ℝ g (Φ x)) (Φ x) := by
    have hcont : ContinuousAt Φ a := hΦc.continuousAt
    filter_upwards [hcont.eventually (hg.eventually (by simp))] with x hx
    exact (hx.differentiableAt (by norm_num)).hasFDerivAt
  have hD1 : (fun x => fderiv ℝ (g ∘ Φ) x) =ᶠ[𝓝 a]
      fun x => (fderiv ℝ g (Φ x)).comp (fderiv ℝ Φ x) := by
    filter_upwards [hΦev, hgev] with x hx1 hx2
    exact (hx2.comp x hx1).fderiv
  -- second derivatives
  have hD2Φ : HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) a) a :=
    ((hΦc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD2g : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) (Φ a)) (Φ a) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hΦa : HasFDerivAt Φ (fderiv ℝ Φ a) a := hΦc.differentiableAt (by norm_num) |>.hasFDerivAt
  have hcomp : HasFDerivAt (fun x => fderiv ℝ g (Φ x))
      ((fderiv ℝ (fderiv ℝ g) (Φ a)).comp (fderiv ℝ Φ a)) a := hD2g.comp a hΦa
  have hfin := hcomp.clm_comp hD2Φ
  have hD2 : ∀ s t : E, fderiv ℝ (fderiv ℝ (g ∘ Φ)) a s t =
      fderiv ℝ g (Φ a) (fderiv ℝ (fderiv ℝ Φ) a s t) +
        fderiv ℝ (fderiv ℝ g) (Φ a) (fderiv ℝ Φ a s) (fderiv ℝ Φ a t) := by
    intro s t
    rw [hD1.fderiv_eq, hfin.fderiv]
    simp [ContinuousLinearMap.compL_apply]
  -- complex linearity of the first derivative
  have hlin : fderiv ℝ Φ a (I • w) = I • fderiv ℂ Φ a w := by
    rw [hΦ.differentiableAt.fderiv_restrictScalars (𝕜 := ℝ),
      ContinuousLinearMap.coe_restrictScalars',
      map_smul]
  have hlin' : fderiv ℝ Φ a w = fderiv ℂ Φ a w := by
    rw [hΦ.differentiableAt.fderiv_restrictScalars (𝕜 := ℝ),
      ContinuousLinearMap.coe_restrictScalars']
  rw [leviForm_eq_fderiv, leviForm_eq_fderiv, hD2, hD2, fderiv_fderiv_smul_I_smul_I hΦ, map_neg,
    hlin, hlin']
  ring

/-- `C²` plurisubharmonic functions compose with holomorphic maps. -/
theorem PlurisubharmonicOn.comp_analyticOnNhd {g : F → ℝ} {V : Set F} (hV : IsOpen V)
    (hgc : ContDiffOn ℝ 2 g V) (hg : PlurisubharmonicOn g V) {Φ : E → F} {U : Set E}
    (hU : IsOpen U) (hΦ : AnalyticOnNhd ℂ Φ U) (hmaps : MapsTo Φ U V) :
    PlurisubharmonicOn (g ∘ Φ) U := by
  have hΦc : ContDiffOn ℝ 2 Φ U := (hΦ.contDiffOn hU.uniqueDiffOn (n := 2)).restrict_scalars ℝ
  refine plurisubharmonicOn_of_leviForm_nonneg hU (hgc.comp hΦc hmaps) fun a ha w => ?_
  rw [leviForm_comp_analytic (hgc.contDiffAt (hV.mem_nhds (hmaps ha))) (hΦ a ha)]
  exact hg.leviForm_nonneg hV hgc (hmaps ha) _

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
