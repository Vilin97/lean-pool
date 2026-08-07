/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Abel.Loops
import LeanPool.JacobianDiffgeo.Dbar
import LeanPool.JacobianDiffgeo.Meromorphic
import LeanPool.JacobianDiffgeo.ProperDegree
import LeanPool.JacobianDiffgeo.SphereTopology

/-!
# abel-theorem: the CR-converse promotion (`docs/design/abel-theorem.md` §4.2 D2, §2.1 step 7)

Unit: abel-theorem. Namespace `RS.Abel`. Two deliverables:

* `wirtingerDbar_exp_neg_mul_eq_zero` — the `dbarF = 0` computation underlying the meromorphic
  promotion: if `u`'s Wirtinger `dbar`-derivative matches `f`'s own logarithmic `dbar`-derivative
  (`dbaru = dbarf / f`) at a point where `f ≠ 0`, then `F := exp(-u) * f` has `dbarF = 0`
  there — a direct
  Leibniz/chain-rule computation (`wirtingerDbar_mul` + the holomorphic-outer chain rule for
  `Complex.exp`, via mathlib's `HasDerivAt.comp_hasFDerivAt`).
* `genus_eq_zero_of_exists_simple_pole_zero` — Forster's necessity shortcut (§2.2): a meromorphic
  function with exactly one simple pole and one simple zero (elsewhere holomorphic and
  non-vanishing) forces `genus X = 0`, composing two ALREADY-BUILT, fully-proved facts (no
  admitted goals) — `RS.homeoSphere_of_exists_simple_pole` (`proper-map-degree`) and
  `RS.SphereTopology.genus_eq_zero_of_homeo_sphere` (`sphere-topology`). `form-trace-tower` is not
  imported anywhere in this unit, matching the design's finding (§2.2).
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS.Abel

/-! ## D2: the `dbar`-product-rule identity (mathlib-only, pure `ℂ → ℂ`) -/

/-- The holomorphic-outer chain rule for `wirtingerDbar`: `Complex.exp` composed with an
arbitrary (only `ℝ`-differentiable) inner function `v` satisfies
`dbar(exp ∘ v) = exp(v z) * dbarv`. -/
private theorem wirtingerDbar_cexp_comp {v : ℂ → ℂ} {z : ℂ} (hv : DifferentiableAt ℝ v z) :
    wirtingerDbar (fun w => Complex.exp (v w)) z = Complex.exp (v z) * wirtingerDbar v z := by
  have hFD : HasFDerivAt v (fderiv ℝ v z) z := hv.hasFDerivAt
  have hexpD : HasFDerivAt (Complex.exp ∘ v) (Complex.exp (v z) • fderiv ℝ v z) z :=
    (Complex.hasDerivAt_exp (v z)).comp_hasFDerivAt z hFD
  have hfderiv_eq : fderiv ℝ (fun w => Complex.exp (v w)) z
      = Complex.exp (v z) • fderiv ℝ v z := hexpD.fderiv
  change (fderiv ℝ (fun w => Complex.exp (v w)) z 1
    + Complex.I * fderiv ℝ (fun w => Complex.exp (v w)) z Complex.I) / 2 = _
  rw [hfderiv_eq]
  simp only [smul_apply, smul_eq_mul]
  show (Complex.exp (v z) * fderiv ℝ v z 1
      + Complex.I * (Complex.exp (v z) * fderiv ℝ v z Complex.I)) / 2
    = Complex.exp (v z) * wirtingerDbar v z
  change _ = Complex.exp (v z) * ((fderiv ℝ v z 1 + Complex.I * fderiv ℝ v z Complex.I) / 2)
  ring

/-- **D2, the `dbarF = 0` computation** (§2.1 step 7): the exponential-corrected function
`F := fun w => exp(-(u w)) * f w` is genuinely `dbar`-flat wherever `u`'s `dbar`-derivative matches
`f`'s own logarithmic one. -/
theorem wirtingerDbar_exp_neg_mul_eq_zero {u f : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (hf : DifferentiableAt ℝ f z)
    (h : wirtingerDbar u z = wirtingerDbar f z / f z) (hfz : f z ≠ 0) :
    wirtingerDbar (fun w => Complex.exp (-(u w)) * f w) z = 0 := by
  have hnegu : DifferentiableAt ℝ (fun w => -(u w)) z := hu.neg
  have hwirt_exp : wirtingerDbar (fun w => Complex.exp (-(u w))) z
      = Complex.exp (-(u z)) * wirtingerDbar (fun w => -(u w)) z :=
    wirtingerDbar_cexp_comp hnegu
  have hnegu_eq : (fun w => -(u w)) = -u := rfl
  have hwirt_negu : wirtingerDbar (fun w => -(u w)) z = -(wirtingerDbar u z) := by
    rw [hnegu_eq]; exact wirtingerDbar_neg u z
  rw [hwirt_negu] at hwirt_exp
  have hexpu_diff : DifferentiableAt ℝ (fun w => Complex.exp (-(u w))) z := by
    have hFD : HasFDerivAt (fun w => -(u w)) (fderiv ℝ (fun w => -(u w)) z) z :=
      hnegu.hasFDerivAt
    have hexpD : HasFDerivAt (Complex.exp ∘ (fun w => -(u w)))
        (Complex.exp (-(u z)) • fderiv ℝ (fun w => -(u w)) z) z :=
      (Complex.hasDerivAt_exp (-(u z))).comp_hasFDerivAt z hFD
    exact hexpD.differentiableAt
  rw [wirtingerDbar_mul hexpu_diff hf, hwirt_exp, h]
  field_simp
  ring

/-! ## §2.2: Forster's necessity shortcut (via ALREADY-BUILT `proper-map-degree`/`sphere-topology`)
-/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The necessity shortcut this unit actually needs** (§2.2): NOT Forster's general
`Trace(ω)`-on-`ℙ¹` necessity construction — just the "one simple pole" specialization, already
fully discharged by two other units. `form-trace-tower` is not imported anywhere here. -/
theorem genus_eq_zero_of_exists_simple_pole (F : RS.Mero X) (Q : X) (hpole : F.ord Q = -1)
    (hreg : ∀ x, x ≠ Q → 0 ≤ F.ord x) : genus X = 0 :=
  RS.SphereTopology.genus_eq_zero_of_homeo_sphere
      (RS.homeoSphere_of_exists_simple_pole F Q hpole hreg)

end RS.Abel

end
