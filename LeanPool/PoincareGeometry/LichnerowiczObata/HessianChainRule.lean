/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.EikonalConnection

/-! # Scalar chain rule for the covariant Hessian -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Differentiate the scalar gradient chain rule using the actual connection's
Leibniz rule. Only local C2 regularity of the inner function is needed. -/
theorem cov_gradient_scalar_comp
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {r : M → ℝ} {x : M} (hr : ContMDiffAt I 𝓘(ℝ, ℝ) 2 r x)
    {g dg : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hdg : ∀ t, HasDerivAt g (dg t) t) {c : ℝ}
    (hddg : HasDerivAt dg c (r x)) (v : TangentSpace I x) :
    cov (gradient (I := I) (g ∘ r)) x v =
      dg (r x) • cov (gradient (I := I) r) x v +
        (c * mvfderiv I r x v) • gradient (I := I) r x := by
  have hrn : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) r y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hr).mono
      (fun y hy => hy.mdifferentiableAt (by simp))
  have he : ∀ᶠ y in 𝓝 x,
      gradient (I := I) (g ∘ r) y = (dg ∘ r) y • gradient (I := I) r y := by
    filter_upwards [hrn] with y hy
    exact gradient_comp_hasDerivAt hy (hdg (r y))
  have hrd := hr.mdifferentiableAt (by norm_num)
  have hcd : MDifferentiableAt I 𝓘(ℝ, ℝ) (dg ∘ r) x :=
    hddg.differentiableAt.mdifferentiableAt.comp x hrd
  have hgr := mdifferentiableAt_gradient hr
  have hgrc := mdifferentiableAt_gradient (hg.contDiffAt.comp_contMDiffAt hr)
  have hcov := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hgrc (hcd.smul_section hgr) (by simp) he
  rw [hcov, cov.isCovariantDerivativeOnUniv.leibniz hgr hcd]
  have hd : mvfderiv I (dg ∘ r) x v = c * mvfderiv I r x v := by
    have hm := mvfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I) x
      hddg.differentiableAt.mdifferentiableAt hrd v
    simp only [mvfderiv, mfderiv_eq_fderiv, hddg.hasFDerivAt.fderiv] at hm
    change mvfderiv I (dg ∘ r) x v = mvfderiv I r x v * c at hm
    simpa only [mul_comm] using hm
  change dg (r x) • cov (gradient (I := I) r) x v +
    mvfderiv I (dg ∘ r) x v • gradient (I := I) r x = _
  rw [hd]

end LichnerowiczObata
