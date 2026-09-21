/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.DivergenceCoordinates
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-! # Actual manifold integral curves in a fixed tangent chart

The derivative conversion uses the same manifold chain rule as Mathlib's
`IsMIntegralCurveAt.eventually_hasDerivAt`, allowing an arbitrary fixed chart.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The coordinate representation of an actual integral curve solves the
coordinate vector field's ODE in any chart containing the evaluation point. -/
theorem hasDerivAt_chart_integralCurve {X : Π y : M, TangentSpace I y}
    {γ : ℝ → M} {t : ℝ} (hγ : IsMIntegralCurveAt γ X t)
    (c : M) (hx : γ t ∈ (chartAt H c).source) :
    HasDerivAt ((extChartAt I c) ∘ γ)
      (coordinateVectorField (I := I) c X (extChartAt I c (γ t))) t := by
  have he : (extChartAt I c).symm (extChartAt I c (γ t)) = γ t :=
    (extChartAt I c).left_inv (by simpa using hx)
  simp only [coordinateVectorField]
  rw [he]
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  have hc := (mdifferentiableAt_extChartAt (I := I) hx).hasMFDerivAt
  apply (hc.comp t hγ.hasMFDerivAt).congr_mfderiv
  ext
  simp only [TangentBundle.continuousLinearMapAt_trivializationAt hx]
  exact (mfderiv I 𝓘(ℝ, E) (extChartAt I c) (γ t)).map_smul (1 : ℝ) (X (γ t))

/-- A manifold family expressed in fixed input and output charts. -/
def chartFlow (η : M × ℝ → M) (c₀ c₁ : M) (z : E × ℝ) : E :=
  extChartAt I c₁ (η ((extChartAt I c₀).symm z.1, z.2))

/-- The natural coordinate domain enforces all three chart and family conditions. -/
def chartFlowDomain (η : M × ℝ → M) (S : Set (M × ℝ)) (c₀ c₁ : M) : Set (E × ℝ) :=
  {z | (z.1 ∈ (extChartAt I c₀).target ∧
    ((extChartAt I c₀).symm z.1, z.2) ∈ S) ∧
    η ((extChartAt I c₀).symm z.1, z.2) ∈ (chartAt H c₁).source}

omit [IsManifold I ∞ M] in
/-- The natural coordinate domain of a continuous family on an open manifold
domain is itself open. -/
theorem isOpen_chartFlowDomain [I.Boundaryless] {η : M × ℝ → M}
    {S : Set (M × ℝ)} (hS : IsOpen S) (hη : ContinuousOn η S) (c₀ c₁ : M) :
    IsOpen (chartFlowDomain (I := I) η S c₀ c₁) := by
  let D : Set (E × ℝ) := Prod.fst ⁻¹' (extChartAt I c₀).target
  let g : E × ℝ → M × ℝ := fun z => ((extChartAt I c₀).symm z.1, z.2)
  have hD : IsOpen D := (isOpen_extChartAt_target c₀).preimage continuous_fst
  have hg : ContinuousOn g D :=
    ((continuousOn_extChartAt_symm (I := I) c₀).comp continuous_fst.continuousOn
      (fun _ hz => hz)).prodMk continuous_snd.continuousOn
  have hDS : IsOpen (D ∩ g ⁻¹' S) := hg.isOpen_inter_preimage hD hS
  have hh : ContinuousOn (η ∘ g) (D ∩ g ⁻¹' S) :=
    hη.comp (hg.mono inter_subset_left) (fun _ hz => hz.2)
  exact hh.isOpen_inter_preimage hDS (chartAt H c₁).open_source

/-- Joint manifold smoothness transfers to the actual coordinate family on
any domain where its input, manifold-family, and output chart conditions hold. -/
theorem contDiffOn_chartFlow [I.Boundaryless] {η : M × ℝ → M}
    {S : Set (M × ℝ)} {n : ℕ}
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I n η S) (c₀ c₁ : M)
    {W : Set (E × ℝ)}
    (hin : ∀ z ∈ W, z.1 ∈ (extChartAt I c₀).target)
    (hdom : ∀ z ∈ W, ((extChartAt I c₀).symm z.1, z.2) ∈ S)
    (hout : ∀ z ∈ W, η ((extChartAt I c₀).symm z.1, z.2) ∈ (chartAt H c₁).source) :
    ContDiffOn ℝ n (chartFlow (I := I) η c₀ c₁) W := by
  have hi : ContMDiffOn 𝓘(ℝ, E × ℝ) I n
      (fun z : E × ℝ => (extChartAt I c₀).symm z.1) W :=
    (contMDiffOn_extChartAt_symm (I := I) (n := n) c₀).comp
      contDiff_fst.contMDiff.contMDiffOn hin
  have hh := hη.comp (hi.prodMk contDiff_snd.contMDiff.contMDiffOn) hdom
  have ho := (contMDiffOn_extChartAt (I := I) (n := n) (x := c₁)).comp hh hout
  exact ho.contDiffOn

/-- The coordinate family retains the manifold family's finite-order smoothness
on its natural domain, without separately supplied chart-validity hypotheses. -/
theorem contDiffOn_chartFlow_domain [I.Boundaryless] {η : M × ℝ → M}
    {S : Set (M × ℝ)} {n : ℕ}
    (hη : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I n η S) (c₀ c₁ : M) :
    ContDiffOn ℝ n (chartFlow (I := I) η c₀ c₁)
      (chartFlowDomain (I := I) η S c₀ c₁) :=
  contDiffOn_chartFlow hη c₀ c₁ (fun _ hz => hz.1.1)
    (fun _ hz => hz.1.2) (fun _ hz => hz.2)

/-- The coordinate family inherits its time equation from actual manifold
integral curves; the source coordinate is held fixed when differentiating. -/
theorem hasDerivAt_chartFlow {η : M × ℝ → M} {X : Π y : M, TangentSpace I y}
    (c₀ c₁ : M) {p : E} {t : ℝ}
    (hη : IsMIntegralCurveAt (fun s => η ((extChartAt I c₀).symm p, s)) X t)
    (hout : η ((extChartAt I c₀).symm p, t) ∈ (chartAt H c₁).source) :
    HasDerivAt (fun s => chartFlow (I := I) η c₀ c₁ (p, s))
      (coordinateVectorField (I := I) c₁ X (chartFlow (I := I) η c₀ c₁ (p, t))) t := by
  exact hasDerivAt_chart_integralCurve hη c₁ hout

end LichnerowiczObata
