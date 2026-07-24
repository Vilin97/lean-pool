/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadialGeometry

/-!
# Weak Stationarity
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The smooth domain-variation stationarity integrand
`|∇u|² div X - 2 ∑ᵢⱼ <∂ᵢu, ∂ⱼu> ∂ᵢXⱼ`. -/
def stationarityIntegrand {n m : ℕ}
    (u : Domain n → Target m) (X : Domain n → Domain n) (x : Domain n) : ℝ :=
  energyDensity u x * divergence X x -
    2 * ∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (partialDerivative u i x) (partialDerivative u j x) *
        vectorFieldPartial X i j x

/-- Smooth analogue of stationarity on an open set `Ω`.

This is the direct Lean translation of the weak identity in the manuscript, with `fderiv`
standing in for the weak derivative. -/
def SmoothStationaryIn {n m : ℕ} (u : Domain n → Target m) (Ω : Set (Domain n)) : Prop :=
  ∀ X : Domain n → Domain n,
    ContDiff ℝ 1 X →
      HasCompactSupport X →
        tsupport X ⊆ Ω →
          (∫ x in Ω, stationarityIntegrand u X x) = 0

/-- Stationarity integrand written directly in terms of an arbitrary gradient
field `Du`.  This is the expression used for `W^{1,2}_{loc}` maps. -/
def weakStationarityIntegrand {n m : ℕ}
    (Du : Domain n → Gradient n m) (X : Domain n → Domain n) (x : Domain n) : ℝ :=
  weakEnergyDensity Du x * divergence X x -
    2 * ∑ i : Fin n, ∑ j : Fin n,
      inner ℝ (Du x i) (Du x j) * vectorFieldPartial X i j x

/-- The stationarity integrand vanishes outside the topological support of the
test vector field.  Outside `tsupport X`, both `X` and its derivative are
locally zero. -/
theorem weakStationarityIntegrand_eq_zero_of_notMem_tsupport {n m : ℕ}
    (Du : Domain n → Gradient n m) {X : Domain n → Domain n} {x : Domain n}
    (hx : x ∉ tsupport X) :
    weakStationarityIntegrand Du X x = 0 := by
  have hf : fderiv ℝ X x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
  simp [weakStationarityIntegrand, divergence, vectorFieldPartial,
    partialDerivative, hf]

/-- Weak stationarity in the domain-variation sense, stated in terms of the
weak gradient field `Du`. -/
def WeakStationaryIn {n m : ℕ}
    (Du : Domain n → Gradient n m) (Ω : Set (Domain n)) : Prop :=
  ∀ X : Domain n → Domain n,
    ContDiff ℝ 1 X →
      HasCompactSupport X →
        tsupport X ⊆ Ω →
          (∫ x in Ω, weakStationarityIntegrand Du X x) = 0

/-- Weak stationarity localizes to smaller domains.  The only measure-theoretic
input needed here is measurability of the larger integration domain. -/
theorem weakStationaryIn_of_subset {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω Ω' : Set (Domain n)}
    (hstationary : WeakStationaryIn Du Ω)
    (hΩ_meas : MeasurableSet Ω)
    (hΩ'_subset : Ω' ⊆ Ω) :
    WeakStationaryIn Du Ω' := by
  intro X hXdiff hXcompact hXsupport
  have hzero_Ω :
      (∫ x in Ω, weakStationarityIntegrand Du X x) = 0 :=
    hstationary X hXdiff hXcompact (hXsupport.trans hΩ'_subset)
  have hvanish :
      ∀ x ∈ Ω \ Ω', weakStationarityIntegrand Du X x = 0 := by
    intro x hx
    have hx_not_support : x ∉ tsupport X := by
      intro hx_support
      exact hx.2 (hXsupport hx_support)
    exact weakStationarityIntegrand_eq_zero_of_notMem_tsupport Du hx_not_support
  have heq :
      (∫ x in Ω, weakStationarityIntegrand Du X x)
        =
      (∫ x in Ω', weakStationarityIntegrand Du X x) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (μ := volume) hΩ_meas hΩ'_subset hvanish
  rwa [heq] at hzero_Ω

/-- Local integrability of a scalar function on compact subsets of `Ω`. -/
def LocallyIntegrableScalarIn {n : ℕ}
    (f : Domain n → ℝ) (Ω : Set (Domain n)) : Prop :=
  ∀ K : Set (Domain n), IsCompact K → K ⊆ Ω → IntegrableOn f K volume

/-- The `L²_loc` requirement for the map itself, stated as local integrability
of `|u|²`. -/
def MapLocallyL2In {n m : ℕ}
    (u : Domain n → Target m) (Ω : Set (Domain n)) : Prop :=
  LocallyIntegrableScalarIn (fun x => ‖u x‖ ^ 2) Ω

/-- The `L²_loc` requirement for a gradient field, stated as local integrability
of its Hilbert-Schmidt energy. -/
def GradientLocallyL2In {n m : ℕ}
    (Du : Domain n → Gradient n m) (Ω : Set (Domain n)) : Prop :=
  LocallyIntegrableScalarIn (fun x => weakEnergyDensity Du x) Ω

/-- The chosen weak gradient is a.e. strongly measurable on the domain.  This is
kept separate from local `L²` control: integrability of the scalar energy
density alone does not imply measurability of the full gradient field. -/
def GradientAEStronglyMeasurableIn {n m : ℕ}
    (Du : Domain n → Gradient n m) (Ω : Set (Domain n)) : Prop :=
  AEStronglyMeasurable Du (volume.restrict Ω)

/-- Local `L²` control of the weak gradient gives integrability of the energy on
any compact subset of the domain. -/
theorem gradientLocallyL2In_integrableOn_compact {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω K : Set (Domain n)}
    (hgrad : GradientLocallyL2In Du Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) K volume :=
  hgrad K hK hKΩ

/-- Local `L²` control of the weak gradient gives integrability of the energy on
closed balls contained in the domain. -/
theorem gradientLocallyL2In_integrableOn_closedBall {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {a : Domain n} {r : ℝ}
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall a r ⊆ Ω) :
    IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
      (Metric.closedBall a r) volume := by
  exact gradientLocallyL2In_integrableOn_compact
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    hgrad (isCompact_closedBall a r) hclosedBall_subset

/-- Local `L²` control of the weak gradient gives integrability of the energy on
open balls whose closed ball is contained in the domain. -/
theorem gradientLocallyL2In_integrableOn_ball {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {a : Domain n} {r : ℝ}
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall a r ⊆ Ω) :
    IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
      (Metric.ball a r) volume := by
  exact (gradientLocallyL2In_integrableOn_closedBall
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    hgrad hclosedBall_subset).mono_set Metric.ball_subset_closedBall

/-- Weak coordinate-gradient relation, using compactly supported `C¹` test maps.

For each coordinate direction `i`, the `i`-th component of `Du` is the weak
derivative of `u` if integration by parts holds against every compactly
supported target-valued test map. -/
def HasWeakGradientIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop :=
  ∀ i : Fin n, ∀ ψ : Domain n → Target m,
    ContDiff ℝ 1 ψ →
      HasCompactSupport ψ →
        tsupport ψ ⊆ Ω →
          (∫ x in Ω, inner ℝ (u x) (partialDerivative ψ i x))
            =
          -∫ x in Ω, inner ℝ (Du x i) (ψ x)

/-- A concrete `W^{1,2}_{loc}` interface for maps with a chosen weak gradient. -/
def W12LocIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop :=
  MapLocallyL2In u Ω ∧
    GradientAEStronglyMeasurableIn Du Ω ∧
      GradientLocallyL2In Du Ω ∧
        HasWeakGradientIn u Du Ω

/-- A weak stationary map: `u ∈ W^{1,2}_{loc}` with weak gradient `Du`, and the
domain-variation stationarity identity holds in terms of `Du`. -/
def WeakStationaryMapIn {n m : ℕ}
    (u : Domain n → Target m) (Du : Domain n → Gradient n m)
    (Ω : Set (Domain n)) : Prop :=
  W12LocIn u Du Ω ∧ WeakStationaryIn Du Ω

theorem W12LocIn.map_locallyL2 {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (h : W12LocIn u Du Ω) :
    MapLocallyL2In u Ω :=
  h.1

theorem W12LocIn.gradient_aestronglyMeasurable {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (h : W12LocIn u Du Ω) :
    GradientAEStronglyMeasurableIn Du Ω :=
  h.2.1

theorem W12LocIn.gradient_locallyL2 {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (h : W12LocIn u Du Ω) :
    GradientLocallyL2In Du Ω :=
  h.2.2.1

theorem W12LocIn.hasWeakGradient {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (h : W12LocIn u Du Ω) :
    HasWeakGradientIn u Du Ω :=
  h.2.2.2

/-- A measurable weak gradient gives a measurable radial derivative.  The proof
uses only measurable algebra, since the factor `|x-a|⁻¹` is not continuous at
`a`. -/
theorem weakRadialDerivative_aestronglyMeasurable {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} (a : Domain n)
    (hDu : AEStronglyMeasurable Du (volume.restrict Ω)) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialDerivative Du a x)
      (volume.restrict Ω) := by
  let μ : Measure (Domain n) := volume.restrict Ω
  have hshift : AEStronglyMeasurable (fun x : Domain n => x - a) μ :=
    (continuous_id.sub continuous_const).aestronglyMeasurable
  have hscale : AEStronglyMeasurable (fun x : Domain n => (‖x - a‖)⁻¹) μ := by
    exact hshift.norm.aemeasurable.inv.aestronglyMeasurable
  have hsum :
      AEStronglyMeasurable
        (fun x : Domain n => ∑ i : Fin n, (x - a) i • Du x i) μ := by
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => by
      have hcoord : AEStronglyMeasurable (fun x : Domain n => (x - a) i) μ :=
        (PiLp.continuous_apply
          (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n => ℝ) i).comp_aestronglyMeasurable hshift
      have hDui : AEStronglyMeasurable (fun x : Domain n => Du x i) μ :=
        (continuous_apply i).comp_aestronglyMeasurable hDu
      exact hcoord.smul hDui)
  exact hscale.smul hsum

/-- A measurable weak gradient gives a measurable radial-energy density. -/
theorem weakRadialEnergyDensity_aestronglyMeasurable {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} (a : Domain n)
    (hDu : AEStronglyMeasurable Du (volume.restrict Ω)) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialEnergyDensity Du a x)
      (volume.restrict Ω) := by
  exact (weakRadialDerivative_aestronglyMeasurable
      (n := n) (m := m) (Du := Du) (Ω := Ω) a hDu).norm.pow 2

/-- On a ball, radial-energy measurability follows from gradient measurability
on any containing closed ball/domain. -/
theorem weakRadialEnergyDensity_aestronglyMeasurable_on_ball_of_gradient {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {a : Domain n} {r : ℝ}
    (hDu : GradientAEStronglyMeasurableIn Du Ω)
    (hclosedBall_subset : Metric.closedBall a r ⊆ Ω) :
    AEStronglyMeasurable (fun x : Domain n => weakRadialEnergyDensity Du a x)
      (volume.restrict (Metric.ball a r)) := by
  exact weakRadialEnergyDensity_aestronglyMeasurable
    (n := n) (m := m) (Du := Du) (Ω := Metric.ball a r) a
    (hDu.mono_set (Subset.trans Metric.ball_subset_closedBall hclosedBall_subset))

/-- Pointwise simplification of the weak stationarity integrand for the radial
test field `X(x)=φ(|x|)x`, away from the origin. -/
theorem weakStationarityIntegrand_radialVectorField {n m : ℕ}
    (Du : Domain n → Gradient n m) {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) :
    ∀ x : Domain n, x ≠ 0 →
      weakStationarityIntegrand Du (radialVectorField phi) x =
        (((n : ℝ) - 2) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖) *
            weakEnergyDensity Du x
          - 2 * (‖x‖ * deriv phi ‖x‖ * weakRadialEnergyDensity Du 0 x) := by
  intro x hx
  have hdiv := radialVectorFieldDivergenceFormula hphi x hx
  have hstress := weakRadialStressContractionFormula Du hphi x hx
  unfold weakStationarityIntegrand
  rw [hdiv, hstress]
  ring

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps
