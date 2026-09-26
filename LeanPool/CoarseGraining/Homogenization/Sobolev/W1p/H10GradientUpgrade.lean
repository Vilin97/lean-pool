/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.H1GradientUpgrade
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.InwardMollificationLp
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.InwardMollificationWeakGradient
public import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.BasicLemmas

/-!
# Upgrading zero-trace `H¹` witnesses from finite-`p` gradients

An `H¹₀` witness whose weak gradient has finite `L^p` control belongs to
`W^{1,p}_0` on every bounded open convex domain.  The zero-trace approximation
is constructed internally by inwardly mollifying the global zero extension.
-/

@[expose] public section

namespace Homogenization

open _root_.Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace H10Function

private theorem tendsto_eLpNorm_restrict_of_tendsto_global
    {l : Filter ℕ}
    {d : ℕ} {f : ℕ → Vec d → ℝ} {p : ENNReal} {U : Set (Vec d)}
    (h : Filter.Tendsto (fun n => eLpNorm (f n) p volume) l (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (f n) p (volume.restrict U)) l (nhds 0) := by
  have hle : ∀ n,
      eLpNorm (f n) p (volume.restrict U) ≤ eLpNorm (f n) p volume := fun n =>
    eLpNorm_mono_measure (f n) Measure.restrict_le_self
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Filter.Eventually.of_forall fun _ => zero_le) (Filter.Eventually.of_forall hle)

private noncomputable def inwardApproximation
    {d : ℕ} {U : Set (Vec d)} (u : H10Function U)
    (x0 : Vec d) (r : ℝ) (n : ℕ) : Vec d → ℝ :=
  inwardMollification (unitConvexApproxKernel (d := d)) u.zeroExtension
    x0 r (unitConvexApproxScale n)

private theorem inwardApproximation_properties
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U) (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (u.inwardApproximation x0 r n) ∧
      HasCompactSupport (u.inwardApproximation x0 r n) ∧
      tsupport (u.inwardApproximation x0 r n) ⊆ U := by
  exact u.inwardMollification_unit_properties hU hball hr
    (W1pFunction.unitConvexApproxScale_pos n)

private theorem tendsto_inwardApproximation_value
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (p : FiniteLpExponent)
    (hu : MemLpOn U p.exponent u.toH1Function.toFun)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => u.inwardApproximation x0 r n x - u.toH1Function.toFun x)
        p.exponent (volume.restrict U)) Filter.atTop (nhds 0) := by
  have hu_zero : MemLp u.zeroExtension p.exponent volume :=
    u.memLp_zeroExtension hU.isOpen.measurableSet hu
  have hglobal := tendsto_eLpNorm_inwardMollification_sub_zero
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) p.one_lt.le
    p.lt_top.ne hu_zero x0 hr tendsto_unitConvexApproxScale_zero
    unitConvexApproxScale_nonneg
    (Filter.Eventually.of_forall W1pFunction.unitConvexApproxScale_pos)
  have hrestricted := tendsto_eLpNorm_restrict_of_tendsto_global (U := U) hglobal
  have heq : (fun n => eLpNorm
        (inwardMollification (unitConvexApproxKernel (d := d)) u.zeroExtension
          x0 r (unitConvexApproxScale n) - u.zeroExtension)
        p.exponent (volume.restrict U)) =ᶠ[Filter.atTop]
      (fun n => eLpNorm
        (fun x => u.inwardApproximation x0 r n x - u.toH1Function.toFun x)
        p.exponent (volume.restrict U)) := by
    filter_upwards with n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    change inwardMollification (unitConvexApproxKernel (d := d)) u.zeroExtension
      x0 r (unitConvexApproxScale n) x - u.zeroExtension x =
      u.inwardApproximation x0 r n x - u.toH1Function.toFun x
    rw [u.zeroExtension_apply_of_mem hx]
    rfl
  exact hrestricted.congr' heq

private theorem tendsto_inwardApproximation_grad
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.toH1Function.grad)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r) (i : Fin d) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x =>
          (fderiv ℝ (u.inwardApproximation x0 r n) x) (basisVec i) -
            u.toH1Function.grad x i)
        p.exponent (volume.restrict U)) Filter.atTop (nhds 0) := by
  have hgrad_zero : GradMemLpOn Set.univ p.exponent u.zeroExtensionGrad :=
    u.gradMemLp_zeroExtensionGrad hU.isOpen.measurableSet hgrad
  have hcoord : MemLp (fun x => u.zeroExtensionGrad x i) p.exponent volume := by
    have hcoord' := hgrad_zero i
    change MemLp (fun x => u.zeroExtensionGrad x i) p.exponent
      (volume.restrict Set.univ) at hcoord'
    simpa only [Measure.restrict_univ] using hcoord'
  have hglobal := tendsto_eLpNorm_one_add_mul_inwardMollification_sub_zero
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) p.one_lt.le
    p.lt_top.ne hcoord x0 hr tendsto_unitConvexApproxScale_zero
    unitConvexApproxScale_nonneg
    (Filter.Eventually.of_forall W1pFunction.unitConvexApproxScale_pos)
  have hrestricted := tendsto_eLpNorm_restrict_of_tendsto_global (U := U) hglobal
  have heq : (fun n => eLpNorm
        (fun x => (1 + unitConvexApproxScale n) *
          inwardMollification (unitConvexApproxKernel (d := d))
            (fun y => u.zeroExtensionGrad y i) x0 r (unitConvexApproxScale n) x -
          u.zeroExtensionGrad x i)
        p.exponent (volume.restrict U)) =ᶠ[Filter.atTop]
      (fun n => eLpNorm
        (fun x =>
          (fderiv ℝ (u.inwardApproximation x0 r n) x) (basisVec i) -
            u.toH1Function.grad x i)
        p.exponent (volume.restrict U)) := by
    filter_upwards with n
    apply eLpNorm_congr_ae
    have hderiv := u.ae_eq_fderiv_inwardMollification_unit_apply_basisVec
      hU.isOpen.measurableSet (x0 := x0) hr
      (W1pFunction.unitConvexApproxScale_pos n) i
    filter_upwards [hderiv.restrict, ae_restrict_mem hU.isOpen.measurableSet] with x hxderiv hxU
    simp only [inwardApproximation]
    rw [hxderiv, u.zeroExtensionGrad_apply_of_mem hxU]
    rfl
  exact hrestricted.congr' heq

private noncomputable def toW10pOfGradMemLpNonempty
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.toH1Function.grad)
    (hU_nonempty : U.Nonempty) : W10pFunction U p.exponent := by
  classical
  let x0 : Vec d := Classical.choose hU_nonempty
  have hx0 : x0 ∈ U := Classical.choose_spec hU_nonempty
  have hδ_exists := Metric.mem_nhds_iff.1 (hU.isOpen.mem_nhds hx0)
  let δ : ℝ := Classical.choose hδ_exists
  have hδ_spec := Classical.choose_spec hδ_exists
  have hδpos : 0 < δ := hδ_spec.1
  have hδsub : Metric.ball x0 δ ⊆ U := hδ_spec.2
  let r : ℝ := δ / 2
  have hr : 0 < r := by positivity
  have hball : Metric.closedBall x0 r ⊆ U := by
    intro y hy
    apply hδsub
    have hy' : dist y x0 ≤ r := by simpa [Metric.mem_closedBall] using hy
    have hr_lt : r < δ := by dsimp only [r]; linarith
    simpa [Metric.mem_ball] using lt_of_le_of_lt hy' hr_lt
  let v : W1pFunction U p.exponent :=
    u.toH1Function.toW1pOfGradMemLp hU p hgrad
  exact
    { toW1pFunction := v
      approx := u.inwardApproximation x0 r
      approx_smooth := fun n => (u.inwardApproximation_properties hU hball hr n).1
      approx_hasCompactSupport := fun n =>
        (u.inwardApproximation_properties hU hball hr n).2.1
      approx_support_subset := fun n =>
        (u.inwardApproximation_properties hU hball hr n).2.2
      tendsto_approx := by
        simpa only [v, H1Function.toW1pOfGradMemLp_toFun] using
          u.tendsto_inwardApproximation_value hU p
            (u.toH1Function.toW1pOfGradMemLp hU p hgrad).memLp
            x0 hr
      tendsto_approx_grad := by
        intro i
        simpa only [v, H1Function.toW1pOfGradMemLp_grad] using
          u.tendsto_inwardApproximation_grad hU p hgrad x0 hr i }

private noncomputable def toW10pOfGradMemLpEmpty
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.toH1Function.grad)
    (hU_empty : U = ∅) : W10pFunction U p.exponent := by
  let v : W1pFunction U p.exponent :=
    u.toH1Function.toW1pOfGradMemLp hU p hgrad
  exact
    { toW1pFunction := v
      approx := fun _ _ => 0
      approx_smooth := fun _ => contDiff_const
      approx_hasCompactSupport := fun _ =>
        (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
      approx_support_subset := by
        intro n
        have hz : tsupport (fun _ : Vec d => (0 : ℝ)) = ∅ := tsupport_zero
        rw [hz]
        exact Set.empty_subset U
      tendsto_approx := by
        simp only [hU_empty, Measure.restrict_empty, eLpNorm_measure_zero]
        exact tendsto_const_nhds
      tendsto_approx_grad := by
        intro i
        simp only [hU_empty, Measure.restrict_empty, eLpNorm_measure_zero]
        exact tendsto_const_nhds }

/-- Upgrade an `H¹₀` witness on a bounded open convex domain to `W^{1,p}_0`
when its weak-gradient coordinates have finite `L^p` control.  Both the
function and weak-gradient representatives are preserved exactly. -/
noncomputable def toW10pOfGradMemLp
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.toH1Function.grad) :
    W10pFunction U p.exponent := by
  by_cases hU_nonempty : U.Nonempty
  · exact u.toW10pOfGradMemLpNonempty hU p hgrad hU_nonempty
  · exact u.toW10pOfGradMemLpEmpty hU p hgrad
      (Set.not_nonempty_iff_eq_empty.mp hU_nonempty)

@[simp] theorem toW10pOfGradMemLp_toFun
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.toH1Function.grad) :
    (u.toW10pOfGradMemLp hU p hgrad).toW1pFunction.toFun =
      u.toH1Function.toFun := by
  rw [toW10pOfGradMemLp]
  split <;> rfl

@[simp] theorem toW10pOfGradMemLp_grad
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (p : FiniteLpExponent)
    (hgrad : GradMemLpOn U p.exponent u.toH1Function.grad) :
    (u.toW10pOfGradMemLp hU p hgrad).toW1pFunction.grad =
      u.toH1Function.grad := by
  rw [toW10pOfGradMemLp]
  split <;> rfl

end H10Function

end

end Homogenization
