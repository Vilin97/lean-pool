/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothGraph

/-!
# Completed two-component graph for cube Euclidean fractional Sobolev tests

The approved inhomogeneous `W^(s,p)` power norm is realized as the ambient
`L^p` norm of the graph containing a scale-weighted field component and its
Gagliardo kernel.  This file only introduces that ambient space, its smooth
graph, and the closure of the graph; it makes no claim about a completed dual
pairing.
-/

namespace Homogenization

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private instance instCubeEuclideanWspGraphFactOneLe (p : FiniteLpExponent) :
    Fact (1 ≤ p.exponent) :=
  ⟨p.one_lt.le⟩

/-- The two heterogeneous `L^p` components of the fractional-Sobolev graph. -/
noncomputable abbrev CubeEuclideanWspGraphComponent {d : ℕ} (Q : TriadicCube d)
    (p : FiniteLpExponent) : Bool → Type _
  | false => Lp (HilbertVec d) p.exponent (normalizedCubeMeasure Q)
  | true => Lp (HilbertVec d) p.exponent
    (Gagliardo.gagliardoCubeMeasure Q)

private instance instCubeEuclideanWspGraphComponentNormedAddCommGroup {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) [Fact (1 ≤ p.exponent)]
    (b : Bool) : NormedAddCommGroup (CubeEuclideanWspGraphComponent Q p b) := by
  cases b <;> infer_instance

private instance instCubeEuclideanWspGraphComponentNormedSpace {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) [Fact (1 ≤ p.exponent)]
    (b : Bool) : NormedSpace ℝ (CubeEuclideanWspGraphComponent Q p b) := by
  cases b <;> infer_instance

/-- The finite two-component ambient `L^p` space for the full cube `W^(s,p)`
graph. -/
noncomputable abbrev CubeEuclideanWspGraphAmbient {d : ℕ} (Q : TriadicCube d)
    (p : FiniteLpExponent) : Type _ :=
  PiLp p.exponent (CubeEuclideanWspGraphComponent Q p)

/-- The two-component ambient graph space is complete because both of its
`L^p` components are complete. -/
noncomputable instance instCompleteSpaceCubeEuclideanWspGraphAmbient {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) :
    CompleteSpace (CubeEuclideanWspGraphAmbient Q p) := by
  let : Fact (1 ≤ p.exponent) := ⟨p.one_lt.le⟩
  let (b : Bool) : CompleteSpace (CubeEuclideanWspGraphComponent Q p b) := by
    cases b <;> infer_instance
  change CompleteSpace (PiLp p.exponent (CubeEuclideanWspGraphComponent Q p))
  exact PiLp.completeSpace _ _

/-- The real scale applied to the field component of the full `W^(s,p)` graph. -/
noncomputable def cubeEuclideanWspGraphFieldScale {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) : ℝ :=
  cubeScaleFactor Q ^ (-s.1)

namespace CubeEuclideanWspSmoothTest

private noncomputable def graphFieldComponent {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    CubeEuclideanWspGraphComponent Q p false :=
  h.toCubeEuclideanWspField.euclideanMemLp.toLp
    (fun x => HilbertVec.ofVec (h.toField x))

private noncomputable def graphKernelComponent {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    CubeEuclideanWspGraphComponent Q p true :=
  h.toCubeEuclideanWspField.euclideanMemWsp.toLp
    (cubeEuclideanWspKernel s p h.toField)

private theorem graphFieldComponent_add {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h k : CubeEuclideanWspSmoothTest Q s p) :
    graphFieldComponent (h + k) = graphFieldComponent h + graphFieldComponent k := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (h + k).toCubeEuclideanWspField.euclideanMemLp,
    MemLp.coeFn_toLp h.toCubeEuclideanWspField.euclideanMemLp,
    MemLp.coeFn_toLp k.toCubeEuclideanWspField.euclideanMemLp,
    Lp.coeFn_add (graphFieldComponent h) (graphFieldComponent k)] with x hhk hh hk hadd
  calc
    graphFieldComponent (h + k) x = HilbertVec.ofVec ((h + k).toField x) := hhk
    _ = HilbertVec.ofVec (h.toField x) + HilbertVec.ofVec (k.toField x) := by
      rw [toField_add, Pi.add_apply]
      change (HilbertVec.ofVecL d) (h.toField x + k.toField x) = _
      simpa only [HilbertVec.ofVecL_apply] using
        (HilbertVec.ofVecL d).map_add (h.toField x) (k.toField x)
    _ = (graphFieldComponent h + graphFieldComponent k) x := by
      have hh' : graphFieldComponent h x = HilbertVec.ofVec (h.toField x) := by
        simpa only [graphFieldComponent, toCubeEuclideanWspField_toField] using hh
      have hk' : graphFieldComponent k x = HilbertVec.ofVec (k.toField x) := by
        simpa only [graphFieldComponent, toCubeEuclideanWspField_toField] using hk
      rw [← hh', ← hk']
      exact hadd.symm

private theorem graphFieldComponent_smul {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} (c : ℝ)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    graphFieldComponent (c • h) = c • graphFieldComponent h := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (c • h).toCubeEuclideanWspField.euclideanMemLp,
    MemLp.coeFn_toLp h.toCubeEuclideanWspField.euclideanMemLp,
    Lp.coeFn_smul c (graphFieldComponent h)] with x hch hh hsmul
  calc
    graphFieldComponent (c • h) x = HilbertVec.ofVec ((c • h).toField x) := hch
    _ = c • HilbertVec.ofVec (h.toField x) := by
      rw [toField_smul, Pi.smul_apply]
      change (HilbertVec.ofVecL d) (c • h.toField x) = _
      simpa only [HilbertVec.ofVecL_apply] using
        (HilbertVec.ofVecL d).map_smul c (h.toField x)
    _ = (c • graphFieldComponent h) x := by
      have hh' : graphFieldComponent h x = HilbertVec.ofVec (h.toField x) := by
        simpa only [graphFieldComponent, toCubeEuclideanWspField_toField] using hh
      rw [← hh']
      exact hsmul.symm

private theorem cubeEuclideanWspKernel_smoothTest_add {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h k : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanWspKernel s p (h + k).toField =
      cubeEuclideanWspKernel s p h.toField + cubeEuclideanWspKernel s p k.toField := by
  funext z
  rw [cubeEuclideanWspKernel_apply, toField_add]
  change (euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) • HilbertVec.ofVec
      ((h.toField z.1 + k.toField z.1) - (h.toField z.2 + k.toField z.2)) =
    (euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
      HilbertVec.ofVec (h.toField z.1 - h.toField z.2) +
    (euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
      HilbertVec.ofVec (k.toField z.1 - k.toField z.2)
  rw [add_sub_add_comm]
  change (euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) • (HilbertVec.ofVecL d)
      ((h.toField z.1 - h.toField z.2) + (k.toField z.1 - k.toField z.2)) = _
  rw [(HilbertVec.ofVecL d).map_add, smul_add]
  simp only [HilbertVec.ofVecL_apply]

private theorem cubeEuclideanWspKernel_smoothTest_smul {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} (c : ℝ)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanWspKernel s p (c • h).toField =
      c • cubeEuclideanWspKernel s p h.toField := by
  funext z
  rw [cubeEuclideanWspKernel_apply, toField_smul, Pi.smul_apply, Pi.smul_apply,
    Pi.smul_apply, cubeEuclideanWspKernel_apply]
  rw [← smul_sub]
  change (euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
      HilbertVec.ofVec (c • (h.toField z.1 - h.toField z.2)) =
    c • ((euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
      HilbertVec.ofVec (h.toField z.1 - h.toField z.2))
  change (euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
    (HilbertVec.ofVecL d) (c • (h.toField z.1 - h.toField z.2)) = _
  rw [(HilbertVec.ofVecL d).map_smul, smul_smul, smul_smul, mul_comm]
  simp only [HilbertVec.ofVecL_apply]

private theorem graphKernelComponent_add {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h k : CubeEuclideanWspSmoothTest Q s p) :
    graphKernelComponent (h + k) = graphKernelComponent h + graphKernelComponent k := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (h + k).toCubeEuclideanWspField.euclideanMemWsp,
    MemLp.coeFn_toLp h.toCubeEuclideanWspField.euclideanMemWsp,
    MemLp.coeFn_toLp k.toCubeEuclideanWspField.euclideanMemWsp,
    Lp.coeFn_add (graphKernelComponent h) (graphKernelComponent k)] with z hhk hh hk hadd
  calc
    graphKernelComponent (h + k) z = cubeEuclideanWspKernel s p (h + k).toField z := hhk
    _ = cubeEuclideanWspKernel s p h.toField z + cubeEuclideanWspKernel s p k.toField z := by
      simpa only [Pi.add_apply] using congrFun (cubeEuclideanWspKernel_smoothTest_add h k) z
    _ = (graphKernelComponent h + graphKernelComponent k) z := by
      have hh' : graphKernelComponent h z = cubeEuclideanWspKernel s p h.toField z := by
        simpa only [graphKernelComponent, toCubeEuclideanWspField_toField] using hh
      have hk' : graphKernelComponent k z = cubeEuclideanWspKernel s p k.toField z := by
        simpa only [graphKernelComponent, toCubeEuclideanWspField_toField] using hk
      rw [← hh', ← hk']
      exact hadd.symm

private theorem graphKernelComponent_smul {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} (c : ℝ)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    graphKernelComponent (c • h) = c • graphKernelComponent h := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (c • h).toCubeEuclideanWspField.euclideanMemWsp,
    MemLp.coeFn_toLp h.toCubeEuclideanWspField.euclideanMemWsp,
    Lp.coeFn_smul c (graphKernelComponent h)] with z hch hh hsmul
  calc
    graphKernelComponent (c • h) z = cubeEuclideanWspKernel s p (c • h).toField z := hch
    _ = c • cubeEuclideanWspKernel s p h.toField z := by
      simpa only [Pi.smul_apply] using congrFun (cubeEuclideanWspKernel_smoothTest_smul c h) z
    _ = (c • graphKernelComponent h) z := by
      have hh' : graphKernelComponent h z = cubeEuclideanWspKernel s p h.toField z := by
        simpa only [graphKernelComponent, toCubeEuclideanWspField_toField] using hh
      rw [← hh']
      exact hsmul.symm

/-- The two ambient `L^p` components of a smooth fractional-Sobolev test. -/
noncomputable def graphPoint {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) : CubeEuclideanWspGraphAmbient Q p :=
  WithLp.toLp p.exponent fun b =>
    match b with
    | false => cubeEuclideanWspGraphFieldScale Q s • graphFieldComponent h
    | true => graphKernelComponent h

/-- The linear smooth graph in the two-component ambient `L^p` space. -/
noncomputable def graph {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} :=
  letI : Fact (1 ≤ p.exponent) := ⟨p.one_lt.le⟩
  show CubeEuclideanWspSmoothTest Q s p →ₗ[ℝ] CubeEuclideanWspGraphAmbient Q p from
    { toFun := graphPoint
      map_add' := by
        intro h k
        apply PiLp.ext
        intro b
        cases b
        · change cubeEuclideanWspGraphFieldScale Q s • graphFieldComponent (h + k) =
            cubeEuclideanWspGraphFieldScale Q s • graphFieldComponent h +
              cubeEuclideanWspGraphFieldScale Q s • graphFieldComponent k
          rw [graphFieldComponent_add, smul_add]
        · exact graphKernelComponent_add h k
      map_smul' := by
        intro c h
        apply PiLp.ext
        intro b
        cases b
        · change cubeEuclideanWspGraphFieldScale Q s • graphFieldComponent (c • h) =
            c • (cubeEuclideanWspGraphFieldScale Q s • graphFieldComponent h)
          rw [graphFieldComponent_smul, smul_smul, smul_smul, mul_comm]
        · exact graphKernelComponent_smul c h }

private theorem enorm_graphFieldComponent {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    ‖graphFieldComponent h‖ₑ =
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent h.toField := by
  have hLp : ‖graphFieldComponent h‖ₑ =
      eLpNorm (fun x => HilbertVec.ofVec (h.toField x)) p.exponent
        (normalizedCubeMeasure Q) :=
    Lp.enorm_toLp h.toCubeEuclideanWspField.euclideanMemLp
  rw [hLp]
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
  unfold BoundedMeasurableDomain.normalizedLpENorm
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  simp only [euclideanNorm_eq_norm_ofVec, eLpNorm_norm]

private theorem enorm_graphKernelComponent {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    ‖graphKernelComponent h‖ₑ = cubeEuclideanWspESeminorm Q s p h.toField := by
  exact Lp.enorm_toLp h.toCubeEuclideanWspField.euclideanMemWsp

private theorem enorm_graphFieldScale_rpow_eq_wspScalePowerWeight {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent) :
    ‖cubeEuclideanWspGraphFieldScale Q s‖ₑ ^ p.exponent.toReal =
      cubeEuclideanWspScalePowerWeight Q s p := by
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  unfold cubeEuclideanWspGraphFieldScale cubeEuclideanWspScalePowerWeight
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hscale.le _),
    ← ENNReal.ofReal_rpow_of_pos hscale]
  rw [← ENNReal.rpow_mul]

/-- The ambient `L^p` norm of a smooth graph point is exactly the approved
full cube fractional-Sobolev norm. -/
theorem graph_enorm_eq_cubeEuclideanWspFullENorm {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    ‖graph h‖ₑ = cubeEuclideanWspFullENorm Q s p h.toField := by
  let : Fact (1 ≤ p.exponent) := ⟨p.one_lt.le⟩
  change ‖graphPoint h‖ₑ = cubeEuclideanWspFullENorm Q s p h.toField
  rw [enorm_eq_nnnorm, PiLp.nnnorm_eq_sum p.lt_top.ne]
  rw [one_div, ENNReal.coe_rpow_of_nonneg _ (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ENNReal.ofNNReal_finsetSum]
  simp_rw [ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
  rw [Fintype.sum_bool]
  change (‖graphKernelComponent h‖ₑ ^ p.exponent.toReal +
      ‖cubeEuclideanWspGraphFieldScale Q s • graphFieldComponent h‖ₑ ^ p.exponent.toReal) ^
        (p.exponent.toReal)⁻¹ = cubeEuclideanWspFullENorm Q s p h.toField
  rw [enorm_smul, enorm_graphKernelComponent, enorm_graphFieldComponent,
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
    enorm_graphFieldScale_rpow_eq_wspScalePowerWeight]
  unfold cubeEuclideanWspFullENorm
  rw [add_comm]

/-- The closed submodule generated by the smooth two-component graph. -/
noncomputable def completedGraphSubmodule {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) :
    Submodule ℝ (CubeEuclideanWspGraphAmbient Q p) :=
  (LinearMap.range (graph (Q := Q) (s := s) (p := p))).topologicalClosure

/-- The completed graph carrier, retaining its inherited normed and complete
linear-space structure. -/
noncomputable abbrev CubeEuclideanWspCompletedDualGraph {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent) : Type _ :=
  completedGraphSubmodule Q s p

/-- The closure of the smooth graph is a complete normed space. -/
noncomputable instance instCompleteSpaceCubeEuclideanWspCompletedDualGraph {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent) :
    CompleteSpace (CubeEuclideanWspCompletedDualGraph Q s p) := by
  change CompleteSpace (completedGraphSubmodule Q s p)
  exact Submodule.topologicalClosure.completeSpace _

/-- The canonical linear inclusion of smooth tests into their completed graph
carrier. -/
noncomputable def graphToCompleted {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} :
    CubeEuclideanWspSmoothTest Q s p →ₗ[ℝ] CubeEuclideanWspCompletedDualGraph Q s p :=
  (graph (Q := Q) (s := s) (p := p)).codRestrict (completedGraphSubmodule Q s p)
    fun h => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ h)

/-- Smooth graph points are dense in the completed graph carrier by construction. -/
theorem denseRange_graphToCompleted {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} :
    DenseRange (graphToCompleted (Q := Q) (s := s) (p := p)) := by
  let G := graph (Q := Q) (s := s) (p := p)
  let M := LinearMap.range G
  let f : CubeEuclideanWspSmoothTest Q s p →ₗ[ℝ] M :=
    G.codRestrict M (LinearMap.mem_range_self G)
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨h, hh⟩
    exact ⟨h, Subtype.ext hh⟩
  change DenseRange ((Submodule.inclusion (Submodule.le_topologicalClosure M)) ∘ f)
  exact ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
    hsurj.denseRange (continuous_inclusion subset_closure)

end CubeEuclideanWspSmoothTest

end

end Homogenization
