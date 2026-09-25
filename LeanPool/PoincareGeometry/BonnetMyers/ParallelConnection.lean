/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.CurveConnection
public import LeanPool.PoincareGeometry.BonnetMyers.MetricParallel
public import LeanPool.PoincareGeometry.BonnetMyers.LocalParallelNorm

/-!
# Intrinsic local parallel transport

`Parallel.lean` constructs the coordinate solution of the linear transport
equation.  This file proves the missing geometric interpretation: after the
coordinate field is expressed through the canonical smooth frame extensions,
its covariant derivative along the local geodesic is zero.  The frame agreement
is retained as a neighbourhood condition, rather than treating a chart frame
as a global frame.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

/-! ## Frame calculations for a transported field -/

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type _)]

omit [CompleteSpace E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- If a family of global frame extensions agrees locally with a chart frame,
then its fixed-coefficient field agrees locally with the corresponding chart
field. -/
lemma frameField_eventuallyEq_coordinateFrameCombination
    (x₀ y : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x) (u : E)
    (hframe : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ z in 𝓝 y, S i z = (trivializationAt E TM x₀).localFrame b i z) :
    (fun z ↦ IntrinsicAcceleration.frameField (I := I) (M := M) b S u z) =ᶠ[𝓝 y]
      fun z ↦ coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u z := by
  have hframes : ∀ᶠ z in 𝓝 y,
      ∀ i ∈ (Finset.univ : Finset (IntrinsicAcceleration.FrameIndex E)),
        S i z = (trivializationAt E TM x₀).localFrame b i z :=
    (Finset.eventually_all Finset.univ).2 fun i _ ↦ hframe i
  filter_upwards [hframes] with z hz
  unfold IntrinsicAcceleration.frameField coordinateFrameCombination
  apply Finset.sum_congr rfl
  intro i hi
  rw [hz i hi]

/-- The covariant derivative of a locally chart-represented frame field is
read by the coordinate parallel operator.  This is the bridge needed to turn
the linear ODE into the intrinsic equation `∇_{γ̇} V = 0`. -/
lemma cov_smoothFrameField_apply_eq_coordinateParallelOperator
    (cov : CovariantDerivative I E TM) (x₀ y : M)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E) (u w : E)
    (hy : y ∈ (chartAt H x₀).source)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hframe : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ z in 𝓝 y,
        smoothFrame (I := I) (M := M) (E := E) x₀ b i z =
          (trivializationAt E TM x₀).localFrame b i z) :
    cov (IntrinsicAcceleration.frameField (I := I) (M := M) b
        (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) w) y
        (IntrinsicAcceleration.frameField (I := I) (M := M) b
          (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) u y) =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (extChartAt I x₀ y) u w) y := by
  have hfieldw := frameField_eventuallyEq_coordinateFrameCombination
    (I := I) (M := M) (E := E) x₀ y b
    (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) w hframe
  have hfieldU := frameField_eventuallyEq_coordinateFrameCombination
    (I := I) (M := M) (E := E) x₀ y b
    (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) u hframe
  have hW : MDiffAt (T% (IntrinsicAcceleration.frameField (I := I) (M := M)
      b (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) w)) y := by
    apply IntrinsicAcceleration.mdiffAt_frameField (I := I) (M := M) b
      (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) w
    intro i
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M) x₀ b i y
  have hWcoord : MDiffAt (T% (coordinateFrameCombination (I := I) (M := M)
      (x₀ := x₀) b w)) y :=
    (coordinateFrameCombination_contMDiffAt (I := I) (M := M)
      (x₀ := x₀) y b w hy).mdifferentiableAt one_ne_zero
  have hcov : cov (IntrinsicAcceleration.frameField (I := I) (M := M)
      b (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) w) y =
      cov (coordinateFrameCombination (I := I) (M := M)
      (x₀ := x₀) b w) y :=
    IsCovariantDerivativeOn.congr_of_eventuallyEq cov.isCovariantDerivativeOn
      hW hWcoord Filter.univ_mem hfieldw
  have hU : IntrinsicAcceleration.frameField (I := I) (M := M) b
      (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) u y =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y := by
    have hUevent : ∀ᶠ z in 𝓝 y,
      IntrinsicAcceleration.frameField (I := I) (M := M) b
        (fun i => smoothFrame (I := I) (M := M) (E := E) x₀ b i) u z =
        coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u z := hfieldU
    exact hUevent.self_of_nhds
  rw [hcov, hU]
  exact cov_coordinateFrameCombination_apply (I := I) (M := M) (E := E)
    cov x₀ y b u w hy hframe

end LocalGeodesicData

/-! ## An intrinsic derivative criterion for a time-dependent field -/

open CurveConnection

/-- The scalar characterization of covariant differentiation applies to an
arbitrary time-dependent frame field along a prescribed velocity, not only to
the special case in which the field is the velocity itself. -/
theorem isCovariantAccelerationAt_timeFrameField_of_velocity
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E TM)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x)
    (u a : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t (timeTangentMap (I := I) t v))
    (hu : ∀ i, HasDerivAt (fun s ↦ b.repr (u s) i) (b.repr (a t) i) t)
    (hS : ∀ i, MDiffAt (T% (S i)) (γ t))
    (hmetric : cov.IsMetricCompatibleTangent) :
    IsCovariantAccelerationAt cov γ
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M)
        b S u s (γ s)) t v
      (IntrinsicAcceleration.frameField (I := I) (M := M) b S (a t) (γ t) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t))
          (γ t) v) := by
  intro W hW
  rw [curveScalarDeriv_inner_timeFrameField (I := I) (M := M)
    cov b S u a γ hγ hu hS hmetric W hW]
  rfl

/-- An intrinsically parallel time-dependent field satisfies the genuine
linear coordinate transport equation in any chart on whose local-frame
agreement neighbourhood it is represented.  The curve velocity and the
transported field have separate coefficient functions; this is the
first-order counterpart of the coordinate geodesic-acceleration bridge. -/
theorem hasDerivAt_coordinateParallel_of_intrinsic_zero
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E TM)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (x₀ : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (u q : ℝ → E) (γ : ℝ → M) {t : ℝ} {v : TM (γ t)} {a : E}
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t
      (timeTangentMap (I := I) t v))
    (hq : HasDerivAt q a t)
    (hmetric : cov.IsMetricCompatibleTangent)
    (hmem : γ t ∈ IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) x₀ b)
    (hframe : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ z in 𝓝 (γ t),
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i z =
          (trivializationAt E TM x₀).localFrame b i z)
    (hvelocity : v = IntrinsicAcceleration.frameField (I := I) (M := M) b
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
        x₀ b i) (u t) (γ t))
    (hzero : IsCovariantAccelerationAt cov γ
      (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) b
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          x₀ b i) q s (γ s)) t v 0) :
    HasDerivAt q
      (-(LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ b (extChartAt I x₀ (γ t)) (u t) (q t))) t := by
  let S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x := fun i =>
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i
  have hS : ∀ i, MDiffAt (T% (S i)) (γ t) := by
    intro i
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M) x₀ b i _
  have hcoeff : ∀ i, HasDerivAt (fun s ↦ b.repr (q s) i)
      (b.repr a i) t := by
    intro i
    have hc : HasDerivAt (fun _ : ℝ ↦ (b.coord i).toContinuousLinearMap) 0 t :=
      hasDerivAt_const t (b.coord i).toContinuousLinearMap
    simpa using hc.clm_apply hq
  have hacc := isCovariantAccelerationAt_timeFrameField_of_velocity
    (I := I) (M := M) cov b S q (fun _ ↦ a) γ hγ hcoeff hS hmetric
  have hzeroField : IntrinsicAcceleration.frameField (I := I) (M := M) b S a
      (γ t) +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (q t))
        (γ t) v = 0 :=
    IsCovariantAccelerationAt.unique hacc hzero
  have hy : γ t ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact hmem.1
  have hderivField : IntrinsicAcceleration.frameField (I := I) (M := M) b S a
      (γ t) = LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b a (γ t) := by
    change (∑ i, (b.repr a i) • S i (γ t)) =
      ∑ i, (b.repr a i) • (trivializationAt E TM x₀).localFrame b i (γ t)
    apply Finset.sum_congr rfl
    intro i hi
    change (b.repr a i) •
        LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i (γ t) = _
    rw [(hframe i).self_of_nhds]
  have hcov : cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S
      (q t)) (γ t)
      (IntrinsicAcceleration.frameField (I := I) (M := M) b S (u t) (γ t)) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b
        (LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
          (E := E) cov x₀ b (extChartAt I x₀ (γ t)) (u t) (q t)) (γ t) := by
    simpa [S] using LocalGeodesicData.cov_smoothFrameField_apply_eq_coordinateParallelOperator
      (I := I) (M := M) (E := E) cov x₀ (γ t) b (u t) (q t) hy hframe
  rw [hvelocity, hderivField, hcov] at hzeroField
  have hsum : IntrinsicAcceleration.coordinateFrameVector (I := I) (M := M)
      x₀ b
      (a + LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ b (extChartAt I x₀ (γ t)) (u t) (q t)) (γ t) = 0 := by
    rw [IntrinsicAcceleration.coordinateFrameVector_add]
    exact hzeroField
  have hsum' : a + LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov x₀ b (extChartAt I x₀ (γ t)) (u t) (q t) = 0 := by
    apply CurveConnection.coordinateFrameLinear_injective_of_mem_source
      (I := I) (M := M) x₀ b hmem.1
    change IntrinsicAcceleration.coordinateFrameVector (I := I) (M := M) x₀ b
      (a + LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ b (extChartAt I x₀ (γ t)) (u t) (q t)) (γ t) =
      IntrinsicAcceleration.coordinateFrameVector (I := I) (M := M) x₀ b 0 (γ t)
    rw [hsum]
    simp [IntrinsicAcceleration.coordinateFrameVector,
      LocalGeodesicData.coordinateFrameCombination]
  rw [eq_neg_of_add_eq_zero_left hsum'] at hq
  exact hq

namespace IntrinsicGeodesic.LocalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- The smooth-frame representative of a coordinate parallel solution along a
local geodesic.  The use of smooth frame extensions lets the covariant
derivative be tested against arbitrary differentiable sections. -/
def canonicalFrameParallel
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (t : ℝ) : TM (IntrinsicGeodesic.LocalGeodesic.curve γ t) :=
  IntrinsicAcceleration.timeFrameField (I := I) (M := M)
    (IntrinsicGeodesic.canonicalBasis (E := E))
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
      (IntrinsicGeodesic.canonicalBasis (E := E)) i)
    wsol.curve t (IntrinsicGeodesic.LocalGeodesic.curve γ t)

/-- The coordinate velocity packaged as the canonical parallel solution along
the same local geodesic.  Its defining ODE has been proved separately from
the coordinate geodesic equation in `localVelocityParallelSolution`. -/
def velocityParallelSolution
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0
      (γ.solution.velocity 0) :=
  LocalGeodesicData.localVelocityParallelSolution (I := I) (M := M) (E := E)
    cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E)) γ.solution

/-- Reverse a coordinate parallel solution together with its local geodesic.
The definition is written directly, rather than transported through an
equality of coefficient functions, so that its curve is definitionally the
time-reversed original curve.  This makes the subsequent tangent-bundle
reversal statement usable without an opaque `Eq.mp` cast. -/
noncomputable def reverseParallelSolution
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀) :
    LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        ((IntrinsicGeodesic.LocalGeodesic.reverse γ).solution.coordinate t)
        ((IntrinsicGeodesic.LocalGeodesic.reverse γ).solution.velocity t)) 0 w₀ := by
  refine {
    curve := fun t ↦ wsol.curve (-t)
    radius := wsol.radius
    radius_pos := wsol.radius_pos
    initial := by simpa using wsol.initial
    hasDeriv := ?_ }
  intro t ht
  have ht' : -t ∈ Ioo (0 - wsol.radius) (0 + wsol.radius) := by
    constructor <;> linarith [ht.1, ht.2]
  change HasDerivAt (wsol.curve ∘ Neg.neg)
    (-((LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
      (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
      ((IntrinsicGeodesic.LocalGeodesic.reverse γ).solution.coordinate t)
      ((IntrinsicGeodesic.LocalGeodesic.reverse γ).solution.velocity t))
      (wsol.curve (-t)))) t
  simpa [Function.comp_def] using
    HasDerivAt.scomp t (wsol.hasDeriv (-t) ht') (hasDerivAt_neg t)

@[simp] theorem reverseParallelSolution_curve
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (t : ℝ) :
    (reverseParallelSolution γ wsol).curve t = wsol.curve (-t) := by
  simp [reverseParallelSolution]

private theorem timeFrameField_eq_cast_of_eq
    {x y : M} (hxy : x = y)
    (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (S : IntrinsicAcceleration.FrameIndex E → (z : M) → TM z)
    (u : ℝ → E) (t : ℝ) :
    IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t x =
      cast (congrArg (TangentSpace I) hxy.symm)
        (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S u t y) := by
  cases hxy
  rfl

private theorem cast_tangent_heq_of_eq
    {x y : M} (hxy : x = y) (u : TM y) :
    HEq (cast (congrArg (TangentSpace I) hxy.symm) u) u := by
  subst y
  rfl

/-- The tangent-valued canonical field of the reversed local geodesic is the
same total tangent-bundle curve as the original field read at negative time.
This is the geometric, chart-independent form of time reversal for local
parallel transport. -/
theorem reverse_canonicalFrameParallel_totalState
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀) (t : ℝ) :
    (⟨IntrinsicGeodesic.LocalGeodesic.curve
        (IntrinsicGeodesic.LocalGeodesic.reverse γ) t,
      IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (IntrinsicGeodesic.LocalGeodesic.reverse γ)
        (reverseParallelSolution γ wsol) t⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨IntrinsicGeodesic.LocalGeodesic.curve γ (-t),
      IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel γ wsol (-t)⟩ := by
  let U : ℝ → E := fun s ↦ wsol.curve (-s)
  have hcurve : IntrinsicGeodesic.LocalGeodesic.curve
      (IntrinsicGeodesic.LocalGeodesic.reverse γ) t =
      IntrinsicGeodesic.LocalGeodesic.curve γ (-t) :=
    IntrinsicGeodesic.LocalGeodesic.reverse_curve γ t
  have hcoeff : (reverseParallelSolution γ wsol).curve t = U t := by
    simpa [U] using reverseParallelSolution_curve γ wsol t
  have hfield : IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
      (IntrinsicGeodesic.LocalGeodesic.reverse γ)
      (reverseParallelSolution γ wsol) t =
      cast (congrArg (TangentSpace I) hcurve.symm)
        (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel γ wsol (-t)) := by
    change IntrinsicAcceleration.timeFrameField (I := I) (M := M)
      (IntrinsicGeodesic.canonicalBasis (E := E))
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
        (IntrinsicGeodesic.canonicalBasis (E := E)) i)
      (reverseParallelSolution γ wsol).curve t
      (IntrinsicGeodesic.LocalGeodesic.curve
        (IntrinsicGeodesic.LocalGeodesic.reverse γ) t) =
      cast (congrArg (TangentSpace I) hcurve.symm)
        (IntrinsicAcceleration.timeFrameField (I := I) (M := M)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
            (IntrinsicGeodesic.canonicalBasis (E := E)) i)
          wsol.curve (-t) (IntrinsicGeodesic.LocalGeodesic.curve γ (-t)))
    simp only [IntrinsicAcceleration.timeFrameField]
    rw [hcoeff]
    exact timeFrameField_eq_cast_of_eq (I := I) (M := M) hcurve
      (IntrinsicGeodesic.canonicalBasis (E := E))
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
        (IntrinsicGeodesic.canonicalBasis (E := E)) i) U t
  apply Bundle.TotalSpace.ext hcurve
  rw [hfield]
  exact cast_tangent_heq_of_eq (I := I) hcurve
    (IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel γ wsol (-t))

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- At the initial time the smooth-frame presentation of a coordinate
parallel field is exactly its coordinate-frame value.  This is kept separate
from the ODE equation: it is the fibre-identification needed to prescribe an
actual tangent vector as initial transport data. -/
theorem canonicalFrameParallel_initial
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀) :
    canonicalFrameParallel (I := I) (M := M) γ wsol 0 =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E)) w₀ x₀ := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  let S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x := fun i =>
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i
  have hframe : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ z in 𝓝 x₀,
        S i z = (trivializationAt E TM x₀).localFrame b i z := by
    intro i
    exact LocalGeodesicData.smoothFrame_eventuallyEq_localFrame
      (I := I) (M := M) (E := E) x₀ b i
  change IntrinsicAcceleration.frameField (I := I) (M := M) b S
      (wsol.curve 0) (IntrinsicGeodesic.LocalGeodesic.curve γ 0) = _
  rw [wsol.initial, IntrinsicGeodesic.LocalGeodesic.curve_initial]
  unfold IntrinsicAcceleration.frameField LocalGeodesicData.coordinateFrameCombination
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun q : TM x₀ ↦ (b.repr w₀ i) • q)
    (hframe i).self_of_nhds

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- Prescribing the model coefficient obtained from a tangent vector really
prescribes that tangent vector.  This removes the chart-fibre artefact from
the local transport existence theorem below. -/
theorem canonicalFrameParallel_initial_of_coordinateVelocity
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (w : TM x₀)
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ w)) :
    canonicalFrameParallel (I := I) (M := M) γ wsol 0 = w := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  rw [IntrinsicGeodesic.LocalGeodesic.curve_initial γ]
  rw [canonicalFrameParallel_initial (I := I) (M := M) γ wsol]
  simpa [b] using LocalGeodesicData.coordinateFrameCombination_coordinateVelocity
    (I := I) (M := M) (E := E) x₀ b w

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- The tangent-valued presentation respects addition of coordinate parallel
solutions.  Together with metric preservation, this will give preservation of
inner products rather than only norms. -/
theorem canonicalFrameParallel_add
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₁ w₂ : E}
    (wsol₁ : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₁)
    (wsol₂ : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₂)
    (t : ℝ) :
    canonicalFrameParallel (I := I) (M := M) γ
        (LocalLinearTransportSolution.add wsol₁ wsol₂) t =
      canonicalFrameParallel (I := I) (M := M) γ wsol₁ t +
        canonicalFrameParallel (I := I) (M := M) γ wsol₂ t := by
  simp [canonicalFrameParallel, LocalLinearTransportSolution.add,
    IntrinsicAcceleration.timeFrameField, map_add, add_smul,
    Finset.sum_add_distrib]

/-- On a sufficiently small common interval, the smooth-frame presentation of
the canonical parallel field agrees with the literal coordinate-frame
combination.  The radius is made explicit so that metric identities proved in
coordinates can be transferred to the actual tangent-valued field. -/
theorem canonicalFrameParallel_eq_coordinateFrameCombination_near_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀) :
    ∃ r > (0 : ℝ), r ≤ min γ.solution.radius wsol.radius ∧
      ∀ t ∈ Ioo (-r) r,
        canonicalFrameParallel (I := I) (M := M) γ wsol t =
          LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E))
            (wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  let S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x := fun i =>
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i
  let T : IntrinsicAcceleration.FrameIndex E → Set M := fun i ↦
    {z | S i z = (trivializationAt E TM x₀).localFrame b i z}
  have hT : ∀ i, T i ∈ 𝓝 x₀ := by
    intro i
    change ∀ᶠ z in 𝓝 x₀,
      LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i z =
        (trivializationAt E TM x₀).localFrame b i z
    exact LocalGeodesicData.smoothFrame_eventuallyEq_localFrame
      (I := I) (M := M) (E := E) x₀ b i
  have hTinter : (⋂ i, T i) ∈ 𝓝 x₀ := (Filter.iInter_mem).2 hT
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp hTinter
  have hzero : (0 : ℝ) ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [γ.solution.radius_pos]
  have hcont : ContinuousAt (IntrinsicGeodesic.LocalGeodesic.curve γ) 0 :=
    (IntrinsicGeodesic.LocalGeodesic.hasMFDerivAt_curve γ hzero).continuousAt
  have hpre : (IntrinsicGeodesic.LocalGeodesic.curve γ) ⁻¹' O ∈ 𝓝 (0 : ℝ) := by
    apply hcont.preimage_mem_nhds
    rw [IntrinsicGeodesic.LocalGeodesic.curve_initial]
    exact hOopen.mem_nhds hxO
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r : ℝ := min (min γ.solution.radius wsol.radius) (δ / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (lt_min γ.solution.radius_pos wsol.radius_pos) (by linarith)
  have hradius : r ≤ min γ.solution.radius wsol.radius := min_le_left _ _
  refine ⟨r, hr, hradius, ?_⟩
  intro t ht
  have htsol : t ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    have hle : r ≤ γ.solution.radius := le_trans hradius (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have hminδ : r ≤ δ / 2 := min_le_right _ _
  have habs : |t| < δ := by
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2, hminδ]
  have htO : IntrinsicGeodesic.LocalGeodesic.curve γ t ∈ O := by
    apply hδsub
    rw [Metric.mem_ball]
    simpa [dist_zero_right] using habs
  have hframeAt : ∀ i : IntrinsicAcceleration.FrameIndex E,
      S i (IntrinsicGeodesic.LocalGeodesic.curve γ t) =
        (trivializationAt E TM x₀).localFrame b i
          (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
    intro i
    exact Set.mem_iInter.mp (hOsub htO) i
  have hy : IntrinsicGeodesic.LocalGeodesic.curve γ t ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    change (extChartAt I x₀).symm (γ.solution.coordinate t) ∈
      (extChartAt I x₀).source
    exact (extChartAt I x₀).map_target (γ.solution.coordinate_mem_target t htsol)
  have hmem : IntrinsicGeodesic.LocalGeodesic.curve γ t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) x₀ b := by
    refine ⟨?_, ?_⟩
    · simpa [IntrinsicGeodesic.LocalGeodesic.curve] using hy
    · simpa [S] using hframeAt
  change IntrinsicAcceleration.frameField (I := I) (M := M) b
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i)
    (wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) = _
  simpa [b, S, canonicalFrameParallel] using
    frameField_eq_coordinateFrameCombination_of_mem_agreement
      (I := I) (M := M) x₀ b (wsol.curve t) hmem

/-- The canonical parallel field obtained from the velocity solution is the
actual tangent velocity of the local geodesic near its initial time.  Thus a
parallel frame initialized with the geodesic direction really retains that
direction, rather than merely preserving a coordinate representative. -/
theorem canonicalFrameParallel_velocity_eq_velocity_near_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    ∃ r > (0 : ℝ), ∀ t ∈ Ioo (-r) r,
      canonicalFrameParallel (I := I) (M := M) γ
        (velocityParallelSolution (I := I) (M := M) γ) t =
        IntrinsicGeodesic.LocalGeodesic.velocity γ t := by
  let wsol := velocityParallelSolution (I := I) (M := M) γ
  obtain ⟨r₁, hr₁, _hr₁radius, hframe⟩ :=
    canonicalFrameParallel_eq_coordinateFrameCombination_near_zero
      (I := I) (M := M) γ wsol
  let r : ℝ := min r₁ γ.solution.radius
  have hr : 0 < r := lt_min hr₁ γ.solution.radius_pos
  refine ⟨r, hr, ?_⟩
  intro t ht
  change canonicalFrameParallel (I := I) (M := M) γ wsol t =
    IntrinsicGeodesic.LocalGeodesic.velocity γ t
  have ht₁ : t ∈ Ioo (-r₁) r₁ := by
    have hle : r ≤ r₁ := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have htγ : t ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    have hle : r ≤ γ.solution.radius := min_le_right _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  calc
    canonicalFrameParallel (I := I) (M := M) γ wsol t =
        LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E))
          (wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) :=
      hframe t ht₁
    _ = LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E))
          (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
      rfl
    _ = IntrinsicGeodesic.LocalGeodesic.velocity γ t := by
      symm
      change LocalGeodesicData.tangentField (I := I) (M := M) (E := E)
        cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E)) γ.solution
        γ.solution.velocity t =
        LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E))
          (γ.solution.velocity t) (LocalChartSecondOrderSolution.curve γ.solution t)
      exact LocalGeodesicData.tangentField_eq_coordinateFrameCombination
        (I := I) (M := M) (E := E) (H := H) cov x₀
        (IntrinsicGeodesic.canonicalBasis (E := E)) γ.solution
        γ.solution.velocity htγ

/-- The genuinely tangent-valued local parallel field preserves its squared
Riemannian norm.  This transfers the coordinate calculation through the
certified smooth-frame agreement above; no global frame is assumed. -/
theorem canonicalFrameParallel_inner_self_constant_near_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), r ≤ min γ.solution.radius wsol.radius ∧
      ∀ t ∈ Ioo (-r) r,
        inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol t)
          (canonicalFrameParallel (I := I) (M := M) γ wsol t) =
        inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol 0)
          (canonicalFrameParallel (I := I) (M := M) γ wsol 0) := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  obtain ⟨r₁, hr₁, hr₁radius, hcoord⟩ :=
    LocalGeodesicData.coordinate_parallel_inner_constant_near_zero
      (I := I) (M := M) (E := E) (H := H) cov x₀ b γ.solution wsol hmetric
  dsimp [b] at hcoord
  obtain ⟨r₂, hr₂, hr₂radius, hfield⟩ :=
    canonicalFrameParallel_eq_coordinateFrameCombination_near_zero
      (I := I) (M := M) γ wsol
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hradius : r ≤ min γ.solution.radius wsol.radius :=
    le_trans (min_le_left _ _) hr₁radius
  refine ⟨r, hr, hradius, ?_⟩
  intro t ht
  have ht₁ : t ∈ Ioo (-r₁) r₁ := by
    have hle : r ≤ r₁ := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have ht₂ : t ∈ Ioo (-r₂) r₂ := by
    have hle : r ≤ r₂ := min_le_right _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  calc
    inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol t)
        (canonicalFrameParallel (I := I) (M := M) γ wsol t) =
      inner ℝ
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := x₀) b (wsol.curve t)
            (IntrinsicGeodesic.LocalGeodesic.curve γ t))
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := x₀) b (wsol.curve t)
            (IntrinsicGeodesic.LocalGeodesic.curve γ t)) := by
      rw [hfield t ht₂]
    _ = inner ℝ
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E)) w₀ x₀)
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E)) w₀ x₀) := by
      change inner ℝ
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E))
            (wsol.curve t) (LocalChartSecondOrderSolution.curve γ.solution t))
          (LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
            (x₀ := x₀) (IntrinsicGeodesic.canonicalBasis (E := E))
            (wsol.curve t) (LocalChartSecondOrderSolution.curve γ.solution t)) = _
      exact hcoord t ht₁
    _ = inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol 0)
          (canonicalFrameParallel (I := I) (M := M) γ wsol 0) := by
      rw [canonicalFrameParallel_initial (I := I) (M := M) γ wsol]
      rw [IntrinsicGeodesic.LocalGeodesic.curve_initial γ]

/-- Two independently prescribed local parallel fields preserve their actual
Riemannian inner product.  The proof uses the homogeneous-linear sum solution
and polarization, so it does not assume an orthonormal frame or a fixed
ambient vector space. -/
theorem canonicalFrameParallel_inner_constant_near_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₁ w₂ : E}
    (wsol₁ : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₁)
    (wsol₂ : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₂)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), ∀ t ∈ Ioo (-r) r,
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol₁ t)
        (canonicalFrameParallel (I := I) (M := M) γ wsol₂ t) =
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol₁ 0)
        (canonicalFrameParallel (I := I) (M := M) γ wsol₂ 0) := by
  obtain ⟨r₁, hr₁, _hr₁radius, hself₁⟩ :=
    canonicalFrameParallel_inner_self_constant_near_zero
      (I := I) (M := M) γ wsol₁ hmetric
  obtain ⟨r₂, hr₂, _hr₂radius, hself₂⟩ :=
    canonicalFrameParallel_inner_self_constant_near_zero
      (I := I) (M := M) γ wsol₂ hmetric
  let wsolSum := LocalLinearTransportSolution.add wsol₁ wsol₂
  obtain ⟨rSum, hrSum, _hrSumRadius, hselfSum⟩ :=
    canonicalFrameParallel_inner_self_constant_near_zero
      (I := I) (M := M) γ wsolSum hmetric
  let r : ℝ := min (min r₁ r₂) rSum
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (lt_min hr₁ hr₂) hrSum
  refine ⟨r, hr, ?_⟩
  intro t ht
  have ht₁ : t ∈ Ioo (-r₁) r₁ := by
    have hle : r ≤ r₁ := by
      dsimp [r]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have ht₂ : t ∈ Ioo (-r₂) r₂ := by
    have hle : r ≤ r₂ := by
      dsimp [r]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have htSum : t ∈ Ioo (-rSum) rSum := by
    have hle : r ≤ rSum := by
      dsimp [r]
      exact min_le_right _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  let V₁ : (s : ℝ) → TM (IntrinsicGeodesic.LocalGeodesic.curve γ s) := fun s ↦
    canonicalFrameParallel (I := I) (M := M) γ wsol₁ s
  let V₂ : (s : ℝ) → TM (IntrinsicGeodesic.LocalGeodesic.curve γ s) := fun s ↦
    canonicalFrameParallel (I := I) (M := M) γ wsol₂ s
  have h₁ : inner ℝ (V₁ t) (V₁ t) = inner ℝ (V₁ 0) (V₁ 0) := by
    simpa [V₁] using hself₁ t ht₁
  have h₂ : inner ℝ (V₂ t) (V₂ t) = inner ℝ (V₂ 0) (V₂ 0) := by
    simpa [V₂] using hself₂ t ht₂
  have hsum : inner ℝ (V₁ t + V₂ t) (V₁ t + V₂ t) =
      inner ℝ (V₁ 0 + V₂ 0) (V₁ 0 + V₂ 0) := by
    simpa [V₁, V₂, wsolSum, canonicalFrameParallel_add] using hselfSum t htSum
  have hsum' := hsum
  simp only [inner_add_left, inner_add_right] at hsum'
  rw [real_inner_comm (V₁ t) (V₂ t),
    real_inner_comm (V₁ 0) (V₂ 0)] at hsum'
  change inner ℝ (V₁ t) (V₂ t) = inner ℝ (V₁ 0) (V₂ 0)
  linarith

/-- Every locally parallel field preserves its inner product with the actual
geodesic velocity.  The proof first identifies that velocity with its own
parallel solution, then applies the two-field metric-preservation theorem.
This is the local transversality invariant needed for Jacobi test fields. -/
theorem canonicalFrameParallel_inner_velocity_constant_near_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), ∀ t ∈ Ioo (-r) r,
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol t)
          (IntrinsicGeodesic.LocalGeodesic.velocity γ t) =
        inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol 0)
          (IntrinsicGeodesic.LocalGeodesic.velocity γ 0) := by
  let vsol := velocityParallelSolution (I := I) (M := M) γ
  obtain ⟨r₁, hr₁, hinner⟩ :=
    canonicalFrameParallel_inner_constant_near_zero
      (I := I) (M := M) γ wsol vsol hmetric
  obtain ⟨r₂, hr₂, hvelocity⟩ :=
    canonicalFrameParallel_velocity_eq_velocity_near_zero
      (I := I) (M := M) γ
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  refine ⟨r, hr, ?_⟩
  intro t ht
  have ht₁ : t ∈ Ioo (-r₁) r₁ := by
    have hle : r ≤ r₁ := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have ht₂ : t ∈ Ioo (-r₂) r₂ := by
    have hle : r ≤ r₂ := min_le_right _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) ht.1,
      lt_of_lt_of_le ht.2 hle⟩
  have hzero : (0 : ℝ) ∈ Ioo (-r₂) r₂ := by
    constructor <;> linarith
  calc
    inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol t)
        (IntrinsicGeodesic.LocalGeodesic.velocity γ t) =
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol t)
        (canonicalFrameParallel (I := I) (M := M) γ vsol t) := by
      rw [hvelocity t ht₂]
    _ = inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol 0)
        (canonicalFrameParallel (I := I) (M := M) γ vsol 0) := hinner t ht₁
    _ = inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol 0)
        (IntrinsicGeodesic.LocalGeodesic.velocity γ 0) := by
      rw [hvelocity 0 hzero]

/-- In particular, a field initially orthogonal to the geodesic velocity
stays orthogonal on a genuine common interval. -/
theorem canonicalFrameParallel_orthogonal_velocity_near_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (horth : inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol 0)
      (IntrinsicGeodesic.LocalGeodesic.velocity γ 0) = 0) :
    ∃ r > (0 : ℝ), ∀ t ∈ Ioo (-r) r,
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ wsol t)
        (IntrinsicGeodesic.LocalGeodesic.velocity γ t) = 0 := by
  obtain ⟨r, hr, hconstant⟩ :=
    canonicalFrameParallel_inner_velocity_constant_near_zero
      (I := I) (M := M) γ wsol hmetric
  refine ⟨r, hr, ?_⟩
  intro t ht
  rw [hconstant t ht, horth]

/-- A finite collection of canonical local parallel fields has one common
interval on which its full Gram matrix is preserved.  The common radius is the
finite infimum of the pairwise radii, so this is stronger than merely having a
separate germ for every pair of vectors. -/
theorem canonicalFrameParallel_finite_inner_constant_near_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : ι → E}
    (wsol : ∀ i, LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 (w₀ i))
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), ∀ i j t, t ∈ Ioo (-r) r →
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ (wsol i) t)
        (canonicalFrameParallel (I := I) (M := M) γ (wsol j) t) =
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ (wsol i) 0)
        (canonicalFrameParallel (I := I) (M := M) γ (wsol j) 0) := by
  classical
  have hpair : ∀ i j, ∃ r > (0 : ℝ), ∀ t ∈ Ioo (-r) r,
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ (wsol i) t)
        (canonicalFrameParallel (I := I) (M := M) γ (wsol j) t) =
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ (wsol i) 0)
        (canonicalFrameParallel (I := I) (M := M) γ (wsol j) 0) := by
    intro i j
    exact canonicalFrameParallel_inner_constant_near_zero
      (I := I) (M := M) γ (wsol i) (wsol j) hmetric
  choose rPair hrPair hPair using hpair
  let r : ℝ := (Finset.univ : Finset (ι × ι)).inf' Finset.univ_nonempty
    (fun ij ↦ rPair ij.1 ij.2)
  have hr : 0 < r := by
    dsimp [r]
    refine (Finset.lt_inf'_iff _).2 ?_
    intro ij hij
    exact hrPair ij.1 ij.2
  refine ⟨r, hr, ?_⟩
  intro i j t ht
  have hle : r ≤ rPair i j := by
    dsimp [r]
    exact Finset.inf'_le (fun ij : ι × ι ↦ rPair ij.1 ij.2)
      (Finset.mem_univ (i, j))
  have htPair : t ∈ Ioo (-(rPair i j)) (rPair i j) := by
    constructor
    · exact lt_of_le_of_lt (neg_le_neg hle) ht.1
    · exact lt_of_lt_of_le ht.2 hle
  exact hPair i j t htPair

/-- A local solution of the coordinate parallel equation is an actual parallel
vector field along the local geodesic on a neighbourhood of the initial time.
The theorem is deliberately local: later continuation must glue these
certificates across charts. -/
theorem eventually_isCovariantAccelerationAt_canonicalFrameParallel_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      IsCovariantAccelerationAt cov (IntrinsicGeodesic.LocalGeodesic.curve γ)
        (canonicalFrameParallel (I := I) (M := M) γ wsol) t
        (IntrinsicAcceleration.frameField (I := I) (M := M)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
            (IntrinsicGeodesic.canonicalBasis (E := E)) i)
          (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t)) 0 := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  let S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x := fun i =>
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i
  let A : ℝ → E →L[ℝ] E := fun t ↦
    LocalGeodesicData.coordinateParallelOperator (I := I) (M := M) (E := E)
      cov x₀ b (γ.solution.coordinate t) (γ.solution.velocity t)
  have hintervalγ : Ioo (-γ.solution.radius) γ.solution.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [γ.solution.radius_pos])
      (by linarith [γ.solution.radius_pos])
  have hintervalw : Ioo (-wsol.radius) wsol.radius ∈ 𝓝 (0 : ℝ) := by
    simpa only [zero_sub, zero_add] using
      (Ioo_mem_nhds (by linarith [wsol.radius_pos])
        (by linarith [wsol.radius_pos]))
  let T : IntrinsicAcceleration.FrameIndex E → Set M := fun i ↦
    {z | S i z = (trivializationAt E TM x₀).localFrame b i z}
  have hT : ∀ i, T i ∈ 𝓝 x₀ := by
    intro i
    change ∀ᶠ z in 𝓝 x₀,
      LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i z =
        (trivializationAt E TM x₀).localFrame b i z
    exact LocalGeodesicData.smoothFrame_eventuallyEq_localFrame
      (I := I) (M := M) (E := E) x₀ b i
  have hTinter : (⋂ i, T i) ∈ 𝓝 x₀ := (Filter.iInter_mem).2 hT
  obtain ⟨O, hOsub, hOopen, hxO⟩ := mem_nhds_iff.mp hTinter
  have hzero : (0 : ℝ) ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [γ.solution.radius_pos]
  have hcont : ContinuousAt (IntrinsicGeodesic.LocalGeodesic.curve γ) 0 := by
    exact (IntrinsicGeodesic.LocalGeodesic.hasMFDerivAt_curve γ hzero).continuousAt
  have hpre : (IntrinsicGeodesic.LocalGeodesic.curve γ) ⁻¹' O ∈ 𝓝 (0 : ℝ) := by
    apply hcont.preimage_mem_nhds
    rw [IntrinsicGeodesic.LocalGeodesic.curve_initial]
    exact hOopen.mem_nhds hxO
  filter_upwards [hintervalγ, hintervalw, hpre] with t htγ htw htO
  have hy : IntrinsicGeodesic.LocalGeodesic.curve γ t ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    change (extChartAt I x₀).symm (γ.solution.coordinate t) ∈
      (extChartAt I x₀).source
    exact (extChartAt I x₀).map_target (γ.solution.coordinate_mem_target t htγ)
  have hframe : ∀ i : IntrinsicAcceleration.FrameIndex E,
      ∀ᶠ z in 𝓝 (IntrinsicGeodesic.LocalGeodesic.curve γ t),
        S i z = (trivializationAt E TM x₀).localFrame b i z := by
    intro i
    filter_upwards [hOopen.mem_nhds htO] with z hz
    exact Set.mem_iInter.mp (hOsub hz) i
  have hframeAt : ∀ i : IntrinsicAcceleration.FrameIndex E,
      S i (IntrinsicGeodesic.LocalGeodesic.curve γ t) =
        (trivializationAt E TM x₀).localFrame b i
          (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
    intro i
    have h : ∀ᶠ z in 𝓝 (IntrinsicGeodesic.LocalGeodesic.curve γ t),
        S i z = (trivializationAt E TM x₀).localFrame b i z := hframe i
    exact h.self_of_nhds
  have hmem : IntrinsicGeodesic.LocalGeodesic.curve γ t ∈
      IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) x₀ b := by
    refine ⟨?_, ?_⟩
    · simpa [IntrinsicGeodesic.LocalGeodesic.curve] using hy
    · simpa [S] using hframeAt
  have hvelocity :
      IntrinsicAcceleration.frameField (I := I) (M := M) b S
        (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀)
        b (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
    simpa [S] using frameField_eq_coordinateFrameCombination_of_mem_agreement
      (I := I) (M := M) x₀ b (γ.solution.velocity t) hmem
  have hraw := LocalGeodesicData.curve_derivative_velocity
    (I := I) (M := M) (E := E) (H := H) cov x₀ b γ.solution htγ
  have hcurve : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (IntrinsicGeodesic.LocalGeodesic.curve γ) t
      (timeTangentMap (I := I) t
        (IntrinsicAcceleration.frameField (I := I) (M := M) b S
          (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t))) := by
    rw [timeTangentMap_eq_toSpanSingleton, hvelocity]
    exact hraw
  have hwderiv : HasDerivAt wsol.curve (deriv wsol.curve t) t := by
    have htw' : t ∈ Ioo (0 - wsol.radius) (0 + wsol.radius) := by
      simpa only [zero_sub, zero_add] using htw
    rw [(wsol.hasDeriv t htw').deriv]
    exact wsol.hasDeriv t htw'
  have hcoeff : ∀ i, HasDerivAt (fun s ↦ b.repr (wsol.curve s) i)
      (b.repr (deriv wsol.curve t) i) t := by
    intro i
    have hc : HasDerivAt (fun _ : ℝ ↦ (b.coord i).toContinuousLinearMap) 0 t :=
      hasDerivAt_const t (b.coord i).toContinuousLinearMap
    simpa using hc.clm_apply hwderiv
  have hS : ∀ i, MDiffAt (T% (S i))
      (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
    intro i
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M) x₀ b i _
  have hacc := isCovariantAccelerationAt_timeFrameField_of_velocity
    (I := I) (M := M) cov b S wsol.curve (fun s ↦ deriv wsol.curve s)
    (IntrinsicGeodesic.LocalGeodesic.curve γ) hcurve hcoeff hS hmetric
  have hcov := LocalGeodesicData.cov_smoothFrameField_apply_eq_coordinateParallelOperator
    (I := I) (M := M) (E := E) cov x₀
    (IntrinsicGeodesic.LocalGeodesic.curve γ t) b
    (γ.solution.velocity t) (wsol.curve t) hy hframe
  have hderiv : deriv wsol.curve t = -(A t) (wsol.curve t) := by
    have htw' : t ∈ Ioo (0 - wsol.radius) (0 + wsol.radius) := by
      simpa only [zero_sub, zero_add] using htw
    exact (wsol.hasDeriv t htw').deriv
  have hchart : (extChartAt I x₀) (IntrinsicGeodesic.LocalGeodesic.curve γ t) =
      γ.solution.coordinate t :=
    LocalChartSecondOrderSolution.curve_eq_chart γ.solution htγ
  have hcov' : cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S
      (wsol.curve t)) (IntrinsicGeodesic.LocalGeodesic.curve γ t)
      (IntrinsicAcceleration.frameField (I := I) (M := M) b S
        (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t)) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        ((A t) (wsol.curve t)) (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
    dsimp [A]
    rw [← hchart]
    simpa [S] using hcov
  have hderivField : IntrinsicAcceleration.frameField (I := I) (M := M) b S
      (deriv wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (deriv wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
    simpa [S] using frameField_eq_coordinateFrameCombination_of_mem_agreement
      (I := I) (M := M) x₀ b (deriv wsol.curve t) hmem
  have hzeroField :
      IntrinsicAcceleration.frameField (I := I) (M := M) b S
        (deriv wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (wsol.curve t))
        (IntrinsicGeodesic.LocalGeodesic.curve γ t)
        (IntrinsicAcceleration.frameField (I := I) (M := M) b S
          (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t)) = 0 := by
    rw [hderivField, hcov', hderiv]
    rw [LocalGeodesicData.coordinateFrameCombination_neg]
    exact neg_add_cancel _
  change IsCovariantAccelerationAt cov (IntrinsicGeodesic.LocalGeodesic.curve γ)
    (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S
      wsol.curve s (IntrinsicGeodesic.LocalGeodesic.curve γ s)) t
    (IntrinsicAcceleration.frameField (I := I) (M := M) b S
      (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t)) 0
  rw [← hzeroField]
  exact hacc

/-- Multiplying a canonical parallel field by a differentiable scalar produces
the expected intrinsic covariant derivative.  The proof supplies the scalar
pairing regularity from the actual time-frame construction, so it does not
silently treat a dependent tangent-bundle field as an ordinary vector-valued
function. -/
theorem eventually_isCovariantAccelerationAt_smul_canonicalFrameParallel
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (f df : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (df t) t)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      IsCovariantAccelerationAt cov (IntrinsicGeodesic.LocalGeodesic.curve γ)
        (fun s ↦ f s • canonicalFrameParallel (I := I) (M := M) γ wsol s) t
        (CurveConnection.canonicalFrameVelocity γ t)
        (df t • canonicalFrameParallel (I := I) (M := M) γ wsol t) := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  let S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x := fun i =>
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i
  have hparallel :=
    eventually_isCovariantAccelerationAt_canonicalFrameParallel_zero
      (I := I) (M := M) γ wsol hmetric
  have hcurve :=
    CurveConnection.localGeodesic_eventually_hasMFDerivAt_curve_canonicalFrameVelocity
      (I := I) (M := M) γ
  have hintervalw : Ioo (-wsol.radius) wsol.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [wsol.radius_pos])
      (by linarith [wsol.radius_pos])
  filter_upwards [hparallel, hcurve, hintervalw] with t hparallel hcurve htw
  have htw' : t ∈ Ioo (0 - wsol.radius) (0 + wsol.radius) := by
    simpa only [zero_sub, zero_add] using htw
  have hwderiv : HasDerivAt wsol.curve (deriv wsol.curve t) t := by
    rw [(wsol.hasDeriv t htw').deriv]
    exact wsol.hasDeriv t htw'
  have hS : ∀ i, MDiffAt (T% (S i))
      (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
    intro i
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M) x₀ b i _
  have hscalar : ∀ W : (x : M) → TM x,
      MDiffAt (T% W) (IntrinsicGeodesic.LocalGeodesic.curve γ t) →
        MDiffAt (fun s ↦ inner ℝ
          (canonicalFrameParallel (I := I) (M := M) γ wsol s)
          (W (IntrinsicGeodesic.LocalGeodesic.curve γ s))) t := by
    intro W hW
    change MDiffAt (fun s ↦ inner ℝ
      (IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S
        wsol.curve s (IntrinsicGeodesic.LocalGeodesic.curve γ s))
      (W (IntrinsicGeodesic.LocalGeodesic.curve γ s))) t
    apply CurveConnection.mdiffAt_inner_timeFrameField_section
      (I := I) (M := M) b S wsol.curve
      (IntrinsicGeodesic.LocalGeodesic.curve γ) hcurve
    · intro i
      have hc : HasDerivAt (fun _ : ℝ ↦
          (b.coord i).toContinuousLinearMap) 0 t :=
        hasDerivAt_const t (b.coord i).toContinuousLinearMap
      exact (hc.clm_apply hwderiv).differentiableAt
    · exact hS
    · exact hW
  have hmul := hparallel.smul (hf t).differentiableAt.mdifferentiableAt hscalar
  have hdf : CurveConnection.curveScalarDeriv f t = df t :=
    CurveConnection.curveScalarDeriv_eq_of_hasDerivAt (hf t)
  rw [hdf] at hmul
  simpa [CurveConnection.canonicalFrameVelocity,
    IntrinsicAcceleration.timeFrameField,
    IntrinsicAcceleration.frameField] using hmul

/-- The canonical local parallel field has zero frame-coordinate covariant
acceleration on a genuine neighbourhood of its initial time.  This exposes
the explicit equation consumed by the two-frame uniqueness theorem, while
the velocity remains the intrinsic tangent-valued velocity of the curve. -/
theorem eventually_canonicalFrameParallel_frameAcceleration_eq_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∀ᶠ t in 𝓝 (0 : ℝ),
      IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
          (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (deriv wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
          (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (wsol.curve t)) (IntrinsicGeodesic.LocalGeodesic.curve γ t)
        (CurveConnection.canonicalFrameVelocity γ t) = 0 := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  let S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x := fun i =>
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀ b i
  have hparallel :=
    eventually_isCovariantAccelerationAt_canonicalFrameParallel_zero
      (I := I) (M := M) γ wsol hmetric
  have hcurve :=
    CurveConnection.localGeodesic_eventually_hasMFDerivAt_curve_canonicalFrameVelocity
      (I := I) (M := M) γ
  have hintervalw : Ioo (-wsol.radius) wsol.radius ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith [wsol.radius_pos])
      (by linarith [wsol.radius_pos])
  change ∀ᶠ t in 𝓝 (0 : ℝ),
    IntrinsicAcceleration.frameField (I := I) (M := M) b S
      (deriv wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S
        (wsol.curve t)) (IntrinsicGeodesic.LocalGeodesic.curve γ t)
        (CurveConnection.canonicalFrameVelocity γ t) = 0
  filter_upwards [hparallel, hcurve, hintervalw] with t hparallel hcurve htw
  have htw' : t ∈ Ioo (0 - wsol.radius) (0 + wsol.radius) := by
    simpa only [zero_sub, zero_add] using htw
  have hwderiv : HasDerivAt wsol.curve (deriv wsol.curve t) t := by
    rw [(wsol.hasDeriv t htw').deriv]
    exact wsol.hasDeriv t htw'
  have hcoeff : ∀ i, HasDerivAt (fun s ↦ b.repr (wsol.curve s) i)
      (b.repr (deriv wsol.curve t) i) t := by
    intro i
    have hc : HasDerivAt (fun _ : ℝ ↦ (b.coord i).toContinuousLinearMap) 0 t :=
      hasDerivAt_const t (b.coord i).toContinuousLinearMap
    simpa using hc.clm_apply hwderiv
  have hS : ∀ i, MDiffAt (T% (S i))
      (IntrinsicGeodesic.LocalGeodesic.curve γ t) := by
    intro i
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M) x₀ b i _
  have hacc := isCovariantAccelerationAt_timeFrameField_of_velocity
    (I := I) (M := M) cov b S wsol.curve (fun s ↦ deriv wsol.curve s)
    (IntrinsicGeodesic.LocalGeodesic.curve γ) hcurve hcoeff hS hmetric
  change IsCovariantAccelerationAt cov (IntrinsicGeodesic.LocalGeodesic.curve γ)
    (fun s ↦ IntrinsicAcceleration.timeFrameField (I := I) (M := M) b S
      wsol.curve s (IntrinsicGeodesic.LocalGeodesic.curve γ s)) t
    (CurveConnection.canonicalFrameVelocity γ t) 0 at hparallel
  exact IsCovariantAccelerationAt.unique hacc hparallel

/-- The explicit parallel equation holds on a nonempty interval, not merely
as a filter germ.  The radius is exposed for the interval uniqueness theorem
that compares two frame descriptions after a local geodesic restart. -/
theorem exists_interval_canonicalFrameParallel_frameAcceleration_eq_zero
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ r > (0 : ℝ), ∀ t ∈ Ioo (-r) r,
      IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
          (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (deriv wsol.curve t) (IntrinsicGeodesic.LocalGeodesic.curve γ t) +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
          (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (wsol.curve t)) (IntrinsicGeodesic.LocalGeodesic.curve γ t)
        (CurveConnection.canonicalFrameVelocity γ t) = 0 := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (eventually_canonicalFrameParallel_frameAcceleration_eq_zero
      (I := I) (M := M) γ wsol hmetric)
  refine ⟨r, hr, ?_⟩
  intro t ht
  apply hsub
  rw [Metric.mem_ball]
  simpa [dist_zero_right, abs_lt] using ht

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- Coordinate parallel solutions with the same initial coefficient determine
the same tangent-valued parallel-field germ.  This is the uniqueness datum
needed when local transport certificates are later glued across a cover of a
global geodesic. -/
theorem canonicalFrameParallel_eventuallyEq_of_same_initial
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol₁ wsol₂ : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    (canonicalFrameParallel (I := I) (M := M) γ wsol₁) =ᶠ[𝓝 (0 : ℝ)]
      canonicalFrameParallel (I := I) (M := M) γ wsol₂ := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hF := LocalGeodesicData.coordinateAcceleration_system_contDiffAt
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
    (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ v₀)
  have hA : ContDiffAt ℝ 1
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 := by
    simpa [b] using
      LocalGeodesicData.coordinateParallelOperator_contDiffAt_along_localChartSolution
        (I := I) (M := M) (E := E) cov x₀ b γ.solution hF
  have hcoeff := LocalLinearTransportSolution.eventuallyEq_of_same_initial
    wsol₁ wsol₂ hA
  filter_upwards [hcoeff] with t ht
  unfold canonicalFrameParallel
  unfold IntrinsicAcceleration.timeFrameField
  rw [ht]

/-- Canonical parallel transport is independent, as a tangent-bundle germ, of
the particular local-geodesic certificate chosen for fixed initial state.  The
proof first identifies the two coordinate geodesic germs, then invokes linear
transport uniqueness only after their coefficient operators have been proved
to agree. -/
theorem canonicalFrameParallel_eventuallyEq_totalState_of_same_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ₁ γ₂ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol₁ : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ₁.solution.coordinate t) (γ₁.solution.velocity t)) 0 w₀)
    (wsol₂ : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ₂.solution.coordinate t) (γ₂.solution.velocity t)) 0 w₀) :
    (fun t ↦ (⟨IntrinsicGeodesic.LocalGeodesic.curve γ₁ t,
      IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
        (I := I) (M := M) γ₁ wsol₁ t⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))) =ᶠ[𝓝 (0 : ℝ)]
      fun t ↦ (⟨IntrinsicGeodesic.LocalGeodesic.curve γ₂ t,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) γ₂ wsol₂ t⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hcoords := LocalGeodesicData.coordinateGeodesic_eventuallyEq_of_same_initial
    (I := I) (M := M) (E := E) (H := H) cov x₀ b γ₁.solution γ₂.solution
  have hF := LocalGeodesicData.coordinateAcceleration_system_contDiffAt
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
    (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ v₀)
  have hA : ContDiffAt ℝ 1
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ₁.solution.coordinate t) (γ₁.solution.velocity t)) 0 := by
    simpa [b] using
      LocalGeodesicData.coordinateParallelOperator_contDiffAt_along_localChartSolution
        (I := I) (M := M) (E := E) cov x₀ b γ₁.solution hF
  have hAeq :
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ₁.solution.coordinate t) (γ₁.solution.velocity t)) =ᶠ[𝓝 (0 : ℝ)]
        fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
          (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
          (γ₂.solution.coordinate t) (γ₂.solution.velocity t) := by
    filter_upwards [hcoords] with t ht
    have hcoordinate : γ₁.solution.coordinate t = γ₂.solution.coordinate t := by
      simpa using congrArg Prod.fst ht
    have hvelocity : γ₁.solution.velocity t = γ₂.solution.velocity t := by
      simpa using congrArg Prod.snd ht
    rw [hcoordinate, hvelocity]
  have htransport :=
    LocalLinearTransportSolution.eventuallyEq_of_same_initial_of_eventuallyEq
      wsol₁ wsol₂ hA hAeq
  obtain ⟨hcurve, _⟩ :=
    IntrinsicGeodesic.eventuallyEq_curve_velocity_of_same_initial
      (I := I) (M := M) (E := E) (H := H) cov x₀ v₀ γ₁ γ₂
  have htimeFrame : ∀ {f g : ℝ → E} {s : ℝ} {y z : M}, f s = g s → y = z →
      HEq
        (IntrinsicAcceleration.timeFrameField (I := I) (M := M)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
            x₀ (IntrinsicGeodesic.canonicalBasis (E := E)) i) f s y)
        (IntrinsicAcceleration.timeFrameField (I := I) (M := M)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
            x₀ (IntrinsicGeodesic.canonicalBasis (E := E)) i) g s z) := by
    intro f g s y z hfg hyz
    subst z
    exact heq_of_eq (by simp [IntrinsicAcceleration.timeFrameField, hfg])
  filter_upwards [hcurve, htransport] with t htcurve httransport
  apply Bundle.TotalSpace.ext htcurve
  change HEq
    (IntrinsicAcceleration.timeFrameField (I := I) (M := M)
      (IntrinsicGeodesic.canonicalBasis (E := E))
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
        x₀ (IntrinsicGeodesic.canonicalBasis (E := E)) i)
      wsol₁.curve t (IntrinsicGeodesic.LocalGeodesic.curve γ₁ t))
    (IntrinsicAcceleration.timeFrameField (I := I) (M := M)
      (IntrinsicGeodesic.canonicalBasis (E := E))
      (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
        x₀ (IntrinsicGeodesic.canonicalBasis (E := E)) i)
      wsol₂.curve t (IntrinsicGeodesic.LocalGeodesic.curve γ₂ t))
  exact htimeFrame httransport htcurve

/-- If a canonical parallel field has the actual geodesic velocity as its
initial tangent vector, then its model initial coefficient is the coordinate
velocity of the local geodesic.  This is the fibrewise injectivity step needed
to apply uniqueness of the linear transport equation without identifying a
tangent fibre with the model space by definition. -/
theorem canonicalFrameParallel_coordinate_initial_eq_velocity
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (hinit : canonicalFrameParallel (I := I) (M := M) γ wsol 0 =
      IntrinsicGeodesic.LocalGeodesic.velocity γ 0) :
    w₀ = γ.solution.velocity 0 := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hframe :
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀)
        b w₀ x₀ =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M) (x₀ := x₀)
        b (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ v₀) x₀ := by
    rw [← canonicalFrameParallel_initial (I := I) (M := M) γ wsol]
    rw [hinit, IntrinsicGeodesic.LocalGeodesic.velocity_initial]
    symm
    exact LocalGeodesicData.coordinateFrameCombination_coordinateVelocity
      (I := I) (M := M) (E := E) x₀ b v₀
  have hxsource : x₀ ∈ (extChartAt I x₀).source := by
    rw [extChartAt_source]
    exact mem_chart_source H x₀
  have hinj := CurveConnection.coordinateFrameLinear_injective_of_mem_source
    (I := I) (M := M) x₀ b hxsource
  have hcoord : w₀ = LocalGeodesicData.coordinateVelocity (I := I) (M := M)
      (E := E) x₀ v₀ := by
    apply hinj
    simpa [IntrinsicAcceleration.coordinateFrameLinear,
      IntrinsicAcceleration.coordinateFrameVector] using hframe
  rw [hcoord, γ.solution.velocity_initial]

/-- A canonical local parallel field initialized with the actual geodesic
velocity agrees with that velocity as a genuine tangent-valued germ.  The
proof uses coefficient uniqueness only after the preceding fibrewise
identification, then combines it with the separately established geometric
identification of the velocity solution. -/
theorem canonicalFrameParallel_eventuallyEq_velocity_of_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀)
    (hinit : canonicalFrameParallel (I := I) (M := M) γ wsol 0 =
      IntrinsicGeodesic.LocalGeodesic.velocity γ 0) :
    (canonicalFrameParallel (I := I) (M := M) γ wsol) =ᶠ[𝓝 (0 : ℝ)]
      IntrinsicGeodesic.LocalGeodesic.velocity γ := by
  have hcoordinate := canonicalFrameParallel_coordinate_initial_eq_velocity
    (I := I) (M := M) γ wsol hinit
  subst w₀
  have heq := canonicalFrameParallel_eventuallyEq_of_same_initial
    (I := I) (M := M) γ wsol
      (velocityParallelSolution (I := I) (M := M) γ)
  obtain ⟨r, hr, hvelocity⟩ :=
    canonicalFrameParallel_velocity_eq_velocity_near_zero
      (I := I) (M := M) γ
  have hinter : Ioo (-r) r ∈ 𝓝 (0 : ℝ) := by
    exact Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [heq, hinter] with t htransport ht
  calc
    canonicalFrameParallel (I := I) (M := M) γ wsol t =
        canonicalFrameParallel (I := I) (M := M) γ
          (velocityParallelSolution (I := I) (M := M) γ) t := htransport
    _ = IntrinsicGeodesic.LocalGeodesic.velocity γ t := hvelocity t ht

/-- Every tangent vector at the start of a local geodesic has a genuine local
parallel extension.  The conclusion packages both pieces needed by later
continuation: its prescribed initial value and its intrinsic zero covariant
derivative (rather than merely a coordinate ODE certificate). -/
theorem exists_canonicalFrameParallel
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (w : TM x₀) (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ w),
      canonicalFrameParallel (I := I) (M := M) γ wsol 0 = w ∧
      ∀ᶠ t in 𝓝 (0 : ℝ),
        IsCovariantAccelerationAt cov (IntrinsicGeodesic.LocalGeodesic.curve γ)
          (canonicalFrameParallel (I := I) (M := M) γ wsol) t
          (IntrinsicAcceleration.frameField (I := I) (M := M)
            (IntrinsicGeodesic.canonicalBasis (E := E))
            (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E) x₀
              (IntrinsicGeodesic.canonicalBasis (E := E)) i)
            (γ.solution.velocity t) (IntrinsicGeodesic.LocalGeodesic.curve γ t)) 0 := by
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hF := LocalGeodesicData.coordinateAcceleration_system_contDiffAt
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
    (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ v₀)
  obtain ⟨wsol⟩ := LocalGeodesicData.exists_local_coordinate_parallel_field
    (I := I) (M := M) (E := E) (H := H) cov x₀ b γ.solution hF
    (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ w)
  refine ⟨wsol, ?_, ?_⟩
  · exact canonicalFrameParallel_initial_of_coordinateVelocity
      (I := I) (M := M) γ w wsol
  · exact eventually_isCovariantAccelerationAt_canonicalFrameParallel_zero
      (I := I) (M := M) γ wsol hmetric

/-- The tangent-bundle total state of a canonical local parallel field is
continuous at its initial time.  This is stronger than continuity of scalar
pairings: the proof reads the field through the actual tangent-bundle
trivialization and identifies that readout with its linear transport ODE.
It is the local regularity input needed to pass curvature expressions from
smooth local frames to globally glued parallel fields. -/
theorem continuousAt_canonicalFrameParallel_totalState_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {w₀ : E}
    (wsol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0 w₀) :
    ContinuousAt (fun s ↦
      (⟨IntrinsicGeodesic.LocalGeodesic.curve γ s,
        canonicalFrameParallel (I := I) (M := M) γ wsol s⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _))) 0 := by
  let F : ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _) := fun s ↦
    ⟨IntrinsicGeodesic.LocalGeodesic.curve γ s,
      canonicalFrameParallel (I := I) (M := M) γ wsol s⟩
  change ContinuousAt F 0
  have hzero : (0 : ℝ) ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [γ.solution.radius_pos]
  apply (FiberBundle.continuousAt_totalSpace E F).mpr
  constructor
  · change ContinuousAt (IntrinsicGeodesic.LocalGeodesic.curve γ) 0
    exact (IntrinsicGeodesic.LocalGeodesic.hasMFDerivAt_curve γ hzero).continuousAt
  · obtain ⟨r, hr, hradius, hfield⟩ :=
      canonicalFrameParallel_eq_coordinateFrameCombination_near_zero
        (I := I) (M := M) γ wsol
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Ioo (-r) r :=
      Ioo_mem_nhds (by linarith [hr]) (by linarith [hr])
    have hcoord : (fun s ↦ ((trivializationAt E
        (TangentSpace I : M → Type _) x₀) (F s)).2) =ᶠ[𝓝 (0 : ℝ)]
        wsol.curve := by
      filter_upwards [hsmall] with s hs
      have htsol : s ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
        have hle : r ≤ γ.solution.radius :=
          le_trans hradius (min_le_left _ _)
        exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
          lt_of_lt_of_le hs.2 hle⟩
      have htarget := γ.solution.coordinate_mem_target s htsol
      have hsource : IntrinsicGeodesic.LocalGeodesic.curve γ s ∈
          (chartAt H x₀).source := by
        rw [← extChartAt_source (I := I) x₀]
        change (extChartAt I x₀).symm (γ.solution.coordinate s) ∈
          (extChartAt I x₀).source
        exact (extChartAt I x₀).map_target htarget
      have hbase : IntrinsicGeodesic.LocalGeodesic.curve γ s ∈
          (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
        rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) x₀,
          ← extChartAt_source (I := I) x₀]
        rw [← extChartAt_source (I := I) x₀] at hsource
        exact hsource
      change ((trivializationAt E (TangentSpace I : M → Type _) x₀)
          ⟨IntrinsicGeodesic.LocalGeodesic.curve γ s,
            canonicalFrameParallel (I := I) (M := M) γ wsol s⟩).2 =
          wsol.curve s
      rw [hfield s hs,
        LocalGeodesicData.coordinateFrameCombination_eq_symmL
          (I := I) (M := M) (x₀ := x₀)
          (IntrinsicGeodesic.canonicalBasis (E := E)) hsource]
      let e := trivializationAt E (TangentSpace I : M → Type _) x₀
      calc
        (e ⟨IntrinsicGeodesic.LocalGeodesic.curve γ s,
          e.symmL ℝ (IntrinsicGeodesic.LocalGeodesic.curve γ s)
            (wsol.curve s)⟩).2 =
            e.continuousLinearMapAt ℝ
              (IntrinsicGeodesic.LocalGeodesic.curve γ s)
              (e.symmL ℝ (IntrinsicGeodesic.LocalGeodesic.curve γ s)
                (wsol.curve s)) := by
              rw [e.apply_eq_prod_continuousLinearEquivAt ℝ
                (IntrinsicGeodesic.LocalGeodesic.curve γ s) hbase]
              rw [e.coe_continuousLinearEquivAt_eq hbase]
        _ = wsol.curve s :=
          e.continuousLinearMapAt_symmL hbase (wsol.curve s)
    have hvalue : ContinuousAt wsol.curve 0 :=
      (wsol.hasDeriv 0 (by
        constructor <;> linarith [wsol.radius_pos])).continuousAt
    have hstate0 : (F 0).proj = x₀ := by
      change IntrinsicGeodesic.LocalGeodesic.curve γ 0 = x₀
      exact IntrinsicGeodesic.LocalGeodesic.curve_initial γ
    rw [hstate0]
    exact hvalue.congr_of_eventuallyEq hcoord

/-- A finite family of prescribed tangent vectors extends to canonical local
parallel fields with a common Gram-preserving interval.  The individual
parallel equations remain available through
`eventually_isCovariantAccelerationAt_canonicalFrameParallel_zero`; this
theorem adds the uniform finite-family radius required for a parallel frame. -/
theorem exists_canonicalFrameParallel_family
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (γ : IntrinsicGeodesic.LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (w : ι → TM x₀)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1] :
    ∃ wsol : ∀ i, LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ (w i)),
      (∀ i, canonicalFrameParallel (I := I) (M := M) γ (wsol i) 0 = w i) ∧
      ∃ r > (0 : ℝ), ∀ i j t, t ∈ Ioo (-r) r →
        inner ℝ (canonicalFrameParallel (I := I) (M := M) γ (wsol i) t)
          (canonicalFrameParallel (I := I) (M := M) γ (wsol j) t) =
        inner ℝ (w i) (w j) := by
  classical
  have hsol : ∀ i, ∃ sol : LocalLinearTransportSolution
      (fun t ↦ LocalGeodesicData.coordinateParallelOperator (I := I) (M := M)
        (E := E) cov x₀ (IntrinsicGeodesic.canonicalBasis (E := E))
        (γ.solution.coordinate t) (γ.solution.velocity t)) 0
      (LocalGeodesicData.coordinateVelocity (I := I) (M := M) (E := E) x₀ (w i)),
      canonicalFrameParallel (I := I) (M := M) γ sol 0 = w i := by
    intro i
    obtain ⟨sol, hinit, _⟩ := exists_canonicalFrameParallel
      (I := I) (M := M) γ (w i) hmetric
    exact ⟨sol, hinit⟩
  choose wsol hinit using hsol
  obtain ⟨r, hr, hgram⟩ :=
    canonicalFrameParallel_finite_inner_constant_near_zero
      (I := I) (M := M) γ wsol hmetric
  refine ⟨wsol, hinit, r, hr, ?_⟩
  intro i j t ht
  calc
    inner ℝ (canonicalFrameParallel (I := I) (M := M) γ (wsol i) t)
        (canonicalFrameParallel (I := I) (M := M) γ (wsol j) t) =
      inner ℝ (canonicalFrameParallel (I := I) (M := M) γ (wsol i) 0)
        (canonicalFrameParallel (I := I) (M := M) γ (wsol j) 0) := hgram i j t ht
    _ = inner ℝ (w i) (w j) := by
      rw [IntrinsicGeodesic.LocalGeodesic.curve_initial γ]
      rw [hinit i, hinit j]

end IntrinsicGeodesic.LocalGeodesic

end BonnetMyersEntry
