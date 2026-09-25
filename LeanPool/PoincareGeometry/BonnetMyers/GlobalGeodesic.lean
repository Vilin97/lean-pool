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

public import LeanPool.PoincareGeometry.BonnetMyers.ChartGluing
public import LeanPool.PoincareGeometry.BonnetMyers.GeodesicContinuation
public import LeanPool.PoincareGeometry.BonnetMyers.GeodesicLength
public import LeanPool.PoincareGeometry.BonnetMyers.GlobalDistance

/-!
# Maximal intrinsic geodesic extensions

This module packages locally defined geodesic states in a form suitable for
Zorn's lemma.  The state lives in the tangent bundle, rather than carrying a
dependent family of tangent vectors separately.  Consequently the union of a
chain has a literal, chart-independent state on every overlap.

The analytic endpoint argument is kept separate from this order-theoretic
layer.  It will supply the strict-extension hypothesis used by the final
globalization theorem below.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

namespace IntrinsicGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-- The tangent-bundle-valued state of a local geodesic. -/
def localState
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    {x₀ : M} {v₀ : TangentSpace I x₀}
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _) :=
  fun t ↦ ⟨LocalGeodesic.curve γ t, LocalGeodesic.velocity γ t⟩

/-- In the preferred tangent trivialization, a local geodesic state's fibre
coordinate is exactly the coordinate ODE velocity. -/
private theorem coordinate_readout_localState
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    {x₀ : M} {v₀ : TangentSpace I x₀}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    {s : ℝ} (hs : s ∈ Ioo (-γ.solution.radius) γ.solution.radius) :
    ((trivializationAt E (TangentSpace I : M → Type _) x₀)
      (localState γ s)).2 = γ.solution.velocity s := by
  have htarget := γ.solution.coordinate_mem_target s hs
  have hsource : LocalGeodesic.curve γ s ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    simpa [LocalGeodesic.curve, LocalChartSecondOrderSolution.curve] using
      (extChartAt I x₀).map_target htarget
  have hsourceSol : γ.solution.curve s ∈ (chartAt H x₀).source := by
    simpa [LocalGeodesic.curve] using hsource
  have hvel := LocalGeodesicData.tangentField_eq_coordinateFrameCombination
    (I := I) (M := M) (E := E) cov x₀ (canonicalBasis (E := E))
      γ.solution γ.solution.velocity hs
  change (trivializationAt E (TangentSpace I : M → Type _) x₀
    ⟨γ.solution.curve s,
      LocalGeodesicData.tangentField cov x₀ (canonicalBasis (E := E))
        γ.solution γ.solution.velocity s⟩).2 = γ.solution.velocity s
  rw [hvel,
    LocalGeodesicData.coordinateFrameCombination_eq_symmL
      (I := I) (M := M) (x₀ := x₀) (canonicalBasis (E := E)) hsourceSol]
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have he : γ.solution.curve s ∈ e.baseSet := by
    change γ.solution.curve s ∈ (chartAt H x₀).source
    exact hsourceSol
  calc
    (e ⟨γ.solution.curve s,
      e.symmL ℝ (γ.solution.curve s) (γ.solution.velocity s)⟩).2 =
        e.continuousLinearEquivAt ℝ (γ.solution.curve s) he
          (e.symmL ℝ (γ.solution.curve s) (γ.solution.velocity s)) := by
      rw [e.apply_eq_prod_continuousLinearEquivAt ℝ (γ.solution.curve s) he]
    _ = e.continuousLinearMapAt ℝ (γ.solution.curve s)
          (e.symmL ℝ (γ.solution.curve s) (γ.solution.velocity s)) := by
      rw [e.coe_continuousLinearEquivAt_eq he]
    _ = γ.solution.velocity s :=
      e.continuousLinearMapAt_symmL he (γ.solution.velocity s)

/-- A local geodesic state is continuous at its initial time. -/
theorem continuousAt_localState_zero
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    {x₀ : M} {v₀ : TangentSpace I x₀}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    ContinuousAt (localState γ) 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [γ.solution.radius_pos]
  apply (FiberBundle.continuousAt_totalSpace E (localState γ)).mpr
  constructor
  · change ContinuousAt (LocalGeodesic.curve γ) 0
    exact (LocalGeodesic.hasMFDerivAt_curve γ hzero).continuousAt
  · have hvel : ContinuousAt γ.solution.velocity 0 :=
      (γ.solution.velocity_hasDeriv 0 hzero).continuousAt
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ),
        s ∈ Ioo (-γ.solution.radius) γ.solution.radius :=
      Ioo_mem_nhds (by linarith [γ.solution.radius_pos])
        (by linarith [γ.solution.radius_pos])
    have hcoord :
        (fun s ↦ ((trivializationAt E (TangentSpace I : M → Type _) x₀)
          (localState γ s)).2) =ᶠ[𝓝 (0 : ℝ)] γ.solution.velocity := by
      filter_upwards [hsmall] with s hs
      exact coordinate_readout_localState γ hs
    have hstate0 : (localState γ 0).proj = x₀ := by
      change LocalGeodesic.curve γ 0 = x₀
      exact LocalGeodesic.curve_initial γ
    rw [hstate0]
    exact hvel.congr_of_eventuallyEq hcoord

/-- On a sufficiently small interval, the actual tangent norm of a packaged
local geodesic is the norm of its initial tangent.  This is the intrinsic
finite-speed form of the local energy law. -/
theorem exists_local_norm_velocity_eq_initial
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {x₀ : M} {v₀ : TangentSpace I x₀}
    (γ : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), r ≤ γ.solution.radius ∧
      ∀ t ∈ Ioo (-r) r, ‖LocalGeodesic.velocity γ t‖ = ‖v₀‖ := by
  obtain ⟨r, hr, hrsol, hspeed⟩ :=
    LocalGeodesicData.local_speed_is_constant_near_zero
      (I := I) (M := M) (E := E) (H := H) cov x₀
        (canonicalBasis (E := E)) γ.solution hmetric
  refine ⟨r, hr, hrsol, ?_⟩
  intro t ht
  have htSol : t ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor
    · exact lt_of_le_of_lt (neg_le_neg hrsol) ht.1
    · exact lt_of_lt_of_le ht.2 hrsol
  have hvelT : LocalGeodesic.velocity γ t =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) (canonicalBasis (E := E)) (γ.solution.velocity t)
        (LocalGeodesic.curve γ t) := by
    rw [LocalGeodesic.velocity]
    simpa [LocalGeodesic.curve] using
      LocalGeodesicData.tangentField_eq_coordinateFrameCombination
        (I := I) (M := M) (E := E) (H := H) cov x₀
          (canonicalBasis (E := E)) γ.solution γ.solution.velocity htSol
  have hzeroSol : (0 : ℝ) ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [γ.solution.radius_pos]
  have hvel0 : LocalGeodesic.velocity γ 0 =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) (canonicalBasis (E := E)) (γ.solution.velocity 0)
        (LocalGeodesic.curve γ 0) := by
    rw [LocalGeodesic.velocity]
    simpa [LocalGeodesic.curve] using
      LocalGeodesicData.tangentField_eq_coordinateFrameCombination
        (I := I) (M := M) (E := E) (H := H) cov x₀
          (canonicalBasis (E := E)) γ.solution γ.solution.velocity hzeroSol
  have hsq : ‖LocalGeodesic.velocity γ t‖ ^ 2 =
      ‖LocalGeodesic.velocity γ 0‖ ^ 2 := by
    have hraw := hspeed t ht
    have hframeSq :
        ‖LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) (canonicalBasis (E := E)) (γ.solution.velocity t)
          (LocalChartSecondOrderSolution.curve γ.solution t)‖ ^ 2 =
        ‖LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
          (x₀ := x₀) (canonicalBasis (E := E)) (γ.solution.velocity 0)
          (LocalChartSecondOrderSolution.curve γ.solution 0)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact hraw
    rw [hvelT, hvel0]
    exact hframeSq
  have heq : ‖LocalGeodesic.velocity γ t‖ = ‖LocalGeodesic.velocity γ 0‖ := by
    nlinarith [norm_nonneg (LocalGeodesic.velocity γ t),
      norm_nonneg (LocalGeodesic.velocity γ 0)]
  calc
    ‖LocalGeodesic.velocity γ t‖ = ‖LocalGeodesic.velocity γ 0‖ := heq
    _ = ‖v₀‖ := by
      rw [LocalGeodesic.curve_initial γ]
      exact congrArg norm (LocalGeodesic.velocity_initial γ)

/-- A partial intrinsic geodesic.  Its state is defined on all times only to
make chain unions convenient; every geometric assertion is restricted to the
open connected `domain`. -/
structure PartialGeodesic
    (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
    (x₀ : M) (v₀ : TangentSpace I x₀) where
  domain : Set ℝ
  domain_open : IsOpen domain
  domain_preconnected : IsPreconnected domain
  zero_mem : (0 : ℝ) ∈ domain
  state : ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _)
  state_zero : state 0 = ⟨x₀, v₀⟩
  state_outside : ∀ t, t ∉ domain → state t = ⟨x₀, v₀⟩
  local_germ : ∀ t ∈ domain,
    ∃ γ : LocalGeodesic (I := I) (M := M) cov (state t).proj (state t).snd,
      (fun s ↦ state (t + s)) =ᶠ[𝓝 (0 : ℝ)] localState γ

/-- A geodesic state defined for all real times.  The local certificate makes
this a chart-independent geodesic rather than an arbitrary tangent-bundle
curve. -/
structure GlobalGeodesic
    (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
    (x₀ : M) (v₀ : TangentSpace I x₀) where
  state : ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _)
  state_zero : state 0 = ⟨x₀, v₀⟩
  local_germ : ∀ t,
    ∃ γ : LocalGeodesic (I := I) (M := M) cov (state t).proj (state t).snd,
      (fun s ↦ state (t + s)) =ᶠ[𝓝 (0 : ℝ)] localState γ

namespace GlobalGeodesic

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- The underlying manifold curve. -/
def curve (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) : ℝ → M :=
  fun t ↦ (γ.state t).proj

/-- The tangent vector along the underlying curve. -/
def velocity (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) : TangentSpace I (curve γ t) :=
  (γ.state t).snd

lemma curve_initial (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) :
    curve γ 0 = x₀ := by
  have h := congrArg Bundle.TotalSpace.proj γ.state_zero
  simpa [curve] using h

lemma velocity_initial (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) :
    velocity γ 0 = v₀ := by
  rw [velocity, γ.state_zero]

/-- Reverse a complete geodesic in time.  The tangent component is negated,
so the resulting state begins at the same base point with the opposite
velocity.  This is the global counterpart of `LocalGeodesic.reverse`; its
local certificate is rebuilt from the reversed local germs rather than
assuming time-reversal invariance at the global level. -/
noncomputable def reverse
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) :
    GlobalGeodesic (I := I) (M := M) cov x₀ (-v₀) where
  state := fun t ↦ ⟨(γ.state (-t)).proj, -(γ.state (-t)).snd⟩
  state_zero := by
    have hzero : -(0 : ℝ) = 0 := by ring
    rw [hzero, γ.state_zero]
  local_germ := by
    intro t
    obtain ⟨α, hα⟩ := γ.local_germ (-t)
    refine ⟨IntrinsicGeodesic.LocalGeodesic.reverse α, ?_⟩
    have hneg : Tendsto (fun s : ℝ ↦ -s) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun s : ℝ ↦ -s) 0 :=
        (continuousAt_id : ContinuousAt (fun s : ℝ ↦ s) 0).neg
      simpa using hcont.tendsto
    have hαneg := hα.comp_tendsto hneg
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ),
        s ∈ Ioo (-α.solution.radius) α.solution.radius :=
      Ioo_mem_nhds (by linarith [α.solution.radius_pos])
        (by linarith [α.solution.radius_pos])
    filter_upwards [hαneg, hsmall] with s hs hsr
    change γ.state (-t + -s) = IntrinsicGeodesic.localState α (-s) at hs
    have hvel := IntrinsicGeodesic.LocalGeodesic.reverse_actual_velocity α hsr
    change ⟨(γ.state (-(t + s))).proj, -(γ.state (-(t + s))).snd⟩ =
      IntrinsicGeodesic.localState (IntrinsicGeodesic.LocalGeodesic.reverse α) s
    rw [show -(t + s) = -t + -s by ring, hs]
    simp only [IntrinsicGeodesic.localState]
    rw [IntrinsicGeodesic.LocalGeodesic.reverse_curve, hvel]
    rfl

@[simp] lemma reverse_state
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    (reverse γ).state t = ⟨(γ.state (-t)).proj, -(γ.state (-t)).snd⟩ := rfl

@[simp] lemma reverse_curve
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    curve (reverse γ) t = curve γ (-t) := rfl

@[simp] lemma reverse_velocity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    velocity (reverse γ) t = -velocity γ (-t) := rfl

/-- Reverse a complete geodesic about an arbitrary time, retaining that time
as the exact initial base point.  Unlike `shift (reverse γ) (-t₀)`, this
definition has the source fibre `TM (curve γ t₀)` and the opposite source
velocity by construction, so it can be used to reflect parallel transport
without first hiding a dependent-fibre cast. -/
noncomputable def reverseAt
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ : ℝ) :
    GlobalGeodesic (I := I) (M := M) cov (curve γ t₀) (-velocity γ t₀) where
  state := fun s ↦ ⟨(γ.state (t₀ - s)).proj, -(γ.state (t₀ - s)).snd⟩
  state_zero := by
    change (⟨(γ.state (t₀ - 0)).proj, -(γ.state (t₀ - 0)).snd⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨(γ.state t₀).proj, -(γ.state t₀).snd⟩
    rw [sub_zero]
  local_germ := by
    intro t
    obtain ⟨α, hα⟩ := γ.local_germ (t₀ - t)
    refine ⟨IntrinsicGeodesic.LocalGeodesic.reverse α, ?_⟩
    have hneg : Tendsto (fun s : ℝ ↦ -s) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun s : ℝ ↦ -s) 0 :=
        (continuousAt_id : ContinuousAt (fun s : ℝ ↦ s) 0).neg
      simpa using hcont.tendsto
    have hαneg := hα.comp_tendsto hneg
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ),
        s ∈ Ioo (-α.solution.radius) α.solution.radius :=
      Ioo_mem_nhds (by linarith [α.solution.radius_pos])
        (by linarith [α.solution.radius_pos])
    filter_upwards [hαneg, hsmall] with s hs hsr
    change γ.state (t₀ - t + -s) = IntrinsicGeodesic.localState α (-s) at hs
    have hvel := IntrinsicGeodesic.LocalGeodesic.reverse_actual_velocity α hsr
    change ⟨(γ.state (t₀ - (t + s))).proj,
      -(γ.state (t₀ - (t + s))).snd⟩ =
      IntrinsicGeodesic.localState (IntrinsicGeodesic.LocalGeodesic.reverse α) s
    rw [show t₀ - (t + s) = t₀ - t + -s by ring, hs]
    simp only [IntrinsicGeodesic.localState]
    rw [IntrinsicGeodesic.LocalGeodesic.reverse_curve, hvel]
    rfl

@[simp] lemma reverseAt_state
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ s : ℝ) :
    (reverseAt γ t₀).state s =
      ⟨(γ.state (t₀ - s)).proj, -(γ.state (t₀ - s)).snd⟩ := rfl

@[simp] lemma reverseAt_curve
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ s : ℝ) :
    curve (reverseAt γ t₀) s = curve γ (t₀ - s) := rfl

@[simp] lemma reverseAt_velocity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ s : ℝ) :
    velocity (reverseAt γ t₀) s = -velocity γ (t₀ - s) := rfl

/-- Translate the time origin of a complete geodesic.  The definition retains
the whole tangent-bundle state, so the restarted curve has the exact tangent
state at its new origin rather than merely the same base-point germ. -/
noncomputable def shift
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ : ℝ) :
    GlobalGeodesic (I := I) (M := M) cov (curve γ t₀) (velocity γ t₀) where
  state := fun s ↦ γ.state (t₀ + s)
  state_zero := by
    change γ.state (t₀ + 0) = ⟨(γ.state t₀).proj, (γ.state t₀).snd⟩
    simp
  local_germ := by
    intro t
    obtain ⟨α, hα⟩ := γ.local_germ (t₀ + t)
    refine ⟨α, ?_⟩
    filter_upwards [hα] with s hs
    change γ.state (t₀ + (t + s)) = localState α s
    convert hs using 1 <;> ring_nf

@[simp] lemma shift_state
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ s : ℝ) :
    (shift γ t₀).state s = γ.state (t₀ + s) := rfl

@[simp] lemma shift_curve
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ s : ℝ) :
    curve (shift γ t₀) s = curve γ (t₀ + s) := rfl

@[simp] lemma shift_velocity
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t₀ s : ℝ) :
    velocity (shift γ t₀) s = velocity γ (t₀ + s) := rfl

/-- Positively rescale the time of a complete geodesic.  The tangent part of
the stored state is scaled at the same time, so the result is again certified
by rescaled local geodesic germs and starts with velocity `a • v₀`. -/
noncomputable def rescale
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) :
    GlobalGeodesic (I := I) (M := M) cov x₀ (a • v₀) where
  state := fun t ↦ ⟨(γ.state (a * t)).proj, a • (γ.state (a * t)).snd⟩
  state_zero := by
    rw [mul_zero, γ.state_zero]
  local_germ := by
    intro t
    obtain ⟨α, hα⟩ := γ.local_germ (a * t)
    let αa := IntrinsicGeodesic.LocalGeodesic.rescale α a ha
    refine ⟨αa, ?_⟩
    have hscale : Tendsto (fun s : ℝ ↦ a * s) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun s : ℝ ↦ a * s) 0 :=
        continuousAt_const.mul continuousAt_id
      simpa only [mul_zero] using hcont.tendsto
    have hαscale := hα.comp_tendsto hscale
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ),
        a * s ∈ Ioo (-α.solution.radius) α.solution.radius :=
      hscale.eventually (Ioo_mem_nhds
        (by linarith [α.solution.radius_pos])
        (by linarith [α.solution.radius_pos]))
    filter_upwards [hαscale, hsmall] with s hs hsint
    change γ.state (a * t + a * s) = IntrinsicGeodesic.localState α (a * s) at hs
    change (⟨(γ.state (a * (t + s))).proj,
      a • (γ.state (a * (t + s))).snd⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      IntrinsicGeodesic.localState αa s
    have hvel := IntrinsicGeodesic.LocalGeodesic.rescale_actual_velocity
      α a ha hsint
    rw [show a * (t + s) = a * t + a * s by ring, hs]
    apply Bundle.TotalSpace.ext
    · exact (IntrinsicGeodesic.LocalGeodesic.rescale_curve α a ha s).symm
    · exact heq_of_eq hvel.symm

@[simp] lemma rescale_state
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (rescale γ a ha).state t =
      ⟨(γ.state (a * t)).proj, a • (γ.state (a * t)).snd⟩ := rfl

@[simp] lemma rescale_curve
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    curve (rescale γ a ha) t = curve γ (a * t) := rfl

@[simp] lemma rescale_velocity
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    velocity (rescale γ a ha) t = a • velocity γ (a * t) := rfl

end GlobalGeodesic

namespace PartialGeodesic

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- Extension is equality of the complete tangent state on the old domain.
This avoids any transport bookkeeping on overlaps. -/
def Extends
    (p q : PartialGeodesic (I := I) (M := M) cov x₀ v₀) : Prop :=
  p.domain ⊆ q.domain ∧ ∀ t ∈ p.domain, p.state t = q.state t

instance : LE (PartialGeodesic (I := I) (M := M) cov x₀ v₀) :=
  ⟨Extends⟩

lemma le_def (p q : PartialGeodesic (I := I) (M := M) cov x₀ v₀) :
    p ≤ q ↔ p.domain ⊆ q.domain ∧ ∀ t ∈ p.domain, p.state t = q.state t :=
  Iff.rfl

lemma le_refl (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) : p ≤ p := by
  exact ⟨Subset.rfl, fun _ _ ↦ rfl⟩

lemma le_trans {p q r : PartialGeodesic (I := I) (M := M) cov x₀ v₀}
    (hpq : p ≤ q) (hqr : q ≤ r) : p ≤ r := by
  refine ⟨hpq.1.trans hqr.1, ?_⟩
  intro t ht
  exact (hpq.2 t ht).trans (hqr.2 t (hpq.1 ht))

lemma le_antisymm {p q : PartialGeodesic (I := I) (M := M) cov x₀ v₀}
    (hpq : p ≤ q) (hqp : q ≤ p) : p = q := by
  cases p with
  | mk pdom popen pconn pzero pstate pstatezero poutside plocal =>
    cases q with
    | mk qdom qopen qconn qzero qstate qstatezero qoutside qlocal =>
      change pdom ⊆ qdom ∧ ∀ t ∈ pdom, pstate t = qstate t at hpq
      change qdom ⊆ pdom ∧ ∀ t ∈ qdom, qstate t = pstate t at hqp
      have hdom : pdom = qdom := Subset.antisymm hpq.1 hqp.1
      subst qdom
      have hstate : pstate = qstate := by
        funext t
        by_cases ht : t ∈ pdom
        · exact hpq.2 t ht
        · exact (poutside t ht).trans (qoutside t ht).symm
      subst qstate
      rfl

instance : PartialOrder (PartialGeodesic (I := I) (M := M) cov x₀ v₀) where
  le := Extends
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

/-- A uniform intrinsic speed bound on a partial state. -/
def HasSpeedBound (C : ℝ)
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) : Prop :=
  ∀ t ∈ p.domain, ‖(p.state t).snd‖ ≤ C

/-- The underlying manifold curve of a partial geodesic. -/
def curve (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) : ℝ → M :=
  fun t ↦ (p.state t).proj

/-- The tangent velocity encoded by a partial geodesic's state. -/
def velocity (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) : TangentSpace I (curve p t) :=
  (p.state t).snd

/-- Negate the tangent component of a tangent-bundle state while retaining
its base point. -/
noncomputable def reverseState
    (z : Bundle.TotalSpace E (TangentSpace I : M → Type _)) :
    Bundle.TotalSpace E (TangentSpace I : M → Type _) :=
  ⟨z.proj, -z.snd⟩

@[simp] lemma reverseState_involutive
    (z : Bundle.TotalSpace E (TangentSpace I : M → Type _)) :
    reverseState (reverseState z) = z := by
  rcases z with ⟨x, v⟩
  change (⟨x, - -v⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
    ⟨x, v⟩
  refine Bundle.TotalSpace.ext ?_ ?_
  · rfl
  · exact heq_of_eq (neg_neg v)

/-- Reverse a partial geodesic in time.  The domain is reflected through the
origin and the tangent component of its state is negated. -/
noncomputable def reverse
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) :
    PartialGeodesic (I := I) (M := M) cov x₀ (-v₀) where
  domain := Neg.neg ⁻¹' p.domain
  domain_open := p.domain_open.preimage continuous_neg
  domain_preconnected := by
    have hdom : Neg.neg ⁻¹' p.domain = Neg.neg '' p.domain := by
      ext t
      constructor
      · intro ht
        exact ⟨-t, ht, neg_neg t⟩
      · rintro ⟨s, hs, hst⟩
        change -t ∈ p.domain
        rw [← hst]
        simpa using hs
    rw [hdom]
    exact p.domain_preconnected.image (fun t : ℝ ↦ -t) continuous_neg.continuousOn
  zero_mem := by simpa using p.zero_mem
  state := fun t ↦ ⟨(p.state (-t)).proj, -(p.state (-t)).snd⟩
  state_zero := by
    have hzero : -(0 : ℝ) = 0 := by ring
    rw [hzero, p.state_zero]
  state_outside := by
    intro t ht
    change -t ∉ p.domain at ht
    rw [p.state_outside (-t) ht]
  local_germ := by
    intro t ht
    change -t ∈ p.domain at ht
    obtain ⟨γ, hγ⟩ := p.local_germ (-t) ht
    refine ⟨LocalGeodesic.reverse γ, ?_⟩
    have hneg : Tendsto (fun s : ℝ ↦ -s) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun s : ℝ ↦ -s) 0 :=
        (continuousAt_id : ContinuousAt (fun s : ℝ ↦ s) 0).neg
      simpa using hcont.tendsto
    have hγneg := hγ.comp_tendsto hneg
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ),
        s ∈ Ioo (-γ.solution.radius) γ.solution.radius :=
      Ioo_mem_nhds (by linarith [γ.solution.radius_pos])
        (by linarith [γ.solution.radius_pos])
    filter_upwards [hγneg, hsmall] with s hs hsr
    change p.state (-t + -s) = localState γ (-s) at hs
    have hvel := LocalGeodesic.reverse_actual_velocity γ hsr
    change ⟨(p.state (-(t + s))).proj, -(p.state (-(t + s))).snd⟩ =
      localState (LocalGeodesic.reverse γ) s
    rw [show -(t + s) = -t + -s by ring, hs]
    simp only [localState]
    rw [LocalGeodesic.reverse_curve, hvel]
    rfl

@[simp] lemma reverse_domain
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) :
    (reverse p).domain = Neg.neg ⁻¹' p.domain := rfl

@[simp] lemma reverse_state
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    (reverse p).state t = ⟨(p.state (-t)).proj, -(p.state (-t)).snd⟩ := rfl

@[simp] lemma reverse_state_eq_reverseState
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    (reverse p).state t = reverseState (p.state (-t)) := rfl

/-- The typed inverse of `reverse` for a partial geodesic whose prescribed
initial velocity is already negated.  Keeping this construction separately
avoids an artificial transport across the propositional equality
`-(-v₀) = v₀`. -/
noncomputable def unreverse
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ (-v₀)) :
    PartialGeodesic (I := I) (M := M) cov x₀ v₀ where
  domain := Neg.neg ⁻¹' p.domain
  domain_open := p.domain_open.preimage continuous_neg
  domain_preconnected := by
    have hdom : Neg.neg ⁻¹' p.domain = Neg.neg '' p.domain := by
      ext t
      constructor
      · intro ht
        exact ⟨-t, ht, neg_neg t⟩
      · rintro ⟨s, hs, hst⟩
        change -t ∈ p.domain
        rw [← hst]
        simpa using hs
    rw [hdom]
    exact p.domain_preconnected.image (fun t : ℝ ↦ -t) continuous_neg.continuousOn
  zero_mem := by simpa using p.zero_mem
  state := fun t ↦ ⟨(p.state (-t)).proj, -(p.state (-t)).snd⟩
  state_zero := by
    have hzero : -(0 : ℝ) = 0 := by ring
    rw [hzero, p.state_zero]
    simp
  state_outside := by
    intro t ht
    change -t ∉ p.domain at ht
    rw [p.state_outside (-t) ht]
    simp
  local_germ := by
    intro t ht
    change -t ∈ p.domain at ht
    obtain ⟨γ, hγ⟩ := p.local_germ (-t) ht
    refine ⟨LocalGeodesic.reverse γ, ?_⟩
    have hneg : Tendsto (fun s : ℝ ↦ -s) (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun s : ℝ ↦ -s) 0 :=
        (continuousAt_id : ContinuousAt (fun s : ℝ ↦ s) 0).neg
      simpa using hcont.tendsto
    have hγneg := hγ.comp_tendsto hneg
    have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ),
        s ∈ Ioo (-γ.solution.radius) γ.solution.radius :=
      Ioo_mem_nhds (by linarith [γ.solution.radius_pos])
        (by linarith [γ.solution.radius_pos])
    filter_upwards [hγneg, hsmall] with s hs hsr
    change p.state (-t + -s) = localState γ (-s) at hs
    have hvel := LocalGeodesic.reverse_actual_velocity γ hsr
    change ⟨(p.state (-(t + s))).proj, -(p.state (-(t + s))).snd⟩ =
      localState (LocalGeodesic.reverse γ) s
    rw [show -(t + s) = -t + -s by ring, hs]
    simp only [localState]
    rw [LocalGeodesic.reverse_curve, hvel]
    rfl

@[simp] lemma unreverse_state
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ (-v₀)) (t : ℝ) :
    (unreverse p).state t = reverseState (p.state (-t)) := rfl

lemma unreverse_hasSpeedBound
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {C : ℝ} (p : PartialGeodesic (I := I) (M := M) cov x₀ (-v₀))
    (hp : HasSpeedBound (I := I) (M := M) C p) :
    HasSpeedBound (I := I) (M := M) C (unreverse p) := by
  intro t ht
  change -t ∈ p.domain at ht
  change ‖-(p.state (-t)).snd‖ ≤ C
  rw [norm_neg]
  exact hp (-t) ht

lemma le_unreverse_of_reverse_le
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {p : PartialGeodesic (I := I) (M := M) cov x₀ v₀}
    {q : PartialGeodesic (I := I) (M := M) cov x₀ (-v₀)}
    (hpq : reverse p ≤ q) : p ≤ unreverse q := by
  refine ⟨?_, ?_⟩
  · intro t ht
    change -t ∈ q.domain
    apply hpq.1
    change -(-t) ∈ p.domain
    simpa using ht
  · intro t ht
    change p.state t = reverseState (q.state (-t))
    have hrev : -t ∈ (reverse p).domain := by
      change -(-t) ∈ p.domain
      simpa using ht
    have hstate := hpq.2 (-t) hrev
    rw [reverse_state_eq_reverseState] at hstate
    have hstate' := congrArg reverseState hstate
    simpa using hstate'

lemma proper_unreverse_of_reverse_proper
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {p : PartialGeodesic (I := I) (M := M) cov x₀ v₀}
    {q : PartialGeodesic (I := I) (M := M) cov x₀ (-v₀)}
    (hpq : (reverse p).domain ⊂ q.domain) :
    p.domain ⊂ (unreverse q).domain := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro t ht
    change -t ∈ q.domain
    apply hpq.1
    change -(-t) ∈ p.domain
    simpa using ht
  · intro hsub
    apply hpq.2
    intro t ht
    have hunrev : -t ∈ (unreverse q).domain := by
      change -(-t) ∈ q.domain
      simpa using ht
    rw [← hsub] at hunrev
    change -t ∈ p.domain at hunrev
    exact hunrev

lemma reverse_hasSpeedBound
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {C : ℝ} (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    (hp : HasSpeedBound (I := I) (M := M) C p) :
    HasSpeedBound (I := I) (M := M) C (reverse p) := by
  intro t ht
  change -t ∈ p.domain at ht
  change ‖-(p.state (-t)).snd‖ ≤ C
  rw [norm_neg]
  exact hp (-t) ht

lemma reverse_le
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {p q : PartialGeodesic (I := I) (M := M) cov x₀ v₀}
    (hpq : p ≤ q) : reverse p ≤ reverse q := by
  refine ⟨?_, ?_⟩
  · intro t ht
    change -t ∈ p.domain at ht
    change -t ∈ q.domain
    exact hpq.1 ht
  · intro t ht
    change -t ∈ p.domain at ht
    change (⟨(p.state (-t)).proj, -(p.state (-t)).snd⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      (⟨(q.state (-t)).proj, -(q.state (-t)).snd⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _))
    rw [hpq.2 (-t) ht]

lemma reverse_proper
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {p q : PartialGeodesic (I := I) (M := M) cov x₀ v₀}
    (hpq : p.domain ⊂ q.domain) :
    (reverse p).domain ⊂ (reverse q).domain := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro t ht
    change -t ∈ p.domain at ht
    change -t ∈ q.domain
    exact hpq.1 ht
  · intro hEq
    apply hpq.2
    intro t ht
    have hrevq : -t ∈ (reverse q).domain := by
      change -(-t) ∈ q.domain
      simpa using ht
    rw [← hEq] at hrevq
    change -(-t) ∈ p.domain at hrevq
    simpa using hrevq

@[simp] lemma reverse_reverse_domain
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) :
    (reverse (reverse p)).domain = p.domain := by
  ext t
  change -(-t) ∈ p.domain ↔ t ∈ p.domain
  simp

@[simp] lemma reverse_reverse_state
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    (reverse (reverse p)).state t = p.state t := by
  change (⟨((reverse p).state (-t)).proj,
    -((reverse p).state (-t)).snd⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) = p.state t
  rw [reverse_state]
  rw [show - -t = t by ring]
  simp

private lemma local_contMDiffAt_curve
    {x : M} {v : TangentSpace I x}
    (γ : LocalGeodesic (I := I) (M := M) cov x v)
    {t : ℝ} (ht : t ∈ Ioo (-γ.solution.radius) γ.solution.radius) :
    ContMDiffAt (𝓘(ℝ, ℝ)) I 1 (LocalGeodesic.curve γ) t := by
  let a : ℝ := (t - γ.solution.radius) / 2
  let c : ℝ := (t + γ.solution.radius) / 2
  have ha : -γ.solution.radius < a := by
    dsimp [a]
    linarith [ht.1]
  have hac : a < c := by
    dsimp [a, c]
    linarith [γ.solution.radius_pos]
  have hc : c < γ.solution.radius := by
    dsimp [c]
    linarith [ht.2]
  have hat : a < t := by
    dsimp [a]
    linarith [ht.1]
  have htc : t < c := by
    dsimp [c]
    linarith [ht.2]
  have hsmooth := LocalGeodesicData.localChartSecondOrderSolution_contMDiffOn_curve
    (I := I) γ.solution ha hc hac
  exact hsmooth.contMDiffAt (Icc_mem_nhds hat htc)

lemma curve_eventuallyEq_shift_local
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {t : ℝ} (ht : t ∈ p.domain) :
    ∃ γ : LocalGeodesic (I := I) (M := M) cov (curve p t) (velocity p t),
      curve p =ᶠ[𝓝 t] (fun s ↦ LocalGeodesic.curve γ (s - t)) := by
  obtain ⟨γ, hγ⟩ := p.local_germ t ht
  refine ⟨γ, ?_⟩
  have hshift : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
    have hid : ContinuousAt (fun s : ℝ ↦ s) t := continuousAt_id
    have hconst : ContinuousAt (fun _ : ℝ ↦ t) t := continuousAt_const
    have hraw := (hid.sub hconst).tendsto
    have hfun : ((fun s : ℝ ↦ s) - fun _ ↦ t) = (fun s ↦ s - t) := by
      funext s
      rfl
    rw [hfun] at hraw
    simpa using hraw
  have hnear := hshift.eventually hγ
  filter_upwards [hnear] with s hs
  change (p.state s).proj = (localState γ (s - t)).proj
  have hs' : p.state s = localState γ (s - t) := by
    convert hs using 1 <;> ring
  exact congrArg Bundle.TotalSpace.proj hs'

/-- The partial curve has its packaged velocity as its actual manifold
derivative at every point of its domain. -/
lemma hasMFDerivAt_curve
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {t : ℝ} (ht : t ∈ p.domain) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) I (curve p) t
      (ContinuousLinearMap.toSpanSingleton ℝ (velocity p t)) := by
  obtain ⟨γ, hγ⟩ := p.local_germ t ht
  have hcurve : curve p =ᶠ[𝓝 t]
      (fun s ↦ LocalGeodesic.curve γ (s - t)) := by
    have hshift : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
      have hid : ContinuousAt (fun s : ℝ ↦ s) t := continuousAt_id
      have hconst : ContinuousAt (fun _ : ℝ ↦ t) t := continuousAt_const
      have hraw := (hid.sub hconst).tendsto
      have hfun : ((fun s : ℝ ↦ s) - fun _ ↦ t) = (fun s ↦ s - t) := by
        funext s
        rfl
      rw [hfun] at hraw
      simpa using hraw
    have hnear := hshift.eventually hγ
    filter_upwards [hnear] with s hs
    change (p.state s).proj = (localState γ (s - t)).proj
    have hs' : p.state s = localState γ (s - t) := by
      convert hs using 1 <;> ring
    exact congrArg Bundle.TotalSpace.proj hs'
  have hzero : (0 : ℝ) ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [γ.solution.radius_pos]
  have hlocal := LocalGeodesic.hasMFDerivAt_curve γ hzero
  have hshiftDeriv : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun s : ℝ ↦ s - t) t (ContinuousLinearMap.id ℝ _) := by
    have hraw : HasFDerivAt (fun s : ℝ ↦ s - t) (ContinuousLinearMap.id ℝ ℝ) t :=
      hasFDerivAt_sub_const t
    exact hraw.hasMFDerivAt
  let σ : ℝ → ℝ := fun s ↦ s - t
  have hlocal' : HasMFDerivAt (𝓘(ℝ, ℝ)) I (LocalGeodesic.curve γ) (σ t)
      (ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity γ 0)) := by
    have hσ : σ t = 0 := by simp [σ]
    rw [hσ]
    exact hlocal
  have hcomp := HasMFDerivAt.comp t hlocal' hshiftDeriv
  have hcomp' : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (fun s ↦ LocalGeodesic.curve γ (s - t)) t
      (ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity γ 0)) := by
    have hmap :
        (ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity γ 0)) ∘SL
          (ContinuousLinearMap.id ℝ _) =
          ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity γ 0) := by
      apply ContinuousLinearMap.ext
      intro r
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    exact hcomp.congr_mfderiv hmap
  have hderivP := hcomp'.congr_of_eventuallyEq hcurve
  rw [LocalGeodesic.velocity_initial γ] at hderivP
  exact hderivP

/-- Smoothness is local in the domain, so the local-state certificate upgrades
the partial curve to a genuine `C¹` manifold curve on its whole domain. -/
lemma contMDiffAt_curve
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {t : ℝ} (ht : t ∈ p.domain) :
    ContMDiffAt (𝓘(ℝ, ℝ)) I 1 (curve p) t := by
  obtain ⟨γ, hcurve⟩ := curve_eventuallyEq_shift_local p ht
  have hzero : (0 : ℝ) ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
    constructor <;> linarith [γ.solution.radius_pos]
  have hlocal := local_contMDiffAt_curve γ hzero
  have hshiftC : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1
      (fun s : ℝ ↦ s - t) t := by
    have hid : ContDiffAt ℝ 1 (fun s : ℝ ↦ s) t := contDiffAt_id
    have hconst : ContDiffAt ℝ 1 (fun _ : ℝ ↦ t) t := contDiffAt_const
    exact (hid.sub hconst).contMDiffAt
  let σ : ℝ → ℝ := fun s ↦ s - t
  have hlocal' : ContMDiffAt (𝓘(ℝ, ℝ)) I 1 (LocalGeodesic.curve γ) (σ t) := by
    have hσ : σ t = 0 := by simp [σ]
    rw [hσ]
    exact hlocal
  have hcomp := hlocal'.comp t hshiftC
  have hcomp' : ContMDiffAt (𝓘(ℝ, ℝ)) I 1
      (fun s ↦ LocalGeodesic.curve γ (s - t)) t := by
    simpa [Function.comp_def, σ] using hcomp
  exact hcomp'.congr_of_eventuallyEq hcurve

/-- On every compact time subinterval of its domain, a partial geodesic is a
`C¹` manifold curve. -/
lemma contMDiffOn_curve_Icc
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {a c : ℝ} (ha : a ∈ p.domain) (hc : c ∈ p.domain) :
    ContMDiffOn (𝓘(ℝ, ℝ)) I 1 (curve p) (Icc a c) := by
  apply contMDiffOn_of_locally_contMDiffOn
  intro t ht
  have htdomain : t ∈ p.domain :=
    p.domain_preconnected.Icc_subset ha hc ht
  have hcont := contMDiffAt_curve p htdomain
  obtain ⟨u, hu, hcontu⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (I := (𝓘(ℝ, ℝ))) (I' := I)
      (n := (1 : WithTop ℕ∞)) (by simp)).mp hcont
  obtain ⟨v, hvsub, hvopen, htv⟩ := mem_nhds_iff.mp hu
  refine ⟨v, hvopen, htv, ?_⟩
  exact hcontu.mono (fun _ hx ↦ hvsub hx.2)

/-- A uniform intrinsic speed bound controls the Riemannian distance between
any two times in the partial domain.  This is the metric input for the
finite-endpoint argument. -/
lemma riemannianEDist_le_speed_mul
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {a c C : ℝ} (ha : a ∈ p.domain) (hc : c ∈ p.domain) (hac : a ≤ c)
    (hC : HasSpeedBound (I := I) (M := M) C p) :
    riemannianEDist I (curve p a) (curve p c) ≤
      ENNReal.ofReal C * ENNReal.ofReal (c - a) := by
  calc
    riemannianEDist I (curve p a) (curve p c) ≤
        pathELength I (curve p) a c :=
      riemannianEDist_le_pathELength (contMDiffOn_curve_Icc p ha hc) rfl rfl hac
    _ = ∫⁻ t in Ioo a c, ‖mfderiv% (curve p) t 1‖ₑ :=
      pathELength_eq_lintegral_mfderiv_Ioo
    _ ≤ ∫⁻ _t in Ioo a c, ENNReal.ofReal C := by
      apply MeasureTheory.setLIntegral_mono measurable_const
      intro t ht
      have htdomain : t ∈ p.domain :=
        p.domain_preconnected.Icc_subset ha hc ⟨ht.1.le, ht.2.le⟩
      rw [(hasMFDerivAt_curve p htdomain).mfderiv]
      change ‖(ContinuousLinearMap.toSpanSingleton ℝ (velocity p t)) 1‖ₑ ≤ _
      rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul,
        ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC t htdomain)
    _ = ENNReal.ofReal C * ENNReal.ofReal (c - a) := by
      rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]

/-- The preceding length estimate becomes an ordinary finite-metric bound as
soon as the metric's `edist` is the Riemannian extended distance. -/
lemma dist_le_speed_mul_of_edist_eq
    [PseudoMetricSpace M]
    (hedist : ∀ x y : M, edist x y = riemannianEDist I x y)
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {a c C : ℝ} (ha : a ∈ p.domain) (hc : c ∈ p.domain) (hac : a ≤ c)
    (hC0 : 0 ≤ C) (hC : HasSpeedBound (I := I) (M := M) C p) :
    dist (curve p a) (curve p c) ≤ C * (c - a) := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 (sub_nonneg.mpr hac))).mp
  calc
    ENNReal.ofReal (dist (curve p a) (curve p c)) =
        edist (curve p a) (curve p c) := (edist_dist _ _).symm
    _ = riemannianEDist I (curve p a) (curve p c) :=
      hedist _ _
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (c - a) :=
      riemannianEDist_le_speed_mul p ha hc hac hC
    _ = ENNReal.ofReal (C * (c - a)) := (ENNReal.ofReal_mul hC0).symm

private lemma Ioo_zero_subset_domain_of_upper_cofinal
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) {b : ℝ}
    (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t) :
    Ioo (0 : ℝ) b ⊆ p.domain := by
  intro t ht
  obtain ⟨u, hu, htu⟩ := hcofinal t ht.2
  exact p.domain_preconnected.Icc_subset p.zero_mem hu ⟨ht.1.le, htu.le⟩

private lemma exists_metric_tendsto_nhdsLT_curve_of_upper_cofinal
    [PseudoMetricSpace M] [CompleteSpace M]
    (hedist : ∀ x y : M, edist x y = riemannianEDist I x y)
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) {b C : ℝ}
    (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t)
    (hC0 : 0 ≤ C) (hC : HasSpeedBound (I := I) (M := M) C p) :
    ∃ x : M, Tendsto (curve p) (𝓝[<] b)
      (@nhds M PseudoMetricSpace.toUniformSpace.toTopologicalSpace x) := by
  apply exists_tendsto_nhdsLT_of_dist_le_linear_eventually hC0
  have hzeroB : (0 : ℝ) < b := hupper 0 p.zero_mem
  refine ⟨0, hzeroB, ?_⟩
  intro s hs t ht
  have hsdom : s ∈ p.domain :=
    Ioo_zero_subset_domain_of_upper_cofinal p hupper hcofinal hs
  have htdom : t ∈ p.domain :=
    Ioo_zero_subset_domain_of_upper_cofinal p hupper hcofinal ht
  rcases le_total s t with hst | hts
  · calc
      dist (curve p s) (curve p t) ≤ C * (t - s) :=
        dist_le_speed_mul_of_edist_eq hedist p hsdom htdom hst hC0 hC
      _ = C * |s - t| := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
  · calc
      dist (curve p s) (curve p t) = dist (curve p t) (curve p s) :=
        dist_comm _ _
      _ ≤ C * (s - t) :=
        dist_le_speed_mul_of_edist_eq hedist p htdom hsdom hts hC0 hC
      _ = C * |s - t| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hts)]

/-- In the finite Riemannian metric associated to a connected manifold, a
bounded partial geodesic approaching a finite upper endpoint has a manifold
limit.  The metric is constructed locally here so that its topology is the
given manifold topology. -/
lemma exists_tendsto_nhdsLT_curve_of_upper_cofinal
    [ConnectedSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (hcomplete : @CompleteSpace M
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace.toUniformSpace)
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀) {b C : ℝ}
    (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t)
    (hC0 : 0 ≤ C) (hC : HasSpeedBound (I := I) (M := M) C p) :
    ∃ x : M, Tendsto (curve p) (𝓝[<] b) (𝓝 x) := by
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide)
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : IsRiemannianManifold I M := by infer_instance
  have hfin : ∀ x y : M, edist x y ≠ (⊤ : ℝ≥0∞) := by
    intro x y
    exact ne_of_lt (edist_lt_top_of_connected (I := I) x y)
  letI : MetricSpace M := EMetricSpace.toMetricSpace hfin
  letI : CompleteSpace M := hcomplete
  apply exists_metric_tendsto_nhdsLT_curve_of_upper_cofinal
    (fun x y ↦ IsRiemannianManifold.out (I := I) (M := M) x y)
    p hupper hcofinal hC0 hC

/-- Reading the coherent tangent-bundle state through a fixed overlapping
endpoint chart agrees with the recharted velocity of its local geodesic germ.
The statement is kept at the state level to avoid any implicit transport
between dependent tangent fibres. -/
private lemma eventuallyEq_endpointChart_velocity_of_local_germ
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {t : ℝ} (ht : t ∈ p.domain)
    (γ : LocalGeodesic (I := I) (M := M) cov (curve p t) (velocity p t))
    (hγ : (fun s ↦ p.state (t + s)) =ᶠ[𝓝 (0 : ℝ)] localState γ)
    (c : M) (btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (hsource : ∀ᶠ s in 𝓝 (0 : ℝ),
      LocalChartSecondOrderSolution.curve γ.solution s ∈
        (extChartAt I c).source) :
    (fun s ↦ (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
      (curve p (t + s)) (velocity p (t + s))) =ᶠ[𝓝 (0 : ℝ)]
      CurveConnection.rechartVelocity (I := I) (M := M) γ.solution c := by
  have hinterval : Ioo (-γ.solution.radius) γ.solution.radius ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [γ.solution.radius_pos])
      (by linarith [γ.solution.radius_pos])
  filter_upwards [hγ, hsource, hinterval] with s hs hsrc hsint
  have hstate := congrArg (fun q : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
    (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
      q.proj q.snd) hs
  have hderivRaw := LocalGeodesic.hasMFDerivAt_curve γ hsint
  have hderiv : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalChartSecondOrderSolution.curve γ.solution) s
      (ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity γ s)) := by
    convert hderivRaw using 1 <;> rfl
  have hread := CurveConnection.rechartVelocity_eq_trivialization_readout_of_hasMFDerivAt
    (I := I) (M := M) γ.solution c btarget hsint hsrc
      (LocalGeodesic.velocity γ s) hderiv
  change (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
      (p.state (t + s)).proj (p.state (t + s)).snd = _
  calc
    (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (p.state (t + s)).proj (p.state (t + s)).snd =
      (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (LocalGeodesic.curve γ s) (LocalGeodesic.velocity γ s) := by
          convert hstate using 1 <;> rfl
    _ = CurveConnection.rechartVelocity (I := I) (M := M) γ.solution c s := hread.symm

/-- Once a partial geodesic converges to a finite endpoint and its domain
contains a final left tail, its state satisfies the geodesic ODE in the fixed
endpoint chart on that same tail. -/
lemma eventually_hasDerivAt_endpoint_chart_pair
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {b : ℝ} {c : M}
    (hdom : ∀ᶠ t in 𝓝[<] b, t ∈ p.domain)
    (hcurve : Tendsto (curve p) (𝓝[<] b) (𝓝 c))
    (btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ t in 𝓝[<] b,
      HasDerivAt (fun s ↦
        (extChartAt I c (p.state s).proj,
          (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
            (p.state s).proj (p.state s).snd))
        (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c btarget)
          (extChartAt I c (p.state t).proj,
            (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
              (p.state t).proj (p.state t).snd)) t := by
  obtain ⟨U, hUsub, hUopen, hcU⟩ := mem_nhds_iff.mp
    (IntrinsicAcceleration.smoothFrameAgreementSet_mem_nhds
      (I := I) (M := M) c btarget)
  have hU : ∀ᶠ t in 𝓝[<] b, curve p t ∈ U :=
    hcurve (hUopen.mem_nhds hcU)
  filter_upwards [hdom, hU] with t ht htU
  obtain ⟨γ, hγ⟩ := p.local_germ t ht
  have hbase0 : LocalChartSecondOrderSolution.curve γ.solution 0 = curve p t := by
    have h := congrArg Bundle.TotalSpace.proj hγ.self_of_nhds
    change (p.state (t + 0)).proj = (LocalGeodesic.curve γ 0) at h
    simpa [LocalGeodesic.curve, curve] using h.symm
  have hcont : ContinuousAt (LocalChartSecondOrderSolution.curve γ.solution) 0 := by
    have hzero : (0 : ℝ) ∈ Ioo (-γ.solution.radius) γ.solution.radius := by
      constructor <;> linarith [γ.solution.radius_pos]
    exact (LocalChartSecondOrderSolution.curve_hasMFDerivAt γ.solution hzero).continuousAt
  have htargetU : ∀ᶠ s in 𝓝 (0 : ℝ),
      LocalChartSecondOrderSolution.curve γ.solution s ∈ U := by
    have hU0 : U ∈ 𝓝 (LocalChartSecondOrderSolution.curve γ.solution 0) := by
      rw [hbase0]
      exact hUopen.mem_nhds htU
    exact hcont.preimage_mem_nhds hU0
  have htarget : ∀ᶠ s in 𝓝 (0 : ℝ),
      LocalChartSecondOrderSolution.curve γ.solution s ∈
        IntrinsicAcceleration.smoothFrameAgreementSet (I := I) (M := M) c btarget :=
    htargetU.mono fun _ hs ↦ hUsub hs
  have hlocal := CurveConnection.localGeodesic_rechart_pair_hasDerivAt_at_zero
    (I := I) (M := M) cov γ c btarget htarget hmetric
  have hz : (fun s ↦ extChartAt I c (p.state (t + s)).proj) =ᶠ[𝓝 (0 : ℝ)]
      CurveConnection.rechartCoordinate (I := I) (M := M) γ.solution c := by
    filter_upwards [hγ] with s hs
    have hbase := congrArg Bundle.TotalSpace.proj hs
    change extChartAt I c (p.state (t + s)).proj = _
    rw [hbase]
    rfl
  have hsource : ∀ᶠ s in 𝓝 (0 : ℝ),
      LocalChartSecondOrderSolution.curve γ.solution s ∈ (extChartAt I c).source :=
    htarget.mono fun _ hs ↦ hs.1
  have hu := eventuallyEq_endpointChart_velocity_of_local_germ
    p ht γ hγ c btarget hsource
  have hpair : (fun s ↦
      (extChartAt I c (p.state (t + s)).proj,
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (p.state (t + s)).proj (p.state (t + s)).snd)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s ↦
        (CurveConnection.rechartCoordinate (I := I) (M := M) γ.solution c s,
          CurveConnection.rechartVelocity (I := I) (M := M) γ.solution c s)) := by
    filter_upwards [hz, hu] with s hzs hus
    exact Prod.ext hzs hus
  have hshift := hlocal.congr_of_eventuallyEq hpair
  have hpair0 := hpair.self_of_nhds
  have hpair0' :
      (extChartAt I c (p.state t).proj,
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (p.state t).proj (p.state t).snd) =
      (CurveConnection.rechartCoordinate (I := I) (M := M) γ.solution c 0,
        CurveConnection.rechartVelocity (I := I) (M := M) γ.solution c 0) := by
    have hstate0 : p.state (t + 0) = p.state t := by rw [add_zero]
    have hfst : extChartAt I c (p.state (t + 0)).proj =
        CurveConnection.rechartCoordinate (I := I) (M := M) γ.solution c 0 := by
      exact congrArg Prod.fst hpair0
    have hsnd : (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (p.state (t + 0)).proj (p.state (t + 0)).snd =
        CurveConnection.rechartVelocity (I := I) (M := M) γ.solution c 0 := by
      exact congrArg Prod.snd hpair0
    apply Prod.ext
    · have hstatefst := congrArg (fun q : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
        extChartAt I c q.proj) hstate0
      exact hstatefst.symm.trans hfst
    · have hstatesnd := congrArg (fun q : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          q.proj q.snd) hstate0
      exact hstatesnd.symm.trans hsnd
  have hvalue : secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c btarget)
      (CurveConnection.rechartCoordinate (I := I) (M := M) γ.solution c 0,
        CurveConnection.rechartVelocity (I := I) (M := M) γ.solution c 0) =
      secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c btarget)
        (extChartAt I c (p.state t).proj,
          (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
            (p.state t).proj (p.state t).snd) := by
    rw [← hpair0']
  rw [hvalue] at hshift
  have hsub : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
    simpa using (hasDerivAt_id' t).sub_const t
  have hshift' : HasDerivAt (fun s ↦
      (extChartAt I c (p.state (t + s)).proj,
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (p.state (t + s)).proj (p.state (t + s)).snd))
      (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c btarget)
        (extChartAt I c (p.state t).proj,
          (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
            (p.state t).proj (p.state t).snd)) (t - t) := by
    simpa using hshift
  have hfinal := HasDerivAt.scomp t (h := fun s : ℝ ↦ s - t) hshift' hsub
  have hfinal' : HasDerivAt (fun s ↦
      (extChartAt I c (p.state (t + (s - t))).proj,
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (p.state (t + (s - t))).proj (p.state (t + (s - t))).snd))
      (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c btarget)
        (extChartAt I c (p.state t).proj,
          (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
            (p.state t).proj (p.state t).snd)) t := by
    simpa [Function.comp_def] using hfinal
  have hfun : (fun s : ℝ ↦
      (extChartAt I c (p.state (t + (s - t))).proj,
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (p.state (t + (s - t))).proj (p.state (t + (s - t))).snd)) =
      (fun s ↦
        (extChartAt I c (p.state s).proj,
          (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
            (p.state s).proj (p.state s).snd)) := by
    funext s
    have htime : t + (s - t) = s := by ring
    rw [htime]
  rw [hfun] at hfinal'
  exact hfinal'

/-- The endpoint-chart ODE restart agrees with the old partial state on its
overlap.  This upgrades equality of the chart coordinate pair to literal
equality in the tangent bundle, which is the coherence required to glue the
fresh local geodesic into a partial extension. -/
private lemma eventuallyEq_state_endpointChart_solution
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {b : ℝ} {c : M} {u : E}
    (sol : LocalChartSecondOrderSolution I
      (LocalGeodesicData.coordinateAcceleration cov c
        (IntrinsicGeodesic.canonicalBasis (E := E))) c u)
    (hsource : ∀ᶠ t in 𝓝[<] b, (p.state t).proj ∈ (extChartAt I c).source)
    (hsol : (fun t ↦
      (extChartAt I c (p.state t).proj,
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (p.state t).proj (p.state t).snd)) =ᶠ[𝓝[<] b]
      (fun t ↦ (sol.coordinate (t - b), sol.velocity (t - b))) ) :
    (fun t ↦ p.state t) =ᶠ[𝓝[<] b]
      (fun t ↦ localState
        (IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution (I := I) (M := M) sol)
        (t - b)) := by
  let δ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution (I := I) (M := M) sol
  have hinterval : ∀ᶠ t in 𝓝[<] b,
      t - b ∈ Ioo (-sol.radius) sol.radius := by
    filter_upwards [Ioo_mem_nhdsLT (a := b - sol.radius)
      (by linarith [sol.radius_pos])] with t ht
    constructor <;> linarith [ht.1, ht.2]
  filter_upwards [hsource, hsol, hinterval] with t htSource hpair htint
  have hz : extChartAt I c (p.state t).proj = sol.coordinate (t - b) :=
    congrArg Prod.fst hpair
  have hu : (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
      (p.state t).proj (p.state t).snd = sol.velocity (t - b) :=
    congrArg Prod.snd hpair
  have hδint : t - b ∈ Ioo (-δ.solution.radius) δ.solution.radius := by
    simpa [δ] using htint
  have hbase : (p.state t).proj = LocalGeodesic.curve δ (t - b) := by
    calc
      (p.state t).proj = (extChartAt I c).symm
          (extChartAt I c (p.state t).proj) :=
        ((extChartAt I c).left_inv htSource).symm
      _ = (extChartAt I c).symm (sol.coordinate (t - b)) :=
        congrArg (extChartAt I c).symm hz
      _ = LocalGeodesic.curve δ (t - b) := by
        simp [δ, LocalGeodesic.curve, LocalChartSecondOrderSolution.curve,
          Function.comp_apply]
  have hbaseChart : (p.state t).proj ∈ (chartAt H c).source := by
    rw [← extChartAt_source (I := I) c]
    exact htSource
  have hδSource : LocalGeodesic.curve δ (t - b) ∈ (chartAt H c).source := by
    rw [← hbase]
    exact hbaseChart
  have hframe : LocalGeodesic.velocity δ (t - b) =
      LocalGeodesicData.coordinateFrameCombination (I := I) (M := M)
        (x₀ := c) (IntrinsicGeodesic.canonicalBasis (E := E))
        (δ.solution.velocity (t - b)) (LocalGeodesic.curve δ (t - b)) := by
    rw [LocalGeodesic.velocity]
    simpa [LocalGeodesic.curve] using
      LocalGeodesicData.tangentField_eq_coordinateFrameCombination
        (I := I) (M := M) (E := E) cov c
          (IntrinsicGeodesic.canonicalBasis (E := E)) δ.solution
          δ.solution.velocity hδint
  have hframe' : LocalGeodesic.velocity δ (t - b) =
      (trivializationAt E (TangentSpace I : M → Type _) c).symmL ℝ
        (LocalGeodesic.curve δ (t - b)) (sol.velocity (t - b)) := by
    rw [hframe,
      LocalGeodesicData.coordinateFrameCombination_eq_symmL
        (I := I) (M := M) (x₀ := c)
        (IntrinsicGeodesic.canonicalBasis (E := E)) hδSource,
      IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution_velocity]
  have hpbase : (p.state t).proj ∈
      (trivializationAt E (TangentSpace I : M → Type _) c).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) c,
      ← extChartAt_source (I := I) c]
    exact htSource
  have hvel : (p.state t).snd =
      (trivializationAt E (TangentSpace I : M → Type _) c).symmL ℝ
        (p.state t).proj (sol.velocity (t - b)) := by
    calc
      (p.state t).snd =
          (trivializationAt E (TangentSpace I : M → Type _) c).symmL ℝ
            (p.state t).proj
              ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
                (p.state t).proj (p.state t).snd) :=
        ((trivializationAt E (TangentSpace I : M → Type _) c).symmL_continuousLinearMapAt
          hpbase (p.state t).snd).symm
      _ = (trivializationAt E (TangentSpace I : M → Type _) c).symmL ℝ
            (p.state t).proj (sol.velocity (t - b)) := by
        rw [hu]
  apply Bundle.TotalSpace.ext hbase
  apply heq_of_eq
  rw [hbase] at hvel
  exact hvel.trans hframe'.symm

/-- Glue a local geodesic across a finite upper endpoint once its tangent
state agrees with the old partial state on the left overlap.  The state is
chosen from the old piece wherever it is available, so extension is literal
state equality; the overlap certificate supplies the local germ at points of
the new piece. -/
private theorem exists_extension_of_upper_state_overlap
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {C b r : ℝ} (hbound : HasSpeedBound (I := I) (M := M) C p)
    (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t) (hr : 0 < r)
    {c : M} {w : TangentSpace I c}
    (δ : LocalGeodesic (I := I) (M := M) cov c w)
    (hoverlap : ∀ t ∈ p.domain, t ∈ Ioo (b - r) b →
      p.state t = localState δ (t - b))
    (hspeed : ∀ s ∈ Ioo (-r) r, ‖LocalGeodesic.velocity δ s‖ ≤ C)
    (hrestart : ∀ τ ∈ Ioo (-r) r,
      ∃ η : LocalGeodesic (I := I) (M := M) cov
        (LocalGeodesic.curve δ τ) (LocalGeodesic.velocity δ τ),
      (fun s ↦ localState δ (τ + s)) =ᶠ[𝓝 (0 : ℝ)] localState η) :
    ∃ q : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      HasSpeedBound (I := I) (M := M) C q ∧ p ≤ q ∧ p.domain ⊂ q.domain := by
  classical
  let J : Set ℝ := Ioo (b - r) (b + r)
  have hJopen : IsOpen J := isOpen_Ioo
  have hJpre : IsPreconnected J := isPreconnected_Ioo
  have hJb : b ∈ J := by
    change b - r < b ∧ b < b + r
    constructor <;> linarith
  have hnotPb : b ∉ p.domain := by
    intro hb
    linarith [hupper b hb]
  have hqpre : IsPreconnected (p.domain ∪ J) := by
    obtain ⟨t, ht, htb⟩ := hcofinal (b - r / 2) (by linarith)
    have htJ : t ∈ J := by
      constructor
      · linarith
      · linarith [hupper t ht, hr]
    exact p.domain_preconnected.union t ht htJ hJpre
  let qstate : ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _) :=
    fun t ↦ if hp : t ∈ p.domain then p.state t else
      if hJ : t ∈ J then localState δ (t - b) else ⟨x₀, v₀⟩
  have hqstate_p : ∀ {t : ℝ}, t ∈ p.domain → qstate t = p.state t := by
    intro t ht
    simp [qstate, ht]
  have hqstate_delta : ∀ {t : ℝ}, t ∈ J → qstate t = localState δ (t - b) := by
    intro t htJ
    by_cases ht : t ∈ p.domain
    · have hov := hoverlap t ht ⟨htJ.1, hupper t ht⟩
      simpa [qstate, ht] using hov
    · simp [qstate, ht, htJ]
  let q : PartialGeodesic (I := I) (M := M) cov x₀ v₀ := {
    domain := p.domain ∪ J
    domain_open := p.domain_open.union hJopen
    domain_preconnected := hqpre
    zero_mem := Set.mem_union_left J p.zero_mem
    state := qstate
    state_zero := by
      rw [hqstate_p p.zero_mem]
      exact p.state_zero
    state_outside := by
      intro t ht
      have htp : t ∉ p.domain := by
        intro hp
        exact ht (Set.mem_union_left J hp)
      have htJ : t ∉ J := by
        intro hJ
        exact ht (Set.mem_union_right p.domain hJ)
      simp [qstate, htp, htJ]
    local_germ := by
      intro t ht
      rcases ht with ht | ht
      · rw [hqstate_p ht]
        obtain ⟨γ, hγ⟩ := p.local_germ t ht
        refine ⟨γ, ?_⟩
        have hshift : Tendsto (fun s : ℝ ↦ t + s) (𝓝 0) (𝓝 t) := by
          have hconst : ContinuousAt (fun _ : ℝ ↦ t) 0 := continuousAt_const
          have hid : ContinuousAt (fun s : ℝ ↦ s) 0 := continuousAt_id
          change Tendsto ((fun _ : ℝ ↦ t) + fun s ↦ s) (𝓝 0) (𝓝 t)
          convert (hconst.add hid).tendsto using 1 <;> simp
        have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ p.domain :=
          hshift.eventually (p.domain_open.mem_nhds ht)
        filter_upwards [hnear, hγ] with s hs hstate
        calc
          qstate (t + s) = p.state (t + s) := hqstate_p hs
          _ = localState γ s := hstate
      · rw [show qstate t = localState δ (t - b) by exact hqstate_delta ht]
        obtain ⟨η, hη⟩ := hrestart (t - b) (by
          change b - r < t ∧ t < b + r at ht
          change -r < t - b ∧ t - b < r
          constructor
          · linarith [ht.1]
          · linarith [ht.2])
        refine ⟨η, ?_⟩
        have hshift : Tendsto (fun s : ℝ ↦ t + s) (𝓝 0) (𝓝 t) := by
          have hconst : ContinuousAt (fun _ : ℝ ↦ t) 0 := continuousAt_const
          have hid : ContinuousAt (fun s : ℝ ↦ s) 0 := continuousAt_id
          change Tendsto ((fun _ : ℝ ↦ t) + fun s ↦ s) (𝓝 0) (𝓝 t)
          convert (hconst.add hid).tendsto using 1 <;> simp
        have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ J :=
          hshift.eventually (hJopen.mem_nhds ht)
        filter_upwards [hnear, hη] with s hs hstate
        calc
          qstate (t + s) = localState δ (t + s - b) := hqstate_delta hs
          _ = localState δ ((t - b) + s) := by
            congr 1
            ring
          _ = localState η s := hstate
    }
  have hqbound : HasSpeedBound (I := I) (M := M) C q := by
    intro t ht
    change t ∈ p.domain ∪ J at ht
    change ‖(qstate t).snd‖ ≤ C
    rcases ht with ht | ht
    · rw [hqstate_p ht]
      exact hbound t ht
    · have hq := hqstate_delta ht
      rw [hq]
      apply hspeed
      change b - r < t ∧ t < b + r at ht
      constructor <;> linarith [ht.1, ht.2]
  have hpq : p ≤ q := by
    refine ⟨?_, ?_⟩
    · intro t ht
      change t ∈ p.domain ∪ J
      exact Set.mem_union_left J ht
    · intro t ht
      change p.state t = qstate t
      exact (hqstate_p ht).symm
  have hproper : p.domain ⊂ q.domain := by
    change p.domain ⊂ p.domain ∪ J
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro t ht
      exact Set.mem_union_left J ht
    intro hEq
    apply hnotPb
    rw [hEq]
    exact Set.mem_union_right p.domain hJb
  exact ⟨q, hqbound, hpq, hproper⟩

/-- A local geodesic whose complete state is the final left germ of a bounded
partial geodesic yields a strict upper extension.  Constant local speed
transfers the old global bound to the new local piece, and local restart
coherence supplies its germs at every point of the glued interval. -/
private theorem exists_extension_of_upper_localState
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {C b : ℝ} (hbound : HasSpeedBound (I := I) (M := M) C p)
    (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t)
    {c : M} {w : TangentSpace I c}
    (δ : LocalGeodesic (I := I) (M := M) cov c w)
    (htail : (fun t ↦ p.state t) =ᶠ[𝓝[<] b]
      (fun t ↦ localState δ (t - b))) :
    ∃ q : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      HasSpeedBound (I := I) (M := M) C q ∧ p ≤ q ∧ p.domain ⊂ q.domain := by
  obtain ⟨ρ, hρ, hρsol, henergy⟩ :=
    exists_local_norm_velocity_eq_initial (I := I) (M := M) δ hmetric
  have hzeroρ : (0 : ℝ) ∈ Ioo (-ρ) ρ := by
    constructor <;> linarith
  have hrestartEvent := LocalGeodesic.eventually_exists_restartedLocalGeodesic_state
    (I := I) (M := M) δ hmetric
  obtain ⟨ε, hε, hrestartSub⟩ := Metric.mem_nhds_iff.mp hrestartEvent
  obtain ⟨a, ha, htailSub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp htail
  let a₀ : ℝ := max a (b - ρ / 2)
  have ha₀ : a₀ < b := by
    dsimp [a₀]
    apply max_lt ha
    linarith
  obtain ⟨t, ht, ha₀t⟩ := hcofinal a₀ ha₀
  have htupper : t < b := hupper t ht
  have hta : a < t := lt_of_le_of_lt (le_max_left _ _) ha₀t
  have htρlower : b - ρ / 2 < t := lt_of_le_of_lt (le_max_right _ _) ha₀t
  have htρ : t - b ∈ Ioo (-ρ) ρ := by
    constructor <;> linarith [hρ]
  have htailt : p.state t = localState δ (t - b) :=
    htailSub ⟨hta, htupper⟩
  have hspeedAt : ‖LocalGeodesic.velocity δ (t - b)‖ ≤ C := by
    have h := hbound t ht
    rw [htailt] at h
    have h' : ‖(localState δ (t - b)).snd‖ ≤ C := by
      exact h
    change ‖LocalGeodesic.velocity δ (t - b)‖ ≤ C at h'
    exact h'
  have hinitial : ‖LocalGeodesic.velocity δ 0‖ ≤ C := by
    calc
      ‖LocalGeodesic.velocity δ 0‖ = ‖w‖ := by
        exact henergy 0 hzeroρ
      _ = ‖LocalGeodesic.velocity δ (t - b)‖ := (henergy (t - b) htρ).symm
      _ ≤ C := hspeedAt
  let r : ℝ := min (min ((b - a) / 2) (ε / 2)) (ρ / 2)
  have hr : 0 < r := by
    dsimp [r]
    apply lt_min
    · apply lt_min
      · linarith [ha]
      · linarith
    · linarith
  have hrinner : r ≤ min ((b - a) / 2) (ε / 2) := min_le_left _ _
  have hra : r ≤ (b - a) / 2 :=
    hrinner.trans (min_le_left _ _)
  have hrε : r ≤ ε / 2 :=
    hrinner.trans (min_le_right _ _)
  have hrρ : r ≤ ρ / 2 := min_le_right _ _
  have htailLower : a < b - r := by
    linarith [hra]
  have hoverlap : ∀ t ∈ p.domain, t ∈ Ioo (b - r) b →
      p.state t = localState δ (t - b) := by
    intro s hs hsI
    apply htailSub
    constructor
    · exact lt_trans htailLower hsI.1
    · exact hsI.2
  have hspeed : ∀ s ∈ Ioo (-r) r, ‖LocalGeodesic.velocity δ s‖ ≤ C := by
    intro s hs
    have hsρ : s ∈ Ioo (-ρ) ρ := by
      constructor <;> linarith [hs.1, hs.2, hrρ, hρ]
    calc
      ‖LocalGeodesic.velocity δ s‖ = ‖w‖ := henergy s hsρ
      _ = ‖LocalGeodesic.velocity δ 0‖ := (henergy 0 hzeroρ).symm
      _ ≤ C := hinitial
  have hrestart : ∀ τ ∈ Ioo (-r) r,
      ∃ η : LocalGeodesic (I := I) (M := M) cov
        (LocalGeodesic.curve δ τ) (LocalGeodesic.velocity δ τ),
      (fun s ↦ localState δ (τ + s)) =ᶠ[𝓝 (0 : ℝ)] localState η := by
    intro τ hτ
    apply hrestartSub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have habs : |τ| < r := (abs_lt).mpr hτ
    exact lt_of_lt_of_le habs (by linarith [hrε, hε])
  exact exists_extension_of_upper_state_overlap p hbound hupper hcofinal hr
    δ hoverlap hspeed hrestart

/-- A bounded partial geodesic with a finite upper endpoint and a limiting
base point admits a strict extension.  The endpoint chart turns its final
state into a local ODE solution; the preceding state-level gluing theorem
then restores a coherent intrinsic partial geodesic. -/
private theorem exists_extension_of_upper_endpoint
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {C b : ℝ} (hbound : HasSpeedBound (I := I) (M := M) C p)
    (hupper : ∀ t ∈ p.domain, t < b)
    (hcofinal : ∀ a < b, ∃ t ∈ p.domain, a < t)
    {c : M} (hcurve : Tendsto (curve p) (𝓝[<] b) (𝓝 c)) :
    ∃ q : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      HasSpeedBound (I := I) (M := M) C q ∧ p ≤ q ∧ p.domain ⊂ q.domain := by
  let btarget : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  have hzeroB : (0 : ℝ) < b := hupper 0 p.zero_mem
  have hdom : ∀ᶠ t in 𝓝[<] b, t ∈ p.domain := by
    filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) hzeroB] with t ht
    exact Ioo_zero_subset_domain_of_upper_cofinal p hupper hcofinal ht
  have hsource : ∀ᶠ t in 𝓝[<] b,
      (p.state t).proj ∈ (extChartAt I c).source :=
    hcurve (extChartAt_source_mem_nhds (I := I) c)
  have hderiv := eventually_hasDerivAt_endpoint_chart_pair
    (I := I) (M := M) p hdom hcurve btarget hmetric
  have hcoordinate : ∀ᶠ t in 𝓝[<] b,
      extChartAt I c (p.state t).proj = extChartAt I c (curve p t) := by
    filter_upwards with t
    rfl
  have hframe : ∀ᶠ t in 𝓝[<] b,
      velocity p t = LocalGeodesicData.coordinateFrameCombination
        (I := I) (M := M) (x₀ := c) btarget
        ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
          (p.state t).proj (p.state t).snd) (curve p t) := by
    filter_upwards [hdom, hsource] with t htdom hsrc
    have hsrcChart : (p.state t).proj ∈ (chartAt H c).source := by
      rw [← extChartAt_source (I := I) c]
      exact hsrc
    have hbase : (p.state t).proj ∈
        (trivializationAt E (TangentSpace I : M → Type _) c).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) c,
        ← extChartAt_source (I := I) c]
      exact hsrc
    change (p.state t).snd = LocalGeodesicData.coordinateFrameCombination
      (I := I) (M := M) (x₀ := c) btarget
      ((trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
        (p.state t).proj (p.state t).snd) (p.state t).proj
    rw [LocalGeodesicData.coordinateFrameCombination_eq_symmL
      (I := I) (M := M) (x₀ := c) btarget hsrcChart]
    exact ((trivializationAt E (TangentSpace I : M → Type _) c).symmL_continuousLinearMapAt
      hbase (p.state t).snd).symm
  have hvelocity : ∀ᶠ t in 𝓝[<] b, ‖velocity p t‖ ≤ C := by
    filter_upwards [hdom] with t ht
    exact hbound t ht
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) := by
    rcases (inferInstance : IsContMDiffRiemannianBundle I 1 E
      (TangentSpace I : M → Type _)).exists_contMDiff with ⟨g, hg, hinner⟩
    exact ⟨g, hg.continuous, hinner⟩
  obtain ⟨u, sol, hsol⟩ :=
    exists_localChartGeodesicSolution_eventuallyEq_left_of_intrinsic_tendsto_of_norm_velocity_eventually_le_eventually_deriv
      (I := I) (M := M) (E := E) (cov := cov) btarget hderiv hcurve
        hcoordinate hframe hvelocity
  let δ := IntrinsicGeodesic.LocalGeodesic.of_coordinateSolution (I := I) (M := M) sol
  have htail : (fun t ↦ p.state t) =ᶠ[𝓝[<] b]
      (fun t ↦ localState δ (t - b)) := by
    simpa [δ] using
      eventuallyEq_state_endpointChart_solution (I := I) (M := M) p sol hsource hsol
  exact exists_extension_of_upper_localState hmetric p hbound hupper hcofinal δ htail

/-- A lower finite endpoint is reduced to the upper-endpoint construction by
time reversal.  The typed `unreverse` construction returns the resulting
strict extension to the original initial tangent without dependent casts. -/
private theorem exists_extension_of_lower_endpoint
    [ConnectedSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (hcomplete : @CompleteSpace M
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace.toUniformSpace)
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    {C a : ℝ} (hbound : HasSpeedBound (I := I) (M := M) C p)
    (hlower : ∀ t ∈ p.domain, a < t)
    (hcofinal : ∀ b > a, ∃ t ∈ p.domain, t < b) :
    ∃ q : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      HasSpeedBound (I := I) (M := M) C q ∧ p ≤ q ∧ p.domain ⊂ q.domain := by
  let pr := reverse p
  have hprbound : HasSpeedBound (I := I) (M := M) C pr :=
    reverse_hasSpeedBound p hbound
  have hC0 : 0 ≤ C := by
    calc
      0 ≤ ‖(p.state 0).snd‖ := norm_nonneg _
      _ ≤ C := hbound 0 p.zero_mem
  have hupper : ∀ t ∈ pr.domain, t < -a := by
    intro t ht
    change -t ∈ p.domain at ht
    have h := hlower (-t) ht
    linarith
  have hcofinalUpper : ∀ b < -a, ∃ t ∈ pr.domain, b < t := by
    intro b hb
    obtain ⟨s, hs, hslt⟩ := hcofinal (-b) (by linarith)
    refine ⟨-s, ?_, ?_⟩
    · change -(-s) ∈ p.domain
      simpa using hs
    · linarith
  obtain ⟨c, hcurve⟩ := exists_tendsto_nhdsLT_curve_of_upper_cofinal
    (I := I) (M := M) hcomplete pr hupper hcofinalUpper
      hC0 hprbound
  obtain ⟨qrev, hqbound, hprq, hproper⟩ :=
    exists_extension_of_upper_endpoint hmetric pr hprbound hupper hcofinalUpper hcurve
  refine ⟨unreverse qrev, unreverse_hasSpeedBound qrev hqbound,
    le_unreverse_of_reverse_le hprq,
    proper_unreverse_of_reverse_proper hproper⟩

/-- A proper open preconnected subset of the real line containing zero has a
finite upper or lower endpoint.  Openness makes the chosen supremum or
infimum lie strictly outside the domain, while conditional completeness gives
the cofinality required by endpoint continuation. -/
private theorem upper_or_lower_endpoint_of_domain_ne_univ
    (p : PartialGeodesic (I := I) (M := M) cov x₀ v₀)
    (hne : p.domain ≠ Set.univ) :
    (∃ b : ℝ, (∀ t ∈ p.domain, t < b) ∧
      ∀ a < b, ∃ t ∈ p.domain, a < t) ∨
    (∃ a : ℝ, (∀ t ∈ p.domain, a < t) ∧
      ∀ b > a, ∃ t ∈ p.domain, t < b) := by
  have hmissing : ∃ r : ℝ, r ∉ p.domain := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hne (Set.eq_univ_of_forall h)
  obtain ⟨r, hrnot⟩ := hmissing
  have hrzero : r ≠ 0 := by
    intro hr
    apply hrnot
    simpa [hr] using p.zero_mem
  have hnonempty : p.domain.Nonempty := ⟨0, p.zero_mem⟩
  rcases lt_or_gt_of_ne hrzero with hrneg | hrpos
  · right
    have hBdd : BddBelow p.domain := by
      refine ⟨r, ?_⟩
      intro t ht
      by_contra hnot
      have htr : t < r := lt_of_not_ge hnot
      apply hrnot
      exact p.domain_preconnected.Icc_subset ht p.zero_mem
        ⟨le_of_lt htr, le_of_lt hrneg⟩
    refine ⟨sInf p.domain, ?_, ?_⟩
    · intro t ht
      have hle : sInf p.domain ≤ t := csInf_le hBdd ht
      apply lt_of_le_of_ne hle
      intro hEq
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (p.domain_open.mem_nhds ht)
      have hprev : t - ε / 2 ∈ p.domain := by
        apply hsub
        rw [Metric.mem_ball, Real.dist_eq]
        have hcalc : t - ε / 2 - t = -ε / 2 := by ring
        rw [hcalc, show -ε / 2 = -(ε / 2) by ring,
          abs_neg, abs_of_pos (by linarith)]
        linarith
      have hprevLower : sInf p.domain ≤ t - ε / 2 := csInf_le hBdd hprev
      rw [← hEq] at hprevLower
      linarith
    · intro b hb
      exact exists_lt_of_csInf_lt hnonempty hb
  · left
    have hBdd : BddAbove p.domain := by
      refine ⟨r, ?_⟩
      intro t ht
      by_contra hnot
      have hrt : r < t := lt_of_not_ge hnot
      apply hrnot
      exact p.domain_preconnected.Icc_subset p.zero_mem ht
        ⟨le_of_lt hrpos, le_of_lt hrt⟩
    refine ⟨sSup p.domain, ?_, ?_⟩
    · intro t ht
      have hle : t ≤ sSup p.domain := le_csSup hBdd ht
      apply lt_of_le_of_ne hle
      intro hEq
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (p.domain_open.mem_nhds ht)
      have hnext : t + ε / 2 ∈ p.domain := by
        apply hsub
        rw [Metric.mem_ball, Real.dist_eq]
        have hcalc : t + ε / 2 - t = ε / 2 := by ring
        rw [hcalc, abs_of_pos (by linarith)]
        linarith
      have hnextUpper : t + ε / 2 ≤ sSup p.domain := le_csSup hBdd hnext
      rw [← hEq] at hnextUpper
      linarith
    · intro a ha
      exact exists_lt_of_lt_csSup hnonempty ha

/-- Local existence and the state-level restart theorem provide a nonempty
family of partial geodesics.  The initial domain is deliberately shrunk so
that every one of its points has a coherent local state representative and
the initial speed bound is retained. -/
theorem exists_initial_with_speed_bound
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      HasSpeedBound (I := I) (M := M) ‖v₀‖ p := by
  obtain ⟨γ⟩ := exists_localGeodesic (I := I) (M := M) cov x₀ v₀
  obtain ⟨ρ, hρ, hρsol, hρspeed⟩ :=
    exists_local_norm_velocity_eq_initial (I := I) (M := M) γ hmetric
  have hrestart := LocalGeodesic.eventually_exists_restartedLocalGeodesic_state
    (I := I) (M := M) γ hmetric
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hrestart
  let r : ℝ := min (min (γ.solution.radius / 2) (δ / 2)) ρ
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (lt_min (by linarith [γ.solution.radius_pos]) (by linarith)) hρ
  let S : Set ℝ := Ioo (-r) r
  let q : ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _) :=
    fun t ↦ if t ∈ S then localState γ t else ⟨x₀, v₀⟩
  refine ⟨{
    domain := S
    domain_open := isOpen_Ioo
    domain_preconnected := isPreconnected_Ioo
    zero_mem := by
      change -r < 0 ∧ 0 < r
      constructor <;> linarith
    state := q
    state_zero := by
      have hzero : (0 : ℝ) ∈ S := by
        change -r < 0 ∧ 0 < r
        constructor <;> linarith
      simp only [q, hzero, localState]
      exact Bundle.TotalSpace.ext (LocalGeodesic.curve_initial γ)
        (heq_of_eq (by simpa [LocalGeodesic.curve_initial γ] using
          LocalGeodesic.velocity_initial γ))
    state_outside := by
      intro t ht
      simp [q, ht]
    local_germ := ?_ }, ?_⟩
  · intro t ht
    have htr : |t| < r := by
      rw [abs_lt]
      exact ht
    have hrinner : r ≤ min (γ.solution.radius / 2) (δ / 2) := min_le_left _ _
    have hrδ : r ≤ δ / 2 := hrinner.trans (min_le_right _ _)
    have htδ : t ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      calc
        |t - 0| = |t| := by rw [sub_zero]
        _ < r := htr
        _ ≤ δ / 2 := hrδ
        _ < δ := by linarith
    obtain ⟨η, hη⟩ := hδsub htδ
    have hqAt : q t = localState γ t := by simp [q, ht]
    rw [hqAt]
    refine ⟨η, ?_⟩
    have hshift : Tendsto (fun s : ℝ ↦ t + s) (𝓝 0) (𝓝 t) := by
      have hconst : ContinuousAt (fun _ : ℝ ↦ t) 0 := continuousAt_const
      have hid : ContinuousAt (fun s : ℝ ↦ s) 0 := continuousAt_id
      change Tendsto ((fun _ : ℝ ↦ t) + fun s : ℝ ↦ s) (𝓝 0) (𝓝 t)
      convert (hconst.add hid).tendsto using 1 <;> simp
    have hSnear : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ S :=
      hshift.eventually (isOpen_Ioo.mem_nhds ht)
    filter_upwards [hSnear, hη] with s hs hstate
    simpa only [q, if_pos hs, localState] using hstate
  · intro t ht
    change t ∈ S at ht
    change ‖(q t).snd‖ ≤ ‖v₀‖
    have hqAt : q t = localState γ t := by simp [q, ht]
    have hrρ : r ≤ ρ := min_le_right _ _
    have htρ : t ∈ Ioo (-ρ) ρ := by
      constructor
      · exact lt_of_le_of_lt (neg_le_neg hrρ) ht.1
      · exact lt_of_lt_of_le ht.2 hrρ
    rw [hqAt]
    change ‖LocalGeodesic.velocity γ t‖ ≤ ‖v₀‖
    rw [hρspeed t htρ]

/-- Forgetting the speed certificate gives the nonempty family used by the
unrestricted maximal-extension construction. -/
theorem nonempty
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent) :
    Nonempty (PartialGeodesic (I := I) (M := M) cov x₀ v₀) := by
  obtain ⟨p, _⟩ := exists_initial_with_speed_bound
    (I := I) (M := M) (cov := cov) (x₀ := x₀) (v₀ := v₀) hmetric
  exact ⟨p⟩

/-- A nonempty chain of partial geodesics has an upper bound.  The only
choice in the construction selects one member of the chain at each time; the
chain order proves that its tangent-bundle state is independent of that
choice. -/
theorem chain_upper_bound
    (c : Set (PartialGeodesic (I := I) (M := M) cov x₀ v₀))
    (hc : IsChain (· ≤ ·) c) (hcne : c.Nonempty) :
    ∃ q : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      (∀ p ∈ c, p ≤ q) ∧
        ∀ t ∈ q.domain, ∃ p ∈ c, t ∈ p.domain := by
  classical
  let ι := {p : PartialGeodesic (I := I) (M := M) cov x₀ v₀ // p ∈ c}
  let U : Set ℝ := ⋃ p : ι, p.1.domain
  have hUopen : IsOpen U := by
    exact isOpen_iUnion fun p ↦ p.1.domain_open
  have hUpreconnected : IsPreconnected U := by
    apply isPreconnected_iUnion
    · refine ⟨0, ?_⟩
      simp only [Set.mem_iInter]
      intro p
      exact p.1.zero_mem
    · intro p
      exact p.1.domain_preconnected
  have hchoose : ∀ t : ℝ, t ∈ U → ∃ p : ι, t ∈ p.1.domain := by
    intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨p, hp⟩
    exact ⟨p, hp⟩
  let pick : ∀ t : ℝ, t ∈ U → ι := fun t ht ↦ Classical.choose (hchoose t ht)
  have hpick : ∀ t (ht : t ∈ U), t ∈ (pick t ht).1.domain := by
    intro t ht
    exact Classical.choose_spec (hchoose t ht)
  have hstate_eq : ∀ {p q : ι} {t : ℝ},
      t ∈ p.1.domain → t ∈ q.1.domain → p.1.state t = q.1.state t := by
    intro p q t htp htq
    rcases hc.total p.2 q.2 with hpq | hqp
    · exact hpq.2 t htp
    · exact (hqp.2 t htq).symm
  let qstate : ℝ → Bundle.TotalSpace E (TangentSpace I : M → Type _) :=
    fun t ↦ if ht : t ∈ U then (pick t ht).1.state t else ⟨x₀, v₀⟩
  have hqstate_of_mem : ∀ (p : ι) {t : ℝ}, t ∈ p.1.domain →
      qstate t = p.1.state t := by
    intro p t ht
    have htU : t ∈ U := Set.mem_iUnion.mpr ⟨p, ht⟩
    rw [show qstate t = (pick t htU).1.state t by simp only [qstate, dif_pos htU]]
    exact hstate_eq (hpick t htU) ht
  refine ⟨{
    domain := U
    domain_open := hUopen
    domain_preconnected := hUpreconnected
    zero_mem := by
      obtain ⟨p, hp⟩ := hcne
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, p.zero_mem⟩
    state := qstate
    state_zero := by
      obtain ⟨p, hp⟩ := hcne
      calc
        qstate 0 = p.state 0 := hqstate_of_mem ⟨p, hp⟩ p.zero_mem
        _ = ⟨x₀, v₀⟩ := p.state_zero
    state_outside := by
      intro t ht
      simp only [qstate, dif_neg ht]
    local_germ := ?_ }, ?_, ?_⟩
  · intro t ht
    let p : ι := pick t ht
    have hpt : t ∈ p.1.domain := hpick t ht
    have hqpt : qstate t = p.1.state t := hqstate_of_mem p hpt
    rw [hqpt]
    obtain ⟨γ, hγ⟩ := p.1.local_germ t hpt
    refine ⟨γ, ?_⟩
    have hshift : Tendsto (fun s : ℝ ↦ t + s) (𝓝 0) (𝓝 t) := by
      have hconst : ContinuousAt (fun _ : ℝ ↦ t) 0 := continuousAt_const
      have hid : ContinuousAt (fun s : ℝ ↦ s) 0 := continuousAt_id
      change Tendsto ((fun _ : ℝ ↦ t) + fun s : ℝ ↦ s) (𝓝 0) (𝓝 t)
      convert (hconst.add hid).tendsto using 1 <;> simp
    have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ p.1.domain :=
      hshift.eventually (p.1.domain_open.mem_nhds hpt)
    filter_upwards [hnear, hγ] with s hs hstate
    calc
      qstate (t + s) = p.1.state (t + s) := hqstate_of_mem p hs
      _ = localState γ s := hstate
  · intro p hp
    refine ⟨?_, ?_⟩
    · intro t ht
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ht⟩
    · intro t ht
      exact (hqstate_of_mem ⟨p, hp⟩ ht).symm
  · intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨p, hp⟩
    exact ⟨p.1, p.2, hp⟩

/-- The chain union preserves any fixed intrinsic speed bound. -/
theorem chain_upper_bound_of_speed_bound
    {C : ℝ} (c : Set (PartialGeodesic (I := I) (M := M) cov x₀ v₀))
    (hc : IsChain (· ≤ ·) c) (hcne : c.Nonempty)
    (hC : ∀ p ∈ c, HasSpeedBound (I := I) (M := M) C p) :
    ∃ q : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      HasSpeedBound (I := I) (M := M) C q ∧
        (∀ p ∈ c, p ≤ q) ∧ ∀ t ∈ q.domain, ∃ p ∈ c, t ∈ p.domain := by
  obtain ⟨q, hq, hcover⟩ := chain_upper_bound (I := I) (M := M)
    (cov := cov) (x₀ := x₀) (v₀ := v₀) c hc hcne
  refine ⟨q, ?_, hq, hcover⟩
  intro t ht
  obtain ⟨p, hp, hpt⟩ := hcover t ht
  have hpq : p ≤ q := hq p hp
  have hstate : p.state t = q.state t := hpq.2 t hpt
  rw [← hstate]
  exact hC p hp t hpt

/-- A maximal partial state can be chosen while retaining the initial speed
bound.  This is the Zorn object used in the metric endpoint argument. -/
theorem exists_maximal_with_speed_bound
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      HasSpeedBound (I := I) (M := M) ‖v₀‖ p ∧
        Maximal (HasSpeedBound (I := I) (M := M) ‖v₀‖) p := by
  obtain ⟨p₀, hp₀⟩ := exists_initial_with_speed_bound
    (I := I) (M := M) (cov := cov) (x₀ := x₀) (v₀ := v₀) hmetric
  let S : Set (PartialGeodesic (I := I) (M := M) cov x₀ v₀) :=
    {p | HasSpeedBound (I := I) (M := M) ‖v₀‖ p}
  have hp₀S : p₀ ∈ S := hp₀
  obtain ⟨p, _, hpmax⟩ := zorn_le_nonempty₀ S (by
    intro c hcS hc y hy
    have hcne : c.Nonempty := ⟨y, hy⟩
    obtain ⟨q, hqbound, hq, _⟩ := chain_upper_bound_of_speed_bound
      (I := I) (M := M) (cov := cov) (x₀ := x₀) (v₀ := v₀)
      c hc hcne (fun z hz ↦ hcS hz)
    refine ⟨q, hqbound, ?_⟩
    intro z hz
    exact hq z hz) p₀ hp₀S
  exact ⟨p, hpmax.prop, hpmax⟩

/-- A strict endpoint extension which preserves the initial speed bound
forces the maximal state to have full real domain. -/
theorem exists_globalGeodesic_of_bounded_strict_extension
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (hextend : ∀ p : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      HasSpeedBound (I := I) (M := M) ‖v₀‖ p → p.domain ≠ Set.univ →
        ∃ q : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
          HasSpeedBound (I := I) (M := M) ‖v₀‖ q ∧ p ≤ q ∧ p.domain ⊂ q.domain) :
    Nonempty (GlobalGeodesic (I := I) (M := M) cov x₀ v₀) := by
  obtain ⟨p, hpbound, hpmax⟩ := exists_maximal_with_speed_bound
    (I := I) (M := M) (cov := cov) (x₀ := x₀) (v₀ := v₀) hmetric
  have hdomain : p.domain = Set.univ := by
    by_contra hne
    obtain ⟨q, hqbound, hpq, hproper⟩ := hextend p hpbound hne
    have hqp : q ≤ p := hpmax.2 hqbound hpq
    exact hproper.2 hqp.1
  refine ⟨{
    state := p.state
    state_zero := p.state_zero
    local_germ := ?_ }⟩
  intro t
  exact p.local_germ t (by simpa [hdomain])

/-- Geodesic completeness in the finite Riemannian metric produces a global
intrinsic geodesic through every prescribed point and tangent vector.  A
maximal bounded partial geodesic cannot stop at either finite endpoint: its
base curve has a metric limit, and the local endpoint construction extends
the complete tangent state past that endpoint. -/
theorem exists_globalGeodesic_of_complete
    [ConnectedSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (hcomplete : @CompleteSpace M
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace.toUniformSpace) :
    Nonempty (GlobalGeodesic (I := I) (M := M) cov x₀ v₀) := by
  apply exists_globalGeodesic_of_bounded_strict_extension
    (I := I) (M := M) (cov := cov) (x₀ := x₀) (v₀ := v₀) hmetric
  intro p hbound hne
  rcases upper_or_lower_endpoint_of_domain_ne_univ p hne with hupper | hlower
  · obtain ⟨b, hupper, hcofinal⟩ := hupper
    obtain ⟨c, hcurve⟩ := exists_tendsto_nhdsLT_curve_of_upper_cofinal
      (I := I) (M := M) hcomplete p hupper hcofinal
        (norm_nonneg v₀) hbound
    exact exists_extension_of_upper_endpoint hmetric p hbound hupper hcofinal hcurve
  · obtain ⟨a, hlower, hcofinal⟩ := hlower
    exact exists_extension_of_lower_endpoint hmetric hcomplete p hbound hlower hcofinal

/-- Zorn's lemma supplies a maximal coherent partial geodesic. -/
theorem exists_maximal
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ p : PartialGeodesic (I := I) (M := M) cov x₀ v₀, IsMax p := by
  letI : Nonempty (PartialGeodesic (I := I) (M := M) cov x₀ v₀) :=
    nonempty (I := I) (M := M) (cov := cov) (x₀ := x₀) (v₀ := v₀) hmetric
  apply zorn_le_nonempty
  intro c hc hcne
  obtain ⟨q, hq, _⟩ := chain_upper_bound (I := I) (M := M)
    (cov := cov) (x₀ := x₀) (v₀ := v₀) c hc hcne
  exact ⟨q, hq⟩

/-- If every non-global partial geodesic admits a strict coherent extension,
the maximal state is defined on all real times.  This isolates the one
geometric obligation of the continuation proof: rule out a finite endpoint.
-/
theorem exists_globalGeodesic_of_strict_extension
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (hextend : ∀ p : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
      p.domain ≠ Set.univ →
        ∃ q : PartialGeodesic (I := I) (M := M) cov x₀ v₀,
          p ≤ q ∧ p.domain ⊂ q.domain) :
    Nonempty (GlobalGeodesic (I := I) (M := M) cov x₀ v₀) := by
  obtain ⟨p, hpmax⟩ := exists_maximal (I := I) (M := M)
    (cov := cov) (x₀ := x₀) (v₀ := v₀) hmetric
  have hdomain : p.domain = Set.univ := by
    by_contra hne
    obtain ⟨q, hpq, hproper⟩ := hextend p hne
    have hpqeq : p = q := hpmax.eq_of_le hpq
    exact hproper.ne (congrArg PartialGeodesic.domain hpqeq)
  refine ⟨{
    state := p.state
    state_zero := p.state_zero
    local_germ := ?_ }⟩
  intro t
  exact p.local_germ t (by simpa [hdomain])

end PartialGeodesic

namespace GlobalGeodesic

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- The total space of the tangent bundle is Hausdorff when the base
manifold is Hausdorff.  Equal-base points are separated in a local tangent
trivialization; distinct base points are separated after projection. -/
private theorem tangentTotalSpace_t2 :
    T2Space (Bundle.TotalSpace E (TangentSpace I : M → Type _)) := by
  constructor
  intro z w hzw
  rcases z with ⟨x, v⟩
  rcases w with ⟨y, w⟩
  by_cases hxy : x = y
  · subst y
    let e := trivializationAt E (TangentSpace I : M → Type _) x
    have hxbase : x ∈ e.baseSet := by
      change x ∈ (chartAt H x).source
      exact mem_chart_source (H := H) x
    have hvsource : (⟨x, v⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) ∈ e.source :=
      e.mem_source.mpr hxbase
    have hwsource : (⟨x, w⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) ∈ e.source :=
      e.mem_source.mpr hxbase
    have hcoord : (e ⟨x, v⟩).2 ≠ (e ⟨x, w⟩).2 := by
      intro h
      apply hzw
      apply e.injOn hvsource hwsource
      exact Prod.ext (by simp [e]) h
    obtain ⟨U, V, hU, hV, huv, hwv, hUV⟩ := t2_separation hcoord
    refine ⟨e.source ∩ e ⁻¹' (e.baseSet ×ˢ U),
      e.source ∩ e ⁻¹' (e.baseSet ×ˢ V),
      e.isOpen_inter_preimage (e.open_baseSet.prod hU),
      e.isOpen_inter_preimage (e.open_baseSet.prod hV), ?_, ?_, ?_⟩
    · constructor
      · exact hvsource
      · refine ⟨hxbase, ?_⟩
        exact huv
    · constructor
      · exact hwsource
      · refine ⟨hxbase, ?_⟩
        exact hwv
    · refine Set.disjoint_left.2 ?_
      intro q hqU hqV
      exact Set.disjoint_left.1 hUV hqU.2.2 hqV.2.2
  · obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
    let projMap : Bundle.TotalSpace E (TangentSpace I : M → Type _) → M :=
      Bundle.TotalSpace.proj
    refine ⟨projMap ⁻¹' U, projMap ⁻¹' V,
      hU.preimage (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)),
      hV.preimage (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)), ?_, ?_, ?_⟩
    · exact hxU
    · exact hyV
    · exact hUV.preimage projMap

/-- Re-index a local geodesic along an equality of its complete initial
tangent-bundle state.  This is the explicit dependent-fibre bridge used when
two global-geodesic presentations have the same state but not definitionally
the same starting fibre. -/
noncomputable def castInitialState
    {x y : M} {v : TangentSpace I x} {w : TangentSpace I y}
    (h : (⟨x, v⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) = ⟨y, w⟩)
    (γ : LocalGeodesic (I := I) (M := M) cov y w) :
    LocalGeodesic (I := I) (M := M) cov x v :=
  Eq.mp (by cases h; rfl) γ

@[simp] theorem localState_castInitialState
    {x y : M} {v : TangentSpace I x} {w : TangentSpace I y}
    (h : (⟨x, v⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) = ⟨y, w⟩)
    (γ : LocalGeodesic (I := I) (M := M) cov y w) :
    localState (castInitialState h γ) = localState γ := by
  cases h
  rfl

/-- Two global geodesics which have the same complete state at a time agree
on a neighbourhood of that time. -/
theorem eventuallyEq_state_of_state_eq
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ δ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    {t : ℝ} (hstate : γ.state t = δ.state t) :
    (fun s ↦ γ.state (t + s)) =ᶠ[𝓝 (0 : ℝ)]
      fun s ↦ δ.state (t + s) := by
  obtain ⟨α, hα⟩ := γ.local_germ t
  obtain ⟨β, hβ⟩ := δ.local_germ t
  let β' := castInitialState hstate β
  have hβ' : (fun s ↦ δ.state (t + s)) =ᶠ[𝓝 (0 : ℝ)] localState β' := by
    simpa [β'] using hβ
  obtain ⟨hcurve, hvelocity⟩ :=
    eventuallyEq_curve_velocity_of_same_initial cov
      (γ.state t).proj (γ.state t).snd α β'
  filter_upwards [hα, hβ', hcurve, hvelocity] with s hsα hsβ hcurve hvelocity
  calc
    γ.state (t + s) = localState α s := hsα
    _ = localState β' s := by
      exact Bundle.TotalSpace.ext hcurve hvelocity
    _ = δ.state (t + s) := hsβ.symm

/-- Every global geodesic state curve is continuous. -/
theorem continuousAt_state
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    ContinuousAt γ.state t := by
  obtain ⟨α, hα⟩ := γ.local_germ t
  have hlocal : ContinuousAt (localState α) 0 :=
    continuousAt_localState_zero α
  have hshift : ContinuousAt (fun s : ℝ ↦ s - t) t :=
    continuousAt_id.sub continuousAt_const
  have hcomp : ContinuousAt (fun s : ℝ ↦ localState α (s - t)) t := by
    change ContinuousAt (localState α ∘ fun s : ℝ ↦ s - t) t
    exact hlocal.comp_of_eq hshift (by simp)
  have hshiftT : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
    change Tendsto (fun s : ℝ ↦ s - t) (𝓝 t)
      (𝓝 ((fun s : ℝ ↦ s - t) t)) at hshift
    simpa only [sub_self] using hshift
  have hnear : γ.state =ᶠ[𝓝 t] (fun s ↦ localState α (s - t)) := by
    have hraw := hshiftT.eventually hα
    filter_upwards [hraw] with s hs
    rw [show t + (s - t) = s by ring] at hs
    exact hs
  exact hcomp.congr_of_eventuallyEq hnear

/-- Global geodesics with the same prescribed initial state have identical
tangent-bundle state curves. -/
theorem state_eq_of_same_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ δ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) :
    γ.state = δ.state := by
  letI : T2Space (Bundle.TotalSpace E (TangentSpace I : M → Type _)) :=
    tangentTotalSpace_t2 (I := I) (M := M)
  let S : Set ℝ := {t | γ.state t = δ.state t}
  have hγcont : Continuous γ.state :=
    continuous_iff_continuousAt.2 (fun t ↦ continuousAt_state γ t)
  have hδcont : Continuous δ.state :=
    continuous_iff_continuousAt.2 (fun t ↦ continuousAt_state δ t)
  have hclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_eq hγcont hδcont
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    change γ.state t = δ.state t at ht
    have hlocal := eventuallyEq_state_of_state_eq γ δ ht
    have hsub : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
      have hcont : ContinuousAt (fun s : ℝ ↦ s - t) t :=
        continuousAt_id.sub continuousAt_const
      change Tendsto (fun s : ℝ ↦ s - t) (𝓝 t)
        (𝓝 ((fun s : ℝ ↦ s - t) t)) at hcont
      simpa only [sub_self] using hcont
    have hnear := hsub.eventually hlocal
    filter_upwards [hnear] with s hs
    change γ.state s = δ.state s
    rw [show t + (s - t) = s by ring] at hs
    exact hs
  have hzero : (0 : ℝ) ∈ S := by
    change γ.state 0 = δ.state 0
    rw [γ.state_zero, δ.state_zero]
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ (⟨hclosed, hopen⟩ : IsClopen S) ⟨0, hzero⟩
  funext t
  have ht : t ∈ S := by rw [hSuniv]; exact Set.mem_univ t
  exact ht

/-- A global geodesic is determined by its state curve. -/
theorem eq_of_state_eq
    {γ δ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    (hstate : γ.state = δ.state) : γ = δ := by
  cases γ with
  | mk γstate γzero γlocal =>
    cases δ with
    | mk δstate δzero δlocal =>
      change γstate = δstate at hstate
      subst δstate
      rfl

/-- There is at most one global geodesic through a prescribed point and
tangent vector. -/
theorem eq_of_same_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ δ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) : γ = δ :=
  eq_of_state_eq (state_eq_of_same_initial γ δ)

/-- A global geodesic agrees near the initial time with every local geodesic
constructed from the same point and tangent vector. -/
theorem agrees_locally
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (α : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    γ.state =ᶠ[𝓝 (0 : ℝ)] localState α := by
  obtain ⟨β, hβ⟩ := γ.local_germ 0
  let β' := castInitialState γ.state_zero.symm β
  have hβ' : γ.state =ᶠ[𝓝 (0 : ℝ)] localState β' := by
    simpa [β'] using hβ
  obtain ⟨hcurve, hvelocity⟩ :=
    eventuallyEq_curve_velocity_of_same_initial cov x₀ v₀ α β'
  filter_upwards [hβ', hcurve, hvelocity] with s hs hcurve hvelocity
  calc
    γ.state s = localState β' s := hs
    _ = localState α s := by
      exact Bundle.TotalSpace.ext hcurve.symm hvelocity.symm

/-- Under the complete finite Riemannian metric hypotheses, a global
geodesic exists through the prescribed initial state and every other such
global geodesic is equal to it. -/
theorem exists_and_unique_of_complete
    [ConnectedSpace M] [T3Space M]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hmetric : cov.IsMetricCompatibleTangent)
    (hcomplete : @CompleteSpace M
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace.toUniformSpace) :
    ∃ γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀,
      ∀ δ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀, δ = γ := by
  obtain ⟨γ⟩ := PartialGeodesic.exists_globalGeodesic_of_complete
    (I := I) (M := M) (cov := cov) (x₀ := x₀) (v₀ := v₀) hmetric hcomplete
  exact ⟨γ, fun δ ↦ eq_of_same_initial δ γ⟩

end GlobalGeodesic

end IntrinsicGeodesic

end BonnetMyersEntry
