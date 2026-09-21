/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.GlobalGeodesic
import LeanPool.PoincareGeometry.BonnetMyers.CurveConnection

/-!
# Intrinsic acceleration of global geodesic germs

The maximal-extension construction stores a global geodesic as tangent-bundle
state germs.  This module connects that storage-level description to the
chart-free covariant-acceleration predicate.  It does not assert endpoint
minimization; it proves the independent fact that every local germ of the
global ODE solution is an actual zero-acceleration germ.
-/

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

local notation "TM" => (TangentSpace I : M → Type _)

namespace IntrinsicGeodesic
namespace LocalGeodesic

open CurveConnection

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- The local coordinate construction has zero covariant acceleration when
expressed with its actual tangent-valued velocity, not merely with a
smooth-frame representative. -/
theorem isCovariantAccelerationAt_velocity_zero
    (α : LocalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) :
    IsCovariantAccelerationAt cov (curve α) (velocity α) 0 (velocity α 0) 0 := by
  have hacc :=
    (CurveConnection.localGeodesic_eventually_isCovariantAccelerationAt_zero
      (I := I) (M := M) α hmetric).self_of_nhds
  change IsCovariantAccelerationAt cov (curve α)
    (CurveConnection.canonicalFrameVelocity α) 0
    (CurveConnection.canonicalFrameVelocity α 0) 0 at hacc
  have hvelocity :=
    CurveConnection.localGeodesic_eventually_canonicalFrameVelocity_eq_velocity
      (I := I) (M := M) α
  have hacc' := hacc.congr_of_eventuallyEq hvelocity
  rw [hvelocity.self_of_nhds] at hacc'
  exact hacc'

end LocalGeodesic

namespace GlobalGeodesic

open CurveConnection

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

/-- At every global time, the stored state agrees with a local curve whose
actual velocity has zero covariant acceleration at its centre.  This is the
intrinsic counterpart of the coordinate ODE datum used by global extension. -/
theorem exists_zeroAcceleration_local_germ
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ α : LocalGeodesic (I := I) (M := M) cov (curve γ t) (velocity γ t),
      (fun s ↦ γ.state (t + s)) =ᶠ[𝓝 (0 : ℝ)] localState α ∧
      IsCovariantAccelerationAt cov (LocalGeodesic.curve α)
        (LocalGeodesic.velocity α) 0 (LocalGeodesic.velocity α 0) 0 := by
  obtain ⟨α, hagrees⟩ := γ.local_germ t
  exact ⟨α, hagrees,
    LocalGeodesic.isCovariantAccelerationAt_velocity_zero
      (I := I) (M := M) α hmetric⟩

/-- The speed of a global geodesic is locally constant.  The equality is
proved through the complete tangent-bundle state germ, so it is insensitive
to changes of the local coordinate chart used by successive ODE solutions. -/
theorem eventually_norm_velocity_eq
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) (hmetric : cov.IsMetricCompatibleTangent) :
    ∀ᶠ s in 𝓝 t, ‖velocity γ s‖ = ‖velocity γ t‖ := by
  obtain ⟨α, hagrees⟩ := γ.local_germ t
  obtain ⟨r, hr, hradius, hnorm⟩ :=
    exists_local_norm_velocity_eq_initial (I := I) (M := M) α hmetric
  have hinter : Ioo (-r) r ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hlocal : ∀ᶠ u in 𝓝 (0 : ℝ),
      ‖velocity γ (t + u)‖ = ‖velocity γ t‖ := by
    filter_upwards [hagrees, hinter] with u hstate hu
    calc
      ‖velocity γ (t + u)‖ = ‖(γ.state (t + u)).snd‖ := rfl
      _ = ‖(localState α u).snd‖ := congrArg (fun z ↦ ‖z.snd‖) hstate
      _ = ‖LocalGeodesic.velocity α u‖ := rfl
      _ = ‖velocity γ t‖ := hnorm u hu
  have hshift : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
    have hraw := (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun s : ℝ ↦ s - t) t).tendsto
    have hfun : (id - fun _ : ℝ ↦ t) = (fun s : ℝ ↦ s - t) := by
      rfl
    rw [hfun] at hraw
    simpa only [sub_self] using hraw
  have htranslated := hshift.eventually hlocal
  filter_upwards [htranslated] with s hs
  have hts : t + (s - t) = s := by ring
  rw [hts] at hs
  exact hs

/-- Metric compatibility makes the norm of a global geodesic velocity equal
to its initial norm on all of real time.  The proof promotes the local state
germ calculation using connectedness of the time line, rather than assuming a
global parallel frame. -/
theorem norm_velocity_eq_initial
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) (t : ℝ) :
    ‖velocity γ t‖ = ‖v₀‖ := by
  let S : Set ℝ := {s | ‖velocity γ s‖ = ‖v₀‖}
  have hzero : (0 : ℝ) ∈ S := by
    change ‖velocity γ 0‖ = ‖v₀‖
    rw [curve_initial γ]
    exact congrArg norm (velocity_initial γ)
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hlocal := eventually_norm_velocity_eq (I := I) (M := M) γ s hmetric
    filter_upwards [hlocal] with q hq
    change ‖velocity γ q‖ = ‖v₀‖
    exact hq.trans hs
  have hcompopen : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    change ¬ ‖velocity γ s‖ = ‖v₀‖ at hs
    have hlocal := eventually_norm_velocity_eq (I := I) (M := M) γ s hmetric
    filter_upwards [hlocal] with q hq
    change ¬ ‖velocity γ q‖ = ‖v₀‖
    intro hqS
    apply hs
    exact hq.symm.trans hqS
  have hclosed : IsClosed S := by
    simpa using hcompopen.isClosed_compl
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ (⟨hclosed, hopen⟩ : IsClopen S) ⟨0, hzero⟩
  have ht : t ∈ S := by
    rw [hSuniv]
    exact Set.mem_univ t
  exact ht

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
private lemma local_contMDiffAt_curve_zero
    (α : LocalGeodesic (I := I) (M := M) cov x₀ v₀) :
    ContMDiffAt (𝓘(ℝ, ℝ)) I 1 (LocalGeodesic.curve α) 0 := by
  let a : ℝ := -α.solution.radius / 2
  let b : ℝ := α.solution.radius / 2
  have ha : -α.solution.radius < a := by
    dsimp [a]
    linarith [α.solution.radius_pos]
  have hab : a < b := by
    dsimp [a, b]
    linarith [α.solution.radius_pos]
  have hb : b < α.solution.radius := by
    dsimp [b]
    linarith [α.solution.radius_pos]
  have hleft : a < (0 : ℝ) := by
    dsimp [a]
    linarith [α.solution.radius_pos]
  have hright : (0 : ℝ) < b := by
    dsimp [b]
    linarith [α.solution.radius_pos]
  change ContMDiffAt (𝓘(ℝ, ℝ)) I 1
    (LocalChartSecondOrderSolution.curve α.solution) 0
  exact (LocalGeodesicData.localChartSecondOrderSolution_contMDiffOn_curve
    (I := I) α.solution ha hb hab).contMDiffAt (Icc_mem_nhds hleft hright)

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- The curve of a global ODE geodesic is genuinely `C¹` at every time.  Its
proof is local in time and therefore preserves the germ-based construction
without choosing a global chart. -/
theorem contMDiffAt_curve
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ)) I 1 (curve γ) t := by
  obtain ⟨α, hagrees⟩ := γ.local_germ t
  have hshift : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
    have hraw := (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun s : ℝ ↦ s - t) t).tendsto
    have hfun : (id - fun _ : ℝ ↦ t) = (fun s : ℝ ↦ s - t) := by
      rfl
    rw [hfun] at hraw
    simpa only [sub_self] using hraw
  have hcurve : curve γ =ᶠ[𝓝 t]
      (fun s ↦ LocalGeodesic.curve α (s - t)) := by
    have hnear := hshift.eventually hagrees
    filter_upwards [hnear] with s hs
    rw [show t + (s - t) = s by ring] at hs
    exact congrArg Bundle.TotalSpace.proj hs
  have hlocal := local_contMDiffAt_curve_zero (I := I) (M := M) α
  have hshiftC : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1
      (fun s : ℝ ↦ s - t) t := by
    have hid : ContDiffAt ℝ 1 (fun s : ℝ ↦ s) t := contDiffAt_id
    have hconst : ContDiffAt ℝ 1 (fun _ : ℝ ↦ t) t := contDiffAt_const
    exact (hid.sub hconst).contMDiffAt
  let σ : ℝ → ℝ := fun s ↦ s - t
  have hlocal' : ContMDiffAt (𝓘(ℝ, ℝ)) I 1
      (LocalGeodesic.curve α) (σ t) := by
    have hσ : σ t = 0 := by simp [σ]
    rw [hσ]
    exact hlocal
  have hcomp := hlocal'.comp t hshiftC
  have hcomp' : ContMDiffAt (𝓘(ℝ, ℝ)) I 1
      (fun s ↦ LocalGeodesic.curve α (s - t)) t := by
    simpa [Function.comp_def, σ] using hcomp
  exact hcomp'.congr_of_eventuallyEq hcurve

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- A global ODE geodesic is `C¹` on every finite time interval. -/
theorem contMDiffOn_curve_Icc
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (a b : ℝ) :
    ContMDiffOn (𝓘(ℝ, ℝ)) I 1 (curve γ) (Icc a b) := by
  apply contMDiffOn_of_locally_contMDiffOn
  intro t ht
  have hcont := contMDiffAt_curve (I := I) (M := M) γ t
  obtain ⟨u, hu, hcontu⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (I := (𝓘(ℝ, ℝ))) (I' := I)
      (n := (1 : WithTop ℕ∞)) (by simp)).mp hcont
  obtain ⟨v, hvsub, hvopen, htv⟩ := mem_nhds_iff.mp hu
  refine ⟨v, hvopen, htv, ?_⟩
  exact hcontu.mono (fun _ hx ↦ hvsub hx.2)

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- The state velocity of a global geodesic is its actual manifold derivative
at every time.  This removes the final coordinate wrapper from the global ODE
curve before it is used in length or variational calculations. -/
theorem hasMFDerivAt_curve
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀) (t : ℝ) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) I (curve γ) t
      (ContinuousLinearMap.toSpanSingleton ℝ (velocity γ t)) := by
  obtain ⟨α, hagrees⟩ := γ.local_germ t
  have hshift : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 0) := by
    have hraw := (continuousAt_id.sub continuousAt_const :
      ContinuousAt (fun s : ℝ ↦ s - t) t).tendsto
    have hfun : (id - fun _ : ℝ ↦ t) = (fun s : ℝ ↦ s - t) := by
      rfl
    rw [hfun] at hraw
    simpa only [sub_self] using hraw
  have hcurve : curve γ =ᶠ[𝓝 t]
      (fun s ↦ LocalGeodesic.curve α (s - t)) := by
    have hnear := hshift.eventually hagrees
    filter_upwards [hnear] with s hs
    rw [show t + (s - t) = s by ring] at hs
    exact congrArg Bundle.TotalSpace.proj hs
  have hzero : (0 : ℝ) ∈ Ioo (-α.solution.radius) α.solution.radius := by
    constructor <;> linarith [α.solution.radius_pos]
  have hlocal := LocalGeodesic.hasMFDerivAt_curve α hzero
  have hshiftDeriv : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun s : ℝ ↦ s - t) t (ContinuousLinearMap.id ℝ _) := by
    have hraw : HasFDerivAt (fun s : ℝ ↦ s - t)
        (ContinuousLinearMap.id ℝ ℝ) t := hasFDerivAt_sub_const t
    exact hraw.hasMFDerivAt
  let σ : ℝ → ℝ := fun s ↦ s - t
  have hlocal' : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (LocalGeodesic.curve α) (σ t)
      (ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity α 0)) := by
    have hσ : σ t = 0 := by simp [σ]
    rw [hσ]
    exact hlocal
  have hcomp := HasMFDerivAt.comp t hlocal' hshiftDeriv
  have hcomp' : HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (fun s ↦ LocalGeodesic.curve α (s - t)) t
      (ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity α 0)) := by
    have hmap :
        (ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity α 0)) ∘SL
          (ContinuousLinearMap.id ℝ _) =
        ContinuousLinearMap.toSpanSingleton ℝ (LocalGeodesic.velocity α 0) := by
      apply ContinuousLinearMap.ext
      intro r
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    exact hcomp.congr_mfderiv hmap
  have hglobal := hcomp'.congr_of_eventuallyEq hcurve
  rw [LocalGeodesic.velocity_initial α] at hglobal
  exact hglobal

/-- In any fixed chart whose smooth coordinate frame agrees on a
neighbourhood of the current point, the coordinate-and-velocity readout of a
global geodesic satisfies the ordinary coordinate geodesic system.  This is
the interval-level uniqueness bridge between a complete intrinsic geodesic
and the cutoff coordinate flow used by a strong normal neighbourhood. -/
theorem hasDerivAt_fixedChartState
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (g : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (c : M) (b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E)
    (hmetric : cov.IsMetricCompatibleTangent) (t : ℝ)
    (hframe : IntrinsicAcceleration.smoothFrameAgreementSet
      (I := I) (M := M) c b ∈ 𝓝 (curve g t)) :
    HasDerivAt (fun s ↦
      (extChartAt I c (curve g s),
        (trivializationAt E (TangentSpace I : M → Type _) c)
          |>.continuousLinearMapAt ℝ (curve g s) (velocity g s)))
      (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c b)
        (extChartAt I c (curve g t),
          (trivializationAt E (TangentSpace I : M → Type _) c)
            |>.continuousLinearMapAt ℝ (curve g t) (velocity g t))) t := by
  obtain ⟨α, hα⟩ := g.local_germ t
  have hstate0 : g.state t = localState α 0 := by
    simpa using hα.self_of_nhds
  have hbase0 : LocalGeodesic.curve α 0 = curve g t := by
    exact (congrArg Bundle.TotalSpace.proj hstate0).symm
  have hzero : (0 : ℝ) ∈ Ioo (-α.solution.radius) α.solution.radius := by
    constructor <;> linarith [α.solution.radius_pos]
  have hcurveCont : ContinuousAt (LocalGeodesic.curve α) 0 :=
    (LocalGeodesic.hasMFDerivAt_curve α hzero).continuousAt
  have htarget : ∀ᶠ s in 𝓝 (0 : ℝ),
      LocalGeodesic.curve α s ∈
        IntrinsicAcceleration.smoothFrameAgreementSet
          (I := I) (M := M) c b := by
    apply hcurveCont.preimage_mem_nhds
    rwa [hbase0]
  have hlocal := CurveConnection.localGeodesic_rechart_pair_hasDerivAt_at_zero
    (I := I) (M := M) cov α c b htarget hmetric
  have hinterval : Ioo (-α.solution.radius) α.solution.radius ∈
      𝓝 (0 : ℝ) := Ioo_mem_nhds
        (by linarith [α.solution.radius_pos])
        (by linarith [α.solution.radius_pos])
  have hpair : (fun s ↦
      (extChartAt I c (curve g (t + s)),
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt
          ℝ (curve g (t + s)) (velocity g (t + s)))) =ᶠ[𝓝 0]
      (fun s ↦
        (CurveConnection.rechartCoordinate (I := I) (M := M) α.solution c s,
          CurveConnection.rechartVelocity (I := I) (M := M) α.solution c s)) := by
    filter_upwards [hα, htarget, hinterval] with s hs htargetS hsint
    have hsrc : LocalGeodesic.curve α s ∈ (extChartAt I c).source :=
      htargetS.1
    have hderiv := LocalGeodesic.hasMFDerivAt_curve α hsint
    have hread :=
      CurveConnection.rechartVelocity_eq_trivialization_readout_of_hasMFDerivAt
        (I := I) (M := M) α.solution c b hsint hsrc
          (LocalGeodesic.velocity α s) hderiv
    have hbase := congrArg Bundle.TotalSpace.proj hs
    have hreadState := congrArg
      (fun q : Bundle.TotalSpace E (TangentSpace I : M → Type _) ↦
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt
          ℝ q.proj q.snd) hs
    apply Prod.ext
    · change extChartAt I c (g.state (t + s)).proj =
        extChartAt I c (LocalGeodesic.curve α s)
      exact congrArg (extChartAt I c) hbase
    · calc
        (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt
            ℝ (curve g (t + s)) (velocity g (t + s)) =
          (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt ℝ
              (LocalGeodesic.curve α s) (LocalGeodesic.velocity α s) := by
                convert hreadState using 1 <;> rfl
        _ = CurveConnection.rechartVelocity
            (I := I) (M := M) α.solution c s := hread.symm
  have hshift := hlocal.congr_of_eventuallyEq hpair
  have hpair0 := hpair.self_of_nhds
  dsimp only at hpair0
  have htzero : t + 0 = t := by ring
  rw [htzero] at hpair0
  have hvalue :
      secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c b)
        (CurveConnection.rechartCoordinate (I := I) (M := M) α.solution c 0,
          CurveConnection.rechartVelocity (I := I) (M := M) α.solution c 0) =
      secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c b)
        (extChartAt I c (curve g t),
          (trivializationAt E (TangentSpace I : M → Type _) c).continuousLinearMapAt
            ℝ (curve g t) (velocity g t)) := by
    have hpair0' :
        (extChartAt I c (curve g t),
          (trivializationAt E (TangentSpace I : M → Type _) c)
            |>.continuousLinearMapAt ℝ (curve g t) (velocity g t)) =
        (CurveConnection.rechartCoordinate (I := I) (M := M) α.solution c 0,
          CurveConnection.rechartVelocity (I := I) (M := M) α.solution c 0) := by
      exact hpair0
    exact congrArg
      (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c b))
      hpair0'.symm
  rw [hvalue] at hshift
  have hsub : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
    simpa using (hasDerivAt_id' t).sub_const t
  have hshift' : HasDerivAt (fun s ↦
      (extChartAt I c (curve g (t + s)),
        (trivializationAt E (TangentSpace I : M → Type _) c)
          |>.continuousLinearMapAt ℝ (curve g (t + s)) (velocity g (t + s))))
      (secondOrderSystem (LocalGeodesicData.coordinateAcceleration cov c b)
        (extChartAt I c (curve g t),
          (trivializationAt E (TangentSpace I : M → Type _) c)
            |>.continuousLinearMapAt ℝ (curve g t) (velocity g t))) (t - t) := by
    simpa using hshift
  have hfinal := HasDerivAt.scomp t (h := fun s : ℝ ↦ s - t) hshift' hsub
  have hfun : (fun s ↦
      (extChartAt I c (curve g (t + (s - t))),
        (trivializationAt E (TangentSpace I : M → Type _) c)
          |>.continuousLinearMapAt ℝ
            (curve g (t + (s - t))) (velocity g (t + (s - t))))) =
      (fun s ↦
        (extChartAt I c (curve g s),
          (trivializationAt E (TangentSpace I : M → Type _) c)
            |>.continuousLinearMapAt ℝ (curve g s) (velocity g s))) := by
    funext s
    rw [show t + (s - t) = s by ring]
  simpa only [Function.comp_def, hfun, one_smul] using hfinal

/-- A global ODE geodesic has exactly constant-speed Riemannian path length
on every finite time interval.  This is obtained from its genuine manifold
derivative and the globally propagated speed identity, rather than from a
single coordinate chart. -/
theorem pathELength_eq_constant_speed_mul
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) (a b : ℝ) :
    pathELength I (curve γ) a b =
      ‖v₀‖ₑ * ENNReal.ofReal (b - a) := by
  rw [pathELength_eq_lintegral_mfderiv_Ioo]
  rw [show (∫⁻ t in Ioo a b, ‖mfderiv% (curve γ) t 1‖ₑ) =
      ∫⁻ _t in Ioo a b, ‖v₀‖ₑ by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
    intro t ht
    change ‖mfderiv% (curve γ) t 1‖ₑ = ‖v₀‖ₑ
    rw [(hasMFDerivAt_curve (I := I) (M := M) γ t).mfderiv]
    change ‖(ContinuousLinearMap.toSpanSingleton ℝ (velocity γ t)) 1‖ₑ = ‖v₀‖ₑ
    rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rw [← ofReal_norm, ← ofReal_norm,
      norm_velocity_eq_initial (I := I) (M := M) γ hmetric t]]
  rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]

/-- Consequently, the intrinsic Riemannian distance along a global ODE
geodesic is bounded by its constant speed times elapsed time.  Unlike the
earlier local estimate, this applies directly to arbitrary real times. -/
theorem riemannianEDist_le_constant_speed_mul
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (hmetric : cov.IsMetricCompatibleTangent) {a b : ℝ} (hab : a ≤ b) :
    riemannianEDist I (curve γ a) (curve γ b) ≤
      ‖v₀‖ₑ * ENNReal.ofReal (b - a) := by
  calc
    riemannianEDist I (curve γ a) (curve γ b) ≤ pathELength I (curve γ) a b :=
      riemannianEDist_le_pathELength
        (contMDiffOn_curve_Icc (I := I) (M := M) γ a b) rfl rfl hab
    _ = ‖v₀‖ₑ * ENNReal.ofReal (b - a) :=
      pathELength_eq_constant_speed_mul (I := I) (M := M) γ hmetric a b

/-- The tangent velocity stored by a global geodesic has zero covariant
acceleration at every time.  The proof passes through the certified local
state germ and explicitly transports the scalar derivative across the time
translation; no global chart or global frame is selected. -/
theorem isCovariantAccelerationAt_velocity_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀)
    (t : ℝ) (hmetric : cov.IsMetricCompatibleTangent) :
    IsCovariantAccelerationAt cov (curve γ) (velocity γ) t (velocity γ t) 0 := by
  unfold IsCovariantAccelerationAt
  intro W hW
  obtain ⟨α, hagrees, hlocal⟩ :=
    exists_zeroAcceleration_local_germ (I := I) (M := M) γ t hmetric
  have hscalar :
      (fun s ↦ inner ℝ (velocity γ (t + s)) (W (curve γ (t + s)))) =ᶠ[𝓝 (0 : ℝ)]
        (fun s ↦ inner ℝ (LocalGeodesic.velocity α s)
          (W (LocalGeodesic.curve α s))) := by
    filter_upwards [hagrees] with s hs
    change inner ℝ (γ.state (t + s)).snd (W (γ.state (t + s)).proj) =
      inner ℝ (LocalGeodesic.velocity α s) (W (LocalGeodesic.curve α s))
    rw [hs]
    rfl
  have htranslate :
      curveScalarDeriv (fun s ↦ inner ℝ (velocity γ s) (W (curve γ s))) t =
        curveScalarDeriv (fun s ↦ inner ℝ (LocalGeodesic.velocity α s)
          (W (LocalGeodesic.curve α s))) 0 :=
    CurveConnection.curveScalarDeriv_eq_of_eventuallyEq_const_add
      (f := fun s ↦ inner ℝ (velocity γ s) (W (curve γ s)))
      (g := fun s ↦ inner ℝ (LocalGeodesic.velocity α s)
        (W (LocalGeodesic.curve α s))) (t := t) hscalar
  have hstate0 : γ.state t = localState α 0 := by
    simpa using hagrees.self_of_nhds
  have hWlocal : MDiffAt (T% W) (LocalGeodesic.curve α 0) := by
    change MDiffAt (T% W) (localState α 0).proj
    rw [← hstate0]
    exact hW
  calc
    curveScalarDeriv (fun s ↦ inner ℝ (velocity γ s) (W (curve γ s))) t =
        curveScalarDeriv (fun s ↦ inner ℝ (LocalGeodesic.velocity α s)
          (W (LocalGeodesic.curve α s))) 0 := htranslate
    _ = inner ℝ 0 (W (LocalGeodesic.curve α 0)) +
          inner ℝ (LocalGeodesic.velocity α 0)
            (cov W (LocalGeodesic.curve α 0) (LocalGeodesic.velocity α 0)) :=
      hlocal W hWlocal
    _ = inner ℝ 0 (W (curve γ t)) +
          inner ℝ (velocity γ t) (cov W (curve γ t) (velocity γ t)) := by
      have hterm :
          inner ℝ (LocalGeodesic.velocity α 0)
            (cov W (LocalGeodesic.curve α 0) (LocalGeodesic.velocity α 0)) =
          inner ℝ (velocity γ t) (cov W (curve γ t) (velocity γ t)) := by
        change inner ℝ (localState α 0).snd
          (cov W (localState α 0).proj (localState α 0).snd) =
          inner ℝ (γ.state t).snd
            (cov W (γ.state t).proj (γ.state t).snd)
        rw [← hstate0]
      simpa using hterm

end GlobalGeodesic
end IntrinsicGeodesic

end BonnetMyersEntry
