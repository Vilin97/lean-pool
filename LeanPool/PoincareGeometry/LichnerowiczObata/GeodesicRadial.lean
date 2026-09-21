/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicHessian

/-! # The radial parameter along geodesics from the maximum pole -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
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

local notation "TM" => (TangentSpace I : M → Type _)

/-- Before the antipodal phase, the radial parameter along a geodesic
from the maximum pole is its initial metric speed times elapsed time. -/
theorem coordinate_geodesic_obataRadial_eq
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm (α 0).1) = 0)
    (hmax : f ((extChartAt I c).symm (α 0).1) = a)
    {t : ℝ} (ht : t ∈ T) (htnonneg : 0 ≤ t)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c
      (α 0).1 (α 0).2 (α 0).2) * t ≤ Real.pi) :
    obataRadial K a f ((extChartAt I c).symm (α t).1) =
      Real.sqrt (coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2) * t := by
  have hcos := coordinate_geodesic_obata_eq_cos cov hm b hf hK.le hH c
    hT hconn hzero hz hα hcrit ht
  rw [hmax] at hcos
  rw [obataRadial, hcos, mul_div_cancel_left₀ _ ha.ne',
    Real.arccos_cos (mul_nonneg (Real.sqrt_nonneg _) htnonneg) hphase,
    Real.sqrt_mul hK.le]
  field_simp

/-- Positive geodesic phases strictly before the antipodal phase lie in
the regular region of the Obata function. -/
theorem coordinate_geodesic_obata_regular
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 ≤ K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm (α 0).1) = 0)
    (hmax : f ((extChartAt I c).symm (α 0).1) = a)
    {t : ℝ} (ht : t ∈ T)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c
      (α 0).1 (α 0).2 (α 0).2) * t ∈ Ioo 0 Real.pi) :
    -a < f ((extChartAt I c).symm (α t).1) ∧
      f ((extChartAt I c).symm (α t).1) < a := by
  have hcos := coordinate_geodesic_obata_eq_cos cov hm b hf hK hH c
    hT hconn hzero hz hα hcrit ht
  rw [hmax] at hcos
  have hlo := Real.strictAntiOn_cos ⟨hphase.1.le, hphase.2.le⟩
    ⟨Real.pi_pos.le, le_rfl⟩ hphase.2
  have hhi := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩
    ⟨hphase.1.le, hphase.2.le⟩ hphase.1
  simp only [Real.cos_pi, Real.cos_zero] at hlo hhi
  constructor <;> nlinarith [mul_pos ha (sub_pos.mpr hlo), mul_pos ha (sub_pos.mpr hhi)]

/-- At a strictly intermediate positive phase, the radial coordinate along
the geodesic has derivative equal to its constant initial metric speed. -/
theorem hasDerivAt_coordinate_geodesic_obataRadial
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm (α 0).1) = 0)
    (hmax : f ((extChartAt I c).symm (α 0).1) = a)
    {t : ℝ} (ht : t ∈ T)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c
      (α 0).1 (α 0).2 (α 0).2) * t ∈ Ioo 0 Real.pi) :
    HasDerivAt (fun s => obataRadial K a f ((extChartAt I c).symm (α s).1))
      (Real.sqrt (coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2)) t := by
  let freq := Real.sqrt (K * coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2)
  let v := Real.sqrt (coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2)
  have hω : 0 ≤ freq := Real.sqrt_nonneg _
  have hnear : ∀ᶠ s in 𝓝 t, freq * s ∈ Ioo 0 Real.pi :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds hphase)
  have he : (fun s => obataRadial K a f ((extChartAt I c).symm (α s).1)) =ᶠ[𝓝 t]
      (fun s => v * s) := by
    filter_upwards [hT.mem_nhds ht, hnear] with s hs hsp
    have hsnonneg : 0 ≤ s := by nlinarith [hsp.1]
    exact coordinate_geodesic_obataRadial_eq cov hm b hf hK ha hH c
      hT hconn hzero hz hα hcrit hmax hs hsnonneg hsp.2.le
  simpa using ((hasDerivAt_id t).const_mul v).congr_of_eventuallyEq he

/-- The intrinsic radial gradient pairs with geodesic velocity to give
the initial metric speed, derived from the radial parameter identity. -/
theorem inner_radial_gradient_coordinate_geodesic_velocity
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm (α 0).1) = 0)
    (hmax : f ((extChartAt I c).symm (α 0).1) = a)
    {t : ℝ} (ht : t ∈ T)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c
      (α 0).1 (α 0).2 (α 0).2) * t ∈ Ioo 0 Real.pi) :
    inner ℝ (gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (α t).1))
      ((trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (α t).1) (α t).2) =
      Real.sqrt (coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2) := by
  let x := (extChartAt I c).symm (α t).1
  have hx : x ∈ (chartAt H c).source := by
    simpa [x] using (extChartAt I c).map_target (hz t ht)
  have hpos : (α t).1 = extChartAt I c x := ((extChartAt I c).right_inv (hz t ht)).symm
  have hreg := coordinate_geodesic_obata_regular cov hm b hf hK.le ha hH c
    hT hconn hzero hz hα hcrit hmax ht hphase
  change -a < f x ∧ f x < a at hreg
  have hlo : -1 < f x / a := (lt_div_iff₀ ha).2 (by nlinarith [hreg.1])
  have hhi : f x / a < 1 := (div_lt_iff₀ ha).2 (by nlinarith [hreg.2])
  have hr : MDiffAt (obataRadial K a f) x :=
    (contMDiffAt_obataRadial (hf x) hlo.ne' hhi.ne).mdifferentiableAt (by norm_num)
  have hp : HasDerivAt (fun s => (α s).1) (α t).2 t :=
    (hasFDerivAt_fst (p := α t)).comp_hasDerivAt t (hα t ht)
  exact (hasDerivAt_chart_curve_value c x hx hr hpos hp).unique
    (hasDerivAt_coordinate_geodesic_obataRadial cov hm b hf hK ha hH c
      hT hconn hzero hz hα hcrit hmax ht hphase)

/-- On a connected manifold satisfying the Obata Hessian equation, a
geodesic from the maximum pole has velocity equal to its initial speed
times the radial gradient throughout the regular positive-phase region. -/
theorem coordinate_geodesic_velocity_eq_radial [PreconnectedSpace M]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K a : ℝ}
    (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α
      (coordinateGeodesicSpray (leviCivitaConnection (I := I)) b c (α s)) s)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm (α 0).1) = 0)
    (hmax : f ((extChartAt I c).symm (α 0).1) = a)
    {t : ℝ} (ht : t ∈ T)
    (hphase : Real.sqrt (K * coordinateMetricBilinear (I := I) c
      (α 0).1 (α 0).2 (α 0).2) * t ∈ Ioo 0 Real.pi) :
    (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (α t).1) (α t).2 =
      Real.sqrt (coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2) •
        gradient (I := I) (obataRadial K a f) ((extChartAt I c).symm (α t).1) := by
  let x := (extChartAt I c).symm (α t).1
  let p := (extChartAt I c).symm (α 0).1
  let N := gradient (I := I) (obataRadial K a f) x
  let v := (trivializationAt E TM c).symmL ℝ x (α t).2
  let e := coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2
  let speed := Real.sqrt e
  have he_nonneg : 0 ≤ e := real_inner_self_nonneg (x :=
    (trivializationAt E TM c).symmL ℝ p (α 0).2)
  have hspeed : speed ^ 2 = e := Real.sq_sqrt he_nonneg
  have hreg := coordinate_geodesic_obata_regular (leviCivitaConnection (I := I))
    leviCivitaConnection_metricCompatible b hf hK.le ha hH c
    hT hconn hzero hz hα hcrit hmax ht hphase
  have hen := obataEnergy_constant hf hH x p
  rw [hcrit, hmax, norm_zero, zero_pow (by norm_num), zero_add] at hen
  have hgrad : ‖gradient (I := I) f x‖ ^ 2 = K * (a ^ 2 - f x ^ 2) := by
    nlinarith [hen]
  have hN : ‖N‖ = 1 := norm_gradient_obataRadial hK ha
    (hf.mdifferentiable (by norm_num) x) hreg hgrad
  have hv := coordinate_geodesic_energy_eq (leviCivitaConnection (I := I))
    leviCivitaConnection_metricCompatible b c hT hconn hz hα ht hzero
  change inner ℝ v v = e at hv
  rw [real_inner_self_eq_norm_sq] at hv
  have hpair := inner_radial_gradient_coordinate_geodesic_velocity
    (leviCivitaConnection (I := I)) leviCivitaConnection_metricCompatible b hf hK ha hH c
    hT hconn hzero hz hα hcrit hmax ht hphase
  change inner ℝ N v = speed at hpair
  have hdiff := norm_sub_sq_real v (speed • N)
  rw [real_inner_smul_right, real_inner_comm N v, hpair, norm_smul, hN,
    mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg e), hv, hspeed] at hdiff
  have heq : ‖v - speed • N‖ = 0 := by nlinarith [norm_nonneg (v - speed • N)]
  exact sub_eq_zero.mp (norm_eq_zero.mp heq)

end LichnerowiczObata
