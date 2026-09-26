/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeodesicEnergy
public import LeanPool.PoincareGeometry.LichnerowiczObata.CoordinateRadialShape
public import LeanPool.PoincareGeometry.LichnerowiczObata.ScalarOscillator

/-! # Hessian evolution alongAlmostSchur actual coordinate geodesics -/

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

/-- Pairing a vector field with geodesic velocity differentiates to its
covariant derivative, with the acceleration term cancelled by the geodesic
equation. All pairings use the actual coordinate metric. -/
theorem hasDerivAt_coordinate_geodesic_field_pairing
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    (X : Π x : M, TM x) (c x : M) (hx : x ∈ (chartAt H c).source)
    (hX : MDiffAt (T% X) x) {α : ℝ → E × E} {t : ℝ}
    (hpos : (α t).1 = extChartAt I c x)
    (hα : HasDerivAt α (coordinateGeodesicSpray cov b c (α t)) t) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (α s).1
      (coordinateVectorField c X (α s).1) (α s).2)
      (inner ℝ (cov X x ((trivializationAt E TM c).symmL ℝ x (α t).2))
        ((trivializationAt E TM c).symmL ℝ x (α t).2)) t := by
  have he : (extChartAt I c).symm (α t).1 = x := by
    rw [hpos]
    exact (extChartAt I c).left_inv (by simpa using hx)
  have hp : HasDerivAt (fun s => (α s).1) (α t).2 t :=
    (hasFDerivAt_fst (p := α t)).comp_hasDerivAt t hα
  have hv : HasDerivAt (fun s => (α s).2)
      (-(frameConnectionCoefficients cov (trivializationAt E TM c) b x
        (α t).2 (α t).2)) t := by
    have hv0 : HasDerivAt (fun s => (α s).2)
        (-(frameConnectionCoefficients cov (trivializationAt E TM c) b
          ((extChartAt I c).symm (α t).1) (α t).2 (α t).2)) t :=
      (hasFDerivAt_snd (p := α t)).comp_hasDerivAt t hα
    rwa [he] at hv0
  have hDX : DifferentiableAt ℝ (coordinateVectorField (I := I) c X) (α t).1 := by
    rw [hpos]
    exact differentiableAt_coordinateVectorField X c x hx hX
  have hu : HasDerivAt (fun s => coordinateVectorField (I := I) c X (α s).1)
      (fderiv ℝ (coordinateVectorField (I := I) c X) (α t).1 (α t).2) t :=
    HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E) (E := E)
      (l := coordinateVectorField (I := I) c X) (f := fun s => (α s).1)
      t hDX.hasFDerivAt hp
  have hc := covariantDerivative_chart cov b X c x hx hX (α t).2
  have hpair := hasDerivAt_coordinateMetric_pairing_connection cov hm b c x hx hpos hp hu hv
  dsimp only at hc hpair
  have hfield : coordinateVectorField (I := I) c X (α t).1 =
      (trivializationAt E TM c).continuousLinearMapAt ℝ x (X x) := by
    unfold coordinateVectorField
    convert congrArg (fun y : M =>
      (trivializationAt E TM c).continuousLinearMapAt ℝ y (X y)) he using 1
  have hsum : fderiv ℝ (coordinateVectorField (I := I) c X) (α t).1 (α t).2 +
      frameConnectionCoefficients cov (trivializationAt E TM c) b x (α t).2
        (coordinateVectorField (I := I) c X (α t).1) =
      (trivializationAt E TM c).continuousLinearMapAt ℝ x
        (cov X x ((trivializationAt E TM c).symmL ℝ x (α t).2)) := by
    rw [hfield, hpos]
    exact (add_comm _ _).trans hc.symm
  rw [hsum] at hpair
  convert hpair using 1
  simp only [neg_add_cancel, map_zero, add_zero, coordinateMetricBilinear_apply]
  rw [he, (trivializationAt E TM c).symmL_continuousLinearMapAt hx]

/-- Along a geodesic, the derivative of the gradient-velocity pairing is
the genuine covariant Hessian evaluated twice on its velocity. -/
theorem hasDerivAt_coordinate_geodesic_gradient_pairing
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f)
    (c x : M) (hx : x ∈ (chartAt H c).source)
    {α : ℝ → E × E} {t : ℝ} (hpos : (α t).1 = extChartAt I c x)
    (hα : HasDerivAt α (coordinateGeodesicSpray cov b c (α t)) t) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (α s).1
      (coordinateVectorField c (gradient (I := I) f) (α s).1) (α s).2)
      (hessian cov f x ((trivializationAt E TM c).symmL ℝ x (α t).2)
        ((trivializationAt E TM c).symmL ℝ x (α t).2)) t :=
  hasDerivAt_coordinate_geodesic_field_pairing cov hm b (gradient (I := I) f) c x hx
    (mdifferentiableAt_gradient (hf x)) hpos hα

/-- The Obata Hessian equation gives the oscillator acceleration alongAlmostSchur a
coordinate geodesic, with its actual squared metric speed as coefficient. -/
theorem hasDerivAt_coordinate_geodesic_obata_pairing
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K : ℝ}
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c x : M) (hx : x ∈ (chartAt H c).source)
    {α : ℝ → E × E} {t : ℝ} (hpos : (α t).1 = extChartAt I c x)
    (hα : HasDerivAt α (coordinateGeodesicSpray cov b c (α t)) t) :
    HasDerivAt (fun s => coordinateMetricBilinear (I := I) c (α s).1
      (coordinateVectorField c (gradient (I := I) f) (α s).1) (α s).2)
      (-K * f x * coordinateMetricBilinear (I := I) c (α t).1 (α t).2 (α t).2) t := by
  have hd := hasDerivAt_coordinate_geodesic_gradient_pairing cov hm b hf c x hx hpos hα
  rw [hH] at hd
  have he : (extChartAt I c).symm (α t).1 = x := by
    rw [hpos]
    exact (extChartAt I c).left_inv (by simpa using hx)
  convert hd using 1
  rw [coordinateMetricBilinear_apply, he]

/-- The value of a function alongAlmostSchur an actual coordinate geodesic has
derivative equal to its gradient paired with the velocity. -/
theorem hasDerivAt_coordinate_geodesic_value
    (cov : CovariantDerivative I E TM)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (c x : M) (hx : x ∈ (chartAt H c).source)
    {α : ℝ → E × E} {t : ℝ} (hpos : (α t).1 = extChartAt I c x)
    (hα : HasDerivAt α (coordinateGeodesicSpray cov b c (α t)) t) :
    HasDerivAt (fun s => f ((extChartAt I c).symm (α s).1))
      (coordinateMetricBilinear (I := I) c (α t).1
        (coordinateVectorField c (gradient (I := I) f) (α t).1) (α t).2) t := by
  have hz : (α t).1 ∈ (extChartAt I c).target := by
    rw [hpos]
    exact (extChartAt I c).map_source (by simpa using hx)
  have he : (extChartAt I c).symm (α t).1 = x := by
    rw [hpos]
    exact (extChartAt I c).left_inv (by simpa using hx)
  have hfc := contDiffOn_chart_comp (I := I) c f hf.contMDiffOn
  have hfd := (hfc.contDiffAt ((isOpen_extChartAt_target c).mem_nhds hz)).differentiableAt
    (show (1 : ℕ∞ω) ≠ 0 by norm_num)
  have hp : HasDerivAt (fun s => (α s).1) (α t).2 t :=
    (hasFDerivAt_fst (p := α t)).comp_hasDerivAt t hα
  have hd := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E) (E := ℝ)
    (l := f ∘ (extChartAt I c).symm) (f := fun s => (α s).1) t hfd.hasFDerivAt hp
  convert hd using 1 <;> try rfl
  rw [hpos, fderiv_chart_comp f c x hx (hf.mdifferentiable (by norm_num) x)]
  rw [coordinateMetricBilinear_apply, coordinateVectorField,
    (extChartAt I c).left_inv (by simpa using hx),
    (trivializationAt E TM c).symmL_continuousLinearMapAt hx, inner_gradient]

/-- The restriction of an Obata function to an actual coordinate geodesic
satisfies the scalar oscillator equation, with squared speed evaluated at
any fixed reference time in the connected time domain. -/
theorem hasDerivAt_deriv_coordinate_geodesic_obata
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K : ℝ}
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    {s₀ t : ℝ} (hs₀ : s₀ ∈ T) (ht : t ∈ T) :
    HasDerivAt (deriv (fun s => f ((extChartAt I c).symm (α s).1)))
      (-K * f ((extChartAt I c).symm (α t).1) *
        coordinateMetricBilinear (I := I) c (α s₀).1 (α s₀).2 (α s₀).2) t := by
  have hx (s : ℝ) (hs : s ∈ T) :
      (extChartAt I c).symm (α s).1 ∈ (chartAt H c).source := by
    simpa using (extChartAt I c).map_target (hz s hs)
  have hp (s : ℝ) (hs : s ∈ T) :
      (α s).1 = extChartAt I c ((extChartAt I c).symm (α s).1) :=
    ((extChartAt I c).right_inv (hz s hs)).symm
  have he : deriv (fun s => f ((extChartAt I c).symm (α s).1)) =ᶠ[𝓝 t]
      (fun s => coordinateMetricBilinear (I := I) c (α s).1
        (coordinateVectorField c (gradient (I := I) f) (α s).1) (α s).2) := by
    filter_upwards [hT.mem_nhds ht] with s hs
    exact (hasDerivAt_coordinate_geodesic_value cov b (hf.of_le (by norm_num)) c
      ((extChartAt I c).symm (α s).1) (hx s hs) (hp s hs) (hα s hs)).deriv
  have hd := hasDerivAt_coordinate_geodesic_obata_pairing cov hm b hf hH c
    ((extChartAt I c).symm (α t).1) (hx t ht) (hp t ht) (hα t ht)
  rw [coordinate_geodesic_energy_eq cov hm b c hT hconn hz hα ht hs₀] at hd
  exact hd.congr_of_eventuallyEq he

/-- From a critical point, the Obata function alongAlmostSchur an actual geodesic is
the cosine of time times its curvature-scaled initial metric speed. -/
theorem coordinate_geodesic_obata_eq_cos
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) {K : ℝ} (hK : 0 ≤ K)
    (hH : ∀ (y : M) (v w : TM y), hessian cov f y v w = -K * f y * inner ℝ v w)
    (c : M) {α : ℝ → E × E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hz : ∀ s ∈ T, (α s).1 ∈ (extChartAt I c).target)
    (hα : ∀ s ∈ T, HasDerivAt α (coordinateGeodesicSpray cov b c (α s)) s)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm (α 0).1) = 0)
    {t : ℝ} (ht : t ∈ T) :
    f ((extChartAt I c).symm (α t).1) =
      f ((extChartAt I c).symm (α 0).1) *
        Real.cos (Real.sqrt (K * coordinateMetricBilinear (I := I) c
          (α 0).1 (α 0).2 (α 0).2) * t) := by
  let F : ℝ → ℝ := fun s => f ((extChartAt I c).symm (α s).1)
  let e : ℝ := coordinateMetricBilinear (I := I) c (α 0).1 (α 0).2 (α 0).2
  have he : 0 ≤ e := by
    exact real_inner_self_nonneg (x :=
      (trivializationAt E TM c).symmL ℝ ((extChartAt I c).symm (α 0).1) (α 0).2)
  have hsq : (Real.sqrt (K * e)) ^ 2 = K * e := Real.sq_sqrt (mul_nonneg hK he)
  have hx (s : ℝ) (hs : s ∈ T) :
      (extChartAt I c).symm (α s).1 ∈ (chartAt H c).source := by
    simpa using (extChartAt I c).map_target (hz s hs)
  have hp (s : ℝ) (hs : s ∈ T) :
      (α s).1 = extChartAt I c ((extChartAt I c).symm (α s).1) :=
    ((extChartAt I c).right_inv (hz s hs)).symm
  have hval (s : ℝ) (hs : s ∈ T) := hasDerivAt_coordinate_geodesic_value cov b
    (hf.of_le (by norm_num)) c ((extChartAt I c).symm (α s).1) (hx s hs) (hp s hs) (hα s hs)
  have hF : ∀ s ∈ T, HasDerivAt F (deriv F s) s :=
    fun s hs => (hval s hs).differentiableAt.hasDerivAt
  have hV : ∀ s ∈ T, HasDerivAt (deriv F) (-(Real.sqrt (K * e) ^ 2) * F s) s := by
    intro s hs
    have hd := hasDerivAt_deriv_coordinate_geodesic_obata cov hm b hf hH c
      hT hconn hz hα hzero hs
    convert hd using 1
    rw [hsq]
    dsimp [F, e]
    ring
  have hvzero : deriv F 0 = 0 := by
    have hd := (hval 0 hzero).deriv
    simpa only [F, coordinateVectorField, hcrit, map_zero, zero_apply] using hd
  exact scalar_oscillator_eq_cos hT hconn hzero hF hV rfl hvzero ht

/-- A local manifold derivative suffices to differentiate a scalar function
alongAlmostSchur a coordinate curve. No global smoothness across critical points is used. -/
theorem hasDerivAt_chart_curve_value
    {f : M → ℝ} (c x : M) (hx : x ∈ (chartAt H c).source) (hf : MDiffAt f x)
    {z : ℝ → E} {d : E} {t : ℝ} (hpos : z t = extChartAt I c x)
    (hz : HasDerivAt z d t) :
    HasDerivAt (fun s => f ((extChartAt I c).symm (z s)))
      (inner ℝ (gradient (I := I) f x) ((trivializationAt E TM c).symmL ℝ x d)) t := by
  have hx' : x ∈ (extChartAt I c).source := by simpa using hx
  have hi : MDiffAt (extChartAt I c).symm (extChartAt I c x) := by
    simpa only [I.range_eq_univ, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm (I := I) (x := c)
        ((extChartAt I c).map_source hx')
  have hfd : DifferentiableAt ℝ (f ∘ (extChartAt I c).symm) (z t) := by
    rw [hpos]
    exact mdifferentiableAt_iff_differentiableAt.mp
      (hf.comp_of_eq (extChartAt I c x) hi ((extChartAt I c).left_inv hx'))
  have hd := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E) (E := ℝ)
    (l := f ∘ (extChartAt I c).symm) (f := z) t hfd.hasFDerivAt hz
  convert hd using 1 <;> try rfl
  rw [hpos, fderiv_chart_comp f c x hx hf, inner_gradient]

end LichnerowiczObata
