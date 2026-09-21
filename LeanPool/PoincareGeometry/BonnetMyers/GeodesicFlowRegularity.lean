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

import LeanPool.PoincareGeometry.BonnetMyers.GeodesicCutoff
import LeanPool.PoincareGeometry.BonnetMyers.IntrinsicAcceleration
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceContinuousDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# `C¹` dependence for localized coordinate geodesic flow

`GeodesicCutoff` turns the chart-local geodesic system into a compactly
supported global `C¹` field near any chosen state.  The same-repository
finite-dimensional flow theorem can therefore supply `C¹` dependence on the
initial state at every prescribed nonnegative time.  This is the regularity
input needed before applying an inverse-function argument to a local endpoint
map.

The theorem deliberately stops short of that inverse-function argument and of
any claim that a metric minimizer is smooth.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [nE : NormedAddCommGroup E] [nsE : NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type u))
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
  (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)

/-- At zero coordinate velocity the Christoffel acceleration is quadratic in
velocity, and hence has zero derivative in the full position--velocity state.

The explicit superclass arguments select the normed product structures used by
the Fréchet-calculus API; this avoids the otherwise competing algebraic product
instances for a generic `E × E`. -/
theorem coordinateAcceleration_hasFDerivAt_zero_velocity
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    @HasFDerivAt ℝ _ (E × E)
      (Prod.normedAddCommGroup : NormedAddCommGroup (E × E)).toAddCommGroup
      (Prod.normedSpace : NormedSpace ℝ (E × E)).toModule
      ((Prod.normedAddCommGroup : NormedAddCommGroup (E × E)).toPseudoMetricSpace).toUniformSpace.toTopologicalSpace
      E nE.toAddCommGroup nsE.toModule
      nE.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (fun q : E × E ↦ coordinateAcceleration (I := I) (M := M) (E := E) cov x₀ b q.1 q.2)
      0 (z, 0) := by
  classical
  let p : E × E := (z, 0)
  have hp_snd : HasFDerivAt (Prod.snd : E × E → E)
      (ContinuousLinearMap.snd ℝ E E) p := by
    exact hasFDerivAt_snd
  have hp_fst : HasFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) p := by
    exact hasFDerivAt_fst
  have hterm (i j k : Fin (Module.finrank ℝ E)) := by
    have hj : HasFDerivAt (fun q : E × E ↦ b.repr q.2 j)
        ((b.coord j).toContinuousLinearMap ∘L
          (ContinuousLinearMap.snd ℝ E E)) p := by
      simpa [Function.comp_def] using
        (HasFDerivAt.comp (𝕜 := ℝ) (E := E × E) p
          (b.coord j).toContinuousLinearMap.hasFDerivAt hp_snd)
    have hk : HasFDerivAt (fun q : E × E ↦ b.repr q.2 k)
        ((b.coord k).toContinuousLinearMap ∘L
          (ContinuousLinearMap.snd ℝ E E)) p := by
      simpa [Function.comp_def] using
        (HasFDerivAt.comp (𝕜 := ℝ) (E := E × E) p
          (b.coord k).toContinuousLinearMap.hasFDerivAt hp_snd)
    have hjk := by
      simpa [p] using
        HasFDerivAt.mul (𝕜 := ℝ) (E := E × E) hj hk
    have hcbase := ((connectionCoefficient_comp_extChartAt_symm_contDiffAt_of_mem_target
        (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
        i j k hz).differentiableAt one_ne_zero).hasFDerivAt
    have hc := HasFDerivAt.comp (𝕜 := ℝ) (E := E × E) p hcbase hp_fst
    have hjkc := by
      simpa [p] using
        HasFDerivAt.mul (𝕜 := ℝ) (E := E × E) hjk hc
    exact hjkc
  have hsumk (i j : Fin (Module.finrank ℝ E)) := by
    simpa only [Finset.sum_apply, Finset.sum_const_zero] using
      HasFDerivAt.sum (𝕜 := ℝ) (E := E × E) (u := Finset.univ)
        (fun k _ ↦ hterm i j k)
  have hsumj (i : Fin (Module.finrank ℝ E)) := by
    simpa only [Finset.sum_apply, Finset.sum_const_zero] using
      HasFDerivAt.sum (𝕜 := ℝ) (E := E × E) (u := Finset.univ)
        (fun j _ ↦ hsumk i j)
  have hsumi := by
    simpa only [Finset.sum_apply, Finset.sum_const_zero] using
      HasFDerivAt.sum (𝕜 := ℝ) (E := E × E) (u := Finset.univ)
        (fun i _ ↦ HasFDerivAt.smul_const (𝕜 := ℝ) (E := E × E) (hsumj i) (b i))
  convert HasFDerivAt.neg (𝕜 := ℝ) (E := E × E) hsumi using 1
  · ext q
    simp [coordinateAcceleration]
  · simp

/-- The linearization of the coordinate geodesic system at zero velocity is
`(δz, δu) ↦ (δu, 0)`. -/
theorem coordinateSecondOrderSystem_hasFDerivAt_zero_velocity
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    @HasFDerivAt ℝ _ (E × E)
      (Prod.normedAddCommGroup : NormedAddCommGroup (E × E)).toAddCommGroup
      (Prod.normedSpace : NormedSpace ℝ (E × E)).toModule
      ((Prod.normedAddCommGroup : NormedAddCommGroup (E × E)).toPseudoMetricSpace).toUniformSpace.toTopologicalSpace
      (E × E) (Prod.normedAddCommGroup : NormedAddCommGroup (E × E)).toAddCommGroup
      (Prod.normedSpace : NormedSpace ℝ (E × E)).toModule
      ((Prod.normedAddCommGroup : NormedAddCommGroup (E × E)).toPseudoMetricSpace).toUniformSpace.toTopologicalSpace
      (fun q : E × E ↦ secondOrderSystem
        (coordinateAcceleration (I := I) (M := M) (E := E) cov x₀ b) q)
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : (E × E) →L[ℝ] E)) (z, 0) := by
  have hacc := coordinateAcceleration_hasFDerivAt_zero_velocity
    (I := I) (M := M) (E := E) cov x₀ b hz
  have hsnd := (hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := E) (p := (z, 0)))
  simpa [secondOrderSystem] using hsnd.prodMk hacc

/-- A compactly supported `C¹` extension of the coordinate geodesic system
has a flow whose prescribed time slice is `C¹` in the initial state.  The
extension agrees with the actual system on a neighbourhood of the selected
state. -/
theorem exists_contDiff_coordinateGeodesic_extension_flow
    {z₀ : E} (hz₀ : z₀ ∈ (extChartAt I x₀).target) (u₀ : E)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ G : E × E → E × E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z₀, u₀)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        ∃ Φ : (E × E) → ℝ → E × E,
          (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
            ContDiff ℝ 1 (fun q ↦ Φ q T) := by
  obtain ⟨G, hG, hGcompact, hGeq⟩ :=
    exists_contDiff_compactSupport_coordinateGeodesic_extension
      (I := I) (M := M) (E := E) cov x₀ b hz₀ u₀
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGcompact hG (by norm_num)
  obtain ⟨DG, hDGcont, hDG⟩ := contDiff_one_iff_hasFDerivAt.mp hG
  obtain ⟨Φ, hΦzero, hΦcurve, hΦsmooth⟩ :=
    RicciFlow.AnalyticPDE.SmoothDependenceCk.exists_flow_contDiff_one_of_continuous_deriv
      (v := fun _ : ℝ ↦ G) (K := K) (t₀ := 0)
      (fun _ ↦ hK) (fun _ ↦ continuous_const)
      (Dv := fun _ : ℝ ↦ DG)
      (fun _ q ↦ by simpa using hDG q)
      (by fun_prop) hT
  exact ⟨G, hG, hGcompact, hGeq, Φ, hΦzero, hΦcurve, hΦsmooth⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Scaling only the velocity component of a product state cannot increase
its distance from a zero-velocity base state when the factor lies in `[0,1]`.
This elementary max-product estimate keeps the rescaled trajectory inside the
cutoff-agreement neighbourhood in the radial-flow argument below. -/
lemma prod_scale_snd_dist_le (x z v : E) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    dist (x, a • v) (z, 0) ≤ dist (x, v) (z, 0) := by
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [dist_zero_right, norm_smul]
  have habs : |a| ≤ 1 := abs_le.2 ⟨by linarith, ha1⟩
  apply max_le
  · exact le_max_left _ _
  · calc
      |a| * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖v‖ := one_mul _
      _ ≤ max (dist x z) ‖v‖ := le_max_right _ _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- Every state neighbourhood of a stationary orbit contains all trajectories
with sufficiently small initial velocity on a prescribed compact symmetric
time interval.  This is the reusable uniform-confinement estimate behind the
normal-coordinate neighbourhood shrinks. -/
theorem eventually_forall_flow_mem_of_stationary
    {G : E × E → E × E} (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    {Φ : (E × E) → ℝ → E × E} (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    {z : E} (hfix : ∀ t, Φ (z, 0) t = (z, 0))
    {S : Set (E × E)} (hS : S ∈ 𝓝 (z, 0)) {T : ℝ} :
    ∀ᶠ u in 𝓝 (0 : E), ∀ t ∈ Icc (-T) T, Φ (z, u) t ∈ S := by
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGcompact hG (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
  let δ : ℝ := ε / Real.exp ((K : ℝ) * T)
  have hδ : 0 < δ := div_pos hε (Real.exp_pos _)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with u hu
  intro t ht
  have hnorm : ‖u‖ < δ := by
    simpa [Real.dist_eq] using (Metric.mem_ball'.mp hu)
  have habs : |t| ≤ T := abs_le.2 ht
  have hexp : Real.exp ((K : ℝ) * |t|) ≤ Real.exp ((K : ℝ) * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs K.coe_nonneg)
  have hflow := RicciFlow.AnalyticPDE.SmoothDependenceCk.dist_flow_apply_le
    (v := fun _ : ℝ ↦ G) (K := K) (t₀ := 0)
    (fun _ ↦ hK) hΦcurve hΦzero (z, u) (z, 0) t
  rw [hfix t] at hflow
  apply hball
  apply Metric.mem_ball'.mpr
  calc
    dist (z, 0) (Φ (z, u) t) = dist (Φ (z, u) t) (z, 0) := dist_comm _ _
    _ ≤ dist (z, u) (z, 0) * Real.exp ((K : ℝ) * |t - 0|) := hflow
    _ = ‖u‖ * Real.exp ((K : ℝ) * |t|) := by
      rw [sub_zero, Prod.dist_eq]
      simp [dist_eq_norm]
    _ ≤ ‖u‖ * Real.exp ((K : ℝ) * T) :=
      mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ < δ * Real.exp ((K : ℝ) * T) :=
      mul_lt_mul_of_pos_right hnorm (Real.exp_pos _)
    _ = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ ε (ne_of_gt (Real.exp_pos _))

/-- Full-state form of `eventually_forall_flow_mem_of_stationary`.  Every
trajectory whose complete initial position--velocity state is sufficiently
close to a stationary state remains in a prescribed neighbourhood throughout
a fixed compact symmetric time interval. -/
theorem eventually_forall_flow_mem_of_stationary_state
    {G : E × E → E × E} (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    {Φ : (E × E) → ℝ → E × E} (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    {z : E} (hfix : ∀ t, Φ (z, 0) t = (z, 0))
    {S : Set (E × E)} (hS : S ∈ 𝓝 (z, 0)) {T : ℝ} :
    ∀ᶠ q in 𝓝 (z, 0), ∀ t ∈ Icc (-T) T, Φ q t ∈ S := by
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGcompact hG (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hS
  let δ : ℝ := ε / Real.exp ((K : ℝ) * T)
  have hδ : 0 < δ := div_pos hε (Real.exp_pos _)
  filter_upwards [Metric.ball_mem_nhds (z, (0 : E)) hδ] with q hq
  intro t ht
  have hdistq : dist q (z, 0) < δ := by
    simpa [dist_comm] using Metric.mem_ball.mp hq
  have habs : |t| ≤ T := abs_le.2 ht
  have hexp : Real.exp ((K : ℝ) * |t|) ≤ Real.exp ((K : ℝ) * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs K.coe_nonneg)
  have hflow := RicciFlow.AnalyticPDE.SmoothDependenceCk.dist_flow_apply_le
    (v := fun _ : ℝ ↦ G) (K := K) (t₀ := 0)
    (fun _ ↦ hK) hΦcurve hΦzero q (z, 0) t
  rw [hfix t] at hflow
  apply hball
  apply Metric.mem_ball'.mpr
  calc
    dist (z, 0) (Φ q t) = dist (Φ q t) (z, 0) := dist_comm _ _
    _
        ≤ dist q (z, 0) * Real.exp ((K : ℝ) * |t - 0|) := hflow
    _ = dist q (z, 0) * Real.exp ((K : ℝ) * |t|) := by rw [sub_zero]
    _ ≤ dist q (z, 0) * Real.exp ((K : ℝ) * T) :=
      mul_le_mul_of_nonneg_left hexp dist_nonneg
    _ < δ * Real.exp ((K : ℝ) * T) :=
      mul_lt_mul_of_pos_right hdistq (Real.exp_pos _)
    _ = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ ε (ne_of_gt (Real.exp_pos _))

omit [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- A compactly supported flow which agrees with the quadratic coordinate
geodesic system near `(z,0)` is radially equivariant on a sufficiently small
velocity neighbourhood.  In particular, flowing `a • u` for time `t` equals
flowing `u` for time `a * t` and scaling its velocity component by `a`.

The proof is not a formal reparameterization shortcut: it first proves that
the rescaled state remains in the agreement ball, then uses interval ODE
uniqueness for the global cutoff field. -/
lemma flow_radial_of_ball
    {z : E}
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    {K : NNReal} (hK : LipschitzWith K G)
    (hGball : ∃ ε > (0 : ℝ), ∀ q : E × E,
      dist q (z, 0) < ε →
        G q = secondOrderSystem (coordinateAcceleration cov x₀ b) q)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G))
    (hfix : ∀ t, Φ (z, 0) t = (z, 0)) :
    ∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      Φ (z, a • u) t =
        ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2) := by
  obtain ⟨ε, hε, hball⟩ := hGball
  let δ : ℝ := ε / Real.exp (K : ℝ)
  have hδ : 0 < δ := div_pos hε (Real.exp_pos _)
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with u hu
  have hu_norm : ‖u‖ < δ := by
    simpa [Real.dist_eq] using (Metric.mem_ball'.mp hu)
  intro a ha t ht
  have ha0 : 0 ≤ a := ha.1
  have ha1 : a ≤ 1 := ha.2
  have habs : |a| ≤ 1 := abs_le.2 ⟨by linarith, ha1⟩
  have hscale_norm : ‖a • u‖ ≤ ‖u‖ := by
    rw [norm_smul]
    calc
      ‖a‖ * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖u‖ := one_mul _
  have hflow_near : ∀ w : E, ‖w‖ ≤ ‖u‖ → ∀ s ∈ Icc (0 : ℝ) 1,
      dist (Φ (z, w) s) (z, 0) < ε := by
    intro w hw s hs
    have hflow := RicciFlow.AnalyticPDE.SmoothDependenceCk.dist_flow_apply_le
      (v := fun _ : ℝ ↦ G) (K := K) (t₀ := 0)
      (fun _ ↦ hK) hΦcurve hΦzero (z, w) (z, 0) s
    rw [hfix s] at hflow
    have hsabs : |s| ≤ 1 := by
      rw [abs_of_nonneg hs.1]
      exact hs.2
    have hexp : Real.exp ((K : ℝ) * |s|) ≤ Real.exp (K : ℝ) := by
      apply Real.exp_le_exp.mpr
      calc
        (K : ℝ) * |s| ≤ (K : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hsabs K.coe_nonneg
        _ = K := mul_one _
    calc
      dist (Φ (z, w) s) (z, 0) ≤
          dist (z, w) (z, 0) * Real.exp ((K : ℝ) * |s - 0|) := hflow
      _ = ‖w‖ * Real.exp ((K : ℝ) * |s|) := by
        rw [sub_zero, Prod.dist_eq]
        simp [dist_eq_norm]
      _ ≤ ‖u‖ * Real.exp (K : ℝ) := by
        calc
          ‖w‖ * Real.exp ((K : ℝ) * |s|) ≤
              ‖u‖ * Real.exp ((K : ℝ) * |s|) :=
            mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
          _ ≤ ‖u‖ * Real.exp (K : ℝ) :=
            mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ < δ * Real.exp (K : ℝ) :=
        mul_lt_mul_of_pos_right hu_norm (Real.exp_pos _)
      _ = ε := by
        dsimp [δ]
        exact div_mul_cancel₀ ε (ne_of_gt (Real.exp_pos _))
  let σ : ℝ → E × E := fun s ↦
    ((Φ (z, u) (a * s)).1, a • (Φ (z, u) (a * s)).2)
  have hσ_deriv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivAt σ (G (σ s)) s := by
    intro s hs
    have has : a * s ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact mul_nonneg ha0 hs.1
      · calc
          a * s ≤ 1 * s := mul_le_mul_of_nonneg_right ha1 hs.1
          _ ≤ 1 := by simpa using hs.2.le
    have horig : dist (Φ (z, u) (a * s)) (z, 0) < ε :=
      hflow_near u le_rfl (a * s) has
    have hσdist : dist (σ s) (z, 0) < ε := by
      dsimp [σ]
      exact lt_of_le_of_lt
        (prod_scale_snd_dist_le
          (Φ (z, u) (a * s)).1 z (Φ (z, u) (a * s)).2 ha0 ha1)
        horig
    have hGorig : G (Φ (z, u) (a * s)) =
        secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) (a * s)) :=
      hball _ horig
    have hGσ : G (σ s) =
        secondOrderSystem (coordinateAcceleration cov x₀ b) (σ s) :=
      hball _ hσdist
    have htime : HasDerivAt (fun r : ℝ ↦ a * r) a s := hasDerivAt_const_mul a
    have hstate := hΦcurve (z, u) (a * s)
    change HasDerivAt (Φ (z, u)) (G (Φ (z, u) (a * s))) (a * s) at hstate
    rw [hGorig] at hstate
    have hxbase : HasDerivAt (fun r ↦ (Φ (z, u) r).1)
        (Φ (z, u) (a * s)).2 (a * s) := by
      simpa [secondOrderSystem] using hstate.hasFDerivAt.fst.hasDerivAt
    have hvbase : HasDerivAt (fun r ↦ (Φ (z, u) r).2)
        (coordinateAcceleration cov x₀ b (Φ (z, u) (a * s)).1
          (Φ (z, u) (a * s)).2) (a * s) := by
      simpa [secondOrderSystem] using hstate.hasFDerivAt.snd.hasDerivAt
    have hx := HasDerivAt.scomp s hxbase htime
    have hv := (HasDerivAt.scomp s hvbase htime).const_smul a
    rw [hGσ]
    change HasDerivAt σ
      (a • (Φ (z, u) (a * s)).2,
        coordinateAcceleration cov x₀ b (Φ (z, u) (a * s)).1
          (a • (Φ (z, u) (a * s)).2)) s
    rw [coordinateAcceleration_smul]
    convert hx.prodMk hv using 1
    · ext r <;> simp [σ, Function.comp_apply, Pi.smul_apply]
    · simp [smul_smul, pow_two]
  have hσcont : Continuous σ := by
    have htimecont : Continuous (fun s : ℝ ↦ a * s) := continuous_const.mul continuous_id
    have hcont := (hΦcurve (z, u)).continuous.comp htimecont
    exact hcont.fst.prodMk (continuous_const.smul hcont.snd)
  have hscaled_cont : Continuous (Φ (z, a • u)) := (hΦcurve (z, a • u)).continuous
  have hinitial : Φ (z, a • u) 0 = σ 0 := by
    simp [σ, hΦzero]
  have hEq := ODE_solution_unique (a := (0 : ℝ)) (b := (1 : ℝ))
    (v := fun _ : ℝ ↦ G) (fun _ ↦ hK)
    hscaled_cont.continuousOn
    (fun s hs ↦ (hΦcurve (z, a • u) s).hasDerivWithinAt)
    hσcont.continuousOn
    (fun s hs ↦ (hσ_deriv s hs).hasDerivWithinAt)
    hinitial
  exact hEq ht

/-- At zero initial velocity, the time-one endpoint map of a compactly
supported coordinate-geodesic extension has derivative the identity in the
velocity variable.  The proof identifies the variational equation at the
stationary state explicitly: its linearization sends `(δz, δu)` to
`(δu, 0)`, whose flow sends it to `(δz + t δu, δu)`.

This is the differential input for a normal-neighborhood inverse-function
argument; the statement itself makes no claim yet about metric minimizers. -/
theorem exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z, 0)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        HasFDerivAt (fun q : E × E ↦ Φ q 1)
          ((ContinuousLinearMap.id ℝ (E × E)) +
            (ContinuousLinearMap.snd ℝ E E).prod
              (0 : (E × E) →L[ℝ] E)) (z, 0) ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
          (ContinuousLinearMap.id ℝ E) 0 := by
  obtain ⟨G, hG, hGcompact, hGeq, Φ, hΦzero, hΦcurve, hΦsmooth⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow
      (I := I) (M := M) (E := E) cov x₀ b hz 0 (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGcompact hG (by norm_num)
  have hGzero : G (z, 0) = 0 := by
    rw [hGeq.eq_of_nhds]
    simp [secondOrderSystem, coordinateAcceleration]
  have hconst : IsIntegralCurve (fun _ : ℝ ↦ (z, 0)) (fun _ ↦ G) := by
    intro t
    simpa [hGzero] using (hasDerivAt_const t (z, 0))
  have hfix : ∀ t, Φ (z, 0) t = (z, 0) := by
    intro t
    exact RicciFlow.AnalyticPDE.SmoothDependenceCk.eq_of_isIntegralCurve_of_eq_at
      (v := fun _ : ℝ ↦ G) (K := K) (fun _ ↦ hK)
      (hΦcurve (z, 0)) hconst (hΦzero (z, 0)) t
  obtain ⟨DG, hDGcont, hDG⟩ := contDiff_one_iff_hasFDerivAt.mp hG
  have hsystemDeriv := coordinateSecondOrderSystem_hasFDerivAt_zero_velocity
    (I := I) (M := M) (E := E) cov x₀ b hz
  have hGderiv := hsystemDeriv.congr_of_eventuallyEq hGeq
  have hDGp : DG (z, 0) = (ContinuousLinearMap.snd ℝ E E).prod
      (0 : (E × E) →L[ℝ] E) := by
    calc
      DG (z, 0) = fderiv ℝ G (z, 0) := (hDG (z, 0)).fderiv.symm
      _ = (ContinuousLinearMap.snd ℝ E E).prod
          (0 : (E × E) →L[ℝ] E) := hGderiv.fderiv
  have hDvc : Continuous (fun p : ℝ × (E × E) ↦ DG p.2) :=
    hDGcont.comp continuous_snd
  have hLbound : ‖(ContinuousLinearMap.snd ℝ E E).prod
      (0 : (E × E) →L[ℝ] E)‖ ≤ (K : ℝ) := by
    rw [← hDGp]
    exact (hDG (z, 0)).le_of_lipschitz hK
  have hA : ∀ s : ℝ, ‖((ContinuousLinearMap.snd ℝ E E).prod
      (0 : (E × E) →L[ℝ] E))‖₊ ≤ K := by
    intro s
    exact_mod_cast hLbound
  obtain ⟨Ψ, hΨzero, hΨcurve⟩ :=
    RicciFlow.AnalyticPDE.SmoothDependenceCk.exists_variationalFlowFamily
      (t₀ := 0) hA continuous_const
  have hflowDeriv :=
    RicciFlow.AnalyticPDE.SmoothDependenceCk.hasFDerivAt_flow_of_continuous_deriv
      (v := fun _ : ℝ ↦ G) (K := K) (t₀ := 0) (fun _ ↦ hK) hA hΨcurve hΨzero
      hΦcurve hΦzero (z, 0) (by norm_num : (0 : ℝ) ≤ 1)
      (Dv := fun _ : ℝ ↦ DG) (fun _ x ↦ hDG x) hDvc
      (fun s ↦ by rw [hfix s, hDGp])
  let L : (E × E) →L[ℝ] (E × E) := (ContinuousLinearMap.snd ℝ E E).prod
    (0 : (E × E) →L[ℝ] E)
  have hLsq : L.comp L = 0 := by
    ext q <;> simp [L]
  have affine_hasDerivAt (q c : E × E) (t : ℝ) :
      @HasDerivAt ℝ _ (E × E)
        (Prod.instAddCommGroup : AddCommGroup (E × E))
        (Prod.instModule : Module ℝ (E × E))
        (instTopologicalSpaceProd : TopologicalSpace (E × E))
        (Prod.continuousSMul : ContinuousSMul ℝ (E × E))
        (fun s : ℝ ↦ q + s • c) c t := by
    apply HasFDerivAtFilter.of_isLittleOTVS
    have hzero : (fun _ : ℝ × ℝ ↦ (0 : E × E)) =o[ℝ; 𝓝 t ×ˢ pure t]
        (fun p : ℝ × ℝ ↦ p.1 - p.2) := by
      refine ⟨?_⟩
      intro U hU
      refine ⟨Set.univ, univ_mem, ?_⟩
      intro ε hε
      exact Filter.Eventually.of_forall fun p ↦ by
        rw [egauge_zero_right _ (Filter.nonempty_of_mem hU)]
        simp
    exact hzero.congr_left fun p ↦ by
      simp only [ContinuousLinearMap.toSpanSingleton_apply, sub_smul]
      abel
  let V : (E × E) → ℝ → (E × E) := fun q t ↦ q + t • L q
  have hVcurve : ∀ q, IsIntegralCurve (V q)
      (RicciFlow.AnalyticPDE.SmoothDependenceCk.variationalFieldVec (fun _ : ℝ ↦ L)) := by
    intro q t
    have hLapp : L (V q t) = L q := by
      rw [show V q t = q + t • L q by rfl, map_add, map_smul]
      have hsqapp : L (L q) = 0 := by
        rw [← ContinuousLinearMap.comp_apply, hLsq]
        rfl
      rw [hsqapp, smul_zero, add_zero]
    change @HasDerivAt ℝ _ (E × E)
      (Prod.instAddCommGroup : AddCommGroup (E × E))
      (Prod.instModule : Module ℝ (E × E))
      (instTopologicalSpaceProd : TopologicalSpace (E × E))
      (Prod.continuousSMul : ContinuousSMul ℝ (E × E))
      (fun s : ℝ ↦ q + s • L q) (L (V q t)) t
    rw [hLapp]
    exact affine_hasDerivAt q (L q) t
  have hfund_apply (q : E × E) :
      RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution hA hΨcurve hΨzero 1 q =
        q + L q := by
    rw [RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution_apply]
    simpa [V] using
      (RicciFlow.AnalyticPDE.SmoothDependenceCk.variationalVec_eq_of_isIntegralCurve
        hA (hΨcurve q) (hVcurve q) (t₁ := 0) (by simpa [V] using hΨzero q) 1)
  have hflowDeriv' : HasFDerivAt (fun q : E × E ↦ Φ q 1)
      ((ContinuousLinearMap.id ℝ (E × E)) +
        (ContinuousLinearMap.snd ℝ E E).prod
          (0 : (E × E) →L[ℝ] E)) (z, 0) := by
    apply hflowDeriv.congr_fderiv
    apply ContinuousLinearMap.ext
    intro q
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply]
    simpa only [L] using hfund_apply q
  have hinit : HasFDerivAt (fun u : E ↦ (z, u))
      ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) 0 := by
    simpa using ((hasFDerivAt_const (c := z) (0 : E)).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) (x := (0 : E))))
  have hstate : HasFDerivAt (fun u : E ↦ Φ (z, u) 1)
      ((RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution hA hΨcurve hΨzero 1).comp
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))) 0 :=
    hflowDeriv.comp 0 hinit
  have hend : HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
      ((ContinuousLinearMap.fst ℝ E E).comp
        ((RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution hA hΨcurve hΨzero 1).comp
          ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)))) 0 := by
    change HasFDerivAt (Prod.fst ∘ fun u : E ↦ Φ (z, u) 1)
      ((ContinuousLinearMap.fst ℝ E E).comp
        ((RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution hA hΨcurve hΨzero 1).comp
          ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)))) 0
    exact (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E)
      (p := Φ (z, 0) 1)).comp 0 hstate
  have hend' : HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
      (ContinuousLinearMap.id ℝ E) 0 := by
    convert hend using 1
    ext u
    change u = (RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution
      hA hΨcurve hΨzero 1 (0, u)).1
    rw [hfund_apply]
    simp [L]
  exact ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth,
    hflowDeriv', hfix, hend'⟩

/-- A common-coordinate endpoint map `(initial position, initial velocity) ↦
(initial position, time-one position)` is a local equivalence near the diagonal.

The source is shrunk so that every represented trajectory on `[-2,2]` stays
inside the chosen manifold chart and solves the genuine coordinate geodesic
system there.  Thus the local equivalence carries both endpoint uniqueness and
the ODE-validity data needed by a strong-normal-neighbourhood construction. -/
theorem exists_twoPoint_coordinateGeodesic_localEquiv
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hzcenter : z = extChartAt I x₀ x₀) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ∃ R : OpenPartialHomeomorph (E × E) (E × E),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      G =ᶠ[𝓝 (z, 0)]
        (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
      (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
      (∀ t, Φ (z, 0) t = (z, 0)) ∧
      ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
      (∀ q, R q = (q.1, (Φ q 1).1)) ∧
      (z, 0) ∈ R.source ∧ (z, z) ∈ R.target ∧
      (∀ y ∈ R.target, ContDiffAt ℝ 1 R.symm y) ∧
      (∀ q ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
        (Φ q t).1 ∈ (extChartAt I x₀).target ∧
          G (Φ q t) =
            secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ q t) ∧
          G =ᶠ[𝓝 (Φ q t)]
            (fun p ↦ secondOrderSystem
              (coordinateAcceleration cov x₀ b) p)) ∧
      (∀ q ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
        ∀ j : Fin (Module.finrank ℝ E),
          smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
            𝓝 ((extChartAt I x₀).symm (Φ q t).1)]
            (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j) := by
  obtain ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth,
    hΦderiv, hfix, _hend⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity
      (I := I) (M := M) (E := E) cov x₀ b hz
  let P : E × E → E × E := fun q ↦ (q.1, (Φ q 1).1)
  let D : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearMap.fst ℝ E E).prod
      ((ContinuousLinearMap.fst ℝ E E) + (ContinuousLinearMap.snd ℝ E E))
  have hD : Function.Bijective D := by
    constructor
    · intro q r hqr
      apply Prod.ext
      · simpa [D] using congrArg Prod.fst hqr
      · have h1 := congrArg Prod.snd hqr
        change q.1 + q.2 = r.1 + r.2 at h1
        have h0 : q.1 = r.1 := by
          simpa [D] using congrArg Prod.fst hqr
        rw [h0] at h1
        exact add_left_cancel h1
    · intro q
      refine ⟨(q.1, q.2 - q.1), ?_⟩
      apply Prod.ext <;> simp [D]
  have hDker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hD.1
  have hDrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hD.2
  let e : (E × E) ≃L[ℝ] (E × E) :=
    ContinuousLinearEquiv.ofBijective D hDker hDrange
  have hP : ContDiff ℝ 1 P := contDiff_fst.prodMk hΦsmooth.fst
  have hfirst : HasFDerivAt (fun q : E × E ↦ q.1)
      (ContinuousLinearMap.fst ℝ E E) (z, 0) := hasFDerivAt_fst
  have hsecond : HasFDerivAt (fun q : E × E ↦ (Φ q 1).1)
      ((ContinuousLinearMap.fst ℝ E E).comp
        ((ContinuousLinearMap.id ℝ (E × E)) +
          (ContinuousLinearMap.snd ℝ E E).prod
            (0 : (E × E) →L[ℝ] E))) (z, 0) :=
    (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E)).comp (z, 0) hΦderiv
  have hPderivRaw := hfirst.prodMk hsecond
  have hPderiv : HasFDerivAt P D (z, 0) := by
    apply hPderivRaw.congr_fderiv
    apply ContinuousLinearMap.ext
    intro q
    apply Prod.ext
    · rfl
    · simp [D]
  have hPderivE : HasFDerivAt P (e : (E × E) →L[ℝ] (E × E)) (z, 0) :=
    hPderiv.congr_fderiv (by rfl)
  have hne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  let hstrict : HasStrictFDerivAt P (e : (E × E) →L[ℝ] (E × E)) (z, 0) :=
    hP.contDiffAt.hasStrictFDerivAt' hPderivE hne
  let R₀ : OpenPartialHomeomorph (E × E) (E × E) :=
    hstrict.toOpenPartialHomeomorph P
  have hR₀ (q : E × E) : R₀ q = P q := by
    simpa only [R₀] using congrFun hstrict.toOpenPartialHomeomorph_coe q
  let F : E × E → E × E := fun q ↦
    secondOrderSystem (coordinateAcceleration cov x₀ b) q
  let S : Set (E × E) := {q | G q = F q}
  let A : Set M := IntrinsicAcceleration.smoothFrameAgreementSet
    (I := I) (M := M) x₀ b
  have hcentre : (extChartAt I x₀).symm z = x₀ := by
    rw [hzcenter]
    exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have hAcoord : {p : E | (extChartAt I x₀).symm p ∈ A} ∈ 𝓝 z := by
    rw [hzcenter]
    apply (continuousAt_extChartAt_symm (I := I) x₀).preimage_mem_nhds
    rw [(extChartAt I x₀).left_inv (mem_extChartAt_source x₀)]
    exact IntrinsicAcceleration.smoothFrameAgreementSet_mem_nhds
      (I := I) (M := M) x₀ b
  have hcoord : (extChartAt I x₀).target ∩
      {p : E | (extChartAt I x₀).symm p ∈ A} ∈ 𝓝 z :=
    inter_mem ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hz) hAcoord
  obtain ⟨N, hNsub, hNopen, hzN⟩ := mem_nhds_iff.mp hcoord
  let T : Set (E × E) := N ×ˢ Set.univ
  have hT : T ∈ 𝓝 (z, 0) :=
    (hNopen.prod isOpen_univ).mem_nhds ⟨hzN, Set.mem_univ _⟩
  obtain ⟨O, hOsub, hOopen, hzO⟩ :=
    mem_nhds_iff.mp (inter_mem (show S ∈ 𝓝 (z, 0) from hGeq) hT)
  have hstay : ∀ᶠ q in 𝓝 (z, 0),
      ∀ t ∈ Icc (-2 : ℝ) 2, Φ q t ∈ O :=
    eventually_forall_flow_mem_of_stationary_state hG hGcompact
      hΦzero hΦcurve hfix (hOopen.mem_nhds hzO)
  obtain ⟨Uflow, hUflowsub, hUflowopen, hzUflow⟩ := mem_nhds_iff.mp hstay
  let Q : Set (E × E) :=
    (fderiv ℝ P) ⁻¹'
      Set.range ((↑) : ((E × E) ≃L[ℝ] (E × E)) →
        (E × E) →L[ℝ] (E × E))
  have hQopen : IsOpen Q := by
    exact ContinuousLinearEquiv.isOpen.preimage
      (hP.continuous_fderiv hne)
  have hzQ : (z, 0) ∈ Q := by
    change fderiv ℝ P (z, 0) ∈
      Set.range ((↑) : ((E × E) ≃L[ℝ] (E × E)) →
        (E × E) →L[ℝ] (E × E))
    rw [hPderivE.fderiv]
    exact Set.mem_range_self e
  let U : Set (E × E) := Uflow ∩ Q
  have hUopen : IsOpen U := hUflowopen.inter hQopen
  have hzU : (z, 0) ∈ U := ⟨hzUflow, hzQ⟩
  let R : OpenPartialHomeomorph (E × E) (E × E) := R₀.restr U
  have hR (q : E × E) : R q = P q := by
    rw [show (R : E × E → E × E) = R₀ from
      OpenPartialHomeomorph.restr_apply R₀ U]
    exact hR₀ q
  have hsource₀ : (z, 0) ∈ R₀.source :=
    hstrict.mem_toOpenPartialHomeomorph_source
  have hsource : (z, 0) ∈ R.source := by
    change (z, 0) ∈ (R₀.restr U).source
    rw [OpenPartialHomeomorph.restr_source, hUopen.interior_eq]
    exact ⟨hsource₀, hzU⟩
  have htarget : (z, z) ∈ R.target := by
    have hmap := R.map_source hsource
    rw [hR] at hmap
    simpa [P, hfix] using hmap
  have hRP : (R : E × E → E × E) = P := funext hR
  have hRcontDiff : ContDiff ℝ 1 (R : E × E → E × E) := hRP.symm ▸ hP
  have hinverseSmooth : ∀ y ∈ R.target, ContDiffAt ℝ 1 R.symm y := by
    intro y hy
    have hxsource : R.symm y ∈ R.source := R.map_target hy
    have hxU : R.symm y ∈ U := by
      change R.symm y ∈ (R₀.restr U).source at hxsource
      rw [OpenPartialHomeomorph.restr_source, hUopen.interior_eq] at hxsource
      exact hxsource.2
    have hxQ := hxU.2
    change fderiv ℝ P (R.symm y) ∈
      Set.range ((↑) : ((E × E) ≃L[ℝ] (E × E)) →
        (E × E) →L[ℝ] (E × E)) at hxQ
    obtain ⟨e', he'⟩ := hxQ
    apply R.contDiffAt_symm (f₀' := e') hy
    · have hPderivAt : HasFDerivAt P (fderiv ℝ P (R.symm y)) (R.symm y) :=
        (hP.differentiable hne (R.symm y)).hasFDerivAt
      have hRderivAt : HasFDerivAt (R : E × E → E × E)
          (fderiv ℝ P (R.symm y)) (R.symm y) := hRP.symm ▸ hPderivAt
      rw [he']
      exact hRderivAt
    · exact hRcontDiff.contDiffAt
  refine ⟨G, Φ, R, hG, hGcompact, hGeq, hΦzero, hΦcurve, hfix, hΦsmooth,
    hR, hsource, htarget, hinverseSmooth, ?_, ?_⟩
  intro q hq t ht
  have hqUflow : q ∈ Uflow := by
    change q ∈ (R₀.restr U).source at hq
    rw [OpenPartialHomeomorph.restr_source, hUopen.interior_eq] at hq
    exact hq.2.1
  have horbitO : Φ q t ∈ O := hUflowsub hqUflow t ht
  have horbitST : Φ q t ∈ S ∩ T := hOsub horbitO
  refine ⟨(hNsub horbitST.2.1).1, horbitST.1, ?_⟩
  change S ∈ 𝓝 (Φ q t)
  exact mem_of_superset (hOopen.mem_nhds horbitO)
    (hOsub.trans inter_subset_left)
  intro q hq t ht j
  have hqUflow : q ∈ Uflow := by
    change q ∈ (R₀.restr U).source at hq
    rw [OpenPartialHomeomorph.restr_source, hUopen.interior_eq] at hq
    exact hq.2.1
  have horbitO : Φ q t ∈ O := hUflowsub hqUflow t
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hpN : (Φ q t).1 ∈ N := (hOsub horbitO).2.1
  let y : M := (extChartAt I x₀).symm (Φ q t).1
  have hySource : y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target (hNsub hpN).1
  have hcoordN : {r : M | extChartAt I x₀ r ∈ N} ∈ 𝓝 y := by
    apply (continuousAt_extChartAt' (I := I) hySource).preimage_mem_nhds
    rw [(extChartAt I x₀).right_inv (hNsub hpN).1]
    exact hNopen.mem_nhds hpN
  have hsourceN : (extChartAt I x₀).source ∈ 𝓝 y :=
    (isOpen_extChartAt_source (I := I) x₀).mem_nhds hySource
  filter_upwards [hcoordN, hsourceN] with r hrN hrSource
  have hrAgree : (extChartAt I x₀).symm (extChartAt I x₀ r) ∈ A :=
    (hNsub hrN).2
  rw [(extChartAt I x₀).left_inv hrSource] at hrAgree
  exact hrAgree.2 j

/-- Time reversal for the cutoff flow whenever both the original and reversed
time-one states remain in the region where the cutoff system is the genuine
coordinate geodesic equation. -/
theorem coordinateGeodesic_flow_reverse_time_one
    (G : E × E → E × E) (Φ : (E × E) → ℝ → E × E)
    (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G))
    (q : E × E)
    (hactual : ∀ s ∈ ({q, ((Φ q 1).1, -(Φ q 1).2)} : Set (E × E)),
      ∀ t ∈ Icc (-2 : ℝ) 2,
        (Φ s t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ s t) = secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ s t)) :
    Φ ((Φ q 1).1, -(Φ q 1).2) 1 = (q.1, -q.2) := by
  let qrev : E × E := ((Φ q 1).1, -(Φ q 1).2)
  let p₁ : ℝ → E × E := fun t ↦ Φ qrev t
  let p₂ : ℝ → E × E := fun t ↦ ((Φ q (1 - t)).1, -(Φ q (1 - t)).2)
  let J : Set ℝ := Ioo (-1 : ℝ) 2
  have hp₁ (t : ℝ) (ht : t ∈ J) :
      HasDerivAt p₁
        (secondOrderSystem (coordinateAcceleration cov x₀ b) (p₁ t)) t := by
    have htI : t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨htl, htr⟩
      constructor <;> linarith
    have h := hΦcurve qrev t
    change HasDerivAt (Φ qrev) (G (Φ qrev t)) t at h
    rw [(hactual qrev (by simp [qrev]) t htI).2] at h
    exact h
  have hp₂ (t : ℝ) (ht : t ∈ J) :
      HasDerivAt p₂
        (secondOrderSystem (coordinateAcceleration cov x₀ b) (p₂ t)) t := by
    have htime : 1 - t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨htl, htr⟩
      constructor <;> linarith
    have h := hΦcurve q (1 - t)
    change HasDerivAt (Φ q) (G (Φ q (1 - t))) (1 - t) at h
    rw [(hactual q (by simp) (1 - t) htime).2] at h
    have h' : HasDerivAt (Φ q)
        ((Φ q (1 - t)).2,
          coordinateAcceleration cov x₀ b (Φ q (1 - t)).1 (Φ q (1 - t)).2)
        (1 - t) := by
      simpa only [secondOrderSystem] using h
    have hclock : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t := by
      simpa using (hasDerivAt_id' t).const_sub (1 : ℝ)
    have hz₀ : HasDerivAt (fun s ↦ (Φ q s).1) (Φ q (1 - t)).2 (1 - t) := by
      simpa using h'.hasFDerivAt.fst.hasDerivAt
    have hu₀ : HasDerivAt (fun s ↦ (Φ q s).2)
        (coordinateAcceleration cov x₀ b (Φ q (1 - t)).1 (Φ q (1 - t)).2)
        (1 - t) := by
      simpa using h'.hasFDerivAt.snd.hasDerivAt
    have hz : HasDerivAt (fun s ↦ (Φ q (1 - s)).1)
        (-(Φ q (1 - t)).2) t := by
      simpa only [Function.comp_def, neg_one_smul] using hz₀.scomp t hclock
    have hu : HasDerivAt (fun s ↦ (Φ q (1 - s)).2)
        (-coordinateAcceleration cov x₀ b (Φ q (1 - t)).1 (Φ q (1 - t)).2) t := by
      simpa only [Function.comp_def, neg_one_smul] using hu₀.scomp t hclock
    have hnegFun : (fun s ↦ -(Φ q (1 - s)).2) =ᶠ[𝓝 t]
        (- fun s ↦ (Φ q (1 - s)).2) := by
      exact Filter.Eventually.of_forall (fun _ ↦ rfl)
    have huNeg : HasDerivAt (fun s ↦ -(Φ q (1 - s)).2)
        (coordinateAcceleration cov x₀ b (Φ q (1 - t)).1 (Φ q (1 - t)).2) t := by
      simpa only [neg_neg] using hu.neg.congr_of_eventuallyEq hnegFun
    simpa only [p₂, secondOrderSystem,
      coordinateAcceleration_neg (I := I) (M := M) cov x₀ b] using hz.prodMk huNeg
  have hF (t : ℝ) (ht : t ∈ J) :
      ContDiffAt ℝ 1
        (fun s : E × E ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) s)
        (p₁ t) := by
    apply coordinateAcceleration_system_contDiffAt_of_mem_target
    have htI : t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨htl, htr⟩
      constructor <;> linarith
    exact (hactual qrev (by simp [qrev]) t htI).1
  have hinitial : p₁ 0 = p₂ 0 := by
    change Φ qrev 0 = ((Φ q (1 - 0)).1, -(Φ q (1 - 0)).2)
    rw [hΦzero]
    simp only [sub_zero, qrev]
  have heq := secondOrder_pair_eqOn_of_same_initial
    (F := coordinateAcceleration cov x₀ b) (J := J)
    isOpen_Ioo isPreconnected_Ioo (by constructor <;> norm_num)
    hp₁ hp₂ hF hinitial
  have hone : (1 : ℝ) ∈ J := by constructor <;> norm_num
  have h := heq hone
  dsimp [p₁, p₂, qrev] at h
  simpa [hΦzero] using h

/-- The two-point endpoint local equivalence can be restricted to a source
which is invariant under terminal-state reversal.  On that source, reversing
a time-one coordinate geodesic and flowing for one more unit recovers the
original position with opposite velocity. -/
theorem exists_reversalInvariant_twoPoint_coordinateGeodesic_localEquiv
    {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hzcenter : z = extChartAt I x₀ x₀) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ∃ R : OpenPartialHomeomorph (E × E) (E × E),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      G =ᶠ[𝓝 (z, 0)]
        (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
      (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
      (∀ t, Φ (z, 0) t = (z, 0)) ∧
      ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
      (∀ q, R q = (q.1, (Φ q 1).1)) ∧
      (z, 0) ∈ R.source ∧ (z, z) ∈ R.target ∧
      (∀ y ∈ R.target, ContDiffAt ℝ 1 R.symm y) ∧
      (∀ q ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
        (Φ q t).1 ∈ (extChartAt I x₀).target ∧
          G (Φ q t) =
            secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ q t) ∧
          G =ᶠ[𝓝 (Φ q t)]
            (fun p ↦ secondOrderSystem
              (coordinateAcceleration cov x₀ b) p)) ∧
      (∀ q ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
        ∀ j : Fin (Module.finrank ℝ E),
          smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
            𝓝 ((extChartAt I x₀).symm (Φ q t).1)]
            (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j) ∧
      ∀ q ∈ R.source,
        let qrev : E × E := ((Φ q 1).1, -(Φ q 1).2)
        qrev ∈ R.source ∧ Φ qrev 1 = (q.1, -q.2) := by
  obtain ⟨G, Φ, R₀, hG, hGcompact, hGeq, hΦzero, hΦcurve, hfix, hΦsmooth,
    hR₀, hsource₀, _htarget₀, hinverseSmooth₀, hactual₀, hframe₀⟩ :=
    exists_twoPoint_coordinateGeodesic_localEquiv
      (I := I) (M := M) (E := E) cov x₀ b hz hzcenter
  let rev : E × E → E × E := fun q ↦ ((Φ q 1).1, -(Φ q 1).2)
  have hrevcont : Continuous rev :=
    (hΦsmooth.fst.prodMk hΦsmooth.snd.neg).continuous
  let U : Set (E × E) := R₀.source ∩ rev ⁻¹' R₀.source
  have hUopen : IsOpen U :=
    R₀.open_source.inter (R₀.open_source.preimage hrevcont)
  have hrevfix : rev (z, 0) = (z, 0) := by
    simp only [rev, hfix, neg_zero]
  have hzU : (z, 0) ∈ U := by
    refine ⟨hsource₀, ?_⟩
    change rev (z, 0) ∈ R₀.source
    rw [hrevfix]
    exact hsource₀
  let R : OpenPartialHomeomorph (E × E) (E × E) := R₀.restr U
  have hR (q : E × E) : R q = (q.1, (Φ q 1).1) := by
    rw [show (R : E × E → E × E) = R₀ from
      OpenPartialHomeomorph.restr_apply R₀ U]
    exact hR₀ q
  have hsource : (z, 0) ∈ R.source := by
    change (z, 0) ∈ (R₀.restr U).source
    rw [R₀.restr_source' U hUopen]
    exact ⟨hsource₀, hzU⟩
  have htarget : (z, z) ∈ R.target := by
    have hmap := R.map_source hsource
    rw [hR] at hmap
    simpa [hfix] using hmap
  have hinverseSmooth : ∀ y ∈ R.target, ContDiffAt ℝ 1 R.symm y := by
    intro y hy
    have hxsource : R.symm y ∈ R.source := R.map_target hy
    have hxsource₀ : R.symm y ∈ R₀.source := by
      change R.symm y ∈ (R₀.restr U).source at hxsource
      rw [R₀.restr_source' U hUopen] at hxsource
      exact hxsource.1
    have hy₀ : y ∈ R₀.target := by
      have hmap := R₀.map_source hxsource₀
      have hvalue' : R₀ (R.symm y) = y := by
        rw [hR₀, ← hR, R.right_inv hy]
      rw [hvalue'] at hmap
      exact hmap
    have hsmooth := hinverseSmooth₀ y hy₀
    have hsymmEq : (R.symm : E × E → E × E) = R₀.symm := by
      exact OpenPartialHomeomorph.restr_symm_apply R₀ U
    rw [hsymmEq]
    exact hsmooth
  have hactual : ∀ q ∈ R.source, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ q t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ q t) = secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ q t) ∧
        G =ᶠ[𝓝 (Φ q t)]
          (fun p ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) p) := by
    intro q hq t ht
    apply hactual₀ q
    · change q ∈ (R₀.restr U).source at hq
      rw [R₀.restr_source' U hUopen] at hq
      exact hq.1
    · exact ht
  have hframe : ∀ q ∈ R.source, ∀ t ∈ Icc (-1 : ℝ) 1,
      ∀ j : Fin (Module.finrank ℝ E),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j =ᶠ[
          𝓝 ((extChartAt I x₀).symm (Φ q t).1)]
          (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j := by
    intro q hq t ht j
    apply hframe₀ q
    · change q ∈ (R₀.restr U).source at hq
      rw [R₀.restr_source' U hUopen] at hq
      exact hq.1
    · exact ht
  refine ⟨G, Φ, R, hG, hGcompact, hGeq, hΦzero, hΦcurve, hfix, hΦsmooth,
    hR, hsource, htarget, hinverseSmooth, hactual, hframe, ?_⟩
  intro q hq
  have hqdata : q ∈ R₀.source ∧ q ∈ U := by
    change q ∈ (R₀.restr U).source at hq
    rwa [R₀.restr_source' U hUopen] at hq
  have hrevR₀ : rev q ∈ R₀.source := hqdata.2.2
  have hreverse : Φ (rev q) 1 = (q.1, -q.2) := by
    apply coordinateGeodesic_flow_reverse_time_one
      (I := I) (M := M) cov x₀ b G Φ hΦzero hΦcurve q
    intro s hs t ht
    simp only [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with hs | hs
    · rw [hs]
      exact ⟨(hactual₀ q hqdata.1 t ht).1,
        (hactual₀ q hqdata.1 t ht).2.1⟩
    · rw [hs]
      exact ⟨(hactual₀ (rev q) hrevR₀ t ht).1,
        (hactual₀ (rev q) hrevR₀ t ht).2.1⟩
  have hrevrev : rev (rev q) = q := by
    simp only [rev]
    rw [hreverse]
    simp only [neg_neg]
  have hrevU : rev q ∈ U := by
    refine ⟨hrevR₀, ?_⟩
    change rev (rev q) ∈ R₀.source
    rw [hrevrev]
    exact hqdata.1
  have hrevSource : rev q ∈ R.source := by
    change rev q ∈ (R₀.restr U).source
    rw [R₀.restr_source' U hUopen]
    exact ⟨hrevR₀, hrevU⟩
  exact ⟨hrevSource, hreverse⟩

/-- The near-zero cutoff flow can be chosen with the radial equivariance
needed for normal-coordinate arguments.  This strengthens the zero-velocity
flow package by an equality of full position--velocity states on the closed
unit square, not merely an equality of time-one endpoints. -/
theorem exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_radial
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z, 0)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
          (ContinuousLinearMap.id ℝ E) 0 ∧
        (∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (z, a • u) t =
            ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2)) := by
  obtain ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth,
    _hflowDeriv, hfix, hend⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity
      (I := I) (M := M) (E := E) cov x₀ b hz
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGcompact hG (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hGeq
  refine ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix, hend, ?_⟩
  apply flow_radial_of_ball (I := I) (M := M) cov x₀ b G Φ hK
    ⟨ε, hε, ?_⟩ hΦzero hΦcurve hfix
  intro q hq
  apply hball
  exact Metric.mem_ball'.mpr (by simpa [dist_comm] using hq)

/-- The cutoff flow from `exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity`
is an actual coordinate-geodesic flow on the whole unit-time window for all
sufficiently small initial velocities.  The proof uses the global Lipschitz
bound only to keep the nearby orbit inside the neighbourhood where the cutoff
field agrees with the coordinate system. -/
theorem exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_local_eventually_radial
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z, 0)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
          (ContinuousLinearMap.id ℝ E) 0 ∧
        (∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (z, a • u) t =
            ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2)) ∧
        (∀ᶠ u in 𝓝 0, ∀ t ∈ Icc (-2 : ℝ) 2,
          (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
            G (Φ (z, u) t) =
              secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t) ∧
            G =ᶠ[𝓝 (Φ (z, u) t)]
              (fun q ↦ secondOrderSystem
                (coordinateAcceleration cov x₀ b) q)) := by
  obtain ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix, hend,
    hradial⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_radial
      (I := I) (M := M) (E := E) cov x₀ b hz
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGcompact hG (by norm_num)
  let F : E × E → E × E := fun q ↦
    secondOrderSystem (coordinateAcceleration cov x₀ b) q
  let S : Set (E × E) := {q | G q = F q}
  have hS : S ∈ 𝓝 (z, 0) := hGeq
  let T : Set (E × E) := (extChartAt I x₀).target ×ˢ Set.univ
  have hT : T ∈ 𝓝 (z, 0) := by
    exact ((isOpen_extChartAt_target x₀).prod isOpen_univ).mem_nhds
      ⟨hz, Set.mem_univ _⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hS hT)
  let δ : ℝ := ε / Real.exp ((K : ℝ) * 2)
  have hδ : 0 < δ := div_pos hε (Real.exp_pos _)
  refine ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix, hend,
    hradial, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with u hu
  intro t ht
  have hnorm : ‖u‖ < δ := by
    simpa [Real.dist_eq] using (Metric.mem_ball'.mp hu)
  have habs : |t| ≤ 2 := by
    rw [abs_le]
    exact ht
  have hexp : Real.exp ((K : ℝ) * |t|) ≤ Real.exp ((K : ℝ) * 2) :=
    Real.exp_le_exp.mpr (by
      calc
        (K : ℝ) * |t| ≤ (K : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left habs K.coe_nonneg
        _ = (K : ℝ) * 2 := rfl)
  have hflow := RicciFlow.AnalyticPDE.SmoothDependenceCk.dist_flow_apply_le
    (v := fun _ : ℝ ↦ G) (K := K) (t₀ := 0)
    (fun _ ↦ hK) hΦcurve hΦzero (z, u) (z, 0) t
  rw [hfix t] at hflow
  have hdist : dist (Φ (z, u) t) (z, 0) < ε := by
    calc
      dist (Φ (z, u) t) (z, 0)
          ≤ dist (z, u) (z, 0) * Real.exp ((K : ℝ) * |t - 0|) := hflow
      _ = ‖u‖ * Real.exp ((K : ℝ) * |t|) := by
        rw [sub_zero, Prod.dist_eq]
        simp [dist_eq_norm]
      _ ≤ ‖u‖ * Real.exp ((K : ℝ) * 2) :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ < δ * Real.exp ((K : ℝ) * 2) :=
        mul_lt_mul_of_pos_right hnorm (Real.exp_pos _)
      _ = ε := by
        dsimp [δ]
        exact div_mul_cancel₀ ε (ne_of_gt (Real.exp_pos _))
  have hmem : Φ (z, u) t ∈ S ∩ T := hball
    (Metric.mem_ball'.mpr (by simpa [dist_comm] using hdist))
  refine ⟨hmem.2.1, hmem.1, ?_⟩
  change {q | G q = F q} ∈ 𝓝 (Φ (z, u) t)
  have horbitBall : Φ (z, u) t ∈ Metric.ball (z, 0) ε :=
    Metric.mem_ball'.mpr (by simpa [dist_comm] using hdist)
  apply mem_of_superset (Metric.isOpen_ball.mem_nhds horbitBall)
  intro q hq
  exact (hball hq).1

/-- Backward-compatible form of the local radial flow package.  The stronger
theorem above additionally records neighbourhood equality of the cutoff and
coordinate vector fields at every nearby orbit point. -/
theorem exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_local_radial
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z, 0)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
          (ContinuousLinearMap.id ℝ E) 0 ∧
        (∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (z, a • u) t =
            ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2)) ∧
        (∀ᶠ u in 𝓝 0, ∀ t ∈ Icc (-2 : ℝ) 2,
          (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
            G (Φ (z, u) t) =
              secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t)) := by
  obtain ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix, hend,
    hradial, hlocal⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_local_eventually_radial
      (I := I) (M := M) (E := E) cov x₀ b hz
  refine ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix, hend,
    hradial, ?_⟩
  filter_upwards [hlocal] with u hu
  intro t ht
  exact ⟨(hu t ht).1, (hu t ht).2.1⟩

/-- Backward-compatible local-flow package, retaining the original contract
while the radial refinement is available through the theorem immediately
above. -/
theorem exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_local
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z, 0)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
          (ContinuousLinearMap.id ℝ E) 0 ∧
        (∀ᶠ u in 𝓝 0, ∀ t ∈ Icc (-2 : ℝ) 2,
          (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
            G (Φ (z, u) t) =
              secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t)) := by
  obtain ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix, hend,
    hradial, hlocal⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_local_radial
      (I := I) (M := M) (E := E) cov x₀ b hz
  exact ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix, hend, hlocal⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- An open `C¹` right inverse has the expected differential right-inverse
identity.  This packages the local normal-coordinate endpoint map and its
inverse as a genuine first-order inverse pair on the open target domain. -/
theorem fderiv_comp_fderiv_of_open_rightInverse
    {f ψ : E → E} {V : Set E} (hf : ContDiff ℝ 1 f)
    (hVopen : IsOpen V) (hψon : ContDiffOn ℝ 1 ψ V)
    (hright : ∀ y ∈ V, f (ψ y) = y) {y : E} (hy : y ∈ V) :
    (fderiv ℝ f (ψ y)).comp (fderiv ℝ ψ y) = ContinuousLinearMap.id ℝ E := by
  have hfderiv : HasFDerivAt f (fderiv ℝ f (ψ y)) (ψ y) :=
    hf.contDiffAt.differentiableAt one_ne_zero |>.hasFDerivAt
  have hψderiv : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
    (hψon.contDiffAt (hVopen.mem_nhds hy)).differentiableAt one_ne_zero |>.hasFDerivAt
  have hcomp : HasFDerivAt (f ∘ ψ)
      ((fderiv ℝ f (ψ y)).comp (fderiv ℝ ψ y)) y :=
    hfderiv.comp y hψderiv
  have heq : (fun z : E ↦ z) =ᶠ[𝓝 y] (f ∘ ψ) := by
    filter_upwards [hVopen.mem_nhds hy] with z hz
    simpa [Function.comp_def] using (hright z hz).symm
  exact (hcomp.congr_of_eventuallyEq heq).unique (hasFDerivAt_id y)

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- In one finite-dimensional model space, a continuous-linear right inverse
is automatically also a left inverse. -/
theorem continuousLinearMap_comp_eq_id_of_comp_eq_id
    (L R : E →L[ℝ] E)
    (hcomp : L.comp R = ContinuousLinearMap.id ℝ E) :
    R.comp L = ContinuousLinearMap.id ℝ E := by
  have hsurj : Function.Surjective L := by
    intro y
    refine ⟨R y, ?_⟩
    have happ := congrArg (fun A : E →L[ℝ] E ↦ A y) hcomp
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using happ
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := E) (V₂ := E) rfl).2 hsurj
  ext x
  apply hinj
  have happ := congrArg (fun A : E →L[ℝ] E ↦ A (L x)) hcomp
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using happ

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- On the open domain of a `C¹` right inverse between equal
finite-dimensional model spaces, the two derivatives are mutual inverses. -/
theorem fderiv_fderiv_comp_of_open_rightInverse
    {f ψ : E → E} {V : Set E} (hf : ContDiff ℝ 1 f)
    (hVopen : IsOpen V) (hψon : ContDiffOn ℝ 1 ψ V)
    (hright : ∀ y ∈ V, f (ψ y) = y) {y : E} (hy : y ∈ V) :
    (fderiv ℝ ψ y).comp (fderiv ℝ f (ψ y)) =
      ContinuousLinearMap.id ℝ E := by
  apply continuousLinearMap_comp_eq_id_of_comp_eq_id
  exact fderiv_comp_fderiv_of_open_rightInverse hf hVopen hψon hright hy

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- The derivative of the local coordinate inverse is a linear bijection at
every point of its open target domain. -/
theorem fderiv_bijective_of_open_rightInverse
    {f ψ : E → E} {V : Set E} (hf : ContDiff ℝ 1 f)
    (hVopen : IsOpen V) (hψon : ContDiffOn ℝ 1 ψ V)
    (hright : ∀ y ∈ V, f (ψ y) = y) {y : E} (hy : y ∈ V) :
    Function.Bijective (fderiv ℝ ψ y) := by
  have hforward :=
    fderiv_comp_fderiv_of_open_rightInverse hf hVopen hψon hright hy
  have hbackward :=
    fderiv_fderiv_comp_of_open_rightInverse hf hVopen hψon hright hy
  constructor
  · intro v w hvw
    have happ := congrArg (fun q ↦ fderiv ℝ f (ψ y) q) hvw
    have hv := congrArg (fun A : E →L[ℝ] E ↦ A v) hforward
    have hw := congrArg (fun A : E →L[ℝ] E ↦ A w) hforward
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      hv.symm.trans (happ.trans hw)
  · intro v
    refine ⟨fderiv ℝ f (ψ y) v, ?_⟩
    have happ := congrArg (fun A : E →L[ℝ] E ↦ A v) hbackward
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using happ

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- The position component of the linearization of a second-order system is
the velocity component of the input variation. -/
theorem fderiv_secondOrderSystem_fst_apply
    {F : E → E → E} {q w : E × E}
    (hF : DifferentiableAt ℝ (secondOrderSystem F) q) :
    (fderiv ℝ (secondOrderSystem F) q w).1 = w.2 := by
  have hfst : HasFDerivAt (fun p : E × E ↦ (secondOrderSystem F p).1)
      ((ContinuousLinearMap.fst ℝ E E).comp
        (fderiv ℝ (secondOrderSystem F) q)) q :=
    hF.hasFDerivAt.fst
  have hsnd : HasFDerivAt (fun p : E × E ↦ p.2)
      (ContinuousLinearMap.snd ℝ E E) q := hasFDerivAt_snd
  have hmaps : (ContinuousLinearMap.fst ℝ E E).comp
      (fderiv ℝ (secondOrderSystem F) q) =
        ContinuousLinearMap.snd ℝ E E := by
    apply HasFDerivAt.unique
    · simpa only [secondOrderSystem_fst] using hfst
    · exact hsnd
  have happ := congrArg (fun L : (E × E) →L[ℝ] E ↦ L w) hmaps
  change (ContinuousLinearMap.fst ℝ E E)
      (fderiv ℝ (secondOrderSystem F) q w) =
    (ContinuousLinearMap.snd ℝ E E) w
  simpa only [ContinuousLinearMap.comp_apply] using happ

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- A compactly supported `C¹` flow admits a genuine first variation for every
initial-state direction.  The returned curve `W` solves the linearized ODE
along the reference trajectory and is the derivative at zero of the perturbed
flow `s ↦ Φ (q + s • w) t` at every nonnegative time.

This is an analytic variation package.  It does not yet assert a geometric
Gauss lemma or a length-minimizing property. -/
theorem exists_firstVariation_of_contDiff_compactSupport_flow
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [CompleteSpace X]
    {G : X → X} (hG : ContDiff ℝ 1 G) (hGcompact : HasCompactSupport G)
    {Φ : X → ℝ → X} (hΦzero : ∀ q, Φ q 0 = q)
    (hΦcurve : ∀ q, IsIntegralCurve (Φ q) (fun _ : ℝ ↦ G))
    (q w : X) :
    ∃ (K : NNReal) (A : ℝ → (X →L[ℝ] X)) (W : ℝ → X),
      (∀ t, ‖A t‖₊ ≤ K) ∧
      (∀ t, A t = fderiv ℝ G (Φ q t)) ∧
      W 0 = w ∧
      (∀ t, HasDerivAt W (A t (W t)) t) ∧
      (∀ t, 0 ≤ t → HasDerivAt (fun s : ℝ ↦ Φ (q + s • w) t) (W t) 0) := by
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hGcompact hG (by norm_num)
  obtain ⟨DG, hDGcont, hDG⟩ := contDiff_one_iff_hasFDerivAt.mp hG
  let A : ℝ → (X →L[ℝ] X) := fun t ↦ DG (Φ q t)
  have hA : ∀ t, ‖A t‖₊ ≤ K := by
    intro t
    dsimp [A]
    exact_mod_cast (hDG (Φ q t)).le_of_lipschitz hK
  have hAcont : Continuous A := by
    dsimp [A]
    exact hDGcont.comp (hΦcurve q).continuous
  obtain ⟨Ψ, hΨzero, hΨcurve⟩ :=
    RicciFlow.AnalyticPDE.SmoothDependenceCk.exists_variationalFlowFamily hA hAcont
  let W : ℝ → X := fun t ↦
    RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution hA hΨcurve hΨzero t w
  refine ⟨K, A, W, hA, ?_, ?_, ?_, ?_⟩
  · intro t
    exact (hDG (Φ q t)).fderiv.symm
  · simpa only [W] using
      RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution_apply_anchor
        hA hΨcurve hΨzero w
  · intro t
    have hW := RicciFlow.AnalyticPDE.SmoothDependenceCk.isIntegralCurve_fundamentalSolution_apply
      hA hΨcurve hΨzero w t
    simpa only [W, RicciFlow.AnalyticPDE.SmoothDependenceCk.variationalFieldVec] using hW
  · intro t ht
    have hflow := RicciFlow.AnalyticPDE.SmoothDependenceCk.hasFDerivAt_flow_of_continuous_deriv
      (v := fun _ : ℝ ↦ G) (K := K) (t₀ := 0) (Φ := Φ)
      (fun _ ↦ hK) hA hΨcurve hΨzero hΦcurve hΦzero q ht
      (Dv := fun _ : ℝ ↦ DG) (fun _ x ↦ hDG x) (by fun_prop) (fun _ ↦ rfl)
    have hinput : HasDerivAt (fun s : ℝ ↦ q + s • w) w 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).smul_const w |>.add_const q
    have hflow' : HasFDerivAt (fun p ↦ Φ p t)
        (RicciFlow.AnalyticPDE.SmoothDependenceCk.fundamentalSolution
          hA hΨcurve hΨzero t) (q + (0 : ℝ) • w) := by
      simpa using hflow
    have hcomp := hflow'.comp 0 hinput.hasFDerivAt
    simpa only [W, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hcomp.hasDerivAt

/-- The localized coordinate-geodesic flow has a first variation in every
initial-velocity direction.  The position component of `W` is exactly the
derivative of the coordinate position reached from `u + s • w`.

The theorem deliberately keeps the compactly supported extension and its
local agreement with the coordinate geodesic system explicit.  A later
Gauss-lemma proof must still establish a uniform actual-system variation and
the required metric identity. -/
theorem exists_firstVariation_localized_coordinateGeodesic_flow
    {z : E} (hz : z ∈ (extChartAt I x₀).target) (u w : E) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E,
      ∃ K : NNReal, ∃ A : ℝ → ((E × E) →L[ℝ] (E × E)), ∃ W : ℝ → E × E,
        ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z, u)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        (∀ t, ‖A t‖₊ ≤ K) ∧
        (∀ t, A t = fderiv ℝ G (Φ (z, u) t)) ∧
        W 0 = (0, w) ∧
        (∀ t, HasDerivAt W (A t (W t)) t) ∧
        (∀ t, 0 ≤ t →
          HasDerivAt (fun s : ℝ ↦ (Φ (z, u + s • w) t).1) (W t).1 0) := by
  obtain ⟨G, hG, hGcompact, hGeq, Φ, hΦzero, hΦcurve, _⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow
      (I := I) (M := M) (E := E) cov x₀ b hz u (T := 0) (by norm_num)
  obtain ⟨K, A, W, hA, hAeq, hWzero, hWderiv, hWvar⟩ :=
    exists_firstVariation_of_contDiff_compactSupport_flow hG hGcompact hΦzero hΦcurve
      (z, u) (0, w)
  refine ⟨G, Φ, K, A, W, hG, hGcompact, hGeq, hΦzero, hΦcurve,
    hA, hAeq, hWzero, hWderiv, ?_⟩
  intro t ht
  have hfirst := (hWvar t ht).hasFDerivAt.fst.hasDerivAt
  have hfst : (ContinuousLinearMap.fst ℝ E E) (W t) = (W t).1 := by
    rfl
  rw [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, hfst] at hfirst
  simpa using hfirst

/-- There is one open neighbourhood of zero initial velocity on which the
cutoff flow is a genuine coordinate-geodesic flow and admits transverse first
variations.  Along every reference orbit in the neighbourhood, the
linearized coefficient is the derivative of the actual second-order
geodesic system, not merely of the cutoff.  Nearby perturbed velocities also
remain actual coordinate geodesics on the whole time window.

This supplies the uniform analytic two-parameter input for a Gauss-lemma
argument; no metric orthogonality or minimizing conclusion is asserted here. -/
theorem exists_open_velocity_neighborhood_actual_firstVariation
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E, ∃ U : Set E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        HasFDerivAt (fun u : E ↦ (Φ (z, u) 1).1)
          (ContinuousLinearMap.id ℝ E) 0 ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        IsOpen U ∧ 0 ∈ U ∧
        (∀ u ∈ U, ∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (z, a • u) t =
            ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2)) ∧
        (∀ u ∈ U, ∀ t ∈ Icc (-2 : ℝ) 2,
          (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
            G (Φ (z, u) t) =
              secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t) ∧
            G =ᶠ[𝓝 (Φ (z, u) t)]
              (fun q ↦ secondOrderSystem
                (coordinateAcceleration cov x₀ b) q)) ∧
        ∀ u ∈ U, ∀ w : E,
          ∃ K : NNReal, ∃ A : ℝ → ((E × E) →L[ℝ] (E × E)), ∃ W : ℝ → E × E,
            (∀ t, ‖A t‖₊ ≤ K) ∧
            (∀ t, A t = fderiv ℝ G (Φ (z, u) t)) ∧
            (∀ t ∈ Icc (-2 : ℝ) 2,
              A t = fderiv ℝ
                (fun q ↦ secondOrderSystem
                  (coordinateAcceleration cov x₀ b) q) (Φ (z, u) t)) ∧
            W 0 = (0, w) ∧
            (∀ t, HasDerivAt W (A t (W t)) t) ∧
            (∀ t ∈ Icc (-2 : ℝ) 2,
              HasDerivAt (fun s ↦ (W s).1) (W t).2 t) ∧
            (∀ t, 0 ≤ t →
              HasDerivAt (fun s : ℝ ↦ Φ (z, u + s • w) t) (W t) 0) ∧
            (∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (-2 : ℝ) 2,
              (Φ (z, u + s • w) t).1 ∈ (extChartAt I x₀).target ∧
                G (Φ (z, u + s • w) t) =
                  secondOrderSystem (coordinateAcceleration cov x₀ b)
                    (Φ (z, u + s • w) t)) := by
  obtain ⟨G, Φ, hG, hGcompact, _, hΦzero, hΦcurve, hΦsmooth, hfix, hend, hradial,
    hlocal⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_local_eventually_radial
      (I := I) (M := M) (E := E) cov x₀ b hz
  have hboth : ∀ᶠ u in 𝓝 (0 : E),
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        Φ (z, a • u) t =
          ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2)) ∧
      (∀ t ∈ Icc (-2 : ℝ) 2,
        (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
          G (Φ (z, u) t) =
            secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t) ∧
          G =ᶠ[𝓝 (Φ (z, u) t)]
            (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q)) :=
    hradial.and hlocal
  obtain ⟨U, hUsub, hUopen, hzeroU⟩ := mem_nhds_iff.mp hboth
  refine ⟨G, Φ, U, hG, hGcompact, hΦzero, hΦcurve, hΦsmooth, hend, hfix,
    hUopen, hzeroU, ?_, ?_, ?_⟩
  · intro u hu
    exact (hUsub hu).1
  · intro u hu
    exact (hUsub hu).2
  · intro u hu w
    obtain ⟨K, A, W, hA, hAeq, hWzero, hWderiv, hWvar⟩ :=
      exists_firstVariation_of_contDiff_compactSupport_flow hG hGcompact
        hΦzero hΦcurve (z, u) (0, w)
    have hactual := (hUsub hu).2
    have hAactual : ∀ t ∈ Icc (-2 : ℝ) 2,
        A t = fderiv ℝ
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q)
            (Φ (z, u) t) := by
      intro t ht
      calc
        A t = fderiv ℝ G (Φ (z, u) t) := hAeq t
        _ = fderiv ℝ
            (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q)
              (Φ (z, u) t) := ((hactual t ht).2.2).fderiv_eq
    have hvariation : ∀ t, 0 ≤ t →
        HasDerivAt (fun s : ℝ ↦ Φ (z, u + s • w) t) (W t) 0 := by
      intro t ht
      simpa using hWvar t ht
    have hpositionVariation : ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivAt (fun s ↦ (W s).1) (W t).2 t := by
      intro t ht
      have hFdiff : DifferentiableAt ℝ
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q)
          (Φ (z, u) t) := by
        have hC1 := coordinateAcceleration_system_contDiffAt_of_mem_target
          (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
          ((hactual t ht).1) (Φ (z, u) t).2
        exact hC1.differentiableAt one_ne_zero
      have htime := (hWderiv t).hasFDerivAt.fst.hasDerivAt
      rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul] at htime
      change HasDerivAt (fun s ↦ (W s).1) ((A t (W t)).1) t at htime
      rw [hAactual t ht,
        fderiv_secondOrderSystem_fst_apply (F := coordinateAcceleration cov x₀ b)
          hFdiff] at htime
      exact htime
    have htendsto : Tendsto (fun s : ℝ ↦ u + s • w) (𝓝 0) (𝓝 u) := by
      have hcont : ContinuousAt (fun s : ℝ ↦ u + s • w) 0 := by fun_prop
      change Tendsto (fun s : ℝ ↦ u + s • w) (𝓝 0)
        (𝓝 (u + (0 : ℝ) • w)) at hcont
      simpa only [zero_smul, add_zero] using hcont
    have hperturbU : ∀ᶠ s in 𝓝 (0 : ℝ), u + s • w ∈ U :=
      htendsto.eventually (hUopen.mem_nhds hu)
    have hperturb : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc (-2 : ℝ) 2,
        (Φ (z, u + s • w) t).1 ∈ (extChartAt I x₀).target ∧
          G (Φ (z, u + s • w) t) =
            secondOrderSystem (coordinateAcceleration cov x₀ b)
              (Φ (z, u + s • w) t) := by
      filter_upwards [hperturbU] with s hs
      intro t ht
      exact ⟨((hUsub hs).2 t ht).1, ((hUsub hs).2 t ht).2.1⟩
    exact ⟨K, A, W, hA, hAeq, hAactual, hWzero, hWderiv,
      hpositionVariation, hvariation, hperturb⟩

/-- The time-one coordinate endpoint map at a stationary state has a genuine
local inverse in the initial-velocity variable.  Both inverse identities are
recorded as neighbourhood statements, which is the form needed to shrink to a
normal coordinate neighbourhood later. -/
theorem exists_localInverse_coordinateGeodesic_endpoint_map_zero_velocity_radial
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E, ∃ ψ : E → E,
      ∃ V : Set E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z, 0)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        (∀ᶠ u in 𝓝 0, ∀ t ∈ Icc (-2 : ℝ) 2,
          (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
            G (Φ (z, u) t) =
              secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t)) ∧
        (∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          Φ (z, a • u) t =
            ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2)) ∧
        IsOpen V ∧ z ∈ V ∧ ContDiffOn ℝ 1 ψ V ∧
        (∀ y ∈ V, (Φ (z, ψ y) 1).1 = y) ∧
        (∀ y ∈ V,
          (fderiv ℝ (fun u : E ↦ (Φ (z, u) 1).1) (ψ y)).comp
            (fderiv ℝ ψ y) = ContinuousLinearMap.id ℝ E) ∧
        (∀ y ∈ V,
          (fderiv ℝ ψ y).comp
            (fderiv ℝ (fun u : E ↦ (Φ (z, u) 1).1) (ψ y)) =
              ContinuousLinearMap.id ℝ E) ∧
        (∀ y ∈ V, Function.Bijective (fderiv ℝ ψ y)) ∧
        (∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1,
          (Φ (z, u) a).1 ∈ V) ∧
        ContinuousAt ψ z ∧
        ContDiffAt ℝ 1 ψ z ∧
        HasStrictFDerivAt ψ (ContinuousLinearMap.id ℝ E) z ∧
        ψ z = 0 ∧
        (∀ᶠ u in 𝓝 0, ψ ((Φ (z, u) 1).1) = u) ∧
        (∀ᶠ y in 𝓝 z, (Φ (z, ψ y) 1).1 = y) := by
  obtain ⟨G, Φ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix, hend,
    hradial, hlocal⟩ :=
    exists_contDiff_coordinateGeodesic_extension_flow_zero_velocity_local_radial
      (I := I) (M := M) (E := E) cov x₀ b hz
  let f : E → E := fun u ↦ (Φ (z, u) 1).1
  have hinit : ContDiff ℝ 1 (fun u : E ↦ (z, u)) := by
    simpa only [id_eq] using
      (contDiff_const (𝕜 := ℝ) (n := 1) (c := z)).prodMk
        (contDiff_id (𝕜 := ℝ) (n := 1))
  have hf : ContDiff ℝ 1 f := by
    change ContDiff ℝ 1 (fun u : E ↦ (Φ (z, u) 1).1)
    simpa only [Function.comp_apply] using (hΦsmooth.comp hinit).fst
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.refl ℝ E
  have hderiv : HasFDerivAt f (e : E →L[ℝ] E) 0 := by
    simpa only [f, e, ContinuousLinearEquiv.coe_refl] using hend
  have hne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  let hstrict : HasStrictFDerivAt f (e : E →L[ℝ] E) 0 :=
    hf.contDiffAt.hasStrictFDerivAt' hderiv hne
  let ψ : E → E := hstrict.localInverse f e 0
  let R : OpenPartialHomeomorph E E := hstrict.toOpenPartialHomeomorph f
  have hψR : ψ = R.symm := by rfl
  let R' : OpenPartialHomeomorph E E := R.restrContDiff ℝ 1 (by norm_num)
  have hfzero : f 0 = z := by
    change (Φ (z, 0) 1).1 = z
    rw [hfix 1]
  have hψsmooth : ContDiffAt ℝ 1 ψ z := by
    rw [← hfzero]
    simpa only [ψ, hstrict, ContDiffAt.localInverse] using
      hf.contDiffAt.to_localInverse hderiv hne
  have hψcont : ContinuousAt ψ z := hψsmooth.continuousAt
  have hψstrict : HasStrictFDerivAt ψ (ContinuousLinearMap.id ℝ E) z := by
    rw [← hfzero]
    have he : ((e.symm : E ≃L[ℝ] E) : E →L[ℝ] E) =
        ContinuousLinearMap.id ℝ E := by
      ext x
      rfl
    rw [← he]
    simpa only [ψ] using hstrict.to_localInverse
  have hψzero : ψ z = 0 := by
    rw [← hfzero]
    simpa only [ψ] using hstrict.localInverse_apply_image
  let V : Set E := R'.target
  have hVopen : IsOpen V := by
    exact R'.open_target
  have hzeroSource : (0 : E) ∈ R'.source := by
    change 0 ∈ R.source ∧ ContDiffAt ℝ 1 R 0 ∧ ContDiffAt ℝ 1 R.symm (R 0)
    refine ⟨hstrict.mem_toOpenPartialHomeomorph_source, ?_, ?_⟩
    · simpa only [R, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hf.contDiffAt
    · rw [← hψR]
      change ContDiffAt ℝ 1 ψ (f 0)
      rw [hfzero]
      exact hψsmooth
  have hzV : z ∈ V := by
    have hmap := R'.map_source hzeroSource
    change R' 0 ∈ V at hmap
    have hR'zero : R' 0 = f 0 := by
      change R 0 = f 0
      simpa only [R] using congrFun hstrict.toOpenPartialHomeomorph_coe 0
    rw [hR'zero, hfzero] at hmap
    exact hmap
  have hψon : ContDiffOn ℝ 1 ψ V := by
    change ContDiffOn ℝ 1 ψ R'.target
    rw [hψR]
    exact R.contDiffOn_restrContDiff_target ℝ (by norm_num)
  have hψR' : ψ = R'.symm := by rfl
  have hrightV : ∀ y ∈ V, f (ψ y) = y := by
    intro y hy
    calc
      f (ψ y) = R' (R'.symm y) := by
        rw [hψR']
        symm
        change R (R'.symm y) = f (R'.symm y)
        simpa only [R] using congrFun hstrict.toOpenPartialHomeomorph_coe (R'.symm y)
      _ = y := R'.right_inv hy
  have hdiffV : ∀ y ∈ V,
      (fderiv ℝ f (ψ y)).comp (fderiv ℝ ψ y) = ContinuousLinearMap.id ℝ E := by
    intro y hy
    exact fderiv_comp_fderiv_of_open_rightInverse hf hVopen hψon hrightV hy
  have hdiffV' : ∀ y ∈ V,
      (fderiv ℝ ψ y).comp (fderiv ℝ f (ψ y)) = ContinuousLinearMap.id ℝ E := by
    intro y hy
    exact fderiv_fderiv_comp_of_open_rightInverse hf hVopen hψon hrightV hy
  have hbijV : ∀ y ∈ V, Function.Bijective (fderiv ℝ ψ y) := by
    intro y hy
    exact fderiv_bijective_of_open_rightInverse hf hVopen hψon hrightV hy
  have hVradial : ∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1,
      (Φ (z, u) a).1 ∈ V := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (R'.open_source.mem_nhds hzeroSource)
    filter_upwards [Metric.ball_mem_nhds (0 : E) hε, hradial] with u hu hradU
    intro a ha
    have hau : a • u ∈ Metric.ball (0 : E) ε := by
      apply Metric.mem_ball'.mpr
      have hu' : ‖u‖ < ε := by
        simpa [Real.dist_eq] using Metric.mem_ball'.mp hu
      rw [dist_comm, dist_zero_right, norm_smul]
      have habs : |a| ≤ 1 := abs_le.2 ⟨by linarith [ha.1], ha.2⟩
      have hscale : |a| * ‖u‖ ≤ ‖u‖ := by
        simpa using mul_le_mul_of_nonneg_right habs (norm_nonneg u)
      exact lt_of_le_of_lt hscale hu'
    have hsource : a • u ∈ R'.source := hball hau
    have hmap := R'.map_source hsource
    change R' (a • u) ∈ V at hmap
    have hfmem : f (a • u) ∈ V := by
      have hR'apply : R' (a • u) = f (a • u) := by
        change R (a • u) = f (a • u)
        simpa only [R] using congrFun hstrict.toOpenPartialHomeomorph_coe (a • u)
      rw [hR'apply] at hmap
      exact hmap
    have hflow := hradU a ha (1 : ℝ) ⟨by norm_num, by norm_num⟩
    have hfst : f (a • u) = (Φ (z, u) a).1 := by
      change (Φ (z, a • u) 1).1 = (Φ (z, u) a).1
      simpa using congrArg Prod.fst hflow
    rw [hfst] at hfmem
    exact hfmem
  refine ⟨G, Φ, ψ, V, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix,
    hlocal, hradial, hVopen, hzV, hψon, hrightV, hdiffV, hdiffV', hbijV, hVradial,
    hψcont, hψsmooth, hψstrict, hψzero, ?_, ?_⟩
  · simpa only [ψ, f] using hstrict.eventually_left_inverse
  · have hright : ∀ᶠ y in 𝓝 (f 0), f (ψ y) = y := by
      simpa only [ψ] using hstrict.eventually_right_inverse
    rw [hfzero] at hright
    simpa only [f] using hright

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- A local inverse for the time-one endpoint map inherits the radial
reparameterization of a coordinate-geodesic flow.  Thus, after one common
neighbourhood shrink, applying the inverse to the position at time `a`
recovers precisely `a • u` for every `a ∈ [0,1]`.

This is a normal-coordinate identity only; it does not assert that the radial
geodesic is minimizing. -/
lemma eventually_leftInverse_flow_radial
    {z : E} (Φ : (E × E) → ℝ → E × E) (ψ : E → E)
    (hradial : ∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        Φ (z, a • u) t =
          ((Φ (z, u) (a * t)).1, a • (Φ (z, u) (a * t)).2))
    (hleft : ∀ᶠ u in 𝓝 (0 : E), ψ ((Φ (z, u) 1).1) = u) :
    ∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1,
      ψ ((Φ (z, u) a).1) = a • u := by
  obtain ⟨εr, hεr, hrball⟩ := Metric.mem_nhds_iff.mp hradial
  obtain ⟨εl, hεl, hlball⟩ := Metric.mem_nhds_iff.mp hleft
  let δ : ℝ := min εr εl
  have hδ : 0 < δ := lt_min hεr hεl
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with u hu
  have hunorm : ‖u‖ < δ := by
    simpa [Real.dist_eq] using Metric.mem_ball'.mp hu
  intro a ha
  have ha0 : 0 ≤ a := ha.1
  have ha1 : a ≤ 1 := ha.2
  have hscale : ‖a • u‖ ≤ ‖u‖ := by
    rw [norm_smul]
    have habs : |a| ≤ 1 := abs_le.2 ⟨by linarith, ha1⟩
    calc
      ‖a‖ * ‖u‖ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
      _ = ‖u‖ := one_mul _
  have hur : u ∈ Metric.ball (0 : E) εr := by
    apply Metric.mem_ball'.mpr
    simpa [dist_comm] using lt_of_lt_of_le hunorm (min_le_left _ _)
  have hual : a • u ∈ Metric.ball (0 : E) εl := by
    apply Metric.mem_ball'.mpr
    simpa [dist_comm] using
      lt_of_le_of_lt hscale (lt_of_lt_of_le hunorm (min_le_right _ _))
  have hrad := hrball hur a ha (1 : ℝ) ⟨by norm_num, by norm_num⟩
  have hradfst : (Φ (z, a • u) 1).1 = (Φ (z, u) a).1 := by
    simpa using congrArg Prod.fst hrad
  have hleft' := hlball hual
  change ψ ((Φ (z, a • u) 1).1) = a • u at hleft'
  rw [hradfst] at hleft'
  exact hleft'

/-- Backward-compatible local endpoint inverse, obtained by forgetting the
radial-flow component of the stronger normal-coordinate package. -/
theorem exists_localInverse_coordinateGeodesic_endpoint_map_zero_velocity
    {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ∃ G : E × E → E × E, ∃ Φ : (E × E) → ℝ → E × E, ∃ ψ : E → E,
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
        G =ᶠ[𝓝 (z, 0)]
          (fun q ↦ secondOrderSystem (coordinateAcceleration cov x₀ b) q) ∧
        (∀ q, Φ q 0 = q) ∧ (∀ q, IsIntegralCurve (Φ q) (fun _ ↦ G)) ∧
        ContDiff ℝ 1 (fun q ↦ Φ q 1) ∧
        (∀ t, Φ (z, 0) t = (z, 0)) ∧
        (∀ᶠ u in 𝓝 0, ∀ t ∈ Icc (-2 : ℝ) 2,
          (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
            G (Φ (z, u) t) =
              secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t)) ∧
        ContinuousAt ψ z ∧
        ψ z = 0 ∧
        (∀ᶠ u in 𝓝 0, ψ ((Φ (z, u) 1).1) = u) ∧
        (∀ᶠ y in 𝓝 z, (Φ (z, ψ y) 1).1 = y) := by
  obtain ⟨G, Φ, ψ, _, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix,
    hlocal, _, _, _, _, _, _, _, _, _, hψcont, _, _, hψzero, hleft, hright⟩ :=
    exists_localInverse_coordinateGeodesic_endpoint_map_zero_velocity_radial
      (I := I) (M := M) (E := E) cov x₀ b hz
  exact ⟨G, Φ, ψ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth, hfix,
    hlocal, hψcont, hψzero, hleft, hright⟩

/-- Every coordinate endpoint sufficiently close to the chart coordinate of
the base point is joined to it by an actual coordinate geodesic on the full
unit interval.  The returned object is a genuine
`LocalChartSecondOrderSolution`, not merely an orbit of the compactly
supported extension: the localization hypothesis supplies both the original
geodesic equation and target membership throughout `[-2, 2]`. -/
theorem exists_eventually_localChartSecondOrderSolution_endpoint :
    ∃ ψ : E → E, ∀ᶠ y in 𝓝 (extChartAt I x₀ x₀),
      ∃ sol : LocalChartSecondOrderSolution I
          (coordinateAcceleration cov x₀ b) x₀ (ψ y),
        sol.radius = 2 ∧ sol.coordinate 1 = y := by
  let z : E := extChartAt I x₀ x₀
  have hz : z ∈ (extChartAt I x₀).target := by
    exact mem_extChartAt_target x₀
  obtain ⟨G, Φ, ψ, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth,
    hfix, hlocal, hψcont, hψzero, hleft, hright⟩ :=
    exists_localInverse_coordinateGeodesic_endpoint_map_zero_velocity
      (I := I) (M := M) (E := E) cov x₀ b hz
  let P : E → Prop := fun u ↦ ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ (z, u) t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t)
  have hlocal' : ∀ᶠ u in 𝓝 0, P u := hlocal
  have hψtendsto : Tendsto ψ (𝓝 z) (𝓝 0) := by
    rw [← hψzero]
    exact hψcont.tendsto
  have hlocalψ' : ∀ᶠ y in 𝓝 z, P (ψ y) :=
    hψtendsto.eventually hlocal'
  have hlocalψ : ∀ᶠ y in 𝓝 z, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ (z, ψ y) t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ (z, ψ y) t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, ψ y) t) := by
    exact hlocalψ'
  refine ⟨ψ, ?_⟩
  change ∀ᶠ y in 𝓝 z, _
  filter_upwards [hlocalψ, hright] with y hlocalY hrightY
  let sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ (ψ y) :=
    { coordinate := fun t ↦ (Φ (z, ψ y) t).1
      velocity := fun t ↦ (Φ (z, ψ y) t).2
      radius := 2
      radius_pos := by norm_num
      coordinate_initial := by
        have hzero := hΦzero (z, ψ y)
        change (Φ (z, ψ y) 0).1 = extChartAt I x₀ x₀
        rw [hzero]
      velocity_initial := by
        have hzero := hΦzero (z, ψ y)
        change (Φ (z, ψ y) 0).2 = ψ y
        rw [hzero]
      coordinate_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hstate := hΦcurve (z, ψ y) t
        change HasDerivAt (Φ (z, ψ y)) (G (Φ (z, ψ y) t)) t at hstate
        rw [(hlocalY t htI).2] at hstate
        simpa [secondOrderSystem] using hstate.hasFDerivAt.fst.hasDerivAt
      velocity_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hstate := hΦcurve (z, ψ y) t
        change HasDerivAt (Φ (z, ψ y)) (G (Φ (z, ψ y) t)) t at hstate
        rw [(hlocalY t htI).2] at hstate
        simpa [secondOrderSystem] using hstate.hasFDerivAt.snd.hasDerivAt
      coordinate_mem_target := by
        intro t ht
        exact (hlocalY t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).1 }
  exact ⟨sol, rfl, hrightY⟩

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1] in
/-- On an actual radial normal-coordinate geodesic, the derivative of the
coordinate inverse sends the geodesic velocity back to its initial coordinate
velocity.  The proof uses the open `C¹` inverse domain and the exact radial
identity; it is a radial differential identity, not a transverse Gauss-lemma
or local-minimization statement. -/
theorem fderiv_coordinateInverse_apply_velocity_eq_initial_of_radial
    (ψ : E → E) (V : Set E) (hVopen : IsOpen V)
    (hψon : ContDiffOn ℝ 1 ψ V) {u : E}
    (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u)
    (hradius : 1 < sol.radius)
    (hVpath : ∀ a ∈ Icc (0 : ℝ) 1, sol.coordinate a ∈ V)
    (hradial : ∀ a ∈ Icc (0 : ℝ) 1,
      ψ (sol.coordinate a) = a • u)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    fderiv ℝ ψ (sol.coordinate a) (sol.velocity a) = u := by
  have haI : a ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [ha.1, ha.2, hradius]
  have hcoord := sol.coordinate_hasDeriv a haI
  have hψat : ContDiffAt ℝ 1 ψ (sol.coordinate a) :=
    hψon.contDiffAt (hVopen.mem_nhds
      (hVpath a ⟨le_of_lt ha.1, le_of_lt ha.2⟩))
  have hψderiv : HasFDerivAt ψ (fderiv ℝ ψ (sol.coordinate a))
      (sol.coordinate a) :=
    hψat.differentiableAt one_ne_zero |>.hasFDerivAt
  have hchain : HasDerivAt (fun s ↦ ψ (sol.coordinate s))
      (fderiv ℝ ψ (sol.coordinate a) (sol.velocity a)) a := by
    change HasDerivAt (ψ ∘ sol.coordinate)
      (fderiv ℝ ψ (sol.coordinate a) (sol.velocity a)) a
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      (hψderiv.comp a hcoord.hasFDerivAt).hasDerivAt
  have hlinear : HasDerivAt (fun s : ℝ ↦ s • u) u a := by
    simpa using (hasDerivAt_id' a).smul_const u
  have hrad : HasDerivAt (fun s ↦ ψ (sol.coordinate s)) u a := by
    apply hlinear.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with s hs
    exact hradial s ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  exact hchain.unique hrad

/-- A radial strengthening of the local normal-endpoint construction.  For
each endpoint in one chart neighbourhood, the returned actual coordinate
geodesic has a common local inverse `ψ` along the entire radial segment:
`ψ (sol.coordinate a) = a • ψ y` for `a ∈ [0,1]`.

This records the normal-coordinate radial identity required by a future
Gauss-lemma argument.  It does not make a local-minimization claim. -/
theorem exists_eventually_localChartSecondOrderSolution_endpoint_radial :
    ∃ ψ : E → E, ∃ V : Set E,
      IsOpen V ∧ extChartAt I x₀ x₀ ∈ V ∧ ContDiffOn ℝ 1 ψ V ∧
      (∀ y ∈ V, Function.Bijective (fderiv ℝ ψ y)) ∧
      ContDiffAt ℝ 1 ψ (extChartAt I x₀ x₀) ∧
      HasStrictFDerivAt ψ (ContinuousLinearMap.id ℝ E) (extChartAt I x₀ x₀) ∧
      ψ (extChartAt I x₀ x₀) = 0 ∧
      ∀ᶠ y in 𝓝 (extChartAt I x₀ x₀),
      y ∈ V ∧ ∃ sol : LocalChartSecondOrderSolution I
          (coordinateAcceleration cov x₀ b) x₀ (ψ y),
        sol.radius = 2 ∧ sol.coordinate 1 = y ∧
          (∀ a ∈ Icc (0 : ℝ) 1, sol.coordinate a ∈ V) ∧
          (∀ a ∈ Icc (0 : ℝ) 1, ψ (sol.coordinate a) = a • ψ y) ∧
          ∀ a ∈ Ioo (0 : ℝ) 1,
            fderiv ℝ ψ (sol.coordinate a) (sol.velocity a) = ψ y := by
  let z : E := extChartAt I x₀ x₀
  have hz : z ∈ (extChartAt I x₀).target := by
    exact mem_extChartAt_target x₀
  obtain ⟨G, Φ, ψ, V, hG, hGcompact, hGeq, hΦzero, hΦcurve, hΦsmooth,
    hfix, hlocal, hradial, hVopen, hzV, hψon, _, _, _, hψbij, hVradial, hψcont,
    hψsmooth, hψstrict, hψzero,
    hleft, hright⟩ :=
    exists_localInverse_coordinateGeodesic_endpoint_map_zero_velocity_radial
      (I := I) (M := M) (E := E) cov x₀ b hz
  let P : E → Prop := fun u ↦ ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ (z, u) t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ (z, u) t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, u) t)
  have hlocal' : ∀ᶠ u in 𝓝 0, P u := hlocal
  have hinverse' : ∀ᶠ u in 𝓝 (0 : E), ∀ a ∈ Icc (0 : ℝ) 1,
      ψ ((Φ (z, u) a).1) = a • u :=
    eventually_leftInverse_flow_radial Φ ψ hradial hleft
  have hψtendsto : Tendsto ψ (𝓝 z) (𝓝 0) := by
    rw [← hψzero]
    exact hψcont.tendsto
  have hlocalψ' : ∀ᶠ y in 𝓝 z, P (ψ y) :=
    hψtendsto.eventually hlocal'
  have hinverseψ' : ∀ᶠ y in 𝓝 z, ∀ a ∈ Icc (0 : ℝ) 1,
      ψ ((Φ (z, ψ y) a).1) = a • ψ y :=
    hψtendsto.eventually hinverse'
  have hVpathψ' : ∀ᶠ y in 𝓝 z, ∀ a ∈ Icc (0 : ℝ) 1,
      (Φ (z, ψ y) a).1 ∈ V :=
    hψtendsto.eventually hVradial
  have hlocalψ : ∀ᶠ y in 𝓝 z, ∀ t ∈ Icc (-2 : ℝ) 2,
      (Φ (z, ψ y) t).1 ∈ (extChartAt I x₀).target ∧
        G (Φ (z, ψ y) t) =
          secondOrderSystem (coordinateAcceleration cov x₀ b) (Φ (z, ψ y) t) := by
    exact hlocalψ'
  have hVnhds : ∀ᶠ y in 𝓝 z, y ∈ V := hVopen.mem_nhds hzV
  refine ⟨ψ, V, hVopen, hzV, hψon, hψbij, ?_, ?_, ?_, ?_⟩
  · simpa only [z] using hψsmooth
  · simpa only [z] using hψstrict
  · simpa only [z] using hψzero
  change ∀ᶠ y in 𝓝 z, _
  filter_upwards [hVnhds, hlocalψ, hinverseψ', hVpathψ', hright] with y hyV hlocalY hinverseY hVpathY hrightY
  let sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ (ψ y) :=
    { coordinate := fun t ↦ (Φ (z, ψ y) t).1
      velocity := fun t ↦ (Φ (z, ψ y) t).2
      radius := 2
      radius_pos := by norm_num
      coordinate_initial := by
        have hzero := hΦzero (z, ψ y)
        change (Φ (z, ψ y) 0).1 = extChartAt I x₀ x₀
        rw [hzero]
      velocity_initial := by
        have hzero := hΦzero (z, ψ y)
        change (Φ (z, ψ y) 0).2 = ψ y
        rw [hzero]
      coordinate_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hstate := hΦcurve (z, ψ y) t
        change HasDerivAt (Φ (z, ψ y)) (G (Φ (z, ψ y) t)) t at hstate
        rw [(hlocalY t htI).2] at hstate
        simpa [secondOrderSystem] using hstate.hasFDerivAt.fst.hasDerivAt
      velocity_hasDeriv := by
        intro t ht
        have htI : t ∈ Icc (-2 : ℝ) 2 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        have hstate := hΦcurve (z, ψ y) t
        change HasDerivAt (Φ (z, ψ y)) (G (Φ (z, ψ y) t)) t at hstate
        rw [(hlocalY t htI).2] at hstate
        simpa [secondOrderSystem] using hstate.hasFDerivAt.snd.hasDerivAt
      coordinate_mem_target := by
        intro t ht
        exact (hlocalY t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).1 }
  refine ⟨hyV, sol, rfl, hrightY, ?_, ?_, ?_⟩
  · intro a ha
    change (Φ (z, ψ y) a).1 ∈ V
    exact hVpathY a ha
  intro a ha
  change ψ ((Φ (z, ψ y) a).1) = a • ψ y
  exact hinverseY a ha
  intro a ha
  exact fderiv_coordinateInverse_apply_velocity_eq_initial_of_radial
    (I := I) (M := M) (E := E) cov x₀ b ψ V hVopen hψon sol
    (by norm_num) hVpathY hinverseY ha

end LocalGeodesicData

end BonnetMyersEntry
