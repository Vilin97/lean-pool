/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalMetricLimit

/-! # Chain rules for rays in a normal coordinate map -/

@[expose] public noncomputable section
open scoped Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The time velocity of a ray in a differentiable normal map. -/
theorem hasDerivAt_normal_ray {F : E → E} {u : E} {s : ℝ}
    (hF : DifferentiableAt ℝ F (s • u)) :
    HasDerivAt (fun r : ℝ => F (r • u)) (fderiv ℝ F (s • u) u) s := by
  have hi : HasDerivAt (fun r : ℝ => r • u) u s := by
    convert (hasDerivAt_id s).smul_const u using 1 <;> simp
  exact hF.hasFDerivAt.comp_hasDerivAt s hi

/-- Spatial variations of the ray family carry one factor of the ray parameter. -/
theorem fderiv_normal_ray_spatial {F : E → E} {u : E} {s : ℝ}
    (hF : DifferentiableAt ℝ F (s • u)) (w : E) :
    fderiv ℝ (fun p : E × ℝ => F (p.2 • p.1)) (u, s) (w, 0) =
      s • fderiv ℝ F (s • u) w := by
  have hi := (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, s))).smul
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, s)))
  have hd := hF.hasFDerivAt.comp (u, s) hi
  have he := congrArg (fun L : E × ℝ →L[ℝ] E => L (w, 0)) hd.fderiv
  simpa [Function.comp_def] using he

/-- The metric of spatial ray variations is parameter squared times the
normal-map pullback metric. This includes zero parameter. -/
theorem normal_ray_spatial_metric {F : E → E}
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) {u : E} {s : ℝ}
    (hF : DifferentiableAt ℝ F (s • u)) (w v : E) :
    g (F (s • u))
      (fderiv ℝ (fun p : E × ℝ => F (p.2 • p.1)) (u, s) (w, 0))
      (fderiv ℝ (fun p : E × ℝ => F (p.2 • p.1)) (u, s) (v, 0)) =
    s ^ 2 * g (F (s • u)) (fderiv ℝ F (s • u) w) (fderiv ℝ F (s • u) v) := by
  rw [fderiv_normal_ray_spatial hF, fderiv_normal_ray_spatial hF]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- A radial derivative identity becomes the constant-speed ray equation
after cancelling the nonzero ray parameter. -/
theorem hasDerivAt_normal_ray_of_radial {F : E → E} {u N : E} {s σ : ℝ}
    (hF : DifferentiableAt ℝ F (s • u)) (hs : s ≠ 0)
    (hrad : fderiv ℝ F (s • u) (s • u) = (s * σ) • N) :
    HasDerivAt (fun r : ℝ => F (r • u)) (σ • N) s := by
  have he : fderiv ℝ F (s • u) u = σ • N := by
    apply (smul_right_injective E hs)
    simpa only [map_smul, mul_smul] using hrad
  simpa only [he] using hasDerivAt_normal_ray hF

/-- An open initial-data neighborhood contains a short positive-phase ray
interval whenever curvature, endpoint time, and initial energy are positive. -/
theorem exists_positive_phase_ray_interval
    (g : E →L[ℝ] E →L[ℝ] ℝ) {V : Set (E × E)} (hV : IsOpen V)
    {z u : E} (hz : (z, (0 : E)) ∈ V) {K t : ℝ}
    (hK : 0 < K) (ht : 0 < t) (hu : 0 < g u u) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ Set.Ioo 0 ε, (z, r • u) ∈ V ∧
      Real.sqrt (K * g (r • u) (r • u)) * t ∈ Set.Ioo 0 Real.pi := by
  have hc : Continuous (fun r : ℝ => (z, r • u)) :=
    continuous_const.prodMk (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), (z, r • u) ∈ V := by
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV.mem_nhds hz)
  let freq := Real.sqrt K * (t * Real.sqrt (g u u))
  have hfreq : 0 < freq := mul_pos (Real.sqrt_pos.mpr hK)
    (mul_pos ht (Real.sqrt_pos.mpr hu))
  have hupper : ∀ᶠ r in 𝓝 (0 : ℝ), freq * r < Real.pi := by
    exact (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
      (isOpen_Iio.mem_nhds (by simpa using Real.pi_pos))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp (hnear.and hupper)
  refine ⟨ε, hε, ?_⟩
  intro r hr
  have hd : dist r 0 < ε := by simpa [Real.dist_eq, abs_of_pos hr.1] using hr.2
  have hh := he hd
  refine ⟨hh.1, ?_⟩
  have hquad : g (r • u) (r • u) = r ^ 2 * g u u := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hphase : Real.sqrt (K * g (r • u) (r • u)) * t = freq * r := by
    rw [Real.sqrt_mul hK.le, hquad, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.1.le]
    dsimp only [freq]
    ring
  rw [hphase]
  exact ⟨mul_pos hfreq hr.1, hh.2⟩

/-- A single initial-velocity ball supports positive phases for every
nonzero direction and every ray parameter between zero and two. This gives
a uniform neighborhood, rather than a radius chosen separately for each ray. -/
theorem exists_uniform_positive_phase_ray_ball
    (g : E →L[ℝ] E →L[ℝ] ℝ) (hg : ∀ u : E, u ≠ 0 → 0 < g u u)
    {V : Set (E × E)} (hV : IsOpen V) {z : E} (hz : (z, (0 : E)) ∈ V)
    {K t : ℝ} (hK : 0 < K) (ht : 0 < t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : E, ‖u‖ < ε → u ≠ 0 →
      ∀ r ∈ Set.Ioo (0 : ℝ) 2, (z, r • u) ∈ V ∧
        Real.sqrt (K * g (r • u) (r • u)) * t ∈ Set.Ioo 0 Real.pi := by
  have hnear : ∀ᶠ u in 𝓝 (0 : E), (z, u) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hz)
  have hgc : Continuous (fun u : E => g u u) := g.continuous.clm_apply continuous_id
  have hpc : Continuous (fun u : E => Real.sqrt (K * g u u) * t) :=
    (Real.continuous_sqrt.comp (continuous_const.mul hgc)).mul continuous_const
  have hupper : ∀ᶠ u in 𝓝 (0 : E), Real.sqrt (K * g u u) * t < Real.pi :=
    hpc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds (by simpa using Real.pi_pos))
  obtain ⟨R, hR, he⟩ := Metric.eventually_nhds_iff.mp (hnear.and hupper)
  refine ⟨R / 2, by positivity, ?_⟩
  intro u hu hune r hr
  have hn : ‖r • u‖ < R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
    nlinarith [norm_nonneg u, hr.1, hr.2]
  have hd : dist (r • u) 0 < R := by simpa only [dist_zero_right] using hn
  have hh := he hd
  refine ⟨hh.1, ?_, hh.2⟩
  exact mul_pos (Real.sqrt_pos.mpr (mul_pos hK (hg _ (smul_ne_zero hr.1.ne' hune)))) ht

end LichnerowiczObata
