/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.WholeSpaceComparisonClosure
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.PressureFlux
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.CompactComparisonBounds

@[expose] public section

/-!
# Whole-space finite-energy comparison

The reference velocity has one compact spatial support throughout the closed
time interval. The competing velocity has only smoothness and a uniform
finite-energy bound. No growth, decay, support or derivative bound is assumed
for the competing pressure or velocity. The pressure flux estimate is derived
from the actual equation by the imported pressure recovery and commutator
theorems.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace NavierStokesR3.WholeSpaceUniqueness

open ProblemStatement Comparison
open NavierStokes.ProblemStatement (spatialDivergence)
open NavierStokes.PeriodicUniqueness (spatial_smooth)

/-- Whole-space comparison on a positive closed time interval. Finite energy
of the reference velocity is a consequence of its compact spatial support. -/
theorem classical_uniqueness_on_Icc {T : ℝ} (hT : 0 < T)
    {u v : VelocityField} {p q : PressureField} {K : Set Space}
    (hu : ContDiffOn ℝ ∞ u (Comparison.slab 0 T))
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hp : ContDiffOn ℝ ∞ p (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hK : IsCompact K)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) T, tsupport (fun x => u (t, x)) ⊆ K)
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdu : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
      navierStokesResidual 1 u p t x = navierStokesResidual 1 v q t x)
    (hzero : ∀ x, u (0, x) = v (0, x)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  have heu := CompactComparisonBounds.uniformFiniteEnergy_of_compact_slab hu hK hsupp
  let H : PressureRecovery.Hypotheses T u v p q :=
    ⟨hT, hu, hv, hp, hq, hdu, hdv, (fun t ht x => by simpa using hNS t ht x), heu, hev⟩
  have hum : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => u (t, x)) volume :=
    fun t ht => (spatial_smooth hu ht).continuous.aestronglyMeasurable
  have hvm : ∀ t ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun x => v (t, x)) volume :=
    fun t ht => (spatial_smooth hv ht).continuous.aestronglyMeasurable
  have hew := uniformFiniteEnergy_sub hum hvm heu hev
  obtain ⟨M, hM0, hM⟩ := uniformFiniteEnergy_lpNorm_two_bound
    (fun t ht => (hum t ht).sub (hvm t ht)) hew
  obtain ⟨U, hU0, hU⟩ := CompactComparisonBounds.exists_lpNorm_three_bound
    hu.continuousOn hK hsupp
  obtain ⟨G₀, hG₀, hTensor⟩ := uniformFiniteEnergy_tensorDiff_lpNorm_one_bound hum hvm heu hev
  obtain ⟨CP, hCP, hpressure⟩ := PressureFlux.exists_uniform_actual_pressure_flux_bound
    H M U G₀ hM0 hU0 hG₀ hM hU hTensor
  obtain ⟨G, hG0, hG⟩ := CompactComparisonBounds.exists_gradient_bound hT hu hK hsupp
  obtain ⟨R₀, _hR₀, hvanish⟩ := CompactComparisonBounds.exists_radius_weight_derivative_zero hK
    hsupp
  apply WholeSpaceComparisonClosure.eq_of_pressure_flux_bound
    hT.le hM0 hG0 hCP hu hv hp hq
    (fun t ht => (hM t ht).1) (fun t ht => (hM t ht).2) hG hdu hdv hNS hzero hvanish
  intro R hR t ht
  simpa only [WholeSpaceComparisonClosure.pressureEnvelope, neg_div] using hpressure R hR t ht

/-- The exact compact candidate agrees with every smooth finite-energy
competitor on each closed interval before time one. -/
theorem candidate_unique_on_Icc {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties 1 u p f K)
    {T : ℝ} (hT : T < 1) {v : VelocityField} {q : PressureField}
    (hv : ContDiffOn ℝ ∞ v (Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Comparison.slab 0 T))
    (hev : UniformFiniteEnergy (Icc (0 : ℝ) T) v)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual 1 v q t x = f (t, x))
    (hvzero : ∀ x, v (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  by_cases hT0 : 0 < T
  · have hsub : Comparison.slab 0 T ⊆ preSingularDomain := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩
    apply classical_uniqueness_on_Icc hT0 (h.velocity_smooth.mono hsub) hv
      (h.pressure_smooth.mono hsub) hq h.support_compact
    · intro t ht
      exact h.velocity_support t ⟨ht.1, ht.2.trans_lt hT⟩
    · exact hev
    · intro t ht x
      exact h.divergence_free t ⟨ht.1.le, ht.2.trans hT⟩ x
    · exact hdv
    · intro t ht x
      exact (h.navier_stokes t ⟨ht.1, ht.2.trans hT⟩ x).trans (hNSv t ht x).symm
    · intro x
      exact (h.zero_initial_velocity x).trans (hvzero x).symm
  · intro t ht x
    have ht0 : t = 0 := le_antisymm (ht.2.trans (le_of_not_gt hT0)) ht.1
    rw [ht0, h.zero_initial_velocity, hvzero]

/-- A global smooth solution with uniformly finite kinetic energy must agree
with the candidate at every time strictly before one. -/
theorem candidate_global_agrees_before_one {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space} (h : CandidateProperties 1 u p f K)
    (v : GlobalFiniteEnergySolution 1 f) :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x, u (t, x) = v.velocity (t, x) := by
  intro t ht
  have hsub : Comparison.slab 0 t ⊆ futureDomain := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  have he := v.energy_bounded.mono (show Icc (0 : ℝ) t ⊆ Ici 0 from fun _ hs => hs.1)
  exact candidate_unique_on_Icc h ht.2 (v.velocity_smooth.mono hsub)
    (v.pressure_smooth.mono hsub) he
    (fun s hs => v.divergence_free s hs.1.le)
    (fun s hs => v.navier_stokes s hs.1)
    v.zero_initial_velocity t ⟨ht.1, le_rfl⟩

end NavierStokesR3.WholeSpaceUniqueness
