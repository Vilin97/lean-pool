/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MaximalLifespan
public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicSobolev
public import LeanPool.NavierStokesAndEuler.NavierStokes.CompactForceDecay
public import LeanPool.NavierStokesAndEuler.NavierStokes.CandidateFromLimits
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedPeriodicAssembly

@[expose] public section

/-!
# Consequences of the actual candidate fields

No candidate existence is asserted here.  The first results use precisely
`CandidateProperties`.  Force derivatives at initial time are taken within the
physical future half-space.  For the actual globally smooth constructed force
these are proved equal to its ordinary full derivatives.
-/

noncomputable section

namespace NavierStokes.CandidateConsequences

open Set Filter Function ProblemStatement
open scoped ContDiff Topology BigOperators Pointwise

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m).le

theorem future_uniqueDiff : UniqueDiffOn ℝ futureDomain :=
  (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

/-- The physical full spacetime jet, including its one-sided value at time zero. -/
noncomputable def futureJet (f : VelocityField) (m : ℕ) :=
  iteratedFDerivWithin ℝ m f futureDomain

theorem futureJet_continuous {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) (m : ℕ) :
    ContinuousOn (futureJet f m) futureDomain :=
  hf.continuousOn_iteratedFDerivWithin (nat_le_infty m) future_uniqueDiff

private theorem future_spatial_translate (e : Space) :
    ((0, e) : SpaceTime) +ᵥ futureDomain = futureDomain := by
  ext z
  change z ∈ (fun w : SpaceTime => (0, e) + w) '' futureDomain ↔ z ∈ futureDomain
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [futureDomain, mem_prod, mem_Ici, mem_univ, and_true,
      Prod.fst_add, Prod.fst_zero, zero_add] using hw
  · intro hz
    refine ⟨z - (0, e), ?_, ?_⟩
    · simpa only [futureDomain, mem_prod, mem_Ici, mem_univ, and_true,
        Prod.fst_sub, sub_zero] using hz
    · simpa only [add_comm] using sub_add_cancel z ((0, e) : SpaceTime)

theorem futureJet_periodic {f : VelocityField}
    (hp : UnitSpatialPeriodsOn (Ici (0 : ℝ)) f) (m : ℕ) :
    UnitSpatialPeriodsOn (Ici (0 : ℝ)) (futureJet f m) := by
  intro t ht x i
  have he : EqOn (fun z : SpaceTime => f (z + (0, coordinateVector i))) f futureDomain := by
    rintro ⟨s,y⟩ hz
    simpa only [Prod.mk_add_mk, add_zero] using hp s hz.1 y i
  have hc := iteratedFDerivWithin_congr (𝕜 := ℝ) he (show (t, x) ∈ futureDomain from ⟨ht, mem_univ
    _⟩) m
  have hs := iteratedFDerivWithin_comp_add_right (𝕜 := ℝ) (f := f)
    (s := futureDomain) m (0, coordinateVector i) (t, x)
  rw [future_spatial_translate] at hs
  simpa only [futureJet, Prod.mk_add_mk, add_zero] using hs.symm.trans hc

theorem futureJet_eq_full {f : VelocityField} {t : ℝ} (ht : 0 ≤ t) (x : Space)
    (m : ℕ) (hf : ContDiffAt ℝ ∞ f (t, x)) :
    futureJet f m (t, x) = iteratedFDeriv ℝ m f (t, x) :=
  iteratedFDerivWithin_eq_iteratedFDeriv future_uniqueDiff (hf.of_le (nat_le_infty m))
    ⟨ht, mem_univ _⟩

theorem futureJet_eq_full_of_pos {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) {t : ℝ} (ht : 0 < t) (x : Space) (m : ℕ) :
    futureJet f m (t, x) = iteratedFDeriv ℝ m f (t, x) :=
  futureJet_eq_full ht.le x m
    (hf.contDiffAt (prod_mem_nhds (Ici_mem_nhds ht) univ_mem))

/-- Compact future time support gives arbitrary polynomial decay of the
physical one-sided jets, using only future smoothness and future periodicity. -/
theorem futureJet_decay {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain)
    (hp : UnitSpatialPeriodsOn (Ici (0 : ℝ)) f) (hs : CompactFutureTimeSupport f)
    (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖futureJet f m (t, x)‖ ≤ C * (1 + t) ^ (-K) := by
  obtain ⟨T, hT, hzero⟩ := hs
  obtain ⟨M, hM, hb⟩ := MaximalLifespan.periodic_bound_on_slab
    ((futureJet_continuous hf m).mono
      (show Icc (0 : ℝ) (T + 1) ×ˢ (univ : Set Space) ⊆ futureDomain from
        fun _ hz => ⟨hz.1.1, hz.2⟩))
    (fun t ht x i => futureJet_periodic hp m t ht.1 x i)
  let C : ℝ := M * (1 + (T + 1)) ^ K
  have hbase : 0 < 1 + (T + 1) := by linarith
  have hC : 0 < C := mul_pos hM (Real.rpow_pos_of_pos hbase K)
  refine ⟨C, hC, ?_⟩
  intro t ht x
  by_cases hsmall : t ≤ T + 1
  · have hpow : (1 + (T + 1)) ^ (-K) ≤ (1 + t) ^ (-K) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (neg_nonpos.mpr hK)
    have hcancel : C * (1 + (T + 1)) ^ (-K) = M := by
      dsimp [C]
      rw [mul_assoc, ← Real.rpow_add hbase]
      simp
    calc
      ‖futureJet f m (t, x)‖ ≤ M := hb t ⟨ht, hsmall⟩ x
      _ = C * (1 + (T + 1)) ^ (-K) := hcancel.symm
      _ ≤ C * (1 + t) ^ (-K) := mul_le_mul_of_nonneg_left hpow hC.le
  · have htpos : 0 < t := by linarith
    rw [futureJet_eq_full_of_pos hf htpos x m,
      CompactForceDecay.iteratedFDeriv_eq_zero_after hzero m (by linarith : T < t) x, norm_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _)

/-- The ordinary tensor bound for the same force.  Global smoothness is
provided by the actual force constructor; negative-time periodicity is not needed. -/
theorem full_forceJet_decay {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (hf : ContDiff ℝ ∞ f) (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDeriv ℝ m f (t, x)‖ ≤ C * (1 + t) ^ (-K) := by
  obtain ⟨C, hC, hb⟩ := futureJet_decay h.force_smooth h.force_periodic h.force_time_support m K hK
  refine ⟨C, hC, ?_⟩
  intro t ht x
  rw [← futureJet_eq_full ht x m hf.contDiffAt]
  exact hb t ht x

theorem full_forceMixed_decay {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (hf : ContDiff ℝ ∞ f) (m : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
        |(iteratedFDeriv ℝ m f (t, x)
          (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
            C * (1 + t) ^ (-K) := by
  obtain ⟨C, hC, hb⟩ := full_forceJet_decay h hf m K hK
  exact ⟨C, hC, fun t ht x directions j =>
    (CompactForceDecay.mixed_component_le_full f m (t, x) directions j).trans (hb t ht x)⟩

/-- All conclusions here follow from the exact candidate properties alone. -/
structure Consequences (u : VelocityField) (p : PressureField) (f : VelocityField) : Prop where
  maximal : MaximalLifespan.IsMaximalClassicalSolution f (fun _ => 0) 1 u p
  lifespans : MaximalLifespan.admissibleLifespans f (fun _ => 0) = Ioc (0 : ℝ) 1
  h3_unbounded : PeriodicSobolev.DerivativeH3UnboundedAtOne u
  force_nonzero : ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : Space, f (t, x) ≠ 0
  force_jet_decay : ∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ‖futureJet f m (t, x)‖ ≤ C * (1 + t) ^ (-K)

theorem consequences_of_candidate {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) : Consequences u p f :=
  ⟨MaximalLifespan.candidate_is_maximal h, MaximalLifespan.candidate_admissible_lifespans h,
    PeriodicSobolev.candidate_derivativeH3_unbounded h,
    MaximalLifespan.candidate_force_nonzero_before_one h,
    futureJet_decay h.force_smooth h.force_periodic h.force_time_support⟩

/-- Retaining one growing physical trajectory strengthens unboundedness to
a genuine limit.  No monotonicity of the velocity or its norm is assumed. -/
theorem h3_tendsto_of_speed_tendsto {u : VelocityField} {p : PressureField} {f : VelocityField}
    (h : CandidateProperties u p f) (x : ℝ → Space)
    (hx : Tendsto (fun t => ‖u (t, x t)‖) (𝓝[<] (1 : ℝ)) atTop) :
    Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun y => u (t, y)))
      (𝓝[<] (1 : ℝ)) atTop := by
  rw [tendsto_atTop]
  intro M
  have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
  have hpre : ∀ᶠ t in 𝓝[<] (1 : ℝ), t < 1 := self_mem_nhdsWithin
  filter_upwards [hx.eventually (eventually_ge_atTop (3 * M)), hpos, hpre] with t hlarge ht ht1
  have hslice := TimeLocalization.spatial_smooth_including_initial u h.velocity_smooth t ⟨ht.le,
    ht1⟩
  have hb := PeriodicSobolev.norm_le_three_derivativeH3Norm hslice
    (h.velocity_periodic t ⟨ht.le, ht1⟩) (x t)
  linarith

theorem mixed_activated_speed_tendsto {A v : VelocityField}
    (haxis : Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖)
      (𝓝[<] (1 : ℝ)) atTop) :
    Tendsto (fun t : ℝ => ‖TimeLocalization.activatedVelocity
      (MixedPeriodicAssembly.periodicVelocity A v) (t, 0)‖) (𝓝[<] (1 : ℝ)) atTop := by
  have he : (fun t : ℝ => ‖TimeLocalization.activatedVelocity
      (MixedPeriodicAssembly.periodicVelocity A v) (t, 0)‖) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖) := by
    filter_upwards [show Ioi (3 / 4 : ℝ) ∈ 𝓝[<] (1 : ℝ) from
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))] with t ht
    rw [TimeLocalization.activatedVelocity_eq_late _ ht.le,
      MixedPeriodicAssembly.periodicVelocity_origin]
  exact haxis.congr' he.symm

/-- The exact mixed assembly inputs produce one force carrying all the
lifespan, Sobolev, and full force-jet conclusions.  Nothing is assumed about
the output force, the infinite-time PDE, or the Sobolev embedding. -/
theorem mixed_exists_force_with_consequences {A v : VelocityField} {p : PressureField}
    (hA : ContDiffOn ℝ ∞ A (SpacetimeEndpoint.openPast 1))
    (hv : ContDiffOn ℝ ∞ v (SpacetimeEndpoint.openPast 1))
    (hp : ContDiffOn ℝ ∞ p (SpacetimeEndpoint.openPast 1))
    (hd : ∀ t < 1, ∀ x, spatialDivergence (SpatialLocalization.cutPotential v) t x = 0)
    (hz : JointResidualLimits.VanishingJointJets (MixedPeriodicAssembly.originalResidual A v p))
    (eA : JointResidualLimits.AwayExtensions A)
    (ev : JointResidualLimits.AwayExtensions v)
    (ep : JointResidualLimits.AwayExtensions p)
    (haxis : Tendsto (fun t : ℝ => ‖MixedPeriodicAssembly.velocity A v (t, 0)‖)
      (𝓝[<] (1 : ℝ)) atTop) :
    ∃ F : VelocityField,
      CandidateProperties (TimeLocalization.activatedVelocity
        (MixedPeriodicAssembly.periodicVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      ContDiff ℝ ∞ F ∧
      Consequences (TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity A v))
        (TimeLocalization.activatedPressure (SpatialLocalization.periodicPressure p)) F ∧
      Tendsto (fun t => PeriodicSobolev.derivativeH3Norm (fun x =>
        TimeLocalization.activatedVelocity (MixedPeriodicAssembly.periodicVelocity A v) (t, x)))
        (𝓝[<] (1 : ℝ)) atTop ∧
      (∀ m : ℕ, ∀ K : ℝ, 0 ≤ K → ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x : Space, ∀ directions : Fin m → Fin 4, ∀ j : Fin 3,
          |(iteratedFDeriv ℝ m F (t, x)
            (fun i => CompactForceDecay.spacetimeCoordinate (directions i))) j| ≤
              C * (1 + t) ^ (-K)) ∧
      (∀ n : ℕ, ∀ x : Space, iteratedFDeriv ℝ n F (1, x) =
        MixedPeriodicAssembly.boundaryLimits A v p eA ev ep x n) := by
  obtain ⟨F, hc, hF, hjet⟩ := MixedPeriodicAssembly.exists_candidate_force hA hv hp hd hz eA ev ep
    haxis
  exact ⟨F, hc, hF, consequences_of_candidate hc,
    h3_tendsto_of_speed_tendsto hc (fun _ => 0) (mixed_activated_speed_tendsto haxis),
    full_forceMixed_decay hc hF, hjet⟩

end NavierStokes.CandidateConsequences
