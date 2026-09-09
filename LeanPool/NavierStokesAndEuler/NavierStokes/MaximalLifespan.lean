/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodicUniqueness

@[expose] public section

/-!
# Conditional maximal classical lifespan of the candidate

An actual `CandidateProperties` witness has maximal classical lifespan one.
The proof uses the proved periodic uniqueness theorem and a compactness bound
for a continuous periodic field across time one. It assumes no general
Navier--Stokes existence theorem and never identifies pressure gauges.
-/

noncomputable section

open Set
open scoped Topology ContDiff

namespace NavierStokes.MaximalLifespan

open ProblemStatement PeriodicIntegration

noncomputable def lifespanDomain (T : ℝ) : Set SpaceTime := Ico 0 T ×ˢ univ

/-- A finite, positive classical lifespan for the exact viscosity-one PDE.
The initial datum is an actual spatial velocity field. Pressures are retained
as witnesses but are never required to agree with a different gauge. -/
structure ClassicalSolution (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) (p : PressureField) : Prop where
  lifespan_pos : 0 < T
  velocity_smooth : ContDiffOn ℝ ∞ u (lifespanDomain T)
  pressure_smooth : ContDiffOn ℝ ∞ p (lifespanDomain T)
  velocity_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) u
  pressure_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) T) p
  initial_velocity : ∀ x : Space, u (0, x) = initial x
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, spatialDivergence u t x = 0
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    navierStokesResidual u p t x = f (t, x)

noncomputable def VelocityAgreesOn (T : ℝ) (u v : VelocityField) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = v (t, x)

/-- An extension has a strictly larger time interval and preserves the
velocity on the entire original interval. Its pressure may have a different
time-dependent spatially constant normalization. -/
noncomputable def HasClassicalExtension (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) : Prop :=
  ∃ S : ℝ, ∃ v : VelocityField, ∃ q : PressureField,
    T < S ∧ ClassicalSolution f initial S v q ∧ VelocityAgreesOn T u v

noncomputable def IsMaximalClassicalSolution (f : VelocityField) (initial : Space → Space)
    (T : ℝ) (u : VelocityField) (p : PressureField) : Prop :=
  ClassicalSolution f initial T u p ∧ ¬HasClassicalExtension f initial T u

/-- The actual set of finite positive times supported by classical solutions
for the fixed force and initial datum. No existence is built into the definition. -/
noncomputable def admissibleLifespans (f : VelocityField) (initial : Space → Space) : Set ℝ :=
  {T | ∃ u : VelocityField, ∃ p : PressureField, ClassicalSolution f initial T u p}

theorem ClassicalSolution.restrict {f : VelocityField} {initial : Space → Space}
    {S T : ℝ} {u : VelocityField} {p : PressureField}
    (h : ClassicalSolution f initial T u p) (hS : 0 < S) (hST : S ≤ T) :
    ClassicalSolution f initial S u p := by
  have hsub : lifespanDomain S ⊆ lifespanDomain T := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_le hST⟩, hz.2⟩
  refine ⟨hS, h.velocity_smooth.mono hsub, h.pressure_smooth.mono hsub, ?_, ?_,
    h.initial_velocity, ?_, ?_⟩
  · intro t ht x i
    exact h.velocity_periodic t ⟨ht.1, ht.2.trans_le hST⟩ x i
  · intro t ht x i
    exact h.pressure_periodic t ⟨ht.1, ht.2.trans_le hST⟩ x i
  · intro t ht x
    exact h.divergence_free t ⟨ht.1, ht.2.trans_le hST⟩ x
  · intro t ht x
    exact h.navier_stokes t ⟨ht.1, ht.2.trans_le hST⟩ x

/-- Any two actual classical solutions agree on their common interval.
This is derived by restriction to each compact subinterval and the proved
energy uniqueness theorem. Only velocity equality is asserted. -/
theorem ClassicalSolution.agree_on_overlap {f : VelocityField} {initial : Space → Space}
    {T S : ℝ} {u v : VelocityField} {p q : PressureField}
    (hu : ClassicalSolution f initial T u p) (hv : ClassicalSolution f initial S v q) :
    VelocityAgreesOn (min T S) u v := by
  intro t ht x
  have htT : t < T := (lt_min_iff.mp ht.2).1
  have htS : t < S := (lt_min_iff.mp ht.2).2
  have hsubT : PeriodicUniqueness.slab 0 t ⊆ lifespanDomain T := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt htT⟩, hz.2⟩
  have hsubS : PeriodicUniqueness.slab 0 t ⊆ lifespanDomain S := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt htS⟩, hz.2⟩
  have hcompact : ∀ r ∈ Icc (0 : ℝ) t, ∀ y : Space, u (r, y) = v (r, y) := by
    apply PeriodicUniqueness.classical_uniqueness_on_Icc
      (hu.velocity_smooth.mono hsubT) (hv.velocity_smooth.mono hsubS)
      (hu.pressure_smooth.mono hsubT) (hv.pressure_smooth.mono hsubS)
    · intro r hr y i
      exact hu.velocity_periodic r ⟨hr.1, hr.2.trans_lt htT⟩ y i
    · intro r hr y i
      exact hv.velocity_periodic r ⟨hr.1, hr.2.trans_lt htS⟩ y i
    · intro r hr y i
      exact hu.pressure_periodic r ⟨hr.1, hr.2.trans_lt htT⟩ y i
    · intro r hr y i
      exact hv.pressure_periodic r ⟨hr.1, hr.2.trans_lt htS⟩ y i
    · intro r hr y
      exact hu.divergence_free r ⟨hr.1.le, hr.2.trans htT⟩ y
    · intro r hr y
      exact hv.divergence_free r ⟨hr.1.le, hr.2.trans htS⟩ y
    · intro r hr y
      exact hu.navier_stokes r ⟨hr.1, hr.2.trans htT⟩ y
    · intro r hr y
      exact hv.navier_stokes r ⟨hr.1, hr.2.trans htS⟩ y
    · intro y
      exact (hu.initial_velocity y).trans (hv.initial_velocity y).symm
  exact hcompact t ⟨ht.1, le_rfl⟩ x

theorem candidate_is_classical_solution {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    ClassicalSolution f (fun _ => 0) 1 u p :=
  ⟨zero_lt_one, h.velocity_smooth, h.pressure_smooth, h.velocity_periodic,
    h.pressure_periodic, h.zero_initial_velocity, h.divergence_free, h.navier_stokes⟩

theorem candidate_agree_on_overlap {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : ClassicalSolution f (fun _ => 0) T v q) :
    VelocityAgreesOn (min T 1) v u :=
  hv.agree_on_overlap (candidate_is_classical_solution h)

/-- Compactness bounds a relatively continuous periodic field on an entire
closed time slab, uniformly over all spatial points. -/
theorem periodic_bound_on_slab {V : Type*} [NormedAddCommGroup V]
    {g : SpaceTime → V} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ (univ : Set Space)))
    (hperiod : UnitSpatialPeriodsOn (Icc a b) g) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x : Space, ‖g (t, x)‖ ≤ B := by
  have hK : IsCompact (toSpace '' cube) :=
    (show IsCompact cube from isCompact_Icc).image toSpace.continuous
  have hgK : ContinuousOn g (Icc a b ×ˢ (toSpace '' cube)) :=
    hg.mono (fun z hz => ⟨hz.1, mem_univ z.2⟩)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hgK
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht x
  obtain ⟨z, hz, hzx⟩ := PeriodicUniqueness.exists_cube_representative
    (f := fun y : Space => g (t, y)) (fun i y => hperiod t ht y i) x
  have hzK : z ∈ toSpace '' cube := by
    refine ⟨toSpace.symm z, ?_, toSpace.apply_symm_apply z⟩
    exact ⟨fun i => (hz i).1, fun i => (hz i).2⟩
  calc
    ‖g (t, x)‖ = ‖g (t, z)‖ := congrArg norm hzx.symm
    _ ≤ B := hB (t, z) ⟨ht, hzK⟩
    _ ≤ max B 1 := le_max_left _ _

/-- Unbounded speed rules out even a continuous periodic extension through
time one, once agreement with the original field is known. -/
theorem unbounded_excludes_continuous_extension {u v : VelocityField}
    (h : SpeedUnboundedAtOne u)
    (hv : ContinuousOn v (Icc (0 : ℝ) 1 ×ˢ (univ : Set Space)))
    (hpv : UnitSpatialPeriodsOn (Icc (0 : ℝ) 1) v)
    (hagrees : VelocityAgreesOn 1 u v) : False := by
  obtain ⟨B, _, hB⟩ := periodic_bound_on_slab hv hpv
  apply unbounded_speed_excludes_uniform_bound h
  refine ⟨B, ?_⟩
  intro t ht x
  rw [hagrees t ht x]
  exact hB t ⟨ht.1, ht.2.le⟩ x

/-- No classical solution for the same force and datum can have lifespan
larger than one. Uniqueness supplies the required pre-one agreement. -/
theorem candidate_no_solution_after_one {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f) (hT : 1 < T)
    (hv : ClassicalSolution f (fun _ => 0) T v q) : False := by
  have hsub : Icc (0 : ℝ) 1 ×ˢ (univ : Set Space) ⊆ lifespanDomain T := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT⟩, hz.2⟩
  apply unbounded_excludes_continuous_extension h.speed_unbounded
    (hv.velocity_smooth.continuousOn.mono hsub)
  · intro t ht x i
    exact hv.velocity_periodic t ⟨ht.1, ht.2.trans_lt hT⟩ x i
  · intro t ht x
    exact (candidate_agree_on_overlap h hv t
      ⟨ht.1, lt_min (ht.2.trans hT) ht.2⟩ x).symm

theorem candidate_all_lifespans_le_one {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : ClassicalSolution f (fun _ => 0) T v q) : T ≤ 1 := by
  by_contra hnot
  exact candidate_no_solution_after_one h (lt_of_not_ge hnot) hv

/-- The given lifespan-one solution is maximal under extension of its
velocity. No literal equality between pressure representatives is required. -/
theorem candidate_is_maximal {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    IsMaximalClassicalSolution f (fun _ => 0) 1 u p := by
  refine ⟨candidate_is_classical_solution h, ?_⟩
  rintro ⟨T, v, q, hT, hv, _⟩
  exact candidate_no_solution_after_one h hT hv

/-- Any shorter classical solution extends by the actual candidate field. -/
theorem candidate_extends_shorter_solution {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : ClassicalSolution f (fun _ => 0) T v q) (hT : T < 1) :
    HasClassicalExtension f (fun _ => 0) T v := by
  refine ⟨1, u, p, hT, candidate_is_classical_solution h, ?_⟩
  simpa only [min_eq_left hT.le] using candidate_agree_on_overlap h hv

/-- Every maximal classical solution for these data has exactly lifespan one. -/
theorem maximal_lifespan_eq_one {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} {T : ℝ} (h : CandidateProperties u p f)
    (hv : IsMaximalClassicalSolution f (fun _ => 0) T v q) : T = 1 := by
  have hle := candidate_all_lifespans_le_one h hv.1
  apply le_antisymm hle
  by_contra hnot
  exact hv.2 (candidate_extends_shorter_solution h hv.1 (lt_of_not_ge hnot))

/-- There is a greatest admissible finite classical lifespan, and it is one.
Existence at that time comes solely from the supplied candidate witness. -/
theorem candidate_greatest_lifespan {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    IsGreatest (admissibleLifespans f (fun _ => 0)) 1 := by
  refine ⟨⟨u, p, candidate_is_classical_solution h⟩, ?_⟩
  rintro T ⟨v, q, hv⟩
  exact candidate_all_lifespans_le_one h hv

/-- The entire set of finite admissible classical lifespans is `(0,1]`. -/
theorem candidate_admissible_lifespans {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    admissibleLifespans f (fun _ => 0) = Ioc (0 : ℝ) 1 := by
  ext T
  constructor
  · rintro ⟨v, q, hv⟩
    exact ⟨hv.lifespan_pos, candidate_all_lifespans_le_one h hv⟩
  · intro ht
    exact ⟨u, p, (candidate_is_classical_solution h).restrict ht.1 ht.2⟩

/-- A global classical solution would restrict to a forbidden lifespan
greater than one. This makes the exclusion of infinite-time continuation
explicit without assuming any existence theorem. -/
theorem candidate_excludes_global_solution {u v : VelocityField} {p q : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f)
    (hv : ContDiffOn ℝ ∞ v futureDomain) (hq : ContDiffOn ℝ ∞ q futureDomain)
    (hpv : UnitSpatialPeriodsOn (Ici (0 : ℝ)) v)
    (hpq : UnitSpatialPeriodsOn (Ici (0 : ℝ)) q)
    (hvzero : ∀ x : Space, v (0, x) = 0)
    (hdv : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, spatialDivergence v t x = 0)
    (hNSv : ∀ t : ℝ, 0 < t → ∀ x : Space, navierStokesResidual v q t x = f (t, x)) :
    False := by
  have hsub : lifespanDomain 2 ⊆ futureDomain := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  apply candidate_no_solution_after_one h (T := 2) (by norm_num)
  refine ⟨by norm_num, hv.mono hsub, hq.mono hsub, ?_, ?_, hvzero, ?_, ?_⟩
  · intro t ht x i
    exact hpv t ht.1 x i
  · intro t ht x i
    exact hpq t ht.1 x i
  · intro t ht x
    exact hdv t ht.1 x
  · intro t ht x
    exact hNSv t ht.1 x

theorem zero_classical_solution_of_zero_force {f : VelocityField} {T : ℝ}
    (hT : 0 < T) (hf : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space, f (t, x) = 0) :
    ClassicalSolution f (fun _ => 0) T (fun _ => 0) (fun _ => 0) := by
  refine ⟨hT, contDiffOn_const, contDiffOn_const, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  · intro t ht x i
    rfl
  · intro t ht x i
    rfl
  · intro t ht x
    simp [spatialDivergence, spatialDerivative]
  · intro t ht x
    exact (zero_residual t x).trans (hf t ht x).symm

/-- The specified force must be nonzero somewhere before the breakdown
time. Otherwise uniqueness identifies the candidate with the zero solution. -/
theorem candidate_force_nonzero_before_one {u : VelocityField} {p : PressureField}
    {f : VelocityField} (h : CandidateProperties u p f) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ x : Space, f (t, x) ≠ 0 := by
  by_contra hnot
  have hf : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space, f (t, x) = 0 := by
    intro t ht x
    by_contra hnonzero
    exact hnot ⟨t, ht, x, hnonzero⟩
  have hz := zero_classical_solution_of_zero_force zero_lt_one hf
  have hagree : VelocityAgreesOn 1 (fun _ => 0) u := by
    simpa only [min_self] using candidate_agree_on_overlap h hz
  apply unbounded_speed_excludes_uniform_bound h.speed_unbounded
  refine ⟨0, ?_⟩
  intro t ht x
  rw [← hagree t ht x]
  exact norm_zero.le

end NavierStokes.MaximalLifespan
