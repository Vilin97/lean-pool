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

import LeanPool.PoincareGeometry.BonnetMyers.GlobalParallel

/-!
# Temporal continuation of local parallel transport

This module develops the missing comparison between a parallel germ and a
fresh germ chosen at a nearby time.  The first lemma makes the underlying
state overlap explicit after translating the global time origin.  Subsequent
lemmas will use that overlap to transport the frame equations into one common
tangent fibre before invoking the two-frame uniqueness theorem.
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
namespace GlobalGeodesic

variable [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type u)}
  {x₀ : M} {v₀ : TangentSpace I x₀}

private theorem exists_pos_radius_of_eventually {P : ℝ → Prop}
    (hP : ∀ᶠ s in 𝓝 (0 : ℝ), P s) :
    ∃ r > (0 : ℝ), ∀ s ∈ Ioo (-r) r, P s := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨r, hr, ?_⟩
  intro s hs
  apply hsub
  rw [Metric.mem_ball]
  simpa [dist_zero_right, abs_lt] using hs

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- A parallel germ's local state description remains valid after a small
change of time origin.  The theorem returns a uniform admissible window for
the new origin and then an explicit nonempty overlap interval for every time
in that window. -/
theorem ParallelGerm.exists_interval_recentered_state
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) :
    ∃ r > (0 : ℝ), ∀ τ ∈ Ioo (-r) r,
      ∃ ε > (0 : ℝ), ∀ s ∈ Ioo (-ε) ε,
        (shift γ (t₀ + τ)).state s =
          IntrinsicGeodesic.localState p.localGeodesic (τ + s) := by
  obtain ⟨r, hr, hstate⟩ := exists_pos_radius_of_eventually p.agrees
  refine ⟨r, hr, ?_⟩
  intro τ hτ
  let ε : ℝ := min (τ + r) (r - τ)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith [hτ.1]) (by linarith [hτ.2])
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hleft : -r < τ + s := by
    have hle : ε ≤ τ + r := min_le_left _ _
    linarith [hs.1]
  have hright : τ + s < r := by
    have hle : ε ≤ r - τ := min_le_right _ _
    linarith [hs.2]
  have hlocal := hstate (τ + s) ⟨hleft, hright⟩
  change γ.state ((t₀ + τ) + s) =
    IntrinsicGeodesic.localState p.localGeodesic (τ + s)
  rw [show (t₀ + τ) + s = t₀ + (τ + s) by ring]
  exact hlocal

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type u)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type u)] in
/-- Recentring a global geodesic twice agrees with recentering it once at the
sum of the two time shifts.  The statement is deliberately at state level,
where the tangent fibre is recorded together with its base point. -/
theorem shift_shift_state
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    (t₀ τ s : ℝ) :
    (shift (shift γ t₀) τ).state s = (shift γ (t₀ + τ)).state s := by
  change γ.state (t₀ + (τ + s)) = γ.state ((t₀ + τ) + s)
  congr 1
  ring

/-- A parallel germ's canonical local field can be read against a freshly
recentered global state without hiding the dependent tangent-fibre cast.  It
is the total-space form needed to compare the old transport with a new germ
started at time `t₀ + τ`. -/
theorem ParallelGerm.shiftedField_totalState_eq_of_recentered_state
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w) (τ s : ℝ)
    (hstate : (shift γ (t₀ + τ)).state s =
      IntrinsicGeodesic.localState p.localGeodesic (τ + s)) :
    (⟨curve (shift γ (t₀ + τ)) s, p.shiftedField (τ + s)⟩ :
      Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic (τ + s),
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution (τ + s)⟩ := by
  have hstate' : (shift γ t₀).state (τ + s) =
      IntrinsicGeodesic.localState p.localGeodesic (τ + s) := by
    change γ.state (t₀ + (τ + s)) =
      IntrinsicGeodesic.localState p.localGeodesic (τ + s)
    rw [show t₀ + (τ + s) = (t₀ + τ) + s by ring]
    exact hstate
  have htotal := p.shiftedField_totalState_eq_of_state_eq (τ + s) hstate'
  have hcurve : curve (shift γ (t₀ + τ)) s =
      curve (shift γ t₀) (τ + s) := by
    change curve γ ((t₀ + τ) + s) = curve γ (t₀ + (τ + s))
    congr 1
    ring
  rw [hcurve]
  exact htotal

/-- The explicit frame-coordinate parallel equation for a germ is valid on
an interval of the actual shifted global curve.  Unlike the intrinsic germ
statement, this exposes the equation in precisely the form required to compare
two independently chosen local frames on an overlap. -/
theorem ParallelGerm.exists_interval_shiftedFrameAcceleration_eq_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), ∀ s ∈ Ioo (-r) r,
      IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (deriv p.coordinateSolution.curve s) (curve (shift γ t₀) s) +
      cov (IntrinsicAcceleration.frameField (I := I) (M := M)
        (IntrinsicGeodesic.canonicalBasis (E := E))
        (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
          (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) i)
        (p.coordinateSolution.curve s)) (curve (shift γ t₀) s)
        (velocity (shift γ t₀) s) = 0 := by
  obtain ⟨rstate, hrstate, hstate⟩ :=
    exists_pos_radius_of_eventually p.agrees
  obtain ⟨rframe, hrframe, hframe⟩ :=
    BonnetMyersEntry.IntrinsicGeodesic.LocalGeodesic.exists_interval_canonicalFrameParallel_frameAcceleration_eq_zero
      (I := I) (M := M) p.localGeodesic p.coordinateSolution hmetric
  have hvelocityGerm :=
    CurveConnection.localGeodesic_eventually_canonicalFrameVelocity_eq_velocity
      (I := I) (M := M) p.localGeodesic
  obtain ⟨rvelocity, hrvelocity, hvelocity⟩ :=
    exists_pos_radius_of_eventually hvelocityGerm
  let r : ℝ := min rstate (min rframe rvelocity)
  have hr : 0 < r := lt_min hrstate (lt_min hrframe hrvelocity)
  refine ⟨r, hr, ?_⟩
  intro s hs
  have hsstate : s ∈ Ioo (-rstate) rstate := by
    have hle : r ≤ rstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hsframe : s ∈ Ioo (-rframe) rframe := by
    have hle : r ≤ rframe := le_trans (min_le_right _ _) (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hsvelocity : s ∈ Ioo (-rvelocity) rvelocity := by
    have hle : r ≤ rvelocity := le_trans (min_le_right _ _) (min_le_right _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hstateAt : (shift γ t₀).state s =
      IntrinsicGeodesic.localState p.localGeodesic s := by
    simpa [shift_state] using hstate s hsstate
  have hlocal := hframe s hsframe
  rw [hvelocity s hsvelocity] at hlocal
  exact frameAcceleration_eq_zero_of_totalState_eq (I := I) (M := M)
    hstateAt (IntrinsicGeodesic.canonicalBasis (E := E))
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
      (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) i)
    (p.coordinateSolution.curve s) (deriv p.coordinateSolution.curve s)
    hlocal

/-- The preceding interval equation is stable under a change of global time
origin.  In particular, the old local transport has an explicit
zero-acceleration frame equation along the newly shifted global geodesic,
which is the common curve used to compare it with a freshly restarted germ. -/
theorem ParallelGerm.exists_interval_recenteredFrameAcceleration_eq_zero
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), ∀ τ ∈ Ioo (-r) r,
      ∃ ε > (0 : ℝ), ∀ s ∈ Ioo (-ε) ε,
        IntrinsicAcceleration.frameField (I := I) (M := M)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
            (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) i)
          (deriv p.coordinateSolution.curve (τ + s))
          (curve (shift γ (t₀ + τ)) s) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M)
          (IntrinsicGeodesic.canonicalBasis (E := E))
          (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
            (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) i)
          (p.coordinateSolution.curve (τ + s)))
          (curve (shift γ (t₀ + τ)) s)
          (velocity (shift γ (t₀ + τ)) s) = 0 := by
  obtain ⟨r, hr, hframe⟩ := p.exists_interval_shiftedFrameAcceleration_eq_zero hmetric
  refine ⟨r, hr, ?_⟩
  intro τ hτ
  let ε : ℝ := min (τ + r) (r - τ)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith [hτ.1]) (by linarith [hτ.2])
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hleft : -r < τ + s := by
    have hle : ε ≤ τ + r := min_le_left _ _
    linarith [hs.1]
  have hright : τ + s < r := by
    have hle : ε ≤ r - τ := min_le_right _ _
    linarith [hs.2]
  have hold := hframe (τ + s) ⟨hleft, hright⟩
  have hstate : (shift γ (t₀ + τ)).state s =
      (shift γ t₀).state (τ + s) := by
    change γ.state ((t₀ + τ) + s) = γ.state (t₀ + (τ + s))
    congr 1
    ring
  exact frameAcceleration_eq_zero_of_totalState_eq (I := I) (M := M)
    hstate (IntrinsicGeodesic.canonicalBasis (E := E))
    (fun i => LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
      (curve γ t₀) (IntrinsicGeodesic.canonicalBasis (E := E)) i)
    (p.coordinateSolution.curve (τ + s))
    (deriv p.coordinateSolution.curve (τ + s)) hold

/-- A parallel germ and any fresh germ restarted from its transported value
coincide on a genuine common interval.  The equality is stated in the total
tangent bundle so that no fibre transport is hidden: the proof compares the
two frame-coordinate equations on the same recentered global curve and then
uses the chart-independent interval uniqueness theorem. -/
theorem ParallelGerm.exists_interval_totalState_eq_of_restart
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), ∀ τ ∈ Ioo (-r) r,
      ∀ q : ParallelGerm (I := I) (M := M) γ (t₀ + τ) (p.shiftedField τ),
      ∃ ε > (0 : ℝ), ∀ s ∈ Ioo (-ε) ε,
        (⟨curve (shift γ (t₀ + τ)) s, p.shiftedField (τ + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + τ)) s, q.shiftedField s⟩ := by
  obtain ⟨rpstate, hrpstate, hpstate⟩ := p.exists_interval_recentered_state
  obtain ⟨rpframe, hrpframe, hpframe⟩ :=
    p.exists_interval_recenteredFrameAcceleration_eq_zero hmetric
  have hpcoordhalf : 0 < p.coordinateSolution.radius / 2 := by
    linarith [p.coordinateSolution.radius_pos]
  let r : ℝ := min rpstate (min rpframe (p.coordinateSolution.radius / 2))
  have hr : 0 < r := lt_min hrpstate (lt_min hrpframe hpcoordhalf)
  refine ⟨r, hr, ?_⟩
  intro τ hτ q
  have hτpstate : τ ∈ Ioo (-rpstate) rpstate := by
    have hle : r ≤ rpstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hτ.1,
      lt_of_lt_of_le hτ.2 hle⟩
  have hτpframe : τ ∈ Ioo (-rpframe) rpframe := by
    have hle : r ≤ rpframe := le_trans (min_le_right _ _) (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hτ.1,
      lt_of_lt_of_le hτ.2 hle⟩
  have hτpcoord : τ ∈ Ioo (-(p.coordinateSolution.radius / 2))
      (p.coordinateSolution.radius / 2) := by
    have hle : r ≤ p.coordinateSolution.radius / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hτ.1,
      lt_of_lt_of_le hτ.2 hle⟩
  obtain ⟨εstate, hεstate, hpstate'⟩ := hpstate τ hτpstate
  obtain ⟨εframe, hεframe, hpframe'⟩ := hpframe τ hτpframe
  obtain ⟨rqstate, hrqstate, hqstate⟩ :=
    exists_pos_radius_of_eventually q.agrees
  obtain ⟨rqframe, hrqframe, hqframe⟩ :=
    q.exists_interval_shiftedFrameAcceleration_eq_zero hmetric
  have hqcoordhalf : 0 < q.coordinateSolution.radius / 2 := by
    linarith [q.coordinateSolution.radius_pos]
  let εtail : ℝ := min rqstate
    (min rqframe (min (p.coordinateSolution.radius / 2)
      (q.coordinateSolution.radius / 2)))
  have hεtail : 0 < εtail := by
    dsimp [εtail]
    exact lt_min hrqstate
      (lt_min hrqframe (lt_min hpcoordhalf hqcoordhalf))
  let ε : ℝ := min εstate (min εframe εtail)
  have hε : 0 < ε := lt_min hεstate (lt_min hεframe hεtail)
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hsstate : s ∈ Ioo (-εstate) εstate := by
    have hle : ε ≤ εstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hsframe : s ∈ Ioo (-εframe) εframe := by
    have hle : ε ≤ εframe := le_trans (min_le_right _ _) (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hstail : s ∈ Ioo (-εtail) εtail := by
    have hle : ε ≤ εtail := le_trans (min_le_right _ _) (min_le_right _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hs.1,
      lt_of_lt_of_le hs.2 hle⟩
  have hsqstate : s ∈ Ioo (-rqstate) rqstate := by
    have hle : εtail ≤ rqstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hstail.1,
      lt_of_lt_of_le hstail.2 hle⟩
  have hsqframe : s ∈ Ioo (-rqframe) rqframe := by
    have hle : εtail ≤ rqframe := le_trans (min_le_right _ _) (min_le_left _ _)
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hstail.1,
      lt_of_lt_of_le hstail.2 hle⟩
  have hspcoordhalf : s ∈ Ioo (-(p.coordinateSolution.radius / 2))
      (p.coordinateSolution.radius / 2) := by
    have hle : εtail ≤ p.coordinateSolution.radius / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hstail.1,
      lt_of_lt_of_le hstail.2 hle⟩
  have hsqcoordhalf : s ∈ Ioo (-(q.coordinateSolution.radius / 2))
      (q.coordinateSolution.radius / 2) := by
    have hle : εtail ≤ q.coordinateSolution.radius / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hstail.1,
      lt_of_lt_of_le hstail.2 hle⟩
  have hspcoord : τ + s ∈ Ioo (-p.coordinateSolution.radius)
      p.coordinateSolution.radius := by
    constructor <;> linarith [hτpcoord.1, hτpcoord.2,
      hspcoordhalf.1, hspcoordhalf.2]
  have hsqcoord : s ∈ Ioo (-q.coordinateSolution.radius)
      q.coordinateSolution.radius := by
    constructor <;> linarith [hsqcoordhalf.1, hsqcoordhalf.2,
      q.coordinateSolution.radius_pos]
  have hpstateAt := hpstate' s hsstate
  have hqstateAt : (shift γ (t₀ + τ)).state s =
      IntrinsicGeodesic.localState q.localGeodesic s := by
    simpa [shift_state] using hqstate s hsqstate
  let b : Module.Basis (IntrinsicAcceleration.FrameIndex E) ℝ E :=
    IntrinsicGeodesic.canonicalBasis (E := E)
  let S : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x := fun i =>
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
      (curve γ t₀) b i
  let T : IntrinsicAcceleration.FrameIndex E → (x : M) → TM x := fun i =>
    LocalGeodesicData.smoothFrame (I := I) (M := M) (E := E)
      (curve γ (t₀ + τ)) b i
  let uP : ℝ → E := fun z => p.coordinateSolution.curve (τ + z)
  let aP : ℝ → E := fun z => deriv p.coordinateSolution.curve (τ + z)
  let uQ : ℝ → E := q.coordinateSolution.curve
  let aQ : ℝ → E := fun z => deriv q.coordinateSolution.curve z
  let G : ℝ → M := curve (shift γ (t₀ + τ))
  let V : (z : ℝ) → TM (G z) := fun z => velocity (shift γ (t₀ + τ)) z
  have hderivP : ∀ z ∈ Ioo (-ε) ε, ∀ i,
      HasDerivAt (fun y => b.repr (uP y) i) (b.repr (aP z) i) z := by
    intro z hz i
    have hzhalf : z ∈ Ioo (-(p.coordinateSolution.radius / 2))
        (p.coordinateSolution.radius / 2) := by
      have hle : ε ≤ p.coordinateSolution.radius / 2 :=
        le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (min_le_left _ _))))
      exact ⟨lt_of_le_of_lt (neg_le_neg hle) hz.1,
        lt_of_lt_of_le hz.2 hle⟩
    have hzcoord : τ + z ∈ Ioo (-p.coordinateSolution.radius)
        p.coordinateSolution.radius := by
      constructor <;> linarith [hτpcoord.1, hτpcoord.2,
        hzhalf.1, hzhalf.2]
    have hsol := p.coordinateSolution.hasDeriv (τ + z) (by
      simpa only [zero_sub, zero_add] using hzcoord)
    have hadd : HasDerivAt (fun y : ℝ ↦ τ + y) 1 z := by
      simpa only [id_eq] using (hasDerivAt_id z).const_add τ
    have hrec : HasDerivAt (fun y : ℝ ↦
        p.coordinateSolution.curve (τ + y))
        (deriv p.coordinateSolution.curve (τ + z)) z := by
      rw [hsol.deriv]
      simpa [Function.comp_def] using HasDerivAt.scomp z hsol hadd
    have hcoord : HasDerivAt
        (fun _ : ℝ ↦ (b.coord i).toContinuousLinearMap) 0 z :=
      hasDerivAt_const z (b.coord i).toContinuousLinearMap
    simpa [uP, aP] using hcoord.clm_apply hrec
  have hderivQ : ∀ z ∈ Ioo (-ε) ε, ∀ i,
      HasDerivAt (fun y => b.repr (uQ y) i) (b.repr (aQ z) i) z := by
    intro z hz i
    have hzhalf : z ∈ Ioo (-(q.coordinateSolution.radius / 2))
        (q.coordinateSolution.radius / 2) := by
      have hle : ε ≤ q.coordinateSolution.radius / 2 :=
        le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
            (min_le_right _ _))))
      exact ⟨lt_of_le_of_lt (neg_le_neg hle) hz.1,
        lt_of_lt_of_le hz.2 hle⟩
    have hzcoord : z ∈ Ioo (-q.coordinateSolution.radius)
        q.coordinateSolution.radius := by
      constructor <;> linarith [hzhalf.1, hzhalf.2,
        q.coordinateSolution.radius_pos]
    have hsol := q.coordinateSolution.hasDeriv z (by
      simpa only [zero_sub, zero_add] using hzcoord)
    have hcoord : HasDerivAt
        (fun _ : ℝ ↦ (b.coord i).toContinuousLinearMap) 0 z :=
      hasDerivAt_const z (b.coord i).toContinuousLinearMap
    change HasDerivAt (fun y => b.repr (q.coordinateSolution.curve y) i)
      (b.repr (deriv q.coordinateSolution.curve z) i) z
    rw [hsol.deriv]
    simpa using hcoord.clm_apply hsol
  have hG : ∀ z ∈ Ioo (-ε) ε,
      HasMFDerivAt (𝓘(ℝ, ℝ)) I G z
        (CurveConnection.timeTangentMap (I := I) z (V z)) := by
    intro z hz
    change HasMFDerivAt (𝓘(ℝ, ℝ)) I (curve (shift γ (t₀ + τ))) z
      (CurveConnection.timeTangentMap (I := I) z
        (velocity (shift γ (t₀ + τ)) z))
    rw [CurveConnection.timeTangentMap_eq_toSpanSingleton]
    exact BonnetMyersEntry.IntrinsicGeodesic.GlobalGeodesic.hasMFDerivAt_curve
      (I := I) (M := M) (shift γ (t₀ + τ)) z
  have hS : ∀ z ∈ Ioo (-ε) ε, ∀ i, MDiffAt (T% (S i)) (G z) := by
    intro z hz i
    change MDiffAt (T% (LocalGeodesicData.smoothFrame (I := I) (M := M)
      (E := E) (curve γ t₀) b i)) (curve (shift γ (t₀ + τ)) z)
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M)
      (curve γ t₀) b i _
  have hT : ∀ z ∈ Ioo (-ε) ε, ∀ i, MDiffAt (T% (T i)) (G z) := by
    intro z hz i
    change MDiffAt (T% (LocalGeodesicData.smoothFrame (I := I) (M := M)
      (E := E) (curve γ (t₀ + τ)) b i))
      (curve (shift γ (t₀ + τ)) z)
    exact IntrinsicAcceleration.mdiffAt_smoothFrame (I := I) (M := M)
      (curve γ (t₀ + τ)) b i _
  have hzeroP : ∀ z ∈ Ioo (-ε) ε,
      IntrinsicAcceleration.frameField (I := I) (M := M) b S (aP z) (G z) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) b S (uP z))
          (G z) (V z) = 0 := by
    intro z hz
    have hzframe : z ∈ Ioo (-εframe) εframe := by
      have hle : ε ≤ εframe := le_trans (min_le_right _ _) (min_le_left _ _)
      exact ⟨lt_of_le_of_lt (neg_le_neg hle) hz.1,
        lt_of_lt_of_le hz.2 hle⟩
    simpa [b, S, uP, aP, G, V] using hpframe' z hzframe
  have hzeroQ : ∀ z ∈ Ioo (-ε) ε,
      IntrinsicAcceleration.frameField (I := I) (M := M) b T (aQ z) (G z) +
        cov (IntrinsicAcceleration.frameField (I := I) (M := M) b T (uQ z))
          (G z) (V z) = 0 := by
    intro z hz
    have hleTail : ε ≤ εtail :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hleFrame : εtail ≤ rqframe :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hle : ε ≤ rqframe := le_trans hleTail hleFrame
    have hzframe : z ∈ Ioo (-rqframe) rqframe :=
      ⟨lt_of_le_of_lt (neg_le_neg hle) hz.1,
        lt_of_lt_of_le hz.2 hle⟩
    simpa [b, T, uQ, aQ, G, V] using hqframe z hzframe
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith [hε]
  have hpstateZero := hpstate' 0 (by
    have hle : ε ≤ εstate := min_le_left _ _
    exact ⟨lt_of_le_of_lt (neg_le_neg hle) hzero.1,
      lt_of_lt_of_le hzero.2 hle⟩)
  have hpstateZero' : (shift γ (t₀ + τ)).state 0 =
      IntrinsicGeodesic.localState p.localGeodesic τ := by
    change γ.state ((t₀ + τ) + 0) =
      IntrinsicGeodesic.localState p.localGeodesic τ
    change γ.state ((t₀ + τ) + 0) =
      IntrinsicGeodesic.localState p.localGeodesic (τ + 0) at hpstateZero
    rw [show τ + 0 = τ by ring] at hpstateZero
    exact hpstateZero
  have hqstateZero : (shift γ (t₀ + τ)).state 0 =
      IntrinsicGeodesic.localState q.localGeodesic 0 := by
    have hzeroq : (0 : ℝ) ∈ Ioo (-rqstate) rqstate := by
      have hle : ε ≤ rqstate := le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))
      exact ⟨lt_of_le_of_lt (neg_le_neg hle) hzero.1,
        lt_of_lt_of_le hzero.2 hle⟩
    simpa [shift_state] using hqstate 0 hzeroq
  have hptotalZero :
      (⟨G 0, p.shiftedField τ⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic τ,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution τ⟩ := by
    have hsource := p.shiftedField_totalState_eq_of_recentered_state
      τ 0 hpstateZero
    rw [show τ + 0 = τ by ring] at hsource
    simpa [G] using hsource
  have hqtotalZero :
      (⟨G 0, q.shiftedField 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) q.localGeodesic q.coordinateSolution 0⟩ := by
    simpa [G] using q.shiftedField_totalState_eq_of_state_eq 0 hqstateZero
  have hqinitial :
      (⟨G 0, q.shiftedField 0⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨G 0, p.shiftedField τ⟩ := by
    have hsource := q.shiftedField_initial_totalState
    have hbase : curve γ (t₀ + τ) = G 0 := by
      simp [G, curve, shift_state]
    calc
      (⟨G 0, q.shiftedField 0⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve γ (t₀ + τ), p.shiftedField τ⟩ := by
          simpa [G] using hsource
      _ = ⟨G 0, p.shiftedField τ⟩ := by
        rw [← hbase]
  have hlocalZero :
      (⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic τ,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution τ⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic 0,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) q.localGeodesic q.coordinateSolution 0⟩ :=
    hptotalZero.symm.trans (hqinitial.symm.trans hqtotalZero)
  have hinit : IntrinsicAcceleration.timeFrameField (I := I) (M := M)
      b S uP 0 (G 0) =
      IntrinsicAcceleration.timeFrameField (I := I) (M := M)
        b T uQ 0 (G 0) := by
    apply timeFrameField_eq_of_totalState_eq (I := I) (M := M)
      hpstateZero' hqstateZero b b S T uP uQ 0
    simpa [IntrinsicAcceleration.timeFrameField, b, S, T, uP, uQ,
      IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel] using hlocalZero
  have htime := CurveConnection.timeFrameField_eq_of_zeroAcceleration_on_Ioo
    (I := I) (M := M) cov b b S T uP aP uQ aQ G V hzero hs hG
    hderivP hderivQ hS hT hmetric hzeroP hzeroQ hinit
  have hlocal :
      (⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic (τ + s),
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) p.localGeodesic p.coordinateSolution (τ + s)⟩ :
        Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
      ⟨IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s,
        IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel
          (I := I) (M := M) q.localGeodesic q.coordinateSolution s⟩ := by
    have hpstateAt' :
        (⟨G s, V s⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic (τ + s),
          IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic (τ + s)⟩ := by
      change (⟨G s, V s⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨IntrinsicGeodesic.LocalGeodesic.curve p.localGeodesic (τ + s),
          IntrinsicGeodesic.LocalGeodesic.velocity p.localGeodesic (τ + s)⟩ at hpstateAt
      exact hpstateAt
    have hqstateAt' :
        (⟨G s, V s⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s,
          IntrinsicGeodesic.LocalGeodesic.velocity q.localGeodesic s⟩ := by
      change (⟨G s, V s⟩ : Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨IntrinsicGeodesic.LocalGeodesic.curve q.localGeodesic s,
          IntrinsicGeodesic.LocalGeodesic.velocity q.localGeodesic s⟩ at hqstateAt
      exact hqstateAt
    apply totalState_timeFrameField_eq_of_totalState_eq (I := I) (M := M)
      hpstateAt' hqstateAt' b b S T uP uQ s
    simpa [b, S, T, uP, uQ,
      IntrinsicGeodesic.LocalGeodesic.canonicalFrameParallel] using htime
  have hptotal := p.shiftedField_totalState_eq_of_recentered_state
    τ s hpstateAt
  have hqtotal := q.shiftedField_totalState_eq_of_state_eq s hqstateAt
  exact hptotal.trans (hlocal.trans hqtotal.symm)

/-- Filter-germ form of restart coherence.  This is the interface used by a
partial-to-global continuation construction: after a nearby restart, the old
and freshly chosen transports define the same tangent-bundle-valued germ. -/
theorem ParallelGerm.eventually_totalState_eq_of_restart
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : TM (curve γ t₀)}
    (p : ParallelGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), ∀ τ ∈ Ioo (-r) r,
      ∀ q : ParallelGerm (I := I) (M := M) γ (t₀ + τ) (p.shiftedField τ),
      ∀ᶠ s in 𝓝 (0 : ℝ),
        (⟨curve (shift γ (t₀ + τ)) s, p.shiftedField (τ + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + τ)) s, q.shiftedField s⟩ := by
  obtain ⟨r, hr, hrestart⟩ :=
    p.exists_interval_totalState_eq_of_restart hmetric
  refine ⟨r, hr, ?_⟩
  intro τ hτ q
  obtain ⟨ε, hε, heq⟩ := hrestart τ hτ q
  have hIoo : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [hε]) (by linarith [hε])
  filter_upwards [hIoo] with s hs
  exact heq s hs

/-- Finite parallel frames inherit the restart coherence already proved for a
single parallel germ.  The two finite minima make the time window uniform in
the frame index, so this is a genuine common overlap for the whole Gram
family, not a collection of componentwise neighbourhoods. -/
theorem ParallelFamilyGerm.exists_interval_totalState_eq_of_restart
    {ι : Type*} [Fintype ι] [Nonempty ι]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), ∀ τ ∈ Ioo (-r) r,
      ∀ q : ParallelFamilyGerm (I := I) (M := M) γ (t₀ + τ)
        (fun i ↦ p.shiftedField i τ),
      ∃ ε > (0 : ℝ), ∀ (i : ι) (s : ℝ), s ∈ Ioo (-ε) ε →
        (⟨curve (shift γ (t₀ + τ)) s, p.shiftedField i (τ + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + τ)) s, q.shiftedField i s⟩ := by
  classical
  have hmember : ∀ i : ι, ∃ r > (0 : ℝ), ∀ τ ∈ Ioo (-r) r,
      ∀ q : ParallelGerm (I := I) (M := M) γ (t₀ + τ)
        ((p.toParallelGerm i).shiftedField τ),
      ∃ ε > (0 : ℝ), ∀ s ∈ Ioo (-ε) ε,
        (⟨curve (shift γ (t₀ + τ)) s,
            (p.toParallelGerm i).shiftedField (τ + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + τ)) s, q.shiftedField s⟩ := by
    intro i
    exact (p.toParallelGerm i).exists_interval_totalState_eq_of_restart hmetric
  choose r hr hrestart using hmember
  let r₀ : ℝ := (Finset.univ : Finset ι).inf' Finset.univ_nonempty r
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    refine (Finset.lt_inf'_iff _).2 ?_
    intro i hi
    exact hr i
  refine ⟨r₀, hr₀, ?_⟩
  intro τ hτ q
  have hrestartFamily : ∀ i : ι, ∃ ε > (0 : ℝ),
      ∀ s ∈ Ioo (-ε) ε,
        (⟨curve (shift γ (t₀ + τ)) s,
            (p.toParallelGerm i).shiftedField (τ + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + τ)) s,
          (q.toParallelGerm i).shiftedField s⟩ := by
    intro i
    have hrle : r₀ ≤ r i := by
      dsimp [r₀]
      exact Finset.inf'_le r (Finset.mem_univ i)
    have hτi : τ ∈ Ioo (-(r i)) (r i) := by
      exact ⟨lt_of_le_of_lt (neg_le_neg hrle) hτ.1,
        lt_of_lt_of_le hτ.2 hrle⟩
    simpa only [ParallelFamilyGerm.shiftedField] using
      hrestart i τ hτi (q.toParallelGerm i)
  choose ε hε heq using hrestartFamily
  let ε₀ : ℝ := (Finset.univ : Finset ι).inf' Finset.univ_nonempty ε
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    refine (Finset.lt_inf'_iff _).2 ?_
    intro i hi
    exact hε i
  refine ⟨ε₀, hε₀, ?_⟩
  intro i s hs
  have hεle : ε₀ ≤ ε i := by
    dsimp [ε₀]
    exact Finset.inf'_le ε (Finset.mem_univ i)
  have hsi : s ∈ Ioo (-(ε i)) (ε i) := by
    exact ⟨lt_of_le_of_lt (neg_le_neg hεle) hs.1,
      lt_of_lt_of_le hs.2 hεle⟩
  simpa only [ParallelFamilyGerm.shiftedField] using heq i s hsi

/-- Filter-germ form of finite-frame restart coherence.  This packages the
common finite-index interval into the form used when local frame pieces are
glued along a time cover. -/
theorem ParallelFamilyGerm.eventually_totalState_eq_of_restart
    {ι : Type*} [Fintype ι] [Nonempty ι]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {γ : GlobalGeodesic (I := I) (M := M) cov x₀ v₀}
    {t₀ : ℝ} {w : ι → TM (curve γ t₀)}
    (p : ParallelFamilyGerm (I := I) (M := M) γ t₀ w)
    (hmetric : cov.IsMetricCompatibleTangent) :
    ∃ r > (0 : ℝ), ∀ τ ∈ Ioo (-r) r,
      ∀ q : ParallelFamilyGerm (I := I) (M := M) γ (t₀ + τ)
        (fun i ↦ p.shiftedField i τ),
      ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i,
        (⟨curve (shift γ (t₀ + τ)) s, p.shiftedField i (τ + s)⟩ :
          Bundle.TotalSpace E (TangentSpace I : M → Type _)) =
        ⟨curve (shift γ (t₀ + τ)) s, q.shiftedField i s⟩ := by
  obtain ⟨r, hr, hrestart⟩ :=
    p.exists_interval_totalState_eq_of_restart hmetric
  refine ⟨r, hr, ?_⟩
  intro τ hτ q
  obtain ⟨ε, hε, heq⟩ := hrestart τ hτ q
  have hIoo : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith [hε]) (by linarith [hε])
  filter_upwards [hIoo] with s hs
  intro i
  exact heq i s hs

end GlobalGeodesic
end IntrinsicGeodesic

end BonnetMyersEntry
