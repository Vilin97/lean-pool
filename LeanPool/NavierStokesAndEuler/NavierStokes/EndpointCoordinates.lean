/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PositiveRepresentatives
public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowBorelBase

@[expose] public section

/-!
# Actual similarity coordinates across the nonzero axial endpoint

At `t=1`, `z != 0`, the explicit positive root lies on the regular stable
branch.  The extension below is built from that branch and agrees with all
actual physical coordinate jets at every point with `t<1`.
-/

noncomputable section

namespace NavierStokes.EndpointCoordinates

open Set Filter Function
open scoped Topology ContDiff
open SimilarityCoordinates

abbrev PhysicalPoint := SimilarityProfile.PhysicalPoint
abbrev Chart := SlowBorelBase.Chart

/-- The positive solution of the zero-time similarity equation. -/
noncomputable def endpointRoot (a z : ℝ) : ℝ := (z ^ 2) ^ (1 - a)⁻¹

theorem endpointRoot_pos (a : ℝ) {z : ℝ} (hz : z ≠ 0) : 0 < endpointRoot a z :=
  Real.rpow_pos_of_pos (sq_pos_of_ne_zero hz) _

theorem endpointRoot_power {a z : ℝ} (ha1 : a < 1) :
    endpointRoot a z ^ (1 - a) = z ^ 2 :=
  Real.rpow_inv_rpow (sq_nonneg z) (sub_pos.mpr ha1).ne'

theorem endpointRoot_equation {a z : ℝ} (ha1 : a < 1) (hz : z ≠ 0) :
    forwardScalar a z (endpointRoot a z) = 0 := by
  rw [forwardScalar_factor (endpointRoot_pos a hz), endpointRoot_power ha1]
  ring

theorem endpointRoot_slope {a z : ℝ} (ha1 : a < 1) (hz : z ≠ 0) :
    scalarSlope a z (endpointRoot a z) = 1 - a := by
  have hp := endpointRoot_pos a hz
  have he := endpointRoot_equation ha1 hz
  have hprod : z ^ 2 * endpointRoot a z ^ a = endpointRoot a z := by
    dsimp only [forwardScalar] at he
    linarith
  rw [scalarSlope, Real.rpow_sub_one hp.ne']
  rw [show z ^ 2 * a * (endpointRoot a z ^ a / endpointRoot a z) =
      a * (z ^ 2 * endpointRoot a z ^ a) / endpointRoot a z by ring,
    hprod, mul_div_cancel_right₀ _ hp.ne']

/-- Every nonzero point of the zero-time axis belongs to the actual regular
stable target. No inverse-coordinate extension is assumed. -/
theorem zeroTime_mem_stableTarget {a z : ℝ} (_ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) :
    (0, z) ∈ PositiveRepresentatives.stableTarget a := by
  refine ⟨(endpointRoot a z, z), ⟨endpointRoot_pos a hz, ?_⟩,
    Prod.ext (endpointRoot_equation ha1 hz) rfl⟩
  change 0 < scalarSlope a z (endpointRoot a z)
  rw [endpointRoot_slope ha1 hz]
  linarith

theorem stableInverse_zeroTime {a z : ℝ} (ha : 0 < a) (ha1 : a < 1) (hz : z ≠ 0) :
    PositiveRepresentatives.stableInverse a (0, z) = (endpointRoot a z, z) := by
  have hs : (endpointRoot a z, z) ∈ PositiveRepresentatives.stableSource a := by
    refine ⟨endpointRoot_pos a hz, ?_⟩
    change 0 < scalarSlope a z (endpointRoot a z)
    rw [endpointRoot_slope ha1 hz]
    linarith
  have he := PositiveRepresentatives.stableInverse_forwardMap ha.le ha1.le hs
  have hf : forwardMap a (endpointRoot a z, z) = (0, z) :=
    Prod.ext (endpointRoot_equation ha1 hz) rfl
  rwa [hf] at he

noncomputable def timeAxial (p : PhysicalPoint) : ℝ × ℝ := (1 - p.1, p.2.2)

noncomputable def domain (h : ℝ) : Set PhysicalPoint :=
  timeAxial ⁻¹' PositiveRepresentatives.stableTarget (2 * h)

noncomputable def qExtension (h : ℝ) (p : PhysicalPoint) : ℝ :=
  (PositiveRepresentatives.stableInverse (2 * h) (timeAxial p)).1

noncomputable def etaExtension (h : ℝ) (p : PhysicalPoint) : ℝ :=
  p.2.2 / qExtension h p ^ ((1 - 2 * h) / 2)

noncomputable def XExtension (h : ℝ) (p : PhysicalPoint) : ℝ := p.2.1 / qExtension h p

noncomputable def innerExtension (h : ℝ) (p : PhysicalPoint) : ℝ × ℝ :=
  (XExtension h p, etaExtension h p)

noncomputable def chartExtension (h : ℝ) (p : PhysicalPoint) : Chart :=
  (qExtension h p, innerExtension h p)

theorem timeAxial_smooth : ContDiff ℝ ∞ timeAxial :=
  (contDiff_const.sub contDiff_fst).prodMk contDiff_snd.snd

theorem domain_open (h : ℝ) : IsOpen (domain h) :=
  (PositiveRepresentatives.stableTarget_open (2 * h)).preimage timeAxial_smooth.continuous

theorem endpoint_mem_domain {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (s : ℝ) {z : ℝ} (hz : z ≠ 0) : (1, (s, z)) ∈ domain h := by
  change (1 - 1, z) ∈ PositiveRepresentatives.stableTarget (2 * h)
  simpa only [sub_self] using zeroTime_mem_stableTarget (by linarith : 0 < 2 * h)
    (by linarith : 2 * h < 1) hz

theorem past_mem_domain {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : p ∈ domain h :=
  PositiveRepresentatives.positiveTime_mem_stableTarget (by linarith) (by linarith) (sub_pos.mpr hp)

theorem qExtension_pos {h : ℝ} {p : PhysicalPoint} (hp : p ∈ domain h) : 0 < qExtension h p :=
  (PositiveRepresentatives.stableInverse_spec hp).1.1

theorem qExtension_equation {h : ℝ} {p : PhysicalPoint} (hp : p ∈ domain h) :
    forwardScalar (2 * h) p.2.2 (qExtension h p) = 1 - p.1 := by
  have hs := (PositiveRepresentatives.stableInverse_spec hp).2
  have hz : (PositiveRepresentatives.stableInverse (2 * h) (timeAxial p)).2 = p.2.2 := by
    simpa only [forwardMap, timeAxial] using congrArg (fun x : ℝ × ℝ => x.2) hs
  have hq := congrArg (fun x : ℝ × ℝ => x.1) hs
  change forwardScalar (2 * h)
    (PositiveRepresentatives.stableInverse (2 * h) (timeAxial p)).2 (qExtension h p) = 1 - p.1 at hq
  rwa [hz] at hq

theorem qExtension_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p ∈ domain h) : ContDiffAt ℝ ∞ (qExtension h) p :=
  ((PositiveRepresentatives.stableInverse_smoothAt (by linarith) (by linarith) hp).comp p
    timeAxial_smooth.contDiffAt).fst

theorem innerExtension_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p ∈ domain h) : ContDiffAt ℝ ∞ (innerExtension h) p := by
  have hq := qExtension_smoothAt hh hh1 hp
  have hpos := qExtension_pos hp
  exact (contDiffAt_snd.fst.div hq hpos.ne').prodMk
    (contDiffAt_snd.snd.div (hq.rpow_const_of_ne hpos.ne') (Real.rpow_pos_of_pos hpos _).ne')

theorem chartExtension_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p ∈ domain h) : ContDiffAt ℝ ∞ (chartExtension h) p :=
  (qExtension_smoothAt hh hh1 hp).prodMk (innerExtension_smoothAt hh hh1 hp)

theorem chartExtension_smoothOn {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (chartExtension h) (domain h) :=
  fun _ hp => (chartExtension_smoothAt hh hh1 hp).contDiffWithinAt

theorem qExtension_endpoint {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (s : ℝ) {z : ℝ} (hz : z ≠ 0) : qExtension h (1, (s, z)) = endpointRoot (2 * h) z := by
  simpa only [qExtension, timeAxial, sub_self] using
    congrArg (fun x : ℝ × ℝ => x.1)
      (stableInverse_zeroTime (by linarith : 0 < 2 * h) (by linarith : 2 * h < 1) hz)

theorem chartExtension_endpoint {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (s : ℝ) {z : ℝ} (hz : z ≠ 0) :
    chartExtension h (1, (s, z)) =
      (endpointRoot (2 * h) z,
        (s / endpointRoot (2 * h) z, z / endpointRoot (2 * h) z ^ ((1 - 2 * h) / 2))) := by
  simp only [chartExtension, innerExtension, XExtension, etaExtension, qExtension_endpoint hh hh1 s
    hz]

theorem qExtension_eq_physical {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : qExtension h p = SimilarityProfile.q h p := by
  simpa only [qExtension, timeAxial, SimilarityProfile.q, inverseMap] using
    congrArg (fun x : ℝ × ℝ => x.1)
      (PositiveRepresentatives.stableInverse_eq_inverseMap
        (by linarith : 0 < 2 * h) (by linarith : 2 * h < 1) (sub_pos.mpr hp))

theorem innerExtension_eq_physical {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : innerExtension h p = SimilarityProfile.inner h p := by
  change (p.2.1 / qExtension h p, p.2.2 / qExtension h p ^ ((1 - 2 * h) / 2)) =
    (p.2.1 / SimilarityProfile.q h p, p.2.2 / SimilarityProfile.q h p ^ ((1 - 2 * h) / 2))
  rw [qExtension_eq_physical hh hh1 hp]

theorem chartExtension_eq_physical {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) : chartExtension h p = SlowBorelBase.physicalChart h p := by
  change (qExtension h p, (p.2.1 / qExtension h p, p.2.2 / qExtension h p ^ ((1 - 2 * h) / 2))) =
    (SimilarityProfile.q h p,
      (p.2.1 / SimilarityProfile.q h p, p.2.2 / SimilarityProfile.q h p ^ ((1 - 2 * h) / 2)))
  rw [qExtension_eq_physical hh hh1 hp]

theorem chartExtension_eventuallyEq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) :
    chartExtension h =ᶠ[𝓝 p] SlowBorelBase.physicalChart h := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
  exact chartExtension_eq_physical hh hh1 hq

theorem jets_eq_of_eventuallyEq {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V} {p : E}
    (he : f =ᶠ[𝓝 p] g) (n : ℕ) : iteratedFDeriv ℝ n f p = iteratedFDeriv ℝ n g p := by
  have he' : f =ᶠ[𝓝[univ] p] g := by simpa only [nhdsWithin_univ] using he
  simpa only [iteratedFDerivWithin_univ] using he'.iteratedFDerivWithin_eq he.self_of_nhds n

theorem chartExtension_jets_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (hp : p.1 < 1) (n : ℕ) :
    iteratedFDeriv ℝ n (chartExtension h) p = iteratedFDeriv ℝ n (SlowBorelBase.physicalChart h) p
      :=
  jets_eq_of_eventuallyEq (chartExtension_eventuallyEq hh hh1 hp) n

noncomputable def lowerDomain (h c : ℝ) : Set PhysicalPoint :=
  domain h ∩ {p | c < qExtension h p}

theorem lowerDomain_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (c : ℝ) :
    IsOpen (lowerDomain h c) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hD := (domain_open h).mem_nhds hp.1
  have hq := (qExtension_smoothAt hh hh1 hp.1).continuousAt.eventually (Ioi_mem_nhds hp.2)
  filter_upwards [hD, hq] with q hDq hqq
  exact ⟨hDq, hqq⟩

/-- An actual open neighborhood across the endpoint, with an explicit
positive lower bound. The bound applies to the physical coordinate on its
past portion and to the smooth extension throughout the neighborhood. -/
theorem endpoint_neighborhood {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (s : ℝ) {z : ℝ} (hz : z ≠ 0) :
    ∃ U : Set PhysicalPoint, IsOpen U ∧ (1, (s, z)) ∈ U ∧ U ⊆ domain h ∧
      ContDiffOn ℝ ∞ (chartExtension h) U ∧
      0 < endpointRoot (2 * h) z / 2 ∧
      ∀ p ∈ U, endpointRoot (2 * h) z / 2 < qExtension h p ∧
        (p.1 < 1 → endpointRoot (2 * h) z / 2 < SimilarityProfile.q h p) := by
  let U := lowerDomain h (endpointRoot (2 * h) z / 2)
  have hq := endpointRoot_pos (2 * h) hz
  have hu : (1, (s, z)) ∈ U := by
    refine ⟨endpoint_mem_domain hh hh1 s hz, ?_⟩
    change endpointRoot (2 * h) z / 2 < qExtension h (1, (s, z))
    rw [qExtension_endpoint hh hh1 s hz]
    linarith
  refine ⟨U, lowerDomain_open hh hh1 _, hu, inter_subset_left,
    (chartExtension_smoothOn hh hh1).mono inter_subset_left, half_pos hq, ?_⟩
  intro p hp
  refine ⟨hp.2, fun ht => ?_⟩
  rw [← qExtension_eq_physical hh hh1 ht]
  exact hp.2

/-! ## The actual Cartesian chart used by the slow base -/

noncomputable def cartesianDomain (h : ℝ) : Set ProblemStatement.SpaceTime :=
  (fun z => AxisymmetricFields.profilePoint z.1 z.2) ⁻¹' domain h

noncomputable def cartesianExtension (h : ℝ) (z : ProblemStatement.SpaceTime) : Chart :=
  chartExtension h (AxisymmetricFields.profilePoint z.1 z.2)

theorem cartesianDomain_open (h : ℝ) : IsOpen (cartesianDomain h) :=
  (domain_open h).preimage (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous

theorem cartesian_endpoint_mem {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : ProblemStatement.Space} (hx : x 2 ≠ 0) : (1, x) ∈ cartesianDomain h :=
  endpoint_mem_domain hh hh1 (AxisymmetricFields.radialEnergy x) hx

theorem cartesianExtension_smoothAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {z : ProblemStatement.SpaceTime} (hz : z ∈ cartesianDomain h) :
    ContDiffAt ℝ ∞ (cartesianExtension h) z :=
  (chartExtension_smoothAt hh hh1 hz).comp z AxisymmetricFields.contDiff_profilePoint.contDiffAt

theorem cartesianExtension_smoothOn {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ (cartesianExtension h) (cartesianDomain h) :=
  fun _ hz => (cartesianExtension_smoothAt hh hh1 hz).contDiffWithinAt

theorem cartesianExtension_pos {h : ℝ} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ cartesianDomain h) : 0 < (cartesianExtension h z).1 := qExtension_pos hz

theorem cartesianExtension_X_nonneg {h : ℝ} {z : ProblemStatement.SpaceTime}
    (hz : z ∈ cartesianDomain h) : 0 ≤ (cartesianExtension h z).2.1 :=
  div_nonneg (AxisymmetricFields.radialEnergy_nonneg z.2) (qExtension_pos hz).le

theorem cartesianExtension_endpoint {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : ProblemStatement.Space} (hx : x 2 ≠ 0) :
    cartesianExtension h (1, x) =
      (endpointRoot (2 * h) (x 2),
        (AxisymmetricFields.radialEnergy x / endpointRoot (2 * h) (x 2),
          x 2 / endpointRoot (2 * h) (x 2) ^ ((1 - 2 * h) / 2))) :=
  chartExtension_endpoint hh hh1 (AxisymmetricFields.radialEnergy x) hx

theorem cartesianExtension_eq_physical {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {z : ProblemStatement.SpaceTime} (hz : z.1 < 1) :
    cartesianExtension h z = SlowBorelBase.cartesianChart h z :=
  chartExtension_eq_physical hh hh1 hz

theorem cartesianExtension_eventuallyEq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {z : ProblemStatement.SpaceTime} (hz : z.1 < 1) :
    cartesianExtension h =ᶠ[𝓝 z] SlowBorelBase.cartesianChart h := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with p hp
  exact cartesianExtension_eq_physical hh hh1 hp

/-- Equality is for arbitrary orders of the genuine space-time derivative. -/
theorem cartesianExtension_jets_eq {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {z : ProblemStatement.SpaceTime} (hz : z.1 < 1) (n : ℕ) :
    iteratedFDeriv ℝ n (cartesianExtension h) z =
      iteratedFDeriv ℝ n (SlowBorelBase.cartesianChart h) z :=
  jets_eq_of_eventuallyEq (cartesianExtension_eventuallyEq hh hh1 hz) n

theorem cartesian_endpoint_neighborhood {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {x : ProblemStatement.Space} (hx : x 2 ≠ 0) :
    ∃ U : Set ProblemStatement.SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧ U ⊆ cartesianDomain h ∧
      ContDiffOn ℝ ∞ (cartesianExtension h) U ∧
      0 < endpointRoot (2 * h) (x 2) / 2 ∧
      ∀ z ∈ U, endpointRoot (2 * h) (x 2) / 2 < (cartesianExtension h z).1 ∧
        (z.1 < 1 → endpointRoot (2 * h) (x 2) / 2 < (SlowBorelBase.cartesianChart h z).1) := by
  obtain ⟨V, hV, hxV, hVD, hsmooth, hq, hb⟩ :=
    endpoint_neighborhood hh hh1 (AxisymmetricFields.radialEnergy x) hx
  let P := fun z : ProblemStatement.SpaceTime => AxisymmetricFields.profilePoint z.1 z.2
  refine ⟨P ⁻¹' V, hV.preimage (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous,
    hxV, fun z hz => hVD hz, ?_, hq, ?_⟩
  · exact (cartesianExtension_smoothOn hh hh1).mono (fun z hz => hVD hz)
  · intro z hz
    refine ⟨(hb (P z) hz).1, fun ht => ?_⟩
    rw [← cartesianExtension_eq_physical hh hh1 ht]
    exact (hb (P z) hz).1

/-! ## Smooth composition and genuine derivative transfer -/

theorem composition_smoothAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ cartesianDomain h) {f : Chart → V}
    (hf : ContDiffAt ℝ ∞ f (cartesianExtension h z)) :
    ContDiffAt ℝ ∞ (fun p => f (cartesianExtension h p)) z :=
  hf.comp z (cartesianExtension_smoothAt hh hh1 hz)

theorem composition_endpoint_smoothAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) {x : ProblemStatement.Space}
    (hx : x 2 ≠ 0) {f : Chart → V}
    (hf : ContDiffAt ℝ ∞ f (cartesianExtension h (1, x))) :
    ContDiffAt ℝ ∞ (fun p => f (cartesianExtension h p)) (1, x) :=
  composition_smoothAt hh hh1 (cartesian_endpoint_mem hh hh1 hx) hf

theorem composition_jets_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (f : Chart → V)
    {z : ProblemStatement.SpaceTime} (hz : z.1 < 1) (n : ℕ) :
    iteratedFDeriv ℝ n (fun p => f (cartesianExtension h p)) z =
      iteratedFDeriv ℝ n (fun p => f (SlowBorelBase.cartesianChart h p)) z := by
  apply jets_eq_of_eventuallyEq _ n
  filter_upwards [cartesianExtension_eventuallyEq hh hh1 hz] with p hp
  exact congrArg f hp

end NavierStokes.EndpointCoordinates
