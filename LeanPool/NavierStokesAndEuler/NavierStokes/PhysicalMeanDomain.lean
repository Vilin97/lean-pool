/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanRankUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanIncrementBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.TemporalMeanUpdate
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Mean reconstruction on an open slow domain

Radial transport and torus integration preserve the slow parameter.  The
operators in this file are the actual operators from `PressureStream` and
`TemporalMeanUpdate`, restricted to an open slow domain.  Cutoffs are used only
to prove local smoothness and equality of germs; none of their derivatives
enters the uniform estimates.
-/

noncomputable section

namespace NavierStokes.PhysicalMeanDomain

open Set Function MeasureTheory Filter
open scoped ContDiff Topology Interval BigOperators
open WeightedClasses WeightedRadialPrimitive


variable {S V : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- All radii and torus variables, with only the slow parameter restricted. -/
noncomputable def slowDomain (U : Set S) : Set (PressureStream.Lift S) :=
  {p | p.2.1 ∈ U}

omit [NormedSpace ℝ S] in
theorem slowDomain_open {U : Set S} (hU : IsOpen U) : IsOpen (slowDomain U) :=
  hU.preimage (continuous_fst.comp continuous_snd)

noncomputable def stripDomain (a b : ℝ) (U : Set S) : Set (PressureStream.Lift S) :=
  {p | p.1 ∈ Ioo a b ∧ p.2.1 ∈ U}

omit [NormedSpace ℝ S] in
theorem stripDomain_open (a b : ℝ) {U : Set S} (hU : IsOpen U) :
    IsOpen (stripDomain a b U) :=
  (isOpen_Ioo.preimage continuous_fst).inter (slowDomain_open hU)

/-- Restriction changes only the domain, leaving all weights and band scales. -/
noncomputable def localStripData (a b cL cR : ℝ) (ha : 0 < a)
    (hcL : 0 < cL) (hcR : 0 < cR) (ε L : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) : StripData (PressureStream.Lift S) :=
  { logStripData a b cL cR ha hcL hcR ε L hε hεone hL with
    domain := stripDomain a b U
    isOpen_domain := stripDomain_open a b hU
    delta_pos := fun _ hp => delta_pos (logPosition_mem ha hp.1)
    zeta_smooth := (logStripData a b cL cR ha hcL hcR ε L hε hεone hL).zeta_smooth.mono
      (fun _ hp => hp.1)
    zeta_nonneg := fun _ hp => (zeta_pos cL cR (logPosition_mem ha hp.1)).le }

theorem localStrip_majorant_eq
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) (α C : ℝ) (k n : ℕ) (p : PressureStream.Lift S)
    (hp : p.1 ∈ Ioo a b) :
    majorant (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU)
      (fun _ x => (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU).zeta x)
      α C k n p = (C * ε n ^ α * L n ^ k) * logWeight cL cR a b k p.1 :=
  logStrip_majorant_eq ha hcL hcR ε L hε hεone hL α C k n p hp

/-- Radial support is required only at slow parameters where the source is used. -/
noncomputable def SupportedOn (a b : ℝ) (U : Set S) (f : PressureStream.Lift S → V) : Prop :=
  ∀ p, p.2.1 ∈ U → f p ≠ 0 → p.1 ∈ Icc a b

noncomputable def PeriodicOn (U : Set S) (f : PressureStream.Lift S → ℝ) : Prop :=
  ∀ r s, s ∈ U → FourierAlias.TorusPeriodic (fun Y => f (r, (s, Y)))

/-- The germ of a source on one entire slow fiber, including a slow neighborhood. -/
noncomputable def FiberGerm (s : S) (f g : PressureStream.Lift S → V) : Prop :=
  ∀ᶠ t in 𝓝 s, ∀ r Y, f (r, (t, Y)) = g (r, (t, Y))

omit [NormedSpace ℝ S] [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem FiberGerm.eventuallyEq {s : S} {f g : PressureStream.Lift S → V}
  (h : FiberGerm s f g) (r : ℝ) (Y : PressureStream.Plane) :
    f =ᶠ[𝓝 (r, (s, Y))] g := by
  have hm : Tendsto (fun p : PressureStream.Lift S => p.2.1) (𝓝 (r, (s, Y))) (𝓝 s) :=
    continuous_snd.fst.continuousAt
  filter_upwards [hm.eventually h] with p hp
  exact hp p.1 p.2.2

theorem FiberGerm.jet_eq {s : S} {f g : PressureStream.Lift S → V}
    (h : FiberGerm s f g) (j : ℕ) (r : ℝ) (Y : PressureStream.Plane) :
    iteratedFDeriv ℝ j f (r, (s, Y)) = iteratedFDeriv ℝ j g (r, (s, Y)) :=
  by
    have he := h.eventuallyEq r Y
    have hw : f =ᶠ[𝓝[univ] (r, (s, Y))] g := by simpa only [nhdsWithin_univ] using he
    simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq he.self_of_nhds j

/-- An auxiliary localization, used only for germs. -/
noncomputable def localize (c : S → ℝ) (f : PressureStream.Lift S → V) (p : PressureStream.Lift S)
  : V :=
  c p.2.1 • f p

theorem localize_smooth {U : Set S} (hU : IsOpen U) {c : S → ℝ}
    (hc : ContDiff ℝ ∞ c) (hcs : tsupport c ⊆ U) {f : PressureStream.Lift S → V}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) : ContDiff ℝ ∞ (localize c f) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.2.1 ∈ tsupport c
  · exact ((hc.comp (contDiff_fst.comp contDiff_snd)).contDiffAt).smul
      (hf.contDiffAt ((slowDomain_open hU).mem_nhds (hcs hp)))
  · have hz : c =ᶠ[𝓝 p.2.1] 0 := (notMem_tsupport_iff_eventuallyEq.mp hp)
    have he : localize c f =ᶠ[𝓝 p] fun _ => 0 := by
      have hm : Tendsto (fun q : PressureStream.Lift S => q.2.1) (𝓝 p) (𝓝 p.2.1) :=
        continuous_snd.fst.continuousAt
      filter_upwards [hm.eventually hz] with q hq
      simp only [localize, hq, Pi.zero_apply, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he

omit [NormedSpace ℝ S] in
theorem localize_supported {a b : ℝ} {U : Set S} {c : S → ℝ}
    (hcs : tsupport c ⊆ U) {f : PressureStream.Lift S → V} (hs : SupportedOn a b U f) :
    RadialAlias.RadiallySupported a b (localize c f) := by
  intro p hp
  have hc : c p.2.1 ≠ 0 := by intro hz; exact hp (by simp [localize, hz])
  have hf : f p ≠ 0 := by intro hz; exact hp (by simp [localize, hz])
  exact hs p (hcs (subset_tsupport c hc)) hf

omit [NormedSpace ℝ S] in
theorem localize_periodic {U : Set S} {c : S → ℝ}
    (hcs : tsupport c ⊆ U) {f : PressureStream.Lift S → ℝ} (hp : PeriodicOn U f) :
    PressureStream.TorusPeriodicLift (localize c f) := by
  intro r s Y k
  by_cases hc : c s = 0
  · simp [localize, hc]
  · simp only [localize, hp r s (hcs (subset_tsupport c hc)) Y k]

theorem exists_fiber_localization [FiniteDimensional ℝ S]
    {U : Set S} (hU : IsOpen U) {s : S} (hs : s ∈ U) {f : PressureStream.Lift S → V}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) :
    ∃ c : S → ℝ, ContDiff ℝ ∞ c ∧ tsupport c ⊆ U ∧
      ContDiff ℝ ∞ (localize c f) ∧ FiberGerm s (localize c f) f := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hs)
  let c : ContDiffBump s :=
    { rIn := ρ / 4, rOut := ρ / 2, rIn_pos := by positivity,
      rIn_lt_rOut := by linarith }
  have hcs : tsupport c ⊆ U := by
    rw [c.tsupport_eq]
    intro t ht
    exact hball ((Metric.closedBall_subset_ball (by dsimp [c]; linarith)) ht)
  refine ⟨c, c.contDiff, hcs, localize_smooth hU c.contDiff hcs hf, ?_⟩
  filter_upwards [c.eventuallyEq_one] with t ht
  intro r Y
  simp only [localize, ht, Pi.one_apply, one_smul]

/-- Freezing the slow parameter never changes a radial transport integral on
that fiber.  It does not freeze any jet appearing in the integrand. -/
noncomputable def freezeSlow (s : S) (f : PressureStream.Lift S → V) (p : PressureStream.Lift S) :
  V :=
  f (p.1, (s, p.2.2))

omit [NormedSpace ℝ S] [NormedSpace ℝ V] in
theorem freezeSlow_continuous {f : PressureStream.Lift S → V} (hf : Continuous f) (s : S) :
    Continuous (freezeSlow s f) :=
  hf.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd.snd))

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [NormedSpace ℝ V] in
theorem freezeSlow_supported {a b : ℝ} {f : PressureStream.Lift S → V}
    (hs : RadialAlias.RadiallySupported a b f) (s : S) :
    RadialAlias.RadiallySupported a b (freezeSlow s f) := by
  intro p hp
  have hf : (p.1, (s, p.2.2)) ∈ support f := hp
  exact @hs (p.1, (s, p.2.2)) hf

theorem pastIntegral_freeze (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → V)
    (p : PressureStream.Lift S) :
    TransportPrimitive.pastIntegral M (0, v) (freezeSlow p.2.1 f) p =
      TransportPrimitive.pastIntegral M (0, v) f p := by
  rcases p with ⟨r, s, Y⟩
  simp [TransportPrimitive.pastIntegral, TransportPrimitive.shift, freezeSlow]

theorem totalIntegral_freeze (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → V)
    (p : PressureStream.Lift S) :
    TransportPrimitive.totalIntegral M (0, v) (freezeSlow p.2.1 f) p =
      TransportPrimitive.totalIntegral M (0, v) f p := by
  rcases p with ⟨r, s, Y⟩
  simp [TransportPrimitive.totalIntegral, TransportPrimitive.shift, freezeSlow]

theorem futureIntegral_freeze (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → V)
    (p : PressureStream.Lift S) :
    TransportPrimitive.futureIntegral M (0, v) (freezeSlow p.2.1 f) p =
      TransportPrimitive.futureIntegral M (0, v) f p := by
  rcases p with ⟨r, s, Y⟩
  simp [TransportPrimitive.futureIntegral, TransportPrimitive.shift, freezeSlow]

/-! ## Weighted estimates on one slow fiber -/

theorem transport_past_left_fiber {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane)
      (f : PressureStream.Lift S → V), Continuous f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      ∀ z : PressureStream.Lift S, z.1 ∈ Ioo a b →
      (∀ X ∈ Ioo a b, ∀ Y : PressureStream.Plane,
        ‖f (X, (z.2.1, Y))‖ ≤ A * logWeight cL cR a b k X) →
      logPosition a z.1 ≤ logLength a b / 2 →
      ‖TransportPrimitive.pastIntegral M (0, v) f z‖ ≤
        K * A * logWeight cL cR a b k z.1 := by
  obtain ⟨K, hK, hb⟩ := transport_past_left_uniform (E := S × PressureStream.Plane)
    (V := V) ha hab hcL hcR k
  refine ⟨K, hK, ?_⟩
  intro M v f hf hs A hA z hz hbound hh
  have he := hb M (0, v) (freezeSlow z.2.1 f) (freezeSlow_continuous hf _)
    (freezeSlow_supported hs _) A hA (fun X hX Y => hbound X hX Y.2) z hz hh
  simpa only [pastIntegral_freeze] using he

theorem transport_future_right_fiber {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane)
      (f : PressureStream.Lift S → V), Continuous f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      ∀ z : PressureStream.Lift S, z.1 ∈ Ioo a b →
      (∀ X ∈ Ioo a b, ∀ Y : PressureStream.Plane,
        ‖f (X, (z.2.1, Y))‖ ≤ A * logWeight cL cR a b k X) →
      logLength a b / 2 ≤ logPosition a z.1 →
      ‖TransportPrimitive.futureIntegral M (0, v) f z‖ ≤
        K * A * logWeight cL cR a b k z.1 := by
  obtain ⟨K, hK, hb⟩ := transport_future_right_uniform (E := S × PressureStream.Plane)
    (V := V) ha hab hcL hcR k
  refine ⟨K, hK, ?_⟩
  intro M v f hf hs A hA z hz hbound hh
  have he := hb M (0, v) (freezeSlow z.2.1 f) (freezeSlow_continuous hf _)
    (freezeSlow_supported hs _) A hA (fun X hX Y => hbound X hX Y.2) z hz hh
  simpa only [futureIntegral_freeze] using he

theorem transport_mass_fiber {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane)
      (f : PressureStream.Lift S → V), Continuous f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A →
      ∀ z : PressureStream.Lift S, z.1 ∈ Ioo a b →
      (∀ X ∈ Ioo a b, ∀ Y : PressureStream.Plane,
        ‖f (X, (z.2.1, Y))‖ ≤ A * logWeight cL cR a b k X) →
      ‖TransportPrimitive.pastIntegral M (0, v) f z‖ ≤ K * A ∧
      ‖TransportPrimitive.totalIntegral M (0, v) f z‖ ≤ K * A := by
  obtain ⟨K, hK, hb⟩ := transport_mass_uniform (E := S × PressureStream.Plane)
    (V := V) ha hab hcL hcR k
  refine ⟨K, hK, ?_⟩
  intro M v f hf hs A hA z hz hbound
  have he := hb M (0, v) (freezeSlow z.2.1 f) (freezeSlow_continuous hf _)
    (freezeSlow_supported hs _) A hA (fun X hX Y => hbound X hX Y.2) z hz
  simpa only [pastIntegral_freeze, totalIntegral_freeze] using he

variable [CompleteSpace V]

theorem transport_compact_finiteJets_fiber
    {a b c d cL cR : ℝ} (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ)
    (hleft : ∀ X, X ≤ c → χ X = 0) (hright : ∀ X, d ≤ X → χ X = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → V), ContDiff
      ℝ ∞ f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A → ∀ s : S,
      (∀ j : ℕ, j ≤ m → ∀ X ∈ Ioo a b, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (X, (s, Y))‖ ≤ A * logWeight cL cR a b p X) →
      ∀ z : PressureStream.Lift S, z.1 ∈ Ioo a b → z.2.1 = s → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (TransportPrimitive.compactIntegral χ M (0, v) f) z‖ ≤
          K * A * logWeight cL cR a b p z.1 := by
  classical
  have hab : a < b := hac.trans (hcd.trans hdb)
  obtain ⟨ρ, hρ, hρL, hl, hr⟩ := exists_log_plateau_width ha hac hcd hdb χ hleft hright
  obtain ⟨d₀, hd₀, hmiddle⟩ := middle_weight_lower_bound
    (L := logLength a b) hcL hcR (half_pos hρ)
  obtain ⟨B, hB, hcut⟩ := cutoff_finiteJet_bound (E := S × PressureStream.Plane) a b χ hχ m
  choose KL hKL hbL using fun j : Fin (m + 1) =>
    transport_past_left_fiber (S := S)
      (V := ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => PressureStream.Lift S) V)
      ha hab hcL hcR p
  choose KR hKR hbR using fun j : Fin (m + 1) =>
    transport_future_right_fiber (S := S)
      (V := ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => PressureStream.Lift S) V)
      ha hab hcL hcR p
  choose DS hDS hbD using fun j : Fin (m + 1) =>
    transport_mass_fiber (S := S)
      (V := ContinuousMultilinearMap ℝ (fun _ : Fin (j : ℕ) => PressureStream.Lift S) V)
      ha hab hcL hcR p
  let L := ∑ j, KL j
  let R := ∑ j, KR j
  let D := ∑ j, DS j
  have hL : 0 ≤ L := Finset.sum_nonneg (fun j _ => hKL j)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun j _ => hKR j)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun j _ => hDS j)
  have hLL (j : Fin (m + 1)) : KL j ≤ L := Finset.single_le_sum (fun k _ => hKL k) (Finset.mem_univ
    j)
  have hRR (j : Fin (m + 1)) : KR j ≤ R := Finset.single_le_sum (fun k _ => hKR k) (Finset.mem_univ
    j)
  have hDD (j : Fin (m + 1)) : DS j ≤ D := Finset.single_le_sum (fun k _ => hDS k) (Finset.mem_univ
    j)
  let KM := D * (1 + (2 : ℝ) ^ m * B) / d₀
  have hKM : 0 ≤ KM := div_nonneg (mul_nonneg hD (by positivity)) hd₀.le
  let K := L + R + KM
  have hLK : L ≤ K := by dsimp [K]; linarith
  have hRK : R ≤ K := by dsimp [K]; linarith
  have hMK : KM ≤ K := by dsimp [K]; linarith
  refine ⟨K, hL.trans hLK, ?_⟩
  intro M v f hf hs A hA s hsource z hz hzs j hj
  subst s
  let j' : Fin (m + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hmass (i : ℕ) (hi : i ≤ m) :
      ‖TransportPrimitive.pastIntegral M (0, v) (iteratedFDeriv ℝ i f) z‖ ≤ D * A ∧
      ‖TransportPrimitive.totalIntegral M (0, v) (iteratedFDeriv ℝ i f) z‖ ≤ D * A := by
    let i' : Fin (m + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
    have h := hbD i' M v (iteratedFDeriv ℝ i f)
      (TransportPrimitive.iteratedFDeriv_contDiff hf i).continuous
      (TransportPrimitive.iteratedFDeriv_supported hs i) A hA z hz (hsource i hi)
    exact ⟨h.1.trans (mul_le_mul_of_nonneg_right (hDD i') hA),
      h.2.trans (mul_le_mul_of_nonneg_right (hDD i') hA)⟩
  have hw : 0 ≤ logWeight cL cR a b p z.1 :=
    (weight_pos cL cR p (logPosition_mem ha hz)).le
  by_cases hzl : logPosition a z.1 ≤ ρ / 2
  · rw [compact_jet_eq_past_on_left ha hl z (ha.trans hz.1) (by linarith) j,
      TransportPrimitive.iteratedFDeriv_pastIntegral hf hs]
    have h := hbL j' M v (iteratedFDeriv ℝ j f)
      (TransportPrimitive.iteratedFDeriv_contDiff hf j).continuous
      (TransportPrimitive.iteratedFDeriv_supported hs j) A hA z hz (hsource j hj) (by linarith)
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((hLL j').trans hLK) hA) hw)
  · by_cases hzr : logLength a b - ρ / 2 ≤ logPosition a z.1
    · rw [compact_jet_eq_neg_future_on_right ha hf.continuous hs hr z (ha.trans hz.1) (by linarith)
      j,
        norm_neg, TransportPrimitive.iteratedFDeriv_futureIntegral hf hs]
      have h := hbR j' M v (iteratedFDeriv ℝ j f)
        (TransportPrimitive.iteratedFDeriv_contDiff hf j).continuous
        (TransportPrimitive.iteratedFDeriv_supported hs j) A hA z hz (hsource j hj) (by linarith)
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ((hRR j').trans hRK) hA) hw)
    · have hwm : d₀ ≤ logWeight cL cR a b p z.1 :=
        hmiddle p (logPosition a z.1) ⟨le_of_not_ge hzl, le_of_not_ge hzr⟩
      have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y : PressureStream.Lift S => χ y.1) z‖ *
          ‖TransportPrimitive.totalIntegral M (0, v) (iteratedFDeriv ℝ (j - i) f) z‖) ≤
          (2 : ℝ) ^ j * B * (D * A) := by
        calc
          _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * (D * A) := by
            apply Finset.sum_le_sum
            intro i hi
            have him : i ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hj
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (hcut i him z ⟨hz.1.le, hz.2.le⟩) (Nat.cast_nonneg _))
              (hmass (j - i) ((Nat.sub_le j i).trans hj)).2 (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) hB)
          _ = (2 : ℝ) ^ j * B * (D * A) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            congr 2
            exact_mod_cast Nat.sum_range_choose j
      calc
        _ ≤ ‖TransportPrimitive.pastIntegral M (0, v) (iteratedFDeriv ℝ j f) z‖ +
            ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i (fun y : PressureStream.Lift S => χ y.1) z‖ *
              ‖TransportPrimitive.totalIntegral M (0, v) (iteratedFDeriv ℝ (j - i) f) z‖ :=
          TransportPrimitive.iteratedFDeriv_compactIntegral_norm_le hχ hf hs j z
        _ ≤ D * A + (2 : ℝ) ^ j * B * (D * A) := add_le_add (hmass j hj).1 hsum
        _ ≤ D * A + (2 : ℝ) ^ m * B * (D * A) := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hB)
              (mul_nonneg hD hA)) _
        _ = (D * (1 + (2 : ℝ) ^ m * B)) * A := by ring
        _ = KM * A * d₀ := by dsimp [KM]; field_simp
        _ ≤ KM * A * logWeight cL cR a b p z.1 :=
          mul_le_mul_of_nonneg_left hwm (mul_nonneg hKM hA)
        _ ≤ K * A * logWeight cL cR a b p z.1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hMK hA) hw

theorem canonical_transport_finiteJets_fiber
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane) (f : PressureStream.Lift S → V), ContDiff
      ℝ ∞ f →
      RadialAlias.RadiallySupported a b f → ∀ A : ℝ, 0 ≤ A → ∀ s : S,
      (∀ j : ℕ, j ≤ m → ∀ X ∈ Ioo a b, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j f (X, (s, Y))‖ ≤ A * logWeight cL cR a b p X) →
      ∀ z : PressureStream.Lift S, z.1 ∈ Ioo a b → z.2.1 = s → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j
          (TransportPrimitive.compactIntegral (TransportPrimitive.interiorCutoff a b) M (0, v) f)
            z‖ ≤
          K * A * logWeight cL cR a b p z.1 := by
  exact transport_compact_finiteJets_fiber (S := S) (V := V) ha
    (c := (2 * a + b) / 3) (d := (a + 2 * b) / 3)
    (by linarith) (by linarith) (by linarith) hcL hcR p m
    (TransportPrimitive.interiorCutoff a b) (TransportPrimitive.interiorCutoff_contDiff a b)
    (fun X hX => TransportPrimitive.interiorCutoff_zero hab hX)
    (fun X hX => TransportPrimitive.interiorCutoff_one hab hX)


open RadialPullback

omit [CompleteSpace V] in
theorem normalizeSource_finiteJets_fiber {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (cL cR : ℝ) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : PressureStream.Lift S → V), ContDiff ℝ ∞ g → ∀ A : ℝ, 0 ≤ A → ∀ s : S,
      (∀ j : ℕ, j ≤ m → ∀ R ∈ Ioo a b, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j g (R, (s, Y))‖ ≤ A * logWeight cL cR a b p R) →
      ∀ z : PressureStream.Lift S, z.1 ∈ Ioo (a ^ d) (b ^ d) → z.2.1 = s → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (normalizeSource d a g) z‖ ≤
          K * A * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p z.1 := by
  obtain ⟨KC, hKC, hbC⟩ := radial_comp_finiteJets_uniform (E := S × PressureStream.Plane) (V := V)
    (a ^ d) (b ^ d) (inverseChart_contDiff ha d) m
  obtain ⟨KM, hKM, hbM⟩ := radial_multiplier_finiteJets_uniform (E := S × PressureStream.Plane) (V
    := V)
    (a ^ d) (b ^ d) (sourceMultiplier_contDiff ha hd) m
  let Q := ((min 1 d⁻¹) ^ p)⁻¹
  have hQ : 0 ≤ Q := (inv_pos.mpr (pow_pos (lt_min zero_lt_one (inv_pos.mpr hd)) p)).le
  refine ⟨KM * KC * Q, mul_nonneg (mul_nonneg hKM hKC) hQ, ?_⟩
  intro g hg A hA s hsource z hz hzs j hj
  subst s
  have hr := inverseChart_mem ha hab hd hz
  have hw : 0 ≤ logWeight cL cR a b p (inverseChart d a z.1) :=
    (weight_pos cL cR p (logPosition_mem ha hr)).le
  have hcomp (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i (g ∘ liftChart (inverseChart d a)) z‖ ≤
        KC * (A * logWeight cL cR a b p (inverseChart d a z.1)) :=
    hbC g hg z ⟨hz.1.le, hz.2.le⟩ _ (mul_nonneg hA hw)
      (fun k hk => hsource k hk _ hr z.2.2) i hi
  have hmul := hbM (g ∘ liftChart (inverseChart d a))
    (hg.comp (liftChart_contDiff (inverseChart_contDiff ha d))) z ⟨hz.1.le, hz.2.le⟩
    (KC * (A * logWeight cL cR a b p (inverseChart d a z.1)))
    (mul_nonneg hKC (mul_nonneg hA hw)) hcomp j hj
  change ‖iteratedFDeriv ℝ j (normalizeSource d a g) z‖ ≤
    KM * (KC * (A * logWeight cL cR a b p (inverseChart d a z.1))) at hmul
  have hweight := logWeight_power_reverse ha hd hr cL cR p
  rw [inverseChart_rpow ha hd hz.1.le] at hweight
  calc
    _ ≤ KM * (KC * (A * logWeight cL cR a b p (inverseChart d a z.1))) := hmul
    _ ≤ KM * (KC * (A * (Q * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p z.1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hweight hA) hKC) hKM
    _ = (KM * KC * Q) * A * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p z.1 := by ring


/-- The complete physical inverse preserves the original exponential weight
and the same finite inverse-edge degree. All constants precede the arbitrary
transport shift, source, amplitude, and evaluation point. -/
theorem physicalCompact_finiteJets_fiber {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane) (g : PressureStream.Lift S → V), ContDiff
      ℝ ∞ g →
      RadialAlias.RadiallySupported a b g → ∀ A : ℝ, 0 ≤ A → ∀ s : S,
      (∀ j : ℕ, j ≤ m → ∀ R ∈ Ioo a b, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ j g (R, (s, Y))‖ ≤ A * logWeight cL cR a b p R) →
      ∀ z : PressureStream.Lift S, z.1 ∈ Ioo a b → z.2.1 = s → ∀ j : ℕ, j ≤ m →
        ‖iteratedFDeriv ℝ j (physicalCompact d a b M (0, v) g) z‖ ≤
          K * A * logWeight cL cR a b p z.1 := by
  have haU : 0 < a ^ d := Real.rpow_pos_of_pos ha d
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  have hcLU : 0 < d ^ 2 * cL := mul_pos (sq_pos_of_pos hd) hcL
  have hcRU : 0 < d ^ 2 * cR := mul_pos (sq_pos_of_pos hd) hcR
  obtain ⟨KN, hKN, hbN⟩ := normalizeSource_finiteJets_fiber (S := S) (V := V) ha hab hd cL cR p m
  obtain ⟨KT, hKT, hbT⟩ := canonical_transport_finiteJets_fiber (S := S) (V := V) haU habU hcLU
    hcRU p m
  obtain ⟨KP, hKP, hbP⟩ := radial_comp_finiteJets_uniform (E := S × PressureStream.Plane) (V := V)
    a b
    (powerChart_contDiff ha d) m
  let Q := ((min 1 d) ^ p)⁻¹
  have hQ : 0 ≤ Q := (inv_pos.mpr (pow_pos (lt_min zero_lt_one hd) p)).le
  refine ⟨KP * KT * KN * Q, mul_nonneg (mul_nonneg (mul_nonneg hKP hKT) hKN) hQ, ?_⟩
  intro M v g hg hs A hA s hsource z hz hzs j hj
  subst s
  have hnf := normalizeSource_contDiff ha hd hg
  have hns := normalizeSource_supported ha hab hd hs
  have hnsource : ∀ i : ℕ, i ≤ m → ∀ U ∈ Ioo (a ^ d) (b ^ d), ∀ Y : PressureStream.Plane,
      ‖iteratedFDeriv ℝ i (normalizeSource d a g) (U, (z.2.1, Y))‖ ≤
        (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p U :=
    fun i hi U hU Y => hbN g hg A hA z.2.1 hsource (U, (z.2.1, Y)) hU rfl i hi
  let F := TransportPrimitive.compactIntegral (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d))
    M (0, v) (normalizeSource d a g)
  have hF : ContDiff ℝ ∞ F := TransportPrimitive.compactIntegral_contDiff
    (TransportPrimitive.interiorCutoff_contDiff _ _) hnf hns
  have hU := powerChart_mem ha hd hz
  have hwU : 0 ≤ logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (powerChart d a z.1) :=
    (weight_pos _ _ p (logPosition_mem haU hU)).le
  have ht (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i F (liftChart (powerChart d a) z)‖ ≤
        KT * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (powerChart d a z.1)
          :=
    hbT M v _ hnf hns (KN * A) (mul_nonneg hKN hA) z.2.1 hnsource
      (liftChart (powerChart d a) z) hU rfl i hi
  have hp := hbP F hF z ⟨hz.1.le, hz.2.le⟩
    (KT * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (powerChart d a z.1))
    (mul_nonneg (mul_nonneg hKT (mul_nonneg hKN hA)) hwU) ht j hj
  change ‖iteratedFDeriv ℝ j (physicalCompact d a b M (0, v) g) z‖ ≤
    KP * (KT * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (powerChart d a
      z.1)) at hp
  rw [powerChart_eq ha (show a / 2 ≤ z.1 by linarith [hz.1]) d] at hp
  have hw := logWeight_power_forward ha hd hz cL cR p
  calc
    _ ≤ KP * (KT * (KN * A) * logWeight (d ^ 2 * cL) (d ^ 2 * cR) (a ^ d) (b ^ d) p (z.1 ^ d)) := hp
    _ ≤ KP * (KT * (KN * A) * (Q * logWeight cL cR a b p z.1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hw (mul_nonneg hKT (mul_nonneg hKN hA))) hKP
    _ = (KP * KT * KN * Q) * A * logWeight cL cR a b p z.1 := by ring


/-! ## The actual operators preserve slow fibers and their germs -/

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

noncomputable def FiberLocal
    (T : (PressureStream.Lift S → V) → PressureStream.Lift S → W) : Prop :=
  ∀ (f g : PressureStream.Lift S → V) (s : S),
    (∀ r Y, f (r, (s, Y)) = g (r, (s, Y))) →
    ∀ r Y, T f (r, (s, Y)) = T g (r, (s, Y))

omit [NormedSpace ℝ S] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace
  ℝ W] in
theorem FiberLocal.germ
    {T : (PressureStream.Lift S → V) → PressureStream.Lift S → W}
    (hT : FiberLocal T) {s : S} {f g : PressureStream.Lift S → V}
    (he : FiberGerm s f g) : FiberGerm s (T f) (T g) := by
  filter_upwards [he] with t ht
  exact hT f g t ht

omit [CompleteSpace V] in
theorem physicalCompact_fiberLocal (d a b M : ℝ) (v : PressureStream.Plane) :
    FiberLocal (V := V) (physicalCompact d a b M ((0 : S), v)) := by
  intro f g s he r Y
  simp [physicalCompact, pullback, Function.comp_apply, TransportPrimitive.compactIntegral,
    TransportPrimitive.pastIntegral, TransportPrimitive.totalIntegral, normalizeSource,
    liftChart, TransportPrimitive.shift, he]

omit [CompleteSpace V] in
theorem physicalAlias_fiberLocal (d a b M : ℝ) (v : PressureStream.Plane) :
    FiberLocal (V := V) (physicalAlias d a b M ((0 : S), v)) := by
  intro f g s he r Y
  simp [physicalAlias, TransportPrimitive.totalIntegral, normalizeSource,
    liftChart, TransportPrimitive.shift, he]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem weightedSource_fiberLocal :
    FiberLocal (S := S) PressureStream.weightedSource := by
  intro f g s he r Y
  simp only [PressureStream.weightedSource, he]

theorem streamPotential_fiberLocal (d a b M : ℝ) (v : PressureStream.Plane) :
    FiberLocal (PressureStream.streamPotential d a b M ((0 : S), v)) := by
  intro f g s he r Y
  exact congrArg (fun x : ℝ => x / r)
    (physicalCompact_fiberLocal d a b M v _ _ s
      (weightedSource_fiberLocal f g s he) r Y)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem liftedTorusAverage_fiberLocal :
    FiberLocal (S := S) MeanMomentBounds.liftedTorusAverage := by
  intro f g s he r Y
  exact PressureStream.torusAverage_congr_slice (r, s) (he r)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem liftedPressureMass_fiberLocal :
    FiberLocal (S := S) MeanMomentBounds.liftedPressureMass := by
  intro f g s he r Y
  apply integral_congr_ae
  exact Eventually.of_forall fun x => PressureStream.torusAverage_congr_slice (x, s) (he x)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem pressureSource_fiberLocal (a b : ℝ) (hab : a < b) :
    FiberLocal (S := S) (PressureStream.pressureSource a b hab) := by
  intro f g s he r Y
  simp only [PressureStream.pressureSource, he]
  rw [show PressureStream.pressureMass f s = PressureStream.pressureMass g s from
    liftedPressureMass_fiberLocal f g s he r Y]

theorem meanPressure_fiberLocal (d a b M : ℝ) (hab : a < b) (v : PressureStream.Plane) :
    FiberLocal (S := S) (PressureStream.meanPressure d a b M hab v) := by
  intro f g s he r Y
  exact physicalCompact_fiberLocal d a b M v _ _ s (pressureSource_fiberLocal a b hab f g s he) r Y

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem centered_fiberLocal : FiberLocal (S := S) TemporalMeanUpdate.centered := by
  intro f g s he r Y
  exact congrArg₂ (fun x y : ℝ => x - y) (he r Y)
    (liftedTorusAverage_fiberLocal f g s he r Y)

section LocalSmoothness

variable [FiniteDimensional ℝ S]

omit [CompleteSpace V] in
/-- A proved fiber-local operator transfers its global smoothness theorem to
local input data.  No global extension is an input to this theorem. -/
theorem FiberLocal.contDiffOn_of_supported
    {T : (PressureStream.Lift S → V) → PressureStream.Lift S → W}
    (hT : FiberLocal T) {a b : ℝ}
    (hTs : ∀ f, ContDiff ℝ ∞ f → RadialAlias.RadiallySupported a b f → ContDiff ℝ ∞ (T f))
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → V}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (T f) (slowDomain U) := by
  intro p hp
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp hf
  exact ((hTs _ hcf (localize_supported hcs hs)).contDiffAt.congr_of_eventuallyEq
    ((hT.germ he).eventuallyEq p.1 p.2.2).symm).contDiffWithinAt

theorem physicalCompact_contDiffOn {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → V}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (physicalCompact d a b M ((0 : S), v) f) (slowDomain U) :=
  (physicalCompact_fiberLocal d a b M v).contDiffOn_of_supported
    (fun _ h hc => physicalCompact_contDiff ha hab hd h hc M (0, v)) hU hf hs

theorem physicalAlias_contDiffOn {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → V}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (physicalAlias d a b M ((0 : S), v) f) (slowDomain U) :=
  (physicalAlias_fiberLocal d a b M v).contDiffOn_of_supported
    (fun _ h hc => physicalAlias_contDiff ha hab hd h hc M (0, v)) hU hf hs

theorem streamPotential_contDiffOn {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (PressureStream.streamPotential d a b M ((0 : S), v) f) (slowDomain U) :=
  (streamPotential_fiberLocal d a b M v).contDiffOn_of_supported
    (fun _ h hc => PressureStream.streamPotential_contDiff ha hab hd (0, v) h hc) hU hf hs

theorem meanPressure_contDiffOn {d a b M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (PressureStream.meanPressure d a b M hab v f) (slowDomain U) :=
  (meanPressure_fiberLocal d a b M hab v).contDiffOn_of_supported
    (fun _ h hc => PressureStream.meanPressure_contDiff ha hab hd v h hc) hU hf hs

theorem liftedPressureMass_contDiffOn {a b : ℝ}
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (MeanMomentBounds.liftedPressureMass f) (slowDomain U) :=
  liftedPressureMass_fiberLocal.contDiffOn_of_supported
    (fun _ h hc => MeanMomentBounds.liftedPressureMass_contDiff h hc) hU hf hs

theorem meanClass_physicalCompact {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) (α : ℝ) (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane)
    (f : ℕ → PressureStream.Lift S → V)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => physicalCompact d a b (M n) ((0 : S), v n) (f n)) := by
  refine ⟨hclass.weight_nonneg, ?_, ?_⟩
  · intro n
    exact (physicalCompact_contDiffOn ha hab hd (v n) hU (hf n) (hs n)).mono (fun _ hp => hp.2)
  · intro m
    obtain ⟨C, hC, k, hb⟩ := hclass.bounds m
    obtain ⟨K, hK, hbound⟩ := physicalCompact_finiteJets_fiber (S := S) (V := V) ha hab hd hcL hcR
      k m
    refine ⟨K * C, mul_nonneg hK hC, k, ?_⟩
    intro n p hp j hj
    obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp.2 (hf n)
    have hA : 0 ≤ C * ε n ^ α * L n ^ k :=
      mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
        (pow_nonneg (zero_le_one.trans (hL n)) _)
    have hin : ∀ i ≤ m, ∀ R ∈ Ioo a b, ∀ Y : PressureStream.Plane,
        ‖iteratedFDeriv ℝ i (localize c (f n)) (R, (p.2.1, Y))‖ ≤
          (C * ε n ^ α * L n ^ k) * logWeight cL cR a b k R := by
      intro i hi R hR Y
      rw [he.jet_eq i R Y]
      have h := hb n (R, (p.2.1, Y)) ⟨hR, hp.2⟩ i hi
      rwa [localStrip_majorant_eq ha hcL hcR ε L hε hεone hL U hU α C k n _ hR] at h
    have hout := hbound (M n) (v n) _ hcf (localize_supported hcs (hs n))
      (C * ε n ^ α * L n ^ k) hA p.2.1 hin p hp.1 rfl j hj
    rw [(physicalCompact_fiberLocal d a b (M n) (v n)).germ he |>.jet_eq j p.1 p.2.2] at hout
    rw [localStrip_majorant_eq ha hcL hcR ε L hε hεone hL U hU α (K * C) k n p hp.1]
    exact hout.trans_eq (by ring)

end LocalSmoothness

section AffineIntegral

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Compact integration needs local domination only, not a bound on all
parameters.  This identity differentiates the literal affine average. -/
theorem iteratedFDeriv_affineAverage (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    (v : E) {a b : ℝ} (hab : a ≤ b) {f : E → F} (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (x : D) :
    iteratedFDeriv ℝ j (MeanMomentBounds.affineAverage L v a b f) x =
      ∫ t in a..b, iteratedFDeriv ℝ j (fun y => f (L y + t • v)) x := by
  let μ := volume.restrict (Ioc a b)
  let g : D → ℝ → F := fun y t => f (L y + t • v)
  have hsm : ∀ᵐ t ∂μ, ContDiff ℝ ∞ (fun y => g y t) :=
    Eventually.of_forall fun t => hf.comp (L.contDiff.add contDiff_const)
  have hm : ∀ k y, AEStronglyMeasurable (SmoothParameterIntegral.jet g k y) μ := by
    intro k y
    have hc : Continuous (fun t : ℝ =>
        (iteratedFDeriv ℝ k f (L y + t • v)).compContinuousLinearMap (fun _ => L)) :=
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => L)).continuous.comp
        ((hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).comp
          (continuous_const.add (continuous_id.smul continuous_const)))
    have he : SmoothParameterIntegral.jet g k y = fun t : ℝ =>
        (iteratedFDeriv ℝ k f (L y + t • v)).compContinuousLinearMap (fun _ => L) :=
      funext fun t => MeanMomentBounds.iteratedFDeriv_affine L (t • v) hf k y
    rw [he]
    exact hc.aestronglyMeasurable
  have hd : SmoothParameterIntegral.LocallyDominated g μ := by
    intro k y
    have hc : Continuous (fun q : D × ℝ => iteratedFDeriv ℝ k f (L q.1 + q.2 • v)) :=
      (hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).comp
        ((L.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const))
    obtain ⟨δ, hδ, C, hC⟩ := TransportPrimitive.uniform_local_bound hc y a b
    refine ⟨δ, hδ, fun _ => C, integrable_const _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro z hz
    exact (MeanMomentBounds.norm_iteratedFDeriv_affine_le L hL (t • v) hf k z).trans
      (hC z hz t (by simpa only [uIcc_of_le hab] using Ioc_subset_Icc_self ht))
  have he := SmoothParameterIntegral.iteratedFDeriv_integral hsm hm hd j x
  have hg : MeanMomentBounds.affineAverage L v a b f = fun y => ∫ t, g y t ∂μ := by
    funext y
    exact intervalIntegral.integral_of_le hab
  rw [hg]
  simpa only [μ, g, ← intervalIntegral.integral_of_le hab] using he

omit [CompleteSpace F] in
theorem affineAverage_jet_bound (L : D →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    (v : E) {a b : ℝ} (hab : a ≤ b) {f : E → F} (hf : ContDiff ℝ ∞ f)
    (j : ℕ) (x : D) (C : ℝ)
    (hC : ∀ t ∈ Icc a b, ‖iteratedFDeriv ℝ j f (L x + t • v)‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (MeanMomentBounds.affineAverage L v a b f) x‖ ≤ C * (b - a) := by
  rw [iteratedFDeriv_affineAverage L hL v hab hf]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (fun t ht => (MeanMomentBounds.norm_iteratedFDeriv_affine_le L hL (t • v) hf j x).trans
      (hC t (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht)))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h

end AffineIntegral

theorem liftedTorusAverage_jet_bound {f : PressureStream.Lift S → ℝ}
    (hf : ContDiff ℝ ∞ f) (j : ℕ) (p : PressureStream.Lift S) (C : ℝ)
    (hb : ∀ Y, ‖iteratedFDeriv ℝ j f (p.1, (p.2.1, Y))‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (MeanMomentBounds.liftedTorusAverage f) p‖ ≤ C := by
  rw [MeanMomentBounds.liftedTorusAverage_eq_affine]
  have hi := affineAverage_jet_bound (MeanMomentBounds.eraseAuxY (P := S))
    (MeanMomentBounds.norm_eraseAuxY_le (P := S))
    (MeanMomentBounds.auxY (P := S)) zero_le_one
    (MeanMomentBounds.affineAverage_contDiff (MeanMomentBounds.eraseAuxX (P := S))
      (MeanMomentBounds.auxX (P := S)) 0 1 hf)
    j p C
  simp only [sub_zero, mul_one] at hi
  apply hi
  intro t ht
  rw [MeanMomentBounds.eraseAuxY_add_smul]
  have hh := affineAverage_jet_bound (MeanMomentBounds.eraseAuxX (P := S))
    (MeanMomentBounds.norm_eraseAuxX_le (P := S))
    (MeanMomentBounds.auxX (P := S)) zero_le_one hf j (p.1, (p.2.1, (p.2.2.1, t))) C
    (fun u _ => by simpa only [MeanMomentBounds.eraseAuxX_add_smul] using hb (u, t))
  simpa only [sub_zero, mul_one] using hh

section LocalClasses

variable [FiniteDimensional ℝ S]

omit [CompleteSpace V] in
theorem FiberLocal.contDiffOn
    {T : (PressureStream.Lift S → V) → PressureStream.Lift S → W}
    (hT : FiberLocal T) (hTs : ∀ f, ContDiff ℝ ∞ f → ContDiff ℝ ∞ (T f))
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → V}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) :
    ContDiffOn ℝ ∞ (T f) (slowDomain U) := by
  intro p hp
  obtain ⟨c, _, _, hcf, he⟩ := exists_fiber_localization hU hp hf
  exact ((hTs _ hcf).contDiffAt.congr_of_eventuallyEq
    ((hT.germ he).eventuallyEq p.1 p.2.2).symm).contDiffWithinAt

theorem FiberLocal.contDiffOn_of_periodic
    {T : (PressureStream.Lift S → ℝ) → PressureStream.Lift S → ℝ}
    (hT : FiberLocal T)
    (hTs : ∀ f, ContDiff ℝ ∞ f → PressureStream.TorusPeriodicLift f → ContDiff ℝ ∞ (T f))
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hp : PeriodicOn U f) :
    ContDiffOn ℝ ∞ (T f) (slowDomain U) := by
  intro p hpu
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hpu hf
  exact ((hTs _ hcf (localize_periodic hcs hp)).contDiffAt.congr_of_eventuallyEq
    ((hT.germ he).eventuallyEq p.1 p.2.2).symm).contDiffWithinAt

omit [CompleteSpace V] [NormedSpace ℝ W] in
theorem FiberLocal.supportedOn
    {T : (PressureStream.Lift S → V) → PressureStream.Lift S → W}
    (hT : FiberLocal T) {a b : ℝ}
    (hTs : ∀ f, ContDiff ℝ ∞ f → RadialAlias.RadiallySupported a b f →
      RadialAlias.RadiallySupported a b (T f))
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → V}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    SupportedOn a b U (T f) := by
  intro p hp hn
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp hf
  have heq := ((hT.germ he).eventuallyEq p.1 p.2.2).self_of_nhds
  have hne : T (localize c f) p ≠ 0 := by simpa only [heq] using hn
  exact hTs _ hcf (localize_supported hcs hs) hne

theorem liftedTorusAverage_contDiffOn {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U)) :
    ContDiffOn ℝ ∞ (MeanMomentBounds.liftedTorusAverage f) (slowDomain U) :=
  liftedTorusAverage_fiberLocal.contDiffOn
    (fun _ h => MeanMomentBounds.liftedTorusAverage_contDiff h) hU hf

theorem liftedTorusAverage_supportedOn {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U))
    (hs : SupportedOn a b U f) :
    SupportedOn a b U (MeanMomentBounds.liftedTorusAverage f) :=
  liftedTorusAverage_fiberLocal.supportedOn
    (fun _ _ h => MeanMomentBounds.liftedTorusAverage_supported h) hU hf hs

theorem centered_contDiffOn {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U)) :
    ContDiffOn ℝ ∞ (TemporalMeanUpdate.centered f) (slowDomain U) :=
  centered_fiberLocal.contDiffOn (fun _ h => TemporalMeanUpdate.centered_smooth h) hU hf

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem centered_periodicOn {U : Set S} {f : PressureStream.Lift S → ℝ}
    (hp : PeriodicOn U f) : PeriodicOn U (TemporalMeanUpdate.centered f) := by
  intro r s hs Y k
  exact congrArg (fun x => x - PressureStream.torusAverage f (r, s)) (hp r s hs Y k)

theorem meanClass_liftedTorusAverage {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => MeanMomentBounds.liftedTorusAverage (f n)) := by
  refine ⟨hclass.weight_nonneg,
    fun n => (liftedTorusAverage_contDiffOn hU (hf n)).mono (fun _ hp => hp.2), ?_⟩
  intro m
  obtain ⟨C, hC, k, hb⟩ := hclass.bounds m
  refine ⟨C, hC, k, ?_⟩
  intro n p hp j hj
  obtain ⟨c, _, _, hcf, he⟩ := exists_fiber_localization hU hp.2 (hf n)
  have hout := liftedTorusAverage_jet_bound hcf j p
    (majorant (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU)
      (fun _ x => (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU).zeta x)
      α C k n p) (fun Y => by
        rw [he.jet_eq j p.1 Y]
        exact hb n (p.1, (p.2.1, Y)) hp j hj)
  rwa [(liftedTorusAverage_fiberLocal.germ he).jet_eq j p.1 p.2.2] at hout

theorem meanClass_centered {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => TemporalMeanUpdate.centered (f n)) :=
  MeanIncrementBounds.Class.sub hclass
    (meanClass_liftedTorusAverage ha hcL hcR ε L hε hεone hL U hU hf hclass)

omit [CompleteSpace V] in
theorem jet_zero_outside {a b : ℝ} {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → V} (hf : ContDiffOn ℝ ∞ f (slowDomain U))
    (hs : SupportedOn a b U f) {p : PressureStream.Lift S} (hp : p.2.1 ∈ U)
    (hr : p.1 ∉ Ioo a b) (j : ℕ) : iteratedFDeriv ℝ j f p = 0 := by
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp hf
  rw [← he.jet_eq j p.1 p.2.2]
  exact MeanMomentBounds.supported_zero_outside_open
    (TransportPrimitive.iteratedFDeriv_contDiff hcf j).continuous
    (TransportPrimitive.iteratedFDeriv_supported (localize_supported hcs hs) j) hr

/-- Uniform band jets on the valid slow domain, including all radial edges. -/
noncomputable def LocalBandJets (U : Set S) (ε L : ℕ → ℝ) (α : ℝ)
    (f : ℕ → PressureStream.Lift S → V) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n p, p.2.1 ∈ U → ∀ j ≤ m,
    ‖iteratedFDeriv ℝ j (f n) p‖ ≤ C * ε n ^ α * L n ^ k

omit [CompleteSpace V] in
theorem meanClass_localBandJets {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → V}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    LocalBandJets U ε L α f := by
  intro m
  obtain ⟨C, hC, k, hb⟩ := hclass.bounds m
  obtain ⟨B, hB, hweight⟩ := weight_uniform_bound hcL hcR (logLength a b) k
  refine ⟨C * B, mul_nonneg hC hB, k, ?_⟩
  intro n p hp j hj
  have hA : 0 ≤ C * ε n ^ α * L n ^ k :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) _)
  by_cases hr : p.1 ∈ Ioo a b
  · have he := hb n p ⟨hr, hp⟩ j hj
    rw [localStrip_majorant_eq ha hcL hcR ε L hε hεone hL U hU α C k n p hr] at he
    calc
      _ ≤ (C * ε n ^ α * L n ^ k) * logWeight cL cR a b k p.1 := he
      _ ≤ (C * ε n ^ α * L n ^ k) * B :=
        mul_le_mul_of_nonneg_left (hweight _ (logPosition_mem ha hr)) hA
      _ = _ := by ring
  · rw [jet_zero_outside hU (hf n) (hs n) hp hr j, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hB) (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) _)

end LocalClasses

omit [CompleteSpace V] in
theorem memClass_restrict {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {w : ℕ → PressureStream.Lift S → ℝ}
    {f : ℕ → PressureStream.Lift S → V}
    (hf : MemClass (logStripData a b cL cR ha hcL hcR ε L hε hεone hL) w α f) :
    MemClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) w α f := by
  refine ⟨fun n p hp => hf.weight_nonneg n p hp.1,
    fun n => (hf.smooth n).mono (fun _ hp => hp.1), ?_⟩
  intro m
  obtain ⟨C, hC, k, hb⟩ := hf.bounds m
  exact ⟨C, hC, k, fun n p hp j hj => hb n p hp.1 j hj⟩

theorem liftedPressureMass_jet_bound {a b : ℝ} (hab : a ≤ b)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (j : ℕ)
    (p : PressureStream.Lift S) (C : ℝ)
    (hb : ∀ R ∈ Icc a b, ∀ Y, ‖iteratedFDeriv ℝ j f (R, (p.2.1, Y))‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (MeanMomentBounds.liftedPressureMass f) p‖ ≤ C * (b - a) := by
  have hF := MeanMomentBounds.liftedTorusAverage_contDiff hf
  have hsF := MeanMomentBounds.liftedTorusAverage_supported hs
  rw [MeanMomentBounds.liftedPressureMass_eq, TransportPrimitive.iteratedFDeriv_totalIntegral hF
    hsF]
  have he := TransportPrimitive.totalIntegral_norm_le
    (M := 0) (v := ((0 : S), (0 : PressureStream.Plane))) hab
    (freezeSlow_continuous (TransportPrimitive.iteratedFDeriv_contDiff hF j).continuous p.2.1)
    (freezeSlow_supported (TransportPrimitive.iteratedFDeriv_supported hsF j) p.2.1)
    (fun R hR Y => liftedTorusAverage_jet_bound hf j (R, (p.2.1, Y.2)) C (hb R hR)) p
  simp only [totalIntegral_freeze] at he
  exact he

section PressureClasses

variable [FiniteDimensional ℝ S]

theorem LocalBandJets.liftedPressureMass {a b : ℝ} (hab : a ≤ b)
    {U : Set S} (hU : IsOpen U) {ε L : ℕ → ℝ} {α : ℝ}
    {f : ℕ → PressureStream.Lift S → ℝ} (hjets : LocalBandJets U ε L α f)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n)) :
    LocalBandJets U ε L α (fun n => MeanMomentBounds.liftedPressureMass (f n)) := by
  intro m
  obtain ⟨C, hC, k, hb⟩ := hjets m
  refine ⟨C * (b - a), mul_nonneg hC (sub_nonneg.mpr hab), k, ?_⟩
  intro n p hp j hj
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp (hf n)
  have hout := liftedPressureMass_jet_bound hab hcf (localize_supported hcs (hs n)) j p
    (C * ε n ^ α * L n ^ k) (fun R _ Y => by
      rw [he.jet_eq j R Y]
      exact hb n (R, (p.2.1, Y)) hp j hj)
  rw [(liftedPressureMass_fiberLocal.germ he).jet_eq j p.1 p.2.2] at hout
  exact hout.trans_eq (by ring)

omit [FiniteDimensional ℝ S] in
omit [CompleteSpace V] in
theorem localBandJets_unweighted {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → V}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U)) (hjets : LocalBandJets U ε L α f) :
    UnweightedClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f := by
  let st := localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU
  refine ⟨fun _ _ _ => zero_le_one, fun n => (hf n).mono (fun _ hp => hp.2), ?_⟩
  intro m
  obtain ⟨C, hC, k, hb⟩ := hjets m
  refine ⟨C, hC, k, ?_⟩
  intro n p hp j hj
  apply (hb n p hp.2 j hj).trans
  change C * ε n ^ α * L n ^ k ≤ C * ε n ^ α * st.growth n p ^ k * 1
  rw [mul_one]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (hL n)) (st.slow_le_growth n p) k)
    (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)

theorem meanClass_pressureMass_lift {a b cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    UnweightedClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n p => PressureStream.pressureMass (f n) p.2.1) := by
  apply localBandJets_unweighted ha hcL hcR ε L hε hεone hL U hU
    (fun n => liftedPressureMass_contDiffOn hU (hf n) (hs n))
  exact (meanClass_localBandJets ha hcL hcR ε L hε hεone hL U hU hf hs hclass).liftedPressureMass
    hab.le hU hf hs

omit [FiniteDimensional ℝ S] in
theorem meanClass_radialMultiply {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n p => φ p.1 * f n p) := by
  have hc := memClass_restrict ha hcL hcR ε L hε hεone hL U hU
    (MeanMomentBounds.radialCoefficient_unweighted (P := S × PressureStream.Plane) (b := b)
      ha hcL hcR ε L hε hεone hL hφ)
  have h := MeanIncrementBounds.Class.coefficient_mul hc hclass
  simp only [zero_add] at h
  exact h

theorem pressureSource_contDiffOn {a b : ℝ} (hab : a < b)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (PressureStream.pressureSource a b hab f) (slowDomain U) :=
  (pressureSource_fiberLocal a b hab).contDiffOn_of_supported
    (fun _ h hsup => PressureStream.pressureSource_contDiff hab h hsup) hU hf hs

theorem pressureSource_supportedOn {a b : ℝ} (hab : a < b)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    SupportedOn a b U (PressureStream.pressureSource a b hab f) :=
  (pressureSource_fiberLocal a b hab).supportedOn
    (fun _ _ hsup => PressureStream.pressureSource_supported hab hsup) hU hf hs

theorem meanClass_pressureSource {a b cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => PressureStream.pressureSource a b hab (f n)) := by
  have hm := meanClass_pressureMass_lift ha hab hcL hcR ε L hε hεone hL U hU hf hs hclass
  have hρ := memClass_restrict ha hcL hcR ε L hε hεone hL U hU
    (MeanIncrementBounds.rho_meanClass (P := S × PressureStream.Plane) ha hab hcL hcR ε L hε hεone
      hL)
  have hprod := MeanIncrementBounds.Class.mul_coefficient hρ hm
  simp only [zero_add] at hprod
  exact MeanIncrementBounds.Class.sub hclass hprod

theorem meanClass_meanPressure {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => PressureStream.meanPressure d a b (M n) hab (v n) (f n)) :=
  meanClass_physicalCompact ha hab hd hcL hcR ε L hε hεone hL U hU α M v _
    (fun n => pressureSource_contDiffOn hab hU (hf n) (hs n))
    (fun n => pressureSource_supportedOn hab hU (hf n) (hs n))
    (meanClass_pressureSource ha hab hcL hcR ε L hε hεone hL U hU hf hs hclass)

end PressureClasses

section MomentsAndChanges

variable [FiniteDimensional ℝ S]

noncomputable def localSlowStripData (U : Set S) (hU : IsOpen U)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n) :
    StripData S :=
  { MeanMomentBounds.slowStripData ε L hε hεone hL with
    domain := U, isOpen_domain := hU
    delta_pos := fun _ _ => zero_lt_one
    zeta_smooth := contDiffOn_const
    zeta_nonneg := fun _ _ => zero_le_one }

theorem meanClass_pressureMass {a b cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    UnweightedClass (localSlowStripData U hU ε L hε hεone hL) α
      (fun n => PressureStream.pressureMass (f n)) := by
  have hm := fun n => liftedPressureMass_contDiffOn hU (hf n) (hs n)
  have hb := (meanClass_localBandJets ha hcL hcR ε L hε hεone hL U hU hf hs
    hclass).liftedPressureMass
    hab.le hU hf hs
  refine ⟨fun _ _ _ => zero_le_one, ?_, ?_⟩
  · intro n
    exact (hm n).comp (MeanMomentBounds.insertSlow (P := S)).contDiff.contDiffOn (fun _ hp => hp)
  · intro m
    obtain ⟨C, hC, k, hbound⟩ := hb m
    refine ⟨C, hC, k, ?_⟩
    intro n s hsu j hj
    change ‖iteratedFDeriv ℝ j
      (MeanMomentBounds.liftedPressureMass (f n) ∘ MeanMomentBounds.insertSlow) s‖ ≤ _
    rw [MeanRankUpdate.iteratedFDeriv_comp_linear (slowDomain_open hU) (hm n)
      MeanMomentBounds.insertSlow j hsu]
    have hn := (iteratedFDeriv ℝ j (MeanMomentBounds.liftedPressureMass (f n))
      (MeanMomentBounds.insertSlow s)).norm_compContinuousLinearMap_le
        (fun _ => MeanMomentBounds.insertSlow (P := S))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hn
    have hp : ‖MeanMomentBounds.insertSlow (P := S)‖ ^ j ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) MeanMomentBounds.norm_insertSlow_le
    have h := hn.trans ((mul_le_of_le_one_right (norm_nonneg _) hp).trans
      (hbound n (MeanMomentBounds.insertSlow s) hsu j hj))
    simpa only [majorant, StripData.growth, localSlowStripData, MeanMomentBounds.slowStripData,
      inv_one, max_self, mul_one] using h

theorem meanClass_radialMoment_lift {a b cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (k : ℕ) :
    UnweightedClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n p => IntegratedMeanBalances.radialMoment k (PressureStream.torusAverage (f n)) p.2.1)
        := by
  have h := meanClass_pressureMass_lift ha hab hcL hcR ε L hε hεone hL U hU
    (fun n => (contDiffOn_fst.pow k).mul (hf n))
    (fun n p hp hn => hs n p hp (right_ne_zero_of_mul hn))
    (meanClass_radialMultiply ha hcL hcR ε L hε hεone hL U hU hclass (contDiff_id.pow k))
  change UnweightedClass _ α (fun n (p : PressureStream.Lift S) =>
    PressureStream.pressureMass (MeanMomentBounds.radialWeighted k (f n)) p.2.1) at h
  simpa only [MeanMomentBounds.pressureMass_radialWeighted] using h

theorem meanClass_radialMoment {a b cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (k : ℕ) :
    UnweightedClass (localSlowStripData U hU ε L hε hεone hL) α
      (fun n => IntegratedMeanBalances.radialMoment k (PressureStream.torusAverage (f n))) := by
  have h := meanClass_pressureMass ha hab hcL hcR ε L hε hεone hL U hU
    (fun n => (contDiffOn_fst.pow k).mul (hf n))
    (fun n p hp hn => hs n p hp (right_ne_zero_of_mul hn))
    (meanClass_radialMultiply ha hcL hcR ε L hε hεone hL U hU hclass (contDiff_id.pow k))
  change UnweightedClass _ α (fun n =>
    PressureStream.pressureMass (MeanMomentBounds.radialWeighted k (f n))) at h
  simpa only [MeanMomentBounds.pressureMass_radialWeighted_fun] using h

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem SupportedOn.sub {a b : ℝ} {U : Set S} {f g : PressureStream.Lift S → ℝ}
    (hf : SupportedOn a b U f) (hg : SupportedOn a b U g) :
    SupportedOn a b U (fun p => f p - g p) := by
  intro p hp hn
  by_cases hz : f p = 0
  · exact hg p hp (fun hz' => hn (by simp [hz, hz']))
  · exact hf p hp hz

/-- The local pressure is the same linear integral operator used globally. -/
theorem meanPressure_sub_on {a b d M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    {U : Set S} (hU : IsOpen U) {f g : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hg : ContDiffOn ℝ ∞ g (slowDomain U))
    (hsf : SupportedOn a b U f) (hsg : SupportedOn a b U g)
    {p : PressureStream.Lift S} (hp : p.2.1 ∈ U) :
    PressureStream.meanPressure d a b M hab v (fun x => f x - g x) p =
      PressureStream.meanPressure d a b M hab v f p - PressureStream.meanPressure d a b M hab v g p
        := by
  obtain ⟨c, _, hcs, hcf, hef⟩ := exists_fiber_localization hU hp hf
  obtain ⟨e, _, hes, heg, heqg⟩ := exists_fiber_localization hU hp hg
  have hF := hef.self_of_nhds
  have hG := heqg.self_of_nhds
  have hsub : ∀ r Y, localize c f (r, (p.2.1, Y)) - localize e g (r, (p.2.1, Y)) =
      f (r, (p.2.1, Y)) - g (r, (p.2.1, Y)) := fun r Y => congrArg₂ (fun x y : ℝ => x - y) (hF r Y)
        (hG r Y)
  rw [← meanPressure_fiberLocal d a b M hab v
      (fun x => localize c f x - localize e g x) (fun x => f x - g x) p.2.1 hsub p.1 p.2.2,
    congrFun (MeanIncrementBounds.meanPressure_sub ha hab hd hcf heg
      (localize_supported hcs hsf) (localize_supported hes hsg) M v) p,
    meanPressure_fiberLocal d a b M hab v _ _ p.2.1 hF p.1 p.2.2,
    meanPressure_fiberLocal d a b M hab v _ _ p.2.1 hG p.1 p.2.2]

theorem meanClass_meanPressure_change {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f g : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hg : ∀ n, ContDiffOn ℝ ∞ (g n) (slowDomain U))
    (hsf : ∀ n, SupportedOn a b U (f n)) (hsg : ∀ n, SupportedOn a b U (g n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α (f - g))
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n p => PressureStream.meanPressure d a b (M n) hab (v n) (f n) p -
        PressureStream.meanPressure d a b (M n) hab (v n) (g n) p) := by
  apply MeanRankUpdate.meanClass_congr_on
    (meanClass_meanPressure ha hab hd hcL hcR ε L hε hεone hL U hU
      (fun n => (hf n).sub (hg n)) (fun n => (hsf n).sub (hsg n)) hclass M v)
  intro n p hp
  exact (meanPressure_sub_on ha hab hd (v n) hU (hf n) (hg n) (hsf n) (hsg n) hp.2).symm

end MomentsAndChanges

/-! ## Exact identification of the positive-time normalized rank domain -/

noncomputable def normalizedSlowDomain (coord qlo qhi : ℝ) : Set PressureStream.Plane :=
  {s | 0 < s.1 ∧ SimilarityCoordinates.coordinateQ coord (s.1, s.2) ∈ Ioo qlo qhi}

theorem chartQ_eq_slow (coord : ℝ) (p : MeanRankUpdate.ChartPoint) :
    MeanRankUpdate.chartQ coord p = SimilarityCoordinates.coordinateQ coord (p.2.1.1, p.2.1.2) :=
      rfl

theorem normalizedSlowDomain_open {coord : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (qlo qhi : ℝ) : IsOpen (normalizedSlowDomain coord qlo qhi) := by
  have h := (MeanRankUpdate.normalizedDomain_isOpen hc hc1 qlo qhi (-1) 1).preimage
    (show Continuous (fun s : PressureStream.Plane => ((0 : ℝ), (s, (0 : PressureStream.Plane))))
      from
      continuous_const.prodMk (continuous_id.prodMk continuous_const))
  convert! h using 1
  ext s
  simp [normalizedSlowDomain, MeanRankUpdate.normalizedDomain, chartQ_eq_slow,
    PhysicalCoordinateBounds.positiveTime, MeanRankUpdate.chartInput_apply]

theorem normalizedDomain_eq (coord qlo qhi rlo rhi : ℝ) :
    MeanRankUpdate.normalizedDomain coord qlo qhi rlo rhi =
      stripDomain rlo rhi (normalizedSlowDomain coord qlo qhi) := by
  ext p
  simp only [MeanRankUpdate.normalizedDomain, stripDomain, normalizedSlowDomain, Set.mem_ofPred_eq,
    chartQ_eq_slow, PhysicalCoordinateBounds.positiveTime, MeanRankUpdate.chartInput_apply]
  tauto

theorem normalizedStripData_eq (coord qlo qhi rlo rhi cL cR : ℝ)
    (hc : 0 < coord) (hc1 : coord < 1) (hrlo : 0 < rlo) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n) :
    MeanRankUpdate.normalizedStripData coord qlo qhi rlo rhi cL cR hc hc1 hrlo hcL hcR
      ε L hε hεone hL =
    localStripData rlo rhi cL cR hrlo hcL hcR ε L hε hεone hL
      (normalizedSlowDomain coord qlo qhi) (normalizedSlowDomain_open hc hc1 qlo qhi) := by
  unfold MeanRankUpdate.normalizedStripData localStripData
  simp only [normalizedDomain_eq]

section TemporalClasses

variable [FiniteDimensional ℝ S]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem temporalInverse_fiberLocal : FiberLocal (S := S) TemporalMeanUpdate.temporalInverse := by
  intro f g s he r Y
  have hslice : SmoothFamilyTorusInverse.slice (TemporalMeanUpdate.sourceToFamily f) (r, s) =
      SmoothFamilyTorusInverse.slice (TemporalMeanUpdate.sourceToFamily g) (r, s) := by
    funext Z
    exact congrArg Complex.ofReal (he r Z)
  have hcoeff : SmoothFamilyTorusInverse.coefficient (TemporalMeanUpdate.sourceToFamily f) (r, s) =
      SmoothFamilyTorusInverse.coefficient (TemporalMeanUpdate.sourceToFamily g) (r, s) := by
    funext k
    unfold SmoothFamilyTorusInverse.coefficient
    rw [hslice]
  dsimp only [TemporalMeanUpdate.temporalInverse, SmoothFamilyTorusInverse.inverse]
  rw [hcoeff]

theorem temporalInverse_contDiffOn {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U))
    (hp : PeriodicOn U f) :
    ContDiffOn ℝ ∞ (TemporalMeanUpdate.temporalInverse f) (slowDomain U) :=
  temporalInverse_fiberLocal.contDiffOn_of_periodic
    (fun _ h hp => TemporalMeanUpdate.temporalInverse_smooth h hp) hU hf hp

theorem meanClass_temporalInverse {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U)) (hp : ∀ n, PeriodicOn U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => TemporalMeanUpdate.temporalInverse (f n)) := by
  let st := localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU
  refine ⟨hclass.weight_nonneg,
    fun n => (temporalInverse_contDiffOn hU (hf n) (hp n)).mono (fun _ hx => hx.2), ?_⟩
  intro m
  obtain ⟨K, hK, hbound⟩ := UniformFourierAlias.realInverse_finiteJets (P := ℝ × S) .temporal m
  obtain ⟨C, hC, k, hb⟩ := hclass.bounds (m + 5)
  refine ⟨K * C, mul_nonneg hK hC, k, ?_⟩
  intro n p hpu j hj
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hpu.2 (hf n)
  let B := majorant st (fun _ x => st.zeta x) α C k n p
  have hB : 0 ≤ B := majorant_nonneg st _ α hC k n p (st.zeta_nonneg p hpu)
  have hin : ∀ i ≤ m + 5, ∀ q ∈ ({(p.1, p.2.1)} : Set (ℝ × S)), ∀ Y,
      ‖iteratedFDeriv ℝ i (UniformFourierAlias.toProduct (localize c (f n))) (q, Y)‖ ≤ B := by
    intro i hi q hq Y
    rcases mem_singleton_iff.mp hq with rfl
    rw [UniformFourierAlias.norm_iteratedFDeriv_toProduct, he.jet_eq i p.1 Y]
    exact hb n (p.1, (p.2.1, Y)) hpu i hi
  have hper : UniformFourierAlias.ParameterPeriodic
      (UniformFourierAlias.toProduct (localize c (f n))) :=
    fun q => localize_periodic hcs (hp n) q.1 q.2
  have ho := hbound _ {(p.1, p.2.1)} B (UniformFourierAlias.toProduct_smooth hcf)
    hper hB hin j hj (p.1, p.2.1) (mem_singleton _) p.2.2
  rw [← UniformFourierAlias.norm_iteratedFDeriv_fromProduct] at ho
  change ‖iteratedFDeriv ℝ j (TemporalMeanUpdate.temporalInverse (localize c (f n))) p‖ ≤ K * B at
    ho
  rw [(temporalInverse_fiberLocal.germ he).jet_eq j p.1 p.2.2] at ho
  exact ho.trans_eq (by dsimp [B, majorant]; ring)

omit [FiniteDimensional ℝ S] in
omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem desiredIncrement_fiberLocal (h : ℝ) (n : ℕ) :
    FiberLocal (S := S) (TemporalMeanUpdate.desiredIncrement h n) := by
  intro f g s he r Y
  exact congrArg (fun x : ℝ => -TemporalMeanUpdate.chartPrefactor h n * x)
    (temporalInverse_fiberLocal _ _ s (centered_fiberLocal f g s he) r Y)

theorem desiredIncrement_contDiffOn (h : ℝ) (n : ℕ) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U))
    (hp : PeriodicOn U f) :
    ContDiffOn ℝ ∞ (TemporalMeanUpdate.desiredIncrement h n f) (slowDomain U) :=
  (desiredIncrement_fiberLocal h n).contDiffOn_of_periodic
    (fun _ hf hp => TemporalMeanUpdate.desiredIncrement_smooth h n hf hp) hU hf hp

theorem desiredIncrement_supportedOn (h : ℝ) (n : ℕ) {a b : ℝ}
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    SupportedOn a b U (TemporalMeanUpdate.desiredIncrement h n f) :=
  (desiredIncrement_fiberLocal h n).supportedOn
    (fun _ _ hs => TemporalMeanUpdate.desiredIncrement_supported h n hs) hU hf hs

theorem meanClass_desiredIncrement {a b cL cR h : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U)) (hp : ∀ n, PeriodicOn U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => TemporalMeanUpdate.desiredIncrement h n (f n)) := by
  have hc := meanClass_centered ha hcL hcR ε L hε hεone hL U hU hf hclass
  have hi := meanClass_temporalInverse ha hcL hcR ε L hε hεone hL U hU
    (fun n => centered_contDiffOn hU (hf n)) (fun n => centered_periodicOn (hp n)) hc
  have hm := (TemporalMeanUpdate.meanClass_chartPrefactor_all hh hscale hi).map
    (-ContinuousLinearMap.id ℝ ℝ)
  change MeanClass _ α (fun n z => -TemporalMeanUpdate.chartPrefactor h n *
    TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered (f n)) z)
  simpa only [TemporalMeanUpdate.desiredIncrement, _root_.neg_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, neg_mul] using hm

end TemporalClasses

theorem dividedAlias_finiteJets_fiber {d a b : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane) (g : PressureStream.Lift S → ℝ),
      ContDiff ℝ ∞ g → RadialAlias.RadiallySupported a b g →
      ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      (∀ j ≤ m, ∀ z : PressureStream.Lift S, z.2.1 = s → ‖iteratedFDeriv ℝ j
        (UniformFourierAlias.exactAlias
        (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d)) M (0, v)
          (RadialPullback.normalizeSource d a g)) z‖ ≤ C) →
      ∀ j ≤ m, ∀ z : PressureStream.Lift S, z.2.1 = s →
        ‖iteratedFDeriv ℝ j (PressureStream.divideRadius (RadialPullback.physicalAlias d a b M (0,
          v) g)) z‖ ≤
          K * C := by
  obtain ⟨KP, hKP, hcomp⟩ := RadialPullback.radial_comp_finiteJets_uniform (E := S ×
    PressureStream.Plane) (V := ℝ)
    a b (RadialPullback.powerChart_contDiff ha d) m
  obtain ⟨KM, hKM, hmul⟩ := RadialPullback.radial_multiplier_finiteJets_uniform (E := S ×
    PressureStream.Plane) (V := ℝ)
    a b (TemporalMeanUpdate.aliasFactor_smooth ha d) m
  refine ⟨KM * KP, mul_nonneg hKM hKP, ?_⟩
  intro M v g hg hs C hC s hbound j hj z hzs
  let A := UniformFourierAlias.exactAlias (TransportPrimitive.interiorCutoff (a ^ d) (b ^ d))
    M (0, v) (RadialPullback.normalizeSource d a g)
  have hAs : ContDiff ℝ ∞ A := UniformFourierAlias.exactAlias_smooth
    (TransportPrimitive.interiorCutoff_contDiff (a ^ d) (b ^ d))
    (RadialPullback.normalizeSource_contDiff ha hd hg) (RadialPullback.normalizeSource_supported ha
      hab hd hs)
  by_cases hz : z.1 ∈ Icc a b
  · rw [TemporalMeanUpdate.dividedAlias_eq_pullback ha hab hd (0, v) g]
    change ‖iteratedFDeriv ℝ j (fun y => TemporalMeanUpdate.aliasFactor d a y.1 •
      (A ∘ RadialPullback.liftChart (RadialPullback.powerChart d a)) y) z‖ ≤ _
    have hc := hcomp A hAs z hz C hC
      (fun i hi => hbound i hi (RadialPullback.liftChart (RadialPullback.powerChart d a) z) hzs)
    have hm := hmul (A ∘ RadialPullback.liftChart (RadialPullback.powerChart d a))
      (hAs.comp (RadialPullback.liftChart_contDiff (RadialPullback.powerChart_contDiff ha d))) z hz
      (KP * C) (mul_nonneg hKP hC) hc j hj
    exact hm.trans_eq (by ring)
  · have hz0 : iteratedFDeriv ℝ j
        (PressureStream.divideRadius (RadialPullback.physicalAlias d a b M (0, v) g)) z = 0 := by
      by_contra hn
      exact hz (TransportPrimitive.iteratedFDeriv_supported
        (PressureStream.divideRadius_supported (RadialPullback.physicalAlias_supported ha hab hd M
          (0, v) g)) j hn)
    rw [hz0, norm_zero]
    exact mul_nonneg (mul_nonneg hKM hKP) hC

theorem totalIntegral_jet_bound_fiber {a b M : ℝ} (hab : a ≤ b) (v : PressureStream.Plane)
    {f : PressureStream.Lift S → V} (hf : ContDiff ℝ ∞ f)
    (hs : RadialAlias.RadiallySupported a b f) (j : ℕ)
    (p : PressureStream.Lift S) (C : ℝ)
    (hb : ∀ R ∈ Icc a b, ∀ Y, ‖iteratedFDeriv ℝ j f (R, (p.2.1, Y))‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M ((0 : S), v) f) p‖ ≤ C * (b - a) := by
  rw [TransportPrimitive.iteratedFDeriv_totalIntegral hf hs]
  have he := TransportPrimitive.totalIntegral_norm_le (M := M) (v := ((0 : S), v)) hab
    (freezeSlow_continuous (TransportPrimitive.iteratedFDeriv_contDiff hf j).continuous p.2.1)
    (freezeSlow_supported (TransportPrimitive.iteratedFDeriv_supported hs j) p.2.1)
    (fun R hR Y => hb R hR Y.2) p
  simp only [totalIntegral_freeze] at he
  exact he

/-- A bounded source gives a bounded actual cutoff alias, with a constant
independent of the transport shift and the slow fiber. -/
theorem exactAlias_bounded_fiber {a b : ℝ} (hab : a ≤ b) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hleft : ∀ u ≤ a, χ u = 0) (hright : ∀ u, b ≤ u → χ u = 1)
    (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane)
      (f : PressureStream.Lift S → V), ContDiff ℝ ∞ f →
      RadialAlias.RadiallySupported a b f → ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      (∀ i ≤ m, ∀ R ∈ Icc a b, ∀ Y, ‖iteratedFDeriv ℝ i f (R, (s, Y))‖ ≤ C) →
      ∀ j ≤ m, ∀ z : PressureStream.Lift S, z.2.1 = s →
      ‖iteratedFDeriv ℝ j (UniformFourierAlias.exactAlias χ M ((0 : S), v) f) z‖ ≤ K * C := by
  obtain ⟨K, hK, hmul⟩ := radial_multiplier_finiteJets_uniform
    (E := S × PressureStream.Plane) (V := V) a b (contDiff_infty_iff_deriv.mp hχ).2 m
  refine ⟨K * (b - a), mul_nonneg hK (sub_nonneg.mpr hab), ?_⟩
  intro M v f hf hs C hC s hb j hj z hzs
  by_cases hz : z.1 ∈ Icc a b
  · have hi : ∀ i ≤ m, ‖iteratedFDeriv ℝ i (TransportPrimitive.totalIntegral M ((0 : S), v) f) z‖ ≤
    C * (b - a) := by
      intro i hi
      exact totalIntegral_jet_bound_fiber hab v hf hs i z C (by simpa only [hzs] using hb i hi)
    have he := hmul (TransportPrimitive.totalIntegral M ((0 : S), v) f)
      (TransportPrimitive.totalIntegral_contDiff hf hs) z hz (C * (b - a))
      (mul_nonneg hC (sub_nonneg.mpr hab)) hi j hj
    exact he.trans_eq (by ring)
  · have hz0 : iteratedFDeriv ℝ j (UniformFourierAlias.exactAlias χ M ((0 : S), v) f) z = 0 := by
      by_contra hn
      exact hz (TransportPrimitive.iteratedFDeriv_supported
        (UniformFourierAlias.exactAlias_supported hleft hright) j hn)
    rw [hz0, norm_zero]
    exact mul_nonneg (mul_nonneg hK (sub_nonneg.mpr hab)) hC

omit [CompleteSpace V] in
theorem normalizeSource_bounded_fiber {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (lo hi : ℝ) (m : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : PressureStream.Lift S → V),
      ContDiff ℝ ∞ f → ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      (∀ i ≤ m, ∀ R Y, ‖iteratedFDeriv ℝ i f (R, (s, Y))‖ ≤ C) →
      ∀ j ≤ m, ∀ R ∈ Icc lo hi, ∀ Y,
      ‖iteratedFDeriv ℝ j (normalizeSource d a f) (R, (s, Y))‖ ≤ K * C := by
  obtain ⟨KC, hKC, hbC⟩ := radial_comp_finiteJets_uniform (E := S × PressureStream.Plane) (V := V)
    lo hi (inverseChart_contDiff ha d) m
  obtain ⟨KM, hKM, hbM⟩ := radial_multiplier_finiteJets_uniform (E := S × PressureStream.Plane) (V
    := V)
    lo hi (sourceMultiplier_contDiff ha hd) m
  refine ⟨KM * KC, mul_nonneg hKM hKC, ?_⟩
  intro f hf C hC s hb j hj R hR Y
  have hc : ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (f ∘ liftChart (inverseChart d a)) (R, (s, Y))‖ ≤ KC * C :=
    fun i hi => hbC f hf (R, (s, Y)) hR C hC (fun k hk => hb k hk _ _) i hi
  have he := hbM (f ∘ liftChart (inverseChart d a))
    (hf.comp (liftChart_contDiff (inverseChart_contDiff ha d))) (R, (s, Y)) hR
    (KC * C) (mul_nonneg hKC hC) hc j hj
  exact he.trans_eq (by ring)

theorem dividedAlias_bounded_fiber {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (M : ℝ) (v : PressureStream.Plane)
      (f : PressureStream.Lift S → ℝ), ContDiff ℝ ∞ f →
      RadialAlias.RadiallySupported a b f → ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      (∀ i ≤ m, ∀ R Y, ‖iteratedFDeriv ℝ i f (R, (s, Y))‖ ≤ C) →
      ∀ j ≤ m, ∀ z : PressureStream.Lift S, z.2.1 = s →
      ‖iteratedFDeriv ℝ j (PressureStream.divideRadius (physicalAlias d a b M ((0 : S), v) f)) z‖ ≤
        K * C := by
  have habU : a ^ d < b ^ d := Real.rpow_lt_rpow ha.le hab hd
  obtain ⟨KN, hKN, hbN⟩ := normalizeSource_bounded_fiber (S := S) (V := ℝ) ha hd (a ^ d) (b ^ d) m
  obtain ⟨KA, hKA, hbA⟩ := exactAlias_bounded_fiber (S := S) (V := ℝ) habU.le
    (TransportPrimitive.interiorCutoff_contDiff (a ^ d) (b ^ d))
    (fun u hu => TransportPrimitive.interiorCutoff_zero habU (by linarith))
    (fun u hu => TransportPrimitive.interiorCutoff_one habU (by linarith)) m
  obtain ⟨KT, hKT, hbT⟩ := dividedAlias_finiteJets_fiber (S := S) ha hab hd m
  refine ⟨KT * KA * KN, mul_nonneg (mul_nonneg hKT hKA) hKN, ?_⟩
  intro M v f hf hs C hC s hb j hj z hzs
  have hN := hbN f hf C hC s hb
  have hA := hbA M v (normalizeSource d a f) (normalizeSource_contDiff ha hd hf)
    (normalizeSource_supported ha hab hd hs) (KN * C) (mul_nonneg hKN hC) s hN
  have he := hbT M v f hf hs (KA * (KN * C)) (mul_nonneg hKA (mul_nonneg hKN hC))
    s hA j hj z hzs
  exact he.trans_eq (by ring)

theorem dividedAlias_fiberLocal (d a b M : ℝ) (v : PressureStream.Plane) :
    FiberLocal (S := S) (fun f => PressureStream.divideRadius (physicalAlias d a b M ((0 : S), v)
      f)) := by
  intro f g s he r Y
  exact congrArg (fun x : ℝ => x / r) (physicalAlias_fiberLocal d a b M v f g s he r Y)

section AliasClasses

variable [FiniteDimensional ℝ S]

theorem dividedAlias_contDiffOn {a b d M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f) :
    ContDiffOn ℝ ∞ (PressureStream.divideRadius (physicalAlias d a b M ((0 : S), v) f)) (slowDomain
      U) :=
  (dividedAlias_fiberLocal d a b M v).contDiffOn_of_supported
    (fun g hg hsg => PressureStream.divideRadius_contDiff ha
      (physicalAlias_contDiff ha hab hd hg hsg M (0, v))
      (physicalAlias_supported ha hab hd M (0, v) g)) hU hf hs

theorem LocalBandJets.dividedAlias {a b d : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    {U : Set S} (hU : IsOpen U) {ε L : ℕ → ℝ}
    (hε : ∀ n, 0 < ε n) (hL : ∀ n, 1 ≤ L n) {α : ℝ}
    {f : ℕ → PressureStream.Lift S → ℝ} (hjets : LocalBandJets U ε L α f)
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n)) (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    LocalBandJets U ε L α (fun n => PressureStream.divideRadius
      (physicalAlias d a b (M n) ((0 : S), v n) (f n))) := by
  intro m
  obtain ⟨K, hK, hbound⟩ := dividedAlias_bounded_fiber (S := S) ha hab hd m
  obtain ⟨C, hC, k, hb⟩ := hjets m
  refine ⟨K * C, mul_nonneg hK hC, k, ?_⟩
  intro n p hp j hj
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp (hf n)
  have hA : 0 ≤ C * ε n ^ α * L n ^ k :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) _)
  have ho := hbound (M n) (v n) _ hcf (localize_supported hcs (hs n))
    (C * ε n ^ α * L n ^ k) hA p.2.1
    (fun i hi R Y => by rw [he.jet_eq i R Y]; exact hb n (R, (p.2.1, Y)) hp i hi) j hj p rfl
  rw [((dividedAlias_fiberLocal d a b (M n) (v n)).germ he).jet_eq j p.1 p.2.2] at ho
  exact ho.trans_eq (by ring)

end AliasClasses

section FinalStreamClasses

variable [FiniteDimensional ℝ S]

omit [CompleteSpace V] in
theorem localBandJets_meanClass_of_support {a b c e cL cR : ℝ}
    (ha : 0 < a) (hac : a < c) (heb : e < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → V}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn c e U (f n)) (hb : LocalBandJets U ε L α f) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f := by
  let st := localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU
  let sb := logStripData (E := S × PressureStream.Plane) a b cL cR ha hcL hcR ε L hε hεone hL
  have hmem (r : ℝ) (hr : r ∈ Icc c e) : (r, (0 : S × PressureStream.Plane)) ∈ sb.domain :=
    ⟨hac.trans_le hr.1, hr.2.trans_lt heb⟩
  have hcont : ContinuousOn (fun r : ℝ => sb.zeta (r, 0)) (Icc c e) :=
    sb.zeta_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hpos (r : ℝ) (hr : r ∈ Icc c e) : 0 < sb.zeta (r, 0) :=
    zeta_pos cL cR (logPosition_mem ha (hmem r hr))
  obtain ⟨δ, hδ, hmargin⟩ := UniformCone.positive_uniform_margin isCompact_Icc hcont hpos
  refine ⟨fun _ p hp => st.zeta_nonneg p hp, fun n => (hf n).mono (fun _ hp => hp.2), ?_⟩
  intro m
  obtain ⟨C, hC, k, hbound⟩ := hb m
  refine ⟨C / δ, div_nonneg hC hδ.le, k, ?_⟩
  intro n p hp j hj
  by_cases hpi : p.1 ∈ Icc c e
  · have hζ : δ ≤ st.zeta p := hmargin p.1 hpi
    have hgr : L n ^ k ≤ st.growth n p ^ k :=
      pow_le_pow_left₀ (zero_le_one.trans (hL n)) (st.slow_le_growth n p) k
    have hA : 0 ≤ C / δ * ε n ^ α * st.growth n p ^ k :=
      mul_nonneg (mul_nonneg (div_nonneg hC hδ.le) (Real.rpow_pos_of_pos (hε n) α).le)
        (pow_nonneg (st.growth_nonneg n p) _)
    calc
      _ ≤ C * ε n ^ α * L n ^ k := hbound n p hp.2 j hj
      _ ≤ C * ε n ^ α * st.growth n p ^ k :=
        mul_le_mul_of_nonneg_left hgr (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      _ = (C / δ * ε n ^ α * st.growth n p ^ k) * δ := by field_simp
      _ ≤ (C / δ * ε n ^ α * st.growth n p ^ k) * st.zeta p := mul_le_mul_of_nonneg_left hζ hA
      _ = _ := rfl
  · rw [jet_zero_outside hU (hf n) (hs n) hp.2 (fun hi => hpi ⟨hi.1.le, hi.2.le⟩) j, norm_zero]
    exact majorant_nonneg st _ α (div_nonneg hC hδ.le) k n p (st.zeta_nonneg p hp)

/-- The actual divided alias preserves the local mean class. No mean-zero
condition or nonzero transport coefficient is needed for this basic bound. -/
theorem meanClass_dividedAlias {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => PressureStream.divideRadius (physicalAlias d a b (M n) ((0 : S), v n) (f n))) := by
  obtain ⟨c, e, hac, _, heb, hsup⟩ :=
    TemporalMeanUpdate.dividedAlias_interior_support (E := S × PressureStream.Plane) ha hab hd
  apply localBandJets_meanClass_of_support ha hac heb hcL hcR ε L hε hεone hL U hU
    (fun n => dividedAlias_contDiffOn ha hab hd (v n) hU (hf n) (hs n))
    (fun n p _ hp => hsup (M n) (0, v n) (f n) hp)
  exact (meanClass_localBandJets ha hcL hcR ε L hε hεone hL U hU hf hs hclass).dividedAlias
    ha hab hd hU hε hL hf hs M v

omit [FiniteDimensional ℝ S] in
theorem meanClass_divideRadius {a b cL cR : ℝ}
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => PressureStream.divideRadius (f n)) := by
  let φ : ℝ → ℝ := fun r => (positiveRadius (a / 4) r)⁻¹
  have hφ : ContDiff ℝ ∞ φ := (positiveRadius_contDiff (a / 4)).inv
    (fun r => (positiveRadius_pos (by positivity) r).ne')
  apply MeanRankUpdate.meanClass_congr_on
    (meanClass_radialMultiply ha hcL hcR ε L hε hεone hL U hU hclass hφ)
  intro n p hp
  dsimp [PressureStream.divideRadius, φ]
  rw [positiveRadius_eq_self (show 0 < a / 4 by positivity) (by linarith [hp.1.1])]
  simp only [div_eq_mul_inv, mul_comm]

theorem meanClass_streamPotential {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => PressureStream.streamPotential d a b (M n) ((0 : S), v n) (f n)) := by
  have hw := meanClass_radialMultiply ha hcL hcR ε L hε hεone hL U hU hclass (φ := id) contDiff_id
  have hi := meanClass_physicalCompact ha hab hd hcL hcR ε L hε hεone hL U hU α M v
    (fun n => PressureStream.weightedSource (f n))
    (fun n => contDiffOn_fst.mul (hf n))
    (fun n p hp hn => hs n p hp (right_ne_zero_of_mul hn)) hw
  exact meanClass_divideRadius ha hcL hcR ε L hε hεone hL U hU hi

theorem meanClass_streamBeta {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) (w : S × PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => PressureStream.streamBeta w (PressureStream.streamPotential d a b (M n) ((0 : S), v
        n) (f n))) := by
  have hi := meanClass_streamPotential ha hab hd hcL hcR ε L hε hεone hL U hU hf hs hclass M v
  have hD := (hi.directional (0, w)).map (-ContinuousLinearMap.id ℝ ℝ)
  simp only [
    _root_.neg_apply, ContinuousLinearMap.id_apply] at hD ⊢
  exact hD

theorem streamGamma_eq_desired_sub_alias_on {a b d M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    {U : Set S} (hU : IsOpen U) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) (hs : SupportedOn a b U f)
    {p : PressureStream.Lift S} (hp : p.2.1 ∈ U) :
    PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : S), v)
      (PressureStream.streamPotential d a b M ((0 : S), v) f) p =
      f p - physicalAlias d a b M ((0 : S), v) (PressureStream.weightedSource f) p / p.1 := by
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp hf
  have hpot := (((streamPotential_fiberLocal d a b M v).germ he).eventuallyEq p.1 p.2.2)
  have halias := (((physicalAlias_fiberLocal d a b M v).germ
    (weightedSource_fiberLocal.germ he)).eventuallyEq p.1 p.2.2).self_of_nhds
  have hval := (he.eventuallyEq p.1 p.2.2).self_of_nhds
  have h := PressureStream.streamGamma_eq_desired_sub_alias_global (M := M) ha hab hd ((0 : S), v)
    hcf (localize_supported hcs hs) p
  simpa only [PressureStream.streamGamma, PressureStream.graphDr, PressureStream.divideRadius,
    hpot.fderiv_eq, hpot.self_of_nhds, halias, hval] using h

theorem meanClass_streamGamma {a b d cL cR : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => PressureStream.streamGamma (PressureStream.physicalSpeed d (M n)) ((0 : S), v n)
        (PressureStream.streamPotential d a b (M n) ((0 : S), v n) (f n))) := by
  have hw := meanClass_radialMultiply ha hcL hcR ε L hε hεone hL U hU hclass (φ := id) contDiff_id
  have hA := meanClass_dividedAlias ha hab hd hcL hcR ε L hε hεone hL U hU
    (f := fun n => PressureStream.weightedSource (f n))
    (fun n => contDiffOn_fst.mul (hf n))
    (fun n p hp hn => hs n p hp (right_ne_zero_of_mul hn)) hw M v
  apply MeanRankUpdate.meanClass_congr_on (MeanIncrementBounds.Class.sub hclass hA)
  intro n p hp
  exact streamGamma_eq_desired_sub_alias_on ha hab hd (v n) hU (hf n) (hs n) hp.2

theorem stream_divergence_zero_on {a b d M : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : PressureStream.Plane)
    (w : S × PressureStream.Plane) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U))
    (hs : SupportedOn a b U f) {p : PressureStream.Lift S} (hp : p.2.1 ∈ U) (hr : p.1 ≠ 0) :
    PressureStream.graphDivergence (PressureStream.physicalSpeed d M) ((0 : S), v) w
      (PressureStream.streamBeta w (PressureStream.streamPotential d a b M ((0 : S), v) f))
      (PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : S), v)
        (PressureStream.streamPotential d a b M ((0 : S), v) f)) p = 0 := by
  have hpot := (streamPotential_contDiffOn (M := M) ha hab hd v hU hf hs).contDiffAt
    ((slowDomain_open hU).mem_nhds hp)
  exact PressureStream.stream_divergence_zero ((0 : S), v) w
    (hpot.of_le (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 2).le)
    ((PressureStream.physicalSpeed_smooth d M hr).differentiableAt (by simp)) hr

end FinalStreamClasses

section ActualTemporalUpdate

variable [FiniteDimensional ℝ S]

theorem desiredIncrement_zeroMean_on (h : ℝ) (n : ℕ) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U))
    (hper : PeriodicOn U f) (p : ℝ × S) (hp : p.2 ∈ U) :
    PressureStream.torusAverage (TemporalMeanUpdate.desiredIncrement h n f) p = 0 := by
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp hf
  have hfg := ((desiredIncrement_fiberLocal h n).germ he).self_of_nhds
  rw [← PressureStream.torusAverage_congr_slice p (hfg p.1)]
  exact TemporalMeanUpdate.desiredIncrement_zeroMean h n hcf (localize_periodic hcs hper) p

theorem desiredIncrement_barMass_on (h : ℝ) (n : ℕ) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U))
    (hper : PeriodicOn U f) (w : ℝ → ℝ) (s : S) (hs : s ∈ U) :
    (∫ r, w r * PressureStream.torusAverage (TemporalMeanUpdate.desiredIncrement h n f) (r, s)) = 0
      := by
  have hz (r : ℝ) := desiredIncrement_zeroMean_on h n hU hf hper (r, s) hs
  simp_rw [hz, mul_zero, integral_zero]

theorem desiredIncrement_fastDerivative_on (h : ℝ) (n : ℕ) {U : Set S} (hU : IsOpen U)
    {f : PressureStream.Lift S → ℝ} (hf : ContDiffOn ℝ ∞ f (slowDomain U))
    (hper : PeriodicOn U f) {p : PressureStream.Lift S} (hp : p.2.1 ∈ U) :
    TemporalMeanUpdate.fastDerivative h n (TemporalMeanUpdate.desiredIncrement h n f) p =
      -TemporalMeanUpdate.centered f p := by
  obtain ⟨c, _, hcs, hcf, he⟩ := exists_fiber_localization hU hp hf
  have hD : fderiv ℝ (TemporalMeanUpdate.desiredIncrement h n (localize c f)) p =
      fderiv ℝ (TemporalMeanUpdate.desiredIncrement h n f) p :=
    (((desiredIncrement_fiberLocal h n).germ he).eventuallyEq p.1 p.2.2).fderiv_eq
  have hC := ((centered_fiberLocal.germ he).eventuallyEq p.1 p.2.2).self_of_nhds
  have ho := TemporalMeanUpdate.desiredIncrement_fastDerivative h n hcf (localize_periodic hcs
    hper) p
  simpa only [TemporalMeanUpdate.fastDerivative, PressureStream.graphDz, hD, hC] using ho

theorem meanClass_axialPotential {a b d cL cR h : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U)) (hp : ∀ n, PeriodicOn U (f n))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => TemporalMeanUpdate.axialPotential d a b (M n) (v n) h n (f n)) :=
  meanClass_streamPotential ha hab hd hcL hcR ε L hε hεone hL U hU
    (fun n => desiredIncrement_contDiffOn h n hU (hf n) (hp n))
    (fun n => desiredIncrement_supportedOn h n hU (hf n) (hs n))
    (meanClass_desiredIncrement ha hcL hcR hh ε L hε hεone hL hscale U hU hf hp hclass) M v

theorem meanClass_radialUpdate {a b d cL cR h : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U)) (hp : ∀ n, PeriodicOn U (f n))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) (w : S × PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => TemporalMeanUpdate.radialUpdate d a b (M n) (v n) w h n (f n)) :=
  meanClass_streamBeta ha hab hd hcL hcR ε L hε hεone hL U hU
    (fun n => desiredIncrement_contDiffOn h n hU (hf n) (hp n))
    (fun n => desiredIncrement_supportedOn h n hU (hf n) (hs n))
    (meanClass_desiredIncrement ha hcL hcR hh ε L hε hεone hL hscale U hU hf hp hclass) M v w

theorem meanClass_scaledRadialUpdate {a b d cL cR h : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U)) (hp : ∀ n, PeriodicOn U (f n))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) (w : S × PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) (α + 1)
      (fun n => TemporalMeanUpdate.radialUpdate d a b (M n) (v n) (ε n • w) h n (f n)) := by
  let st := localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU
  have hb : BandBound st 1 ε := by
    have hb := bandBound_rpow st 1
    simp only [Real.rpow_one] at hb
    exact hb
  have hi := meanClass_radialUpdate ha hab hd hcL hcR hh ε L hε hεone hL hscale U hU hf hp hs
    hclass M v w
  have hout := hi.band_smul hb
  have heq : (fun n => TemporalMeanUpdate.radialUpdate d a b (M n) (v n) (ε n • w) h n (f n)) =
      (fun n z => ε n • TemporalMeanUpdate.radialUpdate d a b (M n) (v n) w h n (f n) z) := by
    funext n z
    exact congrFun (TemporalMeanUpdate.radialUpdate_smul_direction d a b (M n) (v n) w h (ε n) n (f
      n)) z
  rw [heq]
  exact hout

theorem meanClass_axialUpdate {a b d cL cR h : ℝ}
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 ≤ h)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hscale : ∀ n, ChartScales.S n ≤ L n)
    (U : Set S) (hU : IsOpen U) {α : ℝ} {f : ℕ → PressureStream.Lift S → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (slowDomain U)) (hp : ∀ n, PeriodicOn U (f n))
    (hs : ∀ n, SupportedOn a b U (f n))
    (hclass : MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α f)
    (M : ℕ → ℝ) (v : ℕ → PressureStream.Plane) :
    MeanClass (localStripData a b cL cR ha hcL hcR ε L hε hεone hL U hU) α
      (fun n => TemporalMeanUpdate.axialUpdate d a b (M n) (v n) h n (f n)) :=
  meanClass_streamGamma ha hab hd hcL hcR ε L hε hεone hL U hU
    (fun n => desiredIncrement_contDiffOn h n hU (hf n) (hp n))
    (fun n => desiredIncrement_supportedOn h n hU (hf n) (hs n))
    (meanClass_desiredIncrement ha hcL hcR hh ε L hε hεone hL hscale U hU hf hp hclass) M v

end ActualTemporalUpdate

end NavierStokes.PhysicalMeanDomain
