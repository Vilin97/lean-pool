/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeMomentBalances

@[expose] public section

/-!
# Arbitrary decay of the actual moving-gauge compactification alias

The finite-jet estimates are local in the slow variables. The radial
frequency is finally specialized to the actual manuscript exponent.
-/

noncomputable section

namespace NavierStokes.GaugeAliasDecay

open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval BigOperators
open TorusInverse JetBounds UniformFourierAlias

abbrev Plane := TorusInverse.Plane
abbrev Point (S : Type) := PressureStream.Lift S

section FiberInverse

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

noncomputable def fiberShell (a b : ℝ) (s : S) : Set (Point S) :=
  {z | z.1 ∈ Icc a b ∧ z.2.1 = s}

/-- The torus inverse estimate uses only jets on the designated slow fiber. -/
theorem familyInverse_finiteJets_fiber (d : Direction) (a b : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Point S → ℂ), ContDiff ℝ ∞ f →
      SmoothFamilyTorusInverse.Periodic (toProduct f) → ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      FiniteJetBound (m + 5) f (fiberShell a b s) C →
      FiniteJetBound m (familyInverse d f) (fiberShell a b s) (K * C) := by
  obtain ⟨K, hK, hb⟩ := SmoothFamilyTorusInverse.inverse_finiteJets (P := ℝ × S) d m
  refine ⟨K, hK, ?_⟩
  intro f hf hp C hC s hsource
  have hin : SmoothFamilyTorusInverse.JetBound (toProduct f) (Icc a b ×ˢ {s}) (m + 5) C := by
    intro j hj p hpA Y
    rw [norm_iteratedFDeriv_toProduct]
    exact hsource j hj (p.1, (p.2, Y)) ⟨hpA.1, Set.mem_singleton_iff.mp hpA.2⟩
  have hout := hb (toProduct f) (Icc a b ×ˢ {s}) C (toProduct_smooth hf) hp hC hin
  intro j hj z hz
  change ‖iteratedFDeriv ℝ j (fromProduct (SmoothFamilyTorusInverse.inverse d (toProduct f))) z‖ ≤ _
  rw [norm_iteratedFDeriv_fromProduct]
  exact hout j hj (z.1, z.2.1) ⟨hz.1, Set.mem_singleton_iff.mpr hz.2⟩ z.2.2

theorem sourceJet_finiteJets_fiber (d : Direction) (a b : ℝ) (p m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Point S → ℂ), Admissible a b f →
      ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      FiniteJetBound (m + 6 * p) f (fiberShell a b s) C →
      FiniteJetBound m (RadialAlias.sourceJet (familyInverse d) f p) (fiberShell a b s) (K * C) :=
        by
  induction p generalizing m with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro f _ C _ s hb
    simpa only [Nat.mul_zero, Nat.add_zero, RadialAlias.sourceJet_zero, one_mul] using hb
  | succ p ih =>
    obtain ⟨A, hA, ha⟩ := ih (m + 1 + 5)
    obtain ⟨B, hB, hb⟩ := familyInverse_finiteJets_fiber (S := S) d a b (m + 1)
    refine ⟨B * A, mul_nonneg hB hA, ?_⟩
    intro f hf C hC s hsource
    have hg := sourceJet_mem (Admissible a b) (familyInverse d)
      (fun _ hh => admissible_step d hh) p hf
    have hin : FiniteJetBound (m + 1 + 5 + 6 * p) f (fiberShell a b s) C := by
      convert! hsource using 1
      omega
    have hprev := ha f hf C hC s hin
    have hi := hb _ hg.1 hg.2.1 (A * C) (mul_nonneg hA hC) s hprev
    have hd := finiteJetBound_fixedPartial (familyInverse_smooth d hg.1 hg.2.1) hi
      ((1 : ℝ), (0 : S × Plane)) (by simp)
    rw [RadialAlias.sourceJet_succ]
    simp only [mul_assoc]
    exact hd

/-- Every IBP step costs six genuine source-jet orders. The constant is
chosen before the slow point, source, or frequency. -/
theorem totalIntegral_finiteJets_fiber (d : Direction) {a b : ℝ}
    (hab : a ≤ b) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Point S → ℂ), Admissible a b f →
      ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      FiniteJetBound (m + 6 * p) f (fiberShell a b s) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : Point S, z.2.1 = s →
        ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M ((0 : S), vector d) f) z‖ ≤
          K * C * (|M|⁻¹) ^ p := by
  obtain ⟨B, hB, hb⟩ := sourceJet_finiteJets_fiber (S := S) d a b p m
  refine ⟨B * (b - a), mul_nonneg hB (sub_nonneg.mpr hab), ?_⟩
  intro f hf C hC s hsource M hM j hj z hz
  have hgood (n : ℕ) := sourceJet_mem (Admissible a b) (familyInverse d)
    (fun _ hh => admissible_step d hh) n hf
  have hg := hgood p
  have hbound := hb f hf C hC s hsource
  have heq : TransportPrimitive.totalIntegral M ((0 : S), vector d) f = fun z =>
      (-M⁻¹) ^ p • TransportPrimitive.totalIntegral M ((0 : S), vector d)
        (RadialAlias.sourceJet (familyInverse d) f p) z := by
    funext w
    rw [TransportPrimitive.totalIntegral_eq_wholeAlias hf.1.continuous hf.2.2.2,
      TransportPrimitive.totalIntegral_eq_wholeAlias hg.1.continuous hg.2.2.2]
    exact RadialAlias.wholeAlias_sourceJet (familyInverse d) f p hM
      (fun n _ => (familyInverse_smooth d (hgood n).1 (hgood n).2.1).of_le (by simp))
      (fun n _ => familyInverse_supported d (hgood n).2.2.2)
      (fun n _ => familyInverse_solves d (hgood n).1 (hgood n).2.1 (hgood n).2.2.1)
  rw [heq, iteratedFDeriv_const_smul_apply'
    ((TransportPrimitive.totalIntegral_contDiff hg.1 hg.2.2.2).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt]
  have hn := norm_smul ((-M⁻¹) ^ p : ℝ)
    (iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M ((0 : S), vector d)
      (RadialAlias.sourceJet (familyInverse d) f p)) z)
  rw [hn, Real.norm_eq_abs, abs_pow, abs_neg, abs_inv, mul_comm]
  have hnorm := PhysicalMeanDomain.totalIntegral_jet_bound_fiber (M := M) hab (vector d)
    hg.1 hg.2.2.2 j z (B * C) (fun R hR Y => hbound j hj (R, (z.2.1, Y)) ⟨hR, hz⟩)
  calc
    _ ≤ (B * C * (b - a)) * (|M|⁻¹) ^ p :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ = _ := by ring

theorem real_totalIntegral_finiteJets_fiber (d : Direction) {a b : ℝ}
    (hab : a ≤ b) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Point S → ℝ), ContDiff ℝ ∞ f → SourcePeriodic f →
      (∀ q, sourceMean f q = 0) → RadialAlias.RadiallySupported a b f →
      ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      FiniteJetBound (m + 6 * p) f (fiberShell a b s) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : Point S, z.2.1 = s →
        ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M ((0 : S), vector d) f) z‖ ≤
          K * C * (|M|⁻¹) ^ p := by
  obtain ⟨K, hK, hb⟩ := totalIntegral_finiteJets_fiber (S := S) d hab m p
  refine ⟨K, hK, ?_⟩
  intro f hf hp hm hs C hC s hsource M hM j hj z hz
  rw [← norm_iteratedFDeriv_totalIntegral_complexify hf hs]
  apply hb (complexify f) (admissible_complexify hf hp hm hs) C hC s _ M hM j hj z hz
  intro i hi x hx
  rw [norm_iteratedFDeriv_complexify hf]
  exact hsource i hi x hx

theorem realCenterSource_finiteJets_fiber (a b : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Point S → ℝ), ContDiff ℝ ∞ f → SourcePeriodic f →
      ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      FiniteJetBound (m + 4) f (fiberShell a b s) C →
      FiniteJetBound m (realCenterSource f) (fiberShell a b s) (K * C) := by
  obtain ⟨K, hK, hb⟩ := realCentered_finiteJets (P := ℝ × S) m
  refine ⟨K, hK, ?_⟩
  intro f hf hp C hC s hsource
  have hin : ∀ j ≤ m + 4, ∀ p ∈ Icc a b ×ˢ ({s} : Set S), ∀ Y,
      ‖iteratedFDeriv ℝ j (toProduct f) (p, Y)‖ ≤ C := by
    intro j hj q hq Y
    rw [norm_iteratedFDeriv_toProduct]
    exact hsource j hj (q.1, (q.2, Y)) ⟨hq.1, Set.mem_singleton_iff.mp hq.2⟩
  have hout := hb (toProduct f) (Icc a b ×ˢ ({s} : Set S)) C (toProduct_smooth hf)
    (fun q => hp q.1 q.2) hC hin
  intro j hj z hz
  change ‖iteratedFDeriv ℝ j (fromProduct (realCentered (toProduct f))) z‖ ≤ _
  rw [norm_iteratedFDeriv_fromProduct]
  exact hout j hj (z.1, z.2.1) ⟨hz.1, Set.mem_singleton_iff.mpr hz.2⟩ z.2.2

/-- Radial mean zero suffices. Subtracting the torus mean changes the exact
total integral by zero and costs four additional source orders. -/
theorem real_totalIntegral_finiteJets_fiber_of_mass_zero (d : Direction) {a b : ℝ}
    (hab : a ≤ b) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Point S → ℝ), ContDiff ℝ ∞ f → SourcePeriodic f →
      (∀ s, (∫ R in a..b, sourceMean f (R, s)) = 0) → RadialAlias.RadiallySupported a b f →
      ∀ C : ℝ, 0 ≤ C → ∀ s : S,
      FiniteJetBound (m + 6 * p + 4) f (fiberShell a b s) C →
      ∀ M : ℝ, M ≠ 0 → ∀ j ≤ m, ∀ z : Point S, z.2.1 = s →
        ‖iteratedFDeriv ℝ j (TransportPrimitive.totalIntegral M ((0 : S), vector d) f) z‖ ≤
          K * C * (|M|⁻¹) ^ p := by
  obtain ⟨A, hA, ha⟩ := real_totalIntegral_finiteJets_fiber (S := S) d hab m p
  obtain ⟨B, hB, hb⟩ := realCenterSource_finiteJets_fiber (S := S) a b (m + 6 * p)
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro f hf hp hm hs C hC s hsource M hM j hj z hz
  have he : TransportPrimitive.totalIntegral M ((0 : S), vector d) f =
      TransportPrimitive.totalIntegral M ((0 : S), vector d) (realCenterSource f) :=
    funext fun x => (totalIntegral_realCenterSource hf hp hs hm x).symm
  rw [he]
  have hh := ha (realCenterSource f) (realCenterSource_smooth hf hp) (realCenterSource_periodic hp)
    (realCenterSource_zeroMean hf hp) (realCenterSource_supported hs) (B * C) (mul_nonneg hB hC) s
    (hb f hf hp C hC s hsource) M hM j hj z hz
  simpa only [mul_assoc] using hh

end FiberInverse

section PhysicalIntegral

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

omit [FiniteDimensional ℝ S] in
theorem normalizeSource_mean_integral {c e d : ℝ} (hc : 0 < c) (hce : c < e) (hd : 0 < d)
    {f : Point S → ℝ} (hf : ContDiff ℝ ∞ f) (hs : RadialAlias.RadiallySupported c e f) (s : S) :
    (∫ u in (c ^ d)..(e ^ d), sourceMean (RadialPullback.normalizeSource d c f) (u, s)) =
      PressureStream.pressureMass f s := by
  have he (u : ℝ) : sourceMean (RadialPullback.normalizeSource d c f) (u, s) =
      RadialPullback.normalizeSource d c (PressureStream.torusAverage f) (u, s) := by
    change PressureStream.torusAverage (RadialPullback.normalizeSource d c f) (u, s) = _
    rw [TemporalMeanUpdate.normalizeSource_torusAverage]
    rfl
  simp_rw [he]
  have hi := RadialPullback.normalized_radial_integral hc hd hce.le
    (PressureStream.torusAverage_contDiff hf) 0 0 (0 : S) s
  simp only [zero_mul, zero_smul, add_zero] at hi
  rw [hi, PressureStream.pressureMass_eq_interval hf hs]

theorem physicalTotal_finiteJets_fiber (direction : Direction) {c e d : ℝ}
    (hc : 0 < c) (hce : c < e) (hd : 0 < d) (rlo rhi : ℝ) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Point S → ℝ), ContDiff ℝ ∞ f →
      RadialAlias.RadiallySupported c e f → SourcePeriodic f →
      (∀ s, PressureStream.pressureMass f s = 0) → ∀ A : ℝ, 0 ≤ A → ∀ s : S,
      (∀ j ≤ m + 6 * p + 4, ∀ R ∈ Ioo c e, ∀ Y : Plane,
        ‖iteratedFDeriv ℝ j f (R, (s, Y))‖ ≤ A) →
      ∀ M : ℝ, M ≠ 0 → ∀ z : Point S, z.1 ∈ Icc rlo rhi → z.2.1 = s → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (PressureStream.physicalTotal d c M ((0 : S), vector direction) f) z‖ ≤
          K * A * (|M|⁻¹) ^ p := by
  obtain ⟨KN, hKN, hbN⟩ := VariableGaugeMean.normalizeSource_unweighted_fiber (S := S)
    hc hce hd (m + 6 * p + 4)
  obtain ⟨KT, hKT, hbT⟩ := real_totalIntegral_finiteJets_fiber_of_mass_zero (S := S) direction
    (Real.rpow_le_rpow hc.le hce.le hd.le) m p
  obtain ⟨KP, hKP, hbP⟩ := RadialPullback.radial_comp_finiteJets_uniform
    (E := S × Plane) (V := ℝ) rlo rhi (RadialPullback.powerChart_contDiff hc d) m
  refine ⟨KP * KT * KN, mul_nonneg (mul_nonneg hKP hKT) hKN, ?_⟩
  intro f hf hs hp hm A hA s hin M hM z hz hzs j hj
  have hN := RadialPullback.normalizeSource_contDiff hc hd hf
  have hsN := RadialPullback.normalizeSource_supported hc hce hd hs
  have hpN := TemporalMeanUpdate.normalizeSource_periodic d c hp
  have hmN (t : S) : (∫ u in (c ^ d)..(e ^ d),
      sourceMean (RadialPullback.normalizeSource d c f) (u, t)) = 0 := by
    rw [normalizeSource_mean_integral hc hce hd hf hs, hm]
  have hbound : FiniteJetBound (m + 6 * p + 4) (RadialPullback.normalizeSource d c f)
      (fiberShell (c ^ d) (e ^ d) s) (KN * A) := by
    intro k hk w hw
    exact hbN f hf hs A hA s hin w hw.2 k hk
  have htot := hbT _ hN hpN hmN hsN (KN * A) (mul_nonneg hKN hA) s hbound M hM
  have hA' : 0 ≤ KT * (KN * A) * (|M|⁻¹) ^ p := by positivity
  have hh := hbP (TransportPrimitive.totalIntegral M ((0 : S), vector direction)
    (RadialPullback.normalizeSource d c f)) (TransportPrimitive.totalIntegral_contDiff hN hsN)
    z hz _ hA' (fun k hk => htot k hk (RadialPullback.liftChart
      (RadialPullback.powerChart d c) z) hzs) j hj
  exact hh.trans_eq (by ring)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S] in
theorem pressureMass_localize (χ : S → ℝ) (f : Point S → ℝ) (s : S) :
    PressureStream.pressureMass (PhysicalMeanDomain.localize χ f) s =
      χ s * PressureStream.pressureMass f s := by
  have hh := GaugeMomentBalances.radialMoment_localize 0 χ (fun _ => f) 0 s
  simpa only [CorrectionState.radialMoment, GaugeMomentBalances.localizeFamily,
    pow_zero, one_mul] using hh

/-- Slow localization is removed by germ equality. No derivative bound on
the auxiliary slow cutoff enters the constant. -/
theorem physicalTotal_finiteJets_local (direction : Direction) {c e d : ℝ}
    (hc : 0 < c) (hce : c < e) (hd : 0 < d) (rlo rhi : ℝ) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : Set S), IsOpen U → ∀ (f : Point S → ℝ),
      ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U) →
      PhysicalMeanDomain.SupportedOn c e U f → PhysicalMeanDomain.PeriodicOn U f →
      (∀ s ∈ U, PressureStream.pressureMass f s = 0) → ∀ A : ℝ, 0 ≤ A →
      ∀ M : ℝ, M ≠ 0 → ∀ z : Point S, z.2.1 ∈ U → z.1 ∈ Icc rlo rhi →
      (∀ j ≤ m + 6 * p + 4, ∀ R ∈ Ioo c e, ∀ Y : Plane,
        ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y))‖ ≤ A) → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (PressureStream.physicalTotal d c M ((0 : S), vector direction) f) z‖ ≤
          K * A * (|M|⁻¹) ^ p := by
  obtain ⟨K, hK, hb⟩ := physicalTotal_finiteJets_fiber (S := S) direction hc hce hd rlo rhi m p
  refine ⟨K, hK, ?_⟩
  intro U hU f hf hs hp hm A hA M hM z hz hR hin j hj
  obtain ⟨χ, _, hχs, hχf, he⟩ := PhysicalMeanDomain.exists_fiber_localization hU hz hf
  have hχsup := PhysicalMeanDomain.localize_supported hχs hs
  have hχper := PhysicalMeanDomain.localize_periodic hχs hp
  have hχmass (s : S) : PressureStream.pressureMass (PhysicalMeanDomain.localize χ f) s = 0 := by
    rw [pressureMass_localize]
    by_cases hc : χ s = 0
    · rw [hc, zero_mul]
    · rw [hm s (hχs (subset_tsupport χ hc)), mul_zero]
  have hbound := hb (PhysicalMeanDomain.localize χ f) hχf hχsup hχper hχmass A hA z.2.1
    (fun k hk R hR Y => by rw [he.jet_eq k R Y]; exact hin k hk R hR Y)
    M hM z hR rfl j hj
  rw [((VariableGaugeMean.physicalTotal_fiberLocal d c M (vector direction)).germ he).jet_eq
    j z.1 z.2.2] at hbound
  exact hbound

end PhysicalIntegral

section MovingAlias

open VariableGaugeMean LocalSignedRequest WeightedClasses

/-- Source-uniform arbitrary inverse-frequency gain for the actual moving
alias. The input seminorm uses one entire slow fiber, never all slow space. -/
theorem compactAlias_finiteJets_local {coord a b d : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (direction : Direction) (m p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : Point Plane → ℝ),
      ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier) →
      SupportedGauge a b (qLength coord) U.carrier f → PhysicalMeanDomain.PeriodicOn U.carrier f →
      (∀ s ∈ U.carrier, PressureStream.pressureMass f s = 0) →
      ∀ A : ℝ, 0 ≤ A → ∀ M : ℝ, M ≠ 0 → ∀ z : Point Plane, z.2.1 ∈ U.carrier →
      (∀ j ≤ m + 6 * p + 4, ∀ R : ℝ, ∀ Y : Plane,
        ‖iteratedFDeriv ℝ j f (R, (z.2.1, Y))‖ ≤ A) → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (compactAlias d a b M (qLength coord) (vector direction) f) z‖ ≤
          K * A * (|M|⁻¹) ^ p := by
  obtain ⟨c, e, _, hc, hce, _, hl, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  obtain ⟨K, hK, hbK⟩ := physicalTotal_finiteJets_local (S := Plane) direction hc hce hd c e m p
  let V : Set (Point Plane) := {z | z.2.1 ∈ U.carrier ∧ z.1 ∈ Icc c e}
  obtain ⟨B, hB, hbB⟩ := cutoffRadialDerivative_q_finiteJets U.coord_pos U.coord_lt_one U.qlo_pos
    ha d b (V := V) (fun z hz => U.time_pos z.2.1 hz.1) (fun z hz => U.q_mem z.2.1 hz.1)
    (fun _ hz => hz.2) m
  have hC := cutoffRadialDerivative_contDiffOn ha d b
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun s hs => U.time_pos s hs)) hl
  refine ⟨(2 : ℝ) ^ m * B * K, by positivity, ?_⟩
  intro f hf hs hp hm A hA M hM z hz hin j hj
  have hfixed : PhysicalMeanDomain.SupportedOn c e U.carrier f := fun x hx hn =>
    ⟨(hleft _ hx).trans (hs x hx hn).1, (hs x hx hn).2.trans (hright _ hx)⟩
  have hAfixed : PhysicalMeanDomain.SupportedOn c e U.carrier
      (compactAlias d a b M (qLength coord) (vector direction) f) := fun x hx hn =>
    ⟨(hleft _ hx).trans (compactAlias_q_supportedGauge U ha hab hd M (vector direction) f x hx
      hn).1,
      (compactAlias_q_supportedGauge U ha hab hd M (vector direction) f x hx hn).2.trans (hright _
        hx)⟩
  by_cases hr : z.1 ∈ Ioo c e
  · have hJ := physicalTotal_contDiffOn (M := M) hc hce hd (vector direction) U.isOpen hf hfixed
    have he : compactAlias d a b M (qLength coord) (vector direction) f =ᶠ[𝓝 z]
        (fun x => cutoffRadialDerivative d a b (qLength coord) x *
          PressureStream.physicalTotal d c M ((0 : Plane), vector direction) f x) := by
      filter_upwards [(PhysicalMeanDomain.slowDomain_open U.isOpen).mem_nhds hz] with x hx
      exact compactAlias_reference hc ha hab hd (qLength coord) (vector direction) hl hleft hs x hx
    rw [MeanRankUpdate.iteratedFDeriv_congr_germ he j]
    have hh := product_jet_bound (PhysicalMeanDomain.slowDomain_open U.isOpen) hC hJ hz hj hB
      (show 0 ≤ K * A * (|M|⁻¹) ^ p by positivity)
      (fun i hi => hbB i hi z ⟨hz, hr.1.le, hr.2.le⟩)
      (fun i hi => hbK U.carrier U.isOpen f hf hfixed hp hm A hA M hM z hz
        ⟨hr.1.le, hr.2.le⟩ (fun k hk R _ Y => hin k hk R Y) i hi)
    exact hh.trans_eq (by ring)
  · rw [PhysicalMeanDomain.jet_zero_outside U.isOpen
      (compactAlias_q_contDiffOn U ha hab hd M (vector direction) hf hs) hAfixed hz hr j, norm_zero]
    positivity

theorem localBandJets_compactAlias_gain {coord a b d α κ B : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (direction : Direction)
    (ε L M : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hκ : 0 < κ) (hB : 0 ≤ B) (q : ℕ) (hM : ∀ n, M n ≠ 0)
    (hfreq : ∀ n, |M n|⁻¹ ≤ B * ε n ^ κ * L n ^ q)
    {f : ℕ → Point Plane → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hm : ∀ n s, s ∈ U.carrier → PressureStream.pressureMass (f n) s = 0)
    (hsource : PhysicalMeanDomain.LocalBandJets U.carrier ε L α f) (β : ℝ) :
    PhysicalMeanDomain.LocalBandJets U.carrier ε L β
      (fun n => compactAlias d a b (M n) (qLength coord) (vector direction) (f n)) := by
  obtain ⟨p, hpnat⟩ := exists_nat_gt ((β - α) / κ)
  have horder : β ≤ α + κ * (p : ℝ) := by
    have hh := (div_lt_iff₀ hκ).mp hpnat
    nlinarith
  intro m
  obtain ⟨K, hK, hbK⟩ := compactAlias_finiteJets_local U ha hab hd direction m p
  obtain ⟨C, hC, k, hbC⟩ := hsource (m + 6 * p + 4)
  refine ⟨K * C * B ^ p, by positivity, k + q * p, ?_⟩
  intro n z hz j hj
  have hA : 0 ≤ C * ε n ^ α * L n ^ k :=
    mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (hε n) α).le)
      (pow_nonneg (zero_le_one.trans (hL n)) _)
  have hbound := hbK (f n) (hf n) (hs n) (hp n) (hm n) _ hA (M n) (hM n) z hz
    (fun i hi R Y => hbC n (R, (z.2.1, Y)) hz i hi) j hj
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg (M n))) (hfreq n) p
  have hLn : 0 ≤ L n := zero_le_one.trans (hL n)
  calc
    _ ≤ K * (C * ε n ^ α * L n ^ k) * (|M n|⁻¹) ^ p := hbound
    _ ≤ K * (C * ε n ^ α * L n ^ k) * (B * ε n ^ κ * L n ^ q) ^ p :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hK hA)
    _ = (K * C * B ^ p) * ε n ^ (α + κ * (p : ℝ)) * L n ^ (k + q * p) := by
      rw [Real.rpow_add (hε n), Real.rpow_mul_natCast (hε n).le, pow_add, pow_mul, mul_pow, mul_pow]
      ring
    _ ≤ (K * C * B ^ p) * ε n ^ β * L n ^ (k + q * p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (hε n) (hεone n) horder) (by positivity))
        (pow_nonneg hLn _)

end MovingAlias

section ActualFrequency

/-- A finite initial set of bands does not change an all-band bound with a
strictly positive weight. This lemma constructs its enlarged constant. -/
theorem scalar_bound_of_tail (f w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    (A : ℝ) (hA : 0 ≤ A) (N : ℕ) (htail : ∀ n, N ≤ n → |f n| ≤ A * w n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |f n| ≤ C * w n := by
  let B := ∑ n ∈ Finset.range N, |f n| / w n
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n _ => div_nonneg (abs_nonneg _) (hw n).le)
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · exact (htail n hn).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (hw n).le)
  · have hterm : |f n| / w n ≤ B :=
      Finset.single_le_sum (fun k _ => div_nonneg (abs_nonneg _) (hw k).le)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))
    calc
      |f n| = (|f n| / w n) * w n := (div_mul_cancel₀ _ (hw n).ne').symm
      _ ≤ B * w n := mul_le_mul_of_nonneg_right hterm (hw n).le
      _ ≤ (A + B) * w n := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (hw n).le

theorem radialFrequency_abs (h : ℝ) (n i : ℕ) (d Mbase : ℝ) :
    |MeanChartCompatibility.radialFrequency h n i d Mbase| =
      |Mbase| * ChartScales.Lambda ^ i * ChartScales.Q n ^ (d / 2) := by
  rw [MeanChartCompatibility.radialFrequency, abs_mul, abs_mul,
    abs_of_pos (pow_pos ChartScales.Lambda_pos _),
    abs_of_pos (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)]

theorem radialFrequency_ne_zero (h : ℝ) (n i : ℕ) (d : ℝ)
    {Mbase : ℝ} (hM : Mbase ≠ 0) :
    MeanChartCompatibility.radialFrequency h n i d Mbase ≠ 0 :=
  mul_ne_zero (mul_ne_zero hM (pow_ne_zero _ ChartScales.Lambda_pos.ne'))
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).ne'

theorem radialFrequency_inv_compare {h Mbase : ℝ} {n i D : ℕ} (hM : Mbase ≠ 0)
    (hgap : ChartScales.nativeIndex h n ≤ i + D) :
    |MeanChartCompatibility.radialFrequency h n i (ChartScales.radialExponent h) Mbase|⁻¹ ≤
      (ChartScales.Lambda ^ D / |Mbase|) * (ChartScales.radialCoefficient h n)⁻¹ := by
  have hMp := abs_pos.mpr (radialFrequency_ne_zero h n i (ChartScales.radialExponent h) hM)
  have hcoef := ChartScales.radialCoefficient_pos h n
  have hbase := abs_pos.mpr hM
  have hle : ChartScales.radialCoefficient h n ≤ (ChartScales.Lambda ^ D / |Mbase|) *
      |MeanChartCompatibility.radialFrequency h n i (ChartScales.radialExponent h) Mbase| := by
    calc
      _ ≤ ChartScales.Lambda ^ (i + D) * ChartScales.Q n ^ (ChartScales.radialExponent h / 2) :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by linarith [ChartScales.Lambda_two_lt]) hgap)
          (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le
      _ = _ := by
        rw [radialFrequency_abs, pow_add]
        field_simp
  have hh : 1 / |MeanChartCompatibility.radialFrequency h n i (ChartScales.radialExponent h) Mbase|
    ≤
      (ChartScales.Lambda ^ D / |Mbase|) / ChartScales.radialCoefficient h n :=
    (div_le_div_iff₀ hMp hcoef).mpr (by simpa only [one_mul] using hle)
  simpa only [one_div, div_eq_mul_inv, one_mul] using hh

/-- The inverse frequency has a positive epsilon power in every band for
the actual graph exponent. The finite initial bands are included. -/
theorem actual_inverse_frequency_bound {h Mbase : ℝ} (hh : 0 < h) (hM : Mbase ≠ 0)
    (index : ℕ → ℕ) (D : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ q : ℕ, ∀ n,
      |MeanChartCompatibility.radialFrequency h n (index n) (ChartScales.radialExponent h) Mbase|⁻¹
        ≤
        B * ChartScales.epsilon h n ^ ChartScales.kappa * L n ^ q := by
  obtain ⟨q, hq⟩ := exists_nat_ge ChartScales.rho
  let A := (ChartScales.Lambda ^ D / |Mbase|) * ChartScales.Lambda
  have hfactor : 0 ≤ ChartScales.Lambda ^ D / |Mbase| :=
    div_nonneg (pow_nonneg ChartScales.Lambda_pos.le _) (abs_nonneg _)
  have hA : 0 ≤ A := mul_nonneg hfactor ChartScales.Lambda_pos.le
  have hLpos (n : ℕ) : 0 < L n := zero_lt_one.trans_le (hL n)
  have hw (n : ℕ) : 0 < ChartScales.epsilon h n ^ ChartScales.kappa * L n ^ q :=
    mul_pos (Real.rpow_pos_of_pos (ChartScales.epsilon_pos h n) _) (pow_pos (hLpos n) _)
  have htail (n : ℕ) (hn : 4 ≤ n) :
      |(MeanChartCompatibility.radialFrequency h n (index n) (ChartScales.radialExponent h)
        Mbase)⁻¹| ≤
        A * (ChartScales.epsilon h n ^ ChartScales.kappa * L n ^ q) := by
    have hSL : ChartScales.S n ^ ChartScales.rho ≤ L n ^ q := by
      calc
        _ ≤ L n ^ ChartScales.rho :=
          Real.rpow_le_rpow (sq_nonneg (n : ℝ)) (hS n) ChartScales.rho_pos.le
        _ ≤ L n ^ (q : ℝ) := Real.rpow_le_rpow_of_exponent_le (hL n) hq
        _ = _ := Real.rpow_natCast _ _
    rw [abs_inv]
    calc
      _ ≤ (ChartScales.Lambda ^ D / |Mbase|) * (ChartScales.radialCoefficient h n)⁻¹ :=
        radialFrequency_inv_compare hM (hgap n)
      _ ≤ (ChartScales.Lambda ^ D / |Mbase|) *
          (ChartScales.Lambda * ChartScales.epsilon h n ^ ChartScales.kappa * ChartScales.S n ^
            ChartScales.rho) :=
        mul_le_mul_of_nonneg_left (ChartScales.radialCoefficient_inv_upper h hh.le hn) hfactor
      _ ≤ (ChartScales.Lambda ^ D / |Mbase|) *
          (ChartScales.Lambda * ChartScales.epsilon h n ^ ChartScales.kappa * L n ^ q) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSL
          (mul_nonneg ChartScales.Lambda_pos.le
            (Real.rpow_pos_of_pos (ChartScales.epsilon_pos h n) _).le)) hfactor
      _ = _ := by dsimp [A]; ring
  obtain ⟨B, hB, hb⟩ := scalar_bound_of_tail
    (fun n => (MeanChartCompatibility.radialFrequency h n (index n) (ChartScales.radialExponent h)
      Mbase)⁻¹)
    (fun n => ChartScales.epsilon h n ^ ChartScales.kappa * L n ^ q) hw A hA 4 htail
  refine ⟨B, hB, q, ?_⟩
  intro n
  simpa only [abs_inv, mul_assoc] using hb n

/-- The actual common fast coefficient is uniformly bounded when the common
index stays a bounded amount above the native one. -/
theorem actual_fast_coefficient_bound {h : ℝ} (hh : 0 < h)
    (index : ℕ → ℕ) (D : ℕ) (hgap : ∀ n, index n ≤ ChartScales.nativeIndex h n + D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      |ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h)| ≤ C := by
  have htail (n : ℕ) (hn : 4 ≤ n) :
      |ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h)| ≤ ChartScales.Tg ^ D * (1 : ℝ) := by
    rw [abs_of_pos (mul_pos (pow_pos ChartScales.Tg_pos _) (Real.rpow_pos_of_pos (ChartScales.Q_pos
      n) _))]
    calc
      _ ≤ ChartScales.Tg ^ (ChartScales.nativeIndex h n + D) * ChartScales.Q n ^ (1 + h) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ChartScales.Tg_one_lt.le (hgap n))
          (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le
      _ = ChartScales.Tg ^ D * ChartScales.timeCoefficient h n := by
        rw [pow_add, ChartScales.timeCoefficient]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        simpa only [Real.norm_eq_abs, abs_of_pos (ChartScales.timeCoefficient_pos h n)] using
          TemporalMeanUpdate.timeCoefficient_norm_le_one hh.le hn) (pow_pos ChartScales.Tg_pos _).le
  obtain ⟨C, hC, hb⟩ := scalar_bound_of_tail
    (fun n => ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h)) (fun _ => 1)
    (fun _ => zero_lt_one) (ChartScales.Tg ^ D) (pow_pos ChartScales.Tg_pos _).le 4 htail
  exact ⟨C, hC, by simpa only [mul_one] using hb⟩

end ActualFrequency

section ClassConclusions

open VariableGaugeMean LocalSignedRequest WeightedClasses

/-- Every target order is obtained for the literal moving alias at the
actual radial frequency. Only the lower bound on the common index is used. -/
theorem meanClass_compactAlias_superflat {coord a b h Mbase α : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (hh : 0 < h) (hM : Mbase ≠ 0) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
    {f : ℕ → Point Plane → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hm : ∀ n s, s ∈ U.carrier → PressureStream.pressureMass (f n) s = 0)
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α f) (β : ℝ) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) β
      (fun n => compactAlias (ChartScales.radialExponent h) a b
        (MeanChartCompatibility.radialFrequency h n (index n) (ChartScales.radialExponent h) Mbase)
        (qLength coord) (vector .radial) (f n)) := by
  have hd := ChartScales.radialExponent_pos h hh.le
  obtain ⟨B, hB, q, hfreq⟩ := actual_inverse_frequency_bound hh hM index D hgap L hL hS
  have hsrc := meanClass_moving_localBandJets U ha hcL hcR (ChartScales.epsilon h) L
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL hf hs hclass
  have hβ := localBandJets_compactAlias_gain U ha hab hd .radial
    (ChartScales.epsilon h) L
    (fun n => MeanChartCompatibility.radialFrequency h n (index n) (ChartScales.radialExponent h)
      Mbase)
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL
    (by norm_num [ChartScales.kappa]) hB q
    (fun n => radialFrequency_ne_zero h n (index n) (ChartScales.radialExponent h) hM)
    hfreq hf hs hp hm hsrc β
  obtain ⟨c, e, hac, _, heb, hsup⟩ := compactAlias_interior_support (S := Plane) ha hab hd
  apply localBandJets_meanClass_of_gaugeInteriorSupport U ha hcL hcR (ChartScales.epsilon h) L
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL hac heb
    (fun n => compactAlias_q_contDiffOn U ha hab hd _ _ (hf n) (hs n))
    (fun n => hsup (qLength coord) U.carrier
      (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)) _ _ (f n)) hβ

theorem meanClass_dividedAlias_superflat {coord a b h Mbase α : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (hh : 0 < h) (hM : Mbase ≠ 0) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
    {f : ℕ → Point Plane → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hm : ∀ n s, s ∈ U.carrier → PressureStream.pressureMass (f n) s = 0)
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α f) (β : ℝ) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) β
      (fun n => PressureStream.divideRadius (compactAlias (ChartScales.radialExponent h) a b
        (MeanChartCompatibility.radialFrequency h n (index n) (ChartScales.radialExponent h) Mbase)
        (qLength coord) (vector .radial) (f n))) :=
  meanClass_divideRadius_moving U ha hcL hcR (ChartScales.epsilon h) L
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL
    (meanClass_compactAlias_superflat U ha hab hcL hcR hh hM index D hgap L hL hS hf hs hp hm
      hclass β)

theorem actual_fast_coefficient_bandBound (s : StripData (Point Plane)) {h : ℝ} (hh : 0 < h)
    (index : ℕ → ℕ) (D : ℕ) (hgap : ∀ n, index n ≤ ChartScales.nativeIndex h n + D) :
    BandBound s 0 (fun n => ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h)) := by
  obtain ⟨C, hC, hb⟩ := actual_fast_coefficient_bound hh index D hgap
  refine ⟨C, hC, 0, ?_⟩
  intro n
  simpa only [Real.norm_eq_abs, Real.rpow_zero, pow_zero, mul_one] using hb n

/-- The common fast derivative is the actual coefficient at the common
integer index. Its bounded-gap ratio to the native coefficient is proved. -/
theorem meanClass_fastAtIndex (s : StripData (Point Plane)) {h α : ℝ} (hh : 0 < h)
    (index : ℕ → ℕ) (D : ℕ) (hgap : ∀ n, index n ≤ ChartScales.nativeIndex h n + D)
    {f : ℕ → Point Plane → ℝ} (hf : MeanClass s α f) :
    MeanClass s α (fun n => MeanChartCompatibility.fastAtIndex h n (index n) (f n)) := by
  have hd := hf.directional ((0 : ℝ), ((0 : Plane), vector .temporal))
  have hb := hd.band_smul (actual_fast_coefficient_bandBound s hh index D hgap)
  simp only [add_zero, smul_eq_mul] at hb ⊢
  exact hb

theorem meanClass_fastDividedAlias_superflat {coord a b h Mbase α : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (hh : 0 < h) (hM : Mbase ≠ 0) (index : ℕ → ℕ) (D : ℕ)
    (hgapLower : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (hgapUpper : ∀ n, index n ≤ ChartScales.nativeIndex h n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
    {f : ℕ → Point Plane → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hm : ∀ n s, s ∈ U.carrier → PressureStream.pressureMass (f n) s = 0)
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α f) (β : ℝ) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) β
      (fun n => MeanChartCompatibility.fastAtIndex h n (index n)
        (PressureStream.divideRadius (compactAlias (ChartScales.radialExponent h) a b
          (MeanChartCompatibility.radialFrequency h n (index n) (ChartScales.radialExponent h)
            Mbase)
          (qLength coord) (vector .radial) (f n)))) :=
  meanClass_fastAtIndex _ hh index D hgapUpper
    (meanClass_dividedAlias_superflat U ha hab hcL hcR hh hM index D hgapLower L hL hS hf hs hp hm
      hclass β)

end ClassConclusions

section ActualTemporalAlias

open VariableGaugeMean LocalSignedRequest WeightedClasses

noncomputable def temporalSource (h : ℝ) (index : ℕ → ℕ)
    (f : ℕ → Point Plane → ℝ) : ℕ → Point Plane → ℝ :=
  fun n => PressureStream.weightedSource (MeanChartCompatibility.temporalAtIndex h n (index n) (f
    n))

theorem temporalAtIndex_zeroMean_on {coord : ℝ} (U : SlowRegion coord) (h : ℝ) (n i : ℕ)
    {f : Point Plane → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : PhysicalMeanDomain.PeriodicOn U.carrier f) (R : ℝ) {s : Plane} (hs : s ∈ U.carrier) :
    PressureStream.torusAverage (MeanChartCompatibility.temporalAtIndex h n i f) (R, s) = 0 := by
  rw [MeanChartCompatibility.temporalAtIndex_eq_native,
    StateMomentBalances.AuxiliaryAverage.average_const_mul,
    PhysicalMeanDomain.desiredIncrement_zeroMean_on h n U.isOpen hf hp (R, s) hs, mul_zero]

theorem temporalSource_movingField {coord a b : ℝ} (U : SlowRegion coord) (h : ℝ) (index : ℕ → ℕ)
    {f : ℕ → Point Plane → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n)) :
    GaugeMomentBalances.MovingField U a b (temporalSource h index f) := by
  refine ⟨fun n => contDiffOn_fst.mul (temporalAtIndex_contDiffOn h n (index n) U.isOpen (hf n) (hp
    n)), ?_, ?_⟩
  · intro n z hz hn
    exact temporalAtIndex_supportedGauge h n (index n) (hs n) z hz (right_ne_zero_of_mul hn)
  · intro n R s hsm Y k
    exact congrArg (R * ·) (MeanChartCompatibility.temporalAtIndex_periodic h n (index n) (f n) R s
      Y k)

theorem temporalSource_zero_mass {coord : ℝ} (U : SlowRegion coord) (h : ℝ) (index : ℕ → ℕ)
    {f : ℕ → Point Plane → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n)) (n : ℕ)
    {s : Plane} (hs : s ∈ U.carrier) : PressureStream.pressureMass (temporalSource h index f n) s =
      0 := by
  have hz (R : ℝ) : PressureStream.torusAverage (temporalSource h index f n) (R, s) = 0 := by
    rw [temporalSource, PressureStream.torusAverage_weightedSource,
      temporalAtIndex_zeroMean_on U h n (index n) (hf n) (hp n) R hs, mul_zero]
  simp only [PressureStream.pressureMass, hz, integral_zero]

theorem temporalSource_mem {coord a b h α : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    (index : ℕ → ℕ) (D : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
    {f : ℕ → Point Plane → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α f) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α (temporalSource h
        index f) :=
  meanClass_radialMultiply_moving U ha hcL hcR (ChartScales.epsilon h) L
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL contDiff_id
    (meanClass_temporalAtIndex_moving U ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL
      hh.le hS index D hgap hf hp hclass)

/-- The actual stream error in the temporal state update has every target
mean-class order. Its source is the constructed weighted temporal increment. -/
theorem temporalAxialDifference_mem {a b h Mbase α : ℝ} (U : SlowRegion (2 * h))
    (ha : 0 < a) (hab : a < b) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (hh : 0 < h) (hM : Mbase ≠ 0) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
    (c : CorrectionState.Context (Point Plane)) (u : CorrectionState.State (Point Plane))
    (hf : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength (2 * h)) U.carrier (u.axialResidual c n))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α (u.axialResidual c))
        (β : ℝ) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) β
      (temporalAxialDifference (similarityGauge h (ChartScales.radialExponent h) a b Mbase hab
        index)
        h index c u) := by
  have hfield := temporalSource_movingField U h index hf hs hp
  have hsrc := temporalSource_mem U ha hcL hcR hh index D hgap L hL hS hf hp hclass
  have hgain := meanClass_dividedAlias_superflat U ha hab hcL hcR hh hM index D hgap L hL hS
    hfield.smooth hfield.supported hfield.periodic
    (fun n s hs => temporalSource_zero_mass U h index hf hp n hs) hsrc β
  apply MeanRankUpdate.meanClass_congr_on hgain
  intro n z hz
  have hzm := (movingStrip_domain U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL z).mp hz
  have hell := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos z.2.1 hzm.1)
  have hR : z.1 ≠ 0 := ne_of_gt (by
    have hpR : 0 < z.1 / qLength (2 * h) z.2.1 := ha.trans hzm.2.1
    simpa only [zero_mul] using (lt_div_iff₀ hell).mp hpR)
  exact temporalAxialDifference_eq_dividedAlias U
    (similarityGauge h (ChartScales.radialExponent h) a b Mbase hab index)
    ha (ChartScales.radialExponent_pos h hh.le) (fun _ => rfl) c u h index n
    (hf n) (hp n) (hs n) hzm.1 hR

/-- The axial coefficient stored in the actual temporal alias state is
superflat with the true common fast coefficient and torus direction. -/
theorem temporalAliasState_axial_mem {a b h Mbase α : ℝ} (U : SlowRegion (2 * h))
    (ha : 0 < a) (hab : a < b) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (hh : 0 < h) (hM : Mbase ≠ 0) (index : ℕ → ℕ) (D : ℕ)
    (hgapLower : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (hgapUpper : ∀ n, index n ≤ ChartScales.nativeIndex h n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
    (c : CorrectionState.Context (Point Plane)) (u : CorrectionState.State (Point Plane))
    (hfast : c.operators.fastCoefficient = fun n => ChartScales.Tg ^ index n * ChartScales.Q n ^ (1
      + h))
    (hv : c.operators.vT = (0, (0, vector .temporal)))
    (hf : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength (2 * h)) U.carrier (u.axialResidual c n))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α (u.axialResidual c))
        (β : ℝ) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) β
      (fun n z => temporalAliasState
        (similarityGauge h (ChartScales.radialExponent h) a b Mbase hab index) h index c u n (z, 0)
          2) := by
  have hdiff := temporalAxialDifference_mem U ha hab hcL hcR hh hM index D hgapLower L hL hS
    c u hf hs hp hclass β
  have hder := meanClass_fastAtIndex _ hh index D hgapUpper hdiff
  have he := MeanIncrementBounds.Class.neg hder
  simp only [temporalAliasState, Matrix.cons_val_two,
    MeanIncrementBounds.Operators.fastTime, hfast, hv] at he ⊢
  exact he

end ActualTemporalAlias

section ActualPressureAlias

open VariableGaugeMean LocalSignedRequest WeightedClasses

/-- The moving pressure recipe has zero measured mass, derived from its
normalized physical bump, with no imposed zero-mass premise on the raw source. -/
theorem pressureSource_zero_mass {coord a b : ℝ} (U : SlowRegion coord) (hab : a < b)
    {f : Point Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f) {s : Plane} (hsm : s ∈ U.carrier) :
    PressureStream.pressureMass (pressureSource a b hab (qLength coord) f) s = 0 := by
  let F := PhysicalMeanDomain.freezeSlow s f
  have hF : ContDiff ℝ ∞ F := freezeSlow_contDiff U.isOpen hsm hf
  have hFs : RadialAlias.RadiallySupported (qLength coord s * a) (qLength coord s * b) F := by
    intro z hz
    exact hs (z.1, (s, z.2.2)) hsm hz
  have hl : 0 < qLength coord s := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hsm)
  have he (R : ℝ) (Y : Plane) : pressureSource a b hab (qLength coord) f (R, (s, Y)) =
      PressureStream.pressureSource (qLength coord s * a) (qLength coord s * b)
        (mul_lt_mul_of_pos_left hab hl) F (R, (s, Y)) := by
    exact (pressureSource_eq_fixed hab (qLength coord) f (R, (s, Y)) hl).trans
      (PhysicalMeanDomain.pressureSource_fiberLocal _ _ (mul_lt_mul_of_pos_left hab hl)
        f F s (fun _ _ => rfl) R Y)
  have hm : PressureStream.pressureMass (pressureSource a b hab (qLength coord) f) s =
      PressureStream.pressureMass (PressureStream.pressureSource
        (qLength coord s * a) (qLength coord s * b) (mul_lt_mul_of_pos_left hab hl) F) s := by
    apply integral_congr_ae
    filter_upwards [] with R
    exact PressureStream.torusAverage_congr_slice (R, s) (he R)
  rw [hm]
  exact PressureStream.pressureSource_mass_zero (mul_lt_mul_of_pos_left hab hl) hF hFs s

/-- Superflatness of the actual radial coefficient stored by moving
pressure reconstruction. The raw `gr` source may have nonzero pressure debt. -/
theorem pressureAliasState_radial_mem {a b h Mbase α : ℝ} (U : SlowRegion (2 * h))
    (ha : 0 < a) (hab : a < b) {cL cR : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (hh : 0 < h) (hM : Mbase ≠ 0) (index : ℕ → ℕ) (D : ℕ)
    (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
    (c : CorrectionState.Context (Point Plane)) (u : CorrectionState.State (Point Plane))
    (hf : ∀ n, ContDiffOn ℝ ∞ (u.gr c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength (2 * h)) U.carrier (u.gr c n))
    (hp : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.gr c n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α (u.gr c)) (β : ℝ) :
    MeanClass (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) β
      (fun n z => pressureAliasState
        (similarityGauge h (ChartScales.radialExponent h) a b Mbase hab index) c u n (z, 0) 0) := by
  have hsrc := meanClass_pressureSource U ha hcL hcR (ChartScales.epsilon h) L
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL hab hf hs hclass
  have hgain := meanClass_compactAlias_superflat U ha hab hcL hcR hh hM index D hgap L hL hS
    (fun n => pressureSource_q_contDiffOn U ha hab (hf n) (hs n))
    (fun n => pressureSource_supported hab
      (fun s hs => qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs)) (hs n))
    (fun n => pressureSource_periodicOn hab (qLength (2 * h)) (hp n))
    (fun n s hs' => pressureSource_zero_mass U hab (hf n) (hs n) hs') hsrc β
  have he := MeanIncrementBounds.Class.neg hgain
  simp only [pressureAliasState, similarityGauge, Matrix.cons_val_zero] at he ⊢
  exact he

end ActualPressureAlias

end NavierStokes.GaugeAliasDecay
