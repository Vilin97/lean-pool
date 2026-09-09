/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ConstructedSlowBase

/-!
# Exact exterior of the repaired modulated slow base

The pressure constant is obtained from the restored integral of the squared
regular swirl and the unchanged axis pressure.  Exterior equality of the
swirl alone would not determine this constant.

The scheme interface records the actual extended coefficient formulas.  It
allows any seed cutoff with the same order-zero profile and outer radius,
including the entrance-aligned scheme.
-/

@[expose] public section


namespace NavierStokes.ModulatedExterior

noncomputable section

open Set Filter MeasureTheory
open ProblemStatement SimilarityProfile SlowBorelBase BaseExterior
open GlobalSlowProfiles AssembledSlowBase
open scoped Topology ContDiff

section IntegralAnchors

/-- An actual primitive equality propagates through an unchanged tail. -/
theorem integral_equal_after {f g : ℝ → ℝ} {B X : ℝ}
    (hB : 0 ≤ B) (hX : B ≤ X)
    (hf : ContinuousOn f (Icc 0 X)) (hg : ContinuousOn g (Icc 0 X))
    (hanchor : (∫ r in (0 : ℝ)..B, f r) = ∫ r in (0 : ℝ)..B, g r)
    (htail : EqOn f g (Icc B X)) :
    (∫ r in (0 : ℝ)..X, f r) = ∫ r in (0 : ℝ)..X, g r := by
  have hf0 := (hf.mono (Icc_subset_Icc le_rfl hX)).intervalIntegrable_of_Icc (μ := volume) hB
  have hg0 := (hg.mono (Icc_subset_Icc le_rfl hX)).intervalIntegrable_of_Icc (μ := volume) hB
  have hf1 := (hf.mono (Icc_subset_Icc hB le_rfl)).intervalIntegrable_of_Icc (μ := volume) hX
  have hg1 := (hg.mono (Icc_subset_Icc hB le_rfl)).intervalIntegrable_of_Icc (μ := volume) hX
  have he : (∫ r in B..X, f r) = ∫ r in B..X, g r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hX] at hr
    exact htail hr
  rw [← intervalIntegral.integral_add_adjacent_intervals hf0 hf1,
    ← intervalIntegral.integral_add_adjacent_intervals hg0 hg1, hanchor, he]

/-- The fifth restored row fixes the squared-swirl integral once the actual
axis pressure is fixed.  This is an identity of integrals, not a pressure
boundary condition imposed on the output. -/
theorem squared_swirl_anchor_of_rows {D D' : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    (h0 : P.pressure0 = Q.pressure0) {p : ProfileHistories.Point}
    (hrows : ModulatedHistories.profileRows P p = ModulatedHistories.profileRows Q p) :
    ProfileHistories.primitive (fun w => P.f w ^ 2) p =
      ProfileHistories.primitive (fun w => Q.f w ^ 2) p := by
  have he := congrArg (fun row => row (4 : Fin 5)) hrows
  change P.pressure0 p.2 + ProfileHistories.primitive (fun w => P.f w ^ 2) p =
    Q.pressure0 p.2 + ProfileHistories.primitive (fun w => Q.f w ^ 2) p at he
  rw [h0] at he
  exact add_left_cancel he

theorem pressure_equal_after {D D' : ProfileHistories.RadialDomain}
    (P : ProfileHistories.Profiles D) (Q : ProfileHistories.Profiles D')
    {B X eta : ℝ} (hB : 0 ≤ B) (hX : B ≤ X)
    (hP : ∀ r ∈ Icc 0 X, (r, eta) ∈ D.carrier)
    (hQ : ∀ r ∈ Icc 0 X, (r, eta) ∈ D'.carrier)
    (h0 : P.pressure0 = Q.pressure0)
    (hanchor : ProfileHistories.primitive (fun w => P.f w ^ 2) (B, eta) =
      ProfileHistories.primitive (fun w => Q.f w ^ 2) (B, eta))
    (htail : ∀ r ∈ Icc B X, P.f (r, eta) = Q.f (r, eta)) :
    P.pressure (X, eta) = Q.pressure (X, eta) := by
  have he := integral_equal_after hB hX
    ((P.f_smooth.pow 2).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hP)
    ((Q.f_smooth.pow 2).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hQ)
    hanchor (fun r hr => congrArg (fun u : ℝ => u ^ 2) (htail r hr))
  change (∫ r in (0 : ℝ)..X, P.f (r, eta) ^ 2) =
    ∫ r in (0 : ℝ)..X, Q.f (r, eta) ^ 2 at he
  change P.pressure0 eta + (∫ r in (0 : ℝ)..X, P.f (r, eta) ^ 2) =
    Q.pressure0 eta + (∫ r in (0 : ℝ)..X, Q.f (r, eta) ^ 2)
  rw [h0, he]

end IntegralAnchors

section FiniteModification

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

/-- The additional finite row needed to retain the canonical pressure
constant.  The existing finite-modification certificate already retains mass. -/
def RestoredSquaredSwirl : Prop := ∀ eta ∈ S,
  ProfileHistories.primitive (fun w => Q.f w ^ 2) (nominalOuterX W, eta) =
    ProfileHistories.primitive (fun w => W.profiles.f w ^ 2) (nominalOuterX W, eta)

include M

theorem modified_fields_after {X eta : ℝ} (hX : nominalOuterX W ≤ X) (heta : eta ∈ S) :
    Q.f (X, eta) = W.profiles.f (X, eta) ∧ Q.U (X, eta) = W.profiles.U (X, eta) :=
  M.fields (X, eta) ((nominalOuterX_pos W).le.trans hX) heta
    (Or.inr ((modification_before_outer W Q M).le.trans hX))

/-- The restored mass at one radius is propagated by actual integration. -/
theorem modified_mass_after {X eta : ℝ} (hX : nominalOuterX W ≤ X) (heta : eta ∈ S) :
    Q.M (X, eta) = W.profiles.M (X, eta) := by
  apply integral_equal_after (nominalOuterX_pos W).le hX
    (Q.U_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => M.halfPlane r hr.1 eta heta))
    (W.profiles.U_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => modified_original_domain W Q M r hr.1 eta heta))
    (M.mass eta heta)
  exact fun r hr => (modified_fields_after W Q M hr.1 heta).2

theorem modified_pressure_after (henergy : RestoredSquaredSwirl W Q (S := S))
    {X eta : ℝ} (hX : nominalOuterX W ≤ X) (heta : eta ∈ S) :
    Q.pressure (X, eta) = W.profiles.pressure (X, eta) := by
  apply pressure_equal_after Q W.profiles (nominalOuterX_pos W).le hX
    (fun r hr => M.halfPlane r hr.1 eta heta)
    (fun r hr => modified_original_domain W Q M r hr.1 eta heta)
    M.pressure0 (henergy eta heta)
  exact fun r hr => (modified_fields_after W Q M hr.1 heta).1

/-- The reconstructed pressure is the actual canonical tail integral in
the exterior.  Its integration constant was fixed by the restored row. -/
theorem modified_pressure_canonical_after (henergy : RestoredSquaredSwirl W Q (S := S))
    {X eta : ℝ} (hX : nominalOuterX W ≤ X) (heta : eta ∈ Icc (-1 : ℝ) 1) :
    Q.pressure (X, eta) = -(∫ r in Ioi X, Q.f (r, eta) ^ 2) := by
  rw [modified_pressure_after W Q M henergy hX (M.contains heta)]
  change W.Pi (X, eta) = _
  rw [nominal_pressure_regular_integral W ((nominalOuterX_pos W).le.trans hX) heta]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  exact congrArg (fun u : ℝ => u ^ 2)
    (modified_fields_after W Q M (hX.trans hr.le) (M.contains heta)).1.symm

end FiniteModification

section SchemeRealization

/-- Literal scalar coefficient formulas.  No support or residual assertion
is part of this interface, and the inner cutoff is unrestricted. -/
structure RealizesScheme {S : Set ℝ} {h C : ℝ} (s : Scheme S h C)
    (hI : Icc (-1 : ℝ) 1 ⊆ S) (d : Coefficients) : Prop where
  phi : d.phi = fun n => extendedCoefficient s hI n 0
  axial : d.axial = fun n => extendedCoefficient s hI n 1
  pressure : d.pressure = fun n => extendedCoefficient s hI n 3

theorem realizes_coefficients {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
    {base : Fin 5 → InnerProfile} {s : Scheme S h C}
    {A : SlowRecursion.LocalHierarchy rho U h C base}
    (L : Localization s A inner) (B0 : BaseAgreement s A inner)
    (Z0 : ZeroOrderSolved s inner) (hI : Icc (-1 : ℝ) 1 ⊆ S) :
    RealizesScheme s hI (AssembledSlowBase.coefficients L B0 Z0 hI) :=
  ⟨rfl, rfl, rfl⟩

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)
    {s : Scheme S F.data.h W.axis.normalization} {d : Coefficients}
    (hd : RealizesScheme s M.contains d)
    (hbase : s.base = (modifiedScheme W Q M).base)
    (houter : s.B = nominalOuterRadius W)

include hd hbase in
theorem realized_zero_fields {p : Inner} (hX : 0 ≤ p.1) (heta : |p.2| ≤ 1) :
    d.phi 0 p = W.axis.normalization * Q.f p ∧ d.axial 0 p = Q.U p ∧
      d.pressure 0 p = Q.pressure p := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hd.phi]
    apply (extendedCoefficient_eq s M.contains 0 0 hX heta).trans
    change xProfile (profiles s 0).phi p = _
    rw [profiles_zero, hbase]
    exact baseFields_phi (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane hX
  · rw [hd.axial]
    apply (extendedCoefficient_eq s M.contains 0 1 hX heta).trans
    change xProfile (profiles s 0).axial p = _
    rw [profiles_zero, hbase]
    exact baseFields_axial (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane hX
  · rw [hd.pressure]
    apply (extendedCoefficient_eq s M.contains 0 3 hX heta).trans
    change xProfile (profiles s 0).pressure p = _
    rw [profiles_zero, hbase]
    exact baseFields_pressure (modifiedDomain W Q M) W.axis.normalization Q M.halfPlane hX

include hd houter in
theorem realized_positive_exterior {n : ℕ} (hn : 0 < n) {p : Inner}
    (hX : nominalOuterX W ≤ p.1) :
    d.phi n p = 0 ∧ d.axial n p = 0 ∧ d.pressure n p = 0 := by
  have hx : s.B ^ 2 / 2 ≤ p.1 := by rwa [houter, nominalOuterRadius_square]
  rw [hd.phi, hd.axial, hd.pressure]
  exact ⟨extendedCoefficient_zero_exterior s M.contains hn 0 hx,
    extendedCoefficient_zero_exterior s M.contains hn 1 hx,
    extendedCoefficient_zero_exterior s M.contains hn 3 hx⟩

include hd hbase houter

theorem realized_axial_zero_all (n : ℕ) {p : Inner}
    (hX : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) : d.axial n p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [(realized_zero_fields W Q M hd hbase ((nominalOuterX_pos W).le.trans hX) heta).2.1]
    exact ((modified_fields_after W Q M hX (M.contains (abs_le.mp heta))).2).trans
      (nominal_exterior_base W hX heta).1
  · exact (realized_positive_exterior W Q M hd houter hn hX).2.1

theorem realized_primitive_zero_all (n : ℕ) {p : Inner}
    (hX : nominalOuterX W ≤ p.1) (heta : |p.2| ≤ 1) :
    ProfileHistories.primitive (d.axial n) p = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hp0 : 0 ≤ p.1 := (nominalOuterX_pos W).le.trans hX
    have he : EqOn (fun r => d.axial 0 (r, p.2)) (fun r => Q.U (r, p.2)) (uIcc 0 p.1) := by
      intro r hr
      rw [uIcc_of_le hp0] at hr
      exact (realized_zero_fields W Q M hd hbase (p := (r, p.2)) hr.1 heta).2.1
    change (∫ r in (0 : ℝ)..p.1, d.axial 0 (r, p.2)) = 0
    rw [intervalIntegral.integral_congr he]
    exact (modified_mass_after W Q M hX (M.contains (abs_le.mp heta))).trans
      (nominal_exterior_base W hX heta).2
  · rw [hd.axial]
    apply extended_axial_primitive_zero s M.contains hn _ heta
    rwa [houter, nominalOuterRadius_square]

/-- All coefficient support and stream-mass identities are derived from
the actual repaired scheme.  The inner cutoff is absent from the premises. -/
theorem realized_exterior_coefficients : ExteriorCoefficients d (nominalExteriorRadius W) := by
  constructor
  · intro n p hp heta
    exact realized_axial_zero_all W Q M hd hbase houter n
      ((nominalExteriorRadius_ge_outer W).trans hp.le) (abs_le.mpr heta)
  · intro n p hp heta
    exact realized_primitive_zero_all W Q M hd hbase houter n
      ((nominalExteriorRadius_ge_outer W).trans hp.le) (abs_le.mpr heta)
  · intro n hn p hp _
    exact (realized_positive_exterior W Q M hd houter hn
      ((nominalExteriorRadius_ge_outer W).trans hp.le)).1
  · intro n hn p hp _
    exact (realized_positive_exterior W Q M hd houter hn
      ((nominalExteriorRadius_ge_outer W).trans hp.le)).2.2

omit houter in
theorem realized_angular_pure_heat {p : PhysicalPoint}
    (hp : p ∈ exteriorDomain F.data.h (nominalExteriorRadius W)) :
    leadingAngular F.data.h W.axis.normalization d p =
      heatCoefficient (nominalHeatNormalization W) F.data.h p := by
  have hx : nominalOuterX W ≤ X F.data.h p := (nominalExteriorRadius_ge_outer W).trans hp.2.le
  have hx0 : 0 ≤ X F.data.h p := (nominalOuterX_pos W).le.trans hx
  have he := physical_eta_mem F.data.h_pos F.data.h_lt_half hp.1
  have hc := (realized_zero_fields W Q M hd hbase (p := inner F.data.h p) hx0 (abs_le.mpr he)).1
  have hn := (nominalCoefficients_zero_fields W (p := inner F.data.h p) hx0 (abs_le.mpr he)).1
  have hf := (modified_fields_after W Q M hx (M.contains he)).1
  change Q.f (inner F.data.h p) = W.f (inner F.data.h p) at hf
  have hsame : leadingAngular F.data.h W.axis.normalization d p =
      leadingAngular F.data.h W.axis.normalization (nominalCoefficients W) p := by
    unfold leadingAngular pullback
    rw [hc, hn, hf]
  exact hsame.trans (nominal_angular_pure_heat W hp)

omit houter in
theorem realized_pressure_pure_heat (henergy : RestoredSquaredSwirl W Q (S := S))
    {p : PhysicalPoint} (hp : p ∈ exteriorDomain F.data.h (nominalExteriorRadius W)) :
    leadingPressure F.data.h d p = heatPressure (nominalHeatNormalization W) F.data.h p := by
  have hx : nominalOuterX W ≤ X F.data.h p := (nominalExteriorRadius_ge_outer W).trans hp.2.le
  have hx0 : 0 ≤ X F.data.h p := (nominalOuterX_pos W).le.trans hx
  have he := physical_eta_mem F.data.h_pos F.data.h_lt_half hp.1
  have hc := (realized_zero_fields W Q M hd hbase (p := inner F.data.h p) hx0 (abs_le.mpr he)).2.2
  have hn := (nominalCoefficients_zero_fields W (p := inner F.data.h p) hx0 (abs_le.mpr he)).2.2
  have hpq := modified_pressure_after W Q M henergy hx (M.contains he)
  change Q.pressure (inner F.data.h p) = W.Pi (inner F.data.h p) at hpq
  have hsame : leadingPressure F.data.h d p = leadingPressure F.data.h (nominalCoefficients W) p :=
      by
    unfold leadingPressure pullback
    rw [hc, hn, hpq]
  exact hsame.trans (nominal_pressure_pure_heat W hp)

theorem realized_base_eq_heat (hds : SmoothCoefficients d)
    (henergy : RestoredSquaredSwirl W Q (S := S)) {a : ℕ → ℕ} (ha : StrictMono a) :
    EqOn (baseVelocity a F.data.h W.axis.normalization d)
      (heatVelocity (nominalHeatNormalization W) F.data.h)
      (cartesianExterior F.data.h (nominalExteriorRadius W)) ∧
    EqOn (basePressure a F.data.h W.axis.normalization d)
      (heatPressureField (nominalHeatNormalization W) F.data.h)
      (cartesianExterior F.data.h (nominalExteriorRadius W)) :=
  exterior_base_eq_heat ha F.data.h_pos F.data.h_lt_half (nominalExteriorRadius_pos W).le hds
    (realized_exterior_coefficients W Q M hd hbase houter)
    (fun _ hp => realized_angular_pure_heat W Q M hd hbase hp)
    (fun _ hp => realized_pressure_pure_heat W Q M hd hbase henergy hp)

theorem realized_base_residual_zero (hds : SmoothCoefficients d)
    (henergy : RestoredSquaredSwirl W Q (S := S)) {a : ℕ → ℕ} (ha : StrictMono a)
    {z : SpaceTime} (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) :
    navierStokesResidual (baseVelocity a F.data.h W.axis.normalization d)
      (basePressure a F.data.h W.axis.normalization d) z.1 z.2 = 0 :=
  exterior_base_residual_zero ha F.data.h_pos F.data.h_lt_half (nominalExteriorRadius_pos W).le hds
    (realized_exterior_coefficients W Q M hd hbase houter)
    (fun _ hp => realized_angular_pure_heat W Q M hd hbase hp)
    (fun _ hp => realized_pressure_pure_heat W Q M hd hbase henergy hp) hz

theorem realized_residual_germ_zero (hds : SmoothCoefficients d)
    (henergy : RestoredSquaredSwirl W Q (S := S)) {a : ℕ → ℕ} (ha : StrictMono a)
    {z : SpaceTime} (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) :
    (fun y => navierStokesResidual (baseVelocity a F.data.h W.axis.normalization d)
      (basePressure a F.data.h W.axis.normalization d) y.1 y.2) =ᶠ[𝓝 z] (fun _ => 0) := by
  filter_upwards [(cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half
    (nominalExteriorRadius W)).mem_nhds hz] with y hy
  exact realized_base_residual_zero W Q M hd hbase houter hds henergy ha hy

theorem realized_residual_jets_zero (hds : SmoothCoefficients d)
    (henergy : RestoredSquaredSwirl W Q (S := S)) {a : ℕ → ℕ} (ha : StrictMono a)
    {z : SpaceTime} (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => navierStokesResidual
      (baseVelocity a F.data.h W.axis.normalization d)
      (basePressure a F.data.h W.axis.normalization d) y.1 y.2) z = 0 := by
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (realized_residual_germ_zero W Q M hd hbase houter hds henergy ha hz) m).self_of_nhds,
    iteratedFDeriv_fun_zero, Pi.zero_apply]

end SchemeRealization

section ActualModulation

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)

/-- This finite anchor is derived from the actual solved modulation. -/
theorem actual_squared_swirl_restored : RestoredSquaredSwirl W v.profiles (S := v.slowParameters)
    := by
  intro eta heta
  apply squared_swirl_anchor_of_rows v.profiles W.profiles v.pressure0
  apply v.restored eta heta.1
  exact (ModulatedProfileAssembly.repairPatch_before_positive W).le.trans
    ((ReservedPatches.left_lt_right F W.controls.radius W.controls.radius_pos .positive).le.trans
      (nominalOuterX_gt_patch W).le)

theorem actual_realizes :
    RealizesScheme (modifiedScheme W v.profiles v.finiteModification) v.finiteModification.contains
      (ConstructedSlowBase.Modulated.coefficients v) := ⟨rfl, rfl, rfl⟩

theorem actual_exterior_coefficients :
    ExteriorCoefficients (ConstructedSlowBase.Modulated.coefficients v) (nominalExteriorRadius W) :=
  realized_exterior_coefficients W v.profiles v.finiteModification (actual_realizes v) rfl rfl

/-- Exact heat exterior for this actual modulated sequence and any strictly
increasing cutoff schedule.  The pressure anchor is discharged internally. -/
theorem actual_base_eq_heat {a : ℕ → ℕ} (ha : StrictMono a) :
    EqOn (baseVelocity a F.data.h W.axis.normalization (ConstructedSlowBase.Modulated.coefficients
        v))
      (heatVelocity (nominalHeatNormalization W) F.data.h)
      (cartesianExterior F.data.h (nominalExteriorRadius W)) ∧
    EqOn (basePressure a F.data.h W.axis.normalization (ConstructedSlowBase.Modulated.coefficients
        v))
      (heatPressureField (nominalHeatNormalization W) F.data.h)
      (cartesianExterior F.data.h (nominalExteriorRadius W)) :=
  realized_base_eq_heat W v.profiles v.finiteModification (actual_realizes v) rfl rfl
    (ConstructedSlowBase.Modulated.coefficients_smooth v) (actual_squared_swirl_restored v) ha

theorem actual_fields_eq_heat (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    EqOn (ConstructedSlowBase.Modulated.velocity v c hc upper B)
      (heatVelocity (nominalHeatNormalization W) F.data.h)
      (cartesianExterior F.data.h (nominalExteriorRadius W)) ∧
    EqOn (ConstructedSlowBase.Modulated.pressure v c hc upper B)
      (heatPressureField (nominalHeatNormalization W) F.data.h)
      (cartesianExterior F.data.h (nominalExteriorRadius W)) :=
  actual_base_eq_heat v (ConstructedSlowBase.Modulated.scales_strictMono v c hc upper B)

theorem actual_residual_zero (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {z : SpaceTime} (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) :
    navierStokesResidual (ConstructedSlowBase.Modulated.velocity v c hc upper B)
      (ConstructedSlowBase.Modulated.pressure v c hc upper B) z.1 z.2 = 0 :=
  realized_base_residual_zero W v.profiles v.finiteModification (actual_realizes v) rfl rfl
    (ConstructedSlowBase.Modulated.coefficients_smooth v) (actual_squared_swirl_restored v)
    (ConstructedSlowBase.Modulated.scales_strictMono v c hc upper B) hz

theorem actual_residual_jets_zero (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {z : SpaceTime} (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => navierStokesResidual
      (ConstructedSlowBase.Modulated.velocity v c hc upper B)
      (ConstructedSlowBase.Modulated.pressure v c hc upper B) y.1 y.2) z = 0 :=
  realized_residual_jets_zero W v.profiles v.finiteModification (actual_realizes v) rfl rfl
    (ConstructedSlowBase.Modulated.coefficients_smooth v) (actual_squared_swirl_restored v)
    (ConstructedSlowBase.Modulated.scales_strictMono v c hc upper B) hz m

end ActualModulation

section JointTerminalExtension

/-- A strict upper test for the actual positive root of the coordinate
equation.  It uses monotonicity only on the positive branch. -/
theorem coordinateQ_lt_of_forward_lt {a b : ℝ} {p : ℝ × ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hp : 0 < p.1)
    (hf : p.1 < SimilarityCoordinates.forwardScalar a p.2 b) :
    SimilarityCoordinates.coordinateQ a p < b := by
  obtain ⟨hq, heq⟩ := SimilarityCoordinates.coordinateQ_spec ha ha1 hp
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | he
  · have hi := SimilarityCoordinates.forwardScalar_lt ha ha1 hb hlt (hp.trans hf)
    rw [heq] at hi
    exact (not_lt_of_gt hf) hi
  · rw [← he] at heq
    exact (ne_of_lt hf) heq.symm

/-- At every positive radius on the central plane, a full spacetime
neighborhood on the past side lies in the pure exterior.  Spatial position
and time are allowed to approach together. -/
theorem exists_terminal_exterior_neighborhood {h R : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R) {x : Space}
    (hx : x 2 = 0) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      (∀ z ∈ U, 0 < AxisymmetricFields.radialEnergy z.2) ∧
      (∀ z ∈ U, z.1 < 1 → z ∈ cartesianExterior h R) := by
  let b : ℝ := AxisymmetricFields.radialEnergy x / (2 * (R + 1))
  have hb : 0 < b := div_pos hs (by positivity)
  let U : Set SpaceTime := {z | AxisymmetricFields.radialEnergy x / 2 <
      AxisymmetricFields.radialEnergy z.2 ∧
    1 - z.1 < SimilarityCoordinates.forwardScalar (2 * h) (z.2 2) b}
  have hfcont : Continuous (fun z : SpaceTime =>
      SimilarityCoordinates.forwardScalar (2 * h) (z.2 2) b) := by
    exact continuous_const.sub
      ((((AxisymmetricFields.projection 2).continuous.comp continuous_snd).pow 2).mul
          continuous_const)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const
      ((AxisymmetricFields.contDiff_radialEnergy (n := ∞)).continuous.comp continuous_snd)).inter
      (isOpen_lt (continuous_const.sub continuous_fst) hfcont)
  have hxU : (1, x) ∈ U := by
    constructor
    · linarith
    · simpa [SimilarityCoordinates.forwardScalar, hx] using hb
  refine ⟨U, hU, hxU, ?_, ?_⟩
  · intro z hz
    exact (half_pos hs).trans hz.1
  · intro z hz ht
    have hq : 0 < q h (AxisymmetricFields.profilePoint z.1 z.2) := q_pos hh hh1 ht
    have hqb : q h (AxisymmetricFields.profilePoint z.1 z.2) < b :=
      coordinateQ_lt_of_forward_lt (by linarith) (by linarith) hb (sub_pos.mpr ht) hz.2
    have hbeq : b * (2 * (R + 1)) = AxisymmetricFields.radialEnergy x :=
      div_mul_cancel₀ _ (by positivity)
    refine ⟨ht, ?_⟩
    change R < AxisymmetricFields.radialEnergy z.2 / q h (AxisymmetricFields.profilePoint z.1 z.2)
    apply (lt_div_iff₀ hq).mpr
    calc
      R * q h (AxisymmetricFields.profilePoint z.1 z.2) ≤ R * b :=
        mul_le_mul_of_nonneg_left hqb.le hR
      _ < AxisymmetricFields.radialEnergy x / 2 := by nlinarith
      _ < AxisymmetricFields.radialEnergy z.2 := hz.1

/-- The incoming field is retained at every past time; the actual heat
value is supplied at the terminal time. -/
noncomputable def completedVelocity (C h : ℝ) (u : VelocityField) : VelocityField :=
  fun z => if z.1 < 1 then u z else heatVelocity C h z

/-- Completed pressure, defined pointwise by `if z.1 < 1 then p z else heatPressureField C h z`. -/
noncomputable def completedPressure (C h : ℝ) (p : PressureField) : PressureField :=
  fun z => if z.1 < 1 then p z else heatPressureField C h z

theorem completedVelocity_before (C h : ℝ) (u : VelocityField) {z : SpaceTime}
    (ht : z.1 < 1) : completedVelocity C h u z = u z := ite_eq_left ht

theorem completedPressure_before (C h : ℝ) (p : PressureField) {z : SpaceTime}
    (ht : z.1 < 1) : completedPressure C h p z = p z := ite_eq_left ht

/-- Joint one-sided smooth extension of any fields with the proved heat
exterior.  The hypotheses are instantiated below from the coefficient and
integral construction, rather than imposed on the modulated output. -/
theorem completed_fields_smooth_near_terminal {h R C : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R)
    {u : VelocityField} {p : PressureField}
    (hu : EqOn u (heatVelocity C h) (cartesianExterior h R))
    (hp : EqOn p (heatPressureField C h) (cartesianExterior h R))
    {x : Space} (hx : x 2 = 0) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      EqOn (completedVelocity C h u) (heatVelocity C h) U ∧
      EqOn (completedPressure C h p) (heatPressureField C h) U ∧
      ContDiffOn ℝ ∞ (completedVelocity C h u) (U ∩ (Iic 1 ×ˢ (univ : Set Space))) ∧
      ContDiffOn ℝ ∞ (completedPressure C h p) (U ∩ (Iic 1 ×ˢ (univ : Set Space))) := by
  obtain ⟨U, hU, hUx, hrad, hExt⟩ := exists_terminal_exterior_neighborhood hh hh1 hR hx hs
  have heU : EqOn (completedVelocity C h u) (heatVelocity C h) U := by
    intro z hz
    by_cases ht : z.1 < 1
    · rw [completedVelocity_before C h u ht]
      exact hu (hExt z hz ht)
    · exact ite_eq_right ht
  have heP : EqOn (completedPressure C h p) (heatPressureField C h) U := by
    intro z hz
    by_cases ht : z.1 < 1
    · rw [completedPressure_before C h p ht]
      exact hp (hExt z hz ht)
    · exact ite_eq_right ht
  have hsub : U ∩ (Iic 1 ×ˢ (univ : Set Space)) ⊆ closedCartesianHeatDomain :=
    fun z hz => ⟨hz.2.1, hrad z hz.1⟩
  exact ⟨U, hU, hUx, heU, heP,
    ((heatVelocity_contDiffOn_closed C hh).mono hsub).congr (fun _ hz => heU hz.1),
    ((heatPressureField_contDiffOn_closed C hh).mono hsub).congr (fun _ hz => heP hz.1)⟩

theorem realized_terminal_extension {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)
    {s : Scheme S F.data.h W.axis.normalization} {d : Coefficients}
    (hd : RealizesScheme s M.contains d)
    (hbase : s.base = (modifiedScheme W Q M).base) (houter : s.B = nominalOuterRadius W)
    (hds : SmoothCoefficients d) (henergy : RestoredSquaredSwirl W Q (S := S))
    {a : ℕ → ℕ} (ha : StrictMono a) {x : Space}
    (hx : x 2 = 0) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      EqOn (completedVelocity (nominalHeatNormalization W) F.data.h
        (baseVelocity a F.data.h W.axis.normalization d))
        (heatVelocity (nominalHeatNormalization W) F.data.h) U ∧
      EqOn (completedPressure (nominalHeatNormalization W) F.data.h
        (basePressure a F.data.h W.axis.normalization d))
        (heatPressureField (nominalHeatNormalization W) F.data.h) U ∧
      ContDiffOn ℝ ∞ (completedVelocity (nominalHeatNormalization W) F.data.h
        (baseVelocity a F.data.h W.axis.normalization d)) (U ∩ (Iic 1 ×ˢ (univ : Set Space))) ∧
      ContDiffOn ℝ ∞ (completedPressure (nominalHeatNormalization W) F.data.h
        (basePressure a F.data.h W.axis.normalization d)) (U ∩ (Iic 1 ×ˢ (univ : Set Space))) := by
  have he := realized_base_eq_heat W Q M hd hbase houter hds henergy ha
  exact completed_fields_smooth_near_terminal F.data.h_pos F.data.h_lt_half
    (nominalExteriorRadius_pos W).le he.1 he.2 hx hs

theorem actual_terminal_extension {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)
    (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) {x : Space}
    (hx : x 2 = 0) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    ∃ U : Set SpaceTime, IsOpen U ∧ (1, x) ∈ U ∧
      EqOn (completedVelocity (nominalHeatNormalization W) F.data.h
        (ConstructedSlowBase.Modulated.velocity v c hc upper B))
        (heatVelocity (nominalHeatNormalization W) F.data.h) U ∧
      EqOn (completedPressure (nominalHeatNormalization W) F.data.h
        (ConstructedSlowBase.Modulated.pressure v c hc upper B))
        (heatPressureField (nominalHeatNormalization W) F.data.h) U ∧
      ContDiffOn ℝ ∞ (completedVelocity (nominalHeatNormalization W) F.data.h
        (ConstructedSlowBase.Modulated.velocity v c hc upper B)) (U ∩ (Iic 1 ×ˢ (univ : Set
            Space))) ∧
      ContDiffOn ℝ ∞ (completedPressure (nominalHeatNormalization W) F.data.h
        (ConstructedSlowBase.Modulated.pressure v c hc upper B)) (U ∩ (Iic 1 ×ˢ (univ : Set
            Space))) := by
  have he := actual_fields_eq_heat v c hc upper B
  exact completed_fields_smooth_near_terminal F.data.h_pos F.data.h_lt_half
    (nominalExteriorRadius_pos W).le he.1 he.2 hx hs

end JointTerminalExtension

end

end NavierStokes.ModulatedExterior
