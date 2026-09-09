/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatSwitchCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedCone
public import LeanPool.NavierStokesAndEuler.NavierStokes.MatchingConeBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PreparedOutgoing
import LeanPool.NavierStokesAndEuler.NavierStokes.RepairConeBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalHistoryBridge

/-!
# Cone coordinates of one actual nominal profile

The physical coordinates below are computed from the genuine smooth profile
and its axis-integrated histories. The outgoing convention for axial shear
has the opposite sign to the signed shear used by the modulation theorem.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open NavierStokes.ProfileHistories
open NavierStokes.OutgoingProfile
open NavierStokes.NominalProfile (AxisStage Controls SmallDebt)
open NavierStokes.StressActivation

namespace NavierStokes.NominalConeAssembly

/-- Is true, constructed using `ActivationContinuation.IsRelaxed`. -/
noncomputable def IsTrue {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) : Prop :=
  ActivationContinuation.IsRelaxed P h p ∧
    2 < ActivationContinuation.shearSize
      (ActivationContinuation.shearA P p) (ActivationContinuation.shearB P p)

theorem isTrue_iff_loop {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) :
    IsTrue P h p ↔ TrueConeLoop.InTrueCone (ReferenceBounds.p1 P h p)
      (ReferenceBounds.p2 P h p) (ActivationContinuation.shearA P p)
      (ActivationContinuation.shearB P p) := by
  constructor
  · rintro ⟨hc, hv⟩
    exact ⟨hc.first_positive, hv, hc.projection_positive, hc.cone⟩
  · rintro ⟨ha, hv, hp, hc⟩
    exact ⟨⟨ha, hp, hc⟩, hv⟩

theorem p1_eq_stock {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) :
    ReferenceBounds.p1 P h p = ActivationStocks.profileStockOne P h p := rfl

theorem p2_eq_stock {D : RadialDomain} (P : Profiles D) (h : ℝ) (p : Point) :
    ReferenceBounds.p2 P h p = ActivationStocks.profileStockTwo P h p := by
  unfold ReferenceBounds.p2 ReferenceBounds.ns ActivationStocks.profileStockTwo
  ring

/-! ## Local smooth coordinates for the modulation annulus -/

/-- Tilt, given by `ActivationContinuation.shearB P p / ActivationContinuation.shearA P p`. -/
noncomputable def tilt {D : RadialDomain} (P : Profiles D) (p : Point) : ℝ :=
  ActivationContinuation.shearB P p / ActivationContinuation.shearA P p

theorem physicalE_smoothAt {D : RadialDomain} (P : Profiles D) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) : ContDiffAt ℝ ∞ P.E p :=
  ((contDiffAt_const.mul contDiffAt_fst).sqrt (by positivity)).mul
    (P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp))

theorem shears_smoothAt {D : RadialDomain} (P : Profiles D) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    ContDiffAt ℝ ∞ (ActivationContinuation.shearA P) p ∧
      ContDiffAt ℝ ∞ (ActivationContinuation.shearB P) p := by
  have hpf := P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp)
  have hdf := (radialPartial_smooth D P.f_smooth).contDiffAt (D.isOpen.mem_nhds hp)
  have hdu := (radialPartial_smooth D P.U_smooth).contDiffAt (D.isOpen.mem_nhds hp)
  exact ⟨((contDiffAt_const.mul contDiffAt_fst).mul hdf).div hpf hf,
    ((contDiffAt_const.mul contDiffAt_fst).mul hdu).div
      (physicalE_smoothAt P hp hX) (P.E_ne_zero hX hf)⟩

theorem stocks_smoothAt {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0)
    (hL : NaturalAxisData.L h p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (ReferenceBounds.p1 P h) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p2 P h) p := by
  have hLc : ContDiffAt ℝ ∞ (fun q : Point => NaturalAxisData.L h q.2) p :=
    contDiffAt_const.sub ((contDiffAt_const.mul contDiffAt_const).mul (contDiffAt_snd.pow 2))
  exact ⟨(contDiffAt_fst.mul (P.angularLag_smoothAt h hp hX.ne' (P.H_ne_zero hX.ne' hf))).div hLc
      hL,
    (contDiffAt_fst.mul ((P.axialLag_smoothAt h hp hX.ne').div hLc hL)).div
      (physicalE_smoothAt P hp hX) (P.E_ne_zero hX hf)⟩

theorem cone_coordinates_smoothAt {D : RadialDomain} (P : Profiles D) (h : ℝ) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0)
    (ha : ActivationContinuation.shearA P p ≠ 0) (hL : NaturalAxisData.L h p.2 ≠ 0) :
    ContDiffAt ℝ ∞ (ActivationContinuation.shearA P) p ∧
      ContDiffAt ℝ ∞ (tilt P) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p1 P h) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p2 P h) p := by
  have hs := shears_smoothAt P hp hX hf
  exact ⟨hs.1, hs.2.div hs.1 ha, stocks_smoothAt P h hp hX hf hL⟩

/-- Equality of an actual prefix propagates to every history, before any
derivative or stock comparison is made. -/
theorem history_of_prefix {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    {J : Set ℝ} {R : ℝ} (h0 : P.pressure0 = Q.pressure0)
    (hf : ∀ p : Point, p.2 ∈ J → p.1 ≤ R → P.f p = Q.f p)
    (hu : ∀ p : Point, p.2 ∈ J → p.1 ≤ R → P.U p = Q.U p)
    (r : HistoryRow) {X eta : ℝ} (hX : 0 ≤ X) (hR : X ≤ R) (heta : eta ∈ J) :
    profileHistory P r (X, eta) = profileHistory Q r (X, eta) := by
  apply ActivationStocks.profileHistory_congr_across P Q r hX
  · cases r <;> simp only [profileInitial, h0]
  · intro x hx
    exact hf (x, eta) heta (hx.2.trans hR)
  · intro x hx
    exact hu (x, eta) heta (hx.2.trans hR)

/-- The endpoint is included: equality on the left determines the radial
derivative because both fields are genuinely differentiable there. -/
theorem radialPartial_of_left {D D' : RadialDomain} {F G : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (hG : ContDiffOn ℝ ∞ G D'.carrier)
    {R : ℝ} {p : Point} (hp : p ∈ D.carrier) (hq : p ∈ D'.carrier)
    (hR : p.1 ≤ R) (he : ∀ x ≤ R, F (x, p.2) = G (x, p.2)) :
    radialPartial F p = radialPartial G p := by
  exact (uniqueDiffOn_Iic R p.1 hR).eq_deriv _
    (radialPartial_hasDerivAt D hF hp).hasDerivWithinAt
    ((radialPartial_hasDerivAt D' hG hq).hasDerivWithinAt.congr_of_mem he hR)

theorem coordinates_of_prefix {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    (h : ℝ) {J : Set ℝ} (hJ : IsOpen J) {R : ℝ}
    (h0 : P.pressure0 = Q.pressure0)
    (hf : ∀ p : Point, p.2 ∈ J → p.1 ≤ R → P.f p = Q.f p)
    (hu : ∀ p : Point, p.2 ∈ J → p.1 ≤ R → P.U p = Q.U p)
    {p : Point} (hp : p ∈ D.carrier) (hq : p ∈ D'.carrier)
    (hX : 0 < p.1) (hR : p.1 ≤ R) (heta : p.2 ∈ J) (hfne : Q.f p ≠ 0) :
    ActivationContinuation.shearA P p = ActivationContinuation.shearA Q p ∧
      ActivationContinuation.shearB P p = ActivationContinuation.shearB Q p ∧
      ReferenceBounds.p1 P h p = ReferenceBounds.p1 Q h p ∧
      ReferenceBounds.p2 P h p = ReferenceBounds.p2 Q h p := by
  have hfv := hf p heta hR
  have huv := hu p heta hR
  have hfd := radialPartial_of_left P.f_smooth Q.f_smooth hp hq hR
    (fun x hx => hf (x, p.2) heta hx)
  have hud := radialPartial_of_left P.U_smooth Q.U_smooth hp hq hR
    (fun x hx => hu (x, p.2) heta hx)
  have hE : P.E p = Q.E p := by simp only [Profiles.E, hfv]
  have hs := ActivationStocks.profiles_stocks_congr P Q h hJ heta hp hq hX hfv hfne huv
    (fun r eta he => history_of_prefix P Q h0 hf hu r hX.le hR he)
  refine ⟨?_, ?_, hs.1, ?_⟩
  · simp only [ActivationContinuation.shearA, hfd, hfv]
  · simp only [ActivationContinuation.shearB, hud, hE]
  · simpa only [p2_eq_stock] using hs.2

theorem relaxed_of_coordinates {D D' : RadialDomain} (P : Profiles D) (Q : Profiles D')
    {h : ℝ} {p : Point}
    (he : ActivationContinuation.shearA P p = ActivationContinuation.shearA Q p ∧
      ActivationContinuation.shearB P p = ActivationContinuation.shearB Q p ∧
      ReferenceBounds.p1 P h p = ReferenceBounds.p1 Q h p ∧
      ReferenceBounds.p2 P h p = ReferenceBounds.p2 Q h p)
    (hc : ActivationContinuation.IsRelaxed Q h p) : ActivationContinuation.IsRelaxed P h p := by
  unfold ActivationContinuation.IsRelaxed at *
  rwa [he.1, he.2.1, he.2.2.1, he.2.2.2]

theorem controls_seed_coordinates {F : Profile} {A : AxisStage F} (c : Controls A)
    (hsep : c.separation ≤ Real.exp (-8)) {p : Point}
    (hsmall : SmallDebt F c.debt p.2) (hX : 0 < p.1) (hXi : p.1 ≤ NominalProfile.Xi)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.shearA (c.profiles hsep) p = ActivationContinuation.shearA
        c.seedProfiles p ∧
      ActivationContinuation.shearB (c.profiles hsep) p = ActivationContinuation.shearB
          c.seedProfiles p ∧
      ReferenceBounds.p1 (c.profiles hsep) F.data.h p = ReferenceBounds.p1 c.seedProfiles F.data.h
          p ∧
      ReferenceBounds.p2 (c.profiles hsep) F.data.h p = ReferenceBounds.p2 c.seedProfiles F.data.h
          p := by
  apply coordinates_of_prefix (c.profiles hsep) c.seedProfiles F.data.h isOpen_univ rfl
    (fun q _ hq => c.f_before_Xi hq) (fun q _ hq => (c.physical_before_Xi hsep hq).1)
    (c.admissible_nonnegative hX.le (NominalProfile.physical_band_in_parameterInterval heta) hsmall)
    _ hX hXi (mem_univ _)
  · exact (c.seedF_positive (NominalProfile.physical_band_in_parameterInterval heta) hX.le).ne'
  · exact ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg A.scale_pos.le hX.le),
      NominalProfile.physical_band_in_parameterInterval heta⟩

theorem continuation_first_at_Xi {F : Profile} {A : AxisStage F} {N : ℕ} {eps T : ℝ}
    (w : ActivationContinuation.ContinuationWitness A.natural A.scale_pos A.small
      F.axisDatum_contDiff N eps) (hT : 0 < T)
    (hsep : (Controls.ofContinuation A w T hT).separation ≤ Real.exp (-8)) {eta : ℝ}
    (hsmall : SmallDebt F (Controls.ofContinuation A w T hT).debt eta)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    2 < ReferenceBounds.p1 ((Controls.ofContinuation A w T hT).profiles hsep)
      F.data.h (NominalProfile.Xi, eta) := by
  rw [(controls_seed_coordinates (Controls.ofContinuation A w T hT) hsep (p := (NominalProfile.Xi,
      eta)) hsmall
    NominalProfile.Xi_pos le_rfl heta).2.2.1]
  exact w.final_first 110 ⟨w.parameters.hold_lt_final.le, le_rfl⟩ eta heta

/-- History index as an element of `Fin 5`. -/
noncomputable def historyIndex (r : HistoryRow) : Fin 5 := by
  classical
  exact if r = .mass then 0 else if r = .angular then 1 else
    if r = .transport then 2 else if r = .energy then 3 else 4

@[simp] theorem historyIndex_mass : historyIndex .mass = 0 := by simp [historyIndex]
@[simp] theorem historyIndex_angular : historyIndex .angular = 1 := by simp [historyIndex]
@[simp] theorem historyIndex_transport : historyIndex .transport = 2 := by simp [historyIndex]
@[simp] theorem historyIndex_energy : historyIndex .energy = 3 := by simp [historyIndex]
@[simp] theorem historyIndex_pressure : historyIndex .pressure = 4 := by simp [historyIndex]

theorem profileDensity_eq_regular {D : RadialDomain} (P : Profiles D) (r : HistoryRow) (p : Point) :
    profileDensity P r p = NominalProfile.regularDensity P p (historyIndex r) := by
  cases r <;> simp only [historyIndex_mass, historyIndex_angular, historyIndex_transport,
    historyIndex_energy, historyIndex_pressure] <;> rfl

theorem history_eq_moment {D : RadialDomain} (P : Profiles D) (r : HistoryRow)
    {X eta : ℝ} (hX : 0 ≤ X) :
    profileHistory P r (X, eta) = profileInitial P r eta +
      NominalProfile.moments P.U P.E X eta (historyIndex r) := by
  rw [profileHistory_eq_initial_add_primitive]
  congr 1
  rw [primitive, intervalIntegral.integral_of_le hX]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  change profileDensity P r (x, eta) =
    NominalProfile.density (fun t => P.U (t, eta)) (fun t => P.E (t, eta)) x (historyIndex r)
  rw [profileDensity_eq_regular]
  exact congrArg (fun q : NominalProfile.Debt => q (historyIndex r))
    (NominalProfile.regularDensity_eq P hx.1 eta).symm

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem f_positive {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    0 < W.profiles.f p := by
  have he := W.E_positive hX heta
  rw [W.E_eq_sqrt_f hX] at he
  exact pos_of_mul_pos_right he (Real.sqrt_nonneg _)

theorem prefix_f {p : Point} (hp : p.1 ≤ W.controls.heatJoin) :
    W.profiles.f p = (W.controls.profiles W.separated).f p := by
  change W.controls.extendedf W.heat.coefficients p = W.controls.f p
  by_cases hXi : p.1 ≤ NominalProfile.Xi
  · simp only [Controls.extendedf, ite_eq_left hXi]
  · rw [Controls.extendedf, ite_eq_right hXi,
      W.controls.extendedE_before W.heat.coefficients hp, Controls.f, ite_eq_right hXi]

theorem prefix_histories (r : HistoryRow) {X eta : ℝ} (hX : 0 ≤ X)
    (hR : X ≤ W.controls.heatJoin) :
    profileHistory W.profiles r (X, eta) =
      profileHistory (W.controls.profiles W.separated) r (X, eta) :=
  history_of_prefix W.profiles (W.controls.profiles W.separated) (J := univ) rfl
    (fun _ _ hq => prefix_f W hq) (fun _ _ _ => rfl) r hX hR (mem_univ _)

theorem prefix_coordinates {p : Point} (hp : p ∈ W.domain.carrier)
    (hX : 0 < p.1) (hR : p.1 ≤ W.controls.heatJoin)
    (hf : W.controls.f p ≠ 0) :
    ActivationContinuation.shearA W.profiles p =
        ActivationContinuation.shearA (W.controls.profiles W.separated) p ∧
      ActivationContinuation.shearB W.profiles p =
        ActivationContinuation.shearB (W.controls.profiles W.separated) p ∧
      ReferenceBounds.p1 W.profiles F.data.h p =
        ReferenceBounds.p1 (W.controls.profiles W.separated) F.data.h p ∧
      ReferenceBounds.p2 W.profiles F.data.h p =
        ReferenceBounds.p2 (W.controls.profiles W.separated) F.data.h p :=
  coordinates_of_prefix W.profiles (W.controls.profiles W.separated) F.data.h isOpen_univ rfl
    (fun _ _ hq => prefix_f W hq) (fun _ _ _ => rfl) hp hp.1 hX hR (mem_univ _) hf

theorem prefix_relaxed {p : Point} (hX : 0 < p.1) (hR : p.1 ≤ W.controls.heatJoin)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : ActivationContinuation.IsRelaxed (W.controls.profiles W.separated) F.data.h p) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h p := by
  have hf : W.controls.f p ≠ 0 := by
    change (W.controls.profiles W.separated).f p ≠ 0
    rw [← prefix_f W hR]
    exact (f_positive W hX heta).ne'
  exact relaxed_of_coordinates W.profiles (W.controls.profiles W.separated)
    (prefix_coordinates W (W.domain_contains hX.le heta) hX hR hf) hc

theorem seed_coordinates {p : Point} (hX : 0 < p.1) (hXi : p.1 ≤ NominalProfile.Xi)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.shearA W.profiles p = ActivationContinuation.shearA
        W.controls.seedProfiles p ∧
      ActivationContinuation.shearB W.profiles p = ActivationContinuation.shearB
          W.controls.seedProfiles p ∧
      ReferenceBounds.p1 W.profiles F.data.h p = ReferenceBounds.p1 W.controls.seedProfiles
          F.data.h p ∧
      ReferenceBounds.p2 W.profiles F.data.h p = ReferenceBounds.p2 W.controls.seedProfiles
          F.data.h p := by
  apply coordinates_of_prefix W.profiles W.controls.seedProfiles F.data.h isOpen_univ rfl
    (fun q _ hq => (W.controls.extended_seed_fields W.heat.coefficients W.separated hq).1)
    (fun q _ hq => (W.controls.extended_seed_fields W.heat.coefficients W.separated hq).2)
    (W.domain_contains hX.le heta) _ hX hXi (mem_univ _)
  · exact (W.controls.seedF_positive (NominalProfile.physical_band_in_parameterInterval heta)
      hX.le).ne'
  · exact ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg W.axis.scale_pos.le hX.le),
      NominalProfile.physical_band_in_parameterInterval heta⟩

theorem seed_relaxed {p : Point} (hX : 0 < p.1) (hXi : p.1 ≤ NominalProfile.Xi)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : ActivationContinuation.IsRelaxed W.controls.seedProfiles F.data.h p) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h p :=
  relaxed_of_coordinates W.profiles W.controls.seedProfiles (seed_coordinates W hX hXi heta) hc

theorem seed_true {p : Point} (hX : 0 < p.1) (hXi : p.1 ≤ NominalProfile.Xi)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : IsTrue W.controls.seedProfiles F.data.h p) : IsTrue W.profiles F.data.h p := by
  refine ⟨seed_relaxed W hX hXi heta hc.1, ?_⟩
  rw [(seed_coordinates W hX hXi heta).1, (seed_coordinates W hX hXi heta).2.1]
  exact hc.2

theorem continuation_relaxed {N : ℕ} {eps T : ℝ}
    (w : ActivationContinuation.ContinuationWitness W.axis.natural W.axis.scale_pos W.axis.small
      F.axisDatum_contDiff N eps) (hT : 0 < T)
    (hc : W.controls = Controls.ofContinuation W.axis w T hT)
    {p : Point} (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hX : p.1 ∈ Icc w.parameters.startRadius (110 : ℝ)) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h p := by
  apply seed_relaxed W (w.parameters.startRadius_pos.trans_le hX.1) hX.2 heta
  have he : W.controls.seedProfiles = w.parameters.profiles := by rw [hc]; rfl
  rw [he]
  exact w.relaxed p heta hX

theorem moments_eq_profile_moments (X eta : ℝ) :
    NominalProfile.moments W.profiles.U W.profiles.E X eta =
      NominalProfile.moments W.U W.E X eta := by
  ext i
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have he : W.profiles.E (x, eta) = W.E (x, eta) := (W.E_eq_sqrt_f hx.1).symm
  simp only [NominalProfile.density, he]
  rfl

theorem history_after (r : HistoryRow) {X eta : ℝ}
    (hX : W.controls.heatJoin ≤ X) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    profileHistory W.profiles r (X, eta) = profileInitial W.profiles r eta +
      NominalProfile.moments (HeatedOutgoing.U F W.controls.radius)
        (HeatedOutgoing.E F W.controls.radius W.heat.physical.coefficients) X eta (historyIndex r)
            := by
  rw [history_eq_moment W.profiles r (W.controls.heatJoin_pos.le.trans hX),
    moments_eq_profile_moments W, W.moments_after hX heta]

end Witness

/-! ## Literal physical moments in the logarithmic chart -/

/-- Chart, given by `(XR * Real.exp p.1, p.2)`. -/
noncomputable def chart (XR : ℝ) (p : Point) : Point := (XR * Real.exp p.1, p.2)

theorem chart_positive {XR : ℝ} (hXR : 0 < XR) (p : Point) : 0 < (chart XR p).1 :=
  mul_pos hXR (Real.exp_pos _)

theorem integral_log_chart (f : ℝ → ℝ) {XR : ℝ} (hXR : 0 < XR) (y : ℝ) :
    (∫ x in Ioc 0 (XR * Real.exp y), f x) =
      XR * ∫ t in Iic y, Real.exp t * f (XR * Real.exp t) := by
  calc
    _ = ∫ x in Ioc 0 (XR * Real.exp y), (fun v => f (XR * v)) (x / XR) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      dsimp only
      rw [mul_div_cancel₀ x hXR.ne']
    _ = XR * ∫ v in Ioc 0 (Real.exp y), f (XR * v) := by
      simpa only [mul_div_cancel_left₀ _ hXR.ne'] using
        OutgoingDilation.integral_dilate_Ioc (fun v => f (XR * v)) XR (XR * Real.exp y) hXR
    _ = _ := by
      rw [← ReleaseMoments.image_exp_Iic,
        integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
          (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
      simp only [abs_of_pos (Real.exp_pos _), smul_eq_mul]

theorem sqrt_chart {XR : ℝ} (hXR : 0 < XR) (y : ℝ) :
    Real.sqrt (2 * (XR * Real.exp y)) = Real.sqrt (2 * XR) * Real.exp (y / 2) := by
  rw [← mul_assoc, Real.sqrt_mul (by positivity : 0 ≤ 2 * XR)]
  congr 1
  exact (Real.exp_half y).symm

theorem outgoing_U_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR) (p : Point) :
    OutgoingDilation.U F XR (chart XR p) = F.logU p := by
  simp only [chart, OutgoingDilation.U, OutgoingProfile.Profile.U,
    mul_div_cancel_left₀ _ hXR.ne', Real.log_exp, Prod.eta]

theorem outgoing_E_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR) (p : Point) :
    OutgoingDilation.E F XR (chart XR p) = F.logE p := by
  simp only [chart, OutgoingDilation.E, OutgoingProfile.Profile.E,
    mul_div_cancel_left₀ _ hXR.ne', Real.log_exp, Prod.eta]

theorem outgoing_M_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR) (y eta : ℝ) :
    OutgoingDilation.M F XR eta (XR * Real.exp y) =
      XR * OutgoingHistories.M F.data F.amp (y, eta) := by
  unfold OutgoingDilation.M
  rw [integral_log_chart _ hXR, OutgoingHistories.M_eq_integral F.data F.amp_contDiff]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp t * OutgoingDilation.U F XR (chart XR (t, eta)) = _
  rw [outgoing_U_chart F hXR]
  rfl

theorem outgoing_J_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR) (y eta : ℝ) :
    OutgoingDilation.J F XR eta (XR * Real.exp y) =
      (XR * Real.sqrt (2 * XR)) * OutgoingHistories.J F.reset F.amp (y, eta) := by
  unfold OutgoingDilation.J
  rw [integral_log_chart _ hXR, OutgoingHistories.J_eq_integral F.reset F.amp_contDiff]
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp t * (OutgoingDilation.H F XR (chart XR (t, eta)) *
    OutgoingDilation.U F XR (chart XR (t, eta))) = _
  rw [outgoing_U_chart F hXR]
  unfold OutgoingDilation.H
  rw [outgoing_E_chart F hXR]
  change Real.exp t * ((Real.sqrt (2 * (XR * Real.exp t)) * F.logE (t, eta)) * F.logU (t, eta)) = _
  dsimp only
  rw [sqrt_chart hXR, show 3 * t / 2 = t + t / 2 by ring, Real.exp_add]
  dsimp only [OutgoingProfile.Profile.logE, OutgoingProfile.Profile.logU,
    OutgoingHistories.E, OutgoingHistories.U]
  ring

theorem heated_I_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (coef : ℝ → HeatedOutgoing.Coeff) {eta : ℝ} (heta : eta ∈ HeatedOutgoing.parameterDomain)
    (y : ℝ) :
    NominalProfile.moments (HeatedOutgoing.U F XR) (HeatedOutgoing.E F XR coef)
      (XR * Real.exp y) eta 1 =
      (XR * Real.sqrt (2 * XR)) * HeatSwitchCone.logI F XR coef (y, eta) := by
  change (∫ x in Ioc 0 (XR * Real.exp y), Real.sqrt (2 * x) * HeatedOutgoing.E F XR coef (x, eta))
      = _
  rw [integral_log_chart _ hXR, (HeatSwitchCone.logI_eq_past_integral F hXR coef heta y).2,
    mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp t * (Real.sqrt (2 * (XR * Real.exp t)) * HeatedOutgoing.E F XR coef (XR *
      Real.exp t, eta)) = _
  dsimp only
  rw [sqrt_chart hXR, show 3 * t / 2 = t + t / 2 by ring, Real.exp_add]
  unfold HeatSwitchCone.logE
  ring

theorem heated_S_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (coef : ℝ → HeatedOutgoing.Coeff) {eta : ℝ} (heta : eta ∈ HeatedOutgoing.parameterDomain)
    (y : ℝ) :
    NominalProfile.moments (HeatedOutgoing.U F XR) (HeatedOutgoing.E F XR coef)
      (XR * Real.exp y) eta 3 = XR * HeatSwitchCone.logS F XR coef (y, eta) := by
  change (∫ x in Ioc 0 (XR * Real.exp y), HeatedOutgoing.U F XR (x, eta) ^ 2 -
    HeatedOutgoing.E F XR coef (x, eta) ^ 2 / 2) = _
  rw [integral_log_chart _ hXR, (HeatSwitchCone.logS_eq_past_integral F hXR coef heta y).2]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  change Real.exp t * (OutgoingDilation.U F XR (chart XR (t, eta)) ^ 2 -
    HeatSwitchCone.logE F XR coef (t, eta) ^ 2 / 2) = _
  rw [outgoing_U_chart F hXR]

theorem heated_J_chart (F : Profile) {XR : ℝ} (hXR : 0 < XR)
    (coef : ℝ → HeatedOutgoing.Coeff) (y eta : ℝ) :
    NominalProfile.moments (HeatedOutgoing.U F XR) (HeatedOutgoing.E F XR coef)
      (XR * Real.exp y) eta 2 =
      (XR * Real.sqrt (2 * XR)) * OutgoingHistories.J F.reset F.amp (y, eta) := by
  have he : NominalProfile.moments (HeatedOutgoing.U F XR) (HeatedOutgoing.E F XR coef)
      (XR * Real.exp y) eta 2 = HeatedOutgoing.J F XR coef eta (XR * Real.exp y) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    change HeatedOutgoing.U F XR (x, eta) * Real.sqrt (2 * x) * HeatedOutgoing.E F XR coef (x, eta)
        = _
    unfold HeatedOutgoing.H
    ring
  rw [he, HeatedOutgoing.J_unchanged F XR coef eta _ hXR, outgoing_J_chart F hXR]

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem log_histories {p : Point} (hp : W.controls.heatJoin ≤ (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.M (chart W.controls.radius p) = W.controls.radius * OutgoingHistories.M F.data F.amp
        p ∧
    W.profiles.I (chart W.controls.radius p) = (W.controls.radius * Real.sqrt (2 *
        W.controls.radius)) *
      HeatSwitchCone.logI F W.controls.radius W.heat.coefficients p ∧
    W.profiles.J (chart W.controls.radius p) = (W.controls.radius * Real.sqrt (2 *
        W.controls.radius)) *
      OutgoingHistories.J F.reset F.amp p ∧
    W.profiles.S (chart W.controls.radius p) = W.controls.radius *
      HeatSwitchCone.logS F W.controls.radius W.heat.coefficients p := by
  have hm := history_after W .mass hp heta
  have hi := history_after W .angular hp heta
  have hj := history_after W .transport hp heta
  have hs := history_after W .energy hp heta
  simp only [profileHistory, profileInitial, historyIndex_mass, historyIndex_angular,
    historyIndex_transport, historyIndex_energy, zero_add] at hm hi hj hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hm.trans (outgoing_M_chart F W.controls.radius_pos p.1 p.2)
  · exact hi.trans (heated_I_chart F W.controls.radius_pos W.heat.coefficients heta p.1)
  · exact hj.trans (heated_J_chart F W.controls.radius_pos W.heat.coefficients p.1 p.2)
  · exact hs.trans (heated_S_chart F W.controls.radius_pos W.heat.coefficients heta p.1)

theorem log_pressure {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.pressure (chart W.controls.radius p) =
      HeatSwitchCone.logPi F W.controls.radius W.heat.coefficients p := by
  exact (W.heat_agreement hp heta).2.2.trans
    (HeatSwitchCone.logPi_eq_canonical F W.heat.physical p heta).symm

end Witness

theorem parameterPartial_eq_scaled_within {D : RadialDomain} {f g : Field}
    (hf : ContDiffOn ℝ ∞ f D.carrier) {X y eta k : ℝ} (hp : (X, eta) ∈ D.carrier)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) (hk : k ≠ 0)
    (he : ∀ xi ∈ HeatedOutgoing.parameterDomain, f (X, xi) = k * g (y, xi)) :
    parameterPartial f (X, eta) = k *
      derivWithin (fun xi => g (y, xi)) HeatedOutgoing.parameterDomain eta := by
  have hd := (parameterPartial_hasDerivAt D hf hp).div_const k
  have hg : HasDerivWithinAt (fun xi => g (y, xi)) (parameterPartial f (X, eta) / k)
      HeatedOutgoing.parameterDomain eta := by
    apply hd.hasDerivWithinAt.congr_of_mem _ heta
    intro xi hxi
    apply (eq_div_iff hk).mpr
    calc
      g (y, xi) * k = k * g (y, xi) := mul_comm _ _
      _ = f (X, xi) := (he xi hxi).symm
  rw [hg.derivWithin (uniqueDiffOn_Icc (by norm_num) eta heta)]
  field_simp

theorem smooth_parameterWithin_eq_dEta {g : Field} (hg : ContDiff ℝ ∞ g)
    {p : Point} (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    derivWithin (fun xi => g (p.1, xi)) HeatedOutgoing.parameterDomain p.2 =
      OutgoingHistories.dEta g p :=
  (OutgoingHistories.dEta_hasDerivAt hg p).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc (by norm_num) p.2 heta)

theorem angular_scaled_quotient {R r : ℝ} (hR : R ≠ 0) (hr : r ≠ 0)
    (a b c k I Ieta J Jeta x z e : ℝ) :
    (a * (R * r * I) - b * (R * r * Ieta) - c * (R * r * Jeta) + k * (R * r * J)) /
        (R * x * (r * z * e)) =
      (a * I - b * Ieta - c * Jeta + k * J) / (x * z * e) := by
  rw [show a * (R * r * I) - b * (R * r * Ieta) - c * (R * r * Jeta) + k * (R * r * J) =
    (R * r) * (a * I - b * Ieta - c * Jeta + k * J) by ring,
    show R * x * (r * z * e) = (R * r) * (x * z * e) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hR hr)]

theorem scaled_difference_quotient {R : ℝ} (hR : R ≠ 0) (a eta u v x : ℝ) :
    a * (R * u - eta * (R * v)) / (R * x) = a * (u - eta * v) / x := by
  rw [show a * (R * u - eta * (R * v)) = R * (a * (u - eta * v)) by ring,
    mul_div_mul_left _ _ hR]

theorem scaled_affine_quotient {R : ℝ} (hR : R ≠ 0) (a b u v x : ℝ) :
    (a * (R * u) - b * (R * v)) / (R * x) = (a * u - b * v) / x := by
  rw [show a * (R * u) - b * (R * v) = R * (a * u - b * v) by ring,
    mul_div_mul_left _ _ hR]

theorem shear_dilation_cancel {r z f : ℝ} (hr : r ≠ 0) (hz : z ≠ 0) (hf : f ≠ 0)
    (X df : ℝ) :
    -2 * X * df / f = 1 - 2 * (r * (z * (1 / 2)) * f + r * z * (df * X)) / (r * z * f) := by
  rw [show (2 : ℝ) * (r * (z * (1 / 2)) * f + r * z * (df * X)) =
    (r * z) * (f + 2 * df * X) by ring,
    mul_div_mul_left _ _ (mul_ne_zero hr hz)]
  field_simp [hf]; ring

/-- The logarithmic radial chart changes actual derivatives, not independent
formal jets. This statement is also valid for the matching profile before
the heat splice. -/
theorem physical_log_shears {D : RadialDomain} (P : Profiles D) {R : ℝ}
    (hR : 0 < R) (p : Point) (hp : chart R p ∈ D.carrier)
    (hf : P.f (chart R p) ≠ 0) :
    ActivationContinuation.shearA P (chart R p) =
        1 - 2 * deriv (fun y => P.E (R * Real.exp y, p.2)) p.1 / P.E (chart R p) ∧
      ActivationContinuation.shearB P (chart R p) =
        -2 * deriv (fun y => P.U (R * Real.exp y, p.2)) p.1 / P.E (chart R p) := by
  have hc := (Real.hasDerivAt_exp p.1).const_mul R
  have hfd := (radialPartial_hasDerivAt D P.f_smooth hp).comp p.1 hc
  have hud := (radialPartial_hasDerivAt D P.U_smooth hp).comp p.1 hc
  have hr := (((hasDerivAt_id p.1).div_const 2).exp).const_mul (Real.sqrt (2 * R))
  dsimp only [chart, Function.comp_def, id_eq] at hfd hud hr
  have he : (fun y => P.E (R * Real.exp y, p.2)) =
      (fun y => (Real.sqrt (2 * R) * Real.exp (y / 2)) * P.f (R * Real.exp y, p.2)) := by
    funext y
    exact congrArg (fun t => t * P.f (R * Real.exp y, p.2)) (sqrt_chart hR y)
  constructor
  · rw [he, (hr.fun_mul hfd).deriv]
    change -2 * (R * Real.exp p.1) * radialPartial P.f (chart R p) / P.f (chart R p) = _
    rw [show P.E (chart R p) = (Real.sqrt (2 * R) * Real.exp (p.1 / 2)) * P.f (chart R p) from
      congrArg (fun t => t * P.f (chart R p)) (sqrt_chart hR p.1)]
    exact shear_dilation_cancel (Real.sqrt_pos.2 (by positivity)).ne'
      (Real.exp_ne_zero _) hf _ _
  · rw [hud.deriv]
    unfold ActivationContinuation.shearB
    dsimp only [chart]
    ring

theorem physical_shear_cancel {r f X : ℝ} (hr : r ≠ 0) (hf : f ≠ 0)
    (hsq : r ^ 2 = 2 * X) (df : ℝ) :
    1 - 2 * X * (1 / (2 * r) * (2 * 1) * f + r * df) / (r * f) = -2 * X * df / f := by
  have hx : X = r ^ 2 / 2 := by linarith
  rw [hx]
  field_simp; ring

theorem modulated_shears_eq {D : RadialDomain} (P : Profiles D) {p : Point}
    (hp : p ∈ D.carrier) (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    ModulatedCone.angularShear P.E p = ActivationContinuation.shearA P p ∧
      ModulatedCone.signedAxialShear P.E P.U p = ActivationContinuation.shearB P p := by
  have hr : Real.sqrt (2 * p.1) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hr2 := Real.sq_sqrt (show 0 ≤ 2 * p.1 by positivity)
  have hd := ((Real.hasDerivAt_sqrt (show 2 * p.1 ≠ 0 by positivity)).comp p.1
    ((hasDerivAt_id p.1).const_mul 2)).fun_mul (radialPartial_hasDerivAt D P.f_smooth hp)
  dsimp only [Function.comp_def, id_eq] at hd
  constructor
  · unfold ModulatedCone.angularShear ActivationContinuation.shearA
    change 1 - 2 * p.1 * deriv (fun x => Real.sqrt (2 * x) * P.f (x, p.2)) p.1 /
      (Real.sqrt (2 * p.1) * P.f p) = _
    rw [hd.deriv]
    exact physical_shear_cancel hr hf hr2 _
  · unfold ModulatedCone.signedAxialShear ActivationContinuation.shearB
    rw [(radialPartial_hasDerivAt D P.U_smooth hp).deriv]
    ring

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem log_history_parameters {p : Point}
    (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    parameterPartial W.profiles.M (chart W.controls.radius p) = W.controls.radius *
        OutgoingHistories.dEta (OutgoingHistories.M F.data F.amp) p ∧
    parameterPartial W.profiles.I (chart W.controls.radius p) =
      (W.controls.radius * Real.sqrt (2 * W.controls.radius)) *
        derivWithin (fun eta => HeatSwitchCone.logI F W.controls.radius W.heat.coefficients (p.1,
            eta))
          HeatedOutgoing.parameterDomain p.2 ∧
    parameterPartial W.profiles.J (chart W.controls.radius p) =
      (W.controls.radius * Real.sqrt (2 * W.controls.radius)) *
        OutgoingHistories.dEta (OutgoingHistories.J F.reset F.amp) p ∧
    parameterPartial W.profiles.S (chart W.controls.radius p) = W.controls.radius *
        derivWithin (fun eta => HeatSwitchCone.logS F W.controls.radius W.heat.coefficients (p.1,
            eta))
          HeatedOutgoing.parameterDomain p.2 ∧
    parameterPartial W.profiles.pressure (chart W.controls.radius p) =
        derivWithin (fun eta => HeatSwitchCone.logPi F W.controls.radius W.heat.coefficients (p.1,
            eta))
          HeatedOutgoing.parameterDomain p.2 := by
  have hmem := W.domain_contains (chart_positive W.controls.radius_pos p).le heta
  have hroot : W.controls.radius * Real.sqrt (2 * W.controls.radius) ≠ 0 :=
    mul_ne_zero W.controls.radius_pos.ne'
      (Real.sqrt_pos.2 (mul_pos (by norm_num) W.controls.radius_pos)).ne'
  have hm := parameterPartial_eq_scaled_within W.profiles.M_smooth hmem heta
      W.controls.radius_pos.ne'
    (fun eta he => (log_histories W (p := (p.1, eta)) hp.le he).1)
  have hi := parameterPartial_eq_scaled_within W.profiles.I_smooth hmem heta hroot
    (fun eta he => (log_histories W (p := (p.1, eta)) hp.le he).2.1)
  have hj := parameterPartial_eq_scaled_within W.profiles.J_smooth hmem heta hroot
    (fun eta he => (log_histories W (p := (p.1, eta)) hp.le he).2.2.1)
  have hs := parameterPartial_eq_scaled_within W.profiles.S_smooth hmem heta
      W.controls.radius_pos.ne'
    (fun eta he => (log_histories W (p := (p.1, eta)) hp.le he).2.2.2)
  have hP := parameterPartial_eq_scaled_within W.profiles.pressure_smooth hmem heta
    (show (1 : ℝ) ≠ 0 by norm_num) (fun eta he => by
      simp only [one_mul]
      exact log_pressure W (p := (p.1, eta)) hp he)
  rw [smooth_parameterWithin_eq_dEta (OutgoingHistories.M_smooth F.data F.amp_contDiff) heta] at hm
  rw [smooth_parameterWithin_eq_dEta (OutgoingHistories.J_smooth F.reset F.amp_contDiff) heta] at hj
  simp only [one_mul] at hP
  exact ⟨hm, hi, hj, hs, hP⟩

theorem log_fields {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.U (chart W.controls.radius p) = F.logU p ∧
    W.profiles.E (chart W.controls.radius p) = HeatSwitchCone.logE F W.controls.radius
        W.heat.coefficients p ∧
    W.profiles.H (chart W.controls.radius p) = Real.sqrt (2 * W.controls.radius) * Real.exp (p.1 /
        2) *
      HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p := by
  have hx := chart_positive W.controls.radius_pos p
  have he : W.profiles.E (chart W.controls.radius p) =
      HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p :=
    (W.E_eq_sqrt_f hx).symm.trans (W.heat_agreement hp heta).2.1
  refine ⟨(W.U_outgoing hp).trans (outgoing_U_chart F W.controls.radius_pos p), he, ?_⟩
  have hH : W.profiles.H (chart W.controls.radius p) =
      Real.sqrt (2 * (chart W.controls.radius p).1) * W.profiles.E (chart W.controls.radius p) := by
    dsimp only [Profiles.H, Profiles.E]
    rw [← mul_assoc, Real.mul_self_sqrt (mul_nonneg (by norm_num) hx.le)]
  rw [hH, he]
  exact congrArg (fun z => z * HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p)
    (sqrt_chart W.controls.radius_pos p.1)

theorem log_transport {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.W F.data.h (chart W.controls.radius p) = OutgoingHistories.W F.data F.amp p := by
  have hmem := W.domain_contains (chart_positive W.controls.radius_pos p).le heta
  have hv := (log_histories W hp.le heta).1
  have hd := (log_history_parameters W hp heta).1
  have hf := ActivationStocks.profile_massFlux W.profiles F.data.h hmem
  rw [hv, hd] at hf
  unfold OutgoingHistories.W OutgoingHistories.X
  apply (eq_div_iff (Real.exp_ne_zero p.1)).mpr
  apply mul_left_cancel₀ W.controls.radius_pos.ne'
  convert! hf using 1 <;>
    dsimp only [chart, ActivationStocks.massFlux, OutgoingHistories.XW, OutgoingHistories.X,
      NaturalAxisData.D, NaturalAxisData.d, StressAlgebra.axialExponent,
          StressAlgebra.coordinateFactor] <;> ring

theorem log_lags {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    W.profiles.angularLag F.data.h (chart W.controls.radius p) =
        HeatSwitchCone.Qs F W.controls.radius W.heat.coefficients p ∧
    W.profiles.axialLag F.data.h (chart W.controls.radius p) =
        HeatSwitchCone.Ns F W.controls.radius W.heat.coefficients p := by
  have hx := chart_positive W.controls.radius_pos p
  have hmem := W.domain_contains hx.le heta
  have hf := f_positive W hx heta
  have hv := log_histories W hp.le heta
  have hd := log_history_parameters W hp heta
  have he := log_fields W hp heta
  have hroot : Real.sqrt (2 * W.controls.radius) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) W.controls.radius_pos)).ne'
  have hE : HeatSwitchCone.logE F W.controls.radius W.heat.coefficients p ≠ 0 := by
    rw [← he.2.1]
    exact W.profiles.E_ne_zero hx hf.ne'
  constructor
  · rw [W.profiles.angularLag_integrated F.data.h hmem hx.ne' (W.profiles.H_ne_zero hx.ne' hf.ne'),
      log_transport W hp heta, hv.2.1, hv.2.2.1, hd.2.1, hd.2.2.1, he.2.2]
    unfold HeatSwitchCone.Qs
    simp only [chart]
    rw [show 3 * p.1 / 2 = p.1 + p.1 / 2 by ring, Real.exp_add]
    congr 1
    exact angular_scaled_quotient W.controls.radius_pos.ne' hroot _ _ _ _ _ _ _ _ _ _ _
  · rw [W.profiles.axialLag_integrated F.data.h hmem hx, log_transport W hp heta,
      he.1, hv.1, hv.2.2.2, hd.1, hd.2.2.2.1, hd.2.2.2.2, log_pressure W hp heta]
    unfold HeatSwitchCone.Ns
    simp only [chart]
    rw [scaled_difference_quotient W.controls.radius_pos.ne',
      scaled_affine_quotient W.controls.radius_pos.ne']

theorem log_stocks {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ReferenceBounds.p1 W.profiles F.data.h (chart W.controls.radius p) =
        HeatSwitchCone.stressScale F W.controls.radius W.heat.coefficients p ∧
    ReferenceBounds.p2 W.profiles F.data.h (chart W.controls.radius p) =
        W.controls.radius * Real.exp p.1 * HeatSwitchCone.Ns F W.controls.radius
            W.heat.coefficients p /
          (NaturalAxisData.L F.data.h p.2 * HeatSwitchCone.logE F W.controls.radius
              W.heat.coefficients p) := by
  have hh := log_lags W hp heta
  constructor
  · rw [ReferenceBounds.p1, hh.1]
    rfl
  · rw [ReferenceBounds.p2, ReferenceBounds.ns, hh.2, (log_fields W hp heta).2.1]
    simp only [chart]
    ring

/-- Both radial shears are derivatives of the actual fields. The signed
axial convention is explicitly the negative of the outgoing convention. -/
theorem log_shears {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.shearA W.profiles (chart W.controls.radius p) =
        HeatSwitchCone.radialA F W.controls.radius W.heat.coefficients p ∧
    ActivationContinuation.shearB W.profiles (chart W.controls.radius p) =
        -HeatSwitchCone.radialB F W.controls.radius W.heat.coefficients p := by
  have hx := chart_positive W.controls.radius_pos p
  have hmem := W.domain_contains hx.le heta
  have hf := f_positive W hx heta
  have hr : Real.sqrt (2 * W.controls.radius) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) W.controls.radius_pos)).ne'
  have hnear : ∀ᶠ y in 𝓝 p.1, W.controls.heatJoin < W.controls.radius * Real.exp y :=
    (continuous_const.mul Real.continuous_exp).continuousAt.eventually (Ioi_mem_nhds hp)
  have hchart := (Real.hasDerivAt_exp p.1).const_mul W.controls.radius
  have hfp := (radialPartial_hasDerivAt W.domain W.profiles.f_smooth hmem).comp p.1 hchart
  have hup := (radialPartial_hasDerivAt W.domain W.profiles.U_smooth hmem).comp p.1 hchart
  have hroot := (((hasDerivAt_id p.1).div_const 2).exp).const_mul (Real.sqrt (2 *
      W.controls.radius))
  have heq : (fun y => HeatSwitchCone.logE F W.controls.radius W.heat.coefficients (y, p.2)) =ᶠ[𝓝
      p.1]
      (fun y => (Real.sqrt (2 * W.controls.radius) * Real.exp (y / 2)) *
        W.profiles.f (W.controls.radius * Real.exp y, p.2)) := by
    filter_upwards [hnear] with y hy
    rw [← (log_fields W (p := (y, p.2)) hy heta).2.1]
    change Real.sqrt (2 * (W.controls.radius * Real.exp y)) *
      W.profiles.f (W.controls.radius * Real.exp y, p.2) = _
    rw [sqrt_chart W.controls.radius_pos]
  have hEder := (hroot.mul hfp).congr_of_eventuallyEq heq
  have hueq : (fun y => F.logU (y, p.2)) =ᶠ[𝓝 p.1]
      (fun y => W.profiles.U (W.controls.radius * Real.exp y, p.2)) := by
    filter_upwards [hnear] with y hy
    exact (log_fields W (p := (y, p.2)) hy heta).1.symm
  have hUder := hup.congr_of_eventuallyEq hueq
  constructor
  · rw [HeatSwitchCone.radialA, hEder.deriv, heq.eq_of_nhds]
    unfold ActivationContinuation.shearA
    simp only [chart, id_eq, Function.comp_apply]
    exact shear_dilation_cancel hr (Real.exp_ne_zero _) hf.ne' _ _
  · rw [HeatSwitchCone.radialB, OutgoingHistories.dY_eq_deriv F.logU_contDiff, hUder.deriv]
    unfold ActivationContinuation.shearB
    rw [(log_fields W hp heta).2.1]
    simp only [chart]
    ring

end Witness

theorem stock_ratio_identity (x q n L e : ℝ) (hq : q ≠ 0) :
    x * n / (L * e) = (x * q / L) * (n / (e * q)) := by
  by_cases hL : L = 0
  · simp [hL]
  by_cases he : e = 0
  · simp [he]
  field_simp

theorem relaxed_scaled_coordinates {a b s r : ℝ} (ha : 0 < a)
    (hp : 2 < s * (1 - b * r / a))
    (hc : a * (1 + (b / a) ^ 2) <
      ConeAlgebra.coneBound (s * (1 - b * r / a)) (s * (r + b / a))) :
    ActivationContinuation.Relaxed a (-b) s (s * r) := by
  have hP : ActivationContinuation.projection s (s * r) a (-b) = s * (1 - b * r / a) := by
    unfold ActivationContinuation.projection
    ring
  have hJ : ActivationContinuation.transverse s (s * r) a (-b) = s * (r + b / a) := by
    unfold ActivationContinuation.transverse
    ring
  have hV : ActivationContinuation.shearSize a (-b) = a * (1 + (b / a) ^ 2) := by
    simp only [ActivationContinuation.shearSize, neg_div, neg_sq]
  exact ⟨ha, hP ▸ hp, by rwa [hV, hP, hJ]⟩

/-- Heat relaxed at, constructed using `0`. -/
noncomputable def HeatRelaxedAt (F : Profile) (XR : ℝ) (coef : ℝ → HeatedOutgoing.Coeff)
    (p : Point) : Prop :=
  0 < HeatSwitchCone.Qs F XR coef p ∧ 0 < HeatSwitchCone.radialA F XR coef p ∧
    2 < HeatSwitchCone.normalP F XR coef p ∧
    HeatSwitchCone.normalV F XR coef p <
      ConeAlgebra.coneBound (HeatSwitchCone.normalP F XR coef p) (HeatSwitchCone.normalJ F XR coef
          p)

/-- The pressure cancellation and all preceding histories are retained
before the first compensation patch, for every parameter. -/
theorem heated_histories_before_patch (F : Profile) {R : ℝ} (hR : 0 < R)
    (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 ≤ OutgoingDilation.patchClock F) :
    HeatSwitchCone.logI F R coef p = OutgoingHistories.I F.reset p ∧
      HeatSwitchCone.logS F R coef p = OutgoingHistories.S F.reset F.amp p ∧
      HeatSwitchCone.logPi F R coef p = OutgoingHistories.Pi F.reset p := by
  have hdiff (t : ℝ) (ht : t ∈ uIcc (OutgoingDilation.patchClock F) p.1) :
      HeatSwitchCone.logE F R coef (t, p.2) = F.logE (t, p.2) :=
    HeatSwitchCone.logE_before_patch F hR coef (ht.2.trans (max_le le_rfl hp))
  have hi : (∫ t in OutgoingDilation.patchClock F..p.1,
      Real.exp (3 * t / 2) * (HeatSwitchCone.logE F R coef (t, p.2) - F.logE (t, p.2))) = 0 := by
    calc
      _ = ∫ _t in OutgoingDilation.patchClock F..p.1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hdiff t ht, sub_self, mul_zero]
      _ = 0 := by simp
  have hs : (∫ t in OutgoingDilation.patchClock F..p.1,
      Real.exp t * (HeatSwitchCone.logE F R coef (t, p.2) ^ 2 - F.logE (t, p.2) ^ 2)) = 0 := by
    calc
      _ = ∫ _t in OutgoingDilation.patchClock F..p.1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hdiff t ht, sub_self, mul_zero]
      _ = 0 := by simp
  have hpi : (∫ t in OutgoingDilation.patchClock F..p.1,
      HeatSwitchCone.logE F R coef (t, p.2) ^ 2 - F.logE (t, p.2) ^ 2) = 0 := by
    calc
      _ = ∫ _t in OutgoingDilation.patchClock F..p.1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hdiff t ht, sub_self]
      _ = 0 := by simp
  simp only [HeatSwitchCone.logI, HeatSwitchCone.logS, HeatSwitchCone.logPi, hi, hs, hpi,
    mul_zero, add_zero, sub_zero, and_self]

theorem heated_lags_before_patch (F : Profile) {R : ℝ} (hR : 0 < R)
    (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 ≤ OutgoingDilation.patchClock F)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    HeatSwitchCone.Qs F R coef p = OutgoingHistories.Qs F.reset F.amp p ∧
      HeatSwitchCone.Ns F R coef p = OutgoingHistories.Ns F.reset F.amp p := by
  have hi : (fun eta => HeatSwitchCone.logI F R coef (p.1, eta)) =
      (fun eta => OutgoingHistories.I F.reset (p.1, eta)) :=
    funext (fun eta => (heated_histories_before_patch F hR coef (p := (p.1, eta)) hp).1)
  have hs : (fun eta => HeatSwitchCone.logS F R coef (p.1, eta)) =
      (fun eta => OutgoingHistories.S F.reset F.amp (p.1, eta)) :=
    funext (fun eta => (heated_histories_before_patch F hR coef (p := (p.1, eta)) hp).2.1)
  have hpi : (fun eta => HeatSwitchCone.logPi F R coef (p.1, eta)) =
      (fun eta => OutgoingHistories.Pi F.reset (p.1, eta)) :=
    funext (fun eta => (heated_histories_before_patch F hR coef (p := (p.1, eta)) hp).2.2)
  have hv := heated_histories_before_patch F hR coef hp
  constructor
  · rw [HeatSwitchCone.Qs, OutgoingHistories.Qs_integrated, hv.1, hi,
      smooth_parameterWithin_eq_dEta (OutgoingHistories.I_smooth F.reset) heta,
      HeatSwitchCone.logE_before_patch F hR coef hp,
      show OutgoingHistories.X p * OutgoingHistories.H F.reset p =
        Real.exp (3 * p.1 / 2) * F.logE p from OutgoingHistories.angularWeight_eq F.reset p]
  · rw [HeatSwitchCone.Ns, OutgoingHistories.Ns_integrated, hv.2.1, hv.2.2, hs, hpi,
      smooth_parameterWithin_eq_dEta (OutgoingHistories.S_smooth F.reset F.amp_contDiff) heta,
      smooth_parameterWithin_eq_dEta (OutgoingHistories.Pi_smooth F.reset) heta]
    rfl

theorem heated_shears_before_patch (F : Profile) {R : ℝ} (hR : 0 < R)
    (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 < OutgoingDilation.patchClock F) :
    HeatSwitchCone.radialA F R coef p = OutgoingEntranceCone.coneA F.reset p ∧
      HeatSwitchCone.radialB F R coef p = OutgoingEntranceCone.coneB F.reset F.amp p := by
  have he : (fun y => HeatSwitchCone.logE F R coef (y, p.2)) =ᶠ[𝓝 p.1]
      (fun y => F.logE (y, p.2)) := by
    filter_upwards [Iio_mem_nhds hp] with y hy
    exact HeatSwitchCone.logE_before_patch F hR coef hy.le
  constructor
  · rw [HeatSwitchCone.radialA, he.deriv_eq, HeatSwitchCone.logE_before_patch F hR coef hp.le,
      OutgoingEntranceCone.coneA_eq_E_derivative,
      OutgoingHistories.dY_eq_deriv (OutgoingHistories.E_smooth F.reset)]
    rfl
  · rw [HeatSwitchCone.radialB, HeatSwitchCone.logE_before_patch F hR coef hp.le]
    rfl

theorem heated_relaxed_before_patch (F : Profile) {R : ℝ} (hR : 0 < R)
    (coef : ℝ → HeatedOutgoing.Coeff) {p : Point} (hp : p.1 < OutgoingDilation.patchClock F)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : OutgoingCone.RelaxedAt F.reset F.amp R p) : HeatRelaxedAt F R coef p := by
  have hl := heated_lags_before_patch F hR coef hp.le heta
  have ha := heated_shears_before_patch F hR coef hp
  have hr : HeatSwitchCone.ratio F R coef p = OutgoingEntranceCone.coneRatio F.reset F.amp p := by
    simp only [HeatSwitchCone.ratio, hl.1, hl.2, HeatSwitchCone.logE_before_patch F hR coef hp.le]
    rfl
  have hs : HeatSwitchCone.stressScale F R coef p = OutgoingHistories.p1 R F.reset F.amp p := by
    rw [HeatSwitchCone.stressScale, hl.1]
    rfl
  refine ⟨hl.1 ▸ hc.angular_positive, ha.1 ▸ hc.radial_positive, ?_, ?_⟩
  · simp only [HeatSwitchCone.normalP, HeatSwitchCone.sourceC, hs, ha.1, ha.2, hr]
    exact hc.stress_gt_two
  · simp only [HeatSwitchCone.normalP, HeatSwitchCone.normalJ, HeatSwitchCone.normalV,
      HeatSwitchCone.sourceC, HeatSwitchCone.sourceJ, hs, ha.1, ha.2, hr]
    exact hc.root_strict

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem log_second_stock {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hq : HeatSwitchCone.Qs F W.controls.radius W.heat.coefficients p ≠ 0) :
    ReferenceBounds.p2 W.profiles F.data.h (chart W.controls.radius p) =
      HeatSwitchCone.stressScale F W.controls.radius W.heat.coefficients p *
        HeatSwitchCone.ratio F W.controls.radius W.heat.coefficients p := by
  rw [(log_stocks W hp heta).2]
  exact stock_ratio_identity _ _ _ _ _ hq

theorem heat_relaxed {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : HeatRelaxedAt F W.controls.radius W.heat.coefficients p) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h (chart W.controls.radius p) := by
  have hs := log_shears W hp heta
  unfold ActivationContinuation.IsRelaxed
  rw [hs.1, hs.2, (log_stocks W hp heta).1, log_second_stock W hp heta hc.1.ne']
  exact relaxed_scaled_coordinates hc.2.1 hc.2.2.1 hc.2.2.2

theorem heat_true {p : Point} (hp : W.controls.heatJoin < (chart W.controls.radius p).1)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hc : HeatSwitchCone.TrueAt F W.controls.radius W.heat.coefficients p) :
    IsTrue W.profiles F.data.h (chart W.controls.radius p) := by
  refine ⟨heat_relaxed W hp heta ⟨hc.1, hc.2.1, hc.2.2.2.1, hc.2.2.2.2⟩, ?_⟩
  rw [(log_shears W hp heta).1, (log_shears W hp heta).2]
  simp only [ActivationContinuation.shearSize, neg_div, neg_sq]
  exact hc.2.2.1

theorem chart_after_match {p : Point} (hp : 0 ≤ p.1) :
    W.controls.heatJoin < (chart W.controls.radius p).1 := by
  exact W.controls.heatJoin_lt_radius.trans_le
    (le_mul_of_one_le_right W.controls.radius_pos.le (Real.one_le_exp hp))

theorem chart_after_matching {p : Point} (hp : (-5 : ℝ) < p.1) :
    W.controls.heatJoin < (chart W.controls.radius p).1 :=
  mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hp) W.controls.radius_pos

theorem clean_relaxed_before_hold
    (hc : OutgoingCone.ProfileCleanCone F W.controls.radius (-5)) {p : Point}
    (hy : (-5 : ℝ) < p.1) (hhold : p.1 ≤ F.data.core.holdStart)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.IsRelaxed W.profiles F.data.h (chart W.controls.radius p) := by
  have hend : F.data.core.holdStart ≤ OutgoingCone.cleanEnd F.data :=
    (OutgoingTail.coreEndpoint_ge_hold F.data).trans
      (TerminalHistoryBridge.terminalStart_after_endpoint F).le
  exact heat_relaxed W (chart_after_matching W hy) heta
    (heated_relaxed_before_patch F W.controls.radius_pos W.heat.coefficients
      (hhold.trans_lt (OutgoingDilation.patchClock_after_hold F)) heta
      (hc.relaxed p ⟨⟨hy.le, hhold.trans hend⟩, heta⟩))

theorem terminal_true {y eta : ℝ} (hsmall : TerminalCone.SmallTail F.data)
    (hXR : TerminalCone.radiusThreshold F ≤ W.controls.radius)
    (hy : TerminalCone.terminalStart F.data ≤ y) (hy' : y < OutgoingTail.tailEnd F.data)
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    IsTrue W.profiles F.data.h (chart W.controls.radius (y, eta)) := by
  have hy0 : 0 ≤ y := (SchedulePressure.endpoint_pos F.data).le.trans
    ((TerminalHistoryBridge.terminalStart_after_endpoint F).le.trans hy)
  exact heat_true W (chart_after_match W hy0) heta
    (TerminalHistoryBridge.terminal_forward_cone F W.outgoing_specification W.heat.physical
      hsmall hXR hy hy' heta).1

end Witness

/-! ## A compensation bound chosen before the entrance radius -/

/-- Compensated family data, collecting `bound`, `bound_pos`, `radiusFloor`, `radiusFloor_pos`,
`branches`, `true_from_hold`. -/
structure CompensatedFamily (F : Profile) where
  /-- Bound of `CompensatedFamily`, of type `ℝ`. -/
  bound : ℝ
  bound_pos : 0 < bound
  /-- Radius floor of `CompensatedFamily`, of type `ℝ`. -/
  radiusFloor : ℝ
  radiusFloor_pos : 0 < radiusFloor
  branches : ∀ XR : ℝ, radiusFloor ≤ XR → Nonempty (ExtendedHeatedOutgoing.Witness F XR bound)
  true_from_hold : ∀ XR : ℝ, radiusFloor ≤ XR →
    ∀ w : ExtendedHeatedOutgoing.Witness F XR bound,
    ∀ p ∈ OutgoingCone.trueWindow F.data, HeatSwitchCone.TrueAt F XR w.coefficients p

theorem exists_compensatedFamily (F : Profile) {anchor left : ℝ}
    (hc : OutgoingCone.CleanOutgoingCone F.reset anchor left) (ha : 0 < anchor) :
    Nonempty (CompensatedFamily F) := by
  obtain ⟨R0, B, hR0, hB, hbranches⟩ := ExtendedHeatedOutgoing.exists_witness F
  obtain ⟨R1, _hR1, hcone⟩ := HeatSwitchCone.preserves_true_cone F hc ha B
  exact ⟨⟨B, hB, max R0 R1, hR0.trans_le (le_max_left _ _),
    fun XR hXR => hbranches XR ((le_max_left _ _).trans hXR),
    fun XR hXR w p hp => hcone XR ((le_max_right _ _).trans hXR) w.physical p hp⟩⟩

namespace CompensatedFamily

variable {F : Profile} (G : CompensatedFamily F)

/-- The actual heat witness and the nominal fields are constructed only after
the same physical radius has met the previously fixed bound. -/
noncomputable def assemble {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) : NominalProfile.Witness
        F :=
  ⟨A, c, D, hF, G.bound, Classical.choice (G.branches c.radius hr), hsep, hs⟩

theorem assemble_axis {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) :
    (G.assemble hF A c hr hsep hs).axis = A := rfl

theorem assemble_controls {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) :
    (G.assemble hF A c hr hsep hs).controls = c := rfl

theorem assemble_bound {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta) :
    (G.assemble hF A c hr hsep hs).heatBound = G.bound := rfl

theorem assemble_true_from_hold {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta)
    (p : Point) (hp : p ∈ OutgoingCone.trueWindow F.data) :
    HeatSwitchCone.TrueAt F c.radius (G.assemble hF A c hr hsep hs).heat.coefficients p :=
  G.true_from_hold c.radius hr _ p hp

theorem assemble_profile_true {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta)
    (p : Point) (hp : p ∈ OutgoingCone.trueWindow F.data) :
    IsTrue (G.assemble hF A c hr hsep hs).profiles F.data.h (chart c.radius p) := by
  let W := G.assemble hF A c hr hsep hs
  have hy0 : 0 ≤ p.1 := F.data.core.holdStart_pos.le.trans hp.1.1
  exact Witness.heat_true W (Witness.chart_after_match W hy0) hp.2
    (G.assemble_true_from_hold hF A c hr hsep hs p hp)

theorem assemble_profile_true_late {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta)
    (hsmall : TerminalCone.SmallTail F.data) (hXR : TerminalCone.radiusThreshold F ≤ c.radius)
    {p : Point} (hp : F.data.core.holdStart ≤ p.1) (hend : p.1 < OutgoingTail.tailEnd F.data)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    IsTrue (G.assemble hF A c hr hsep hs).profiles F.data.h (chart c.radius p) := by
  by_cases hy : p.1 ≤ OutgoingCone.cleanEnd F.data
  · exact G.assemble_profile_true hF A c hr hsep hs p ⟨⟨hp, hy⟩, heta⟩
  · exact Witness.terminal_true (G.assemble hF A c hr hsep hs) hsmall hXR
      (le_of_not_ge hy) hend heta

theorem assemble_profile_relaxed_outer {D : ℝ} (hF : OutgoingProfile.Specification F D)
    (A : AxisStage F) (c : Controls A) (hr : G.radiusFloor ≤ c.radius)
    (hsep : c.separation ≤ Real.exp (-8))
    (hs : ∀ eta ∈ HeatedOutgoing.parameterDomain, SmallDebt F c.debt eta)
    (hsmall : TerminalCone.SmallTail F.data) (hXR : TerminalCone.radiusThreshold F ≤ c.radius)
    (hclean : OutgoingCone.ProfileCleanCone F c.radius (-5))
    {p : Point} (hp : (-5 : ℝ) < p.1) (hend : p.1 < OutgoingTail.tailEnd F.data)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.IsRelaxed (G.assemble hF A c hr hsep hs).profiles F.data.h
      (chart c.radius p) := by
  by_cases hy : p.1 ≤ F.data.core.holdStart
  · exact Witness.clean_relaxed_before_hold (G.assemble hF A c hr hsep hs) hclean hp hy heta
  · exact (G.assemble_profile_true_late hF A c hr hsep hs hsmall hXR (le_of_not_ge hy) hend heta).1

/-- The already selected axis stage and continuation are used literally in
the final fields; only the compensation branch is selected here. -/
noncomputable def assemblePrepared {D : ℝ} (hF : OutgoingProfile.Specification F D)
    {N : ℕ} {delta radiusFloor : ℝ}
    (M : MatchingConeBounds.PreparedWitness F N delta radiusFloor)
    (hr : G.radiusFloor ≤ radiusFloor) : NominalProfile.Witness F :=
  G.assemble hF M.axis M.controls (hr.trans M.bounds.radius_large)
    M.bounds.matching.separation.le (fun _eta heta => M.bounds.matching.smallDebt
        M.bounds.debt_radius heta)

theorem prepared_continuation_relaxed {D : ℝ} (hF : OutgoingProfile.Specification F D)
    {N : ℕ} {delta radiusFloor : ℝ}
    (M : MatchingConeBounds.PreparedWitness F N delta radiusFloor)
    (hr : G.radiusFloor ≤ radiusFloor) {p : Point}
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain)
    (hp : p.1 ∈ Icc M.continuation.parameters.startRadius (110 : ℝ)) :
    ActivationContinuation.IsRelaxed (G.assemblePrepared hF M hr).profiles F.data.h p :=
  Witness.continuation_relaxed (G.assemblePrepared hF M hr) M.continuation M.shapeTime_pos rfl heta
      hp

theorem prepared_shape_relaxed {D : ℝ} (hF : OutgoingProfile.Specification F D)
    {N : ℕ} {delta radiusFloor : ℝ}
    (M : MatchingConeBounds.PreparedWitness F N delta radiusFloor)
    (hr : G.radiusFloor ≤ radiusFloor) {X eta : ℝ}
    (hX : NominalProfile.Xi ≤ X) (hR : X ≤ M.controls.radius * Real.exp (-8))
    (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.IsRelaxed (G.assemblePrepared hF M hr).profiles F.data.h (X, eta) := by
  let W := G.assemblePrepared hF M hr
  have hsmall := M.bounds.matching.smallDebt M.bounds.debt_radius heta
  have hinit := continuation_first_at_Xi M.continuation M.shapeTime_pos
    M.bounds.matching.separation.le hsmall heta
  have hc := M.bounds.shape_relaxed hX hR heta hinit
  apply Witness.prefix_relaxed W (NominalProfile.Xi_pos.trans_le hX) _ heta hc
  exact hR.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ -5)) M.controls.radius_pos.le)

end CompensatedFamily

namespace Initial

open NaturalAxisCoefficients

/-- Exact physical shears on the initial natural collar. -/
theorem physical_initial_shears {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (E : NaturalEntrance.EntranceProfile d Λ C) {hΛ : 0 < Λ}
    {hsmall : NaturalAxisData.SmallParameters h j} {hP0 : ContDiff ℝ ∞ P0}
    (r : ActivationContinuation.RampParameters E.profile.family hΛ hsmall hP0)
    {y η : ℝ} (hy : y ≤ r.refTime) (hη : η ∈ ReferencePath.parameterInterval) :
    let N := ReferencePath.Input.ofNatural hΛ E.profile.family
    let L := StressActivation.FromReference.refLog N r.refTime
    let U := StressActivation.FromReference.refAxial N r.refTime
    let z : Point := (radius N.endpoint y, η)
    ActivationContinuation.shearA r.profiles z = actualP1 r.actTime r.kappa L (y, η) ∧
      ActivationContinuation.shearB r.profiles z = actualP2 r.actTime r.kappa N.endpoint L U (y, η)
          := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  let L := StressActivation.FromReference.refLog N r.refTime
  let U := StressActivation.FromReference.refAxial N r.refTime
  let z : Point := (radius N.endpoint y, η)
  let R := r.reference
  let P := r.profiles
  have hx : 0 < z.1 := mul_pos N.endpoint_pos (Real.exp_pos y)
  have hlog : R.logPoint z = (y, η) := by
    change (R.logTime (radius R.radius0 y), η) = (y, η)
    rw [R.logTime_chart]
  have hd := TransitionRamp.physical_radial_equations E.profile.family hΛ hsmall
    r.refTime_pos r.refTime_bound hP0 (κ := r.kappa) r.actTime_pos r.before_big
      r.widthU_pos r.widthA_pos hη hx
  change (z.1 * radialPartial P.f z / P.f z =
      TransitionRamp.angularSlope r.actTime r.kappa R.bigTime r.widthU r.widthA R.angularStock
          (R.logPoint z)) ∧
    (z.1 * radialPartial P.U z =
      TransitionRamp.axialSlope r.actTime r.kappa R.bigTime r.widthU R.axialStock (R.logPoint z))
          at hd
  rw [hlog] at hd
  have hs := TransitionRamp.ofNatural_stock_slopes E.profile.family hΛ hsmall
    r.refTime_pos r.refTime_bound hP0 y hy hη
  change R.angularStock (y, η) = -2 * radialPartial L (y, η) ∧
    R.axialStock (y, η) = -2 * radialPartial U (y, η) at hs
  have hb : y ≤ R.bigTime := hy.trans r.before_big
  have hb' : y ≤ R.bigTime + r.widthU := by linarith [r.widthU_pos]
  have hR : z.1 ≤ N.endpoint * Real.exp r.refTime :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) N.endpoint_pos.le
  have hf : P.f z = activatedAngular r.actTime r.kappa L (y, η) :=
    (r.initial_fields hη hR).1.trans
      (StressActivation.FromReference.f_logPullback N r.actTime_pos r.refTime_pos r.refTime_bound
          r.kappa y hη)
  have hE : P.E z = velocity N.endpoint (activatedAngular r.actTime r.kappa L) (y, η) := by
    change Real.sqrt (2 * z.1) * P.f z = _
    rw [hf]
    rfl
  have hL := StressActivation.FromReference.refLog_smooth N r.refTime_pos r.refTime_bound
  have hU := StressActivation.FromReference.refAxial_smooth N r.refTime_pos r.refTime_bound
  constructor
  · change ActivationContinuation.shearA P z = _
    calc
      _ = -2 * (z.1 * radialPartial P.f z / P.f z) := by unfold ActivationContinuation.shearA; ring
      _ = -2 * TransitionRamp.baseSlope r.actTime r.kappa R.angularStock (y, η) := by
        rw [hd.1, TransitionRamp.angularSlope_before r.widthA_pos R.angularStock hb']
      _ = damping r.actTime r.kappa y * referenceP1 L (y, η) := by
        unfold TransitionRamp.baseSlope
        rw [hs.1]
        unfold referenceP1
        ring
      _ = _ := (actualP1_eq r.actTime r.kappa ReferencePath.parameterInterval_open hL y hη).symm
  · change ActivationContinuation.shearB P z = _
    calc
      _ = -2 * (z.1 * radialPartial P.U z) / P.E z := by unfold ActivationContinuation.shearB; ring
      _ = -2 * TransitionRamp.baseSlope r.actTime r.kappa R.axialStock (y, η) /
          velocity N.endpoint (activatedAngular r.actTime r.kappa L) (y, η) := by
        rw [hd.2, TransitionRamp.axialSlope_before r.widthU_pos R.axialStock hb, hE]
      _ = -2 * (damping r.actTime r.kappa y * radialPartial U (y, η)) /
          velocity N.endpoint (activatedAngular r.actTime r.kappa L) (y, η) := by
        unfold TransitionRamp.baseSlope
        rw [hs.2]
        ring
      _ = _ := by
        unfold actualP2
        rw [(controlled_hasDerivAt r.actTime r.kappa ReferencePath.parameterInterval_open hU y
            hη).deriv]

/-- Positivity from this same constructed entrance profile. -/
theorem referenceP1_positive_initial {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (E : NaturalEntrance.EntranceProfile d Λ C) {hΛ : 0 < Λ}
    {hsmall : NaturalAxisData.SmallParameters h j} {hP0 : ContDiff ℝ ∞ P0}
    (r : ActivationContinuation.RampParameters E.profile.family hΛ hsmall hP0)
    {y η : ℝ} (hy : y ≤ r.refTime) (hη : η ∈ Icc (-1 : ℝ) 1) :
    0 < referenceP1 (StressActivation.FromReference.refLog
      (ReferencePath.Input.ofNatural hΛ E.profile.family) r.refTime) (y, η) := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  rw [ActivationCone.referenceP1_natural N r.refTime_pos r.refTime_bound hy
      (original_interval_interior hη)]
  apply E.slope_positive
  · change (Λ * (N.fromLog (y, η)).1, η) ∈ NaturalEntrance.entranceSet
    have hyT : y < ReferencePath.rampLimit := by linarith [r.refTime_pos, r.refTime_bound]
    have he : Real.exp y < 41 / 40 := by
      simpa only [ReferencePath.rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)]
        using Real.exp_lt_exp.mpr hyT
    have hid : Λ * (N.fromLog (y, η)).1 = 4 * Real.exp y := N.fromLog_scaled (y, η)
    exact ⟨⟨by rw [hid]; positivity, by rw [hid]; linarith⟩, hη⟩
  · exact mul_pos N.endpoint_pos (Real.exp_pos y)

theorem shearSize_eq_initial (a b : ℝ) (ha : a ≠ 0) :
    ActivationContinuation.shearSize a b = a + b ^ 2 / a := by
  unfold ActivationContinuation.shearSize
  field_simp

theorem projection_eq_initial (h X0 T κ : ℝ) (I : HistoryRow → ℝ → ℝ)
    (L U : ProfileHistories.Field) (p : Point) :
    ActivationContinuation.projection (ActivationCone.activatedStockOne h X0 I L U T κ p)
      (ActivationCone.activatedStockTwo h X0 I L U T κ p)
      (actualP1 T κ L p) (actualP2 T κ X0 L U p) =
        ActivationCone.activatedProjection h X0 I L U T κ p := rfl

theorem transverse_eq_initial (h X0 T κ : ℝ) (I : HistoryRow → ℝ → ℝ)
    (L U : ProfileHistories.Field) (p : Point) :
    ActivationContinuation.transverse (ActivationCone.activatedStockOne h X0 I L U T κ p)
      (ActivationCone.activatedStockTwo h X0 I L U T κ p)
      (actualP1 T κ L p) (actualP2 T κ X0 L U p) =
        ActivationCone.activatedCross h X0 I L U T κ p := rfl


/-- The actual ACT histories of the same continuation witness give the
logarithmic stock coordinates in its initial activation certificate. -/
theorem physical_initial_stocks {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0}
    (r : ActivationContinuation.RampParameters E.profile.family hΛ hsmall hP0)
    {y η : ℝ} (hy : y ≤ r.refTime) (hη : η ∈ ReferencePath.parameterInterval) :
    let N := ReferencePath.Input.ofNatural hΛ E.profile.family
    let L := StressActivation.FromReference.refLog N r.refTime
    let U := StressActivation.FromReference.refAxial N r.refTime
    let I := ActivationStocks.FromReference.initial N r.refTime_pos r.refTime_bound P0 hP0
    let z : Point := (radius N.endpoint y, η)
    ReferenceBounds.p1 r.profiles h z =
      ActivationCone.activatedStockOne h N.endpoint I L U r.actTime r.kappa (y, η) ∧
    ReferenceBounds.p2 r.profiles h z =
      ActivationCone.activatedStockTwo h N.endpoint I L U r.actTime r.kappa (y, η) := by
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  let z : Point := (radius N.endpoint y, η)
  let Q := StressActivation.FromReference.histories N r.actTime_pos r.refTime_pos
    r.refTime_bound r.kappa P0 hP0
  have hz : z ∈ N.radialDomain.carrier := StressActivation.FromReference.log_radius_mem N y hη
  have hX : 0 < z.1 := mul_pos N.endpoint_pos (Real.exp_pos y)
  have hR : z.1 ≤ N.endpoint * Real.exp r.refTime :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) N.endpoint_pos.le
  have hf : Q.f z ≠ 0 :=
    (StressActivation.FromReference.f_pos N r.actTime r.kappa r.refTime hz hX.le).ne'
  have hc := NominalConeAssembly.coordinates_of_prefix r.profiles Q h
    ReferencePath.parameterInterval_open (R := N.endpoint * Real.exp r.refTime) rfl
    (fun p hp hpR => (r.initial_fields hp hpR).1)
    (fun p hp hpR => (r.initial_fields hp hpR).2)
    (p := z) hz hz hX hR hη hf
  have h1 := ActivationStocks.FromReference.actual_stockOne_logView N r.actTime_pos
    r.refTime_pos r.refTime_bound r.kappa h P0 hP0 y hη
  have h2 := ActivationStocks.FromReference.actual_stockTwo_logView N r.actTime_pos
    r.refTime_pos r.refTime_bound r.kappa h P0 hP0 y hη
  refine ⟨hc.2.2.1.trans ?_, hc.2.2.2.trans ?_⟩
  · exact (NominalConeAssembly.p1_eq_stock Q h z).trans h1
  · exact (NominalConeAssembly.p2_eq_stock Q h z).trans h2


theorem activation_cone {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : AnalyticInputs h j σ P0} (E : NaturalEntrance.EntranceProfile d Λ C)
    {hΛ : 0 < Λ} {hsmall : NaturalAxisData.SmallParameters h j}
    {hP0 : ContDiff ℝ ∞ P0} {order : ℕ} {eps : ℝ}
    (w : ActivationContinuation.ContinuationWitness E hΛ hsmall hP0 order eps) :
    let N := ReferencePath.Input.ofNatural hΛ E.profile.family
    (∀ y eta : ℝ, 0 < y → y ≤ w.parameters.actTime → eta ∈ Icc (-1 : ℝ) 1 →
      ActivationContinuation.IsRelaxed w.parameters.profiles h (radius N.endpoint y, eta)) ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ w.parameters.actTime ∧
      ∀ y eta : ℝ, 0 < y → y ≤ t → eta ∈ Icc (-1 : ℝ) 1 →
        IsTrue w.parameters.profiles h (radius N.endpoint y, eta) := by
  let r := w.parameters
  let N := ReferencePath.Input.ofNatural hΛ E.profile.family
  let L := StressActivation.FromReference.refLog N r.refTime
  let U := StressActivation.FromReference.refAxial N r.refTime
  let I := ActivationStocks.FromReference.initial N r.refTime_pos r.refTime_bound P0 hP0
  obtain ⟨theta, htheta, htheta1, hcert⟩ := w.initial_activation
  have hpositive (y eta : ℝ) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      0 < actualP1 r.actTime r.kappa L (y, eta) := by
    exact actualP1_pos r.actTime ⟨r.kappa_pos, r.kappa_lt_one.le⟩
      ReferencePath.parameterInterval_open
      (StressActivation.FromReference.refLog_smooth N r.refTime_pos r.refTime_bound) y
      (original_interval_interior heta) (referenceP1_positive_initial E r (hy.trans r.actTime_le)
          heta)
  have hsize (y eta : ℝ) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      ActivationContinuation.shearSize
        (ActivationContinuation.shearA r.profiles (radius N.endpoint y, eta))
        (ActivationContinuation.shearB r.profiles (radius N.endpoint y, eta)) =
          StressActivation.shearSize r.actTime r.kappa N.endpoint L U (y, eta) := by
    have hs := physical_initial_shears E r (hy.trans r.actTime_le) (original_interval_interior heta)
    rw [hs.1, hs.2, shearSize_eq_initial _ _ (hpositive y eta hy heta).ne']
    rfl
  have hproj (y eta : ℝ) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      ActivationContinuation.projection
        (ReferenceBounds.p1 r.profiles h (radius N.endpoint y, eta))
        (ReferenceBounds.p2 r.profiles h (radius N.endpoint y, eta))
        (ActivationContinuation.shearA r.profiles (radius N.endpoint y, eta))
        (ActivationContinuation.shearB r.profiles (radius N.endpoint y, eta)) =
          ActivationCone.activatedProjection h N.endpoint I L U r.actTime r.kappa (y, eta) := by
    have hs := physical_initial_shears E r (hy.trans r.actTime_le) (original_interval_interior heta)
    have hp := physical_initial_stocks E r (hy.trans r.actTime_le) (original_interval_interior heta)
    rw [hs.1, hs.2, hp.1, hp.2]
    rfl
  have hcross (y eta : ℝ) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      ActivationContinuation.transverse
        (ReferenceBounds.p1 r.profiles h (radius N.endpoint y, eta))
        (ReferenceBounds.p2 r.profiles h (radius N.endpoint y, eta))
        (ActivationContinuation.shearA r.profiles (radius N.endpoint y, eta))
        (ActivationContinuation.shearB r.profiles (radius N.endpoint y, eta)) =
          ActivationCone.activatedCross h N.endpoint I L U r.actTime r.kappa (y, eta) := by
    have hs := physical_initial_shears E r (hy.trans r.actTime_le) (original_interval_interior heta)
    have hp := physical_initial_stocks E r (hy.trans r.actTime_le) (original_interval_interior heta)
    rw [hs.1, hs.2, hp.1, hp.2]
    rfl
  have hrelaxed (y eta : ℝ) (hy0 : 0 < y) (hy : y ≤ r.actTime) (heta : eta ∈ Icc (-1 : ℝ) 1) :
      ActivationContinuation.IsRelaxed r.profiles h (radius N.endpoint y, eta) := by
    have hc := hcert y ⟨hy0, hy⟩ eta heta
    have hs := physical_initial_shears E r (hy.trans r.actTime_le) (original_interval_interior heta)
    refine ⟨?_, ?_, ?_⟩
    · rw [hs.1]
      exact hpositive y eta hy heta
    · rw [hproj y eta hy heta]
      exact lt_trans (by norm_num : (2 : ℝ) < 2 + 1 / 32) hc.2.1
    · rw [hsize y eta hy heta, hproj y eta hy heta, hcross y eta hy heta]
      exact hc.2.2.2.1
  refine ⟨hrelaxed, theta * r.actTime, mul_pos htheta r.actTime_pos, ?_, ?_⟩
  · nlinarith [r.actTime_pos]
  · intro y eta hy0 hy heta
    have hyT : y ≤ r.actTime := hy.trans (by nlinarith [r.actTime_pos])
    refine ⟨hrelaxed y eta hy0 hyT heta, ?_⟩
    rw [hsize y eta hyT heta]
    exact lt_trans (by norm_num : (2 : ℝ) < 2 + 1 / 16) ((hcert y ⟨hy0, hyT⟩ eta heta).2.2.2.2 hy)

end Initial

/-! ## The active annulus and one common ordered choice -/

/-- Active left, given by `4 / W.axis.scale`. -/
noncomputable def activeLeft {F : Profile} (W : NominalProfile.Witness F) : ℝ := 4 / W.axis.scale

/-- Active right, given by `W.controls.radius * Real.exp (OutgoingTail.tailEnd F.data)`. -/
noncomputable def activeRight {F : Profile} (W : NominalProfile.Witness F) : ℝ :=
  W.controls.radius * Real.exp (OutgoingTail.tailEnd F.data)

theorem activeLeft_pos {F : Profile} (W : NominalProfile.Witness F) : 0 < activeLeft W :=
  div_pos (by norm_num) W.axis.scale_pos

theorem activeLeft_lt_Xi {F : Profile} (W : NominalProfile.Witness F) :
    activeLeft W < NominalProfile.Xi := by
  have he := Real.one_lt_exp_iff.mpr W.controls.referenceWidth_pos
  have hmul : activeLeft W < activeLeft W * Real.exp W.controls.referenceWidth := by
    nlinarith [activeLeft_pos W]
  exact hmul.trans_le W.controls.activation_collar_le_Xi

theorem chart_log {R : ℝ} (hR : 0 < R) {p : Point} (hp : 0 < p.1) :
    chart R (Real.log (p.1 / R), p.2) = p := by
  apply Prod.ext
  · dsimp only [chart]
    rw [Real.exp_log (div_pos hp hR), mul_div_cancel₀ _ hR.ne']
  · rfl

theorem log_chart_lt {R X y : ℝ} (hR : 0 < R) (hX : 0 < X)
    (hy : X < R * Real.exp y) : Real.log (X / R) < y := by
  have hh : X / R < Real.exp y := (div_lt_iff₀ hR).mpr (by simpa only [mul_comm] using hy)
  simpa only [Real.log_exp] using Real.log_lt_log (div_pos hX hR) hh

theorem lt_log_chart {R X y : ℝ} (hR : 0 < R)
    (hy : R * Real.exp y < X) : y < Real.log (X / R) := by
  have hh : Real.exp y < X / R := (lt_div_iff₀ hR).mpr (by simpa only [mul_comm] using hy)
  simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos y) hh

/-- Every assertion concerns the same physical fields and absolute
histories. The extra lower speed condition is asserted only on the two
regions where the pre-modulation construction proves it. -/
structure Certificate {F : Profile} (W : NominalProfile.Witness F) : Prop where
  relaxed : ∀ p : Point, activeLeft W < p.1 → p.1 < activeRight W →
    p.2 ∈ HeatedOutgoing.parameterDomain → ActivationContinuation.IsRelaxed W.profiles F.data.h p
  initial : ∃ t : ℝ, 0 < t ∧ t ≤ W.controls.activationTime ∧
    ∀ y eta : ℝ, 0 < y → y ≤ t → eta ∈ HeatedOutgoing.parameterDomain →
      IsTrue W.profiles F.data.h (chart (activeLeft W) (y, eta))
  outgoing : ∀ y eta : ℝ, F.data.core.holdStart ≤ y → y < OutgoingTail.tailEnd F.data →
    eta ∈ HeatedOutgoing.parameterDomain → IsTrue W.profiles F.data.h (chart W.controls.radius (y,
        eta))

theorem Certificate.coordinates_smoothAt {F : Profile} {W : NominalProfile.Witness F}
    (hW : Certificate W) {p : Point} (hl : activeLeft W < p.1) (hr : p.1 < activeRight W)
    (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ContDiffAt ℝ ∞ (ActivationContinuation.shearA W.profiles) p ∧
      ContDiffAt ℝ ∞ (tilt W.profiles) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p1 W.profiles F.data.h) p ∧
      ContDiffAt ℝ ∞ (ReferenceBounds.p2 W.profiles F.data.h) p := by
  have hx := (activeLeft_pos W).trans hl
  exact cone_coordinates_smoothAt W.profiles F.data.h (W.domain_contains hx.le heta) hx
    (Witness.f_positive W hx heta).ne' (hW.relaxed p hl hr heta).first_positive.ne'
    (NaturalAxisData.L_pos W.axis.small heta).ne'

/-- Intermediate data retain the actual continuation and its repair
coefficients. The existence theorem below constructs every cone field in
this record from the already proved estimates. -/
structure Assembly (d : PreparedOutgoing.PreparedProfile) where
  /-- Family of `Assembly`, of type `CompensatedFamily d.profile`. -/
  family : CompensatedFamily d.profile
  /-- Delta of `Assembly`, of type `ℝ`. -/
  delta : ℝ
  /-- Radius floor of `Assembly`, of type `ℝ`. -/
  radiusFloor : ℝ
  /-- Matching of `Assembly`, of type `MatchingConeBounds.PreparedWitness d.profile 1 delta
  radiusFloor`. -/
  matching : MatchingConeBounds.PreparedWitness d.profile 1 delta radiusFloor
  family_floor : family.radiusFloor ≤ radiusFloor
  terminal_floor : TerminalCone.radiusThreshold d.profile ≤ matching.controls.radius
  clean : OutgoingCone.ProfileCleanCone d.profile matching.controls.radius (-5)
  repair : ∀ p : Point,
    p.1 ∈ Icc (matching.controls.radius * Real.exp (-8)) (matching.controls.radius * Real.exp (-5))
        →
    p.2 ∈ HeatedOutgoing.parameterDomain →
    ActivationContinuation.IsRelaxed
      (matching.controls.profiles matching.bounds.matching.separation.le) d.profile.data.h p

namespace Assembly

variable {d : PreparedOutgoing.PreparedProfile} (A : Assembly d)

/-- Witness, given by `A.family.assemblePrepared d.specification A.matching A.family_floor`. -/
noncomputable def witness : NominalProfile.Witness d.profile :=
  A.family.assemblePrepared d.specification A.matching A.family_floor

theorem outgoing {y eta : ℝ} (hy : d.profile.data.core.holdStart ≤ y)
    (hend : y < OutgoingTail.tailEnd d.profile.data) (heta : eta ∈ HeatedOutgoing.parameterDomain) :
    IsTrue A.witness.profiles d.profile.data.h (chart A.witness.controls.radius (y, eta)) :=
  A.family.assemble_profile_true_late d.specification A.matching.axis A.matching.controls
    (A.family_floor.trans A.matching.bounds.radius_large) A.matching.bounds.matching.separation.le
    _ d.terminal A.terminal_floor hy hend heta

theorem outer_relaxed {p : Point} (hXi : NominalProfile.Xi ≤ p.1)
    (hend : p.1 < activeRight A.witness) (heta : p.2 ∈ HeatedOutgoing.parameterDomain) :
    ActivationContinuation.IsRelaxed A.witness.profiles d.profile.data.h p := by
  have hx := NominalProfile.Xi_pos.trans_le hXi
  by_cases hshape : p.1 ≤ A.matching.controls.radius * Real.exp (-8)
  · exact A.family.prepared_shape_relaxed d.specification A.matching A.family_floor hXi hshape heta
  by_cases hrepair : p.1 ≤ A.matching.controls.radius * Real.exp (-5)
  · exact Witness.prefix_relaxed A.witness hx hrepair heta
      (A.repair p ⟨(lt_of_not_ge hshape).le, hrepair⟩ heta)
  have hlo := lt_log_chart A.matching.controls.radius_pos (lt_of_not_ge hrepair)
  have hhi := log_chart_lt A.matching.controls.radius_pos hx hend
  have hc := A.family.assemble_profile_relaxed_outer d.specification A.matching.axis
      A.matching.controls
    (A.family_floor.trans A.matching.bounds.radius_large) A.matching.bounds.matching.separation.le
    (fun _eta hη => A.matching.bounds.matching.smallDebt A.matching.bounds.debt_radius hη)
    d.terminal A.terminal_floor A.clean (p := (Real.log (p.1 / A.matching.controls.radius), p.2))
        hlo hhi heta
  rwa [chart_log A.matching.controls.radius_pos hx] at hc

theorem initial_cones :
    (∀ y eta : ℝ, 0 < y → y ≤ A.witness.controls.activationTime →
      eta ∈ HeatedOutgoing.parameterDomain →
      ActivationContinuation.IsRelaxed A.witness.profiles d.profile.data.h
        (chart (activeLeft A.witness) (y, eta))) ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ A.witness.controls.activationTime ∧
      ∀ y eta : ℝ, 0 < y → y ≤ t → eta ∈ HeatedOutgoing.parameterDomain →
        IsTrue A.witness.profiles d.profile.data.h (chart (activeLeft A.witness) (y, eta)) := by
  have hb := Initial.activation_cone A.matching.axis.natural A.matching.continuation
  have hXi (y eta : ℝ) (hy : y ≤ A.witness.controls.activationTime) :
      (chart (activeLeft A.witness) (y, eta)).1 ≤ NominalProfile.Xi := by
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (hy.trans A.witness.controls.activationTime_le))
      (activeLeft_pos A.witness).le).trans A.witness.controls.activation_collar_le_Xi
  constructor
  · intro y eta hy0 hy heta
    exact Witness.seed_relaxed A.witness (chart_positive (activeLeft_pos A.witness) (y, eta))
      (hXi y eta hy) heta (hb.1 y eta hy0 hy heta)
  · obtain ⟨t, ht, htT, htrue⟩ := hb.2
    refine ⟨t, ht, htT, ?_⟩
    intro y eta hy0 hy heta
    exact Witness.seed_true A.witness (chart_positive (activeLeft_pos A.witness) (y, eta))
      (hXi y eta (hy.trans htT)) heta (htrue y eta hy0 hy heta)

/-- The nominal profile has the relaxed cone throughout its active
annulus and the true cone in its initial collar and from the shaped hold
through the terminal region. Every component uses the stored witness. -/
theorem certificate : Certificate A.witness := by
  have hi := A.initial_cones
  refine ⟨?_, hi.2, ?_⟩
  · intro p hl hr heta
    have hx := (activeLeft_pos A.witness).trans hl
    by_cases hXi : p.1 ≤ NominalProfile.Xi
    · have hy0 : 0 < Real.log (p.1 / activeLeft A.witness) := by
        apply lt_log_chart (activeLeft_pos A.witness)
        simpa only [Real.exp_zero, mul_one] using hl
      by_cases hy : Real.log (p.1 / activeLeft A.witness) ≤ A.witness.controls.activationTime
      · have hc := hi.1 (Real.log (p.1 / activeLeft A.witness)) p.2 hy0 hy heta
        rwa [chart_log (activeLeft_pos A.witness) hx] at hc
      · have hstart : A.matching.continuation.parameters.startRadius ≤ p.1 := by
          change activeLeft A.witness * Real.exp A.witness.controls.activationTime ≤ p.1
          by_contra hn
          exact hy (log_chart_lt (activeLeft_pos A.witness) hx (lt_of_not_ge hn)).le
        exact A.family.prepared_continuation_relaxed d.specification A.matching A.family_floor
          heta ⟨hstart, hXi⟩
    · exact A.outer_relaxed (le_of_not_ge hXi) hr heta
  · intro y eta hy hend heta
    exact A.outgoing hy hend heta

end Assembly

theorem assembly_exists (d : PreparedOutgoing.PreparedProfile) : Nonempty (Assembly d) := by
  obtain ⟨cleanFloor, hcleanFloor, hclean⟩ := d.clean (-5) (by norm_num)
  have hanchor : 0 < cleanFloor + 1 := by linarith
  obtain ⟨G⟩ := exists_compensatedFamily d.profile (hclean (cleanFloor + 1) (by linarith)) hanchor
  obtain ⟨delta, repairFloor, hdelta, _hrepairFloor, hrepair⟩ :=
      RepairConeBounds.exists_repair_cone d.profile
  let floor := max G.radiusFloor (max (cleanFloor + 1) (max repairFloor
      (TerminalCone.radiusThreshold d.profile)))
  obtain ⟨M⟩ := MatchingConeBounds.preparedWitness_exists d.profile d.amplitude_lower d.height_upper
    1 le_rfl hdelta floor
  have hG : G.radiusFloor ≤ floor := le_max_left _ _
  have hC : cleanFloor + 1 ≤ floor := (le_max_left _ _).trans (le_max_right _ _)
  have hR : repairFloor ≤ floor := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hT : TerminalCone.radiusThreshold d.profile ≤ floor := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hendpoint : JetBounds.FiniteJetBound 1 (RepairConeBounds.endpointError M.controls)
      (Icc (-1 : ℝ) 1) delta := by
    intro n hn eta heta
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact M.bounds.endpoint eta heta n hn
  refine ⟨⟨G, delta, floor, M, hG, hT.trans M.bounds.radius_large,
    hclean M.controls.radius ?_, ?_⟩⟩
  · have hh := hC.trans M.bounds.radius_large
    exact lt_of_lt_of_le (by linarith : cleanFloor < cleanFloor + 1) hh
  · intro p hp heta
    exact hrepair M.axis M.controls M.bounds.matching.separation.le hendpoint M.bounds.coefficients
      (hR.trans M.bounds.radius_large) p hp heta (M.bounds.matching.smallDebt M.bounds.debt_radius
          heta)

/-- Any one prepared outgoing profile has a nominal witness with the
complete actual cone certificate. No cone or matching-debt assumption is
added to the prepared profile. -/
theorem exists_certificate (d : PreparedOutgoing.PreparedProfile) :
    ∃ W : NominalProfile.Witness d.profile, Certificate W := by
  obtain ⟨A⟩ := assembly_exists d
  exact ⟨A.witness, A.certificate⟩

theorem exists_nominal_cone :
    ∃ (F : Profile) (W : NominalProfile.Witness F), Certificate W := by
  obtain ⟨d⟩ := PreparedOutgoing.exists_prepared
  obtain ⟨W, hW⟩ := exists_certificate d
  exact ⟨d.profile, W, hW⟩

end NavierStokes.NominalConeAssembly
