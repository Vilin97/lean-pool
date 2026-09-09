/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.StressAlgebra
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothParameterIntegral
import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricFlatFactor
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Genuine smooth profile histories

The histories are actual integrals of jointly smooth profiles. Their parameter
derivatives and radial identities are derived from differentiation under the
integral and the fundamental theorem of calculus, rather than supplied as
independent history data.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ProfileHistories

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff

/-- Point: an abbreviation for `ℝ × ℝ`. -/
abbrev Point := ℝ × ℝ
/-- Field: an abbreviation for `Point → ℝ`. -/
abbrev Field := Point → ℝ

/-- An open profile domain containing every radial segment from the axis to
one of its points. Open rectangles centered radially at zero are examples. -/
structure RadialDomain where
  /-- Carrier of `RadialDomain`, of type `Set Point`. -/
  carrier : Set Point
  isOpen : IsOpen carrier
  scale_mem : ∀ p ∈ carrier, ∀ t ∈ Icc (0 : ℝ) 1, (t * p.1, p.2) ∈ carrier

/-- A concrete open rectangle meeting the axis. Positivity of R is needed
only to make it nonempty, not for the radial stability proof. -/
def RadialDomain.rectangle (R a b : ℝ) : RadialDomain where
  carrier := Ioo (-R) R ×ˢ Ioo a b
  isOpen := isOpen_Ioo.prod isOpen_Ioo
  scale_mem := by
    intro p hp t ht
    refine ⟨?_, hp.2⟩
    have hX : |p.1| < R := abs_lt.mpr hp.1
    have hmul : |t * p.1| ≤ |p.1| := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (abs_nonneg _) ht.2
    exact abs_lt.mp (hmul.trans_lt hX)

/-- Radial partial, given by `fderiv ℝ F p (1, 0)`. -/
def radialPartial (F : Field) (p : Point) : ℝ := fderiv ℝ F p (1, 0)
/-- Parameter partial, given by `fderiv ℝ F p (0, 1)`. -/
def parameterPartial (F : Field) (p : Point) : ℝ := fderiv ℝ F p (0, 1)

theorem radialPartial_hasDerivAt (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun x => F (x, p.2)) (radialPartial F p) p.1 := by
  have hf := (hF.contDiffAt (D.isOpen.mem_nhds hp)).differentiableAt (by simp)
  simpa only [radialPartial, Function.comp_def, id_eq, Prod.eta] using
    hf.hasFDerivAt.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

theorem parameterPartial_hasDerivAt (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun η => F (p.1, η)) (parameterPartial F p) p.2 := by
  have hf := (hF.contDiffAt (D.isOpen.mem_nhds hp)).differentiableAt (by simp)
  simpa only [parameterPartial, Function.comp_def, id_eq, Prod.eta] using
    hf.hasFDerivAt.comp_hasDerivAt p.2 ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))

theorem radialPartial_smooth (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) : ContDiffOn ℝ ∞ (radialPartial F) D.carrier := by
  exact (hF.fderiv_of_isOpen D.isOpen (by simp)).clm_apply contDiffOn_const

theorem parameterPartial_smooth (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) : ContDiffOn ℝ ∞ (parameterPartial F) D.carrier := by
  exact (hF.fderiv_of_isOpen D.isOpen (by simp)).clm_apply contDiffOn_const

section CompactParameterIntegral

variable {s : Set Point} {G : Point → ℝ → ℝ}

theorem compact_parameter_jet_continuous
    (hG : ∀ p ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ (fun z : Point × ℝ => G z.1 z.2) (p, t)) (k : ℕ) :
    ContinuousOn (fun z : Point × ℝ => SmoothParameterIntegral.jet G k z.1 z.2)
      (s ×ˢ Icc (0 : ℝ) 1) := by
  rintro ⟨p, t⟩ ⟨hp, ht⟩
  have hflip : ContDiffAt ℝ ∞ (Function.uncurry (fun t p => G p t)) (t, p) :=
    (hG p hp t ht).comp (t, p) (contDiffAt_snd.prodMk contDiffAt_fst)
  have h := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv (fun t p => G p t) k t p hflip
  exact ((h.comp (p, t) (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt).continuousWithinAt

theorem compact_parameter_integral_smooth (hs : IsOpen s)
    (hG : ∀ p ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ (fun z : Point × ℝ => G z.1 z.2) (p, t)) :
    ContDiffOn ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, G p t) s := by
  apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet hs zero_le_one
  · intro t ht p hp
    exact ((hG p hp t ht).comp p (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · exact compact_parameter_jet_continuous hG

theorem compact_parameter_fderiv_continuous
    (hG : ∀ p ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ (fun z : Point × ℝ => G z.1 z.2) (p, t)) :
    ContinuousOn (fun z : Point × ℝ => fderiv ℝ (fun p => G p z.2) z.1)
      (s ×ˢ Icc (0 : ℝ) 1) := by
  rintro ⟨p, t⟩ ⟨hp, ht⟩
  have hdup : ContDiffAt ℝ ∞
      (fun z : (Point × ℝ) × Point => G z.2 z.1.2) ((p, t), p) :=
    (hG p hp t ht).comp ((p, t), p) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  have hd : ContDiffAt ℝ ∞
      (fun z : Point × ℝ => fderiv ℝ (fun q => G q z.2) z.1) (p, t) :=
    hdup.fderiv contDiffAt_fst (by simp)
  exact hd.continuousAt.continuousWithinAt

/-- The derivative of the compact parameter integral is the integral of the
genuine parameter derivative. Joint smoothness supplies the local majorant. -/
theorem compact_parameter_integral_hasFDerivAt (hs : IsOpen s)
    (hG : ∀ p ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ (fun z : Point × ℝ => G z.1 z.2) (p, t))
    {p : Point} (hp : p ∈ s) :
    HasFDerivAt (fun q => ∫ t in (0 : ℝ)..1, G q t)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun q => G q t) p) p := by
  have hcont : ContinuousOn (fun z : Point × ℝ => G z.1 z.2) (s ×ˢ Icc (0 : ℝ) 1) := by
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    exact (hG q hq t ht).continuousAt.continuousWithinAt
  have hD := compact_parameter_fderiv_continuous hG
  obtain ⟨ε, hε, hεs⟩ := nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hp)
  have hcompact : IsCompact (closedBall p ε ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall p ε).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hD.mono (Set.prod_mono hεs Subset.rfl))
  have hslice : ∀ q ∈ s, ContinuousOn (G q) (Icc (0 : ℝ) 1) := by
    intro q hq
    exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hq, ht⟩)
  have hDslice : ContinuousOn (fun t => fderiv ℝ (fun q => G q t) p) (Icc (0 : ℝ) 1) :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hp, ht⟩)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := fun q t => fderiv ℝ (fun y => G y t) q)
    (bound := fun _ => C) (Metric.ball_mem_nhds _ hε)
  · filter_upwards [hs.mem_nhds hp] with q hq
    simpa only [uIoc_of_le zero_le_one] using
      ((hslice q hq).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · exact (hslice p hp).intervalIntegrable_of_Icc zero_le_one
  · simpa only [uIoc_of_le zero_le_one] using
      (hDslice.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · apply Filter.Eventually.of_forall
    intro t ht q hq
    rw [uIoc_of_le zero_le_one] at ht
    exact hC (q, t) ⟨ball_subset_closedBall hq, ht.1.le, ht.2⟩
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t ht q hq
    rw [uIoc_of_le zero_le_one] at ht
    exact (((hG q (hεs (ball_subset_closedBall hq)) t ⟨ht.1.le, ht.2⟩).comp q
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)).hasFDerivAt

end CompactParameterIntegral

/-- Regular radial average, including its value at the axis. -/
def average (F : Field) (p : Point) : ℝ := ∫ t in (0 : ℝ)..1, F (t * p.1, p.2)

/-- Actual radial history from the axis. -/
def primitive (F : Field) (p : Point) : ℝ := ∫ x in (0 : ℝ)..p.1, F (x, p.2)

theorem primitive_eq_mul_average (F : Field) (p : Point) :
    primitive F p = p.1 * average F p := by
  simpa only [primitive, average, smul_eq_mul, zero_mul, one_mul] using
    (intervalIntegral.smul_integral_comp_mul_right (fun x => F (x, p.2)) p.1
      (a := (0 : ℝ)) (b := 1)).symm

theorem average_at_axis (F : Field) (η : ℝ) : average F (0, η) = F (0, η) := by
  simp [average]

theorem primitive_at_axis (F : Field) (η : ℝ) : primitive F (0, η) = 0 := by
  simp [primitive]

theorem average_integrand_smooth (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (p : Point) (hp : p ∈ D.carrier)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun z : Point × ℝ => F (z.2 * z.1.1, z.1.2)) (p, t) := by
  apply (hF.contDiffAt (D.isOpen.mem_nhds (D.scale_mem p hp t ht))).comp (p, t)
  exact (contDiffAt_snd.mul contDiffAt_fst.fst).prodMk contDiffAt_fst.snd

theorem average_smooth (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) : ContDiffOn ℝ ∞ (average F) D.carrier :=
  compact_parameter_integral_smooth D.isOpen (average_integrand_smooth D hF)

theorem primitive_smooth (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) : ContDiffOn ℝ ∞ (primitive F) D.carrier := by
  have heq : primitive F = fun p => p.1 * average F p := funext (primitive_eq_mul_average F)
  rw [heq]
  exact contDiffOn_fst.mul (average_smooth D hF)

theorem RadialDomain.segment_mem (D : RadialDomain) {p : Point}
    (hp : p ∈ D.carrier) {x : ℝ} (hx : x ∈ uIcc 0 p.1) : (x, p.2) ∈ D.carrier := by
  rcases lt_trichotomy p.1 0 with hn | hz | hp'
  · rw [uIcc_of_ge hn.le] at hx
    have ht : x / p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg_of_nonpos hx.2 hn.le, (div_le_one_of_neg hn).2 hx.1⟩
    simpa only [div_mul_cancel₀ _ hn.ne] using D.scale_mem p hp (x / p.1) ht
  · have hx0 : x = 0 := by simpa only [hz, uIcc_self, mem_singleton_iff] using hx
    have hp' : (p.1, p.2) ∈ D.carrier := hp
    simpa only [hx0, hz] using hp'
  · rw [uIcc_of_le hp'.le] at hx
    have ht : x / p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx.1 hp'.le, (div_le_one hp').2 hx.2⟩
    simpa only [div_mul_cancel₀ _ hp'.ne'] using D.scale_mem p hp (x / p.1) ht

theorem radial_slice_continuous (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) (η : ℝ) :
    ContinuousOn (fun x => F (x, η)) {x | (x, η) ∈ D.carrier} :=
  hF.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _ hx => hx)

theorem radial_slice_intervalIntegrable (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    IntervalIntegrable (fun x => F (x, p.2)) volume 0 p.1 :=
  ((radial_slice_continuous D hF p.2).mono (fun _ hx => D.segment_mem hp hx)).intervalIntegrable

/-- The history has its defining integrand as genuine radial derivative. -/
theorem primitive_hasDerivAt (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun x => primitive F (x, p.2)) (F p) p.1 := by
  have hs : IsOpen {x | (x, p.2) ∈ D.carrier} :=
    D.isOpen.preimage (continuous_id.prodMk continuous_const)
  have hc := radial_slice_continuous D hF p.2
  simpa only [primitive, Prod.eta] using intervalIntegral.integral_hasDerivAt_right
    (radial_slice_intervalIntegrable D hF hp)
    (hc.stronglyMeasurableAtFilter hs p.1 hp)
    (hc.continuousAt (hs.mem_nhds hp))

theorem radialPartial_primitive (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    radialPartial (primitive F) p = F p :=
  (radialPartial_hasDerivAt D (primitive_smooth D hF) hp).unique (primitive_hasDerivAt D hF hp)

theorem compact_parameter_integral_parameterPartial {s : Set Point} {G : Point → ℝ → ℝ}
    (hs : IsOpen s)
    (hG : ∀ p ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ (fun z : Point × ℝ => G z.1 z.2) (p, t))
    {p : Point} (hp : p ∈ s) :
    parameterPartial (fun q => ∫ t in (0 : ℝ)..1, G q t) p =
      ∫ t in (0 : ℝ)..1, parameterPartial (fun q => G q t) p := by
  have hi : IntervalIntegrable (fun t => fderiv ℝ (fun q => G q t) p) volume 0 1 :=
    ((compact_parameter_fderiv_continuous hG).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hp,
          ht⟩)).intervalIntegrable_of_Icc zero_le_one
  unfold parameterPartial
  rw [(compact_parameter_integral_hasFDerivAt hs hG hp).fderiv]
  exact ContinuousLinearMap.intervalIntegral_apply hi (0, 1)

/-- Parameter differentiation commutes with the regular average, including at X=0. -/
theorem parameterPartial_average (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial (average F) p = average (parameterPartial F) p := by
  change parameterPartial (fun q => ∫ t in (0 : ℝ)..1, F (t * q.1, q.2)) p = _
  rw [compact_parameter_integral_parameterPartial D.isOpen
    (average_integrand_smooth D hF) hp]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hg : DifferentiableAt ℝ (fun q : Point => F (t * q.1, q.2)) p :=
    (((average_integrand_smooth D hF p hp t ht).comp p
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
  have hd : HasDerivAt (fun η => F (t * p.1, η))
      (parameterPartial (fun q : Point => F (t * q.1, q.2)) p) p.2 := by
    simpa only [parameterPartial, Function.comp_def, id_eq, Prod.eta] using
      hg.hasFDerivAt.comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  exact hd.unique (parameterPartial_hasDerivAt D hF (D.scale_mem p hp t ht))

/-- The parameter derivative of a history is the actual history of the
parameter derivative; no history derivative is assumed. -/
theorem parameterPartial_primitive (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial (primitive F) p = primitive (parameterPartial F) p := by
  have hd := (parameterPartial_hasDerivAt D (average_smooth D hF) hp).const_mul p.1
  rw [parameterPartial_average D hF hp] at hd
  have hd' : HasDerivAt (fun η => primitive F (p.1, η))
      (primitive (parameterPartial F) p) p.2 := by
    simpa only [primitive_eq_mul_average] using hd
  exact (parameterPartial_hasDerivAt D (primitive_smooth D hF) hp).unique hd'

/-- Mixed radial/parameter differentiation of an actual history. -/
theorem parameterPartial_primitive_hasDerivAt (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun x => parameterPartial (primitive F) (x, p.2))
      (parameterPartial F p) p.1 := by
  apply (primitive_hasDerivAt D (parameterPartial_smooth D hF) hp).congr_of_eventuallyEq
  have hn : ∀ᶠ x in 𝓝 p.1, (x, p.2) ∈ D.carrier :=
    (continuous_id.prodMk continuous_const).continuousAt (D.isOpen.mem_nhds hp)
  filter_upwards [hn] with x hx
  exact parameterPartial_primitive D hF hx

theorem parameterPartial_primitive_at_axis (D : RadialDomain) {F : Field}
    (hF : ContDiffOn ℝ ∞ F D.carrier) {η : ℝ} (hη : (0, η) ∈ D.carrier) :
    parameterPartial (primitive F) (0, η) = 0 := by
  rw [parameterPartial_primitive D hF hη, primitive_at_axis]

theorem average_eq_quotient (F : Field) {p : Point} (hX : p.1 ≠ 0) :
    average F p = primitive F p / p.1 := by
  rw [primitive_eq_mul_average, mul_div_cancel_left₀ _ hX]

/-- Smooth profiles and an arbitrary smooth axial pressure normalization.
Only local smoothness at the relevant parameter values is required. -/
structure Profiles (D : RadialDomain) where
  /-- F of `Profiles`, of type `Field`. -/
  f : Field
  /-- U of `Profiles`, of type `Field`. -/
  U : Field
  f_smooth : ContDiffOn ℝ ∞ f D.carrier
  U_smooth : ContDiffOn ℝ ∞ U D.carrier
  /-- Pressure0 of `Profiles`, of type `ℝ → ℝ`. -/
  pressure0 : ℝ → ℝ
  pressure0_smooth : ∀ p ∈ D.carrier, ContDiffAt ℝ ∞ pressure0 p.2

namespace Profiles

open StressAlgebra

variable {D : RadialDomain} (P : Profiles D)

/-- H, defined pointwise by `2 * p.1 * P.f p`. -/
def H : Field := fun p => 2 * p.1 * P.f p
/-- E, defined pointwise by `Real.sqrt (2 * p.1) * P.f p`. -/
def E : Field := fun p => Real.sqrt (2 * p.1) * P.f p
/-- Eη, defined pointwise by `Real.sqrt (2 * p.1) * parameterPartial P.f p`. -/
def Eη : Field := fun p => Real.sqrt (2 * p.1) * parameterPartial P.f p
/-- Transport density, defined pointwise by `P.U p * P.H p`. -/
def transportDensity : Field := fun p => P.U p * P.H p
/-- Energy density, defined pointwise by `P.U p ^ 2 - p.1 * P.f p ^ 2`. -/
def energyDensity : Field := fun p => P.U p ^ 2 - p.1 * P.f p ^ 2
/-- M, given by `primitive P.U`. -/
def M : Field := primitive P.U
/-- I, given by `primitive P.H`. -/
def I : Field := primitive P.H
/-- J, given by `primitive P.transportDensity`. -/
def J : Field := primitive P.transportDensity
/-- S, given by `primitive P.energyDensity`. -/
def S : Field := primitive P.energyDensity
/-- Ubar, given by `average P.U`. -/
def Ubar : Field := average P.U
/-- Pressure, defined pointwise by `P.pressure0 p.2 + primitive (fun q => P.f q ^ 2) p`. -/
def pressure : Field := fun p => P.pressure0 p.2 + primitive (fun q => P.f q ^ 2) p
/-- W, defined pointwise by `1 - 2 * axialExponent h * p.2 * P.Ubar p - coordinateFactor p.2 *
average (parameterPartial P.U) p`. -/
def W (h : ℝ) : Field := fun p =>
  1 - 2 * axialExponent h * p.2 * P.Ubar p -
    coordinateFactor p.2 * average (parameterPartial P.U) p

theorem H_smooth : ContDiffOn ℝ ∞ P.H D.carrier :=
  (contDiffOn_const.mul contDiffOn_fst).mul P.f_smooth

theorem transportDensity_smooth : ContDiffOn ℝ ∞ P.transportDensity D.carrier :=
  P.U_smooth.mul P.H_smooth

theorem energyDensity_smooth : ContDiffOn ℝ ∞ P.energyDensity D.carrier :=
  (P.U_smooth.pow 2).sub (contDiffOn_fst.mul (P.f_smooth.pow 2))

theorem M_smooth : ContDiffOn ℝ ∞ P.M D.carrier := primitive_smooth D P.U_smooth
theorem I_smooth : ContDiffOn ℝ ∞ P.I D.carrier := primitive_smooth D P.H_smooth
theorem J_smooth : ContDiffOn ℝ ∞ P.J D.carrier := primitive_smooth D P.transportDensity_smooth
theorem S_smooth : ContDiffOn ℝ ∞ P.S D.carrier := primitive_smooth D P.energyDensity_smooth
theorem Ubar_smooth : ContDiffOn ℝ ∞ P.Ubar D.carrier := average_smooth D P.U_smooth

theorem pressure_smooth : ContDiffOn ℝ ∞ P.pressure D.carrier := by
  apply ContDiffOn.add _ (primitive_smooth D (P.f_smooth.pow 2))
  intro p hp
  exact ((P.pressure0_smooth p hp).comp p contDiffAt_snd).contDiffWithinAt

theorem W_smooth (h : ℝ) : ContDiffOn ℝ ∞ (P.W h) D.carrier := by
  apply ContDiffOn.sub
  · exact contDiffOn_const.sub
      (((contDiffOn_const.mul contDiffOn_const).mul contDiffOn_snd).mul P.Ubar_smooth)
  · exact (contDiffOn_const.sub (contDiffOn_snd.pow 2)).mul
      (average_smooth D (parameterPartial_smooth D P.U_smooth))

theorem Ubar_at_axis (η : ℝ) : P.Ubar (0, η) = P.U (0, η) := average_at_axis P.U η

theorem Ubar_eq_mass_quotient {p : Point} (hX : p.1 ≠ 0) :
    P.Ubar p = P.M p / p.1 := average_eq_quotient P.U hX

theorem W_formula (h : ℝ) {p : Point} (hp : p ∈ D.carrier) :
    P.W h p = 1 - 2 * axialExponent h * p.2 * P.Ubar p -
      coordinateFactor p.2 * parameterPartial P.Ubar p := by
  rw [show parameterPartial P.Ubar p = average (parameterPartial P.U) p from
    parameterPartial_average D P.U_smooth hp]
  rfl

theorem XW_eq_histories (h : ℝ) (p : Point) :
    p.1 * P.W h p = p.1 - 2 * axialExponent h * p.2 * P.M p -
      coordinateFactor p.2 * primitive (parameterPartial P.U) p := by
  simp only [W, M, Ubar, primitive_eq_mul_average]
  ring

/-- The key identity used in both integrations by parts is derived from FTC. -/
theorem XW_hasDerivAt (h : ℝ) {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun x => x * P.W h (x, p.2))
      (1 - 2 * axialExponent h * p.2 * P.U p -
        coordinateFactor p.2 * parameterPartial P.U p) p.1 := by
  have hd := ((hasDerivAt_id p.1).sub
    ((primitive_hasDerivAt D P.U_smooth hp).const_mul (2 * axialExponent h * p.2))).sub
      ((primitive_hasDerivAt D (parameterPartial_smooth D P.U_smooth) hp).const_mul
        (coordinateFactor p.2))
  convert! hd using 1
  funext x
  exact P.XW_eq_histories h (x, p.2)

theorem W_balance (h : ℝ) {p : Point} (hp : p ∈ D.carrier) :
    P.W h p + p.1 * radialPartial (P.W h) p =
      1 - 2 * axialExponent h * p.2 * P.U p -
        coordinateFactor p.2 * parameterPartial P.U p := by
  have hd := (hasDerivAt_id p.1).fun_mul (radialPartial_hasDerivAt D (P.W_smooth h) hp)
  simpa only [id_eq, Prod.eta, one_mul] using hd.unique (P.XW_hasDerivAt h hp)

theorem parameterPartial_H {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial P.H p = 2 * p.1 * parameterPartial P.f p := by
  have hd := (parameterPartial_hasDerivAt D P.f_smooth hp).const_mul (2 * p.1)
  exact (parameterPartial_hasDerivAt D P.H_smooth hp).unique hd

theorem parameterPartial_transportDensity {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial P.transportDensity p =
      parameterPartial P.U p * P.H p + P.U p * parameterPartial P.H p :=
  (parameterPartial_hasDerivAt D P.transportDensity_smooth hp).unique
    ((parameterPartial_hasDerivAt D P.U_smooth hp).mul
      (parameterPartial_hasDerivAt D P.H_smooth hp))

theorem parameterPartial_energyDensity {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial P.energyDensity p = 2 * P.U p * parameterPartial P.U p -
      2 * p.1 * P.f p * parameterPartial P.f p := by
  have hd := ((parameterPartial_hasDerivAt D P.U_smooth hp).pow 2).sub
    (((parameterPartial_hasDerivAt D P.f_smooth hp).fun_pow 2).const_mul p.1)
  have heq := (parameterPartial_hasDerivAt D P.energyDensity_smooth hp).unique hd
  simpa only [Nat.cast_ofNat, pow_one, Nat.reduceSub] using heq.trans (by ring)

theorem E_sq {p : Point} (hX : 0 ≤ p.1) : P.E p ^ 2 / 2 = p.1 * P.f p ^ 2 := by
  have hs : (Real.sqrt (2 * p.1)) ^ 2 = 2 * p.1 := Real.sq_sqrt (by positivity)
  simp only [E, mul_pow, hs]
  ring

theorem E_mul_Eη {p : Point} (hX : 0 ≤ p.1) :
    P.E p * P.Eη p = 2 * p.1 * P.f p * parameterPartial P.f p := by
  have hs : (Real.sqrt (2 * p.1)) ^ 2 = 2 * p.1 := Real.sq_sqrt (by positivity)
  dsimp [E, Eη]
  calc
    _ = Real.sqrt (2 * p.1) ^ 2 * P.f p * parameterPartial P.f p := by ring
    _ = _ := by rw [hs]

theorem Eη_hasDerivAt {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun η => P.E (p.1, η)) (P.Eη p) p.2 :=
  (parameterPartial_hasDerivAt D P.f_smooth hp).const_mul (Real.sqrt (2 * p.1))

theorem pressure_hasDerivAt {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun x => P.pressure (x, p.2)) (P.f p ^ 2) p.1 := by
  unfold pressure
  simpa only [zero_add] using
    (hasDerivAt_const p.1 (P.pressure0 p.2)).fun_add
      (primitive_hasDerivAt D (P.f_smooth.pow 2) hp)

theorem radialPartial_pressure {p : Point} (hp : p ∈ D.carrier) :
    radialPartial P.pressure p = P.f p ^ 2 :=
  (radialPartial_hasDerivAt D P.pressure_smooth hp).unique (P.pressure_hasDerivAt hp)

theorem parameterPartial_pressure {p : Point} (hp : p ∈ D.carrier) :
    parameterPartial P.pressure p = deriv P.pressure0 p.2 +
      parameterPartial (primitive (fun q => P.f q ^ 2)) p := by
  exact (parameterPartial_hasDerivAt D P.pressure_smooth hp).unique
    (((P.pressure0_smooth p hp).differentiableAt (by simp)).hasDerivAt.add
      (parameterPartial_hasDerivAt D (primitive_smooth D (P.f_smooth.pow 2)) hp))

theorem parameterPartial_pressure_hasDerivAt {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun x => parameterPartial P.pressure (x, p.2))
      (2 * P.f p * parameterPartial P.f p) p.1 := by
  have hd := (hasDerivAt_const p.1 (deriv P.pressure0 p.2)).add
    (parameterPartial_primitive_hasDerivAt D (P.f_smooth.pow 2) hp)
  have hder : parameterPartial (fun q => P.f q ^ 2) p =
      2 * P.f p * parameterPartial P.f p := by
    exact (parameterPartial_hasDerivAt D (P.f_smooth.pow 2) hp).unique
      (by simpa only [Nat.cast_ofNat, pow_one, Nat.reduceSub] using
        (parameterPartial_hasDerivAt D P.f_smooth hp).fun_pow 2)
  rw [hder, zero_add] at hd
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ x in 𝓝 p.1, (x, p.2) ∈ D.carrier :=
    (continuous_id.prodMk continuous_const).continuousAt (D.isOpen.mem_nhds hp)
  filter_upwards [hn] with x hx
  exact P.parameterPartial_pressure hx

theorem axis_mem {p : Point} (hp : p ∈ D.carrier) : (0, p.2) ∈ D.carrier := by
  simpa only [zero_mul] using D.scale_mem p hp 0 ⟨le_rfl, zero_le_one⟩

/-- Every field and every derivative in the angular stress data is obtained
from the actual profiles and the actual integral histories. -/
noncomputable def angularData (h : ℝ) (p : Point) (hp : p ∈ D.carrier) :
    AngularMomentData h p.2 p.1 where
  W := fun x => P.W h (x, p.2)
  Wx := fun x => radialPartial (P.W h) (x, p.2)
  H := fun x => P.H (x, p.2)
  Hx := fun x => radialPartial P.H (x, p.2)
  Hη := fun x => parameterPartial P.H (x, p.2)
  U := fun x => P.U (x, p.2)
  Uη := fun x => parameterPartial P.U (x, p.2)
  I := fun x => P.I (x, p.2)
  Iη := fun x => parameterPartial P.I (x, p.2)
  J := fun x => P.J (x, p.2)
  Jη := fun x => parameterPartial P.J (x, p.2)
  W_deriv := fun _ hx => radialPartial_hasDerivAt D (P.W_smooth h) (D.segment_mem hp hx)
  H_deriv := fun _ hx => radialPartial_hasDerivAt D P.H_smooth (D.segment_mem hp hx)
  I_deriv := fun _ hx => primitive_hasDerivAt D P.H_smooth (D.segment_mem hp hx)
  Iη_deriv := fun _ hx => parameterPartial_primitive_hasDerivAt D P.H_smooth (D.segment_mem hp hx)
  J_deriv := fun _ hx => primitive_hasDerivAt D P.transportDensity_smooth (D.segment_mem hp hx)
  Jη_deriv := by
    intro x hx
    apply (parameterPartial_primitive_hasDerivAt D P.transportDensity_smooth
      (D.segment_mem hp hx)).congr_deriv
    exact P.parameterPartial_transportDensity (D.segment_mem hp hx)
  W_balance := fun _ hx => P.W_balance h (D.segment_mem hp hx)
  I_zero := primitive_at_axis P.H p.2
  Iη_zero := parameterPartial_primitive_at_axis D P.H_smooth (axis_mem hp)
  J_zero := primitive_at_axis P.transportDensity p.2
  Jη_zero := parameterPartial_primitive_at_axis D P.transportDensity_smooth (axis_mem hp)

/-- The axial data also use the pressure constructed by integrating f². -/
noncomputable def axialData (h : ℝ) (p : Point) (hp : p ∈ D.carrier) (hX : 0 ≤ p.1) :
    AxialMomentData h p.2 p.1 where
  W := fun x => P.W h (x, p.2)
  Wx := fun x => radialPartial (P.W h) (x, p.2)
  U := fun x => P.U (x, p.2)
  Ux := fun x => radialPartial P.U (x, p.2)
  Uη := fun x => parameterPartial P.U (x, p.2)
  E := fun x => P.E (x, p.2)
  Eη := fun x => P.Eη (x, p.2)
  P := fun x => P.pressure (x, p.2)
  Px := fun x => P.f (x, p.2) ^ 2
  Pη := fun x => parameterPartial P.pressure (x, p.2)
  Pηx := fun x => 2 * P.f (x, p.2) * parameterPartial P.f (x, p.2)
  M := fun x => P.M (x, p.2)
  Mη := fun x => parameterPartial P.M (x, p.2)
  S := fun x => P.S (x, p.2)
  Sη := fun x => parameterPartial P.S (x, p.2)
  W_deriv := fun _ hx => radialPartial_hasDerivAt D (P.W_smooth h) (D.segment_mem hp hx)
  U_deriv := fun _ hx => radialPartial_hasDerivAt D P.U_smooth (D.segment_mem hp hx)
  M_deriv := fun _ hx => primitive_hasDerivAt D P.U_smooth (D.segment_mem hp hx)
  Mη_deriv := fun _ hx => parameterPartial_primitive_hasDerivAt D P.U_smooth (D.segment_mem hp hx)
  S_deriv := by
    intro x hx
    have hx0 : 0 ≤ x := (show x ∈ Icc 0 p.1 by simpa only [uIcc_of_le hX] using hx).1
    apply (primitive_hasDerivAt D P.energyDensity_smooth (D.segment_mem hp hx)).congr_deriv
    rw [P.E_sq hx0]
    rfl
  Sη_deriv := by
    intro x hx
    have hx0 : 0 ≤ x := (show x ∈ Icc 0 p.1 by simpa only [uIcc_of_le hX] using hx).1
    apply (parameterPartial_primitive_hasDerivAt D P.energyDensity_smooth
      (D.segment_mem hp hx)).congr_deriv
    rw [P.parameterPartial_energyDensity (D.segment_mem hp hx), P.E_mul_Eη hx0]
  P_deriv := fun _ hx => P.pressure_hasDerivAt (D.segment_mem hp hx)
  Pη_deriv := fun _ hx => P.parameterPartial_pressure_hasDerivAt (D.segment_mem hp hx)
  W_balance := fun _ hx => P.W_balance h (D.segment_mem hp hx)
  pressure_balance := by
    intro x hx
    have hx0 : 0 ≤ x := (show x ∈ Icc 0 p.1 by simpa only [uIcc_of_le hX] using hx).1
    exact (P.E_sq (p := (x, p.2)) hx0).symm
  pressure_η_balance := by
    intro x hx
    have hx0 : 0 ≤ x := (show x ∈ Icc 0 p.1 by simpa only [uIcc_of_le hX] using hx).1
    rw [P.E_mul_Eη hx0]
    ring
  M_zero := primitive_at_axis P.U p.2
  Mη_zero := parameterPartial_primitive_at_axis D P.U_smooth (axis_mem hp)
  S_zero := primitive_at_axis P.energyDensity p.2
  Sη_zero := parameterPartial_primitive_at_axis D P.energyDensity_smooth (axis_mem hp)

/-- Angular source, defined pointwise by `StressAlgebra.angularSource h p.2 p.1 (P.W h p) (P.U
p) (P.H p) (radialPartial P.H p) (parameterPartial P.H p)`. -/
def angularSource (h : ℝ) : Field := fun p =>
  StressAlgebra.angularSource h p.2 p.1 (P.W h p) (P.U p) (P.H p)
    (radialPartial P.H p) (parameterPartial P.H p)

/-- Axial source as an element of `Field`. -/
def axialSource (h : ℝ) : Field := fun p =>
  StressAlgebra.axialSource h p.2 p.1 (P.W h p) (P.U p)
    (radialPartial P.U p) (parameterPartial P.U p) (P.pressure p)
      (P.f p ^ 2) (parameterPartial P.pressure p)

theorem angularSource_smooth (h : ℝ) : ContDiffOn ℝ ∞ (P.angularSource h) D.carrier := by
  exact ((((P.W_smooth h).neg.mul contDiffOn_fst).mul (radialPartial_smooth D P.H_smooth)).sub
    ((contDiffOn_const.mul (contDiffOn_const.sub
      ((contDiffOn_const.mul contDiffOn_snd).mul P.U_smooth))).mul P.H_smooth)).sub
    (((contDiffOn_const.mul contDiffOn_snd).add
      ((contDiffOn_const.sub (contDiffOn_snd.pow 2)).mul P.U_smooth)).mul
        (parameterPartial_smooth D P.H_smooth))

theorem axialSource_smooth (h : ℝ) : ContDiffOn ℝ ∞ (P.axialSource h) D.carrier := by
  exact (((((((P.W_smooth h).neg.mul contDiffOn_fst).mul
    (radialPartial_smooth D P.U_smooth)).sub
      ((contDiffOn_const.mul (contDiffOn_const.sub
        ((contDiffOn_const.mul contDiffOn_snd).mul P.U_smooth))).mul P.U_smooth)).sub
      (((contDiffOn_const.mul contDiffOn_snd).add
        ((contDiffOn_const.sub (contDiffOn_snd.pow 2)).mul P.U_smooth)).mul
          (parameterPartial_smooth D P.U_smooth))).sub
      ((contDiffOn_const.sub (contDiffOn_snd.pow 2)).mul
        (parameterPartial_smooth D P.pressure_smooth))).add
      (((contDiffOn_const.mul contDiffOn_const).mul contDiffOn_snd).mul P.pressure_smooth)).add
      (((contDiffOn_const.mul contDiffOn_snd).mul contDiffOn_fst).mul (P.f_smooth.pow 2))

/-- The printed Q_s is the regular primitive divided by its integrating factor. -/
def angularLag (h : ℝ) : Field := fun p => primitive (P.angularSource h) p / (p.1 * P.H p)

/-- The printed N_s is the regular primitive divided by X. -/
def axialLag (h : ℝ) : Field := fun p => primitive (P.axialSource h) p / p.1

/-- Equation (9), angular row, for actual smooth profile histories. -/
theorem angularLag_integrated (h : ℝ) {p : Point} (hp : p ∈ D.carrier)
    (hX : p.1 ≠ 0) (hH : P.H p ≠ 0) :
    P.angularLag h p = -P.W h p +
      ((1 - h) * P.I p - axialExponent h * p.2 * parameterPartial P.I p -
        coordinateFactor p.2 * parameterPartial P.J p +
          2 * (h - axialExponent h) * p.2 * P.J p) / (p.1 * P.H p) := by
  exact angular_integrated_lag (P.angularData h p hp) hX hH
    (radial_slice_intervalIntegrable D (P.angularSource_smooth h) hp)

/-- Equation (9), axial row, with constructed pressure and actual histories. -/
theorem axialLag_integrated (h : ℝ) {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1) :
    P.axialLag h p = -P.W h p * P.U p +
      axialExponent h * (P.M p - p.2 * parameterPartial P.M p) / p.1 +
        (4 * h * p.2 * P.S p - coordinateFactor p.2 * parameterPartial P.S p) / p.1 +
          4 * velocityExponent h * p.2 * P.pressure p - coordinateFactor p.2 * parameterPartial
              P.pressure p := by
  exact axial_integrated_lag (P.axialData h p hp hX.le) hX.ne'
    (radial_slice_intervalIntegrable D (P.axialSource_smooth h) hp)

theorem angularLag_smoothAt (h : ℝ) {p : Point} (hp : p ∈ D.carrier)
    (hX : p.1 ≠ 0) (hH : P.H p ≠ 0) : ContDiffAt ℝ ∞ (P.angularLag h) p :=
  ((primitive_smooth D (P.angularSource_smooth h)).contDiffAt (D.isOpen.mem_nhds hp)).div
    (contDiffAt_fst.mul (P.H_smooth.contDiffAt (D.isOpen.mem_nhds hp))) (mul_ne_zero hX hH)

theorem axialLag_smoothAt (h : ℝ) {p : Point} (hp : p ∈ D.carrier)
    (hX : p.1 ≠ 0) : ContDiffAt ℝ ∞ (P.axialLag h) p :=
  ((primitive_smooth D (P.axialSource_smooth h)).contDiffAt (D.isOpen.mem_nhds hp)).div
    contDiffAt_fst hX

theorem angularLag_hasDerivAt (h : ℝ) {p : Point} (hp : p ∈ D.carrier)
    (hX : p.1 ≠ 0) (hH : P.H p ≠ 0) :
    HasDerivAt (fun x => P.angularLag h (x, p.2))
      ((P.angularSource h p * (p.1 * P.H p) -
        primitive (P.angularSource h) p * (P.H p + p.1 * radialPartial P.H p)) /
          (p.1 * P.H p) ^ 2) p.1 := by
  unfold angularLag
  simpa only [id_eq, Prod.eta, one_mul] using
    (primitive_hasDerivAt D (P.angularSource_smooth h) hp).fun_div
      ((hasDerivAt_id p.1).fun_mul (radialPartial_hasDerivAt D P.H_smooth hp))
        (mul_ne_zero hX hH)

theorem axialLag_hasDerivAt (h : ℝ) {p : Point} (hp : p ∈ D.carrier) (hX : p.1 ≠ 0) :
    HasDerivAt (fun x => P.axialLag h (x, p.2))
      ((P.axialSource h p * p.1 - primitive (P.axialSource h) p) / p.1 ^ 2) p.1 := by
  unfold axialLag
  simpa only [id_eq, Prod.eta, mul_one] using
    (primitive_hasDerivAt D (P.axialSource_smooth h) hp).fun_div (hasDerivAt_id p.1) hX

/-- The angular differential equation (6), with logarithmic slopes as ratios
of genuine derivatives. -/
theorem angularLag_equation (h : ℝ) {p : Point} (hp : p ∈ D.carrier)
    (hX : p.1 ≠ 0) (hH : P.H p ≠ 0) :
    p.1 * deriv (fun x => P.angularLag h (x, p.2)) p.1 +
      (1 + p.1 * radialPartial P.H p / P.H p) * P.angularLag h p =
        P.angularSource h p / P.H p := by
  rw [(P.angularLag_hasDerivAt h hp hX hH).deriv]
  unfold angularLag
  field_simp; ring

/-- The axial differential equation (6), with the actual primitive-defined N_s. -/
theorem axialLag_equation (h : ℝ) {p : Point} (hp : p ∈ D.carrier) (hX : p.1 ≠ 0) :
    p.1 * deriv (fun x => P.axialLag h (x, p.2)) p.1 + P.axialLag h p =
      P.axialSource h p := by
  rw [(P.axialLag_hasDerivAt h hp hX).deriv]
  unfold axialLag
  field_simp; ring

theorem H_ne_zero {p : Point} (hX : p.1 ≠ 0) (hf : P.f p ≠ 0) : P.H p ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) hX) hf

theorem E_ne_zero {p : Point} (hX : 0 < p.1) (hf : P.f p ≠ 0) : P.E p ≠ 0 :=
  mul_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by positivity))) hf

theorem logH_radial_deriv {p : Point} (hp : p ∈ D.carrier) (hH : P.H p ≠ 0) :
    deriv (fun x => Real.log (P.H (x, p.2))) p.1 = radialPartial P.H p / P.H p :=
  ((radialPartial_hasDerivAt D P.H_smooth hp).log hH).deriv

theorem logE_parameter_deriv {p : Point} (hp : p ∈ D.carrier)
    (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    deriv (fun η => Real.log (P.E (p.1, η))) p.2 = parameterPartial P.H p / P.H p := by
  rw [((P.Eη_hasDerivAt hp).log (P.E_ne_zero hX hf)).deriv, P.parameterPartial_H hp]
  have hs : Real.sqrt (2 * p.1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  dsimp [Eη, E, H]
  field_simp

/-- The angular row of (6) with actual logarithms, not surrogate slope data. -/
theorem angularLag_equation_logarithmic (h : ℝ) {p : Point} (hp : p ∈ D.carrier)
    (hX : 0 < p.1) (hf : P.f p ≠ 0) :
    p.1 * deriv (fun x => P.angularLag h (x, p.2)) p.1 +
      (1 + p.1 * deriv (fun x => Real.log (P.H (x, p.2))) p.1) * P.angularLag h p =
        -P.W h p * (p.1 * deriv (fun x => Real.log (P.H (x, p.2))) p.1) -
          h * (1 - 2 * p.2 * P.U p) -
            (axialExponent h * p.2 + coordinateFactor p.2 * P.U p) *
              deriv (fun η => Real.log (P.E (p.1, η))) p.2 := by
  have hH := P.H_ne_zero hX.ne' hf
  rw [P.logH_radial_deriv hp hH, P.logE_parameter_deriv hp hX hf]
  rw [← mul_div_assoc]
  rw [P.angularLag_equation h hp hX.ne' hH]
  dsimp [angularSource, StressAlgebra.angularSource]
  field_simp

/-- The axial row of (6), with the pressure derivative proved from its integral. -/
theorem axialLag_equation_explicit (h : ℝ) {p : Point} (hp : p ∈ D.carrier) (hX : 0 < p.1) :
    p.1 * deriv (fun x => P.axialLag h (x, p.2)) p.1 + P.axialLag h p =
      -P.W h p * (p.1 * radialPartial P.U p) -
        velocityExponent h * (1 - 2 * p.2 * P.U p) * P.U p -
          (axialExponent h * p.2 + coordinateFactor p.2 * P.U p) * parameterPartial P.U p -
            coordinateFactor p.2 * parameterPartial P.pressure p +
              4 * velocityExponent h * p.2 * P.pressure p +
                2 * p.2 * (p.1 * radialPartial P.pressure p) := by
  rw [P.axialLag_equation h hp hX.ne', P.radialPartial_pressure hp]
  dsimp [axialSource, StressAlgebra.axialSource]
  ring

end Profiles

end NavierStokes.ProfileHistories

end
