/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ProfileHistories
public import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalProfile
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

/-!
# The same-radius reference continuation

The reference path integrates the natural slopes evaluated at the original
radius. A smooth cutoff damps those slopes to zero; no radial reparametrization
is substituted for the prescribed differential equation.
-/

noncomputable section

namespace NavierStokes.ReferencePath

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
open ProfileHistories

def fullStrip (J : Set ℝ) (hJ : IsOpen J) : RadialDomain where
  carrier := univ ×ˢ J
  isOpen := isOpen_univ.prod hJ
  scale_mem := fun _ hp _ _ => ⟨mem_univ _, hp.2⟩

def earlyStrip (T : ℝ) (hT : 0 < T) (J : Set ℝ) (hJ : IsOpen J) : RadialDomain where
  carrier := Iio T ×ˢ J
  isOpen := isOpen_Iio.prod hJ
  scale_mem := by
    intro p hp t ht
    refine ⟨?_, hp.2⟩
    rcases le_total p.1 0 with hx | hx
    · exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos ht.1 hx) hT
    · exact lt_of_le_of_lt (mul_le_of_le_one_left hx ht.2) hp.1

/-- One until t=δ, smooth transition on (δ,2δ), and zero from 2δ onward. -/
def slopeCutoff (δ t : ℝ) : ℝ := 1 - Real.smoothTransition ((t - δ) / δ)

theorem slopeCutoff_smooth (δ : ℝ) : ContDiff ℝ ∞ (slopeCutoff δ) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const δ))

theorem slopeCutoff_mem (δ t : ℝ) : slopeCutoff δ t ∈ Icc (0 : ℝ) 1 := by
  have hlo := Real.smoothTransition.nonneg ((t - δ) / δ)
  have hhi := Real.smoothTransition.le_one ((t - δ) / δ)
  constructor <;> dsimp [slopeCutoff] <;> linarith

theorem slopeCutoff_one {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) : slopeCutoff δ t = 1 := by
  rw [slopeCutoff, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le), sub_zero]

theorem slopeCutoff_zero {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) : slopeCutoff δ t = 0 := by
  rw [slopeCutoff, Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ hδ).2 (by linarith)), sub_self]

def dampedSlope (δ : ℝ) (G : Field) : Field :=
  fun p => slopeCutoff δ p.1 * radialPartial G p

/-- The prescribed continuation, defined by an actual integral of the
same-time natural derivative. -/
def continuation (δ : ℝ) (G : Field) : Field :=
  fun p => G (0, p.2) + primitive (dampedSlope δ G) p

theorem dampedSlope_smooth {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier) :
    ContDiffOn ℝ ∞ (dampedSlope δ G) (fullStrip J hJ).carrier := by
  intro p hp
  by_cases ht : p.1 < T
  · have hs := (radialPartial_smooth (earlyStrip T hT J hJ) hG).contDiffAt
      ((earlyStrip T hT J hJ).isOpen.mem_nhds ⟨ht, hp.2⟩)
    exact (((slopeCutoff_smooth δ).contDiffAt.comp p contDiffAt_fst).mul hs).contDiffWithinAt
  · have hfar : 2 * δ < p.1 := hδT.trans_le (le_of_not_gt ht)
    have heq : dampedSlope δ G =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hfar)] with q hq
      simp only [dampedSlope, slopeCutoff_zero hδ hq.le, zero_mul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt

theorem continuation_smooth {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier) :
    ContDiffOn ℝ ∞ (continuation δ G) (fullStrip J hJ).carrier := by
  apply ContDiffOn.add _ (primitive_smooth (fullStrip J hJ) (dampedSlope_smooth hT hδ hδT hJ hG))
  intro p hp
  exact ((hG.contDiffAt ((earlyStrip T hT J hJ).isOpen.mem_nhds
    (show (0, p.2) ∈ (earlyStrip T hT J hJ).carrier from ⟨hT, hp.2⟩))).comp p
    (contDiffAt_const.prodMk contDiffAt_snd)).contDiffWithinAt

theorem continuation_hasDerivAt {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    {p : Point} (hp : p.2 ∈ J) :
    HasDerivAt (fun t => continuation δ G (t, p.2))
      (slopeCutoff δ p.1 * radialPartial G p) p.1 := by
  have hd := (hasDerivAt_const p.1 (G (0, p.2))).fun_add
    (primitive_hasDerivAt (fullStrip J hJ) (dampedSlope_smooth hT hδ hδT hJ hG) ⟨mem_univ _, hp⟩)
  simp only [zero_add] at hd
  exact hd

theorem continuation_eq_natural {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    {p : Point} (hp : p.2 ∈ J) (ht : p.1 ≤ δ) : continuation δ G p = G p := by
  have hd : ∀ t ∈ uIcc 0 p.1,
      HasDerivAt (fun t => G (t, p.2)) (dampedSlope δ G (t, p.2)) t := by
    intro t ht'
    have htδ : t ≤ δ := (mem_uIcc.mp ht').elim
      (fun h => h.2.trans ht) (fun h => h.2.trans hδ.le)
    have htT : t < T := htδ.trans_lt (by linarith)
    simpa only [dampedSlope, slopeCutoff_one hδ htδ, one_mul] using
      radialPartial_hasDerivAt (earlyStrip T hT J hJ) hG (p := (t, p.2)) ⟨htT, hp⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (radial_slice_intervalIntegrable (fullStrip J hJ)
      (dampedSlope_smooth hT hδ hδT hJ hG) (p := p) ⟨mem_univ _, hp⟩)
  change G (0, p.2) + _ = _
  rw [show primitive (dampedSlope δ G) p = G p - G (0, p.2) from hi]
  ring

theorem continuation_frozen {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    {p : Point} (hp : p.2 ∈ J) (ht : 2 * δ ≤ p.1) :
    continuation δ G p = continuation δ G (2 * δ, p.2) := by
  have hd : ∀ t ∈ uIcc (2 * δ) p.1,
      HasDerivAt (fun t => continuation δ G (t, p.2)) 0 t := by
    intro t ht'
    have hlow : 2 * δ ≤ t := (show t ∈ Icc (2 * δ) p.1 by simpa only [uIcc_of_le ht] using ht').1
    simpa only [slopeCutoff_zero hδ hlow, zero_mul] using
      continuation_hasDerivAt hT hδ hδT hJ hG (p := (t, p.2)) hp
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (2 * δ) p.1)
  have heq : (0 : ℝ) = continuation δ G p - continuation δ G (2 * δ, p.2) := by
    simpa only [intervalIntegral.integral_zero, Prod.eta] using hi
  linarith

section CompactSmoothIntegral

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {s : Set H} {F : H → ℝ → ℝ}

theorem compact_integral_smooth (hs : IsOpen s)
    (hF : ∀ p ∈ s, ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ ∞ (fun z : H × ℝ => F z.1 z.2) (p, t)) :
    ContDiffOn ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, F p t) s := by
  apply SmoothParameterIntegral.contDiffOn_intervalIntegral_of_continuous_jet hs zero_le_one
  · intro t ht p hp
    exact ((hF p hp t ht).comp p (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · intro k
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    have hflip : ContDiffAt ℝ ∞ (Function.uncurry (fun t p => F p t)) (t, p) :=
      (hF p hp t ht).comp (t, p) (contDiffAt_snd.prodMk contDiffAt_fst)
    have hd := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv (fun t p => F p t) k t p hflip
    exact ((hd.comp (p, t) (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt).continuousWithinAt

end CompactSmoothIntegral

abbrev MasterPoint := (ℝ × ℝ) × ℝ

def masterDomain (T : ℝ) (J : Set ℝ) : Set MasterPoint :=
  {p | |p.1.1 * p.1.2| < T ∧ p.2 ∈ J}

theorem masterDomain_open (T : ℝ) {J : Set ℝ} (hJ : IsOpen J) : IsOpen (masterDomain T J) :=
  (isOpen_lt ((continuous_fst.fst.mul continuous_fst.snd).abs) continuous_const).inter
    (hJ.preimage continuous_snd)

/-- The rescaled transition on a fixed parameter interval, smooth even at δ=0. -/
def master (G : Field) (p : MasterPoint) : ℝ :=
  G (0, p.2) + p.1.1 * p.1.2 *
    ∫ v in (0 : ℝ)..1, slopeCutoff 1 (p.1.2 * v) * radialPartial G (p.1.1 * (p.1.2 * v), p.2)

theorem master_at_zero (G : Field) (u η : ℝ) : master G ((0, u), η) = G (0, η) := by
  simp [master]

theorem slopeCutoff_scaled {δ : ℝ} (hδ : δ ≠ 0) (u : ℝ) :
    slopeCutoff δ (δ * u) = slopeCutoff 1 u := by
  unfold slopeCutoff
  congr 2
  field_simp

theorem continuation_rescaled (G : Field) {δ : ℝ} (hδ : δ ≠ 0) (u η : ℝ) :
    continuation δ G (δ * u, η) = master G ((δ, u), η) := by
  unfold continuation master
  rw [primitive_eq_mul_average]
  apply congrArg (fun x : ℝ => G (0, η) + δ * u * x)
  apply intervalIntegral.integral_congr
  intro v _
  change slopeCutoff δ (v * (δ * u)) * radialPartial G (v * (δ * u), η) = _
  rw [show v * (δ * u) = δ * (u * v) by ring, slopeCutoff_scaled hδ]

theorem master_smooth {T : ℝ} (hT : 0 < T) {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier) :
    ContDiffOn ℝ ∞ (master G) (masterDomain T J) := by
  apply ContDiffOn.add
  · intro p hp
    exact ((hG.contDiffAt ((earlyStrip T hT J hJ).isOpen.mem_nhds
      (show (0, p.2) ∈ (earlyStrip T hT J hJ).carrier from ⟨hT, hp.2⟩))).comp p
        (contDiffAt_const.prodMk contDiffAt_snd)).contDiffWithinAt
  · apply ContDiffOn.mul (contDiffOn_fst.fst.mul contDiffOn_fst.snd)
    apply compact_integral_smooth (masterDomain_open T hJ)
    intro p hp v hv
    have hbound : |p.1.1 * (p.1.2 * v)| ≤ |p.1.1 * p.1.2| := by
      rw [← mul_assoc, abs_mul, abs_of_nonneg hv.1]
      exact mul_le_of_le_one_right (abs_nonneg _) hv.2
    have hpv : (p.1.1 * (p.1.2 * v), p.2) ∈ (earlyStrip T hT J hJ).carrier :=
      ⟨(le_abs_self _).trans_lt (hbound.trans_lt hp.1), hp.2⟩
    have hd := (radialPartial_smooth (earlyStrip T hT J hJ) hG).contDiffAt
      ((earlyStrip T hT J hJ).isOpen.mem_nhds hpv)
    exact ((slopeCutoff_smooth 1).contDiffAt.comp (p, v)
      (contDiffAt_fst.fst.snd.mul contDiffAt_snd)).mul
        (hd.comp (p, v) ((contDiffAt_fst.fst.fst.mul
          (contDiffAt_fst.fst.snd.mul contDiffAt_snd)).prodMk contDiffAt_fst.snd))

/-- The master representation covers the entire hold by saturating its
rescaled time at two. This does not change the natural slope's evaluation point. -/
def holdTime (δ t : ℝ) : ℝ := min (t / δ) 2

theorem holdTime_mem {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) : holdTime δ t ∈ Icc (0 : ℝ) 2 := by
  exact ⟨le_min (div_nonneg ht hδ.le) (by norm_num), min_le_right _ _⟩

theorem continuation_eq_master_hold {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : 2 * δ < T)
    {J : Set ℝ} (hJ : IsOpen J) {G : Field}
    (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    {t η : ℝ} (hη : η ∈ J) (_ : 0 ≤ t) :
    continuation δ G (t, η) = master G ((δ, holdTime δ t), η) := by
  by_cases hsmall : t ≤ 2 * δ
  · have htdiv : t / δ ≤ 2 := (div_le_iff₀ hδ).2 (by nlinarith)
    rw [holdTime, min_eq_left htdiv, ← continuation_rescaled G hδ.ne']
    rw [mul_div_cancel₀ _ hδ.ne']
  · have hbig : 2 * δ ≤ t := (lt_of_not_ge hsmall).le
    have htdiv : 2 ≤ t / δ := (le_div_iff₀ hδ).2 (by nlinarith)
    rw [continuation_frozen hT hδ hδT hJ hG hη hbig,
      holdTime, min_eq_right htdiv, ← continuation_rescaled G hδ.ne']
    rw [mul_comm δ 2]

def parameterJet (k : ℕ) (F : MasterPoint → ℝ) (p : MasterPoint) : ℝ :=
  iteratedDeriv k (fun η => F (p.1, η)) p.2

theorem parameterJet_continuousAt {F : MasterPoint → ℝ} {p : MasterPoint}
    (hF : ContDiffAt ℝ ∞ F p) (k : ℕ) : ContinuousAt (parameterJet k F) p := by
  have hd := ParametricFlatFactor.contDiffAt_partial_iteratedFDeriv
    (fun a η => F (a, η)) k p.1 p.2 hF
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin k) ℝ).symm.continuous.continuousAt.comp
    hd.continuousAt

/-- Compactness supplies uniform control of every fixed genuine parameter jet
of a smooth master family at δ=0. -/
theorem master_parameter_jet_close {T : ℝ} (hT : 0 < T) {J : Set ℝ} (hJ : IsOpen J)
    {F : MasterPoint → ℝ} (hF : ContDiffOn ℝ ∞ F (masterDomain T J))
    (base : ℝ → ℝ) (hzero : ∀ u η, F ((0, u), η) = base η)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, |δ| < δ₀ → ∀ u ∈ Icc (0 : ℝ) 2, ∀ η ∈ K,
      |parameterJet k F ((δ, u), η) - iteratedDeriv k base η| < ε := by
  let a : ℝ := T / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let C : Set MasterPoint := (Icc (-a) a ×ˢ Icc (0 : ℝ) 2) ×ˢ K
  have hC : IsCompact C := (isCompact_Icc.prod isCompact_Icc).prod hK
  have hCD : C ⊆ masterDomain T J := by
    rintro ⟨⟨δ, u⟩, η⟩ ⟨⟨hδ, hu⟩, hη⟩
    refine ⟨?_, hKJ hη⟩
    have hδabs : |δ| ≤ a := abs_le.mpr hδ
    have huabs : |u| ≤ 2 := by rw [abs_of_nonneg hu.1]; exact hu.2
    have hprod := mul_le_mul hδabs huabs (abs_nonneg u) ha.le
    rw [abs_mul]
    exact hprod.trans_lt (by dsimp [a]; linarith)
  have hc : ContinuousOn (parameterJet k F) C := by
    intro p hp
    exact (parameterJet_continuousAt (hF.contDiffAt ((masterDomain_open T hJ).mem_nhds (hCD hp)))
      k).continuousWithinAt
  obtain ⟨r, hr, hdist⟩ := (Metric.uniformContinuousOn_iff.mp
    (hC.uniformContinuousOn_of_continuous hc)) ε hε
  refine ⟨min a r, lt_min ha hr, ?_⟩
  intro δ hδ u hu η hη
  have hδa : |δ| < a := hδ.trans_le (min_le_left _ _)
  have hδr : |δ| < r := hδ.trans_le (min_le_right _ _)
  have hx : ((δ, u), η) ∈ C := ⟨⟨abs_le.mp hδa.le, hu⟩, hη⟩
  have hy : ((0, u), η) ∈ C := ⟨⟨⟨neg_nonpos.mpr ha.le, ha.le⟩, hu⟩, hη⟩
  have hdxy : dist (((δ, u), η) : MasterPoint) ((0, u), η) < r := by
    simpa only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, max_self,
      max_eq_left (abs_nonneg δ)] using hδr
  have hz : parameterJet k F ((0, u), η) = iteratedDeriv k base η := by
    unfold parameterJet
    congr 1
    funext x
    exact hzero u x
  simpa only [Real.dist_eq, hz] using hdist _ hx _ hy hdxy

def transformedMaster (Φ : ℝ × ℝ → ℝ) (G : Field) (p : MasterPoint) : ℝ :=
  Φ (master G p, G (0, p.2))

theorem transformedMaster_smooth {T : ℝ} (hT : 0 < T) {J : Set ℝ} (hJ : IsOpen J)
    {G : Field} (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiffOn ℝ ∞ (transformedMaster Φ G) (masterDomain T J) := by
  apply hΦ.comp_contDiffOn
  apply (master_smooth hT hJ hG).prodMk
  intro p hp
  exact ((hG.contDiffAt ((earlyStrip T hT J hJ).isOpen.mem_nhds
    (show (0, p.2) ∈ (earlyStrip T hT J hJ).carrier from ⟨hT, hp.2⟩))).comp p
      (contDiffAt_const.prodMk contDiffAt_snd)).contDiffWithinAt

/-- All fixed parameter jets of any smooth transformation of the path and its
endpoint converge uniformly on the whole nonnegative-time hold. Applying Φ
to x, exp x, x-b, or exp(x-b) gives field, log-field, and relative-field jets. -/
theorem continuation_parameter_jet_close {T : ℝ} (hT : 0 < T) {J : Set ℝ} (hJ : IsOpen J)
    {G : Field} (hG : ContDiffOn ℝ ∞ G (earlyStrip T hT J hJ).carrier)
    {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∀ t, 0 ≤ t → ∀ η ∈ K,
      |iteratedDeriv k (fun y => Φ (continuation δ G (t, y), G (0, y))) η -
        iteratedDeriv k (fun y => Φ (G (0, y), G (0, y))) η| < ε := by
  obtain ⟨r, hr, hc⟩ := master_parameter_jet_close hT hJ
    (transformedMaster_smooth hT hJ hG hΦ) (fun y => Φ (G (0, y), G (0, y)))
    (fun u η => by simp only [transformedMaster, master_at_zero]) hK hKJ k hε
  refine ⟨min r (T / 4), lt_min hr (by positivity), ?_⟩
  intro δ hδ hδ₀ t ht η hη
  have hδT : 2 * δ < T := by have := hδ₀.trans_le (min_le_right _ _); linarith
  have hδr : |δ| < r := by rw [abs_of_pos hδ]; exact hδ₀.trans_le (min_le_left _ _)
  have heq : (fun y => Φ (continuation δ G (t, y), G (0, y))) =ᶠ[𝓝 η]
      (fun y => transformedMaster Φ G ((δ, holdTime δ t), y)) := by
    filter_upwards [hJ.mem_nhds (hKJ hη)] with y hy
    rw [continuation_eq_master_hold hT hδ hδT hJ hG hy ht]
    rfl
  rw [heq.iteratedDeriv_eq k]
  exact hc δ hδr (holdTime δ t) (holdTime_mem hδ ht) η hη

def parameterInterval : Set ℝ :=
  Ioo NaturalAxisCoefficients.window.left NaturalAxisCoefficients.window.right

theorem parameterInterval_open : IsOpen parameterInterval := isOpen_Ioo

def rampLimit : ℝ := Real.log (41 / 40 : ℝ)

theorem rampLimit_pos : 0 < rampLimit := Real.log_pos (by norm_num)

theorem exists_small_length {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ 2 * δ < rampLimit ∧ δ < ε := by
  have hT := rampLimit_pos
  refine ⟨min (rampLimit / 4) (ε / 2), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · have := min_le_left (rampLimit / 4) (ε / 2)
    have := rampLimit_pos
    linarith
  · have := min_le_right (rampLimit / 4) (ε / 2)
    linarith

/-- Only the proved natural-profile regularity and positivity are used in
constructing REF. The natural ODE is not replaced by a surrogate assumption. -/
structure Input where
  scale : ℝ
  scale_pos : 0 < scale
  f : Field
  U : Field
  f_smooth : ContDiffOn ℝ ∞ f (NaturalProfile.domain scale)
  U_smooth : ContDiffOn ℝ ∞ U (NaturalProfile.domain scale)
  positive : ∀ p ∈ NaturalProfile.domain scale, 0 ≤ scale * p.1 →
    scale * p.1 ≤ 41 / 10 → 0 < f p

def Input.ofNatural {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalProfile.ProfileFamily d Λ C) : Input where
  scale := Λ
  scale_pos := hΛ
  f := F.f
  U := F.U
  f_smooth := F.natural.f_smooth
  U_smooth := F.natural.U_smooth
  positive := F.positive

namespace Input

variable (N : Input)

def endpoint : ℝ := 4 / N.scale

theorem endpoint_pos : 0 < N.endpoint := div_pos (by norm_num) N.scale_pos

theorem scale_endpoint : N.scale * N.endpoint = 4 := by
  dsimp [endpoint]
  field_simp [N.scale_pos.ne']

def fromLog (p : Point) : Point := (N.endpoint * Real.exp p.1, p.2)
def logTime (X : ℝ) : ℝ := Real.log (X / N.endpoint)
def logF : Field := fun p => Real.log (N.f (N.fromLog p))
def logU : Field := fun p => N.U (N.fromLog p)

theorem fromLog_smooth : ContDiff ℝ ∞ N.fromLog :=
  (contDiff_const.mul contDiff_fst.exp).prodMk contDiff_snd

theorem fromLog_scaled (p : Point) : N.scale * (N.fromLog p).1 = 4 * Real.exp p.1 := by
  dsimp [fromLog]
  rw [← mul_assoc, N.scale_endpoint]

theorem fromLog_mem {p : Point}
    (hp : p ∈ (earlyStrip rampLimit rampLimit_pos parameterInterval
      parameterInterval_open).carrier) :
    N.fromLog p ∈ NaturalProfile.domain N.scale := by
  change (-20 < N.scale * (N.fromLog p).1 ∧ N.scale * (N.fromLog p).1 < 20) ∧ p.2 ∈
    parameterInterval
  rw [N.fromLog_scaled]
  have hupper : Real.exp p.1 < 41 / 40 := by
    simpa only [rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)] using
      Real.exp_lt_exp.mpr hp.1
  refine ⟨⟨?_, ?_⟩, hp.2⟩ <;> nlinarith [Real.exp_pos p.1]

theorem fromLog_f_pos {p : Point}
    (hp : p ∈ (earlyStrip rampLimit rampLimit_pos parameterInterval
      parameterInterval_open).carrier) :
    0 < N.f (N.fromLog p) := by
  apply N.positive _ (N.fromLog_mem hp)
  · rw [N.fromLog_scaled]; positivity
  · rw [N.fromLog_scaled]
    have hupper : Real.exp p.1 < 41 / 40 := by
      simpa only [rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)] using
        Real.exp_lt_exp.mpr hp.1
    linarith

theorem logF_smooth : ContDiffOn ℝ ∞ N.logF
    (earlyStrip rampLimit rampLimit_pos parameterInterval parameterInterval_open).carrier := by
  intro p hp
  exact (((N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds
    (N.fromLog_mem hp))).comp p N.fromLog_smooth.contDiffAt).log (N.fromLog_f_pos
      hp).ne').contDiffWithinAt

theorem logU_smooth : ContDiffOn ℝ ∞ N.logU
    (earlyStrip rampLimit rampLimit_pos parameterInterval parameterInterval_open).carrier :=
  N.U_smooth.comp N.fromLog_smooth.contDiffOn (fun _ hp => N.fromLog_mem hp)

theorem fromLog_logTime {X η : ℝ} (hX : 0 < X) :
    N.fromLog (N.logTime X, η) = (X, η) := by
  ext
  · dsimp [fromLog, logTime]
    rw [Real.exp_log (div_pos hX N.endpoint_pos)]
    field_simp [N.endpoint_pos.ne']
  · rfl

theorem logTime_fromLog (t : ℝ) : N.logTime (N.endpoint * Real.exp t) = t := by
  dsimp [logTime]
  rw [mul_div_cancel_left₀ _ N.endpoint_pos.ne', Real.log_exp]

theorem logTime_le_iff {X t : ℝ} (hX : 0 < X) :
    N.logTime X ≤ t ↔ X ≤ N.endpoint * Real.exp t := by
  rw [logTime, Real.log_le_iff_le_exp (div_pos hX N.endpoint_pos), div_le_iff₀ N.endpoint_pos]
  rw [mul_comm]

theorem le_logTime_iff {X t : ℝ} (hX : 0 < X) :
    t ≤ N.logTime X ↔ N.endpoint * Real.exp t ≤ X := by
  rw [logTime, Real.le_log_iff_exp_le (div_pos hX N.endpoint_pos), le_div_iff₀ N.endpoint_pos]
  rw [mul_comm]

/-- The radial domain of the extended profiles has no upper radial endpoint. -/
def radialDomain : RadialDomain where
  carrier := {p | -20 < N.scale * p.1 ∧ p.2 ∈ parameterInterval}
  isOpen := (isOpen_lt continuous_const (continuous_const.mul continuous_fst)).inter
    (parameterInterval_open.preimage continuous_snd)
  scale_mem := by
    intro p hp t ht
    refine ⟨?_, hp.2⟩
    rw [show N.scale * (t * p.1) = t * (N.scale * p.1) by ring]
    rcases le_total (N.scale * p.1) 0 with hs | hs
    · have hb := mul_le_mul_of_nonpos_right ht.2 hs
      exact hp.1.trans_le (by simpa only [one_mul] using hb)
    · exact lt_of_lt_of_le (by norm_num) (mul_nonneg ht.1 hs)

theorem natural_mem_of_le_endpoint {p : Point} (hp : p ∈ N.radialDomain.carrier)
    (hX : p.1 ≤ N.endpoint) : p ∈ NaturalProfile.domain N.scale := by
  change (-20 < N.scale * p.1 ∧ N.scale * p.1 < 20) ∧ p.2 ∈ parameterInterval
  refine ⟨⟨hp.1, ?_⟩, hp.2⟩
  have hb := mul_le_mul_of_nonneg_left hX N.scale_pos.le
  rw [N.scale_endpoint] at hb
  linarith

def refF (δ : ℝ) : Field := fun p => if p.1 ≤ N.endpoint then N.f p else
  Real.exp (continuation δ N.logF (N.logTime p.1, p.2))

def refU (δ : ℝ) : Field := fun p => if p.1 ≤ N.endpoint then N.U p else
  continuation δ N.logU (N.logTime p.1, p.2)

theorem refF_eq_natural_initial (δ : ℝ) {p : Point} (hp : p.1 ≤ N.endpoint) :
    N.refF δ p = N.f p := ite_eq_left hp

theorem refU_eq_natural_initial (δ : ℝ) {p : Point} (hp : p.1 ≤ N.endpoint) :
    N.refU δ p = N.U p := ite_eq_left hp

theorem refF_pos (δ : ℝ) {p : Point} (hp : p ∈ N.radialDomain.carrier) (hX : 0 ≤ p.1) :
    0 < N.refF δ p := by
  by_cases hx : p.1 ≤ N.endpoint
  · rw [N.refF_eq_natural_initial δ hx]
    apply N.positive _ (N.natural_mem_of_le_endpoint hp hx) (mul_nonneg N.scale_pos.le hX)
    have hb := mul_le_mul_of_nonneg_left hx N.scale_pos.le
    rw [N.scale_endpoint] at hb
    linarith
  · rw [refF, ite_eq_right hx]
    exact Real.exp_pos _

theorem refF_eq_natural {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : p.1 ≤ N.endpoint * Real.exp δ) :
    N.refF δ p = N.f p := by
  by_cases hx : p.1 ≤ N.endpoint
  · exact N.refF_eq_natural_initial δ hx
  · have hxpos : 0 < p.1 := N.endpoint_pos.trans (lt_of_not_ge hx)
    have ht := (N.logTime_le_iff hxpos).2 hX
    have htT : N.logTime p.1 < rampLimit := ht.trans_lt (by linarith)
    rw [refF, ite_eq_right hx, continuation_eq_natural rampLimit_pos hδ hδT
      parameterInterval_open N.logF_smooth (p := (N.logTime p.1, p.2)) hη ht]
    change Real.exp (Real.log (N.f (N.fromLog (N.logTime p.1, p.2)))) = _
    rw [Real.exp_log (N.fromLog_f_pos (p := (N.logTime p.1, p.2)) ⟨htT, hη⟩), N.fromLog_logTime
      hxpos]

theorem refU_eq_natural {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : p.1 ≤ N.endpoint * Real.exp δ) :
    N.refU δ p = N.U p := by
  by_cases hx : p.1 ≤ N.endpoint
  · exact N.refU_eq_natural_initial δ hx
  · have hxpos : 0 < p.1 := N.endpoint_pos.trans (lt_of_not_ge hx)
    rw [refU, ite_eq_right hx, continuation_eq_natural rampLimit_pos hδ hδT
      parameterInterval_open N.logU_smooth (p := (N.logTime p.1, p.2)) hη ((N.logTime_le_iff
        hxpos).2 hX)]
    change N.U (N.fromLog (N.logTime p.1, p.2)) = _
    rw [N.fromLog_logTime hxpos]

theorem refF_eq_logtime {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    N.refF δ p = Real.exp (continuation δ N.logF (N.logTime p.1, p.2)) := by
  by_cases hx : p.1 ≤ N.endpoint
  · have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hX).2 (by simpa only [Real.exp_zero, mul_one]
    using hx)
    have htδ := ht.trans hδ.le
    rw [refF, ite_eq_left hx, continuation_eq_natural rampLimit_pos hδ hδT
      parameterInterval_open N.logF_smooth (p := (N.logTime p.1, p.2)) hη htδ]
    have hpos := N.fromLog_f_pos (p := (N.logTime p.1, p.2)) ⟨ht.trans_lt rampLimit_pos, hη⟩
    dsimp [logF]
    rw [Real.exp_log hpos, N.fromLog_logTime hX]
  · exact ite_eq_right hx

theorem refU_eq_logtime {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    N.refU δ p = continuation δ N.logU (N.logTime p.1, p.2) := by
  by_cases hx : p.1 ≤ N.endpoint
  · have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hX).2 (by simpa only [Real.exp_zero, mul_one]
    using hx)
    rw [refU, ite_eq_left hx, continuation_eq_natural rampLimit_pos hδ hδT
      parameterInterval_open N.logU_smooth (p := (N.logTime p.1, p.2)) hη (ht.trans hδ.le)]
    change N.U p = N.U (N.fromLog (N.logTime p.1, p.2))
    rw [N.fromLog_logTime hX]
  · exact ite_eq_right hx

theorem logtime_smoothAt {p : Point} (hX : 0 < p.1) :
    ContDiffAt ℝ ∞ (fun q : Point => (N.logTime q.1, q.2)) p :=
  ((contDiffAt_fst.div_const N.endpoint).log (div_ne_zero hX.ne' N.endpoint_pos.ne')).prodMk
    contDiffAt_snd

theorem refF_smooth {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) :
    ContDiffOn ℝ ∞ (N.refF δ) N.radialDomain.carrier := by
  intro p hp
  by_cases hX : 0 < p.1
  · have hs := ((continuation_smooth rampLimit_pos hδ hδT parameterInterval_open
    N.logF_smooth).contDiffAt
      ((fullStrip parameterInterval parameterInterval_open).isOpen.mem_nhds
        (show (N.logTime p.1, p.2) ∈ (fullStrip parameterInterval parameterInterval_open).carrier
          from
          ⟨mem_univ _, hp.2⟩))).comp p (N.logtime_smoothAt hX)
    have heq : N.refF δ =ᶠ[𝓝 p] (fun q => Real.exp (continuation δ N.logF (N.logTime q.1, q.2))) :=
      by
      filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX),
        continuousAt_snd.eventually (parameterInterval_open.mem_nhds hp.2)] with q hqX hqη
      exact N.refF_eq_logtime hδ hδT hqη hqX
    exact (hs.exp.congr_of_eventuallyEq heq).contDiffWithinAt
  · have hbefore : p.1 < N.endpoint := (le_of_not_gt hX).trans_lt N.endpoint_pos
    have hs := N.f_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds
      (N.natural_mem_of_le_endpoint hp hbefore.le))
    have heq : N.refF δ =ᶠ[𝓝 p] N.f := by
      filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hbefore)] with q hq
      exact N.refF_eq_natural_initial δ hq.le
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt

theorem refU_smooth {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) :
    ContDiffOn ℝ ∞ (N.refU δ) N.radialDomain.carrier := by
  intro p hp
  by_cases hX : 0 < p.1
  · have hs := ((continuation_smooth rampLimit_pos hδ hδT parameterInterval_open
    N.logU_smooth).contDiffAt
      ((fullStrip parameterInterval parameterInterval_open).isOpen.mem_nhds
        (show (N.logTime p.1, p.2) ∈ (fullStrip parameterInterval parameterInterval_open).carrier
          from
          ⟨mem_univ _, hp.2⟩))).comp p (N.logtime_smoothAt hX)
    have heq : N.refU δ =ᶠ[𝓝 p] (fun q => continuation δ N.logU (N.logTime q.1, q.2)) := by
      filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX),
        continuousAt_snd.eventually (parameterInterval_open.mem_nhds hp.2)] with q hqX hqη
      exact N.refU_eq_logtime hδ hδT hqη hqX
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt
  · have hbefore : p.1 < N.endpoint := (le_of_not_gt hX).trans_lt N.endpoint_pos
    have hs := N.U_smooth.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds
      (N.natural_mem_of_le_endpoint hp hbefore.le))
    have heq : N.refU δ =ᶠ[𝓝 p] N.U := by
      filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hbefore)] with q hq
      exact N.refU_eq_natural_initial δ hq.le
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt

theorem refF_frozen {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : N.endpoint * Real.exp (2 * δ) ≤ p.1) :
    N.refF δ p = Real.exp (continuation δ N.logF (2 * δ, p.2)) := by
  have hp : 0 < p.1 := (mul_pos N.endpoint_pos (Real.exp_pos _)).trans_le hX
  rw [N.refF_eq_logtime hδ hδT hη hp,
    continuation_frozen rampLimit_pos hδ hδT parameterInterval_open N.logF_smooth
      (p := (N.logTime p.1, p.2)) hη ((N.le_logTime_iff hp).2 hX)]

theorem refU_frozen {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : N.endpoint * Real.exp (2 * δ) ≤ p.1) :
    N.refU δ p = continuation δ N.logU (2 * δ, p.2) := by
  have hp : 0 < p.1 := (mul_pos N.endpoint_pos (Real.exp_pos _)).trans_le hX
  rw [N.refU_eq_logtime hδ hδT hη hp,
    continuation_frozen rampLimit_pos hδ hδT parameterInterval_open N.logU_smooth
      (p := (N.logTime p.1, p.2)) hη ((N.le_logTime_iff hp).2 hX)]

/-- Actual pressure, moments, and lag variables are recomputed from REF. -/
def histories {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) : ProfileHistories.Profiles N.radialDomain where
  f := N.refF δ
  U := N.refU δ
  f_smooth := N.refF_smooth hδ hδT
  U_smooth := N.refU_smooth hδ hδT
  pressure0 := P0
  pressure0_smooth := fun _ _ => hP0.contDiffAt

theorem logTime_hasDerivAt {X : ℝ} (hX : 0 < X) : HasDerivAt N.logTime (1 / X) X := by
  have hd := ((hasDerivAt_id X).div_const N.endpoint).log
    (div_ne_zero hX.ne' N.endpoint_pos.ne')
  apply hd.congr_deriv
  simp only [id_eq]
  field_simp [N.endpoint_pos.ne', hX.ne']

theorem log_refF_hasDerivAt {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    HasDerivAt (fun X => Real.log (N.refF δ (X, p.2)))
      (slopeCutoff δ (N.logTime p.1) * radialPartial N.logF (N.logTime p.1, p.2) / p.1) p.1 := by
  have hd := (continuation_hasDerivAt rampLimit_pos hδ hδT parameterInterval_open
    N.logF_smooth (p := (N.logTime p.1, p.2)) hη).comp p.1 (N.logTime_hasDerivAt hX)
  have hd' : HasDerivAt (fun X => continuation δ N.logF (N.logTime X, p.2))
      (slopeCutoff δ (N.logTime p.1) * radialPartial N.logF (N.logTime p.1, p.2) / p.1) p.1 := by
    convert! hd using 1 ; ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hX] with X hXX
  rw [N.refF_eq_logtime hδ hδT (p := (X, p.2)) hη hXX, Real.log_exp]

theorem refU_hasDerivAt {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    HasDerivAt (fun X => N.refU δ (X, p.2))
      (slopeCutoff δ (N.logTime p.1) * radialPartial N.logU (N.logTime p.1, p.2) / p.1) p.1 := by
  have hd := (continuation_hasDerivAt rampLimit_pos hδ hδT parameterInterval_open
    N.logU_smooth (p := (N.logTime p.1, p.2)) hη).comp p.1 (N.logTime_hasDerivAt hX)
  have hd' : HasDerivAt (fun X => continuation δ N.logU (N.logTime X, p.2))
      (slopeCutoff δ (N.logTime p.1) * radialPartial N.logU (N.logTime p.1, p.2) / p.1) p.1 := by
    convert! hd using 1 ; ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hX] with X hXX
  exact N.refU_eq_logtime hδ hδT hη hXX

theorem natural_logtime_deriv {F : Field} (hF : ContDiffOn ℝ ∞ F (NaturalProfile.domain N.scale))
    {p : Point} (hp : p ∈ (earlyStrip rampLimit rampLimit_pos parameterInterval
      parameterInterval_open).carrier) :
    HasDerivAt (fun t => F (N.fromLog (t, p.2)))
      ((N.fromLog p).1 * radialPartial F (N.fromLog p)) p.1 := by
  have hf := (hF.contDiffAt ((NaturalProfile.domain_isOpen N.scale).mem_nhds (N.fromLog_mem
    hp))).differentiableAt (by simp)
  have hs := hf.hasFDerivAt.comp_hasDerivAt (N.fromLog p).1
    ((hasDerivAt_id (N.fromLog p).1).prodMk (hasDerivAt_const (N.fromLog p).1 p.2))
  have hd := hs.comp p.1 ((Real.hasDerivAt_exp p.1).const_mul N.endpoint)
  simpa only [fromLog, radialPartial, Function.comp_def, id_eq, mul_comm] using hd

theorem radialPartial_logF {p : Point}
    (hp : p ∈ (earlyStrip rampLimit rampLimit_pos parameterInterval
      parameterInterval_open).carrier) :
    radialPartial N.logF p =
      (N.fromLog p).1 * radialPartial N.f (N.fromLog p) / N.f (N.fromLog p) :=
  (radialPartial_hasDerivAt (earlyStrip rampLimit rampLimit_pos parameterInterval
    parameterInterval_open)
    N.logF_smooth hp).unique ((N.natural_logtime_deriv N.f_smooth hp).log (N.fromLog_f_pos hp).ne')

theorem radialPartial_logU {p : Point}
    (hp : p ∈ (earlyStrip rampLimit rampLimit_pos parameterInterval
      parameterInterval_open).carrier) :
    radialPartial N.logU p = (N.fromLog p).1 * radialPartial N.U (N.fromLog p) :=
  (radialPartial_hasDerivAt (earlyStrip rampLimit rampLimit_pos parameterInterval
    parameterInterval_open)
    N.logU_smooth hp).unique (N.natural_logtime_deriv N.U_smooth hp)

/-- Exact same-X damping of the natural logarithmic slope on the natural region. -/
theorem same_radius_log_slope {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) (ht : N.logTime p.1 < rampLimit) :
    p.1 * deriv (fun X => Real.log (N.refF δ (X, p.2))) p.1 =
      slopeCutoff δ (N.logTime p.1) * (p.1 * radialPartial N.f p / N.f p) := by
  rw [(N.log_refF_hasDerivAt hδ hδT hη hX).deriv,
    N.radialPartial_logF (p := (N.logTime p.1, p.2)) ⟨ht, hη⟩, N.fromLog_logTime hX]
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hX.ne']

/-- Exact same-X damping of the natural axial slope. -/
theorem same_radius_U_slope {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) (ht : N.logTime p.1 < rampLimit) :
    p.1 * deriv (fun X => N.refU δ (X, p.2)) p.1 =
      slopeCutoff δ (N.logTime p.1) * (p.1 * radialPartial N.U p) := by
  rw [(N.refU_hasDerivAt hδ hδT hη hX).deriv,
    N.radialPartial_logU (p := (N.logTime p.1, p.2)) ⟨ht, hη⟩, N.fromLog_logTime hX]
  field_simp

theorem endpoint_f_pos {η : ℝ} (hη : η ∈ parameterInterval) : 0 < N.f (N.endpoint, η) := by
  simpa only [fromLog, Real.exp_zero, mul_one] using N.fromLog_f_pos (p := (0, η)) ⟨rampLimit_pos,
    hη⟩

theorem ref_log_transformed_jet_close {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ parameterInterval) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∀ X, N.endpoint ≤ X → ∀ η ∈ K,
      |iteratedDeriv k (fun y => Φ (Real.log (N.refF δ (X, y)), Real.log (N.f (N.endpoint, y)))) η -
        iteratedDeriv k (fun y => Φ (Real.log (N.f (N.endpoint, y)), Real.log (N.f (N.endpoint,
          y)))) η| < ε := by
  obtain ⟨r, hr, hc⟩ := continuation_parameter_jet_close rampLimit_pos parameterInterval_open
    N.logF_smooth hΦ hK hKJ k hε
  refine ⟨min r (rampLimit / 4), lt_min hr (div_pos rampLimit_pos (by norm_num)), ?_⟩
  intro δ hδ hδ₀ X hX η hη
  have hδT : 2 * δ < rampLimit := by have := hδ₀.trans_le (min_le_right _ _); linarith
  have hXpos := N.endpoint_pos.trans_le hX
  have ht : 0 ≤ N.logTime X := (N.le_logTime_iff hXpos).2 (by simpa only [Real.exp_zero, mul_one]
    using hX)
  have heq : (fun y => Φ (Real.log (N.refF δ (X, y)), Real.log (N.f (N.endpoint, y)))) =ᶠ[𝓝 η]
      (fun y => Φ (continuation δ N.logF (N.logTime X, y), N.logF (0, y))) := by
    filter_upwards [parameterInterval_open.mem_nhds (hKJ hη)] with y hy
    rw [N.refF_eq_logtime hδ hδT hy hXpos, Real.log_exp]
    simp only [logF, fromLog, Real.exp_zero, mul_one]
  rw [heq.iteratedDeriv_eq k]
  simpa only [logF, fromLog, Real.exp_zero, mul_one] using
    hc δ hδ (hδ₀.trans_le (min_le_left _ _)) (N.logTime X) ht η hη

theorem ref_U_transformed_jet_close {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ parameterInterval) (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∀ X, N.endpoint ≤ X → ∀ η ∈ K,
      |iteratedDeriv k (fun y => Φ (N.refU δ (X, y), N.U (N.endpoint, y))) η -
        iteratedDeriv k (fun y => Φ (N.U (N.endpoint, y), N.U (N.endpoint, y))) η| < ε := by
  obtain ⟨r, hr, hc⟩ := continuation_parameter_jet_close rampLimit_pos parameterInterval_open
    N.logU_smooth hΦ hK hKJ k hε
  refine ⟨min r (rampLimit / 4), lt_min hr (div_pos rampLimit_pos (by norm_num)), ?_⟩
  intro δ hδ hδ₀ X hX η hη
  have hδT : 2 * δ < rampLimit := by have := hδ₀.trans_le (min_le_right _ _); linarith
  have hXpos := N.endpoint_pos.trans_le hX
  have ht : 0 ≤ N.logTime X := (N.le_logTime_iff hXpos).2 (by simpa only [Real.exp_zero, mul_one]
    using hX)
  have heq : (fun y => Φ (N.refU δ (X, y), N.U (N.endpoint, y))) =ᶠ[𝓝 η]
      (fun y => Φ (continuation δ N.logU (N.logTime X, y), N.logU (0, y))) := by
    filter_upwards [parameterInterval_open.mem_nhds (hKJ hη)] with y hy
    rw [N.refU_eq_logtime hδ hδT hy hXpos]
    simp only [logU, fromLog, Real.exp_zero, mul_one]
  rw [heq.iteratedDeriv_eq k]
  simpa only [logU, fromLog, Real.exp_zero, mul_one] using
    hc δ hδ (hδ₀.trans_le (min_le_left _ _)) (N.logTime X) ht η hη

theorem iteratedDeriv_zero_function (k : ℕ) :
    iteratedDeriv k (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext x
    rw [iteratedDeriv_succ, ih]
    exact deriv_const x 0

theorem ref_log_error_jet_close {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ parameterInterval) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∀ X, N.endpoint ≤ X → ∀ η ∈ K,
      |iteratedDeriv k (fun y => Real.log (N.refF δ (X, y)) - Real.log (N.f (N.endpoint, y))) η| <
        ε := by
  obtain ⟨r, hr, hc⟩ := N.ref_log_transformed_jet_close
    (contDiff_fst.sub contDiff_snd) hK hKJ k hε
  refine ⟨r, hr, ?_⟩
  intro δ hδ hδr X hX η hη
  simpa only [sub_self, iteratedDeriv_zero_function, sub_zero] using hc δ hδ hδr X hX η hη

theorem ref_U_error_jet_close {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ parameterInterval) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∀ X, N.endpoint ≤ X → ∀ η ∈ K,
      |iteratedDeriv k (fun y => N.refU δ (X, y) - N.U (N.endpoint, y)) η| < ε := by
  obtain ⟨r, hr, hc⟩ := N.ref_U_transformed_jet_close
    (contDiff_fst.sub contDiff_snd) hK hKJ k hε
  refine ⟨r, hr, ?_⟩
  intro δ hδ hδr X hX η hη
  simpa only [sub_self, iteratedDeriv_zero_function, sub_zero] using hc δ hδ hδr X hX η hη

theorem ref_relative_error_jet_close {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ parameterInterval) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∀ X, N.endpoint ≤ X → ∀ η ∈ K,
      |iteratedDeriv k (fun y => N.refF δ (X, y) / N.f (N.endpoint, y) - 1) η| < ε := by
  obtain ⟨r, hr, hc⟩ := N.ref_log_transformed_jet_close
    (Φ := fun p => Real.exp (p.1 - p.2) - 1)
    ((contDiff_fst.sub contDiff_snd).exp.sub contDiff_const) hK hKJ k hε
  refine ⟨r, hr, ?_⟩
  intro δ hδ hδr X hX η hη
  have hXpos := N.endpoint_pos.trans_le hX
  have hb : |iteratedDeriv k (fun y => Real.exp
      (Real.log (N.refF δ (X, y)) - Real.log (N.f (N.endpoint, y))) - 1) η| < ε := by
    simpa only [sub_self, Real.exp_zero, iteratedDeriv_zero_function, sub_zero] using hc δ hδ hδr X
      hX η hη
  have heq : (fun y => N.refF δ (X, y) / N.f (N.endpoint, y) - 1) =ᶠ[𝓝 η]
      (fun y => Real.exp (Real.log (N.refF δ (X, y)) - Real.log (N.f (N.endpoint, y))) - 1) := by
    filter_upwards [parameterInterval_open.mem_nhds (hKJ hη)] with y hy
    have hp : (X, y) ∈ N.radialDomain.carrier :=
      ⟨lt_trans (by norm_num) (mul_pos N.scale_pos hXpos), hy⟩
    rw [Real.exp_sub, Real.exp_log (N.refF_pos δ hp hXpos.le), Real.exp_log (N.endpoint_f_pos hy)]
  rw [heq.iteratedDeriv_eq k]
  exact hb

theorem ref_field_error_jet_close {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ parameterInterval) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ δ, 0 < δ → δ < δ₀ → ∀ X, N.endpoint ≤ X → ∀ η ∈ K,
      |iteratedDeriv k (fun y => N.refF δ (X, y) - N.f (N.endpoint, y)) η| < ε := by
  obtain ⟨r, hr, hc⟩ := N.ref_log_transformed_jet_close
    (contDiff_fst.exp.sub contDiff_snd.exp) hK hKJ k hε
  refine ⟨r, hr, ?_⟩
  intro δ hδ hδr X hX η hη
  have hXpos := N.endpoint_pos.trans_le hX
  have hb : |iteratedDeriv k (fun y => Real.exp (Real.log (N.refF δ (X, y))) -
      Real.exp (Real.log (N.f (N.endpoint, y)))) η| < ε := by
    simpa only [sub_self, iteratedDeriv_zero_function, sub_zero] using hc δ hδ hδr X hX η hη
  have heq : (fun y => N.refF δ (X, y) - N.f (N.endpoint, y)) =ᶠ[𝓝 η]
      (fun y => Real.exp (Real.log (N.refF δ (X, y))) - Real.exp (Real.log (N.f (N.endpoint, y))))
        := by
    filter_upwards [parameterInterval_open.mem_nhds (hKJ hη)] with y hy
    have hp : (X, y) ∈ N.radialDomain.carrier :=
      ⟨lt_trans (by norm_num) (mul_pos N.scale_pos hXpos), hy⟩
    rw [Real.exp_log (N.refF_pos δ hp hXpos.le), Real.exp_log (N.endpoint_f_pos hy)]
  rw [heq.iteratedDeriv_eq k]
  exact hb

def Xbig : ℝ := 100
def Xi : ℝ := 110

theorem freeze_before_Xbig (hscale : 1 ≤ N.scale) {δ : ℝ} (hδT : 2 * δ < rampLimit) :
    N.endpoint * Real.exp (2 * δ) < Xbig := by
  have he : Real.exp (2 * δ) < 41 / 40 := by
    simpa only [rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)] using
      Real.exp_lt_exp.mpr hδT
  have hb : N.endpoint ≤ 4 := by
    change 4 / N.scale ≤ 4
    apply (div_le_iff₀ N.scale_pos).2
    linarith
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (2 * δ)).le
  dsimp [Xbig]
  linarith

/-- In particular the reference is already frozen throughout [100,110]. -/
theorem frozen_through_Xi (hscale : 1 ≤ N.scale) {δ : ℝ} (hδ : 0 < δ)
    (hδT : 2 * δ < rampLimit) {p : Point} (hη : p.2 ∈ parameterInterval)
    (hX : p.1 ∈ Icc Xbig Xi) :
    N.refF δ p = Real.exp (continuation δ N.logF (2 * δ, p.2)) ∧
      N.refU δ p = continuation δ N.logU (2 * δ, p.2) := by
  have hfreeze := (N.freeze_before_Xbig hscale hδT).le.trans hX.1
  exact ⟨N.refF_frozen hδ hδT hη hfreeze, N.refU_frozen hδ hδT hη hfreeze⟩

end Input

end NavierStokes.ReferencePath

end
