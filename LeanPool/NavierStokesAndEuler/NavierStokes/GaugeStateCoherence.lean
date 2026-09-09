/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalResidualNaturality
public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean

/-!
# Coherence of the actual moving-gauge pressure reconstruction

The hypotheses transport the primitive gauge data and the incoming state on
whole radial/torus fibers.  The recomputed pressure and retained cutoff alias
are obtained from their genuine integral definitions.
-/

@[expose] public section


namespace NavierStokes.GaugeStateCoherence

noncomputable section

open Set Function Filter
open scoped ContDiff Topology
open PhysicalResidualNaturality

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- The actual invertible map on the universal cover. -/
noncomputable def chartEquiv (l : ℝ) (hl : l ≠ 0) (P : S ≃L[ℝ] T) (k : ℕ) :
    PressureStream.Lift S ≃L[ℝ] PressureStream.Lift T :=
  (PhysicalResidualNaturality.scalarEquiv ℝ l hl).prodCongr
    (P.prodCongr (CommonCoverSolve.coverPower k))

@[simp] theorem chartEquiv_apply (l : ℝ) (hl : l ≠ 0) (P : S ≃L[ℝ] T) (k : ℕ)
    (z : PressureStream.Lift S) :
    chartEquiv l hl P k z = (l * z.1, (P z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) := by
  simp only [chartEquiv, ContinuousLinearEquiv.prodCongr_apply,
    PhysicalResidualNaturality.scalarEquiv_apply, smul_eq_mul,
    MeanChartCompatibility.coverMap_eq_coverPower]

theorem chartEquiv_toContinuousLinearMap (l : ℝ) (hl : l ≠ 0) (P : S ≃L[ℝ] T) (k : ℕ) :
    (chartEquiv l hl P k).toContinuousLinearMap =
      MeanChartCompatibility.chartLinear l
        (P.toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k)) := by
  apply ContinuousLinearMap.ext
  intro z
  exact chartEquiv_apply l hl P k z

theorem coverPull_eq (l : ℝ) (hl : l ≠ 0) (P : S ≃L[ℝ] T) (k : ℕ)
    (u : ℝ) (f : PressureStream.Lift T → ℝ) (z : PressureStream.Lift S) :
    MeanChartCompatibility.coverPull l P.toContinuousLinearMap k u f z =
      u * f (chartEquiv l hl P k z) := by
  rw [chartEquiv_apply]
  rfl

/-! ## Whole-fiber locality of the actual gauge operators -/

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem pressureSource_fiberLocal (a b : ℝ) (hab : a < b) (ell : S → ℝ) :
    PhysicalMeanDomain.FiberLocal (VariableGaugeMean.pressureSource a b hab ell) := by
  intro f g s he r Y
  unfold VariableGaugeMean.pressureSource
  rw [he r Y, show PressureStream.pressureMass f s = PressureStream.pressureMass g s from
    PhysicalMeanDomain.liftedPressureMass_fiberLocal f g s he r Y]

theorem meanPressure_fiberLocal (d a b M : ℝ) (hab : a < b) (ell : S → ℝ) (v : Plane) :
    PhysicalMeanDomain.FiberLocal (VariableGaugeMean.meanPressure d a b M hab ell v) := by
  intro f g s he r Y
  exact VariableGaugeMean.compactPrimitive_fiberLocal d a b M ell v _ _ s
    (pressureSource_fiberLocal a b hab ell f g s he) r Y

theorem meanPressure_congr_profile {d a b d' a' b' : ℝ} {hab : a < b} {hab' : a' < b'}
    (hd : d = d') (ha : a = a') (hb : b = b') (M : ℝ) (ell : S → ℝ)
    (v : Plane) (f : PressureStream.Lift S → ℝ) :
    VariableGaugeMean.meanPressure d a b M hab ell v f =
      VariableGaugeMean.meanPressure d' a' b' M hab' ell v f := by
  subst d'
  subst a'
  subst b'
  rfl

/-- The scalar whose negative is the radial component of `pressureAliasState`. -/
noncomputable def pressureAlias (d a b M : ℝ) (hab : a < b) (ell : S → ℝ)
    (v : Plane) (f : PressureStream.Lift S → ℝ) : PressureStream.Lift S → ℝ :=
  VariableGaugeMean.compactAlias d a b M ell v
    (VariableGaugeMean.pressureSource a b hab ell f)

theorem pressureAlias_fiberLocal (d a b M : ℝ) (hab : a < b) (ell : S → ℝ) (v : Plane) :
    PhysicalMeanDomain.FiberLocal (pressureAlias d a b M hab ell v) := by
  intro f g s he r Y
  exact PhysicalMeanDomain.physicalAlias_fiberLocal d (ell s * a) (ell s * b) M v _ _ s
    (pressureSource_fiberLocal a b hab ell f g s he) r Y

theorem pressureAlias_eq_fixed {a b : ℝ} (hab : a < b) (d M : ℝ) (ell : S → ℝ)
    (v : Plane) (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S)
    (hl : 0 < ell z.2.1) :
    pressureAlias d a b M hab ell v f z =
      PressureStream.pressureAlias d (ell z.2.1 * a) (ell z.2.1 * b) M
        (mul_lt_mul_of_pos_left hab hl) v f z := by
  exact PhysicalMeanDomain.physicalAlias_fiberLocal d (ell z.2.1 * a) (ell z.2.1 * b) M v
    _ _ z.2.1 (fun r Y => VariableGaugeMean.pressureSource_eq_fixed hab ell f
      (r, (z.2.1, Y)) hl) z.1 z.2.2

theorem pressureAlias_congr_endpoints {a b a' b' : ℝ} {hab : a < b} {hab' : a' < b'}
    (ha : a = a') (hb : b = b') (d M : ℝ) (v : Plane)
    (f : PressureStream.Lift S → ℝ) (z : PressureStream.Lift S) :
    PressureStream.pressureAlias d a b M hab v f z =
      PressureStream.pressureAlias d a' b' M hab' v f z := by
  subst a'
  subst b'
  rfl

/-! ## Recomputed pressure from transported primitive data -/

/-- Only primitive gauge data are compared: profile endpoints, exponent,
length and actual radial transport vector. -/
structure GaugeOn (V : Set S) (l : ℝ) (P : S →L[ℝ] T) (k : ℕ)
    (g : VariableGaugeMean.GaugeData S) (r : VariableGaugeMean.GaugeData T)
    (n nr : ℕ) : Prop where
  exponent : r.radial.exponent = g.radial.exponent
  inner : r.radial.inner = g.radial.inner
  outer : r.radial.outer = g.radial.outer
  positive : ∀ s ∈ V, 0 < g.length n s
  length : ∀ s ∈ V, r.length nr (P s) = l * g.length n s
  frequency : g.radial.frequency n • TemporalMeanUpdate.coverMap k g.radial.radialDirection =
    (r.radial.frequency nr * l ^ g.radial.exponent) • r.radial.radialDirection

theorem meanPressure_on {l : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {a b d M N u : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v w : Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    (ell : S → ℝ) (ell' : T → ℝ) {V : Set S} {U : Set T} (hU : IsOpen U)
    (hmap : MapsTo P V U) (hpos : ∀ s ∈ V, 0 < ell s)
    (hlen : ∀ s ∈ V, ell' (P s) = l * ell s)
    {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u f fr)
    (hf : ContDiffOn ℝ ∞ fr (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U fr)
    (hs : VariableGaugeMean.SupportedGauge a b ell' U fr) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (u / l)
      (VariableGaugeMean.meanPressure d a b M hab ell v f)
      (VariableGaugeMean.meanPressure d a b N hab ell' w fr) := by
  intro z hz
  have hfiber : ∀ r Y, f (r, (z.2.1, Y)) =
      MeanChartCompatibility.coverPull l P.toContinuousLinearMap k u fr (r, (z.2.1, Y)) := by
    intro r Y
    rw [coverPull_eq l hl.ne' P k]
    exact he _ hz
  rw [meanPressure_fiberLocal d a b M hab ell v _ _ z.2.1 hfiber z.1 z.2.2]
  have ht := VariableGaugeMean.meanPressure_coverPull hl ha hab hd P.toContinuousLinearMap
    k M N u v w hshift ell ell' hU hf hp hs z (hmap hz) (hpos _ hz) (hlen _ hz)
  rw [chartEquiv_apply]
  exact ht

theorem reconstructState_on {l c : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {V : Set S} {U : Set T} (hV : IsOpen V) (hU : IsOpen U) (hmap : MapsTo P V U)
    (g : VariableGaugeMean.GaugeData S) (gr : VariableGaugeMean.GaugeData T)
    (C : CorrectionState.Context (PressureStream.Lift S))
    (Cr : CorrectionState.Context (PressureStream.Lift T))
    (s : CorrectionState.State (PressureStream.Lift S))
    (r : CorrectionState.State (PressureStream.Lift T)) (n nr : ℕ)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : GaugeOn V l P.toContinuousLinearMap k g gr n nr)
    (H : StateOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l s r n nr)
    (G : ContextOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l C Cr n nr)
    (hf : ContDiffOn ℝ ∞ (r.gr Cr nr) (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U (r.gr Cr nr))
    (hs : VariableGaugeMean.SupportedGauge gr.radial.inner gr.radial.outer (gr.length nr) U (r.gr
        Cr nr)) :
    StateOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l
      (VariableGaugeMean.reconstructState g C s) (VariableGaugeMean.reconstructState gr Cr r) n nr
          := by
  refine ⟨H.mean, ?_, H.oscillation, H.oscillatoryPressure, H.baseError, H.gaussian, H.aliasError⟩
  have hgr := H.gr G (PhysicalMeanDomain.slowDomain_open hV) hl.ne'
  have hsup : VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (gr.length nr) U (r.gr
      Cr nr) := by
    simpa only [hg.inner, hg.outer] using hs
  have ht := meanPressure_on hl P k ha g.radial.inner_lt_outer hd
    g.radial.radialDirection gr.radial.radialDirection hg.frequency (g.length n) (gr.length nr)
    hU hmap hg.positive hg.length hgr hf hp hsup
  have hfactor : c * c * l / l = c * c := mul_div_cancel_right₀ (c*c) hl.ne'
  change ScalarOn _ _ _ (VariableGaugeMean.meanPressure _ _ _ _ _ _ _ _)
    (VariableGaugeMean.meanPressure _ _ _ _ _ _ _ _)
  rw [meanPressure_congr_profile (hab' := g.radial.inner_lt_outer) hg.exponent hg.inner hg.outer
    (gr.radial.frequency nr) (gr.length nr) gr.radial.radialDirection (r.gr Cr nr)]
  exact ht.reweight hfactor

/-! ## The retained pressure alias has the residual units -/

theorem fixedPressureAlias_fiberLocal (d a b M : ℝ) (hab : a < b) (v : Plane) :
    PhysicalMeanDomain.FiberLocal (S := S) (PressureStream.pressureAlias d a b M hab v) := by
  intro f g s he r Y
  exact PhysicalMeanDomain.physicalAlias_fiberLocal d a b M v _ _ s
    (PhysicalMeanDomain.pressureSource_fiberLocal a b hab f g s he) r Y

theorem pressureAlias_zero_of_nonpositive {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (M : ℝ) (ell : S → ℝ) (v : Plane) (f : PressureStream.Lift S → ℝ)
    (z : PressureStream.Lift S) (hl : 0 < ell z.2.1) (hz : z.1 ≤ 0) :
    pressureAlias d a b M hab ell v f z = 0 := by
  by_contra hn
  have hh := RadialPullback.physicalAlias_supported (mul_pos hl ha)
    (mul_lt_mul_of_pos_left hab hl) hd M ((0 : S), v)
    (VariableGaugeMean.pressureSource a b hab ell f) hn
  exact (not_lt_of_ge (hh.1.trans hz)) (mul_pos hl ha)

theorem pressureAlias_supported {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (M : ℝ) (ell : S → ℝ) (v : Plane) (f : PressureStream.Lift S → ℝ)
    (V : Set S) (hl : ∀ s ∈ V, 0 < ell s) :
    VariableGaugeMean.SupportedGauge a b ell V (pressureAlias d a b M hab ell v f) := by
  intro z hz hn
  exact RadialPullback.physicalAlias_supported (mul_pos (hl _ hz) ha)
    (mul_lt_mul_of_pos_left hab (hl _ hz)) hd M ((0 : S), v)
    (VariableGaugeMean.pressureSource a b hab ell f) hn

theorem pressureAlias_congr_profile {d a b d' a' b' : ℝ} {hab : a < b} {hab' : a' < b'}
    (hd : d = d') (ha : a = a') (hb : b = b') (M : ℝ) (ell : S → ℝ)
    (v : Plane) (f : PressureStream.Lift S → ℝ) :
    pressureAlias d a b M hab ell v f = pressureAlias d' a' b' M hab' ell v f := by
  subst d'
  subst a'
  subst b'
  rfl

/-- Naturality of the actual variable-gauge alias, including all nonpositive
radii where the cutoff makes both sides vanish. -/
theorem pressureAlias_coverPull {l a b d : ℝ} (hl : 0 < l) (ha : 0 < a)
    (hab : a < b) (hd : 0 < d) (P : S →L[ℝ] T) (k : ℕ) (M N u : ℝ)
    (v w : Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    (ell : S → ℝ) (ell' : T → ℝ) {U : Set T} (hU : IsOpen U)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U f) (hs : VariableGaugeMean.SupportedGauge a b ell' U f)
    (z : PressureStream.Lift S) (hz : P z.2.1 ∈ U) (hzl : 0 < ell z.2.1)
    (hell : ell' (P z.2.1) = l * ell z.2.1) :
    pressureAlias d a b M hab ell v (MeanChartCompatibility.coverPull l P k u f) z =
      u * pressureAlias d a b N hab ell' w f
        (MeanChartCompatibility.chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z) := by
  have hzl' : 0 < ell' (P z.2.1) := by rw [hell]; exact mul_pos hl hzl
  by_cases hr : 0 ≤ z.1
  · let g := PhysicalMeanDomain.freezeSlow (P z.2.1) f
    have hg : ContDiff ℝ ∞ g := VariableGaugeMean.freezeSlow_contDiff hU hz hf
    have hgp : PressureStream.TorusPeriodicLift g := by
      intro r s Y j
      exact hp r (P z.2.1) hz Y j
    have hgs : RadialAlias.RadiallySupported (l * (ell z.2.1 * a)) (l * (ell z.2.1 * b)) g := by
      intro p hne
      have h := hs (p.1, (P z.2.1, p.2.2)) hz hne
      rw [hell] at h
      simp only [mul_assoc] at h
      exact h
    have he (r : ℝ) (Y : Plane) : g (r, (P z.2.1, Y)) = f (r, (P z.2.1, Y)) := rfl
    have hscaleA : l * (ell z.2.1 * a) = ell' (P z.2.1) * a := by rw [hell]; ring
    have hscaleB : l * (ell z.2.1 * b) = ell' (P z.2.1) * b := by rw [hell]; ring
    have ht := MeanChartCompatibility.pressureAlias_coverPull hl (mul_pos hzl ha)
      (mul_lt_mul_of_pos_left hab hzl) hd P k M N u v w hshift hg hgp hgs z hr
    have hleft : PressureStream.pressureAlias d (ell z.2.1 * a) (ell z.2.1 * b) M
        (mul_lt_mul_of_pos_left hab hzl) v (MeanChartCompatibility.coverPull l P k u g) z =
      PressureStream.pressureAlias d (ell z.2.1 * a) (ell z.2.1 * b) M
        (mul_lt_mul_of_pos_left hab hzl) v (MeanChartCompatibility.coverPull l P k u f) z :=
      fixedPressureAlias_fiberLocal d _ _ M _ v
        (MeanChartCompatibility.coverPull l P k u g) (MeanChartCompatibility.coverPull l P k u f)
        z.2.1 (fun _ _ => rfl) z.1 z.2.2
    rw [pressureAlias_eq_fixed hab d M ell v _ z hzl,
      pressureAlias_eq_fixed hab d N ell' w f _ hzl']
    change _ = u * PressureStream.pressureAlias d (l * (ell z.2.1 * a))
      (l * (ell z.2.1 * b)) N _ w g
        (MeanChartCompatibility.chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z) at ht
    rw [hleft] at ht
    rw [pressureAlias_congr_endpoints (hab' := mul_lt_mul_of_pos_left hab hzl') hscaleA hscaleB]
        at ht
    exact ht.trans (congrArg (fun t : ℝ => u * t)
      (fixedPressureAlias_fiberLocal d (ell' (P z.2.1) * a)
        (ell' (P z.2.1) * b) N (mul_lt_mul_of_pos_left hab hzl') w g f (P z.2.1) he
        (l * z.1) (TemporalMeanUpdate.coverMap k z.2.2)))
  · have hzr : z.1 ≤ 0 := (lt_of_not_ge hr).le
    rw [pressureAlias_zero_of_nonpositive ha hab hd M ell v _ z hzl hzr,
      pressureAlias_zero_of_nonpositive ha hab hd N ell' w f _ hzl'
        (mul_nonpos_of_nonneg_of_nonpos hl.le hzr), mul_zero]

theorem pressureAlias_on {l : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {a b d M N u : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v w : Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    (ell : S → ℝ) (ell' : T → ℝ) {V : Set S} {U : Set T} (hU : IsOpen U)
    (hmap : MapsTo P V U) (hpos : ∀ s ∈ V, 0 < ell s)
    (hlen : ∀ s ∈ V, ell' (P s) = l * ell s)
    {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u f fr)
    (hf : ContDiffOn ℝ ∞ fr (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U fr)
    (hs : VariableGaugeMean.SupportedGauge a b ell' U fr) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u
      (pressureAlias d a b M hab ell v f) (pressureAlias d a b N hab ell' w fr) := by
  intro z hz
  have hfiber : ∀ r Y, f (r, (z.2.1, Y)) =
      MeanChartCompatibility.coverPull l P.toContinuousLinearMap k u fr (r, (z.2.1, Y)) := by
    intro r Y
    rw [coverPull_eq l hl.ne' P k]
    exact he _ hz
  rw [pressureAlias_fiberLocal d a b M hab ell v _ _ z.2.1 hfiber z.1 z.2.2]
  have ht := pressureAlias_coverPull hl ha hab hd P.toContinuousLinearMap
    k M N u v w hshift ell ell' hU hf hp hs z (hmap hz) (hpos _ hz) (hlen _ hz)
  rw [chartEquiv_apply]
  exact ht

theorem pressureAliasState_on {l c : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {V : Set S} {U : Set T} (hV : IsOpen V) (hU : IsOpen U) (hmap : MapsTo P V U)
    (g : VariableGaugeMean.GaugeData S) (gr : VariableGaugeMean.GaugeData T)
    (C : CorrectionState.Context (PressureStream.Lift S))
    (Cr : CorrectionState.Context (PressureStream.Lift T))
    (s : CorrectionState.State (PressureStream.Lift S))
    (r : CorrectionState.State (PressureStream.Lift T)) (n nr : ℕ)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : GaugeOn V l P.toContinuousLinearMap k g gr n nr)
    (H : StateOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l s r n nr)
    (G : ContextOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l C Cr n nr)
    (hf : ContDiffOn ℝ ∞ (r.gr Cr nr) (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U (r.gr Cr nr))
    (hs : VariableGaugeMean.SupportedGauge gr.radial.inner gr.radial.outer (gr.length nr) U (r.gr
        Cr nr)) :
    ∀ z ∈ PhysicalMeanDomain.slowDomain V, ∀ theta i,
      VariableGaugeMean.pressureAliasState g C s n (z, theta) i =
        (c*c*l) * VariableGaugeMean.pressureAliasState gr Cr r nr
          (chartEquiv l hl.ne' P k z, theta) i := by
  have hgr := H.gr G (PhysicalMeanDomain.slowDomain_open hV) hl.ne'
  have hsup : VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (gr.length nr) U (r.gr
      Cr nr) := by
    simpa only [hg.inner, hg.outer] using hs
  have ht := pressureAlias_on hl P k ha g.radial.inner_lt_outer hd
    g.radial.radialDirection gr.radial.radialDirection hg.frequency (g.length n) (gr.length nr)
    hU hmap hg.positive hg.length hgr hf hp hsup
  have heq := pressureAlias_congr_profile (hab := gr.radial.inner_lt_outer) (hab' :=
      g.radial.inner_lt_outer)
    hg.exponent hg.inner hg.outer (gr.radial.frequency nr) (gr.length nr) gr.radial.radialDirection
        (r.gr Cr nr)
  intro z hz theta i
  have he := ht z hz
  rw [← heq] at he
  fin_cases i
  · change -pressureAlias _ _ _ _ _ _ _ _ z = (c*c*l) * -pressureAlias _ _ _ _ _ _ _ _ _
    rw [he]
    ring
  · change (0 : ℝ) = (c*c*l) * 0
    simp
  · change (0 : ℝ) = (c*c*l) * 0
    simp

/-! ## The actual similarity gauge in two bands -/

/-- Band scale, given by `(ChartScales.Q n / ChartScales.Q m) ^ (1 / 2 : ℝ)`. -/
noncomputable def bandScale (n m : ℕ) : ℝ :=
  (ChartScales.Q n / ChartScales.Q m) ^ (1 / 2 : ℝ)

theorem bandScale_pos (n m : ℕ) : 0 < bandScale n m :=
  Real.rpow_pos_of_pos (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)) _

/-- Band velocity scale, given by `(ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.A h`. -/
noncomputable def bandVelocityScale (h : ℝ) (n m : ℕ) : ℝ :=
  (ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.A h

/-- The slow coordinates are ordered `(T,Z)`, as in the moving mean gauge. -/
noncomputable def bandSlowEquiv (h : ℝ) (n m : ℕ) : Plane ≃L[ℝ] Plane :=
  (PhysicalResidualNaturality.scalarEquiv ℝ (ChartScales.Q n / ChartScales.Q m)
    (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)).ne').prodCongr
  (PhysicalResidualNaturality.scalarEquiv ℝ
    ((ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.D h)
    (Real.rpow_pos_of_pos (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)) _).ne')

@[simp] theorem bandSlowEquiv_apply (h : ℝ) (n m : ℕ) (s : Plane) :
    bandSlowEquiv h n m s =
      ((ChartScales.Q n / ChartScales.Q m) * s.1,
        (ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.D h * s.2) := rfl

/-- Band chart equiv, given by `chartEquiv (bandScale n m) (bandScale_pos n m).ne'
(bandSlowEquiv h n m) k`. -/
noncomputable def bandChartEquiv (h : ℝ) (n m k : ℕ) : PressureStream.Lift Plane ≃L[ℝ]
    PressureStream.Lift Plane :=
  chartEquiv (bandScale n m) (bandScale_pos n m).ne' (bandSlowEquiv h n m) k

@[simp] theorem bandChartEquiv_apply (h : ℝ) (n m k : ℕ) (z : PressureStream.Lift Plane) :
    bandChartEquiv h n m k z =
      (bandScale n m * z.1, (bandSlowEquiv h n m z.2.1, TemporalMeanUpdate.coverMap k z.2.2)) :=
  chartEquiv_apply _ _ _ _ _

theorem qLength_bandSlowEquiv {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (n m : ℕ) {s : Plane} (hs : 0 < s.1) :
    VariableGaugeMean.qLength (2*h) (bandSlowEquiv h n m s) =
      bandScale n m * VariableGaugeMean.qLength (2*h) s := by
  change Real.sqrt (SimilarityCoordinates.coordinateQ (2*h)
      ((ChartScales.Q n / ChartScales.Q m) * s.1,
        (ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.D h * s.2)) = _
  rw [SimilarityHomogeneity.coordinateQ_scale_h hh hh1
    (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)) hs,
    Real.sqrt_mul (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)).le]
  rw [Real.sqrt_eq_rpow]
  rfl

theorem radialFrequency_band_transport (h d M : ℝ) (n m k i ir : ℕ) (hi : i + k = ir) :
    MeanChartCompatibility.radialFrequency h n i d M * ChartScales.Lambda ^ k =
      MeanChartCompatibility.radialFrequency h m ir d M * bandScale n m ^ d := by
  have hp : bandScale n m ^ d = ChartScales.Q n ^ (d / 2) / ChartScales.Q m ^ (d / 2) := by
    unfold bandScale
    rw [← Real.rpow_mul (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)).le]
    rw [show (1 / 2 : ℝ) * d = d / 2 by ring]
    exact Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le (d / 2)
  rw [MeanChartCompatibility.radialFrequency, MeanChartCompatibility.radialFrequency, hp, ← hi,
      pow_add]
  field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos m) (d / 2)).ne']

/-- The similarity gauge satisfies all primitive transport laws with the
actual band scales and actual common-index gap. -/
theorem similarityGaugeOn {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (d a b M : ℝ) (hab : a < b) (index : ℕ → ℕ) (n m k : ℕ)
    (hi : index n + k = index m) {V : Set Plane} (hV : ∀ s ∈ V, 0 < s.1) :
    GaugeOn V (bandScale n m) (bandSlowEquiv h n m).toContinuousLinearMap k
      (VariableGaugeMean.similarityGauge h d a b M hab index)
      (VariableGaugeMean.similarityGauge h d a b M hab index) n m := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro s hs
    exact VariableGaugeMean.qLength_pos (by linarith) (by linarith) (hV s hs)
  · intro s hs
    exact qLength_bandSlowEquiv hh hh1 n m (hV s hs)
  · change MeanChartCompatibility.radialFrequency h n (index n) d M •
      TemporalMeanUpdate.coverMap k (TorusInverse.vector .radial) =
      (MeanChartCompatibility.radialFrequency h m (index m) d M * bandScale n m ^ d) •
        TorusInverse.vector .radial
    rw [MeanChartCompatibility.coverMap_radial, smul_smul,
      radialFrequency_band_transport h d M n m k (index n) (index m) hi]

theorem bandScale_eq_ratioPower (n m : ℕ) :
    bandScale n m = PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) (1/2) :=
  Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le _

theorem bandVelocityScale_eq_ratioPower (h : ℝ) (n m : ℕ) :
    bandVelocityScale h n m =
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) (CoordinateAlgebra.A h)
          :=
  Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le _

/-- Concrete band/common-cover reconstruction, with the length and frequency
transport laws derived from `similarityGauge` itself. -/
theorem similarity_reconstruction_on {h d a b M : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (index : ℕ → ℕ) (n m k : ℕ) (hi : index n + k = index m)
    {V U : Set Plane} (hV : IsOpen V) (hU : IsOpen U) (htime : ∀ s ∈ V, 0 < s.1)
    (hmap : MapsTo (bandSlowEquiv h n m) V U)
    (C Cr : CorrectionState.Context (PressureStream.Lift Plane))
    (s r : CorrectionState.State (PressureStream.Lift Plane))
    (H : StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) s r n m)
    (G : ContextOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) C Cr n m)
    (hf : ContDiffOn ℝ ∞ (r.gr Cr m) (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U (r.gr Cr m))
    (hs : VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength (2 * h)) U (r.gr Cr m)) :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m)
      (VariableGaugeMean.reconstructState (VariableGaugeMean.similarityGauge h d a b M hab index) C
          s)
      (VariableGaugeMean.reconstructState (VariableGaugeMean.similarityGauge h d a b M hab index)
          Cr r) n m ∧
    ∀ z ∈ PhysicalMeanDomain.slowDomain V, ∀ theta i,
      VariableGaugeMean.pressureAliasState (VariableGaugeMean.similarityGauge h d a b M hab index)
          C s n
        (z, theta) i =
      (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) *
        VariableGaugeMean.pressureAliasState (VariableGaugeMean.similarityGauge h d a b M hab
            index) Cr r m
          (bandChartEquiv h n m k z, theta) i := by
  have hg := similarityGaugeOn hh hh1 d a b M hab index n m k hi htime
  exact ⟨reconstructState_on (bandScale_pos n m) (bandSlowEquiv h n m) k hV hU hmap
    _ _ C Cr s r n m ha hd hg H G hf hp hs,
    pressureAliasState_on (bandScale_pos n m) (bandSlowEquiv h n m) k hV hU hmap
    _ _ C Cr s r n m ha hd hg H G hf hp hs⟩

/-! ## Actual support, on the same moving shell -/

theorem supportedGauge_of_scalarOn {l u a b : ℝ} (hl : 0 < l)
    (P : S ≃L[ℝ] T) (k : ℕ) (ell : S → ℝ) (ell' : T → ℝ) {V : Set S} {U : Set T}
    (hmap : MapsTo P V U) (hlen : ∀ s ∈ V, ell' (P s) = l * ell s)
    {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u f fr)
    (hs : VariableGaugeMean.SupportedGauge a b ell' U fr) :
    VariableGaugeMean.SupportedGauge a b ell V f := by
  intro z hz hn
  have hne : fr (chartEquiv l hl.ne' P k z) ≠ 0 := by
    intro hh
    apply hn
    rw [he z hz, hh, mul_zero]
  have hmem : (chartEquiv l hl.ne' P k z).2.1 ∈ U := by
    simpa only [chartEquiv_apply] using hmap hz
  have hbnd := hs _ hmem hne
  rw [chartEquiv_apply] at hbnd
  change l * z.1 ∈ Icc (ell' (P z.2.1) * a) (ell' (P z.2.1) * b) at hbnd
  rw [hlen _ hz, mul_assoc, mul_assoc] at hbnd
  exact ⟨(mul_le_mul_iff_right₀ hl).mp hbnd.1, (mul_le_mul_iff_right₀ hl).mp hbnd.2⟩

theorem meanPressure_supported {a b d : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (M : ℝ) (ell : S → ℝ) (v : Plane) {U : Set S} (hU : IsOpen U)
    (hl : ∀ s ∈ U, 0 < ell s) {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge a b ell U f) :
    VariableGaugeMean.SupportedGauge a b ell U (VariableGaugeMean.meanPressure d a b M hab ell v f)
        := by
  intro z hz hn
  let g := PhysicalMeanDomain.freezeSlow z.2.1 f
  have hg : ContDiff ℝ ∞ g := VariableGaugeMean.freezeSlow_contDiff hU hz hf
  have hgs : RadialAlias.RadiallySupported (ell z.2.1 * a) (ell z.2.1 * b) g :=
    fun p hp => hs (p.1, (z.2.1, p.2.2)) hz hp
  have hvalue : PressureStream.meanPressure d (ell z.2.1 * a) (ell z.2.1 * b) M
      (mul_lt_mul_of_pos_left hab (hl _ hz)) v g z =
      VariableGaugeMean.meanPressure d a b M hab ell v f z := by
    rw [VariableGaugeMean.meanPressure_eq_fixed hab d M ell v f z (hl _ hz)]
    exact PhysicalMeanDomain.meanPressure_fiberLocal d _ _ M _ v g f z.2.1 (fun _ _ => rfl) z.1
        z.2.2
  apply PressureStream.meanPressure_supported (M := M) (mul_pos (hl _ hz) ha)
    (mul_lt_mul_of_pos_left hab (hl _ hz)) hd v hg hgs
  exact fun hh => hn (hvalue.symm.trans hh)

theorem reconstructState_pressure_supported (g : VariableGaugeMean.GaugeData S)
    (C : CorrectionState.Context (PressureStream.Lift S)) (s : CorrectionState.State
        (PressureStream.Lift S))
    (n : ℕ) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) {U : Set S} (hU : IsOpen U)
    (hl : ∀ t ∈ U, 0 < g.length n t)
    (hf : ContDiffOn ℝ ∞ (s.gr C n) (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (g.length n) U (s.gr C n))
        :
    VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (g.length n) U
      ((VariableGaugeMean.reconstructState g C s).pressure n) :=
  meanPressure_supported ha g.radial.inner_lt_outer hd (g.radial.frequency n) (g.length n)
    g.radial.radialDirection hU hl hf hs

theorem pressureAliasState_supported (g : VariableGaugeMean.GaugeData S)
    (C : CorrectionState.Context (PressureStream.Lift S)) (s : CorrectionState.State
        (PressureStream.Lift S))
    (n : ℕ) (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent) {U : Set S}
    (hl : ∀ t ∈ U, 0 < g.length n t) (theta : ℝ) (i : Fin 3) :
    VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (g.length n) U
      (fun z => VariableGaugeMean.pressureAliasState g C s n (z, theta) i) := by
  intro z hz hn
  fin_cases i
  · apply pressureAlias_supported ha g.radial.inner_lt_outer hd (g.radial.frequency n)
      (g.length n) g.radial.radialDirection (s.gr C n) U hl z hz
    exact neg_ne_zero.mp hn
  · exact (hn rfl).elim
  · exact (hn rfl).elim

end

end NavierStokes.GaugeStateCoherence
