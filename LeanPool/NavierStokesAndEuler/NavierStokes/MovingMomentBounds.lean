/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalRankDefect

/-!
# Actual moments on the moving profile strip

The moment map integrates the given fields. It preserves the epsilon
exponent using the same moving edge weight. The containing annulus is used
only to justify the actual integrals and local smoothness.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.MovingMomentBounds

open Set Filter MeasureTheory CorrectionState WeightedClasses MeanIncrementBounds
open VariableGaugeMean LocalSignedRequest
open scoped ContDiff Topology BigOperators

section Moments

variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

include hab

/-- A smooth radial multiplier is bounded on the actual moving strip by
the compact containing annulus supplied by the positive coordinate range. -/
theorem radialCoefficient_unweighted {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) :
    UnweightedClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) 0
      (fun _ x => q x.1) := by
  obtain ⟨a₀, b₀, R, _, _, _, hpositive, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  apply unweighted_of_finiteJetBounds _ _ (hq.comp contDiff_fst).contDiffOn
  intro m
  obtain ⟨C, _, hb⟩ := WeightedRadialPrimitive.cutoff_finiteJet_bound
    (E := PressureStream.Plane × PressureStream.Plane) a₀ b₀ q hq m
  refine ⟨C, ?_⟩
  intro j hj x hx
  obtain ⟨hslow, hrad⟩ := (movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx
  have hpos := hpositive x.2.1 hslow
  apply hb j hj x
  constructor
  · apply (hleft _ hslow).trans
    simpa only [mul_comm] using ((lt_div_iff₀ hpos).mp hrad.1).le
  · apply le_trans ((div_lt_iff₀ hpos).mp hrad.2).le
    simpa only [mul_comm] using hright _ hslow

/-- Actual pressure-mass integration sends the moving mean class to the
slow class. The proof bounds the actual jets before integrating them. -/
theorem pressureMass_mem {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f) :
    UnweightedClass
      (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL) α
      (fun n => PressureStream.pressureMass (f n)) := by
  obtain ⟨a₀, b₀, R, _, hab₀, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have hfixed (n : ℕ) : PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) :=
    fun x hx hn => ⟨(hleft _ hx).trans (hs n x hx hn).1,
      (hs n x hx hn).2.trans (hright _ hx)⟩
  have hm := fun n => PhysicalMeanDomain.liftedPressureMass_contDiffOn U.isOpen (hf n) (hfixed n)
  have hsource := meanClass_moving_localBandJets U ha hcL hcR ε L hε hεone hL hf hs hclass
  have hb := hsource.liftedPressureMass hab₀.le U.isOpen hf hfixed
  refine ⟨fun _ _ _ => zero_le_one, ?_, ?_⟩
  · intro n
    exact (hm n).comp (MeanMomentBounds.insertSlow (P := PressureStream.Plane)).contDiff.contDiffOn
      (fun _ hp => hp)
  · intro m
    obtain ⟨C, hC, k, hbound⟩ := hb m
    refine ⟨C, hC, k, ?_⟩
    intro n s hsu j hj
    change ‖iteratedFDeriv ℝ j
      (MeanMomentBounds.liftedPressureMass (f n) ∘ MeanMomentBounds.insertSlow) s‖ ≤ _
    rw [MeanRankUpdate.iteratedFDeriv_comp_linear (PhysicalMeanDomain.slowDomain_open U.isOpen)
      (hm n) MeanMomentBounds.insertSlow j hsu]
    have hn := (iteratedFDeriv ℝ j (MeanMomentBounds.liftedPressureMass (f n))
      (MeanMomentBounds.insertSlow s)).norm_compContinuousLinearMap_le
        (fun _ => MeanMomentBounds.insertSlow (P := PressureStream.Plane))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hn
    have hp : ‖MeanMomentBounds.insertSlow (P := PressureStream.Plane)‖ ^ j ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) MeanMomentBounds.norm_insertSlow_le
    have h := hn.trans ((mul_le_of_le_one_right (norm_nonneg _) hp).trans
      (hbound n (MeanMomentBounds.insertSlow s) hsu j hj))
    simpa only [majorant, StripData.growth, PhysicalMeanDomain.localSlowStripData,
      MeanMomentBounds.slowStripData, inv_one, max_self, mul_one] using h

theorem radialMoment_mem {α : ℝ} {f : ℕ → Point → ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : ∀ n, SupportedGauge a b (qLength coord) U.carrier (f n))
    (hclass : MeanClass (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α f)
    (k : ℕ) :
    UnweightedClass
      (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL) α
      (radialMoment k f) := by
  have hR := radialCoefficient_unweighted U ha hab hcL hcR ε L hε hεone hL (contDiff_id.pow k)
  have hweighted : MeanClass
      (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) α
      (fun n x => x.1 ^ k * f n x) := by
    have he := hR.mul hclass
    simp only [one_mul, zero_add, id_eq] at he
    exact he
  exact pressureMass_mem U ha hab hcL hcR ε L hε hεone hL
    (fun n => (contDiffOn_fst.pow k).mul (hf n))
    (fun n x hx hn => hs n x hx (right_ne_zero_of_mul hn)) hweighted


end Moments

open Set Filter MeasureTheory CorrectionState WeightedClasses MeanIncrementBounds
open VariableGaugeMean LocalSignedRequest
open scoped ContDiff Topology BigOperators

section Support

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Support, given by `∀ n, SupportedGauge a b ell U (f n)`. -/
def Support (a b : ℝ) (ell : S → ℝ) (U : Set S) (f : ScalarField (PressureStream.Lift S)) : Prop :=
  ∀ n, SupportedGauge a b ell U (f n)

namespace Support

variable {a b : ℝ} {ell : S → ℝ} {U : Set S} {f g : ScalarField (PressureStream.Lift S)}

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem add (hf : Support a b ell U f) (hg : Support a b ell U g) : Support a b ell U (f + g) := by
  intro n x hx hn
  by_cases hz : f n x = 0
  · exact hg n x hx (by simpa only [Pi.add_apply, hz, zero_add] using hn)
  · exact hf n x hx hz

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem neg (hf : Support a b ell U f) : Support a b ell U (-f) :=
  fun n x hx hn => hf n x hx (neg_ne_zero.mp hn)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sub (hf : Support a b ell U f) (hg : Support a b ell U g) : Support a b ell U (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem mul_left (hf : Support a b ell U f) (g : ScalarField (PressureStream.Lift S)) :
    Support a b ell U (g * f) := fun n x hx hn => hf n x hx (right_ne_zero_of_mul hn)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem mul_right (hf : Support a b ell U f) (g : ScalarField (PressureStream.Lift S)) :
    Support a b ell U (f * g) := fun n x hx hn => hf n x hx (left_ne_zero_of_mul hn)

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem smul (hf : Support a b ell U f) (r : ℝ) : Support a b ell U (r • f) :=
  fun n x hx hn => hf n x hx (right_ne_zero_of_mul hn)

theorem directional (hf : Support a b ell U f) (hU : IsOpen U) (hl : ContinuousOn ell U)
    (v : PressureStream.Lift S) : Support a b ell U (fun n x => fderiv ℝ (f n) x v) :=
  fun n => fderiv_apply_supportedGauge hU hl (hf n) (fun _ => v)

theorem dr (hf : Support a b ell U f) (hU : IsOpen U) (hl : ContinuousOn ell U)
    (o : Operators (PressureStream.Lift S)) : Support a b ell U (o.dr f) := by
  have hh := (hf.directional hU hl o.eR).add
    ((hf.directional hU hl o.vR).mul_left (fun n x => o.radialFrequency n * o.radialProfile x))
  convert! hh using 1
  funext n x
  simp only [Operators.dr, graphDerivative, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  ring

theorem dz (hf : Support a b ell U f) (hU : IsOpen U) (hl : ContinuousOn ell U)
    (o : Operators (PressureStream.Lift S)) : Support a b ell U (o.dz f) :=
  (hf.directional hU hl o.eZ).mul_left (fun n _ => o.epsilon n)

theorem time (hf : Support a b ell U f) (hU : IsOpen U) (hl : ContinuousOn ell U)
    (o : Operators (PressureStream.Lift S)) : Support a b ell U (o.time f) :=
  ((hf.directional hU hl o.eT).mul_left (fun n _ => o.epsilon n)).neg.add
    ((hf.directional hU hl o.vT).mul_left (fun n _ => o.fastCoefficient n))

theorem radialDiv (hf : Support a b ell U f) (hU : IsOpen U) (hl : ContinuousOn ell U)
    (o : Operators (PressureStream.Lift S)) (r : ℝ) : Support a b ell U (o.radialDiv r f) :=
  (hf.dr hU hl o).add ((hf.mul_left o.invRadius).smul r)

theorem viscosity (hf : Support a b ell U f) (hU : IsOpen U) (hl : ContinuousOn ell U)
    (o : Operators (PressureStream.Lift S)) (r : ℝ) : Support a b ell U (o.viscosity r f) :=
  (((((hf.dr hU hl o).dr hU hl o).add ((hf.dr hU hl o).mul_left o.invRadius)).add
    ((hf.dz hU hl o).dz hU hl o)).sub
      (((hf.mul_left o.invRadius).mul_left o.invRadius).smul r)).mul_left (fun n _ => o.epsilon n)

end Support

/-- Supported triple data, collecting `radial`, `angular`, `axial`. -/
structure SupportedTriple (a b : ℝ) (ell : S → ℝ) (U : Set S)
    (m : Triple (PressureStream.Lift S)) : Prop where
  radial : Support a b ell U m.radial
  angular : Support a b ell U m.angular
  axial : Support a b ell U m.axial

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem SupportedTriple.updated {a b : ℝ} {ell : S → ℝ} {U : Set S}
    {m h : Triple (PressureStream.Lift S)} (hm : SupportedTriple a b ell U m)
    (hh : SupportedTriple a b ell U h) : SupportedTriple a b ell U (updated m h) :=
  ⟨hm.radial.add hh.radial, hm.angular.add hh.angular, hm.axial.add hh.axial⟩

theorem gr_support {a b : ℝ} {ell : S → ℝ} {U : Set S}
    (hU : IsOpen U) (hl : ContinuousOn ell U)
    (o : Operators (PressureStream.Lift S)) (base m : Triple (PressureStream.Lift S))
    (W : Fin 3 → Fin 3 → ScalarField (PressureStream.Lift S)) (hm : SupportedTriple a b ell U m)
    (hW : ∀ i j, Support a b ell U (W i j)) : Support a b ell U (gr o base m W) := by
  have hrr : Support a b ell U (radialRadial base m) :=
    ((hm.radial.mul_left base.radial).smul 2).add (hm.radial.mul_right m.radial)
  have hzr : Support a b ell U (axialRadial base m) :=
    ((hm.axial.mul_left base.radial).add (hm.radial.mul_right base.axial)).add
      (hm.radial.mul_right m.axial)
  have htt : Support a b ell U (radialAngular base m) :=
    ((hm.angular.mul_left base.angular).smul 2).add (hm.angular.mul_right m.angular)
  exact (((((hm.radial.time hU hl o).add ((hrr.add (hW 0 0)).radialDiv hU hl o 1)).add
    ((hzr.add (hW 2 0)).dz hU hl o)).sub ((htt.add (hW 1 1)).mul_left o.invRadius)).sub
      (hm.radial.viscosity hU hl o 1)).neg

end Support

section Remainders

open DefectIncrementBounds

variable {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)

include hab in
/-- Actual equation-(32) remainders gain their full exponent under the
moving moment map. Every covariance and differentiated mean term remains
in the source before integration. -/
theorem remainders_mem {o : Operators Point} {base m h : Triple Point} {κ H : ℝ}
    (hop : LocalRankDefect.LocalOperators U.carrier o)
    (hbs : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) base)
    (hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) m)
    (hhc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) h)
    (hms : SupportedTriple a b (qLength coord) U.carrier m)
    (hhs : SupportedTriple a b (qLength coord) U.carrier h)
    (W : Fin 3 → Fin 3 → CorrectionState.ScalarField Point) (hWc : ∀ i j, SmoothOn
        (PhysicalMeanDomain.slowDomain U.carrier) (W i j))
    (hWs : ∀ i j, Support a b (qLength coord) U.carrier (W i j))
    (ho : OperatorBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) o κ)
    (hb : BaseBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) base)
    (hm : MeanIncrementBounds.CumulativeBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone
        hL) m)
    (hh : IncrementBounds (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL) H h)
    (hH : 9 / 10 ≤ H) (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      (H + 9 / 10 - 2 * κ) (fun n x => DefectIncrementBounds.remainders o base m h W n x i) := by
  obtain ⟨a₀, b₀, R₀, ha₀, _, _, _, hleft, hright, _⟩ := qLength_reference_bounds U ha hab
  have hfixed {f : CorrectionState.ScalarField Point} (hs : Support a b (qLength coord) U.carrier
      f) :
      ∀ n, PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) := by
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hs n x hx hn).1, (hs n x hx hn).2.trans (hright _ hx)⟩
  have hml : LocalRankDefect.LocalTriple a₀ b₀ U.carrier m :=
    ⟨⟨hmc.radial, hfixed hms.radial⟩, ⟨hmc.angular, hfixed hms.angular⟩, ⟨hmc.axial, hfixed
        hms.axial⟩⟩
  have hhl : LocalRankDefect.LocalTriple a₀ b₀ U.carrier h :=
    ⟨⟨hhc.radial, hfixed hhs.radial⟩, ⟨hhc.angular, hfixed hhs.angular⟩, ⟨hhc.axial, hfixed
        hhs.axial⟩⟩
  have hwl (i j : Fin 3) : LocalRankDefect.LocalShell a₀ b₀ U.carrier (W i j) :=
    ⟨hWc i j, hfixed (hWs i j)⟩
  have hrc := actualRadialError_mem ho hb hm hh hH W
    (fun i j n => (hWc i j n).mono (fun x hx =>
      ((movingStrip_domain U a b cL cR ha hcL hcR ε L hε hεone hL x).mp hx).1))
  have hrl := LocalRankDefect.actualRadialError_localShell ha₀ U.isOpen hbs hml hhl hop W hwl
  have hl : ContinuousOn (qLength coord) U.carrier :=
    ((qLength_contDiffOn U.coord_pos U.coord_lt_one).mono (fun x hx => U.time_pos x
        hx)).continuousOn
  have hrs : Support a b (qLength coord) U.carrier (actualRadialError o base m h W) :=
    ((gr_support U.isOpen hl o base (updated m h) W (hms.updated hhs) hWs).sub
      (gr_support U.isOpen hl o base m W hms hWs)).sub
      (((hhs.angular.mul_left base.angular).smul 2).mul_left o.invRadius)
  have hts : Support a b (qLength coord) U.carrier (thetaQuadratic m h) :=
    ((hms.axial.mul_right h.angular).add (hhs.axial.mul_right m.angular)).add
      (hhs.axial.mul_right h.angular)
  have hzs : Support a b (qLength coord) U.carrier (axialQuadratic m h) :=
    ((hms.axial.mul_right h.axial).smul 2).add (hhs.axial.mul_right h.axial)
  have hP := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hrl.smooth hrs hrc 0
  have hP2 := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL hrl.smooth hrs hrc 2
  have hT := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL
    (LocalRankDefect.thetaQuadratic_localShell hml hhl).smooth hts (thetaQuadratic_mem ho hm hh hH)
        2
  have hZ := radialMoment_mem U ha hab hcL hcR ε L hε hεone hL
    (LocalRankDefect.axialQuadratic_localShell hml hhl).smooth hzs (axialQuadratic_mem ho hm hh hH)
        1
  fin_cases i
  · exact hP
  · exact hT
  · exact Class.sub hZ (Class.smul hP2 (1 / 2))

end Remainders

section RankDefect

variable {coord cL cR : ℝ} (U : SlowRegion coord)
    (g : GaugeData PressureStream.Plane) (r : RankData PressureStream.Plane)
    (ha : 0 < g.radial.inner) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (hell : ∀ n, g.length n = qLength coord)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (c : Context Point) (u : State Point)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)

include hell hg in
/-- The actual five-row rank stage gains the defect exponent on the
original moving strip. The row cancellation is derived from RankGeometry;
the pressure source and quadratic remainders are integrated literally. -/
theorem rankStage_defect_class {κ H : ℝ}
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbc : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : SupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (hWc : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, Support g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i
        j))
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial)
    (ho : OperatorBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
        hεone hL)
      c.operators κ)
    (hb : BaseBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
        hL) c.base)
    (hm : MeanIncrementBounds.CumulativeBounds
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL) u.mean)
    (hi : IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
        hεone hL)
      H (rankIncrementState g r axial c u)) (hH : 9 / 10 ≤ H) (i : Fin 3) :
    UnweightedClass (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      (H + 9 / 10 - 2 * κ) (fun n x => debt c (rankStageState g r axial c u) n x i) := by
  obtain ⟨a₀, b₀, R₀, ha₀, hab₀, _, _, hleft, hright, _⟩ :=
    qLength_reference_bounds U ha g.radial.inner_lt_outer
  have hl (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : a₀ ≤ r.length n x * r.inner :=
      by
    have hh := hg.gauge_left n x hx
    rw [hell n] at hh
    exact (hleft x hx).trans hh
  have hr (n : ℕ) (x : PressureStream.Plane) (hx : x ∈ U.carrier) : r.length n x * r.outer ≤ b₀ :=
      by
    have hh := hg.gauge_right n x hx
    rw [hell n] at hh
    exact hh.trans (hright x hx)
  have hfixed {f : ScalarField Point}
      (hs : Support g.radial.inner g.radial.outer (qLength coord) U.carrier f) :
      ∀ n, PhysicalMeanDomain.SupportedOn a₀ b₀ U.carrier (f n) := by
    intro n x hx hn
    exact ⟨(hleft _ hx).trans (hs n x hx hn).1, (hs n x hx hn).2.trans (hright _ hx)⟩
  have hml : LocalRankDefect.LocalTriple a₀ b₀ U.carrier u.mean :=
    ⟨⟨hmc.radial, hfixed hms.radial⟩, ⟨hmc.angular, hfixed hms.angular⟩,
      ⟨hmc.axial, hfixed hms.axial⟩⟩
  have hwl (i j : Fin 3) : LocalRankDefect.LocalShell a₀ b₀ U.carrier (u.covariance i j) :=
    ⟨hWc i j, hfixed (hWs i j)⟩
  have hir := hg.increment_localTriple ha₀ hab₀ U.isOpen hl hr axial
  have his : SupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier
      (rankIncrementState g r axial c u) := by
    have hcontain (n : ℕ) {f : Point → ℝ}
        (hs : SupportedGauge r.inner r.outer (r.length n) U.carrier f) :
        SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier f := by
      intro z hz hn
      obtain ⟨hzl, hzr⟩ := hs z hz hn
      have hgl := hg.gauge_left n z.2.1 hz
      have hgr := hg.gauge_right n z.2.1 hz
      rw [hell n] at hgl hgr
      exact ⟨hgl.trans hzl, hzr.trans hgr⟩
    exact ⟨fun n => hcontain n (hg.increment_supportedGauge ha₀ hab₀ U.isOpen hl hr axial n).1,
      fun n => hcontain n (hg.increment_supportedGauge ha₀ hab₀ U.isOpen hl hr axial n).2.1,
      fun n => hcontain n (hg.increment_supportedGauge ha₀ hab₀ U.isOpen hl hr axial n).2.2⟩
  have hrem := remainders_mem U ha g.radial.inner_lt_outer hcL hcR ε L hε hεone hL hop hbc hmc
    hir.smooth hms his u.covariance hWc hWs ho hb hm hi hH i
  apply LinearWaveBounds.class_congr hrem
  intro n x hx
  exact congrArg (fun v : Fin 3 → ℝ => v i)
    (hg.debt_eq_remainders ha₀ hab₀ U.isOpen hl hr axial hop hbc hml hwl hV hG n hx).symm

include hell hg in
theorem rankStage_defectBounds {κ H σ : ℝ}
    (hop : LocalRankDefect.LocalOperators U.carrier c.operators)
    (hbc : SmoothTriple (LocalRankDefect.positiveDomain U.carrier) c.base)
    (hmc : SmoothTriple (PhysicalMeanDomain.slowDomain U.carrier) u.mean)
    (hms : SupportedTriple g.radial.inner g.radial.outer (qLength coord) U.carrier u.mean)
    (hWc : ∀ i j, SmoothOn (PhysicalMeanDomain.slowDomain U.carrier) (u.covariance i j))
    (hWs : ∀ i j, Support g.radial.inner g.radial.outer (qLength coord) U.carrier (u.covariance i
        j))
    (hV : LocalRankDefect.IsSlowOn U.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn U.carrier c.base.axial)
    (ho : OperatorBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
        hεone hL)
      c.operators κ)
    (hb : BaseBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone
        hL) c.base)
    (hm : MeanIncrementBounds.CumulativeBounds
      (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε hεone hL) u.mean)
    (hi : IncrementBounds (movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
        hεone hL)
      H (rankIncrementState g r axial c u)) (hH : 9 / 10 ≤ H)
    (hσ : 1 + σ ≤ H + 9 / 10 - 2 * κ) :
    DefectBounds (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      σ c (rankStageState g r axial c u) := by
  intro i
  exact (rankStage_defect_class U g r ha hcL hcR ε L hε hεone hL hell axial c u hg
    hop hbc hmc hms hWc hWs hV hG ho hb hm hi hH i).mono_exponent hσ

end RankDefect

end NavierStokes.MovingMomentBounds
