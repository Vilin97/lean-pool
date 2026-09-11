/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleExcluded
import LeanPool.NavierStokesAndEuler.NavierStokes.CycleMeanEquation
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCrossDefectClass
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
import LeanPool.NavierStokesAndEuler.NavierStokes.FiniteHeadClass

/-!
# Analytic preservation for the literal correction cycle

The wave inputs below are estimates and local identities for the two actual
constructed increments.  The full residual, mean, debt, covariance, and
stored-error conclusions are derived for `CycleState.step`.
-/

section

/-!
# Mean composition with the actual signed cross covariance

The cross covariance need not equal the requested stress on the finitely
many bands before the primary partition is complete.  This file retains
its literal difference and its radial divergence.  The composition below
has no `SignedMeanGain.NativeData` input.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.CrossBasedMeanComposition

open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators
open WeightedClasses MeanIncrementBounds CorrectionState SignedMeanGain

/-- Point: an abbreviation for `SignedMeanGain.Point`. -/
abbrev Point := SignedMeanGain.Point
/-- Scalar field: an abbreviation for `SignedMeanGain.ScalarField`. -/
abbrev ScalarField := SignedMeanGain.ScalarField

/-- The actual averaged cross covariance minus the requested physical
stress, before applying the radial divergence. -/
noncomputable def crossDefect (G : Geometry) (e : ℕ)
    (f X : ScalarField Point) : ScalarField Point :=
  StateMomentBalances.meanBar X - physicalSigma G e f

theorem meanBar_eq_sigma_add_defect (G : Geometry) (e : ℕ)
    (f X : ScalarField Point) :
    StateMomentBalances.meanBar X = physicalSigma G e f + crossDefect G e f X := by
  unfold crossDefect
  abel

theorem crossDefect_mem_of_cross (G : Geometry) (e : ℕ)
    (f X : ScalarField Point) (α : ℝ)
    (hcross : Agree G.strip.domain (StateMomentBalances.meanBar X) (physicalSigma G e f)) :
    MeanClass G.strip α (crossDefect G e f X) := by
  apply class_congr (MemClass.zero (fun n x hx => G.strip.zeta_nonneg x hx))
  intro n x hx
  simp only [crossDefect, Pi.sub_apply, hcross n hx, sub_self]

/-- A baseline weighted estimate and actual tail agreement suffice for
every exponent.  The finitely many earlier bands are retained, not set to zero. -/
theorem crossDefect_all_exponents_of_tail (G : Geometry) (e : ℕ)
    (f X : ScalarField Point) {α : ℝ}
    (hbase : MeanClass G.strip α (crossDefect G e f X)) (N : ℕ)
    (htail : ∀ n, N ≤ n → ∀ x ∈ G.strip.domain,
      StateMomentBalances.meanBar X n x = physicalSigma G e f n x) :
    ∀ β : ℝ, MeanClass G.strip β (crossDefect G e f X) := by
  apply FiniteHeadClass.meanClass_all_exponents hbase N
  intro n hn x hx
  exact sub_eq_zero.mpr (htail n hn x hx)

/-- The physical cancellation keeps the radial divergence of the actual
cross defect.  No cancellation on the finite head is assumed. -/
theorem cross_cancels_with_defect (G : Geometry) (e : ℕ) (he : e = 2 ∨ e = 1)
    {f X : ScalarField Point} (hf : SmoothOn G.domain f)
    (hs : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (f n))
    (hX : MovingField G X)
    (hD : SmoothOn G.strip.domain (crossDefect G e f X))
    (n : ℕ) {x : Point} (hx : x ∈ G.strip.domain) :
    StateMomentBalances.meanBar f n x +
        StateMomentBalances.meanBar (G.operators.radialDiv (e : ℝ) X) n x =
      removedBump G e f n x + G.operators.radialDiv (e : ℝ) (crossDefect G e f X) n x := by
  rw [meanBar_radialDiv_on G.region.isOpen G.operators rfl
    (fun _ _ _ => rfl) hX.smooth hX.periodic (e : ℝ) n (G.strip_subset hx)]
  rw [meanBar_eq_sigma_add_defect G e f X]
  rw [G.operators.radialDiv_add G.strip.isOpen_domain (e : ℝ)
    (fun n => (physicalSigma_smooth G e hf hs n).mono G.strip_subset) hD n hx]
  have hc := physicalSigma_cancels G e he hf hs n hx
  simp only [Pi.add_apply]
  linarith

/-- Averaging the literal updated residual produces the removed moment
bump, the usual covariance/pressure remainder, and the cross defect. -/
theorem averaged_residual_decomposition_with_defect
    (G : Geometry) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point)
    (gaussian : Oscillation Point)
    (H : LocalData G c u w q gaussian) (S E : Tensor Point)
    (hS : ∀ i j, MovingField G (S i j))
    (hE : ∀ i j, MovingField G (E i j))
    (hX : covarianceIncrement u.oscillation w = S + E)
    (hDθ : SmoothOn G.strip.domain (crossDefect G 2 (u.thetaResidual c) (S 0 1)))
    (hDz : SmoothOn G.strip.domain (crossDefect G 1 (u.axialResidual c) (S 0 2))) :
    Agree G.strip.domain
      (StateMomentBalances.meanBar ((waveStage G.gauge c u w q gaussian).thetaResidual c))
      (removedBump G 2 (u.thetaResidual c)
        + StateMomentBalances.meanBar (thetaRemainderField G S E)
        + G.operators.radialDiv 2 (crossDefect G 2 (u.thetaResidual c) (S 0 1))) ∧
    Agree G.strip.domain
      (StateMomentBalances.meanBar ((waveStage G.gauge c u w q gaussian).axialResidual c))
      (removedBump G 1 (u.axialResidual c)
        + StateMomentBalances.meanBar
            (axialRemainderField G S E (pressureChange G.gauge c u w q gaussian))
        + G.operators.radialDiv 1 (crossDefect G 1 (u.axialResidual c) (S 0 2))) := by
  have hSs := fun i j n => ((hS i j).smooth n).mono G.strip_subset
  have hEs := fun i j n => ((hE i j).smooth n).mono G.strip_subset
  have hRestθ : SmoothOn G.domain (thetaRemainderField G S E) :=
    (MovingField.covariance_flux_smooth hE).1.add
      (SmoothOn.dz (hS 2 1).smooth G.domain_open G.operators)
  have hRestz : SmoothOn G.domain
      (axialRemainderField G S E (pressureChange G.gauge c u w q gaussian)) :=
    ((MovingField.covariance_flux_smooth hE).2.1.add
      (SmoothOn.dz (hS 2 2).smooth G.domain_open G.operators)).add
        (H.pressureChange_smooth.dz G.domain_open G.operators)
  obtain ⟨a,b,_,ha,_,_,_,hl,hr,_⟩ :=
    VariableGaugeMean.qLength_reference_bounds G.region G.patch.a_pos G.patch.a_lt_b
  have hlocal (i j) :
      LocalRankDefect.LocalShell a b G.region.carrier (S i j) :=
    ⟨(hS i j).smooth, ((hS i j).containing hl hr).supported⟩
  constructor
  · intro n x hx
    have hbar := G.average_congr (H.theta_split hSs hEs hX) n hx
    have hrad :=
      ((hlocal 0 1).radialDiv ha G.region.isOpen G.local_operators 2).smooth
    have hbump := cross_cancels_with_defect G 2 (Or.inl rfl) H.theta H.theta_support
      (hS 0 1) hDθ n hx
    rw [meanBar_add_on (H.theta.add hrad) hRestθ n (G.strip_subset hx),
        meanBar_add_on H.theta hrad n (G.strip_subset hx)] at hbar
    norm_num only [Nat.cast_ofNat] at hbump
    simp only [Pi.add_apply] at hbar hbump ⊢
    linarith
  · intro n x hx
    have hbar := G.average_congr (H.axial_split hSs hEs hX) n hx
    have hrad :=
      ((hlocal 0 2).radialDiv ha G.region.isOpen G.local_operators 1).smooth
    have hbump := cross_cancels_with_defect G 1 (Or.inr rfl) H.axial H.axial_support
      (hS 0 2) hDz n hx
    rw [meanBar_add_on (H.axial.add hrad) hRestz n (G.strip_subset hx),
        meanBar_add_on H.axial hrad n (G.strip_subset hx)] at hbar
    norm_num only [Nat.cast_ofNat] at hbump
    simp only [Pi.add_apply] at hbar hbump ⊢
    linarith

/-- The same four mean gains as the exact-cross theorem, allowing the
literal cross defects at the derivative-adjusted gain exponent. -/
theorem signed_mean_gain_of_cross_defects
    (G : Geometry) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : Assembly f)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hold : u.oscillation = oldField f a)
    (H : LocalData G c u (tangentField f a + curlField f a) q gaussian)
    (ho : OperatorBounds G.strip G.operators κ)
    (hX : ∀ i j, MovingField G (incrementTensor f a i j))
    (hS : ∀ i j, MovingField G (crossTensor f a i j))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip (σ - κ) c u)
    (hDθ : MeanClass G.strip (1 + σ + 17 / 100 + κ)
      (crossDefect G 2 (u.thetaResidual c) (crossTensor f a 0 1)))
    (hDz : MeanClass G.strip (1 + σ + 17 / 100 + κ)
      (crossDefect G 1 (u.axialResidual c) (crossTensor f a 0 2))) :
    let v := waveStage G.gauge c u (tangentField f a + curlField f a) q gaussian
    MeanClass G.strip (1 + σ - 2 * κ) (v.thetaResidual c) ∧
    MeanClass G.strip (1 + σ - 2 * κ) (v.axialResidual c) ∧
    MeanClass G.strip (1 + σ + 17 / 100) (StateMomentBalances.meanBar (v.thetaResidual c)) ∧
    MeanClass G.strip (1 + σ + 17 / 100) (StateMomentBalances.meanBar (v.axialResidual c)) := by
  dsimp only
  obtain ⟨hXi, hEi⟩ := signed_tensor_bounds hσ hκsmall f a
  have hEeq : remainderTensor f a = incrementTensor f a - crossTensor f a := by
    rw [incrementTensor_split]
    abel
  have hSeq : crossTensor f a = incrementTensor f a - remainderTensor f a := by
    rw [incrementTensor_split]
    abel
  have hEc : ∀ i j, MovingField G (remainderTensor f a i j) := by
    intro i j
    rw [hEeq]
    exact (hX i j).sub (hS i j)
  have hSi : TensorClass G.strip (1 + σ - κ) (crossTensor f a) := by
    intro i j
    rw [hSeq]
    exact Class.sub (hXi i j) ((hEi i j).mono_exponent (by linarith))
  have hactual : covarianceIncrement u.oscillation (tangentField f a + curlField f a) =
      crossTensor f a + remainderTensor f a := by
    rw [hold]
    exact incrementTensor_split f a
  have hactualClass : TensorClass G.strip (1 + σ - κ)
      (covarianceIncrement u.oscillation (tangentField f a + curlField f a)) := by
    simp only [hold]
    exact hXi
  have hp : MeanClass G.strip (1 + σ - 2 * κ)
      (pressureChange G.gauge c u (tangentField f a + curlField f a) q gaussian) := by
    convert! H.pressureChange_mem ho hactualClass using 1
    ring
  have htchange : MeanClass G.strip (1 + σ - 2 * κ)
      ((waveStage G.gauge c u (tangentField f a + curlField f a) q gaussian).thetaResidual c -
        u.thetaResidual c) := by
    have hh := thetaCovarianceChange_mem ho hactualClass
    have heq := waveStage_theta_change G.strip.isOpen_domain G.gauge c u
      (tangentField f a + curlField f a) q gaussian H.base H.mean H.covariance
      (fun i j => (hactualClass i j).smooth)
    rw [H.operators_eq] at heq
    convert! class_congr hh heq using 1
    ring
  have hzchange : MeanClass G.strip (1 + σ - 2 * κ)
      ((waveStage G.gauge c u (tangentField f a + curlField f a) q gaussian).axialResidual c -
        u.axialResidual c) := by
    have hh : MeanClass G.strip (1 + σ - 2 * κ)
        (axialCovarianceChange G.operators
          (covarianceIncrement u.oscillation (tangentField f a + curlField f a))) := by
      convert! axialCovarianceChange_mem ho hactualClass using 1
      ring
    have heq := waveStage_axial_change G.strip.isOpen_domain G.gauge c u
      (tangentField f a + curlField f a) q gaussian H.base H.mean H.covariance
      (fun i j => (hactualClass i j).smooth)
      (fun n => (H.pressure_smooth n).mono G.strip_subset) hp.smooth
    rw [H.operators_eq] at heq
    exact class_congr (hh.add ((ho.dz hp).mono_exponent (by linarith))) heq
  have hRestθ : MeanClass G.strip (1 + σ + 17 / 100)
      (thetaRemainderField G (crossTensor f a) (remainderTensor f a)) := by
    apply MemClass.add
    · convert! thetaCovarianceChange_mem ho hEi using 1
      ring
    · exact (ho.dz (hSi 2 1)).mono_exponent (by linarith)
  have hRestz : MeanClass G.strip (1 + σ + 17 / 100)
      (axialRemainderField G (crossTensor f a) (remainderTensor f a)
        (pressureChange G.gauge c u (tangentField f a + curlField f a) q gaussian)) := by
    apply MemClass.add
    · apply MemClass.add
      · convert! axialCovarianceChange_mem ho hEi using 1
        ring
      · exact (ho.dz (hSi 2 2)).mono_exponent (by linarith)
    · exact (ho.dz hp).mono_exponent (by linarith)
  have hRestθs : SmoothOn G.domain (thetaRemainderField G (crossTensor f a) (remainderTensor f a))
      :=
    (MovingField.covariance_flux_smooth hEc).1.add
      (SmoothOn.dz (hS 2 1).smooth G.domain_open G.operators)
  have hRestzs : SmoothOn G.domain (axialRemainderField G (crossTensor f a) (remainderTensor f a)
      (pressureChange G.gauge c u (tangentField f a + curlField f a) q gaussian)) :=
    ((MovingField.covariance_flux_smooth hEc).2.1.add
      (SmoothOn.dz (hS 2 2).smooth G.domain_open G.operators)).add
        (H.pressureChange_smooth.dz G.domain_open G.operators)
  have hdebt : ∀ i : Fin 3, UnweightedClass G.slowStrip (1 + σ - κ) (fun n z => debt c u n z i) :=
      by
    intro i
    convert! hd i using 1
    ring
  obtain ⟨hbθ, hbz⟩ := G.removed_bumps_mem c u H.operators_eq H.angular_flux H.axial_flux
    H.source H.reconstructed H.angular_mass H.axial_mass hdebt
  have hbar := averaged_residual_decomposition_with_defect G c u (tangentField f a + curlField f a)
    q gaussian H (crossTensor f a) (remainderTensor f a) hS hEc hactual hDθ.smooth hDz.smooth
  have hdθ : MeanClass G.strip (1 + σ + 17 / 100)
      (G.operators.radialDiv 2 (crossDefect G 2 (u.thetaResidual c) (crossTensor f a 0 1))) := by
    convert! ho.radialDiv hDθ 2 using 1
    ring
  have hdz : MeanClass G.strip (1 + σ + 17 / 100)
      (G.operators.radialDiv 1 (crossDefect G 1 (u.axialResidual c) (crossTensor f a 0 2))) := by
    convert! ho.radialDiv hDz 1 using 1
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply class_congr ((hθ.mono_exponent (by linarith)).add htchange)
    intro n x _
    simp only [Pi.sub_apply]
    ring
  · apply class_congr ((hz.mono_exponent (by linarith)).add hzchange)
    intro n x _
    simp only [Pi.sub_apply]
    ring
  · exact class_congr (((hbθ.mono_exponent (by
      linarith)).add (G.average_mem hRestθs hRestθ)).add hdθ) hbar.1
  · exact class_congr (((hbz.mono_exponent (by
      linarith)).add (G.average_mem hRestzs hRestz)).add hdz) hbar.2

open CorrectionStep VariableGaugeMean LocalSignedRequest

/-- Pressure, cumulative, and measured-debt bounds for the actual signed
stage.  Only the actual cross defect enters, without a native-selection record. -/
theorem bandSignedStage_mean_debt_of_cross_defects {ι : Type}
    (G : SignedMeanGain.Geometry)
    (c : Context Point) (u : State Point)
    {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : SignedMeanGain.Assembly f)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hold : u.oscillation = SignedMeanGain.oldField f a)
    (H : SignedMeanGain.LocalData G c u
      (SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a) q gaussian)
    (ho : OperatorBounds G.strip G.operators κ)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain G.region.carrier) c.base)
    (hm : GaugeDebtIncrement.RegularTriple G.region G.patch.a G.patch.b u.mean)
    (hW : ∀ i j, GaugeDebtIncrement.Regular G.region G.patch.a G.patch.b (u.covariance i j))
    (hX : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor f a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor f a i j))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip (σ - κ) c u)
    (hDθ : MeanClass G.strip (1 + σ + 17 / 100 + κ)
      (crossDefect G 2 (u.thetaResidual c) (crossTensor f a 0 1)))
    (hDz : MeanClass G.strip (1 + σ + 17 / 100 + κ)
      (crossDefect G 1 (u.axialResidual c) (crossTensor f a 0 2))) :
    let v := SignedMeanGain.waveStage G.gauge c u
      (SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a) q gaussian
    MeanClass G.strip (1+σ-2*κ) (v.pressure - u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip v ∧
    MeanClass G.strip (1+σ-2*κ) (v.thetaResidual c) ∧
    MeanClass G.strip (1+σ-2*κ) (v.axialResidual c) ∧
    MeanClass G.strip (1+σ+17/100) (meanBar (v.thetaResidual c)) ∧
    MeanClass G.strip (1+σ+17/100) (meanBar (v.axialResidual c)) ∧
    DefectBounds G.slowStrip (σ-2*κ) c v := by
  let w := SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a
  let v := SignedMeanGain.waveStage G.gauge c u w q gaussian
  have hXT : SignedMeanGain.TensorClass G.strip (1+σ-κ)
      (SignedMeanGain.covarianceIncrement u.oscillation w) := by
    simpa only [hold, w, SignedMeanGain.incrementTensor] using
      (SignedMeanGain.signed_tensor_bounds hσ hκsmall f a).1
  have hXR : ∀ i j, GaugeDebtIncrement.Regular G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j) := by
    intro i j
    have hf := hX i j
    change GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.incrementTensor f a i j) at hf
    rw [hold]
    exact ⟨hf.smooth, hf.supported⟩
  have hpressure : MeanClass G.strip (1+σ-2*κ) (SignedMeanGain.pressureChange G.gauge c u w q
      gaussian) := by
    simpa only [show 1+σ-κ-κ = 1+σ-2*κ by ring] using H.pressureChange_mem ho hXT
  have hc : OperatorBounds G.strip c.operators κ := by simpa only [H.operators_eq] using ho
  have hop : LocalRankDefect.LocalOperators G.region.carrier c.operators := by
    rw [H.operators_eq]
    exact G.local_operators
  have hdebt := GaugeDebtIncrement.waveStage_defectBounds G.region G.patch.a_pos G.patch.a_lt_b
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one
    G.gauge c u w q gaussian hop hbase hm hW hXR hc hXT
    (show σ-2*κ ≤ σ-κ by linarith) (show 1+(σ-2*κ) ≤ (1+σ-κ)-κ by linarith) hd
  have hgain := signed_mean_gain_of_cross_defects G c u hσ hκ hκsmall f a
    q gaussian hold H ho hX hS hθ hz hd hDθ hDz
  have hcum : CorrectionState.CumulativeBounds G.strip v :=
    gaugeWaveStage_cumulative G.gauge c u w q ⟨0,gaussian,0⟩ hu hpressure (by linarith)
  exact ⟨hpressure, hcum, hgain.1, hgain.2.1, hgain.2.2.1, hgain.2.2.2, hdebt⟩

/-- Exact cross identities recover the original signed-stage conclusion
without the normalized-domain native-selection assumption. -/
theorem bandSignedStage_mean_debt_of_cross {ι : Type}
    (G : SignedMeanGain.Geometry)
    (c : Context Point) (u : State Point)
    {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : SignedMeanGain.Assembly f)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hold : u.oscillation = SignedMeanGain.oldField f a)
    (H : SignedMeanGain.LocalData G c u
      (SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a) q gaussian)
    (ho : OperatorBounds G.strip G.operators κ)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hbase : SmoothTriple (LocalRankDefect.positiveDomain G.region.carrier) c.base)
    (hm : GaugeDebtIncrement.RegularTriple G.region G.patch.a G.patch.b u.mean)
    (hW : ∀ i j, GaugeDebtIncrement.Regular G.region G.patch.a G.patch.b (u.covariance i j))
    (hX : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor f a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor f a i j))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip (σ - κ) c u)
    (hcrossθ : Agree G.strip.domain (StateMomentBalances.meanBar (crossTensor f a 0 1))
      (physicalSigma G 2 (u.thetaResidual c)))
    (hcrossz : Agree G.strip.domain (StateMomentBalances.meanBar (crossTensor f a 0 2))
      (physicalSigma G 1 (u.axialResidual c))) :
    let v := SignedMeanGain.waveStage G.gauge c u
      (SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a) q gaussian
    MeanClass G.strip (1+σ-2*κ) (v.pressure - u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip v ∧
    MeanClass G.strip (1+σ-2*κ) (v.thetaResidual c) ∧
    MeanClass G.strip (1+σ-2*κ) (v.axialResidual c) ∧
    MeanClass G.strip (1+σ+17/100) (meanBar (v.thetaResidual c)) ∧
    MeanClass G.strip (1+σ+17/100) (meanBar (v.axialResidual c)) ∧
    DefectBounds G.slowStrip (σ-2*κ) c v := by
  exact bandSignedStage_mean_debt_of_cross_defects G c u hσ hκ hκsmall f a
    q gaussian hold H ho hu hbase hm hW hX hS hθ hz hd
    (crossDefect_mem_of_cross G 2 (u.thetaResidual c) (crossTensor f a 0 1) _ hcrossθ)
    (crossDefect_mem_of_cross G 1 (u.axialResidual c) (crossTensor f a 0 2) _ hcrossz)

section MeanCycle
variable {ι : Type} (G : SignedMeanGain.Geometry)
    (c : Context Point) (u : State Point)
    (w₁ : Oscillation Point) (q₁ : OscillatoryScalar Point) (e₁ : Oscillation Point)
    {P : ι → ℕ → Point → ℝ} {σ κ : ℝ}
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25) (1 / 2 + σ - κ) (1 + σ - 2 * κ))
    (a : SignedMeanGain.Assembly f)
    (q₂ : OscillatoryScalar Point) (e₂ : Oscillation Point)

local notation "u₁" => SignedMeanGain.waveStage G.gauge c u w₁ q₁ e₁
local notation "w₂" => SignedMeanGain.tangentField f a + SignedMeanGain.curlField f a
local notation "u₂" => SignedMeanGain.waveStage G.gauge c u₁ w₂ q₂ e₂

/-- The two actual wave updates, temporal inverse, and rank solve form one
mean/debt gain. All intermediate residual and flux regularity is derived
from the original primitive fields and the actual covariance increments. -/
theorem fourStage_mean_gain_of_cross_defects
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hop : c.operators = G.operators)
    (ho : OperatorBounds G.strip G.operators κ) (hb : BaseBounds G.strip c.base)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    (hmθ : ∀ n z, z ∈ G.region.carrier → radialMoment 2 u.mean.angular n z = 0)
    (hmz : ∀ n z, z ∈ G.region.carrier → radialMoment 1 u.mean.axial n z = 0)
    (hθ : MeanClass G.strip (1 + σ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip σ c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w₁ i j))
    (hX₁class : SignedMeanGain.TensorClass G.strip (1 + σ)
      (SignedMeanGain.covarianceIncrement u.oscillation w₁))
    (hX₂ : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor f a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor f a i j))
    (hold : (u₁).oscillation = SignedMeanGain.oldField f a)
    (hDθ : MeanClass G.strip (1 + σ + 17 / 100 + κ)
      (crossDefect G 2 ((u₁).thetaResidual c) (crossTensor f a 0 1)))
    (hDz : MeanClass G.strip (1 + σ + 17 / 100 + κ)
      (crossDefect G 1 ((u₁).axialResidual c) (crossTensor f a 0 2)))
    (r : RankData PressureStream.Plane) (h : ℝ) (index : ℕ → ℕ)
    (axial : PressureStream.Plane × PressureStream.Plane)
    (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ G.slow n)
    (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^
        (1 + h))
    (hV : LocalRankDefect.IsSlowOn G.region.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn G.region.carrier c.base.axial)
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c
      (temporalStageState G.gauge h index axial c u₂))
    {A₀ B₀ : ℝ} (hparam : RankStateBounds.NormalizedParameters G.coord A₀ B₀ r G.region.carrier)
    (hB : B₀ ≠ 0) (hleft : G.patch.a < r.inner) (hright : r.outer < G.patch.b) :
    let t := temporalStageState G.gauge h index axial c u₂
    let v := rankStageState G.gauge r axial c t
    MeanClass G.strip (1+σ-2*κ) ((u₂).thetaResidual c) ∧
    MeanClass G.strip (1+σ-2*κ) ((u₂).axialResidual c) ∧
    CorrectionState.CumulativeBounds G.strip u₂ ∧
    IncrementBounds G.strip (1+σ-2*κ) (temporalIncrementState G.gauge h index axial c u₂) ∧
    IncrementBounds G.strip (1+σ-2*κ) (rankIncrementState G.gauge r axial c t) ∧
    MeanClass G.strip (1+σ-2*κ) (v.pressure-u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip v ∧
    DefectBounds G.slowStrip (σ+1/10) c v ∧
    MeanClass G.strip (1+(σ+1/10)) (v.thetaResidual c) ∧
    MeanClass G.strip (1+(σ+1/10))
      (v.axialResidual c - fun n x => temporalAliasState G.gauge h index c u₂ n (x,0) 2) := by
  have hs : movingStripData G.region G.gauge.radial.inner G.gauge.radial.outer
      G.leftWeight G.rightWeight G.inner_pos G.left_pos G.right_pos
      G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one = G.strip := by
    simp only [SignedMeanGain.Geometry.strip, G.inner_eq, G.outer_eq]
  have H₀ : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c
      u := by
    simpa only [G.inner_eq, G.outer_eq] using H
  have HX₁ : ∀ i j, GaugeDebtIncrement.Regular G.region G.gauge.radial.inner G.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation w₁ i j) := by
    simpa only [G.inner_eq, G.outer_eq] using
      (fun i j => MeanStateRegularity.MovingField.regular (hX₁ i j))
  have hc : OperatorBounds G.strip c.operators κ := by simpa only [hop] using ho
  have hfirst := gaugeWaveStage_mean_from_covariance G.region G.gauge G.inner_pos G.exponent_pos
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one G.length_eq
    c u w₁ q₁ e₁ H.operators.regular H.base.smooth H₀.mean.regular
    (fun i j => MeanStateRegularity.MovingField.regular (H₀.covariance i j)) HX₁
    (hs.symm ▸ hc) (hs.symm ▸ hX₁class) hfixed (hs.symm ▸ hb) (hs.symm ▸ hu)
    (show 9/10 ≤ (1+σ)-κ by linarith) le_rfl
    (hs.symm ▸ hθ.mono_exponent (by linarith)) (hs.symm ▸ hz.mono_exponent (by linarith))
    (fun i => (hd i).mono_exponent (by linarith))
  rw [hs] at hfirst
  obtain ⟨hp₁, hu₁, hθ₁, hz₁, hd₁⟩ := hfirst
  have H₁ := H.waveStage G.gauge w₁ q₁ e₁ hX₁
  have HX₂ : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement (u₁).oscillation w₂ i j) := by
    simp only [hold]
    exact hX₂
  have Hsigned := MeanStateRegularity.localData G c u₁ w₂ q₂ e₂ H₁ hop HX₂
    (GaugeMomentBalances.reconstructState_idempotent _ _ _)
    (by simpa only [SignedMeanGain.waveStage_mean] using hmθ)
    (by simpa only [SignedMeanGain.waveStage_mean] using hmz)
  have hdebt₁ : DefectBounds G.slowStrip (σ-κ) c u₁ := by
    simpa only [DefectBounds, SignedMeanGain.Geometry.slowStrip,
      show 1+(σ-κ) = 1+σ-κ by ring] using hd₁
  obtain ⟨hp₂, hu₂, hθ₂, hz₂, hbarθ, hbarz, hd₂⟩ :=
    bandSignedStage_mean_debt_of_cross_defects G c u₁ hσ hκ hκsmall f a
      q₂ e₂ hold Hsigned ho hu₁ H.base.smooth H₁.mean.regular
      (fun i j => MeanStateRegularity.MovingField.regular (H₁.covariance i j)) hX₂ hS
      hθ₁ hz₁ hdebt₁ hDθ hDz
  have H₂ := H₁.waveStage G.gauge w₂ q₂ e₂ HX₂
  have H₂g : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c
      u₂ := by
    simpa only [G.inner_eq, G.outer_eq] using H₂
  have hθreg := H₂g.theta G.inner_pos G.gauge.radial.inner_lt_outer
  have hzreg := H₂g.axial_reconstructed G.inner_pos G.exponent_pos G.length_eq rfl
  have hmean := meanStages_constructed G.gauge r h index axial c u₂ G.region G.inner_pos
      G.exponent_pos
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one G.length_eq
    rfl hσ hκsmall hh hscale gap hgap hv hfast (hs.symm ▸ hc) (hs.symm ▸ hb) (hs.symm ▸ hu₂)
    H.operators.regular H.base.smooth hV hG H₂g.mean.regular.smooth
    ⟨H₂g.mean.radial.supported, H₂g.mean.angular.supported, H₂g.mean.axial.supported⟩
    (fun i j => (H₂g.covariance i j).smooth) (fun i j => (H₂g.covariance i j).supported)
    hθreg.smooth hzreg.smooth hθreg.periodic hzreg.periodic hθreg.supported hzreg.supported
    (hs.symm ▸ hθ₂) (hs.symm ▸ hz₂) (hs.symm ▸ hbarθ) (hs.symm ▸ hbarz)
    (by simpa only [DefectBounds, SignedMeanGain.Geometry.slowStrip,
      show 1+(σ-2*κ) = 1+σ-2*κ by ring] using hd₂)
    hg hparam hB (by simpa only [G.inner_eq] using hleft) (by simpa only [G.outer_eq] using hright)
  rw [hs] at hmean
  obtain ⟨hi, hr, hpmean, hcum, hdebt, htheta, haxial⟩ := hmean
  refine ⟨hθ₂, hz₂, hu₂, hi, hr, ?_, hcum, hdebt, htheta, haxial⟩
  apply class_congr (((hp₁.mono_exponent (by linarith)).add hp₂).add hpmean)
  intro n x hx
  change (rankStageState G.gauge r axial c (temporalStageState G.gauge h index axial c
      u₂)).pressure n x -
      u.pressure n x = ((u₁).pressure n x - u.pressure n x +
      ((u₂).pressure n x - (u₁).pressure n x)) +
      ((rankStageState G.gauge r axial c (temporalStageState G.gauge h index axial c u₂)).pressure
          n x -
      (u₂).pressure n x)
  ring

end MeanCycle

namespace CycleParameters

open CorrectionStep.CycleParameters

section ActualMean
variable {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency)
    (r : RankData PressureStream.Plane)
    (v : CycleCoefficients ι) (c : Context CyclePoint) (u : State CyclePoint)
    (primary : ι → HarmonicBlock CyclePoint) (P : ι → ℕ → CyclePoint → ℝ)
    {σ κ : ℝ} (hσ : 1 / 5 ≤ σ) (N : ℕ)
    (hprimary : ∀ l, (primary l).BandLimited N) (hband : CoefficientBands v)
    (hcp : ∀ l, SameCarrier (v.blocks l) (primary l))

variable (hcs : ∀ l, SameCarrier (v.blocks l) ((ofGeometry G h index axial particular signed
    r).signedBlock v c u l))
    (hold : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1 / 2)
      (fun l n x => (v.blocks l).velocity n i j x))
    (hdiff : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (17 / 25)
      (fun l n x => (v.blocks l).velocity n i j x - (primary l).velocity n i j x))
    (hpart : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1 / 2 + σ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).particularBlock v c u
          l).velocity n i j x))
    (htangent : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1 / 2 + σ - κ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).signedTangent v c u
          l).velocity n i j x))
    (hcurl : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1 + σ - 2 * κ)
      (fun l n x => ((ofGeometry G h index axial particular signed r).signedCurl v c u l).velocity
          n i j x))
    (hP0 : ∀ l n x, x ∈ G.strip.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ G.strip.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (v.blocks l).angularFrequency n ≠ 0)

local notation "F" => signedFamily (ofGeometry G h index axial particular signed r) v c u primary P
    hσ N hprimary hband hcp hcs
  hold hdiff hpart htangent hcurl hP0 hP1 hkp

/-- The complete measured-mean gain for `next`. The signed family is
computed from this cycle's actual particular, tangent, and curl blocks;
its first covariance estimate is derived from the same finite labels. -/
theorem mean_gain_from_waves_of_cross_defects
    (a : SignedMeanGain.Assembly F) (halabels : a.labels = v.labels)
    {axis : AxisymmetricAlias} (hrep : CycleRepresentation v u axis)
    (hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (v.blocks l))
    (hpartzero : ∀ l, HarmonicWaveInteraction.ZeroMode ((ofGeometry G h index axial particular
        signed r).particularBlock v c u l))
    (hsold : LabelSumBounds.SupportedOscillations a.slots a.label a.window a.auxiliary
        G.strip.domain
      (fun l => (v.blocks l).oscillation))
    (hspart : LabelSumBounds.SupportedOscillations a.slots a.label a.window a.auxiliary
        G.strip.domain
      (fun l => ((ofGeometry G h index axial particular signed r).particularBlock v c u
          l).oscillation))
    (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hop : c.operators = G.operators)
    (ho : OperatorBounds G.strip G.operators κ) (hb : BaseBounds G.strip c.base)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    (hmθ : ∀ n z, z ∈ G.region.carrier → radialMoment 2 u.mean.angular n z = 0)
    (hmz : ∀ n z, z ∈ G.region.carrier → radialMoment 1 u.mean.axial n z = 0)
    (hθ : MeanClass G.strip (1 + σ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip σ c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation ((ofGeometry G h index axial particular
          signed r).particularVelocity v c u) i j))
    (hX₂ : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor F a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor F a i j))
    (hDθ : MeanClass G.strip (1 + σ + 17 / 100 + κ)
      (crossDefect G 2 (((ofGeometry G h index axial particular signed r).afterParticular v c
          u).thetaResidual c)
        (crossTensor F a 0 1)))
    (hDz : MeanClass G.strip (1 + σ + 17 / 100 + κ)
      (crossDefect G 1 (((ofGeometry G h index axial particular signed r).afterParticular v c
          u).axialResidual c)
        (crossTensor F a 0 2)))
    (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ G.slow n)
    (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^
        (1 + h))
    (hV : LocalRankDefect.IsSlowOn G.region.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn G.region.carrier c.base.axial)
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c ((ofGeometry G h index axial
        particular signed r).afterTemporal v c u))
    {A₀ B₀ : ℝ} (hparam : RankStateBounds.NormalizedParameters G.coord A₀ B₀ r G.region.carrier)
    (hB : B₀ ≠ 0) (hleft : G.patch.a < r.inner) (hright : r.outer < G.patch.b) :
    MeanClass G.strip (1+σ-2*κ)
      (((ofGeometry G h index axial particular signed r).afterSigned v c u).thetaResidual c) ∧
    MeanClass G.strip (1+σ-2*κ)
      (((ofGeometry G h index axial particular signed r).afterSigned v c u).axialResidual c) ∧
    CorrectionState.CumulativeBounds G.strip ((ofGeometry G h index axial particular signed
        r).afterSigned v c u) ∧
    IncrementBounds G.strip (1+σ-2*κ) ((ofGeometry G h index axial particular signed
        r).temporalIncrement v c u) ∧
    IncrementBounds G.strip (1+σ-2*κ) ((ofGeometry G h index axial particular signed
        r).rankIncrement v c u) ∧
    MeanClass G.strip (1+σ-2*κ) (((ofGeometry G h index axial particular signed r).next v c
        u).pressure-u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip ((ofGeometry G h index axial particular signed r).next
        v c u) ∧
    DefectBounds G.slowStrip (σ+1/10) c ((ofGeometry G h index axial particular signed r).next v c
        u) ∧
    MeanClass G.strip (1+(σ+1/10)) (((ofGeometry G h index axial particular signed r).next v c
        u).thetaResidual c) ∧
    MeanClass G.strip (1+(σ+1/10))
      (((ofGeometry G h index axial particular signed r).next v c u).axialResidual c - fun n x =>
          temporalAliasState G.gauge h index c
        ((ofGeometry G h index axial particular signed r).afterSigned v c u) n (x,0) 2) := by
  have hrep₀ : u.oscillation = LabelSumBounds.fieldSum a.labels (fun l => (v.blocks l).oscillation)
      := by
    rw [halabels]
    funext n x i
    exact hrep.velocity n x i
  have hcov := assembledCovarianceIncrement_mem (show (1:ℝ)/2 ≤ 1/2+σ by linarith)
    a.labels a.label a.injective a.level a.window a.window_continuous a.auxiliary
    v.blocks ((ofGeometry G h index axial particular signed r).particularBlock v c u)
        v.residualBand hband.velocityPressure
    ((ofGeometry G h index axial particular signed r).particularBlock_band v c u) (fun _ =>
        ⟨rfl,rfl,rfl⟩)
    (fun i j _ => hold i j) (fun i j _ => hpart i j) hzero hpartzero hP0 hP1 hkp hsold hspart u
        hrep₀
  have hcov' : SignedMeanGain.TensorClass G.strip (1+σ)
      (SignedMeanGain.covarianceIncrement u.oscillation ((ofGeometry G h index axial particular
          signed r).particularVelocity v c u)) := by
    simp only [halabels, particularVelocity, show (1:ℝ)/2+(1/2+σ) = 1+σ by ring] at hcov ⊢
    exact hcov
  have hrep₁ : ((ofGeometry G h index axial particular signed r).afterParticular v c u).oscillation
      = SignedMeanGain.oldField F a := by
    simpa only [SignedMeanGain.oldField, halabels, signedFamily] using (ofGeometry G h index axial
        particular signed r).beforeSignedBlock_represents v c u hrep
  have hw₂ : SignedMeanGain.tangentField F a + SignedMeanGain.curlField F a = (ofGeometry G h index
      axial particular signed r).signedVelocity v c u := by
    simpa only [SignedMeanGain.tangentField, SignedMeanGain.curlField, signedFamily, halabels] using
      ((ofGeometry G h index axial particular signed r).signedVelocity_split v c u).symm
  have hgain := fourStage_mean_gain_of_cross_defects G c u ((ofGeometry G h index axial particular
      signed r).particularVelocity v c u) ((ofGeometry G h index axial particular signed
          r).particularPressure v c u)
    ((ofGeometry G h index axial particular signed r).particularGaussian v c u) F a ((ofGeometry G
        h index axial particular signed r).signedPressure v c u) ((ofGeometry G h index axial
            particular signed r).signedGaussian v c u)
    hσ hκ hκsmall H hop ho hb hu hfixed hmθ hmz hθ hz hd hX₁ hcov' hX₂ hS hrep₁ hDθ hDz
    r h index axial hh hscale gap hgap hv hfast hV hG
    (by erw [hw₂]; exact hg) hparam hB hleft hright
  erw [hw₂] at hgain
  obtain ⟨hsθ, hsz, hscum, hi, hr, hpmean, hcum, hdebt, htheta, haxial⟩ := hgain
  exact ⟨hsθ, hsz, ⟨hscum.velocity, hscum.pressure⟩,
    hi, hr, hpmean, ⟨hcum.velocity, hcum.pressure⟩, hdebt, htheta, haxial⟩

/-- The complete cycle needs only one baseline class for each cross defect
and actual agreement after a fixed band.  Finite-head promotion retains
its contribution and preserves the original mean/debt gain. -/
theorem mean_gain_from_waves_of_finite_head
    (a : SignedMeanGain.Assembly F) (halabels : a.labels = v.labels)
    {axis : AxisymmetricAlias} (hrep : CycleRepresentation v u axis)
    (hzero : ∀ l, HarmonicWaveInteraction.ZeroMode (v.blocks l))
    (hpartzero : ∀ l, HarmonicWaveInteraction.ZeroMode ((ofGeometry G h index axial particular
        signed r).particularBlock v c u l))
    (hsold : LabelSumBounds.SupportedOscillations a.slots a.label a.window a.auxiliary
        G.strip.domain
      (fun l => (v.blocks l).oscillation))
    (hspart : LabelSumBounds.SupportedOscillations a.slots a.label a.window a.auxiliary
        G.strip.domain
      (fun l => ((ofGeometry G h index axial particular signed r).particularBlock v c u
          l).oscillation))
    (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hop : c.operators = G.operators)
    (ho : OperatorBounds G.strip G.operators κ) (hb : BaseBounds G.strip c.base)
    (hu : CorrectionState.CumulativeBounds G.strip u)
    (hfixed : (reconstructState G.gauge c u).pressure = u.pressure)
    (hmθ : ∀ n z, z ∈ G.region.carrier → radialMoment 2 u.mean.angular n z = 0)
    (hmz : ∀ n z, z ∈ G.region.carrier → radialMoment 1 u.mean.axial n z = 0)
    (hθ : MeanClass G.strip (1 + σ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip σ c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation ((ofGeometry G h index axial particular
          signed r).particularVelocity v c u) i j))
    (hX₂ : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor F a i j))
    (hS : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor F a i j))
    {αθ αz : ℝ}
    (hDθ : MeanClass G.strip αθ
      (crossDefect G 2 (((ofGeometry G h index axial particular signed r).afterParticular v c
          u).thetaResidual c)
        (crossTensor F a 0 1)))
    (hDz : MeanClass G.strip αz
      (crossDefect G 1 (((ofGeometry G h index axial particular signed r).afterParticular v c
          u).axialResidual c)
        (crossTensor F a 0 2)))
    (Ncross : ℕ)
    (htailθ : ∀ n, Ncross ≤ n → ∀ x ∈ G.strip.domain,
      StateMomentBalances.meanBar (crossTensor F a 0 1) n x =
        physicalSigma G 2 (((ofGeometry G h index axial particular signed r).afterParticular v c
            u).thetaResidual c) n x)
    (htailz : ∀ n, Ncross ≤ n → ∀ x ∈ G.strip.domain,
      StateMomentBalances.meanBar (crossTensor F a 0 2) n x =
        physicalSigma G 1 (((ofGeometry G h index axial particular signed r).afterParticular v c
            u).axialResidual c) n x)
    (hh : 0 ≤ h) (hscale : ∀ n, ChartScales.S n ≤ G.slow n)
    (gap : ℕ) (hgap : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap)
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hfast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^
        (1 + h))
    (hV : LocalRankDefect.IsSlowOn G.region.carrier c.base.angular)
    (hG : LocalRankDefect.IsSlowOn G.region.carrier c.base.axial)
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c ((ofGeometry G h index axial
        particular signed r).afterTemporal v c u))
    {A₀ B₀ : ℝ} (hparam : RankStateBounds.NormalizedParameters G.coord A₀ B₀ r G.region.carrier)
    (hB : B₀ ≠ 0) (hleft : G.patch.a < r.inner) (hright : r.outer < G.patch.b) :
    MeanClass G.strip (1+σ-2*κ)
      (((ofGeometry G h index axial particular signed r).afterSigned v c u).thetaResidual c) ∧
    MeanClass G.strip (1+σ-2*κ)
      (((ofGeometry G h index axial particular signed r).afterSigned v c u).axialResidual c) ∧
    CorrectionState.CumulativeBounds G.strip ((ofGeometry G h index axial particular signed
        r).afterSigned v c u) ∧
    IncrementBounds G.strip (1+σ-2*κ) ((ofGeometry G h index axial particular signed
        r).temporalIncrement v c u) ∧
    IncrementBounds G.strip (1+σ-2*κ) ((ofGeometry G h index axial particular signed
        r).rankIncrement v c u) ∧
    MeanClass G.strip (1+σ-2*κ) (((ofGeometry G h index axial particular signed r).next v c
        u).pressure-u.pressure) ∧
    CorrectionState.CumulativeBounds G.strip ((ofGeometry G h index axial particular signed r).next
        v c u) ∧
    DefectBounds G.slowStrip (σ+1/10) c ((ofGeometry G h index axial particular signed r).next v c
        u) ∧
    MeanClass G.strip (1+(σ+1/10)) (((ofGeometry G h index axial particular signed r).next v c
        u).thetaResidual c) ∧
    MeanClass G.strip (1+(σ+1/10))
      (((ofGeometry G h index axial particular signed r).next v c u).axialResidual c - fun n x =>
          temporalAliasState G.gauge h index c
        ((ofGeometry G h index axial particular signed r).afterSigned v c u) n (x,0) 2) := by
  exact mean_gain_from_waves_of_cross_defects G h index axial particular signed r
    v c u primary P hσ N hprimary hband hcp hcs hold hdiff hpart htangent hcurl
    hP0 hP1 hkp a halabels hrep hzero hpartzero hsold hspart hκ hκsmall
    H hop ho hb hu hfixed hmθ hmz hθ hz hd hX₁ hX₂ hS
    (crossDefect_all_exponents_of_tail G 2 _ _ hDθ Ncross htailθ _)
    (crossDefect_all_exponents_of_tail G 1 _ _ hDz Ncross htailz _)
    hh hscale gap hgap hv hfast hV hG hg hparam hB hleft hright

end ActualMean

end CycleParameters

end NavierStokes.CrossBasedMeanComposition

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.CorrectionAnalyticStep

open Set Filter Function
open WeightedClasses MeanIncrementBounds CorrectionState CorrectionStep
open VariableGaugeMean LocalSignedRequest
open scoped ContDiff Topology BigOperators

/-- Point: an abbreviation for `CorrectionStep.CyclePoint`. -/
abbrev Point := CorrectionStep.CyclePoint

/-- Outputs of the two native constructions, on their literal current
source and request.  No complete updated residual or mean estimate is an
input to this record. -/
structure WaveData {ι : Type} (G : SignedMeanGain.Geometry)
    (p : CycleParameters ι) (v : CycleCoefficients ι) (c : Context Point) (u : State Point)
    (P : ι → ℕ → Point → ℝ) (S : ι → ℕ → Set Point) (σ κ : ℝ) : Prop where
  carrier : ∀ l, SameCarrier ((v).blocks l) ((p).signedBlock v c u l)
  particular : ∀ i j, LabelSumBounds.UniformWaveClass (p).strip P (1/2+σ)
    (fun l n z => ((p).particularBlock v c u l).velocity n i j z)
  tangent : ∀ i j, LabelSumBounds.UniformWaveClass (p).strip P (1/2+σ-κ)
    (fun l n z => ((p).signedTangent v c u l).velocity n i j z)
  curl : ∀ i j, LabelSumBounds.UniformWaveClass (p).strip P (1+σ-2*κ)
    (fun l n z => ((p).signedCurl v c u l).velocity n i j z)
  particularPressure : ∀ j, LabelSumBounds.UniformWaveClass (p).strip P (1+σ)
    (fun l n z => ((p).particularBlock v c u l).pressure n j z)
  signedPressure : ∀ j, LabelSumBounds.UniformWaveClass (p).strip P (1+σ-κ)
    (fun l n z => ((p).signedBlock v c u l).pressure n j z)
  particularSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (((p).particularBlock v c u l).velocity n i)
  signedSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (((p).signedBlock v c u l).velocity n i)
  particularPressureSmooth : ∀ l n, HarmonicResidual.SmoothCoefficients G.domain
    (((p).particularBlock v c u l).pressure n)
  signedPressureSmooth : ∀ l n, HarmonicResidual.SmoothCoefficients G.domain
    (((p).signedBlock v c u l).pressure n)
  particularGaussianSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (((p).particularGaussianBlock v c u l).velocity n i)
  signedGaussianSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (((p).signedGaussianBlock v c u l).velocity n i)
  particularSolenoidal : ∀ l,
    HarmonicWaveInteraction.ModeSolenoidal (p).strip c ((p).particularBlock v c u l)
  signedSolenoidal : ∀ l,
    HarmonicWaveInteraction.ModeSolenoidal (p).strip c ((p).signedBlock v c u l)
  particularSupport : ∀ l, HarmonicSourceSupport.InputSupportOn G.domain (S l)
    ((p).particularBlock v c u l) ((p).particularGaussianBlock v c u l).velocity 0
  signedSupport : ∀ l, HarmonicSourceSupport.InputSupportOn G.domain (S l)
    ((p).signedBlock v c u l) ((p).signedGaussianBlock v c u l).velocity 0
  particularGaussian : ∀ β i j, LabelSumBounds.UniformClass (p).strip
    (fun _ _ z => Real.sqrt ((p).strip.zeta z)) β
    (fun l n z => ((p).particularGaussianBlock v c u l).velocity n i j z)
  signedGaussian : ∀ β i j, LabelSumBounds.UniformClass (p).strip
    (fun _ _ z => Real.sqrt ((p).strip.zeta z)) β
    (fun l n z => ((p).signedGaussianBlock v c u l).velocity n i j z)
  particularField : WaveStateRegularity.AngularSmooth G.domain ((p).particularVelocity v c u)
  signedField : WaveStateRegularity.AngularSmooth G.domain ((p).signedVelocity v c u)
  particularPressureField : ∀ n, ContDiffOn ℝ ∞ ((p).particularPressure v c u n)
    (G.domain ×ˢ (univ : Set ℝ))
  signedPressureField : ∀ n, ContDiffOn ℝ ∞ ((p).signedPressure v c u n)
    (G.domain ×ˢ (univ : Set ℝ))
  particularPeriodic : OscillationPeriodic G.region.carrier ((p).particularVelocity v c u)
  signedPeriodic : OscillationPeriodic G.region.carrier ((p).signedVelocity v c u)
  particularRadialSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
    ((p).particularVelocity v c u)
  signedRadialSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
    ((p).signedVelocity v c u)
  tangentField : WaveStateRegularity.AngularSmooth G.domain
    (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation))
  tangentPeriodic : OscillationPeriodic G.region.carrier
    (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation))
  tangentRadialSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
    (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation))
  particularLinear : ∀ i j, j ≠ 0 → LabelSumBounds.UniformWaveClass (p).strip P (1+σ-3*κ)
    (fun l n z =>
      (HarmonicResidual.residualBlock c u ((v).blocks l) ((v).gaussian l) ((v).aliasCoefficients
          l)).velocity n i j z +
      (HarmonicWaveInteraction.linearGoodBlock c ((v).blocks l) ((p).particularBlock v c u l)
        ((p).particularGaussianBlock v c u l).velocity).velocity n i j z)
  signedLinear : UniformHarmonicInteraction.UniformVelocity (p).strip P (1+σ-4*κ)
    (fun l => HarmonicWaveInteraction.linearGoodBlock c ((p).beforeSignedBlock v c u l)
      ((p).signedBlock v c u l) ((p).signedGaussianBlock v c u l).velocity)

namespace WaveData

variable {ι : Type} {G : SignedMeanGain.Geometry} {p : CycleParameters ι}
    {v : CycleCoefficients ι} {c : Context Point} {u : State Point}
    {P : ι → ℕ → Point → ℝ} {S : ι → ℕ → Set Point} {σ κ : ℝ}
    (W : WaveData G p v c u P S σ κ)

include W

/-- The signed exact coefficient is its tangent coefficient plus the
literal curl difference. -/
theorem signed (hκ : κ ≤ 1 / 2) : ∀ i j,
    LabelSumBounds.UniformWaveClass (p).strip P (1/2+σ-κ)
      (fun l n z => ((p).signedBlock v c u l).velocity n i j z) := by
  intro i j
  apply ((W.tangent i j).add ((W.curl i j).mono_exponent (by linarith))).congr
  intro l n z hz
  change ((p).signedTangent v c u l).velocity n i j z +
      (((p).signedBlock v c u l).velocity n i j z - ((p).signedTangent v c u l).velocity n i j z) =
          _
  ring

theorem particular_zero_germ (hS : ∀ l n, IsClosed (S l n))
    (l : ι) (n : ℕ) {z : Point} (hz : z ∈ G.domain) (hn : z ∉ S l n)
    (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    ((p).particularBlock v c u l).velocity n i j =ᶠ[𝓝 z] fun _ => 0 :=
  block_velocity_zero_germ_of_inputSupport G.domain_open (hS l) (W.particularSupport l)
    ((p).particularBlock_real v c u l).1 n hz hn i j hj

theorem signed_zero_germ (hS : ∀ l n, IsClosed (S l n))
    (l : ι) (n : ℕ) {z : Point} (hz : z ∈ G.domain) (hn : z ∉ S l n)
    (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    ((p).signedBlock v c u l).velocity n i j =ᶠ[𝓝 z] fun _ => 0 :=
  block_velocity_zero_germ_of_inputSupport G.domain_open (hS l) (W.signedSupport l)
    ((p).signedBlock_real v c u l).1 n hz hn i j hj

/-- The two tensor regularity inputs are consequences of the actual
finite wave fields, their radial support and their torus periodicity. -/
theorem covariance_moving
    (hu : WaveStateRegularity.AngularSmooth G.domain (u).oscillation)
    (hup : OscillationPeriodic G.region.carrier (u).oscillation) :
    (∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement (u).oscillation ((p).particularVelocity v c u) i j)) ∧
    (∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement ((p).afterParticular v c u).oscillation
        ((p).signedVelocity v c u) i j)) := by
  refine ⟨covarianceIncrement_moving G.region hu W.particularField
    W.particularRadialSupport hup W.particularPeriodic, ?_⟩
  exact covarianceIncrement_moving G.region (hu.add W.particularField) W.signedField
    W.signedRadialSupport (hup.add W.particularPeriodic) W.signedPeriodic

end WaveData

/-- The fixed geometry and primitive operator data shared by every cycle.
The similarity data are identified with the same region, strip and gauge
used in the invariant, including the entire radial and free-torus fiber. -/
structure StaticData (G : SignedMeanGain.Geometry) (h : ℝ) (index : ℕ → ℕ)
    (axial : PressureStream.Plane × PressureStream.Plane) (r : RankData PressureStream.Plane)
    (c : Context Point) (κ : ℝ) where
  /-- Alias data of `StaticData`, of type `ActualCycleExcluded.SimilarityData`. -/
  aliasData : ActualCycleExcluded.SimilarityData
  coord : G.coord = 2 * aliasData.h
  region : HEq G.region aliasData.region
  inner : G.patch.a = aliasData.inner
  outer : G.patch.b = aliasData.outer
  gauge : G.gauge = aliasData.gauge
  strip : G.strip = aliasData.strip
  time : h = aliasData.h
  index_eq : index = aliasData.index
  operators_eq : c.operators = G.operators
  operators : OperatorBounds G.strip c.operators κ
  base : BaseBounds G.strip c.base
  axial_eq : axial = (G.axial, 0)
  temporal : c.operators.vT = (0, (0, TorusInverse.vector .temporal))
  fast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^ (1+h)
  angular_slow : LocalRankDefect.IsSlowOn G.region.carrier c.base.angular
  axial_slow : LocalRankDefect.IsSlowOn G.region.carrier c.base.axial
  /-- Rank exponent of `StaticData`, of type `ℝ`. -/
  rankExponent : ℝ
  /-- Rank coefficient of `StaticData`, of type `ℝ`. -/
  rankCoefficient : ℝ
  rankParameters : RankStateBounds.NormalizedParameters G.coord rankExponent rankCoefficient r
      G.region.carrier
  rankCoefficient_ne : rankCoefficient ≠ 0
  rank_left : G.patch.a < r.inner
  rank_right : r.outer < G.patch.b

namespace StaticData

variable {G : SignedMeanGain.Geometry} {h : ℝ} {index : ℕ → ℕ}
    {axial : PressureStream.Plane × PressureStream.Plane} {r : RankData PressureStream.Plane}
    {c : Context Point} {κ : ℝ} (D : StaticData G h index axial r c κ)

include D

theorem radius_pos {z : Point} (hz : z ∈ G.strip.domain) : 0 < c.operators.radius z := by
  rw [D.operators_eq]
  exact G.strip_radius_pos hz

theorem graph : ∃ slowTime : PressureStream.Plane × PressureStream.Plane,
    ∃ temporal : PressureStream.Plane,
      c.operators = graphOperators G.gauge.radial c.operators.epsilon c.operators.fastCoefficient
        axial slowTime temporal := by
  refine ⟨(G.time,0), G.temporal, ?_⟩
  rw [D.operators_eq, D.axial_eq]
  rfl

theorem time_nonneg : 0 ≤ h := by
  rw [D.time]
  exact D.aliasData.h_pos.le

theorem slow_scale : ∀ n, ChartScales.S n ≤ G.slow n := by
  have hs : G.slow = D.aliasData.slow := congrArg (fun s : StripData Point => s.slow) D.strip
  rw [hs]
  exact D.aliasData.slow_scale

theorem index_lower : ∀ n, ChartScales.nativeIndex h n ≤ index n + D.aliasData.gap := by
  simpa only [D.time, D.index_eq] using D.aliasData.index_lower

theorem compatible {ι : Type} (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters Point TorusInverse.Frequency) :
    ActualCycleExcluded.Compatible D.aliasData
      (CycleParameters.ofGeometry G h index axial particular signed r) c := by
  refine ⟨D.gauge, D.strip, D.time, D.index_eq, ?_, D.temporal⟩
  funext n
  simpa only [D.time, D.index_eq] using D.fast n

end StaticData

private theorem primitive_region_transport {coord coord' a b : ℝ}
    {U : SlowRegion coord} {V : SlowRegion coord'} {c : Context Point} {u : State Point}
    (hc : coord = coord') (hU : HEq U V)
    (H : MeanStateRegularity.PrimitiveData U a b c u) :
    MeanStateRegularity.PrimitiveData V a b c u := by
  subst coord'
  have hUV := eq_of_heq hU
  subst V
  exact H

private theorem moving_region_transport {coord coord' a b : ℝ}
    {U : SlowRegion coord} {V : SlowRegion coord'} {f : MeanIncrementBounds.Field Point}
    (hc : coord = coord') (hU : HEq U V)
    (H : GaugeMomentBalances.MovingField U a b f) :
    GaugeMomentBalances.MovingField V a b f := by
  subst coord'
  have hUV := eq_of_heq hU
  subst V
  exact H

private theorem region_carrier_eq {coord coord' : ℝ} {U : SlowRegion coord} {V : SlowRegion coord'}
    (hc : coord = coord') (hU : HEq U V) : U.carrier = V.carrier := by
  subst coord'
  have hUV := eq_of_heq hU
  subst V
  rfl

section Assemble

variable {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters Point TorusInverse.Frequency)
    (r : RankData PressureStream.Plane) (c : Context Point) (x : CycleState ι)
    (primary : ι → HarmonicBlock Point) (P : ι → ℕ → Point → ℝ)
    (S : ι → ℕ → Set Point) {σ κ : ℝ}

local notation "p" => CycleParameters.ofGeometry G h index axial particular signed r
local notation "v" => x.coefficients
local notation "u" => x.state

private theorem meanStepData
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (W : WaveData G p v c u P S σ κ)
    (hPrimitive : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner
      G.gauge.radial.outer c u)
    (hXPg : ∀ i j, GaugeMomentBalances.MovingField G.region G.gauge.radial.inner
      G.gauge.radial.outer (SignedMeanGain.covarianceIncrement (u).oscillation
        ((p).particularVelocity v c u) i j))
    (hXSg : ∀ i j, GaugeMomentBalances.MovingField G.region G.gauge.radial.inner
      G.gauge.radial.outer (SignedMeanGain.covarianceIncrement ((p).afterParticular v c
          u).oscillation
        ((p).signedVelocity v c u) i j))
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c u)
    (hgraph : ∃ slowTime : PressureStream.Plane × PressureStream.Plane,
      ∃ temporal : PressureStream.Plane,
        c.operators = graphOperators G.gauge.radial c.operators.epsilon c.operators.fastCoefficient
          axial slowTime temporal) : CycleMeanEquation.StepData G.region p v c u := {
    inner_pos := G.inner_pos
    exponent_pos := G.exponent_pos
    length := G.length_eq
    domain := fun z hz => ⟨G.strip_radius_pos hz, G.strip_subset hz⟩
    primitive := hPrimitive
    particular_covariance := hXPg
    signed_covariance := hXSg
    rank := hg
    operators := hgraph
    particular_regular := fun l => {
      phase := H.phase l
      velocity := fun n i j => (W.particularSmooth l n i j).mono G.strip_subset
      pressure := fun n j => (W.particularPressureSmooth l n j).mono G.strip_subset }
    signed_regular := fun l => {
      phase := by simp only [(W.carrier l).phase]; exact H.phase l
      velocity := fun n i j => (W.signedSmooth l n i j).mono G.strip_subset
      pressure := fun n j => (W.signedPressureSmooth l n j).mono G.strip_subset }
    particular_solenoidal := W.particularSolenoidal
    signed_solenoidal := W.signedSolenoidal
    angular := H.angular
    signed_carrier := W.carrier }

/-- Assemble the invariant after the quantitative mean calculation.
The public preservation theorem below derives those mean inputs from
the same finite waves and measured cross defects. -/
private theorem assemble
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (W : WaveData G p v c u P S σ κ)
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (ho : OperatorBounds G.strip c.operators κ) (hb : BaseBounds G.strip c.base)
    (hR : ∀ z ∈ G.strip.domain, 0 < c.operators.radius z)
    (hS : ∀ l n, IsClosed (S l n)) {C : ℕ → ι → Set Point}
    (hSC : ∀ l n, S l n ⊆ C n l)
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted G.strip C 0
      (fun n l z => HarmonicMeanInteraction.slowNormal c ho hR ((v).blocks l).phase n z i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted G.strip C (-(1 / 2))
      (fun n l _ => ((v).blocks l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted G.strip C (-(1 / 2))
      (fun n l _ => (((v).blocks l).angularFrequency n : ℝ)))
    (hP0 : ∀ l n z, z ∈ G.strip.domain → 0 ≤ P l n z)
    (hP1 : ∀ l n z, z ∈ G.strip.domain → P l n z ≤ 1)
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c u)
    (hrlength : ∀ n z, z ∈ G.region.carrier → r.length n z = qLength G.coord z)
    (hrleft : G.patch.a ≤ r.inner) (hrright : r.outer ≤ G.patch.b)
    (hgraph : ∃ slowTime : PressureStream.Plane × PressureStream.Plane,
      ∃ temporal : PressureStream.Plane,
        c.operators = graphOperators G.gauge.radial c.operators.epsilon c.operators.fastCoefficient
          axial slowTime temporal)
    (hCovP : SignedMeanGain.TensorClass G.strip (1 + σ)
      (SignedMeanGain.covarianceIncrement (u).oscillation ((p).particularVelocity v c u)))
    (hCovS : SignedMeanGain.TensorClass G.strip (1 + σ - κ)
      (SignedMeanGain.covarianceIncrement ((p).afterParticular v c u).oscillation
          ((p).signedVelocity v c u)))
    (hTemporal : IncrementBounds G.strip (1 + σ - 2 * κ) ((p).temporalIncrement v c u))
    (hRank : IncrementBounds G.strip (1 + σ - 2 * κ) ((p).rankIncrement v c u))
    (hCumulative : CorrectionState.CumulativeBounds G.strip ((p).next v c u))
    (hDebt : DefectBounds G.slowStrip (σ + 1 / 10) c ((p).next v c u))
    (hTheta : MeanClass G.strip (1 + (σ + 1 / 10)) (((p).next v c u).thetaResidual c))
    (hAxial : MeanClass G.strip (1 + (σ + 1 / 10))
      (((p).next v c u).axialResidual c - fun n z =>
        temporalAliasState G.gauge h index c ((p).afterSigned v c u) n (z, 0) 2))
    (hAxis : ∀ β, MeanClass G.strip β ((p).nextAxisymmetricAlias v c u x.axisymmetricAlias)) :
    CycleAnalyticInvariant G c primary P S (σ+1/10) (CycleState.step p c x) := by
  have hsigned := W.signed (show κ ≤ 1/2 by linarith)
  have hzpart n l z (hz : z ∈ G.strip.domain) (hn : z ∉ C n l) i j hj :=
    W.particular_zero_germ hS l n (G.strip_subset hz) (fun hmem => hn (hSC l n hmem)) i j hj
  have hzsigned n l z (hz : z ∈ G.strip.domain) (hn : z ∉ C n l) i j hj :=
    W.signed_zero_germ hS l n (G.strip_subset hz) (fun hmem => hn (hSC l n hmem)) i j hj
  have hNewSupport := (p).next_inputSupport v c u H.inputSupport W.particularSupport W.signedSupport
  have hNewReal := (p).next_realCoefficients v c u H.realCoefficients
  have hzfinal n l z (hz : z ∈ G.strip.domain) (hn : z ∉ C n l) i j hj :=
    velocity_zero_germ_of_inputSupport G.domain_open hS hNewSupport hNewReal l n
      (G.strip_subset hz) (fun hmem => hn (hSC l n hmem)) i j hj
  obtain ⟨hAfter, hSolenoidal⟩ := (p).waveStages_residual_gain v c u hσ hκsmall ho hR hb
    H.cumulative.velocity W.carrier H.wave W.particular hsigned
    (fun l n j => (H.pressureCoefficientSmooth l n j).mono G.strip_subset)
    (fun l n j => (W.particularPressureSmooth l n j).mono G.strip_subset)
    (fun l n j => (W.signedPressureSmooth l n j).mono G.strip_subset)
    H.zeroVelocity H.bands.velocityPressure H.phase H.frequency H.angular H.solenoidal
    W.particularSolenoidal W.signedSolenoidal hNormal hFreq hAng hzpart hzsigned hP0 hP1
    W.particularLinear W.signedLinear
  obtain ⟨hWave, hDifference⟩ := (p).finalBlock_uniform_cumulative v c u primary hσ hκsmall
    H.wave H.difference W.particular hsigned
  have hResidual := (p).meanStages_residual_gain v c u hκsmall ho hR hb.smooth
    H.cumulative.velocity.smooth hTemporal hRank (fun i j _ => hWave i j)
    hNormal hFreq hAng hzfinal hAfter
  have hPressure := (p).finalBlock_pressure_cumulative v c u hσ hκsmall
    H.pressure W.particularPressure W.signedPressure
  obtain ⟨hXP, hXS⟩ := W.covariance_moving H.oscillationSmooth H.oscillationPeriodic
  have hPrimitive : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner
      G.gauge.radial.outer c u := by
    simpa only [G.inner_eq, G.outer_eq] using H.primitives
  have hXPg : ∀ i j, GaugeMomentBalances.MovingField G.region G.gauge.radial.inner
      G.gauge.radial.outer (SignedMeanGain.covarianceIncrement (u).oscillation
        ((p).particularVelocity v c u) i j) := by
    simpa only [G.inner_eq, G.outer_eq] using hXP
  have hXSg : ∀ i j, GaugeMomentBalances.MovingField G.region G.gauge.radial.inner
      G.gauge.radial.outer (SignedMeanGain.covarianceIncrement ((p).afterParticular v c
          u).oscillation
        ((p).signedVelocity v c u) i j) := by
    simpa only [G.inner_eq, G.outer_eq] using hXS
  have hpr := (p).next_primitive v c u G.region G.inner_pos G.exponent_pos G.length_eq
    hPrimitive hXPg hXSg hg
  have hmass := (p).next_zeroMassesOn v c u G.region G.inner_pos G.exponent_pos G.length_eq
    hPrimitive hXPg hXSg hg hrlength
    (by change G.gauge.radial.inner ≤ r.inner; rw [G.inner_eq]; exact hrleft)
    (by change r.outer ≤ G.gauge.radial.outer; rw [G.outer_eq]; exact hrright) H.masses
  have hStep := meanStepData G h index axial particular signed r c x primary P S H W
    hPrimitive hXPg hXSg hg hgraph
  have hAlias := H.representation.alias_eq_lift H.aliasCoefficients
  have hAliasContinuous : AngularContinuous (u).errors.aliasError := by
    rw [hAlias]
    intro n z i
    change Continuous (fun _ : ℝ => x.axisymmetricAlias n z i)
    exact continuous_const
  have hAliasMean : angularMeanVector (u).errors.aliasError = x.axisymmetricAlias := by
    rw [hAlias]
    funext n z i
    exact congrFun (congrFun (angularAverage_axisymmetric (fun n z => x.axisymmetricAlias n z i))
        n) z
  have hGaussianMeans (i : Fin 3) : MeanClass G.strip (1+(σ+1/10))
      (fun n z => angularMeanVector (u).errors.gaussian n z i) := by
    rw [H.gaussianMean]
    exact MemClass.zero (fun _ z hz => G.strip.zeta_nonneg z hz)
  have hAliasMeans (i : Fin 3) : MeanClass G.strip (1+(σ+1/10))
      (fun n z => angularMeanVector (u).errors.aliasError n z i) := by
    rw [hAliasMean]
    exact (H.axisFlat _).map (ContinuousLinearMap.proj i)
  have hMean := (p).next_meanResidualBounds v c u H.angular W.carrier
    (fun n z hz i => H.baseAngular n z (G.strip_subset hz) i)
    H.representation.gaussian_angularContinuous hAliasContinuous hTheta hAxial
    (hGaussianMeans 1) (hGaussianMeans 2) (hAliasMeans 1) (hAliasMeans 2)
  refine {
    representation := (p).next_representation v c u H.representation W.carrier
    bands := (p).next_coefficient_bands v c u H.bands
    realCoefficients := hNewReal
    inputSupport := hNewSupport
    sourceBand := (p).next_residual_band v c u H.bands
    zeroVelocity := (p).finalBlock_zero v c u H.zeroVelocity
    zeroPressure := (p).finalBlock_pressure_zero v c u H.zeroPressure
    carrier := fun l => ⟨(H.carrier l).frequency, (H.carrier l).phase, (H.carrier l).angular⟩
    phase := H.phase
    frequency := H.frequency
    angular := H.angular
    coefficientSmooth := fun l n i j =>
      ((H.coefficientSmooth l n i j).add (W.particularSmooth l n i j)).add (W.signedSmooth l n i j)
    pressureCoefficientSmooth := fun l n j =>
      ((H.pressureCoefficientSmooth l n j).add (W.particularPressureSmooth l n j)).add
        (W.signedPressureSmooth l n j)
    gaussianCoefficientSmooth := fun l n i j =>
      ((H.gaussianCoefficientSmooth l n i j).add (W.particularGaussianSmooth l n i j)).add
        (W.signedGaussianSmooth l n i j)
    solenoidal := hSolenoidal
    wave := hWave
    pressure := hPressure
    difference := hDifference
    cumulative := hCumulative
    covariance := (p).next_covariance_mem v c u (by linarith : (1:ℝ) ≤ 1+σ)
      (by linarith : (1:ℝ) ≤ 1+σ-κ) H.covariance hCovP hCovS
    residual := hResidual
    mean := hMean
    meanHypotheses := hStep.next_meanHypotheses H.meanHypotheses
    debt := hDebt
    primitives := ?_
    reconstructed := hpr.2
    masses := hmass
    oscillationSmooth := (p).next_oscillation_smooth v c u H.oscillationSmooth W.particularField
        W.signedField
    oscillatoryPressureSmooth := ?_
    oscillationPeriodic := (p).next_oscillation_periodic v c u H.oscillationPeriodic
      W.particularPeriodic W.signedPeriodic
    oscillationSupport := (p).next_oscillation_support v c u H.oscillationSupport
      W.particularRadialSupport W.signedRadialSupport
    gaussianFlat := fun β => (p).next_gaussian_mem v c u (H.gaussianFlat β)
      (W.particularGaussian β) (W.signedGaussian β)
    gaussianMean := ?_
    aliasCoefficients := H.aliasCoefficients
    axisFlat := hAxis
    baseAngular := ?_ }
  · have hpn := hpr.1
    change MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer
      c ((p).next v c u) at hpn
    simp only [G.inner_eq, G.outer_eq] at hpn
    exact hpn
  · intro n
    change ContDiffOn ℝ ∞ (((p).next v c u).oscillatoryPressure n) _
    rw [(p).next_oscillatoryPressure]
    exact ((H.oscillatoryPressureSmooth n).add (W.particularPressureField n)).add
        (W.signedPressureField n)
  · exact ((p).next_gaussian_angularMean v c u H.angular W.carrier
      H.representation.gaussian_angularContinuous).trans H.gaussianMean
  · intro n z hz i
    change Continuous (fun θ => ((p).next v c u).errors.base n (z,θ) i)
    rw [(p).next_base_error]
    exact H.baseAngular n z hz i

end Assemble

section Preservation

variable {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters Point TorusInverse.Frequency)
    (r : RankData PressureStream.Plane) (c : Context Point) (x : CycleState ι)
    (primary : ι → HarmonicBlock Point) (P : ι → ℕ → Point → ℝ)
    (S : ι → ℕ → Set Point) {σ κ : ℝ}

local notation "p" => CycleParameters.ofGeometry G h index axial particular signed r
local notation "v" => x.coefficients
local notation "u" => x.state

/-- The remaining inputs to one cycle are on its actual native waves and
their fixed geometric assembly.  The only leading-covariance identity is
on a fixed tail; the finite head is retained by the proof. -/
structure StepData (D : StaticData G h index axial r c κ)
    (H : CycleAnalyticInvariant G c primary P S σ x) (hσ : 1 / 5 ≤ σ) where
  waves : WaveData G p v c u P S σ κ
  /-- Primary band of `StepData`, of type `ℕ`. -/
  primaryBand : ℕ
  primary_band : ∀ l, (primary l).BandLimited primaryBand
  envelope_nonneg : ∀ l n z, z ∈ G.strip.domain → 0 ≤ P l n z
  envelope_le_one : ∀ l n z, z ∈ G.strip.domain → P l n z ≤ 1
  /-- Cells of `StepData`, of type `ℕ → ι → Set Point`. -/
  cells : ℕ → ι → Set Point
  carrier_closed : ∀ l n, IsClosed (S l n)
  carrier_cells : ∀ l n, S l n ⊆ cells n l
  normal : ∀ i, LocalizedWaveBounds.LocalUnweighted G.strip cells 0
    (fun n l z => HarmonicMeanInteraction.slowNormal c D.operators
      (fun _ hz => D.radius_pos hz) ((v).blocks l).phase n z i)
  frequency : LocalizedWaveBounds.LocalUnweighted G.strip cells (-(1/2))
    (fun n l _ => ((v).blocks l).frequency n)
  angular : LocalizedWaveBounds.LocalUnweighted G.strip cells (-(1/2))
    (fun n l _ => (((v).blocks l).angularFrequency n : ℝ))
  /-- Assembly supplied by `StepData`. -/
  assembly : SignedMeanGain.Assembly
    ((p).signedFamily v c u primary P hσ primaryBand primary_band H.bands H.carrier waves.carrier
      H.wave H.difference waves.particular waves.tangent waves.curl
      envelope_nonneg envelope_le_one H.angular)
  labels : assembly.labels = (v).labels
  old_support : LabelSumBounds.SupportedOscillations assembly.slots assembly.label assembly.window
    assembly.auxiliary G.strip.domain (fun l => ((v).blocks l).oscillation)
  particular_support : LabelSumBounds.SupportedOscillations assembly.slots assembly.label
      assembly.window
    assembly.auxiliary G.strip.domain (fun l => ((p).particularBlock v c u l).oscillation)
  primary_smooth : WaveStateRegularity.AngularSmooth G.domain (SignedMeanGain.primaryField _
      assembly)
  primary_periodic : OscillationPeriodic G.region.carrier (SignedMeanGain.primaryField _ assembly)
  rank_geometry : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c u
  /-- Tail start of `StepData`, of type `ℕ`. -/
  tailStart : ℕ
  cross_tail : ∀ n, tailStart ≤ n → ∀ z ∈ G.strip.domain, ∀ i : Fin 2,
    StateMomentBalances.meanBar (SignedMeanGain.crossTensor _ assembly 0 i.succ) n z =
      LocalSignedRequest.requestedStress G.patch G.coord c ((p).afterParticular v c u) n z i

/-- In addition to preservation, keep the actual increments needed by
the physical-stage estimates. -/
structure StepResult : Prop where
  invariant : CycleAnalyticInvariant G c primary P S (σ+1/10) (CycleState.step p c x)
  temporal : IncrementBounds G.strip (1+σ-2*κ) ((p).temporalIncrement v c u)
  rank : IncrementBounds G.strip (1+σ-2*κ) ((p).rankIncrement v c u)
  pressure : MeanClass G.strip (1+σ-2*κ) (((p).next v c u).pressure - (u).pressure)
  velocityCoefficients : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1/2+σ-κ)
    (fun l n z => ((p).finalBlock v c u l).velocity n i j z - ((v).blocks l).velocity n i j z)
  pressureCoefficients : ∀ j, LabelSumBounds.UniformWaveClass G.strip P (1+σ-κ)
    (fun l n z => ((p).finalBlock v c u l).pressure n j z - ((v).blocks l).pressure n j z)
  afterSignedTheta : MeanClass G.strip (1+σ-2*κ) (((p).afterSigned v c u).thetaResidual c)
  afterSignedAxial : MeanClass G.strip (1+σ-2*κ) (((p).afterSigned v c u).axialResidual c)

/-- The complete analytic step, with actual covariance estimates,
finite-head cross defects, temporal/rank reconstruction, and all error
bookkeeping derived in the proof. -/
theorem step (D : StaticData G h index axial r c κ)
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (d : StepData G h index axial particular signed r c x primary P S D H hσ) :
    StepResult G h index axial particular signed r c x primary P S (σ := σ) (κ := κ) := by
  let W := d.waves
  let F := (p).signedFamily v c u primary P hσ d.primaryBand d.primary_band H.bands H.carrier
    W.carrier H.wave H.difference W.particular W.tangent W.curl d.envelope_nonneg d.envelope_le_one
        H.angular
  let a : SignedMeanGain.Assembly F := d.assembly
  have halabels : a.labels = (v).labels := d.labels
  have hκ : 0 ≤ κ := D.operators.kappa_nonneg
  have hfixed : (reconstructState G.gauge c u).pressure = (u).pressure :=
    congrArg (fun z : State Point => z.pressure) H.reconstructed
  have hrep₀ : (u).oscillation = LabelSumBounds.fieldSum a.labels (fun l => ((v).blocks
      l).oscillation) := by
    rw [halabels]
    funext n z i
    exact H.representation.velocity n z i
  have hCov₀ := assembledCovarianceIncrement_mem (show (1:ℝ)/2 ≤ 1/2+σ by linarith)
    a.labels a.label a.injective a.level a.window a.window_continuous a.auxiliary
    (v).blocks ((p).particularBlock v c u) (v).residualBand H.bands.velocityPressure
    ((p).particularBlock_band v c u) (fun _ => ⟨rfl,rfl,rfl⟩)
    (fun i j _ => H.wave i j) (fun i j _ => W.particular i j)
    H.zeroVelocity ((p).particularBlock_zero v c u) d.envelope_nonneg d.envelope_le_one H.angular
    d.old_support d.particular_support u hrep₀
  have hCovP : SignedMeanGain.TensorClass G.strip (1+σ)
      (SignedMeanGain.covarianceIncrement (u).oscillation ((p).particularVelocity v c u)) := by
    simp only [halabels, CycleParameters.particularVelocity,
      show (1:ℝ)/2+(1/2+σ) = 1+σ by ring] at hCov₀ ⊢
    exact hCov₀
  have hrep₁ : ((p).afterParticular v c u).oscillation = SignedMeanGain.oldField F a := by
    simpa only [SignedMeanGain.oldField, halabels, F, CycleParameters.signedFamily] using
      (p).beforeSignedBlock_represents v c u H.representation
  have hw₂ : SignedMeanGain.tangentField F a + SignedMeanGain.curlField F a =
      (p).signedVelocity v c u := by
    simpa only [SignedMeanGain.tangentField, SignedMeanGain.curlField, F,
      CycleParameters.signedFamily, halabels] using ((p).signedVelocity_split v c u).symm
  have hCovS : SignedMeanGain.TensorClass G.strip (1+σ-κ)
      (SignedMeanGain.covarianceIncrement ((p).afterParticular v c u).oscillation
        ((p).signedVelocity v c u)) := by
    have hh := (SignedMeanGain.signed_tensor_bounds hσ hκsmall F a).1
    rwa [SignedMeanGain.incrementTensor, ← hrep₁, hw₂] at hh
  obtain ⟨hXP, hXS⟩ := W.covariance_moving H.oscillationSmooth H.oscillationPeriodic
  have hXSFamily : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor F a i j) :=
      by
    intro i j
    rw [SignedMeanGain.incrementTensor, ← hrep₁, hw₂]
    exact hXS i j
  have hTangent : WaveStateRegularity.AngularSmooth G.domain (SignedMeanGain.tangentField F a) := by
    simpa only [SignedMeanGain.tangentField, F, CycleParameters.signedFamily, halabels] using
        W.tangentField
  have hTangentPer : OscillationPeriodic G.region.carrier (SignedMeanGain.tangentField F a) := by
    simpa only [SignedMeanGain.tangentField, F, CycleParameters.signedFamily, halabels] using
        W.tangentPeriodic
  have hTangentSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
      (SignedMeanGain.tangentField F a) := by
    simpa only [SignedMeanGain.tangentField, F, CycleParameters.signedFamily, halabels] using
        W.tangentRadialSupport
  have hCross : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor F a i j) :=
    symmetricCovariance_moving G.region d.primary_smooth hTangent hTangentSupport
        d.primary_periodic hTangentPer
  obtain ⟨hθ, hz⟩ := H.raw_mean_bounds
  obtain ⟨_, _, hθ₁, hz₁, _, _⟩ := waveStage_mean_gain G c u ((p).particularVelocity v c u)
    ((p).particularPressure v c u) ((p).particularGaussian v c u) hσ hκ hκsmall H.primitives
    D.operators D.base H.cumulative hfixed hθ hz H.debt hXP hCovP
  have H₁ := H.primitives.waveStage G.gauge ((p).particularVelocity v c u)
    ((p).particularPressure v c u) ((p).particularGaussian v c u) hXP
  have hDefects := SignedCrossDefectClass.residual_defects_all_exponents_of_primitive G c
    ((p).afterParticular v c u) F a hCross H₁ rfl hθ₁ hz₁ d.tailStart d.cross_tail
  have H₂ := H₁.waveStage G.gauge ((p).signedVelocity v c u)
    ((p).signedPressure v c u) ((p).signedGaussian v c u) hXS
  have H₂g : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer
      c ((p).afterSigned v c u) := by
    simp only [G.inner_eq, G.outer_eq] at H₂ ⊢
    exact H₂
  have HT := MeanStageRegularity.temporalStage_primitive H₂g G.inner_pos G.exponent_pos G.length_eq
    rfl h index axial
  have HG := MeanStageRegularity.rankGeometry_for_state HT G.inner_pos
      G.gauge.radial.inner_lt_outer d.rank_geometry
  have hMean := CrossBasedMeanComposition.CycleParameters.mean_gain_from_waves_of_cross_defects
    G h index axial particular signed r v c u primary P hσ d.primaryBand d.primary_band H.bands
    H.carrier W.carrier H.wave H.difference W.particular W.tangent W.curl
    d.envelope_nonneg d.envelope_le_one H.angular a halabels H.representation H.zeroVelocity
    ((p).particularBlock_zero v c u) d.old_support d.particular_support hκ hκsmall H.primitives
    D.operators_eq (by simpa only [D.operators_eq] using D.operators) D.base H.cumulative hfixed
    (fun n z hz => (H.masses n z hz).1) (fun n z hz => (H.masses n z hz).2)
    hθ hz H.debt hXP hXSFamily hCross (hDefects (1+σ+17/100+κ)).1 (hDefects (1+σ+17/100+κ)).2
    D.time_nonneg D.slow_scale D.aliasData.gap D.index_lower D.temporal D.fast
    D.angular_slow D.axial_slow HG D.rankParameters D.rankCoefficient_ne D.rank_left D.rank_right
  obtain ⟨hSθ, hSz, _, hT, hRank, hPressure, hCumulative, hDebt, hTheta, hAxial⟩ := hMean
  have HAlias : MeanStateRegularity.PrimitiveData D.aliasData.region D.aliasData.inner
      D.aliasData.outer c u := by
    simpa only [D.inner, D.outer] using primitive_region_transport D.coord D.region H.primitives
  have hXPAlias : ∀ i j, GaugeMomentBalances.MovingField D.aliasData.region D.aliasData.inner
      D.aliasData.outer
      (SignedMeanGain.covarianceIncrement (u).oscillation ((p).particularVelocity v c u) i j) := by
    intro i j
    simpa only [D.inner, D.outer] using moving_region_transport D.coord D.region (hXP i j)
  have hXSAlias : ∀ i j, GaugeMomentBalances.MovingField D.aliasData.region D.aliasData.inner
      D.aliasData.outer
      (SignedMeanGain.covarianceIncrement ((p).afterParticular v c u).oscillation
          ((p).signedVelocity v c u) i j) := by
    intro i j
    simpa only [D.inner, D.outer] using moving_region_transport D.coord D.region (hXS i j)
  have hRankAlias : LocalRankDefect.RankGeometry G.gauge r D.aliasData.region.carrier c u := by
    simpa only [region_carrier_eq D.coord D.region] using d.rank_geometry
  have hAxis := ActualCycleExcluded.nextAxisymmetricAlias_all_powers D.aliasData p v c u
    (D.compatible particular signed) HAlias hXPAlias hXSAlias hRankAlias D.operators D.base
    H.cumulative hCumulative H.covariance
    (fun i j => (hCovP i j).mono_exponent (show (1:ℝ) ≤ 1+σ by linarith))
    (fun i j => (hCovS i j).mono_exponent (show (1:ℝ) ≤ 1+σ-κ by linarith))
    hSz x.axisymmetricAlias H.axisFlat
  have hFull := assemble G h index axial particular signed r c x primary P S H W hσ hκsmall
    D.operators D.base (fun _ hz => D.radius_pos hz) d.carrier_closed d.carrier_cells
    d.normal d.frequency d.angular d.envelope_nonneg d.envelope_le_one d.rank_geometry
    D.rankParameters.length D.rank_left.le D.rank_right.le D.graph
    hCovP hCovS hT hRank hCumulative hDebt hTheta hAxial hAxis
  have hInc := (p).finalBlock_increment_bounds v c u hκ W.particular (W.signed (by linarith))
    W.particularPressure W.signedPressure
  exact ⟨hFull, hT, hRank, hPressure, hInc.1, hInc.2, hSθ, hSz⟩

/-- Projection of the complete step estimate to the stored invariant. -/
theorem step_preserves (D : StaticData G h index axial r c κ)
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (d : StepData G h index axial particular signed r c x primary P S D H hσ) :
    CycleAnalyticInvariant G c primary P S (σ+1/10) (CycleState.step p c x) :=
  (step G h index axial particular signed r c x primary P S D H hσ hκsmall d).invariant

end Preservation

section Iteration

variable {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters Point TorusInverse.Frequency)
    (r : RankData PressureStream.Plane) (c : Context Point) (seed : CycleState ι)
    (primary : ι → HarmonicBlock Point) (P : ι → ℕ → Point → ℝ)
    (S : ι → ℕ → Set Point) {κ : ℝ}

local notation "p" => CycleParameters.ofGeometry G h index axial particular signed r
local notation "state" => CycleState.iterate (fun _ => p) c seed

/-- All stages use the same primitive parameters, strip, gauge, carriers,
and comparison primary.  The supplied data construct each actual wave;
they do not assume preservation of the invariant. -/
theorem iterate_invariant (D : StaticData G h index axial r c κ)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 / 5 ≤ σ n) (hσstep : ∀ n, σ (n + 1) = σ n + 1 / 10)
    (hκsmall : κ ≤ 1 / 100000)
    (hseed : CycleAnalyticInvariant G c primary P S (σ 0) seed)
    (data : ∀ n (H : CycleAnalyticInvariant G c primary P S (σ n) (state n)),
      StepData G h index axial particular signed r c (state n) primary P S D H (hσ n)) :
    ∀ n, CycleAnalyticInvariant G c primary P S (σ n) (state n) := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    have hn := step_preserves G h index axial particular signed r c (state n) primary P S
      D ih (hσ n) hκsmall (data n ih)
    simpa only [CycleState.iterate_succ, hσstep] using hn

/-- The same induction also retains the actual increment estimates for
each positive physical stage. -/
theorem iterate_results (D : StaticData G h index axial r c κ)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 / 5 ≤ σ n) (hσstep : ∀ n, σ (n + 1) = σ n + 1 / 10)
    (hκsmall : κ ≤ 1 / 100000)
    (hseed : CycleAnalyticInvariant G c primary P S (σ 0) seed)
    (data : ∀ n (H : CycleAnalyticInvariant G c primary P S (σ n) (state n)),
      StepData G h index axial particular signed r c (state n) primary P S D H (hσ n)) :
    (∀ n, CycleAnalyticInvariant G c primary P S (σ n) (state n)) ∧
    ∀ n, StepResult G h index axial particular signed r c (state n) primary P S
      (σ := σ n) (κ := κ) := by
  have hi := iterate_invariant G h index axial particular signed r c seed primary P S
    D σ hσ hσstep hκsmall hseed data
  exact ⟨hi, fun n => step G h index axial particular signed r c (state n) primary P S
    D (hi n) (hσ n) hκsmall (data n (hi n))⟩

end Iteration

end NavierStokes.CorrectionAnalyticStep
