/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeStateCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.RankStateBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseRankPatch
public import LeanPool.NavierStokesAndEuler.NavierStokes.TemporalStateCoherence

@[expose] public section

/-!
# Coherence of the actual five-row rank correction

The debt is recomputed from the complete incoming state.  Primitive chart
data and the shared normalized inverse are transported before applying the
actual variable-gauge stream and pressure constructors.
-/

noncomputable section

namespace NavierStokes.RankStateCoherence

open Set Function Filter
open scoped Topology ContDiff
open PhysicalResidualNaturality GaugeStateCoherence

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

omit [NormedAddCommGroup S] [NormedSpace ℝ S] in
theorem sourceMoment_fiber (m : ℕ) (f g : PressureStream.Lift S → ℝ) (s : S)
    (he : ∀ R Y, f (R,(s,Y)) = g (R,(s,Y))) :
    MeanChartCompatibility.sourceMoment m f s = MeanChartCompatibility.sourceMoment m g s := by
  exact PhysicalMeanDomain.liftedPressureMass_fiberLocal _ _ s
    (fun R Y => congrArg (R^m * ·) (he R Y)) 0 0

/-- The whole-fiber moment of a compatible field, using only local slow
regularity and the actual torus covering. -/
theorem sourceMoment_on {l a : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k m : ℕ)
    {V : Set S} {U : Set T} (hU : IsOpen U) (hmap : MapsTo P V U)
    {f : PressureStream.Lift S → ℝ} {g : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k)
      a f g)
    (hg : ContDiffOn ℝ ∞ g (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U g) {s : S} (hs : s ∈ V) :
    MeanChartCompatibility.sourceMoment m f s =
      (a/l^(m+1)) * MeanChartCompatibility.sourceMoment m g (P s) := by
  let G := PhysicalMeanDomain.freezeSlow (P s) g
  have hG : ContDiff ℝ ∞ G := VariableGaugeMean.freezeSlow_contDiff hU (hmap hs) hg
  have hGp : PressureStream.TorusPeriodicLift G := by
    intro R t Y j
    exact hp R (P s) (hmap hs) Y j
  have hfiber : ∀ R Y, f (R,(s,Y)) =
      MeanChartCompatibility.coverPull l P.toContinuousLinearMap k a G (R,(s,Y)) := by
    intro R Y
    rw [GaugeStateCoherence.coverPull_eq l hl.ne' P k]
    exact he (R,(s,Y)) hs
  rw [sourceMoment_fiber m f _ s hfiber,
    MeanChartCompatibility.sourceMoment_coverPull hl P.toContinuousLinearMap k m a hG hGp]
  rfl

/-- Reference fields needed for the actual three measured debts. -/
structure DebtRegular (U : Set T) (C : CorrectionState.Context (PressureStream.Lift T))
    (u : CorrectionState.State (PressureStream.Lift T)) (n : ℕ) : Prop where
  radial : ContDiffOn ℝ ∞ (u.gr C n) (PhysicalMeanDomain.slowDomain U)
  angular : ContDiffOn ℝ ∞
    ((MeanIncrementBounds.thetaAxial C.base u.mean + u.covariance 2 1) n)
    (PhysicalMeanDomain.slowDomain U)
  axial : ContDiffOn ℝ ∞
    ((MeanIncrementBounds.axialAxial C.base u.mean + u.covariance 2 2) n)
    (PhysicalMeanDomain.slowDomain U)
  radial_periodic : PhysicalMeanDomain.PeriodicOn U (u.gr C n)
  angular_periodic : PhysicalMeanDomain.PeriodicOn U
    ((MeanIncrementBounds.thetaAxial C.base u.mean + u.covariance 2 1) n)
  axial_periodic : PhysicalMeanDomain.PeriodicOn U
    ((MeanIncrementBounds.axialAxial C.base u.mean + u.covariance 2 2) n)

/-- All three debts are measured from the full base and state.  The powers
are pressure `c²`, angular `c²/l³`, and axial `c²/l²`. -/
theorem measured_debt_on {l c : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {V : Set S} {U : Set T} (hV : IsOpen V) (hU : IsOpen U) (hmap : MapsTo P V U)
    {C : CorrectionState.Context (PressureStream.Lift S)}
    {Cr : CorrectionState.Context (PressureStream.Lift T)}
    {u : CorrectionState.State (PressureStream.Lift S)}
    {ur : CorrectionState.State (PressureStream.Lift T)} {n nr : ℕ}
    (H : StateOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c
      l u ur n nr)
    (G : ContextOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k)
      c l C Cr n nr)
    (R : DebtRegular U Cr ur nr) {s : S} (hs : s ∈ V) :
    CorrectionState.debt C u n s =
      MeanRankUpdate.scaleDebt l⁻¹ c (CorrectionState.debt Cr ur nr (P s)) := by
  have hrad := H.gr G (PhysicalMeanDomain.slowDomain_open hV) hl.ne'
  have htheta := (G.base.thetaAxial H.mean).add (H.covariance 2 1)
  have haxial := (G.base.axialAxial H.mean).add (H.covariance 2 2)
  have h0 := sourceMoment_on hl P k 0 hU hmap hrad R.radial R.radial_periodic hs
  have h2 := sourceMoment_on hl P k 2 hU hmap hrad R.radial R.radial_periodic hs
  have htheta2 := sourceMoment_on hl P k 2 hU hmap htheta R.angular R.angular_periodic hs
  have haxial1 := sourceMoment_on hl P k 1 hU hmap haxial R.axial R.axial_periodic hs
  rw [MeanChartCompatibility.stateDebt_eq_sourceDebt,
    MeanChartCompatibility.stateDebt_eq_sourceDebt]
  ext i
  fin_cases i
  · change MeanChartCompatibility.sourceMoment 0 (u.gr C n) s = _
    rw [h0]
    simp [MeanRankUpdate.scaleDebt, MeanChartCompatibility.sourceDebt, hl.ne', pow_two]
  · change MeanChartCompatibility.sourceMoment 2
      (MeanIncrementBounds.thetaAxial C.base u.mean n + u.covariance 2 1 n) s = _
    rw [htheta2]
    simp [MeanRankUpdate.scaleDebt, MeanChartCompatibility.sourceDebt,
      div_eq_mul_inv, pow_two, mul_comm, mul_assoc]
  · change MeanChartCompatibility.sourceMoment 1
      (MeanIncrementBounds.axialAxial C.base u.mean n + u.covariance 2 2 n) s - (1/2:ℝ) *
      MeanChartCompatibility.sourceMoment 2 (u.gr C n) s = _
    rw [haxial1, h2]
    simp only [MeanRankUpdate.scaleDebt, MeanChartCompatibility.sourceDebt,
      Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_succ, Function.comp_def, Pi.add_apply]
    field_simp ; ring

/-- Primitive rank data use one dimensionless kernel.  No rank-output or
debt equality is a field of this structure. -/
structure RankOn (V : Set S) (P : S → T) (l c : ℝ)
    (r : CorrectionState.RankData S) (rr : CorrectionState.RankData T) (n nr : ℕ) : Prop where
  lambda : r.lambda = rr.lambda
  inner : r.inner = rr.inner
  outer : r.outer = rr.outer
  length : ∀ s ∈ V, r.length n s = l⁻¹ * rr.length nr (P s)
  velocity : ∀ s ∈ V, r.velocity n s = c * rr.velocity nr (P s)
  coefficient : ∀ s ∈ V, r.coefficient n s = rr.coefficient nr (P s)
  reference_length : ∀ s ∈ V, rr.length nr (P s) ≠ 0
  reference_velocity : ∀ s ∈ V, rr.velocity nr (P s) ≠ 0

theorem RankOn.angular {V : Set S} {P : S → T} {l c : ℝ} (hl : l ≠ 0) (hc : c ≠ 0)
    {r : CorrectionState.RankData S} {rr : CorrectionState.RankData T} {n nr : ℕ}
    (H : RankOn V P l c r rr n nr)
    {C : CorrectionState.Context (PressureStream.Lift S)}
    {Cr : CorrectionState.Context (PressureStream.Lift T)}
    {u : CorrectionState.State (PressureStream.Lift S)}
    {ur : CorrectionState.State (PressureStream.Lift T)} {s : S} (hs : s ∈ V)
    (hd : CorrectionState.debt C u n s = MeanRankUpdate.scaleDebt l⁻¹ c (CorrectionState.debt Cr ur
      nr (P s)))
    (R : ℝ) : CorrectionState.rankAngular r C u n (R,s) =
      c * CorrectionState.rankAngular rr Cr ur nr (l*R,P s) := by
  change MeanRankUpdate.angularIncrement r.lambda (r.coefficient n s) r.inner r.outer
    (r.length n s) (r.velocity n s) (CorrectionState.debt C u n s) R = _
  rw [H.lambda, H.inner, H.outer, H.length s hs, H.velocity s hs, H.coefficient s hs, hd]
  have he := MeanChartCompatibility.rankAngular_scale (inv_ne_zero hl) hc
    (H.reference_length s hs) (H.reference_velocity s hs) rr.lambda (rr.coefficient nr (P s))
    rr.inner rr.outer (CorrectionState.debt Cr ur nr (P s)) (l*R)
  simp only [inv_mul_cancel_left₀ hl] at he
  exact he

theorem RankOn.desiredAxial {V : Set S} {P : S → T} {l c : ℝ} (hl : l ≠ 0) (hc : c ≠ 0)
    {r : CorrectionState.RankData S} {rr : CorrectionState.RankData T} {n nr : ℕ}
    (H : RankOn V P l c r rr n nr)
    {C : CorrectionState.Context (PressureStream.Lift S)}
    {Cr : CorrectionState.Context (PressureStream.Lift T)}
    {u : CorrectionState.State (PressureStream.Lift S)}
    {ur : CorrectionState.State (PressureStream.Lift T)} {s : S} (hs : s ∈ V)
    (hd : CorrectionState.debt C u n s = MeanRankUpdate.scaleDebt l⁻¹ c (CorrectionState.debt Cr ur
      nr (P s)))
    (R : ℝ) : CorrectionState.rankDesiredAxial r C u n (R,s) =
      c * CorrectionState.rankDesiredAxial rr Cr ur nr (l*R,P s) := by
  change MeanRankUpdate.desiredAxialIncrement r.lambda (r.coefficient n s) r.inner r.outer
    (r.length n s) (r.velocity n s) (CorrectionState.debt C u n s) R = _
  rw [H.lambda, H.inner, H.outer, H.length s hs, H.velocity s hs, H.coefficient s hs, hd]
  have he := MeanChartCompatibility.rankDesiredAxial_scale (inv_ne_zero hl) hc
    (H.reference_length s hs) (H.reference_velocity s hs) rr.lambda (rr.coefficient nr (P s))
    rr.inner rr.outer (CorrectionState.debt Cr ur nr (P s)) (l*R)
  simp only [inv_mul_cancel_left₀ hl] at he
  exact he

section ActualStep

variable {l c : ℝ} (hl : 0 < l) (hc : c ≠ 0) (P : S ≃L[ℝ] T) (k : ℕ)
  {V : Set S} {U : Set T} (hV : IsOpen V) (hU : IsOpen U) (hmap : MapsTo P V U)
  {C : CorrectionState.Context (PressureStream.Lift S)}
  {Cr : CorrectionState.Context (PressureStream.Lift T)}
  {u : CorrectionState.State (PressureStream.Lift S)}
  {ur : CorrectionState.State (PressureStream.Lift T)} {n nr : ℕ}
  (H : StateOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c l
    u ur n nr)
  (G : ContextOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c
    l C Cr n nr)
  (R : DebtRegular U Cr ur nr)
  {r : CorrectionState.RankData S} {rr : CorrectionState.RankData T}
  (K : RankOn V P l c r rr n nr)

include hc hV hU hmap H G R K

theorem rankAngular_on :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c
      (MeanRankUpdate.slowLift (CorrectionState.rankAngular r C u n))
      (MeanRankUpdate.slowLift (CorrectionState.rankAngular rr Cr ur nr)) := by
  intro z hz
  exact K.angular hl.ne' hc hz (measured_debt_on hl P k hV hU hmap H G R hz) z.1

theorem rankDesiredAxial_on :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c
      (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r C u n))
      (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial rr Cr ur nr)) := by
  intro z hz
  exact K.desiredAxial hl.ne' hc hz (measured_debt_on hl P k hV hU hmap H G R hz) z.1

variable {g : VariableGaugeMean.GaugeData S} {gr : VariableGaugeMean.GaugeData T}
  (J : GaugeOn V l P.toContinuousLinearMap k g gr n nr)
  (F : LocalRankDefect.RankGeometry gr rr U Cr ur)

include J F

/-- Naturality of the literal moving-gauge rank potential.  Its source is
the already constructed five-row inverse of the measured debt. -/
theorem rankPotential_on :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) (c/l)
      (VariableGaugeMean.rankPotential g r C u n) (VariableGaugeMean.rankPotential gr rr Cr ur nr)
        := by
  have ha : 0 < g.radial.inner := J.inner ▸ F.primitive_inner_pos
  have hd : 0 < g.radial.exponent := J.exponent ▸ F.exponent_pos
  have hs : VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (gr.length nr) U
      (MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial rr Cr ur nr)) := by
    intro z hz hn
    have he := F.desired_slice_support nr hz (F.gauge_left nr _ hz) (F.gauge_right nr _ hz) hn
    simpa only [J.inner, J.outer] using he
  have he := TemporalStateCoherence.streamPotential_on hl P k ha g.radial.inner_lt_outer hd
    g.radial.radialDirection gr.radial.radialDirection J.frequency (g.length n) (gr.length nr)
    hU hmap J.positive J.length (rankDesiredAxial_on hl hc P k hV hU hmap H G R K)
    (F.desired_lift_smooth nr) hs
  change ScalarOn _ _ _ (VariableGaugeMean.streamPotential _ _ _ _ _ _ _)
    (VariableGaugeMean.streamPotential _ _ _ _ _ _ _)
  rw [TemporalStateCoherence.streamPotential_congr_profile J.exponent J.inner J.outer
    (gr.radial.frequency nr) (gr.length nr) gr.radial.radialDirection]
  exact he

/-- All three components are the actual stream reconstruction of the
rank correction.  No output-increment coherence is assumed. -/
theorem rankIncrementState_on (axial : S × PressureStream.Plane) (axialr : T × PressureStream.Plane)
    (ha : (P.toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k))
        (C.operators.epsilon n • axial) = l • (Cr.operators.epsilon nr • axialr)) :
    TripleOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c
      (VariableGaugeMean.rankIncrementState g r axial C u)
      (VariableGaugeMean.rankIncrementState gr rr axialr Cr ur) n nr := by
  have hpot := rankPotential_on hl hc P k hV hU hmap H G R K J F
  have hb := TemporalStateCoherence.streamBeta_on hl P k (C.operators.epsilon n • axial)
    (Cr.operators.epsilon nr • axialr) ha hV hpot
  have hgamma := TemporalStateCoherence.streamGamma_on hl P k g.radial.radialDirection
    gr.radial.radialDirection J.frequency hV hpot
  refine ⟨hb.reweight (div_mul_cancel₀ c hl.ne'), rankAngular_on hl hc P k hV hU hmap H G R K, ?_⟩
  simpa only [VariableGaugeMean.rankIncrementState, J.exponent] using
    hgamma.reweight (div_mul_cancel₀ c hl.ne')

end ActualStep

/-- The actual state before the rank step's pressure is reconstructed. -/
noncomputable def rankAddedState (g : VariableGaugeMean.GaugeData S) (r : CorrectionState.RankData
  S)
    (axial : S × PressureStream.Plane) (C : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S)) : CorrectionState.State
      (PressureStream.Lift S) :=
  u.addIncrement (VariableGaugeMean.rankIncrementState g r axial C u) 0 0 0
    CorrectionState.ExcludedErrors.zero

theorem add_mean_on {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {u : CorrectionState.State D} {ur : CorrectionState.State E} {n nr : ℕ}
    (H : StateOn V e c l u ur n nr) {m : MeanIncrementBounds.Triple D} {mr :
      MeanIncrementBounds.Triple E}
    (hm : TripleOn V e c m mr n nr) :
    StateOn V e c l
      (u.addIncrement m 0 0 0 CorrectionState.ExcludedErrors.zero)
      (ur.addIncrement mr 0 0 0 CorrectionState.ExcludedErrors.zero) n nr := by
  refine ⟨H.mean.updated hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [CorrectionState.State.addIncrement, add_zero] using H.pressure
  · simpa only [CorrectionState.State.addIncrement, add_zero] using H.oscillation
  · simpa only [CorrectionState.State.addIncrement, add_zero] using H.oscillatoryPressure
  · simpa only [CorrectionState.State.addIncrement, CorrectionState.ExcludedErrors.add,
      CorrectionState.ExcludedErrors.zero, add_zero] using H.baseError
  · simpa only [CorrectionState.State.addIncrement, CorrectionState.ExcludedErrors.add,
      CorrectionState.ExcludedErrors.zero, add_zero] using H.gaussian
  · simpa only [CorrectionState.State.addIncrement, CorrectionState.ExcludedErrors.add,
      CorrectionState.ExcludedErrors.zero, add_zero] using H.aliasError

/-- Coherence survives the complete rank step, including the pressure
recomputed from the new actual radial residual. -/
theorem rankStageState_on {l c : ℝ} (hl : 0 < l) (hc : c ≠ 0) (P : S ≃L[ℝ] T) (k : ℕ)
    {V : Set S} {U : Set T} (hV : IsOpen V) (hU : IsOpen U) (hmap : MapsTo P V U)
    {C : CorrectionState.Context (PressureStream.Lift S)}
    {Cr : CorrectionState.Context (PressureStream.Lift T)}
    {u : CorrectionState.State (PressureStream.Lift S)}
    {ur : CorrectionState.State (PressureStream.Lift T)} {n nr : ℕ}
    (H : StateOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c
      l u ur n nr)
    (G : ContextOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k)
      c l C Cr n nr)
    (R : DebtRegular U Cr ur nr)
    {r : CorrectionState.RankData S} {rr : CorrectionState.RankData T}
    (K : RankOn V P l c r rr n nr)
    {g : VariableGaugeMean.GaugeData S} {gr : VariableGaugeMean.GaugeData T}
    (J : GaugeOn V l P.toContinuousLinearMap k g gr n nr)
    (F : LocalRankDefect.RankGeometry gr rr U Cr ur)
    (axial : S × PressureStream.Plane) (axialr : T × PressureStream.Plane)
    (ha : (P.toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k))
        (C.operators.epsilon n • axial) = l • (Cr.operators.epsilon nr • axialr))
    (hf : ContDiffOn ℝ ∞ ((rankAddedState gr rr axialr Cr ur).gr Cr nr)
      (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U ((rankAddedState gr rr axialr Cr ur).gr Cr nr))
    (hs : VariableGaugeMean.SupportedGauge gr.radial.inner gr.radial.outer (gr.length nr) U
      ((rankAddedState gr rr axialr Cr ur).gr Cr nr)) :
    StateOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c l
      (VariableGaugeMean.rankStageState g r axial C u)
      (VariableGaugeMean.rankStageState gr rr axialr Cr ur) n nr := by
  have hi := rankIncrementState_on hl hc P k hV hU hmap H G R K J F axial axialr ha
  have hm := add_mean_on H hi
  exact GaugeStateCoherence.reconstructState_on hl P k hV hU hmap g gr C Cr
    (rankAddedState g r axial C u) (rankAddedState gr rr axialr Cr ur) n nr
    (J.inner ▸ F.primitive_inner_pos) (J.exponent ▸ F.exponent_pos) J hm G hf hp hs

/-! ## The actual normalized data used by the recurrence -/

theorem normalized_rank_on {h : ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (B lam a b : ℝ) (n m : ℕ) {V : Set PressureStream.Plane}
    (hV : ∀ s ∈ V, 0 < s.1) :
    RankOn V (bandSlowEquiv h n m) (bandScale n m) (bandVelocityScale h n m)
      (RankStateBounds.normalizedData (2*h) (CoordinateAlgebra.A h) B lam a b)
      (RankStateBounds.normalizedData (2*h) (CoordinateAlgebra.A h) B lam a b) n m := by
  have hQ : 0 < ChartScales.Q n / ChartScales.Q m := div_pos (ChartScales.Q_pos n)
    (ChartScales.Q_pos m)
  have hpos (s : PressureStream.Plane) (hs : s ∈ V) : 0 < (bandSlowEquiv h n m s).1 :=
    mul_pos hQ (hV s hs)
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    change VariableGaugeMean.qLength (2*h) s =
      (bandScale n m)⁻¹ * VariableGaugeMean.qLength (2*h) (bandSlowEquiv h n m s)
    rw [qLength_bandSlowEquiv hh hh1 n m (hV s hs), inv_mul_cancel_left₀ (bandScale_pos n m).ne']
  · intro s hs
    change SimilarityCoordinates.coordinateQ (2*h) s ^ (-CoordinateAlgebra.A h) =
      (ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.A h *
        SimilarityCoordinates.coordinateQ (2*h)
          ((ChartScales.Q n / ChartScales.Q m)*s.1,
            (ChartScales.Q n / ChartScales.Q m)^CoordinateAlgebra.D h*s.2) ^ (-CoordinateAlgebra.A
              h)
    rw [SimilarityHomogeneity.coordinateQ_scale_h hh hh1 hQ (hV s hs),
      Real.mul_rpow hQ.le (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith) (hV s
        hs)).1.le,
      ← mul_assoc, ← Real.rpow_add hQ, add_neg_cancel, Real.rpow_zero, one_mul]
  · intro s hs
    change MeanRankUpdate.shapedAmplitude B (SimilarityCoordinates.coordinateEta (2*h) s) =
      MeanRankUpdate.shapedAmplitude B (SimilarityCoordinates.coordinateEta (2*h)
        ((ChartScales.Q n / ChartScales.Q m)*s.1,
          (ChartScales.Q n / ChartScales.Q m)^CoordinateAlgebra.D h*s.2))
    rw [SimilarityHomogeneity.coordinateEta_scale_h hh hh1 hQ (hV s hs)]
  · intro s hs
    exact (VariableGaugeMean.qLength_pos (by linarith) (by linarith) (hpos s hs)).ne'
  · intro s hs
    exact (Real.rpow_pos_of_pos
      (SimilarityCoordinates.coordinateQ_spec (by linarith) (by linarith) (hpos s hs)).1 _).ne'

theorem normalized_rank_on_of_parameters {h B : ℝ} (hh : 0 < h) (hh1 : h < 1/2)
    (n m : ℕ) {V U : Set PressureStream.Plane} (htime : ∀ s ∈ V, 0 < s.1)
    (hmap : MapsTo (bandSlowEquiv h n m) V U)
    {r rr : CorrectionState.RankData PressureStream.Plane}
    (hr : RankStateBounds.NormalizedParameters (2*h) (CoordinateAlgebra.A h) B r V)
    (hrr : RankStateBounds.NormalizedParameters (2*h) (CoordinateAlgebra.A h) B rr U)
    (hlam : r.lambda = rr.lambda) (ha : r.inner = rr.inner) (hb : r.outer = rr.outer) :
    RankOn V (bandSlowEquiv h n m) (bandScale n m) (bandVelocityScale h n m) r rr n m := by
  have H := normalized_rank_on hh hh1 B r.lambda r.inner r.outer n m htime
  refine ⟨hlam, ha, hb, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rw [hr.length n s hs, hrr.length m _ (hmap hs)]
    exact H.length s hs
  · intro s hs
    rw [hr.velocity n s hs, hrr.velocity m _ (hmap hs)]
    exact H.velocity s hs
  · intro s hs
    rw [hr.coefficient n s hs, hrr.coefficient m _ (hmap hs)]
    exact H.coefficient s hs
  · intro s hs
    rw [hrr.length m _ (hmap hs)]
    exact H.reference_length s hs
  · intro s hs
    rw [hrr.velocity m _ (hmap hs)]
    exact H.reference_velocity s hs

/-! ## All five rows, against the full base -/

theorem fiveRows_chart {l c : ℝ} (hl : 0 < l)
    {v g f z vr gr fr zr : ℝ → ℝ} {d dr : MeanRankUpdate.Debt}
    (H : FiveRowRank.FiveRows vr gr dr fr zr)
    (hv : ∀ R, v R = c * vr (l*R)) (hg : ∀ R, g R = c * gr (l*R))
    (hf : ∀ R, f R = c * fr (l*R)) (hz : ∀ R, z R = c * zr (l*R))
    (hd : d = MeanRankUpdate.scaleDebt l⁻¹ c dr) :
    FiveRowRank.FiveRows v g d f z := by
  have ev : v = MeanRankUpdate.scaleField l⁻¹ c vr := by
    funext R
    simpa only [MeanRankUpdate.scaleField, div_inv_eq_mul, mul_comm R l] using hv R
  have eg : g = MeanRankUpdate.scaleField l⁻¹ c gr := by
    funext R
    simpa only [MeanRankUpdate.scaleField, div_inv_eq_mul, mul_comm R l] using hg R
  have ef : f = MeanRankUpdate.scaleField l⁻¹ c fr := by
    funext R
    simpa only [MeanRankUpdate.scaleField, div_inv_eq_mul, mul_comm R l] using hf R
  have ez : z = MeanRankUpdate.scaleField l⁻¹ c zr := by
    funext R
    simpa only [MeanRankUpdate.scaleField, div_inv_eq_mul, mul_comm R l] using hz R
  rw [ev, eg, ef, ez, hd]
  exact MeanRankUpdate.fiveRows_scaled (inv_pos.mpr hl) c H

theorem scalarOn_slice {l c : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {V : Set S} {f : PressureStream.Lift S → ℝ} {g : PressureStream.Lift T → ℝ}
    (H : ScalarOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c
      f g)
    {s : S} (hs : s ∈ V) (R : ℝ) : f (R,(s,0)) = c * g (l*R,(P s,0)) := by
  simpa only [GaugeStateCoherence.chartEquiv_apply, map_zero] using H (R,(s,0)) hs

/-- The five-row conclusion is transported from the actual reference
rank solve.  Both background slices here are the complete stored base. -/
theorem rankIncrementState_fiveRows_on [FiniteDimensional ℝ T]
    {l c : ℝ} (hl : 0 < l) (hc : c ≠ 0) (P : S ≃L[ℝ] T) (k : ℕ)
    {V : Set S} {U : Set T} (hV : IsOpen V) (hU : IsOpen U) (hmap : MapsTo P V U)
    {C : CorrectionState.Context (PressureStream.Lift S)}
    {Cr : CorrectionState.Context (PressureStream.Lift T)}
    {u : CorrectionState.State (PressureStream.Lift S)}
    {ur : CorrectionState.State (PressureStream.Lift T)} {n nr : ℕ}
    (H : StateOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k) c
      l u ur n nr)
    (G : ContextOn (PhysicalMeanDomain.slowDomain V) (GaugeStateCoherence.chartEquiv l hl.ne' P k)
      c l C Cr n nr)
    (R : DebtRegular U Cr ur nr)
    {r : CorrectionState.RankData S} {rr : CorrectionState.RankData T}
    (K : RankOn V P l c r rr n nr)
    {g : VariableGaugeMean.GaugeData S} {gr : VariableGaugeMean.GaugeData T}
    (J : GaugeOn V l P.toContinuousLinearMap k g gr n nr)
    (F : LocalRankDefect.RankGeometry gr rr U Cr ur)
    (axial : S × PressureStream.Plane) (axialr : T × PressureStream.Plane)
    (ha : (P.toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k))
        (C.operators.epsilon n • axial) = l • (Cr.operators.epsilon nr • axialr))
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hleft : ∀ m t, t ∈ U → lo ≤ rr.length m t * rr.inner)
    (hright : ∀ m t, t ∈ U → rr.length m t * rr.outer ≤ hi)
    {s : S} (hs : s ∈ V) :
    FiveRowRank.FiveRows (DefectIncrementBounds.slowSlice C.base.angular n s)
      (DefectIncrementBounds.slowSlice C.base.axial n s) (CorrectionState.debt C u n s)
      (DefectIncrementBounds.slowSlice (VariableGaugeMean.rankIncrementState g r axial C u).angular
        n s)
      (DefectIncrementBounds.slowSlice (VariableGaugeMean.rankIncrementState g r axial C u).axial n
        s) := by
  have hinc := rankIncrementState_on hl hc P k hV hU hmap H G R K J F axial axialr ha
  exact fiveRows_chart hl (F.fiveRows hlo hlohi hU hleft hright axialr nr (hmap hs))
    (scalarOn_slice hl P k G.base.angular hs) (scalarOn_slice hl P k G.base.axial hs)
    (scalarOn_slice hl P k hinc.angular hs) (scalarOn_slice hl P k hinc.axial hs)
    (measured_debt_on hl P k hV hU hmap H G R hs)

/-- The physical axial unit has the required chart differential, with the
actual viscosity/axial coefficient `Q^h`. -/
theorem band_axial_vector (h : ℝ) (n m k : ℕ) :
    ((bandSlowEquiv h n m).toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k))
      (ChartScales.Q n ^ h • (((0,1) : PressureStream.Plane), (0 : PressureStream.Plane))) =
      bandScale n m • (ChartScales.Q m ^ h • (((0,1) : PressureStream.Plane), (0 :
        PressureStream.Plane))) := by
  have hQ : 0 < ChartScales.Q n / ChartScales.Q m := div_pos (ChartScales.Q_pos n)
    (ChartScales.Q_pos m)
  have he : ChartScales.Q n ^ h = (ChartScales.Q n / ChartScales.Q m)^h * ChartScales.Q m ^ h := by
    rw [Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]
    exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos (ChartScales.Q_pos m) h).ne').symm
  have hp : (ChartScales.Q n / ChartScales.Q m)^CoordinateAlgebra.D h * ChartScales.Q n ^ h =
      bandScale n m * ChartScales.Q m ^ h := by
    rw [he, ← mul_assoc, ← Real.rpow_add hQ]
    congr 2
    unfold CoordinateAlgebra.D
    ring
  apply Prod.ext
  · apply Prod.ext
    · simp [bandSlowEquiv_apply]
    · change (ChartScales.Q n / ChartScales.Q m)^CoordinateAlgebra.D h * (ChartScales.Q n ^ h * 1) =
        bandScale n m * (ChartScales.Q m ^ h * 1)
      simpa only [mul_one] using hp
  · simp

/-- Concrete normalized rank stage at the common cover.  Every rank
parameter and axial scaling law is derived from the shared data. -/
theorem normalized_rankStageState_on {h d a b M B lam ra rb : ℝ}
    (hh : 0 < h) (hh1 : h < 1/2) (hab : a < b)
    (index : ℕ → ℕ) (n m k : ℕ) (hi : index n + k = index m)
    {V U : Set PressureStream.Plane} (hV : IsOpen V) (hU : IsOpen U)
    (htime : ∀ s ∈ V, 0 < s.1) (hmap : MapsTo (bandSlowEquiv h n m) V U)
    (C Cr : CorrectionState.Context (PressureStream.Lift PressureStream.Plane))
    (u ur : CorrectionState.State (PressureStream.Lift PressureStream.Plane))
    (H : StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) u ur n m)
    (G : ContextOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) C Cr n m)
    (R : DebtRegular U Cr ur m)
    (F : LocalRankDefect.RankGeometry (VariableGaugeMean.similarityGauge h d a b M hab index)
      (RankStateBounds.normalizedData (2*h) (CoordinateAlgebra.A h) B lam ra rb) U Cr ur)
    (heps : C.operators.epsilon n = ChartScales.Q n ^ h)
    (hepsr : Cr.operators.epsilon m = ChartScales.Q m ^ h)
    (hf : ContDiffOn ℝ ∞ ((rankAddedState (VariableGaugeMean.similarityGauge h d a b M hab index)
      (RankStateBounds.normalizedData (2*h) (CoordinateAlgebra.A h) B lam ra rb) ((0,1),0) Cr
        ur).gr Cr m)
      (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U ((rankAddedState (VariableGaugeMean.similarityGauge h d a
      b M hab index)
      (RankStateBounds.normalizedData (2*h) (CoordinateAlgebra.A h) B lam ra rb) ((0,1),0) Cr
        ur).gr Cr m))
    (hs : VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength (2*h)) U
      ((rankAddedState (VariableGaugeMean.similarityGauge h d a b M hab index)
        (RankStateBounds.normalizedData (2*h) (CoordinateAlgebra.A h) B lam ra rb) ((0,1),0) Cr
          ur).gr Cr m)) :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m)
      (VariableGaugeMean.rankStageState (VariableGaugeMean.similarityGauge h d a b M hab index)
        (RankStateBounds.normalizedData (2*h) (CoordinateAlgebra.A h) B lam ra rb) ((0,1),0) C u)
      (VariableGaugeMean.rankStageState (VariableGaugeMean.similarityGauge h d a b M hab index)
        (RankStateBounds.normalizedData (2*h) (CoordinateAlgebra.A h) B lam ra rb) ((0,1),0) Cr ur)
          n m := by
  apply rankStageState_on (bandScale_pos n m)
    (Real.rpow_pos_of_pos (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)) _).ne'
    (bandSlowEquiv h n m) k hV hU hmap H G R
    (normalized_rank_on hh hh1 B lam ra rb n m htime)
    (similarityGaugeOn hh hh1 d a b M hab index n m k hi htime) F ((0,1),0) ((0,1),0) _ hf hp hs
  rw [heps, hepsr]
  exact band_axial_vector h n m k

end NavierStokes.RankStateCoherence
