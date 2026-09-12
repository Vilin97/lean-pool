/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStateRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeAliasDecay

/-!
# Full-vector bounds for the actual moving-gauge excluded aliases

The pressure source class is derived from the primitive base, operators,
mean, and covariance.  Scalar alias estimates are then applied to that
actual source and lifted through fixed linear component maps.  All
regularity is supplied by the incoming primitive fields and the genuine
pressure reconstruction, not by a hypothesis on an alias output.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GaugeExcludedBounds

open Set Function Filter WeightedClasses MeanIncrementBounds
open VariableGaugeMean LocalSignedRequest
open scoped Topology ContDiff BigOperators

section RadialSource

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- An ordinary class for the literal radial forcing, before pressure
reconstruction.  No class of `gr` is an input. -/
theorem radialSource_mem {s : StripData D} {o : Operators D} {base mean : Triple D}
    {κ γ : ℝ} (ho : OperatorBounds s o κ) (hb : BaseBounds s base)
    (hm : MeanIncrementBounds.CumulativeBounds s mean)
    (W : Fin 3 → Fin 3 → MeanIncrementBounds.Field D) (hW : ∀ i j, MeanClass s γ (W i j)) :
    MeanClass s (min (9 / 10) γ - 2 * κ) (gr o base mean W) := by
  let ν : ℝ := min (9 / 10) γ
  have hν : ν ≤ 9 / 10 := min_le_left _ _
  have hνγ : ν ≤ γ := min_le_right _ _
  have hκ := ho.kappa_nonneg
  have hrr : MeanClass s ν (radialRadial base mean) :=
    ((Class.smul (Class.coefficient_mul hb.radial hm.radial) 2).mono_exponent (by linarith)).add
      ((Class.product hm.radial hm.radial ho.weight_le_one).mono_exponent (by linarith))
  have hzr : MeanClass s ν (axialRadial base mean) :=
    (((Class.coefficient_mul hb.radial hm.axial).mono_exponent (by linarith)).add
      ((Class.mul_coefficient hm.radial hb.axial).mono_exponent (by linarith))).add
        ((Class.product hm.radial hm.axial ho.weight_le_one).mono_exponent (by linarith))
  have hθ : MeanClass s ν (radialAngular base mean) :=
    ((Class.smul (Class.coefficient_mul hb.angular hm.angular) 2).mono_exponent (by linarith)).add
      ((Class.product hm.angular hm.angular ho.weight_le_one).mono_exponent (by linarith))
  have ht : MeanClass s (ν - 2 * κ) (o.time mean.radial) :=
    (ho.time hm.radial).mono_exponent (by linarith)
  have hr : MeanClass s (ν - 2 * κ) (o.radialDiv 1 (radialRadial base mean + W 0 0)) :=
    (ho.radialDiv (hrr.add ((hW 0 0).mono_exponent hνγ)) 1).mono_exponent (by linarith)
  have hz : MeanClass s (ν - 2 * κ) (o.dz (axialRadial base mean + W 2 0)) :=
    (ho.dz (hzr.add ((hW 2 0).mono_exponent hνγ))).mono_exponent (by linarith)
  have hi : MeanClass s (ν - 2 * κ) (o.invRadius * (radialAngular base mean + W 1 1)) :=
    (ho.inv_mul (hθ.add ((hW 1 1).mono_exponent hνγ))).mono_exponent (by linarith)
  have hv : MeanClass s (ν - 2 * κ) (o.viscosity 1 mean.radial) :=
    (ho.viscosity hm.radial 1).mono_exponent (by linarith)
  exact Class.neg (Class.sub (Class.sub ((ht.add hr).add hz) hi) hv)

theorem state_gr_mem {s : StripData D} {c : CorrectionState.Context D}
    {u : CorrectionState.State D} {κ γ : ℝ}
    (ho : OperatorBounds s c.operators κ) (hb : BaseBounds s c.base)
    (hu : CorrectionState.CumulativeBounds s u)
    (hW : ∀ i j, MeanClass s γ (u.covariance i j)) :
    MeanClass s (min (9 / 10) γ - 2 * κ) (u.gr c) :=
  radialSource_mem ho hb hu.velocity u.covariance hW

theorem meanClass_unweighted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData D} {β : ℝ} {f : ℕ → D → E}
    (hf : MeanClass s β f) (hζ : ∀ x ∈ s.domain, s.zeta x ≤ 1) :
    UnweightedClass s β f :=
  hf.mono_weight (fun _ _ _ => zero_le_one) (fun _ x hx => hζ x hx)

end RadialSource

section VectorLifts

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem pressureAlias_axisymmetric (g : GaugeData S)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S))
    (n : ℕ) (z : PressureStream.Lift S) (θ : ℝ) :
    pressureAliasState g c u n (z, θ) = pressureAliasState g c u n (z, 0) := rfl

theorem temporalAlias_axisymmetric (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S))
    (n : ℕ) (z : PressureStream.Lift S) (θ : ℝ) :
    temporalAliasState g h index c u n (z, θ) = temporalAliasState g h index c u n (z, 0) := rfl

theorem pressureAlias_vector_mem {s : StripData (PressureStream.Lift S)} {β : ℝ}
    (g : GaugeData S) (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S))
    (hf : MeanClass s β (fun n z => pressureAliasState g c u n (z, 0) 0)) :
    MeanClass s β (fun n z => pressureAliasState g c u n (z, 0)) := by
  have hm := hf.map (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) 0)
  convert! hm using 1
  funext n z i
  fin_cases i <;> simp [pressureAliasState]

theorem temporalAlias_vector_mem {s : StripData (PressureStream.Lift S)} {β : ℝ}
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S))
    (hf : MeanClass s β (fun n z => temporalAliasState g h index c u n (z, 0) 2)) :
    MeanClass s β (fun n z => temporalAliasState g h index c u n (z, 0)) := by
  have hm := hf.map (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) 2)
  convert! hm using 1
  funext n z i
  fin_cases i <;> simp [temporalAliasState]

theorem pressureAlias_angle_mem {s : StripData (PressureStream.Lift S)} {β : ℝ}
    (g : GaugeData S) (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S))
    (hf : MeanClass s β (fun n z => pressureAliasState g c u n (z, 0) 0)) :
    MeanClass (HarmonicWaveInteraction.productStrip s) β (pressureAliasState g c u) :=
  HarmonicWaveInteraction.class_lift (pressureAlias_vector_mem g c u hf)

theorem temporalAlias_angle_mem {s : StripData (PressureStream.Lift S)} {β : ℝ}
    (g : GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (c : CorrectionState.Context (PressureStream.Lift S))
    (u : CorrectionState.State (PressureStream.Lift S))
    (hf : MeanClass s β (fun n z => temporalAliasState g h index c u n (z, 0) 2)) :
    MeanClass (HarmonicWaveInteraction.productStrip s) β (temporalAliasState g h index c u) :=
  HarmonicWaveInteraction.class_lift (temporalAlias_vector_mem g h index c u hf)

end VectorLifts

section MovingWeight

theorem movingStrip_zeta_le_one {coord a b cL cR : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (x : MeanStateRegularity.Point) :
    (movingStripData U a b cL cR ha hcL hcR ε L hε hεone hL).zeta x ≤ 1 := by
  change WeightedRadialPrimitive.zeta cL cR (WeightedRadialPrimitive.logLength a b)
    (WeightedRadialPrimitive.logPosition a (profileMap coord x).1) ≤ 1
  unfold WeightedRadialPrimitive.zeta
  exact (mul_le_mul (WeightedRadialPrimitive.edge_le_one hcL.le _)
    (WeightedRadialPrimitive.edge_le_one hcR.le _) (FlatCutoff.edge_nonneg _ _)
    zero_le_one).trans_eq (one_mul 1)

end MovingWeight

/-- The actual moving strip, with the manuscript's band scale. -/
noncomputable abbrev actualStrip {a b h cL cR : ℝ}
    (U : SlowRegion (2 * h)) (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) : StripData MeanStateRegularity.Point :=
  movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
    (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL

/-- The actual moving pressure/stream gauge. -/
noncomputable abbrev actualGauge (h a b Mbase : ℝ) (hab : a < b) (index : ℕ → ℕ) :=
  similarityGauge h (ChartScales.radialExponent h) a b Mbase hab index

section ActualAliases

/-- Point: an abbreviation for `MeanStateRegularity.Point`. -/
abbrev Point := MeanStateRegularity.Point

variable {a b h Mbase cL cR : ℝ}
  (U : SlowRegion (2 * h)) (ha : 0 < a) (hab : a < b)
  (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h) (hM : Mbase ≠ 0)
  (index : ℕ → ℕ) (D : ℕ)
  (hgapLower : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
  (hgapUpper : ∀ n, index n ≤ ChartScales.nativeIndex h n + D)
  (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
  (c : CorrectionState.Context Point) (u : CorrectionState.State Point)

include hM D hgapLower hS in
/-- The actual pressure alias as a full vector, both on the stripped
domain and on its angular lift.  Its source class is derived internally. -/
theorem pressureAliasState_mean_bounds {κ γ : ℝ}
    (H : MeanStateRegularity.PrimitiveData U a b c u)
    (ho : OperatorBounds (actualStrip (b := b) U ha hcL hcR hh L hL) c.operators κ)
    (hb : BaseBounds (actualStrip (b := b) U ha hcL hcR hh L hL) c.base)
    (hu : CorrectionState.CumulativeBounds (actualStrip (b := b) U ha hcL hcR hh L hL) u)
    (hW : ∀ i j, MeanClass (actualStrip (b := b) U ha hcL hcR hh L hL) γ (u.covariance i j)) (β :
        ℝ) :
    MeanClass (actualStrip (b := b) U ha hcL hcR hh L hL) β
      (fun n z => pressureAliasState (actualGauge h a b Mbase hab index) c u n (z, 0)) ∧
      MeanClass (HarmonicWaveInteraction.productStrip (actualStrip (b := b) U ha hcL hcR hh L hL)) β
        (pressureAliasState (actualGauge h a b Mbase hab index) c u) := by
  have hreg := H.source ha hab
  have hgr := state_gr_mem ho hb hu hW
  have hs := GaugeAliasDecay.pressureAliasState_radial_mem U ha hab hcL hcR hh hM index D
    hgapLower L hL hS c u hreg.smooth hreg.supported hreg.periodic hgr β
  exact ⟨pressureAlias_vector_mem (actualGauge h a b Mbase hab index) c u hs,
    pressureAlias_angle_mem (actualGauge h a b Mbase hab index) c u hs⟩

include hM D hgapLower hS in
/-- Every real target power is available, hence every positive one.
The vector signs are those of the literal `pressureAliasState`. -/
theorem pressureAliasState_bounds {κ γ : ℝ}
    (H : MeanStateRegularity.PrimitiveData U a b c u)
    (ho : OperatorBounds (actualStrip (b := b) U ha hcL hcR hh L hL) c.operators κ)
    (hb : BaseBounds (actualStrip (b := b) U ha hcL hcR hh L hL) c.base)
    (hu : CorrectionState.CumulativeBounds (actualStrip (b := b) U ha hcL hcR hh L hL) u)
    (hW : ∀ i j, MeanClass (actualStrip (b := b) U ha hcL hcR hh L hL) γ (u.covariance i j)) (β :
        ℝ) :
    UnweightedClass (actualStrip (b := b) U ha hcL hcR hh L hL) β
      (fun n z => pressureAliasState (actualGauge h a b Mbase hab index) c u n (z, 0)) ∧
      UnweightedClass (HarmonicWaveInteraction.productStrip (actualStrip (b := b) U ha hcL hcR hh L
          hL)) β
        (pressureAliasState (actualGauge h a b Mbase hab index) c u) := by
  obtain ⟨hv, hl⟩ := pressureAliasState_mean_bounds U ha hab hcL hcR hh hM index D hgapLower
    L hL hS c u H ho hb hu hW β
  have hζ (x : Point) : (actualStrip (b := b) U ha hcL hcR hh L hL).zeta x ≤ 1 :=
    movingStrip_zeta_le_one U ha hcL hcR _ L _ _ hL x
  exact ⟨meanClass_unweighted hv (fun x _ => hζ x),
    meanClass_unweighted hl (fun x _ => hζ x.1)⟩

include hM D hgapLower hgapUpper hS in
/-- Regularity of the actual raw axial residual follows from the
primitive fields and the pressure reconstruction invariant.  Only its
ordinary incoming class is an induction input. -/
theorem temporalAliasState_mean_bounds {α : ℝ}
    (H : MeanStateRegularity.PrimitiveData U a b c u)
    (hfixed : (reconstructState (actualGauge h a b Mbase hab index) c u).pressure = u.pressure)
    (hfast : c.operators.fastCoefficient =
      fun n => ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hraw : MeanClass (actualStrip (b := b) U ha hcL hcR hh L hL) α (u.axialResidual c)) (β : ℝ) :
    MeanClass (actualStrip (b := b) U ha hcL hcR hh L hL) β
      (fun n z => temporalAliasState (actualGauge h a b Mbase hab index) h index c u n (z, 0)) ∧
      MeanClass (HarmonicWaveInteraction.productStrip (actualStrip (b := b) U ha hcL hcR hh L hL)) β
        (temporalAliasState (actualGauge h a b Mbase hab index) h index c u) := by
  have hreg := H.axial_reconstructed (g := actualGauge h a b Mbase hab index) ha
    (ChartScales.radialExponent_pos h hh.le) (fun _ => rfl) hfixed
  have hs := GaugeAliasDecay.temporalAliasState_axial_mem U ha hab hcL hcR hh hM index D
    hgapLower hgapUpper L hL hS c u hfast hv hreg.smooth hreg.supported hreg.periodic hraw β
  exact ⟨temporalAlias_vector_mem (actualGauge h a b Mbase hab index) h index c u hs,
    temporalAlias_angle_mem (actualGauge h a b Mbase hab index) h index c u hs⟩

include hM D hgapLower hgapUpper hS in
theorem temporalAliasState_bounds {α : ℝ}
    (H : MeanStateRegularity.PrimitiveData U a b c u)
    (hfixed : (reconstructState (actualGauge h a b Mbase hab index) c u).pressure = u.pressure)
    (hfast : c.operators.fastCoefficient =
      fun n => ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hraw : MeanClass (actualStrip (b := b) U ha hcL hcR hh L hL) α (u.axialResidual c)) (β : ℝ) :
    UnweightedClass (actualStrip (b := b) U ha hcL hcR hh L hL) β
      (fun n z => temporalAliasState (actualGauge h a b Mbase hab index) h index c u n (z, 0)) ∧
      UnweightedClass (HarmonicWaveInteraction.productStrip (actualStrip (b := b) U ha hcL hcR hh L
          hL)) β
        (temporalAliasState (actualGauge h a b Mbase hab index) h index c u) := by
  obtain ⟨hm, hl⟩ := temporalAliasState_mean_bounds U ha hab hcL hcR hh hM index D
    hgapLower hgapUpper L hL hS c u H hfixed hfast hv hraw β
  have hζ (x : Point) : (actualStrip (b := b) U ha hcL hcR hh L hL).zeta x ≤ 1 :=
    movingStrip_zeta_le_one U ha hcL hcR _ L _ _ hL x
  exact ⟨meanClass_unweighted hm (fun x _ => hζ x),
    meanClass_unweighted hl (fun x _ => hζ x.1)⟩

end ActualAliases

section ReconstructedInput

theorem primitiveData_reconstruct {coord a b : ℝ} {U : SlowRegion coord}
    {c : CorrectionState.Context Point} {u : CorrectionState.State Point}
    (H : MeanStateRegularity.PrimitiveData U a b c u) (g : GaugeData TorusInverse.Plane) :
    MeanStateRegularity.PrimitiveData U a b c (reconstructState g c u) :=
  ⟨H.operators, H.base, H.mean, H.covariance, H.virtualTheta, H.virtualAxial⟩

theorem reconstructed_pressure_fixed (g : GaugeData TorusInverse.Plane)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) :
    (reconstructState g c (reconstructState g c u)).pressure = (reconstructState g c u).pressure :=
        rfl

/-- For a literally reconstructed incoming state the fixed-pressure
invariant is discharged by the construction itself. -/
theorem temporalAliasState_reconstructed_bounds
    {a b h Mbase cL cR α : ℝ} (U : SlowRegion (2 * h)) (ha : 0 < a) (hab : a < b)
    (hcL : 0 < cL) (hcR : 0 < cR) (hh : 0 < h) (hM : Mbase ≠ 0)
    (index : ℕ → ℕ) (D : ℕ)
    (hgapLower : ∀ n, ChartScales.nativeIndex h n ≤ index n + D)
    (hgapUpper : ∀ n, index n ≤ ChartScales.nativeIndex h n + D)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hS : ∀ n, ChartScales.S n ≤ L n)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData U a b c u)
    (hfast : c.operators.fastCoefficient =
      fun n => ChartScales.Tg ^ index n * ChartScales.Q n ^ (1 + h))
    (hv : c.operators.vT = (0, (0, TorusInverse.vector .temporal)))
    (hraw : MeanClass
      (movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
        (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL) α
      ((reconstructState (similarityGauge h (ChartScales.radialExponent h) a b Mbase hab index) c
          u).axialResidual c))
    (β : ℝ) :
    let g := similarityGauge h (ChartScales.radialExponent h) a b Mbase hab index
    let s := movingStripData U a b cL cR ha hcL hcR (ChartScales.epsilon h) L
      (ChartScales.epsilon_pos h) (ChartScales.epsilon_le_one h hh.le) hL
    UnweightedClass s β (fun n z => temporalAliasState g h index c (reconstructState g c u) n (z,
        0)) ∧
      UnweightedClass (HarmonicWaveInteraction.productStrip s) β
        (temporalAliasState g h index c (reconstructState g c u)) := by
  dsimp only
  exact temporalAliasState_bounds U ha hab hcL hcR hh hM index D hgapLower hgapUpper L hL hS c _
    (primitiveData_reconstruct H _) (reconstructed_pressure_fixed _ c u) hfast hv hraw β

end ReconstructedInput

end NavierStokes.GaugeExcludedBounds
