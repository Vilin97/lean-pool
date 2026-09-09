/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeMomentBalances
public import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSumBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalRankDefect

/-!
# The mean gain of the actual signed wave update

The state is updated with the same primary/signed native pulses and its
pressure is recomputed by the moving-gauge operator.  The removed physical
bumps are controlled by actual moment identities; the complete covariance
remainder retains the signed square and the curl terms.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.SignedMeanGain

open Set Function Filter MeasureTheory
open scoped ContDiff Topology BigOperators
open WeightedClasses MeanIncrementBounds CorrectionState

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Scalar field: an abbreviation for `MeanIncrementBounds.Field D`. -/
abbrev ScalarField (D : Type) := MeanIncrementBounds.Field D
/-- Tensor: an abbreviation for `Fin 3 → Fin 3 → ScalarField D`. -/
abbrev Tensor (D : Type) := Fin 3 → Fin 3 → ScalarField D

/-- These are changes of the literal covariance terms in (32). -/
noncomputable def thetaCovarianceChange (o : Operators D) (X : Tensor D) : ScalarField D :=
  o.radialDiv 2 (X 0 1) + o.dz (X 2 1)

/-- Axial covariance change, given by `o.radialDiv 1 (X 0 2) + o.dz (X 2 2)`. -/
noncomputable def axialCovarianceChange (o : Operators D) (X : Tensor D) : ScalarField D :=
  o.radialDiv 1 (X 0 2) + o.dz (X 2 2)

/-- Radial covariance change, given by `-o.radialDiv 1 (X 0 0) - o.dz (X 2 0) + o.invRadius * X
1 1`. -/
noncomputable def radialCovarianceChange (o : Operators D) (X : Tensor D) : ScalarField D :=
  -o.radialDiv 1 (X 0 0) - o.dz (X 2 0) + o.invRadius * X 1 1

theorem smooth_updated {U : Set D} {m h : Triple D}
    (hm : SmoothTriple U m) (hh : SmoothTriple U h) : SmoothTriple U (updated m h) :=
  ⟨hm.radial.add hh.radial, hm.angular.add hh.angular, hm.axial.add hh.axial⟩

section CovarianceChanges

variable {U : Set D} (hU : IsOpen U) (o : Operators D)
  {b m : Triple D} (hb : SmoothTriple U b) (hm : SmoothTriple U m)
  (W X : Tensor D) (hW : ∀ i j, SmoothOn U (W i j))
  (hX : ∀ i j, SmoothOn U (X i j))

include hU hb hm hW hX in
theorem thetaResidual_covariance_change (T : ScalarField D) :
    Agree U (thetaResidual o b m (W + X) T - thetaResidual o b m W T)
      (thetaCovarianceChange o X) := by
  have hr : thetaRadial b m + (W + X) 0 1 = (thetaRadial b m + W 0 1) + X 0 1 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  have hz : thetaAxial b m + (W + X) 2 1 = (thetaAxial b m + W 2 1) + X 2 1 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  simp only [Pi.add_apply] at hr hz
  intro n x hx
  simp only [thetaResidual, Pi.sub_apply, Pi.add_apply]
  rw [hr, hz, o.radialDiv_add hU 2 ((hb.thetaRadial hm).add (hW 0 1)) (hX 0 1) n hx,
    o.dz_add hU ((hb.thetaAxial hm).add (hW 2 1)) (hX 2 1) n hx]
  simp only [thetaCovarianceChange, Pi.add_apply]
  ring

include hU hb hm hW hX in
theorem axialResidual_covariance_change (p T : ScalarField D) (hp : SmoothOn U p) :
    Agree U (axialResidual o b m (W + X) p T - axialResidual o b m W p T)
      (axialCovarianceChange o X) := by
  have hr : axialRadial b m + (W + X) 0 2 = (axialRadial b m + W 0 2) + X 0 2 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  have hz : axialAxial b m + (W + X) 2 2 + p = (axialAxial b m + W 2 2 + p) + X 2 2 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  simp only [Pi.add_apply] at hr hz
  intro n x hx
  simp only [axialResidual, Pi.sub_apply, Pi.add_apply]
  rw [hr, hz, o.radialDiv_add hU 1 ((hb.axialRadial hm).add (hW 0 2)) (hX 0 2) n hx,
    o.dz_add hU (((hb.axialAxial hm).add (hW 2 2)).add hp) (hX 2 2) n hx]
  simp only [axialCovarianceChange, Pi.add_apply]
  ring

include hU hb hm hW hX in
theorem gr_covariance_change :
    Agree U (gr o b m (W + X) - gr o b m W) (radialCovarianceChange o X) := by
  have hr : radialRadial b m + (W + X) 0 0 = (radialRadial b m + W 0 0) + X 0 0 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  have hz : axialRadial b m + (W + X) 2 0 = (axialRadial b m + W 2 0) + X 2 0 := by
    funext n x
    simp only [Pi.add_apply]
    ring
  simp only [Pi.add_apply] at hr hz
  intro n x hx
  simp only [gr, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.mul_apply]
  rw [hr, hz, o.radialDiv_add hU 1 ((hb.radialRadial hm).add (hW 0 0)) (hX 0 0) n hx,
    o.dz_add hU ((hb.axialRadial hm).add (hW 2 0)) (hX 2 0) n hx]
  simp only [radialCovarianceChange, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.mul_apply]
  ring

end CovarianceChanges

/-- A bound on each actual tensor entry. It is not a bound on the resulting
residual and contains no update-preservation assertion. -/
def TensorClass (s : StripData D) (α : ℝ) (X : Tensor D) : Prop :=
  ∀ i j, MeanClass s α (X i j)

section CovarianceBounds

variable {s : StripData D} {o : Operators D} {κ α : ℝ}
  (ho : OperatorBounds s o κ) {X : Tensor D} (hX : TensorClass s α X)

include ho hX in
theorem thetaCovarianceChange_mem :
    MeanClass s (α - κ) (thetaCovarianceChange o X) := by
  exact (ho.radialDiv (hX 0 1) 2).add
    ((ho.dz (hX 2 1)).mono_exponent (by linarith [ho.kappa_nonneg]))

include ho hX in
theorem axialCovarianceChange_mem :
    MeanClass s (α - κ) (axialCovarianceChange o X) := by
  exact (ho.radialDiv (hX 0 2) 1).add
    ((ho.dz (hX 2 2)).mono_exponent (by linarith [ho.kappa_nonneg]))

include ho hX in
theorem radialCovarianceChange_mem :
    MeanClass s (α - κ) (radialCovarianceChange o X) := by
  exact (Class.sub (Class.neg (ho.radialDiv (hX 0 0) 1))
    ((ho.dz (hX 2 0)).mono_exponent (by linarith [ho.kappa_nonneg]))).add
    ((ho.inv_mul (hX 1 1)).mono_exponent (by linarith [ho.kappa_nonneg]))

end CovarianceBounds


/-! ## Literal state and covariance increments -/

/-- Zero triple, given by `⟨0, 0, 0⟩`. -/
noncomputable def zeroTriple : Triple D := ⟨0, 0, 0⟩

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem updated_zeroTriple (m : Triple D) : updated m zeroTriple = m := by
  cases m
  simp [updated, zeroTriple]

/-- Covariance increment, given by `bilinearCovariance (u + w) (u + w) - bilinearCovariance u
u`. -/
noncomputable def covarianceIncrement (u w : Oscillation D) : Tensor D :=
  bilinearCovariance (u + w) (u + w) - bilinearCovariance u u

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_increment_split (p u t k : Oscillation D)
    (hu : LabelSumBounds.AngularContinuous u)
    (ht : LabelSumBounds.AngularContinuous t)
    (hk : LabelSumBounds.AngularContinuous k) :
    covarianceIncrement u (t + k) = LabelSumBounds.symmetricCovariance p t +
      LabelSumBounds.signedRemainder p u t k := by
  rw [covarianceIncrement, LabelSumBounds.covariance_increment_exact u (t + k) hu (ht.add hk)]
  unfold LabelSumBounds.signedRemainder
  abel

section ActualState

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- Wave stage, given by `VariableGaugeMean.reconstructState g c (u.addIncrement zeroTriple 0 w
q ⟨0, gaussian, 0⟩)`. -/
noncomputable def waveStage (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (w : Oscillation (PressureStream.Lift S)) (q : OscillatoryScalar (PressureStream.Lift S))
    (gaussian : Oscillation (PressureStream.Lift S)) : State (PressureStream.Lift S) :=
  VariableGaugeMean.reconstructState g c (u.addIncrement zeroTriple 0 w q ⟨0, gaussian, 0⟩)

/-- Pressure change, given by `(waveStage g c u w q gaussian).pressure - u.pressure`. -/
noncomputable def pressureChange (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (w : Oscillation (PressureStream.Lift S)) (q : OscillatoryScalar (PressureStream.Lift S))
    (gaussian : Oscillation (PressureStream.Lift S)) : ScalarField (PressureStream.Lift S) :=
  (waveStage g c u w q gaussian).pressure - u.pressure

theorem waveStage_mean (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (w : Oscillation (PressureStream.Lift S)) (q : OscillatoryScalar (PressureStream.Lift S))
    (gaussian : Oscillation (PressureStream.Lift S)) :
    (waveStage g c u w q gaussian).mean = u.mean := updated_zeroTriple u.mean

theorem waveStage_covariance (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (w : Oscillation (PressureStream.Lift S)) (q : OscillatoryScalar (PressureStream.Lift S))
    (gaussian : Oscillation (PressureStream.Lift S)) :
    (waveStage g c u w q gaussian).covariance = u.covariance + covarianceIncrement u.oscillation w
        := by
  change bilinearCovariance (u.oscillation + w) (u.oscillation + w) = _
  unfold covarianceIncrement State.covariance
  abel

theorem waveStage_gaussian (g : VariableGaugeMean.GaugeData S)
    (c : Context (PressureStream.Lift S)) (u : State (PressureStream.Lift S))
    (w : Oscillation (PressureStream.Lift S)) (q : OscillatoryScalar (PressureStream.Lift S))
    (gaussian : Oscillation (PressureStream.Lift S)) :
    (waveStage g c u w q gaussian).errors.gaussian = u.errors.gaussian + gaussian := rfl

theorem waveStage_theta_change {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (g : VariableGaugeMean.GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (gaussian : Oscillation (PressureStream.Lift S))
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hX : ∀ i j, SmoothOn U (covarianceIncrement u.oscillation w i j)) :
    Agree U ((waveStage g c u w q gaussian).thetaResidual c - u.thetaResidual c)
      (thetaCovarianceChange c.operators (covarianceIncrement u.oscillation w)) := by
  change Agree U (MeanIncrementBounds.thetaResidual c.operators c.base
    (waveStage g c u w q gaussian).mean (waveStage g c u w q gaussian).covariance c.virtualTheta -
        _) _
  rw [waveStage_mean, waveStage_covariance]
  exact thetaResidual_covariance_change hU c.operators hb hm u.covariance
    (covarianceIncrement u.oscillation w) hW hX c.virtualTheta

theorem waveStage_gr_change {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (g : VariableGaugeMean.GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (gaussian : Oscillation (PressureStream.Lift S))
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hX : ∀ i j, SmoothOn U (covarianceIncrement u.oscillation w i j)) :
    Agree U ((waveStage g c u w q gaussian).gr c - u.gr c)
      (radialCovarianceChange c.operators (covarianceIncrement u.oscillation w)) := by
  change Agree U (MeanIncrementBounds.gr c.operators c.base
    (waveStage g c u w q gaussian).mean (waveStage g c u w q gaussian).covariance - _) _
  rw [waveStage_mean, waveStage_covariance]
  exact gr_covariance_change hU c.operators hb hm u.covariance
    (covarianceIncrement u.oscillation w) hW hX

theorem axialResidual_pressure_change {U : Set D} (hU : IsOpen U) (o : Operators D)
    {b m : Triple D} (hb : SmoothTriple U b) (hm : SmoothTriple U m)
    (W : Tensor D) (hW : ∀ i j, SmoothOn U (W i j))
    (p q T : ScalarField D) (hp : SmoothOn U p) (hq : SmoothOn U q) :
    Agree U (MeanIncrementBounds.axialResidual o b m W (p + q) T -
      MeanIncrementBounds.axialResidual o b m W p T) (o.dz q) := by
  have he : axialAxial b m + W 2 2 + (p + q) = (axialAxial b m + W 2 2 + p) + q := by abel
  intro n x hx
  simp only [MeanIncrementBounds.axialResidual, Pi.sub_apply, Pi.add_apply]
  rw [he, o.dz_add hU (((hb.axialAxial hm).add (hW 2 2)).add hp) hq n hx]
  simp only [Pi.add_apply]
  ring

theorem waveStage_axial_change {U : Set (PressureStream.Lift S)} (hU : IsOpen U)
    (g : VariableGaugeMean.GaugeData S) (c : Context (PressureStream.Lift S))
    (u : State (PressureStream.Lift S)) (w : Oscillation (PressureStream.Lift S))
    (q : OscillatoryScalar (PressureStream.Lift S)) (e : Oscillation (PressureStream.Lift S))
    (hb : SmoothTriple U c.base) (hm : SmoothTriple U u.mean)
    (hW : ∀ i j, SmoothOn U (u.covariance i j))
    (hX : ∀ i j, SmoothOn U (covarianceIncrement u.oscillation w i j))
    (hp : SmoothOn U u.pressure) (hδp : SmoothOn U (pressureChange g c u w q e)) :
    Agree U ((waveStage g c u w q e).axialResidual c - u.axialResidual c)
      (axialCovarianceChange c.operators (covarianceIncrement u.oscillation w) +
        c.operators.dz (pressureChange g c u w q e)) := by
  have hpressure : (waveStage g c u w q e).pressure =
      u.pressure + pressureChange g c u w q e := by unfold pressureChange; abel
  have hc := axialResidual_covariance_change hU c.operators hb hm u.covariance
    (covarianceIncrement u.oscillation w) hW hX
    (u.pressure + pressureChange g c u w q e) c.virtualAxial (hp.add hδp)
  have hd := axialResidual_pressure_change hU c.operators hb hm u.covariance hW
    u.pressure (pressureChange g c u w q e) c.virtualAxial hp hδp
  intro n x hx
  have hc' := hc n hx
  have hd' := hd n hx
  change MeanIncrementBounds.axialResidual c.operators c.base (waveStage g c u w q e).mean
    (waveStage g c u w q e).covariance (waveStage g c u w q e).pressure c.virtualAxial n x - _ = _
  rw [waveStage_mean, waveStage_covariance g c u w q e, hpressure]
  simp only [Pi.add_apply, Pi.sub_apply] at hc' hd' ⊢
  change _ - MeanIncrementBounds.axialResidual c.operators c.base u.mean u.covariance
    u.pressure c.virtualAxial n x = _
  linarith


end ActualState


/-! ## Averaging on the actual open slow domain -/

section LocalAverage

variable {S : Type} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]

open StateMomentBalances PhysicalMeanDomain

omit [FiniteDimensional ℝ S] in
theorem torus_slice_continuous {U : Set S} {f : PressureStream.Lift S → ℝ}
    (hf : ContDiffOn ℝ ∞ f (slowDomain U)) {x : ℝ × S} (hx : x.2 ∈ U) :
    Continuous (fun Y : PressureStream.Plane => f (x.1, (x.2, Y))) := by
  exact hf.continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_const.prodMk continuous_id)) (fun _ => hx)

omit [FiniteDimensional ℝ S] in
theorem meanBar_add_on {U : Set S} {f g : ScalarField (PressureStream.Lift S)}
    (hf : SmoothOn (slowDomain U) f) (hg : SmoothOn (slowDomain U) g)
    (n : ℕ) {x : PressureStream.Lift S} (hx : x.2.1 ∈ U) :
    meanBar (f + g) n x = meanBar f n x + meanBar g n x := by
  exact FourierAlias.torusMean_add
    (torus_slice_continuous (hf n) hx) (torus_slice_continuous (hg n) hx)

omit [FiniteDimensional ℝ S] in
theorem meanBar_sub_on {U : Set S} {f g : ScalarField (PressureStream.Lift S)}
    (hf : SmoothOn (slowDomain U) f) (hg : SmoothOn (slowDomain U) g)
    (n : ℕ) {x : PressureStream.Lift S} (hx : x.2.1 ∈ U) :
    meanBar (f - g) n x = meanBar f n x - meanBar g n x := by
  exact FourierAlias.torusMean_sub
    (torus_slice_continuous (hf n) hx) (torus_slice_continuous (hg n) hx)

theorem meanBar_radialDiv_on {U : Set S} (hU : IsOpen U)
    (o : Operators (PressureStream.Lift S)) (hradius : o.radius = Prod.fst)
    (hprofile : ∀ R z Y, o.radialProfile (R, (z, Y)) = o.radialProfile (R, (z, 0)))
    {f : ScalarField (PressureStream.Lift S)} (hf : SmoothOn (slowDomain U) f)
    (hp : ∀ n, PeriodicOn U (f n)) (e : ℝ) (n : ℕ)
    {x : PressureStream.Lift S} (hx : x.2.1 ∈ U) :
    meanBar (o.radialDiv e f) n x = o.radialDiv e (meanBar f) n x := by
  obtain ⟨χ, _, hχs, hχf, he⟩ := exists_fiber_localization hU hx (hf n)
  let F : ScalarField (PressureStream.Lift S) := fun _ => localize χ (f n)
  have hl : meanBar (o.radialDiv e F) n x = meanBar (o.radialDiv e f) n x := by
    apply PressureStream.torusAverage_congr_slice
    intro Y
    have hj : fderiv ℝ (localize χ (f n)) (x.1, (x.2.1, Y)) =
        fderiv ℝ (f n) (x.1, (x.2.1, Y)) := (he.eventuallyEq x.1 Y).fderiv_eq
    have hv := (he.eventuallyEq x.1 Y).self_of_nhds
    simp only [Operators.radialDiv, Operators.dr, graphDerivative, Operators.invRadius,
      Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, F, hj, hv]
  have hb := (liftedTorusAverage_fiberLocal.germ he).eventuallyEq x.1 x.2.2
  have hr : o.radialDiv e (meanBar F) n x = o.radialDiv e (meanBar f) n x := by
    simp only [Operators.radialDiv, Operators.dr, graphDerivative, Operators.invRadius,
      Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, meanBar, F,
      hb.fderiv_eq, hb.self_of_nhds]
  exact hl.symm.trans ((congrArg (fun a : ScalarField (PressureStream.Lift S) => a n x)
    (AuxiliaryAverage.meanBar_radialDiv o hradius hprofile F (fun _ => hχf)
      (fun _ => localize_periodic hχs (hp n)) e)).trans hr)

omit [FiniteDimensional ℝ S] in
/-- Only a germ near the positive radius is used; no global extension of the
physical stress or the slow domain is assumed. -/
theorem native_radialDiv_slow_on (r : ReconstructionData) (ε fast : ℕ → ℝ)
    (z t : S) (v : PressureStream.Plane) {U : Set S} (hU : IsOpen U)
    {F : ℕ → ℝ × S → ℝ}
    (hF : SmoothOn (slowDomain U) (liftSlow F))
    (e : ℝ) (n : ℕ) {x : PressureStream.Lift S} (hx : x.2.1 ∈ U) :
    (nativeOperators r ε fast z t v).radialDiv e (liftSlow F) n x =
      IntegratedMeanBalances.radialDivergence e (fun q => F n (q, x.2.1)) x.1 := by
  have hdiff := ((hF n).contDiffAt ((slowDomain_open hU).mem_nhds hx)).differentiableAt
    (by simp)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 (x.2.1, x.2.2)))
  have hdr : deriv (fun q => F n (q, x.2.1)) x.1 =
      fderiv ℝ (liftSlow F n) x (1, (0, 0)) := hd.deriv
  have hv : fderiv ℝ (liftSlow F n) x (0, (0, r.radialDirection)) = 0 := by
    have hin : HasDerivAt (fun q : ℝ => x + q • (0, (0, r.radialDirection)))
        (0, (0, r.radialDirection)) 0 := by
      have he := (hasDerivAt_const (0 : ℝ) x).fun_add
        ((hasDerivAt_id (0 : ℝ)).smul_const (0, (0, r.radialDirection)))
      simp only [Prod.smul_mk, smul_eq_mul, mul_zero, smul_zero, hasDerivAt_const_add_iff, id_eq,
          one_smul, zero_add] at he ⊢
      exact he
    have hf0 : HasFDerivAt (liftSlow F n) (fderiv ℝ (liftSlow F n) x)
        (x + (0 : ℝ) • (0, (0, r.radialDirection))) := by simpa using hdiff.hasFDerivAt
    have hh := hf0.comp_hasDerivAt (0 : ℝ) hin
    have hc : (fun q : ℝ => liftSlow F n (x + q • (0, (0, r.radialDirection)))) =
        (fun _ => F n (x.1, x.2.1)) := by
      funext q
      simp [liftSlow]
    simpa only [zero_smul, add_zero, zero_add, one_smul, hc, Function.comp_def, deriv_const] using
        hh.deriv.symm
  simp only [Operators.radialDiv, Operators.dr, graphDerivative, Operators.invRadius,
    Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, nativeOperators, graphOperators,
    hv, mul_zero, add_zero, liftSlow, IntegratedMeanBalances.radialDivergence, hdr,
    div_eq_mul_inv, mul_assoc]

end LocalAverage


/-! ## Uniform estimates for the actual finite label sums -/

section Families

open LabelSumBounds
variable {ι : Type} {s : StripData D} {P : ι → ℕ → D → ℝ} {α δ β η : ℝ}

/-- Primitive geometry of the active label assembly; the overlap estimate
is derived by `LabelSumBounds` independently of the size of `labels n`. -/
structure Assembly (f : SignedFamily s P α δ β η) where
  /-- Width of `Assembly`, of type `ℝ`. -/
  width : ℝ
  /-- Exponent of `Assembly`, of type `ℝ`. -/
  exponent : ℝ
  /-- Vr of `Assembly`, of type `TorusInverse.Plane`. -/
  vr : TorusInverse.Plane
  /-- Vt of `Assembly`, of type `TorusInverse.Plane`. -/
  vt : TorusInverse.Plane
  /-- Slots of `Assembly`, of type `PartitionedCovariance.SlotSystem width exponent vr vt`. -/
  slots : PartitionedCovariance.SlotSystem width exponent vr vt
  /-- Label type of `Assembly`, of type `ℕ → Finset ι`. -/
  labels : ℕ → Finset ι
  /-- Label of `Assembly`, of type `ℕ → ι → SlotColoring.Label`. -/
  label : ℕ → ι → SlotColoring.Label
  injective : ∀ n, Set.InjOn (label n) (labels n : Set ι)
  level : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1
  /-- Window of `Assembly`, of type `ℕ → D → WindowPoint`. -/
  window : ℕ → D → WindowPoint
  window_continuous : ∀ n, ContinuousOn (window n) s.domain
  /-- Auxiliary of `Assembly`, of type `ℕ → D → TorusInverse.Plane`. -/
  auxiliary : ℕ → D → TorusInverse.Plane
  primary_support : SupportedOscillations slots label window auxiliary s.domain
    (fun l => (f.primary l).oscillation)
  old_support : SupportedOscillations slots label window auxiliary s.domain
    (fun l => (f.old l).oscillation)
  tangent_support : SupportedOscillations slots label window auxiliary s.domain
    (fun l => (f.tangent l).oscillation)
  curl_support : SupportedOscillations slots label window auxiliary s.domain
    (fun l => (f.curl l).oscillation)

/-- Primary field, given by `fieldSum a.labels (fun l => (f.primary l).oscillation)`. -/
noncomputable def primaryField (f : SignedFamily s P α δ β η) (a : Assembly f) : Oscillation D :=
  fieldSum a.labels (fun l => (f.primary l).oscillation)
/-- Old field, given by `fieldSum a.labels (fun l => (f.old l).oscillation)`. -/
noncomputable def oldField (f : SignedFamily s P α δ β η) (a : Assembly f) : Oscillation D :=
  fieldSum a.labels (fun l => (f.old l).oscillation)
/-- Tangent field, given by `fieldSum a.labels (fun l => (f.tangent l).oscillation)`. -/
noncomputable def tangentField (f : SignedFamily s P α δ β η) (a : Assembly f) : Oscillation D :=
  fieldSum a.labels (fun l => (f.tangent l).oscillation)
/-- Curl field, given by `fieldSum a.labels (fun l => (f.curl l).oscillation)`. -/
noncomputable def curlField (f : SignedFamily s P α δ β η) (a : Assembly f) : Oscillation D :=
  fieldSum a.labels (fun l => (f.curl l).oscillation)
/-- Remainder tensor, given by `signedRemainder (primaryField f a) (oldField f a) (tangentField
f a) (curlField f a)`. -/
noncomputable def remainderTensor (f : SignedFamily s P α δ β η) (a : Assembly f) : Tensor D :=
  signedRemainder (primaryField f a) (oldField f a) (tangentField f a) (curlField f a)
/-- Cross tensor, given by `symmetricCovariance (primaryField f a) (tangentField f a)`. -/
noncomputable def crossTensor (f : SignedFamily s P α δ β η) (a : Assembly f) : Tensor D :=
  symmetricCovariance (primaryField f a) (tangentField f a)
/-- Increment tensor, given by `covarianceIncrement (oldField f a) (tangentField f a + curlField
f a)`. -/
noncomputable def incrementTensor (f : SignedFamily s P α δ β η) (a : Assembly f) : Tensor D :=
  covarianceIncrement (oldField f a) (tangentField f a + curlField f a)

theorem incrementTensor_split (f : SignedFamily s P α δ β η) (a : Assembly f) :
    incrementTensor f a = crossTensor f a + remainderTensor f a := by
  exact covariance_increment_split _ _ _ _
    (fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _))
    (fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _))
    (fieldSum_angularContinuous _ _ (fun _ => block_angularContinuous _))

theorem remainderTensor_mem (f : SignedFamily s P α δ β η) (a : Assembly f) {γ : ℝ}
    (hβη : β ≤ η) (hγd : γ ≤ δ + β) (hγc : γ ≤ α + η) (hγs : γ ≤ 2 * β) :
    TensorClass s γ (remainderTensor f a) := by
  intro i j
  exact f.remainder_sum_mem hβη hγd hγc hγs a.labels a.label a.injective a.level
    a.window a.window_continuous a.auxiliary a.primary_support a.old_support
    a.tangent_support a.curl_support i j

theorem incrementTensor_mem (f : SignedFamily s P α δ β η) (a : Assembly f)
    (hαβ : α ≤ β) (hβη : β ≤ η) : TensorClass s (α + β) (incrementTensor f a) := by
  let inc := fun l => addBlock (f.tangent l) (f.curl l)
  have htc : ∀ l, SameCarrier (f.tangent l) (f.curl l) := fun l =>
    ⟨(f.curl_carrier l).frequency.trans (f.tangent_carrier l).frequency.symm,
      (f.curl_carrier l).phase.trans (f.tangent_carrier l).phase.symm,
      (f.curl_carrier l).angular.trans (f.tangent_carrier l).angular.symm⟩
  have he : (fun l => (inc l).oscillation) =
      (fun l => (f.tangent l).oscillation + (f.curl l).oscillation) := by
    funext l
    exact addBlock_oscillation _ _ (htc l)
  have hi : ∀ i j, UniformWaveClass s P β (fun l n x => (inc l).velocity n i j x) :=
    fun i j => (f.tangent_bounds i j).add ((f.curl_bounds i j).mono_exponent hβη)
  have hsi : SupportedOscillations a.slots a.label a.window a.auxiliary s.domain
      (fun l => (inc l).oscillation) := by
    rw [he]
    exact a.tangent_support.add a.curl_support
  intro i j
  have hh := harmonic_covariance_increment_sum_mem hαβ a.labels a.label a.injective a.level
    a.window a.window_continuous a.auxiliary f.old inc f.bandwidth f.old_band
    (fun l => addBlock_band (f.tangent_band l) (f.curl_band l))
    (fun l => ⟨(f.tangent_carrier l).frequency, (f.tangent_carrier l).phase,
      (f.tangent_carrier l).angular⟩) f.old_bounds hi f.envelope_nonneg f.envelope_le_one
    f.angular_ne_zero a.old_support hsi i j
  simp only [he, fieldSum_add, incrementTensor, covarianceIncrement, oldField,
    tangentField, curlField, Pi.sub_apply] at hh ⊢
  exact hh

theorem signed_tensor_bounds {σ κ : ℝ} (hσ : 1 / 5 ≤ σ)
    (hκsmall : κ ≤ 1 / 100000)
    (f : SignedFamily s P (1 / 2) (17 / 25) (1 / 2 + σ - κ) (1 + σ - 2 * κ))
    (a : Assembly f) :
    TensorClass s (1 + σ - κ) (incrementTensor f a) ∧
      TensorClass s (1 + σ + 17 / 100 + κ) (remainderTensor f a) := by
  constructor
  · convert! incrementTensor_mem f a (by linarith) (by linarith) using 1
    ring
  · exact remainderTensor_mem f a (by linarith) (by linarith) (by linarith) (by linarith)

end Families

/-! ## The exact native cross, for the physical moving-gauge request -/

section Native

open PartitionedCovariance SignedWaveUpdate

variable {d h : ℝ} {vr vt : TorusInverse.Plane} {sys : SlotSystem d h vr vt}

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nativeTangentBlock_zero {l : UnsignedLabel} (P : PairData sys l)
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : ℝ) (a : SignedWaveUpdate.Vec2)
    (q : ℝ) (x : SlotColoring.Position) (j : Fin 2) (hm : mask d l q x = 0)
    (Y : TorusInverse.Plane) (θ : ℝ) (i : Fin 3) :
    (nativeTangentBlock P hdet outer ε a q x j).oscillation 0 (Y, θ) i = 0 := by
  rw [nativeTangentBlock, coefficientBlock_velocity]
  simp [hm, CurlClassBounds.complexify_apply]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem nativeAssembly_eq_finite {N : ℕ}
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (outer ε : UnsignedLabel → ℝ)
    (a : UnsignedLabel → SignedWaveUpdate.Vec2) (q : ℝ) (x : SlotColoring.Position)
    (F : Finset (UnsignedLabel × Fin 2))
    (hF : ∀ l, l ∉ F → mask d (tailLabel N l.1) q x = 0)
    (Y : TorusInverse.Plane) (θ : ℝ) (i : Fin 3) :
    nativeAssembly P hdet outer ε a q x Y θ i =
      ∑ l ∈ F, (nativeTangentBlock (P l.1) hdet (outer l.1) (ε l.1) (a l.1)
        q x l.2).oscillation 0 (Y, θ) i := by
  unfold nativeAssembly
  apply finsum_eq_sum_of_support_subset
  intro l hl
  by_contra hn
  exact hl (nativeTangentBlock_zero (P l.1) hdet _ _ _ _ _ _ (hF l hn) Y θ i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem native_physical_cross
    (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (P : (U : UnsignedLabel) → PairData sys (tailLabel N U))
    {q : ℝ} (hq : 0 < q) (hqN : q ≤ ChartScales.Q N) (x : SlotColoring.Position)
    (T σ : SignedWaveUpdate.Vec2)
    (hcone : ∀ U, mask d (tailLabel N U) q x ≠ 0 →
      SmoothCovariance.StrictCone (P U).matrix (chartTarget h q N T U)) (i : Fin 2) :
    let primary := nativeAssembly P hdet (physicalOuter h N) (physicalViscosity h N)
      (fun U => SmoothCovariance.amplitudes (P U).matrix (chartTarget h q N T U)) q x
    let signed := nativeAssembly P hdet (physicalOuter h N) (physicalViscosity h N)
      (fun U => SignedCovariance.increment (P U).matrix (chartTarget h q N T U)
        (SignedCovariance.chartStress h N σ U)) q x
    doubleAverage (fun Y θ => primary Y θ 0 * signed Y θ i.succ +
      signed Y θ 0 * primary Y θ i.succ) = σ i := by
  dsimp only
  simp_rw [nativeAssembly_radial, nativeAssembly_tangent]
  exact SignedCovariance.physical_signed_cross_covariance sys hdet N hN P hq hqN x T σ hcone i

end Native

/-! ## One moving chart and its measured debts -/

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane

/-- Geometry data, collecting `coord`, `region`, `patch`, `leftWeight`, `rightWeight`,
`left_pos` and their compatibility conditions. -/
structure Geometry where
  /-- Coord of `Geometry`, of type `ℝ`. -/
  coord : ℝ
  /-- Region of `Geometry`, of type `LocalSignedRequest.SlowRegion coord`. -/
  region : LocalSignedRequest.SlowRegion coord
  /-- Patch of `Geometry`, of type `SignedStressPrimitive.Patch`. -/
  patch : SignedStressPrimitive.Patch
  /-- Left weight of `Geometry`, of type `ℝ`. -/
  leftWeight : ℝ
  /-- Right weight of `Geometry`, of type `ℝ`. -/
  rightWeight : ℝ
  left_pos : 0 < leftWeight
  right_pos : 0 < rightWeight
  /-- Epsilon of `Geometry`, of type `ℕ → ℝ`. -/
  epsilon : ℕ → ℝ
  /-- Slow of `Geometry`, of type `ℕ → ℝ`. -/
  slow : ℕ → ℝ
  epsilon_pos : ∀ n, 0 < epsilon n
  epsilon_le_one : ∀ n, epsilon n ≤ 1
  slow_ge_one : ∀ n, 1 ≤ slow n
  /-- Gauge of `Geometry`, of type `VariableGaugeMean.GaugeData Plane`. -/
  gauge : VariableGaugeMean.GaugeData Plane
  inner_eq : gauge.radial.inner = patch.a
  outer_eq : gauge.radial.outer = patch.b
  exponent_pos : 0 < gauge.radial.exponent
  length_eq : ∀ n, gauge.length n = VariableGaugeMean.qLength coord
  /-- Fast of `Geometry`, of type `ℕ → ℝ`. -/
  fast : ℕ → ℝ
  /-- Axial of `Geometry`, of type `Plane`. -/
  axial : Plane
  /-- Time of `Geometry`, of type `Plane`. -/
  time : Plane
  /-- Temporal of `Geometry`, of type `Plane`. -/
  temporal : Plane

namespace Geometry

/-- Strip, constructed using `LocalSignedRequest.movingStripData`. -/
noncomputable def strip (G : Geometry) : StripData Point :=
  LocalSignedRequest.movingStripData G.region G.patch.a G.patch.b G.leftWeight G.rightWeight
    G.patch.a_pos G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos
    G.epsilon_le_one G.slow_ge_one

/-- Slow strip, constructed using `PhysicalMeanDomain.localSlowStripData`. -/
noncomputable def slowStrip (G : Geometry) : StripData Plane :=
  PhysicalMeanDomain.localSlowStripData G.region.carrier G.region.isOpen G.epsilon G.slow
    G.epsilon_pos G.epsilon_le_one G.slow_ge_one

/-- Domain, given by `PhysicalMeanDomain.slowDomain G.region.carrier`. -/
noncomputable def domain (G : Geometry) : Set Point := PhysicalMeanDomain.slowDomain
    G.region.carrier

/-- Operators, given by `StateMomentBalances.nativeOperators G.gauge.radial G.epsilon G.fast
G.axial G.time G.temporal`. -/
noncomputable def operators (G : Geometry) : Operators Point :=
  StateMomentBalances.nativeOperators G.gauge.radial G.epsilon G.fast G.axial G.time G.temporal

theorem inner_pos (G : Geometry) : 0 < G.gauge.radial.inner := by
    rw [G.inner_eq]; exact G.patch.a_pos

theorem domain_open (G : Geometry) : IsOpen G.domain := PhysicalMeanDomain.slowDomain_open
    G.region.isOpen

theorem strip_subset (G : Geometry) : G.strip.domain ⊆ G.domain := by
  intro x hx
  exact ((LocalSignedRequest.movingStrip_domain G.region G.patch.a G.patch.b G.leftWeight
    G.rightWeight G.patch.a_pos G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos
    G.epsilon_le_one G.slow_ge_one x).mp hx).1

theorem strip_fiber (G : Geometry) {x : Point} (hx : x ∈ G.strip.domain) (Y : Plane) :
    (x.1, (x.2.1, Y)) ∈ G.strip.domain := by
  apply (LocalSignedRequest.movingStrip_domain G.region G.patch.a G.patch.b G.leftWeight
    G.rightWeight G.patch.a_pos G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos
    G.epsilon_le_one G.slow_ge_one _).mpr
  exact (LocalSignedRequest.movingStrip_domain G.region G.patch.a G.patch.b G.leftWeight
    G.rightWeight G.patch.a_pos G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos
    G.epsilon_le_one G.slow_ge_one _).mp hx

theorem strip_radius_pos (G : Geometry) {x : Point} (hx : x ∈ G.strip.domain) : 0 < x.1 := by
  have hh := (LocalSignedRequest.movingStrip_domain G.region G.patch.a G.patch.b G.leftWeight
    G.rightWeight G.patch.a_pos G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos
    G.epsilon_le_one G.slow_ge_one _).mp hx
  have hq := Real.sqrt_pos.mpr (G.region.chartQ_pos hh.1)
  have hp : 0 < x.1 / Real.sqrt (MeanRankUpdate.chartQ G.coord x) :=
    G.patch.a_pos.trans hh.2.1
  exact (div_pos_iff.mp hp).resolve_right (fun hn => (not_lt_of_ge hq.le) hn.2) |>.1

theorem local_operators (G : Geometry) : LocalRankDefect.LocalOperators G.region.carrier
    G.operators :=
  ⟨rfl, (StateMomentBalances.nativeOperators_positive G.gauge.radial G.epsilon G.fast
    G.axial G.time G.temporal).radialProfile.mono (fun _ hx => hx.1)⟩

theorem average_mem (G : Geometry) {α : ℝ} {f : ScalarField Point}
    (hf : SmoothOn G.domain f) (hclass : MeanClass G.strip α f) :
    MeanClass G.strip α (StateMomentBalances.meanBar f) :=
  LocalSignedRequest.meanClass_liftedTorusAverage G.region G.patch.a G.patch.b
    G.leftWeight G.rightWeight G.patch.a_pos G.left_pos G.right_pos
    G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one hf hclass

theorem average_congr (G : Geometry) {f g : ScalarField Point} (he : Agree G.strip.domain f g) :
    Agree G.strip.domain (StateMomentBalances.meanBar f) (StateMomentBalances.meanBar g) := by
  intro n x hx
  exact PressureStream.torusAverage_congr_slice _ (fun Y => he n (G.strip_fiber hx Y))

/-- The actual slow jet bound lifts through the norm-one slow projection. -/
theorem slowClass_lift (G : Geometry) {α : ℝ} {f : ℕ → Plane → ℝ}
    (hf : UnweightedClass G.slowStrip α f) :
    UnweightedClass G.strip α (fun n x => f n x.2.1) := by
  let pr := StateMomentBalances.slowProjection (S := Plane)
  have hsm : SmoothOn G.domain (fun n x => f n x.2.1) := fun n =>
    (hf.smooth n).comp_continuousLinearMap pr
  apply VariableGaugeMean.localBandJets_unweighted_moving G.region G.patch.a_pos G.left_pos
    G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one hsm
  intro m
  obtain ⟨C, hC, k, hb⟩ := hf.bounds m
  refine ⟨C, hC, k, ?_⟩
  intro n x hx j hj
  have hpopen : IsOpen (pr ⁻¹' G.region.carrier) := G.region.isOpen.preimage pr.continuous
  have he := pr.iteratedFDerivWithin_comp_right (hf.smooth n) G.region.isOpen.uniqueDiffOn
    hpopen.uniqueDiffOn hx (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
  change iteratedFDerivWithin ℝ j (f n ∘ pr) (pr ⁻¹' G.region.carrier) x =
    (iteratedFDerivWithin ℝ j (f n) G.region.carrier (pr x)).compContinuousLinearMap (fun _ => pr)
        at he
  rw [iteratedFDerivWithin_of_isOpen j hpopen hx,
    iteratedFDerivWithin_of_isOpen (f := f n) j G.region.isOpen
      (show pr x ∈ G.region.carrier from hx)] at he
  have hnorm : ‖iteratedFDeriv ℝ j (fun y : Point => f n y.2.1) x‖ ≤
      ‖iteratedFDeriv ℝ j (f n) x.2.1‖ := by
    rw [show (fun y : Point => f n y.2.1) = f n ∘ pr from rfl, he]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg pr) StateMomentBalances.norm_slowProjection_le)
  apply hnorm.trans
  simpa only [majorant, StripData.growth, slowStrip, PhysicalMeanDomain.localSlowStripData,
    MeanMomentBounds.slowStripData, inv_one, max_self, mul_one] using hb n x.2.1 hx j hj

end Geometry

/-- Regularity is imposed on actual fluxes, before any class estimate on
their derivatives is derived. -/
def MovingField (G : Geometry) (f : ScalarField Point) : Prop :=
  GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b f

namespace MovingField

theorem sub {G : Geometry} {f g : ScalarField Point} (hf : MovingField G f) (hg : MovingField G g) :
    MovingField G (f - g) := by
  refine ⟨fun n => (hf.smooth n).sub (hg.smooth n), fun n => (hf.supported n).sub (hg.supported n),
      ?_⟩
  intro n r z hz Y k
  exact congrArg₂ (· - ·) (hf.periodic n r z hz Y k) (hg.periodic n r z hz Y k)

theorem covariance_flux_smooth {G : Geometry} {X : Tensor Point}
    (hX : ∀ i j, MovingField G (X i j)) :
    SmoothOn G.domain (thetaCovarianceChange G.operators X) ∧
      SmoothOn G.domain (axialCovarianceChange G.operators X) ∧
      SmoothOn G.domain (radialCovarianceChange G.operators X) := by
  obtain ⟨c, e, _, hc, _, _, _, hl, hr, _⟩ :=
    VariableGaugeMean.qLength_reference_bounds G.region G.patch.a_pos G.patch.a_lt_b
  have hf (i j) : LocalRankDefect.LocalShell c e G.region.carrier (X i j) :=
    ⟨(hX i j).smooth, ((hX i j).containing hl hr).supported⟩
  have hθ := ((hf 0 1).radialDiv hc G.region.isOpen G.local_operators 2).add
    ((hf 2 1).dz G.region.isOpen G.operators)
  have hz := ((hf 0 2).radialDiv hc G.region.isOpen G.local_operators 1).add
    ((hf 2 2).dz G.region.isOpen G.operators)
  have hr := (((hf 0 0).radialDiv hc G.region.isOpen G.local_operators 1).neg.sub
    ((hf 2 0).dz G.region.isOpen G.operators)).add
      ((hf 1 1).inv_mul hc G.region.isOpen G.local_operators)
  exact ⟨hθ.smooth, hz.smooth, hr.smooth⟩

end MovingField

/-! ## Actual pressure recomputation and the physical cancellation -/

/-- Physical sigma, defined pointwise by `SignedStressPrimitive.physicalBarSigma G.patch e
(SimilarityCoordinates.coordinateQ G.coord) (f n) (x.1, x.2.1)`. -/
noncomputable def physicalSigma (G : Geometry) (e : ℕ) (f : ScalarField Point) : ScalarField Point
    :=
  fun n x => SignedStressPrimitive.physicalBarSigma G.patch e
    (SimilarityCoordinates.coordinateQ G.coord) (f n) (x.1, x.2.1)

/-- Removed bump as an element of `ScalarField Point`. -/
noncomputable def removedBump (G : Geometry) (e : ℕ) (f : ScalarField Point) : ScalarField Point :=
  fun n x => SignedStressPrimitive.physicalBump G.patch e
    (SimilarityCoordinates.coordinateQ G.coord) (PressureStream.torusAverage (f n)) (x.1, x.2.1)

theorem radialDiv_congr {U : Set D} (hU : IsOpen U) (o : Operators D) (e : ℝ)
    {f g : ScalarField D} (he : Agree U f g) : Agree U (o.radialDiv e f) (o.radialDiv e g) := by
  intro n x hx
  simp only [Operators.radialDiv, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
    o.dr_congr hU he n hx, he n hx]

theorem pressureChange_mem (G : Geometry) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (h0 : MovingField G (u.gr c))
    (h1 : MovingField G ((waveStage G.gauge c u w q gaussian).gr c))
    {α : ℝ} (hclass : MeanClass G.strip α
      ((waveStage G.gauge c u w q gaussian).gr c - u.gr c)) :
    MeanClass G.strip α (pressureChange G.gauge c u w q gaussian) := by
  have hpres (s : State Point) : (VariableGaugeMean.reconstructState G.gauge c s).pressure =
      fun n x => VariableGaugeMean.meanPressure G.gauge.radial.exponent G.patch.a G.patch.b
        (G.gauge.radial.frequency n) G.patch.a_lt_b (VariableGaugeMean.qLength G.coord)
        G.gauge.radial.radialDirection (s.gr c n) x := by
    funext n x
    simp only [VariableGaugeMean.reconstructState, G.length_eq, G.inner_eq, G.outer_eq]
  have hold : u.pressure = fun n x => VariableGaugeMean.meanPressure G.gauge.radial.exponent
      G.patch.a G.patch.b (G.gauge.radial.frequency n) G.patch.a_lt_b
      (VariableGaugeMean.qLength G.coord) G.gauge.radial.radialDirection (u.gr c n) x := by
    rw [← hfixed]
    exact hpres (VariableGaugeMean.reconstructState G.gauge c u)
  have hnew := hpres (u.addIncrement zeroTriple 0 w q ⟨0, gaussian, 0⟩)
  have hh := VariableGaugeMean.meanClass_meanPressure_change G.region G.patch.a_pos
    G.patch.a_lt_b G.exponent_pos G.left_pos G.right_pos G.epsilon G.slow
    G.epsilon_pos G.epsilon_le_one G.slow_ge_one h1.smooth h0.smooth h1.supported h0.supported
    hclass G.gauge.radial.frequency (fun _ => G.gauge.radial.radialDirection)
  convert! hh using 1
  funext n x
  simp only [pressureChange, Pi.sub_apply, hold]
  exact congrArg (fun a : ℝ => a - VariableGaugeMean.meanPressure G.gauge.radial.exponent
    G.patch.a G.patch.b (G.gauge.radial.frequency n) G.patch.a_lt_b
    (VariableGaugeMean.qLength G.coord) G.gauge.radial.radialDirection (u.gr c n) x)
      (congrArg (fun a : ScalarField Point => a n x) hnew)

theorem physicalSigma_smooth (G : Geometry) (e : ℕ) {f : ScalarField Point}
    (hf : SmoothOn G.domain f)
    (hs : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (f n))
        :
    SmoothOn G.domain (physicalSigma G e f) := fun n =>
  LocalSignedRequest.physicalBarSigma_contDiffOn G.region G.patch e (hf n) (hs n)

theorem physicalSigma_cancels (G : Geometry) (e : ℕ) (he : e = 2 ∨ e = 1)
    {f : ScalarField Point} (hf : SmoothOn G.domain f)
    (hs : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (f n))
    (n : ℕ) {x : Point} (hx : x ∈ G.strip.domain) :
    StateMomentBalances.meanBar f n x + G.operators.radialDiv (e : ℝ) (physicalSigma G e f) n x =
      removedBump G e f n x := by
  have hrad := native_radialDiv_slow_on G.gauge.radial G.epsilon G.fast G.axial G.time G.temporal
    G.region.isOpen (physicalSigma_smooth G e hf hs) (e : ℝ) n (G.strip_subset hx)
  change G.operators.radialDiv (e : ℝ) (physicalSigma G e f) n x = _ at hrad
  rw [hrad]
  rcases he with rfl | rfl
  · rw [show ((2 : ℕ) : ℝ) = 2 from rfl,
      LocalSignedRequest.physicalBarSigma_angular_divergence G.region G.patch (hf n) (hs n)
        (G.strip_subset hx) (G.strip_radius_pos hx)]
    simp only [StateMomentBalances.meanBar, MeanMomentBounds.liftedTorusAverage, removedBump,
      SignedStressPrimitive.physicalAdjusted]
    ring
  · rw [show ((1 : ℕ) : ℝ) = 1 from by norm_num,
      LocalSignedRequest.physicalBarSigma_axial_divergence G.region G.patch (hf n) (hs n)
        (G.strip_subset hx) (G.strip_radius_pos hx)]
    simp only [StateMomentBalances.meanBar, MeanMomentBounds.liftedTorusAverage, removedBump,
      SignedStressPrimitive.physicalAdjusted]
    ring

theorem cross_cancels (G : Geometry) (e : ℕ) (he : e = 2 ∨ e = 1)
    {f X : ScalarField Point} (hf : SmoothOn G.domain f)
    (hs : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord G.region.carrier (f n))
    (hX : MovingField G X)
    (hcross : Agree G.strip.domain (StateMomentBalances.meanBar X) (physicalSigma G e f))
    (n : ℕ) {x : Point} (hx : x ∈ G.strip.domain) :
    StateMomentBalances.meanBar f n x + StateMomentBalances.meanBar (G.operators.radialDiv (e : ℝ)
        X) n x =
      removedBump G e f n x := by
  rw [meanBar_radialDiv_on G.region.isOpen G.operators rfl
    (fun _ _ _ => rfl) hX.smooth hX.periodic (e : ℝ) n (G.strip_subset hx),
    radialDiv_congr G.strip.isOpen_domain G.operators (e : ℝ) hcross n hx]
  exact physicalSigma_cancels G e he hf hs n hx

namespace Geometry

theorem removed_bumps_mem (G : Geometry) (c : Context Point) (u : State Point) {α : ℝ}
    (ho : c.operators = G.operators)
    (Hθ : GaugeMomentBalances.MovingAngularInputs G.region G.patch.a G.patch.b c u)
    (Hz : GaugeMomentBalances.MovingAxialInputs G.region G.patch.a G.patch.b c u)
    (hr : MovingField G (u.gr c))
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hmθ : ∀ n z, z ∈ G.region.carrier → radialMoment 2 u.mean.angular n z = 0)
    (hmz : ∀ n z, z ∈ G.region.carrier → radialMoment 1 u.mean.axial n z = 0)
    (hD : ∀ i : Fin 3, UnweightedClass G.slowStrip α (fun n z => debt c u n z i)) :
    MeanClass G.strip (α + 1) (removedBump G 2 (u.thetaResidual c)) ∧
      MeanClass G.strip (α + 1) (removedBump G 1 (u.axialResidual c)) := by
  have hP := G.slowClass_lift (hD 0)
  have hθ := G.slowClass_lift (hD 1)
  have hz := G.slowClass_lift (hD 2)
  simp only [debt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hP hθ hz
  constructor
  · exact GaugeMomentBalances.state_angular_bump_improvedClass G.region G.patch G.left_pos
      G.right_pos
      G.patch.a_pos G.patch.a_lt_b G.gauge.radial G.epsilon G.fast G.slow G.epsilon_pos
      G.epsilon_le_one G.slow_ge_one G.axial G.time G.temporal c u α ho Hθ hmθ hθ
  · apply GaugeMomentBalances.state_axial_bump_improvedClass G.region G.patch G.left_pos G.right_pos
      G.gauge G.inner_pos G.exponent_pos G.length_eq G.epsilon G.fast G.slow G.epsilon_pos
      G.epsilon_le_one G.slow_ge_one G.axial G.time G.temporal c u α ho
    · simpa only [G.inner_eq, G.outer_eq] using Hz
    · simp only [G.inner_eq, G.outer_eq]
      exact hr
    · exact hfixed
    · exact hmz
    · exact hP
    · exact hz

end Geometry

/-! ## The literal averaged residual after the update -/

/-- Theta remainder field, given by `thetaCovarianceChange G.operators E + G.operators.dz (S 2
1)`. -/
noncomputable def thetaRemainderField (G : Geometry) (S E : Tensor Point) : ScalarField Point :=
  thetaCovarianceChange G.operators E + G.operators.dz (S 2 1)

/-- Axial remainder field, given by `axialCovarianceChange G.operators E + G.operators.dz (S 2
2) + G.operators.dz p`. -/
noncomputable def axialRemainderField (G : Geometry) (S E : Tensor Point) (p : ScalarField Point) :
    ScalarField Point := axialCovarianceChange G.operators E + G.operators.dz (S 2 2) +
        G.operators.dz p

/-- These hypotheses concern local regularity and the actual incoming
state. None is a bound or a cancellation assertion about the updated residual. -/
structure LocalData (G : Geometry) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point) : Prop
        where
  operators_eq : c.operators = G.operators
  base : SmoothTriple G.strip.domain c.base
  mean : SmoothTriple G.strip.domain u.mean
  covariance : ∀ i j, SmoothOn G.strip.domain (u.covariance i j)
  theta : SmoothOn G.domain (u.thetaResidual c)
  axial : SmoothOn G.domain (u.axialResidual c)
  theta_support : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord
    G.region.carrier (u.thetaResidual c n)
  axial_support : ∀ n, LocalSignedRequest.MovingSupport G.patch.a G.patch.b G.coord
    G.region.carrier (u.axialResidual c n)
  angular_flux : GaugeMomentBalances.MovingAngularInputs G.region G.patch.a G.patch.b c u
  axial_flux : GaugeMomentBalances.MovingAxialInputs G.region G.patch.a G.patch.b c u
  source : MovingField G (u.gr c)
  updated_source : MovingField G ((waveStage G.gauge c u w q gaussian).gr c)
  reconstructed : VariableGaugeMean.reconstructState G.gauge c u = u
  angular_mass : ∀ n z, z ∈ G.region.carrier → radialMoment 2 u.mean.angular n z = 0
  axial_mass : ∀ n z, z ∈ G.region.carrier → radialMoment 1 u.mean.axial n z = 0

namespace LocalData

variable {G : Geometry} {c : Context Point} {u : State Point} {w : Oscillation Point}
  {q : OscillatoryScalar Point} {gaussian : Oscillation Point}
  (H : LocalData G c u w q gaussian)

include H

theorem pressure_smooth : SmoothOn G.domain u.pressure := by
  have hh := GaugeMomentBalances.pressureRecipe_movingField G.region G.gauge G.inner_pos
    G.exponent_pos G.length_eq c u
    (by simp only [G.inner_eq, G.outer_eq]; exact H.source)
  have he := hh.smooth
  simp only [GaugeMomentBalances.pressureRecipe, H.reconstructed] at he
  exact he

theorem pressureChange_smooth : SmoothOn G.domain (pressureChange G.gauge c u w q gaussian) := by
  have hh := GaugeMomentBalances.pressureRecipe_movingField G.region G.gauge G.inner_pos
    G.exponent_pos G.length_eq c (waveStage G.gauge c u w q gaussian)
    (by simp only [G.inner_eq, G.outer_eq]; exact H.updated_source)
  have hn : SmoothOn G.domain (waveStage G.gauge c u w q gaussian).pressure := by
    have he := hh.smooth
    simp only [GaugeMomentBalances.pressureRecipe, waveStage,
      GaugeMomentBalances.reconstructState_idempotent] at he ⊢
    exact he
  exact hn.sub H.pressure_smooth

theorem pressureChange_mem {α κ : ℝ} (ho : OperatorBounds G.strip G.operators κ)
    (hX : TensorClass G.strip α (covarianceIncrement u.oscillation w)) :
    MeanClass G.strip (α - κ) (pressureChange G.gauge c u w q gaussian) := by
  apply SignedMeanGain.pressureChange_mem G c u w q gaussian H.reconstructed H.source
      H.updated_source
  apply class_congr (radialCovarianceChange_mem ho hX)
  simpa only [H.operators_eq] using waveStage_gr_change G.strip.isOpen_domain
    G.gauge c u w q gaussian H.base H.mean H.covariance (fun i j => (hX i j).smooth)

theorem theta_split {S E : Tensor Point}
    (hS : ∀ i j, SmoothOn G.strip.domain (S i j))
    (hE : ∀ i j, SmoothOn G.strip.domain (E i j))
    (hX : covarianceIncrement u.oscillation w = S + E) :
    Agree G.strip.domain ((waveStage G.gauge c u w q gaussian).thetaResidual c)
      (u.thetaResidual c + G.operators.radialDiv 2 (S 0 1) + thetaRemainderField G S E) := by
  have hXs : ∀ i j, SmoothOn G.strip.domain (covarianceIncrement u.oscillation w i j) := by
    rw [hX]
    exact fun i j => (hS i j).add (hE i j)
  intro n x hx
  have hh := waveStage_theta_change G.strip.isOpen_domain G.gauge c u w q gaussian
    H.base H.mean H.covariance hXs n hx
  rw [H.operators_eq, hX] at hh
  have hr := G.operators.radialDiv_add G.strip.isOpen_domain 2 (hS 0 1) (hE 0 1) n hx
  have hz := G.operators.dz_add G.strip.isOpen_domain (hS 2 1) (hE 2 1) n hx
  simp only [thetaCovarianceChange, Pi.sub_apply, Pi.add_apply] at hh hr hz
  simp only [thetaRemainderField, thetaCovarianceChange, Pi.add_apply]
  linarith

theorem axial_split {S E : Tensor Point}
    (hS : ∀ i j, SmoothOn G.strip.domain (S i j))
    (hE : ∀ i j, SmoothOn G.strip.domain (E i j))
    (hX : covarianceIncrement u.oscillation w = S + E) :
    Agree G.strip.domain ((waveStage G.gauge c u w q gaussian).axialResidual c)
      (u.axialResidual c + G.operators.radialDiv 1 (S 0 2) +
        axialRemainderField G S E (pressureChange G.gauge c u w q gaussian)) := by
  have hXs : ∀ i j, SmoothOn G.strip.domain (covarianceIncrement u.oscillation w i j) := by
    rw [hX]
    exact fun i j => (hS i j).add (hE i j)
  intro n x hx
  have hh := waveStage_axial_change G.strip.isOpen_domain G.gauge c u w q gaussian
    H.base H.mean H.covariance hXs (fun n => (H.pressure_smooth n).mono G.strip_subset)
    (fun n => (H.pressureChange_smooth n).mono G.strip_subset) n hx
  rw [H.operators_eq, hX] at hh
  have hr := G.operators.radialDiv_add G.strip.isOpen_domain 1 (hS 0 2) (hE 0 2) n hx
  have hz := G.operators.dz_add G.strip.isOpen_domain (hS 2 2) (hE 2 2) n hx
  simp only [axialCovarianceChange, Pi.sub_apply, Pi.add_apply] at hh hr hz
  simp only [axialRemainderField, axialCovarianceChange, Pi.add_apply]
  linarith

end LocalData

/-- A direct identity for the torus average: the radial primary cross
cancels the adjusted old residual. The axial cross flux and pressure change
are displayed explicitly in the remaining term. -/
theorem averaged_residual_decomposition (G : Geometry) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (H : LocalData G c u w q gaussian) (S E : Tensor Point)
    (hS : ∀ i j, MovingField G (S i j)) (hE : ∀ i j, MovingField G (E i j))
    (hX : covarianceIncrement u.oscillation w = S + E)
    (hcrossθ : Agree G.strip.domain (StateMomentBalances.meanBar (S 0 1))
      (physicalSigma G 2 (u.thetaResidual c)))
    (hcrossz : Agree G.strip.domain (StateMomentBalances.meanBar (S 0 2))
      (physicalSigma G 1 (u.axialResidual c))) :
    Agree G.strip.domain (StateMomentBalances.meanBar ((waveStage G.gauge c u w q
        gaussian).thetaResidual c))
      (removedBump G 2 (u.thetaResidual c) + StateMomentBalances.meanBar (thetaRemainderField G S
          E)) ∧
    Agree G.strip.domain (StateMomentBalances.meanBar ((waveStage G.gauge c u w q
        gaussian).axialResidual c))
      (removedBump G 1 (u.axialResidual c) +
        StateMomentBalances.meanBar (axialRemainderField G S E (pressureChange G.gauge c u w q
            gaussian))) := by
  have hSs := fun i j n => ((hS i j).smooth n).mono G.strip_subset
  have hEs := fun i j n => ((hE i j).smooth n).mono G.strip_subset
  have hRestθ : SmoothOn G.domain (thetaRemainderField G S E) :=
    (MovingField.covariance_flux_smooth hE).1.add (SmoothOn.dz (hS 2 1).smooth G.domain_open
        G.operators)
  have hRestz : SmoothOn G.domain (axialRemainderField G S E (pressureChange G.gauge c u w q
      gaussian)) :=
    ((MovingField.covariance_flux_smooth hE).2.1.add
      (SmoothOn.dz (hS 2 2).smooth G.domain_open G.operators)).add
        (H.pressureChange_smooth.dz G.domain_open G.operators)
  obtain ⟨a, b, _, ha, _, _, _, hl, hr, _⟩ :=
    VariableGaugeMean.qLength_reference_bounds G.region G.patch.a_pos G.patch.a_lt_b
  have hlocal (i j) : LocalRankDefect.LocalShell a b G.region.carrier (S i j) :=
    ⟨(hS i j).smooth, ((hS i j).containing hl hr).supported⟩
  constructor
  · intro n x hx
    have hbar := G.average_congr (H.theta_split hSs hEs hX) n hx
    have hrad := ((hlocal 0 1).radialDiv ha G.region.isOpen G.local_operators 2).smooth
    have hbump := cross_cancels G 2 (Or.inl rfl) H.theta H.theta_support (hS 0 1) hcrossθ n hx
    rw [meanBar_add_on (H.theta.add hrad) hRestθ n (G.strip_subset hx),
      meanBar_add_on H.theta hrad n (G.strip_subset hx)] at hbar
    norm_num only [Nat.cast_ofNat] at hbump
    simp only [Pi.add_apply] at hbar hbump ⊢
    linarith
  · intro n x hx
    have hbar := G.average_congr (H.axial_split hSs hEs hX) n hx
    have hrad := ((hlocal 0 2).radialDiv ha G.region.isOpen G.local_operators 1).smooth
    have hbump := cross_cancels G 1 (Or.inr rfl) H.axial H.axial_support (hS 0 2) hcrossz n hx
    rw [meanBar_add_on (H.axial.add hrad) hRestz n (G.strip_subset hx),
      meanBar_add_on H.axial hrad n (G.strip_subset hx)] at hbar
    norm_num only [Nat.cast_ofNat] at hbump
    simp only [Pi.add_apply] at hbar hbump ⊢
    linarith

/-! ## Quantitative mean gain -/

/-- This intermediate estimate isolates the two exact cross identities.
The native theorem below discharges them by the signed inverse construction. -/
theorem signed_mean_gain_of_cross
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
    (hcrossθ : Agree G.strip.domain (StateMomentBalances.meanBar (crossTensor f a 0 1))
      (physicalSigma G 2 (u.thetaResidual c)))
    (hcrossz : Agree G.strip.domain (StateMomentBalances.meanBar (crossTensor f a 0 2))
      (physicalSigma G 1 (u.axialResidual c))) :
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
  have hbar := averaged_residual_decomposition G c u (tangentField f a + curlField f a)
    q gaussian H (crossTensor f a) (remainderTensor f a) hS hEc hactual hcrossθ hcrossz
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply class_congr ((hθ.mono_exponent (by linarith)).add htchange)
    intro n x _
    simp only [Pi.sub_apply]
    ring
  · apply class_congr ((hz.mono_exponent (by linarith)).add hzchange)
    intro n x _
    simp only [Pi.sub_apply]
    ring
  · exact class_congr ((hbθ.mono_exponent (by linarith)).add (G.average_mem hRestθs hRestθ)) hbar.1
  · exact class_congr ((hbz.mono_exponent (by linarith)).add (G.average_mem hRestzs hRestz)) hbar.2

/-! ## A shared native construction, before any signed output is known -/

/-- Native index: an abbreviation for `PartitionedCovariance.UnsignedLabel × Fin 2`. -/
abbrev NativeIndex := PartitionedCovariance.UnsignedLabel × Fin 2

/-- All matches concern the common matrix, unit fundamental, mask and
carrier. The signed coefficient is constructed below from the measured
physical request, not included as a realization hypothesis. -/
structure NativeData (G : Geometry) where
  /-- Width of `NativeData`, of type `ℝ`. -/
  width : ℝ
  /-- Exponent of `NativeData`, of type `ℝ`. -/
  exponent : ℝ
  /-- Vr of `NativeData`, of type `Plane`. -/
  vr : Plane
  /-- Vt of `NativeData`, of type `Plane`. -/
  vt : Plane
  /-- Slots of `NativeData`, of type `PartitionedCovariance.SlotSystem width exponent vr vt`. -/
  slots : PartitionedCovariance.SlotSystem width exponent vr vt
  determinant : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0
  /-- Index of `NativeData`, of type `ℕ → ℕ`. -/
  index : ℕ → ℕ
  index_pos : ∀ n, 1 ≤ index n
  /-- Pairs supplied by `NativeData`. -/
  pairs : (n : ℕ) → (ℝ × Plane) → (l : PartitionedCovariance.UnsignedLabel) →
    PartitionedCovariance.PairData slots (PartitionedCovariance.tailLabel (index n) l)
  /-- Position of `NativeData`, of type `ℕ → (ℝ × Plane) → SlotColoring.Position`. -/
  position : ℕ → (ℝ × Plane) → SlotColoring.Position
  /-- Model target of `NativeData`, of type `ℕ → (ℝ × Plane) → SignedWaveUpdate.Vec2`. -/
  modelTarget : ℕ → (ℝ × Plane) → SignedWaveUpdate.Vec2
  /-- Matrix of `NativeData`, of type `PartitionedCovariance.UnsignedLabel → ℕ → Point →
  SignedWaveUpdate.Mat2`. -/
  matrix : PartitionedCovariance.UnsignedLabel → ℕ → Point → SignedWaveUpdate.Mat2
  /-- Target of `NativeData`, of type `PartitionedCovariance.UnsignedLabel → ℕ → Point →
  SignedWaveUpdate.Vec2`. -/
  target : PartitionedCovariance.UnsignedLabel → ℕ → Point → SignedWaveUpdate.Vec2
  /-- Mask of `NativeData`, of type `PartitionedCovariance.UnsignedLabel → ℕ → Point → ℝ`. -/
  mask : PartitionedCovariance.UnsignedLabel → ℕ → Point → ℝ
  /-- Unit of `NativeData`, of type `NativeIndex → ℕ → Point → SignedWaveUpdate.Space`. -/
  unit : NativeIndex → ℕ → Point → SignedWaveUpdate.Space
  /-- Frequency of `NativeData`, of type `NativeIndex → ℕ → ℝ`. -/
  frequency : NativeIndex → ℕ → ℝ
  /-- Phase of `NativeData`, of type `NativeIndex → ℕ → Point → ℝ`. -/
  phase : NativeIndex → ℕ → Point → ℝ
  /-- Angular of `NativeData`, of type `NativeIndex → ℕ → ℤ`. -/
  angular : NativeIndex → ℕ → ℤ
  matrix_match : ∀ l n x, x ∈ G.strip.domain →
    matrix l n x = (pairs n (x.1, x.2.1) l).matrix
  target_match : ∀ l n x, x ∈ G.strip.domain → target l n x =
    PartitionedCovariance.chartTarget exponent (SimilarityCoordinates.coordinateQ G.coord x.2.1)
      (index n) (modelTarget n (x.1, x.2.1)) l
  mask_match : ∀ l n x, x ∈ G.strip.domain → mask l n x =
    PartitionedCovariance.mask width (PartitionedCovariance.tailLabel (index n) l)
      (SimilarityCoordinates.coordinateQ G.coord x.2.1) (position n (x.1, x.2.1))
  unit_match : ∀ l n x, x ∈ G.strip.domain → unit l n x =
    SignedWaveUpdate.nativeUnit (pairs n (x.1, x.2.1) l.1) determinant l.2 x.2.2
  phase_match : ∀ l n x, x ∈ G.strip.domain → frequency l n * phase l n x =
    (pairs n (x.1, x.2.1) l.1).phases l.2 x.2.2
  angular_match : ∀ l n x, x ∈ G.strip.domain → angular l n = (pairs n (x.1, x.2.1) l.1).modes l.2
  tail_bound : ∀ n x, x ∈ G.strip.domain →
    SimilarityCoordinates.coordinateQ G.coord x.2.1 ≤ ChartScales.Q (index n)
  cone : ∀ n x, x ∈ G.strip.domain → ∀ l,
    PartitionedCovariance.mask width (PartitionedCovariance.tailLabel (index n) l)
      (SimilarityCoordinates.coordinateQ G.coord x.2.1) (position n (x.1, x.2.1)) ≠ 0 →
    SmoothCovariance.StrictCone (pairs n (x.1, x.2.1) l).matrix
      (PartitionedCovariance.chartTarget exponent (SimilarityCoordinates.coordinateQ G.coord x.2.1)
        (index n) (modelTarget n (x.1, x.2.1)) l)
  /-- Label type of `NativeData`, of type `ℕ → Finset NativeIndex`. -/
  labels : ℕ → Finset NativeIndex
  coverage : ∀ n x, x ∈ G.strip.domain → ∀ l, l ∉ labels n →
    PartitionedCovariance.mask width (PartitionedCovariance.tailLabel (index n) l.1)
      (SimilarityCoordinates.coordinateQ G.coord x.2.1) (position n (x.1, x.2.1)) = 0

namespace NativeData

variable {G : Geometry} (B : NativeData G)

/-- Block, constructed using `SignedWaveUpdate.coefficientBlock`. -/
noncomputable def block (A : PartitionedCovariance.UnsignedLabel → ℕ → Point →
    SignedWaveUpdate.Vec2)
    (l : NativeIndex) : HarmonicBlock Point :=
  SignedWaveUpdate.coefficientBlock (B.frequency l) (B.phase l) (B.angular l)
    (fun n x => CurlClassBounds.complexify
      ((PartitionedCovariance.physicalOuter B.exponent (B.index n) l.1 *
        (Real.sqrt (PartitionedCovariance.physicalViscosity B.exponent (B.index n) l.1) *
          A l.1 n x l.2 * B.mask l.1 n x)) • B.unit l n x)) 0

/-- Primary blocks, given by `B.block (fun l n x => SmoothCovariance.amplitudes (B.matrix l n x)
(B.target l n x))`. -/
noncomputable def primaryBlocks : NativeIndex → HarmonicBlock Point :=
  B.block (fun l n x => SmoothCovariance.amplitudes (B.matrix l n x) (B.target l n x))

/-- Signed blocks, constructed using `B.block`. -/
noncomputable def signedBlocks (c : Context Point) (u : State Point) : NativeIndex → HarmonicBlock
    Point :=
  B.block (fun l n x => SignedCovariance.increment (B.matrix l n x) (B.target l n x)
    (SignedCovariance.chartStress B.exponent (B.index n)
      (LocalSignedRequest.requestedStress G.patch G.coord c u n x) l))

theorem block_realization
    (A : PartitionedCovariance.UnsignedLabel → ℕ → Point → SignedWaveUpdate.Vec2)
    (l : NativeIndex) (n : ℕ) {x : Point} (hx : x ∈ G.strip.domain) (θ : ℝ) (i : Fin 3) :
    (B.block A l).oscillation n (x, θ) i =
      (SignedWaveUpdate.nativeTangentBlock (B.pairs n (x.1, x.2.1) l.1) B.determinant
        (PartitionedCovariance.physicalOuter B.exponent (B.index n) l.1)
        (PartitionedCovariance.physicalViscosity B.exponent (B.index n) l.1)
        (A l.1 n x) (SimilarityCoordinates.coordinateQ G.coord x.2.1)
        (B.position n (x.1, x.2.1)) l.2).oscillation 0 (x.2.2, θ) i := by
  simp only [block, SignedWaveUpdate.nativeTangentBlock, SignedWaveUpdate.coefficientBlock_velocity]
  rw [B.unit_match l n x hx, B.mask_match l.1 n x hx, B.phase_match l n x hx,
    B.angular_match l n x hx]
  simp only [one_mul]

theorem primary_realization (l : NativeIndex) (n : ℕ) {x : Point} (hx : x ∈ G.strip.domain)
    (θ : ℝ) (i : Fin 3) :
    (B.primaryBlocks l).oscillation n (x, θ) i =
      (SignedWaveUpdate.nativeTangentBlock (B.pairs n (x.1, x.2.1) l.1) B.determinant
        (PartitionedCovariance.physicalOuter B.exponent (B.index n) l.1)
        (PartitionedCovariance.physicalViscosity B.exponent (B.index n) l.1)
        (SmoothCovariance.amplitudes (B.pairs n (x.1, x.2.1) l.1).matrix
          (PartitionedCovariance.chartTarget B.exponent (SimilarityCoordinates.coordinateQ G.coord
              x.2.1)
            (B.index n) (B.modelTarget n (x.1, x.2.1)) l.1))
        (SimilarityCoordinates.coordinateQ G.coord x.2.1)
        (B.position n (x.1, x.2.1)) l.2).oscillation 0 (x.2.2, θ) i := by
  rw [primaryBlocks, B.block_realization _ l n hx θ i, B.matrix_match l.1 n x hx,
    B.target_match l.1 n x hx]

theorem signed_realization (c : Context Point) (u : State Point)
    (l : NativeIndex) (n : ℕ) {x : Point} (hx : x ∈ G.strip.domain) (θ : ℝ) (i : Fin 3) :
    (B.signedBlocks c u l).oscillation n (x, θ) i =
      (SignedWaveUpdate.nativeTangentBlock (B.pairs n (x.1, x.2.1) l.1) B.determinant
        (PartitionedCovariance.physicalOuter B.exponent (B.index n) l.1)
        (PartitionedCovariance.physicalViscosity B.exponent (B.index n) l.1)
        (SignedCovariance.increment (B.pairs n (x.1, x.2.1) l.1).matrix
          (PartitionedCovariance.chartTarget B.exponent (SimilarityCoordinates.coordinateQ G.coord
              x.2.1)
            (B.index n) (B.modelTarget n (x.1, x.2.1)) l.1)
          (SignedCovariance.chartStress B.exponent (B.index n)
            (LocalSignedRequest.requestedStress G.patch G.coord c u n x) l.1))
        (SimilarityCoordinates.coordinateQ G.coord x.2.1)
        (B.position n (x.1, x.2.1)) l.2).oscillation 0 (x.2.2, θ) i := by
  rw [signedBlocks, B.block_realization _ l n hx θ i, B.matrix_match l.1 n x hx,
    B.target_match l.1 n x hx]

end NativeData

theorem meanBar_symmetricCovariance (p t : Oscillation Point)
    (hp : LabelSumBounds.AngularContinuous p) (ht : LabelSumBounds.AngularContinuous t)
    (i j : Fin 3) (n : ℕ) (x : Point) :
    StateMomentBalances.meanBar (LabelSumBounds.symmetricCovariance p t i j) n x =
      PartitionedCovariance.doubleAverage (fun Y θ =>
        p n ((x.1, (x.2.1, Y)), θ) i * t n ((x.1, (x.2.1, Y)), θ) j +
        t n ((x.1, (x.2.1, Y)), θ) i * p n ((x.1, (x.2.1, Y)), θ) j) := by
  change PressureStream.torusAverage
    (fun z => bilinearCovariance p t i j n z + bilinearCovariance t p i j n z) (x.1, x.2.1) =
    PressureStream.torusAverage (fun z => SmoothLoop.angularMean (fun θ =>
      p n (z, θ) i * t n (z, θ) j + t n (z, θ) i * p n (z, θ) j)) (x.1, x.2.1)
  apply PressureStream.torusAverage_congr_slice
  intro Y
  simp only [ bilinearCovariance,
    angularAverage, SmoothLoop.angularMean]
  rw [intervalIntegral.integral_add (((hp n _ i).fun_mul (ht n _ j)).intervalIntegrable _ _)
    (((ht n _ i).fun_mul (hp n _ j)).intervalIntegrable _ _), add_div]

theorem NativeData.requested_cross {G : Geometry} (B : NativeData G)
    (c : Context Point) (u : State Point) (i : Fin 2) :
    Agree G.strip.domain
      (StateMomentBalances.meanBar (LabelSumBounds.symmetricCovariance
        (LabelSumBounds.fieldSum B.labels (fun l => (B.primaryBlocks l).oscillation))
        (LabelSumBounds.fieldSum B.labels (fun l => (B.signedBlocks c u l).oscillation)) 0 i.succ))
      (fun n x => LocalSignedRequest.requestedStress G.patch G.coord c u n x i) := by
  intro n x hx
  rw [meanBar_symmetricCovariance _ _
    (LabelSumBounds.fieldSum_angularContinuous _ _ (fun _ => LabelSumBounds.block_angularContinuous
        _))
    (LabelSumBounds.fieldSum_angularContinuous _ _ (fun _ => LabelSumBounds.block_angularContinuous
        _))]
  have hp (Y : Plane) (θ : ℝ) (j : Fin 3) :
      LabelSumBounds.fieldSum B.labels (fun l => (B.primaryBlocks l).oscillation)
        n ((x.1, (x.2.1, Y)), θ) j =
      SignedWaveUpdate.nativeAssembly (B.pairs n (x.1, x.2.1)) B.determinant
        (PartitionedCovariance.physicalOuter B.exponent (B.index n))
        (PartitionedCovariance.physicalViscosity B.exponent (B.index n))
        (fun l => SmoothCovariance.amplitudes (B.pairs n (x.1, x.2.1) l).matrix
          (PartitionedCovariance.chartTarget B.exponent (SimilarityCoordinates.coordinateQ G.coord
              x.2.1)
            (B.index n) (B.modelTarget n (x.1, x.2.1)) l))
        (SimilarityCoordinates.coordinateQ G.coord x.2.1) (B.position n (x.1, x.2.1)) Y θ j := by
    rw [nativeAssembly_eq_finite _ _ _ _ _ _ _ (B.labels n) (B.coverage n x hx)]
    apply Finset.sum_congr rfl
    intro l _
    exact B.primary_realization l n (G.strip_fiber hx Y) θ j
  have ht (Y : Plane) (θ : ℝ) (j : Fin 3) :
      LabelSumBounds.fieldSum B.labels (fun l => (B.signedBlocks c u l).oscillation)
        n ((x.1, (x.2.1, Y)), θ) j =
      SignedWaveUpdate.nativeAssembly (B.pairs n (x.1, x.2.1)) B.determinant
        (PartitionedCovariance.physicalOuter B.exponent (B.index n))
        (PartitionedCovariance.physicalViscosity B.exponent (B.index n))
        (fun l => SignedCovariance.increment (B.pairs n (x.1, x.2.1) l).matrix
          (PartitionedCovariance.chartTarget B.exponent (SimilarityCoordinates.coordinateQ G.coord
              x.2.1)
            (B.index n) (B.modelTarget n (x.1, x.2.1)) l)
          (SignedCovariance.chartStress B.exponent (B.index n)
            (LocalSignedRequest.requestedStress G.patch G.coord c u n x) l))
        (SimilarityCoordinates.coordinateQ G.coord x.2.1) (B.position n (x.1, x.2.1)) Y θ j := by
    rw [nativeAssembly_eq_finite _ _ _ _ _ _ _ (B.labels n) (B.coverage n x hx)]
    apply Finset.sum_congr rfl
    intro l _
    exact B.signed_realization c u l n (G.strip_fiber hx Y) θ j
  simp_rw [hp, ht]
  exact native_physical_cross B.determinant (B.index n) (B.index_pos n) _
    (G.region.qlo_pos.trans_le (G.region.q_mem x.2.1 (G.strip_subset hx)).1)
    (B.tail_bound n x hx) _ _ _ (B.cone n x hx) i

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- Equality of the stored harmonic coefficients and carrier metadata
identifies the actual oscillations; the pressure coefficients need not agree. -/
theorem oscillation_eq_of_coefficients (a b : HarmonicBlock D)
    (hv : a.velocity = b.velocity) (hc : LabelSumBounds.SameCarrier a b) :
    a.oscillation = b.oscillation := by
  unfold HarmonicBlock.oscillation
  rw [hv, hc.frequency, hc.phase, hc.angular]

/-- This binds the abstract label-estimate package to the explicit common
native construction by its coefficient definitions. The physical cross is
a conclusion, with no signed-output realization as a hypothesis. -/
theorem native_family_cross
    (G : Geometry) (B : NativeData G) (c : Context Point) (u : State Point)
    {P : NativeIndex → ℕ → Point → ℝ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily G.strip P α δ β η) (a : Assembly f)
    (hl : a.labels = B.labels)
    (hp : ∀ l, (f.primary l).velocity = (B.primaryBlocks l).velocity)
    (hcp : ∀ l, LabelSumBounds.SameCarrier (f.primary l) (B.primaryBlocks l))
    (ht : ∀ l, (f.tangent l).velocity = (B.signedBlocks c u l).velocity)
    (hct : ∀ l, LabelSumBounds.SameCarrier (f.tangent l) (B.signedBlocks c u l)) :
    Agree G.strip.domain (StateMomentBalances.meanBar (crossTensor f a 0 1))
      (physicalSigma G 2 (u.thetaResidual c)) ∧
    Agree G.strip.domain (StateMomentBalances.meanBar (crossTensor f a 0 2))
      (physicalSigma G 1 (u.axialResidual c)) := by
  have hprimary : primaryField f a = LabelSumBounds.fieldSum B.labels
      (fun l => (B.primaryBlocks l).oscillation) := by
    unfold primaryField
    rw [hl]
    apply congrArg (LabelSumBounds.fieldSum B.labels)
    funext l
    exact oscillation_eq_of_coefficients _ _ (hp l) (hcp l)
  have htangent : tangentField f a = LabelSumBounds.fieldSum B.labels
      (fun l => (B.signedBlocks c u l).oscillation) := by
    unfold tangentField
    rw [hl]
    apply congrArg (LabelSumBounds.fieldSum B.labels)
    funext l
    exact oscillation_eq_of_coefficients _ _ (ht l) (hct l)
  constructor
  · have he := B.requested_cross c u 0
    simp only [crossTensor, hprimary, htangent, LocalSignedRequest.requestedStress,
      Matrix.cons_val_zero] at he ⊢
    exact he
  · have he := B.requested_cross c u 1
    simp only [crossTensor, hprimary, htangent, LocalSignedRequest.requestedStress,
      Matrix.cons_val_one] at he ⊢
    exact he

/-- The signed-wave mean gain for the actual reconstructed state. Incoming
raw residuals and measured defects have exponent `1+σ-κ`; the output raw
residuals have exponent `1+σ-2κ`, and their actual torus means gain `17/100`.
The same native primary, masks, matrix, quotient, and fundamental supply the
cross cancellation. All remaining covariance terms are estimated literally. -/
theorem native_signed_mean_gain
    (G : Geometry) (B : NativeData G) (c : Context Point) (u : State Point)
    {P : NativeIndex → ℕ → Point → ℝ} {σ κ : ℝ}
    (hσ : 1 / 5 ≤ σ) (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1 / 100000)
    (f : LabelSumBounds.SignedFamily G.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : Assembly f)
    (hl : a.labels = B.labels)
    (hp : ∀ l, (f.primary l).velocity = (B.primaryBlocks l).velocity)
    (hcp : ∀ l, LabelSumBounds.SameCarrier (f.primary l) (B.primaryBlocks l))
    (ht : ∀ l, (f.tangent l).velocity = (B.signedBlocks c u l).velocity)
    (hct : ∀ l, LabelSumBounds.SameCarrier (f.tangent l) (B.signedBlocks c u l))
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hold : u.oscillation = oldField f a)
    (H : LocalData G c u (tangentField f a + curlField f a) q gaussian)
    (ho : OperatorBounds G.strip G.operators κ)
    (hX : ∀ i j, MovingField G (incrementTensor f a i j))
    (hS : ∀ i j, MovingField G (crossTensor f a i j))
    (hθ : MeanClass G.strip (1 + σ - κ) (u.thetaResidual c))
    (hz : MeanClass G.strip (1 + σ - κ) (u.axialResidual c))
    (hd : DefectBounds G.slowStrip (σ - κ) c u) :
    let v := waveStage G.gauge c u (tangentField f a + curlField f a) q gaussian
    MeanClass G.strip (1 + σ - 2 * κ) (v.thetaResidual c) ∧
    MeanClass G.strip (1 + σ - 2 * κ) (v.axialResidual c) ∧
    MeanClass G.strip (1 + σ + 17 / 100) (StateMomentBalances.meanBar (v.thetaResidual c)) ∧
    MeanClass G.strip (1 + σ + 17 / 100) (StateMomentBalances.meanBar (v.axialResidual c)) := by
  obtain ⟨hcθ, hcz⟩ := native_family_cross G B c u f a hl hp hcp ht hct
  exact signed_mean_gain_of_cross G c u hσ hκ hκsmall f a q gaussian hold H ho hX hS hθ hz hd hcθ
      hcz

/-- The excluded Gaussian field is carried by the very same output state.
The raw mean estimate does not set this field or its average to zero. -/
theorem native_stage_gaussian_retained
    (G : Geometry) (c : Context Point) (u : State Point)
    {ι : Type} {P : ι → ℕ → Point → ℝ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily G.strip P α δ β η) (a : Assembly f)
    (q : OscillatoryScalar Point) (gaussian : Oscillation Point) :
    (waveStage G.gauge c u (tangentField f a + curlField f a) q gaussian).errors.gaussian =
      u.errors.gaussian + gaussian := rfl

end NavierStokes.SignedMeanGain
