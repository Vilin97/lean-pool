/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeStateCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.CommonBaseContext

/-!
# Naturality of the actual common-index temporal state update

All equalities are on full radial and free-torus fibers.  The angular inverse,
stream construction, retained alias and recomputed pressure are the literal
operators used by `VariableGaugeMean.temporalStageState`.
-/

@[expose] public section


namespace NavierStokes.TemporalStateCoherence

noncomputable section

open Set Function Filter
open scoped ContDiff Topology
open PhysicalResidualNaturality GaugeStateCoherence

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane

variable {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup T] [NormedSpace ℝ T]

/-! ## Actual stream transport, reusable by the rank update -/

theorem mul_rpow_pos_left {l : ℝ} (hl : 0 < l) (r d : ℝ) :
    (l * r) ^ d = l ^ d * r ^ d := by
  by_cases hr : 0 ≤ r
  · exact Real.mul_rpow hl.le hr
  · have hrn : r < 0 := lt_of_not_ge hr
    rw [Real.rpow_def_of_neg (mul_neg_of_pos_of_neg hl hrn),
      Real.rpow_def_of_pos hl, Real.rpow_def_of_neg hrn,
      Real.log_mul hl.ne' hrn.ne, add_mul, Real.exp_add]
    ring

theorem physicalSpeed_vector_all {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {l : ℝ} (hl : 0 < l)
    (C : E →L[ℝ] F) (d M N R : ℝ) (v : E) (w : F)
    (hshift : M • C v = (N * l ^ d) • w) :
    C (PressureStream.physicalSpeed d M R • v) =
      l • (PressureStream.physicalSpeed d N (l * R) • w) := by
  have hp : l * l ^ (d - 1) = l ^ d := by
    conv_lhs => lhs; rw [← Real.rpow_one l]
    rw [← Real.rpow_add hl]
    congr 1
    ring
  calc
    _ = (d * R ^ (d - 1)) • (M • C v) := by
      simp only [PressureStream.physicalSpeed, RadialPullback.radialJacobian, map_smul, smul_smul]
    _ = (d * R ^ (d - 1)) • ((N * l ^ d) • w) := by rw [hshift]
    _ = _ := by
      simp only [PressureStream.physicalSpeed, RadialPullback.radialJacobian, smul_smul,
        mul_rpow_pos_left hl]
      congr 1
      rw [show l * (d * (l ^ (d - 1) * R ^ (d - 1)) * N) =
        d * R ^ (d - 1) * N * (l * l ^ (d - 1)) by ring, hp]
      ring

theorem streamPotential_fiberLocal (d a b M : ℝ) (ell : S → ℝ) (v : Plane) :
    PhysicalMeanDomain.FiberLocal (VariableGaugeMean.streamPotential d a b M ell v) := by
  intro f g s he r Y
  exact VariableGaugeMean.divideRadius_fiberLocal _ _ s
    (VariableGaugeMean.compactPrimitive_fiberLocal d a b M ell v _ _ s
      (PhysicalMeanDomain.weightedSource_fiberLocal f g s he)) r Y

theorem streamPotential_congr_profile {d a b d' a' b' : ℝ}
    (hd : d = d') (ha : a = a') (hb : b = b') (M : ℝ) (ell : S → ℝ)
    (v : Plane) (f : PressureStream.Lift S → ℝ) :
    VariableGaugeMean.streamPotential d a b M ell v f =
      VariableGaugeMean.streamPotential d' a' b' M ell v f := by
  subst d'
  subst a'
  subst b'
  rfl

theorem streamPotential_on {l : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {a b d M N u : ℝ} (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (v w : Plane) (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    (ell : S → ℝ) (ell' : T → ℝ) {V : Set S} {U : Set T} (hU : IsOpen U)
    (hmap : MapsTo P V U) (hpos : ∀ s ∈ V, 0 < ell s)
    (hlen : ∀ s ∈ V, ell' (P s) = l * ell s)
    {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u f fr)
    (hf : ContDiffOn ℝ ∞ fr (PhysicalMeanDomain.slowDomain U))
    (hs : VariableGaugeMean.SupportedGauge a b ell' U fr) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (u / l)
      (VariableGaugeMean.streamPotential d a b M ell v f)
      (VariableGaugeMean.streamPotential d a b N ell' w fr) := by
  intro z hz
  have hfiber : ∀ r Y, f (r, (z.2.1, Y)) =
      MeanChartCompatibility.coverPull l P.toContinuousLinearMap k u fr (r, (z.2.1, Y)) := by
    intro r Y
    rw [GaugeStateCoherence.coverPull_eq l hl.ne' P k]
    exact he _ hz
  rw [streamPotential_fiberLocal d a b M ell v _ _ z.2.1 hfiber z.1 z.2.2]
  have ht := VariableGaugeMean.streamPotential_coverPull hl ha hab hd P.toContinuousLinearMap
    k M N u v w hshift ell ell' hU hf hs z (hmap hz) (hpos _ hz) (hlen _ hz)
  rw [GaugeStateCoherence.chartEquiv_apply]
  exact ht

theorem graphDr_on {l : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {d M N u : ℝ} (v w : Plane)
    (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    {V : Set S} (hV : IsOpen V) {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u f fr) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (u*l)
      (PressureStream.graphDr (PressureStream.physicalSpeed d M) ((0 : S), v) f)
      (PressureStream.graphDr (PressureStream.physicalSpeed d N) ((0 : T), w) fr) := by
  apply he.along (PhysicalMeanDomain.slowDomain_open hV)
  intro z hz
  rw [GaugeStateCoherence.chartEquiv_apply]
  apply Prod.ext
  · simp [PressureStream.radialVector]
  · change (P.toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k))
        (PressureStream.physicalSpeed d M z.1 • ((0 : S), v)) =
      l • (PressureStream.physicalSpeed d N (l * z.1) • ((0 : T), w))
    apply physicalSpeed_vector_all hl
    apply Prod.ext
    · simp
    · exact hshift

theorem divideRadius_on {l : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {u : ℝ} {V : Set S} {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u f fr) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (u*l)
      (PressureStream.divideRadius f) (PressureStream.divideRadius fr) := by
  intro z hz
  change f z / z.1 = (u*l) * (fr (chartEquiv l hl.ne' P k z) / (chartEquiv l hl.ne' P k z).1)
  rw [he z hz, GaugeStateCoherence.chartEquiv_apply]
  by_cases hr : z.1 = 0
  · simp [hr]
  · field_simp

theorem streamGamma_on {l : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {d M N u : ℝ} (v w : Plane)
    (hshift : M • TemporalMeanUpdate.coverMap k v = (N * l ^ d) • w)
    {V : Set S} (hV : IsOpen V) {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u f fr) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (u*l)
      (PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : S), v) f)
      (PressureStream.streamGamma (PressureStream.physicalSpeed d N) ((0 : T), w) fr) :=
  (graphDr_on hl P k v w hshift hV he).add (divideRadius_on hl P k he)

theorem streamBeta_on {l : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {u b : ℝ} (v : S × Plane) (w : T × Plane)
    (hvec : (P.toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k)) v = b • w)
    {V : Set S} (hV : IsOpen V) {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u f fr) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (u*b)
      (PressureStream.streamBeta v f) (PressureStream.streamBeta w fr) := by
  have hd := he.along (PhysicalMeanDomain.slowDomain_open hV)
    (V := fun _ => ((0 : ℝ), v)) (W := fun _ => ((0 : ℝ), w)) (b := b) (by
      intro z hz
      rw [GaugeStateCoherence.chartEquiv_apply]
      apply Prod.ext
      · simp
      · exact hvec)
  have hn := hd.smul (-1)
  simp only [
    neg_one_smul] at hn ⊢
  exact hn

/-! ## The actual common-index inverse and its normalization -/

/-- Clock, given by `ChartScales.Tg ^ i * ChartScales.Q n ^ (1+h)`. -/
noncomputable def clock (h : ℝ) (n i : ℕ) : ℝ :=
  ChartScales.Tg ^ i * ChartScales.Q n ^ (1+h)

theorem clock_pos (h : ℝ) (n i : ℕ) : 0 < clock h n i :=
  mul_pos (pow_pos ChartScales.Tg_pos _) (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _)

theorem clock_factor (h : ℝ) (n i nr ir k : ℕ) (c l : ℝ)
    (hclock : clock h n i * ChartScales.Tg ^ k = (c * l) * clock h nr ir) :
    (clock h n i)⁻¹ * (ChartScales.Tg ^ k)⁻¹ * (c*c*l) = c * (clock h nr ir)⁻¹ := by
  field_simp [(clock_pos h n i).ne', (clock_pos h nr ir).ne',
    (pow_pos ChartScales.Tg_pos k).ne']
  calc
    _ = c * (c*l*clock h nr ir) := by ring
    _ = _ := by rw [hclock]; ring

theorem temporalAtIndex_coverPull (h : ℝ) (n i nr ir k : ℕ) (c l : ℝ)
    (P : S →L[ℝ] T)
    (hclock : clock h n i * ChartScales.Tg ^ k = (c * l) * clock h nr ir)
    {f : PressureStream.Lift T → ℝ} (hf : ContDiff ℝ ∞ f)
    (hp : PressureStream.TorusPeriodicLift f) (z : PressureStream.Lift S) :
    MeanChartCompatibility.temporalAtIndex h n i
      (MeanChartCompatibility.coverPull l P k (c*c*l) f) z =
      c * MeanChartCompatibility.temporalAtIndex h nr ir f
        (MeanChartCompatibility.chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z) := by
  unfold MeanChartCompatibility.temporalAtIndex
  rw [MeanChartCompatibility.temporalInverse_centered_coverPull l P k (c*c*l) hf hp z]
  change -(clock h n i)⁻¹ * ((ChartScales.Tg ^ k)⁻¹ *
      ((c*c*l) * TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)
        (MeanChartCompatibility.chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z))) = _
  calc
    _ = -((clock h n i)⁻¹ * (ChartScales.Tg ^ k)⁻¹ * (c*c*l)) *
        TemporalMeanUpdate.temporalInverse (TemporalMeanUpdate.centered f)
          (MeanChartCompatibility.chartLinear l (P.prodMap (TemporalMeanUpdate.coverMap k)) z) := by
              ring
    _ = _ := by rw [clock_factor h n i nr ir k c l hclock]; dsimp only [clock]; ring

section FiniteParameters

variable [FiniteDimensional ℝ S] [FiniteDimensional ℝ T]

omit [FiniteDimensional ℝ S] [FiniteDimensional ℝ T] in
theorem temporalAtIndex_on {l c : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    (h : ℝ) (n i nr ir : ℕ)
    (hclock : clock h n i * ChartScales.Tg ^ k = (c * l) * clock h nr ir)
    {V : Set S} {U : Set T} (hU : IsOpen U) (hmap : MapsTo P V U)
    {f : PressureStream.Lift S → ℝ} {fr : PressureStream.Lift T → ℝ}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (c * c * l) f fr)
    (hf : ContDiffOn ℝ ∞ fr (PhysicalMeanDomain.slowDomain U))
    (hp : PhysicalMeanDomain.PeriodicOn U fr) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c
      (MeanChartCompatibility.temporalAtIndex h n i f)
      (MeanChartCompatibility.temporalAtIndex h nr ir fr) := by
  intro z hz
  let g := PhysicalMeanDomain.freezeSlow (P z.2.1) fr
  have hg : ContDiff ℝ ∞ g := VariableGaugeMean.freezeSlow_contDiff hU (hmap hz) hf
  have hgp : PressureStream.TorusPeriodicLift g := fun r s Y j => hp r (P z.2.1) (hmap hz) Y j
  have hfiber : ∀ r Y, f (r, (z.2.1, Y)) =
      MeanChartCompatibility.coverPull l P.toContinuousLinearMap k (c*c*l) g (r, (z.2.1, Y)) := by
    intro r Y
    rw [GaugeStateCoherence.coverPull_eq l hl.ne' P k]
    have ht := he (r, (z.2.1, Y)) hz
    simp only [GaugeStateCoherence.chartEquiv_apply] at ht ⊢
    exact ht
  rw [VariableGaugeMean.temporalAtIndex_fiberLocal h n i _ _ z.2.1 hfiber z.1 z.2.2]
  have ht := temporalAtIndex_coverPull h n i nr ir k c l P.toContinuousLinearMap hclock hg hgp z
  have hr := VariableGaugeMean.temporalAtIndex_fiberLocal h nr ir g fr (P z.2.1)
    (fun _ _ => rfl) (l*z.1) (TemporalMeanUpdate.coverMap k z.2.2)
  rw [GaugeStateCoherence.chartEquiv_apply]
  exact ht.trans (congrArg (fun x : ℝ => c*x) hr)

end FiniteParameters

theorem fastTime_on {l : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
    {u b : ℝ} {V : Set S} (hV : IsOpen V)
    (o : MeanIncrementBounds.Operators (PressureStream.Lift S))
    (r : MeanIncrementBounds.Operators (PressureStream.Lift T)) (n nr : ℕ)
    (hv : chartEquiv l hl.ne' P k (o.fastCoefficient n • o.vT) =
      b • (r.fastCoefficient nr • r.vT))
    {f : MeanIncrementBounds.Field (PressureStream.Lift S)}
    {fr : MeanIncrementBounds.Field (PressureStream.Lift T)}
    (he : ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) u (f n) (fr nr)) :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (u*b)
      (o.fastTime f n) (r.fastTime fr nr) := by
  have ht := he.along (PhysicalMeanDomain.slowDomain_open hV)
    (V := fun _ => o.fastCoefficient n • o.vT)
    (W := fun _ => r.fastCoefficient nr • r.vT) (fun _ _ => hv)
  intro z hz
  simpa only [MeanIncrementBounds.Operators.fastTime, HarmonicCalculus.along, map_smul,
    smul_eq_mul] using ht z hz

/-! ## Literal temporal fields and retained alias -/

section StateFields

variable [FiniteDimensional ℝ S] [FiniteDimensional ℝ T]
  {l c : ℝ} (hl : 0 < l) (P : S ≃L[ℝ] T) (k : ℕ)
  {V : Set S} {U : Set T} (hV : IsOpen V) (hU : IsOpen U) (hmap : MapsTo P V U)
  (g : VariableGaugeMean.GaugeData S) (gr : VariableGaugeMean.GaugeData T)
  (C : CorrectionState.Context (PressureStream.Lift S))
  (Cr : CorrectionState.Context (PressureStream.Lift T))
  (s : CorrectionState.State (PressureStream.Lift S))
  (r : CorrectionState.State (PressureStream.Lift T))
  (h : ℝ) (index indexr : ℕ → ℕ) (n nr : ℕ)
  (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
  (hg : GaugeOn V l P.toContinuousLinearMap k g gr n nr)
  (H : StateOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l s r n nr)
  (G : ContextOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l C Cr n nr)
  (hclock : clock h n (index n) * ChartScales.Tg ^ k = (c * l) * clock h nr (indexr nr))
  (hfz : ContDiffOn ℝ ∞ (r.axialResidual Cr nr) (PhysicalMeanDomain.slowDomain U))
  (hpz : PhysicalMeanDomain.PeriodicOn U (r.axialResidual Cr nr))
  (hsz : VariableGaugeMean.SupportedGauge gr.radial.inner gr.radial.outer (gr.length nr) U
      (r.axialResidual Cr nr))

include hV hU hmap ha hd hg H G hclock hfz hpz hsz

omit [FiniteDimensional ℝ S] in
theorem temporalPotential_on :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) (c/l)
      (VariableGaugeMean.temporalPotential g h index C s n)
      (VariableGaugeMean.temporalPotential gr h indexr Cr r nr) := by
  have hE := H.axialResidual G (PhysicalMeanDomain.slowDomain_open hV) hl.ne'
  have hD := temporalAtIndex_on hl P k h n (index n) nr (indexr nr) hclock hU hmap hE hfz hpz
  have hDf := VariableGaugeMean.temporalAtIndex_contDiffOn h nr (indexr nr) hU hfz hpz
  have hDs := VariableGaugeMean.temporalAtIndex_supportedGauge h nr (indexr nr) hsz
  have hsup : VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (gr.length nr) U
      (MeanChartCompatibility.temporalAtIndex h nr (indexr nr) (r.axialResidual Cr nr)) := by
    simpa only [hg.inner, hg.outer] using hDs
  change ScalarOn _ _ _ (VariableGaugeMean.streamPotential _ _ _ _ _ _ _)
    (VariableGaugeMean.streamPotential _ _ _ _ _ _ _)
  rw [streamPotential_congr_profile hg.exponent hg.inner hg.outer
    (gr.radial.frequency nr) (gr.length nr) gr.radial.radialDirection
    (MeanChartCompatibility.temporalAtIndex h nr (indexr nr) (r.axialResidual Cr nr))]
  exact streamPotential_on hl P k ha g.radial.inner_lt_outer hd
    g.radial.radialDirection gr.radial.radialDirection hg.frequency (g.length n) (gr.length nr)
    hU hmap hg.positive hg.length hD hDf hsup

variable (axial : S × Plane) (axialr : T × Plane)
  (haxial : (P.toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k)) (C.operators.epsilon
      n • axial) =
    l • (Cr.operators.epsilon nr • axialr))
  (hfθ : ContDiffOn ℝ ∞ (r.thetaResidual Cr nr) (PhysicalMeanDomain.slowDomain U))
  (hpθ : PhysicalMeanDomain.PeriodicOn U (r.thetaResidual Cr nr))

include haxial hfθ hpθ

omit [FiniteDimensional ℝ S] in
theorem temporalIncrement_on :
    TripleOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c
      (VariableGaugeMean.temporalIncrementState g h index axial C s)
      (VariableGaugeMean.temporalIncrementState gr h indexr axialr Cr r) n nr := by
  have hpot := temporalPotential_on hl P k hV hU hmap g gr C Cr s r h index indexr n nr
    ha hd hg H G hclock hfz hpz hsz
  refine ⟨?_, ?_, ?_⟩
  · exact (streamBeta_on hl P k _ _ haxial hV hpot).reweight (div_mul_cancel₀ c hl.ne')
  · exact temporalAtIndex_on hl P k h n (index n) nr (indexr nr) hclock hU hmap
      (H.thetaResidual G (PhysicalMeanDomain.slowDomain_open hV) hl.ne') hfθ hpθ
  · have hγ := (streamGamma_on hl P k g.radial.radialDirection gr.radial.radialDirection
      hg.frequency hV hpot).reweight (div_mul_cancel₀ c hl.ne')
    simpa only [VariableGaugeMean.temporalIncrementState, hg.exponent] using hγ

omit [FiniteDimensional ℝ S] in
theorem temporalAxialDifference_on :
    ScalarOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c
      (VariableGaugeMean.temporalAxialDifference g h index C s n)
      (VariableGaugeMean.temporalAxialDifference gr h indexr Cr r nr) := by
  have hD := temporalAtIndex_on hl P k h n (index n) nr (indexr nr) hclock hU hmap
    (H.axialResidual G (PhysicalMeanDomain.slowDomain_open hV) hl.ne') hfz hpz
  have hI := temporalIncrement_on hl P k hV hU hmap g gr C Cr s r h index indexr n nr
    ha hd hg H G hclock hfz hpz hsz axial axialr haxial hfθ hpθ
  exact hD.sub hI.axial

variable (hfast : chartEquiv l hl.ne' P k (C.operators.fastCoefficient n • C.operators.vT) =
  (c * l) • (Cr.operators.fastCoefficient nr • Cr.operators.vT))

include hfast

omit [FiniteDimensional ℝ S] in
theorem temporalAliasState_on :
    ∀ z ∈ PhysicalMeanDomain.slowDomain V, ∀ theta i,
      VariableGaugeMean.temporalAliasState g h index C s n (z, theta) i =
        (c*c*l) * VariableGaugeMean.temporalAliasState gr h indexr Cr r nr
          (chartEquiv l hl.ne' P k z, theta) i := by
  have hD := temporalAxialDifference_on hl P k hV hU hmap g gr C Cr s r h index indexr n nr
    ha hd hg H G hclock hfz hpz hsz axial axialr haxial hfθ hpθ
  have ht := (fastTime_on hl P k hV C.operators Cr.operators n nr hfast hD).reweight
    (b := c*c*l) (by ring)
  intro z hz theta i
  fin_cases i
  · change (0 : ℝ) = (c*c*l) * 0
    simp
  · change (0 : ℝ) = (c*c*l) * 0
    simp
  · change -C.operators.fastTime _ n z = (c*c*l) * -Cr.operators.fastTime _ nr _
    rw [ht z hz]
    ring

omit [FiniteDimensional ℝ S] in
theorem temporalBeforePressure_on :
    StateOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l
      (s.addIncrement (VariableGaugeMean.temporalIncrementState g h index axial C s) 0 0 0
        ⟨0, 0, VariableGaugeMean.temporalAliasState g h index C s⟩)
      (r.addIncrement (VariableGaugeMean.temporalIncrementState gr h indexr axialr Cr r) 0 0 0
        ⟨0, 0, VariableGaugeMean.temporalAliasState gr h indexr Cr r⟩) n nr := by
  have hI := temporalIncrement_on hl P k hV hU hmap g gr C Cr s r h index indexr n nr
    ha hd hg H G hclock hfz hpz hsz axial axialr haxial hfθ hpθ
  have hA := temporalAliasState_on hl P k hV hU hmap g gr C Cr s r h index indexr n nr
    ha hd hg H G hclock hfz hpz hsz axial axialr haxial hfθ hpθ hfast
  refine ⟨H.mean.updated hI, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    change s.pressure n z + 0 = (c*c) * (r.pressure nr (chartEquiv l hl.ne' P k z) + 0)
    simpa only [add_zero] using H.pressure z hz
  · intro z hz theta i
    change s.oscillation n (z,theta) i + 0 = c * (r.oscillation nr (chartEquiv l hl.ne' P k
        z,theta) i + 0)
    simpa only [add_zero] using H.oscillation z hz theta i
  · intro z hz theta
    change s.oscillatoryPressure n (z,theta) + 0 =
      (c*c) * (r.oscillatoryPressure nr (chartEquiv l hl.ne' P k z,theta) + 0)
    simpa only [add_zero] using H.oscillatoryPressure z hz theta
  · intro z hz theta i
    change s.errors.base n (z,theta) i + 0 =
      (c*c*l) * (r.errors.base nr (chartEquiv l hl.ne' P k z,theta) i + 0)
    simpa only [add_zero] using H.baseError z hz theta i
  · intro z hz theta i
    change s.errors.gaussian n (z,theta) i + 0 =
      (c*c*l) * (r.errors.gaussian nr (chartEquiv l hl.ne' P k z,theta) i + 0)
    simpa only [add_zero] using H.gaussian z hz theta i
  · intro z hz theta i
    change s.errors.aliasError n (z,theta) i + VariableGaugeMean.temporalAliasState g h index C s n
        (z,theta) i =
      (c*c*l) * (r.errors.aliasError nr (chartEquiv l hl.ne' P k z,theta) i +
        VariableGaugeMean.temporalAliasState gr h indexr Cr r nr (chartEquiv l hl.ne' P k z,theta)
            i)
    rw [H.aliasError z hz theta i, hA z hz theta i, mul_add]

omit [FiniteDimensional ℝ S] in
/-- Full coherence of the literal temporal stage, including recomputed
pressure. The analytic conditions concern the source supplied to that pressure
integral; output coherence is derived. -/
theorem temporalStage_on
    (hfpost : ContDiffOn ℝ ∞ ((VariableGaugeMean.temporalStageState gr h indexr axialr Cr r).gr Cr
        nr)
      (PhysicalMeanDomain.slowDomain U))
    (hppost : PhysicalMeanDomain.PeriodicOn U
      ((VariableGaugeMean.temporalStageState gr h indexr axialr Cr r).gr Cr nr))
    (hspost : VariableGaugeMean.SupportedGauge gr.radial.inner gr.radial.outer (gr.length nr) U
      ((VariableGaugeMean.temporalStageState gr h indexr axialr Cr r).gr Cr nr)) :
    StateOn (PhysicalMeanDomain.slowDomain V) (chartEquiv l hl.ne' P k) c l
      (VariableGaugeMean.temporalStageState g h index axial C s)
      (VariableGaugeMean.temporalStageState gr h indexr axialr Cr r) n nr := by
  have hb := temporalBeforePressure_on hl P k hV hU hmap g gr C Cr s r h index indexr n nr
    ha hd hg H G hclock hfz hpz hsz axial axialr haxial hfθ hpθ hfast
  exact GaugeStateCoherence.reconstructState_on hl P k hV hU hmap g gr C Cr _ _ n nr
    ha hd hg hb G hfpost hppost hspost

end StateFields

theorem temporalStage_gr_eq (g : VariableGaugeMean.GaugeData S) (h : ℝ) (index : ℕ → ℕ)
    (axial : S × Plane) (C : CorrectionState.Context (PressureStream.Lift S))
    (s : CorrectionState.State (PressureStream.Lift S)) :
    (VariableGaugeMean.temporalStageState g h index axial C s).gr C =
      MeanIncrementBounds.gr C.operators C.base
        (MeanIncrementBounds.updated s.mean (VariableGaugeMean.temporalIncrementState g h index
            axial C s))
        s.covariance := by
  change MeanIncrementBounds.gr _ _ _
    (CorrectionState.bilinearCovariance (s.oscillation + 0) (s.oscillation + 0)) = _
  simp only [add_zero]
  rfl

/-! ## Actual similarity bands and common graph operators -/

theorem clock_band_transport (h : ℝ) (n m i ir k : ℕ) (hi : i + k = ir) :
    clock h n i * ChartScales.Tg ^ k =
      (bandVelocityScale h n m * bandScale n m) * clock h m ir := by
  have hu : bandVelocityScale h n m * bandScale n m =
      (ChartScales.Q n / ChartScales.Q m) ^ (1+h) := by
    rw [bandVelocityScale, bandScale,
      ← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m))]
    congr 1
    unfold CoordinateAlgebra.A
    ring
  rw [hu, clock, clock, ← hi, pow_add,
    Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le]
  field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos m) (1+h)).ne']

/-- Axial direction, given by `((0,1),0)`. -/
noncomputable def axialDirection : Plane × Plane := ((0,1),0)

theorem band_axial_scalar (h : ℝ) (n m : ℕ) :
    (ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.D h * ChartScales.epsilon h n =
      bandScale n m * ChartScales.epsilon h m := by
  unfold CoordinateAlgebra.D ChartScales.epsilon bandScale
  rw [Real.rpow_sub (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)),
    Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le h]
  field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos n) h).ne',
    (Real.rpow_pos_of_pos (ChartScales.Q_pos m) h).ne']

theorem band_axial_transport (h : ℝ) (n m k : ℕ) :
    ((bandSlowEquiv h n m).toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k))
      (ChartScales.epsilon h n • axialDirection) =
        bandScale n m • (ChartScales.epsilon h m • axialDirection) := by
  have hP : bandSlowEquiv h n m (ChartScales.epsilon h n • ((0 : ℝ), (1 : ℝ))) =
      bandScale n m • (ChartScales.epsilon h m • ((0 : ℝ), (1 : ℝ))) := by
    rw [bandSlowEquiv_apply]
    ext <;> simp [band_axial_scalar]
  apply Prod.ext
  · exact hP
  · simp [axialDirection]

theorem band_temporalVector_transport (h : ℝ) (n m k : ℕ) :
    bandChartEquiv h n m k ((0 : ℝ), ((0 : Plane), TorusInverse.vector .temporal)) =
      ChartScales.Tg ^ k • ((0 : ℝ), ((0 : Plane), TorusInverse.vector .temporal)) := by
  rw [bandChartEquiv_apply, TemporalMeanUpdate.coverMap_temporal]
  simp

theorem common_fast_transport (h : ℝ) (index : ℕ → ℕ) (a b : ℝ) (hab : a < b)
    (n m k : ℕ) (hi : index n + k = index m) :
    bandChartEquiv h n m k ((CommonBaseContext.operators h index a b hab).fastCoefficient n •
      (CommonBaseContext.operators h index a b hab).vT) =
      (bandVelocityScale h n m * bandScale n m) •
        ((CommonBaseContext.operators h index a b hab).fastCoefficient m •
          (CommonBaseContext.operators h index a b hab).vT) := by
  change bandChartEquiv h n m k (clock h n (index n) •
      ((0 : ℝ), ((0 : Plane), TorusInverse.vector .temporal))) =
    (bandVelocityScale h n m * bandScale n m) •
      (clock h m (index m) • ((0 : ℝ), ((0 : Plane), TorusInverse.vector .temporal)))
  rw [map_smul, band_temporalVector_transport, smul_smul,
    clock_band_transport h n m (index n) (index m) k hi, smul_smul]

section Similarity

variable {h d a b M ca cb : ℝ}
  (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hab : a < b) (hd : 0 < d) (hcab : ca < cb)
  (index : ℕ → ℕ) (n m k : ℕ) (hi : index n + k = index m)
  {V U : Set Plane} (hV : IsOpen V) (hU : IsOpen U) (htime : ∀ s ∈ V, 0 < s.1)
  (hmap : MapsTo (bandSlowEquiv h n m) V U)
  (C Cr : CorrectionState.Context (PressureStream.Lift Plane))
  (s r : CorrectionState.State (PressureStream.Lift Plane))
  (hC : C.operators = CommonBaseContext.operators h index ca cb hcab)
  (hCr : Cr.operators = CommonBaseContext.operators h index ca cb hcab)
  (H : StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
    (bandVelocityScale h n m) (bandScale n m) s r n m)
  (G : ContextOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
    (bandVelocityScale h n m) (bandScale n m) C Cr n m)
  (hfz : ContDiffOn ℝ ∞ (r.axialResidual Cr m) (PhysicalMeanDomain.slowDomain U))
  (hpz : PhysicalMeanDomain.PeriodicOn U (r.axialResidual Cr m))
  (hsz : VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength (2 * h)) U (r.axialResidual
      Cr m))
  (hfθ : ContDiffOn ℝ ∞ (r.thetaResidual Cr m) (PhysicalMeanDomain.slowDomain U))
  (hpθ : PhysicalMeanDomain.PeriodicOn U (r.thetaResidual Cr m))


include hh hh1 ha hd hi hV hU htime hmap hC hCr H G hfz hpz hsz hfθ hpθ

theorem similarity_temporalFields_on :
    TripleOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k) (bandVelocityScale h n m)
      (VariableGaugeMean.temporalIncrementState (VariableGaugeMean.similarityGauge h d a b M hab
          index) h index axialDirection C s)
      (VariableGaugeMean.temporalIncrementState (VariableGaugeMean.similarityGauge h d a b M hab
          index) h index axialDirection Cr r) n m ∧
    ∀ z ∈ PhysicalMeanDomain.slowDomain V, ∀ theta i,
      VariableGaugeMean.temporalAliasState (VariableGaugeMean.similarityGauge h d a b M hab index)
          h index C s n (z,theta) i =
      (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) *
        VariableGaugeMean.temporalAliasState (VariableGaugeMean.similarityGauge h d a b M hab
            index) h index Cr r m (bandChartEquiv h n m k z,theta) i := by
  have hg := similarityGaugeOn hh hh1 d a b M hab index n m k hi htime
  have hclock := clock_band_transport h n m (index n) (index m) k hi
  have haxial : ((bandSlowEquiv h n m).toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap
      k))
      (C.operators.epsilon n • axialDirection) =
        bandScale n m • (Cr.operators.epsilon m • axialDirection) := by
    rw [hC, hCr]
    exact band_axial_transport h n m k
  have hfast : bandChartEquiv h n m k (C.operators.fastCoefficient n • C.operators.vT) =
      (bandVelocityScale h n m * bandScale n m) • (Cr.operators.fastCoefficient m •
          Cr.operators.vT) := by
    rw [hC, hCr]
    exact common_fast_transport h index ca cb hcab n m k hi
  exact ⟨temporalIncrement_on (bandScale_pos n m) (bandSlowEquiv h n m) k hV hU hmap
    (VariableGaugeMean.similarityGauge h d a b M hab index) (VariableGaugeMean.similarityGauge h d
        a b M hab index) C Cr s r h index index n m ha hd hg H G hclock hfz hpz hsz
    axialDirection axialDirection haxial hfθ hpθ,
    temporalAliasState_on (bandScale_pos n m) (bandSlowEquiv h n m) k hV hU hmap
    (VariableGaugeMean.similarityGauge h d a b M hab index) (VariableGaugeMean.similarityGauge h d
        a b M hab index) C Cr s r h index index n m ha hd hg H G hclock hfz hpz hsz
    axialDirection axialDirection haxial hfθ hpθ hfast⟩

theorem similarity_temporalStage_on
    (hfpost : ContDiffOn ℝ ∞ ((VariableGaugeMean.temporalStageState
        (VariableGaugeMean.similarityGauge h d a b M hab index) h index axialDirection Cr r).gr Cr
            m)
      (PhysicalMeanDomain.slowDomain U))
    (hppost : PhysicalMeanDomain.PeriodicOn U
      ((VariableGaugeMean.temporalStageState (VariableGaugeMean.similarityGauge h d a b M hab
          index) h index axialDirection Cr r).gr Cr m))
    (hspost : VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength (2 * h)) U
      ((VariableGaugeMean.temporalStageState (VariableGaugeMean.similarityGauge h d a b M hab
          index) h index axialDirection Cr r).gr Cr m)) :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m)
      (VariableGaugeMean.temporalStageState (VariableGaugeMean.similarityGauge h d a b M hab index)
          h index axialDirection C s)
      (VariableGaugeMean.temporalStageState (VariableGaugeMean.similarityGauge h d a b M hab index)
          h index axialDirection Cr r) n m := by
  have hg := similarityGaugeOn hh hh1 d a b M hab index n m k hi htime
  have hclock := clock_band_transport h n m (index n) (index m) k hi
  have haxial : ((bandSlowEquiv h n m).toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap
      k))
      (C.operators.epsilon n • axialDirection) =
        bandScale n m • (Cr.operators.epsilon m • axialDirection) := by
    rw [hC, hCr]
    exact band_axial_transport h n m k
  have hfast : bandChartEquiv h n m k (C.operators.fastCoefficient n • C.operators.vT) =
      (bandVelocityScale h n m * bandScale n m) • (Cr.operators.fastCoefficient m •
          Cr.operators.vT) := by
    rw [hC, hCr]
    exact common_fast_transport h index ca cb hcab n m k hi
  exact temporalStage_on (bandScale_pos n m) (bandSlowEquiv h n m) k hV hU hmap
    (VariableGaugeMean.similarityGauge h d a b M hab index) (VariableGaugeMean.similarityGauge h d
        a b M hab index) C Cr s r h index index n m ha hd hg H G hclock hfz hpz hsz
    axialDirection axialDirection haxial hfθ hpθ hfast hfpost hppost hspost

end Similarity

end

end NavierStokes.TemporalStateCoherence
