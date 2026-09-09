/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FinalSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSumBounds

/-!
# The actual normalized radial base component

The radial coefficient is obtained from the same summed curl base and the
same admissible schedule as the angular and axial coefficients.  Its small
factor is `Q^h`.  The exact stream formula includes the factor `1/2` in
`AxisymmetricFields.velocity_zero`.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.BaseRadialJets

open Set Filter Function BaseChartJets PhaseJetBounds PrimaryPulseBounds
open scoped ContDiff Topology BigOperators

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

/-- Average sequence, defined pointwise by `ProfileHistories.average (d.axial j)`. -/
noncomputable def averageSequence (d : SlowBorelBase.Coefficients) : ℕ → Inner → ℝ :=
  fun j => ProfileHistories.average (d.axial j)

theorem averageSequence_eq_component (C : ℝ) (d : SlowBorelBase.Coefficients) :
    averageSequence d = SlowBorelBase.bundleComponent C d 0 := by
  funext j w
  rfl

theorem averageSequence_smooth {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d) (j : ℕ) : ContDiff ℝ ∞ (averageSequence d j) :=
  SlowBorelBase.average_smooth (hd.axial j)

theorem averageSequence_admissible {a : ℕ → ℕ} {h C : ℝ}
    {d : SlowBorelBase.Coefficients} {K : Set Inner} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d) K a) :
    SlowBorelBase.AdmissibleScales h (averageSequence d) K a := by
  rw [averageSequence_eq_component C d]
  exact SlowBorelBase.admissible_component hd ha 0

/-- Band input, given by `(1 - Q * p.2.2, (Q * p.1 ^ 2 / 2, Q ^ CoordinateAlgebra.D h *
p.2.1))`. -/
noncomputable def bandInput (h Q : ℝ) (p : Slow) : Chart :=
  (1 - Q * p.2.2, (Q * p.1 ^ 2 / 2, Q ^ CoordinateAlgebra.D h * p.2.1))

theorem bandInput_eq (h Q : ℝ) (p : Slow) :
    bandInput h Q p = SimilarityHomogeneity.physicalScale h Q (physicalInput p) := by
  apply Prod.ext
  · change 1 - Q * p.2.2 = 1 - Q * (1 - (1 - p.2.2))
    ring
  · apply Prod.ext
    · change Q * p.1 ^ 2 / 2 = Q * (p.1 ^ 2 / 2)
      ring
    · rfl

theorem bandInput_smooth (h Q : ℝ) : ContDiff ℝ ∞ (bandInput h Q) :=
  (contDiff_const.sub (contDiff_const.mul contDiff_snd.snd)).prodMk
    (((contDiff_const.mul (contDiff_fst.pow 2)).div_const 2).prodMk
      (contDiff_const.mul contDiff_snd.fst))

theorem bandInput_deriv_Z (h Q : ℝ) (p : Slow) :
    fderiv ℝ (bandInput h Q) p (0, (1, 0)) = (0, (0, Q ^ CoordinateAlgebra.D h)) := by
  have hc : HasDerivAt (fun t : ℝ => (p.1, (p.2.1 + t, p.2.2))) (0, (1, 0)) 0 :=
    (hasDerivAt_const 0 p.1).prodMk
      (((hasDerivAt_id 0).const_add p.2.1).prodMk (hasDerivAt_const 0 p.2.2))
  have hd := ((bandInput_smooth h Q).differentiable (by
      simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hc
  have hd' : HasDerivAt (fun t : ℝ => bandInput h Q (p.1, (p.2.1 + t, p.2.2)))
      (0, (0, Q ^ CoordinateAlgebra.D h)) 0 := by
    have hdZ := ((hasDerivAt_id 0).const_add p.2.1).const_mul (Q ^ CoordinateAlgebra.D h)
    have hfull := (hasDerivAt_const 0 (1 - Q * p.2.2)).prodMk
      ((hasDerivAt_const 0 (Q * p.1 ^ 2 / 2)).prodMk hdZ)
    simpa only [bandInput, mul_one, id_eq] using hfull
  simpa only [add_zero] using hd.unique hd'

/-- Full normalized average stream; no new coefficient sequence or cutoff
schedule is chosen. -/
noncomputable def normalizedStream (a : ℕ → ℕ) (h : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  axialFactor h p * SlowBorelBase.slowSum a h (averageSequence d)
    (SlowBorelBase.scaleMap Q (normalizedCoordinates h p))

theorem normalizedStream_eq {a : ℕ → ℕ} {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    (d : SlowBorelBase.Coefficients) {p : Slow} (hT : 0 < p.2.2) :
    normalizedStream a h d Q p = Q ^ CoordinateAlgebra.A h *
      SlowBorelBase.streamFactor a h C d (bandInput h Q p) := by
  rw [bandInput_eq]
  unfold SlowBorelBase.streamFactor SlowBorelBase.physicalProfile
  rw [physicalChart_band hh hh1 hQ hT, ← averageSequence_eq_component]
  simp only [SlowBorelBase.scaleMap_apply, smul_eq_mul]
  rw [← mul_assoc, normalized_power hQ (normalizedCoordinates_q_pos hh hh1 hT)]
  rfl

theorem normalizedStream_smoothAt {a : ℕ → ℕ} (ha : StrictMono a) {h Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) : ContDiffAt ℝ ∞ (normalizedStream a h d Q) p := by
  have hc := normalizedCoordinates_smoothAt hh hh1 hT
  have hq := normalizedCoordinates_q_pos hh hh1 hT
  have hcs := (SlowBorelBase.scaleMap Q).contDiff.contDiffAt.comp p hc
  have hs : ContDiffAt ℝ ∞ (SlowBorelBase.slowSum a h (averageSequence d))
      (SlowBorelBase.scaleMap Q (normalizedCoordinates h p)) :=
    SlowBorelBase.slowSum_smoothAt ha (averageSequence_smooth hd) h
      (show 0 < (SlowBorelBase.scaleMap Q (normalizedCoordinates h p)).1 from mul_pos hQ hq)
  have hp : ContDiffAt ℝ ∞ (axialFactor h) p := hc.fst.rpow_const_of_ne hq.ne'
  have hsc := hs.comp p hcs
  apply hp.mul
  exact hsc

/-- Chain rule for the actual physical axial coordinate. -/
theorem normalizedStream_deriv_Z {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    PhaseCalculus.slowZ (normalizedStream a h d Q) p =
      Q ^ CoordinateAlgebra.A h * Q ^ CoordinateAlgebra.D h *
        AxisymmetricFields.partialZ (SlowBorelBase.streamFactor a h C d) (bandInput h Q p) := by
  have ht : (bandInput h Q p).1 < 1 := by
    change 1 - Q * p.2.2 < 1
    linarith [mul_pos hQ hT]
  have hs := (SlowBorelBase.physicalProfile_smoothAt ha hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 0) (-CoordinateAlgebra.A h) ht).differentiableAt (by
        simp)
  change DifferentiableAt ℝ (SlowBorelBase.streamFactor a h C d) (bandInput h Q p) at hs
  have he : normalizedStream a h d Q =ᶠ[𝓝 p]
      (fun q => Q ^ CoordinateAlgebra.A h * SlowBorelBase.streamFactor a h C d (bandInput h Q q))
          := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd.snd).mem_nhds hT] with q hq
    exact normalizedStream_eq hh hh1 hQ d hq
  have hb := ((bandInput_smooth h Q).differentiable (by
      simp)).differentiableAt (x := p) |>.hasFDerivAt
  have hder := (hs.hasFDerivAt.comp p hb).const_mul (Q ^ CoordinateAlgebra.A h)
  simp only [Function.comp_apply] at hder
  unfold PhaseCalculus.slowZ
  rw [he.fderiv_eq, hder.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, bandInput_deriv_Z]
  have hez : ((0, (0, Q ^ CoordinateAlgebra.D h)) : Chart) =
      Q ^ CoordinateAlgebra.D h • (0, (0, 1)) := by simp
  rw [hez, map_smul]
  simp only [smul_eq_mul, AxisymmetricFields.partialZ]
  ring

/-- Reduced radial, given by `-(p.1 / 2) * PhaseCalculus.slowZ (normalizedStream a h d Q) p`. -/
noncomputable def reducedRadial (a : ℕ → ℕ) (h : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  -(p.1 / 2) * PhaseCalculus.slowZ (normalizedStream a h d Q) p

/-- Literal normalized radial component of the constructed curl base. -/
noncomputable def radial (a : ℕ → ℕ) (h C : ℝ) (d : SlowBorelBase.Coefficients)
    (Q : ℝ) (p : Slow) : ℝ :=
  Q ^ CoordinateAlgebra.A h * SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 0

theorem radial_eq {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    radial a h C d Q p = Q ^ h * reducedRadial a h d Q p := by
  have ht := bandPoint_time (h := h) hQ hT
  have hH := (SlowBorelBase.physicalProfile_smoothAt ha hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 0) (-CoordinateAlgebra.A h)
    (p := AxisymmetricFields.profilePoint (bandPoint h Q p).1 (bandPoint h Q p).2)
        ht).differentiableAt (by
        simp)
  have hK := (SlowBorelBase.physicalProfile_smoothAt ha hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 1) (1 / 2 - CoordinateAlgebra.A h)
    (p := AxisymmetricFields.profilePoint (bandPoint h Q p).1 (bandPoint h Q p).2)
        ht).differentiableAt (by
        simp)
  have hv := AxisymmetricFields.velocity_zero (SlowBorelBase.streamFactor a h C d)
    (SlowBorelBase.swirlPotential a h C d) (bandPoint h Q p).1 (bandPoint h Q p).2 hH hK
  change SlowBorelBase.baseVelocity a h C d (bandPoint h Q p) 0 =
    -(Real.sqrt Q * p.1) * AxisymmetricFields.partialZ (SlowBorelBase.streamFactor a h C d)
      (AxisymmetricFields.profilePoint (bandPoint h Q p).1 (bandPoint h Q p).2) / 2 + 0 * _ at hv
  rw [zero_mul, add_zero, bandPoint_profile hQ.le, ← bandInput_eq] at hv
  have hpow : Real.sqrt Q = Q ^ h * Q ^ CoordinateAlgebra.D h := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hQ]
    congr 1
    unfold CoordinateAlgebra.D
    ring
  unfold radial reducedRadial
  rw [hv, normalizedStream_deriv_Z ha hh hh1 hQ hd hT, hpow]
  ring

/-- Expanded formula, including the exact one-half factor. -/
theorem radial_eq_stream {a : ℕ → ℕ} (ha : StrictMono a) {h C Q : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hQ : 0 < Q)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    {p : Slow} (hT : 0 < p.2.2) :
    radial a h C d Q p = -(Q ^ h * p.1 / 2) *
      PhaseCalculus.slowZ (normalizedStream a h d Q) p := by
  rw [radial_eq ha hh hh1 hQ hd hT]
  unfold reducedRadial
  ring

/-- The same scalar component schedule controls the actual normalized sum.
The result is uniform in every band/label index of `D`. -/
theorem scaled_sum_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {f : ℕ → Inner → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (ha : SlowBorelBase.AdmissibleScales h f (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    PolynomialJets (unitScale D) (fun i p =>
      SlowBorelBase.slowSum a h f (SlowBorelBase.scaleMap (Q i) (normalizedCoordinates h p))) := by
  let err : Chart → ℝ := fun y => SlowBorelBase.slowSum a h f y - f 0 y.2
  have hs : ContDiffOn ℝ ∞ err sumRegion := by
    intro y hy
    exact ((SlowBorelBase.slowSum_smoothAt ha.strictMono hf h hy.1).sub
      ((hf 0).contDiffAt.comp y contDiffAt_snd)).contDiffWithinAt
  have he := normalized_error_envelope hh hqlo hqhi hlo Q hQ hsmall err hs
    (fun j => SlowBorelBase.normalized_correction_bound hh hf (SlowBorelBase.innerBox_isCompact lo
        hi) ha j)
  have hc := normalizedCoordinates_polynomial hh hh1 hqlo H
  have hmap (i : ι) (p : Slow) (hp : p ∈ (unitScale D).carrier i) :
      normalizedCoordinates h p ∈ innerRegion qlo qhi lo hi := by
    exact ⟨H.q_range i p hp, H.x_range i p hp,
      abs_lt.mp (normalizedCoordinates_eta hh hh1 (H.time i p hp))⟩
  have hec := he.comp hc (fun _ => rfl) hmap
  have hlead : PolynomialJets (unitScale D) (fun _ p => f 0 (normalizedCoordinates h p).2) := by
    apply (hc.clm (ContinuousLinearMap.snd ℝ ℝ Inner)).compact_comp isOpen_univ
      (hf 0).contDiffOn (SlowBorelBase.innerBox_isCompact lo hi) (subset_univ _)
    intro i p hp
    have heta := abs_lt.mp (normalizedCoordinates_eta hh hh1 (H.time i p hp))
    exact ⟨⟨(H.x_range i p hp).1.le, (H.x_range i p hp).2.le⟩, heta.1.le, heta.2.le⟩
  have hep := hec.to_polynomial (fun i _ _ =>
    Real.rpow_le_one (hQ i).le (hQ1 i) (show 0 ≤ 2 * h by linarith))
  apply (hep.add hlead).congr
  intro i p hp
  simp only [err, Function.comp_apply, SlowBorelBase.scaleMap_apply, sub_add_cancel]

theorem normalizedStream_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    PolynomialJets (unitScale D) (fun i => normalizedStream a h d (Q i)) := by
  have hs := scaled_sum_polynomial hh hh1 hqlo hqhi hlo H (averageSequence_smooth hd)
    (averageSequence_admissible hd ha) Q hQ hQ1 hsmall
  exact (geometry_factors_polynomial hh hh1 hr hM hqlo H).2.mul hs

theorem reducedRadial_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    PolynomialJets (unitScale D) (fun i => reducedRadial a h d (Q i)) := by
  have hs := normalizedStream_polynomial hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1 hsmall
  have hR : PolynomialJets (unitScale D) (fun _ p => p.1) := by
    have hb : ∀ i, ∀ p ∈ (unitScale D).carrier i,
        ‖(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p + 0‖ ≤ M * (unitScale D).scale i ^ 0 := by
      intro i p hp
      simpa only [ContinuousLinearMap.coe_fst', add_zero, pow_zero, mul_one] using
        (norm_fst_le p).trans (H.bounded i p hp)
    simpa only [ContinuousLinearMap.coe_fst', add_zero] using
      (PolynomialJets.affine (D := unitScale D) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (fun _ => 0) (m := 0) hM hb)
  exact (hR.div_const 2).neg.mul (hs.directional (0, (1, 0)))

/-- A band-only nonnegative factor is an exact envelope and has no slow
derivatives. This does not divide by any vanishing spatial weight. -/
theorem scalar_envelope {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Domain ι E) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    EnvelopeJets (unitScale D) (fun i _ => w i) (fun i _ => w i) := by
  apply uniform_envelope D.isOpen hw (fun _ => contDiffOn_const)
  intro j
  refine ⟨1, zero_lt_one, fun i x hx => ?_⟩
  cases j with
  | zero =>
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, one_mul] using le_of_eq
          (abs_of_nonneg (hw i))
  | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, one_mul]; exact hw i

/-- The actual physical radial coefficient has an all-order `Q^h`
envelope, uniformly before the band and label are selected. -/
theorem radial_envelope {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    EnvelopeJets (unitScale D) (fun i _ => Q i ^ h) (fun i => radial a h C d (Q i)) := by
  have hp := reducedRadial_polynomial hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1 hsmall
  have hw := scalar_envelope D (fun i => Q i ^ h) (fun i => (Real.rpow_pos_of_pos (hQ i) h).le)
  apply (hw.smul_polynomial hp).congr
  intro i p hp
  simpa only [smul_eq_mul] using (radial_eq ha.strictMono hh hh1 (hQ i) hd (H.time i p hp)).symm

/-- All actual derivatives of `b/Q^h` are uniformly bounded. -/
theorem radial_quotient_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    PolynomialJets (unitScale D) (fun i p => radial a h C d (Q i) p / Q i ^ h) := by
  apply (reducedRadial_polynomial hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1 hsmall).congr
  intro i p hp
  change reducedRadial a h d (Q i) p = radial a h C d (Q i) p / Q i ^ h
  rw [radial_eq (C := C) ha.strictMono hh hh1 (hQ i) hd (H.time i p hp)]
  field_simp [(Real.rpow_pos_of_pos (hQ i) h).ne']

/-- A direct finite-jet statement for the actual physical component. -/
theorem radial_uniform_jets {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ i p, p ∈ D.carrier i → ∀ j, j ≤ N →
      ‖iteratedFDeriv ℝ j (radial a h C d (Q i)) p‖ ≤ K * Q i ^ h :=
  envelope_unit_bound (radial_envelope hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1 hsmall) N

/-- Fixed linear native/common coordinate changes preserve the genuine
order-one class. Only the original small factor is used as a weight;
there is no vanishing spatial `zeta` factor in this conclusion. -/
theorem radial_uniform_pullback {ι : Type*} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : WeightedClasses.StripData E) (L : E →L[ℝ] Slow)
    {D : Domain (ℕ × ι) Slow} {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : (ℕ × ι) → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1)
    (heps : ∀ n l, Q (n, l) ^ h = s.epsilon n)
    (hmap : ∀ n l, MapsTo L s.domain (D.carrier (n, l))) :
    LabelSumBounds.UniformClass s (fun _ _ _ => 1) 1
      (fun l n x => radial a h C d (Q (n, l)) (L x)) := by
  let V : Domain (ℕ × ι) E := oneDomain (ℕ × ι) (fun _ => s.domain) (fun _ => s.isOpen_domain)
  have he := radial_envelope hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1 hsmall
  have hp := he.precomp_linear (D := V) (fun _ => L) (fun _ => rfl)
    (fun i => hmap i.1 i.2) (C := max 1 ‖L‖) (k := 0) (le_max_left _ _)
    (fun _ => by simpa only [pow_zero, mul_one] using le_max_right 1 ‖L‖)
  apply LabelSumBounds.uniformClass_of_envelopeJets hp (K := 1) (q := 0) le_rfl
    (fun n l => by simp [V, oneDomain]) (fun _ _ => subset_rfl)
    (fun _ _ _ _ => zero_le_one)
  intro l n x hx
  simp only [heps, Real.rpow_one, mul_one, le_refl]

section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- The corrected one-half identity for the same final aligned base. -/
theorem final_radial_eq (upper : ℝ) (B : ℕ) {Q : ℝ} (hQ : 0 < Q)
    {p : Slow} (hT : 0 < p.2.2) :
    Q ^ CoordinateAlgebra.A F.data.h * FinalSlowBase.velocity H v upper B
      (bandPoint F.data.h Q p) 0 =
      -(Q ^ F.data.h * p.1 / 2) * PhaseCalculus.slowZ
        (normalizedStream (FinalSlowBase.scales H v upper B) F.data.h
          (FinalSlowBase.coefficients H v) Q) p :=
  radial_eq_stream (FinalSlowBase.scales_strictMono H v upper B) F.data.h_pos F.data.h_lt_half hQ
    (FinalSlowBase.coefficients_smooth H v) hT

/-- The very same final weighted-bundle schedule supplies the averaged
axial estimates. No replacement scale choice is introduced. -/
theorem final_radial_envelope {ι : Type*} {D : Domain ι Slow}
    (upper : ℝ) (B : ℕ) {r M qlo qhi lo hi : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (hhi : hi ≤ FinalSlowBase.boxRadius W upper)
    (hgeom : GeometryBounds D F.data.h r M qlo qhi lo hi)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1)
    (hsmall : ∀ i, Q i * qhi ≤ 1) :
    EnvelopeJets (unitScale D) (fun i _ => Q i ^ F.data.h) (fun i p =>
      Q i ^ CoordinateAlgebra.A F.data.h *
        FinalSlowBase.velocity H v upper B (bandPoint F.data.h (Q i) p) 0) :=
  radial_envelope F.data.h_pos F.data.h_lt_half hr hM hqlo hqhi hlo hgeom
    (FinalSlowBase.coefficients_smooth H v)
    (FinalSlowBase.scales_admissible_on H v upper B hlo.le hhi) Q hQ hQ1 hsmall

end FinalBase

end NavierStokes.BaseRadialJets
