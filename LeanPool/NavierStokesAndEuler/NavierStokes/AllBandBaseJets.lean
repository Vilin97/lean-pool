/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseRadialJets

@[expose] public section

/-!
# Base-field jet bounds on every dyadic band

The positive-order Borel stages vanish when their physical scale is at least
one.  Their error jets therefore vanish on the open region above one.  This
extends the normalized bounds to every positive physical scale and removes
the auxiliary restriction `Q * qhi ≤ 1` from the chart estimates.
-/

noncomputable section

namespace NavierStokes.AllBandBaseJets

open Set Filter Function BaseChartJets PhaseJetBounds PrimaryPulseBounds
open scoped ContDiff Topology BigOperators

abbrev Slow := PhaseCalculus.Slow

section Cutoff

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Positivity of the integer cutoff scales is enough; no asymptotic band
condition is used. -/
theorem slowStage_eq_zero_of_one_le {a : ℕ → ℕ} (ha : ∀ j, 0 < a j)
    (h : ℝ) (f : ℕ → Inner → V) (j : ℕ) {y : Chart} (hy : 1 ≤ y.1) :
    SlowBorelBase.slowStage a h f j y = 0 := by
  have haj : (1 : ℝ) ≤ a j := by exact_mod_cast ha j
  have hprod : 1 ≤ (a j : ℝ) * y.1 := by nlinarith
  have hz := SmoothCutoffs.scaledCutoff_zero_of_one_le_abs
    (a := (a j : ℝ)) (q := y.1) (hprod.trans (le_abs_self _))
  simp only [SlowBorelBase.slowStage, SolenoidalDiagonal.cutStage, hz, zero_smul]

/-- The literal infinite sum equals its uncut order-zero coefficient above
the cutoff. -/
theorem slowSum_eq_leading_of_one_le {a : ℕ → ℕ} (ha : ∀ j, 0 < a j)
    (h : ℝ) (f : ℕ → Inner → V) {y : Chart} (hy : 1 ≤ y.1) :
    SlowBorelBase.slowSum a h f y = f 0 y.2 := by
  have hz : SlowBorelBase.positiveSum a h f y = 0 := by
    change (∑' j, SlowBorelBase.slowStage a h f j y) = 0
    simp only [slowStage_eq_zero_of_one_le ha h f _ hy, tsum_zero]
  simp only [SlowBorelBase.slowSum, hz, add_zero]

/-- A zero germ, rather than only a zero value, kills every actual blown
derivative.  The lemma does not assume differentiability of the function. -/
theorem blownJet_eq_zero_of_above_one {f : Chart → V}
    (hf : ∀ y : Chart, 1 < y.1 → f y = 0) {q : ℝ} (hq : 1 < q)
    (w : Inner) (m : ℕ) : SlowBorelBase.blownJet m f (q, w) = 0 := by
  have he : f =ᶠ[𝓝 (q, w)] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hq] with y hy
    exact hf y hy
  have hmap : SlowBorelBase.scaleMap q (1, w) = (q, w) := by simp
  have ht : Tendsto (SlowBorelBase.scaleMap q) (𝓝 (1, w)) (𝓝 (q, w)) := by
    rw [← hmap]
    exact (SlowBorelBase.scaleMap q).continuous.continuousAt
  have hj := (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (he.comp_tendsto ht) m).self_of_nhds
  simpa only [SlowBorelBase.blownJet, Function.comp_def, iteratedFDeriv_fun_zero,
    Pi.zero_apply] using hj

theorem correction_blownJet_eq_zero {a : ℕ → ℕ} (ha : ∀ j, 0 < a j)
    (h : ℝ) (f : ℕ → Inner → V) {q : ℝ} (hq : 1 < q) (w : Inner) (m : ℕ) :
    SlowBorelBase.blownJet m
      (fun y => SlowBorelBase.slowSum a h f y - f 0 y.2) (q, w) = 0 := by
  apply blownJet_eq_zero_of_above_one (q := q) _ hq w m
  intro y hy
  rw [slowSum_eq_leading_of_one_le ha h f hy.le, sub_self]

/-- The existing small-scale theorem and the exact cutoff identity cover
all positive scales, with the same constant. -/
theorem normalized_correction_bound {a : ℕ → ℕ} {h : ℝ} (hh : 0 < h)
    {f : ℕ → Inner → V} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    {K : Set Inner} (hK : IsCompact K)
    (ha : SlowBorelBase.AdmissibleScales h f K a) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → ∀ w ∈ K,
      ‖SlowBorelBase.blownJet m
        (fun y => SlowBorelBase.slowSum a h f y - f 0 y.2) (q, w)‖ ≤
          C * q ^ (2 * h) := by
  obtain ⟨C, hC, hb⟩ := SlowBorelBase.normalized_correction_bound hh hf hK ha m
  refine ⟨C, hC, fun q hq w hw => ?_⟩
  by_cases hq1 : q ≤ 1
  · exact hb q hq hq1 w hw
  · rw [correction_blownJet_eq_zero ha.positive h f (lt_of_not_ge hq1), norm_zero]
    exact mul_nonneg hC.le (Real.rpow_nonneg hq.le _)

end Cutoff

/-- Both tangential errors retain their original `q^(2*h)` bounds at every
positive physical scale. -/
theorem normalized_tangential_bounds {a : ℕ → ℕ} {h C lo hi : ℝ}
    (hh : 0 < h) (hlo : 0 < lo) {d : SlowBorelBase.Coefficients}
    (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a) (m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 0 < q → ∀ w ∈ SlowBorelBase.innerBox lo hi,
      ‖SlowBorelBase.blownJet m (swirlError a h C d) (q, w)‖ ≤ B * q ^ (2 * h) ∧
      ‖SlowBorelBase.blownJet m (axialError a h d) (q, w)‖ ≤ B * q ^ (2 * h) := by
  obtain ⟨B, hB, hb⟩ := SlowBorelBase.normalized_tangential_bounds hh hlo hd ha m
  refine ⟨B, hB, fun q hq w hw => ?_⟩
  by_cases hq1 : q ≤ 1
  · exact hb q hq hq1 w hw
  · have hq1' : 1 < q := lt_of_not_ge hq1
    have hv : SlowBorelBase.blownJet m (swirlError a h C d) (q, w) = 0 := by
      apply blownJet_eq_zero_of_above_one _ hq1' w m
      intro y hy
      simp only [swirlError, SlowBorelBase.normalizedSwirl,
        slowSum_eq_leading_of_one_le ha.positive h d.phi hy.le,
        SlowBorelBase.leadingSwirl, sub_self]
    have hg := correction_blownJet_eq_zero ha.positive h d.axial hq1' w m
    change SlowBorelBase.blownJet m (axialError a h d) (q, w) = 0 at hg
    rw [hv, hg, norm_zero]
    exact ⟨mul_nonneg hB.le (Real.rpow_nonneg hq.le _),
      mul_nonneg hB.le (Real.rpow_nonneg hq.le _)⟩

/-- Pulling back an all-positive-scale estimate needs only fixed upper and
lower bounds on the normalized scale, not a band cutoff. -/
theorem normalized_error_envelope {ι : Type*} {h qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i)
    (f : Chart → ℝ) (hf : ContDiffOn ℝ ∞ f sumRegion)
    (hb : ∀ j : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 0 < q →
      ∀ w ∈ SlowBorelBase.innerBox lo hi,
        ‖SlowBorelBase.blownJet j f (q, w)‖ ≤ B * q ^ (2 * h)) :
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => f ∘ SlowBorelBase.scaleMap (Q i)) := by
  apply uniform_envelope _ (fun i => (Real.rpow_pos_of_pos (hQ i) _).le)
  · intro i
    apply hf.comp (SlowBorelBase.scaleMap (Q i)).contDiff.contDiffOn
    intro y hy
    exact ⟨mul_pos (hQ i) (hqlo.trans hy.1.1), hlo.trans hy.2.1.1, mem_univ _⟩
  · intro j
    obtain ⟨B, hB, hb⟩ := hb j
    let K := max 1 (1 / qlo)
    have hK : 1 ≤ K := le_max_left _ _
    refine ⟨B * qhi ^ (2 * h) * K ^ j, by positivity, ?_⟩
    intro i y hy
    have hrho : 0 < y.1 := hqlo.trans hy.1.1
    have hinv : 1 / y.1 ≤ K :=
      (one_div_le_one_div_of_le hqlo hy.1.1.le).trans (le_max_right _ _)
    have hscaled := scaled_jet_from_blown hf (hQ i) hrho (hlo.trans hy.2.1.1) hK hinv j
    have hw : y.2 ∈ SlowBorelBase.innerBox lo hi :=
      ⟨⟨hy.2.1.1.le, hy.2.1.2.le⟩, hy.2.2.1.le, hy.2.2.2.le⟩
    have hr : y.1 ^ (2 * h) ≤ qhi ^ (2 * h) :=
      Real.rpow_le_rpow hrho.le hy.1.2.le (by linarith)
    calc
      _ ≤ ‖SlowBorelBase.blownJet j f (Q i * y.1, y.2)‖ * K ^ j := hscaled
      _ ≤ (B * (Q i * y.1) ^ (2 * h)) * K ^ j :=
        mul_le_mul_of_nonneg_right (hb _ (mul_pos (hQ i) hrho) _ hw) (by positivity)
      _ = (B * Q i ^ (2 * h) * y.1 ^ (2 * h)) * K ^ j := by
        rw [Real.mul_rpow (hQ i).le hrho.le]
        ring
      _ ≤ (B * Q i ^ (2 * h) * qhi ^ (2 * h)) * K ^ j :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr (mul_nonneg hB.le (Real.rpow_nonneg (hQ i).le _))) (by
            positivity)
      _ = _ := by ring

/-- The actual swirl and axial errors on the fixed normalized chart. -/
theorem actual_error_envelopes {ι : Type*} {a : ℕ → ℕ} {h C qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) :
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => swirlError a h C d ∘ SlowBorelBase.scaleMap (Q i)) ∧
    EnvelopeJets (oneDomain ι (fun _ => innerRegion qlo qhi lo hi)
      (fun _ => innerRegion_open _ _ _ _)) (fun i _ => Q i ^ (2 * h))
      (fun i => axialError a h d ∘ SlowBorelBase.scaleMap (Q i)) := by
  have hs := errors_smooth ha.strictMono h C hd
  constructor
  · apply normalized_error_envelope hh hqlo hqhi hlo Q hQ _ hs.1
    intro j
    obtain ⟨B, hB, hb⟩ := normalized_tangential_bounds hh hlo hd ha j
    exact ⟨B, hB, fun q hq w hw => (hb q hq w hw).1⟩
  · apply normalized_error_envelope hh hqlo hqhi hlo Q hQ _ hs.2
    intro j
    obtain ⟨B, hB, hb⟩ := normalized_tangential_bounds hh hlo hd ha j
    exact ⟨B, hB, fun q hq w hw => (hb q hq w hw).2⟩

/-- The same literal field estimates as `BaseChartJets.Estimates`, now
for every band with `0 < Q ≤ 1`. -/
theorem actual_estimates {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) : Estimates D Q a h C d := by
  have he := actual_error_envelopes hh hqlo hqhi hlo hd ha Q hQ
  have hc := normalizedCoordinates_polynomial hh hh1 hqlo H
  have hmap (i : ι) (p : Slow) (hp : p ∈ (unitScale D).carrier i) : normalizedCoordinates h p ∈
    innerRegion qlo qhi lo hi := by
    have heta := abs_lt.mp (normalizedCoordinates_eta hh hh1 (H.time i p hp))
    exact ⟨H.q_range i p hp, H.x_range i p hp, heta⟩
  have hev := he.1.comp hc (fun _ => rfl) hmap
  have heg := he.2.comp hc (fun _ => rfl) hmap
  have hf := geometry_factors_polynomial hh hh1 hr hM hqlo H
  have h0 := leading_fields_polynomial (C := C) hh hh1 hr hM hqlo hlo H hd
  have hF : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
      (fun i p => frequency a h C d (Q i) p - leadingFrequency h C d p) := by
    apply (hev.polynomial_smul hf.1).congr
    intro i p _
    simp only [frequency, leadingFrequency, swirlError, Function.comp_apply, smul_eq_mul, mul_sub,
      SlowBorelBase.scaleMap_apply]
  have hG : EnvelopeJets (unitScale D) (fun i _ => Q i ^ (2 * h))
      (fun i p => axial a h d (Q i) p - leadingAxial h d p) := by
    apply (heg.polynomial_smul hf.2).congr
    intro i p _
    simp only [axial, leadingAxial, axialError, Function.comp_apply, smul_eq_mul, mul_sub,
      SlowBorelBase.scaleMap_apply]
  have hw i p (_hp : p ∈ (unitScale D).carrier i) : Q i ^ (2 * h) ≤ 1 :=
    Real.rpow_le_one (hQ i).le (hQ1 i) (by linarith)
  refine ⟨hF, hG, h0.1, h0.2, ?_, ?_⟩
  · exact ((hF.to_polynomial hw).add h0.1).congr (fun _ _ _ => sub_add_cancel _ _)
  · exact ((hG.to_polynomial hw).add h0.2).congr (fun _ _ _ => sub_add_cancel _ _)

/-- All fixed jets and the local first/second derivative base bounds
share constants chosen before any band or label. -/
theorem actual_localBase_and_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    (hconvex : ∀ i, Convex ℝ (D.carrier i))
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    PolynomialJets D (fun i => frequency a h C d (Q i)) ∧
    PolynomialJets D (fun i => axial a h d (Q i)) ∧
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      PhaseEstimates.LocalBaseBounds (frequency a h C d (Q i)) (axial a h d (Q i))
        (leadingFrequency h C d) (leadingAxial h d) (D.carrier i) B (Q i ^ h) := by
  have he := actual_estimates hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1
  exact ⟨he.polynomial_fields.1, he.polynomial_fields.2,
    he.localBaseBounds hh.le hQ hQ1 hconvex⟩

open BaseRadialJets

/-- The same scalar Borel sum has bounded chart jets on every band. -/
theorem scaled_sum_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {f : ℕ → Inner → ℝ} (hf : ∀ j, ContDiff ℝ ∞ (f j))
    (ha : SlowBorelBase.AdmissibleScales h f (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    PolynomialJets (unitScale D) (fun i p =>
      SlowBorelBase.slowSum a h f (SlowBorelBase.scaleMap (Q i) (normalizedCoordinates h p))) := by
  let err : Chart → ℝ := fun y => SlowBorelBase.slowSum a h f y - f 0 y.2
  have hs : ContDiffOn ℝ ∞ err sumRegion := by
    intro y hy
    exact ((SlowBorelBase.slowSum_smoothAt ha.strictMono hf h hy.1).sub
      ((hf 0).contDiffAt.comp y contDiffAt_snd)).contDiffWithinAt
  have he := normalized_error_envelope hh hqlo hqhi hlo Q hQ err hs
    (fun j => normalized_correction_bound hh hf (SlowBorelBase.innerBox_isCompact lo hi) ha j)
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
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    PolynomialJets (unitScale D) (fun i => normalizedStream a h d (Q i)) := by
  have hs := scaled_sum_polynomial hh hh1 hqlo hqhi hlo H (averageSequence_smooth hd)
    (averageSequence_admissible hd ha) Q hQ hQ1
  exact (geometry_factors_polynomial hh hh1 hr hM hqlo H).2.mul hs

theorem reducedRadial_polynomial {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    PolynomialJets (unitScale D) (fun i => reducedRadial a h d (Q i)) := by
  have hs := normalizedStream_polynomial hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1
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
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    EnvelopeJets (unitScale D) (fun i _ => Q i ^ h) (fun i => radial a h C d (Q i)) := by
  have hp := reducedRadial_polynomial hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1
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
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    PolynomialJets (unitScale D) (fun i p => radial a h C d (Q i) p / Q i ^ h) := by
  apply (reducedRadial_polynomial hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1).congr
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
    (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ i p, p ∈ D.carrier i → ∀ j, j ≤ N →
      ‖iteratedFDeriv ℝ j (radial a h C d (Q i)) p‖ ≤ K * Q i ^ h :=
  envelope_unit_bound (radial_envelope hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1) N

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
    (heps : ∀ n l, Q (n, l) ^ h = s.epsilon n)
    (hmap : ∀ n l, MapsTo L s.domain (D.carrier (n, l))) :
    LabelSumBounds.UniformClass s (fun _ _ _ => 1) 1
      (fun l n x => radial a h C d (Q (n, l)) (L x)) := by
  let V : Domain (ℕ × ι) E := oneDomain (ℕ × ι) (fun _ => s.domain) (fun _ => s.isOpen_domain)
  have he := radial_envelope hh hh1 hr hM hqlo hqhi hlo H hd ha Q hQ hQ1
  have hp := he.precomp_linear (D := V) (fun _ => L) (fun _ => rfl)
    (fun i => hmap i.1 i.2) (C := max 1 ‖L‖) (k := 0) (le_max_left _ _)
    (fun _ => by simpa only [pow_zero, mul_one] using le_max_right 1 ‖L‖)
  apply LabelSumBounds.uniformClass_of_envelopeJets hp (K := 1) (q := 0) le_rfl
    (fun n l => by simp [V, oneDomain]) (fun _ _ => subset_rfl)
    (fun _ _ _ _ => zero_le_one)
  intro l n x hx
  simp only [heps, Real.rpow_one, mul_one, le_refl]

/-- Every original dyadic band is covered; the epsilon sequence is unchanged. -/
theorem dyadic_actual_bounds {ι : Type*} {D : Domain ι Slow}
    {a : ℕ → ℕ} {h C r M qlo qhi lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hr : 0 < r) (hM : 1 ≤ M)
    (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (H : GeometryBounds D h r M qlo qhi lo hi)
    (hconvex : ∀ i, Convex ℝ (D.carrier i))
    {d : SlowBorelBase.Coefficients} (hd : SlowBorelBase.SmoothCoefficients d)
    (ha : SlowBorelBase.AdmissibleScales h (SlowBorelBase.coefficientBundle C d)
      (SlowBorelBase.innerBox lo hi) a)
    (band : ι → ℕ) :
    PolynomialJets D (fun i => frequency a h C d (ChartScales.Q (band i))) ∧
    PolynomialJets D (fun i => axial a h d (ChartScales.Q (band i))) ∧
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i,
      PhaseEstimates.LocalBaseBounds
        (frequency a h C d (ChartScales.Q (band i)))
        (axial a h d (ChartScales.Q (band i)))
        (leadingFrequency h C d) (leadingAxial h d) (D.carrier i) B
        (ChartScales.epsilon h (band i)) :=
  actual_localBase_and_polynomial hh hh1 hr hM hqlo hqhi hlo H hconvex hd ha
    (fun i => ChartScales.Q (band i)) (fun i => ChartScales.Q_pos (band i))
    (fun i => ChartScales.Q_le_one (band i))

section FinalBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- The fixed final aligned schedule supplies the all-band tangential
estimates without a replacement schedule or a low-band exception. -/
theorem final_estimates {ι : Type*} {D : Domain ι Slow}
    (upper : ℝ) (B : ℕ) {r M qlo qhi lo hi : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (hhi : hi ≤ FinalSlowBase.boxRadius W upper)
    (hgeom : GeometryBounds D F.data.h r M qlo qhi lo hi)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    Estimates D Q (FinalSlowBase.scales H v upper B) F.data.h W.axis.normalization
      (FinalSlowBase.coefficients H v) :=
  actual_estimates F.data.h_pos F.data.h_lt_half hr hM hqlo hqhi hlo hgeom
    (FinalSlowBase.coefficients_smooth H v)
    (FinalSlowBase.scales_admissible_on H v upper B hlo.le hhi) Q hQ hQ1

/-- The very same final weighted-bundle schedule supplies the averaged
axial estimates. No replacement scale choice is introduced. -/
theorem final_radial_envelope {ι : Type*} {D : Domain ι Slow}
    (upper : ℝ) (B : ℕ) {r M qlo qhi lo hi : ℝ}
    (hr : 0 < r) (hM : 1 ≤ M) (hqlo : 0 < qlo) (hqhi : 0 < qhi) (hlo : 0 < lo)
    (hhi : hi ≤ FinalSlowBase.boxRadius W upper)
    (hgeom : GeometryBounds D F.data.h r M qlo qhi lo hi)
    (Q : ι → ℝ) (hQ : ∀ i, 0 < Q i) (hQ1 : ∀ i, Q i ≤ 1) :
    EnvelopeJets (unitScale D) (fun i _ => Q i ^ F.data.h) (fun i p =>
      Q i ^ CoordinateAlgebra.A F.data.h *
        FinalSlowBase.velocity H v upper B (bandPoint F.data.h (Q i) p) 0) :=
  radial_envelope F.data.h_pos F.data.h_lt_half hr hM hqlo hqhi hlo hgeom
    (FinalSlowBase.coefficients_smooth H v)
    (FinalSlowBase.scales_admissible_on H v upper B hlo.le hhi) Q hQ hQ1

end FinalBase

end NavierStokes.AllBandBaseJets
