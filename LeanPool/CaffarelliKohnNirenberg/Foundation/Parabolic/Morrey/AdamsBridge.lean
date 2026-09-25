/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsEndpoints

/-!
# Adams Bridge

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The cylinder integral is bounded by the Morrey seminorm at every scale. -/
theorem cylinderPowerIntegral_le_morreyNorm_pow
    {p q : ℝ} (hp : 0 < p) {f : ParabolicPoint → ℝ}
    (_ : AEMeasurable f volume) {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    cylinderPowerIntegral p f z r ≤
      (ENNReal.ofReal r) ^ (5 * (1 - p / q)) * morreyNorm p q f ^ p := by
  let A : ℝ≥0∞ := ENNReal.ofReal r
  let I : ℝ≥0∞ := cylinderPowerIntegral p f z r
  let α : ℝ := 5 * (1 - p / q)
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := by
    dsimp [A]
    exact ENNReal.ofReal_ne_top
  have hcell : morreyCell p q f z r ≤ morreyNorm p q f := by
    unfold morreyNorm
    exact le_iSup_of_le z (le_iSup_of_le ⟨r, hr⟩ le_rfl)
  have hpow' := ENNReal.rpow_le_rpow hcell hp.le
  rw [morreyCell_eq] at hpow'
  have hpow_raw : ((A ^ (-α / p) * (I ^ (1 / p))) ^ p) ≤
      morreyNorm p q f ^ p := by
    have hexp : -(5 * (1 - p / q) / p) = -(5 * (1 - p / q)) / p := by
      ring_nf
    rw [hexp] at hpow'
    simpa [A, I, α] using hpow'
  have hpow_eq : (A ^ (-α / p) * (I ^ (1 / p))) ^ p =
      A ^ (-α) * I := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul]
    have hα : (-α / p) * p = -α := by
      field_simp [hp.ne']
    have hpone : (1 / p) * p = 1 := by
      field_simp [hp.ne']
    rw [hα, hpone, ENNReal.rpow_one]
  have hpow : A ^ (-α) * I ≤ morreyNorm p q f ^ p := by
    rw [← hpow_eq]
    exact hpow_raw
  have hscale : A ^ α * (A ^ (-α) * I) = I := by
    calc
      A ^ α * (A ^ (-α) * I) = (A ^ α * A ^ (-α)) * I := by ac_rfl
      _ = A ^ (α + (-α)) * I := by
        rw [← ENNReal.rpow_add _ _ hA0 hAtop]
      _ = I := by rw [add_neg_cancel, ENNReal.rpow_zero, one_mul]
  have hmul := mul_le_mul_left hpow (A ^ α)
  have hmul' : A ^ α * (A ^ (-α) * I) ≤
      A ^ α * morreyNorm p q f ^ p := by
    simpa [mul_comm] using hmul
  rw [hscale] at hmul'
  calc
    I ≤ A ^ α * morreyNorm p q f ^ p := hmul'
    _ = (ENNReal.ofReal r) ^ (5 * (1 - p / q)) * morreyNorm p q f ^ p := by
      rfl

/-- A metric ball has the volume forced by the contained parabolic cylinder. -/
theorem volume_metricBall_lower {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder 0 0 1) ≤
      volume (Metric.ball z r) := by
  let T : ℝ := z.2 + r ^ 2 / 2
  have hball := parabolicCylinder_subset_metricBall
    (x := z.1) (t := T) (r := r) hr
  have hcenter : (z.1, T - r ^ 2 / 2) = z := by
    dsimp [T]
    congr 1
    ring_nf
  rw [hcenter] at hball
  have hscale := volume_parabolicCylinder_radius_scale
    (x := z.1) (t := T) (r := 1) (a := r) hr
  have hunit : volume (parabolicCylinder z.1 T 1) =
      volume (parabolicCylinder 0 0 1) := by
    rw [volume_parabolicCylinder_zero, volume_parabolicCylinder_zero]
  calc
    ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder 0 0 1) =
        ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder z.1 T 1) := by
      rw [hunit]
    _ = volume (parabolicCylinder z.1 T (r * 1)) := hscale.symm
    _ = volume (parabolicCylinder z.1 T r) := by rw [mul_one]
    _ ≤ volume (Metric.ball z r) := measure_mono hball

/-- Metric-ball averages are controlled by the cylinder Morrey seminorm. -/
theorem metricBall_average_le_morreyNorm
    {q : ℝ} (hq : 1 ≤ q) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in Metric.ball z r, ENNReal.ofReal |f w|) /
        volume (Metric.ball z r) ≤
      ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
        volume (parabolicCylinder 0 0 1)) *
        ENNReal.ofReal r ^ (-(5 / q)) * morreyNorm 1 q f := by
  let V : ℝ≥0∞ := volume (parabolicCylinder 0 0 1)
  let α : ℝ := 5 * (1 - 1 / q)
  let A : ℝ≥0∞ := ENNReal.ofReal r
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hV0 : V ≠ 0 := by
    dsimp [V]
    exact (Integration.volume_parabolicCylinder_pos (by norm_num)).ne'
  have hVtop : V ≠ ∞ := by
    dsimp [V]
    exact Integration.volume_parabolicCylinder_lt_top.ne
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  have hAtop : A ≠ ∞ := by
    dsimp [A]
    exact ENNReal.ofReal_ne_top
  have hnum : (∫⁻ w in Metric.ball z r, ENNReal.ofReal |f w|) ≤
      (ENNReal.ofReal (2 * r)) ^ α * morreyNorm 1 q f := by
    let T : ℝ := z.2 + (2 * r) ^ 2 / 2
    have hball := metricBall_subset_parabolicCylinder
      (x := z.1) (t := T) (r := 2 * r) (by positivity)
    have hcenter : (z.1, T - (2 * r) ^ 2 / 2) = z := by
      dsimp [T]
      congr 1
      ring_nf
    have hradius : (2 * r) / 2 = r := by ring_nf
    rw [hcenter, hradius] at hball
    exact (lintegral_mono_set hball).trans
      (cylinderAbsIntegral_le_morreyNorm hq hf
        (z.1, T) (by positivity))
  have hvol := volume_metricBall_lower (z := z) hr
  have hvol' : A ^ (5 : ℝ) * V ≤ volume (Metric.ball z r) := by
    simpa [A, V, ENNReal.ofReal_pow (by positivity : 0 ≤ r) 5,
      ENNReal.rpow_natCast] using hvol
  apply (ENNReal.div_le_iff (volume_parabolicBall_pos hr).ne'
    (volume_parabolicBall_lt_top hr).ne).2
  calc
    (∫⁻ w in Metric.ball z r, ENNReal.ofReal |f w|) ≤
        (ENNReal.ofReal (2 * r)) ^ α * morreyNorm 1 q f := hnum
    _ = (((ENNReal.ofReal (2 : ℝ)) ^ α / V) *
          A ^ (-(5 / q)) * morreyNorm 1 q f) * (A ^ (5 : ℝ) * V) := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
        show ENNReal.ofReal r = A by rfl,
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hAtop]
      have hpow : -(5 / q) + 5 = α := by
        dsimp [α]
        field_simp [hq0.ne']
        ring_nf
      have hAcombine : A ^ (-(5 / q)) * A ^ (5 : ℝ) = A ^ α := by
        calc
          A ^ (-(5 / q)) * A ^ (5 : ℝ) = A ^ (-(5 / q) + 5) :=
            (ENNReal.rpow_add _ _ hA0 hAtop).symm
          _ = A ^ α := by rw [hpow]
      symm
      calc
        (((ENNReal.ofReal (2 : ℝ)) ^ α / V) *
            A ^ (-(5 / q)) * morreyNorm 1 q f) * (A ^ (5 : ℝ) * V) =
            ENNReal.ofReal (2 : ℝ) ^ α * morreyNorm 1 q f *
              (A ^ (-(5 / q)) * A ^ (5 : ℝ)) * (V⁻¹ * V) := by
                rw [show ENNReal.ofReal (2 : ℝ) ^ α / V =
                  ENNReal.ofReal (2 : ℝ) ^ α * V⁻¹ by
                    rw [div_eq_mul_inv]]
                ac_rfl
        _ = ENNReal.ofReal (2 : ℝ) ^ α * morreyNorm 1 q f * A ^ α := by
              rw [hAcombine, ENNReal.inv_mul_cancel hV0 hVtop, mul_one]
        _ = ENNReal.ofReal (2 : ℝ) ^ α * A ^ α * morreyNorm 1 q f := by
              ac_rfl
    _ ≤ (((ENNReal.ofReal (2 : ℝ)) ^ α / V) *
          A ^ (-(5 / q)) * morreyNorm 1 q f) * volume (Metric.ball z r) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_left hvol' (((ENNReal.ofReal (2 : ℝ)) ^ α / V) *
          A ^ (-(5 / q)) * morreyNorm 1 q f))

/-- The same metric-ball estimate with a higher integrability exponent. -/
theorem metricBall_average_le_morreyNorm_of_lower_p
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) {f : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    (∫⁻ w in Metric.ball z r, ENNReal.ofReal |f w|) /
        volume (Metric.ball z r) ≤
      ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
        volume (parabolicCylinder 0 0 1)) *
        ENNReal.ofReal r ^ (-(5 / q)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
            morreyNorm p q f := by
  have hlow := metricBall_average_le_morreyNorm
    (q := q) (z := z) (r := r) (hp.trans hpq) hf hr
  have hnorm := morreyNorm_lower_p (p' := 1) (p := p) (q := q)
    (by norm_num) hp hpq hf
  calc
    _ ≤ ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
        volume (parabolicCylinder 0 0 1)) *
        ENNReal.ofReal r ^ (-(5 / q)) * morreyNorm 1 q f := hlow
    _ ≤ ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
        volume (parabolicCylinder 0 0 1)) *
        ENNReal.ofReal r ^ (-(5 / q)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
            morreyNorm p q f := by
      have hnorm' : morreyNorm 1 q f ≤
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
            morreyNorm p q f := by
        simpa using hnorm
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_left hnorm'
          (((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
            volume (parabolicCylinder 0 0 1)) *
            ENNReal.ofReal r ^ (-(5 / q))))

/-- The maximal function is subadditive on nonnegative measurable data. -/
theorem parabolicMaximalFunction_add_le'
    {F G : ParabolicPoint → ℝ≥0∞} (hF : Measurable F) (_ : Measurable G)
    (z : ParabolicPoint) :
    parabolicMaximalFunction (F + G) z ≤
      parabolicMaximalFunction F z + parabolicMaximalFunction G z := by
  rw [parabolicMaximalFunction, parabolicMaximalFunction]
  refine iSup_le fun c ↦ iSup_le fun r ↦ ?_
  by_cases hz : z ∈ Metric.ball c r
  · simp only [indicator_of_mem hz]
    calc
      ⨍⁻ y in Metric.ball c r, (F + G) y ∂volume ≤
          ⨍⁻ y in Metric.ball c r, F y ∂volume +
            ⨍⁻ y in Metric.ball c r, G y ∂volume := by
        simp only [Pi.add_apply]
        rw [setLAverage_eq, setLAverage_eq, setLAverage_eq, lintegral_add_left
          (μ := volume.restrict (Metric.ball c r)) hF, ENNReal.add_div]
      _ ≤ parabolicMaximalFunction F z + parabolicMaximalFunction G z := by
        gcongr
        · calc
            ⨍⁻ y in Metric.ball c r, F y ∂volume =
                (Metric.ball c r).indicator
                  (fun _ ↦ ⨍⁻ y in Metric.ball c r, F y ∂volume) z :=
              (indicator_of_mem hz (fun _ ↦
                ⨍⁻ y in Metric.ball c r, F y ∂volume)).symm
            _ ≤ parabolicMaximalFunction F z := by
              exact le_iSup₂_of_le c r le_rfl
        · calc
            ⨍⁻ y in Metric.ball c r, G y ∂volume =
                (Metric.ball c r).indicator
                  (fun _ ↦ ⨍⁻ y in Metric.ball c r, G y ∂volume) z :=
              (indicator_of_mem hz (fun _ ↦
                ⨍⁻ y in Metric.ball c r, G y ∂volume)).symm
            _ ≤ parabolicMaximalFunction G z := by
              exact le_iSup₂_of_le c r le_rfl
  · change (Metric.ball c r).indicator _ z ≤ _
    rw [indicator_of_notMem hz]
    exact bot_le

/-- A maximal-function tail outside a doubled ball is bounded by a Morrey norm. -/
theorem parabolicMaximalFunction_compl_ball_le
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) {f : ParabolicPoint → ℝ}
    (hf : Measurable f) {c z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ Metric.ball c r) :
    parabolicMaximalFunction
        ((Metric.ball c (4 * r))ᶜ.indicator (fun w ↦ ENNReal.ofReal |f w|)) z ≤
      ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
        volume (parabolicCylinder 0 0 1)) *
        ENNReal.ofReal r ^ (-(5 / q)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
            morreyNorm p q f := by
  let F : ParabolicPoint → ℝ≥0∞ := fun w ↦ ENNReal.ofReal |f w|
  let U : Set ParabolicPoint := Metric.ball c (4 * r)
  let B : ℝ≥0∞ := ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
        volume (parabolicCylinder 0 0 1)) *
        ENNReal.ofReal r ^ (-(5 / q)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
            morreyNorm p q f
  have hq0 : 0 < q := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hp) hpq
  have hB : ∀ {d : ParabolicPoint} {s : ℝ}, 0 < s →
      (⨍⁻ w in Metric.ball d s, F w ∂volume) ≤
        ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
          volume (parabolicCylinder 0 0 1)) *
          ENNReal.ofReal s ^ (-(5 / q)) *
            (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
              morreyNorm p q f := by
    intro d s hs
    rw [setLAverage_eq]
    simpa [F, B] using
      (metricBall_average_le_morreyNorm_of_lower_p hp hpq hf.aemeasurable
        (z := d) (r := s) hs)
  rw [parabolicMaximalFunction]
  refine iSup_le fun d ↦ iSup_le fun s ↦ ?_
  by_cases hzd : z ∈ Metric.ball d s
  · simp only [indicator_of_mem hzd]
    have hs : 0 < s := lt_of_le_of_lt dist_nonneg (by
      simpa [mem_ball] using hzd)
    by_cases hsub : Metric.ball d s ⊆ U
    · have hzero : ∀ᵐ w ∂volume.restrict (Metric.ball d s),
          Uᶜ.indicator F w = 0 := by
        filter_upwards [self_mem_ae_restrict
          (Metric.isOpen_ball.measurableSet : MeasurableSet (Metric.ball d s))]
          with w hw
        simp [hsub hw]
      rw [setLAverage_eq]
      have hzero' :
          (∫⁻ w in Metric.ball d s, Uᶜ.indicator F w) = 0 :=
        lintegral_eq_zero_of_ae_eq_zero hzero
      rw [hzero']
      simp
    · obtain ⟨w, hwd, hwU⟩ := Set.not_subset.mp hsub
      have hinner : 4 * r ≤ dist w c := by
        apply le_of_not_gt
        intro hlt
        apply hwU
        exact hlt
      have htriangle : dist w c ≤ dist w d + (dist d z + dist z c) := by
        exact (dist_triangle w d c).trans
          (add_le_add (le_refl _) (dist_triangle d z c))
      have hlt : dist w c < s + (s + r) := by
        calc
          dist w c ≤ dist w d + (dist d z + dist z c) := htriangle
          _ < s + (s + r) := by
            gcongr
            · simpa [mem_ball] using hwd
            · simpa [mem_ball, dist_comm] using hzd
            · simpa [mem_ball] using hz
      have hsr : r < s := by
        by_contra hnot
        have hsr' : s ≤ r := le_of_not_gt hnot
        linarith only [hinner, hlt, hr, hsr']
      rw [setLAverage_eq]
      calc
        (∫⁻ w in Metric.ball d s, Uᶜ.indicator F w) /
            volume (Metric.ball d s) ≤
          (∫⁻ w in Metric.ball d s, F w) /
              volume (Metric.ball d s) := by
          gcongr
          by_cases hy : w ∈ Uᶜ
          · simp [hy]
          · simp [hy]
        _ ≤ B := by
          have hBs :
              (∫⁻ w in Metric.ball d s, F w) / volume (Metric.ball d s) ≤
                ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
                  volume (parabolicCylinder 0 0 1)) *
                  ENNReal.ofReal s ^ (-(5 / q)) *
                    (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
                      morreyNorm p q f := by
            simpa only [setLAverage_eq] using
              (hB (d := d) (s := s) hs)
          exact hBs.trans (by
            have hbase : ENNReal.ofReal r ^ (5 / q) ≤
                ENNReal.ofReal s ^ (5 / q) := by
              exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hsr.le)
                (by positivity)
            have hinv : ENNReal.ofReal s ^ (-(5 / q)) ≤
                ENNReal.ofReal r ^ (-(5 / q)) := by
              rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ENNReal.inv_le_inv]
              exact hbase
            change
              ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
                  volume (parabolicCylinder 0 0 1)) *
                ENNReal.ofReal s ^ (-(5 / q)) *
                  (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
                    morreyNorm p q f ≤
              ((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / q)) /
                  volume (parabolicCylinder 0 0 1)) *
                ENNReal.ofReal r ^ (-(5 / q)) *
                  (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / p) *
                    morreyNorm p q f
            gcongr)
  · change (Metric.ball d s).indicator _ z ≤ _
    rw [indicator_of_notMem hzd]
    exact bot_le

end CKN.Foundation.Parabolic.Morrey
