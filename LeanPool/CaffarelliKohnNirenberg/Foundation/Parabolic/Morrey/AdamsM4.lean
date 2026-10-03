/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge

/-!
# Adams M4

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology


noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- A concrete constant for the localized maximal-function estimate. -/
@[expose]
def parabolicAdamsMaximalConstant (P τ : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (P - 1) *
    (parabolicMaximalStrongConstant P *
        ENNReal.ofReal (8 : ℝ) ^ (5 * (1 - P / τ)) +
      volume (parabolicCylinder 0 0 1) *
        (((ENNReal.ofReal (2 : ℝ)) ^ (5 * (1 - 1 / τ)) /
          volume (parabolicCylinder 0 0 1)) *
          (volume (parabolicCylinder 0 0 1)) ^ (1 - 1 / P)) ^ P)

/-- A concrete constant in the parabolic Adams inequality. -/
@[expose]
def parabolicAdamsPotentialConstant (β P τ : ℝ) : ℝ≥0∞ :=
  let lam : ℝ := 1 - β * τ / 5
  let theta : ℝ := β * τ / 5
  let s : ℝ := P / lam
  let D : ℝ≥0∞ := volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)
  (((parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) *
      D ^ theta) ^ s * parabolicAdamsMaximalConstant P τ) ^ (1 / s)

private theorem test_ofReal_toReal_rpow_le
    {p : ℝ} (hp : 0 ≤ p) (G : ParabolicPoint → ℝ≥0∞) (w : ParabolicPoint) :
    ENNReal.ofReal |(G w).toReal| ^ p ≤ G w ^ p := by
  have hnonneg : 0 ≤ (G w).toReal := ENNReal.toReal_nonneg
  by_cases htop : G w = ∞
  · rcases hp.eq_or_lt with rfl | hp
    · simp [htop]
    · rw [htop, ENNReal.toReal_top, abs_zero, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hp, ENNReal.top_rpow_of_pos hp]
      exact bot_le
  · rw [abs_of_nonneg hnonneg, ENNReal.ofReal_toReal htop]

/-- The real-valued Morrey cell is controlled by the corresponding ENNReal integral. -/
theorem morreyCell_toReal_le_lintegral_rpow
    {p q : ℝ} (hp : 0 ≤ p) {G : ParabolicPoint → ℝ≥0∞}
    {z : ParabolicPoint} {r : ℝ} :
    morreyCell p q (fun w ↦ (G w).toReal) z r ≤
      (ENNReal.ofReal r) ^ (-(5 * (1 - p / q) / p)) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r, G w ^ p) ^ (1 / p) := by
  unfold morreyCell cylinderPowerIntegral
  apply mul_le_mul_right
  apply ENNReal.rpow_le_rpow
  · apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (by
      rw [parabolicCylinder]
      exact (vec3Ball_measurable z.1 r).prod measurableSet_Ioc)] with w hw
    exact test_ofReal_toReal_rpow_le hp G w
  · exact one_div_nonneg.mpr hp

private theorem test_volume_parabolicCylinder_eq_unit
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    volume (parabolicCylinder z.1 z.2 r) =
      ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder 0 0 1) := by
  have hs := volume_parabolicCylinder_radius_scale
    (x := z.1) (t := z.2) (r := 1) (a := r) hr
  have ht := Integration.volume_parabolicCylinder_translate z.1 (0 : Vec3) z.2 0 1
  calc
    volume (parabolicCylinder z.1 z.2 r) =
        ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder z.1 z.2 1) := by
      simpa using hs
    _ = ENNReal.ofReal (r ^ 5) * volume (parabolicCylinder 0 0 1) := by
      rw [show volume (parabolicCylinder z.1 z.2 1) =
          volume (parabolicCylinder 0 0 1) by simpa using ht]

private theorem test_cylinder_integral_le
    {P τ : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) {f : ParabolicPoint → ℝ}
    (hf : Measurable f) (hNtop : morreyNorm P τ f ≠ ∞)
    {z₀ : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    let c : ParabolicPoint := (z₀.1, z₀.2 - r ^ 2 / 2)
    let U : Set ParabolicPoint := Metric.ball c (4 * r)
    ∫⁻ w in U, (ENNReal.ofReal |f w|) ^ P ∂volume ≤
      (ENNReal.ofReal (8 * r)) ^ (5 * (1 - P / τ)) * morreyNorm P τ f ^ P := by
  dsimp
  let c : ParabolicPoint := (z₀.1, z₀.2 - r ^ 2 / 2)
  let U : Set ParabolicPoint := Metric.ball c (4 * r)
  have hUsubset : U ⊆ parabolicCylinder c.1
      (c.2 + (8 * r) ^ 2 / 2) (8 * r) := by
    have hball := metricBall_subset_parabolicCylinder
      (x := c.1) (t := c.2 + (8 * r) ^ 2 / 2) (r := 8 * r) (by positivity)
    have hcenter : (c.1, c.2 + (8 * r) ^ 2 / 2 - (8 * r) ^ 2 / 2) = c := by
      dsimp [c]
      congr 1
      ring_nf
    rw [hcenter] at hball
    have hradius : (8 * r) / 2 = 4 * r := by ring_nf
    rw [hradius] at hball
    simpa [U] using hball
  have hUint :
      (∫⁻ w in U, (ENNReal.ofReal |f w|) ^ P) ≤
        cylinderPowerIntegral P f (c.1, c.2 + (8 * r) ^ 2 / 2) (8 * r) := by
    simpa [cylinderPowerIntegral] using
      (lintegral_mono_set (μ := volume) (s := U)
        (t := parabolicCylinder c.1 (c.2 + (8 * r) ^ 2 / 2) (8 * r))
        (f := fun w ↦ ENNReal.ofReal |f w| ^ P) hUsubset)
  have hcy := cylinderPowerIntegral_le_morreyNorm_pow
    (p := P) (q := τ) (hp := lt_trans zero_lt_one hP) hf.aemeasurable
    (z := (c.1, c.2 + (8 * r) ^ 2 / 2)) (r := 8 * r) (by positivity)
  have hP0 : 0 ≤ 5 * (1 - P / τ) := by
    have hτ0 : 0 < τ := lt_of_lt_of_le (lt_trans zero_lt_one hP) hPτ
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr ((div_le_one hτ0).2 hPτ))
  have hRtop : ENNReal.ofReal (8 * r) ^ (5 * (1 - P / τ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hP0 ENNReal.ofReal_ne_top
  have hNpowtop : morreyNorm P τ f ^ P ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (lt_trans zero_lt_one hP).le hNtop
  exact hUint.trans hcy

private lemma maximal_morrey_hfarint_1 :
    ∀ {P τ : ℝ},
      1 < P →
        P ≤ τ →
          ∀ {f : ParabolicPoint → ℝ},
            Morrey.morreyNorm P τ f ≠ ∞ →
              ∀ {z₀ : ParabolicPoint} {r : ℝ},
                0 < r →
                  let F : ParabolicPoint → ℝ≥0∞ := fun w => ENNReal.ofReal |f w|;
                  let c : ParabolicPoint := (z₀.1, z₀.2 - r ^ 2 / 2);
                  let U : Set ParabolicPoint := Metric.ball c (4 * r);
                  let F₂ : ParabolicPoint → ℝ≥0∞ := Uᶜ.indicator F;
                  let N : ℝ≥0∞ := Morrey.morreyNorm P τ f;
                  let V : ℝ≥0∞ := volume (parabolicCylinder 0 0 1);
                  let e : ℝ := 5 * (1 - P / τ);
                  let K : ℝ≥0∞ := ENNReal.ofReal 2 ^ (5 * (1 - 1 / τ)) / V * V ^ (1 - 1 / P);
                  0 < P →
                    0 < τ →
                      MeasurableSet (parabolicCylinder z₀.1 z₀.2 r) →
                        (∀ w ∈ parabolicCylinder z₀.1 z₀.2 r,
                            parabolicMaximalFunction F₂ w ≤
                              K * ENNReal.ofReal r ^ (-(5 / τ)) * N) →
                          ∫⁻ (w : ParabolicPoint) in parabolicCylinder z₀.1 z₀.2 r,
                              parabolicMaximalFunction F₂ w ^ P ≤
                            V * K ^ P * ENNReal.ofReal r ^ e * N ^ P
    := by
  intro P τ hP hPτ f hNtop z₀ r hr F c U F₂ N V e K hP0 hτ0 hQmeas hfar
  let B : ℝ≥0∞ := K * ENNReal.ofReal r ^ (-(5 / τ)) * N
  have hB : ∀ᵐ w ∂volume.restrict (parabolicCylinder z₀.1 z₀.2 r),
      parabolicMaximalFunction F₂ w ^ P ≤ B ^ P := by
    filter_upwards [ae_restrict_mem
      hQmeas] with w hw
    exact ENNReal.rpow_le_rpow (hfar w hw) (by positivity)
  calc
    _ ≤ ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r, B ^ P :=
      lintegral_mono_ae hB
    _ = B ^ P * volume (parabolicCylinder z₀.1 z₀.2 r) := by
      rw [setLIntegral_const]
    _ = V * K ^ P * ENNReal.ofReal r ^ e * N ^ P := by
      have hV0 : V ≠ 0 := by
        dsimp [V]
        exact (Integration.volume_parabolicCylinder_pos (by norm_num)).ne'
      have hVtop : V ≠ ∞ := by
        dsimp [V]
        exact Integration.volume_parabolicCylinder_lt_top.ne
      have hKtop : K ≠ ∞ := by
        dsimp [K]
        have hPpow : 0 ≤ 1 - 1 / P := by
          exact sub_nonneg.mpr ((div_le_one hP0).2 hP.le)
        have hτpow : 0 ≤ 5 * (1 - 1 / τ) := by
          exact mul_nonneg (by norm_num)
            (sub_nonneg.mpr ((div_le_one hτ0).2 (hP.le.trans hPτ)))
        apply ENNReal.mul_ne_top
        · exact ENNReal.div_ne_top
            (ENNReal.rpow_ne_top_of_nonneg hτpow ENNReal.ofReal_ne_top)
            hV0
        · exact ENNReal.rpow_ne_top_of_nonneg hPpow hVtop
      have hAtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
      have hA0 : ENNReal.ofReal r ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hr).ne'
      have hAnegTop : ENNReal.ofReal r ^ (-(5 / τ)) ≠ ∞ :=
        ENNReal.rpow_ne_top_of_ne_zero hA0 hAtop
      have hBpow : B ^ P = K ^ P *
          (ENNReal.ofReal r ^ (-(5 / τ))) ^ P * N ^ P := by
        dsimp [B, N]
        rw [ENNReal.mul_rpow_of_ne_top
          (ENNReal.mul_ne_top hKtop
            hAnegTop) hNtop]
        rw [ENNReal.mul_rpow_of_ne_top hKtop hAnegTop]
      have hQvol := test_volume_parabolicCylinder_eq_unit (z := z₀) hr
      have hQvol' : volume (parabolicCylinder z₀.1 z₀.2 r) =
          V * ENNReal.ofReal r ^ (5 : ℝ) := by
        rw [hQvol, ENNReal.ofReal_pow hr.le, ← ENNReal.rpow_natCast]
        ac_rfl
      rw [hBpow, hQvol']
      rw [← ENNReal.rpow_mul]
      have hexp : (-(5 / τ)) * P + 5 = e := by
        dsimp [e]
        field_simp [hτ0.ne']
        ring_nf
      calc
        K ^ P * ENNReal.ofReal r ^ (-(5 / τ) * P) * N ^ P *
            (V * ENNReal.ofReal r ^ (5 : ℝ)) =
            V * K ^ P * N ^ P *
              (ENNReal.ofReal r ^ (-(5 / τ) * P) *
                ENNReal.ofReal r ^ (5 : ℝ)) := by ac_rfl
        _ = V * K ^ P * N ^ P * ENNReal.ofReal r ^ e := by
          rw [← ENNReal.rpow_add _ _ hA0 hAtop, hexp]
        _ = V * K ^ P * ENNReal.ofReal r ^ e * N ^ P := by ac_rfl

private theorem test_setLIntegral_rpow_parabolicMaximalFunction_morrey_le
    {P τ : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) {f : ParabolicPoint → ℝ}
    (hf : Measurable f) (hNtop : morreyNorm P τ f ≠ ∞)
    {z₀ : ParabolicPoint} {r : ℝ} (hr : 0 < r) :
    ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
        parabolicMaximalFunction (fun y ↦ ENNReal.ofReal |f y|) w ^ P ≤
      parabolicAdamsMaximalConstant P τ *
        ENNReal.ofReal r ^ (5 * (1 - P / τ)) * morreyNorm P τ f ^ P := by
  let F : ParabolicPoint → ℝ≥0∞ := fun w ↦ ENNReal.ofReal |f w|
  let c : ParabolicPoint := (z₀.1, z₀.2 - r ^ 2 / 2)
  let U : Set ParabolicPoint := Metric.ball c (4 * r)
  let F₁ : ParabolicPoint → ℝ≥0∞ := U.indicator F
  let F₂ : ParabolicPoint → ℝ≥0∞ := Uᶜ.indicator F
  let N : ℝ≥0∞ := morreyNorm P τ f
  let V : ℝ≥0∞ := volume (parabolicCylinder 0 0 1)
  let e : ℝ := 5 * (1 - P / τ)
  let K : ℝ≥0∞ := (ENNReal.ofReal (2 : ℝ) ^ (5 * (1 - 1 / τ)) / V) *
    V ^ (1 - 1 / P)
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hτ0 : 0 < τ := lt_of_lt_of_le hP0 hPτ
  have he : 0 ≤ e := by
    dsimp [e]
    exact mul_nonneg (by norm_num)
      (sub_nonneg.mpr ((div_le_one hτ0).2 hPτ))
  have hF : Measurable F := by
    exact hf.norm.ennreal_ofReal
  have hUmeas : MeasurableSet U := Metric.isOpen_ball.measurableSet
  have hQsub : parabolicCylinder z₀.1 z₀.2 r ⊆ Metric.ball c r := by
    simpa [c] using (parabolicCylinder_subset_metricBall
      (x := z₀.1) (t := z₀.2) (r := r) hr)
  have hQsubU : parabolicCylinder z₀.1 z₀.2 r ⊆ U := by
    intro w hw
    have hwr := hQsub hw
    apply mem_ball'.2
    exact lt_of_lt_of_le (mem_ball'.1 hwr) (by linarith only [hr])
  have hQmeas : MeasurableSet (parabolicCylinder z₀.1 z₀.2 r) := by
    rw [parabolicCylinder]
    exact (vec3Ball_measurable z₀.1 r).prod measurableSet_Ioc
  have hUbound : ∫⁻ w in U, F w ^ P ∂volume ≤
      (ENNReal.ofReal (8 * r)) ^ e * N ^ P := by
    simpa [F, N, e] using
      (test_cylinder_integral_le hP hPτ hf hNtop (z₀ := z₀) (r := r) hr)
  have hfinite :
      ENNReal.ofReal (8 * r) ^ e * N ^ P < ∞ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_nonneg he ENNReal.ofReal_ne_top))
      (lt_top_iff_ne_top.mpr
        (ENNReal.rpow_ne_top_of_nonneg hP0.le hNtop))
  have hUfp : ∫⁻ w in U, F w ^ P ∂volume < ∞ :=
    lt_of_le_of_lt hUbound hfinite
  have hstrong := setLIntegral_rpow_parabolicMaximalFunction_indicator_le
    U hUmeas Metric.isOpen_ball Metric.isBounded_ball hF hP
      hUfp
  have hF₁ : Measurable F₁ := hF.indicator hUmeas
  have hF₂ : Measurable F₂ := hF.indicator hUmeas.compl
  have hsplit : F₁ + F₂ = F := by
    funext w
    by_cases hw : w ∈ U
    · simp [F₁, F₂, hw]
    · simp [F₁, F₂, hw]
  have hmax : ∀ w, parabolicMaximalFunction F w ≤
      parabolicMaximalFunction F₁ w + parabolicMaximalFunction F₂ w := by
    intro w
    rw [← hsplit]
    exact parabolicMaximalFunction_add_le' hF₁ hF₂ w
  have hfar : ∀ w ∈ parabolicCylinder z₀.1 z₀.2 r,
      parabolicMaximalFunction F₂ w ≤ K *
        ENNReal.ofReal r ^ (-(5 / τ)) * N := by
    intro w hw
    have hwball : w ∈ Metric.ball c r := hQsub hw
    simpa [F₂, U, K, N, V, mul_assoc, mul_left_comm, mul_comm] using
      (parabolicMaximalFunction_compl_ball_le
        (p := P) (q := τ) (c := c) (z := w) (r := r)
        hP.le hPτ hf hr hwball)
  have hpow : ∀ w ∈ parabolicCylinder z₀.1 z₀.2 r,
      parabolicMaximalFunction F w ^ P ≤
        (2 : ℝ≥0∞) ^ (P - 1) *
          (parabolicMaximalFunction F₁ w ^ P +
            parabolicMaximalFunction F₂ w ^ P) := by
    intro w hw
    exact (ENNReal.rpow_le_rpow (hmax w) (by positivity)).trans
      (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hP.le)
  have hpoint :
      (∫⁻ w in parabolicCylinder z₀.1 z₀.2 r, parabolicMaximalFunction F w ^ P) ≤
        (2 : ℝ≥0∞) ^ (P - 1) *
          ((∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
              parabolicMaximalFunction F₁ w ^ P) +
            ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
              parabolicMaximalFunction F₂ w ^ P) := by
    calc
      _ ≤ ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
          (2 : ℝ≥0∞) ^ (P - 1) *
            (parabolicMaximalFunction F₁ w ^ P +
              parabolicMaximalFunction F₂ w ^ P) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (by
          rw [parabolicCylinder]
          exact (vec3Ball_measurable z₀.1 r).prod measurableSet_Ioc)]
          with w hw
        exact hpow w hw
      _ = _ := by
        have hMF₁ : Measurable (fun w ↦ parabolicMaximalFunction F₁ w ^ P) :=
          ENNReal.continuous_rpow_const.measurable.comp
            (measurable_parabolicMaximalFunction F₁)
        have htwoTop : (2 : ℝ≥0∞) ^ (P - 1) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hP.le)
            ENNReal.ofNat_ne_top
        rw [lintegral_const_mul' _ _ htwoTop, lintegral_add_left
          (μ := volume.restrict (parabolicCylinder z₀.1 z₀.2 r))
          hMF₁]
  have hlocal :
      (∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
          parabolicMaximalFunction F₁ w ^ P) ≤
        parabolicMaximalStrongConstant P *
          (ENNReal.ofReal (8 * r)) ^ e * N ^ P := by
    calc
      _ ≤ ∫⁻ w in U, parabolicMaximalFunction F₁ w ^ P :=
        lintegral_mono_set hQsubU
      _ ≤ parabolicMaximalStrongConstant P *
          ∫⁻ w in U, F w ^ P := hstrong
      _ ≤ parabolicMaximalStrongConstant P *
          ((ENNReal.ofReal (8 * r)) ^ e * N ^ P) := by
        exact mul_le_mul_right hUbound _
      _ = parabolicMaximalStrongConstant P *
          (ENNReal.ofReal (8 * r)) ^ e * N ^ P := by ac_rfl
  have hfarint := @maximal_morrey_hfarint_1 P τ hP hPτ f hNtop z₀ r hr hP0 hτ0 hQmeas hfar
  have h8scale : ENNReal.ofReal (8 * r) ^ e =
      ENNReal.ofReal (8 : ℝ) ^ e * ENNReal.ofReal r ^ e := by
    rw [ENNReal.ofReal_mul (by norm_num),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (P - 1) *
        ((∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
            parabolicMaximalFunction F₁ w ^ P) +
          ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
            parabolicMaximalFunction F₂ w ^ P) := hpoint
    _ ≤ (2 : ℝ≥0∞) ^ (P - 1) *
        (parabolicMaximalStrongConstant P *
            (ENNReal.ofReal (8 * r)) ^ e * N ^ P +
          V * K ^ P * ENNReal.ofReal r ^ e * N ^ P) := by
      gcongr
    _ = parabolicAdamsMaximalConstant P τ *
        ENNReal.ofReal r ^ e * N ^ P := by
      rw [h8scale]
      dsimp [parabolicAdamsMaximalConstant, K, e, V]
      rw [mul_add]
      ring

private lemma parabolicRieszPotential_adams_finite_hIint_1 :
    ∀ {P τ β : ℝ},
      1 < P →
        P ≤ τ →
          ∀ {f : ParabolicPoint → ℝ},
            Measurable f →
              Morrey.morreyNorm P τ f ≠ 0 →
                Morrey.morreyNorm P τ f ≠ ∞ →
                  let theta : ℝ := β * τ / 5;
                  let lam : ℝ := 1 - theta;
                  let s : ℝ := P / lam;
                  let N : ℝ≥0∞ := Morrey.morreyNorm P τ f;
                  let D : ℝ≥0∞ :=
                    HPow.hPow (α := ℝ≥0∞) (volume (parabolicCylinder 0 0 1) : ℝ≥0∞) (1 - 1 / P);
                  let C₀ : ℝ≥0∞ :=
                    (Morrey.parabolicHedbergNearConstant β +
                        Morrey.parabolicTailKernelConstant β τ) *
                      D ^ theta;
                  let M : ParabolicPoint → ℝ≥0∞ :=
                    parabolicMaximalFunction fun w => ENNReal.ofReal |f w|;
                  let I : ParabolicPoint → ℝ≥0∞ := fun w => Morrey.parabolicRieszPotential β f w;
                  theta * s + P = s →
                    C₀ ^ s * N ^ (theta * s) ≠ ∞ →
                      (∀ (w : ParabolicPoint), I w ^ s ≤ C₀ ^ s * M w ^ P * N ^ (theta * s)) →
                        ∀ {z : ParabolicPoint} {r : ℝ},
                          0 < r →
                            ∫⁻ (w : ParabolicPoint) in parabolicCylinder z.1 z.2 r, I w ^ s ≤
                              C₀ ^ s * Morrey.parabolicAdamsMaximalConstant P τ *
                                  ENNReal.ofReal r ^ (5 * (1 - P / τ)) *
                                N ^ s
    := by
  intro P τ β hP hPτ f hf hN0 hNtop theta lam s N D C₀ M I htheta_s hfacTop hpoint z r hr
  have hQmeas : MeasurableSet (parabolicCylinder z.1 z.2 r) := by
    rw [parabolicCylinder]
    exact (vec3Ball_measurable z.1 r).prod measurableSet_Ioc
  have hMlocal := test_setLIntegral_rpow_parabolicMaximalFunction_morrey_le
    hP hPτ hf hNtop (z₀ := z) (r := r) hr
  have hmono :
      (∫⁻ w in parabolicCylinder z.1 z.2 r, I w ^ s) ≤
        ∫⁻ w in parabolicCylinder z.1 z.2 r,
          C₀ ^ s * M w ^ P * N ^ (theta * s) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hQmeas] with w hw
    exact hpoint w
  calc
    _ ≤ ∫⁻ w in parabolicCylinder z.1 z.2 r,
        (C₀ ^ s * N ^ (theta * s)) * M w ^ P := by
      exact hmono.trans_eq (by
        apply congrArg
        funext w
        ac_rfl)
    _ = (C₀ ^ s * N ^ (theta * s)) *
        ∫⁻ w in parabolicCylinder z.1 z.2 r, M w ^ P := by
      rw [lintegral_const_mul' _ _ hfacTop]
    _ ≤ (C₀ ^ s * N ^ (theta * s)) *
        (parabolicAdamsMaximalConstant P τ *
          ENNReal.ofReal r ^ (5 * (1 - P / τ)) * N ^ P) := by
      gcongr
    _ = (C₀ ^ s * parabolicAdamsMaximalConstant P τ) *
        ENNReal.ofReal r ^ (5 * (1 - P / τ)) * N ^ s := by
      have hNcombine : N ^ (theta * s) * N ^ P = N ^ s := by
        rw [← ENNReal.rpow_add _ _ (by simpa [N] using hN0) hNtop,
          htheta_s]
      calc
        C₀ ^ s * N ^ (theta * s) *
            (parabolicAdamsMaximalConstant P τ *
              ENNReal.ofReal r ^ (5 * (1 - P / τ)) * N ^ P) =
            C₀ ^ s * parabolicAdamsMaximalConstant P τ *
              ENNReal.ofReal r ^ (5 * (1 - P / τ)) *
              (N ^ (theta * s) * N ^ P) := by ac_rfl
        _ = C₀ ^ s * parabolicAdamsMaximalConstant P τ *
              ENNReal.ofReal r ^ (5 * (1 - P / τ)) * N ^ s := by
          rw [hNcombine]

private theorem parabolicRieszPotential_adams_finite
    {P τ β : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) (hβ : 0 < β)
    (hβτ : β * τ < 5) {f : ParabolicPoint → ℝ}
    (hf : Measurable f) (hN0 : morreyNorm P τ f ≠ 0)
    (hNtop : morreyNorm P τ f ≠ ∞)
    (hCtop : parabolicHedbergNearConstant β +
      parabolicTailKernelConstant β τ ≠ ∞) :
    morreyNorm (P / (1 - β * τ / 5)) (τ / (1 - β * τ / 5))
        (fun z ↦ (parabolicRieszPotential β f z).toReal) ≤
      parabolicAdamsPotentialConstant β P τ * morreyNorm P τ f := by
  let theta : ℝ := β * τ / 5
  let lam : ℝ := 1 - theta
  let s : ℝ := P / lam
  let N : ℝ≥0∞ := morreyNorm P τ f
  let N₁ : ℝ≥0∞ := morreyNorm 1 τ f
  let D : ℝ≥0∞ := volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)
  let C₀ : ℝ≥0∞ :=
    (parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) * D ^ theta
  let M : ParabolicPoint → ℝ≥0∞ :=
    parabolicMaximalFunction (fun w ↦ ENNReal.ofReal |f w|)
  let I : ParabolicPoint → ℝ≥0∞ :=
    fun w ↦ parabolicRieszPotential β f w
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have hτ1 : 1 < τ := lt_of_lt_of_le hP hPτ
  have hτ0 : 0 < τ := lt_trans zero_lt_one hτ1
  have hβ5 : β < 5 := by
    simpa using (lt_trans (mul_lt_mul_of_pos_left hτ1 hβ) hβτ)
  have htheta : 0 < theta := by
    dsimp [theta]
    positivity
  have hlam : 0 < lam := by
    dsimp [lam, theta]
    exact sub_pos.mpr ((div_lt_one (by norm_num)).2 hβτ)
  have hsl : 1 < s := by
    apply (one_lt_div hlam).2
    have hlam_le_one : lam ≤ 1 := by
      dsimp [lam]
      exact sub_le_self 1 htheta.le
    exact lt_of_le_of_lt hlam_le_one hP
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one hsl.le
  have hst : 0 ≤ 1 / s := one_div_nonneg.mpr hs.le
  have hls : lam * s = P := by
    dsimp [s]
    field_simp [hlam.ne']
  have htheta_s : theta * s + P = s := by
    have hsum : theta + lam = 1 := by
      dsimp [lam]
      ring
    calc
      theta * s + P = theta * s + lam * s := by rw [hls]
      _ = (theta + lam) * s := by ring
      _ = s := by rw [hsum, one_mul]
  have hNlower : N₁ ≤ D * N := by
    simpa [N₁, D, N] using
      (morreyNorm_lower_p (p' := 1) (p := P) (q := τ)
        (by norm_num) hP.le hPτ hf.aemeasurable)
  have hMmajor : IsParabolicMaximalMajorant f M := by
    simpa [M, parabolicMaximalMajorant] using
      isParabolicMaximalMajorant_parabolicMaximalMajorant f
  have hC₀top : C₀ ≠ ∞ := by
    have hVtop : volume (parabolicCylinder 0 0 1) ≠ ∞ :=
      Integration.volume_parabolicCylinder_lt_top.ne
    have hDtop : D ≠ ∞ := by
      dsimp [D]
      exact ENNReal.rpow_ne_top_of_nonneg
        (sub_nonneg.mpr ((div_le_one hP0).2 hP.le)) hVtop
    exact ENNReal.mul_ne_top hCtop
      (ENNReal.rpow_ne_top_of_ne_zero (by
        have hV0 : volume (parabolicCylinder 0 0 1) ≠ 0 :=
          (Integration.volume_parabolicCylinder_pos (by norm_num)).ne'
        exact ENNReal.rpow_pos (by positivity) hVtop |>.ne') hDtop)
  have hNpowtop : N ^ (theta * s) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg
      (mul_nonneg htheta.le hs.le) hNtop
  have hCpowtop : C₀ ^ s ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hs.le hC₀top
  have hfacTop : C₀ ^ s * N ^ (theta * s) ≠ ∞ :=
    ENNReal.mul_ne_top hCpowtop hNpowtop
  have hpoint : ∀ w, I w ^ s ≤ C₀ ^ s * M w ^ P * N ^ (theta * s) := by
    intro w
    have hhed := parabolicRieszPotential_hedberg'
      hβ hβ5 hτ1.le hβτ hf.aemeasurable hMmajor w
    have hN₁pow : N₁ ^ theta ≤ D ^ theta * N ^ theta := by
      calc
        N₁ ^ theta ≤ (D * N) ^ theta :=
          ENNReal.rpow_le_rpow hNlower htheta.le
        _ = D ^ theta * N ^ theta :=
          ENNReal.mul_rpow_of_nonneg _ _ htheta.le
    have hbase : I w ≤ C₀ * M w ^ lam * N ^ theta := by
      have hhed' : I w ≤
          (parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) *
            M w ^ lam * N₁ ^ theta := by
        simpa [I, M, N₁, lam, theta] using hhed
      calc
        I w ≤ (parabolicHedbergNearConstant β +
            parabolicTailKernelConstant β τ) * M w ^ lam * N₁ ^ theta := hhed'
        _ ≤ (parabolicHedbergNearConstant β +
            parabolicTailKernelConstant β τ) * M w ^ lam *
              (D ^ theta * N ^ theta) := by
          gcongr
        _ = C₀ * M w ^ lam * N ^ theta := by
          simp only [C₀]
          ac_rfl
    have hpow := ENNReal.rpow_le_rpow hbase hs.le
    have hpow_eq : (C₀ * M w ^ lam * N ^ theta) ^ s =
        C₀ ^ s * M w ^ P * N ^ (theta * s) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le,
        ENNReal.mul_rpow_of_nonneg _ _ hs.le,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hls]
    exact hpow.trans_eq hpow_eq
  have hIint : ∀ {z : ParabolicPoint} {r : ℝ}, 0 < r →
      (∫⁻ w in parabolicCylinder z.1 z.2 r, I w ^ s) ≤
        (C₀ ^ s * parabolicAdamsMaximalConstant P τ) *
          ENNReal.ofReal r ^ (5 * (1 - P / τ)) * N ^ s := by
    exact @parabolicRieszPotential_adams_finite_hIint_1 P τ β hP hPτ f hf hN0 hNtop htheta_s
      hfacTop hpoint
  unfold morreyNorm
  refine iSup_le fun z ↦ iSup_le fun r ↦ ?_
  have hcell := morreyCell_toReal_le_lintegral_rpow
    (p := s) (q := τ / lam) (by positivity) (G := I)
      (z := z) (r := r.1)
  have hIntegral := hIint (z := z) (r := r.1) r.2
  have hratio : s / (τ / lam) = P / τ := by
    dsimp [s]
    field_simp [hτ0.ne', hlam.ne']
  have hexp : 5 * (1 - s / (τ / lam)) = 5 * (1 - P / τ) := by
    rw [hratio]
  have hcell' : morreyCell s (τ / lam)
      (fun w ↦ (I w).toReal) z r.1 ≤
      (ENNReal.ofReal r.1) ^
          (-(5 * (1 - P / τ) / s)) *
        ((C₀ ^ s * parabolicAdamsMaximalConstant P τ) *
          ENNReal.ofReal r.1 ^ (5 * (1 - P / τ)) * N ^ s) ^ (1 / s) := by
    rw [hexp] at hcell
    exact hcell.trans (by
      simpa [mul_comm] using (mul_le_mul_left
        (ENNReal.rpow_le_rpow hIntegral (one_div_nonneg.mpr hs.le))
        (ENNReal.ofReal r.1 ^ (-(5 * (1 - P / τ) / s)))))
  have hR0 : ENNReal.ofReal r.1 ≠ 0 := (ENNReal.ofReal_pos.mpr r.2).ne'
  have hRtop : ENNReal.ofReal r.1 ≠ ∞ := ENNReal.ofReal_ne_top
  have hroot :
      ((C₀ ^ s * parabolicAdamsMaximalConstant P τ) *
        ENNReal.ofReal r.1 ^ (5 * (1 - P / τ)) * N ^ s) ^ (1 / s) =
        (C₀ ^ s * parabolicAdamsMaximalConstant P τ) ^ (1 / s) *
          ENNReal.ofReal r.1 ^ (5 * (1 - P / τ) / s) * N := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hst,
      ENNReal.mul_rpow_of_nonneg _ _ hst,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    have hsone : s * (1 / s) = 1 := by field_simp [hs.ne']
    rw [hsone, ENNReal.rpow_one]
    congr 2
    field_simp [hs.ne']
  have hcellfinal : morreyCell s (τ / lam)
      (fun w ↦ (I w).toReal) z r.1 ≤
      parabolicAdamsPotentialConstant β P τ * N := by
    have hcancel : ENNReal.ofReal r.1 ^
        (-(5 * (1 - P / τ) / s)) *
        ENNReal.ofReal r.1 ^ (5 * (1 - P / τ) / s) = 1 := by
      rw [← ENNReal.rpow_add _ _ hR0 hRtop]
      simp
    calc
      morreyCell s (τ / lam)
          (fun w ↦ (I w).toReal) z r.1 ≤
          ENNReal.ofReal r.1 ^
            (-(5 * (1 - P / τ) / s)) *
            (C₀ ^ s * parabolicAdamsMaximalConstant P τ *
              ENNReal.ofReal r.1 ^ (5 * (1 - P / τ)) * N ^ s) ^ (1 / s) := hcell'
      _ = ENNReal.ofReal r.1 ^
            (-(5 * (1 - P / τ) / s)) *
            ((C₀ ^ s * parabolicAdamsMaximalConstant P τ) ^ (1 / s) *
              ENNReal.ofReal r.1 ^ (5 * (1 - P / τ) / s) * N) := by
        rw [hroot]
      _ = (C₀ ^ s * parabolicAdamsMaximalConstant P τ) ^ (1 / s) *
          (ENNReal.ofReal r.1 ^
            (-(5 * (1 - P / τ) / s)) *
            ENNReal.ofReal r.1 ^ (5 * (1 - P / τ) / s)) * N := by ac_rfl
      _ = (C₀ ^ s * parabolicAdamsMaximalConstant P τ) ^ (1 / s) * N := by
        rw [hcancel, mul_one]
      _ = parabolicAdamsPotentialConstant β P τ * N := by
        rfl
  exact hcellfinal

private theorem morreyNorm_eq_zero_of_ae_eq_zero
    {p q : ℝ} (hp : 0 < p) {g : ParabolicPoint → ℝ}
    (hzero : g =ᵐ[volume] 0) : morreyNorm p q g = 0 := by
  apply le_antisymm
  · unfold morreyNorm
    refine iSup_le fun z ↦ iSup_le fun r ↦ ?_
    unfold morreyCell cylinderPowerIntegral
    have hintegral : (∫⁻ w in parabolicCylinder z.1 z.2 r.1,
        (ENNReal.ofReal |g w|) ^ p) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      apply (ae_restrict_iff' (by
        rw [parabolicCylinder]
        exact (vec3Ball_measurable z.1 r.1).prod measurableSet_Ioc)).2
      filter_upwards [hzero] with w hw
      intro _
      simp only [hw, Pi.zero_apply, abs_zero, ENNReal.ofReal_zero]
      exact ENNReal.zero_rpow_of_pos hp
    have hpinv : 0 < 1 / p := one_div_pos.mpr hp
    rw [hintegral, ENNReal.zero_rpow_of_pos hpinv, mul_zero]
  · exact bot_le

/-- Adams's Morrey estimate in the range `1 < P ≤ τ` and `0 < βτ < 5`. -/
theorem parabolicRieszPotential_adams
    {P τ β : ℝ} (hP : 1 < P) (hPτ : P ≤ τ) (hβ : 0 < β)
    (hβτ : β * τ < 5) {f : ParabolicPoint → ℝ}
    (hf : Measurable f) :
    morreyNorm (P / (1 - β * τ / 5)) (τ / (1 - β * τ / 5))
        (fun z ↦ (parabolicRieszPotential β f z).toReal) ≤
      parabolicAdamsPotentialConstant β P τ * morreyNorm P τ f := by
  let N : ℝ≥0∞ := morreyNorm P τ f
  let I : ParabolicPoint → ℝ≥0∞ :=
    fun z ↦ parabolicRieszPotential β f z
  change morreyNorm (P / (1 - β * τ / 5)) (τ / (1 - β * τ / 5))
      (fun z ↦ (parabolicRieszPotential β f z).toReal) ≤
    parabolicAdamsPotentialConstant β P τ * N
  have hτ1 : 1 < τ := lt_of_lt_of_le hP hPτ
  have hβ5 : β < 5 := by
    simpa using (lt_trans (mul_lt_mul_of_pos_left hτ1 hβ) hβτ)
  have hP0 : 0 < P := lt_trans zero_lt_one hP
  have htheta : 0 < β * τ / 5 := by positivity
  have hlam : 0 < 1 - β * τ / 5 := by
    exact sub_pos.mpr ((div_lt_one (by norm_num)).2 hβτ)
  have hs : 0 < P / (1 - β * τ / 5) := div_pos hP0 hlam
  have hsinv : 0 < 1 / (P / (1 - β * τ / 5)) := one_div_pos.mpr hs
  have hVpos : 0 < volume (parabolicCylinder 0 0 1) :=
    Integration.volume_parabolicCylinder_pos (by norm_num)
  have hVtop : volume (parabolicCylinder 0 0 1) ≠ ∞ :=
    Integration.volume_parabolicCylinder_lt_top.ne
  have hstrongpos : 0 < parabolicMaximalStrongConstant P := by
    unfold parabolicMaximalStrongConstant
    apply ENNReal.div_pos
    · positivity
    · exact ENNReal.ofReal_ne_top
  have hmaxpos : 0 < parabolicAdamsMaximalConstant P τ := by
    unfold parabolicAdamsMaximalConstant
    positivity
  have hApos : 0 < parabolicHedbergNearConstant β +
      parabolicTailKernelConstant β τ := by
    exact add_pos_of_pos_of_nonneg
      (parabolicHedbergNearConstant_pos (β := β)) bot_le
  have hDpos : 0 < volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P) :=
    ENNReal.rpow_pos hVpos hVtop
  have hDtop : volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg
      (sub_nonneg.mpr ((div_le_one hP0).2 hP.le)) hVtop
  by_cases hN0 : N = 0
  · have hN₁ : morreyNorm 1 τ f = 0 := by
      have hle := morreyNorm_lower_p (p' := 1) (p := P) (q := τ)
        (by norm_num) hP.le hPτ hf.aemeasurable
      have hN₁' : morreyNorm 1 τ f ≤ 0 := by simpa [N, hN0] using hle
      exact bot_unique hN₁'
    have hfzero := ae_eq_zero_of_morreyNorm_eq_zero hτ1.le hf.aemeasurable hN₁
    have hIzero : ∀ z, I z = 0 := by
      intro z
      exact parabolicRieszPotential_eq_zero_of_ae_eq_zero hfzero z
    have hgzero : (fun z ↦ (parabolicRieszPotential β f z).toReal) =ᵐ[volume] 0 := by
      filter_upwards [] with z
      exact congrArg ENNReal.toReal (hIzero z)
    have hnormzero := morreyNorm_eq_zero_of_ae_eq_zero
      (q := τ / (1 - β * τ / 5)) hs hgzero
    rw [hnormzero, hN0, mul_zero]
  by_cases hCtop : parabolicHedbergNearConstant β +
      parabolicTailKernelConstant β τ = ∞
  · have hpot : parabolicAdamsPotentialConstant β P τ = ∞ := by
      have hCzero :
          (parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) *
            (volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)) ^
              (β * τ / 5) = ∞ := by
        rw [hCtop, ENNReal.top_mul]
        exact (ENNReal.rpow_pos hDpos hDtop).ne'
      unfold parabolicAdamsPotentialConstant
      dsimp
      rw [hCzero, ENNReal.top_rpow_of_pos hs,
        ENNReal.top_mul hmaxpos.ne', ENNReal.top_rpow_of_pos hsinv]
    rw [hpot, ENNReal.top_mul (by simpa [N] using hN0)]
    exact le_top
  have hstrongtop : parabolicMaximalStrongConstant P ≠ ∞ := by
    unfold parabolicMaximalStrongConstant
    apply ENNReal.div_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg hP0.le ENNReal.ofNat_ne_top
        · exact ENNReal.ofReal_ne_top
      · exact ENNReal.ofReal_ne_top
    · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hP)).ne'
  have hmax_top : parabolicAdamsMaximalConstant P τ ≠ ∞ := by
    unfold parabolicAdamsMaximalConstant
    apply ENNReal.mul_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.mpr hP.le)
        ENNReal.ofNat_ne_top
    · apply ENNReal.add_ne_top.mpr
      have hτ0 : 0 < τ := lt_trans zero_lt_one hτ1
      have he : 0 ≤ 5 * (1 - P / τ) := by
        exact mul_nonneg (by norm_num)
          (sub_nonneg.mpr ((div_le_one hτ0).2 hPτ))
      constructor
      · exact ENNReal.mul_ne_top hstrongtop
          (ENNReal.rpow_ne_top_of_nonneg he ENNReal.ofReal_ne_top)
      · have hkexp : 0 ≤ 5 * (1 - 1 / τ) := by
          exact mul_nonneg (by norm_num)
            (sub_nonneg.mpr ((div_le_one hτ0).2 hτ1.le))
        have hV0 : volume (parabolicCylinder 0 0 1) ≠ 0 := hVpos.ne'
        have hKtop :
            ((ENNReal.ofReal (2 : ℝ) ^ (5 * (1 - 1 / τ)) /
              volume (parabolicCylinder 0 0 1)) *
              volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)) ≠ ∞ := by
          apply ENNReal.mul_ne_top
          · exact ENNReal.div_ne_top
              (ENNReal.rpow_ne_top_of_nonneg hkexp
                ENNReal.ofReal_ne_top) hV0
          · exact ENNReal.rpow_ne_top_of_nonneg
              (sub_nonneg.mpr ((div_le_one hP0).2 hP.le)) hVtop
        apply ENNReal.mul_ne_top hVtop
        exact ENNReal.rpow_ne_top_of_nonneg hP0.le hKtop
  have hCpos : 0 < parabolicAdamsPotentialConstant β P τ := by
    unfold parabolicAdamsPotentialConstant
    dsimp
    have hAtop : parabolicHedbergNearConstant β +
        parabolicTailKernelConstant β τ ≠ ∞ := hCtop
    have hC0pos : 0 <
        (parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) *
          (volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)) ^
            (β * τ / 5) := by
      exact ENNReal.mul_pos hApos.ne'
        (ENNReal.rpow_pos hDpos hDtop).ne'
    have hC0top :
        (parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) *
          (volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)) ^
            (β * τ / 5) ≠ ∞ := by
      exact ENNReal.mul_ne_top hAtop
        (ENNReal.rpow_ne_top_of_nonneg htheta.le hDtop)
    have hC0pow : 0 <
        ((parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) *
          (volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)) ^
            (β * τ / 5)) ^ (P / (1 - β * τ / 5)) :=
      ENNReal.rpow_pos hC0pos hC0top
    have hC0powtop :
        ((parabolicHedbergNearConstant β + parabolicTailKernelConstant β τ) *
          (volume (parabolicCylinder 0 0 1) ^ (1 - 1 / P)) ^
            (β * τ / 5)) ^ (P / (1 - β * τ / 5)) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hs.le hC0top
    exact ENNReal.rpow_pos
      (ENNReal.mul_pos hC0pow.ne' hmaxpos.ne')
      (ENNReal.mul_ne_top hC0powtop
      hmax_top)
  by_cases hNtop : N = ∞
  · rw [hNtop, ENNReal.mul_top hCpos.ne']
    exact le_top
  exact parabolicRieszPotential_adams_finite hP hPτ hβ hβτ hf
    (by simpa [N] using hN0) (by simpa [N] using hNtop) hCtop

end CKN.Foundation.Parabolic.Morrey
