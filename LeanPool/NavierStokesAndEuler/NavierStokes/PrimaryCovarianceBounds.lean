/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryPulseBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ChartScales

@[expose] public section

/-!
# Zeroth-order bounds for the actual primary covariance

The covariance is the same normalized-slot integral used by
`PrimaryPulseBounds`. Compact model cone margins, actual Gaussian pulse
integrals, and the native chart scales produce the determinant and inverse
weight bounds. Flat target weights are retained as factors.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.PrimaryCovarianceBounds

abbrev Mat2 := SmoothCovariance.Mat2
abbrev Vec2 := SmoothCovariance.Vec2
abbrev Datum := Mat2 × Vec2

noncomputable local instance : NormedAddCommGroup Mat2 :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Fin 2 → ℝ))

noncomputable local instance : NormedSpace ℝ Mat2 :=
  inferInstanceAs (NormedSpace ℝ (Fin 2 → Fin 2 → ℝ))

/-- The same compact model cone supplies quantitative margins for every
nearby actual matrix, without assuming continuity of the competing family. -/
theorem compact_model_margins {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (H0 : X → Mat2) (T0 : X → Vec2)
    (hH0 : ∀ i j, ContinuousOn (fun p => H0 p i j) K)
    (hT0 : ∀ i, ContinuousOn (fun p => T0 p i) K)
    (hcone : ∀ p ∈ K, SmoothCovariance.StrictCone (H0 p) (T0 p)) :
    ∃ rho delta M : ℝ, 0 < rho ∧ 0 < delta ∧ 1 ≤ M ∧
      ∀ p ∈ K, ∀ H : Mat2, (∀ i j, |H i j - H0 p i j| ≤ rho) →
        delta ≤ |H.det| ∧ (∀ j, delta ≤ SmoothCovariance.weights H (T0 p) j) ∧
          (∀ i j, |H i j| ≤ M) := by
  let f : X → Datum := fun p => (H0 p, T0 p)
  have hf : ContinuousOn f K :=
    (continuousOn_pi.mpr (fun i => continuousOn_pi.mpr (hH0 i))).prodMk
      (continuousOn_pi.mpr hT0)
  let A : Set Datum := f '' K
  have hA : IsCompact A := hK.image_of_continuousOn hf
  have hAc : A ⊆ SmoothCovariance.strictConeRegion := by
    rintro z ⟨p, hp, rfl⟩
    exact hcone p hp
  obtain ⟨rho, hrho, hstable⟩ := SmoothCovariance.compact_perturbation_stability hA hAc
  let B : Set Datum := (fun z : Datum × Datum => z.1 + z.2) ''
    (A ×ˢ Metric.closedBall 0 rho)
  have hB : IsCompact B :=
    (hA.prod (isCompact_closedBall (0 : Datum) rho)).image (continuous_fst.add continuous_snd)
  have hBc : ∀ z ∈ B, SmoothCovariance.StrictCone z.1 z.2 := by
    rintro z ⟨⟨a, e⟩, ⟨ha, he⟩, rfl⟩
    apply hstable a ha (a + e)
    have heq : (a + e) - a = e := by abel
    change dist (a + e) a ≤ rho
    rw [dist_eq_norm, heq]
    simpa only [Metric.mem_closedBall, dist_zero_right] using he
  have hH : ∀ i j, ContinuousOn (fun z : Datum => z.1 i j) B := fun i j =>
    ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).continuousOn
  have hT : ∀ i, ContinuousOn (fun z : Datum => z.2 i) B := fun i =>
    ((continuous_apply i).comp continuous_snd).continuousOn
  obtain ⟨delta, hdelta, hbound⟩ := SmoothCovariance.compact_uniform_positive hB hH hT hBc
  obtain ⟨M0, hM0⟩ := hB.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (fun z : Datum => z.1) B)
  refine ⟨rho, delta, max 1 M0, hrho, hdelta, le_max_left _ _, ?_⟩
  intro p hp H hclose
  have hdist : dist (H, T0 p) (H0 p, T0 p) ≤ rho := by
    rw [dist_prod_same_right]
    apply (dist_pi_le_iff hrho.le).mpr
    intro i
    apply (dist_pi_le_iff hrho.le).mpr
    intro j
    simpa only [Real.dist_eq] using hclose i j
  have hmem : (H, T0 p) ∈ B := by
    refine ⟨((H0 p, T0 p), (H, T0 p) - (H0 p, T0 p)), ?_, ?_⟩
    · exact ⟨mem_image_of_mem f hp, by
        simpa only [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] using hdist⟩
    · dsimp only
      abel
  refine ⟨(hbound _ hmem).1, (hbound _ hmem).2, ?_⟩
  intro i j
  exact (norm_le_pi_norm (H i) j).trans
    ((norm_le_pi_norm H i).trans ((hM0 _ hmem).trans (le_max_right _ _)))

theorem normalized_columns (R : ℝ) (H : Mat2) (c : Vec2) :
    PrimaryPulseBounds.normalizedMatrix R (FlatCovariance.columns H c) =
      FlatCovariance.columns H (fun j => R * c j) := by
  ext i j
  simp only [PrimaryPulseBounds.normalizedMatrix, FlatCovariance.columns]
  ring

/-- Column factors of size `1/R` turn the model margins into an actual
normalized determinant gap and an inverse lower bound proportional to
`R*zeta`. No positive minimum of the flat factor is used. -/
theorem column_scale_bounds (H : Mat2) (T : Vec2) (c : Vec2)
    {R lo hi delta M zeta : ℝ} (hR : 0 < R) (hlo : 0 < lo) (hhi : 0 < hi)
    (hdelta : 0 < delta) (hzeta : 0 ≤ zeta)
    (hc : ∀ j, lo ≤ R * c j ∧ R * c j ≤ hi)
    (hdet : delta ≤ |H.det|) (hw : ∀ j, delta ≤ SmoothCovariance.weights H T j)
    (hentry : ∀ i j, |H i j| ≤ M) :
    lo ^ 2 * delta ≤ |(PrimaryPulseBounds.normalizedMatrix R (FlatCovariance.columns H c)).det| ∧
      (∀ i j, |R * FlatCovariance.columns H c i j| ≤ hi * M) ∧
      (∀ j, (delta / hi) * R * zeta ≤ SmoothCovariance.weights
        (FlatCovariance.columns H c) (FlatCovariance.scaledTarget zeta T) j) := by
  have hcpos (j : Fin 2) : 0 < c j := by
    have h := hlo.trans_le (hc j).1
    exact pos_of_mul_pos_right h hR.le
  have hcn (j : Fin 2) : c j ≠ 0 := (hcpos j).ne'
  have hdn : H.det ≠ 0 := by
    intro hd
    rw [hd, abs_zero] at hdet
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [normalized_columns, FlatCovariance.determinant_columns, abs_mul, abs_mul,
      abs_of_pos (mul_pos hR (hcpos 0)), abs_of_pos (mul_pos hR (hcpos 1))]
    have hprod : lo ^ 2 ≤ (R * c 0) * (R * c 1) := by
      simpa only [pow_two] using mul_le_mul (hc 0).1 (hc 1).1 hlo.le
        (mul_pos hR (hcpos 0)).le
    exact mul_le_mul hprod hdet hdelta.le
      (mul_nonneg (mul_pos hR (hcpos 0)).le (mul_pos hR (hcpos 1)).le)
  · intro i j
    change |R * (c j * H i j)| ≤ _
    rw [← mul_assoc, abs_mul, abs_of_pos (mul_pos hR (hcpos j))]
    exact mul_le_mul (hc j).2 (hentry i j) (abs_nonneg _) hhi.le
  · intro j
    rw [FlatCovariance.weights_columns H c T zeta hdn hcn]
    have hinv : R / hi ≤ 1 / c j := by
      apply (div_le_div_iff₀ hhi (hcpos j)).mpr
      simpa only [one_mul] using (hc j).2
    calc
      (delta / hi) * R * zeta = (R / hi) * zeta * delta := by ring
      _ ≤ (1 / c j) * zeta * delta := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinv hzeta) hdelta.le
      _ ≤ (1 / c j) * zeta * SmoothCovariance.weights H T j :=
        mul_le_mul_of_nonneg_left (hw j) (mul_nonneg (div_pos zero_lt_one (hcpos j)).le hzeta)
      _ = _ := by ring

theorem slotCutoff_bounds {r : ℝ} (hr : 1 ≤ r) :
    PulseCovariance.CutoffBounds r (GaussianTailFlat.slotCutoff (r ^ 2)) := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hrp
  refine ⟨(GaussianTailFlat.slotCutoff_contDiff _).continuous, ?_, ?_, ?_⟩
  · intro v
    exact (abs_of_nonneg (GaussianTailFlat.profile_mem_Icc _).1).trans_le
      (GaussianTailFlat.profile_mem_Icc _).2
  · intro v hv
    apply GaussianTailFlat.slotCutoff_zero hr2
    by_contra h
    have hb := abs_lt.mp (lt_of_not_ge h)
    apply hv
    constructor <;> linarith [hb.1, hb.2]
  · intro v hv
    apply GaussianTailFlat.slotCutoff_one hr2
    apply abs_le.mpr
    constructor <;> nlinarith [hv.1, hv.2]

/-! ## Native chart scale and the positive scalar column sizes -/

noncomputable def slotRadius (r0 h : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (ChartScales.slotLength r0 h n)

theorem slotLength_pos {r0 : ℝ} (hr0 : 0 < r0) (h : ℝ) (n : ℕ) :
    0 < ChartScales.slotLength r0 h n :=
  div_pos (by positivity) (ChartScales.timeCoefficient_pos h n)

theorem slotRadius_pos {r0 : ℝ} (hr0 : 0 < r0) (h : ℝ) (n : ℕ) :
    0 < slotRadius r0 h n := Real.sqrt_pos.mpr (slotLength_pos hr0 h n)

theorem slotRadius_sq {r0 : ℝ} (hr0 : 0 < r0) (h : ℝ) (n : ℕ) :
    slotRadius r0 h n ^ 2 = ChartScales.slotLength r0 h n :=
  Real.sq_sqrt (slotLength_pos hr0 h n).le

theorem chart_length_identity (r0 h : ℝ) (n : ℕ) :
    ChartScales.timeCoefficient h n * ChartScales.slotLength r0 h n = 2 * r0 := by
  exact mul_div_cancel₀ _ (ChartScales.timeCoefficient_pos h n).ne'

theorem chart_scalar_factor_bounds {r0 h : ℝ} (hr0 : 0 < r0) (hh : 0 ≤ h)
    {n : ℕ} (hn : 4 ≤ n) :
    Real.sqrt (2 * r0 / ChartScales.Tg) ≤
      Real.sqrt (ChartScales.S n) * ChartScales.timeCoefficient h n * slotRadius r0 h n ∧
    Real.sqrt (ChartScales.S n) * ChartScales.timeCoefficient h n * slotRadius r0 h n ≤
      Real.sqrt (2 * r0) := by
  let c := ChartScales.timeCoefficient h n
  let S := ChartScales.S n
  let R := Real.sqrt S * c * slotRadius r0 h n
  have hc : 0 < c := ChartScales.timeCoefficient_pos h n
  have hS : 0 < S := ChartScales.S_pos (by omega)
  have hr : 0 < slotRadius r0 h n := slotRadius_pos hr0 h n
  have hTg : 0 < ChartScales.Tg := ChartScales.Tg_pos
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hSc : 1 / ChartScales.Tg ≤ S * c ∧ S * c ≤ 1 := by
    have hb := ChartScales.timeCoefficient_bounds h hh hn
    constructor
    · apply (div_le_iff₀ ChartScales.Tg_pos).mpr
      have ht := (div_le_iff₀ (mul_pos ChartScales.Tg_pos hS)).mp hb.1
      dsimp [S, c] at *
      nlinarith
    · have ht := (le_div_iff₀ hS).mp hb.2
      nlinarith
  have hRsq : R ^ 2 = 2 * r0 * (S * c) := by
    dsimp [R]
    calc
      _ = (Real.sqrt S) ^ 2 * c ^ 2 * slotRadius r0 h n ^ 2 := by ring
      _ = S * c ^ 2 * ChartScales.slotLength r0 h n := by
        rw [Real.sq_sqrt hS.le, slotRadius_sq hr0]
      _ = (c * ChartScales.slotLength r0 h n) * (S * c) := by ring
      _ = _ := by rw [chart_length_identity]
  have hlow : 2 * r0 / ChartScales.Tg ≤ R ^ 2 := by
    rw [hRsq]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hSc.1 (by positivity : 0 ≤ 2 * r0)
  have hhigh : R ^ 2 ≤ 2 * r0 := by
    rw [hRsq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hSc.2 (by positivity : 0 ≤ 2 * r0)
  constructor
  · have hs := Real.sq_sqrt (show 0 ≤ 2 * r0 / ChartScales.Tg by positivity)
    have hspos := Real.sqrt_nonneg (2 * r0 / ChartScales.Tg)
    change Real.sqrt (2 * r0 / ChartScales.Tg) ≤ R
    nlinarith
  · have hs := Real.sq_sqrt (show 0 ≤ 2 * r0 by positivity)
    have hspos := Real.sqrt_nonneg (2 * r0)
    change R ≤ Real.sqrt (2 * r0)
    nlinarith

noncomputable def scalarLower (kappa r0 a B : ℝ) : ℝ :=
  kappa * PulseCovariance.PulseBounds.lowerMassConstant a B * Real.sqrt (2 * r0 / ChartScales.Tg)

noncomputable def scalarUpper (kappa r0 A b : ℝ) : ℝ :=
  kappa * (A ^ 2 * Real.sqrt (Real.pi / (2 * b))) * Real.sqrt (2 * r0)

theorem scalarLower_pos {kappa r0 a B : ℝ} (hkappa : 0 < kappa) (hr0 : 0 < r0) (ha : 0 < a) :
    0 < scalarLower kappa r0 a B := by
  unfold scalarLower PulseCovariance.PulseBounds.lowerMassConstant
  have hTg := ChartScales.Tg_pos
  positivity

theorem scalarUpper_pos {kappa r0 A b : ℝ} (hkappa : 0 < kappa) (hr0 : 0 < r0)
    (hA : 0 < A) (hb : 0 < b) : 0 < scalarUpper kappa r0 A b := by
  unfold scalarUpper
  positivity

theorem chart_column_mass_bounds {r0 h kappa a A b B : ℝ}
    (hr0 : 0 < r0) (hh : 0 ≤ h) (hkappa : 0 < kappa) {n : ℕ} (hn : 4 ≤ n)
    {psi x : ℝ → ℝ} (hp : PulseCovariance.PulseBounds (slotRadius r0 h n) a A b B psi x) :
    scalarLower kappa r0 a B ≤ Real.sqrt (ChartScales.S n) *
      (kappa * ChartScales.timeCoefficient h n * PulseCovariance.mass psi x) ∧
    Real.sqrt (ChartScales.S n) *
      (kappa * ChartScales.timeCoefficient h n * PulseCovariance.mass psi x) ≤
      scalarUpper kappa r0 A b := by
  have hs := chart_scalar_factor_bounds hr0 hh hn
  have hS : 0 ≤ Real.sqrt (ChartScales.S n) := Real.sqrt_nonneg _
  have hc := (ChartScales.timeCoefficient_pos h n).le
  have hlo := hp.lowerMassConstant_pos.le
  have hhi : 0 ≤ A ^ 2 * Real.sqrt (Real.pi / (2 * b)) := by positivity
  constructor
  · calc
      _ ≤ kappa * PulseCovariance.PulseBounds.lowerMassConstant a B *
          (Real.sqrt (ChartScales.S n) * ChartScales.timeCoefficient h n * slotRadius r0 h n) :=
        mul_le_mul_of_nonneg_left hs.1 (mul_nonneg hkappa.le hlo)
      _ = (kappa * (Real.sqrt (ChartScales.S n) * ChartScales.timeCoefficient h n)) *
          (PulseCovariance.PulseBounds.lowerMassConstant a B * slotRadius r0 h n) := by ring
      _ ≤ (kappa * (Real.sqrt (ChartScales.S n) * ChartScales.timeCoefficient h n)) *
          PulseCovariance.mass psi x := mul_le_mul_of_nonneg_left hp.mass_lower (by positivity)
      _ = _ := by ring
  · calc
      _ = (kappa * (Real.sqrt (ChartScales.S n) * ChartScales.timeCoefficient h n)) *
          PulseCovariance.mass psi x := by ring
      _ ≤ (kappa * (Real.sqrt (ChartScales.S n) * ChartScales.timeCoefficient h n)) *
          (A ^ 2 * Real.sqrt (Real.pi / (2 * b)) * slotRadius r0 h n) :=
        mul_le_mul_of_nonneg_left hp.mass_upper (by positivity)
      _ = (kappa * (A ^ 2 * Real.sqrt (Real.pi / (2 * b)))) *
          (Real.sqrt (ChartScales.S n) * ChartScales.timeCoefficient h n * slotRadius r0 h n) := by
            ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs.2 (mul_nonneg hkappa.le hhi)

theorem eventually_slotRadius_large {r0 h : ℝ} (hr0 : 0 < r0) (hh : 0 ≤ h) (R : ℝ) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n → R ≤ slotRadius r0 h n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max 0 (R / Real.sqrt (2 * r0)))
  refine ⟨max 4 N, le_max_left _ _, ?_⟩
  intro n hn
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have hroot : 0 < Real.sqrt (2 * r0) := Real.sqrt_pos.mpr (by positivity)
  have hRn : R ≤ Real.sqrt (2 * r0) * n := by
    have hd : R / Real.sqrt (2 * r0) ≤ n := (le_max_right _ _).trans (hN.trans hnN)
    have hx := (div_le_iff₀ hroot).mp hd
    nlinarith
  apply hRn.trans
  have hlen := (ChartScales.slotLength_bounds r0 h hr0.le hh hn4).1
  have hsq := slotRadius_sq hr0 h n
  have hr := (slotRadius_pos hr0 h n).le
  have hs := Real.sq_sqrt (show 0 ≤ 2 * r0 by positivity)
  dsimp [ChartScales.S] at hlen
  nlinarith [sq_nonneg (Real.sqrt (2 * r0) * n - slotRadius r0 h n)]

/-! ## The actual pair matrix -/

noncomputable def normalizedPair (P : Fin 2 → PartitionedCovariance.Pulse) : Mat2 :=
  fun i j => PulseCovariance.normalizedColumn (P j).ψ (P j).x (P j).t i

noncomputable def pairScales (kappa : ℝ) (ci : Vec2) (P : Fin 2 → PartitionedCovariance.Pulse) :
  Vec2 :=
  fun j => kappa * ci j * PulseCovariance.mass (P j).ψ (P j).x

theorem pairMatrix_factorization {r a A b B : ℝ}
    (P : Fin 2 → PartitionedCovariance.Pulse)
    (hP : ∀ j, PulseCovariance.PulseBounds r a A b B (P j).ψ (P j).x)
    (vr vt : TorusInverse.Plane) (r0 : ℝ) (ci : Vec2) :
    PartitionedCovariance.pairMatrix vr vt r0 ci P =
      FlatCovariance.columns (normalizedPair P)
        (pairScales (PartitionedCovariance.nativePrefactor vr vt r0) ci P) := by
  ext i j
  have he := congrFun ((hP j).actualColumn_factorization (ci j) (P j).t) i
  change PartitionedCovariance.nativePrefactor vr vt r0 * PulseCovariance.actualColumn
    (ci j) (P j).ψ (P j).x (P j).t i = _
  rw [he]
  dsimp [FlatCovariance.columns, normalizedPair, pairScales]
  ring

theorem normalizedPair_entry_error {r a A b B E D : ℝ}
    (P : Fin 2 → PartitionedCovariance.Pulse)
    (hP : ∀ j, PulseCovariance.PulseBounds r a A b B (P j).ψ (P j).x)
    (H0 : Mat2) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hratio : ∀ j i v, v ∈ Icc 0 (r ^ 2) →
      |(P j).t v i / (P j).x v - H0 i j| ≤
        E / r ^ 2 + D * |v - r ^ 2 / 2| / r ^ 2) (i j : Fin 2) :
    |normalizedPair P i j - H0 i j| ≤
      (E + D * PulseCovariance.concentrationConstant a A b B) / r := by
  exact (hP j).averagedDirection_error_order
    ((hP j).ratio_continuousOn
      (fun k => ((continuous_apply k).comp (P j).t_continuous).continuousOn) i)
    hE hD (hratio j i)

/-- Precisely the zeroth-order inputs used by `PrimaryPulseBounds`, with
the stronger inverse lower bound retaining the factor `R`. -/
structure ZeroOrderBounds (R detGap entryBound inverseLower zeta : ℝ) (H : Mat2) (T : Vec2) : Prop
  where
  determinant : detGap ≤ |(PrimaryPulseBounds.normalizedMatrix R H).det|
  entries : ∀ i j, |R * H i j| ≤ entryBound
  weights : ∀ j, inverseLower * R * zeta ≤ SmoothCovariance.weights H T j

theorem ZeroOrderBounds.weight_lower {R detGap entryBound inverseLower zeta : ℝ}
    {H : Mat2} {T : Vec2} (h : ZeroOrderBounds R detGap entryBound inverseLower zeta H T)
    (hR : 1 ≤ R) (ha : 0 ≤ inverseLower) (hzeta : 0 ≤ zeta) (j : Fin 2) :
    inverseLower * zeta ≤ SmoothCovariance.weights H T j := by
  exact (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ha hR) hzeta).trans (h.weights j)

theorem ZeroOrderBounds.det_ne_zero {R detGap entryBound inverseLower zeta : ℝ}
    {H : Mat2} {T : Vec2} (h : ZeroOrderBounds R detGap entryBound inverseLower zeta H T)
    (hgap : 0 < detGap) : H.det ≠ 0 := by
  intro hz
  have hd := h.determinant
  rw [PrimaryPulseBounds.normalizedMatrix_det, hz, mul_zero, abs_zero] at hd
  exact (not_le_of_gt hgap) hd

theorem ZeroOrderBounds.weights_pos {R detGap entryBound inverseLower zeta : ℝ}
    {H : Mat2} {T : Vec2} (h : ZeroOrderBounds R detGap entryBound inverseLower zeta H T)
    (hR : 0 < R) (ha : 0 < inverseLower) (hzeta : 0 < zeta) (j : Fin 2) :
    0 < SmoothCovariance.weights H T j :=
  (mul_pos (mul_pos ha hR) hzeta).trans_le (h.weights j)

theorem ZeroOrderBounds.strictCone {R detGap entryBound inverseLower zeta : ℝ}
    {H : Mat2} {T : Vec2} (h : ZeroOrderBounds R detGap entryBound inverseLower zeta H T)
    (hR : 0 < R) (ha : 0 < inverseLower) (hzeta : 0 < zeta) :
    SmoothCovariance.StrictCone H T :=
  (SmoothCovariance.weights_pos_iff H T).mp (h.weights_pos hR ha hzeta)

theorem sqrt_S_eq (n : ℕ) : Real.sqrt (ChartScales.S n) = (n : ℝ) := by
  exact Real.sqrt_sq (Nat.cast_nonneg n)

/-- The weaker inverse bound required by the square-root jet theorem is
an immediate consequence, without losing the flat target factor. -/
theorem ZeroOrderBounds.primary_weight_lower {n : ℕ} {detGap entryBound inverseLower zeta : ℝ}
    {H : Mat2} {T : Vec2}
    (h : ZeroOrderBounds (Real.sqrt (ChartScales.S n)) detGap entryBound inverseLower zeta H T)
    (hn : 1 ≤ n) (ha : 0 ≤ inverseLower) (hzeta : 0 ≤ zeta) (j : Fin 2) :
    inverseLower * zeta ≤ SmoothCovariance.weights H T j := by
  apply h.weight_lower _ ha hzeta j
  rw [sqrt_S_eq]
  exact_mod_cast hn

/-- For the actual native pair, all uniform zeroth-order constants are
chosen before the band. Only pointwise pulse and normalized-direction
estimates are inputs; no integrated matrix margin is assumed. -/
theorem compact_chart_pair_bounds {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (H0 : X → Mat2) (T0 : X → Vec2)
    (hH0 : ∀ i j, ContinuousOn (fun p => H0 p i j) K)
    (hT0 : ∀ i, ContinuousOn (fun p => T0 p i) K)
    (hcone : ∀ p ∈ K, SmoothCovariance.StrictCone (H0 p) (T0 p))
    (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    {r0 h a A b B E D : ℝ} (hr0 : 0 < r0) (hh : 0 ≤ h)
    (ha : 0 < a) (hA : 0 < A) (hb : 0 < b) (hE : 0 ≤ E) (hD : 0 ≤ D) :
    ∃ N : ℕ, 4 ≤ N ∧ ∃ detGap entryBound inverseLower : ℝ,
      0 < detGap ∧ 1 ≤ entryBound ∧ 0 < inverseLower ∧
      ∀ n : ℕ, N ≤ n → ∀ p ∈ K, ∀ P : Fin 2 → PartitionedCovariance.Pulse,
        (∀ j, PulseCovariance.PulseBounds (slotRadius r0 h n) a A b B (P j).ψ (P j).x) →
        (∀ j i v, v ∈ Icc 0 (ChartScales.slotLength r0 h n) →
          |(P j).t v i / (P j).x v - H0 p i j| ≤ E / ChartScales.slotLength r0 h n +
            D * |v - ChartScales.slotLength r0 h n / 2| / ChartScales.slotLength r0 h n) →
        ∀ zeta : ℝ, 0 ≤ zeta →
        ZeroOrderBounds (Real.sqrt (ChartScales.S n)) detGap entryBound inverseLower zeta
          (PartitionedCovariance.pairMatrix vr vt r0 (fun _ => ChartScales.timeCoefficient h n) P)
          (FlatCovariance.scaledTarget zeta (T0 p)) := by
  obtain ⟨rho, delta, M, hrho, hdelta, hM, hmargin⟩ := compact_model_margins hK H0 T0 hH0 hT0 hcone
  let kappa := PartitionedCovariance.nativePrefactor vr vt r0
  have hkappa : 0 < kappa := PartitionedCovariance.nativePrefactor_pos hdet hr0
  let lo := scalarLower kappa r0 a B
  let hi := scalarUpper kappa r0 A b
  have hlo : 0 < lo := scalarLower_pos hkappa hr0 ha
  have hhi : 0 < hi := scalarUpper_pos hkappa hr0 hA hb
  let Q := E + D * |PulseCovariance.concentrationConstant a A b B|
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨N, hN4, hN⟩ := eventually_slotRadius_large hr0 hh (max 1 (Q / rho))
  refine ⟨N, hN4, lo ^ 2 * delta, max 1 (hi * M), delta / hi,
    by positivity, le_max_left _ _, div_pos hdelta hhi, ?_⟩
  intro n hn p hp P hP hratio zeta hzeta
  have hn4 : 4 ≤ n := hN4.trans hn
  have hr : 0 < slotRadius r0 h n := slotRadius_pos hr0 h n
  have hrlarge : Q / rho ≤ slotRadius r0 h n := (le_max_right _ _).trans (hN n hn)
  have hsmall : Q / slotRadius r0 h n ≤ rho := by
    apply (div_le_iff₀ hr).mpr
    have ht := (div_le_iff₀ hrho).mp hrlarge
    nlinarith
  have hclose (i j : Fin 2) : |normalizedPair P i j - H0 p i j| ≤ rho := by
    have he := normalizedPair_entry_error P hP (H0 p) hE hD
      (by simpa only [slotRadius_sq hr0] using hratio) i j
    apply he.trans
    apply le_trans _ hsmall
    apply div_le_div_of_nonneg_right _ hr.le
    exact add_le_add_right (mul_le_mul_of_nonneg_left (le_abs_self _) hD) _
  obtain ⟨hd, hw, he⟩ := hmargin p hp (normalizedPair P) hclose
  have hscale (j : Fin 2) : lo ≤ Real.sqrt (ChartScales.S n) *
      pairScales kappa (fun _ => ChartScales.timeCoefficient h n) P j ∧
      Real.sqrt (ChartScales.S n) * pairScales kappa (fun _ => ChartScales.timeCoefficient h n) P j
        ≤ hi :=
    chart_column_mass_bounds hr0 hh hkappa hn4 (hP j)
  have hR : 0 < Real.sqrt (ChartScales.S n) := Real.sqrt_pos.mpr (ChartScales.S_pos (by omega))
  have hbounds := column_scale_bounds (normalizedPair P) (T0 p)
    (pairScales kappa (fun _ => ChartScales.timeCoefficient h n) P)
    hR hlo hhi hdelta hzeta hscale hd hw he
  rw [pairMatrix_factorization P hP vr vt r0]
  exact ⟨hbounds.1, fun i j => (hbounds.2.1 i j).trans (le_max_right _ _), hbounds.2.2⟩

/-! ## Uniform constants for the actual reference envelopes -/

/-- Compact positive reference parameters give one spectral gap and two
Gaussian constants, chosen independently of every slot length. -/
theorem compact_reference_bounds {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (lam u : X → ℝ)
    (hlam : ContinuousOn lam K) (hu : ContinuousOn u K)
    (hlampos : ∀ p ∈ K, 0 < lam p) (hupos : ∀ p ∈ K, 0 < u p) :
    ∃ gap b B : ℝ, 0 < gap ∧ 0 < b ∧ 0 < B ∧
      ∀ p ∈ K, ∀ L : ℝ, 0 < L → ∀ v ∈ Icc 0 L,
        gap ≤ ViscousPropagator.referenceEigenvalue (lam p) (u p) L v ∧
          Real.exp (-B * (v - L / 2) ^ 2 / L) ≤
            PrimaryPulseBounds.referenceP (lam p) (u p) L v ∧
          PrimaryPulseBounds.referenceP (lam p) (u p) L v ≤
            Real.exp (-b * (v - L / 2) ^ 2 / L) := by
  let g := fun p => lam p / Real.sqrt (1 + (3 * u p / 2) ^ 2)
  let blo := fun p => u p * GaussianEnvelope.referenceMinSlope (lam p) (u p) / 2
  let bhi := fun p => u p * GaussianEnvelope.referenceMaxSlope (lam p) (u p) / 2
  have hg : ContinuousOn g K := by
    exact hlam.div ((continuousOn_const.add (((continuousOn_const.mul hu).div_const 2).pow 2)).sqrt)
      (fun p _ => (PulseGrowth.radius_pos _).ne')
  have hden : ContinuousOn (fun p => (1 + u p ^ 2) * Real.sqrt (1 + u p ^ 2)) K :=
    (continuousOn_const.add (hu.pow 2)).mul (continuousOn_const.add (hu.pow 2)).sqrt
  have hlo : ContinuousOn blo K := by
    exact (hu.mul ((hlam.mul hu).div hden
      (fun p _ => (PulseGrowth.dampingDenominator_pos _).ne'))).div_const 2
  have hhi : ContinuousOn bhi K := by
    exact (hu.mul (((continuousOn_const.mul hlam).mul hu).div_const 2 |>.add
      (((continuousOn_const.mul hlam).mul hu).div hden
        (fun p _ => (PulseGrowth.dampingDenominator_pos _).ne')))).div_const 2
  obtain ⟨gap, hgap, hgapbound⟩ := hK.exists_forall_le' hg
    (fun p hp => div_pos (hlampos p hp) (PulseGrowth.radius_pos _))
  obtain ⟨b, hb, hbbound⟩ := hK.exists_forall_le' hlo
    (fun p hp => div_pos (mul_pos (hupos p hp)
      (GaussianEnvelope.referenceMinSlope_pos (hlampos p hp) (hupos p hp))) (by norm_num))
  obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn hhi
  refine ⟨gap, b, 1 + |B0|, hgap, hb, by positivity, ?_⟩
  intro p hp L hL v hv
  have hBbound : bhi p ≤ 1 + |B0| := by
    have ht := hB0 p hp
    rw [Real.norm_eq_abs] at ht
    exact (le_abs_self _).trans (ht.trans (by linarith [le_abs_self B0]))
  have hbounds := GaussianEnvelope.reference_gaussian_bounds (hlampos p hp) (hupos p hp) hL hv
  have hfactor : 0 ≤ (v - L / 2) ^ 2 / L := div_nonneg (sq_nonneg _) hL.le
  refine ⟨(hgapbound p hp).trans
    (PrimaryODE.referenceEigenvalue_lower (hlampos p hp) (hupos p hp).le hL hv), ?_, ?_⟩
  · apply le_trans _ hbounds.1
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right (neg_le_neg hBbound) hfactor
    dsimp [bhi] at ht
    convert! ht using 1 <;> ring
  · apply hbounds.2.trans
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right (neg_le_neg (hbbound p hp)) hfactor
    dsimp [blo] at ht
    convert! ht using 1 <;> ring

theorem eventually_slow_large (C : ℝ) :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ n : ℕ, N ≤ n → C ≤ ChartScales.S n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 C)
  refine ⟨max 4 N, le_max_left _ _, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (le_max_right 4 N).trans hn
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans (hN.trans hNn)
  have hCn : C ≤ n := (le_max_right _ _).trans (hN.trans hNn)
  change C ≤ (n : ℝ) ^ 2
  nlinarith

noncomputable def primaryLower (C D L : ℝ) : ℝ := Real.exp (-(D + 2 * C) * L) / 2
noncomputable def primaryUpper (C D L : ℝ) : ℝ := 3 * Real.exp ((D + 2 * C) * L) / 2

theorem primaryLower_pos (C D L : ℝ) : 0 < primaryLower C D L := by
  unfold primaryLower
  positivity

theorem primaryUpper_pos (C D L : ℝ) : 0 < primaryUpper C D L := by
  unfold primaryUpper
  positivity

section CanonicalPrimary

variable {Q : Type} [NormedAddCommGroup Q]

theorem canonicalPrimaryPulse_x_radial
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) {v : ℝ} (hv : v ∈ Icc 0 L) :
    (PrimaryPulseBounds.canonicalPrimaryPulse d lam u hL U hA p hp hk).x v =
      PrimaryODE.radialPrimary hL.le d (fun z => PrimaryPulseBounds.referenceP lam u L z.2) p v :=
        by
  rw [PrimaryPulseBounds.canonicalPrimaryPulse_x d lam u hL U hA p hp hk hv]
  rfl

theorem canonicalPrimaryPulse_ratio
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L : ℝ} (hL : 0 < L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L)) {v : ℝ} (hv : v ∈ Icc 0 L)
    (i : Fin 2) :
    (PrimaryPulseBounds.canonicalPrimaryPulse d lam u hL U hA p hp hk).t v i /
        (PrimaryPulseBounds.canonicalPrimaryPulse d lam u hL U hA p hp hk).x v =
      PrimaryPulseBounds.normalizedPulse d lam u L (p, v / L) i.succ /
        PrimaryPulseBounds.normalizedPulse d lam u L (p, v / L) 0 := by
  rw [PrimaryPulseBounds.canonicalPrimaryPulse_x d lam u hL U hA p hp hk hv,
    PrimaryPulseBounds.canonicalPrimaryPulse_t d lam u hL U hA p hp hk hv]
  have hLv : L * (v / L) = v := by field_simp
  simp only [PrimaryPulseBounds.normalizedPulse, hLv]
  rw [PrimaryPulseBounds.fundamental_eq_primary hL U hA hp hv]

/-- The cutoff and the radial component of the canonical primary satisfy
the covariance pulse bounds. The radial estimate is derived from the
actual homogeneous ODE, using only its coefficient errors and the scalar
reference envelope. -/
theorem canonicalPrimaryPulse_bounds
    (d : PrimaryODE.FrameData Q) (lam u : ℝ) {L r : ℝ} (hL : 0 < L)
    (hr : 1 ≤ r) (hrsq : r ^ 2 = L)
    (U : Set Q) (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 L))
    (p : Q) (hp : p ∈ U) (hk : d.Kinematics p (Icc 0 L))
    {gap b B S C D K : ℝ} (hgap : 0 < gap) (hb : 0 < b) (hB : 0 < B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hS : 0 < S)
    (hlarge : 2 * GrowingMode.coneConstant gap C ≤ S) (hslot : L ≤ K * S)
    (heigen : ∀ v ∈ Icc 0 L,
      d.eigenvalue (p, v) = ViscousPropagator.referenceEigenvalue lam u L v)
    (herr : ∀ v ∈ Icc 0 L,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S)
    (hvisc : ∀ v ∈ Icc 0 L,
      |d.viscosity (p, v) - ViscousPropagator.referenceViscosity lam u L v| ≤ D / S)
    (hreference : ∀ v ∈ Icc 0 L,
      gap ≤ ViscousPropagator.referenceEigenvalue lam u L v ∧
        Real.exp (-B * (v - L / 2) ^ 2 / L) ≤ PrimaryPulseBounds.referenceP lam u L v ∧
        PrimaryPulseBounds.referenceP lam u L v ≤ Real.exp (-b * (v - L / 2) ^ 2 / L)) :
    PulseCovariance.PulseBounds r (primaryLower C D K) (primaryUpper C D K) b B
      (PrimaryPulseBounds.canonicalPrimaryPulse d lam u hL U hA p hp hk).ψ
      (PrimaryPulseBounds.canonicalPrimaryPulse d lam u hL U hA p hp hk).x := by
  have hdP (v : ℝ) (hv : v ∈ Icc 0 L) :
      HasDerivAt (PrimaryPulseBounds.referenceP lam u L)
        ((d.eigenvalue (p, v) - ViscousPropagator.referenceViscosity lam u L v) *
          PrimaryPulseBounds.referenceP lam u L v) v := by
    rw [heigen v hv]
    exact PrimaryPulseBounds.referenceP_hasDerivAt lam u L v
  have hbound := PrimaryODE.primary_bounds hL.le d
    (fun z => PrimaryPulseBounds.referenceP lam u L z.2) hA hp hgap hC hD hS hlarge
    (by simpa only [sub_zero] using hslot) (ViscousPropagator.referenceViscosity lam u L)
    (fun v hv => by rw [heigen v hv]; exact (hreference v hv).1) herr hvisc
    (fun v _ => PrimaryPulseBounds.referenceP_pos lam u L v) hdP
  apply PulseCovariance.pulseBounds_of_envelope hr (primaryLower_pos _ _ _)
    (primaryUpper_pos _ _ _) hb hB
    (P := PrimaryPulseBounds.referenceP lam u L)
  · change PulseCovariance.CutoffBounds r (GaussianTailFlat.slotCutoff L)
    rw [← hrsq]
    exact slotCutoff_bounds hr
  · exact (PrimaryPulseBounds.canonicalPrimaryPulse d lam u hL U hA p hp hk).x_continuous
  · intro v hv
    rw [hrsq] at hv
    simpa only [PulseCovariance.gaussian_eq_length, hrsq] using (hreference v hv).2
  · intro v hv
    rw [hrsq] at hv
    rw [canonicalPrimaryPulse_x_radial d lam u hL U hA p hp hk hv]
    exact ⟨(hbound v hv).2.1, (hbound v hv).2.2.1⟩

end CanonicalPrimary

section NativePrimary

variable {Q : Type} [NormedAddCommGroup Q]

/-- Pointwise input estimates on the actual moving-frame coefficient.
These are coefficient hypotheses, not bounds on a solution or covariance. -/
structure CoefficientControl (d : PrimaryODE.FrameData Q) (lam u L S C D : ℝ) (p : Q) : Prop where
  eigenvalue : ∀ v ∈ Icc 0 L,
    d.eigenvalue (p, v) = ViscousPropagator.referenceEigenvalue lam u L v
  errors : ∀ v ∈ Icc 0 L,
    |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
    |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S
  viscosity : ∀ v ∈ Icc 0 L,
    |d.viscosity (p, v) - ViscousPropagator.referenceViscosity lam u L v| ≤ D / S

/-- The literal `primaryCovariance` with the native chart prefactor and
slot length; the integrands still use the actual constructed ODE solution. -/
noncomputable def nativePrimaryCovariance
    (vr vt : TorusInverse.Plane) (r0 h : ℝ)
    (d : Fin 2 → ℕ → PrimaryODE.FrameData Q) (lam u : Fin 2 → ℕ → ℝ)
    (n : ℕ) (p : Q) : Mat2 :=
  PrimaryPulseBounds.primaryCovariance
    (fun _ n => PartitionedCovariance.nativePrefactor vr vt r0 *
      ChartScales.timeCoefficient h n * ChartScales.slotLength r0 h n)
    d lam u (fun _ n => ChartScales.slotLength r0 h n) n p

/-- Uniform zeroth-order bounds for the same actual primary covariance
used in `PrimaryPulseBounds`.  All constants and the band threshold are
chosen from the fixed compact model, reference range, and coefficient
error constants.  In particular they are chosen before the band, the
particular ODE coefficients, and the possibly flat target factor `zeta`.

The only directional input is a pointwise ratio estimate for the actual
uncut primary.  Gaussian size, positive column masses, determinant gap,
and inverse-weight lower bounds are derived in the proof. -/
theorem compact_native_primary_bounds {K : Set Q}
    (hK : IsCompact K) (H0 : Q → Mat2) (T0 : Q → Vec2)
    (hH0 : ∀ i j, ContinuousOn (fun p => H0 p i j) K)
    (hT0 : ∀ i, ContinuousOn (fun p => T0 p i) K)
    (hcone : ∀ p ∈ K, SmoothCovariance.StrictCone (H0 p) (T0 p))
    {R : Set (ℝ × ℝ)} (hR : IsCompact R)
    (hRpos : ∀ z ∈ R, 0 < z.1 ∧ 0 < z.2)
    (vr vt : TorusInverse.Plane) (hdet : vr.1 * vt.2 - vr.2 * vt.1 ≠ 0)
    {r0 h C D E F : ℝ} (hr0 : 0 < r0) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ N : ℕ, 4 ≤ N ∧ ∃ detGap entryBound inverseLower : ℝ,
      0 < detGap ∧ 1 ≤ entryBound ∧ 0 < inverseLower ∧
      ∀ n : ℕ, N ≤ n →
      ∀ (d : Fin 2 → ℕ → PrimaryODE.FrameData Q) (lam u : Fin 2 → ℕ → ℝ)
        (U : Set Q),
      (∀ c, ContinuousOn ((d c n).coefficient 1) (U ×ˢ Icc 0 (ChartScales.slotLength r0 h n))) →
      ∀ p ∈ K, p ∈ U →
      (∀ c, (d c n).Kinematics p (Icc 0 (ChartScales.slotLength r0 h n))) →
      (∀ c, (lam c n, u c n) ∈ R) →
      (∀ c, CoefficientControl (d c n) (lam c n) (u c n)
        (ChartScales.slotLength r0 h n) (ChartScales.S n) C D p) →
      (∀ c i v, v ∈ Icc 0 (ChartScales.slotLength r0 h n) →
        |PrimaryPulseBounds.normalizedPulse (d c n) (lam c n) (u c n)
              (ChartScales.slotLength r0 h n) (p, v / ChartScales.slotLength r0 h n) i.succ /
            PrimaryPulseBounds.normalizedPulse (d c n) (lam c n) (u c n)
              (ChartScales.slotLength r0 h n) (p, v / ChartScales.slotLength r0 h n) 0 - H0 p i c| ≤
          E / ChartScales.slotLength r0 h n +
            F * |v - ChartScales.slotLength r0 h n / 2| / ChartScales.slotLength r0 h n) →
      ∀ zeta : ℝ, 0 ≤ zeta →
        ZeroOrderBounds (Real.sqrt (ChartScales.S n)) detGap entryBound inverseLower zeta
          (nativePrimaryCovariance vr vt r0 h d lam u n p)
          (FlatCovariance.scaledTarget zeta (T0 p)) := by
  obtain ⟨gap, b, B, hgap, hb, hB, href⟩ := compact_reference_bounds hR
    Prod.fst Prod.snd continuous_fst.continuousOn continuous_snd.continuousOn
    (fun z hz => (hRpos z hz).1) (fun z hz => (hRpos z hz).2)
  let Kslot := 2 * r0 * ChartScales.Tg
  let a := primaryLower C D Kslot
  let A := primaryUpper C D Kslot
  have ha : 0 < a := primaryLower_pos _ _ _
  have hApos : 0 < A := primaryUpper_pos _ _ _
  obtain ⟨N0, hN04, detGap, M, alpha, hgapM, hM, halpha, hpair⟩ :=
    compact_chart_pair_bounds hK H0 T0 hH0 hT0 hcone vr vt hdet
      (B := B) hr0 hh ha hApos hb hE hF
  obtain ⟨N1, hN14, hN1⟩ := eventually_slow_large (2 * GrowingMode.coneConstant gap C)
  obtain ⟨N2, hN24, hN2⟩ := eventually_slotRadius_large hr0 hh 1
  refine ⟨max N0 (max N1 N2), hN04.trans (le_max_left _ _),
    detGap, M, alpha, hgapM, hM, halpha, ?_⟩
  intro n hn d lam u U hA p hp hpU hk hrange hcoeff hratio zeta hzeta
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hn1 : N1 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn2 : N2 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn4 : 4 ≤ n := hN04.trans hn0
  have hL : 0 < ChartScales.slotLength r0 h n := slotLength_pos hr0 h n
  let P : Fin 2 → PartitionedCovariance.Pulse := fun c =>
    PrimaryPulseBounds.canonicalPrimaryPulse (d c n) (lam c n) (u c n)
      hL U (hA c) p hpU (hk c)
  have hPulse (c : Fin 2) : PulseCovariance.PulseBounds (slotRadius r0 h n) a A b B
      (P c).ψ (P c).x := by
    apply canonicalPrimaryPulse_bounds (d c n) (lam c n) (u c n) hL
      (hN2 n hn2) (slotRadius_sq hr0 h n) U (hA c) p hpU (hk c)
      hgap hb hB hC hD (ChartScales.S_pos (by omega)) (hN1 n hn1)
    · simpa only [Kslot, mul_assoc] using (ChartScales.slotLength_bounds r0 h hr0.le hh hn4).2
    · exact (hcoeff c).eigenvalue
    · exact (hcoeff c).errors
    · exact (hcoeff c).viscosity
    · exact href (lam c n, u c n) (hrange c) _ hL
  have hactual := hpair n hn0 p hp P hPulse
    (fun c i v hv => by
      rw [canonicalPrimaryPulse_ratio (d c n) (lam c n) (u c n) hL U (hA c) p hpU (hk c) hv]
      exact hratio c i v hv) zeta hzeta
  have heq : nativePrimaryCovariance vr vt r0 h d lam u n p =
      PartitionedCovariance.pairMatrix vr vt r0 (fun _ => ChartScales.timeCoefficient h n) P := by
    exact PrimaryPulseBounds.primaryCovariance_eq_canonicalPairMatrix _ _ _ _ _ n U p hpU
      (fun _ => hL) hA hk vr vt r0 (fun _ => ChartScales.timeCoefficient h n) (fun _ => rfl)
  rw [heq]
  exact hactual

end NativePrimary

/-! ## Scalar-cone input adapter -/

/-- The manuscript's two signed model columns satisfy all model-side
inputs of `compact_native_primary_bounds` directly from the scalar cone.
The actual pulse directions may be compared to these columns using the
ratio hypothesis of that theorem. -/
theorem scalar_cone_model {X : Type*} [TopologicalSpace X] {K : Set X}
    {c₀ u m t : X → ℝ} (hc₀ : ContinuousOn c₀ K) (hu : ContinuousOn u K)
    (hm : ContinuousOn m K) (ht : ContinuousOn t K)
    (hc₀neg : ∀ p ∈ K, c₀ p < 0) (hupos : ∀ p ∈ K, 0 < u p)
    (hcone : ∀ p ∈ K, |Covariance.normalMagnitude (c₀ p) (u p) * t p| < u p * m p) :
    (∀ i j, ContinuousOn (fun p => PulseCovariance.signedModel (c₀ p) (u p) i j) K) ∧
      (∀ i, ContinuousOn (fun p => Covariance.target (m p) (t p) i) K) ∧
      (∀ p ∈ K, SmoothCovariance.StrictCone (PulseCovariance.signedModel (c₀ p) (u p))
        (Covariance.target (m p) (t p))) := by
  refine ⟨PulseCovariance.signedModel_continuousOn hc₀ hu, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hm.fun_neg
    · exact ht
  · intro p hp
    exact PulseCovariance.signedModel_strictCone (hc₀neg p hp) (hupos p hp) (hcone p hp)

end NavierStokes.PrimaryCovarianceBounds
