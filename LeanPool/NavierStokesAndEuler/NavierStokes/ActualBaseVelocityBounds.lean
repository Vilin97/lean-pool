/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.FinalSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalWaveSum
import LeanPool.NavierStokesAndEuler.NavierStokes.AnnularEndpoint

/-!
# Fixed losses for the actual physical slow velocity

The compact similarity region uses the selected Borel scales and the existing
prefix estimates, including the axis. Outside the positive-order support the
velocity is its actual leading angular field. In the far exterior it is the
physical heat field. The final rate is on the full open-past endpoint filter.
-/

@[expose] public section


noncomputable section

open Set Filter Function
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ActualBaseVelocityBounds

open ProblemStatement SlowBorelBase BaseResidual DiagonalResidual

/-- Endpoint, given by `𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))`. -/
noncomputable def endpoint : Filter SpaceTime :=
  𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space))

theorem endpoint_past : ∀ᶠ z in endpoint, z.1 < 1 := by
  have h : ∀ᶠ z in endpoint, z ∈ SpacetimeEndpoint.openPast 1 :=
    self_mem_nhdsWithin
  exact h.mono (fun _ hz => hz.1)

theorem endpoint_compact :
    ∀ᶠ z in endpoint, z ∈ Metric.closedBall (1, (0 : Space)) 1 :=
  nhdsWithin_le_nhds (Metric.closedBall_mem_nhds _ (by norm_num))

theorem q_eq (h : ℝ) (z : SpaceTime) :
    (cartesianChart h z).1 = PhysicalWaveSum.physicalQ h z := rfl

theorem endpoint_q_small {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) :
    ∀ᶠ z in endpoint, 0 < PhysicalWaveSum.physicalQ h z ∧
      PhysicalWaveSum.physicalQ h z ≤ 1 := by
  have ht := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  filter_upwards [endpoint_past, ht.eventually (gt_mem_nhds zero_lt_one)] with z hz hq
  exact ⟨PhysicalWaveSum.physicalQ_pos hh hh1 hz, hq.le⟩

/-- Physical energy, given by `AxisymmetricFields.radialEnergy z.2`. -/
noncomputable def physicalEnergy (z : SpaceTime) : ℝ :=
  AxisymmetricFields.radialEnergy z.2

theorem physicalEnergy_smooth : ContDiff ℝ ∞ physicalEnergy :=
  AxisymmetricFields.contDiff_radialEnergy.comp contDiff_snd

theorem X_eq (h : ℝ) (z : SpaceTime) :
    (cartesianChart h z).2.1 = physicalEnergy z / PhysicalWaveSum.physicalQ h z := rfl

theorem X_nonneg {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) {z : SpaceTime}
    (hz : z.1 < 1) : 0 ≤ (cartesianChart h z).2.1 := by
  rw [X_eq]
  exact div_nonneg (AxisymmetricFields.radialEnergy_nonneg _) (PhysicalWaveSum.physicalQ_pos hh hh1
      hz).le

theorem rate_glue {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter D} {q : D → ℝ} {f : D → E} {S : Set D} {m : ℕ} {r : ℝ}
    (hq : ∀ᶠ z in l, 0 < q z)
    (hleft : JetRate (l ⊓ 𝓟 S) q f m r)
    (hright : JetRate (l ⊓ 𝓟 Sᶜ) q f m r) : JetRate l q f m r := by
  obtain ⟨A, hA, ha⟩ := hleft
  obtain ⟨B, hB, hb⟩ := hright
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  filter_upwards [hq, eventually_inf_principal.mp ha, eventually_inf_principal.mp hb]
    with z hz hza hzb
  by_cases hs : z ∈ S
  · exact (hza hs).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB)
      (Real.rpow_nonneg hz.le _))
  · exact (hzb hs).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA)
      (Real.rpow_nonneg hz.le _))

/-- Bounded approach, bundling `carrier`, `compact`, `in_carrier`, `past` and the required
compatibility proofs. -/
noncomputable def boundedApproach {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {l : Filter SpaceTime} (hl : l ≤ endpoint) (R : ℝ)
    (hR : ∀ᶠ z in l, (cartesianChart h z).2.1 ≤ R) : PhysicalApproach l h 0 R where
  carrier := Metric.closedBall (1, (0 : Space)) 1
  compact := isCompact_closedBall _ _
  in_carrier := endpoint_compact.filter_mono hl
  past := endpoint_past.filter_mono hl
  radial := by
    filter_upwards [endpoint_past.filter_mono hl, hR] with z hz hzR
    exact ⟨X_nonneg hh hh1 hz, hzR⟩
  scale := by
    simpa only [q_eq] using
      (AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl).mono_left hl

/-- Compact physical derivatives and a geometric lower bound control negative
powers. No derivative bound for the output power is assumed. -/
theorem negative_power_le {a q x p : ℝ} (ha : 0 < a) (hq : 0 < q) (hq1 : q ≤ 1)
    (hax : a * q ≤ x) (hp : -2 ≤ p ∧ p ≤ 0) :
    x ^ p ≤ a ^ p * q ^ (-2 : ℝ) := by
  calc
    x ^ p ≤ (a * q) ^ p := Real.rpow_le_rpow_of_nonpos (mul_pos ha hq) hax hp.2
    _ = a ^ p * q ^ p := Real.mul_rpow ha.le hq.le
    _ ≤ a ^ p * q ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hq hq1 hp.1) (Real.rpow_nonneg ha.le _)

/-- Power loss, given by `2 * (2 * (m : ℝ) + 1)`. -/
noncomputable def powerLoss (m : ℕ) : ℝ := 2 * (2 * (m : ℝ) + 1)

theorem powerLoss_nonneg (m : ℕ) : 0 ≤ powerLoss m := by unfold powerLoss; positivity

theorem finiteRate_negative_power {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {l : Filter D} {q f : D → ℝ} {K : Set D}
    (hf : ContDiff ℝ ∞ f) (hK : IsCompact K) (hlK : ∀ᶠ z in l, z ∈ K)
    (hq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1) {a p : ℝ} (ha : 0 < a)
    (hlower : ∀ᶠ z in l, a * q z ≤ f z) (hp : -2 ≤ p ∧ p ≤ 0) (m : ℕ) :
    FiniteJetRate l q (fun z => f z ^ p) m (-powerLoss m) := by
  obtain ⟨D, hD, hd⟩ := finiteRate_compact (q := q) hf hK hlK m
  let C := 1 + D + a ^ p + a⁻¹
  have hap : 0 ≤ a ^ p := Real.rpow_nonneg ha.le _
  have hai : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hpC : a ^ p ≤ C := by dsimp [C]; linarith
  have hiC : a⁻¹ ≤ C := by dsimp [C]; linarith
  have hU : IsOpen {z | 0 < f z} := isOpen_lt continuous_const hf.continuous
  refine ⟨WeightedQuotients.orderBound p m * C ^ (2 * m + 1), by
    exact mul_nonneg (WeightedQuotients.orderBound_nonneg p m) (pow_nonneg (zero_le_one.trans hC)
        _), ?_⟩
  filter_upwards [hq, hlower, hd] with z hz hlo hdz
  have hfp : 0 < f z := (mul_pos ha hz.1).trans_le hlo
  have hqpow : 1 ≤ q z ^ (-2 : ℝ) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hz.1 hz.2 (by norm_num : (-2 : ℝ) ≤ 0)
  have hB : 1 ≤ C * q z ^ (-2 : ℝ) := one_le_mul_of_one_le_of_one_le hC hqpow
  have hpow : f z ^ p ≤ C * q z ^ (-2 : ℝ) :=
    (negative_power_le ha hz.1 hz.2 hlo hp).trans
      (mul_le_mul_of_nonneg_right hpC (Real.rpow_nonneg hz.1.le _))
  have hinv : (f z)⁻¹ ≤ C * q z ^ (-2 : ℝ) := by
    have h := negative_power_le ha hz.1 hz.2 hlo (p := -1) (by constructor <;> norm_num)
    simp only [Real.rpow_neg_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right hiC (Real.rpow_nonneg hz.1.le _))
  have hjet : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f z‖ ≤ C * q z ^ (-2 : ℝ) := by
    intro i hi
    have hiD : ‖iteratedFDeriv ℝ i f z‖ ≤ D := by
        simpa only [Real.rpow_zero, mul_one] using hdz i hi
    exact hiD.trans (hDC.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hqpow))
  intro i hi
  calc
    ‖iteratedFDeriv ℝ i (fun z => f z ^ p) z‖ ≤
        WeightedQuotients.orderBound p m * (C * q z ^ (-2 : ℝ)) ^ (2 * m + 1) :=
      WeightedQuotients.rpow_comp_jets_bound hU hf.contDiffOn (fun _ hx => hx)
        hfp p m hB hpow hinv hjet hi
    _ = (WeightedQuotients.orderBound p m * C ^ (2 * m + 1)) * q z ^ (-powerLoss m) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hz.1.le]
      have he : (-2 : ℝ) * ((2 * m + 1 : ℕ) : ℝ) = -powerLoss m := by
        push_cast
        unfold powerLoss
        ring
      rw [he]
      ring

theorem finiteRate_uniform_comp {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {l : Filter D} {q f : D → ℝ} {U : Set D} (hU : IsOpen U)
    (hlU : ∀ᶠ z in l, z ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) {m : ℕ} {L A : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hgb : ∀ i ≤ m, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ A)
    (hq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1)
    (hr : FiniteJetRate l q f m (-L)) :
    FiniteJetRate l q (g ∘ f) m (-(L * m)) := by
  obtain ⟨C, hC, hc⟩ := hr
  refine ⟨(m.factorial : ℝ) * A * (C + 1) ^ m, by positivity, ?_⟩
  filter_upwards [hlU, hq, hc] with z hz hqz hcz
  have hqpow : 1 ≤ q z ^ (-L) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hqz.1 hqz.2 (neg_nonpos.mpr hL)
  have hB : 1 ≤ (C + 1) * q z ^ (-L) :=
    one_le_mul_of_one_le_of_one_le (by linarith) hqpow
  have hfb : ∀ i, 1 ≤ i → i ≤ m →
      ‖iteratedFDeriv ℝ i f z‖ ≤ (C + 1) * q z ^ (-L) := by
    intro i _ hi
    exact (hcz i hi).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hqz.1.le _))
  intro i hi
  calc
    ‖iteratedFDeriv ℝ i (g ∘ f) z‖ ≤
        (m.factorial : ℝ) * A * ((C + 1) * q z ^ (-L)) ^ m :=
      PhysicalClassBounds.composition_jet_bound hg hU hf hz m hA hB
        (fun j hj => hgb j hj _) hfb i hi
    _ = ((m.factorial : ℝ) * A * (C + 1) ^ m) * q z ^ (-(L * m)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hqz.1.le]
      rw [neg_mul]
      ring

theorem finiteRate_mul {l : Filter SpaceTime} {q f g : SpaceTime → ℝ}
    {U : Set SpaceTime} {m : ℕ} {r s : ℝ}
    (hf : FiniteJetRate l q f m r) (hg : FiniteJetRate l q g m s)
    (hU : IsOpen U) (hlU : ∀ᶠ z in l, z ∈ U) (hq : ∀ᶠ z in l, 0 < q z)
    (hsf : ContDiffOn ℝ ∞ f U) (hsg : ContDiffOn ℝ ∞ g U) :
    FiniteJetRate l q (fun z => f z * g z) m (r + s) := by
  exact finiteRate_bilinear hf hg hU hlU hq hsf hsg (ContinuousLinearMap.mul ℝ ℝ)

/-- Positive radius, given by `{z | 0 < physicalEnergy z}`. -/
noncomputable def positiveRadius : Set SpaceTime := {z | 0 < physicalEnergy z}

theorem positiveRadius_isOpen : IsOpen positiveRadius :=
  isOpen_lt continuous_const physicalEnergy_smooth.continuous

/-- Heat time, given by `2 * (1 - z.1)`. -/
noncomputable def heatTime (z : SpaceTime) : ℝ := 2 * (1 - z.1)

theorem heatTime_smooth : ContDiff ℝ ∞ heatTime :=
  contDiff_const.mul (contDiff_const.sub contDiff_fst)

/-- Heat ratio, given by `heatTime z * physicalEnergy z ^ (-1 : ℝ)`. -/
noncomputable def heatRatio (z : SpaceTime) : ℝ := heatTime z * physicalEnergy z ^ (-1 : ℝ)

theorem energyPower_smooth (p : ℝ) :
    ContDiffOn ℝ ∞ (fun z => physicalEnergy z ^ p) positiveRadius :=
  physicalEnergy_smooth.contDiffOn.rpow_const_of_ne (fun _ hz => hz.ne')

theorem heatRatio_smooth : ContDiffOn ℝ ∞ heatRatio positiveRadius :=
  heatTime_smooth.contDiffOn.mul (energyPower_smooth (-1))

/-- Heat model coefficient as an element of `ℝ`. -/
noncomputable def heatModelCoefficient (C h : ℝ) (z : SpaceTime) : ℝ :=
  (C * (physicalEnergy z ^ RadialHeatProfile.spatialExponent (1 + h) *
    HeatProfileExtension.extension (1 + h) (heatRatio z))) *
    (2 * physicalEnergy z) ^ (-(1 / 2 : ℝ))

theorem doubleEnergyPower_smooth (p : ℝ) :
    ContDiffOn ℝ ∞ (fun z => (2 * physicalEnergy z) ^ p) positiveRadius :=
  (contDiffOn_const.mul physicalEnergy_smooth.contDiffOn).rpow_const_of_ne
    (fun _ hz => mul_ne_zero (by norm_num) hz.ne')

theorem heatModelCoefficient_smooth (C : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (heatModelCoefficient C h) positiveRadius :=
  (contDiffOn_const.mul ((energyPower_smooth _).mul
    ((HeatProfileExtension.extension_contDiff (by linarith : 1 < 1 + h)).comp_contDiffOn
      heatRatio_smooth))).mul (doubleEnergyPower_smooth _)

/-- Heat model velocity, given by `heatModelCoefficient C h z • angularVector z`. -/
noncomputable def heatModelVelocity (C h : ℝ) (z : SpaceTime) : Space :=
  heatModelCoefficient C h z • angularVector z

theorem heatModelCoefficient_eq (C h : ℝ) {z : SpaceTime}
    (ht : z.1 < 1) (hs : 0 < physicalEnergy z) :
    heatModelCoefficient C h z =
      BaseExterior.heatCoefficient C h (AxisymmetricFields.profilePoint z.1 z.2) := by
  have hr : heatRatio z = 2 * (1 - z.1) / physicalEnergy z := by
    simp [heatRatio, heatTime, Real.rpow_neg_one, div_eq_mul_inv]
  have hnonneg : 0 ≤ heatRatio z := by
    rw [hr]
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr ht.le)) hs.le
  rw [heatModelCoefficient, HeatProfileExtension.extension_eq_profile _ hnonneg,
    hr, BaseExterior.heatCoefficient_eq]
  change C * (physicalEnergy z ^ RadialHeatProfile.spatialExponent (1 + h) *
    RadialHeatProfile.profile (1 + h) (2 * (1 - z.1) / physicalEnergy z)) *
    (2 * physicalEnergy z) ^ (-(1 / 2 : ℝ)) =
    C * (physicalEnergy z ^ RadialHeatProfile.spatialExponent (1 + h) *
    RadialHeatProfile.profile (1 + h) (2 * (1 - z.1) / physicalEnergy z)) /
    Real.sqrt (2 * physicalEnergy z)
  rw [Real.rpow_neg (by positivity : 0 ≤ 2 * physicalEnergy z), Real.sqrt_eq_rpow,
    div_eq_mul_inv]
  simp only [div_eq_mul_inv]

theorem heatModelVelocity_eq (C h : ℝ) {z : SpaceTime}
    (ht : z.1 < 1) (hs : 0 < physicalEnergy z) :
    heatModelVelocity C h z = BaseExterior.heatVelocity C h z := by
  rw [BaseExterior.heatVelocity_eq_angularVector]
  exact congrArg (fun c => c • angularVector z) (heatModelCoefficient_eq C h ht hs)

theorem extension_uniform_jets {a : ℝ} (ha : 1 < a) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i ≤ m, ∀ x,
      ‖iteratedFDeriv ℝ i (HeatProfileExtension.extension a) x‖ ≤ A := by
  refine ⟨∑ i ∈ Finset.range (m + 1), HeatProfileExtension.derivativeBound a i,
    Finset.sum_nonneg (fun i _ => HeatProfileExtension.derivativeBound_nonneg a i), ?_⟩
  intro i hi x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (HeatProfileExtension.extension_derivative_bound ha i x).trans
    (Finset.single_le_sum (fun j _ => HeatProfileExtension.derivativeBound_nonneg a j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))

/-- Heat loss, given by `powerLoss m * ((m : ℝ) + 2)`. -/
noncomputable def heatLoss (m : ℕ) : ℝ := powerLoss m * ((m : ℝ) + 2)

theorem heatLoss_eq (m : ℕ) : heatLoss m = (4 * (m : ℝ) + 2) * ((m : ℝ) + 2) := by
  unfold heatLoss powerLoss
  ring

theorem heatLoss_nonneg (m : ℕ) : 0 ≤ heatLoss m :=
  mul_nonneg (powerLoss_nonneg m) (by positivity)

theorem heat_velocity_rate {l : Filter SpaceTime} (hl : l ≤ endpoint)
    {h R : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 < R)
    (hlR : ∀ᶠ z in l, R < (cartesianChart h z).2.1) (C : ℝ) (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ h) (BaseExterior.heatVelocity C h)
      m (-heatLoss m) := by
  let q := PhysicalWaveSum.physicalQ h
  have hq := (endpoint_q_small hh hh1).filter_mono hl
  have hq0 := hq.mono (fun _ hz => hz.1)
  have hK := endpoint_compact.filter_mono hl
  have hlow : ∀ᶠ z in l, R * q z ≤ physicalEnergy z := by
    filter_upwards [hlR, hq] with z hz hqz
    exact ((lt_div_iff₀ hqz.1).mp (by simpa only [X_eq] using hz)).le
  have hlU : ∀ᶠ z in l, z ∈ positiveRadius := by
    filter_upwards [hlow, hq] with z hz hqz
    exact (mul_pos hR hqz.1).trans_le hz
  have hi := finiteRate_negative_power physicalEnergy_smooth (isCompact_closedBall _ _) hK hq
    hR hlow (p := -1) (by constructor <;> norm_num) m
  have ht := finiteRate_compact (q := q) heatTime_smooth (isCompact_closedBall _ _) hK m
  have hr : FiniteJetRate l q heatRatio m (-powerLoss m) := by
    have he := finiteRate_mul ht hi positiveRadius_isOpen hlU hq0
      heatTime_smooth.contDiffOn (energyPower_smooth (-1))
    simp only [zero_add] at he
    exact he
  obtain ⟨A, hA, ha⟩ := extension_uniform_jets (by linarith : 1 < 1 + h) m
  have he := finiteRate_uniform_comp positiveRadius_isOpen hlU heatRatio_smooth
    (HeatProfileExtension.extension (1 + h)) (HeatProfileExtension.extension_contDiff (by linarith))
    (powerLoss_nonneg m) hA ha hq hr
  have hp := finiteRate_negative_power physicalEnergy_smooth (isCompact_closedBall _ _) hK hq
    hR hlow (p := RadialHeatProfile.spatialExponent (1 + h))
    (by unfold RadialHeatProfile.spatialExponent; constructor <;> linarith) m
  have hs := (energyPower_smooth (RadialHeatProfile.spatialExponent (1 + h))).mul
    ((HeatProfileExtension.extension_contDiff (by linarith : 1 < 1 + h)).comp_contDiffOn
      heatRatio_smooth)
  have hpe := finiteRate_mul hp he positiveRadius_isOpen hlU hq0 (energyPower_smooth _)
    ((HeatProfileExtension.extension_contDiff (by linarith : 1 < 1 + h)).comp_contDiffOn
      heatRatio_smooth)
  have hC := scalarConst_rate hpe positiveRadius_isOpen hlU hs C
  have hlow2 : ∀ᶠ z in l, (2 * R) * q z ≤ 2 * physicalEnergy z := by
    filter_upwards [hlow] with z hz
    nlinarith
  have hd := finiteRate_negative_power (contDiff_const.mul physicalEnergy_smooth)
    (isCompact_closedBall _ _) hK hq (mul_pos (by norm_num) hR) hlow2
    (p := -(1 / 2 : ℝ)) (by constructor <;> norm_num) m
  have hc : FiniteJetRate l q (heatModelCoefficient C h) m (-heatLoss m) := by
    convert! finiteRate_mul hC hd positiveRadius_isOpen hlU hq0
      (contDiffOn_const.mul hs) (doubleEnergyPower_smooth _) using 1
    dsimp only [heatModelCoefficient, heatLoss, Function.comp_apply]
    ring
  have hv : FiniteJetRate l q (heatModelVelocity C h) m (-heatLoss m) := by
    have he := finiteRate_bilinear hc
      (finiteRate_compact (q := q) angularVector_smooth (isCompact_closedBall _ _) hK m)
      positiveRadius_isOpen hlU hq0 (heatModelCoefficient_smooth C hh)
      angularVector_smooth.contDiffOn (ContinuousLinearMap.lsmul ℝ ℝ)
    simp only [add_zero] at he
    exact he
  apply finiteRate_congr_on hv (BaseExterior.cartesianExterior_isOpen hh hh1 R)
    (show ∀ᶠ z in l, z ∈ BaseExterior.cartesianExterior h R from
      (endpoint_past.filter_mono hl).and hlR)
  intro z hz
  have hpq := PhysicalWaveSum.physicalQ_pos hh hh1 hz.1
  have hxs : 0 < physicalEnergy z := (mul_pos hR hpq).trans
    ((lt_div_iff₀ hpq).mp (by simpa only [X_eq] using hz.2))
  exact heatModelVelocity_eq C h hz.1 hxs

theorem monomial_rate {l : Filter SpaceTime} {h lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {f : Inner → ℝ} (hf : ContDiff ℝ ∞ f) (b : ℝ) (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ h) (cartesianMonomial h b f) m (b - m) := by
  have hq := A.positive_small hh hh1
  apply finiteJetRate_of_jetRate (hq.mono (fun _ hz => hz.1))
  intro i hii
  obtain ⟨C, hC, hb⟩ := cartesian_monomial_bound hh hh1 hf b lo hi A.compact i
  have hr : JetRate l (PhysicalWaveSum.physicalQ h) (cartesianMonomial h b f) i (b - i) := by
    refine ⟨C, hC.le, ?_⟩
    filter_upwards [A.in_carrier, A.past, A.radial, hq] with z hz ht hX hqz
    exact hb z hz ht hqz.2 hX
  exact hr.weaken hq (sub_le_sub_left (by exact_mod_cast hii) b)

/-- Leading velocity, given by `(C⁻¹ * cartesianMonomial h (-CoordinateAlgebra.A h - 1 / 2)
(d.phi 0) z) • angularVector z`. -/
noncomputable def leadingVelocity (h C : ℝ) (d : Coefficients) (z : SpaceTime) : Space :=
  (C⁻¹ * cartesianMonomial h (-CoordinateAlgebra.A h - 1 / 2) (d.phi 0) z) • angularVector z

theorem leadingVelocity_eq (h C : ℝ) (d : Coefficients) (z : SpaceTime) :
    leadingVelocity h C d z =
      AxisymmetricResidual.velocity (fun _ => 0) (BaseExterior.leadingAngular h C d)
        (fun _ => 0) z := by
  ext i
  fin_cases i <;>
    simp [leadingVelocity, AxisymmetricResidual.velocity, AxisymmetricResidual.componentX,
      AxisymmetricResidual.componentY, AxisymmetricResidual.lift, AxisymmetricResidual.pack,
      BaseExterior.leadingAngular, cartesianMonomial, angularVector, coordinateVector, Fin.ext_iff]
          <;> ring

theorem leadingVelocity_rate {l : Filter SpaceTime} {h C lo hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (A : PhysicalApproach l h lo hi)
    {d : Coefficients} (hd : SmoothCoefficients d) (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ h) (leadingVelocity h C d)
      m (-CoordinateAlgebra.A h - 1 / 2 - m) := by
  have hp : ∀ᶠ z in l, z ∈ past := A.past.mono (fun _ hz => ⟨hz, mem_univ _⟩)
  have hs : ContDiffOn ℝ ∞ (cartesianMonomial h (-CoordinateAlgebra.A h - 1 / 2) (d.phi 0)) past :=
    fun _ hz => (cartesianMonomial_smoothAt hh hh1 hz.1 (hd.phi 0).contDiffAt).contDiffWithinAt
  have hr := scalarConst_rate (monomial_rate hh hh1 A (hd.phi 0)
    (-CoordinateAlgebra.A h - 1 / 2) m) past_isOpen hp hs C⁻¹
  have he := finiteRate_bilinear hr
    (finiteRate_compact (q := PhysicalWaveSum.physicalQ h) angularVector_smooth A.compact
        A.in_carrier m)
    past_isOpen hp ((A.positive_small hh hh1).mono (fun _ hz => hz.1))
    (contDiffOn_const.mul hs) angularVector_smooth.contDiffOn (ContinuousLinearMap.lsmul ℝ ℝ)
  simp only [add_zero] at he
  exact he

theorem restricted_mem {D : Type*} (l : Filter D) (S : Set D) :
    ∀ᶠ z in l ⊓ 𝓟 S, z ∈ S :=
  eventually_inf_principal.mpr (Eventually.of_forall (fun _ hz => hz))

theorem heatLoss_controls_core {h : ℝ} (hh1 : h < 1 / 2) (m : ℕ) :
    -heatLoss m ≤ -CoordinateAlgebra.A h - 2 * ((m : ℝ) + 1) := by
  unfold heatLoss powerLoss CoordinateAlgebra.A
  have hm : 0 ≤ (m : ℝ) := by positivity
  nlinarith [sq_nonneg (m : ℝ)]

theorem heatLoss_controls_middle {h : ℝ} (hh1 : h < 1 / 2) (m : ℕ) :
    -heatLoss m ≤ -CoordinateAlgebra.A h - 1 / 2 - m := by
  have hc := heatLoss_controls_core hh1 m
  have hm : 0 ≤ (m : ℝ) := by positivity
  linarith

theorem heatLoss_mono {n m : ℕ} (hnm : n ≤ m) : heatLoss n ≤ heatLoss m := by
  unfold heatLoss powerLoss
  gcongr

section Actual

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)

/-- The support and zero-mass identities are consequences of the actual
coefficient construction, not hypotheses on the final velocity. -/
theorem actual_exterior_coefficients :
    BaseExterior.ExteriorCoefficients (FinalSlowBase.coefficients H v)
      (AssembledSlowBase.nominalOuterX W) := by
  have hd := FinalSlowBase.realizesScheme H v
  have hb := EntranceAlignedBase.modulated_base_eq H v
  have ho := EntranceAlignedBase.modulated_outer H v
  constructor
  · intro n p hp heta
    exact ModulatedExterior.realized_axial_zero_all W v.profiles v.finiteModification hd hb ho
      n hp.le (abs_le.mpr heta)
  · intro n p hp heta
    exact ModulatedExterior.realized_primitive_zero_all W v.profiles v.finiteModification hd hb ho
      n hp.le (abs_le.mpr heta)
  · intro n hn p hp _
    exact (ModulatedExterior.realized_positive_exterior W v.profiles v.finiteModification hd ho hn
        hp.le).1
  · intro n hn p hp _
    exact (ModulatedExterior.realized_positive_exterior W v.profiles v.finiteModification hd ho hn
        hp.le).2.2

theorem actual_leading_eq (upper : ℝ) (B : ℕ) :
    EqOn (FinalSlowBase.velocity H v upper B)
      (leadingVelocity F.data.h W.axis.normalization (FinalSlowBase.coefficients H v))
      (BaseExterior.cartesianExterior F.data.h (AssembledSlowBase.nominalOuterX W)) := by
  intro z hz
  rw [leadingVelocity_eq]
  exact BaseExterior.exterior_velocity_eq_leading (FinalSlowBase.scales_strictMono H v upper B)
    F.data.h_pos F.data.h_lt_half (AssembledSlowBase.nominalOuterX_pos W).le
    (FinalSlowBase.coefficients_smooth H v) (actual_exterior_coefficients H v) hz

theorem actual_bounded_rate (upper : ℝ) (B : ℕ) {l : Filter SpaceTime}
    (hl : l ≤ endpoint)
    (hbox : ∀ᶠ z in l, (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper)
    (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.velocity H v upper B)
      m (-CoordinateAlgebra.A F.data.h - 2 * ((m : ℝ) + 1)) := by
  let A := boundedApproach F.data.h_pos F.data.h_lt_half hl (FinalSlowBase.boxRadius W upper) hbox
  have hp : ∀ᶠ z in l, z ∈ past := A.past.mono (fun _ hz => ⟨hz, mem_univ _⟩)
  have hq := A.positive_small F.data.h_pos F.data.h_lt_half
  have hd := FinalSlowBase.coefficients_smooth H v
  have ha := FinalSlowBase.scales_admissible H v upper B
  have hr := velocity_prefix_rate F.data.h_pos F.data.h_lt_half A hd ha m m (by omega)
  have hs := prefixVelocity_growth (C := W.axis.normalization) F.data.h_pos F.data.h_lt_half A hd m
      m
  have hr' := finiteRate_weaken hr hq (show -CoordinateAlgebra.A F.data.h - 2 * ((m : ℝ) + 1) ≤
      F.data.h * ((m : ℝ) + 1) - CoordinateAlgebra.A F.data.h - 2 * ((m : ℝ) + 1) by
    have hm : 0 ≤ F.data.h * ((m : ℝ) + 1) := mul_nonneg F.data.h_pos.le (by positivity)
    linarith)
  have hs' := finiteRate_weaken hs hq (show -CoordinateAlgebra.A F.data.h - 2 * ((m : ℝ) + 1) ≤
      -CoordinateAlgebra.A F.data.h - ((m : ℝ) + 1) by
    have hm : 0 ≤ (m : ℝ) := by positivity
    linarith)
  have hsum := finiteRate_add hr' hs' past_isOpen hp
    ((FinalSlowBase.velocity_smooth H v upper B).sub
      (prefixVelocity_smooth F.data.h_pos F.data.h_lt_half hd m W.axis.normalization))
    (prefixVelocity_smooth F.data.h_pos F.data.h_lt_half hd m W.axis.normalization)
  simp only [sub_add_cancel] at hsum
  exact hsum

theorem actual_middle_rate (upper : ℝ) (B : ℕ) {l : Filter SpaceTime}
    (hl : l ≤ endpoint) {R : ℝ}
    (hR : ∀ᶠ z in l, (cartesianChart F.data.h z).2.1 ≤ R)
    (houter : ∀ᶠ z in l, AssembledSlowBase.nominalOuterX W < (cartesianChart F.data.h z).2.1)
    (m : ℕ) :
    FiniteJetRate l (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.velocity H v upper B)
      m (-CoordinateAlgebra.A F.data.h - 1 / 2 - m) := by
  let A := boundedApproach F.data.h_pos F.data.h_lt_half hl R hR
  have hr := leadingVelocity_rate (C := W.axis.normalization) F.data.h_pos F.data.h_lt_half A
    (FinalSlowBase.coefficients_smooth H v) m
  exact finiteRate_congr_on hr
    (BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _)
    ((endpoint_past.filter_mono hl).and houter) (actual_leading_eq H v upper B).symm

/-- The entire region outside the coefficient support, including unbounded
similarity radii, has one fixed polynomial loss. -/
theorem actual_outer_rate (upper : ℝ) (B : ℕ) {l : Filter SpaceTime}
    (hl : l ≤ endpoint)
    (houter : ∀ᶠ z in l, AssembledSlowBase.nominalOuterX W < (cartesianChart F.data.h z).2.1)
    (m : ℕ) :
    JetRate l (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.velocity H v upper B)
      m (-heatLoss m) := by
  let S : Set SpaceTime := {z | (cartesianChart F.data.h z).2.1 ≤
      BaseExterior.nominalExteriorRadius W}
  have hq := (endpoint_q_small F.data.h_pos F.data.h_lt_half).filter_mono hl
  apply rate_glue (S := S) (hq.mono (fun _ hz => hz.1))
  · have hl' : l ⊓ 𝓟 S ≤ endpoint := inf_le_left.trans hl
    have hR : ∀ᶠ z in l ⊓ 𝓟 S,
        (cartesianChart F.data.h z).2.1 ≤ BaseExterior.nominalExteriorRadius W := restricted_mem l S
    have hr := actual_middle_rate H v upper B hl' hR (houter.filter_mono inf_le_left) m
    exact (finiteRate_at hr le_rfl).weaken (hq.filter_mono inf_le_left)
      (heatLoss_controls_middle F.data.h_lt_half m)
  · have hl' : l ⊓ 𝓟 Sᶜ ≤ endpoint := inf_le_left.trans hl
    have hR : ∀ᶠ z in l ⊓ 𝓟 Sᶜ,
        BaseExterior.nominalExteriorRadius W < (cartesianChart F.data.h z).2.1 :=
      (restricted_mem l Sᶜ).mono (fun _ hz => lt_of_not_ge hz)
    have hr := heat_velocity_rate hl' F.data.h_pos F.data.h_lt_half
      (BaseExterior.nominalExteriorRadius_pos W) hR (BaseExterior.nominalHeatNormalization W) m
    have ha := finiteRate_congr_on hr
      (BaseExterior.cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half _)
      ((endpoint_past.filter_mono hl').and hR) (FinalSlowBase.exterior_fields_eq_heat H v upper
          B).1.symm
    exact finiteRate_at ha le_rfl

theorem outer_lt_box (upper : ℝ) :
    AssembledSlowBase.nominalOuterX W < FinalSlowBase.boxRadius W upper := by
  rw [FinalSlowBase.boxRadius_eq]
  exact (ConstructedSlowBase.outer_before_upper W).trans_le (le_max_right _ _)

/-- Full physical endpoint estimate for the actual constructed base.  The
universal loss `(4*m+2)*(m+2)` depends only on derivative order.  Constants
and the eventual neighborhood may depend on the fixed base data. -/
theorem velocity_rate (upper : ℝ) (B m : ℕ) :
    JetRate endpoint (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.velocity H v upper B)
      m (-heatLoss m) := by
  let S : Set SpaceTime := {z | (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper}
  have hq := endpoint_q_small F.data.h_pos F.data.h_lt_half
  apply rate_glue (S := S) (hq.mono (fun _ hz => hz.1))
  · have hr := actual_bounded_rate H v upper B (show endpoint ⊓ 𝓟 S ≤ endpoint from inf_le_left)
      (show ∀ᶠ z in endpoint ⊓ 𝓟 S,
        (cartesianChart F.data.h z).2.1 ≤ FinalSlowBase.boxRadius W upper from restricted_mem
            endpoint S) m
    exact (finiteRate_at hr le_rfl).weaken (hq.filter_mono inf_le_left)
      (heatLoss_controls_core F.data.h_lt_half m)
  · apply actual_outer_rate H v upper B inf_le_left _ m
    exact (restricted_mem endpoint Sᶜ).mono (fun _ hz =>
      (outer_lt_box (W := W) upper).trans (lt_of_not_ge hz))

/-- A common constant and neighborhood control the entire finite jet. -/
theorem velocity_finite_rate (upper : ℝ) (B m : ℕ) :
    FiniteJetRate endpoint (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.velocity H v upper B)
      m (-heatLoss m) := by
  have hq := endpoint_q_small F.data.h_pos F.data.h_lt_half
  apply finiteJetRate_of_jetRate (hq.mono (fun _ hz => hz.1))
  intro i hi
  exact (velocity_rate H v upper B i).weaken hq (neg_le_neg (heatLoss_mono hi))

/-- Public statement with the endpoint filter and existential loss explicit. -/
theorem exists_fixed_loss (upper : ℝ) (B : ℕ) :
    ∀ m : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
        (PhysicalWaveSum.physicalQ F.data.h) (FinalSlowBase.velocity H v upper B) m (-L) := by
  intro m
  exact ⟨heatLoss m, heatLoss_nonneg m, velocity_rate H v upper B m⟩

end Actual

end NavierStokes.ActualBaseVelocityBounds
