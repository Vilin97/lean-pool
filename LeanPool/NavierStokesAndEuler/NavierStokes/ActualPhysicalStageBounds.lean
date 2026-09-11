/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualIterationLedger
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedCandidateAssembly
import LeanPool.NavierStokesAndEuler.NavierStokes.LocalMeanPhysicalBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalStageBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.FinalSlowBase
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalWaveSum
import LeanPool.NavierStokesAndEuler.NavierStokes.AnnularEndpoint

/-!
# Physical stage estimates from the actual native mean region

Mean families are supplied on the original normalized region `(1/2,2)`.
Only native smoothness, support, and class estimates are input. The
physical stage bounds and the initialized velocity estimate are derived.
-/

section

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

end
end

end

section

/-!
# Initial physical velocity bounds from the actual base and native data

The base potential is the anchored `TailGaugePotential.finalPotential`.
Its curl is the constructed `FinalSlowBase.velocity`.  Only the finite
initialization potential pays the derivative used by the curl estimate;
no growth estimate on the base potential or its gauge is required.
-/

section

/-!
# Finite background bounds from the raw increments

The raw-stage interface starts at index one. A bound for the actual
initialized stage is therefore kept explicit. Together with the raw
increment bounds it controls every finite prefix with one derivative-loss
function, independent of the number of correction stages.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.MixedFiniteBackground

open Set Filter DiagonalResidual ProblemStatement
open scoped ContDiff Topology BigOperators

section General

variable {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem raw_jetRate {l : Filter D} {q : D → ℝ} {A : ℕ → D → V}
    {g L : ℕ → ℝ} {C : ℕ → ℕ → ℝ} {S : Set D}
    (hraw : CutStageEstimates.RawStageBounds q A g L C (fun _ _ => 0) S)
    (hS : ∀ᶠ x in l, x ∈ S) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    {j : ℕ} (hj : 1 ≤ j) (m : ℕ) :
    JetRate l q (A j) m (g j - L m) := by
  refine ⟨max (C j m) 0, le_max_right _ _, ?_⟩
  filter_upwards [hS, hq] with x hx hqx
  have hb : ‖iteratedFDeriv ℝ m (A j) x‖ ≤ C j m * q x ^ (g j - L m) := by
    simpa only [Real.rpow_zero, mul_one] using hraw j hj m x hx hqx.2
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg hqx.1.le _))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedSpace ℝ V] in
theorem uncutPrefix_succ (A : ℕ → D → V) (N : ℕ) :
    DiagonalJetBounds.uncutPrefix A (N + 1) =
      fun x => DiagonalJetBounds.uncutPrefix A N x + A N x := by
  funext x
  exact Finset.sum_range_succ (fun j => A j x) N

theorem nonemptyPrefix_jetRate {l : Filter D} {q : D → ℝ} {A : ℕ → D → V}
    {U : Set D} {m : ℕ} {r : ℝ}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hzero : JetRate l q (A 0) m r)
    (hpos : ∀ j, 1 ≤ j → JetRate l q (A j) m r) (J : ℕ) :
    JetRate l q (DiagonalJetBounds.uncutPrefix A (J + 1)) m r := by
  induction J with
  | zero =>
    have he : DiagonalJetBounds.uncutPrefix A (0 + 1) = A 0 := by
      funext x
      simp [DiagonalJetBounds.uncutPrefix]
    rw [he]
    exact hzero
  | succ J ih =>
    rw [show J.succ + 1 = (J + 1) + 1 from rfl, uncutPrefix_succ]
    exact ih.add (hpos (J + 1) (by omega)) hU hlU
      (ContDiffOn.sum (fun j _ => hA j)) (hA (J + 1))

theorem prefix_background {l : Filter D} {q : D → ℝ} {A : ℕ → D → V}
    {g L Lzero : ℕ → ℝ} {C : ℕ → ℕ → ℝ} {U S : Set D}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hS : ∀ᶠ x in l, x ∈ S) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hraw : CutStageEstimates.RawStageBounds q A g L C (fun _ _ => 0) S)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hzero : ∀ m, JetRate l q (A 0) m (-Lzero m)) (J m : ℕ) :
    JetRate l q (DiagonalJetBounds.uncutPrefix A (J + 1)) m (-max (L m) (Lzero m)) := by
  apply nonemptyPrefix_jetRate hU hlU hA
  · exact (hzero m).weaken hq (neg_le_neg (le_max_right _ _))
  · intro j hj
    apply (raw_jetRate hraw hS hq hj m).weaken hq
    have hmax := le_max_left (L m) (Lzero m)
    have hgain := hg j hj
    linarith

end General

/-- The one derivative needed for the potential is paid independently of
the correction index. The direct field pays no curl derivative. -/
noncomputable def backgroundLoss (LA LB LAzero LBzero : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (max (LA (m + 1)) (LAzero (m + 1))) (max (LB m) (LBzero m))

theorem mixed_background {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {A B : ℕ → VelocityField} {g LA LB LAzero LBzero : ℕ → ℝ}
    {CA CB : ℕ → ℕ → ℝ} {U S : Set SpaceTime}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hS : ∀ᶠ x in l, x ∈ S) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hrawA : CutStageEstimates.RawStageBounds q A g LA CA (fun _ _ => 0) S)
    (hrawB : CutStageEstimates.RawStageBounds q B g LB CB (fun _ _ => 0) S)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hzeroA : ∀ m, JetRate l q (A 0) m (-LAzero m))
    (hzeroB : ∀ m, JetRate l q (B 0) m (-LBzero m)) (J m : ℕ) :
    JetRate l q (MixedDiagonalResidual.uncutVelocity A B J) m
      (-backgroundLoss LA LB LAzero LBzero m) := by
  have hpA := prefix_background hU hlU hS hq hA hrawA hg hzeroA J (m + 1)
  have hpB := prefix_background hU hlU hS hq hB hrawB hg hzeroB J m
  have hsA : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix A (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hA j)
  have hsB : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix B (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hB j)
  have hc := (hpA.spatialCurl hU hlU hsA).weaken hq
    (neg_le_neg (le_max_left (max (LA (m + 1)) (LAzero (m + 1))) (max (LB m) (LBzero m))))
  have hb := hpB.weaken hq
    (neg_le_neg (le_max_right (max (LA (m + 1)) (LAzero (m + 1))) (max (LB m) (LBzero m))))
  have hsCurl : ContDiffOn ℝ ∞
      (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1))) U := by
    intro x hx
    exact (SpatialCurl.contDiffAt_spatialCurl (hsA.contDiffAt (hU.mem_nhds hx))
      (by simp)).contDiffWithinAt
  exact hc.add hb hU hlU hsCurl hsB

/-- Stage velocity, defined pointwise by `SpatialCurl.spatialCurl (A j) x + B j x`. -/
noncomputable def stageVelocity (A B : ℕ → VelocityField) (j : ℕ) : VelocityField :=
  fun x => SpatialCurl.spatialCurl (A j) x + B j x

theorem uncutVelocity_zero (A B : ℕ → VelocityField) :
    MixedDiagonalResidual.uncutVelocity A B 0 = stageVelocity A B 0 := by
  have hA : DiagonalJetBounds.uncutPrefix A (0 + 1) = A 0 := by
    funext x
    simp [DiagonalJetBounds.uncutPrefix]
  have hB : DiagonalJetBounds.uncutPrefix B (0 + 1) = B 0 := by
    funext x
    simp [DiagonalJetBounds.uncutPrefix]
  funext x
  change SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (0 + 1)) x +
    DiagonalJetBounds.uncutPrefix B (0 + 1) x =
    SpatialCurl.spatialCurl (A 0) x + B 0 x
  rw [hA, hB]

theorem uncutVelocity_eq_stagePrefix {U : Set SpaceTime} (hU : IsOpen U)
    (A B : ℕ → VelocityField) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (J : ℕ) :
    EqOn (MixedDiagonalResidual.uncutVelocity A B J)
      (DiagonalJetBounds.uncutPrefix (stageVelocity A B) (J + 1)) U := by
  intro x hx
  have hcurl := PhysicalParticularWave.spatialCurl_finset_sum (Finset.range (J + 1)) A
    (fun j _ => (hA j).contDiffAt (hU.mem_nhds hx) |>.differentiableAt (by simp))
  change SpatialCurl.spatialCurl (fun w => ∑ i ∈ Finset.range (J + 1), A i w) x +
    (∑ i ∈ Finset.range (J + 1), B i x) =
    ∑ i ∈ Finset.range (J + 1), (SpatialCurl.spatialCurl (A i) x + B i x)
  rw [hcurl]
  rw [Finset.sum_add_distrib]

/-- This version only needs a bound for the initialized physical velocity.
It imposes no growth assumption on the gauge of the initial potential. -/
noncomputable def initialBackgroundLoss (Lzero LA LB : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (Lzero m) (max (LA (m + 1)) (LB m))

theorem mixed_background_from_initial {l : Filter SpaceTime} {q : SpaceTime → ℝ}
    {A B : ℕ → VelocityField} {g LA LB Lzero : ℕ → ℝ}
    {CA CB : ℕ → ℕ → ℝ} {U S : Set SpaceTime}
    (hU : IsOpen U) (hlU : ∀ᶠ x in l, x ∈ U)
    (hS : ∀ᶠ x in l, x ∈ S) (hq : ∀ᶠ x in l, 0 < q x ∧ q x ≤ 1)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hrawA : CutStageEstimates.RawStageBounds q A g LA CA (fun _ _ => 0) S)
    (hrawB : CutStageEstimates.RawStageBounds q B g LB CB (fun _ _ => 0) S)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hzero : ∀ m, JetRate l q (MixedDiagonalResidual.uncutVelocity A B 0) m (-Lzero m))
    (J m : ℕ) :
    JetRate l q (MixedDiagonalResidual.uncutVelocity A B J) m
      (-initialBackgroundLoss Lzero LA LB m) := by
  have hLzero : Lzero m ≤ initialBackgroundLoss Lzero LA LB m := le_max_left _ _
  have hLA : LA (m + 1) ≤ initialBackgroundLoss Lzero LA LB m :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hLB : LB m ≤ initialBackgroundLoss Lzero LA LB m :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hcurl (j : ℕ) : ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl (A j)) U := by
    intro x hx
    exact (SpatialCurl.contDiffAt_spatialCurl ((hA j).contDiffAt (hU.mem_nhds hx))
      (by simp)).contDiffWithinAt
  have hstage (j : ℕ) : ContDiffOn ℝ ∞ (stageVelocity A B j) U :=
    (hcurl j).add (hB j)
  have hinit : JetRate l q (stageVelocity A B 0) m
      (-initialBackgroundLoss Lzero LA LB m) := by
    have hz := (hzero m).weaken hq (neg_le_neg hLzero)
    rwa [uncutVelocity_zero] at hz
  have hpos (j : ℕ) (hj : 1 ≤ j) : JetRate l q (stageVelocity A B j) m
      (-initialBackgroundLoss Lzero LA LB m) := by
    have hgain := hg j hj
    have ha := ((raw_jetRate hrawA hS hq hj (m + 1)).spatialCurl hU hlU (hA j)).weaken hq
      (show -initialBackgroundLoss Lzero LA LB m ≤ g j - LA (m + 1) by linarith)
    have hb := (raw_jetRate hrawB hS hq hj m).weaken hq
      (show -initialBackgroundLoss Lzero LA LB m ≤ g j - LB m by linarith)
    exact ha.add hb hU hlU (hcurl j) (hB j)
  exact (nonemptyPrefix_jetRate hU hlU hstage hinit hpos J).congr_on hU hlU
    (uncutVelocity_eq_stagePrefix hU A B hA J).symm

end NavierStokes.MixedFiniteBackground

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.InitializedPhysicalBackground

open Set Filter ProblemStatement DiagonalResidual PhysicalStageBounds
open scoped Topology ContDiff BigOperators

/-- The loss for the actual finite initialization potential, before curl.
The offsets absorb its own native homogeneity, without a positivity
assumption on the initialization gain. -/
noncomputable def seedPotentialLoss (h waveAlpha waveShift meanAlpha : ℝ) (m : ℕ) : ℝ :=
  potentialLoss h (-(h * waveAlpha + waveShift)) (-(h * meanAlpha)) m

/-- Seed direct loss, given by `directLoss h (-(h * meanAlpha)) m`. -/
noncomputable def seedDirectLoss (h meanAlpha : ℝ) (m : ℕ) : ℝ :=
  directLoss h (-(h * meanAlpha)) m

/-- This loss depends only on fixed initialization data and derivative
order. It has no later correction-stage parameter. -/
noncomputable def initialLoss (h waveAlpha waveShift potentialAlpha directAlpha : ℝ)
    (m : ℕ) : ℝ :=
  max (ActualBaseVelocityBounds.heatLoss m)
    (max (seedPotentialLoss h waveAlpha waveShift potentialAlpha (m + 1))
      (seedDirectLoss h directAlpha m))

theorem initialLoss_nonneg (h waveAlpha waveShift potentialAlpha directAlpha : ℝ)
    (m : ℕ) : 0 ≤ initialLoss h waveAlpha waveShift potentialAlpha directAlpha m :=
  (ActualBaseVelocityBounds.heatLoss_nonneg m).trans (le_max_left _ _)

theorem endpoint_sublevel {h qbig : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (hqbig : 0 < qbig) :
    ∀ᶠ w in ActualBaseVelocityBounds.endpoint,
      w ∈ CutStageEstimates.physicalSublevel h qbig := by
  have ht := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  filter_upwards [ActualBaseVelocityBounds.endpoint_past,
    ht.eventually (gt_mem_nhds hqbig)] with w hw hqw
  exact ⟨hw, hqw⟩

theorem spatialCurl_add_on {U : Set SpaceTime} (hU : IsOpen U)
    {A B : VelocityField} (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) :
    EqOn (SpatialCurl.spatialCurl (fun w => A w + B w))
      (fun w => SpatialCurl.spatialCurl A w + SpatialCurl.spatialCurl B w) U := by
  intro w hw
  have ha := ResidualStability.spatialSlice_differentiable hU hA hw
  have hb := ResidualStability.spatialSlice_differentiable hU hB hw
  change SpatialCurl.curlLinear
    (fderiv ℝ (fun y => A (w.1, y) + B (w.1, y)) w.2) = _
  rw [fderiv_fun_add ha hb, map_add]
  rfl

theorem spatialCurl_smoothOn {U : Set SpaceTime} (hU : IsOpen U)
    {A : VelocityField} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (SpatialCurl.spatialCurl A) U := by
  intro w hw
  exact (SpatialCurl.contDiffAt_spatialCurl (hA.contDiffAt (hU.mem_nhds hw))
    (by simp)).contDiffWithinAt

section NativeInitialization

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}

/-- This applies the actual native-copy estimate at initialization, where
the positive-stage `RawStageBounds` interface is not available. -/
theorem potentialIncrement_rate (WA : WaveData h D I K (Fin 3))
    (MA : MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqbig : 0 < qbig) (hq : qbig ≤ ChartScales.Q MA.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      (potentialIncrement WA MA) m
      (-seedPotentialLoss h WA.alpha WA.shift MA.alpha m) := by
  obtain ⟨C, hC, hb⟩ := potentialIncrement_bound
    (g := 0) (waveOffset := -(h * WA.alpha + WA.shift)) (meanOffset := -(h * MA.alpha))
    WA MA hh hh1 hq (by linarith) (by linarith) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  simpa only [seedPotentialLoss, zero_sub] using hb w hw hqw.2

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem directIncrement_rate (MB : MeanData h (CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqbig : 0 < qbig) (hq : qbig ≤ ChartScales.Q MB.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      MB.family.angularField m (-seedDirectLoss h MB.alpha m) := by
  obtain ⟨C, hC, hb⟩ := MB.angular_bound_with_gain
    (g := 0) (delta := -(h * MB.alpha)) hh hh1 hq (by linarith) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  simpa only [seedDirectLoss, directLoss, zero_sub] using hb w hw hqw.2

end NativeInitialization

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- Initialized potential, defined pointwise by `TailGaugePotential.finalPotential H v upper B w
+ potentialIncrement WA MA w`. -/
noncomputable def initializedPotential (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2)) : VelocityField :=
  fun w => TailGaugePotential.finalPotential H v upper B w + potentialIncrement WA MA w

/-- Literal curl of the initialized potential plus the direct angular
initialization. The latter is not differentiated as a potential. -/
noncomputable def initializedVelocity (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h)) : VelocityField :=
  fun w => SpatialCurl.spatialCurl (initializedPotential H v upper B WA MA) w +
    MB.family.angularField w

theorem initializedPotential_smooth (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q MA.firstBand) :
    ContDiffOn ℝ ∞ (initializedPotential H v upper B WA MA)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
  ((TailGaugePotential.finalPotential_smooth H v upper B).mono
    (fun _ hw => ⟨hw.1, mem_univ _⟩)).add
      (potentialIncrement_smooth WA MA F.data.h_pos F.data.h_lt_half hq)

/-- The only use of the anchored gauge is its proved equality of curls. -/
theorem initializedVelocity_decomposition (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q MA.firstBand) :
    EqOn (initializedVelocity H v upper B WA MA MB)
      (fun w => FinalSlowBase.velocity H v upper B w +
        SpatialCurl.spatialCurl (potentialIncrement WA MA) w + MB.family.angularField w)
      (CutStageEstimates.physicalSublevel F.data.h qbig) := by
  have hbase : ContDiffOn ℝ ∞ (TailGaugePotential.finalPotential H v upper B)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
    (TailGaugePotential.finalPotential_smooth H v upper B).mono
      (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hinc := potentialIncrement_smooth WA MA F.data.h_pos F.data.h_lt_half hq
  intro w hw
  unfold initializedVelocity initializedPotential
  rw [spatialCurl_add_on (CutStageEstimates.physicalSublevel_open F.data.h_pos
    F.data.h_lt_half qbig) hbase hinc hw]
  dsimp only
  rw [TailGaugePotential.finalPotential_sameCurl H v upper B hw.1]

theorem initializedVelocity_smooth (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h))
    {qbig : ℝ} (hqA : qbig ≤ ChartScales.Q MA.firstBand)
    (hqB : qbig ≤ ChartScales.Q MB.firstBand) :
    ContDiffOn ℝ ∞ (initializedVelocity H v upper B WA MA MB)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
  (spatialCurl_smoothOn (CutStageEstimates.physicalSublevel_open F.data.h_pos
    F.data.h_lt_half qbig) (initializedPotential_smooth H v upper B WA MA hqA)).add
      (MB.angular_smooth F.data.h_pos F.data.h_lt_half hqB)

/-- Initial physical velocity bound from native initialization data and
the actual constructed base. There is no initial-velocity rate premise. -/
theorem initializedVelocity_rate (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h)) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (initializedVelocity H v upper B WA MA MB) m
      (-initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha m) := by
  let qbig := min (ChartScales.Q MA.firstBand) (ChartScales.Q MB.firstBand)
  have hqbig : 0 < qbig := lt_min (ChartScales.Q_pos _) (ChartScales.Q_pos _)
  have hqA : qbig ≤ ChartScales.Q MA.firstBand := min_le_left _ _
  have hqB : qbig ≤ ChartScales.Q MB.firstBand := min_le_right _ _
  let U := CutStageEstimates.physicalSublevel F.data.h qbig
  have hU : IsOpen U := CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig
  have hlU : ∀ᶠ w in ActualBaseVelocityBounds.endpoint, w ∈ U :=
    endpoint_sublevel F.data.h_pos F.data.h_lt_half hqbig
  have hq := ActualBaseVelocityBounds.endpoint_q_small F.data.h_pos F.data.h_lt_half
  have hsBase : ContDiffOn ℝ ∞ (FinalSlowBase.velocity H v upper B) U :=
    (FinalSlowBase.velocity_smooth H v upper B).mono (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hsInc : ContDiffOn ℝ ∞ (potentialIncrement WA MA) U :=
    potentialIncrement_smooth WA MA F.data.h_pos F.data.h_lt_half hqA
  have hsDirect : ContDiffOn ℝ ∞ MB.family.angularField U :=
    MB.angular_smooth F.data.h_pos F.data.h_lt_half hqB
  have hsCurl := spatialCurl_smoothOn hU hsInc
  have hbase := (ActualBaseVelocityBounds.velocity_rate H v upper B m).weaken hq
    (neg_le_neg (le_max_left (ActualBaseVelocityBounds.heatLoss m)
      (max (seedPotentialLoss F.data.h WA.alpha WA.shift MA.alpha (m + 1))
        (seedDirectLoss F.data.h MB.alpha m))))
  have hinc : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (SpatialCurl.spatialCurl (potentialIncrement WA MA)) m
      (-initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha m) := by
    apply ((potentialIncrement_rate WA MA F.data.h_pos F.data.h_lt_half hqbig hqA
      (m + 1)).spatialCurl hU hlU hsInc).weaken hq
    exact neg_le_neg ((le_max_left _ _).trans (le_max_right _ _))
  have hdirect : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      MB.family.angularField m (-initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha m) := by
    apply (directIncrement_rate MB F.data.h_pos F.data.h_lt_half hqbig hqB m).weaken hq
    exact neg_le_neg ((le_max_right _ _).trans (le_max_right _ _))
  have hsum := (hbase.add hinc hU hlU hsBase hsCurl).add hdirect hU hlU
    (hsBase.add hsCurl) hsDirect
  exact hsum.congr_on hU hlU
    (initializedVelocity_decomposition H v upper B WA MA MB hqA).symm

theorem initializedVelocity_finite_rate (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h)) (m : ℕ) :
    FiniteJetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (initializedVelocity H v upper B WA MA MB) m
      (-maxJetLoss (initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha) m) := by
  have hq := ActualBaseVelocityBounds.endpoint_q_small F.data.h_pos F.data.h_lt_half
  apply finiteJetRate_of_jetRate (hq.mono (fun _ hw => hw.1))
  intro i hi
  exact (initializedVelocity_rate H v upper B WA MA MB i).weaken hq
    (neg_le_neg (le_maxJetLoss _ hi))

theorem uncutVelocity_zero_eq_initialized (upper : ℝ) (B : ℕ)
    (WA : ℕ → WaveData F.data.h D I K (Fin 3))
    (MA : ℕ → MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : ℕ → MeanData F.data.h (CoordinateAlgebra.A F.data.h)) :
    MixedDiagonalResidual.uncutVelocity
        (potentialStages (TailGaugePotential.finalPotential H v upper B) WA MA)
        (directStages MB) 0 =
      initializedVelocity H v upper B (WA 0) (MA 0) (MB 0) := by
  rw [MixedFiniteBackground.uncutVelocity_zero]
  rfl

/-- Direct input for `MixedFiniteBackground.mixed_background_from_initial`,
using the actual index-zero native estimates. -/
theorem stages_initial_rate (upper : ℝ) (B : ℕ)
    (WA : ℕ → WaveData F.data.h D I K (Fin 3))
    (MA : ℕ → MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : ℕ → MeanData F.data.h (CoordinateAlgebra.A F.data.h)) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (MixedDiagonalResidual.uncutVelocity
        (potentialStages (TailGaugePotential.finalPotential H v upper B) WA MA)
        (directStages MB) 0) m
      (-initialLoss F.data.h (WA 0).alpha (WA 0).shift (MA 0).alpha (MB 0).alpha m) := by
  rw [uncutVelocity_zero_eq_initialized]
  exact initializedVelocity_rate H v upper B (WA 0) (MA 0) (MB 0) m

/-- An exact representation adapter for initialization assembled elsewhere.
Its inputs identify the literal potential and direct angular field on an
eventual open neighborhood; no bound on either initialized velocity or
the base gauge is assumed. -/
theorem represented_initial_rate (upper : ℝ) (B : ℕ)
    (WA : WaveData F.data.h D I K (Fin 3))
    (MA : MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanData F.data.h (CoordinateAlgebra.A F.data.h))
    {A Bdirect : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hlU : ∀ᶠ w in ActualBaseVelocityBounds.endpoint, w ∈ U)
    (hA : EqOn (A 0) (initializedPotential H v upper B WA MA) U)
    (hB : EqOn (Bdirect 0) MB.family.angularField U) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (MixedDiagonalResidual.uncutVelocity A Bdirect 0) m
      (-initialLoss F.data.h WA.alpha WA.shift MA.alpha MB.alpha m) := by
  apply (initializedVelocity_rate H v upper B WA MA MB m).congr_on hU hlU
  intro w hw
  have he : A 0 =ᶠ[𝓝 w] initializedPotential H v upper B WA MA := by
    filter_upwards [hU.mem_nhds hw] with y hy
    exact hA hy
  rw [MixedFiniteBackground.uncutVelocity_zero]
  change SpatialCurl.spatialCurl (initializedPotential H v upper B WA MA) w +
    MB.family.angularField w = SpatialCurl.spatialCurl (A 0) w + Bdirect 0 w
  rw [SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq he, hB hw]

/-- Every native finite background now follows without an assumed
index-zero velocity bound. Its loss is fixed for the whole sequence. -/
theorem native_background_rate (upper : ℝ) (B : ℕ)
    (WA : ℕ → WaveData F.data.h D I K (Fin 3))
    (MA : ℕ → MeanData F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : ℕ → MeanData F.data.h (CoordinateAlgebra.A F.data.h))
    {qbig : ℝ} (hqbig : 0 < qbig)
    (hqA : ∀ j, qbig ≤ ChartScales.Q (MA j).firstBand)
    (hqB : ∀ j, qbig ≤ ChartScales.Q (MB j).firstBand)
    (g : ℕ → ℝ) (waveOffset potentialOffset directOffset : ℝ)
    (hg : ∀ j, 1 ≤ j → 0 ≤ g j)
    (hwave : ∀ j, 1 ≤ j → g j ≤ F.data.h * (WA j).alpha + (WA j).shift + waveOffset)
    (hpotential : ∀ j, 1 ≤ j → g j ≤ F.data.h * (MA j).alpha + potentialOffset)
    (hdirect : ∀ j, 1 ≤ j → g j ≤ F.data.h * (MB j).alpha + directOffset)
    (J m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (MixedDiagonalResidual.uncutVelocity
        (potentialStages (TailGaugePotential.finalPotential H v upper B) WA MA)
        (directStages MB) J) m
      (-MixedFiniteBackground.initialBackgroundLoss
        (initialLoss F.data.h (WA 0).alpha (WA 0).shift (MA 0).alpha (MB 0).alpha)
        (potentialLoss F.data.h waveOffset potentialOffset)
        (directLoss F.data.h directOffset) m) := by
  have hU := CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig
  have hlU := endpoint_sublevel F.data.h_pos F.data.h_lt_half hqbig
  have hsBase : ContDiffOn ℝ ∞ (TailGaugePotential.finalPotential H v upper B)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
    (TailGaugePotential.finalPotential_smooth H v upper B).mono
      (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hsA := potentialStages_smooth (TailGaugePotential.finalPotential H v upper B) WA MA
    F.data.h_pos F.data.h_lt_half hsBase hqA
  have hsB := directStages_smooth MB F.data.h_pos F.data.h_lt_half hqB
  obtain ⟨CA, _, hrawA⟩ := potentialStages_raw (TailGaugePotential.finalPotential H v upper B)
    WA MA F.data.h_pos F.data.h_lt_half hqA g waveOffset potentialOffset hwave hpotential
  obtain ⟨CB, _, hrawB⟩ := directStages_raw MB F.data.h_pos F.data.h_lt_half hqB g directOffset
      hdirect
  exact MixedFiniteBackground.mixed_background_from_initial hU hlU
    (ActualBaseVelocityBounds.endpoint_past.and hlU)
    (ActualBaseVelocityBounds.endpoint_q_small F.data.h_pos F.data.h_lt_half)
    hsA hsB hrawA hrawB hg (stages_initial_rate H v upper B WA MA MB) J m

end ActualBase

end NavierStokes.InitializedPhysicalBackground

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualPhysicalStageBounds

open Set Function Filter ProblemStatement DiagonalResidual
open scoped Topology ContDiff BigOperators

/-- Region, given by `PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2`. -/
noncomputable def region (h : ℝ) : Set PhysicalGraphBounds.Plane :=
  PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2

theorem region_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) : IsOpen (region h) :=
  PhysicalMeanDomain.normalizedSlowDomain_open (by linarith) (by linarith) _ _

/-- Native facts about an already constructed coherent mean family.
This record neither constructs a new physical field nor assumes physical
derivative bounds. -/
structure MeanInput (h degree : ℝ) where
  /-- First band of `MeanInput`, of type `ℕ`. -/
  firstBand : ℕ
  /-- Gap bound of `MeanInput`, of type `ℕ`. -/
  gapBound : ℕ
  /-- Lower radius of `MeanInput`, of type `ℝ`. -/
  lowerRadius : ℝ
  /-- Upper radius of `MeanInput`, of type `ℝ`. -/
  upperRadius : ℝ
  /-- Alpha of `MeanInput`, of type `ℝ`. -/
  alpha : ℝ
  /-- Family of `MeanInput`, of type `PhysicalMeanJetBounds.CoherentFamily h degree firstBand
  gapBound (region h) ℝ`. -/
  family : PhysicalMeanJetBounds.CoherentFamily h degree firstBand gapBound (region h) ℝ
  band_four : 4 ≤ firstBand
  lower_pos : 0 < lowerRadius
  radii_lt : lowerRadius < upperRadius
  smooth : ∀ n ≥ firstBand, ContDiffOn ℝ ∞ (family.native n)
    (PhysicalMeanDomain.slowDomain (region h))
  support : PhysicalMeanJetBounds.NativeSupport h lowerRadius upperRadius firstBand (region h)
      family.native
  jets : PhysicalMeanJetBounds.NativeJets firstBand (region h) (h * alpha) family.native

/-- Package the existing moving-field and native-class theorems without
changing the supplied coherent physical field. -/
noncomputable def MeanInput.ofMoving {h degree a b α : ℝ} {N Δ : ℕ}
    (R : LocalSignedRequest.SlowRegion (2 * h)) (hR : R.carrier = region h)
    (M : PhysicalMeanJetBounds.CoherentFamily h degree N Δ (region h) ℝ)
    (hN : 4 ≤ N) (ha : 0 < a) (hab : a < b)
    (hm : GaugeMomentBalances.MovingField R a b M.native)
    (hj : PhysicalMeanJetBounds.NativeJets N R.carrier (h * α) M.native) : MeanInput h degree where
  firstBand := N
  gapBound := Δ
  lowerRadius := a
  upperRadius := b
  alpha := α
  family := M
  band_four := hN
  lower_pos := ha
  radii_lt := hab
  smooth n _ := by simpa only [hR] using hm.smooth n
  support n _ := by
    have hs := hm.supported n
    simp only [hR] at hs
    exact hs
  jets := by simpa only [hR] using hj

theorem MeanInput.field_smooth {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ M.family.field (CutStageEstimates.physicalSublevel h qbig) :=
  LocalMeanPhysicalBounds.field_sublevel_smooth M.family hh hh1 M.lower_pos M.radii_lt
    (region_open hh hh1) (fun _ hx => hx) M.smooth M.support hq

theorem MeanInput.angular_smooth {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ M.family.angularField (CutStageEstimates.physicalSublevel h qbig) :=
  LocalMeanPhysicalBounds.angularField_sublevel_smooth M.family hh hh1 M.lower_pos M.radii_lt
    (region_open hh hh1) (fun _ hx => hx) M.smooth M.support hq

theorem MeanInput.field_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (h * M.alpha - PhysicalMeanJetBounds.loss degree m) :=
  LocalMeanPhysicalBounds.field_sublevel_bound M.family hh hh1 M.lower_pos M.radii_lt M.band_four
    (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets hq m

theorem MeanInput.angular_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (h * M.alpha - PhysicalMeanJetBounds.loss degree m) :=
  LocalMeanPhysicalBounds.angularField_sublevel_bound M.family hh hh1 M.lower_pos M.radii_lt
      M.band_four
    (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets hq m

theorem MeanInput.field_bound_with_gain {h degree qbig g delta : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hg : g ≤ h * M.alpha + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - (PhysicalMeanJetBounds.loss degree m + delta)) :=
            by
  obtain ⟨C, hC, hb⟩ := M.field_bound hh hh1 hq m
  refine ⟨C, hC, fun w hw hqw => (hb w hw hqw).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw
      (by linarith)) hC

theorem MeanInput.angular_bound_with_gain {h degree qbig g delta : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hg : g ≤ h * M.alpha + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - (PhysicalMeanJetBounds.loss degree m + delta)) :=
            by
  obtain ⟨C, hC, hb⟩ := M.angular_bound hh hh1 hq m
  refine ⟨C, hC, fun w hw hqw => (hb w hw hqw).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw
      (by linarith)) hC

section JetAlgebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig : ℝ} {f g : SpaceTime → V} {m : ℕ} {r s : ℝ}

theorem weaken_bound (hh : 0 < h) (hh1 : h < 1 / 2) (hsr : s ≤ r)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ s := by
  obtain ⟨C, hC, hb⟩ := hb
  exact ⟨C, hC, fun w hw hqw => (hb w hw hqw).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge
      (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw hsr) hC)⟩

theorem add_bounds (hh : 0 < h) (hh1 : h < 1 / 2)
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hg : ContDiffOn ℝ ∞ g (CutStageEstimates.physicalSublevel h qbig))
    (hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r)
    (hgb : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m g w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (fun z => f z + g z) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r := by
  obtain ⟨A, hA, hfa⟩ := hfb
  obtain ⟨B, hB, hgb⟩ := hgb
  refine ⟨A + B, add_nonneg hA hB, fun w hw hqw => ?_⟩
  exact (ResidualStability.norm_jet_add_le
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig) hf hg hw m).trans
    ((add_le_add (hfa w hw hqw) (hgb w hw hqw)).trans_eq (by ring))

end JetAlgebra

section Increments

variable {h : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}

/-- The four actual potential contributions of one cycle. -/
noncomputable def potentialIncrement
    (WP : PhysicalStageBounds.WaveData h DP IP KP (Fin 3))
    (WS : PhysicalStageBounds.WaveData h DS IS KS (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2)) : VelocityField :=
  fun w => WP.vector w + WS.vector w + MT.family.angularField w + MR.family.angularField w

/-- Pressure increment, defined pointwise by `WP.pressure w + WS.pressure w + MP.family.field
w`. -/
noncomputable def pressureIncrement
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    (WS : PhysicalStageBounds.WaveData h DS IS KS Unit)
    (MP : MeanInput h (2 * CoordinateAlgebra.A h)) : PressureField :=
  fun w => WP.pressure w + WS.pressure w + MP.family.field w

theorem potentialIncrement_smooth
    (WP : PhysicalStageBounds.WaveData h DP IP KP (Fin 3))
    (WS : PhysicalStageBounds.WaveData h DS IS KS (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) :
    ContDiffOn ℝ ∞ (potentialIncrement WP WS MT MR) (CutStageEstimates.physicalSublevel h qbig) :=
  ((((WP.vector_smooth hh hh1).mono inter_subset_left).add
    ((WS.vector_smooth hh hh1).mono inter_subset_left)).add
      (MT.angular_smooth hh hh1 hqT)).add (MR.angular_smooth hh hh1 hqR)

theorem pressureIncrement_smooth
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    (WS : PhysicalStageBounds.WaveData h DS IS KS Unit)
    (MP : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q MP.firstBand) :
    ContDiffOn ℝ ∞ (pressureIncrement WP WS MP) (CutStageEstimates.physicalSublevel h qbig) :=
  (((WP.pressure_smooth hh hh1).mono inter_subset_left).add
    ((WS.pressure_smooth hh hh1).mono inter_subset_left)).add (MP.field_smooth hh hh1 hq)

theorem potentialIncrement_bound
    (WP : PhysicalStageBounds.WaveData h DP IP KP (Fin 3))
    (WS : PhysicalStageBounds.WaveData h DS IS KS (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig g dw dm : ℝ}
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand)
    (hWP : g ≤ h * WP.alpha + WP.shift + dw) (hWS : g ≤ h * WS.alpha + WS.shift + dw)
    (hMT : g ≤ h * MT.alpha + dm) (hMR : g ≤ h * MR.alpha + dm) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (potentialIncrement WP WS MT MR) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - PhysicalStageBounds.potentialLoss h dw dm m) := by
  have hp0 := WP.vector_bound_with_gain hh hh1 hWP m
  have hs0 := WS.vector_bound_with_gain hh hh1 hWS m
  have hp := weaken_bound (qbig := qbig) (s := g - PhysicalStageBounds.potentialLoss h dw dm m) hh
      hh1
    (sub_le_sub_left (le_max_left _ _) g) (by
      obtain ⟨C, hC, hb⟩ := hp0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hs := weaken_bound (qbig := qbig) (s := g - PhysicalStageBounds.potentialLoss h dw dm m) hh
      hh1
    (sub_le_sub_left (le_max_left _ _) g) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have ht := weaken_bound (s := g - PhysicalStageBounds.potentialLoss h dw dm m)
    hh hh1 (sub_le_sub_left (le_max_right _ _) g)
    (MT.angular_bound_with_gain hh hh1 hqT hMT m)
  have hr := weaken_bound (s := g - PhysicalStageBounds.potentialLoss h dw dm m)
    hh hh1 (sub_le_sub_left (le_max_right _ _) g)
    (MR.angular_bound_with_gain hh hh1 hqR hMR m)
  have sp : ContDiffOn ℝ ∞ WP.vector (CutStageEstimates.physicalSublevel h qbig) :=
    (WP.vector_smooth hh hh1).mono inter_subset_left
  have ss : ContDiffOn ℝ ∞ WS.vector (CutStageEstimates.physicalSublevel h qbig) :=
    (WS.vector_smooth hh hh1).mono inter_subset_left
  have st := MT.angular_smooth hh hh1 hqT
  exact add_bounds hh hh1 ((sp.add ss).add st) (MR.angular_smooth hh hh1 hqR)
    (add_bounds hh hh1 (sp.add ss) st (add_bounds hh hh1 sp ss hp hs) ht) hr

theorem pressureIncrement_bound
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    (WS : PhysicalStageBounds.WaveData h DS IS KS Unit)
    (MP : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig g dw dm : ℝ}
    (hq : qbig ≤ ChartScales.Q MP.firstBand)
    (hWP : g ≤ h * WP.alpha + WP.shift + dw) (hWS : g ≤ h * WS.alpha + WS.shift + dw)
    (hMP : g ≤ h * MP.alpha + dm) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (pressureIncrement WP WS MP) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - PhysicalStageBounds.pressureLoss h dw dm m) := by
  have hp0 := WP.pressure_bound_with_gain hh hh1 hWP m
  have hs0 := WS.pressure_bound_with_gain hh hh1 hWS m
  have hp := weaken_bound (qbig := qbig) (s := g - PhysicalStageBounds.pressureLoss h dw dm m) hh
      hh1
    (sub_le_sub_left (le_max_left _ _) g) (by
      obtain ⟨C, hC, hb⟩ := hp0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hs := weaken_bound (qbig := qbig) (s := g - PhysicalStageBounds.pressureLoss h dw dm m) hh
      hh1
    (sub_le_sub_left (le_max_left _ _) g) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hm := weaken_bound (s := g - PhysicalStageBounds.pressureLoss h dw dm m)
    hh hh1 (sub_le_sub_left (le_max_right _ _) g)
    (MP.field_bound_with_gain hh hh1 hq hMP m)
  have sp : ContDiffOn ℝ ∞ WP.pressure (CutStageEstimates.physicalSublevel h qbig) :=
    (WP.pressure_smooth hh hh1).mono inter_subset_left
  have ss : ContDiffOn ℝ ∞ WS.pressure (CutStageEstimates.physicalSublevel h qbig) :=
    (WS.pressure_smooth hh hh1).mono inter_subset_left
  exact add_bounds hh hh1 (sp.add ss) (MP.field_smooth hh hh1 hq)
    (add_bounds hh hh1 sp ss hp hs) hm

end Increments

/-! ## Positive correction stages and the exact ledger gain -/

/-- Cycle inputs data, collecting `particularPotential`, `signedPotential`,
`particularPressure`, `signedPressure`, `temporal`, `rank` and their compatibility
conditions. -/
structure CycleInputs (h : ℝ) (DP : Type) [NormedAddCommGroup DP] [NormedSpace ℝ DP]
    (IP KP : Type*) (DS : Type) [NormedAddCommGroup DS] [NormedSpace ℝ DS] (IS KS : Type*) where
  /-- Particular potential of `CycleInputs`, of type `ℕ → PhysicalStageBounds.WaveData h DP IP
  KP (Fin 3)`. -/
  particularPotential : ℕ → PhysicalStageBounds.WaveData h DP IP KP (Fin 3)
  /-- Signed potential of `CycleInputs`, of type `ℕ → PhysicalStageBounds.WaveData h DS IS KS
  (Fin 3)`. -/
  signedPotential : ℕ → PhysicalStageBounds.WaveData h DS IS KS (Fin 3)
  /-- Particular pressure of `CycleInputs`, of type `ℕ → PhysicalStageBounds.WaveData h DP IP KP
  Unit`. -/
  particularPressure : ℕ → PhysicalStageBounds.WaveData h DP IP KP Unit
  /-- Signed pressure of `CycleInputs`, of type `ℕ → PhysicalStageBounds.WaveData h DS IS KS
  Unit`. -/
  signedPressure : ℕ → PhysicalStageBounds.WaveData h DS IS KS Unit
  /-- Temporal of `CycleInputs`, of type `ℕ → MeanInput h (CoordinateAlgebra.A h - 1 / 2)`. -/
  temporal : ℕ → MeanInput h (CoordinateAlgebra.A h - 1 / 2)
  /-- Rank of `CycleInputs`, of type `ℕ → MeanInput h (CoordinateAlgebra.A h - 1 / 2)`. -/
  rank : ℕ → MeanInput h (CoordinateAlgebra.A h - 1 / 2)
  /-- Angular of `CycleInputs`, of type `ℕ → MeanInput h (CoordinateAlgebra.A h)`. -/
  angular : ℕ → MeanInput h (CoordinateAlgebra.A h)
  /-- Pressure field of `CycleInputs`, of type `ℕ → MeanInput h (2 * CoordinateAlgebra.A h)`. -/
  pressure : ℕ → MeanInput h (2 * CoordinateAlgebra.A h)

namespace CycleInputs

variable {h : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (D : CycleInputs h DP IP KP DS IS KS)

/-- Potential, given by `potentialIncrement (D.particularPotential k) (D.signedPotential k)
(D.temporal k) (D.rank k)`. -/
noncomputable def potential (k : ℕ) : VelocityField :=
  potentialIncrement (D.particularPotential k) (D.signedPotential k) (D.temporal k) (D.rank k)

/-- Direct, given by `(D.angular k).family.angularField`. -/
noncomputable def direct (k : ℕ) : VelocityField := (D.angular k).family.angularField

/-- Pressure field, given by `pressureIncrement (D.particularPressure k) (D.signedPressure k)
(D.pressure k)`. -/
noncomputable def pressureField (k : ℕ) : PressureField :=
  pressureIncrement (D.particularPressure k) (D.signedPressure k) (D.pressure k)

/-- Cycle `k` contributes physical stage `k+1`. These are native exponent
and chart-degree comparisons, not physical estimates. -/
structure Metadata (κ : ℝ) : Prop where
  particularPotential : ∀ k, ActualIterationLedger.waveNative κ (k + 1) ≤ (D.particularPotential
      k).alpha
  particularPotentialShift : ∀ k, -h ≤ (D.particularPotential k).shift
  signedPotential : ∀ k, ActualIterationLedger.waveNative κ (k + 1) ≤ (D.signedPotential k).alpha
  signedPotentialShift : ∀ k, -h ≤ (D.signedPotential k).shift
  temporal : ∀ k, ActualIterationLedger.meanNative κ (k + 1) ≤ (D.temporal k).alpha
  rank : ∀ k, ActualIterationLedger.meanNative κ (k + 1) ≤ (D.rank k).alpha
  angular : ∀ k, ActualIterationLedger.meanNative κ (k + 1) ≤ (D.angular k).alpha
  particularPressure : ∀ k, ActualIterationLedger.wavePressureNative κ (k + 1) ≤
      (D.particularPressure k).alpha
  particularPressureShift : ∀ k, -(2 * CoordinateAlgebra.A h) ≤ (D.particularPressure k).shift
  signedPressure : ∀ k, ActualIterationLedger.wavePressureNative κ (k + 1) ≤ (D.signedPressure
      k).alpha
  signedPressureShift : ∀ k, -(2 * CoordinateAlgebra.A h) ≤ (D.signedPressure k).shift
  pressure : ∀ k, ActualIterationLedger.meanNative κ (k + 1) ≤ (D.pressure k).alpha

/-- Valid scale data, collecting `temporal`, `rank`, `angular`, `pressure`. -/
structure ValidScale (qbig : ℝ) : Prop where
  temporal : ∀ k, qbig ≤ ChartScales.Q (D.temporal k).firstBand
  rank : ∀ k, qbig ≤ ChartScales.Q (D.rank k).firstBand
  angular : ∀ k, qbig ≤ ChartScales.Q (D.angular k).firstBand
  pressure : ∀ k, qbig ≤ ChartScales.Q (D.pressure k).firstBand

end CycleInputs

private theorem potential_gain {h κ α s : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000)
    (k : ℕ) (hα : ActualIterationLedger.waveNative κ (k + 1) ≤ α) (hs : -h ≤ s) :
    ActualIterationLedger.gain h (k + 1) ≤ h * α + s + h := by
  have hg := ActualIterationLedger.gain_le_wave hh hκ (Nat.succ_pos k)
  have ha := mul_le_mul_of_nonneg_left hα hh
  linarith

private theorem pressure_gain {h κ α s : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000)
    (k : ℕ) (hα : ActualIterationLedger.wavePressureNative κ (k + 1) ≤ α)
    (hs : -(2 * CoordinateAlgebra.A h) ≤ s) :
    ActualIterationLedger.gain h (k + 1) ≤ h * α + s + 2 * CoordinateAlgebra.A h := by
  have hg := ActualIterationLedger.gain_le_wavePressure hh hκ (Nat.succ_pos k)
  have ha := mul_le_mul_of_nonneg_left hα hh
  linarith

private theorem mean_gain {h κ α : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000)
    (k : ℕ) (hα : ActualIterationLedger.meanNative κ (k + 1) ≤ α) :
    ActualIterationLedger.gain h (k + 1) ≤ h * α + 0 := by
  simpa using (ActualIterationLedger.gain_le_mean hh hκ (Nat.succ_pos k)).trans
    (mul_le_mul_of_nonneg_left hα hh)

namespace CycleInputs

variable {h κ qbig : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (D : CycleInputs h DP IP KP DS IS KS)

theorem potential_bound (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.potential k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (ActualIterationLedger.gain h (k + 1) - PhysicalStageBounds.potentialLoss h h 0 m) :=
  potentialIncrement_bound (D.particularPotential k) (D.signedPotential k) (D.temporal k) (D.rank k)
    hh hh1 (Q.temporal k) (Q.rank k)
    (potential_gain hh.le hκ k (H.particularPotential k) (H.particularPotentialShift k))
    (potential_gain hh.le hκ k (H.signedPotential k) (H.signedPotentialShift k))
    (mean_gain hh.le hκ k (H.temporal k)) (mean_gain hh.le hκ k (H.rank k)) m

theorem direct_bound (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.direct k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (ActualIterationLedger.gain h (k + 1) - PhysicalStageBounds.directLoss h 0 m) :=
  (D.angular k).angular_bound_with_gain hh hh1 (Q.angular k) (mean_gain hh.le hκ k (H.angular k)) m

theorem pressure_bound (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.pressureField k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (ActualIterationLedger.gain h (k + 1) - PhysicalStageBounds.pressureLoss h (2 *
            CoordinateAlgebra.A h) 0 m) :=
  pressureIncrement_bound (D.particularPressure k) (D.signedPressure k) (D.pressure k)
    hh hh1 (Q.pressure k)
    (pressure_gain hh.le hκ k (H.particularPressure k) (H.particularPressureShift k))
    (pressure_gain hh.le hκ k (H.signedPressure k) (H.signedPressureShift k))
    (mean_gain hh.le hκ k (H.pressure k)) m

theorem potential_smooth (Q : D.ValidScale qbig) (hh : 0 < h) (hh1 : h < 1 / 2) (k : ℕ) :
    ContDiffOn ℝ ∞ (D.potential k) (CutStageEstimates.physicalSublevel h qbig) :=
  potentialIncrement_smooth _ _ _ _ hh hh1 (Q.temporal k) (Q.rank k)

theorem direct_smooth (Q : D.ValidScale qbig) (hh : 0 < h) (hh1 : h < 1 / 2) (k : ℕ) :
    ContDiffOn ℝ ∞ (D.direct k) (CutStageEstimates.physicalSublevel h qbig) :=
  (D.angular k).angular_smooth hh hh1 (Q.angular k)

theorem pressure_smooth (Q : D.ValidScale qbig) (hh : 0 < h) (hh1 : h < 1 / 2) (k : ℕ) :
    ContDiffOn ℝ ∞ (D.pressureField k) (CutStageEstimates.physicalSublevel h qbig) :=
  pressureIncrement_smooth _ _ _ hh hh1 (Q.pressure k)

end CycleInputs

section RawTransfer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig : ℝ} {f g : SpaceTime → V} {m : ℕ} {r : ℝ}

theorem bound_congr (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : EqOn f g (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m g w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r := by
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, fun w hw hqw => ?_⟩
  rw [← ResidualStability.iteratedFDeriv_eqOn
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig) he m hw]
  exact hb w hw hqw

theorem raw_of_positive_bounds {F : ℕ → SpaceTime → V} {gain L : ℕ → ℝ}
    (hb : ∀ k m, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (F (k + 1)) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (gain (k + 1) - L
          m)) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j m, 0 ≤ C j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) F gain L C (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  classical
  choose C hC hb using hb
  refine ⟨fun j m => if j = 0 then 0 else C (j - 1) m, ?_, ?_⟩
  · intro j m
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hC _ _
  · intro j hj m w hw hqw
    cases j with
    | zero => omega
    | succ k => simpa only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one,
        Real.rpow_zero, mul_one] using hb k m w hw.2 hqw

end RawTransfer

namespace CycleInputs

variable {h κ qbig : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (D : CycleInputs h DP IP KP DS IS KS)

/-- Literal sequence identities transfer the derived estimates to the
actual potential/direct/pressure stages. Index zero is deliberately absent. -/
theorem represented_raw_bounds (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000)
    (A B : ℕ → VelocityField) (P : ℕ → PressureField)
    (hA : ∀ k, EqOn (D.potential k) (A (k + 1)) (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ k, EqOn (D.direct k) (B (k + 1)) (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ k, EqOn (D.pressureField k) (P (k + 1)) (CutStageEstimates.physicalSublevel h qbig)) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j m, 0 ≤ CA j m ∧ 0 ≤ CB j m ∧ 0 ≤ CP j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A (ActualIterationLedger.gain
          h)
        (PhysicalStageBounds.potentialLoss h h 0) CA (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B (ActualIterationLedger.gain
          h)
        (PhysicalStageBounds.directLoss h 0) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P (ActualIterationLedger.gain
          h)
        (PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0) CP (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  obtain ⟨CA, hCA, ha⟩ := raw_of_positive_bounds
    (fun k m => bound_congr hh hh1 (hA k) (D.potential_bound H Q hh hh1 hκ k m))
  obtain ⟨CB, hCB, hb⟩ := raw_of_positive_bounds
    (fun k m => bound_congr hh hh1 (hB k) (D.direct_bound H Q hh hh1 hκ k m))
  obtain ⟨CP, hCP, hp⟩ := raw_of_positive_bounds
    (fun k m => bound_congr hh hh1 (hP k) (D.pressure_bound H Q hh hh1 hκ k m))
  exact ⟨CA, CB, CP, fun j m => ⟨hCA j m, hCB j m, hCP j m⟩, ha, hb, hp⟩

end CycleInputs

/-! ## Initialization on the true native mean domain -/

open InitializedPhysicalBackground (seedPotentialLoss seedDirectLoss initialLoss)

section InitialIncrement

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- Initial increment, defined pointwise by `W.vector w + MT.family.angularField w +
MR.family.angularField w`. -/
noncomputable def initialIncrement (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2)) : VelocityField :=
  fun w => W.vector w + MT.family.angularField w + MR.family.angularField w

theorem initialIncrement_smooth (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) :
    ContDiffOn ℝ ∞ (initialIncrement W MT MR) (CutStageEstimates.physicalSublevel h qbig) :=
  (((W.vector_smooth hh hh1).mono inter_subset_left).add
    (MT.angular_smooth hh hh1 hqT)).add (MR.angular_smooth hh hh1 hqR)

theorem initialIncrement_bound (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (initialIncrement W MT MR) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (-seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m) := by
  have htGain : 0 ≤ h * MT.alpha + -(h * min MT.alpha MR.alpha) := by
    have := mul_le_mul_of_nonneg_left (min_le_left MT.alpha MR.alpha) hh.le
    linarith
  have hrGain : 0 ≤ h * MR.alpha + -(h * min MT.alpha MR.alpha) := by
    have := mul_le_mul_of_nonneg_left (min_le_right MT.alpha MR.alpha) hh.le
    linarith
  have hp0 := W.vector_bound_with_gain (g := 0) (delta := -(h * W.alpha + W.shift))
    hh hh1 (by linarith) m
  have ht0 := MT.angular_bound_with_gain hh hh1 hqT htGain m
  have hr0 := MR.angular_bound_with_gain hh hh1 hqR hrGain m
  simp only [zero_sub] at hp0 ht0 hr0
  have hp := weaken_bound (qbig := qbig)
    (s := -seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m) hh hh1
    (neg_le_neg (le_max_left _ _)) (by
      obtain ⟨C, hC, hb⟩ := hp0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have ht := weaken_bound (s := -seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m)
    hh hh1 (neg_le_neg (le_max_right _ _)) ht0
  have hr := weaken_bound (s := -seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m)
    hh hh1 (neg_le_neg (le_max_right _ _)) hr0
  have sp : ContDiffOn ℝ ∞ W.vector (CutStageEstimates.physicalSublevel h qbig) :=
    (W.vector_smooth hh hh1).mono inter_subset_left
  have st := MT.angular_smooth hh hh1 hqT
  exact add_bounds hh hh1 (sp.add st) (MR.angular_smooth hh hh1 hqR)
    (add_bounds hh hh1 sp st hp ht) hr

theorem initialIncrement_rate (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hqbig : 0 < qbig)
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      (initialIncrement W MT MR) m
      (-seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m) := by
  obtain ⟨C, hC, hb⟩ := initialIncrement_bound W MT MR hh hh1 hqT hqR m
  refine ⟨C, hC, ?_⟩
  filter_upwards [InitializedPhysicalBackground.endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  exact hb w hw hqw.2

/-- The finite pressure inserted at initialization, apart from the actual
base pressure. Both terms retain their original native class exponents. -/
noncomputable def initialPressureIncrement (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h)) : PressureField :=
  fun w => W.pressure w + M.family.field w

/-- Initial pressure loss, given by `PhysicalStageBounds.pressureLoss h (-(h * waveAlpha +
waveShift)) (-(h * meanAlpha)) m`. -/
noncomputable def initialPressureLoss (h waveAlpha waveShift meanAlpha : ℝ) (m : ℕ) : ℝ :=
  PhysicalStageBounds.pressureLoss h (-(h * waveAlpha + waveShift)) (-(h * meanAlpha)) m

theorem initialPressureIncrement_smooth (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ (initialPressureIncrement W M) (CutStageEstimates.physicalSublevel h qbig) :=
  ((W.pressure_smooth hh hh1).mono inter_subset_left).add (M.field_smooth hh hh1 hq)

theorem initialPressureIncrement_bound (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (initialPressureIncrement W M) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (-initialPressureLoss h W.alpha W.shift M.alpha m) := by
  have hw0 := W.pressure_bound_with_gain (g := 0) (delta := -(h * W.alpha + W.shift))
    hh hh1 (by linarith) m
  have hm0 := M.field_bound_with_gain (g := 0) (delta := -(h * M.alpha))
    hh hh1 hq (by linarith) m
  simp only [zero_sub] at hw0 hm0
  have hw := weaken_bound (qbig := qbig)
    (s := -initialPressureLoss h W.alpha W.shift M.alpha m) hh hh1
    (neg_le_neg (le_max_left _ _)) (by
      obtain ⟨C, hC, hb⟩ := hw0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hm := weaken_bound (s := -initialPressureLoss h W.alpha W.shift M.alpha m)
    hh hh1 (neg_le_neg (le_max_right _ _)) hm0
  have sw : ContDiffOn ℝ ∞ W.pressure (CutStageEstimates.physicalSublevel h qbig) :=
    (W.pressure_smooth hh hh1).mono inter_subset_left
  exact add_bounds hh hh1 sw (M.field_smooth hh hh1 hq) hw hm

theorem initialPressureIncrement_rate (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hqbig : 0 < qbig)
    (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      (initialPressureIncrement W M) m (-initialPressureLoss h W.alpha W.shift M.alpha m) := by
  obtain ⟨C, hC, hb⟩ := initialPressureIncrement_bound W M hh hh1 hq m
  refine ⟨C, hC, ?_⟩
  filter_upwards [InitializedPhysicalBackground.endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  exact hb w hw hqw.2

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem initialDirect_rate (MB : MeanInput h (CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hqbig : 0 < qbig)
    (hq : qbig ≤ ChartScales.Q MB.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      MB.family.angularField m (-seedDirectLoss h MB.alpha m) := by
  obtain ⟨C, hC, hb⟩ := MB.angular_bound_with_gain (g := 0) (delta := -(h * MB.alpha))
    hh hh1 hq (by linarith) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [InitializedPhysicalBackground.endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  simpa only [seedDirectLoss, PhysicalStageBounds.directLoss, zero_sub] using hb w hw hqw.2

end InitialIncrement

section ActualInitialBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- Initial potential, defined pointwise by `TailGaugePotential.finalPotential H v upper B w +
initialIncrement WA MT MR w`. -/
noncomputable def initialPotential (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2)) : VelocityField :=
  fun w => TailGaugePotential.finalPotential H v upper B w + initialIncrement WA MT MR w

/-- Initial velocity, defined pointwise by `SpatialCurl.spatialCurl (initialPotential H v upper
B WA MT MR) w + MB.family.angularField w`. -/
noncomputable def initialVelocity (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h)) : VelocityField :=
  fun w => SpatialCurl.spatialCurl (initialPotential H v upper B WA MT MR) w +
      MB.family.angularField w

theorem initialPotential_smooth (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    {qbig : ℝ} (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) :
    ContDiffOn ℝ ∞ (initialPotential H v upper B WA MT MR)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
  ((TailGaugePotential.finalPotential_smooth H v upper B).mono
    (fun _ hw => ⟨hw.1, mem_univ _⟩)).add
      (initialIncrement_smooth WA MT MR F.data.h_pos F.data.h_lt_half hqT hqR)

theorem initialVelocity_decomposition (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h))
    {qbig : ℝ} (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) :
    EqOn (initialVelocity H v upper B WA MT MR MB)
      (fun w => FinalSlowBase.velocity H v upper B w +
        SpatialCurl.spatialCurl (initialIncrement WA MT MR) w + MB.family.angularField w)
      (CutStageEstimates.physicalSublevel F.data.h qbig) := by
  have hbase : ContDiffOn ℝ ∞ (TailGaugePotential.finalPotential H v upper B)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
    (TailGaugePotential.finalPotential_smooth H v upper B).mono
      (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hinc := initialIncrement_smooth WA MT MR F.data.h_pos F.data.h_lt_half hqT hqR
  intro w hw
  unfold initialVelocity initialPotential
  rw [InitializedPhysicalBackground.spatialCurl_add_on
    (CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig) hbase hinc hw]
  dsimp only
  rw [TailGaugePotential.finalPotential_sameCurl H v upper B hw.1]

/-- The true-domain initialization has the same fixed loss as the prior
physical-background calculation, using the minimum of the two stream classes. -/
theorem initialVelocity_rate (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h)) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (initialVelocity H v upper B WA MT MR MB) m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) := by
  let qbig := min (ChartScales.Q MT.firstBand) (min (ChartScales.Q MR.firstBand) (ChartScales.Q
      MB.firstBand))
  have hqbig : 0 < qbig := lt_min (ChartScales.Q_pos _) (lt_min (ChartScales.Q_pos _)
      (ChartScales.Q_pos _))
  have hqT : qbig ≤ ChartScales.Q MT.firstBand := min_le_left _ _
  have hqR : qbig ≤ ChartScales.Q MR.firstBand := (min_le_right _ _).trans (min_le_left _ _)
  have hqB : qbig ≤ ChartScales.Q MB.firstBand := (min_le_right _ _).trans (min_le_right _ _)
  let U := CutStageEstimates.physicalSublevel F.data.h qbig
  have hU : IsOpen U := CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig
  have hlU : ∀ᶠ w in ActualBaseVelocityBounds.endpoint, w ∈ U :=
    InitializedPhysicalBackground.endpoint_sublevel F.data.h_pos F.data.h_lt_half hqbig
  have hq := ActualBaseVelocityBounds.endpoint_q_small F.data.h_pos F.data.h_lt_half
  have hsBase : ContDiffOn ℝ ∞ (FinalSlowBase.velocity H v upper B) U :=
    (FinalSlowBase.velocity_smooth H v upper B).mono (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hsInc : ContDiffOn ℝ ∞ (initialIncrement WA MT MR) U :=
    initialIncrement_smooth WA MT MR F.data.h_pos F.data.h_lt_half hqT hqR
  have hsDirect : ContDiffOn ℝ ∞ MB.family.angularField U :=
    MB.angular_smooth F.data.h_pos F.data.h_lt_half hqB
  have hsCurl := InitializedPhysicalBackground.spatialCurl_smoothOn hU hsInc
  have hbase : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (FinalSlowBase.velocity H v upper B) m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) :=
    (ActualBaseVelocityBounds.velocity_rate H v upper B m).weaken hq (neg_le_neg (le_max_left _ _))
  have hinc : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (SpatialCurl.spatialCurl (initialIncrement WA MT MR)) m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) := by
    apply ((initialIncrement_rate WA MT MR F.data.h_pos F.data.h_lt_half hqbig hqT hqR
      (m + 1)).spatialCurl hU hlU hsInc).weaken hq
    exact neg_le_neg ((le_max_left _ _).trans (le_max_right _ _))
  have hdirect : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      MB.family.angularField m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) := by
    apply (initialDirect_rate MB F.data.h_pos F.data.h_lt_half hqbig hqB m).weaken hq
    exact neg_le_neg ((le_max_right _ _).trans (le_max_right _ _))
  exact ((hbase.add hinc hU hlU hsBase hsCurl).add hdirect hU hlU
    (hsBase.add hsCurl) hsDirect).congr_on hU hlU
      (initialVelocity_decomposition H v upper B WA MT MR MB hqT hqR).symm

theorem represented_initial_rate (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h))
    {A Bdirect : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hlU : ∀ᶠ w in ActualBaseVelocityBounds.endpoint, w ∈ U)
    (hA : EqOn (A 0) (initialPotential H v upper B WA MT MR) U)
    (hB : EqOn (Bdirect 0) MB.family.angularField U) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (MixedDiagonalResidual.uncutVelocity A Bdirect 0) m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) := by
  apply (initialVelocity_rate H v upper B WA MT MR MB m).congr_on hU hlU
  intro w hw
  have he : A 0 =ᶠ[𝓝 w] initialPotential H v upper B WA MT MR := by
    filter_upwards [hU.mem_nhds hw] with y hy
    exact hA hy
  rw [MixedFiniteBackground.uncutVelocity_zero]
  change SpatialCurl.spatialCurl (initialPotential H v upper B WA MT MR) w +
    MB.family.angularField w = SpatialCurl.spatialCurl (A 0) w + Bdirect 0 w
  rw [SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq he, hB hw]

/-- The finite-background consumer now uses only native wave/mean data
on the true domain, plus exact initial and positive-stage identities. -/
theorem background_from_representations
    {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
    [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
    (Cyc : CycleInputs F.data.h DP IP KP DS IS KS) {κ qbig : ℝ}
    (HM : Cyc.Metadata κ) (HQ : Cyc.ValidScale qbig) (hκ : κ ≤ 1 / 100000)
    (hqbig : 0 < qbig) (upper : ℝ) (bandFloor : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h))
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand)
    (hqB : qbig ≤ ChartScales.Q MB.firstBand)
    (A B : ℕ → VelocityField)
    (hA0 : EqOn (A 0) (initialPotential H v upper bandFloor WA MT MR)
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hB0 : EqOn (B 0) MB.family.angularField (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hA : ∀ k, EqOn (Cyc.potential k) (A (k + 1)) (CutStageEstimates.physicalSublevel F.data.h
        qbig))
    (hB : ∀ k, EqOn (Cyc.direct k) (B (k + 1)) (CutStageEstimates.physicalSublevel F.data.h qbig))
    (J m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (MixedDiagonalResidual.uncutVelocity A B J) m
      (-MixedFiniteBackground.initialBackgroundLoss
        (initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha)
        (PhysicalStageBounds.potentialLoss F.data.h F.data.h 0)
        (PhysicalStageBounds.directLoss F.data.h 0) m) := by
  have hU := CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig
  have hlU := InitializedPhysicalBackground.endpoint_sublevel F.data.h_pos F.data.h_lt_half hqbig
  have hsa : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel F.data.h qbig) := by
    intro j
    cases j with
    | zero =>
      exact (initialPotential_smooth H v upper bandFloor WA MT MR hqT hqR).congr
        (fun _ hw => hA0 hw)
    | succ k =>
      exact (Cyc.potential_smooth HQ F.data.h_pos F.data.h_lt_half k).congr
        (fun _ hw => (hA k hw).symm)
  have hsb : ∀ j, ContDiffOn ℝ ∞ (B j) (CutStageEstimates.physicalSublevel F.data.h qbig) := by
    intro j
    cases j with
    | zero =>
      exact (MB.angular_smooth F.data.h_pos F.data.h_lt_half hqB).congr (fun _ hw => hB0 hw)
    | succ k =>
      exact (Cyc.direct_smooth HQ F.data.h_pos F.data.h_lt_half k).congr
        (fun _ hw => (hB k hw).symm)
  obtain ⟨CA, _, hrawA⟩ := raw_of_positive_bounds (fun k m =>
    bound_congr F.data.h_pos F.data.h_lt_half (hA k)
      (Cyc.potential_bound HM HQ F.data.h_pos F.data.h_lt_half hκ k m))
  obtain ⟨CB, _, hrawB⟩ := raw_of_positive_bounds (fun k m =>
    bound_congr F.data.h_pos F.data.h_lt_half (hB k)
      (Cyc.direct_bound HM HQ F.data.h_pos F.data.h_lt_half hκ k m))
  exact MixedFiniteBackground.mixed_background_from_initial hU hlU
    (ActualBaseVelocityBounds.endpoint_past.and hlU)
    (ActualBaseVelocityBounds.endpoint_q_small F.data.h_pos F.data.h_lt_half)
    hsa hsb hrawA hrawB (fun j _ => ActualIterationLedger.gain_nonneg F.data.h_pos.le j)
    (represented_initial_rate H v upper bandFloor WA MT MR MB hU hlU hA0 hB0) J m

end ActualInitialBase

/-! ## Literal candidate sequence interface -/

universe u

section CandidateSequences

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}

/-- Quantitative bounds for the actual MCA/MAS indexing convention.
The remaining representations concern the literal component fields. -/
theorem candidate_raw_bounds
    (Cyc : CycleInputs F.data.h DP IP KP DS IS KS) {κ qbig : ℝ}
    (HM : Cyc.Metadata κ) (HQ : Cyc.ValidScale qbig) (hκ : κ ≤ 1 / 100000)
    (upper : ℝ) (bandFloor : ℕ)
    (initial : MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (stages : ℕ → MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (angular : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h
        qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (hA : ∀ k, EqOn (Cyc.potential k) (stages k).field (CutStageEstimates.physicalSublevel F.data.h
        qbig))
    (hB : ∀ k, EqOn (Cyc.direct k) (LocalAngularDiagonal.rawSeries angular (k + 1))
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hP : ∀ k, EqOn (Cyc.pressureField k) (pStages k) (CutStageEstimates.physicalSublevel F.data.h
        qbig)) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j m, 0 ≤ CA j m ∧ 0 ≤ CB j m ∧ 0 ≤ CP j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ F.data.h)
        (MixedCandidateAssembly.potentialStages H v upper bandFloor initial stages)
        (ActualIterationLedger.gain F.data.h) (PhysicalStageBounds.potentialLoss F.data.h F.data.h
            0)
        CA (fun _ _ => 0) (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel
            F.data.h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ F.data.h)
        (LocalAngularDiagonal.rawSeries angular) (ActualIterationLedger.gain F.data.h)
        (PhysicalStageBounds.directLoss F.data.h 0) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel F.data.h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ F.data.h)
        (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages)
        (ActualIterationLedger.gain F.data.h)
        (PhysicalStageBounds.pressureLoss F.data.h (2 * CoordinateAlgebra.A F.data.h) 0)
        CP (fun _ _ => 0) (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel
            F.data.h qbig) := by
  apply Cyc.represented_raw_bounds HM HQ F.data.h_pos F.data.h_lt_half hκ
  · intro k
    simpa only [MixedCandidateAssembly.potentialStages,
        MixedAxisPreservation.initializedSeries_succ] using hA k
  · exact hB
  · intro k
    simpa only [MixedCandidateAssembly.pressureStages_succ] using hP k

end CandidateSequences

/-! ## Adapters for the constructed native mean families -/

section ConstructedMeans

open CorrectionInitialization.ActualPrimary ActualMeanPhysicalData
open CorrectionStep CorrectionState

/-- The constructed initialization families, with their proved native
classes and common band choice. No native estimate is left as an input. -/
noncomputable def actualInitialTemporalInput (B N0 N : ℕ) (hN : 4 ≤ N) :
    MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  MeanInput.ofMoving standardRegion rfl (initialTemporalFamily B N0 N) hN
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (initialTemporal_moving B N0) (initialTemporal_nativeJets B N0 N (by omega))

/-- Actual initial rank input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualInitialRankInput (B N0 N : ℕ) (hN : 4 ≤ N) :
    MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  MeanInput.ofMoving standardRegion rfl (initialRankFamily B N0 N) hN
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (initialRank_moving B N0) (initialRank_nativeJets B N0 N (by omega))

/-- Actual initial angular input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualInitialAngularInput (B N0 N : ℕ) (hN : 4 ≤ N) :
    MeanInput h (CoordinateAlgebra.A h) :=
  MeanInput.ofMoving standardRegion rfl (initialAngularFamily B N0 N) hN
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (initial_mean_moving B N0).angular (initialAngular_nativeJets B N0 N (by omega))

/-- Actual initial pressure input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualInitialPressureInput (B N0 N : ℕ) (hN : 4 ≤ N) :
    MeanInput h (2 * CoordinateAlgebra.A h) :=
  MeanInput.ofMoving standardRegion rfl (initialPressureFamily B N0 N) hN
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (initial_pressure_moving B N0) (initialPressure_nativeJets B N0 N (by omega))

@[simp] theorem actualInitialTemporalInput_family (B N0 N : ℕ) (hN : 4 ≤ N) :
    (actualInitialTemporalInput B N0 N hN).family = initialTemporalFamily B N0 N := rfl

@[simp] theorem actualInitialRankInput_family (B N0 N : ℕ) (hN : 4 ≤ N) :
    (actualInitialRankInput B N0 N hN).family = initialRankFamily B N0 N := rfl

@[simp] theorem actualInitialAngularInput_family (B N0 N : ℕ) (hN : 4 ≤ N) :
    (actualInitialAngularInput B N0 N hN).family = initialAngularFamily B N0 N := rfl

@[simp] theorem actualInitialPressureInput_family (B N0 N : ℕ) (hN : 4 ≤ N) :
    (actualInitialPressureInput B N0 N hN).family = initialPressureFamily B N0 N := rfl

/-- The actual initialized velocity, with its actual initial temporal,
rank, and direct angular families. Only the primary wave representation
is supplied by the separate physical-copy construction. -/
theorem actualInitialVelocity_rate
    {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}
    (B N0 N : ℕ) (hN : 4 ≤ N) (WA : PhysicalStageBounds.WaveData h D I K (Fin 3)) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      (initialVelocity certificate modulation upper B WA
        (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
        (actualInitialAngularInput B N0 N hN)) m
      (-initialLoss h WA.alpha WA.shift (1 - ChartScales.kappa) (9 / 10) m) := by
  simpa only [actualInitialTemporalInput, actualInitialRankInput, actualInitialAngularInput,
    MeanInput.ofMoving, min_self] using
    initialVelocity_rate certificate modulation upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
      (actualInitialAngularInput B N0 N hN) m

variable {B N0 N : ℕ} {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}

/-- These four cycle adapters retain the literal families of the actual
iterate. Their quantitative hypotheses are native source, debt, or mean
classes; physical derivative bounds are conclusions of the earlier API. -/
noncomputable def actualCycleTemporalInput (H : InitialCycleInput B N0 N p)
    (j : ℕ) (hN : 4 ≤ N) {α : ℝ}
    (HC : WeightedClasses.MeanClass ActualInitialMean.strip α
      (((p j).afterSigned
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state).axialResidual
        (commonContext B))) : MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  MeanInput.ofMoving standardRegion rfl ((initialCycleData H).temporalFamily j) hN
    initialGeometry.inner_pos initialGeometry.inner_lt_outer
    ((initialCycleData H).temporal_moving j) (cycleTemporal_nativeJets H j (by omega) HC)

/-- Actual cycle rank input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualCycleRankInput (H : InitialCycleInput B N0 N p)
    (j : ℕ) (hN : 4 ≤ N) {α : ℝ}
    (HC : WeightedClasses.UnweightedClass ActualInitialMean.slowStrip α
      (CorrectionState.debt (commonContext B)
        ((p j).afterTemporal
          (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
              j).coefficients
          (commonContext B) (CycleState.iterate p (commonContext B)
              (ActualInitialization.initialCycleState B N0) j).state))) :
    MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  MeanInput.ofMoving standardRegion rfl ((initialCycleData H).rankFamily j) hN
    initialGeometry.inner_pos initialGeometry.inner_lt_outer
    ((initialCycleData H).rank_moving j) (cycleRank_nativeJets H j (by omega) HC)

/-- Actual cycle angular input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualCycleAngularInput (H : InitialCycleInput B N0 N p)
    (j : ℕ) (hN : 4 ≤ N) {α : ℝ}
    (HT : MeanIncrementBounds.IncrementBounds ActualInitialMean.strip α
      ((p j).temporalIncrement
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state))
    (HR : MeanIncrementBounds.IncrementBounds ActualInitialMean.strip α
      ((p j).rankIncrement
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state)) :
    MeanInput h (CoordinateAlgebra.A h) :=
  MeanInput.ofMoving standardRegion rfl ((initialCycleData H).angularIncrementFamily j) hN
    initialGeometry.inner_pos initialGeometry.inner_lt_outer
    ((initialCycleData H).angularIncrement_moving j) (angularIncrement_nativeJets H j (by
        omega) HT HR)

/-- Actual cycle pressure input as an element of `MeanInput h (2 * CoordinateAlgebra.A h)`. -/
noncomputable def actualCyclePressureInput (H : InitialCycleInput B N0 N p)
    (j : ℕ) (hN : 4 ≤ N) {α : ℝ}
    (HC : WeightedClasses.MeanClass ActualInitialMean.strip α
      ((CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          (j + 1)).state.pressure -
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).state.pressure)) :
    MeanInput h (2 * CoordinateAlgebra.A h) := by
  have hs : (VariableGaugeMean.reconstructState initialGeometry.gauge (commonContext B)
      (ActualInitialization.initialCycleState B N0).state).pressure =
      (ActualInitialization.initialCycleState B N0).state.pressure := by
    rw [initialGeometry_gauge]
    rfl
  exact MeanInput.ofMoving standardRegion rfl ((initialCycleData H).pressureIncrementFamily j) hN
    initialGeometry.inner_pos initialGeometry.inner_lt_outer
    ((initialCycleData H).pressureIncrement_moving hs j) (pressureIncrement_nativeJets H j (by
        omega) HC)

end ConstructedMeans

end NavierStokes.ActualPhysicalStageBounds
