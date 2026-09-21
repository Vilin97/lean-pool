/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.OscillatoryReductionLimit
import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertFiniteTruncationWeakOneOne
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Principal-value closure from the uniform maximal weak estimate

Smooth compactly supported functions are approximated using Mathlib's actual
`L¹` density theorem. The sole classical input is the uniform weak estimate
for the genuine ordinary Hilbert maximal truncation on `L0Infinity`.
-/

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap Topology

namespace QuadraticCarleson
namespace HilbertPrincipalValueClosure

open HilbertFiniteTruncationWeakOneOne OscillatoryReduction


/-- The single remaining classical input, stated only for the actual
ordinary maximal truncation and the paper's bounded compact-support domain. -/
def HasUniformHilbertMaximalWeakBound (C : ℝ≥0∞) : Prop :=
  C < ∞ ∧ ∀ (f : L0Infinity) (a : ℝ≥0∞),
    a * volume {x | a < quadraticHilbertMaximalTruncation 0 f x} ≤
      C * ∫⁻ x, ‖f x‖ₑ

/-- Positive real thresholds suffice for the classical input; zero and
infinite ENNReal thresholds add no analytic requirement. -/
theorem hasUniformHilbertMaximalWeakBound_of_real
    {C : ℝ≥0∞} (hC : C < ∞)
    (hweak : ∀ (f : L0Infinity) (a : ℝ), 0 < a →
      ENNReal.ofReal a * volume {x | ENNReal.ofReal a < quadraticHilbertMaximalTruncation 0 f x} ≤
        C * ∫⁻ x, ‖f x‖ₑ) :
    HasUniformHilbertMaximalWeakBound C := by
  refine ⟨hC, fun f a ↦ ?_⟩
  by_cases ha : a = 0
  · simp only [ha, zero_mul, zero_le]
  by_cases hat : a = ∞
  · simp [hat]
  simpa only [ENNReal.ofReal_toReal hat] using
    hweak f a.toReal (ENNReal.toReal_pos ha hat)

noncomputable def schwartzResidual (f : L0Infinity) (g : 𝓢(ℝ, ℂ))
    (hg : HasCompactSupport (g : ℝ → ℂ)) : L0Infinity where
  toFun := fun x ↦ f x - g x
  measurable_toFun := f.measurable_toFun.sub g.continuous.measurable
  bounded_toFun := by
    obtain ⟨A, hA⟩ := f.bounded_toFun
    refine ⟨A + SchwartzMap.seminorm ℂ 0 0 g, fun x ↦ ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hA x) (g.norm_le_seminorm ℂ x))
  hasCompactSupport_toFun := f.hasCompactSupport_toFun.sub hg

/-- Actual smooth compactly supported `L¹` approximation, with an explicit
bound on the residual's absolute integral. -/
theorem exists_compactSchwartz_lintegral_residual_le
    (f : L0Infinity) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : 𝓢(ℝ, ℂ)) (hg : HasCompactSupport (g : ℝ → ℂ)),
      (∫⁻ x, ‖schwartzResidual f g hg x‖ₑ) ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hg, hgs, happrox⟩ := MeasureTheory.MemLp.exist_eLpNorm_sub_le
    (p := 1) (by norm_num) (by norm_num)
    (memLp_one_iff_integrable.mpr f.integrable) hε
  refine ⟨hg.toSchwartzMap hgs, hg, ?_⟩
  change (∫⁻ x, ‖f x - g x‖ₑ) ≤ ENNReal.ofReal ε
  simpa only [eLpNorm_one_eq_lintegral_enorm
    (f.integrable.aestronglyMeasurable.sub hgs.continuous.aestronglyMeasurable),
    Pi.sub_apply] using happrox

theorem zeroHilbertTrunc_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    quadraticHilbertTrunc 0 ε (fun y ↦ f y - g y) x =
      quadraticHilbertTrunc 0 ε f x - quadraticHilbertTrunc 0 ε g x := by
  unfold quadraticHilbertTrunc
  simp only [zero_mul, phase_zero, mul_one, sub_div]
  exact integral_sub (integrableOn_zeroHilbertTail hε hf x)
    (integrableOn_zeroHilbertTail hε hg x)

theorem norm_zeroHilbertTrunc_le_of_maximal_le
    (f : ℝ → ℂ) {a : ℝ} (ha : 0 ≤ a) {x ε : ℝ} (hε : 0 < ε)
    (hmax : quadraticHilbertMaximalTruncation 0 f x ≤ ENNReal.ofReal a) :
    ‖quadraticHilbertTrunc 0 ε f x‖ ≤ a := by
  apply (ENNReal.ofReal_le_ofReal_iff ha).mp
  rw [ofReal_norm]
  exact (le_iSup (fun δ : {δ : ℝ // 0 < δ} ↦
    ‖quadraticHilbertTrunc 0 δ.1 f x‖ₑ) ⟨ε, hε⟩).trans hmax

/-- A positive tail-oscillation obstruction to the Cauchy property. Its
outer measure suffices; no measurability of the uncountable quantifiers is
assumed. -/
def badHilbertCauchySet (f : ℝ → ℂ) (η : ℝ) : Set ℝ :=
  {x | ∀ δ : ℝ, 0 < δ → ∃ s : ℝ, 0 < s ∧ s < δ ∧
    ∃ t : ℝ, 0 < t ∧ t < δ ∧
      η < ‖quadraticHilbertTrunc 0 s f x - quadraticHilbertTrunc 0 t f x‖}

theorem principalValue_tail_pair_small
    {g : ℝ → ℂ} {x : ℝ} {w : ℂ}
    (hg : HasQuadraticPrincipalValue 0 g x w) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∀ t : ℝ, 0 < t → t < δ →
        ‖quadraticHilbertTrunc 0 s g x - quadraticHilbertTrunc 0 t g x‖ < η := by
  have he := hg (Metric.ball_mem_nhds w (by positivity : 0 < η / 2))
  obtain ⟨δ, hδ, hδsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (by norm_num : (0 : ℝ) < 1)).mp he
  refine ⟨δ, hδ, fun s hs hsδ t ht htδ ↦ ?_⟩
  have hsclose := hδsub ⟨hs, hsδ⟩
  have htclose := hδsub ⟨ht, htδ⟩
  change dist (quadraticHilbertTrunc 0 s g x) w < η / 2 at hsclose
  change dist (quadraticHilbertTrunc 0 t g x) w < η / 2 at htclose
  rw [← dist_eq_norm]
  have hh := dist_triangle (quadraticHilbertTrunc 0 s g x) w
    (quadraticHilbertTrunc 0 t g x)
  rw [dist_comm w] at hh
  linarith

/-- Smooth convergence and a uniformly small maximal residual exclude a
tail-oscillation obstruction for the original input. -/
theorem badHilbertCauchySet_subset_maximal_residual
    (f : L0Infinity) (g : 𝓢(ℝ, ℂ)) (hg : HasCompactSupport (g : ℝ → ℂ))
    {η : ℝ} (hη : 0 < η) :
    badHilbertCauchySet f η ⊆
      {x | ENNReal.ofReal (η / 4) < quadraticHilbertMaximalTruncation 0
        (schwartzResidual f g hg) x} := by
  intro x hx
  by_contra hnot
  change ¬ ENNReal.ofReal (η / 4) < quadraticHilbertMaximalTruncation 0
    (schwartzResidual f g hg) x at hnot
  have hmax := le_of_not_gt hnot
  obtain ⟨δ, hδ, hsmall⟩ := principalValue_tail_pair_small
    (hasQuadraticPrincipalValue_schwartz 0 g x) (by positivity : 0 < η / 2)
  obtain ⟨s, hs, hsδ, t, ht, htδ, hbad⟩ := hx δ hδ
  have hresS := norm_zeroHilbertTrunc_le_of_maximal_le (schwartzResidual f g hg)
    (by positivity : 0 ≤ η / 4) hs hmax
  have hresT := norm_zeroHilbertTrunc_le_of_maximal_le (schwartzResidual f g hg)
    (by positivity : 0 ≤ η / 4) ht hmax
  have hgs := hsmall s hs hsδ t ht htδ
  have heqS : quadraticHilbertTrunc 0 s (schwartzResidual f g hg) x =
      quadraticHilbertTrunc 0 s f x - quadraticHilbertTrunc 0 s g x :=
    zeroHilbertTrunc_sub f.integrable g.integrable hs x
  have heqT : quadraticHilbertTrunc 0 t (schwartzResidual f g hg) x =
      quadraticHilbertTrunc 0 t f x - quadraticHilbertTrunc 0 t g x :=
    zeroHilbertTrunc_sub f.integrable g.integrable ht x
  have hbound : ‖quadraticHilbertTrunc 0 s f x - quadraticHilbertTrunc 0 t f x‖ ≤
      ‖quadraticHilbertTrunc 0 s (schwartzResidual f g hg) x‖ +
        ‖quadraticHilbertTrunc 0 t (schwartzResidual f g hg) x‖ +
          ‖quadraticHilbertTrunc 0 s g x - quadraticHilbertTrunc 0 t g x‖ := by
    calc
      _ = ‖(quadraticHilbertTrunc 0 s (schwartzResidual f g hg) x -
          quadraticHilbertTrunc 0 t (schwartzResidual f g hg) x) +
            (quadraticHilbertTrunc 0 s g x - quadraticHilbertTrunc 0 t g x)‖ := by
        rw [heqS, heqT]
        congr 1
        ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  linarith

/-- Every positive Cauchy-obstruction level has outer measure zero. The
proof sends the actual smooth-approximation error to zero in `L¹`. -/
theorem volume_badHilbertCauchySet_eq_zero
    {C : ℝ≥0∞} (hweak : HasUniformHilbertMaximalWeakBound C)
    (f : L0Infinity) {η : ℝ} (hη : 0 < η) :
    volume (badHilbertCauchySet f η) = 0 := by
  have hbound {ε : ℝ} (hε : 0 < ε) :
      ENNReal.ofReal (η / 4) * volume (badHilbertCauchySet f η) ≤ C * ENNReal.ofReal ε := by
    obtain ⟨g, hg, happrox⟩ := exists_compactSchwartz_lintegral_residual_le f hε
    apply (mul_le_mul' le_rfl
      (measure_mono (badHilbertCauchySet_subset_maximal_residual f g hg hη))).trans
    exact (hweak.2 (schwartzResidual f g hg) (ENNReal.ofReal (η / 4))).trans
      (mul_le_mul' le_rfl happrox)
  have hlim : Tendsto (fun n : ℕ ↦ C * ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    have hreal := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have he := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    have hc := (ENNReal.continuous_const_mul hweak.1.ne).tendsto (ENNReal.ofReal 0)
    simpa only [ENNReal.ofReal_zero, mul_zero, Function.comp_def] using hc.comp he
  have hzero : ENNReal.ofReal (η / 4) * volume (badHilbertCauchySet f η) = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun n : ℕ ↦
      hbound (by positivity : 0 < 1 / ((n : ℝ) + 1)))) bot_le
  exact (mul_eq_zero.mp hzero).resolve_left
    (ENNReal.ofReal_pos.mpr (by positivity : 0 < η / 4)).ne'

/-- Vanishing of countably many positive Cauchy obstructions produces a
limit along the full right-hand neighborhood filter, not only a sequence. -/
theorem exists_principalValue_of_not_mem_badHilbertCauchySet
    (f : ℝ → ℂ) (x : ℝ)
    (hx : ∀ n : ℕ, x ∉ badHilbertCauchySet f (1 / ((n : ℝ) + 1))) :
    ∃ z : ℂ, HasQuadraticPrincipalValue 0 f x z := by
  apply cauchy_map_iff_exists_tendsto.mp
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance, fun ε hε ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  have hnobad := hx n
  change ¬ ∀ δ : ℝ, 0 < δ → ∃ s : ℝ, 0 < s ∧ s < δ ∧
    ∃ t : ℝ, 0 < t ∧ t < δ ∧
      1 / ((n : ℝ) + 1) <
        ‖quadraticHilbertTrunc 0 s f x - quadraticHilbertTrunc 0 t f x‖ at hnobad
  push Not at hnobad
  obtain ⟨δ, hδ, hp⟩ := hnobad
  let T : ℝ → ℂ := fun r ↦ quadraticHilbertTrunc 0 r f x
  refine ⟨T '' Ioo 0 δ, ?_, ?_⟩
  · change T ⁻¹' (T '' Ioo 0 δ) ∈ 𝓝[>] (0 : ℝ)
    exact mem_of_superset (Ioo_mem_nhdsGT hδ) fun r hr ↦ ⟨r, hr, rfl⟩
  · rintro u ⟨s, hs, rfl⟩ v ⟨t, ht, rfl⟩
    rw [dist_eq_norm]
    exact (hp s hs.1 hs.2 t ht.1 ht.2).trans_lt hn

/-- Density plus the uniform maximal weak estimate closes ordinary Hilbert
principal-value existence on the entire paper domain. -/
theorem ae_exists_ordinaryHilbert_principalValue
    {C : ℝ≥0∞} (hweak : HasUniformHilbertMaximalWeakBound C) (f : L0Infinity) :
    ∀ᵐ x, ∃ z : ℂ, HasQuadraticPrincipalValue 0 f x z := by
  have hn (n : ℕ) : ∀ᵐ x, x ∉ badHilbertCauchySet f (1 / ((n : ℝ) + 1)) := by
    exact ae_iff.mpr (by
      simpa only [not_not, ofPred_mem_eq] using volume_badHilbertCauchySet_eq_zero hweak f
        (by positivity : 0 < 1 / ((n : ℝ) + 1)))
  filter_upwards [ae_all_iff.mpr hn] with x hx
  exact exists_principalValue_of_not_mem_badHilbertCauchySet f x hx

/-- The same null set works for every real modulation, including zero. No
uncountable intersection of separately obtained almost-everywhere events is
taken: all modulations follow pointwise from the ordinary PV. -/
theorem ae_forall_real_exists_quadraticPrincipalValue
    {C : ℝ≥0∞} (hweak : HasUniformHilbertMaximalWeakBound C) (f : L0Infinity) :
    ∀ᵐ x, ∀ lam : ℝ, ∃ z : ℂ, HasQuadraticPrincipalValue lam f x z := by
  filter_upwards [ae_exists_ordinaryHilbert_principalValue hweak f] with x hx
  intro lam
  by_cases hlam : lam = 0
  · simpa only [hlam] using hx
  · exact (exists_quadraticPrincipalValue_iff_hilbert lam hlam f x).mpr hx

theorem ae_forall_lacunary_exists_quadraticPrincipalValue
    {C : ℝ≥0∞} (hweak : HasUniformHilbertMaximalWeakBound C) (f : L0Infinity) :
    ∀ᵐ x, ∀ m : ℤ, ∃ z : ℂ, HasQuadraticPrincipalValue (dyadicModulation m) f x z := by
  filter_upwards [ae_forall_real_exists_quadraticPrincipalValue hweak f] with x hx
  exact fun m ↦ hx (dyadicModulation m)

/-- The canonical limsup representative agrees with the genuine PV norm,
simultaneously at every real modulation outside a single null set. -/
theorem ae_forall_real_limsup_eq_principalValue_norm
    {C : ℝ≥0∞} (hweak : HasUniformHilbertMaximalWeakBound C) (f : L0Infinity) :
    ∀ᵐ x, ∀ lam : ℝ, ∃ z : ℂ, HasQuadraticPrincipalValue lam f x z ∧
      quadraticHilbertL0Limsup lam f x = ENNReal.ofReal ‖z‖ := by
  filter_upwards [ae_forall_real_exists_quadraticPrincipalValue hweak f] with x hx
  intro lam
  obtain ⟨z, hz⟩ := hx lam
  exact ⟨z, hz, quadraticHilbertL0Limsup_eq_of_principalValue lam f x z hz⟩


end HilbertPrincipalValueClosure
end QuadraticCarleson
