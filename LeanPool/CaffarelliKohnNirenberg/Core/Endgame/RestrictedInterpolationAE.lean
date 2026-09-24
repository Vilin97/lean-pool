/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.InterpolationRestricted
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.ENNRealHalfScale

/-! # Restricted interpolation with almost-everywhere sublinearity

This version of the restricted interpolation argument permits null exceptional
sets in sublinearity. The tail containment is interpreted modulo null sets;
the truncations, layer-cake argument, and numerical constant are unchanged
from `Foundation.Euclidean.InterpolationRestricted`.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Endgame

/-- The distribution-function bound for a splitting `f = f·1_s + f·1_{sᶜ}`, with the
sublinearity, weak `(1,1)` and strong `(2,2)` inputs already specialized to the two
pieces.  This is the analytic core of `tail_bound` with every hypothesis that the
proof actually uses spelled out. -/
private lemma tail_bound_of_pieces {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ : ℝ}
    {f : Vec3 → ℝ} {t : ℝ} (ht : 0 < t)
    {s : Set Vec3} (hsm : MeasurableSet s)
    (hsub : ∀ᵐ x ∂volume, |T (s.indicator f + sᶜ.indicator f) x| ≤
      |T (s.indicator f) x| + |T (sᶜ.indicator f) x|)
    (hTlow : Measurable (T (sᶜ.indicator f)))
    (hweak : volume {x | t / 2 < |T (s.indicator f) x|} ≤
      ENNReal.ofReal A₁ * (∫⁻ x, absE (s.indicator f) x) / ENNReal.ofReal (t / 2))
    (hstrong : ∫⁻ x, absE (T (sᶜ.indicator f)) x ^ 2 ≤
      ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE (sᶜ.indicator f) x ^ 2) :
    volume {x | t < |T f x|} ≤
      (ENNReal.ofReal (2 * A₁ / t) * ∫⁻ x in s, absE f x) +
        (ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2) := by
  have ht2 : 0 < t / 2 := by linarith only [ht]
  have hsplit : s.indicator f + sᶜ.indicator f = f := by
    funext x
    rw [Pi.add_apply]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx)]
      simp
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx)]
      simp
  have hTf : T f = T (s.indicator f + sᶜ.indicator f) := by rw [hsplit]
  have hsub' : {x : Vec3 | t < |T f x|} ≤ᵐ[volume]
      {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} ∪
        {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} := by
    filter_upwards [hsub] with x hsubx
    intro hx
    have hx' : t < |T (s.indicator f) x| + |T (sᶜ.indicator f) x| := by
      rw [hTf] at hx
      linarith only [hx, hsubx]
    rcases lt_or_ge (t / 2) (|T (s.indicator f) x|) with ha | ha
    · left
      simp only [Set.mem_ofPred_eq]
      show ENNReal.ofReal (t / 2) < ENNReal.ofReal |T (s.indicator f) x|
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht2.le]
      exact ha
    · right
      simp only [Set.mem_ofPred_eq]
      show ENNReal.ofReal (t / 2) < ENNReal.ofReal |T (sᶜ.indicator f) x|
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht2.le]
      linarith only [hx', ha]
  have h1 : volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} ≤
      ENNReal.ofReal (2 * A₁ / t) * ∫⁻ x in s, absE f x := by
    have hset : {x : Vec3 | t / 2 < |T (s.indicator f) x|} =
        {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      show t / 2 < |T (s.indicator f) x| ↔
        ENNReal.ofReal (t / 2) < ENNReal.ofReal |T (s.indicator f) x|
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht2.le]
    rw [hset] at hweak
    calc volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x}
        ≤ ENNReal.ofReal A₁ * (∫⁻ x in s, absE f x) / ENNReal.ofReal (t / 2) := by
          rw [← lintegral_absE_indicator hsm f]
          exact hweak
      _ = ENNReal.ofReal (2 * A₁ / t) * ∫⁻ x in s, absE f x := CKN.Foundation.Measure.ofReal_mul_div_ofReal_half ht _
  have h2 : volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} ≤
      ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2 := by
    have hmarkov := mul_meas_ge_le_lintegral (μ := volume)
      ((measurable_absE hTlow).pow_const 2) ((ENNReal.ofReal (t / 2)) ^ 2)
    have hsub2 : {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} ⊆
        {x : Vec3 | (ENNReal.ofReal (t / 2)) ^ 2 ≤ absE (T (sᶜ.indicator f)) x ^ 2} := by
      intro x hx
      exact ENNReal.pow_le_pow_left hx.le
    have hchain : (ENNReal.ofReal (t / 2)) ^ 2 *
        volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} ≤
        ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2 := by
      calc (ENNReal.ofReal (t / 2)) ^ 2 *
            volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x}
          ≤ (ENNReal.ofReal (t / 2)) ^ 2 *
            volume {x : Vec3 |
              (ENNReal.ofReal (t / 2)) ^ 2 ≤ absE (T (sᶜ.indicator f)) x ^ 2} :=
            mul_le_mul' le_rfl (measure_mono hsub2)
        _ ≤ ∫⁻ x, absE (T (sᶜ.indicator f)) x ^ 2 := hmarkov
        _ ≤ ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2 := by
            rw [← lintegral_absE_indicator_sq hsm.compl f]
            exact hstrong
    have hcne : (ENNReal.ofReal (t / 2)) ^ 2 ≠ 0 :=
      ENNReal.pow_ne_zero (by rw [ENNReal.ofReal_ne_zero_iff]; exact ht2) 2
    have hctop : (ENNReal.ofReal (t / 2)) ^ 2 ≠ ∞ :=
      ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hvol : volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} ≤
        ENNReal.ofReal (A₂ ^ 2) * (∫⁻ x in sᶜ, absE f x ^ 2) /
          (ENNReal.ofReal (t / 2)) ^ 2 :=
      (ENNReal.le_div_iff_mul_le (Or.inl hcne) (Or.inl hctop)).mpr (by
        rw [mul_comm]
        exact hchain)
    calc volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x}
        ≤ ENNReal.ofReal (A₂ ^ 2) * (∫⁻ x in sᶜ, absE f x ^ 2) /
            (ENNReal.ofReal (t / 2)) ^ 2 := hvol
      _ = ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2 :=
          CKN.Foundation.Measure.ofReal_mul_div_ofReal_half_sq ht _
  calc volume {x : Vec3 | t < |T f x|}
      ≤ volume ({x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} ∪
          {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x}) :=
        measure_mono_ae hsub'
    _ ≤ volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (s.indicator f)) x} +
        volume {x : Vec3 | ENNReal.ofReal (t / 2) < absE (T (sᶜ.indicator f)) x} :=
        measure_union_le _ _
    _ ≤ (ENNReal.ofReal (2 * A₁ / t) * ∫⁻ x in s, absE f x) +
        (ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * ∫⁻ x in sᶜ, absE f x ^ 2) :=
        add_le_add h1 h2

/-! ### The layer-cake integration -/

/-- The layer-cake half of the interpolation theorem: the distribution-function
bound at every level, integrated against the weight `p t^{p-1}`.  This is the proof
of `interpolation_weak11_strong22` with the tail estimate taken as a hypothesis. -/
private lemma interpolation_of_tail_bound {T : (Vec3 → ℝ) → (Vec3 → ℝ)} {A₁ A₂ p : ℝ}
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2) {f : Vec3 → ℝ} (hf : Measurable f)
    (hTf : Measurable (T f))
    (htail : ∀ t : ℝ, 0 < t → volume {x | t < |T f x|} ≤
      ENNReal.ofReal (2 * A₁ / t) * highTail (absE f) t +
        ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * lowTail (absE f) t) :
    ∫⁻ x, absE (T f) x ^ p ≤
      ENNReal.ofReal (p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))) *
        ∫⁻ x, absE f x ^ p := by
  have hp0 : (0 : ℝ) ≤ p := by linarith only [hp1]
  have hM : Measurable (absE f) := measurable_absE hf
  have hMfin : ∀ x, absE f x < ∞ := fun _ => ENNReal.ofReal_lt_top
  let _ : SFinite (volume : Measure Vec3) := inferInstance
  have hF1 : AEMeasurable (fun t : ℝ => ENNReal.ofReal (2 * A₁) *
      (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_weightedHighIntegrand hM (p := p)).lintegral_prod_right.congr
      (Eventually.of_forall fun t => inner_High_eq hM t)).const_mul _
  calc ∫⁻ x, absE (T f) x ^ p
      = ∫⁻ t in Ioi (0 : ℝ), volume {x | t < |T f x|} * ENNReal.ofReal (p * t ^ (p - 1)) :=
        layer_cake hTf hp1
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 * A₁ / t) * highTail (absE f) t +
            ENNReal.ofReal (4 * A₂ ^ 2 / t ^ 2) * lowTail (absE f) t) *
          ENNReal.ofReal (p * t ^ (p - 1)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_le_mul_left (htail t ht) _
    _ = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
          (ENNReal.ofReal (2 * A₁) *
              (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t) +
            ENNReal.ofReal (4 * A₂ ^ 2) *
              (ENNReal.ofReal (rpowExt (p - 3) t) * lowTail (absE f) t)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        rw [interp_integrand hA₁ hp1 ht, ← rpowExt_eq (a := p - 2) ht,
          ← rpowExt_eq (a := p - 3) ht]
    _ = ENNReal.ofReal p *
          ((∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * A₁) *
              (ENNReal.ofReal (rpowExt (p - 2) t) * highTail (absE f) t)) +
            (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (4 * A₂ ^ 2) *
              (ENNReal.ofReal (rpowExt (p - 3) t) * lowTail (absE f) t))) := by
        rw [lintegral_add_left' hF1]
    _ = ENNReal.ofReal p *
          (ENNReal.ofReal (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p))) *
            ∫⁻ x, absE f x ^ p) := by
        rw [weighted_combined hM hMfin hA₁ hp1 hp2]
    _ = ENNReal.ofReal (p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))) *
          ∫⁻ x, absE f x ^ p := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hp0]


/-- Restricted weak and strong endpoint bounds interpolate when sublinearity
holds almost everywhere on the actual L² input class. -/
theorem interpolation_weak11_strong22_of_l2_classes_ae {T : (Vec3 → ℝ) → (Vec3 → ℝ)}
    {A₁ A₂ p : ℝ}
    (hTsub : ∀ f g, Measurable f → Integrable f volume → MemLp f 2 volume →
      Measurable g → MemLp g 2 volume → ∀ᵐ x ∂volume, |T (f + g) x| ≤ |T f x| + |T g x|)
    (hTmeas : ∀ f, Measurable f → MemLp f 2 volume → Measurable (T f))
    (hweak : ∀ f, Measurable f → Integrable f volume → MemLp f 2 volume →
      ∀ l : ℝ, 0 < l →
        volume {x | l < |T f x|} ≤
          ENNReal.ofReal A₁ * (∫⁻ x, absE f x) / ENNReal.ofReal l)
    (hstrong : ∀ f, Measurable f → MemLp f 2 volume →
      ∫⁻ x, absE (T f) x ^ 2 ≤ ENNReal.ofReal (A₂ ^ 2) * ∫⁻ x, absE f x ^ 2)
    (hA₁ : 0 ≤ A₁) (hp1 : 1 < p) (hp2 : p < 2) {f : Vec3 → ℝ} (hf : Measurable f)
    (hfp : MemLp f (ENNReal.ofReal p) volume) (hf2 : MemLp f 2 volume) :
    ∫⁻ x, absE (T f) x ^ p ≤
      ENNReal.ofReal (p * (2 ^ p * (A₁ / (p - 1) + A₂ ^ 2 / (2 - p)))) *
        ∫⁻ x, absE f x ^ p := by
  refine interpolation_of_tail_bound hA₁ hp1 hp2 hf (hTmeas f hf hf2) ?_
  intro t ht
  have ht2 : (0 : ℝ) < t / 2 := by linarith only [ht]
  have hsm : MeasurableSet (absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2))) :=
    measurableSet_Ioi.preimage (measurable_absE hf)
  have hscompl : (absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2)))ᶜ =
      absE f ⁻¹' Iic (ENNReal.ofReal (t / 2)) := by
    rw [← Set.preimage_compl, Set.compl_Ioi]
  have hf₁ : Measurable ((absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2))).indicator f) :=
    hf.indicator hsm
  have hf₂ : Measurable ((absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2)))ᶜ.indicator f) :=
    hf.indicator hsm.compl
  have hint₁ : Integrable ((absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2))).indicator f) volume :=
    integrable_indicator_gt_of_memLp hf hp1 hfp ht2
  have hmem₁ : MemLp ((absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2))).indicator f) 2 volume :=
    hf2.indicator hsm
  have hmem₂ : MemLp ((absE f ⁻¹' Ioi (ENNReal.ofReal (t / 2)))ᶜ.indicator f) 2 volume :=
    hf2.indicator hsm.compl
  have hcore := tail_bound_of_pieces (T := T) (A₁ := A₁) (A₂ := A₂) (f := f) ht hsm
    (hTsub _ _ hf₁ hint₁ hmem₁ hf₂ hmem₂) (hTmeas _ hf₂ hmem₂)
    (hweak _ hf₁ hint₁ hmem₁ (t / 2) ht2) (hstrong _ hf₂ hmem₂)
  rw [hscompl] at hcore
  simpa only [highTail, lowTail] using hcore


end CKN.Core.Endgame
