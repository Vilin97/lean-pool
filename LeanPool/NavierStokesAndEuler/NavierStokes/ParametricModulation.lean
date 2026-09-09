/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialModulation
public import LeanPool.NavierStokesAndEuler.NavierStokes.TrueConeLoop
public import LeanPool.NavierStokesAndEuler.NavierStokes.ParametricRephase
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Joint periodic primitives and realization of the constructed true-cone loops

The primitives in this file are actual normalized interval integrals. Their
joint smoothness is derived through compact-interval parameter integration.
-/

noncomputable section

namespace NavierStokes.ParametricModulation

open Set Filter MeasureTheory Function
open scoped Topology ContDiff


variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def primitiveFamily (q : P × ℝ → ℝ) (z : P × ℝ) : ℝ :=
  RadialModulation.periodicPrimitive (fun θ => q (z.1, θ)) z.2

def normalizedPrimitiveFamily (q : P × ℝ → ℝ) (z : P × ℝ) : ℝ :=
  RadialModulation.zeroMeanPrimitive (fun θ => q (z.1, θ)) z.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The variable-endpoint integral is an integral over the fixed unit interval. -/
theorem primitiveFamily_unit_interval (q : P × ℝ → ℝ) (z : P × ℝ) :
    primitiveFamily q z = z.2 * intervalIntegral (fun s => q (z.1, z.2 * s)) 0 1 volume := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun θ => q (z.1, θ)) z.2 (a := 0) (b := 1)
  simpa only [primitiveFamily, RadialModulation.periodicPrimitive, smul_eq_mul,
    mul_zero, mul_one] using h.symm

/-- Joint smoothness of the actual primitive; all domination comes from the
compact integration interval, through `SmoothParameterIntegral`. -/
theorem primitiveFamily_contDiffOn
    (q : P × ℝ → ℝ) (U : Set P) (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (primitiveFamily q) (U ×ˢ (univ : Set ℝ)) := by
  let F : (P × ℝ) × ℝ → ℝ := fun z => q (z.1.1, z.1.2 * z.2)
  have hF : ContDiffOn ℝ ∞ F ((U ×ˢ (univ : Set ℝ)) ×ˢ (univ : Set ℝ)) :=
    hq.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd)).contDiffOn
      (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  have hi := ParametricRephase.intervalIntegral_contDiffOn_of_joint F
    (U ×ˢ (univ : Set ℝ)) (hU.prod isOpen_univ) hF 0 1 (by norm_num)
  have heq : primitiveFamily q =
      (fun z => z.2 * intervalIntegral (fun s => F (z, s)) 0 1 volume) :=
    funext (primitiveFamily_unit_interval q)
  rw [heq]
  exact contDiff_snd.contDiffOn.mul hi

/-- Subtracting the actual parameter-dependent mean preserves joint smoothness. -/
theorem normalizedPrimitiveFamily_contDiffOn
    (q : P × ℝ → ℝ) (U : Set P) (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ (univ : Set ℝ))) :
    ContDiffOn ℝ ∞ (normalizedPrimitiveFamily q) (U ×ˢ (univ : Set ℝ)) := by
  have hp := primitiveFamily_contDiffOn q U hU hq
  have hm := ParametricRephase.intervalIntegral_contDiffOn_of_joint
    (primitiveFamily q) U hU hp 0 1 (by norm_num)
  exact hp.sub (hm.comp contDiff_fst.contDiffOn (fun _ hz => hz.1))

omit [FiniteDimensional ℝ P] in
theorem source_slice_contDiff
    (q : P × ℝ → ℝ) (U : Set P)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ (univ : Set ℝ))) (p : P) (hp : p ∈ U) :
    ContDiff ℝ ∞ (fun θ => q (p, θ)) := by
  apply hq.comp_contDiff (contDiff_const.prodMk contDiff_id)
  intro θ
  exact ⟨hp, mem_univ θ⟩

omit [FiniteDimensional ℝ P] in
theorem normalizedPrimitiveFamily_hasDerivAt
    (q : P × ℝ → ℝ) (U : Set P)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ (univ : Set ℝ))) (p : P) (hp : p ∈ U) (θ : ℝ) :
    HasDerivAt (fun s => normalizedPrimitiveFamily q (p, s)) (q (p, θ)) θ :=
  RadialModulation.zeroMeanPrimitive_hasDerivAt _
    (source_slice_contDiff q U hq p hp).continuous θ

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem normalizedPrimitiveFamily_periodic
    (q : P × ℝ → ℝ) (p : P) (hq : Continuous (fun θ => q (p, θ)))
    (hper : Function.Periodic (fun θ => q (p, θ)) 1)
    (hmean : intervalIntegral (fun θ => q (p, θ)) 0 1 volume = 0) :
    Function.Periodic (fun θ => normalizedPrimitiveFamily q (p, θ)) 1 := by
  intro θ
  unfold normalizedPrimitiveFamily RadialModulation.zeroMeanPrimitive
  dsimp only
  rw [RadialModulation.periodicPrimitive_periodic _ hq hper hmean θ]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem normalizedPrimitiveFamily_mean_zero
    (q : P × ℝ → ℝ) (p : P) (hq : Continuous (fun θ => q (p, θ))) :
    intervalIntegral (fun θ => normalizedPrimitiveFamily q (p, θ)) 0 1 volume = 0 :=
  RadialModulation.zeroMeanPrimitive_integral _ hq

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- Exact vanishing, including the mean normalization, when the loop is nominal. -/
theorem normalizedPrimitiveFamily_zero
    (q : P × ℝ → ℝ) (p : P) (hq : ∀ θ, q (p, θ) = 0) (θ : ℝ) :
    normalizedPrimitiveFamily q (p, θ) = 0 := by
  unfold normalizedPrimitiveFamily RadialModulation.zeroMeanPrimitive
    RadialModulation.periodicPrimitive
  simp only [hq, intervalIntegral.integral_zero, sub_zero]

/-- A cutoff which equals one around K and vanishes locally outside U. -/
structure CompactCutoff (K U : Set P) where
  value : P → ℝ
  smooth : ContDiff ℝ ∞ value
  neighborhood : Set P
  open_neighborhood : IsOpen neighborhood
  contains : K ⊆ neighborhood
  subset_domain : neighborhood ⊆ U
  one_on : ∀ p ∈ neighborhood, value p = 1
  zero_near : ∀ p, p ∉ U → value =ᶠ[𝓝 p] (fun _ => 0)

/-- A smooth plateau cutoff is constructed from a smooth function supported
exactly on U and its positive minimum over K. -/
theorem exists_compactCutoff (K U : Set P) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    Nonempty (CompactCutoff K U) := by
  obtain ⟨f, hsupp, hf, hrange⟩ := hU.exists_contDiff_support_eq
  have hnonneg : ∀ p, 0 ≤ f p := fun p => (hrange (mem_range_self p)).1
  have hpos : ∀ p ∈ K, 0 < f p := by
    intro p hp
    have hn : f p ≠ 0 := by simpa only [← hsupp, mem_support] using hKU hp
    exact lt_of_le_of_ne (hnonneg p) (Ne.symm hn)
  obtain ⟨δ, hδ, hδf⟩ := UniformCone.positive_uniform_margin hK hf.continuous.continuousOn hpos
  let O : Set P := {p | δ / 2 < f p}
  let χ : P → ℝ := fun p => Real.smoothTransition ((f p - δ / 4) / (δ / 4))
  have hd4 : 0 < δ / 4 := by positivity
  have hχ : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((hf.sub contDiff_const).div_const _)
  have hO : IsOpen O := isOpen_lt continuous_const hf.continuous
  have hKO : K ⊆ O := by
    intro p hp
    exact lt_of_lt_of_le (by linarith) (hδf p hp)
  have hOU : O ⊆ U := by
    intro p hp
    rw [← hsupp, mem_support]
    have hfp : 0 < f p := lt_trans (by positivity : 0 < δ / 2) hp
    exact ne_of_gt hfp
  have hχone : ∀ p ∈ O, χ p = 1 := by
    intro p hp
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hd4).mpr
    dsimp [O] at hp
    linarith
  have hχzero : ∀ p, p ∉ U → χ =ᶠ[𝓝 p] (fun _ => 0) := by
    intro p hp
    have hfp : f p = 0 := by
      have hn : p ∉ support f := by simpa only [hsupp] using hp
      simpa only [mem_support, not_not] using hn
    have hnear : ∀ᶠ y in 𝓝 p, f y < δ / 4 :=
      hf.continuous.continuousAt.eventually (gt_mem_nhds (by simpa only [hfp] using hd4))
    filter_upwards [hnear] with y hy
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hd4.le
  exact ⟨⟨χ, hχ, O, hO, hKO, hOU, hχone, hχzero⟩⟩

omit [FiniteDimensional ℝ P] in
/-- Multiplication by the constructed cutoff extends a locally smooth periodic
profile to a globally smooth function, unchanged around K. -/
theorem CompactCutoff.mul_contDiff
    {K U : Set P} (χ : CompactCutoff K U) (hU : IsOpen U)
    (f : P × ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f (U ×ˢ (univ : Set ℝ))) :
    ContDiff ℝ ∞ (fun z : P × ℝ => χ.value z.1 * f z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z.1 ∈ U
  · exact (χ.smooth.contDiffAt.comp z contDiffAt_fst).mul
      (hf.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hz, mem_univ _⟩))
  · have hzero : (fun w : P × ℝ => χ.value w.1 * f w) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(χ.zero_near z.1 hz).comp_tendsto continuous_fst.continuousAt] with w hw
      change χ.value w.1 = 0 at hw
      rw [hw, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

def centeredSource (f : P × ℝ → ℝ) (m c : P → ℝ) (z : P × ℝ) : ℝ :=
  c z.1 * (f z - m z.1)

def extendedPrimitive {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ) (z : P × ℝ) : ℝ :=
  χ.value z.1 * normalizedPrimitiveFamily (centeredSource f m c) z

omit [FiniteDimensional ℝ P] in
theorem centeredSource_contDiffOn
    (f : P × ℝ → ℝ) (m c : P → ℝ) (U : Set P)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ (univ : Set ℝ)))
    (hm : ContDiff ℝ ∞ m) (hc : ContDiff ℝ ∞ c) :
    ContDiffOn ℝ ∞ (centeredSource f m c) (U ×ˢ (univ : Set ℝ)) :=
  (hc.comp contDiff_fst).contDiffOn.mul (hf.sub (hm.comp contDiff_fst).contDiffOn)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem centeredSource_periodic
    (f : P × ℝ → ℝ) (m c : P → ℝ) (p : P)
    (hf : Function.Periodic (fun θ => f (p, θ)) 1) :
    Function.Periodic (fun θ => centeredSource f m c (p, θ)) 1 := by
  intro θ
  change c p * (f (p, θ + 1) - m p) = c p * (f (p, θ) - m p)
  have h : f (p, θ + 1) = f (p, θ) := hf θ
  rw [h]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem centeredSource_mean_zero
    (f : P × ℝ → ℝ) (m c : P → ℝ) (p : P)
    (hf : Continuous (fun θ => f (p, θ)))
    (hm : intervalIntegral (fun θ => f (p, θ)) 0 1 volume = m p) :
    intervalIntegral (fun θ => centeredSource f m c (p, θ)) 0 1 volume = 0 := by
  change intervalIntegral (fun θ => c p * (f (p, θ) - m p)) 0 1 volume = 0
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)]
  simp [hm]

theorem extendedPrimitive_contDiff
    {K U : Set P} (χ : CompactCutoff K U) (hU : IsOpen U)
    (f : P × ℝ → ℝ) (m c : P → ℝ)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ (univ : Set ℝ)))
    (hm : ContDiff ℝ ∞ m) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (extendedPrimitive χ f m c) :=
  χ.mul_contDiff hU _ (normalizedPrimitiveFamily_contDiffOn _ U hU
    (centeredSource_contDiffOn f m c U hf hm hc))

omit [FiniteDimensional ℝ P] in
theorem extendedPrimitive_periodic
    {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ)
    (hf : ∀ p ∈ U, Continuous (fun θ => f (p, θ)))
    (hper : ∀ p ∈ U, Function.Periodic (fun θ => f (p, θ)) 1)
    (hm : ∀ p ∈ U, intervalIntegral (fun θ => f (p, θ)) 0 1 volume = m p)
    (p : P) : Function.Periodic (fun θ => extendedPrimitive χ f m c (p, θ)) 1 := by
  by_cases hp : p ∈ U
  · have hq : Continuous (fun θ => centeredSource f m c (p, θ)) := by
      change Continuous (fun θ => c p * (f (p, θ) - m p))
      exact continuous_const.mul ((hf p hp).sub continuous_const)
    have hP := normalizedPrimitiveFamily_periodic _ p hq
      (centeredSource_periodic f m c p (hper p hp))
      (centeredSource_mean_zero f m c p (hf p hp) (hm p hp))
    intro θ
    change χ.value p * normalizedPrimitiveFamily (centeredSource f m c) (p, θ + 1) =
      χ.value p * normalizedPrimitiveFamily (centeredSource f m c) (p, θ)
    have h : normalizedPrimitiveFamily (centeredSource f m c) (p, θ + 1) =
        normalizedPrimitiveFamily (centeredSource f m c) (p, θ) := hP θ
    rw [h]
  · have hz : χ.value p = 0 := (χ.zero_near p hp).eq_of_nhds
    intro θ
    simp [extendedPrimitive, hz]

omit [FiniteDimensional ℝ P] in
theorem extendedPrimitive_mean_zero
    {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ)
    (hf : ∀ p ∈ U, Continuous (fun θ => f (p, θ))) (p : P) :
    intervalIntegral (fun θ => extendedPrimitive χ f m c (p, θ)) 0 1 volume = 0 := by
  by_cases hp : p ∈ U
  · have hq : Continuous (fun θ => centeredSource f m c (p, θ)) := by
      change Continuous (fun θ => c p * (f (p, θ) - m p))
      exact continuous_const.mul ((hf p hp).sub continuous_const)
    change intervalIntegral
      (fun θ => χ.value p * normalizedPrimitiveFamily (centeredSource f m c) (p, θ))
      0 1 volume = 0
    rw [intervalIntegral.integral_const_mul, normalizedPrimitiveFamily_mean_zero _ p hq,
      mul_zero]
  · have hz : χ.value p = 0 := (χ.zero_near p hp).eq_of_nhds
    simp [extendedPrimitive, hz]

omit [FiniteDimensional ℝ P] in
theorem extendedPrimitive_hasDerivAt
    {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ)
    (hf : ∀ p ∈ U, Continuous (fun θ => f (p, θ)))
    (p : P) (hp : p ∈ K) (θ : ℝ) :
    HasDerivAt (fun s => extendedPrimitive χ f m c (p, s))
      (c p * (f (p, θ) - m p)) θ := by
  have hq : Continuous (fun θ => centeredSource f m c (p, θ)) := by
    change Continuous (fun θ => c p * (f (p, θ) - m p))
    exact continuous_const.mul ((hf p (χ.subset_domain (χ.contains hp))).sub continuous_const)
  have hd := (RadialModulation.zeroMeanPrimitive_hasDerivAt
    (fun θ => centeredSource f m c (p, θ)) hq θ).const_mul (χ.value p)
  simpa only [extendedPrimitive, normalizedPrimitiveFamily, centeredSource,
    χ.one_on p (χ.contains hp), one_mul] using hd

omit [FiniteDimensional ℝ P] in
theorem extendedPrimitive_zero
    {K U : Set P} (χ : CompactCutoff K U)
    (f : P × ℝ → ℝ) (m c : P → ℝ) (p : P)
    (hf : ∀ θ, f (p, θ) = m p) (θ : ℝ) :
    extendedPrimitive χ f m c (p, θ) = 0 := by
  have hq : ∀ θ, centeredSource f m c (p, θ) = 0 := by
    intro s
    simp only [centeredSource, hf s, sub_self, mul_zero]
  unfold extendedPrimitive
  rw [normalizedPrimitiveFamily_zero _ p hq θ, mul_zero]

/-- The only choice data are the already constructed true-cone loop parameters
and an actual smooth compact-set cutoff. Primitives below are defined by integrals. -/
structure TrueConeRealization (a m p₁ p₂ : P → ℝ) (K B : Set P) where
  choices : TrueConeLoop.FamilyChoices a m p₁ p₂ K B
  cutoff : CompactCutoff K {p | 0 < a p}

theorem exists_trueConeRealization
    (a m p₁ p₂ : P → ℝ) (K B : Set P)
    (hK : IsCompact K) (hB : IsCompact B)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (haK : ∀ p ∈ K, 0 < a p) (hPK : ∀ p ∈ K, 2 < p₁ p + p₂ p * m p)
    (htrueB : ∀ p ∈ B, 2 < TrueConeLoop.nominalSpeed (a p) (m p)) :
    Nonempty (TrueConeRealization a m p₁ p₂ K B) := by
  obtain ⟨c⟩ := TrueConeLoop.exists_family_choices a m p₁ p₂ hK hB
    ha.continuous hm.continuous hp₁.continuous hp₂.continuous haK hPK htrueB
  obtain ⟨χ⟩ := exists_compactCutoff K {p | 0 < a p} hK
    (isOpen_lt continuous_const ha.continuous) haK
  exact ⟨⟨c, χ⟩⟩

namespace TrueConeRealization

variable {a m p₁ p₂ : P → ℝ} {K B : Set P}

def angularLoop (r : TrueConeRealization a m p₁ p₂ K B) : P × ℝ → ℝ :=
  TrueConeLoop.familyA a m p₂ r.choices.d r.choices.delta
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos

/-- This is the signed loop coordinate `-b_L`, in the convention of TrueConeLoop. -/
def signedAxialLoop (r : TrueConeRealization a m p₁ p₂ K B) : P × ℝ → ℝ :=
  TrueConeLoop.familyC a m p₂ r.choices.d r.choices.delta
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos

def angularPrimitive (r : TrueConeRealization a m p₁ p₂ K B) : P × ℝ → ℝ :=
  extendedPrimitive r.cutoff r.angularLoop a (fun _ => -1 / 2)

def axialPrimitive (r : TrueConeRealization a m p₁ p₂ K B) (E : P → ℝ) : P × ℝ → ℝ :=
  extendedPrimitive r.cutoff r.signedAxialLoop (fun p => a p * m p) (fun p => -E p / 2)

theorem loop_smooth (r : TrueConeRealization a m p₁ p₂ K B)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂) :
    ContDiffOn ℝ ∞ r.angularLoop ({p | 0 < a p} ×ˢ (univ : Set ℝ)) ∧
      ContDiffOn ℝ ∞ r.signedAxialLoop ({p | 0 < a p} ×ˢ (univ : Set ℝ)) :=
  TrueConeLoop.family_joint_contDiffOn a m p₂ r.choices.d r.choices.delta ha hm hp₂
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos

omit [FiniteDimensional ℝ P] in
theorem loop_periods_means (r : TrueConeRealization a m p₁ p₂ K B)
    (p : P) (hp : 0 < a p) :
    Function.Periodic (fun θ => r.angularLoop (p, θ)) 1 ∧
      Function.Periodic (fun θ => r.signedAxialLoop (p, θ)) 1 ∧
      intervalIntegral (fun θ => r.angularLoop (p, θ)) 0 1 volume = a p ∧
      intervalIntegral (fun θ => r.signedAxialLoop (p, θ)) 0 1 volume = a p * m p := by
  have hA := TrueConeLoop.familyA_eq_constructed a m p₂ r.choices.d r.choices.delta
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos p hp
  have hC := TrueConeLoop.familyC_eq_constructed a m p₂ r.choices.d r.choices.delta
    (ne_of_gt r.choices.d_pos) r.choices.delta_pos p hp
  have hper := TrueConeLoop.constructed_periodic (a p) (m p) r.choices.d (p₂ p)
    r.choices.delta hp (ne_of_gt r.choices.d_pos) r.choices.delta_pos
  have hmean := TrueConeLoop.constructed_means (a p) (m p) r.choices.d (p₂ p)
    r.choices.delta hp (ne_of_gt r.choices.d_pos) r.choices.delta_pos
  change Function.Periodic _ 1 ∧ Function.Periodic _ 1 ∧ _ = _ ∧ _ = _
  simpa only [angularLoop, signedAxialLoop, hA, hC] using
    And.intro hper.1 (And.intro hper.2 hmean)

theorem primitives_smooth (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₂ : ContDiff ℝ ∞ p₂) (hE : ContDiff ℝ ∞ E) :
    ContDiff ℝ ∞ r.angularPrimitive ∧ ContDiff ℝ ∞ (r.axialPrimitive E) := by
  have hs := r.loop_smooth ha hm hp₂
  have hU : IsOpen {p | 0 < a p} := isOpen_lt continuous_const ha.continuous
  exact ⟨extendedPrimitive_contDiff r.cutoff hU _ _ _ hs.1 ha contDiff_const,
    extendedPrimitive_contDiff r.cutoff hU _ _ _ hs.2 (ha.mul hm) (hE.neg.div_const 2)⟩

theorem primitives_periodic (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₂ : ContDiff ℝ ∞ p₂) (p : P) :
    Function.Periodic (fun θ => r.angularPrimitive (p, θ)) 1 ∧
      Function.Periodic (fun θ => r.axialPrimitive E (p, θ)) 1 := by
  have hs := r.loop_smooth ha hm hp₂
  have hca := fun p hp => (source_slice_contDiff _ _ hs.1 p hp).continuous
  have hcb := fun p hp => (source_slice_contDiff _ _ hs.2 p hp).continuous
  exact ⟨extendedPrimitive_periodic r.cutoff _ _ _ hca
      (fun p hp => (r.loop_periods_means p hp).1)
      (fun p hp => (r.loop_periods_means p hp).2.2.1) p,
    extendedPrimitive_periodic r.cutoff _ _ _ hcb
      (fun p hp => (r.loop_periods_means p hp).2.1)
      (fun p hp => (r.loop_periods_means p hp).2.2.2) p⟩

theorem primitives_mean_zero (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₂ : ContDiff ℝ ∞ p₂) (p : P) :
    intervalIntegral (fun θ => r.angularPrimitive (p, θ)) 0 1 volume = 0 ∧
      intervalIntegral (fun θ => r.axialPrimitive E (p, θ)) 0 1 volume = 0 := by
  have hs := r.loop_smooth ha hm hp₂
  exact ⟨extendedPrimitive_mean_zero r.cutoff _ _ _
      (fun p hp => (source_slice_contDiff _ _ hs.1 p hp).continuous) p,
    extendedPrimitive_mean_zero r.cutoff _ _ _
      (fun p hp => (source_slice_contDiff _ _ hs.2 p hp).continuous) p⟩

theorem primitive_derivatives (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₂ : ContDiff ℝ ∞ p₂) (p : P) (hp : p ∈ K) (θ : ℝ) :
    HasDerivAt (fun s => r.angularPrimitive (p, s))
        (-(r.angularLoop (p, θ) - a p) / 2) θ ∧
      HasDerivAt (fun s => r.axialPrimitive E (p, s))
        (E p * (-r.signedAxialLoop (p, θ) + a p * m p) / 2) θ := by
  have hs := r.loop_smooth ha hm hp₂
  have hca := fun p hp => (source_slice_contDiff _ _ hs.1 p hp).continuous
  have hcb := fun p hp => (source_slice_contDiff _ _ hs.2 p hp).continuous
  constructor
  · apply (extendedPrimitive_hasDerivAt r.cutoff _ a (fun _ => -1 / 2) hca p hp θ).congr_deriv
    ring
  · apply (extendedPrimitive_hasDerivAt r.cutoff _ (fun p => a p * m p)
      (fun p => -E p / 2) hcb p hp θ).congr_deriv
    ring

omit [FiniteDimensional ℝ P] in
theorem boundary_vanishing (r : TrueConeRealization a m p₁ p₂ K B)
    (E : P → ℝ) (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K) :
    ∃ N : Set P, IsOpen N ∧ B ⊆ N ∧ ∀ p ∈ N, ∀ θ,
      r.angularPrimitive (p, θ) = 0 ∧ r.axialPrimitive E (p, θ) = 0 := by
  obtain ⟨N, hN, hBN, hNU, hn⟩ := TrueConeLoop.family_nominal_neighborhood a m p₁ p₂
    r.choices ha.continuous hm.continuous hBK
  refine ⟨N, hN, hBN, ?_⟩
  intro p hp θ
  exact ⟨extendedPrimitive_zero r.cutoff _ _ _ p (fun s => (hn p hp s).1) θ,
    extendedPrimitive_zero r.cutoff _ _ _ p (fun s => (hn p hp s).2) θ⟩

omit [FiniteDimensional ℝ P] in
theorem loop_trueCone (r : TrueConeRealization a m p₁ p₂ K B)
    (hrelaxed : ∀ p ∈ K, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p)) :
    ∀ p ∈ K, ∀ θ, TrueConeLoop.InTrueCone (p₁ p) (p₂ p)
      (r.angularLoop (p, θ)) (r.signedAxialLoop (p, θ)) := by
  intro p hp θ
  exact (TrueConeLoop.family_pointwise_properties a m p₁ p₂ r.choices hrelaxed p hp).2.2.2.2 θ

end TrueConeRealization

section RadialProfiles

abbrev RadialParameter := ℝ × ℝ

/-- Reassociation between slow-parameter/angle coordinates and the radial
modulation module's `(X,η,θ)` coordinates. -/
def asRadialPrimitive (Q : RadialParameter × ℝ → ℝ) : RadialModulation.PrimitiveProfile :=
  fun z => Q ((z.1, z.2.1), z.2.2)

theorem asRadialPrimitive_contDiff
    (Q : RadialParameter × ℝ → ℝ) (hQ : ContDiff ℝ ∞ Q) :
    ContDiff ℝ ∞ (asRadialPrimitive Q) :=
  hQ.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)

variable {a m p₁ p₂ : RadialParameter → ℝ} {K B : Set RadialParameter}

def realizedE (r : TrueConeRealization a m p₁ p₂ K B) (E : RadialParameter → ℝ)
    (n X η : ℝ) : ℝ :=
  RadialModulation.modulatedE n (fun X η => E (X, η))
    (asRadialPrimitive r.angularPrimitive) X η

def realizedU (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (n X η : ℝ) : ℝ :=
  RadialModulation.modulatedU n (fun X η => U (X, η))
    (asRadialPrimitive (r.axialPrimitive E)) X η

/-- Smoothness of the realized profiles follows from the constructed integral
primitives, without any primitive-smoothness assumption. -/
theorem realized_profiles_contDiffAt
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U) (n X η : ℝ) (hX : X ≠ 0) :
    ContDiffAt ℝ ∞ (Function.uncurry (realizedE r E n)) (X, η) ∧
      ContDiffAt ℝ ∞ (Function.uncurry (realizedU r E U n)) (X, η) := by
  have hprim := r.primitives_smooth E ha hm hp₂ hE
  exact ⟨RadialModulation.modulatedE_contDiffAt _ _ n X η hE
      (asRadialPrimitive_contDiff _ hprim.1) hX,
    RadialModulation.modulatedU_contDiffAt _ _ n X η hU
      (asRadialPrimitive_contDiff _ hprim.2) hX⟩

/-- Every fixed actual η jet is `O(1/n)`, now for the primitives constructed
from the actual TrueConeLoop family, uniformly on arbitrary compact sets. -/
theorem realized_profiles_uniform_eta_jets
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (KX Kη : Set ℝ) (hKX : IsCompact KX) (hKη : IsCompact Kη) (k : ℕ) :
    ∃ CE CU : ℝ, 0 ≤ CE ∧ 0 ≤ CU ∧ ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη,
      |iteratedDeriv k (realizedE r E n X) η - iteratedDeriv k (fun e => E (X, e)) η| ≤ CE / n ∧
      |iteratedDeriv k (realizedU r E U n X) η - iteratedDeriv k (fun e => U (X, e)) η| ≤ CU / n :=
        by
  have hprim := r.primitives_smooth E ha hm hp₂ hE
  have hperiodA : ∀ X η, Function.Periodic
      (fun θ => asRadialPrimitive r.angularPrimitive (X, η, θ)) 1 :=
    fun X η => (r.primitives_periodic E ha hm hp₂ (X, η)).1
  have hperiodB : ∀ X η, Function.Periodic
      (fun θ => asRadialPrimitive (r.axialPrimitive E) (X, η, θ)) 1 :=
    fun X η => (r.primitives_periodic E ha hm hp₂ (X, η)).2
  obtain ⟨CE, hCE, hbE⟩ := RadialModulation.uniform_modulatedE_eta_jets
    (fun X η => E (X, η)) (asRadialPrimitive r.angularPrimitive)
    hE (asRadialPrimitive_contDiff _ hprim.1) hperiodA KX Kη hKX hKη k
  obtain ⟨CU, hCU, hbU⟩ := RadialModulation.uniform_modulatedU_eta_jets
    (fun X η => U (X, η)) (asRadialPrimitive (r.axialPrimitive E))
    hU (asRadialPrimitive_contDiff _ hprim.2) hperiodB KX Kη hKX hKη k
  exact ⟨CE, CU, hCE, hCU, fun n hn X hX η hη => ⟨hbE n hn X hX η hη, hbU n hn X hX η hη⟩⟩

/-- The constructed profiles agree exactly with the nominal profiles on one
open neighborhood of the prescribed boundary set, for every frequency. -/
theorem realized_profiles_boundary_match
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hBK : B ⊆ K) :
    ∃ N : Set RadialParameter, IsOpen N ∧ B ⊆ N ∧ ∀ n X η : ℝ, (X, η) ∈ N →
      realizedE r E n X η = E (X, η) ∧ realizedU r E U n X η = U (X, η) := by
  obtain ⟨N, hN, hBN, hz⟩ := r.boundary_vanishing E ha hm hBK
  refine ⟨N, hN, hBN, ?_⟩
  intro n X η hp
  have h := hz (X, η) hp (n * Real.log X)
  simp only [realizedE, realizedU, RadialModulation.modulatedE, RadialModulation.modulatedU,
    asRadialPrimitive, RadialModulation.phasePoint, h.1, h.2, zero_div,
    Real.exp_zero, mul_one, add_zero, and_self]

theorem theta_derivative_asRadialPrimitive
    (Q : RadialParameter × ℝ → ℝ) (hQ : ContDiff ℝ ∞ Q) (X η θ : ℝ) :
    HasDerivAt (fun s => Q ((X, η), s))
      (RadialModulation.partialTheta (asRadialPrimitive Q) (X, η, θ)) θ := by
  have hg := (hasDerivAt_const θ X).prodMk ((hasDerivAt_const θ η).prodMk (hasDerivAt_id θ))
  exact (((asRadialPrimitive_contDiff Q hQ).differentiable (by simp) (X, η,
    θ)).hasFDerivAt).comp_hasDerivAt θ hg

/-- The prescribed loop derivatives are established for the constructed
primitives, including the sign change from `C = -b_L`. -/
theorem realized_primitive_theta
    (r : TrueConeRealization a m p₁ p₂ K B) (E : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (X η θ : ℝ) (hp : (X, η) ∈ K) :
    RadialModulation.partialTheta (asRadialPrimitive r.angularPrimitive) (X, η, θ) =
        -(r.angularLoop ((X, η), θ) - a (X, η)) / 2 ∧
      RadialModulation.partialTheta (asRadialPrimitive (r.axialPrimitive E)) (X, η, θ) =
        E (X, η) * (-r.signedAxialLoop ((X, η), θ) + a (X, η) * m (X, η)) / 2 := by
  have hprim := r.primitives_smooth E ha hm hp₂ hE
  have hd := r.primitive_derivatives E ha hm hp₂ (X, η) hp θ
  exact ⟨(theta_derivative_asRadialPrimitive _ hprim.1 X η θ).unique hd.1,
    (theta_derivative_asRadialPrimitive _ hprim.2 X η θ).unique hd.2⟩

/-- Exact shear identities after composition of the constructed true-cone
loop, its actual integral primitives, and radial modulation. -/
theorem realized_shears_exact
    (r : TrueConeRealization a m p₁ p₂ K B) (E U : RadialParameter → ℝ)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (n X η : ℝ) (hn : n ≠ 0) (hX : X ≠ 0) (hE0 : E (X, η) ≠ 0) (hp : (X, η) ∈ K)
    (haNom : a (X, η) = 1 - 2 * X * deriv (fun x => E (x, η)) X / E (X, η))
    (hbNom : -a (X, η) * m (X, η) = 2 * X * deriv (fun x => U (x, η)) X / E (X, η)) :
    (1 - 2 * X * deriv (fun x => realizedE r E n x η) X / realizedE r E n X η =
      r.angularLoop ((X, η), n * Real.log X) -
        2 * X * RadialModulation.partialX (asRadialPrimitive r.angularPrimitive)
          (X, η, n * Real.log X) / n) ∧
    (2 * X * deriv (fun x => realizedU r E U n x η) X / realizedE r E n X η =
      (-r.signedAxialLoop ((X, η), n * Real.log X) +
        2 * X * RadialModulation.partialX (asRadialPrimitive (r.axialPrimitive E))
          (X, η, n * Real.log X) / (n * E (X, η))) /
            Real.exp (r.angularPrimitive ((X, η), n * Real.log X) / n)) := by
  have hprim := r.primitives_smooth E ha hm hp₂ hE
  have hθ := realized_primitive_theta r E ha hm hp₂ hE X η (n * Real.log X) hp
  have hEr : DifferentiableAt ℝ (fun x => E (x, η)) X :=
    (hE.differentiable (by simp) (X, η)).comp X
      (differentiableAt_id.prodMk (differentiableAt_const η))
  have hUr : DifferentiableAt ℝ (fun x => U (x, η)) X :=
    (hU.differentiable (by simp) (X, η)).comp X
      (differentiableAt_id.prodMk (differentiableAt_const η))
  constructor
  · apply RadialModulation.angular_shear_exact _ _ n X η _ hn hX hE0 hEr
      ((asRadialPrimitive_contDiff _ hprim.1).differentiable (by simp) _)
    simpa only [RadialModulation.phasePoint, haNom] using hθ.1
  · apply RadialModulation.axial_shear_exact _ _ _ _ n X η _ hn hX hE0 hUr
      ((asRadialPrimitive_contDiff _ hprim.2).differentiable (by simp) _)
    change RadialModulation.partialTheta (asRadialPrimitive (r.axialPrimitive E))
      (X, η, n * Real.log X) = _
    rw [hθ.2, ← hbNom]
    ring

/-- End-to-end existence from nominal scalar data: construct the actual
TrueConeLoop family, its normalized integral primitives, and modulated profiles.
All smoothness and finite-jet conclusions are proved for these constructions. -/
theorem exists_modulated_trueCone_profiles
    (a m p₁ p₂ E U : RadialParameter → ℝ) (KX Kη : Set ℝ) (B : Set RadialParameter)
    (hKX : IsCompact KX) (hKη : IsCompact Kη) (hB : IsCompact B) (hBK : B ⊆ KX ×ˢ Kη)
    (ha : ContDiff ℝ ∞ a) (hm : ContDiff ℝ ∞ m)
    (hp₁ : ContDiff ℝ ∞ p₁) (hp₂ : ContDiff ℝ ∞ p₂)
    (hE : ContDiff ℝ ∞ E) (hU : ContDiff ℝ ∞ U)
    (haK : ∀ p ∈ KX ×ˢ Kη, 0 < a p)
    (hPK : ∀ p ∈ KX ×ˢ Kη, 2 < p₁ p + p₂ p * m p)
    (hrelaxed : ∀ p ∈ KX ×ˢ Kη, TrueConeLoop.nominalSpeed (a p) (m p) <
      ConeAlgebra.coneBound (p₁ p + p₂ p * m p) (p₂ p - p₁ p * m p))
    (htrueB : ∀ p ∈ B, 2 < TrueConeLoop.nominalSpeed (a p) (m p)) :
    ∃ r : TrueConeRealization a m p₁ p₂ (KX ×ˢ Kη) B,
      (∀ p ∈ KX ×ˢ Kη, ∀ θ, TrueConeLoop.InTrueCone (p₁ p) (p₂ p)
        (r.angularLoop (p, θ)) (r.signedAxialLoop (p, θ))) ∧
      (∀ n X η : ℝ, X ≠ 0 →
        ContDiffAt ℝ ∞ (Function.uncurry (realizedE r E n)) (X, η) ∧
        ContDiffAt ℝ ∞ (Function.uncurry (realizedU r E U n)) (X, η)) ∧
      (∀ k : ℕ, ∃ CE CU : ℝ, 0 ≤ CE ∧ 0 ≤ CU ∧
        ∀ n : ℝ, 1 ≤ n → ∀ X ∈ KX, ∀ η ∈ Kη,
          |iteratedDeriv k (realizedE r E n X) η - iteratedDeriv k (fun e => E (X, e)) η| ≤ CE / n ∧
          |iteratedDeriv k (realizedU r E U n X) η - iteratedDeriv k (fun e => U (X, e)) η| ≤ CU /
            n) ∧
      (∃ N : Set RadialParameter, IsOpen N ∧ B ⊆ N ∧ ∀ n X η : ℝ, (X, η) ∈ N →
        realizedE r E n X η = E (X, η) ∧ realizedU r E U n X η = U (X, η)) := by
  obtain ⟨r⟩ := exists_trueConeRealization a m p₁ p₂ (KX ×ˢ Kη) B
    (hKX.prod hKη) hB ha hm hp₁ hp₂ haK hPK htrueB
  exact ⟨r, r.loop_trueCone hrelaxed,
    realized_profiles_contDiffAt r E U ha hm hp₂ hE hU,
    realized_profiles_uniform_eta_jets r E U ha hm hp₂ hE hU KX Kη hKX hKη,
    realized_profiles_boundary_match r E U ha hm hBK⟩

end RadialProfiles

end NavierStokes.ParametricModulation
