/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardEnergy
public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyNonstandardGenerations

/-!
# An explicit energy classification for the Krause--Lacey argument

The monomial proof, https://arxiv.org/pdf/1609.01564v2, Section 4 (Lemma
4.6, pp. 8--9, and the diagonal calculation (4.16)--(4.18), p. 11), uses
the near and far terms of the
correlation estimate (2.4). The a.e. pointwise predicate `IsNonstandard`
in the older module has no valid complementary uniform pointwise bound.
This module therefore introduces a distinct, explicitly scalar energy
test. It does not identify this test with the negation of that predicate.

We prove the actual near-plus-far energy inequality first. Comparing
the actual energy with 100 times its positive near term then gives an
exhaustive partition with both required energy consequences.

Source distinction: arXiv:2609.04101 invokes Theorem 1.1 of the general
paper https://arxiv.org/pdf/1701.05249v2. Its local lemma is Lemma 3.4,
with displayed estimate (3.5). It cites the earlier monomial proof as
reference [14]. The present degree-two modules implement that earlier
specialized route; equation numbers (4.16)--(4.18) refer to it.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction

attribute [local instance] Classical.propDecidable

theorem localUnitMass_nonneg (I : RealInterval) (b : ℝ → ℂ) (x : ℝ) :
    0 ≤ localUnitMass I b x := integral_nonneg (fun _ ↦ norm_nonneg _)

theorem localUnitMass_le_total (I : RealInterval) {b : ℝ → ℂ}
    (hb : Integrable b) (x : ℝ) :
    localUnitMass I b x ≤ ∫ t, ‖I.centralThird.indicator b t‖ :=
  setIntegral_le_integral (hb.indicator I.measurableSet_centralThird).norm
    (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))

theorem localUnitMass_eq_integral_indicator (I : RealInterval) (b : ℝ → ℂ) (x : ℝ) :
    localUnitMass I b x =
      ∫ t, if |x - t| ≤ (1 / 2 : ℝ) then ‖I.centralThird.indicator b t‖ else 0 := by
  rw [localUnitMass, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  have heq : t ∈ Icc (x - 1 / 2) (x + 1 / 2) ↔ |x - t| ≤ (1 / 2 : ℝ) := by
    rw [mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [indicator_apply, heq]

theorem aestronglyMeasurable_localUnitMass (I : RealInterval) {b : ℝ → ℂ}
    (hb : Integrable b) : AEStronglyMeasurable (localUnitMass I b) volume := by
  have hm : MeasurableSet {z : ℝ × ℝ | |z.1 - z.2| ≤ (1 / 2 : ℝ)} :=
    isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const |>.measurableSet
  have h := ((hb.indicator I.measurableSet_centralThird).norm.aestronglyMeasurable.comp_snd
    (μ := volume) (ν := volume)).indicator hm
  have hi := h.integral_prod_right'
  change AEStronglyMeasurable (fun x ↦ ∫ y,
    if |x - y| ≤ (1 / 2 : ℝ) then ‖I.centralThird.indicator b y‖ else 0) volume at hi
  simpa only [← localUnitMass_eq_integral_indicator] using hi

theorem integrable_mul_localUnitMass (I : RealInterval) {b : ℝ → ℂ}
    (hb : Integrable b) :
    Integrable (fun x ↦ ‖I.centralThird.indicator b x‖ * localUnitMass I b x) := by
  have hbound : ∀ᵐ x ∂volume, ‖localUnitMass I b x‖ ≤
      ∫ t, ‖I.centralThird.indicator b t‖ := by
    filter_upwards with x
    rw [Real.norm_of_nonneg (localUnitMass_nonneg I b x)]
    exact localUnitMass_le_total I hb x
  exact (hb.indicator I.measurableSet_centralThird).norm.mul_bdd
    (aestronglyMeasurable_localUnitMass I hb) hbound

/-- The genuine squared `L²` energy of one localized oscillatory piece. -/
noncomputable def localizedEnergy (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) : ℝ :=
  ∫ x, ‖krauseLaceyLocalizedPiece 1 k I b x‖ ^ 2

/-- The positive near-diagonal energy from the first term of (2.4).
The kernel radius is `|I|/8`, explaining the coefficient `16`. -/
noncomputable def nearEnergy (I : RealInterval) (b : ℝ → ℂ) : ℝ :=
  (16 * positiveDyadicAmplitudeBound ^ 2 / I.length) *
    ∫ x, ‖I.centralThird.indicator b x‖ * localUnitMass I b x

/-- The far energy budget from the second term of (2.4). -/
noncomputable def farEnergy (I : RealInterval) (b : ℝ → ℂ) : ℝ :=
  (128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
    (∫ x in I.centralThird, ‖b x‖) ^ 2

theorem nearEnergy_nonneg (I : RealInterval) (b : ℝ → ℂ) : 0 ≤ nearEnergy I b := by
  apply mul_nonneg (by positivity [I.length_pos])
    (integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg _) (localUnitMass_nonneg I b x)))

theorem farEnergy_nonneg (I : RealInterval) (b : ℝ → ℂ) : 0 ≤ farEnergy I b := by
  unfold farEnergy
  positivity

/-- The actual adjoint correlation, bounded by its two positive regions. -/
theorem krauseLaceyPositiveKernel_same_adjoint_le (k : ℤ) (I : RealInterval)
    (hscale : I.length = (2 : ℝ) ^ (k + 2)) (x y : ℝ) :
    ‖∫ t, conj (krauseLaceyPositiveKernel k t x) * krauseLaceyPositiveKernel k t y‖ ≤
      (if |x - y| ≤ (1 / 2 : ℝ) then 16 * positiveDyadicAmplitudeBound ^ 2 / I.length
        else 0) + 128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2 := by
  have h := krauseLacey_positiveDyadicCorrelation_le k (-x) (-y)
  dsimp only at h
  have heq : ‖∫ t, conj (krauseLaceyPositiveKernel k t x) *
      krauseLaceyPositiveKernel k t y‖ =
      ‖∫ t, annularQuadraticKernel (positiveDyadicAmplitude k) 1 (-x - t) *
        conj (annularQuadraticKernel (positiveDyadicAmplitude k) 1 (-y - t))‖ := by
    rw [← RCLike.norm_conj, ← integral_conj]
    simp only [map_mul, starRingEnd_self_apply, krauseLaceyPositiveKernel_apply]
    rw [← MeasureTheory.integral_sub_left_eq_self
      (fun t ↦ annularQuadraticKernel (positiveDyadicAmplitude k) 1 (-x - t) *
        conj (annularQuadraticKernel (positiveDyadicAmplitude k) 1 (-y - t))) volume 0]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    simp only [zero_sub]
    rw [show -x - -t = t - x by ring, show -y - -t = t - y by ring]
  have hlen : I.length = 8 * (2 : ℝ) ^ (k - 1) := by
    rw [hscale, show k + 2 = (k - 1) + 3 by ring, zpow_add₀ (by norm_num)]
    norm_num
    ring
  have hnear : 2 * positiveDyadicAmplitudeBound ^ 2 / (2 : ℝ) ^ (k - 1) =
      16 * positiveDyadicAmplitudeBound ^ 2 / I.length := by rw [hlen]; ring
  have hfar : 2 * positiveDyadicAmplitudeBound ^ 2 / ((2 : ℝ) ^ (k - 1)) ^ 2 =
      128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2 := by rw [hlen]; ring
  rw [heq]
  apply h.trans
  rw [show -y - -x = x - y by ring, hnear, hfar]
  have hA : 0 ≤ 16 * positiveDyadicAmplitudeBound ^ 2 / I.length := by
    positivity [I.length_pos]
  have hB : 0 ≤ 128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2 := by positivity
  split_ifs <;> linarith

/-- The concrete adjoint majorant used to pass from the kernel estimate
to the scalar energy split. -/
theorem norm_adjoint_localizedPiece_le_near_add_far
    (k : ℤ) (I : RealInterval) (hscale : I.length = (2 : ℝ) ^ (k + 2))
    {b : ℝ → ℂ} (hb : Integrable b) (x : ℝ) :
    ‖(krauseLaceyPositiveKernel k).adjoint.applyIntegral
      (krauseLaceyLocalizedPiece 1 k I b) x‖ ≤
      (16 * positiveDyadicAmplitudeBound ^ 2 / I.length) * localUnitMass I b x +
      (128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        ∫ y in I.centralThird, ‖b y‖ := by
  let K := krauseLaceyPositiveKernel k
  let c := I.centralThird.indicator b
  let A := 16 * positiveDyadicAmplitudeBound ^ 2 / I.length
  let B := 128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2
  have hc : Integrable c := hb.indicator I.measurableSet_centralThird
  have ha : K.applyIntegral c = krauseLaceyLocalizedPiece 1 k I b := by
    funext y
    exact (krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution k I b y).symm
  rw [← ha, K.adjoint.applyIntegral_comp_eq_mixed K hc x]
  have hi : Integrable (fun y ↦ (∫ t, K.adjoint x t * K t y) * c y) := by
    simpa only [integral_mul_const] using
      (K.adjoint.integrable_mixedComposition_integrand K hc x).integral_prod_right
  have hn : Integrable (fun y ↦ if |x - y| ≤ (1 / 2 : ℝ) then ‖c y‖ else 0) := by
    have hm : MeasurableSet {y : ℝ | |x - y| ≤ (1 / 2 : ℝ)} :=
      isClosed_le (continuous_const.sub continuous_id).abs continuous_const |>.measurableSet
    exact hc.norm.indicator hm
  calc
    _ ≤ ∫ y, ‖(∫ t, K.adjoint x t * K t y) * c y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, A * (if |x - y| ≤ (1 / 2 : ℝ) then ‖c y‖ else 0) + B * ‖c y‖ := by
      apply integral_mono hi.norm ((hn.const_mul A).add (hc.norm.const_mul B))
      intro y
      dsimp only [Pi.add_apply]
      rw [norm_mul]
      have h := mul_le_mul_of_nonneg_right
        (krauseLaceyPositiveKernel_same_adjoint_le k I hscale x y) (norm_nonneg (c y))
      dsimp only [A, B, K] at *
      convert h using 1 <;> first | rfl | (split_ifs <;> ring)
    _ = _ := by
      rw [integral_add (hn.const_mul A) (hc.norm.const_mul B), integral_const_mul,
        integral_const_mul, ← localUnitMass_eq_integral_indicator]
      simp only [A, B, c, norm_indicator_eq_indicator_norm,
        integral_indicator I.measurableSet_centralThird]

/-- A variable adjoint majorant controls the genuine energy. -/
theorem localizedEnergy_le_integral_adjoint_majorant
    (k : ℤ) (I : RealInterval) {b : ℝ → ℂ} (hb : Integrable b)
    (H : ℝ → ℝ)
    (hH : Integrable (fun x ↦ ‖I.centralThird.indicator b x‖ * H x))
    (hadj : ∀ᵐ x ∂volume, x ∈ I.centralThird →
      ‖(krauseLaceyPositiveKernel k).adjoint.applyIntegral
        (krauseLaceyLocalizedPiece 1 k I b) x‖ ≤ H x) :
    localizedEnergy k I b ≤ ∫ x, ‖I.centralThird.indicator b x‖ * H x := by
  let K := krauseLaceyPositiveKernel k
  let c := I.centralThird.indicator b
  have hc : Integrable c := hb.indicator I.measurableSet_centralThird
  have ha : K.applyIntegral c = krauseLaceyLocalizedPiece 1 k I b := by
    funext x
    exact (krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution k I b x).symm
  have hpair := K.integral_pairing_adjoint hc (K.integrable_applyIntegral hc)
  rw [ha] at hpair
  rw [localizedEnergy, integral_sq_localizedPiece_eq_norm_pairing, hpair]
  have hm := (K.adjoint.integrable_applyIntegral
    (integrable_krauseLaceyLocalizedPiece k I hb)).aestronglyMeasurable
  have hg : Integrable (fun x ↦ c x * conj (K.adjoint.applyIntegral
      (krauseLaceyLocalizedPiece 1 k I b) x)) := by
    exact hc.mul_bdd (Complex.continuous_conj.comp_aestronglyMeasurable hm)
      (Filter.Eventually.of_forall (fun x ↦ by
        simpa only [RCLike.norm_conj] using K.adjoint.norm_applyIntegral_le
          (integrable_krauseLaceyLocalizedPiece k I hb) x))
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae hg.norm hH
  filter_upwards [hadj] with x hx
  rw [norm_mul, RCLike.norm_conj]
  by_cases hxI : x ∈ I.centralThird
  · exact mul_le_mul_of_nonneg_left (hx hxI) (norm_nonneg _)
  · simp [c, indicator_of_notMem hxI]

/-- The actual `TT*` energy is bounded by the sum of the two explicit
positive budgets. No classification hypothesis is used. -/
theorem localizedEnergy_le_near_add_far
    (k : ℤ) (I : RealInterval) (hscale : I.length = (2 : ℝ) ^ (k + 2))
    {b : ℝ → ℂ} (hb : Integrable b) :
    localizedEnergy k I b ≤ nearEnergy I b + farEnergy I b := by
  let A := 16 * positiveDyadicAmplitudeBound ^ 2 / I.length
  let B := 128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2
  let m := ∫ x in I.centralThird, ‖b x‖
  let c := I.centralThird.indicator b
  have hc : Integrable c := hb.indicator I.measurableSet_centralThird
  have hn := integrable_mul_localUnitMass I hb
  have heq : (fun x ↦ ‖c x‖ * (A * localUnitMass I b x + B * m)) =
      (fun x ↦ A * (‖c x‖ * localUnitMass I b x) + (B * m) * ‖c x‖) := by
    funext x
    ring
  have hi : Integrable (fun x ↦ ‖c x‖ * (A * localUnitMass I b x + B * m)) := by
    rw [heq]
    exact (hn.const_mul A).add (hc.norm.const_mul (B * m))
  apply (localizedEnergy_le_integral_adjoint_majorant k I hb
    (fun x ↦ A * localUnitMass I b x + B * m) hi
    (Filter.Eventually.of_forall (fun x _ ↦
      norm_adjoint_localizedPiece_le_near_add_far k I hscale hb x))).trans_eq
  change (∫ x, ‖c x‖ * (A * localUnitMass I b x + B * m)) = _
  rw [heq, integral_add (hn.const_mul A) (hc.norm.const_mul (B * m)),
    integral_const_mul, integral_const_mul]
  have hm : (∫ x, ‖c x‖) = m := by
    simp only [c, m, norm_indicator_eq_indicator_norm,
      integral_indicator I.measurableSet_centralThird]
  rw [hm]
  unfold nearEnergy farEnergy
  dsimp only [A, B, m, c]
  ring

/-- Explicit scalar near-energy classification. This is a new predicate,
not a redefinition of the old a.e. pointwise `IsNonstandard`. -/
def IsEnergyNonstandard (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) : Prop :=
  localizedEnergy k I b ≤ 100 * nearEnergy I b

/-- Complementary scalar branch. Failure of the scalar near-energy test
does imply the far-energy estimate proved below. -/
def IsEnergyStandard (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) : Prop :=
  100 * nearEnergy I b < localizedEnergy k I b

theorem not_isEnergyNonstandard_iff (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) :
    ¬ IsEnergyNonstandard k I b ↔ IsEnergyStandard k I b := not_le

theorem energy_classification (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) :
    IsEnergyNonstandard k I b ∨ IsEnergyStandard k I b := le_or_gt _ _

/-- The old pointwise condition implies the scalar near-energy branch;
the converse is neither assumed nor needed. -/
theorem IsNonstandard.isEnergyNonstandard
    {k : ℤ} {I : RealInterval} {b : ℝ → ℂ} (h : IsNonstandard k I b)
    (hb : Integrable b) : IsEnergyNonstandard k I b := by
  have hn := integrable_mul_localUnitMass I hb
  let C := 1600 * positiveDyadicAmplitudeBound ^ 2 / I.length
  have hi : Integrable (fun x ↦ ‖I.centralThird.indicator b x‖ *
      (C * localUnitMass I b x)) := by
    convert hn.const_mul C using 1
    funext x
    ring
  apply (localizedEnergy_le_integral_adjoint_majorant k I hb
    (fun x ↦ C * localUnitMass I b x) hi h).trans_eq
  simp_rw [show ∀ x, ‖I.centralThird.indicator b x‖ * (C * localUnitMass I b x) =
      C * (‖I.centralThird.indicator b x‖ * localUnitMass I b x) by intro x; ring]
  rw [integral_const_mul]
  unfold nearEnergy
  dsimp [C]
  ring

/-- A genuine uniform standard energy estimate, obtained by absorbing
the near term. The loss is exactly `100 / 99`. -/
theorem IsEnergyStandard.localizedEnergy_le_far
    {k : ℤ} {I : RealInterval} {b : ℝ → ℂ} (h : IsEnergyStandard k I b)
    (hb : Integrable b) (hscale : I.length = (2 : ℝ) ^ (k + 2)) :
    localizedEnergy k I b ≤ (100 / 99 : ℝ) * farEnergy I b := by
  have he := localizedEnergy_le_near_add_far k I hscale hb
  unfold IsEnergyStandard at h
  linarith

/-- The positive near energy of an actual bad-scale input has the desired
`2^(-s)` gain, derived from stopping parents and the unit-window bound. -/
theorem nearEnergy_badScaleInput_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ k s : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    {I : RealInterval} (hscale : I.length = (2 : ℝ) ^ (k + 2))
    (hℓ : 0 ≤ k + 2 - s) :
    nearEnergy I (badScaleInput S f I₀ k₀ (k + 2 - s)) ≤
      (960 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) *
          ∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (k + 2 - s) x‖ := by
  let b := badScaleInput S f I₀ k₀ (k + 2 - s)
  let M := 60 * intervalL1Average f I₀ * (2 : ℝ) ^ (k + 2 - s)
  have hb : Integrable b := integrable_badScaleInput S hf I₀ k₀ _
  have hm (x : ℝ) : localUnitMass I b x ≤ M :=
    (localUnitMass_le I hb x).trans
      (badScaleInput_unitWindowMass_le hf I₀ k₀ (k + 2 - s) hℓ hlam hparent hsub x)
  have hn : (∫ x, ‖I.centralThird.indicator b x‖ * localUnitMass I b x) ≤
      M * ∫ x in I.centralThird, ‖b x‖ := by
    calc
      _ ≤ ∫ x, M * ‖I.centralThird.indicator b x‖ := by
        apply integral_mono (integrable_mul_localUnitMass I hb)
          ((hb.indicator I.measurableSet_centralThird).norm.const_mul M)
        intro x
        dsimp only
        exact (mul_le_mul_of_nonneg_left (hm x) (norm_nonneg _)).trans_eq (mul_comm _ _)
      _ = _ := by
        rw [integral_const_mul]
        simp only [norm_indicator_eq_indicator_norm,
          integral_indicator I.measurableSet_centralThird]
  unfold nearEnergy
  apply (mul_le_mul_of_nonneg_left hn
    (by positivity [I.length_pos] : 0 ≤ 16 * positiveDyadicAmplitudeBound ^ 2 / I.length)).trans_eq
  have hpow : (2 : ℝ) ^ (k + 2 - s) = (2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (-s) := by
    rw [show k + 2 - s = (k + 2) + (-s) by ring, zpow_add₀ (by norm_num)]
  dsimp only [M, b]
  rw [hscale, hpow]
  field_simp
  ring

/-- The new near-energy branch recovers the concrete diagonal estimate
without assuming any pointwise adjoint-majorization property. -/
theorem energyNonstandard_badPiece_diagonalEnergy_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ k s : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    {I : RealInterval} (hscale : I.length = (2 : ℝ) ^ (k + 2))
    (hℓ : 0 ≤ k + 2 - s)
    (hNS : IsEnergyNonstandard k I (badScaleInput S f I₀ k₀ (k + 2 - s))) :
    localizedEnergy k I (badScaleInput S f I₀ k₀ (k + 2 - s)) ≤
      (96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) *
          ∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (k + 2 - s) x‖ := by
  apply hNS.trans
  apply (mul_le_mul_of_nonneg_left
    (nearEnergy_badScaleInput_le hf I₀ k₀ k s hlam hparent hsub hscale hℓ)
    (by norm_num : (0 : ℝ) ≤ 100)).trans_eq
  ring

/-- All admissible interval/bad-scale pairs at a fixed gap, before the
energy comparison. Geometry and stopping conditions are unchanged. -/
noncomputable def energyEligibleIntervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : Finset RealInterval :=
  (goodCollection S f 0 I₀).filter fun I ↦
    I.length = (2 : ℝ) ^ (scale I + 2) ∧ k₀ ≤ scale I + 2 - s

/-- The eligible intervals satisfying the nonstandard energy condition for their bad-scale
input. -/
noncomputable def energyNonstandardIntervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : Finset RealInterval :=
  (energyEligibleIntervals S f I₀ k₀ s scale).filter fun I ↦
    IsEnergyNonstandard (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s))

/-- The eligible intervals satisfying the standard energy condition for their bad-scale input. -/
noncomputable def energyStandardIntervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : Finset RealInterval :=
  (energyEligibleIntervals S f I₀ k₀ s scale).filter fun I ↦
    IsEnergyStandard (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s))

theorem energyIntervals_partition
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) :
    energyNonstandardIntervals S f I₀ k₀ s scale ∪
      energyStandardIntervals S f I₀ k₀ s scale = energyEligibleIntervals S f I₀ k₀ s scale := by
  ext I
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hn | hs
    · exact (Finset.mem_filter.mp hn).1
    · exact (Finset.mem_filter.mp hs).1
  · intro h
    rcases energy_classification (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) with hn | hs
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨h, hn⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨h, hs⟩))

theorem energyIntervals_disjoint
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) :
    Disjoint (energyNonstandardIntervals S f I₀ k₀ s scale)
      (energyStandardIntervals S f I₀ k₀ s scale) := by
  rw [Finset.disjoint_left]
  intro I hn hs
  exact not_lt_of_ge (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hs).2

theorem energyEligibleIntervals_subset
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : energyEligibleIntervals S f I₀ k₀ s scale ⊆ S := by
  intro I hI
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1

/-- Every old pointwise nonstandard interval belongs to the new scalar
near branch, with no converse assertion. -/
theorem nonstandardIntervals_subset_energyNonstandardIntervals
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ) :
    nonstandardIntervals S f I₀ k₀ s scale ⊆ energyNonstandardIntervals S f I₀ k₀ s scale := by
  intro I hI
  obtain ⟨hg, hscale, hgap, hns⟩ := Finset.mem_filter.mp hI
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hg, hscale, hgap⟩,
    hns.isEnergyNonstandard (integrable_badScaleInput S hf I₀ k₀ _)⟩

/-- Summed near energy with no cardinality or scale-count loss. -/
theorem sum_energyNonstandard_badPiece_diagonalEnergy_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval)
    (hN : N ⊆ energyNonstandardIntervals S f I₀ k₀ s scale) :
    (∑ I ∈ N, localizedEnergy (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s))) ≤
      (96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∫ x, ‖f x‖ := by
  let C := 96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ * (2 : ℝ) ^ (-s)
  have he (I : RealInterval) (hI : I ∈ N) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hI)).1).2
  have hNS (I : RealInterval) (hI : I ∈ N) := (Finset.mem_filter.mp (hN hI)).2
  have hNSsub : N ⊆ S :=
    hN.trans ((Finset.filter_subset _ _).trans
      (energyEligibleIntervals_subset S f I₀ k₀ s scale))
  calc
    _ ≤ ∑ I ∈ N, C * ∫ x in I.centralThird,
        ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖ := by
      apply Finset.sum_le_sum
      intro I hI
      exact energyNonstandard_badPiece_diagonalEnergy_le hf I₀ k₀ (scale I) s
        hlam hparent hsub (he I hI).1 (hk₀.trans (he I hI).2) (hNS I hI)
    _ = C * ∑ I ∈ N, ∫ x in I.centralThird,
        ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_intervalBadInput_mass_le hf I₀ k₀ s scale hlam N hNSsub (fun I hI ↦ (he I hI).1))
      (by dsimp [C]; positivity [intervalL1Average_nonneg f I₀])

/-- Standard energy at an actual good interval gains its inverse length.
The only upper average bound used is the proved stopping bound. -/
theorem energyStandard_badPiece_diagonalEnergy_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ k s : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    {I : RealInterval} (hI : I ∈ goodCollection S f 0 I₀)
    (hscale : I.length = (2 : ℝ) ^ (k + 2))
    (hstd : IsEnergyStandard k I (badScaleInput S f I₀ k₀ (k + 2 - s))) :
    localizedEnergy k I (badScaleInput S f I₀ k₀ (k + 2 - s)) ≤
      (2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ / I.length) *
        ∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (k + 2 - s) x‖ := by
  let b := badScaleInput S f I₀ k₀ (k + 2 - s)
  let m := ∫ x in I.centralThird, ‖b x‖
  have hm : 0 ≤ m := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hmass : m ≤ 10 * intervalL1Average f I₀ * I.length :=
    badScaleInput_localMass_le hf I₀ k₀ (k + 2 - s) hlam hsub hI
  have hfar := hstd.localizedEnergy_le_far (integrable_badScaleInput S hf I₀ k₀ _) hscale
  have hnear : localizedEnergy k I b ≤ 2 * farEnergy I b :=
    hfar.trans (mul_le_mul_of_nonneg_right (by norm_num) (farEnergy_nonneg I b))
  apply hnear.trans
  unfold farEnergy
  change 2 * (128 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2 * m ^ 2) ≤ _
  calc
    _ = (256 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) * (m * m) := by ring
    _ ≤ (256 * positiveDyadicAmplitudeBound ^ 2 / I.length ^ 2) *
        ((10 * intervalL1Average f I₀ * I.length) * m) := by
      gcongr
    _ = _ := by dsimp [m, b]; field_simp; ring

/-- Uniform summed standard diagonal energy above a physical scale.
This retains geometric decay in the physical scale and does not charge
the number of intervals or the number of represented physical scales. -/
theorem sum_energyStandard_badPiece_diagonalEnergy_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s kmin : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval)
    (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hmin : ∀ I ∈ N, kmin ≤ scale I) :
    (∑ I ∈ N, localizedEnergy (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s))) ≤
      (2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ (kmin + 2)) * ∫ x, ‖f x‖ := by
  let C := 2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀
  have he (I : RealInterval) (hI : I ∈ N) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hI)).1)
  have hNSsub : N ⊆ S :=
    hN.trans ((Finset.filter_subset _ _).trans
      (energyEligibleIntervals_subset S f I₀ k₀ s scale))
  calc
    _ ≤ ∑ I ∈ N, (C / (2 : ℝ) ^ (kmin + 2)) * ∫ x in I.centralThird,
        ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖ := by
      apply Finset.sum_le_sum
      intro I hI
      apply (energyStandard_badPiece_diagonalEnergy_le hf I₀ k₀ (scale I) s hlam hsub
        (he I hI).1 (he I hI).2.1 (Finset.mem_filter.mp (hN hI)).2).trans
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ ↦ norm_nonneg _))
      apply div_le_div_of_nonneg_left (by positivity [intervalL1Average_nonneg f I₀])
        (by positivity : 0 < (2 : ℝ) ^ (kmin + 2))
      rw [(he I hI).2.1]
      exact zpow_le_zpow_right₀ (by norm_num) (by have := hmin I hI; omega)
    _ = (C / (2 : ℝ) ^ (kmin + 2)) * ∑ I ∈ N, ∫ x in I.centralThird,
        ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_intervalBadInput_mass_le hf I₀ k₀ s scale hlam N hNSsub
        (fun I hI ↦ (he I hI).2.1))
      (by dsimp [C]; positivity [intervalL1Average_nonneg f I₀])

/-- On a single physical scale, disjoint output supports turn the summed
standard diagonal estimate into an estimate for the actual operator sum. -/
theorem norm_energyStandard_fixedScale_sum_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s k : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval)
    (hN : N ⊆ energyStandardIntervals S f I₀ k₀ s scale)
    (hfixed : ∀ I ∈ N, scale I = k) :
    ‖∑ I ∈ N, badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤
      (2560 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ /
        (2 : ℝ) ^ (k + 2)) * ∫ x, ‖f x‖ := by
  have he (I : RealInterval) (hI : I ∈ N) :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hN hI)).1).2.1
  have hNSsub : N ⊆ S :=
    hN.trans ((Finset.filter_subset _ _).trans
      (energyEligibleIntervals_subset S f I₀ k₀ s scale))
  rw [norm_sum_sq_eq_sum_of_inner_zero]
  · simp_rw [badPieceLp, norm_localizedPieceLp_sq]
    exact sum_energyStandard_badPiece_diagonalEnergy_le hf I₀ k₀ s k scale hlam hsub N hN
      (fun I hI ↦ (hfixed I hI).ge)
  · intro I hI J hJ hne
    have hlen : I.length = J.length := by
      rw [he I hI, he J hJ, hfixed I hI, hfixed J hJ]
    have hd : Disjoint I.carrier J.carrier := by
      rcases hlam (hNSsub hI) (hNSsub hJ) hne with hsub | hsub | hd
      · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)).elim
      · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm).elim
      · exact hd
    exact inner_localizedPieceLp_eq_zero_of_disjoint _ _ _ _ _ _ _ _ (he I hI) (he J hJ) hd


end KrauseLaceyBadScale
end QuadraticCarleson
