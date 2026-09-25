/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/
module


public import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyBadScaleInputs

/-!
# Actual nonstandard intervals and their diagonal energy

The nonstandard test is the source's adjoint-composition test, rather than
the desired `L²` estimate. Its right side is the actual unit-window
convolution of the restricted bad input. The diagonal estimate below is
derived from this test and the proved stopping-cell local-mass bound.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction


open Classical in
/-- The near-diagonal positive convolution in the source nonstandard test. -/
noncomputable def localUnitMass (I : RealInterval) (b : ℝ → ℂ) (x : ℝ) : ℝ :=
  ∫ t in Icc (x - 1 / 2) (x + 1 / 2), ‖I.centralThird.indicator b t‖

open Classical in
/-- Literal source nonstandard condition, with the concrete near-diagonal
constant multiplied by `100`. We use the equivalent a.e. form. -/
def IsNonstandard (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) : Prop :=
  ∀ᵐ x ∂volume, x ∈ I.centralThird →
    ‖(krauseLaceyPositiveKernel k).adjoint.applyIntegral
      (krauseLaceyLocalizedPiece 1 k I b) x‖ ≤
      (1600 * positiveDyadicAmplitudeBound ^ 2 / I.length) * localUnitMass I b x

open Classical in
/-- The actual nonstandard collection at kernel index `k` and bad-scale
gap `s`. Interval length has exponent `k + 2` in our kernel normalization. -/
noncomputable def nonstandardCollection
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ k s : ℤ) :
    Finset RealInterval :=
  (goodCollection S f 0 I₀).filter fun I ↦
    I.length = (2 : ℝ) ^ (k + 2) ∧ k₀ ≤ k + 2 - s ∧
      IsNonstandard k I (badScaleInput S f I₀ k₀ (k + 2 - s))

open Classical in
/-- All actual nonstandard intervals at one fixed bad-scale gap. The
finite candidate collection supplies the finite physical scale range. -/
noncomputable def nonstandardIntervals
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) : Finset RealInterval :=
  (goodCollection S f 0 I₀).filter fun I ↦
    I.length = (2 : ℝ) ^ (scale I + 2) ∧ k₀ ≤ scale I + 2 - s ∧
      IsNonstandard (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s))

open Classical in
theorem nonstandardIntervals_subset (S : Finset RealInterval) (f : ℝ → ℂ)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ) :
    nonstandardIntervals S f I₀ k₀ s scale ⊆ S := by
  intro I hI
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1

open Classical in
theorem localUnitMass_le (I : RealInterval) {b : ℝ → ℂ} (hb : Integrable b) (x : ℝ) :
    localUnitMass I b x ≤ ∫ t in Icc (x - 1 / 2) (x + 1 / 2), ‖b t‖ := by
  apply integral_mono (hb.indicator I.measurableSet_centralThird).norm.integrableOn
    hb.norm.integrableOn
  intro t
  exact norm_indicator_le_norm_self _ _

open Classical in
theorem integral_sq_localizedPiece_eq_norm_pairing
    (k : ℤ) (I : RealInterval) (b : ℝ → ℂ) :
    (∫ x, ‖krauseLaceyLocalizedPiece 1 k I b x‖ ^ 2) =
      ‖∫ x, krauseLaceyLocalizedPiece 1 k I b x *
        conj (krauseLaceyLocalizedPiece 1 k I b x)‖ := by
  simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
  rw [integral_complex_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]

open Classical in
/-- A bound on the actual adjoint action controls the energy of the
localized piece. The integral identity, integrability, and null-set handling
are all proved here. -/
theorem integral_sq_localizedPiece_le_of_adjoint_bound
    (k : ℤ) (I : RealInterval) {b : ℝ → ℂ} (hb : Integrable b)
    {H : ℝ}
    (hadj : ∀ᵐ x ∂volume, x ∈ I.centralThird →
      ‖(krauseLaceyPositiveKernel k).adjoint.applyIntegral
        (krauseLaceyLocalizedPiece 1 k I b) x‖ ≤ H) :
    (∫ x, ‖krauseLaceyLocalizedPiece 1 k I b x‖ ^ 2) ≤
      H * ∫ x in I.centralThird, ‖b x‖ := by
  let K := krauseLaceyPositiveKernel k
  let c := I.centralThird.indicator b
  have hc : Integrable c := hb.indicator I.measurableSet_centralThird
  have hact : K.applyIntegral c = krauseLaceyLocalizedPiece 1 k I b := by
    funext x
    exact (krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution k I b x).symm
  have hpair := K.integral_pairing_adjoint hc (K.integrable_applyIntegral hc)
  rw [hact] at hpair
  rw [integral_sq_localizedPiece_eq_norm_pairing, hpair]
  have hm := (K.adjoint.integrable_applyIntegral
    (integrable_krauseLaceyLocalizedPiece k I hb)).aestronglyMeasurable
  have hg : Integrable (fun x ↦ c x * conj (K.adjoint.applyIntegral
      (krauseLaceyLocalizedPiece 1 k I b) x)) := by
    apply hc.mul_bdd (Complex.continuous_conj.comp_aestronglyMeasurable hm)
    · filter_upwards with x
      simpa only [RCLike.norm_conj] using K.adjoint.norm_applyIntegral_le
        (integrable_krauseLaceyLocalizedPiece k I hb) x
  calc
    _ ≤ ∫ x, ‖c x * conj (K.adjoint.applyIntegral (krauseLaceyLocalizedPiece 1 k I b) x)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, H * ‖c x‖ := by
      apply integral_mono_ae hg.norm (hc.norm.const_mul H)
      filter_upwards [hadj] with x hx
      rw [norm_mul, RCLike.norm_conj]
      by_cases hxI : x ∈ I.centralThird
      · exact (mul_le_mul_of_nonneg_left (hx hxI) (norm_nonneg _)).trans_eq (mul_comm _ _)
      · simp [c, indicator_of_notMem hxI]
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simp only [c, norm_indicator_eq_indicator_norm, integral_indicator
        I.measurableSet_centralThird]

open Classical in
/-- The diagonal estimate for an actual nonstandard bad piece. The
`2^(-s)` gain is derived from its literal bad-scale index. -/
theorem nonstandard_badPiece_diagonalEnergy_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ k s : ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    {I : RealInterval} (hscale : I.length = (2 : ℝ) ^ (k + 2))
    (hℓ : 0 ≤ k + 2 - s)
    (hNS : IsNonstandard k I (badScaleInput S f I₀ k₀ (k + 2 - s))) :
    (∫ x, ‖krauseLaceyLocalizedPiece 1 k I
      (badScaleInput S f I₀ k₀ (k + 2 - s)) x‖ ^ 2) ≤
      (96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) *
          ∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (k + 2 - s) x‖ := by
  let b := badScaleInput S f I₀ k₀ (k + 2 - s)
  have hb : Integrable b := integrable_badScaleInput S hf I₀ k₀ (k + 2 - s)
  have hC : 0 ≤ 1600 * positiveDyadicAmplitudeBound ^ 2 / I.length := by
    positivity [I.length_pos]
  have hH : 0 ≤ 96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
      (2 : ℝ) ^ (-s) := by positivity [intervalL1Average_nonneg f I₀]
  apply integral_sq_localizedPiece_le_of_adjoint_bound k I hb
  filter_upwards [hNS] with x hx hxI
  apply (hx hxI).trans
  calc
    _ ≤ (1600 * positiveDyadicAmplitudeBound ^ 2 / I.length) *
        (60 * intervalL1Average f I₀ * (2 : ℝ) ^ (k + 2 - s)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact (localUnitMass_le I hb x).trans
        (badScaleInput_unitWindowMass_le hf I₀ k₀ (k + 2 - s) hℓ hlam hparent hsub x)
    _ = _ := by
      have hpow : (2 : ℝ) ^ (k + 2 - s) = (2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ (-s) := by
        rw [show k + 2 - s = (k + 2) + (-s) by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      rw [hscale, hpow]
      field_simp; ring

open Classical in
/-- The full diagonal energy has no dependence on the number of intervals
or physical scales. The actual restricted-input mass packing supplies it. -/
theorem sum_nonstandard_badPiece_diagonalEnergy_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ nonstandardIntervals S f I₀ k₀ s scale) :
    (∑ I ∈ N, ∫ x, ‖krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖ ^ 2) ≤
      (96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∫ x, ‖f x‖ := by
  let C := 96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
    (2 : ℝ) ^ (-s)
  have hC : 0 ≤ C := by dsimp [C]; positivity [intervalL1Average_nonneg f I₀]
  calc
    _ ≤ ∑ I ∈ N, C * ∫ x in I.centralThird,
        ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖ := by
      apply Finset.sum_le_sum
      intro I hI
      have hn := (Finset.mem_filter.mp (hN hI)).2
      exact nonstandard_badPiece_diagonalEnergy_le hf I₀ k₀ (scale I) s hlam hparent hsub
        hn.1 (hk₀.trans hn.2.1) hn.2.2
    _ = C * ∑ I ∈ N, ∫ x in I.centralThird,
        ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_intervalBadInput_mass_le hf I₀ k₀ s scale hlam N
      (hN.trans (nonstandardIntervals_subset S f I₀ k₀ s scale))
      (fun I hI ↦ (Finset.mem_filter.mp (hN hI)).2.1)) hC


end KrauseLaceyBadScale
end QuadraticCarleson
