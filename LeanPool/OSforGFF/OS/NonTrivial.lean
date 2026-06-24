/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import LeanPool.OSforGFF.Measure.Construct
import LeanPool.OSforGFF.Covariance.RealForm
import LeanPool.OSforGFF.Spacetime.ComplexTestFunction
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Nontriviality of the Gaussian Free Field

The OS axiom verification in `OS.Master` would be trivially satisfied by the Dirac
measure at ω = 0 (the "zero field").  This file closes that loophole by proving
the GFF measure is **strictly non-degenerate**:

1. The square-root propagator embedding `T : S(ℝ⁴) → L²` is injective.
2. The smeared covariance `C(f,f) > 0` for every nonzero test function `f`.
3. Every field pairing `⟨ω,f⟩` has strictly positive variance under `muGFF`.
4. The pointwise kernel `C(x,y) → +∞` as `x → y` (UV divergence).

## Proof strategy

Injectivity of T follows from:
- Fourier transform is injective on Schwartz space (Mathlib's `FourierPair` instance
  gives a left inverse `𝓕⁻ ∘ 𝓕 = id`).
- The momentum-space weight `1/√(‖k‖² + m²)` is everywhere positive, so
  multiplication by it cannot create new zeros.
- A continuous function that vanishes a.e. with respect to Lebesgue measure
  vanishes everywhere (volume is an `IsOpenPosMeasure`).

## Main results

- `toComplex_injective` : embedding `S(ℝ⁴,ℝ) ↪ S(ℝ⁴,ℂ)` is injective
- `fourierTransform_schwartz_injective` : `𝓕` on Schwartz space is injective
- `embeddingMap_injective` : the square-root propagator embedding is injective
- `freeCovarianceFormR_strictPos` : `C(f,f) > 0` for `f ≠ 0`
- `gaussianFreeField_variance_pos` : `Var[⟨ω,f⟩] > 0` for `f ≠ 0`
- `gaussianFreeField_not_dirac` : `muGFF ≠ δ₀`
- `besselK1_tendsto_atTop_at_zero` : `K₁(z) → +∞` as `z → 0⁺`
- `freeCovariance_tendsto_atTop` : `C(x,y) → +∞` as `x → y`

## References

- Glimm–Jaffe, *Quantum Physics*, §6.1 (nondegeneracy of the free field)
- Reed–Simon, *Methods of Modern Mathematical Physics* II, §IX.8
-/

open MeasureTheory Complex QFT
open scoped Real BigOperators SchwartzMap

noncomputable section

namespace OSforGFF

/-! ## Injectivity of the real-to-complex embedding -/

/-- The embedding `toComplex : S(ℝ⁴,ℝ) → S(ℝ⁴,ℂ)` is injective.
    Follows from injectivity of `ℝ → ℂ` applied pointwise.
-/
theorem toComplex_injective : Function.Injective (toComplex : TestFunction → TestFunctionℂ) := by
  intro f g h
  ext x
  have hx : toComplex f x = toComplex g x := congr_fun (congr_arg _ h) x
  simpa only [toComplex_apply, Complex.ofReal_inj] using hx

/-! ## Injectivity of the Fourier transform on Schwartz space -/

/-- The Fourier transform is injective on complex Schwartz space.
    Proof: `FourierPair` gives `𝓕⁻(𝓕 f) = f`, so `𝓕` has a left inverse.
-/
theorem fourierTransform_schwartz_injective :
    Function.Injective
      (SchwartzMap.fourierTransformCLM ℂ : TestFunctionℂ → TestFunctionℂ) := by
  intro f g h
  -- SchwartzMap.fourierTransformCLM agrees with FourierTransform.fourier, and
  -- FourierPair gives 𝓕⁻ ∘ 𝓕 = id on Schwartz space
  have h' : FourierTransform.fourier f = FourierTransform.fourier g := h
  calc f = FourierTransform.fourierInv (FourierTransform.fourier f) :=
        (FourierTransform.fourierInv_fourier_eq f).symm
    _ = FourierTransform.fourierInv (FourierTransform.fourier g) := by rw [h']
    _ = g := FourierTransform.fourierInv_fourier_eq g

/-! ## Continuous functions that vanish a.e. vanish everywhere -/

/-- A continuous function `SpaceTime → ℂ` that is zero a.e. with respect to
    Lebesgue measure is zero everywhere.

    Proof: if `f(x₀) ≠ 0`, then `U = f⁻¹(ℂ \ {0})` is open and nonempty.
    Since volume on `ℝ⁴` is an `IsOpenPosMeasure`, `μ(U) > 0`,
    contradicting `f = 0` a.e.
-/
private lemma eq_zero_of_continuous_ae_zero
    {f : SpaceTime → ℂ} (hcont : Continuous f) (hae : f =ᵐ[volume] 0) :
    f = 0 := by
  funext x
  by_contra hx
  have hU_pos : 0 < volume {y : SpaceTime | f y ≠ 0} :=
    (hcont.isOpen_preimage _ isOpen_compl_singleton).measure_pos volume ⟨x, hx⟩
  have hU_zero : volume {y : SpaceTime | f y ≠ 0} = 0 := by
    rw [← ae_iff]; exact hae.mono fun y hy => by simpa using hy
  exact absurd hU_zero (ne_of_gt hU_pos)

/-! ## Injectivity of the square-root propagator embedding -/

/-- The square-root propagator map is zero pointwise only if f = 0.

    `sqrtPropagatorMap m f k = 𝓕(toComplex f)(k) · w(k)` where `w(k) > 0`,
    so vanishing of the product forces `𝓕(toComplex f) = 0`, hence `f = 0`
    by Fourier injectivity.
-/
theorem sqrtPropagatorMap_eq_zero_iff (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
    (∀ k : SpaceTime, sqrtPropagatorMap m f k = 0) ↔ f = 0 := by
  have h_tc_0 : toComplex (0 : TestFunction) = 0 := by ext x; simp [toComplex_apply]
  constructor
  · intro h
    -- Each factor: 𝓕(toComplex f)(k) * w(k) = 0, and w(k) > 0, so 𝓕(toComplex f)(k) = 0
    have h_ft_zero_fn : SchwartzMap.fourierTransformCLM ℂ (toComplex f) = 0 := by
      ext k
      have hk := h k
      unfold sqrtPropagatorMap at hk
      have hw_pos : (momentumWeightSqrtMathlib m k : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (momentumWeightSqrt_mathlib_pos m k).ne'
      exact (mul_eq_zero.mp hk).resolve_right hw_pos
    -- By Fourier injectivity then toComplex injectivity, f = 0
    have h_tc_zero : toComplex f = 0 :=
      fourierTransform_schwartz_injective (by rw [h_ft_zero_fn, map_zero])
    exact toComplex_injective (h_tc_zero.trans h_tc_0.symm)
  · intro h; subst h; intro k
    unfold sqrtPropagatorMap
    rw [h_tc_0, ContinuousLinearMap.map_zero]
    simp

/-- The embedding `T : S(ℝ⁴,ℝ) → L²(ℝ⁴,ℂ)` is injective.

    If `T f = T g` then `‖T(f−g)‖ = 0`, so `∫ |sqrtPropagatorMap m (f−g)|² = 0`.
    The integrand is continuous and nonneg, so it vanishes a.e., hence everywhere
    (volume is `IsOpenPosMeasure`).  Since the momentum weight is positive, the
    Fourier transform of `f−g` vanishes, giving `f = g`.
-/
theorem embeddingMap_injective (m : ℝ) [Fact (0 < m)] :
    Function.Injective (embeddingMap m) := by
  intro f g h
  suffices f - g = 0 from eq_of_sub_eq_zero this
  -- ‖T(f-g)‖² = ∫ |sqrtPropagatorMap|² = 0
  have h_norm_zero : ‖embeddingMap m (f - g)‖ = 0 := by rw [map_sub, h, sub_self, norm_zero]
  have h_int_zero : ∫ k, ‖sqrtPropagatorMap m (f - g) k‖ ^ 2 ∂volume = 0 := by
    have h_sq := embeddingMap_norm_sq m (f - g)
    rw [h_norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at h_sq
    linarith
  -- Nonneg continuous integrand with zero integral vanishes a.e., hence (‖·‖²=0 ⟹ ·=0) a.e.
  have h_ae_sq : ∀ᵐ k ∂volume, ‖sqrtPropagatorMap m (f - g) k‖ ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun k => sq_nonneg _)
      (sqrtPropagatorMap_sq_integrable (m := m) (f := f - g))).mp h_int_zero
  have h_ae_zero' : ∀ᵐ k ∂volume, sqrtPropagatorMap m (f - g) k = 0 :=
    h_ae_sq.mono fun k hk => by rwa [sq_eq_zero_iff, norm_eq_zero] at hk
  -- Continuous function zero a.e. is zero everywhere
  have h_cont : Continuous (fun k => sqrtPropagatorMap m (f - g) k) := by
    unfold sqrtPropagatorMap
    exact ((SchwartzMap.fourierTransformCLM ℂ (toComplex (f - g))).continuous).mul
      (continuous_ofReal.comp (momentumWeightSqrt_mathlib_continuous m))
  have h_eq := eq_zero_of_continuous_ae_zero h_cont (h_ae_zero'.mono fun k hk => by simp [hk])
  exact (sqrtPropagatorMap_eq_zero_iff m (f - g)).mp fun k => congr_fun h_eq k

/-! ## Strict positivity of the covariance -/

/-- **Strict positive definiteness**: the smeared covariance `C(f,f) > 0` for any
    nonzero test function `f`.  This rules out the Dirac-at-zero measure as
    a model satisfying the OS axioms.

    Proof: `C(f,f) = ‖T f‖²` where `T` is injective, so `f ≠ 0 ⟹ T f ≠ 0
    ⟹ ‖T f‖ > 0 ⟹ ‖T f‖² > 0`.
-/
theorem freeCovarianceFormR_strictPos (m : ℝ) [Fact (0 < m)]
    (f : TestFunction) (hf : f ≠ 0) :
    0 < freeCovarianceFormR m f f := by
  rw [freeCovarianceFormR_eq_normSq m f]
  have h_ne : embeddingMap m f ≠ 0 := by
    intro h_abs
    exact hf (embeddingMap_injective m (h_abs.trans (map_zero (embeddingMap m)).symm))
  exact sq_pos_of_pos (norm_pos_iff.mpr h_ne)

/-! ## Nontriviality of the GFF measure -/

/-- The variance of `⟨ω,f⟩` under the GFF is strictly positive for `f ≠ 0`.
    Equivalently, the pushforward by the pairing is a non-degenerate Gaussian.
-/
theorem gaussianFreeField_variance_pos (m : ℝ) [Fact (0 < m)]
    (f : TestFunction) (hf : f ≠ 0) :
    0 < ∫ ω, (distributionPairingCLM f ω) ^ 2 ∂(muGFF m).toMeasure := by
  rw [gff_second_moment_eq_covariance]
  exact freeCovarianceFormR_strictPos m f hf

/-- **The GFF is not a Dirac measure**: there exists a test function whose pairing
    with ω has nonzero variance.  This is the formal statement that the OS axiom
    verification in `Master.lean` is nontrivial.

    Any nonzero Schwartz function witnesses this.  We use a standard bump
    function on ℝ⁴, which exists by `ContDiff.exists_eq_one_of_isOpen`.
-/
theorem gaussianFreeField_not_dirac (m : ℝ) [Fact (0 < m)] :
    ∃ f : TestFunction, f ≠ 0 ∧
      0 < ∫ ω, (distributionPairingCLM f ω) ^ 2 ∂(muGFF m).toMeasure := by
  -- Schwartz space on ℝ⁴ is nontrivial: exhibit a nonzero element.
  -- This uses the existence of smooth compactly-supported bump functions.
  have ⟨f, hf⟩ : ∃ f : TestFunction, f ≠ 0 := by
    let φ : ContDiffBump (0 : SpaceTime) := ⟨1, 2, by norm_num, by norm_num⟩
    refine ⟨φ.hasCompactSupport.toSchwartzMap φ.contDiff, fun h => ?_⟩
    have h1 : φ (0 : SpaceTime) = 1 :=
      φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
    have h2 : (φ.hasCompactSupport.toSchwartzMap φ.contDiff) (0 : SpaceTime) =
              φ (0 : SpaceTime) := rfl
    rw [h] at h2; simp only [zero_apply, h1] at h2; exact one_ne_zero h2.symm
  exact ⟨f, hf, gaussianFreeField_variance_pos m f hf⟩

/-! ## UV divergence: pointwise covariance diverges at coincident points

The pointwise regularization `C(x,x) = 0` in `freeCovarianceBessel` is a convention
for the smeared (distribution) theory.  The actual limit diverges, confirming that
the free field has genuine UV singularity.

The smeared covariance `C(f,f) = ∫∫ f(x) C(x,y) f(y) dx dy` remains finite for all
Schwartz functions because the `1/r²` singularity of `K₁(mr)/r` is integrable
in 4 spatial dimensions (surface area ~ r³ compensates the kernel ~ 1/r²).
-/

/-- `K₁(z) → +∞` as `z → 0⁺`.

    For any `T > 0`,
    `K₁(z) = ∫₀^∞ e^{-z cosh t} cosh t dt ≥ T · e^{-z cosh T}`
    since `cosh t ≥ 1` on `[0,T]`.  As `z → 0⁺` the RHS → `T`,
    so `K₁(z)` eventually exceeds any bound.

    Formal proof uses monotone convergence: the integrand
    `e^{-z cosh t} cosh t` increases monotonically to `cosh t`
    as `z ↓ 0`, and `∫₀^∞ cosh t dt = +∞`.
-/
theorem besselK1_tendsto_atTop_at_zero :
    Filter.Tendsto besselK1 (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  -- Pick T so that T > M (T will be our integration range)
  set T := max M 1 + 1 with hT_def
  have hT_pos : (0 : ℝ) < T := by positivity
  have hT_gt_M : M < T := by simp only [hT_def]; linarith [le_max_left M 1]
  -- Integrability (from positivity: if not integrable, Bochner integral = 0, contradicting K₁ > 0)
  have h_int : ∀ z, 0 < z → IntegrableOn
      (fun t => Real.exp (-z * Real.cosh t) * Real.cosh t) (Set.Ici 0) volume :=
    fun z hz => not_not.mp fun h => absurd (integral_undef h) (besselK1_pos z hz).ne'
  -- Lower bound: K₁(z) ≥ exp(-z cosh T) * T for z > 0
  have h_lower : ∀ z, 0 < z → T * Real.exp (-z * Real.cosh T) ≤ besselK1 z := by
    intro z hz
    unfold besselK1
    -- On [0,T]: cosh t ≤ cosh T, so exp(-z cosh t) ≥ exp(-z cosh T); also cosh t ≥ 1
    have h_bound : ∀ t ∈ Set.Icc (0 : ℝ) T,
        Real.exp (-z * Real.cosh T) ≤ Real.exp (-z * Real.cosh t) * Real.cosh t := by
      intro t ht
      have h_ct : Real.cosh t ≤ Real.cosh T := by
        rw [Real.cosh_le_cosh, abs_of_nonneg ht.1, abs_of_nonneg hT_pos.le]; exact ht.2
      calc Real.exp (-z * Real.cosh T)
          ≤ Real.exp (-z * Real.cosh t) := by
            apply Real.exp_le_exp.mpr; nlinarith [Real.cosh_pos t]
        _ ≤ Real.exp (-z * Real.cosh t) * Real.cosh t := by
            nlinarith [Real.one_le_cosh t, Real.exp_nonneg (-z * Real.cosh t)]
    have h_cont_integrand : Continuous (fun t : ℝ => Real.exp (-z * Real.cosh t) * Real.cosh t) :=
      (Real.continuous_exp.comp (continuous_const.mul Real.continuous_cosh)).mul
        Real.continuous_cosh
    calc T * Real.exp (-z * Real.cosh T)
        = Real.exp (-z * Real.cosh T) * volume.real (Set.Icc 0 T) := by
          rw [Real.volume_real_Icc_of_le hT_pos.le]; ring
      _ ≤ ∫ t in Set.Icc 0 T, Real.exp (-z * Real.cosh t) * Real.cosh t :=
          setIntegral_ge_of_const_le_real measurableSet_Icc
            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
            h_bound h_cont_integrand.integrableOn_Icc
      _ ≤ ∫ t in Set.Ici 0, Real.exp (-z * Real.cosh t) * Real.cosh t :=
          setIntegral_mono_set (h_int z hz)
            (Filter.Eventually.of_forall fun t =>
              mul_nonneg (Real.exp_nonneg _) (Real.cosh_pos t).le)
            (HasSubset.Subset.eventuallyLE fun t (ht : t ∈ Set.Icc 0 T) => ht.1)
  -- As z → 0⁺, T * exp(-z cosh T) → T > M, so eventually K₁(z) ≥ M
  have h_open : IsOpen {z : ℝ | M < T * Real.exp (-z * Real.cosh T)} :=
    isOpen_lt continuous_const (by fun_prop)
  have h_zero_mem : (0 : ℝ) ∈ {z : ℝ | M < T * Real.exp (-z * Real.cosh T)} := by
    simp only [Set.mem_setOf_eq, neg_zero, zero_mul, Real.exp_zero, mul_one]; exact hT_gt_M
  exact ((Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (h_open.mem_nhds h_zero_mem)).and self_mem_nhdsWithin).mono
    fun z ⟨hz1, hz2⟩ => le_trans hz1.le (h_lower z hz2)

/-- The free covariance `C(x,y) → +∞` as `x → y` (UV divergence).

    `C(x,y) = (m/(4π²r)) · K₁(mr)` where `r = ‖x-y‖`.  As `r → 0⁺`,
    `K₁(mr) ≥ K₁(1) > 0` for `mr ≤ 1` and `m/(4π²r) → +∞`,
    so the product diverges.
-/
theorem freeCovariance_tendsto_atTop (m : ℝ) [Fact (0 < m)] (x₀ : SpaceTime) :
    Filter.Tendsto (fun x => freeCovarianceBessel m x₀ x)
      (nhdsWithin x₀ {x₀}ᶜ) Filter.atTop := by
  have hm := Fact.out (self := ‹Fact (0 < m)›)
  -- Step 1: ‖x₀ - x‖ → 0⁺ as x → x₀ through {x₀}ᶜ
  have h_norm : Filter.Tendsto (fun x => ‖x₀ - x‖)
      (nhdsWithin x₀ {x₀}ᶜ) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun x : SpaceTime => ‖x₀ - x‖) x₀ :=
        (continuous_norm.comp (continuous_const.sub continuous_id)).continuousAt
      simp only [ContinuousAt, sub_self, norm_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun x hx =>
        norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hx (Set.mem_singleton_iff.mpr h.symm))
  -- Step 2: m/(4π²) * r⁻¹ → ∞ as r → 0⁺
  have h_prefactor : Filter.Tendsto (fun r : ℝ => m / (4 * Real.pi ^ 2) * r⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity : 0 < m / (4 * Real.pi ^ 2))
      tendsto_inv_nhdsGT_zero
  -- Step 3: K₁(mr) → ∞ as r → 0⁺
  have h_K1 : Filter.Tendsto (fun r => besselK1 (m * r))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    apply besselK1_tendsto_atTop_at_zero.comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun r : ℝ => m * r) 0 :=
        (continuous_const.mul continuous_id).continuousAt
      simp only [ContinuousAt, mul_zero] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun r hr => mul_pos hm hr
  -- Step 4: Product → ∞
  have h_prod := h_prefactor.atTop_mul_atTop₀ h_K1
  -- Step 5: Compose with norm and identify with freeCovarianceBessel
  rw [Filter.tendsto_atTop]; intro M
  refine (Filter.tendsto_atTop.mp (h_prod.comp h_norm) M).mono fun x hx => ?_
  -- For x in our filter, freeCovarianceBessel equals the product (m/(4π²)) r⁻¹ K₁(mr)
  suffices h : freeCovarianceBessel m x₀ x = m / (4 * Real.pi ^ 2) * ‖x₀ - x‖⁻¹ *
      besselK1 (m * ‖x₀ - x‖) by rw [h]; exact hx
  unfold freeCovarianceBessel
  by_cases hr : ‖x₀ - x‖ = 0
  · simp [hr]
  · simp only [hr, ↓reduceIte]; field_simp

end OSforGFF
