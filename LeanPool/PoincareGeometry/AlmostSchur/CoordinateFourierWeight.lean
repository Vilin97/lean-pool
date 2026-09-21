/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakJetFourierRepresentative
public import LeanPool.PoincareGeometry.AlmostSchur.CompactWeakFourierMultiplier
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Coordinate moments control the Sobolev Fourier weight

An actual orthonormal basis is required. The optional coordinate represents
the zeroth-order factor 1, so products of n factors contain every lower order
without a separate low-frequency argument.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ContDiff
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

/-- Optional coordinate: `none` is the low-frequency factor 1. -/
def basisFrequencyCoordinate (b : OrthonormalBasis ι ℝ E) (x : E) : Option ι → ℝ
  | none => 1
  | some i => inner ℝ (b i) x

/-- Basis reconstruction, not a spanning-family assumption, controls the norm. -/
theorem one_add_norm_le_sum_basisFrequencyCoordinate
    (b : OrthonormalBasis ι ℝ E) (x : E) :
    1 + ‖x‖ ≤ ∑ i : Option ι, |basisFrequencyCoordinate b x i| := by
  classical
  have hn : ‖x‖ ≤ ∑ i, |inner ℝ (b i) x| := by
    calc
      ‖x‖ = ‖∑ i, inner ℝ (b i) x • b i‖ := congrArg norm (b.sum_repr' x).symm
      _ ≤ ∑ i, ‖inner ℝ (b i) x • b i‖ := norm_sum_le _ _
      _ = _ := by simp [norm_smul, b.norm_eq_one, Real.norm_eq_abs]
  simpa [Fintype.sum_option, basisFrequencyCoordinate, add_comm] using add_le_add_left hn 1

/-- All optional coordinate monomials of length n control the complete
weight `(1 + ‖ξ‖)^n` in L². No nonzero-dimension assumption is needed. -/
theorem memLp_weight_of_coordinate_moments
    (b : OrthonormalBasis ι ℝ E) (n : ℕ) {F : E → ℂ}
    (hF : AEStronglyMeasurable F volume)
    (hm : ∀ p : Fin n → Option ι,
      MemLp (fun x => (∏ j, (basisFrequencyCoordinate b x (p j) : ℂ)) * F x) 2 volume) :
    MemLp (fun x => (1 + ‖x‖) ^ n * ‖F x‖) 2 volume := by
  classical
  have hsum := memLp_finsetSum Finset.univ
    (fun p (_ : p ∈ (Finset.univ : Finset (Fin n → Option ι))) => (hm p).norm)
  apply hsum.mono
    ((by fun_prop : AEStronglyMeasurable (fun x : E => (1 + ‖x‖) ^ n) volume).mul hF.norm)
  filter_upwards [] with x
  have hnonneg : 0 ≤ ∑ p : Fin n → Option ι,
      ‖(∏ j, (basisFrequencyCoordinate b x (p j) : ℂ)) * F x‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  change ‖(1 + ‖x‖) ^ n * ‖F x‖‖ ≤
    ‖∑ p : Fin n → Option ι, ‖(∏ j, (basisFrequencyCoordinate b x (p j) : ℂ)) * F x‖‖
  rw [Real.norm_of_nonneg hnonneg,
    Real.norm_of_nonneg (show 0 ≤ (1 + ‖x‖) ^ n * ‖F x‖ by positivity)]
  calc
    (1 + ‖x‖) ^ n * ‖F x‖ ≤
        (∑ i : Option ι, |basisFrequencyCoordinate b x i|) ^ n * ‖F x‖ :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (one_add_norm_le_sum_basisFrequencyCoordinate b x) n)
        (norm_nonneg _)
    _ = ∑ p : Fin n → Option ι,
        ‖(∏ j, (basisFrequencyCoordinate b x (p j) : ℂ)) * F x‖ := by
      rw [Fintype.sum_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      simp [norm_mul, norm_prod, Complex.norm_real, Real.norm_eq_abs]

/-- Coordinate moment control above half the dimension plus k gives a C^k
representative of an integrable input. The moment hypotheses are analytic
Fourier statements, to be supplied by localized weak derivative identities. -/
theorem exists_contDiff_representative_of_coordinate_moments
    (b : OrthonormalBasis ι ℝ E) (n k : ℕ)
    (hn : (Module.finrank ℝ E : ℝ) < 2 * ((n : ℝ) - k))
    {u : E → ℂ} (hu : Integrable u volume)
    (hm : ∀ p : Fin n → Option ι,
      MemLp (fun x => (∏ j, (basisFrequencyCoordinate b x (p j) : ℂ)) * 𝓕 u x) 2 volume) :
    ∃ g : E → ℂ, ContDiff ℝ k g ∧ g =ᵐ[volume] u := by
  have hFc : Continuous (𝓕 u) := by
    rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr hu)]
    exact BoundedContinuousFunction.continuous _
  apply exists_contDiff_representative_of_weighted_fourier hu k hn
  simpa only [Real.rpow_natCast] using memLp_weight_of_coordinate_moments b n
    hFc.aestronglyMeasurable hm

/-- The ordinary Fourier integral of actual L¹ ∩ L² function data is L²;
all quotient-to-function conversions are justified by almost-everywhere equality. -/
theorem memLp_fourier_of_L1_L2 {f : E → ℂ}
    (h₁ : Integrable f volume) (h₂ : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume := by
  have hi : Integrable (h₂.toLp f : E → ℂ) volume := h₁.congr h₂.coeFn_toLp.symm
  have hm := memLp_fourier_integral_of_integrable_L2 (h₂.toLp f) hi
  have he : 𝓕 (h₂.toLp f : E → ℂ) = 𝓕 f := by
    funext x
    exact Real.fourier_congr_ae h₂.coeFn_toLp x
  rwa [he] at hm

/-- Iterating the proved weak derivative multiplier identity gives the exact
ordered monomial formula for every valid word. -/
theorem fourier_word_of_weak_jet (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (U : List ι → E → ℝ)
    (h₁ : ∀ w, w.length ≤ n → Integrable (U w) volume)
    (hweak : ∀ w, w.length < n → ∀ i (φ : E → ℝ), ContDiff ℝ ∞ φ →
      (∫ x, U w x * fderiv ℝ φ x (b i)) = -(∫ x, U (i :: w) x * φ x))
    (w : List ι) (hw : w.length ≤ n) (ξ : E) :
    𝓕 (fun x => (U w x : ℂ)) ξ = (2 * Real.pi * Complex.I) ^ w.length *
      (w.map (fun i => (inner ℝ (b i) ξ : ℂ))).prod * 𝓕 (fun x => (U [] x : ℂ)) ξ := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hwl : w.length < n := by simp only [List.length_cons] at hw; omega
    rw [fourier_weak_derivative_multiplier (b i) (h₁ w hwl.le) (h₁ (i :: w) hw)
      (hweak w hwl i), ih hwl.le]
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ, real_inner_comm ξ (b i)]
    ring

/-- Weak derivative fields supply L² control of each raw coordinate monomial,
not merely a formal multiplier equation. -/
theorem memLp_word_frequency_of_weak_jet (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (U : List ι → E → ℝ)
    (h₁ : ∀ w, w.length ≤ n → Integrable (U w) volume)
    (h₂ : ∀ w, w.length ≤ n → MemLp (U w) 2 volume)
    (hweak : ∀ w, w.length < n → ∀ i (φ : E → ℝ), ContDiff ℝ ∞ φ →
      (∫ x, U w x * fderiv ℝ φ x (b i)) = -(∫ x, U (i :: w) x * φ x))
    (w : List ι) (hw : w.length ≤ n) :
    MemLp (fun ξ => (w.map (fun i => (inner ℝ (b i) ξ : ℂ))).prod *
      𝓕 (fun x => (U [] x : ℂ)) ξ) 2 volume := by
  have hm : MemLp (𝓕 (fun x => (U w x : ℂ))) 2 volume :=
    memLp_fourier_of_L1_L2 (f := fun x => (U w x : ℂ)) (h₁ w hw).ofReal (h₂ w hw).ofReal
  have hn : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  convert! hm.const_mul ((2 * Real.pi * Complex.I) ^ w.length)⁻¹ using 1
  funext ξ
  apply (eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hn)).mpr
  simpa only [mul_assoc] using (fourier_word_of_weak_jet b n U h₁ hweak w hw ξ).symm

/-- Omitting optional zero-order factors preserves the coordinate product. -/
theorem optional_coordinate_product (b : OrthonormalBasis ι ℝ E) (ξ : E)
    (l : List (Option ι)) :
    (l.map (fun i => (basisFrequencyCoordinate b ξ i : ℂ))).prod =
      ((l.filterMap id).map (fun i => (inner ℝ (b i) ξ : ℂ))).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases a <;> simp only [List.map_cons, List.prod_cons, List.filterMap_cons,
      id_eq, basisFrequencyCoordinate, Complex.ofReal_one, one_mul]
    · exact ih
    · exact congrArg (fun z : ℂ => (inner ℝ (b _) ξ : ℂ) * z) ih

/-- A genuine finite whole-space L¹ ∩ L² weak jet controls the full order-n
Fourier weight. No frequency hypothesis remains in this statement. -/
theorem weak_jet_weighted_fourier (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (U : List ι → E → ℝ)
    (h₁ : ∀ w, w.length ≤ n → Integrable (U w) volume)
    (h₂ : ∀ w, w.length ≤ n → MemLp (U w) 2 volume)
    (hweak : ∀ w, w.length < n → ∀ i (φ : E → ℝ), ContDiff ℝ ∞ φ →
      (∫ x, U w x * fderiv ℝ φ x (b i)) = -(∫ x, U (i :: w) x * φ x)) :
    MemLp (fun ξ => (1 + ‖ξ‖) ^ n * ‖𝓕 (fun x => (U [] x : ℂ)) ξ‖) 2 volume := by
  have hFc : Continuous (𝓕 (fun x => (U [] x : ℂ))) := by
    rw [← Real.fourierTransform_toLp
      (memLp_one_iff_integrable.mpr (h₁ [] (by simp)).ofReal)]
    exact BoundedContinuousFunction.continuous _
  apply memLp_weight_of_coordinate_moments b n hFc.aestronglyMeasurable
  intro p
  let w := (List.ofFn p).filterMap id
  have hw : w.length ≤ n := by
    exact (List.length_filterMap_le _ _).trans (by simp)
  have hm := memLp_word_frequency_of_weak_jet b n U h₁ h₂ hweak w hw
  convert! hm using 1
  funext ξ
  congr 1
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_apply, w] using
    optional_coordinate_product b ξ (List.ofFn p)

/-- Finite weak L² derivative data above half the dimension plus k yield an
actual real C^k representative. The whole-space test identities are an
explicit interface satisfied by compact localization, not regularity premises. -/
theorem weak_jet_exists_contDiff_representative
    (b : OrthonormalBasis ι ℝ E) (n k : ℕ)
    (hn : (Module.finrank ℝ E : ℝ) < 2 * ((n : ℝ) - k))
    (U : List ι → E → ℝ)
    (h₁ : ∀ w, w.length ≤ n → Integrable (U w) volume)
    (h₂ : ∀ w, w.length ≤ n → MemLp (U w) 2 volume)
    (hweak : ∀ w, w.length < n → ∀ i (φ : E → ℝ), ContDiff ℝ ∞ φ →
      (∫ x, U w x * fderiv ℝ φ x (b i)) = -(∫ x, U (i :: w) x * φ x)) :
    ∃ g : E → ℝ, ContDiff ℝ k g ∧ g =ᵐ[volume] U [] := by
  have hm := weak_jet_weighted_fourier b n U h₁ h₂ hweak
  have hmr : MemLp (fun ξ => (1 + ‖ξ‖) ^ (n : ℝ) *
      ‖𝓕 (fun x => (U [] x : ℂ)) ξ‖) 2 volume := by
    simpa only [Real.rpow_natCast] using hm
  obtain ⟨g, hg, hge⟩ := exists_contDiff_representative_of_weighted_fourier
    (h₁ [] (by simp)).ofReal k hn hmr
  refine ⟨fun x => (g x).re, Complex.reCLM.contDiff.comp hg, ?_⟩
  filter_upwards [hge] with x hx
  simpa using congrArg Complex.re hx

end AlmostSchur
