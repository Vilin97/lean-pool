/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.SynthesisRegularity
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.ConvolutionAlgebra
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Limits
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Resolvent

/-!
# Transport between position space and momentum space

Dictionary between smooth `2πℤⁿ`-periodic functions `f : ℝⁿ → ℂ` and their coefficient
sequences `stdFourierCoeff n f : ℤⁿ → ℂ`, used to move Günther's fixed-point equation
from the momentum side (where it is solved) back to position space (where Theorem B is
stated):

* coefficients of smooth periodic functions are rapidly decaying (`IsRapidDecay`);
* `stdFourierCoeff` is linear (sums, differences, scalar multiples) and turns products
  into `seqConv`, `∂ⱼ` into `partialCoeff j`, and `L = ∑ₖ ∂ₖ²` into `-laplacianCoeff`;
* real-valued functions have `conjReflect`-fixed coefficients;
* `fourierSynthesis` is linear on absolutely summable sequences;
* `IsRapidDecay` is closed under all the momentum-side operations of the Günther operator.
-/

open scoped BigOperators ComplexConjugate ContDiff
open Complex

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Rapid decay of coefficients -/

/-- Coefficients of smooth periodic functions are rapidly decaying
(`stdFourierCoeff_rapid_decay` + `memSobolev_of_rapid_decay`). -/
theorem isRapidDecay_stdFourierCoeff (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) :
    IsRapidDecay n (stdFourierCoeff n f) := fun s =>
  memSobolev_of_rapid_decay hn (fun N => stdFourierCoeff_rapid_decay hn hsmooth hper N) s

/-! ## Linearity of coefficients (continuous integrands) -/

/-- Integrability on the period cube of `θ ↦ f θ · e_{-m}(θ)` for continuous `f`. -/
private lemma integrableOn_mul_fourierExp {f : (Fin n → ℝ) → ℂ} (hf : Continuous f)
    (m : Fin n → ℤ) :
    MeasureTheory.IntegrableOn (fun θ : Fin n → ℝ => f θ * fourierExp n (-m) θ)
      (Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • (1 : Fin n → ℝ))) MeasureTheory.volume :=
  (hf.mul ((fourierExp_contDiff (-m)).continuous)).continuousOn.integrableOn_compact isCompact_Icc

lemma stdFourierCoeff_add {f g : (Fin n → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g) :
    stdFourierCoeff n (fun x => f x + g x) = fun m => stdFourierCoeff n f m + stdFourierCoeff n g m := by
  funext m
  unfold stdFourierCoeff
  simp only [add_mul]
  rw [MeasureTheory.integral_add (integrableOn_mul_fourierExp hf m)
    (integrableOn_mul_fourierExp hg m), mul_add]

lemma stdFourierCoeff_sub {f g : (Fin n → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g) :
    stdFourierCoeff n (fun x => f x - g x) = fun m => stdFourierCoeff n f m - stdFourierCoeff n g m := by
  funext m
  unfold stdFourierCoeff
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub (integrableOn_mul_fourierExp hf m)
    (integrableOn_mul_fourierExp hg m), mul_sub]

lemma stdFourierCoeff_const_mul (c : ℂ) (f : (Fin n → ℝ) → ℂ) :
    stdFourierCoeff n (fun x => c * f x) = fun m => c * stdFourierCoeff n f m := by
  funext m
  unfold stdFourierCoeff
  simp_rw [mul_assoc]
  rw [MeasureTheory.integral_const_mul]
  ring

lemma stdFourierCoeff_neg (f : (Fin n → ℝ) → ℂ) :
    stdFourierCoeff n (fun x => -f x) = fun m => -stdFourierCoeff n f m := by
  funext m
  unfold stdFourierCoeff
  rw [show (fun θ => -f θ * fourierExp n (-m) θ) = fun θ => -(f θ * fourierExp n (-m) θ) from
    funext fun θ => by ring, MeasureTheory.integral_neg]
  ring

lemma stdFourierCoeff_finset_sum' {ι : Type*} (S : Finset ι) {f : ι → (Fin n → ℝ) → ℂ}
    (hf : ∀ i ∈ S, Continuous (f i)) :
    stdFourierCoeff n (fun x => ∑ i ∈ S, f i x) = fun m => ∑ i ∈ S, stdFourierCoeff n (f i) m := by
  funext m
  exact stdFourierCoeff_finset_sum S f hf m

/-! ## Products, derivatives, the Laplacian -/

/-- **Coefficients of a product are the convolution of the coefficients** (for smooth
periodic factors): `f = (f̂)ˇ`, `g = (ĝ)ˇ` by Fourier inversion, `f g = (f̂ ⊛ ĝ)ˇ` by B2, and
the coefficients of a synthesis of a rapidly decaying sequence are that sequence. -/
theorem stdFourierCoeff_mul (hn : 0 < n) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfp : IsPeriodic2Pi f) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodic2Pi g) :
    stdFourierCoeff n (fun x => f x * g x) = seqConv (stdFourierCoeff n f) (stdFourierCoeff n g) := by
  have hsa : Summable (fun m => ‖stdFourierCoeff n f m‖) :=
    (isRapidDecay_stdFourierCoeff hn hf hfp).summable_norm hn
  have hsb : Summable (fun m => ‖stdFourierCoeff n g m‖) :=
    (isRapidDecay_stdFourierCoeff hn hg hgp).summable_norm hn
  have hfun : (fun x => f x * g x)
      = fourierSynthesis n (seqConv (stdFourierCoeff n f) (stdFourierCoeff n g)) := by
    funext x
    rw [fourierSynthesis_seqConv hsa hsb x,
      fourierSynthesis_stdFourierCoeff_of_smoothPeriodic hn hf hfp x,
      fourierSynthesis_stdFourierCoeff_of_smoothPeriodic hn hg hgp x]
  funext m
  rw [hfun]
  exact stdFourierCoeff_fourierSynthesis (summable_norm_seqConv hsa hsb) m

/-- `stdFourierCoeff_partialDeriv` as an equality of sequences. -/
theorem stdFourierCoeff_partialDeriv' (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) (j : Fin n) :
    stdFourierCoeff n (partialDeriv j f) = partialCoeff j (stdFourierCoeff n f) := by
  funext m
  exact stdFourierCoeff_partialDeriv hn hf hper j m

/-- `∂ⱼ∂ⱼ` on coefficients is multiplication by `-mⱼ²`; summing over `j`,
`L = ∑ⱼ ∂ⱼ²` corresponds to `-laplacianCoeff`. -/
theorem stdFourierCoeff_sumSqDeriv (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) :
    stdFourierCoeff n (fun x => ∑ k, partialDeriv k (partialDeriv k f) x)
      = fun m => -laplacianCoeff (stdFourierCoeff n f) m := by
  funext m
  have h : stdFourierCoeff n (fun x => ∑ k, partialDeriv k (partialDeriv k f) x) m
      = stdFourierCoeff n (laplacian f) m := rfl
  rw [h, stdFourierCoeff_laplacian hn hf hper m, laplacianCoeff]
  push_cast
  ring

/-- Real-valued functions have `conjReflect`-fixed coefficients. -/
theorem conjReflect_stdFourierCoeff_of_real {f : (Fin n → ℝ) → ℂ} (hf : Continuous f)
    (hreal : ∀ x, (f x).im = 0) : conjReflect (stdFourierCoeff n f) = stdFourierCoeff n f := by
  funext m
  have hc : ∀ θ : Fin n → ℝ, (starRingEnd ℂ) (f θ * fourierExp n m θ)
      = f θ * fourierExp n (-m) θ := by
    intro θ
    rw [map_mul, starRingEnd_fourierExp, Complex.conj_eq_iff_im.2 (hreal θ)]
  simp only [conjReflect, stdFourierCoeff, neg_neg]
  rw [map_mul, ← integral_conj]
  simp_rw [hc]
  congr 1
  simp [map_inv₀, map_ofNat]

/-- Coefficient injectivity on smooth periodic functions (from Fourier inversion). -/
theorem eq_of_stdFourierCoeff_eq (hn : 0 < n) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfp : IsPeriodic2Pi f) (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodic2Pi g)
    (h : stdFourierCoeff n f = stdFourierCoeff n g) : f = g := by
  funext x
  rw [← fourierSynthesis_stdFourierCoeff_of_smoothPeriodic hn hf hfp x,
    ← fourierSynthesis_stdFourierCoeff_of_smoothPeriodic hn hg hgp x, h]

/-! ## Linearity of synthesis -/

lemma fourierSynthesis_add' {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖)) (hb : Summable (fun m => ‖b m‖)) :
    fourierSynthesis n (fun m => a m + b m) = fun θ => fourierSynthesis n a θ + fourierSynthesis n b θ := by
  funext θ
  exact fourierSynthesis_add ha hb θ

lemma fourierSynthesis_sub {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖)) (hb : Summable (fun m => ‖b m‖)) :
    fourierSynthesis n (fun m => a m - b m) = fun θ => fourierSynthesis n a θ - fourierSynthesis n b θ := by
  funext θ
  unfold fourierSynthesis
  rw [← Summable.tsum_sub]
  · exact tsum_congr fun m => sub_mul _ _ _
  · exact .of_norm <| by simpa [norm_fourierExp] using ha
  · exact .of_norm <| by simpa [norm_fourierExp] using hb

lemma fourierSynthesis_const_mul (c : ℂ) (a : (Fin n → ℤ) → ℂ) :
    fourierSynthesis n (fun m => c * a m) = fun θ => c * fourierSynthesis n a θ := by
  funext θ
  unfold fourierSynthesis
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

lemma fourierSynthesis_neg (a : (Fin n → ℤ) → ℂ) :
    fourierSynthesis n (fun m => -a m) = fun θ => -fourierSynthesis n a θ := by
  funext θ
  unfold fourierSynthesis
  rw [← tsum_neg]
  exact tsum_congr fun m => by ring

lemma fourierSynthesis_finset_sum {ι : Type*} (S : Finset ι) {a : ι → (Fin n → ℤ) → ℂ}
    (ha : ∀ i ∈ S, Summable (fun m => ‖a i m‖)) :
    fourierSynthesis n (fun m => ∑ i ∈ S, a i m) = fun θ => ∑ i ∈ S, fourierSynthesis n (a i) θ := by
  funext θ
  unfold fourierSynthesis
  rw [show (fun m : Fin n → ℤ => (∑ i ∈ S, a i m) * fourierExp n m θ)
      = fun m => ∑ i ∈ S, a i m * fourierExp n m θ from
    funext fun m => by rw [Finset.sum_mul]]
  exact Summable.tsum_finsetSum fun i hi =>
    .of_norm <| by simpa [norm_fourierExp] using ha i hi

/-! ## Closure of rapid decay -/

lemma isRapidDecay_zero : IsRapidDecay n (fun _ => (0 : ℂ)) := fun s => memSobolev_zero s

lemma IsRapidDecay.add {a b : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) (hb : IsRapidDecay n b) :
    IsRapidDecay n (fun m => a m + b m) := fun s => (ha s).add (hb s)

lemma IsRapidDecay.sub {a b : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) (hb : IsRapidDecay n b) :
    IsRapidDecay n (fun m => a m - b m) := fun s => (ha s).sub (hb s)

lemma IsRapidDecay.neg {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) :
    IsRapidDecay n (fun m => -a m) := fun s => (ha s).neg

lemma IsRapidDecay.const_mul {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) (c : ℂ) :
    IsRapidDecay n (fun m => c * a m) := fun s => (ha s).smul c

lemma IsRapidDecay.finset_sum {ι : Type*} (S : Finset ι) {a : ι → (Fin n → ℤ) → ℂ}
    (ha : ∀ i ∈ S, IsRapidDecay n (a i)) : IsRapidDecay n (fun m => ∑ i ∈ S, a i m) :=
  fun s => MemSobolev.finset_sum S fun i hi => ha i hi s

lemma IsRapidDecay.resolventCoeff {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) :
    IsRapidDecay n (resolventCoeff a) := by
  intro s
  have := memSobolev_resolventCoeff (ha (s - 2))
  simpa using this

lemma IsRapidDecay.laplacianCoeff {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) :
    IsRapidDecay n (laplacianCoeff a) := fun s => memSobolev_laplacianCoeff (ha (s + 2))

/-- Convolution of rapidly decaying sequences is rapidly decaying (MT2 at every level
`s > n/2`, then monotonicity). -/
lemma IsRapidDecay.seqConv (hn : 0 < n) {a b : (Fin n → ℤ) → ℂ}
    (ha : IsRapidDecay n a) (hb : IsRapidDecay n b) : IsRapidDecay n (seqConv a b) := by
  intro s
  set t : ℝ := max s (n : ℝ) + 1 with ht
  have hst : s ≤ t := by
    have := le_max_left s (n : ℝ)
    simp only [ht]; linarith
  have hnt : (n : ℝ) < 2 * t := by
    have := le_max_right s (n : ℝ)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [ht]; linarith
  exact ((second_multiplication_theorem_seq hn hnt (ha t) (hb t)).1).mono hst

end NashEmbedding.Sobolev

end
