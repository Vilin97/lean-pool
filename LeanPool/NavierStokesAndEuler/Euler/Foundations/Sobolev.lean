/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-!
Actual Fourier Sobolev estimates on Euclidean spaces. The Sobolev norm below is
the L² norm of `(1 + |ξ|²)^(s/2) 𝓕f(ξ)`, so its relation to the represented
function is explicit. All estimates are proved from inversion and Hölder.
-/

@[expose] public section

noncomputable section

namespace EulerSobolev

open MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

/-- The real Euclidean domain of dimension `d`. -/
abbrev Domain (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Fourier weight defining the inhomogeneous Sobolev order `s`. -/
noncomputable def besselWeight (d : ℕ) (s : ℝ) (ξ : Domain d) : ℝ :=
  (1 + ‖ξ‖ ^ 2) ^ (s / 2)

theorem besselWeight_temperate (d : ℕ) (s : ℝ) :
    (besselWeight d s).HasTemperateGrowth :=
  Function.hasTemperateGrowth_one_add_norm_sq_rpow (Domain d) (s / 2)

theorem besselWeight_pos (d : ℕ) (s : ℝ) (ξ : Domain d) : 0 < besselWeight d s ξ := by
  unfold besselWeight
  positivity

theorem besselWeight_neg_mul (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d (-s) ξ * besselWeight d s ξ = 1 := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  have he : -s / 2 + s / 2 = 0 := by ring
  rw [he, Real.rpow_zero]

theorem besselWeight_add (d : ℕ) (s t : ℝ) (ξ : Domain d) :
    besselWeight d (s + t) ξ = besselWeight d s ξ * besselWeight d t ξ := by
  unfold besselWeight
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

/-- One derivative factor is absorbed by one Sobolev order. -/
theorem besselWeight_mul_norm_le (d : ℕ) (s : ℝ) (ξ : Domain d) :
    besselWeight d s ξ * ‖ξ‖ ≤ besselWeight d (s + 1) ξ := by
  have hn : ‖ξ‖ ≤ besselWeight d 1 ξ := by
    unfold besselWeight
    rw [← Real.sqrt_eq_rpow]
    calc
      ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg ξ)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  rw [besselWeight_add]
  exact mul_le_mul_of_nonneg_left hn (besselWeight_pos d s ξ).le

/-- The reciprocal Bessel weight is in L² exactly in the range needed here. -/
theorem reciprocal_weight_memLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    MemLp (besselWeight d (-s)) 2 (volume : Measure (Domain d)) := by
  have hm : AEStronglyMeasurable (besselWeight d (-s)) (volume : Measure (Domain d)) :=
    (besselWeight_temperate d (-s)).1.continuous.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  have hi : Integrable (fun ξ : Domain d => (1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq (by simpa [Domain] using hs)
  apply hi.congr
  filter_upwards with ξ
  dsimp only [besselWeight]
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

/-- The reciprocal Fourier weight represented as a genuine `L²` element. -/
noncomputable def reciprocalWeightLp (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (reciprocal_weight_memLp d s hs).toLp (besselWeight d (-s))

/-- A finite Sobolev embedding constant: the `L²` norm of the reciprocal weight. -/
noncomputable def embeddingConstant (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s) : ℝ :=
  ‖reciprocalWeightLp d s hs‖

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Fourier transform multiplied by the Sobolev weight. -/
noncomputable def weightedFourier (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) :
    𝓢(Domain d, F) :=
  SchwartzMap.smulLeftCLM F (besselWeight d s) (𝓕 f)

omit [CompleteSpace F] in
theorem weightedFourier_apply (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) (ξ : Domain d) :
    weightedFourier d s f ξ = besselWeight d s ξ • 𝓕 f ξ := by
  simp [weightedFourier, SchwartzMap.smulLeftCLM_apply_apply (besselWeight_temperate d s)]

/-- The inhomogeneous Fourier `Hˢ` norm of a Schwartz function. -/
noncomputable def sobolevNorm (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) : ℝ :=
  ‖(weightedFourier d s f).toLp 2‖

/-- Fourier inversion bounds a Schwartz function pointwise by the L¹ norm of its transform. -/
theorem norm_apply_le_fourier_L1 (d : ℕ) (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖f x‖ ≤ ‖(𝓕 f).toLp 1‖ := by
  have h := SchwartzMap.norm_fourier_apply_le_toLp_one (𝓕 f) (-x)
  have he : ‖f x‖ = ‖𝓕 (𝓕 f) (-x)‖ := by
    change ‖f x‖ = ‖(𝓕⁻ (𝓕 f)) x‖
    rw [fourierInv_fourier_eq]
  exact he ▸ h

omit [CompleteSpace F] in
/-- Hölder with the reciprocal weight converts the Fourier L¹ norm into the Hˢ norm. -/
theorem fourier_L1_le_sobolevNorm (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s)
    (f : 𝓢(Domain d, F)) :
    ‖(𝓕 f).toLp 1‖ ≤ embeddingConstant d s hs * sobolevNorm d s f := by
  have hid : (besselWeight d (-s) • (weightedFourier d s f : Domain d → F)) =
      ((𝓕 f : 𝓢(Domain d, F)) : Domain d → F) := by
    ext ξ
    simp only [Pi.smul_apply', weightedFourier_apply, smul_smul, besselWeight_neg_mul, one_smul]
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    ((weightedFourier d s f).memLp 2 volume).1 (reciprocal_weight_memLp d s hs).1
  rw [hid] at hh
  have hfin : eLpNorm (besselWeight d (-s)) 2 volume *
      eLpNorm (weightedFourier d s f) 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (reciprocal_weight_memLp d s hs).eLpNorm_ne_top
      ((weightedFourier d s f).memLp 2 volume).eLpNorm_ne_top
  have h := ENNReal.toReal_mono hfin hh
  simpa only [SchwartzMap.norm_toLp, embeddingConstant, reciprocalWeightLp,
    Lp.norm_toLp, sobolevNorm, ENNReal.toReal_mul] using h

/-- A genuine pointwise Sobolev embedding for every `s > d/2`. -/
theorem norm_apply_le_sobolevNorm (d : ℕ) (s : ℝ) (hs : (d : ℝ) < 2 * s)
    (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖f x‖ ≤ embeddingConstant d s hs * sobolevNorm d s f :=
  (norm_apply_le_fourier_L1 d f x).trans (fourier_L1_le_sobolevNorm d s hs f)

open scoped LineDeriv

omit [CompleteSpace F] in
/-- The actual Fourier multiplier formula bounds each directional derivative. -/
theorem fourier_lineDeriv_norm_le (d : ℕ) (f : 𝓢(Domain d, F)) (m ξ : Domain d) :
    ‖𝓕 (∂_{m} f) ξ‖ ≤ (2 * Real.pi) * ‖ξ‖ * ‖m‖ * ‖𝓕 f ξ‖ := by
  have ht : (fun ξ : Domain d => inner ℝ ξ m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have he : 𝓕 (∂_{m} f) ξ = (2 * Real.pi * Complex.I) • ((inner ℝ ξ m) • 𝓕 f ξ) := by
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    simp [SchwartzMap.smulLeftCLM_apply_apply ht]
  have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [he, norm_smul, norm_smul, hc]
  have hi := norm_inner_le_norm (𝕜 := ℝ) ξ m
  nlinarith [mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hi (norm_nonneg (𝓕 f ξ))) (show 0 ≤ 2 * Real.pi by positivity)]

omit [CompleteSpace F] in
theorem weightedFourier_lineDeriv_norm_le (d : ℕ) (s : ℝ)
    (f : 𝓢(Domain d, F)) (m ξ : Domain d) :
    ‖weightedFourier d s (∂_{m} f) ξ‖ ≤
      (2 * Real.pi * ‖m‖) * ‖weightedFourier d (s + 1) f ξ‖ := by
  rw [weightedFourier_apply, weightedFourier_apply, norm_smul, norm_smul,
    Real.norm_of_nonneg (besselWeight_pos d s ξ).le,
    Real.norm_of_nonneg (besselWeight_pos d (s + 1) ξ).le]
  calc
    _ ≤ besselWeight d s ξ * ((2 * Real.pi) * ‖ξ‖ * ‖m‖ * ‖𝓕 f ξ‖) :=
      mul_le_mul_of_nonneg_left (fourier_lineDeriv_norm_le d f m ξ) (besselWeight_pos d s ξ).le
    _ = (2 * Real.pi * ‖m‖) * (besselWeight d s ξ * ‖ξ‖) * ‖𝓕 f ξ‖ := by ring
    _ ≤ (2 * Real.pi * ‖m‖) * besselWeight d (s + 1) ξ * ‖𝓕 f ξ‖ := by
      gcongr
      exact besselWeight_mul_norm_le d s ξ
    _ = _ := by ring

omit [CompleteSpace F] in
/-- A directional derivative maps H^(s+1) to H^s with its explicit Fourier factor. -/
theorem sobolevNorm_lineDeriv_le (d : ℕ) (s : ℝ) (f : 𝓢(Domain d, F)) (m : Domain d) :
    sobolevNorm d s (∂_{m} f) ≤ (2 * Real.pi * ‖m‖) * sobolevNorm d (s + 1) f := by
  unfold sobolevNorm
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(weightedFourier d s (∂_{m} f)).coeFn_toLp 2,
    (weightedFourier d (s + 1) f).coeFn_toLp 2] with ξ hd hf
  rw [hd, hf]
  exact weightedFourier_lineDeriv_norm_le d s f m ξ

omit [CompleteSpace F] in
/-- Iterating the Fourier multiplier estimate loses exactly one Sobolev order per derivative. -/
theorem sobolevNorm_iteratedLineDeriv_le (d k : ℕ) (s : ℝ)
    (f : 𝓢(Domain d, F)) (m : Fin k → Domain d) :
    sobolevNorm d s (∂^{m} f) ≤
      (2 * Real.pi) ^ k * (∏ i, ‖m i‖) * sobolevNorm d (s + k) f := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left]
    calc
      _ ≤ (2 * Real.pi * ‖m 0‖) * sobolevNorm d (s + 1) (∂^{Fin.tail m} f) :=
        sobolevNorm_lineDeriv_le d s (∂^{Fin.tail m} f) (m 0)
      _ ≤ (2 * Real.pi * ‖m 0‖) *
          ((2 * Real.pi) ^ k * (∏ i, ‖Fin.tail m i‖) *
            sobolevNorm d ((s + 1) + k) f) := by
        gcongr
        exact ih (s + 1) (Fin.tail m)
      _ = _ := by
        rw [Fin.prod_univ_succ, pow_succ]
        have he : (s + 1) + (k : ℝ) = s + (↑(k + 1) : ℝ) := by push_cast; ring
        rw [he]
        simp only [Fin.tail]
        ring

/-- Sobolev embedding controls the operator norm of every actual Fréchet derivative. -/
theorem iteratedFDeriv_norm_le_sobolevNorm (d k : ℕ) (s : ℝ)
    (hs : (d : ℝ) < 2 * s) (f : 𝓢(Domain d, F)) (x : Domain d) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant d s hs * (2 * Real.pi) ^ k * sobolevNorm d (s + k) f := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by
    unfold embeddingConstant sobolevNorm
    positivity)
  intro m
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  calc
    _ ≤ embeddingConstant d s hs * sobolevNorm d s (∂^{m} f) :=
      norm_apply_le_sobolevNorm d s hs (∂^{m} f) x
    _ ≤ embeddingConstant d s hs *
        ((2 * Real.pi) ^ k * (∏ i, ‖m i‖) * sobolevNorm d (s + k) f) :=
      mul_le_mul_of_nonneg_left (sobolevNorm_iteratedLineDeriv_le d k s f m) (norm_nonneg _)
    _ = _ := by ring

/-- Coordinatewise complexification is an actual linear isometry of Euclidean spaces. -/
noncomputable def complexify (q : ℕ) :
    Domain q →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin q) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℂ))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp [Complex.real_smul]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp

/-- Coordinatewise isometric complexification of a real Schwartz vector field. -/
noncomputable def complexifySchwartz (d q : ℕ) (f : 𝓢(Domain d, Domain q)) :
    𝓢(Domain d, EuclideanSpace ℂ (Fin q)) :=
  SchwartzMap.postcompCLM (complexify q).toContinuousLinearMap f

/-- The usual Fourier Hˢ norm of a real vector field, via isometric complexification. -/
noncomputable def realSobolevNorm (d q : ℕ) (s : ℝ) (f : 𝓢(Domain d, Domain q)) : ℝ :=
  sobolevNorm d s (complexifySchwartz d q f)

theorem complexifySchwartz_iteratedFDeriv_norm (d q k : ℕ)
    (f : 𝓢(Domain d, Domain q)) (x : Domain d) :
    ‖iteratedFDeriv ℝ k (complexifySchwartz d q f) x‖ = ‖iteratedFDeriv ℝ k f x‖ := by
  change ‖iteratedFDeriv ℝ k ((complexify q) ∘ f) x‖ = _
  exact (complexify q).norm_iteratedFDeriv_comp_left f.smooth'.contDiffAt (by simp)

/-- Sobolev embedding for genuine real Euclidean vector fields and all derivative orders. -/
theorem real_iteratedFDeriv_norm_le_sobolevNorm (d q k : ℕ) (s : ℝ)
    (hs : (d : ℝ) < 2 * s) (f : 𝓢(Domain d, Domain q)) (x : Domain d) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant d s hs * (2 * Real.pi) ^ k * realSobolevNorm d q (s + k) f := by
  rw [← complexifySchwartz_iteratedFDeriv_norm d q k f x]
  exact iteratedFDeriv_norm_le_sobolevNorm d k s hs (complexifySchwartz d q f) x

/-- On ℝ³, `H^(k+2)` controls every derivative of order `k`. In particular, `H³ → C¹`. -/
theorem real_three_dimensional_sobolev (q k : ℕ)
    (f : 𝓢(Domain 3, Domain q)) (x : Domain 3) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant 3 2 (by norm_num) * (2 * Real.pi) ^ k *
        realSobolevNorm 3 q (2 + k) f :=
  real_iteratedFDeriv_norm_le_sobolevNorm 3 q k 2 (by norm_num) f x

/-- On ℝ⁴, `H^(k+3)` controls every derivative of order `k`. -/
theorem real_four_dimensional_sobolev (q k : ℕ)
    (f : 𝓢(Domain 4, Domain q)) (x : Domain 4) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant 4 3 (by norm_num) * (2 * Real.pi) ^ k *
        realSobolevNorm 4 q (3 + k) f :=
  real_iteratedFDeriv_norm_le_sobolevNorm 4 q k 3 (by norm_num) f x

/-- The same concrete Fourier norm, now for an unbundled smooth compactly supported field. -/
noncomputable def compactSobolevNorm (d q : ℕ) (s : ℝ) (f : Domain d → Domain q)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : ℝ :=
  realSobolevNorm d q s (hc.toSchwartzMap hf)

theorem compact_iteratedFDeriv_norm_le (q k : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      embeddingConstant 3 2 (by norm_num) * (2 * Real.pi) ^ k *
        compactSobolevNorm 3 q (2 + k) f hf hc :=
  real_three_dimensional_sobolev q k (hc.toSchwartzMap hf) x

open Filter EulerSmoothLimit

/--
The all-order Sobolev estimates construct the actual smooth, compactly supported,
finite-energy solenoidal limit. Uniform derivative bounds are derived by Fourier
analysis inside the proof, rather than supplied as an additional hypothesis.
-/
theorem smooth_compact_solenoidal_limit_of_sobolev
    (f : ℕ → Space → Space) (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hc : ∀ n, HasCompactSupport (f n))
    (hSob : ∀ k : ℕ, Summable (fun n =>
      compactSobolevNorm 3 3 (2 + k) (f n) (hf n) (hc n)))
    (K : Set Space) (hK : IsCompact K) (hsupp : ∀ n, Function.support (f n) ⊆ K)
    (hdiv : ∀ n x, divergence (f n) x = 0) :
    ∃ u : Space → Space,
      (∀ x, HasSum (fun n => f n x) (u x)) ∧
      TendstoUniformly (fun N x => ∑ n ∈ Finset.range N, f n x) u atTop ∧
      ContDiff ℝ ∞ u ∧ tsupport u ⊆ K ∧ HasCompactSupport u ∧
      MemLp u 2 volume ∧ Integrable (fun x => ‖u x‖ ^ 2) volume ∧
      (∀ x, divergence u x = 0) ∧
      (∀ k x, iteratedFDeriv ℝ k u x = ∑' n, iteratedFDeriv ℝ k (f n) x) := by
  let v : ℕ → ℕ → ℝ := fun k n =>
    embeddingConstant 3 2 (by norm_num) * (2 * Real.pi) ^ k *
      compactSobolevNorm 3 3 (2 + k) (f n) (hf n) (hc n)
  have hv : ∀ k, Summable (v k) := fun k => (hSob k).mul_left _
  have hb : ∀ k n x, ‖iteratedFDeriv ℝ k (f n) x‖ ≤ v k n :=
    fun k n x => compact_iteratedFDeriv_norm_le 3 k (f n) (hf n) (hc n) x
  exact EulerSmoothLimit.smooth_compact_solenoidal_limit f v hf hv hb K hK hsupp hdiv

end EulerSobolev
