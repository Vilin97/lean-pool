/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisymmetricResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityProfile
public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialFluxResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalAxisymmetricResidual
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Finite slow expansions and their physical residuals

Finite products are expanded exactly. Terms above the retained slow order and
the last axial-viscosity term are displayed as explicit finite remainders.
-/

noncomputable section

namespace NavierStokes.SlowExpansionResidual

open AxisymmetricFields
open SimilarityProfile (InnerProfile InnerPoint pullback partialX T Z)
open scoped BigOperators Topology ContDiff

/-- The manuscript's slow order `λ_n=2nh`. -/
def slowOrder (h : ℝ) (n : ℕ) : ℝ := 2 * (n : ℝ) * h

@[simp] theorem slowOrder_zero (h : ℝ) : slowOrder h 0 = 0 := by simp [slowOrder]
theorem slowOrder_add (h : ℝ) (i j : ℕ) :
    slowOrder h (i + j) = slowOrder h i + slowOrder h j := by
  simp [slowOrder, Nat.cast_add]
  ring
theorem slowOrder_succ (h : ℝ) (n : ℕ) :
    slowOrder h (n + 1) = slowOrder h n + 2 * h := by
  simp [slowOrder, Nat.cast_add]
  ring

def finiteSeries (N : ℕ) (q h b : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), q ^ (b + slowOrder h n) * a n

noncomputable def pairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (N + 1) ×ˢ Finset.range (N + 1)

def convolution (K : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ ij ∈ Finset.antidiagonal n, K ij.1 ij.2

def finiteConvolution (N : ℕ) (K : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ ij ∈ (pairs N).filter (fun ij => ij.1 + ij.2 = n), K ij.1 ij.2

def pairTail (N : ℕ) (w : ℕ → ℝ) (K : ℕ → ℕ → ℝ) : ℝ :=
  ∑ ij ∈ (pairs N).filter (fun ij => N < ij.1 + ij.2), w (ij.1 + ij.2) * K ij.1 ij.2

noncomputable def previous (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a n

@[simp] theorem previous_zero (a : ℕ → ℝ) : previous a 0 = 0 := rfl
@[simp] theorem previous_succ (a : ℕ → ℝ) (n : ℕ) : previous a (n + 1) = a n := rfl

@[simp] theorem finiteSeries_order_zero (q h b : ℝ) (a : ℕ → ℝ) :
    finiteSeries 0 q h b a = q ^ b * a 0 := by simp [finiteSeries]

@[simp] theorem pairTail_order_zero (w : ℕ → ℝ) (K : ℕ → ℕ → ℝ) :
    pairTail 0 w K = 0 := by
  simp [pairTail, pairs, Finset.sum_filter]

theorem finiteConvolution_eq {N n : ℕ} (hn : n ≤ N) (K : ℕ → ℕ → ℝ) :
    finiteConvolution N K n = convolution K n := by
  have hs : (pairs N).filter (fun ij => ij.1 + ij.2 = n) = Finset.antidiagonal n := by
    ext ij
    simp only [Finset.mem_filter, pairs, Finset.mem_product, Finset.mem_range,
      Finset.mem_antidiagonal]
    omega
  unfold finiteConvolution convolution
  rw [hs]

theorem rpow_product_order {q : ℝ} (hq : 0 < q) (h b c : ℝ) (i j : ℕ) :
    q ^ (b + slowOrder h i) * q ^ (c + slowOrder h j) =
      q ^ (b + c + slowOrder h (i + j)) := by
  rw [← Real.rpow_add hq, slowOrder_add]
  congr 1
  ring

/-- Exact Cauchy product of two finite slow expansions. -/
theorem finiteSeries_mul {q : ℝ} (hq : 0 < q) (N : ℕ) (h b c : ℝ) (a d : ℕ → ℝ) :
    finiteSeries N q h b a * finiteSeries N q h c d =
      ∑ ij ∈ pairs N, q ^ (b + c + slowOrder h (ij.1 + ij.2)) * (a ij.1 * d ij.2) := by
  unfold finiteSeries pairs
  rw [Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (q ^ (b + slowOrder h i) * q ^ (c + slowOrder h j)) * (a i * d j) := by ring
    _ = _ := by rw [rpow_product_order hq]

theorem finiteSeries_add (N : ℕ) (q h b : ℝ) (a d : ℕ → ℝ) :
    finiteSeries N q h b (fun n => a n + d n) =
      finiteSeries N q h b a + finiteSeries N q h b d := by
  simp [finiteSeries, mul_add, Finset.sum_add_distrib]

theorem finiteSeries_scale (N : ℕ) (q h b c : ℝ) (a : ℕ → ℝ) :
    finiteSeries N q h b (fun n => c * a n) = c * finiteSeries N q h b a := by
  unfold finiteSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem finiteSeries_mul_q {q : ℝ} (hq : 0 < q) (N : ℕ) (h b : ℝ) (a : ℕ → ℝ) :
    q * finiteSeries N q h b a = finiteSeries N q h (b + 1) a := by
  unfold finiteSeries
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hp : q * q ^ (b + slowOrder h n) = q ^ (b + 1 + slowOrder h n) := by
    conv_lhs => lhs; rw [← Real.rpow_one q]
    rw [← Real.rpow_add hq]
    congr 1
    ring
  rw [← mul_assoc, hp]

theorem finiteSeries_div_qX {q X : ℝ} (hq : 0 < q) (hX : X ≠ 0)
    (N : ℕ) (h b : ℝ) (a : ℕ → ℝ) :
    finiteSeries N q h b a / (q * X) =
      finiteSeries N q h (b - 1) (fun n => a n / X) := by
  unfold finiteSeries
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show b - 1 + slowOrder h n = b + slowOrder h n - 1 by ring,
    Real.rpow_sub_one hq.ne']
  field_simp

theorem radialDiffusion_series {q : ℝ} (hq : 0 < q) (N : ℕ)
    (h b X m : ℝ) (a d : ℕ → ℝ) :
    2 * (q * X) * finiteSeries N q h (b - 2) d +
      2 * m * finiteSeries N q h (b - 1) a =
      finiteSeries N q h (b - 1) (fun n => 2 * (X * d n + m * a n)) := by
  have hp := finiteSeries_mul_q hq N h (b - 2) d
  rw [show b - 2 + 1 = b - 1 by ring] at hp
  calc
    _ = 2 * X * (q * finiteSeries N q h (b - 2) d) +
        2 * m * finiteSeries N q h (b - 1) a := by ring
    _ = 2 * X * finiteSeries N q h (b - 1) d +
        2 * m * finiteSeries N q h (b - 1) a := by rw [hp]
    _ = _ := by
      rw [← finiteSeries_scale, ← finiteSeries_scale, ← finiteSeries_add]
      congr 1
      funext n
      ring

theorem axialViscosity_shift (N : ℕ) (q h b : ℝ) (a : ℕ → ℝ) :
    finiteSeries N q h (b - 2 * CoordinateAlgebra.D h) a =
      ∑ n ∈ Finset.range (N + 1), q ^ (b - 1 + slowOrder h (n + 1)) * a n := by
  unfold finiteSeries
  apply Finset.sum_congr rfl
  intro n hn
  rw [slowOrder_succ]
  congr 2
  unfold CoordinateAlgebra.D
  ring

theorem pair_sum_low (N : ℕ) (w : ℕ → ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), w n * finiteConvolution N K n) =
      ∑ ij ∈ (pairs N).filter (fun ij => ij.1 + ij.2 ≤ N),
        w (ij.1 + ij.2) * K ij.1 ij.2 := by
  unfold finiteConvolution
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ n ∈ Finset.range (N + 1),
        ∑ ij ∈ (pairs N).filter (fun ij => ij.1 + ij.2 = n),
          w (ij.1 + ij.2) * K ij.1 ij.2 := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro ij hij
      rw [(Finset.mem_filter.mp hij).2]
    _ = _ := by
      rw [Finset.sum_fiberwise_eq_sum_filter]
      simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- Low convolution coefficients and the exact omitted pair interactions. -/
theorem pair_sum_split (N : ℕ) (w : ℕ → ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ ij ∈ pairs N, w (ij.1 + ij.2) * K ij.1 ij.2) =
      (∑ n ∈ Finset.range (N + 1), w n * convolution K n) + pairTail N w K := by
  have hlo : (∑ n ∈ Finset.range (N + 1), w n * convolution K n) =
      ∑ n ∈ Finset.range (N + 1), w n * finiteConvolution N K n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteConvolution_eq (by have := Finset.mem_range.mp hn; omega)]
  rw [hlo, pair_sum_low]
  unfold pairTail
  simpa only [not_le] using
    (Finset.sum_filter_add_sum_filter_not (pairs N) (fun ij => ij.1 + ij.2 ≤ N)
      (fun ij => w (ij.1 + ij.2) * K ij.1 ij.2)).symm

/-- An axial derivative raises slow order by one. The last term is retained
here as a literal remainder rather than silently discarded. -/
theorem shifted_sum (N : ℕ) (w a : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), w (n + 1) * a n) =
      (∑ n ∈ Finset.range (N + 1), w n * previous a n) + w (N + 1) * a N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ, previous_succ] at ih ⊢
      linarith

def recurrence (L : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (A : ℕ → ℝ) (n : ℕ) : ℝ :=
  L n + convolution K n - previous A n

/-- Universal finite-order recurrence identity used by the angular, axial,
and radial-flux equations. -/
theorem recurrence_truncation (N : ℕ) (w L A : ℕ → ℝ) (K : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), w n * L n) +
      (∑ ij ∈ pairs N, w (ij.1 + ij.2) * K ij.1 ij.2) -
      (∑ n ∈ Finset.range (N + 1), w (n + 1) * A n) =
    (∑ n ∈ Finset.range (N + 1), w n * recurrence L K A n) +
      pairTail N w K - w (N + 1) * A N := by
  rw [pair_sum_split, shifted_sum]
  simp only [recurrence, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- If the retained coefficient equations hold, the physical finite
expansion still has these explicit omitted interactions and viscosity term. -/
theorem recurrence_truncation_of_zero (N : ℕ) (w L A : ℕ → ℝ) (K : ℕ → ℕ → ℝ)
    (hzero : ∀ n ≤ N, recurrence L K A n = 0) :
    (∑ n ∈ Finset.range (N + 1), w n * L n) +
      (∑ ij ∈ pairs N, w (ij.1 + ij.2) * K ij.1 ij.2) -
      (∑ n ∈ Finset.range (N + 1), w (n + 1) * A n) =
      pairTail N w K - w (N + 1) * A N := by
  rw [recurrence_truncation]
  have hs : (∑ n ∈ Finset.range (N + 1), w n * recurrence L K A n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [hzero n (by have := Finset.mem_range.mp hn; omega), mul_zero]
  rw [hs, zero_add]

def transportLinear (X m : ℝ) (gt gx gxx source : ℕ → ℝ) (n : ℕ) : ℝ :=
  gt n - 2 * (X * gxx n + m * gx n) + source n

def transportPair (X α : ℝ) (v u g gx gz : ℕ → ℝ) (i j : ℕ) : ℝ :=
  v i * (gx j + α * g j / X) + u i * gz j

/-- Scalar transport/diffusion for arbitrary finite jets, with all product
orders and the final shifted viscosity displayed exactly. -/
theorem transport_series_identity {q X : ℝ} (hq : 0 < q) (hX : X ≠ 0)
    (N : ℕ) (h e α m : ℝ) (v u g gt gx gxx gz gzz source : ℕ → ℝ) :
    finiteSeries N q h (e - 1) gt +
      finiteSeries N q h 0 v * (finiteSeries N q h (e - 1) gx +
        α * (finiteSeries N q h e g / (q * X))) +
      finiteSeries N q h (-CoordinateAlgebra.A h) u *
        finiteSeries N q h (e - CoordinateAlgebra.D h) gz -
      (2 * (q * X) * finiteSeries N q h (e - 2) gxx +
        2 * m * finiteSeries N q h (e - 1) gx +
        finiteSeries N q h (e - 2 * CoordinateAlgebra.D h) gzz) +
      finiteSeries N q h (e - 1) source =
    finiteSeries N q h (e - 1)
      (recurrence (transportLinear X m gt gx gxx source) (transportPair X α v u g gx gz) gzz) +
      pairTail N (fun n => q ^ (e - 1 + slowOrder h n)) (transportPair X α v u g gx gz) -
      q ^ (e - 1 + slowOrder h (N + 1)) * gzz N := by
  have hradial : finiteSeries N q h (e - 1) gx +
      α * (finiteSeries N q h e g / (q * X)) =
      finiteSeries N q h (e - 1) (fun n => gx n + α * g n / X) := by
    rw [finiteSeries_div_qX hq hX,
      ← finiteSeries_scale N q h (e - 1) α (fun n => g n / X), ← finiteSeries_add]
    congr 1
    funext n
    ring
  have hv := finiteSeries_mul hq N h 0 (e - 1) v (fun n => gx n + α * g n / X)
  simp only [zero_add] at hv
  have hu := finiteSeries_mul hq N h (-CoordinateAlgebra.A h)
    (e - CoordinateAlgebra.D h) u gz
  rw [show -CoordinateAlgebra.A h + (e - CoordinateAlgebra.D h) = e - 1 by
    unfold CoordinateAlgebra.A CoordinateAlgebra.D; ring] at hu
  rw [hradial, hv, hu, radialDiffusion_series hq, axialViscosity_shift]
  change _ = (∑ n ∈ Finset.range (N + 1),
    q ^ (e - 1 + slowOrder h n) *
      recurrence (transportLinear X m gt gx gxx source) (transportPair X α v u g gx gz) gzz n) + _
        - _
  rw [← recurrence_truncation]
  simp only [finiteSeries, transportLinear, transportPair, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Ordinary directional derivative on physical profile space. -/
def derivativeAlong (v : ProfilePoint) (f : Profile) (p : ProfilePoint) : ℝ :=
  fderiv ℝ f p v

theorem derivativeAlong_sum {ι : Type*} (s : Finset ι) (f : ι → Profile)
    (v p : ProfilePoint) (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) p) :
    derivativeAlong v (fun y => ∑ i ∈ s, f i y) p =
      ∑ i ∈ s, derivativeAlong v (f i) p := by
  unfold derivativeAlong
  rw [fderiv_fun_sum hf, _root_.sum_apply]

/-- Finite sums commute with actual second derivatives under C² regularity. -/
theorem secondAlong_sum {ι : Type*} (s : Finset ι) (f : ι → Profile)
    (v w p : ProfilePoint) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) p) :
    derivativeAlong w (derivativeAlong v (fun y => ∑ i ∈ s, f i y)) p =
      ∑ i ∈ s, derivativeAlong w (derivativeAlong v (f i)) p := by
  have hev : ∀ᶠ y in nhds p, ∀ i ∈ s, DifferentiableAt ℝ (f i) y := by
    rw [Finset.eventually_all]
    intro i hi
    exact ((hf i hi).eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have he : derivativeAlong v (fun y => ∑ i ∈ s, f i y) =ᶠ[nhds p]
      (fun y => ∑ i ∈ s, derivativeAlong v (f i) y) := by
    filter_upwards [hev] with y hy
    exact derivativeAlong_sum s f v y hy
  change fderiv ℝ _ p w = _
  rw [he.fderiv_eq]
  exact derivativeAlong_sum s (fun i => derivativeAlong v (f i)) w p
    (fun i hi => (((hf i hi).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num))

def finiteProfile (N : ℕ) (h b : ℝ) (f : ℕ → InnerProfile) : Profile :=
  fun p => ∑ n ∈ Finset.range (N + 1), pullback h (b + slowOrder h n) (f n) p

@[simp] theorem finiteProfile_order_zero (h b : ℝ) (f : ℕ → InnerProfile) :
    finiteProfile 0 h b f = pullback h b (f 0) := by
  funext p
  simp [finiteProfile]

theorem finiteProfile_value (N : ℕ) (h b : ℝ) (f : ℕ → InnerProfile) (p : ProfilePoint) :
    finiteProfile N h b f p = finiteSeries N (SimilarityProfile.q h p) h b
      (fun n => f n (SimilarityProfile.inner h p)) := rfl

theorem partialT_finiteProfile {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : ℕ → InnerProfile) {p : ProfilePoint} (hp : p.1 < 1)
    (hf : ∀ n ≤ N, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    AxisymmetricResidual.partialT (finiteProfile N h b f) p =
      finiteProfile N h (b - 1) (fun n => T h (b + slowOrder h n) (f n)) p := by
  unfold finiteProfile
  change derivativeAlong (1, (0, 0)) _ p = _
  rw [derivativeAlong_sum _ _ _ _ (fun n hn => SimilarityProfile.pullback_differentiableAt
    hh hh1 hp (hf n (by have := Finset.mem_range.mp hn; omega)))]
  apply Finset.sum_congr rfl
  intro n hn
  change SimilarityProfile.partialT _ p = _
  rw [SimilarityProfile.partialT_pullback hh hh1 hp
    (hf n (by have := Finset.mem_range.mp hn; omega))]
  rw [show b + slowOrder h n - 1 = b - 1 + slowOrder h n by ring]

theorem partialS_finiteProfile {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : ℕ → InnerProfile) {p : ProfilePoint} (hp : p.1 < 1)
    (hf : ∀ n ≤ N, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    partialS (finiteProfile N h b f) p =
      finiteProfile N h (b - 1) (fun n => partialX (f n)) p := by
  unfold finiteProfile
  change derivativeAlong (0, (1, 0)) _ p = _
  rw [derivativeAlong_sum _ _ _ _ (fun n hn => SimilarityProfile.pullback_differentiableAt
    hh hh1 hp (hf n (by have := Finset.mem_range.mp hn; omega)))]
  apply Finset.sum_congr rfl
  intro n hn
  change SimilarityProfile.partialS _ p = _
  rw [SimilarityProfile.partialS_pullback hh hh1 hp
    (hf n (by have := Finset.mem_range.mp hn; omega))]
  rw [show b + slowOrder h n - 1 = b - 1 + slowOrder h n by ring]

theorem partialZ_finiteProfile {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : ℕ → InnerProfile) {p : ProfilePoint} (hp : p.1 < 1)
    (hf : ∀ n ≤ N, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    partialZ (finiteProfile N h b f) p =
      finiteProfile N h (b - CoordinateAlgebra.D h)
        (fun n => Z h (b + slowOrder h n) (f n)) p := by
  unfold finiteProfile
  change derivativeAlong (0, (0, 1)) _ p = _
  rw [derivativeAlong_sum _ _ _ _ (fun n hn => SimilarityProfile.pullback_differentiableAt
    hh hh1 hp (hf n (by have := Finset.mem_range.mp hn; omega)))]
  apply Finset.sum_congr rfl
  intro n hn
  change SimilarityProfile.partialZ _ p = _
  rw [SimilarityProfile.partialZ_pullback hh hh1 hp
    (hf n (by have := Finset.mem_range.mp hn; omega))]
  rw [show b + slowOrder h n - CoordinateAlgebra.D h =
    b - CoordinateAlgebra.D h + slowOrder h n by ring]

def Z2 (h b : ℝ) (f : InnerProfile) : InnerProfile :=
  Z h (b - CoordinateAlgebra.D h) (Z h b f)

theorem partialSS_finiteProfile {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : ℕ → InnerProfile) {p : ProfilePoint} (hp : p.1 < 1)
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f n) (SimilarityProfile.inner h p)) :
    partialS (partialS (finiteProfile N h b f)) p =
      finiteProfile N h (b - 2) (fun n => partialX (partialX (f n))) p := by
  unfold finiteProfile
  change derivativeAlong (0, (1, 0)) (derivativeAlong (0, (1, 0)) _) p = _
  rw [secondAlong_sum _ _ _ _ _ (fun n hn => SimilarityProfile.pullback_smoothAt
    hh hh1 hp (hf n (by have := Finset.mem_range.mp hn; omega)))]
  apply Finset.sum_congr rfl
  intro n hn
  change SimilarityProfile.partialS (SimilarityProfile.partialS _) p = _
  rw [SimilarityProfile.partialS_partialS_pullback hh hh1 hp
    (hf n (by have := Finset.mem_range.mp hn; omega))]
  rw [show b + slowOrder h n - 2 = b - 2 + slowOrder h n by ring]

theorem partialZZ_finiteProfile {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : ℕ → InnerProfile) {p : ProfilePoint} (hp : p.1 < 1)
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f n) (SimilarityProfile.inner h p)) :
    partialZ (partialZ (finiteProfile N h b f)) p =
      finiteProfile N h (b - 2 * CoordinateAlgebra.D h)
        (fun n => Z2 h (b + slowOrder h n) (f n)) p := by
  unfold finiteProfile
  change derivativeAlong (0, (0, 1)) (derivativeAlong (0, (0, 1)) _) p = _
  rw [secondAlong_sum _ _ _ _ _ (fun n hn => SimilarityProfile.pullback_smoothAt
    hh hh1 hp (hf n (by have := Finset.mem_range.mp hn; omega)))]
  apply Finset.sum_congr rfl
  intro n hn
  change SimilarityProfile.partialZ (SimilarityProfile.partialZ _) p = _
  rw [SimilarityProfile.partialZ_partialZ_pullback hh hh1 hp
    (hf n (by have := Finset.mem_range.mp hn; omega))]
  rw [show b + slowOrder h n - 2 * CoordinateAlgebra.D h =
    b - 2 * CoordinateAlgebra.D h + slowOrder h n by ring]
  rfl

def transportResidual (α m : ℝ) (V U G source : Profile) (p : ProfilePoint) : ℝ :=
  AxisymmetricResidual.partialT G p + V p * (partialS G p + α * (G p / p.2.1)) +
    U p * partialZ G p -
    (2 * p.2.1 * partialS (partialS G) p + 2 * m * partialS G p + partialZ (partialZ G) p) +
    source p

def transportCoefficient (h e α m : ℝ) (v u f source : ℕ → InnerProfile)
    (n : ℕ) (w : InnerPoint) : ℝ :=
  recurrence
    (transportLinear w.1 m (fun j => T h (e + slowOrder h j) (f j) w)
      (fun j => partialX (f j) w) (fun j => partialX (partialX (f j)) w) (fun j => source j w))
    (transportPair w.1 α (fun j => v j w) (fun j => u j w) (fun j => f j w)
      (fun j => partialX (f j) w) (fun j => Z h (e + slowOrder h j) (f j) w))
    (fun j => Z2 h (e + slowOrder h j) (f j) w) n

def transportTail (N : ℕ) (q h e α : ℝ) (v u f : ℕ → InnerProfile) (w : InnerPoint) : ℝ :=
  pairTail N (fun n => q ^ (e - 1 + slowOrder h n))
    (transportPair w.1 α (fun j => v j w) (fun j => u j w) (fun j => f j w)
      (fun j => partialX (f j) w) (fun j => Z h (e + slowOrder h j) (f j) w)) -
    q ^ (e - 1 + slowOrder h (N + 1)) * Z2 h (e + slowOrder h N) (f N) w

@[simp] theorem transportTail_order_zero (q h e α : ℝ)
    (v u f : ℕ → InnerProfile) (w : InnerPoint) :
    transportTail 0 q h e α v u f w =
      -q ^ (e - 1 + 2 * h) * Z2 h e (f 0) w := by
  simp [transportTail, slowOrder_succ]

theorem q_mul_X {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : ProfilePoint} (hp : p.1 < 1) :
    SimilarityProfile.q h p * (SimilarityProfile.inner h p).1 = p.2.1 := by
  simp only [SimilarityProfile.inner, SimilarityProfile.X]
  field_simp [(SimilarityProfile.q_pos hh hh1 hp).ne']

/-- The finite transport recurrence is obtained from genuine derivatives of
the reconstructed profiles, rather than from formal coefficient placeholders. -/
theorem transport_finiteProfile {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (α m : ℝ) (v u f source : ℕ → InnerProfile) {p : ProfilePoint}
    (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f n) (SimilarityProfile.inner h p)) :
    transportResidual α m (finiteProfile N h 0 v)
      (finiteProfile N h (-CoordinateAlgebra.A h) u) (finiteProfile N h e f)
      (finiteProfile N h (e - 1) source) p =
    finiteSeries N (SimilarityProfile.q h p) h (e - 1)
      (fun n => transportCoefficient h e α m v u f source n (SimilarityProfile.inner h p)) +
    transportTail N (SimilarityProfile.q h p) h e α v u f (SimilarityProfile.inner h p) := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  have hX : (SimilarityProfile.inner h p).1 ≠ 0 := by
    change p.2.1 / SimilarityProfile.q h p ≠ 0
    exact div_ne_zero hs.ne' hq.ne'
  have hd : ∀ n ≤ N, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p) :=
    fun n hn => (hf n hn).differentiableAt (by norm_num)
  unfold transportResidual
  rw [partialT_finiteProfile hh hh1 N f hp hd, partialS_finiteProfile hh hh1 N f hp hd,
    partialZ_finiteProfile hh hh1 N f hp hd, partialSS_finiteProfile hh hh1 N f hp hf,
    partialZZ_finiteProfile hh hh1 N f hp hf]
  simp_rw [finiteProfile_value]
  rw [← q_mul_X hh hh1 hp]
  have hcalc := transport_series_identity hq hX N h e α m
    (fun n => v n (SimilarityProfile.inner h p)) (fun n => u n (SimilarityProfile.inner h p))
    (fun n => f n (SimilarityProfile.inner h p))
    (fun n => T h (e + slowOrder h n) (f n) (SimilarityProfile.inner h p))
    (fun n => partialX (f n) (SimilarityProfile.inner h p))
    (fun n => partialX (partialX (f n)) (SimilarityProfile.inner h p))
    (fun n => Z h (e + slowOrder h n) (f n) (SimilarityProfile.inner h p))
    (fun n => Z2 h (e + slowOrder h n) (f n) (SimilarityProfile.inner h p))
    (fun n => source n (SimilarityProfile.inner h p))
  simpa only [transportCoefficient, transportTail, add_sub_assoc] using hcalc

theorem finiteProfile_smoothAt {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : ℕ → InnerProfile) {p : ProfilePoint} (hp : p.1 < 1)
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f n) (SimilarityProfile.inner h p)) :
    ContDiffAt ℝ 2 (finiteProfile N h e f) p := by
  apply ContDiffAt.sum
  intro n hn
  exact SimilarityProfile.pullback_smoothAt hh hh1 hp
    (hf n (by have := Finset.mem_range.mp hn; omega))

theorem finiteProfile_differentiableAt {h e : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : ℕ → InnerProfile) {p : ProfilePoint} (hp : p.1 < 1)
    (hf : ∀ n ≤ N, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    DifferentiableAt ℝ (finiteProfile N h e f) p := by
  apply DifferentiableAt.fun_sum
  intro n hn
  exact SimilarityProfile.pullback_differentiableAt hh hh1 hp
    (hf n (by have := Finset.mem_range.mp hn; omega))

theorem derivativeAlong_scale (c : ℝ) {f : Profile} {p : ProfilePoint}
    (hf : DifferentiableAt ℝ f p) (v : ProfilePoint) :
    derivativeAlong v (fun y => c * f y) p = c * derivativeAlong v f p := by
  unfold derivativeAlong
  rw [fderiv_const_mul hf]
  rfl

theorem secondAlong_scale (c : ℝ) {f : Profile} {p : ProfilePoint}
    (hf : ContDiffAt ℝ 2 f p) (v w : ProfilePoint) :
    derivativeAlong w (derivativeAlong v (fun y => c * f y)) p =
      c * derivativeAlong w (derivativeAlong v f) p := by
  have he : derivativeAlong v (fun y => c * f y) =ᶠ[nhds p]
      (fun y => c * derivativeAlong v f y) := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact derivativeAlong_scale c (hy.differentiableAt (by norm_num)) v
  change fderiv ℝ _ p w = _
  rw [he.fderiv_eq]
  exact derivativeAlong_scale c
    (((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by
      norm_num)) w

theorem transportResidual_scale (c α m : ℝ) (V U : Profile) {G : Profile} {p : ProfilePoint}
    (hG : ContDiffAt ℝ 2 G p) :
    transportResidual α m V U (fun y => c * G y) (fun _ => 0) p =
      c * transportResidual α m V U G (fun _ => 0) p := by
  have hd := hG.differentiableAt (by norm_num)
  unfold transportResidual
  change derivativeAlong (1, (0, 0)) _ p + V p *
    (derivativeAlong (0, (1, 0)) _ p + α * (c * G p / p.2.1)) +
    U p * derivativeAlong (0, (0, 1)) _ p -
    (2 * p.2.1 * derivativeAlong (0, (1, 0)) (derivativeAlong (0, (1, 0)) _) p +
      2 * m * derivativeAlong (0, (1, 0)) _ p +
      derivativeAlong (0, (0, 1)) (derivativeAlong (0, (0, 1)) _) p) + 0 = _
  rw [derivativeAlong_scale c hd, derivativeAlong_scale c hd, derivativeAlong_scale c hd,
    secondAlong_scale c hG, secondAlong_scale c hG]
  change _ = c * (derivativeAlong (1, (0, 0)) G p + V p *
    (derivativeAlong (0, (1, 0)) G p + α * (G p / p.2.1)) +
    U p * derivativeAlong (0, (0, 1)) G p -
    (2 * p.2.1 * derivativeAlong (0, (1, 0)) (derivativeAlong (0, (1, 0)) G) p +
      2 * m * derivativeAlong (0, (1, 0)) G p +
      derivativeAlong (0, (0, 1)) (derivativeAlong (0, (0, 1)) G) p) + 0)
  ring

def angularExponent (h : ℝ) : ℝ := -CoordinateAlgebra.A h - 1 / 2
def axialExponent (h : ℝ) : ℝ := -CoordinateAlgebra.A h
def pressureExponent (h : ℝ) : ℝ := -2 * CoordinateAlgebra.A h

structure SlowProfiles where
  phi : ℕ → InnerProfile
  axial : ℕ → InnerProfile
  flux : ℕ → InnerProfile
  pressure : ℕ → InnerProfile

def slowFlux (N : ℕ) (h : ℝ) (f : SlowProfiles) : Profile := finiteProfile N h 0 f.flux
def slowSwirl (N : ℕ) (h C : ℝ) (f : SlowProfiles) : Profile :=
  fun p => C⁻¹ * finiteProfile N h (angularExponent h) f.phi p
def slowAxial (N : ℕ) (h : ℝ) (f : SlowProfiles) : Profile :=
  finiteProfile N h (axialExponent h) f.axial
def slowPressure (N : ℕ) (h : ℝ) (f : SlowProfiles) : Profile :=
  finiteProfile N h (pressureExponent h) f.pressure

def axialPressureSource (h : ℝ) (f : SlowProfiles) (n : ℕ) : InnerProfile :=
  Z h (pressureExponent h + slowOrder h n) (f.pressure n)

def angularCoefficient (h : ℝ) (f : SlowProfiles) (n : ℕ) : InnerProfile :=
  transportCoefficient h (angularExponent h) 1 2 f.flux f.axial f.phi (fun _ _ => 0) n
def axialCoefficient (h : ℝ) (f : SlowProfiles) (n : ℕ) : InnerProfile :=
  transportCoefficient h (axialExponent h) 0 1 f.flux f.axial f.axial (axialPressureSource h f) n
def omegaCoefficient (h : ℝ) (f : SlowProfiles) (n : ℕ) : InnerProfile :=
  transportCoefficient h 0 (-(1 / 2)) 0 f.flux f.axial f.flux (fun _ _ => 0) n
def divergenceCoefficient (h : ℝ) (f : SlowProfiles) (n : ℕ) (w : InnerPoint) : ℝ :=
  partialX (f.flux n) w + Z h (axialExponent h + slowOrder h n) (f.axial n) w
def pressureCoefficient (h C : ℝ) (f : SlowProfiles) (n : ℕ) (w : InnerPoint) : ℝ :=
  partialX (f.pressure n) w - C⁻¹ ^ 2 * convolution (fun i j => f.phi i w * f.phi j w) n +
    previous (fun j => omegaCoefficient h f j w) n / (2 * w.1)

@[simp] theorem finiteProfile_zero (N : ℕ) (h b : ℝ) :
    finiteProfile N h b (fun _ _ => 0) = fun _ => 0 := by
  funext p
  simp [finiteProfile, SimilarityProfile.pullback]

/-- The physical angular equation for the finite swirl expansion. -/
theorem angular_finite_expansion {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) {p : ProfilePoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f.phi n) (SimilarityProfile.inner h p)) :
    transportResidual 1 2 (slowFlux N h f) (slowAxial N h f) (slowSwirl N h C f) (fun _ => 0) p =
      C⁻¹ * (finiteSeries N (SimilarityProfile.q h p) h (angularExponent h - 1)
        (fun n => angularCoefficient h f n (SimilarityProfile.inner h p)) +
        transportTail N (SimilarityProfile.q h p) h (angularExponent h) 1
          f.flux f.axial f.phi (SimilarityProfile.inner h p)) := by
  unfold slowSwirl
  rw [transportResidual_scale C⁻¹ 1 2 _ _ (finiteProfile_smoothAt hh hh1 N f.phi hp hf)]
  have he := transport_finiteProfile (e := angularExponent h) hh hh1 N 1 2
    f.flux f.axial f.phi (fun _ _ => 0) hp hs hf
  simpa only [finiteProfile_zero, slowFlux, slowAxial, axialExponent, angularCoefficient] using
    congrArg (fun z => C⁻¹ * z) he

/-- The axial equation includes the complete axial pressure derivative. -/
theorem axial_finite_expansion {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : SlowProfiles) {p : ProfilePoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f.axial n) (SimilarityProfile.inner h p))
    (hπ : ∀ n ≤ N, DifferentiableAt ℝ (f.pressure n) (SimilarityProfile.inner h p)) :
    transportResidual 0 1 (slowFlux N h f) (slowAxial N h f) (slowAxial N h f)
      (partialZ (slowPressure N h f)) p =
    finiteSeries N (SimilarityProfile.q h p) h (axialExponent h - 1)
      (fun n => axialCoefficient h f n (SimilarityProfile.inner h p)) +
      transportTail N (SimilarityProfile.q h p) h (axialExponent h) 0
        f.flux f.axial f.axial (SimilarityProfile.inner h p) := by
  have hpz := partialZ_finiteProfile (b := pressureExponent h) hh hh1 N f.pressure hp hπ
  rw [show pressureExponent h - CoordinateAlgebra.D h = axialExponent h - 1 by
    unfold pressureExponent axialExponent CoordinateAlgebra.A CoordinateAlgebra.D; ring] at hpz
  have he := transport_finiteProfile (e := axialExponent h) hh hh1 N 0 1
    f.flux f.axial f.axial (axialPressureSource h f) hp hs hf
  change _ = _ at he
  have hpz' : partialZ (slowPressure N h f) p =
      finiteProfile N h (axialExponent h - 1) (axialPressureSource h f) p := hpz
  unfold transportResidual
  rw [hpz']
  exact he

/-- The radial acceleration flux `Ω`, before centrifugal and pressure terms. -/
theorem omega_finite_expansion {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : SlowProfiles) {p : ProfilePoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f.flux n) (SimilarityProfile.inner h p)) :
    transportResidual (-(1 / 2)) 0 (slowFlux N h f) (slowAxial N h f) (slowFlux N h f)
      (fun _ => 0) p =
    finiteSeries N (SimilarityProfile.q h p) h (-1)
      (fun n => omegaCoefficient h f n (SimilarityProfile.inner h p)) +
      transportTail N (SimilarityProfile.q h p) h 0 (-(1 / 2))
        f.flux f.axial f.flux (SimilarityProfile.inner h p) := by
  simpa only [finiteProfile_zero, zero_sub, slowFlux, slowAxial, axialExponent,
    omegaCoefficient] using transport_finiteProfile (e := 0) hh hh1 N (-(1 / 2)) 0
      f.flux f.axial f.flux (fun _ _ => 0) hp hs hf

/-- Equation (21) is the exact divergence coefficient at every retained order. -/
theorem divergence_finite_expansion {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (f : SlowProfiles) {p : ProfilePoint} (hp : p.1 < 1)
    (hv : ∀ n ≤ N, DifferentiableAt ℝ (f.flux n) (SimilarityProfile.inner h p))
    (hu : ∀ n ≤ N, DifferentiableAt ℝ (f.axial n) (SimilarityProfile.inner h p)) :
    partialS (slowFlux N h f) p + partialZ (slowAxial N h f) p =
      finiteSeries N (SimilarityProfile.q h p) h (-1)
        (fun n => divergenceCoefficient h f n (SimilarityProfile.inner h p)) := by
  unfold slowFlux slowAxial
  rw [partialS_finiteProfile hh hh1 N f.flux hp hv,
    partialZ_finiteProfile hh hh1 N f.axial hp hu]
  rw [show axialExponent h - CoordinateAlgebra.D h = -1 by
    unfold axialExponent CoordinateAlgebra.A CoordinateAlgebra.D; ring]
  simp only [zero_sub, finiteProfile_value, divergenceCoefficient]
  exact (finiteSeries_add _ _ _ _ _ _).symm

theorem pressure_series_identity {q X : ℝ} (hq : 0 < q) (hX : X ≠ 0)
    (N : ℕ) (h C tail : ℝ) (phi px omega : ℕ → ℝ) :
    finiteSeries N q h (-1) omega + tail +
      2 * (q * X) * (finiteSeries N q h (pressureExponent h - 1) px -
        (C⁻¹ * finiteSeries N q h (angularExponent h) phi) ^ 2) =
    2 * X * finiteSeries N q h (pressureExponent h)
      (fun n => px n - C⁻¹ ^ 2 * convolution (fun i j => phi i * phi j) n +
        previous omega n / (2 * X)) +
      (tail + q ^ (pressureExponent h + slowOrder h (N + 1)) * omega N -
        2 * X * C⁻¹ ^ 2 * pairTail N (fun n => q ^ (pressureExponent h + slowOrder h n))
          (fun i j => phi i * phi j)) := by
  let conv := convolution (fun i j => phi i * phi j)
  let ptail := pairTail N (fun n => q ^ (pressureExponent h + slowOrder h n))
    (fun i j => phi i * phi j)
  have hs : finiteSeries N q h (-1) omega =
      finiteSeries N q h (pressureExponent h) (previous omega) +
        q ^ (pressureExponent h + slowOrder h (N + 1)) * omega N := by
    have he : finiteSeries N q h (-1) omega =
        ∑ n ∈ Finset.range (N + 1), q ^ (pressureExponent h + slowOrder h (n + 1)) * omega n := by
      unfold finiteSeries
      apply Finset.sum_congr rfl
      intro n hn
      rw [slowOrder_succ]
      congr 2
      unfold pressureExponent CoordinateAlgebra.A
      ring
    rw [he]
    exact shifted_sum N (fun n => q ^ (pressureExponent h + slowOrder h n)) omega
  have hp := finiteSeries_mul_q hq N h (pressureExponent h - 1) px
  rw [show pressureExponent h - 1 + 1 = pressureExponent h by ring] at hp
  have hphi : q * (finiteSeries N q h (angularExponent h) phi) ^ 2 =
      finiteSeries N q h (pressureExponent h) conv + ptail := by
    rw [pow_two, finiteSeries_mul hq, Finset.mul_sum]
    have he : (∑ ij ∈ pairs N,
        q * (q ^ (angularExponent h + angularExponent h + slowOrder h (ij.1 + ij.2)) *
          (phi ij.1 * phi ij.2))) =
        ∑ ij ∈ pairs N, q ^ (pressureExponent h + slowOrder h (ij.1 + ij.2)) *
          (phi ij.1 * phi ij.2) := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [← mul_assoc]
      congr 1
      conv_lhs => lhs; rw [← Real.rpow_one q]
      rw [← Real.rpow_add hq]
      congr 1
      unfold angularExponent pressureExponent
      ring
    rw [he]
    exact pair_sum_split N (fun n => q ^ (pressureExponent h + slowOrder h n))
      (fun i j => phi i * phi j)
  have hphysical : 2 * (q * X) * (finiteSeries N q h (pressureExponent h - 1) px -
      (C⁻¹ * finiteSeries N q h (angularExponent h) phi) ^ 2) =
      2 * X * finiteSeries N q h (pressureExponent h) px -
        2 * X * C⁻¹ ^ 2 * (finiteSeries N q h (pressureExponent h) conv + ptail) := by
    calc
      _ = 2 * X * (q * finiteSeries N q h (pressureExponent h - 1) px) -
          2 * X * C⁻¹ ^ 2 * (q * (finiteSeries N q h (angularExponent h) phi) ^ 2) := by ring
      _ = _ := by rw [hp, hphi]
  have hnormal : 2 * X * finiteSeries N q h (pressureExponent h)
      (fun n => px n - C⁻¹ ^ 2 * conv n + previous omega n / (2 * X)) =
      2 * X * finiteSeries N q h (pressureExponent h) px -
      2 * X * C⁻¹ ^ 2 * finiteSeries N q h (pressureExponent h) conv +
      finiteSeries N q h (pressureExponent h) (previous omega) := by
    have he : (fun n => px n - C⁻¹ ^ 2 * conv n + previous omega n / (2 * X)) =
        (fun n => (1 : ℝ) * px n + (-C⁻¹ ^ 2) * conv n + (2 * X)⁻¹ * previous omega n) := by
      funext n
      ring
    rw [he, finiteSeries_add, finiteSeries_add, finiteSeries_scale, finiteSeries_scale,
      finiteSeries_scale]
    field_simp ; ring
  change _ = 2 * X * finiteSeries N q h (pressureExponent h)
      (fun n => px n - C⁻¹ ^ 2 * conv n + previous omega n / (2 * X)) +
      (tail + q ^ (pressureExponent h + slowOrder h (N + 1)) * omega N - 2 * X * C⁻¹ ^ 2 * ptail)
  rw [hs, hphysical, hnormal]
  ring

def pressureTail (N : ℕ) (q h C : ℝ) (f : SlowProfiles) (w : InnerPoint) : ℝ :=
  transportTail N q h 0 (-(1 / 2)) f.flux f.axial f.flux w +
    q ^ (pressureExponent h + slowOrder h (N + 1)) * omegaCoefficient h f N w -
    2 * w.1 * C⁻¹ ^ 2 * pairTail N (fun n => q ^ (pressureExponent h + slowOrder h n))
      (fun i j => f.phi i w * f.phi j w)

/-- The pressure row of (22), including the shifted radial acceleration and
the exact finite pressure remainder. -/
theorem pressure_finite_expansion {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) {p : ProfilePoint} (hp : p.1 < 1) (hs : 0 < p.2.1)
    (hv : ∀ n ≤ N, ContDiffAt ℝ 2 (f.flux n) (SimilarityProfile.inner h p))
    (hπ : ∀ n ≤ N, DifferentiableAt ℝ (f.pressure n) (SimilarityProfile.inner h p)) :
    RadialFluxResidual.fluxResidual (slowFlux N h f) (slowSwirl N h C f)
      (slowAxial N h f) (slowPressure N h f) p =
    2 * (SimilarityProfile.inner h p).1 *
      finiteSeries N (SimilarityProfile.q h p) h (pressureExponent h)
        (fun n => pressureCoefficient h C f n (SimilarityProfile.inner h p)) +
      pressureTail N (SimilarityProfile.q h p) h C f (SimilarityProfile.inner h p) := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  have hX : (SimilarityProfile.inner h p).1 ≠ 0 := by
    change p.2.1 / SimilarityProfile.q h p ≠ 0
    exact div_ne_zero hs.ne' hq.ne'
  have hflux : RadialFluxResidual.fluxResidual (slowFlux N h f) (slowSwirl N h C f)
      (slowAxial N h f) (slowPressure N h f) p =
      transportResidual (-(1 / 2)) 0 (slowFlux N h f) (slowAxial N h f) (slowFlux N h f)
        (fun _ => 0) p + 2 * p.2.1 *
        (partialS (slowPressure N h f) p - (slowSwirl N h C f p) ^ 2) := by
    unfold RadialFluxResidual.fluxResidual transportResidual
    ring
  rw [hflux, omega_finite_expansion hh hh1 N f hp hs hv]
  have hpS := partialS_finiteProfile (b := pressureExponent h) hh hh1 N f.pressure hp hπ
  change partialS (slowPressure N h f) p = _ at hpS
  rw [hpS]
  unfold slowSwirl
  simp_rw [finiteProfile_value]
  rw [← q_mul_X hh hh1 hp]
  exact pressure_series_identity hq hX N h C
    (transportTail N (SimilarityProfile.q h p) h 0 (-(1 / 2)) f.flux f.axial f.flux
      (SimilarityProfile.inner h p))
    (fun n => f.phi n (SimilarityProfile.inner h p))
    (fun n => partialX (f.pressure n) (SimilarityProfile.inner h p))
    (fun n => omegaCoefficient h f n (SimilarityProfile.inner h p))

/-- The first differential equation in (21), with the actual inner derivative. -/
theorem divergenceCoefficient_eq_zero_iff (h : ℝ) (f : SlowProfiles)
    (n : ℕ) (w : InnerPoint) :
    divergenceCoefficient h f n w = 0 ↔
      partialX (f.flux n) w =
        -Z h (axialExponent h + slowOrder h n) (f.axial n) w := by
  unfold divergenceCoefficient
  constructor <;> intro he <;> linarith

/-- The angular row of (22). `previous` makes the missing order `-1` equal zero. -/
theorem angularCoefficient_eq_zero_iff (h : ℝ) (f : SlowProfiles)
    (n : ℕ) (w : InnerPoint) :
    angularCoefficient h f n w = 0 ↔
      2 * (w.1 * partialX (partialX (f.phi n)) w + 2 * partialX (f.phi n) w) =
        T h (angularExponent h + slowOrder h n) (f.phi n) w +
          convolution (fun i j => f.flux i w *
              (partialX (f.phi j) w + f.phi j w / w.1) +
            f.axial i w * Z h (angularExponent h + slowOrder h j) (f.phi j) w) n -
          previous (fun j => Z2 h (angularExponent h + slowOrder h j) (f.phi j) w) n := by
  unfold angularCoefficient transportCoefficient recurrence transportLinear transportPair
  simp only [one_mul, add_zero]
  constructor <;> intro he <;> linarith

/-- The axial row of (22), including the pressure derivative and viscosity shift. -/
theorem axialCoefficient_eq_zero_iff (h : ℝ) (f : SlowProfiles)
    (n : ℕ) (w : InnerPoint) :
    axialCoefficient h f n w = 0 ↔
      2 * (w.1 * partialX (partialX (f.axial n)) w + partialX (f.axial n) w) =
        T h (axialExponent h + slowOrder h n) (f.axial n) w +
          convolution (fun i j => f.flux i w * partialX (f.axial j) w +
            f.axial i w * Z h (axialExponent h + slowOrder h j) (f.axial j) w) n +
          Z h (pressureExponent h + slowOrder h n) (f.pressure n) w -
          previous (fun j => Z2 h (axialExponent h + slowOrder h j) (f.axial j) w) n := by
  unfold axialCoefficient transportCoefficient recurrence transportLinear transportPair
    axialPressureSource
  simp only [zero_mul, zero_div, add_zero, one_mul]
  constructor <;> intro he <;> linarith

/-- The radial acceleration coefficient appearing in the pressure row of (22). -/
theorem omegaCoefficient_eq (h : ℝ) (f : SlowProfiles) (n : ℕ) (w : InnerPoint) :
    omegaCoefficient h f n w =
      T h (slowOrder h n) (f.flux n) w +
        convolution (fun i j => f.flux i w *
            (partialX (f.flux j) w - f.flux j w / (2 * w.1)) +
          f.axial i w * Z h (slowOrder h j) (f.flux j) w) n -
        2 * w.1 * partialX (partialX (f.flux n)) w -
        previous (fun j => Z2 h (slowOrder h j) (f.flux j) w) n := by
  unfold omegaCoefficient transportCoefficient recurrence transportLinear transportPair
  simp only [zero_add, zero_mul, add_zero]
  have hk : (fun i j => f.flux i w *
      (partialX (f.flux j) w + -(1 / 2 : ℝ) * f.flux j w / w.1) +
      f.axial i w * Z h (slowOrder h j) (f.flux j) w) =
      (fun i j => f.flux i w *
        (partialX (f.flux j) w - f.flux j w / (2 * w.1)) +
        f.axial i w * Z h (slowOrder h j) (f.flux j) w) := by
    funext i j
    ring
  rw [hk]
  ring

/-- The pressure row of (22), including the preceding radial acceleration. -/
theorem pressureCoefficient_eq_zero_iff (h C : ℝ) (f : SlowProfiles)
    (n : ℕ) (w : InnerPoint) :
    pressureCoefficient h C f n w = 0 ↔
      partialX (f.pressure n) w =
        C⁻¹ ^ 2 * convolution (fun i j => f.phi i w * f.phi j w) n -
          previous (fun j => omegaCoefficient h f j w) n / (2 * w.1) := by
  unfold pressureCoefficient
  constructor <;> intro he <;> linarith

/-- The angular coefficient in Cartesian coordinates has the opposite sign
because it multiplies `(y,-x,0)` in the residual formula. -/
theorem residualAngular_radialB (V F U : Profile) {p : ProfilePoint} (hs : p.2.1 ≠ 0) :
    AxisymmetricResidual.residualAngular (RadialFluxResidual.radialB V) F U p =
      -transportResidual 1 2 V U F (fun _ => 0) p := by
  unfold AxisymmetricResidual.residualAngular AxisymmetricResidual.advectionAngular
    AxisymmetricResidual.laplaceWeighted RadialFluxResidual.radialB transportResidual
  field_simp [hs] ; ring

theorem residualAxial_radialB (V U P : Profile) {p : ProfilePoint} (hs : p.2.1 ≠ 0) :
    AxisymmetricResidual.residualAxial (RadialFluxResidual.radialB V) U P p =
      transportResidual 0 1 V U U (partialZ P) p := by
  unfold AxisymmetricResidual.residualAxial AxisymmetricResidual.advectionAxial
    AxisymmetricResidual.laplaceScalar RadialFluxResidual.radialB transportResidual
  field_simp [hs] ; ring

noncomputable def slowVelocity (N : ℕ) (h C : ℝ) (f : SlowProfiles) :
    ProblemStatement.VelocityField :=
  AxisymmetricResidual.velocity (RadialFluxResidual.radialB (slowFlux N h f))
    (slowSwirl N h C f) (slowAxial N h f)

noncomputable def slowPressureField (N : ℕ) (h : ℝ) (f : SlowProfiles) :
    ProblemStatement.PressureField := AxisymmetricResidual.pressure (slowPressure N h f)

/-- Cartesian realization of the radial-flux and swirl ansatz. -/
theorem slowVelocity_components (N : ℕ) (h C : ℝ) (f : SlowProfiles)
    (t : ℝ) (x : ProblemStatement.Space) :
    slowVelocity N h C f (t, x) =
      AxisymmetricResidual.pack
        (x 0 * (slowFlux N h f (profilePoint t x) / (2 * radialEnergy x)) -
          x 1 * slowSwirl N h C f (profilePoint t x))
        (x 1 * (slowFlux N h f (profilePoint t x) / (2 * radialEnergy x)) +
          x 0 * slowSwirl N h C f (profilePoint t x))
        (slowAxial N h f (profilePoint t x)) := by
  ext i
  fin_cases i <;>
    simp [slowVelocity, AxisymmetricResidual.velocity, AxisymmetricResidual.componentX,
      AxisymmetricResidual.componentY, AxisymmetricResidual.lift, RadialFluxResidual.radialB,
      AxisymmetricResidual.pack, ProblemStatement.coordinateVector,
      profilePoint] <;> ring

theorem slowVelocity_radial_flux (N : ℕ) (h C : ℝ) (f : SlowProfiles)
    (t : ℝ) (x : ProblemStatement.Space) (hs : 0 < radialEnergy x) :
    x 0 * slowVelocity N h C f (t, x) 0 + x 1 * slowVelocity N h C f (t, x) 1 =
      slowFlux N h f (profilePoint t x) :=
  RadialFluxResidual.radial_flux_velocity _ _ _ _ _ hs

/-- The finite field's divergence is exactly its finite divergence-coefficient
sum. This assertion uses the actual Euclidean divergence, away from the axis. -/
theorem divergence_slowVelocity {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) {t : ℝ} {x : ProblemStatement.Space}
    (ht : t < 1) (hs : 0 < radialEnergy x)
    (hv : ∀ n ≤ N, DifferentiableAt ℝ (f.flux n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hf : ∀ n ≤ N, DifferentiableAt ℝ (f.phi n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hu : ∀ n ≤ N, DifferentiableAt ℝ (f.axial n)
      (SimilarityProfile.inner h (profilePoint t x))) :
    ProblemStatement.spatialDivergence (slowVelocity N h C f) t x =
      finiteSeries N (SimilarityProfile.q h (profilePoint t x)) h (-1)
        (fun n => divergenceCoefficient h f n (SimilarityProfile.inner h (profilePoint t x))) := by
  have hV := finiteProfile_differentiableAt (e := 0) hh hh1 N f.flux ht hv
  have hF := (finiteProfile_differentiableAt (e := angularExponent h) hh hh1 N f.phi ht
    hf).const_mul C⁻¹
  have hU := finiteProfile_differentiableAt (e := axialExponent h) hh hh1 N f.axial ht hu
  change ProblemStatement.spatialDivergence
    (AxisymmetricResidual.velocity (RadialFluxResidual.radialB (slowFlux N h f))
      (slowSwirl N h C f) (slowAxial N h f)) t x = _
  exact (RadialFluxResidual.divergence_radialB hV hF hU hs).trans
    (divergence_finite_expansion hh hh1 N f ht hv hu)

theorem finiteSeries_eq_zero (N : ℕ) (q h e : ℝ) (a : ℕ → ℝ)
    (ha : ∀ n ≤ N, a n = 0) : finiteSeries N q h e a = 0 := by
  unfold finiteSeries
  apply Finset.sum_eq_zero
  intro n hn
  rw [ha n (by have := Finset.mem_range.mp hn; omega), mul_zero]

theorem divergence_slowVelocity_eq_zero {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) {t : ℝ} {x : ProblemStatement.Space}
    (ht : t < 1) (hs : 0 < radialEnergy x)
    (hv : ∀ n ≤ N, DifferentiableAt ℝ (f.flux n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hf : ∀ n ≤ N, DifferentiableAt ℝ (f.phi n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hu : ∀ n ≤ N, DifferentiableAt ℝ (f.axial n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hdiv : ∀ n ≤ N, divergenceCoefficient h f n
      (SimilarityProfile.inner h (profilePoint t x)) = 0) :
    ProblemStatement.spatialDivergence (slowVelocity N h C f) t x = 0 := by
  rw [divergence_slowVelocity hh hh1 N C f ht hs hv hf hu]
  exact finiteSeries_eq_zero _ _ _ _ _ hdiv

noncomputable def angularExpansion (N : ℕ) (q h C : ℝ) (f : SlowProfiles)
    (w : InnerPoint) : ℝ :=
  C⁻¹ * (finiteSeries N q h (angularExponent h - 1) (fun n => angularCoefficient h f n w) +
    transportTail N q h (angularExponent h) 1 f.flux f.axial f.phi w)

noncomputable def axialExpansion (N : ℕ) (q h : ℝ) (f : SlowProfiles)
    (w : InnerPoint) : ℝ :=
  finiteSeries N q h (axialExponent h - 1) (fun n => axialCoefficient h f n w) +
    transportTail N q h (axialExponent h) 0 f.flux f.axial f.axial w

noncomputable def radialFluxExpansion (N : ℕ) (q h C : ℝ) (f : SlowProfiles)
    (w : InnerPoint) : ℝ :=
  2 * w.1 * finiteSeries N q h (pressureExponent h) (fun n => pressureCoefficient h C f n w) +
    pressureTail N q h C f w

/-- Reconstruction of the full Cartesian Navier--Stokes residual of the
finite slow expansion. Every derivative on the left is the genuine spatial
or temporal Fréchet derivative from `ProblemStatement`. -/
theorem navierStokesResidual_slowVelocity {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) {t : ℝ} {x : ProblemStatement.Space}
    (ht : t < 1) (hs : 0 < radialEnergy x)
    (hv : ∀ n ≤ N, ContDiffAt ℝ 2 (f.flux n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f.phi n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hu : ∀ n ≤ N, ContDiffAt ℝ 2 (f.axial n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hπ : ∀ n ≤ N, DifferentiableAt ℝ (f.pressure n)
      (SimilarityProfile.inner h (profilePoint t x))) :
    ProblemStatement.navierStokesResidual (slowVelocity N h C f) (slowPressureField N h f) t x =
      let q := SimilarityProfile.q h (profilePoint t x)
      let w := SimilarityProfile.inner h (profilePoint t x)
      AxisymmetricResidual.pack
        (x 0 * (radialFluxExpansion N q h C f w / (2 * radialEnergy x)) -
          x 1 * angularExpansion N q h C f w)
        (x 1 * (radialFluxExpansion N q h C f w / (2 * radialEnergy x)) +
          x 0 * angularExpansion N q h C f w)
        (axialExpansion N q h f w) := by
  have hV : ContDiffAt ℝ 2 (slowFlux N h f) (profilePoint t x) :=
    finiteProfile_smoothAt hh hh1 N f.flux ht hv
  have hF : ContDiffAt ℝ 2 (slowSwirl N h C f) (profilePoint t x) :=
    contDiffAt_const.mul (finiteProfile_smoothAt hh hh1 N f.phi ht hf)
  have hU : ContDiffAt ℝ 2 (slowAxial N h f) (profilePoint t x) :=
    finiteProfile_smoothAt hh hh1 N f.axial ht hu
  have hP : DifferentiableAt ℝ (slowPressure N h f) (profilePoint t x) :=
    finiteProfile_differentiableAt hh hh1 N f.pressure ht hπ
  have hB := RadialFluxResidual.contDiffAt_radialB hV hs.ne'
  have hR : AxisymmetricResidual.residualRadial (RadialFluxResidual.radialB (slowFlux N h f))
      (slowSwirl N h C f) (slowAxial N h f) (slowPressure N h f) (profilePoint t x) =
      radialFluxExpansion N (SimilarityProfile.q h (profilePoint t x)) h C f
        (SimilarityProfile.inner h (profilePoint t x)) / (2 * radialEnergy x) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hs.ne')).2
    rw [mul_comm]
    exact (RadialFluxResidual.residualRadial_radialB _ _ _ hV hs).trans
      (pressure_finite_expansion hh hh1 N C f ht hs hv hπ)
  have hA : AxisymmetricResidual.residualAngular (RadialFluxResidual.radialB (slowFlux N h f))
      (slowSwirl N h C f) (slowAxial N h f) (profilePoint t x) =
      -angularExpansion N (SimilarityProfile.q h (profilePoint t x)) h C f
        (SimilarityProfile.inner h (profilePoint t x)) := by
    rw [residualAngular_radialB _ _ _ hs.ne']
    exact congrArg Neg.neg (angular_finite_expansion hh hh1 N C f ht hs hf)
  have hZ : AxisymmetricResidual.residualAxial (RadialFluxResidual.radialB (slowFlux N h f))
      (slowAxial N h f) (slowPressure N h f) (profilePoint t x) =
      axialExpansion N (SimilarityProfile.q h (profilePoint t x)) h f
        (SimilarityProfile.inner h (profilePoint t x)) := by
    rw [residualAxial_radialB _ _ _ hs.ne']
    exact axial_finite_expansion hh hh1 N f ht hs hu hπ
  have he := LocalAxisymmetricResidual.navierStokesResidual_velocity hB hF hU hP
  rw [hR, hA, hZ] at he
  unfold slowVelocity slowPressureField
  simpa only [mul_neg, sub_neg_eq_add, ← sub_eq_add_neg] using he

/-- The explicit forcing left by truncation once all retained coefficient
equations hold. This includes omitted quadratic interactions and the final
axial-viscosity and radial-acceleration terms. -/
noncomputable def truncationResidual (N : ℕ) (h C : ℝ) (f : SlowProfiles)
    (t : ℝ) (x : ProblemStatement.Space) : ProblemStatement.Space :=
  let q := SimilarityProfile.q h (profilePoint t x)
  let w := SimilarityProfile.inner h (profilePoint t x)
  let R := pressureTail N q h C f w / (2 * radialEnergy x)
  let A := C⁻¹ * transportTail N q h (angularExponent h) 1 f.flux f.axial f.phi w
  let U := transportTail N q h (axialExponent h) 0 f.flux f.axial f.axial w
  AxisymmetricResidual.pack (x 0 * R - x 1 * A) (x 1 * R + x 0 * A) U

/-- Solving all retained coefficient equations produces precisely the
displayed truncation forcing; it does not make that forcing disappear. -/
theorem navierStokesResidual_slowVelocity_of_coefficients
    {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (N : ℕ) (C : ℝ) (f : SlowProfiles) {t : ℝ} {x : ProblemStatement.Space}
    (ht : t < 1) (hs : 0 < radialEnergy x)
    (hv : ∀ n ≤ N, ContDiffAt ℝ 2 (f.flux n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hf : ∀ n ≤ N, ContDiffAt ℝ 2 (f.phi n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hu : ∀ n ≤ N, ContDiffAt ℝ 2 (f.axial n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hπ : ∀ n ≤ N, DifferentiableAt ℝ (f.pressure n)
      (SimilarityProfile.inner h (profilePoint t x)))
    (hA : ∀ n ≤ N, angularCoefficient h f n (SimilarityProfile.inner h (profilePoint t x)) = 0)
    (hZ : ∀ n ≤ N, axialCoefficient h f n (SimilarityProfile.inner h (profilePoint t x)) = 0)
    (hR : ∀ n ≤ N, pressureCoefficient h C f n (SimilarityProfile.inner h (profilePoint t x)) = 0) :
    ProblemStatement.navierStokesResidual (slowVelocity N h C f) (slowPressureField N h f) t x =
      truncationResidual N h C f t x := by
  rw [navierStokesResidual_slowVelocity hh hh1 N C f ht hs hv hf hu hπ]
  simp only [radialFluxExpansion, angularExpansion, axialExpansion,
    finiteSeries_eq_zero _ _ _ _ _ hA, finiteSeries_eq_zero _ _ _ _ _ hZ,
    finiteSeries_eq_zero _ _ _ _ _ hR, mul_zero, zero_add]
  rfl

end NavierStokes.SlowExpansionResidual
