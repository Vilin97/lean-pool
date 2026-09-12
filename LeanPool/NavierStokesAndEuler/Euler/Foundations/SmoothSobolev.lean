/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Sobolev
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! Sobolev embedding for general smooth fields on R³, without Schwartz assumptions. -/

@[expose] public section

noncomputable section

namespace EulerSmoothSobolev

open MeasureTheory FourierTransform EulerSobolev
open scoped SchwartzMap ENNReal NNReal ContDiff Topology LineDeriv

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Repeated directional derivatives of a vector-valued Schwartz function. -/
noncomputable def pureDerivative (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, F)) :
    𝓢(Domain d, F) := schwartzIteratedDerivative (fun _ : Fin n => v) f

omit [CompleteSpace F] in
theorem fourier_pureDerivative_norm (d n : ℕ) (v : Domain d)
    (f : 𝓢(Domain d, F)) (ξ : Domain d) :
    ‖schwartzFourier (pureDerivative d n v f) ξ‖ =
      (2 * Real.pi) ^ n * ‖inner ℝ ξ v‖ ^ n * ‖schwartzFourier f ξ‖ := by
  change ‖𝓕 (pureDerivative d n v f) ξ‖ =
      (2 * Real.pi) ^ n * ‖inner ℝ ξ v‖ ^ n * ‖𝓕 f ξ‖
  induction n with
  | zero => simp [pureDerivative]
  | succ n ih =>
    have ht : (fun ξ : Domain d => inner ℝ ξ v).HasTemperateGrowth :=
      ((innerSL ℝ).flip v).hasTemperateGrowth
    have hd : pureDerivative d (n+1) v f = ∂_{v} (pureDerivative d n v f) := rfl
    rw [hd, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul]
    have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc, ih, pow_succ, pow_succ]
    ring

/-- The pointwise norm of a Schwartz function, represented in the real `L²` space. -/
noncomputable def normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (f.memLp 2 volume).norm.toLp (fun x => ‖f x‖)

omit [CompleteSpace F] in
theorem norm_normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    ‖normLp d f‖ = ‖f.toLp 2‖ := by
  simp only [normLp, Lp.norm_toLp, eLpNorm_norm, SchwartzMap.norm_toLp]

omit [CompleteSpace F] in
theorem coe_normLp (d : ℕ) (f : 𝓢(Domain d, F)) :
    (normLp d f : Domain d → ℝ) =ᵐ[volume] (fun x => ‖f x‖) :=
  (f.memLp 2 volume).norm.coeFn_toLp

omit [CompleteSpace F] in
theorem normLp_le_sum {ι : Type*} [Fintype ι] (d : ℕ) (f : 𝓢(Domain d, F))
    (g : ι → 𝓢(Domain d, F)) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ∑ i, ‖g i x‖) :
    ‖f.toLp 2‖ ≤ C * ∑ i, ‖(g i).toLp 2‖ := by
  have hs : ∀ᵐ x ∂(volume : Measure (Domain d)), ∀ i, normLp d (g i) x = ‖g i x‖ :=
    Filter.eventually_all.2 (fun i => coe_normLp d (g i))
  have hb : ‖f.toLp 2‖ ≤ C * ‖∑ i, normLp d (g i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [f.coeFn_toLp 2, Lp.coeFn_finsetSum Finset.univ (fun i => normLp d (g i)), hs]
      with x hf hsum hx
    rw [hf, hsum]
    simp only [Finset.sum_apply, hx, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact h x
  refine hb.trans ?_
  calc
    _ ≤ C * ∑ i, ‖normLp d (g i)‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC
    _ = _ := by simp only [norm_normLp]

theorem sobolevNorm_two_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, F)) :
    sobolevNorm d 2 f ≤ 1 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin d, ‖(pureDerivative d 2 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, F) := fun i => match i with
    | none => schwartzFourier f
    | some i => ((2 * Real.pi) ^ (-2 : ℤ) : ℝ) •
        schwartzFourier (pureDerivative d 2 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 2 f ξ‖ ≤ 1 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 2 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 2) * ‖schwartzFourier f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-2 : ℤ)),
        fourier_pureDerivative_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-2 : ℤ) * (2 * Real.pi) ^ (2 : ℕ) = 1 := by
        rw [show (-2 : ℤ) = -(2 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (le_of_eq (show besselWeight d 2 ξ = 1 + ∑ i, ‖ξ i‖ ^ 2 by
        norm_num [besselWeight, EuclideanSpace.norm_sq_eq])) (norm_nonneg (schwartzFourier f ξ))]
  have h := normLp_le_sum d (weightedFourier d 2 f) g 1
    (by norm_num) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-2 : ℤ) * ∑ i : Fin d,
        ‖(pureDerivative d 2 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ F 2 volume (((2 * Real.pi) ^ (-2 : ℤ)) •
        𝓕 (pureDerivative d 2 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-2 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

/-- The sharp three-dimensional H² pointwise bound in terms of actual second derivatives. -/
theorem pointwise_le_L2_second_derivatives (f : 𝓢(Domain 3, F)) (x : Domain 3) :
    ‖f x‖ ≤ embeddingConstant 3 2 (by norm_num) *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-2 : ℤ) *
        ∑ i : Fin 3, ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  have hA := norm_apply_le_sobolevNorm 3 2 (by norm_num) f x
  have hB := mul_le_mul_of_nonneg_left (sobolevNorm_two_le_pure_derivatives 3 f)
    (show 0 ≤ embeddingConstant 3 2 (by norm_num) from norm_nonneg _)
  simpa only [one_mul] using hA.trans hB

/-- The sum of the actual L² norms of Fréchet derivatives through order `s`. -/
noncomputable def tensorSobolevNorm (s : ℕ) (f : Domain 3 → F) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal)

omit [CompleteSpace F] in
theorem tensorSobolevNorm_nonneg (s : ℕ) (f : Domain 3 → F) : 0 ≤ tensorSobolevNorm s f :=
  Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

omit [CompleteSpace F] in
theorem tensorSobolevNorm_mono {s t : ℕ} (hst : s ≤ t) (f : Domain 3 → F) :
    tensorSobolevNorm s f ≤ tensorSobolevNorm t f :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by
      omega)) (fun _ _ _ => ENNReal.toReal_nonneg)

/-- Sum of the pointwise norms of all derivatives through a fixed order. -/
noncomputable def derivativeMagnitude (s : ℕ) (f : Domain 3 → F) (x : Domain 3) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => ‖iteratedFDeriv ℝ j f x‖)

omit [CompleteSpace F] in
theorem derivativeMagnitude_nonneg (s : ℕ) (f : Domain 3 → F) (x : Domain 3) :
    0 ≤ derivativeMagnitude s f x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [CompleteSpace F] in
theorem derivativeMagnitude_memLp (s : ℕ) (f : Domain 3 → F)
    (hfL2 : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (derivativeMagnitude s f) 2 volume :=
  memLp_finsetSum _ (fun j hj => (hfL2 j (by have := Finset.mem_range.1 hj; omega)).norm)

omit [CompleteSpace F] in
theorem derivativeMagnitude_L2_le (s : ℕ) (f : Domain 3 → F)
    (hfL2 : ∀ j ≤ s, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    ‖(derivativeMagnitude_memLp s f hfL2).toLp (derivativeMagnitude s f)‖ ≤ tensorSobolevNorm s f
        := by
  have he : derivativeMagnitude s f = ∑ j ∈ Finset.range (s+1), fun x => ‖iteratedFDeriv ℝ j f x‖
      := by
    funext x
    simp [derivativeMagnitude]
  have hA : eLpNorm (derivativeMagnitude s f) 2 volume ≤
      ∑ j ∈ Finset.range (s+1), eLpNorm (iteratedFDeriv ℝ j f) 2 volume := by
    rw [he]
    simpa only [eLpNorm_norm] using eLpNorm_sum_le (fun j hj =>
      (hfL2 j (by have := Finset.mem_range.1 hj; omega)).1.norm) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfin (j : ℕ) (hj : j ∈ Finset.range (s+1)) : eLpNorm (iteratedFDeriv ℝ j f) 2 volume ≠ ⊤ :=
    (hfL2 j (by have := Finset.mem_range.1 hj; omega)).eLpNorm_ne_top
  have hB := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin) hA
  rw [ENNReal.toReal_sum hfin] at hB
  rw [Lp.norm_toLp]
  exact hB

/-- A fixed bump equal to one near zero, independent of the function being estimated. -/
noncomputable def unitBump : ContDiffBump (0 : Domain 3) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The same fixed bump as a Schwartz function. -/
noncomputable def unitBumpSchwartz : 𝓢(Domain 3, ℝ) :=
  unitBump.hasCompactSupport.toSchwartzMap unitBump.contDiff

/-- A finite derivative bound for the fixed bump. -/
noncomputable def unitBumpBound (j : ℕ) : NNReal :=
  ⟨SchwartzMap.seminorm ℝ 0 j unitBumpSchwartz, apply_nonneg _ _⟩

/-- The finite Leibniz coefficient for localizing an order `n` derivative. -/
noncomputable def unitBumpCoefficient (n : ℕ) : NNReal :=
  Finset.sum (Finset.range (n+1)) (fun j => (n.choose j : ℝ≥0) * unitBumpBound j)

/-- An actual smooth compact localization of an arbitrary smooth function about `x`. -/
noncomputable def localize (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x : Domain 3) : 𝓢(Domain 3, F)
    :=
  (unitBump.hasCompactSupport.smul_right (f' := fun z => f (x+z))).toSchwartzMap
    (unitBump.contDiff.smul (hf.comp (contDiff_const.add contDiff_id)))

omit [CompleteSpace F] in
@[simp] theorem localize_apply (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x z : Domain 3) :
    localize f hf x z = unitBump z • f (x+z) := rfl

omit [CompleteSpace F] in
theorem localize_zero (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    localize f hf x 0 = f x := by
  rw [localize_apply, unitBump.one_of_mem_closedBall (by simp [unitBump]), one_smul, add_zero]

omit [CompleteSpace F] in
/-- Localization obeys the actual tensor Leibniz estimate. -/
theorem localize_tensor_bound (n : ℕ) (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) (x z : Domain 3) :
    ‖iteratedFDeriv ℝ n (localize f hf x) z‖ ≤
      (unitBumpCoefficient n : ℝ) * derivativeMagnitude n f (x+z) := by
  have hshift : ContDiff ℝ ∞ (fun z => f (x+z)) := hf.comp (contDiff_const.add contDiff_id)
  have hA := norm_iteratedFDeriv_smul_le unitBump.contDiff
    hshift z (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  apply hA.trans
  have hb (j : ℕ) : ‖iteratedFDeriv ℝ j unitBump z‖ ≤ unitBumpBound j :=
    SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ unitBumpSchwartz j z
  have hd (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      ‖iteratedFDeriv ℝ (n-j) (fun z => f (x+z)) z‖ ≤ derivativeMagnitude n f (x+z) := by
    rw [iteratedFDeriv_comp_add_left]
    exact Finset.single_le_sum (f := fun k => ‖iteratedFDeriv ℝ k f (x+z)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ) * unitBumpBound j) * derivativeMagnitude n f
        (x+z) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg _)) (hd j hj)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (unitBumpBound j).coe_nonneg)
    _ = _ := by
        simp only [unitBumpCoefficient, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_natCast,
            Finset.sum_mul]

omit [CompleteSpace F] in
/-- Each localized pure derivative is controlled by the global physical Sobolev norm. -/
theorem localize_pureDerivative_L2_le (n : ℕ) (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : ∀ j ≤ n, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖(pureDerivative 3 n (EuclideanSpace.single i 1) (localize f hf x)).toLp 2‖ ≤
      (unitBumpCoefficient n : ℝ) * tensorSobolevNorm n f := by
  have hq := derivativeMagnitude_memLp n f hfL2
  have htrans := measurePreserving_add_left (volume : Measure (Domain 3)) x
  have hqt : MemLp (fun z => derivativeMagnitude n f (x+z)) 2 volume := hq.comp_measurePreserving
      htrans
  have hb (z : Domain 3) :
      ‖pureDerivative 3 n (EuclideanSpace.single i 1) (localize f hf x) z‖ ≤
        (unitBumpCoefficient n : ℝ) * ‖derivativeMagnitude n f (x+z)‖ := by
    rw [pureDerivative, schwartzIteratedDerivative_apply,
      Real.norm_of_nonneg (derivativeMagnitude_nonneg n f (x+z))]
    have hA := (iteratedFDeriv ℝ n (localize f hf x) z).le_opNorm
      (fun _ : Fin n => EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, Finset.prod_const_one, mul_one] at hA
    exact hA.trans (localize_tensor_bound n f hf x z)
  have hA := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Domain 3)))
    (Filter.Eventually.of_forall hb) 2
  have hfin : (unitBumpCoefficient n : ℝ≥0∞) *
      eLpNorm (fun z => derivativeMagnitude n f (x+z)) 2 volume ≠ ⊤ := by finiteness
  have hB := ENNReal.toReal_mono hfin hA
  have he : eLpNorm (fun z => derivativeMagnitude n f (x+z)) 2 volume =
      eLpNorm (derivativeMagnitude n f) 2 volume := by
    simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞)) hq.1
        htrans
  rw [he] at hB
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hB
  rw [SchwartzMap.norm_toLp]
  have hC := mul_le_mul_of_nonneg_left (derivativeMagnitude_L2_le n f hfL2) (unitBumpCoefficient
      n).coe_nonneg
  rw [Lp.norm_toLp] at hC
  exact hB.trans hC

/-- A fixed finite three-dimensional H² embedding constant. -/
noncomputable def smoothEmbeddingConstant : ℝ :=
  embeddingConstant 3 2 (by norm_num) *
    ((unitBumpCoefficient 0 : ℝ) + (2 * Real.pi)^(-2 : ℤ) * 3 * unitBumpCoefficient 2)

theorem smoothEmbeddingConstant_nonneg : 0 ≤ smoothEmbeddingConstant := by
  have h : 0 ≤ embeddingConstant 3 2 (by norm_num) := norm_nonneg _
  unfold smoothEmbeddingConstant
  positivity

/-- Genuine H² to L∞ embedding for every smooth Hilbert-valued function on R³. -/
theorem smooth_pointwise_le_H2 (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 2, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖f x‖ ≤ smoothEmbeddingConstant * tensorSobolevNorm 2 f := by
  have hzero := localize_pureDerivative_L2_le 0 0 f hf (fun j hj => hfL2 j (by omega)) x
  have he : pureDerivative 3 0 (EuclideanSpace.single 0 1) (localize f hf x) = localize f hf x := by
    ext z
    simp [pureDerivative]
  rw [he] at hzero
  have hzero' := hzero.trans (mul_le_mul_of_nonneg_left (tensorSobolevNorm_mono (show 0 ≤ 2 by
      omega) f)
    (unitBumpCoefficient 0).coe_nonneg)
  have htwo : (∑ i : Fin 3, ‖(pureDerivative 3 2 (EuclideanSpace.single i 1) (localize f hf
      x)).toLp 2‖) ≤
      3 * ((unitBumpCoefficient 2 : ℝ) * tensorSobolevNorm 2 f) := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
      localize_pureDerivative_L2_le 2 i f hf hfL2 x)
  have hA := pointwise_le_L2_second_derivatives (localize f hf x) 0
  rw [localize_zero] at hA
  have hB := add_le_add hzero' (mul_le_mul_of_nonneg_left htwo
    (zpow_nonneg (by positivity : (0 : ℝ) ≤ 2*Real.pi) (-2 : ℤ)))
  have hC := mul_le_mul_of_nonneg_left hB (show 0 ≤ embeddingConstant 3 2 (by
      norm_num) from norm_nonneg _)
  have harith (C A B p S : ℝ) : C * (A*S+p*(3*(B*S))) = (C*(A+p*3*B))*S := by ring
  exact hA.trans (hC.trans_eq (harith _ _ _ _ _))

/-- The actual derivative in one Euclidean coordinate direction. -/
noncomputable def coordinateDerivative (i : Fin 3) (f : Domain 3 → F) : Domain 3 → F :=
  fun x => fderiv ℝ f x (EuclideanSpace.single i 1)

omit [CompleteSpace F] in
theorem coordinateDerivative_smooth (i : Fin 3) (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coordinateDerivative i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

omit [CompleteSpace F] in
theorem coordinateDerivative_tensor_bound (j : ℕ) (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ j (coordinateDerivative i f) x‖ ≤ ‖iteratedFDeriv ℝ (j+1) f x‖ := by
  let L : (Domain 3 →L[ℝ] F) →L[ℝ] F :=
    ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i 1)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro A
    simpa only [L, ContinuousLinearMap.apply_apply, PiLp.norm_single, norm_one, one_mul, mul_one]
        using
      A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
  have hA := L.norm_iteratedFDeriv_comp_left (x := x)
    (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).contDiffAt
    (by simp : (j : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  change ‖iteratedFDeriv ℝ j (coordinateDerivative i f) x‖ ≤ _ at hA
  have hB := mul_le_mul_of_nonneg_right hL (norm_nonneg (iteratedFDeriv ℝ j (fderiv ℝ f) x))
  rw [one_mul, norm_iteratedFDeriv_fderiv] at hB
  rw [norm_iteratedFDeriv_fderiv] at hA
  exact hA.trans hB

omit [CompleteSpace F] in
theorem coordinateDerivative_tensor_memLp {j : ℕ} (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : MemLp (iteratedFDeriv ℝ (j + 1) f) 2 volume) :
    MemLp (iteratedFDeriv ℝ j (coordinateDerivative i f)) 2 volume :=
  hfL2.of_le ((coordinateDerivative_smooth i f hf).continuous_iteratedFDeriv (by
      simp)).aestronglyMeasurable
    (Filter.Eventually.of_forall (coordinateDerivative_tensor_bound j i f hf))

omit [CompleteSpace F] in
theorem coordinateDerivative_H2_le_H3 (i : Fin 3) (f : Domain 3 → F)
    (hf : ContDiff ℝ ∞ f) (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    tensorSobolevNorm 2 (coordinateDerivative i f) ≤ 3 * tensorSobolevNorm 3 f := by
  have hA : tensorSobolevNorm 2 (coordinateDerivative i f) ≤
      ∑ _j ∈ Finset.range 3, tensorSobolevNorm 3 f := by
    apply Finset.sum_le_sum
    intro j hj
    have hj3 : j+1 ≤ 3 := by have := Finset.mem_range.1 hj; omega
    have hB := ENNReal.toReal_mono (hfL2 (j+1) hj3).eLpNorm_ne_top
      (eLpNorm_mono (coordinateDerivative_tensor_bound j i f hf))
    have hC : (eLpNorm (iteratedFDeriv ℝ (j+1) f) 2 volume).toReal ≤ tensorSobolevNorm 3 f :=
      Finset.single_le_sum (f := fun k => (eLpNorm (iteratedFDeriv ℝ k f) 2 volume).toReal)
        (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_range.2 (by omega))
    exact hB.trans hC
  simpa using hA

omit [CompleteSpace F] in
/-- A linear map is controlled by the sum of its values on the coordinate basis. -/
theorem linear_norm_le_coordinate_sum (A : Domain 3 →L[ℝ] F) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (EuclideanSpace.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have hx : (∑ i : Fin 3, (x i) • EuclideanSpace.single i (1 : ℝ)) = x := by
    ext i
    simp [Pi.single_apply, mul_ite]
  have hA : A x = ∑ i : Fin 3, (x i) • A (EuclideanSpace.single i (1 : ℝ)) := by
    simp_rw [← map_smul]
    rw [← map_sum, hx]
  rw [hA]
  calc
    _ ≤ ∑ i : Fin 3, ‖(x i) • A (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖x i‖ * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i)
          (norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The exact regularity needed in the limiting Euler contradiction: H³ controls the C¹ derivative.
-/
theorem smooth_fderiv_le_H3 (f : Domain 3 → F) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖fderiv ℝ f x‖ ≤ (9 * smoothEmbeddingConstant) * tensorSobolevNorm 3 f := by
  have hA := linear_norm_le_coordinate_sum (fderiv ℝ f x)
  have hB (i : Fin 3) : ‖coordinateDerivative i f x‖ ≤
      smoothEmbeddingConstant * (3 * tensorSobolevNorm 3 f) := by
    have hC := smooth_pointwise_le_H2 (coordinateDerivative i f) (coordinateDerivative_smooth i f
        hf)
      (fun j hj => coordinateDerivative_tensor_memLp i f hf (hfL2 (j+1) (by omega))) x
    exact hC.trans (mul_le_mul_of_nonneg_left (coordinateDerivative_H2_le_H3 i f hf hfL2)
      smoothEmbeddingConstant_nonneg)
  have hC := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hB i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hC
  have he (C A : ℝ) : (3 : ℝ)*(C*(3*A)) = (9*C)*A := by ring
  exact hA.trans (hC.trans_eq (he _ _))

/-- The physical tensor Sobolev norm for real Euclidean vector fields. -/
noncomputable def realTensorSobolevNorm (q s : ℕ) (f : Domain 3 → Domain q) : ℝ :=
  Finset.sum (Finset.range (s+1)) (fun j => (eLpNorm (iteratedFDeriv ℝ j f) 2 volume).toReal)

theorem complexification_tensor_norm (q j : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (x : Domain 3) :
    ‖iteratedFDeriv ℝ j (complexify q ∘ f) x‖ = ‖iteratedFDeriv ℝ j f x‖ :=
  (complexify q).norm_iteratedFDeriv_comp_left hf.contDiffAt (by simp)

theorem complexification_tensor_memLp (q j : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) (hfL2 : MemLp (iteratedFDeriv ℝ j f) 2 volume) :
    MemLp (iteratedFDeriv ℝ j (complexify q ∘ f)) 2 volume := by
  have hc : Continuous (iteratedFDeriv ℝ j (complexify q ∘ f)) :=
    ((complexify q).contDiff.comp hf).continuous_iteratedFDeriv (by simp)
  apply hfL2.of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  exact (complexification_tensor_norm q j f hf x).le

theorem complexification_sobolevNorm (q s : ℕ) (f : Domain 3 → Domain q)
    (hf : ContDiff ℝ ∞ f) :
    tensorSobolevNorm s (complexify q ∘ f) = realTensorSobolevNorm q s f := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (complexification_tensor_norm q j f hf))

/-- Real vector-valued H³ to C¹ on R³, for general smooth functions with actual L² derivatives. -/
theorem real_smooth_fderiv_le_H3 (q : ℕ) (f : Domain 3 → Domain q) (hf : ContDiff ℝ ∞ f)
    (hfL2 : ∀ j ≤ 3, MemLp (iteratedFDeriv ℝ j f) 2 volume) (x : Domain 3) :
    ‖fderiv ℝ f x‖ ≤ (9 * smoothEmbeddingConstant) * realTensorSobolevNorm q 3 f := by
  have h := smooth_fderiv_le_H3 (complexify q ∘ f) ((complexify q).contDiff.comp hf)
    (fun j hj => complexification_tensor_memLp q j f hf (hfL2 j hj)) x
  have he : ‖fderiv ℝ (complexify q ∘ f) x‖ = ‖fderiv ℝ f x‖ := by
    simpa only [norm_iteratedFDeriv_one] using complexification_tensor_norm q 1 f hf x
  rw [he, complexification_sobolevNorm q 3 f hf] at h
  exact h

end EulerSmoothSobolev
