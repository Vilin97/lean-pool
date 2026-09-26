/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Cutoff.Box
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.FixedPhase.Resample

/-!
# The per-core cutoff datum

For the per-core energy bound (`local_block_energy`, T2) behind the fixed-phase
variance (Proposition 4.3) we need, for each core `coreBox ℓ σ k`, a smooth
cutoff `η` that is `1` on the core, supported in the `ℓ`-enlargement, with the
two integral estimates of `e.corridor.cutoff`:

* support-volume bound `(vol (supp η ∩ U)).toReal ≤ (3ℓ)^d`;
* squared-gradient bound `∫_U Σᵢ (∂ᵢ η)² ≤ d · (16/ℓ)² · (3ℓ)^d`.

The cutoff is the `boxCutoff` for the closed core box (which is exactly
`Set.Icc (coreLo ℓ σ k) (coreHi ℓ σ k)`) with margin `ℓ`.  The gradient integral
is finite because the gradient is supported in the (closed, bounded) enlargement
`Set.Icc (coreLo − ℓ) (coreHi + ℓ)`: off that enlargement `η` vanishes on an open
set, so its Fréchet derivative is zero there.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators

namespace Homogenization

variable {d : ℕ} {ℓ : ℝ}

/-! ## The core box as a closed axis box -/

/-- The lower corner of the closed core box. -/
def coreLo (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) : Vec d :=
  fun i => σ i + (k i : ℝ) * ℓ + 1

/-- The upper corner of the closed core box. -/
def coreHi (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) : Vec d :=
  fun i => σ i + ((k i : ℝ) + 1) * ℓ - 1

theorem coreBox_eq_Icc (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) :
    coreBox ℓ σ k = Set.Icc (coreLo ℓ σ k) (coreHi ℓ σ k) := by
  rw [coreBox, ← Set.pi_univ_Icc]; rfl

/-- Side length `hi − lo = ℓ − 2` in every coordinate. -/
theorem coreHi_sub_coreLo (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) (i : Fin d) :
    coreHi ℓ σ k i - coreLo ℓ σ k i = ℓ - 2 := by
  simp only [coreHi, coreLo]; ring

theorem coreLo_le_coreHi (hℓ : (2 : ℝ) ≤ ℓ) (σ : Vec d) (k : Fin d → ℤ) :
    coreLo ℓ σ k ≤ coreHi ℓ σ k := by
  intro i
  have := coreHi_sub_coreLo ℓ σ k i
  linarith

/-! ## The per-core cutoff -/

/-- The per-core smooth cutoff: `boxCutoff` of the closed core box with
margin `ℓ`. -/
noncomputable def coreCutoff (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) : Vec d → ℝ :=
  boxCutoff (coreLo ℓ σ k) (coreHi ℓ σ k) ℓ

theorem coreCutoff_contDiff (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (coreCutoff ℓ σ k) := boxCutoff_contDiff

theorem coreCutoff_mem_Icc (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) (x : Vec d) :
    coreCutoff ℓ σ k x ∈ Set.Icc (0 : ℝ) 1 :=
  Set.mem_Icc.2 ⟨boxCutoff_nonneg x, boxCutoff_le_one x⟩

theorem coreCutoff_deriv_bound (hℓ : 0 < ℓ) (σ : Vec d) (k : Fin d → ℤ)
    (x : Vec d) (i : Fin d) :
    |fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)| ≤ 16 / ℓ :=
  boxCutoff_deriv_bound hℓ x i

/-- On the core box the cutoff is identically `1`. -/
theorem coreCutoff_eq_one_of_mem_coreBox (hℓ : 0 < ℓ) (σ : Vec d) (k : Fin d → ℤ)
    {x : Vec d} (hx : x ∈ coreBox ℓ σ k) : coreCutoff ℓ σ k x = 1 := by
  rw [coreBox_eq_Icc] at hx
  exact boxCutoff_eq_one hℓ hx

/-! ## The closed enlargement and the support of the gradient -/

/-- The closed `ℓ`-enlargement of the core box. -/
def coreEnlarge (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) : Set (Vec d) :=
  Set.Icc (fun i => coreLo ℓ σ k i - ℓ) (fun i => coreHi ℓ σ k i + ℓ)

theorem measurableSet_coreEnlarge (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) :
    MeasurableSet (coreEnlarge ℓ σ k) := measurableSet_Icc

/-- Off the enlargement, `η` vanishes on an open set, so its Fréchet derivative
is zero. -/
theorem coreCutoff_fderiv_eq_zero_of_notMem (hℓ : 0 < ℓ) (σ : Vec d) (k : Fin d → ℤ)
    {x : Vec d} (hx : x ∉ coreEnlarge ℓ σ k) :
    fderiv ℝ (coreCutoff ℓ σ k) x = 0 := by
  have hopen : IsOpen (coreEnlarge ℓ σ k)ᶜ := (isClosed_Icc).isOpen_compl
  have hmem : (coreEnlarge ℓ σ k)ᶜ ∈ nhds x := hopen.mem_nhds hx
  have heq : coreCutoff ℓ σ k =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [hmem] with y hy
    exact boxCutoff_eq_zero hℓ hy
  rw [heq.fderiv_eq, fderiv_const_apply]

/-- The squared gradient vanishes off the enlargement. -/
theorem coreCutoff_sqGrad_eq_zero_of_notMem (hℓ : 0 < ℓ) (σ : Vec d) (k : Fin d → ℤ)
    {x : Vec d} (hx : x ∉ coreEnlarge ℓ σ k) :
    (∑ i, (fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)) ^ 2) = 0 := by
  rw [coreCutoff_fderiv_eq_zero_of_notMem hℓ σ k hx]
  simp

/-! ## The two integral estimates -/

/-- Volume of the closed enlargement, as a real number: `(3ℓ − 2)^d`. -/
theorem volume_coreEnlarge_toReal (hℓ : 2 ≤ ℓ) (σ : Vec d) (k : Fin d → ℤ) :
    (volume (coreEnlarge ℓ σ k)).toReal = (3 * ℓ - 2) ^ d := by
  have hpos : (0 : ℝ) ≤ 3 * ℓ - 2 := by linarith
  rw [coreEnlarge, Real.volume_Icc_pi]
  rw [ENNReal.toReal_prod]
  have hterm : ∀ i : Fin d,
      (ENNReal.ofReal ((coreHi ℓ σ k i + ℓ) - (coreLo ℓ σ k i - ℓ))).toReal = 3 * ℓ - 2 := by
    intro i
    have := coreHi_sub_coreLo ℓ σ k i
    rw [ENNReal.toReal_ofReal (by linarith)]
    linarith
  rw [Finset.prod_congr rfl (fun i _ => hterm i)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Support-volume bound.**  `(vol (supp η ∩ U)).toReal ≤ (3ℓ)^d` for any set `U`. -/
theorem coreCutoff_support_volume_le (hℓ : 4 ≤ ℓ) (σ : Vec d) (k : Fin d → ℤ)
    (U : Set (Vec d)) :
    (volume (Function.support (coreCutoff ℓ σ k) ∩ U)).toReal ≤ (3 * ℓ) ^ d := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hle : coreLo ℓ σ k ≤ coreHi ℓ σ k := coreLo_le_coreHi (by linarith) σ k
  have hsub : Function.support (coreCutoff ℓ σ k) ∩ U ⊆ coreEnlarge ℓ σ k := by
    intro x hx
    by_contra hxn
    have : coreCutoff ℓ σ k x = 0 := boxCutoff_eq_zero hℓ0 hxn
    exact hx.1 this
  have hmono : volume (Function.support (coreCutoff ℓ σ k) ∩ U) ≤ volume (coreEnlarge ℓ σ k) :=
    measure_mono hsub
  have hfin : volume (coreEnlarge ℓ σ k) ≠ (⊤ : ENNReal) := by
    rw [coreEnlarge, Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
  calc (volume (Function.support (coreCutoff ℓ σ k) ∩ U)).toReal
      ≤ (volume (coreEnlarge ℓ σ k)).toReal := ENNReal.toReal_mono hfin hmono
    _ = (3 * ℓ - 2) ^ d := volume_coreEnlarge_toReal (by linarith) σ k
    _ ≤ (3 * ℓ) ^ d := by
        gcongr
        · linarith
        · linarith

/-- The squared gradient, as a function. -/
noncomputable def coreSqGrad (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) : Vec d → ℝ :=
  fun x => ∑ i, (fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)) ^ 2

theorem coreSqGrad_nonneg (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) (x : Vec d) :
    0 ≤ coreSqGrad ℓ σ k x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem continuous_coreSqGrad (ℓ : ℝ) (σ : Vec d) (k : Fin d → ℤ) :
    Continuous (coreSqGrad ℓ σ k) := by
  have hf : Continuous (fderiv ℝ (coreCutoff ℓ σ k)) :=
    (coreCutoff_contDiff ℓ σ k).continuous_fderiv (by simp)
  refine continuous_finsetSum _ (fun i _ => ?_)
  exact (hf.clm_apply continuous_const).pow 2

/-- The squared gradient is supported in the closed enlargement, hence globally
integrable. -/
theorem integrable_coreSqGrad (hℓ : 4 ≤ ℓ) (σ : Vec d) (k : Fin d → ℤ) :
    Integrable (coreSqGrad ℓ σ k) := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hEmeas : MeasurableSet (coreEnlarge ℓ σ k) := measurableSet_coreEnlarge ℓ σ k
  have hIntOn : IntegrableOn (coreSqGrad ℓ σ k) (coreEnlarge ℓ σ k) :=
    (continuous_coreSqGrad ℓ σ k).continuousOn.integrableOn_compact
      (isCompact_Icc (a := fun i => coreLo ℓ σ k i - ℓ) (b := fun i => coreHi ℓ σ k i + ℓ))
  have hg_eq : coreSqGrad ℓ σ k = (coreEnlarge ℓ σ k).indicator (coreSqGrad ℓ σ k) := by
    funext x
    by_cases hx : x ∈ coreEnlarge ℓ σ k
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact coreCutoff_sqGrad_eq_zero_of_notMem hℓ0 σ k hx
  rw [hg_eq]
  exact (integrable_indicator_iff hEmeas).2 hIntOn

/-- **Squared-gradient integral bound.**  `∫_U Σᵢ (∂ᵢ η)² ≤ d · (16/ℓ)² · (3ℓ)^d`. -/
theorem coreCutoff_sqGrad_integral_le (hℓ : 4 ≤ ℓ) (σ : Vec d) (k : Fin d → ℤ)
    (U : Set (Vec d)) :
    (∫ x in U, ∑ i, (fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)) ^ 2)
      ≤ (d : ℝ) * (16 / ℓ) ^ 2 * (3 * ℓ) ^ d := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hEmeas : MeasurableSet (coreEnlarge ℓ σ k) := measurableSet_coreEnlarge ℓ σ k
  have hInt : Integrable (coreSqGrad ℓ σ k) := integrable_coreSqGrad hℓ σ k
  have hIntOn : IntegrableOn (coreSqGrad ℓ σ k) (coreEnlarge ℓ σ k) :=
    hInt.integrableOn
  set C : ℝ := (d : ℝ) * (16 / ℓ) ^ 2 with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  -- restrict ≤ global
  have h1 : (∫ x in U, coreSqGrad ℓ σ k x) ≤ ∫ x, coreSqGrad ℓ σ k x :=
    setIntegral_le_integral hInt (ae_of_all _ (coreSqGrad_nonneg ℓ σ k))
  -- global = integral over the enlargement
  have hg_eq : coreSqGrad ℓ σ k = (coreEnlarge ℓ σ k).indicator (coreSqGrad ℓ σ k) := by
    funext x
    by_cases hx : x ∈ coreEnlarge ℓ σ k
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact coreCutoff_sqGrad_eq_zero_of_notMem hℓ0 σ k hx
  have h2 : (∫ x, coreSqGrad ℓ σ k x) = ∫ x in coreEnlarge ℓ σ k, coreSqGrad ℓ σ k x := by
    conv_lhs => rw [hg_eq]
    exact integral_indicator hEmeas
  have hfin : volume (coreEnlarge ℓ σ k) ≠ (⊤ : ENNReal) := by
    simp only [coreEnlarge, Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
  -- pointwise bound by `C` on the enlargement
  have h3 : (∫ x in coreEnlarge ℓ σ k, coreSqGrad ℓ σ k x)
      ≤ ∫ _x in coreEnlarge ℓ σ k, C := by
    refine setIntegral_mono_on hIntOn (integrableOn_const hfin) hEmeas
      (fun x _ => ?_)
    exact boxCutoff_sq_grad_bound hℓ0 x
  have h4 : (∫ _x in coreEnlarge ℓ σ k, C) = (volume (coreEnlarge ℓ σ k)).toReal * C := by
    rw [setIntegral_const, smul_eq_mul]; rfl
  have h5 : (volume (coreEnlarge ℓ σ k)).toReal = (3 * ℓ - 2) ^ d :=
    volume_coreEnlarge_toReal (by linarith) σ k
  have h6 : (3 * ℓ - 2) ^ d * C ≤ (3 * ℓ) ^ d * C := by
    apply mul_le_mul_of_nonneg_right _ hC0
    gcongr
    · linarith
    · linarith
  calc (∫ x in U, ∑ i, (fderiv ℝ (coreCutoff ℓ σ k) x (basisVec i)) ^ 2)
      = ∫ x in U, coreSqGrad ℓ σ k x := rfl
    _ ≤ ∫ x, coreSqGrad ℓ σ k x := h1
    _ = ∫ x in coreEnlarge ℓ σ k, coreSqGrad ℓ σ k x := h2
    _ ≤ ∫ _x in coreEnlarge ℓ σ k, C := h3
    _ = (volume (coreEnlarge ℓ σ k)).toReal * C := h4
    _ = (3 * ℓ - 2) ^ d * C := by rw [h5]
    _ ≤ (3 * ℓ) ^ d * C := h6
    _ = C * (3 * ℓ) ^ d := by ring
    _ = (d : ℝ) * (16 / ℓ) ^ 2 * (3 * ℓ) ^ d := by rw [hCdef]

end Homogenization
