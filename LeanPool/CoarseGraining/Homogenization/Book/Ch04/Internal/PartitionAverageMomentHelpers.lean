/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageFluctuations
import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.Corollaries

/-! # Partition Average Moment Helpers -/

namespace Homogenization

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** `L^p` / `eLpNorm` and root-comparison helper lemmas
that transport integrability and `|·|^p` integrals along `Measure.map`
equalities and through a.e. translations. These are the algebraic
substrate underneath the centered descendant-average finite-moment bounds.

**Consumed by:** `Theorems/PartitionAverageMoments/Rosenthal.lean`
(`integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_descendantsAtScale_of_restrictionUnitRangeDependentLaw`
and the public Rosenthal-type endpoints it feeds).

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

theorem integrable_abs_pow_of_map_eq_map
    {d : ℕ} {P : MeasureTheory.Measure (RegCoeffField d)}
    {f g : RegCoeffField d → ℝ} {p : ℕ}
    (hf : Measurable f) (hg : Measurable g)
    (hmap : MeasureTheory.Measure.map f P = MeasureTheory.Measure.map g P)
    (hg_int : MeasureTheory.Integrable (fun a => |g a| ^ p) P) :
    MeasureTheory.Integrable (fun a => |f a| ^ p) P := by
  let φ : ℝ → ℝ := fun x => |x| ^ p
  have hφ_aesm_f :
      MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.Measure.map f P) := by
    exact (continuous_abs.measurable.pow_const p).aemeasurable.aestronglyMeasurable
  have hφ_aesm_g :
      MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.Measure.map g P) := by
    exact (continuous_abs.measurable.pow_const p).aemeasurable.aestronglyMeasurable
  have hφ_int_g : MeasureTheory.Integrable φ (MeasureTheory.Measure.map g P) := by
    exact (MeasureTheory.integrable_map_measure hφ_aesm_g hg.aemeasurable).mpr
      (by simpa [φ] using! hg_int)
  have hφ_int_f : MeasureTheory.Integrable φ (MeasureTheory.Measure.map f P) := by
    simpa [hmap] using! hφ_int_g
  exact (MeasureTheory.integrable_map_measure hφ_aesm_f hf.aemeasurable).mp
    (by simpa [φ] using! hφ_int_f)

/-- A.e.-measurable version of `integrable_abs_pow_of_map_eq_map`. -/
theorem integrable_abs_pow_of_map_eq_map_aemeasurable
    {d : ℕ} {P : MeasureTheory.Measure (RegCoeffField d)}
    {f g : RegCoeffField d → ℝ} {p : ℕ}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hmap : MeasureTheory.Measure.map f P = MeasureTheory.Measure.map g P)
    (hg_int : MeasureTheory.Integrable (fun a => |g a| ^ p) P) :
    MeasureTheory.Integrable (fun a => |f a| ^ p) P := by
  let φ : ℝ → ℝ := fun x => |x| ^ p
  have hφ_aesm_f :
      MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.Measure.map f P) := by
    exact (continuous_abs.measurable.pow_const p).aemeasurable.aestronglyMeasurable
  have hφ_aesm_g :
      MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.Measure.map g P) := by
    exact (continuous_abs.measurable.pow_const p).aemeasurable.aestronglyMeasurable
  have hφ_int_g : MeasureTheory.Integrable φ (MeasureTheory.Measure.map g P) := by
    exact (MeasureTheory.integrable_map_measure hφ_aesm_g hg).mpr
      (by simpa [φ] using! hg_int)
  have hφ_int_f : MeasureTheory.Integrable φ (MeasureTheory.Measure.map f P) := by
    simpa [hmap] using! hφ_int_g
  exact (MeasureTheory.integrable_map_measure hφ_aesm_f hf).mp
    (by simpa [φ] using! hφ_int_f)

theorem integral_abs_pow_eq_of_map_eq_map
    {d : ℕ} {P : MeasureTheory.Measure (RegCoeffField d)}
    {f g : RegCoeffField d → ℝ} {p : ℕ}
    (hf : Measurable f) (hg : Measurable g)
    (hmap : MeasureTheory.Measure.map f P = MeasureTheory.Measure.map g P) :
    ∫ a, |f a| ^ p ∂P = ∫ a, |g a| ^ p ∂P := by
  have hφ_aesm_f :
      MeasureTheory.AEStronglyMeasurable (fun x : ℝ => |x| ^ p)
        (MeasureTheory.Measure.map f P) := by
    exact (continuous_abs.measurable.pow_const p).aemeasurable.aestronglyMeasurable
  have hφ_aesm_g :
      MeasureTheory.AEStronglyMeasurable (fun x : ℝ => |x| ^ p)
        (MeasureTheory.Measure.map g P) := by
    exact (continuous_abs.measurable.pow_const p).aemeasurable.aestronglyMeasurable
  calc
    ∫ a, |f a| ^ p ∂P = ∫ x, |x| ^ p ∂MeasureTheory.Measure.map f P := by
      symm
      rw [MeasureTheory.integral_map hf.aemeasurable hφ_aesm_f]
    _ = ∫ x, |x| ^ p ∂MeasureTheory.Measure.map g P := by
      rw [hmap]
    _ = ∫ a, |g a| ^ p ∂P := by
      rw [MeasureTheory.integral_map hg.aemeasurable hφ_aesm_g]

/-- A.e.-measurable version of `integral_abs_pow_eq_of_map_eq_map`. -/
theorem integral_abs_pow_eq_of_map_eq_map_aemeasurable
    {d : ℕ} {P : MeasureTheory.Measure (RegCoeffField d)}
    {f g : RegCoeffField d → ℝ} {p : ℕ}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hmap : MeasureTheory.Measure.map f P = MeasureTheory.Measure.map g P) :
    ∫ a, |f a| ^ p ∂P = ∫ a, |g a| ^ p ∂P := by
  have hφ_aesm_f :
      MeasureTheory.AEStronglyMeasurable (fun x : ℝ => |x| ^ p)
        (MeasureTheory.Measure.map f P) := by
    exact (continuous_abs.measurable.pow_const p).aemeasurable.aestronglyMeasurable
  have hφ_aesm_g :
      MeasureTheory.AEStronglyMeasurable (fun x : ℝ => |x| ^ p)
        (MeasureTheory.Measure.map g P) := by
    exact (continuous_abs.measurable.pow_const p).aemeasurable.aestronglyMeasurable
  calc
    ∫ a, |f a| ^ p ∂P = ∫ x, |x| ^ p ∂MeasureTheory.Measure.map f P := by
      symm
      rw [MeasureTheory.integral_map hf hφ_aesm_f]
    _ = ∫ x, |x| ^ p ∂MeasureTheory.Measure.map g P := by
      rw [hmap]
    _ = ∫ a, |g a| ^ p ∂P := by
      rw [MeasureTheory.integral_map hg hφ_aesm_g]

theorem integral_abs_pow_rpow_inv_le_iff_of_map_eq_map
    {d : ℕ} {P : MeasureTheory.Measure (RegCoeffField d)}
    {f g : RegCoeffField d → ℝ} {p : ℕ} {K : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hmap : MeasureTheory.Measure.map f P = MeasureTheory.Measure.map g P) :
    ((∫ a, |f a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K ↔
      (∫ a, |g a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K) := by
  rw [integral_abs_pow_eq_of_map_eq_map hf hg hmap]

theorem toReal_eLpNorm_eq_integral_abs_pow_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {f : Ω → ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hf : Measurable f)
    (hLp_int : MeasureTheory.Integrable (fun ω => |f ω| ^ p) μ) :
    ENNReal.toReal (MeasureTheory.eLpNorm f p μ) =
      (∫ ω, |f ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_nat_ne_zero : p ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp)
  have h_memLp : MeasureTheory.MemLp f (p : ENNReal) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff
      hf.aestronglyMeasurable (by exact_mod_cast hp_nat_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hLp_int
  have hnonneg :
      0 ≤ (∫ a, ‖f a‖ ^ (p : ENNReal).toReal ∂μ) ^ (p : ENNReal).toReal⁻¹ := by
    positivity
  rw [h_memLp.eLpNorm_eq_integral_rpow_norm
      (by exact_mod_cast hp_nat_ne_zero) (by simp),
    ENNReal.toReal_ofReal hnonneg]
  simp [Real.norm_eq_abs, one_div]

/-- A.e.-measurable version of
`toReal_eLpNorm_eq_integral_abs_pow_rpow_inv`. -/
theorem toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {f : Ω → ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hf : AEMeasurable f μ)
    (hLp_int : MeasureTheory.Integrable (fun ω => |f ω| ^ p) μ) :
    ENNReal.toReal (MeasureTheory.eLpNorm f p μ) =
      (∫ ω, |f ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_nat_ne_zero : p ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp)
  have h_memLp : MeasureTheory.MemLp f (p : ENNReal) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff
      hf.aestronglyMeasurable (by exact_mod_cast hp_nat_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hLp_int
  have hnonneg :
      0 ≤ (∫ a, ‖f a‖ ^ (p : ENNReal).toReal ∂μ) ^ (p : ENNReal).toReal⁻¹ := by
    positivity
  rw [h_memLp.eLpNorm_eq_integral_rpow_norm
      (by exact_mod_cast hp_nat_ne_zero) (by simp),
    ENNReal.toReal_ofReal hnonneg]
  simp [Real.norm_eq_abs, one_div]

theorem integral_abs_finsetSum_pow_rpow_inv_le_sum
    {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω}
    {f : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hp : 1 ≤ p)
    (h_meas : ∀ i ∈ s, Measurable (f i))
    (hLp_int : ∀ i ∈ s, MeasureTheory.Integrable (fun ω => |f i ω| ^ p) μ) :
    (∫ ω, |∑ i ∈ s, f i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      ∑ i ∈ s, (∫ ω, |f i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_nat_ne_zero : p ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp)
  let g : Ω → ℝ := fun a => ∑ i ∈ s, f i a
  have hg_meas : Measurable g := by
    simpa [g] using Finset.measurable_sum s (fun i hi => h_meas i hi)
  have h_memLp :
      ∀ i ∈ s, MeasureTheory.MemLp (f i) (p : ENNReal) μ := by
    intro i hi
    refine (MeasureTheory.integrable_norm_rpow_iff
      (h_meas i hi).aestronglyMeasurable
      (by exact_mod_cast hp_nat_ne_zero) (by simp)).1 ?_
    simpa [Real.norm_eq_abs] using hLp_int i hi
  have hg_memLp : MeasureTheory.MemLp g (p : ENNReal) μ := by
    simpa [g] using MeasureTheory.memLp_finsetSum s h_memLp
  have hg_eq : g = ∑ i ∈ s, f i := by
    funext a
    simp [g]
  have hg_int :
      MeasureTheory.Integrable (fun ω => |g ω| ^ p) μ := by
    simpa [g, Real.norm_eq_abs] using hg_memLp.integrable_norm_pow
      (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp))
  have hg_eLp :
      MeasureTheory.eLpNorm g (p : ENNReal) μ ≤
        ∑ i ∈ s, MeasureTheory.eLpNorm (f i) (p : ENNReal) μ := by
    have hp_ennreal : (1 : ENNReal) ≤ (p : ENNReal) := by
      exact_mod_cast hp
    rw [hg_eq]
    exact
      MeasureTheory.eLpNorm_sum_le
        (μ := μ) (s := s) (f := f)
        (fun i hi => (h_meas i hi).aestronglyMeasurable)
        hp_ennreal
  have hg_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm g (p : ENNReal) μ) =
        (∫ ω, |g ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv hp hg_meas hg_int
  have hg_toReal_le :
      ENNReal.toReal (MeasureTheory.eLpNorm g (p : ENNReal) μ) ≤
        ENNReal.toReal (∑ i ∈ s, MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) := by
    exact ENNReal.toReal_mono
      (ENNReal.sum_ne_top.2 fun i hi => (h_memLp i hi).2.ne) hg_eLp
  have hsum_rhs :
      ENNReal.toReal (∑ i ∈ s, MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) =
        ∑ i ∈ s, ENNReal.toReal (MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) := by
    exact ENNReal.toReal_sum (fun i hi => (h_memLp i hi).2.ne)
  have hterm :
      ∀ i ∈ s,
        ENNReal.toReal (MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) =
          (∫ ω, |f i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
    intro i hi
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv hp (h_meas i hi) (hLp_int i hi)
  calc
    (∫ ω, |∑ i ∈ s, f i ω| ^ p ∂μ) ^ (1 / (p : ℝ))
        = (∫ ω, |g ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
          simp [g]
    _ = ENNReal.toReal (MeasureTheory.eLpNorm g (p : ENNReal) μ) := by
          rw [hg_toReal]
    _ ≤ ENNReal.toReal (∑ i ∈ s, MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) := hg_toReal_le
    _ = ∑ i ∈ s, ENNReal.toReal (MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) := hsum_rhs
    _ = ∑ i ∈ s, (∫ ω, |f i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i hi

/-- A.e.-measurable finite-sum root triangle inequality. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_sum_aemeasurable
    {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω}
    {f : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hp : 1 ≤ p)
    (h_aemeas : ∀ i ∈ s, AEMeasurable (f i) μ)
    (hLp_int : ∀ i ∈ s, MeasureTheory.Integrable (fun ω => |f i ω| ^ p) μ) :
    (∫ ω, |∑ i ∈ s, f i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      ∑ i ∈ s, (∫ ω, |f i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_nat_ne_zero : p ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp)
  let g : Ω → ℝ := fun a => ∑ i ∈ s, f i a
  have hg_aemeas : AEMeasurable g μ := by
    have hsum : AEMeasurable (∑ i ∈ s, f i) μ :=
      Finset.aemeasurable_sum s h_aemeas
    convert hsum using 1
    ext a
    simp [g]
  have h_memLp :
      ∀ i ∈ s, MeasureTheory.MemLp (f i) (p : ENNReal) μ := by
    intro i hi
    refine (MeasureTheory.integrable_norm_rpow_iff
      (h_aemeas i hi).aestronglyMeasurable
      (by exact_mod_cast hp_nat_ne_zero) (by simp)).1 ?_
    simpa [Real.norm_eq_abs] using hLp_int i hi
  have hg_memLp : MeasureTheory.MemLp g (p : ENNReal) μ := by
    simpa [g] using MeasureTheory.memLp_finsetSum s h_memLp
  have hg_eq : g = ∑ i ∈ s, f i := by
    funext a
    simp [g]
  have hg_int :
      MeasureTheory.Integrable (fun ω => |g ω| ^ p) μ := by
    simpa [g, Real.norm_eq_abs] using hg_memLp.integrable_norm_pow
      (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp))
  have hg_eLp :
      MeasureTheory.eLpNorm g (p : ENNReal) μ ≤
        ∑ i ∈ s, MeasureTheory.eLpNorm (f i) (p : ENNReal) μ := by
    have hp_ennreal : (1 : ENNReal) ≤ (p : ENNReal) := by
      exact_mod_cast hp
    rw [hg_eq]
    exact
      MeasureTheory.eLpNorm_sum_le
        (μ := μ) (s := s) (f := f)
        (fun i hi => (h_aemeas i hi).aestronglyMeasurable)
        hp_ennreal
  have hg_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm g (p : ENNReal) μ) =
        (∫ ω, |g ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable
      hp hg_aemeas hg_int
  have hg_toReal_le :
      ENNReal.toReal (MeasureTheory.eLpNorm g (p : ENNReal) μ) ≤
        ENNReal.toReal (∑ i ∈ s, MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) := by
    exact ENNReal.toReal_mono
      (ENNReal.sum_ne_top.2 fun i hi => (h_memLp i hi).2.ne) hg_eLp
  have hsum_rhs :
      ENNReal.toReal (∑ i ∈ s, MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) =
        ∑ i ∈ s, ENNReal.toReal (MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) := by
    exact ENNReal.toReal_sum (fun i hi => (h_memLp i hi).2.ne)
  have hterm :
      ∀ i ∈ s,
        ENNReal.toReal (MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) =
          (∫ ω, |f i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
    intro i hi
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable
      hp (h_aemeas i hi) (hLp_int i hi)
  calc
    (∫ ω, |∑ i ∈ s, f i ω| ^ p ∂μ) ^ (1 / (p : ℝ))
        = (∫ ω, |g ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
          simp [g]
    _ = ENNReal.toReal (MeasureTheory.eLpNorm g (p : ENNReal) μ) := by
          rw [hg_toReal]
    _ ≤ ENNReal.toReal (∑ i ∈ s, MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) := hg_toReal_le
    _ = ∑ i ∈ s, ENNReal.toReal (MeasureTheory.eLpNorm (f i) (p : ENNReal) μ) := hsum_rhs
    _ = ∑ i ∈ s, (∫ ω, |f i ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i hi

theorem integral_abs_sq_rpow_half_le_integral_abs_pow_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {f : Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (hf : Measurable f)
    (hLp_int : MeasureTheory.Integrable (fun ω => |f ω| ^ p) μ) :
    (∫ ω, |f ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) ≤
      (∫ ω, |f ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_ne_zero : p ≠ 0 := by omega
  have hf_ae : MeasureTheory.AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have h_memLp_p : MeasureTheory.MemLp f (p : ENNReal) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff
      hf_ae (by exact_mod_cast hp_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hLp_int
  have h_memLp_two : MeasureTheory.MemLp f (2 : ENNReal) μ := by
    exact h_memLp_p.mono_exponent (by exact_mod_cast hp)
  have hcmp :
      MeasureTheory.eLpNorm f (2 : ENNReal) μ ≤
        MeasureTheory.eLpNorm f (p : ENNReal) μ := by
    exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (μ := μ) (f := f) (by exact_mod_cast hp) hf_ae
  rw [h_memLp_two.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp),
    h_memLp_p.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hp_ne_zero) (by simp)] at hcmp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (by
    simpa [Real.norm_eq_abs, one_div] using hcmp)

/-- A.e.-measurable version of
`integral_abs_sq_rpow_half_le_integral_abs_pow_rpow_inv`. -/
theorem integral_abs_sq_rpow_half_le_integral_abs_pow_rpow_inv_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {f : Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (hf : AEMeasurable f μ)
    (hLp_int : MeasureTheory.Integrable (fun ω => |f ω| ^ p) μ) :
    (∫ ω, |f ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) ≤
      (∫ ω, |f ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_ne_zero : p ≠ 0 := by omega
  have hf_ae : MeasureTheory.AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have h_memLp_p : MeasureTheory.MemLp f (p : ENNReal) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff
      hf_ae (by exact_mod_cast hp_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hLp_int
  have h_memLp_two : MeasureTheory.MemLp f (2 : ENNReal) μ := by
    exact h_memLp_p.mono_exponent (by exact_mod_cast hp)
  have hcmp :
      MeasureTheory.eLpNorm f (2 : ENNReal) μ ≤
        MeasureTheory.eLpNorm f (p : ENNReal) μ := by
    exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (μ := μ) (f := f) (by exact_mod_cast hp) hf_ae
  rw [h_memLp_two.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp),
    h_memLp_p.eLpNorm_eq_integral_rpow_norm (by exact_mod_cast hp_ne_zero) (by simp)] at hcmp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (by
    simpa [Real.norm_eq_abs, one_div] using hcmp)

theorem integral_abs_le_integral_abs_sq_rpow_half
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    (hf : Measurable f)
    (hL2_int : MeasureTheory.Integrable (fun ω => |f ω| ^ (2 : ℕ)) μ) :
    ∫ ω, |f ω| ∂μ ≤ (∫ ω, |f ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) := by
  have hf_ae : MeasureTheory.AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have h_memLp_two : MeasureTheory.MemLp f (2 : ENNReal) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hf_ae (by norm_num) (by simp)]
    simpa [Real.norm_eq_abs] using hL2_int
  have h_memLp_one : MeasureTheory.MemLp f (1 : ENNReal) μ := by
    exact h_memLp_two.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)
  have hcmp :
      MeasureTheory.eLpNorm f (1 : ENNReal) μ ≤
        MeasureTheory.eLpNorm f (2 : ENNReal) μ := by
    exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (μ := μ) (f := f) (by norm_num : (1 : ENNReal) ≤ 2) hf_ae
  have hL1_int_f : MeasureTheory.Integrable f μ := by
    rwa [MeasureTheory.memLp_one_iff_integrable] at h_memLp_one
  have hL1_int : MeasureTheory.Integrable (fun ω => |f ω|) μ := by
    simpa [Real.norm_eq_abs] using hL1_int_f.norm
  have hL1_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm f (1 : ENNReal) μ) = ∫ ω, |f ω| ∂μ := by
    calc
      ENNReal.toReal (MeasureTheory.eLpNorm f (1 : ENNReal) μ)
          = (∫ ω, |f ω| ^ (1 : ℕ) ∂μ) ^ (1 / (1 : ℝ)) := by
              simpa using
                (toReal_eLpNorm_eq_integral_abs_pow_rpow_inv
                  (μ := μ) (f := f) (p := 1) (show 1 ≤ (1 : ℕ) by norm_num)
                  hf (by simpa using hL1_int))
      _ = ∫ ω, |f ω| ∂μ := by simp
  have hL2_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm f (2 : ENNReal) μ) =
        (∫ ω, |f ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) := by
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv (show 1 ≤ (2 : ℕ) by norm_num)
      hf hL2_int
  have hcmp_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm f (1 : ENNReal) μ) ≤
        ENNReal.toReal (MeasureTheory.eLpNorm f (2 : ENNReal) μ) := by
    exact ENNReal.toReal_mono h_memLp_two.2.ne hcmp
  simpa [hL1_toReal, hL2_toReal] using hcmp_toReal

/-- A.e.-measurable version of
`integral_abs_le_integral_abs_sq_rpow_half`. -/
theorem integral_abs_le_integral_abs_sq_rpow_half_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {f : Ω → ℝ}
    (hf : AEMeasurable f μ)
    (hL2_int : MeasureTheory.Integrable (fun ω => |f ω| ^ (2 : ℕ)) μ) :
    ∫ ω, |f ω| ∂μ ≤ (∫ ω, |f ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) := by
  have hf_ae : MeasureTheory.AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have h_memLp_two : MeasureTheory.MemLp f (2 : ENNReal) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hf_ae (by norm_num) (by simp)]
    simpa [Real.norm_eq_abs] using hL2_int
  have h_memLp_one : MeasureTheory.MemLp f (1 : ENNReal) μ := by
    exact h_memLp_two.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)
  have hcmp :
      MeasureTheory.eLpNorm f (1 : ENNReal) μ ≤
        MeasureTheory.eLpNorm f (2 : ENNReal) μ := by
    exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (μ := μ) (f := f) (by norm_num : (1 : ENNReal) ≤ 2) hf_ae
  have hL1_int_f : MeasureTheory.Integrable f μ := by
    rwa [MeasureTheory.memLp_one_iff_integrable] at h_memLp_one
  have hL1_int : MeasureTheory.Integrable (fun ω => |f ω|) μ := by
    simpa [Real.norm_eq_abs] using hL1_int_f.norm
  have hL1_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm f (1 : ENNReal) μ) = ∫ ω, |f ω| ∂μ := by
    calc
      ENNReal.toReal (MeasureTheory.eLpNorm f (1 : ENNReal) μ)
          = (∫ ω, |f ω| ^ (1 : ℕ) ∂μ) ^ (1 / (1 : ℝ)) := by
              simpa using
                (toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable
                  (μ := μ) (f := f) (p := 1) (show 1 ≤ (1 : ℕ) by norm_num)
                  hf (by simpa using hL1_int))
      _ = ∫ ω, |f ω| ∂μ := by simp
  have hL2_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm f (2 : ENNReal) μ) =
        (∫ ω, |f ω| ^ (2 : ℕ) ∂μ) ^ (1 / (2 : ℝ)) := by
    exact toReal_eLpNorm_eq_integral_abs_pow_rpow_inv_aemeasurable
      (show 1 ≤ (2 : ℕ) by norm_num) hf hL2_int
  have hcmp_toReal :
      ENNReal.toReal (MeasureTheory.eLpNorm f (1 : ENNReal) μ) ≤
        ENNReal.toReal (MeasureTheory.eLpNorm f (2 : ENNReal) μ) := by
    exact ENNReal.toReal_mono h_memLp_two.2.ne hcmp
  simpa [hL1_toReal, hL2_toReal] using hcmp_toReal

theorem sum_rpow_inv_le_card_rpow_mul_rpow_sum
    {ι : Type*} {s : Finset ι} {p : ℕ} {f : ι → ℝ}
    (hp : 1 ≤ p)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ (1 / (p : ℝ)) ≤
      (s.card : ℝ) ^ (1 - 1 / (p : ℝ)) * (∑ i ∈ s, f i) ^ (1 / (p : ℝ)) := by
  have hp_real : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  let g : ι → ℝ := fun i => (max (f i) 0) ^ (1 / (p : ℝ))
  have hp_nat_ne_zero : p ≠ 0 := by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one hp)
  have hp_real_ne_zero : (p : ℝ) ≠ 0 := by
    exact_mod_cast hp_nat_ne_zero
  have hroot :=
    Real.inner_le_weight_mul_Lp_of_nonneg
      (s := s) (p := (p : ℝ)) hp_real
      (w := fun _ => (1 : ℝ))
      (f := g)
      (fun _ => by positivity)
      (fun i => Real.rpow_nonneg (le_max_right _ _) _)
  have hleft :
      ∑ i ∈ s, (fun _ => (1 : ℝ)) i * g i = ∑ i ∈ s, f i ^ (1 / (p : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [g, max_eq_left (hf i hi)]
  have hright :
      ∑ i ∈ s, (fun _ => (1 : ℝ)) i * g i ^ (p : ℝ) = ∑ i ∈ s, f i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp only [one_mul]
    dsimp [g]
    rw [max_eq_left (hf i hi), ← Real.rpow_mul (hf i hi)]
    have : (1 / (p : ℝ)) * p = 1 := by
      field_simp [hp_real_ne_zero]
    rw [this, Real.rpow_one]
  calc
    ∑ i ∈ s, f i ^ (1 / (p : ℝ))
        = ∑ i ∈ s, (fun _ => (1 : ℝ)) i * g i := by simpa using hleft.symm
    _ ≤ (∑ i ∈ s, (fun _ => (1 : ℝ)) i) ^ (1 - (p : ℝ)⁻¹) *
          (∑ i ∈ s, (fun _ => (1 : ℝ)) i * g i ^ (p : ℝ)) ^ ((p : ℝ)⁻¹) := hroot
    _ = (s.card : ℝ) ^ (1 - 1 / (p : ℝ)) * (∑ i ∈ s, f i) ^ (1 / (p : ℝ)) := by
          rw [hright]
          simp



end Homogenization
