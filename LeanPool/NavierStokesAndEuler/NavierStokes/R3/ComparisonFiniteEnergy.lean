/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.ComparisonSetup
public import LeanPool.NavierStokesAndEuler.NavierStokes.R3.LpNormTools

@[expose] public section

/-!
# Finite-energy bounds for whole-space comparison

The hypotheses in this module concern only square integrability and
measurability. In particular, the comparison field need not have compact
support or any globally bounded derivative.
-/


noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace NavierStokesR3.Comparison

open ProblemStatement

/-- The explicit square-integrability condition is the usual `MemLp` condition
once measurability of the velocity slice is known. -/
theorem squareIntegrableAtTime_iff_memLp {u : VelocityField} {t : ℝ}
    (hu : AEStronglyMeasurable (fun x : Space => u (t, x)) volume) :
    SquareIntegrableAtTime u t ↔ MemLp (fun x : Space => u (t, x)) 2 volume :=
  (memLp_two_iff_integrable_sq_norm hu).symm

/-- Joint continuity on a time slab gives continuity of every spatial slice,
including a boundary time. -/
theorem continuous_slice_of_continuousOn {times : Set ℝ} {u : VelocityField}
    (hu : ContinuousOn u (times ×ˢ univ)) {t : ℝ} (ht : t ∈ times) :
    Continuous (fun x : Space => u (t, x)) := by
  have hc : ContinuousOn (fun x : Space => u (t, x)) univ :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun x _ => ⟨ht, mem_univ x⟩)
  exact continuous_iff_continuousAt.2 (fun x => (hc x (mem_univ x)).continuousAt
    Filter.univ_mem)

/-- No integrability hypothesis is needed for nonnegativity of the totalized
integral defining the squared norm. -/
theorem l2Sq_nonneg {E : Type*} [NormedAddCommGroup E] (f : Space → E) :
    0 ≤ l2Sq f :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- The elementary pointwise estimate used for the difference energy. -/
theorem norm_sub_sq_le_twice {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := mul_self_le_mul_self (norm_nonneg (a - b)) (norm_sub_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- A difference of square-integrable slices remains square integrable. -/
theorem squareIntegrableAtTime_sub {u v : VelocityField} {t : ℝ}
    (hu_meas : AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv_meas : AEStronglyMeasurable (fun x : Space => v (t, x)) volume)
    (hu : SquareIntegrableAtTime u t) (hv : SquareIntegrableAtTime v t) :
    SquareIntegrableAtTime (fun z => u z - v z) t := by
  exact (squareIntegrableAtTime_iff_memLp (hu_meas.sub hv_meas)).2
    (((squareIntegrableAtTime_iff_memLp hu_meas).1 hu).sub
      ((squareIntegrableAtTime_iff_memLp hv_meas).1 hv))

/-- The squared `L²` norm of a difference is bounded by the two original
energies. -/
theorem l2Sq_sub_le {E : Type*} [NormedAddCommGroup E] {f g : Space → E}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2Sq (fun x => f x - g x) ≤ 2 * (l2Sq f + l2Sq g) := by
  have hf_sq := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hg_sq := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  have hfg_sq := (memLp_two_iff_integrable_sq_norm (hf.sub hg).1).1 (hf.sub hg)
  calc
    l2Sq (fun x => f x - g x) ≤
        ∫ x : Space, 2 * (‖f x‖ ^ 2 + ‖g x‖ ^ 2) :=
      integral_mono hfg_sq ((hf_sq.add hg_sq).const_mul 2)
        (fun x => norm_sub_sq_le_twice (f x) (g x))
    _ = 2 * (l2Sq f + l2Sq g) := by
      rw [integral_const_mul, integral_add hf_sq hg_sq]
      rfl

/-- Uniform finite energy is stable under taking the velocity difference. -/
theorem uniformFiniteEnergy_sub {times : Set ℝ} {u v : VelocityField}
    (hu_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => v (t, x)) volume)
    (hu : UniformFiniteEnergy times u) (hv : UniformFiniteEnergy times v) :
    UniformFiniteEnergy times (fun z => u z - v z) := by
  obtain ⟨Eu, hEu, hu⟩ := hu
  obtain ⟨Ev, hEv, hv⟩ := hv
  refine ⟨2 * (Eu + Ev), by positivity, ?_⟩
  intro t ht
  obtain ⟨hu_sq, hu_bound⟩ := hu t ht
  obtain ⟨hv_sq, hv_bound⟩ := hv t ht
  refine ⟨squareIntegrableAtTime_sub (hu_meas t ht) (hv_meas t ht) hu_sq hv_sq, ?_⟩
  have hdiff := l2Sq_sub_le
    ((squareIntegrableAtTime_iff_memLp (hu_meas t ht)).1 hu_sq)
    ((squareIntegrableAtTime_iff_memLp (hv_meas t ht)).1 hv_sq)
  dsimp [kineticEnergy, l2Sq] at hu_bound hv_bound hdiff ⊢
  linarith

/-- The preceding result applies to fields jointly continuous on the slab. -/
theorem uniformFiniteEnergy_sub_of_continuousOn {times : Set ℝ} {u v : VelocityField}
    (hu_cont : ContinuousOn u (times ×ˢ univ))
    (hv_cont : ContinuousOn v (times ×ˢ univ))
    (hu : UniformFiniteEnergy times u) (hv : UniformFiniteEnergy times v) :
    UniformFiniteEnergy times (fun z => u z - v z) :=
  uniformFiniteEnergy_sub
    (fun _ ht => (continuous_slice_of_continuousOn hu_cont ht).aestronglyMeasurable)
    (fun _ ht => (continuous_slice_of_continuousOn hv_cont ht).aestronglyMeasurable) hu hv

/-- A kinetic-energy bound is also a bound for the squared `L²` norm. -/
theorem uniformFiniteEnergy_l2Sq_bound {times : Set ℝ} {u : VelocityField}
    (hu : UniformFiniteEnergy times u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ times,
      SquareIntegrableAtTime u t ∧ l2Sq (fun x => u (t, x)) ≤ M := by
  obtain ⟨E, hE, hu⟩ := hu
  refine ⟨2 * E, by positivity, ?_⟩
  intro t ht
  obtain ⟨hint, hbound⟩ := hu t ht
  refine ⟨hint, ?_⟩
  dsimp [kineticEnergy, l2Sq] at hbound ⊢
  linarith

/-- Every component product is dominated by the Euclidean squared norm. -/
theorem norm_component_mul_le_sq (a : Space) (i j : Fin 3) :
    ‖a i * a j‖ ≤ ‖a‖ ^ 2 := by
  rw [norm_mul, pow_two]
  exact mul_le_mul (PiLp.norm_apply_le a i) (PiLp.norm_apply_le a j)
    (norm_nonneg _) (norm_nonneg _)

/-- Pointwise domination of the nonlinear tensor by the two energy densities. -/
theorem tensorDiff_norm_le (u v : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) :
    ‖tensorDiff u v t i j x‖ ≤ ‖u (t, x)‖ ^ 2 + ‖v (t, x)‖ ^ 2 := by
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_component_mul_le_sq (u (t, x)) i j)
      (norm_component_mul_le_sq (v (t, x)) i j))

/-- The nonlinear tensor has measurable components whenever both velocities
have measurable spatial slices. -/
theorem tensorDiff_aestronglyMeasurable {u v : VelocityField} {t : ℝ}
    (hu : AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv : AEStronglyMeasurable (fun x : Space => v (t, x)) volume) (i j : Fin 3) :
    AEStronglyMeasurable (tensorDiff u v t i j) volume := by
  have hui := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hu
  have huj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hu
  have hvi := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hv
  have hvj := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hv
  exact (hui.mul huj).sub (hvi.mul hvj)

/-- Every component of the tensor difference lies in `L¹`. -/
theorem tensorDiff_integrable {u v : VelocityField} {t : ℝ}
    (hu : MemLp (fun x : Space => u (t, x)) 2 volume)
    (hv : MemLp (fun x : Space => v (t, x)) 2 volume) (i j : Fin 3) :
    Integrable (tensorDiff u v t i j) volume := by
  have hu_sq := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv_sq := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  exact (hu_sq.add hv_sq).mono' (tensorDiff_aestronglyMeasurable hu.1 hv.1 i j)
    (ae_of_all _ (tensorDiff_norm_le u v t i j))

/-- Its `L¹` norm is bounded using only the two ordinary energies. -/
theorem tensorDiff_norm_integral_le {u v : VelocityField} {t : ℝ}
    (hu : MemLp (fun x : Space => u (t, x)) 2 volume)
    (hv : MemLp (fun x : Space => v (t, x)) 2 volume) (i j : Fin 3) :
    (∫ x : Space, ‖tensorDiff u v t i j x‖) ≤
      l2Sq (fun x => u (t, x)) + l2Sq (fun x => v (t, x)) := by
  have hu_sq := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have hv_sq := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  calc
    (∫ x : Space, ‖tensorDiff u v t i j x‖) ≤
        ∫ x : Space, ‖u (t, x)‖ ^ 2 + ‖v (t, x)‖ ^ 2 :=
      integral_mono (tensorDiff_integrable hu hv i j).norm (hu_sq.add hv_sq)
        (tensorDiff_norm_le u v t i j)
    _ = _ := integral_add hu_sq hv_sq

/-- A single `L¹` bound works for all times and all tensor components. -/
theorem uniformFiniteEnergy_tensorDiff_bound {times : Set ℝ} {u v : VelocityField}
    (hu_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => v (t, x)) volume)
    (hu : UniformFiniteEnergy times u) (hv : UniformFiniteEnergy times v) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ times, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧
        (∫ x : Space, ‖tensorDiff u v t i j x‖) ≤ M := by
  obtain ⟨Mu, hMu, hu⟩ := uniformFiniteEnergy_l2Sq_bound hu
  obtain ⟨Mv, hMv, hv⟩ := uniformFiniteEnergy_l2Sq_bound hv
  refine ⟨Mu + Mv, add_nonneg hMu hMv, ?_⟩
  intro t ht i j
  obtain ⟨hu_sq, hu_bound⟩ := hu t ht
  obtain ⟨hv_sq, hv_bound⟩ := hv t ht
  have hu_lp := (squareIntegrableAtTime_iff_memLp (hu_meas t ht)).1 hu_sq
  have hv_lp := (squareIntegrableAtTime_iff_memLp (hv_meas t ht)).1 hv_sq
  exact ⟨tensorDiff_integrable hu_lp hv_lp i j,
    (tensorDiff_norm_integral_le hu_lp hv_lp i j).trans (add_le_add hu_bound hv_bound)⟩

/-- The finite energy hypothesis gives a uniform bound for the ordinary `L²`
norm, with membership in `L²` recorded explicitly. -/
theorem uniformFiniteEnergy_lpNorm_two_bound {times : Set ℝ} {u : VelocityField}
    (hu_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hu : UniformFiniteEnergy times u) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ times,
      MemLp (fun x : Space => u (t, x)) 2 volume ∧
        comparisonLpNorm 2 (fun x => u (t, x)) ≤ M := by
  obtain ⟨M, _, hM⟩ := uniformFiniteEnergy_l2Sq_bound hu
  refine ⟨Real.sqrt M, Real.sqrt_nonneg M, ?_⟩
  intro t ht
  obtain ⟨hint, hbound⟩ := hM t ht
  have hLp := (squareIntegrableAtTime_iff_memLp (hu_meas t ht)).1 hint
  refine ⟨hLp, ?_⟩
  rw [LpNormTools.lpNorm_two_eq_sqrt_l2Sq hLp]
  exact Real.sqrt_le_sqrt hbound

/-- The uniform tensor estimate in the common `comparisonLpNorm` notation. -/
theorem uniformFiniteEnergy_tensorDiff_lpNorm_one_bound {times : Set ℝ}
    {u v : VelocityField}
    (hu_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => u (t, x)) volume)
    (hv_meas : ∀ t ∈ times,
      AEStronglyMeasurable (fun x : Space => v (t, x)) volume)
    (hu : UniformFiniteEnergy times u) (hv : UniformFiniteEnergy times v) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ times, ∀ i j : Fin 3,
      Integrable (tensorDiff u v t i j) volume ∧ comparisonLpNorm 1 (tensorDiff u v t i j) ≤ M := by
  obtain ⟨M, hM, hbound⟩ := uniformFiniteEnergy_tensorDiff_bound hu_meas hv_meas hu hv
  refine ⟨M, hM, ?_⟩
  intro t ht i j
  obtain ⟨hint, hle⟩ := hbound t ht i j
  refine ⟨hint, ?_⟩
  rwa [LpNormTools.lpNorm_one_eq_integral_norm hint]

end NavierStokesR3.Comparison
