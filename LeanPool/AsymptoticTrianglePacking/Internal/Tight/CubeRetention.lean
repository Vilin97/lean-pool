/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — the Bernoulli retention carried by the finite cube

`LeanPool.AsymptoticTrianglePacking.Internal.exists_bernoulliRetention` produces *some* probability space carrying a Bernoulli retention.
For the sharp variance bound of `LeanPool.AsymptoticTrianglePacking.Internal.Tight.SharpVariance` we need a space on which the
Efron–Stein inequality of `LeanPool.AsymptoticTrianglePacking.Internal.Tight.CubeVariance` is available, i.e. an honest product of
independent coordinates.  This file provides it: the cube `ι → Bool` with the explicit weighted
counting measure

  `cubeMeasure p = ∑_ω ofReal (wt p ω) · δ_ω`,

for which

* integrals are the elementary sums `LeanPool.AsymptoticTrianglePacking.Internal.Cube.Exp` (`LeanPool.AsymptoticTrianglePacking.Internal.integral_cubeMeasure`),
* the coordinate events are independent with probability `p` (`LeanPool.AsymptoticTrianglePacking.Internal.iIndepSet_cubeCoord`), hence
  the cube carries a `LeanPool.AsymptoticTrianglePacking.Internal.BernoulliRetention` (`LeanPool.AsymptoticTrianglePacking.Internal.cubeRetention`), and
* the Efron–Stein bound holds in integral form (`LeanPool.AsymptoticTrianglePacking.Internal.cube_centred_sq_le`).
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CubeVariance
import LeanPool.AsymptoticTrianglePacking.Internal.Covered
import LeanPool.AsymptoticTrianglePacking.Internal.Prelude

open MeasureTheory ProbabilityTheory Finset

namespace LeanPool.AsymptoticTrianglePacking.Internal

namespace Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Bernoulli(`p`) measure on the finite cube `ι → Bool`. -/
noncomputable def cubeMeasure (p : ℝ) : Measure (ι → Bool) :=
  ∑ ω : ι → Bool, ENNReal.ofReal (wt p ω) • Measure.dirac ω

/-- The finite cube as a measure space. -/
noncomputable def cubeSpace (p : ℝ) : MeasureSpace (ι → Bool) := ⟨cubeMeasure p⟩

theorem cubeMeasure_apply {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (ι → Bool)) :
    cubeMeasure p A = ENNReal.ofReal (∑ ω, wt p ω * Set.indicator A 1 ω) := by
  classical
  have hind : ∀ ω : ι → Bool, (0 : ℝ) ≤ Set.indicator A (1 : (ι → Bool) → ℝ) ω := by
    intro ω; by_cases h : ω ∈ A <;> simp [h]
  rw [cubeMeasure, Measure.coe_finset_sum]
  simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul, MeasureTheory.Measure.dirac_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun ω _ => mul_nonneg (wt_nonneg hp0 hp1 ω) (hind ω))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ENNReal.ofReal_mul (wt_nonneg hp0 hp1 ω)]
  congr 1
  by_cases h : ω ∈ A <;> simp [h]

theorem isProbabilityMeasure_cubeMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (cubeMeasure (ι := ι) p) := by
  constructor
  rw [cubeMeasure_apply hp0 hp1]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [sum_wt]
  simp

/-- Integrals against the cube measure are the elementary sums `Exp`. -/
theorem integral_cubeMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → ℝ) :
    ∫ ω, f ω ∂(cubeMeasure p) = Exp p f := by
  rw [cubeMeasure, integral_finset_sum_measure]
  · rw [Exp]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (wt_nonneg hp0 hp1 ω)]
  · intro ω _
    exact Integrable.smul_measure (integrable_dirac (by finiteness)) (by simp)

/-! ## Independence of the coordinates -/

theorem indicator_biInter_eq (S : Finset ι) (ω : ι → Bool) :
    Set.indicator (⋂ e ∈ S, {ω : ι → Bool | ω e = true}) 1 ω
      = ∏ i, (if i ∈ S then (if ω i then (1 : ℝ) else 0) else 1) := by
  classical
  by_cases h : ∀ e ∈ S, ω e = true
  · rw [Set.indicator_of_mem (by simpa using h)]
    refine (Finset.prod_eq_one ?_).symm
    intro i _
    by_cases hi : i ∈ S
    · simp [hi, h i hi]
    · simp [hi]
  · push_neg at h
    obtain ⟨e, heS, he⟩ := h
    have hnot : ω ∉ (⋂ e ∈ S, {ω : ι → Bool | ω e = true}) := by
      intro hmem
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hmem
      exact he (hmem e heS)
    rw [Set.indicator_of_notMem hnot]
    refine (Finset.prod_eq_zero (Finset.mem_univ e) ?_).symm
    simp [heS, he]

theorem Exp_indicator_biInter (p : ℝ) (S : Finset ι) :
    Exp p (fun ω => Set.indicator (⋂ e ∈ S, {ω : ι → Bool | ω e = true}) 1 ω) = p ^ S.card := by
  classical
  rw [Exp, Finset.sum_congr rfl (fun ω _ => by rw [indicator_biInter_eq S ω])]
  have h := Exp_prod p (fun (i : ι) (b : Bool) => if i ∈ S then (if b then (1 : ℝ) else 0) else 1)
  rw [Exp] at h
  rw [h, Finset.prod_congr rfl (g := fun i => if i ∈ S then p else 1)
    (fun i _ => by by_cases hi : i ∈ S <;> simp [hi]), ← Finset.prod_filter]
  simp

theorem cubeMeasure_biInter {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) :
    cubeMeasure p (⋂ e ∈ S, {ω : ι → Bool | ω e = true}) = ENNReal.ofReal (p ^ S.card) := by
  rw [cubeMeasure_apply hp0 hp1]
  exact congrArg ENNReal.ofReal (Exp_indicator_biInter p S)

theorem cubeMeasure_coord {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : ι) :
    cubeMeasure p {ω : ι → Bool | ω e = true} = ENNReal.ofReal p := by
  have h := cubeMeasure_biInter hp0 hp1 ({e} : Finset ι)
  simpa using h

theorem iIndepSet_cubeCoord {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    iIndepSet (fun e : ι => {ω : ι → Bool | ω e = true}) (cubeMeasure p) := by
  refine (iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)).mpr fun S => ?_
  rw [cubeMeasure_biInter hp0 hp1 S]
  rw [Finset.prod_congr rfl (fun e _ => cubeMeasure_coord hp0 hp1 e), Finset.prod_const,
    ← ENNReal.ofReal_pow hp0]

/-! ## Efron–Stein in integral form -/

theorem cube_centred_sq_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : (ι → Bool) → ℝ) :
    ∫ ω, (f ω - ∫ ω', f ω' ∂(cubeMeasure p)) ^ 2 ∂(cubeMeasure p)
      ≤ ∑ i : ι, p * (1 - p)
          * ∫ ω, (f (Function.update ω i true) - f (Function.update ω i false)) ^ 2
              ∂(cubeMeasure p) := by
  rw [integral_cubeMeasure hp0 hp1]
  simp only [integral_cubeMeasure hp0 hp1]
  exact centred_sq_le_sum_sq_diff hp0 hp1 f

end Cube

/-! ## The retention carried by the cube -/

open Cube

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The Bernoulli retention on the finite cube.**  The coordinate events of the cube
`Finset V → Bool` form an independent family of events of probability `p`. -/
noncomputable def cubeRetention (H : Finset (Finset V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    @BernoulliRetention V _ (Finset V → Bool) (cubeSpace p) H p :=
  @BernoulliRetention.mk V _ (Finset V → Bool) (cubeSpace p) H p
    (fun e => {ω : Finset V → Bool | ω e = true}) (fun _ => MeasurableSet.of_discrete)
    (iIndepSet_cubeCoord hp0 hp1) (fun e _ => cubeMeasure_coord hp0 hp1 e)

theorem retainedSet_cubeRetention (H : Finset (Finset V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : Finset V → Bool) :
    @retainedSet V _ (Finset V → Bool) (cubeSpace p) H p (cubeRetention H hp0 hp1) ω
      = H.filter (fun e => ω e = true) := by
  ext e
  simp [retainedSet, cubeRetention]

end LeanPool.AsymptoticTrianglePacking.Internal
