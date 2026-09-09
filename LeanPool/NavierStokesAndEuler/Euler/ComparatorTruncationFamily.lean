/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
public import LeanPool.NavierStokesAndEuler.Euler.TruncationFamily
public import LeanPool.NavierStokesAndEuler.Euler.TruncationFamilySmooth
public import LeanPool.NavierStokesAndEuler.Euler.CompactSmoothTimeField

@[expose] public section

/-! The actual radial-potential truncation of a Comparator Euler solution
forms a smooth bounded coefficient family with uniformly bounded energy.
No integrability of spatial derivatives of the original solution is needed. -/

noncomputable section


open Set MeasureTheory EulerSmoothLimit Euler.ComparatorBridge
open scoped ContDiff Topology

namespace Euler.ComparatorBridge

/-- Square-root reparametrization of the unit time interval. -/
def unitSqrtTime : C(Icc (0 : ℝ) 1, Icc (0 : ℝ) 1) where
  toFun t := ⟨Real.sqrt t, Real.sqrt_nonneg _, by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt t.property.2⟩
  continuous_toFun := (Real.continuous_sqrt.comp continuous_subtype_val).subtype_mk _

@[simp] theorem unitSqrtTime_apply (t : Icc (0 : ℝ) 1) :
    (unitSqrtTime t : ℝ) = Real.sqrt t := rfl

end Euler.ComparatorBridge

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

/-- The square-time parametrization is jointly smooth and uniformly supported,
so all its spatial jets form continuous bounded time paths. -/
def finiteEnergyTruncationSquareTimeField (R : ℝ) (hR : 0 < R) :
    SmoothTimeField (Icc (0 : ℝ) 1) Space Space :=
  SmoothTimeField.ofContDiffOnCompactSupport (Icc (0 : ℝ) 1)
    (fun tx : ℝ × Space => finiteEnergyTruncation (fun y => v y (tx.1 ^ 2)) R tx.2)
    ((potentialTruncation_square_family_smooth (Function.uncurry v) h.velocity_smooth
      (truncationCutoff R) (truncationCutoff_smooth R)).comp
        (contDiff_snd.prodMk contDiff_fst)).contDiffOn
    (Metric.closedBall 0 (2 * R)) (isCompact_closedBall _ _)
    (fun t _ht => finiteEnergyTruncation_support (fun y => v y (t ^ 2)) R hR)

/-- Reparametrizing by square root recovers the exact physical-time
truncation, while retaining continuity of every bounded spatial jet. -/
def finiteEnergyTruncationTimeField (R : ℝ) (hR : 0 < R) :
    SmoothTimeField (Icc (0 : ℝ) 1) Space Space :=
  (h.finiteEnergyTruncationSquareTimeField R hR).reparametrize unitSqrtTime

@[simp] theorem finiteEnergyTruncationTimeField_apply (R : ℝ) (hR : 0 < R)
    (t : Icc (0 : ℝ) 1) (x : Space) :
    (h.finiteEnergyTruncationTimeField R hR).field t x =
      finiteEnergyTruncation (v · (t : ℝ)) R x := by
  change finiteEnergyTruncation (fun y => v y ((Real.sqrt (t : ℝ)) ^ 2)) R x = _
  rw [Real.sq_sqrt t.property.1]

theorem finiteEnergyTruncationTimeField_field (R : ℝ) (hR : 0 < R)
    (t : Icc (0 : ℝ) 1) :
    ((h.finiteEnergyTruncationTimeField R hR).field t : Space → Space) =
      finiteEnergyTruncation (v · (t : ℝ)) R := by
  funext x
  exact h.finiteEnergyTruncationTimeField_apply R hR t x

/-- Every actual Comparator solution supplies the truncation family used by
the finite-energy flow argument. The uniform energy is a fixed multiple of
the reference solution's energy bound. -/
def finiteEnergyTruncationFamily : FiniteEnergyTruncationFamily v := by
  classical
  let coefficient : ℝ → SmoothTimeField (Icc (0 : ℝ) 1) Space Space := fun R =>
    if hR : 0 < R then h.finiteEnergyTruncationTimeField R hR
    else h.finiteEnergyTruncationTimeField 1 (by norm_num)
  have hc (R : ℝ) (hR : 0 < R) (t : Icc (0 : ℝ) 1) :
      ((coefficient R).field t : Space → Space) =
        finiteEnergyTruncation (v · (t : ℝ)) R := by
    simp only [coefficient, dite_eq_left hR]
    exact h.finiteEnergyTruncationTimeField_field R hR t
  refine
    { coefficient := coefficient
      energy := truncationEnergyConstant * h.globally_bounded_energy.choose
      divergence := ?_
      memLp := ?_
      energy_bound := ?_
      agrees := ?_ }
  · intro R hR t x
    rw [hc R hR t]
    exact finiteEnergyTruncation_divergence _ (h.velocity_contDiff t t.property.1) R x
  · intro R hR t
    rw [hc R hR t]
    exact (finiteEnergyTruncation_energy_bound _ (h.velocity_contDiff t t.property.1)
      (fun x => h.div_free x t t.property.1) (h.velocity_memLp t t.property.1) R hR).1
  · intro R hR t
    rw [hc R hR t]
    exact (finiteEnergyTruncation_energy_bound _ (h.velocity_contDiff t t.property.1)
      (fun x => h.div_free x t t.property.1) (h.velocity_memLp t t.property.1) R hR).2.trans
      (mul_le_mul_of_nonneg_left
        (h.globally_bounded_energy.choose_spec t t.property.1).le
        truncationEnergyConstant_nonneg)
  · intro R hR t x hx
    rw [hc R hR t]
    exact finiteEnergyTruncation_eq _ (h.velocity_contDiff t t.property.1)
      (fun x => h.div_free x t t.property.1) R hR x hx

end Euler.EulerExistenceAndSmoothnessR3
