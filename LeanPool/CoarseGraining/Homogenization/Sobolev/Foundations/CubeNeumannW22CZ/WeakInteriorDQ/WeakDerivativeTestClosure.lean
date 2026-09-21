/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit

/-! # Weak Derivative Test Closure -/

namespace Homogenization

open scoped ENNReal Manifold

noncomputable section

namespace HasWeakPartialDerivOn

/-- Extend the weak-partial-derivative identity from admissible smooth compact
tests to any test reached as an `L²` limit together with its coordinate
derivative.

This is the closure step needed for cube boundary tests: the geometric cutoff
argument supplies the approximating sequence `ψn`; this lemma performs the
functional-analytic handoff to the weak derivative identity. -/
theorem integral_mul_deriv_eq_neg_integral_mul_of_eLpNorm_approx
    {d : ℕ} {U : Set (Vec d)} {i : Fin d} {u gi ψ Dψ : Vec d → ℝ}
    (huweak : HasWeakPartialDerivOn U i u gi)
    (hu : MemScalarL2 U u) (hgi : MemScalarL2 U gi)
    (hψ : MemScalarL2 U ψ) (hDψ : MemScalarL2 U Dψ)
    (ψn : ℕ → Vec d → ℝ)
    (hψn_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψn n))
    (hψn_compact : ∀ n, HasCompactSupport (ψn n))
    (hψn_sub : ∀ n, tsupport (ψn n) ⊆ U)
    (hψn_mem : ∀ n, MemScalarL2 U (ψn n))
    (hDψn_mem : ∀ n, MemScalarL2 U (fun x => euclideanCoordDeriv i (ψn n) x))
    (hψn_to_ψ :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm (fun x => ψn n x - ψ x) 2 (volumeMeasureOn U))
        Filter.atTop (nhds 0))
    (hDψn_to_Dψ :
      Filter.Tendsto
        (fun n =>
          MeasureTheory.eLpNorm
            (fun x => euclideanCoordDeriv i (ψn n) x - Dψ x) 2
            (volumeMeasureOn U))
        Filter.atTop (nhds 0)) :
    ∫ x in U, u x * Dψ x ∂MeasureTheory.volume =
      -∫ x in U, gi x * ψ x ∂MeasureTheory.volume := by
  let Dψn : ℕ → Vec d → ℝ := fun n x => euclideanCoordDeriv i (ψn n) x
  have hDψn_mem' : ∀ n, MemScalarL2 U (Dψn n) := by
    intro n
    simpa [Dψn] using hDψn_mem n
  have hDψn_toScalar :
      Filter.Tendsto
        (fun n => toScalarL2 (hDψn_mem' n))
        Filter.atTop
        (nhds (toScalarL2 hDψ)) := by
    refine
      tendsto_toScalarL2_of_tendsto_eLpNorm
        (F := Dψn) (G := Dψ) hDψn_mem' hDψ ?_
    simpa [Dψn] using hDψn_to_Dψ
  have hleft :
      Filter.Tendsto
        (fun n => ∫ x in U, u x * Dψn n x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, u x * Dψ x ∂MeasureTheory.volume)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2 hu hDψn_mem' hDψ hDψn_toScalar
  have hψn_toScalar :
      Filter.Tendsto
        (fun n => toScalarL2 (hψn_mem n))
        Filter.atTop
        (nhds (toScalarL2 hψ)) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm
      (F := ψn) (G := ψ) hψn_mem hψ hψn_to_ψ
  have hright :
      Filter.Tendsto
        (fun n => -∫ x in U, gi x * ψn n x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (-∫ x in U, gi x * ψ x ∂MeasureTheory.volume)) := by
    exact
      (tendsto_integral_mul_of_tendsto_toScalarL2 hgi hψn_mem hψ hψn_toScalar).neg
  have hseq :
      (fun n => ∫ x in U, u x * Dψn n x ∂MeasureTheory.volume) =
        fun n => -∫ x in U, gi x * ψn n x ∂MeasureTheory.volume := by
    funext n
    simpa [Dψn, euclideanCoordDeriv] using
      huweak (ψn n) (hψn_smooth n) (hψn_compact n) (hψn_sub n)
  exact tendsto_nhds_unique (hleft.congr' (Filter.EventuallyEq.of_eq hseq)) hright

end HasWeakPartialDerivOn

end

end Homogenization
