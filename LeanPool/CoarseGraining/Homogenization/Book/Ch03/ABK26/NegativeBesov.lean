/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspCongruence
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence

/-!
# ABK26 running-scale negative Besov seminorm

This file owns the literal finite-`p` concrete negative Besov quantity used
by the Chapter 3 local coarse-graining statement.  Its summation variable is
the descendant depth `j`; the physical source scale is consequently
`Q.scale - j` at every summand.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The unrooted running-scale depth contribution to the concrete finite-`p`
negative Besov seminorm. -/
noncomputable def cubeEuclideanNegativeBesovDepthEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal
      (Real.rpow 3
        (s.1 * p.exponent.toReal *
          (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) *
    ((descendantsAtScale Q (Q.scale - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
      (descendantsAtScale Q (Q.scale - (j : ℤ))).attach.sum (fun R =>
        (ENNReal.ofReal ‖cubeAverageVec R.1 F.toField‖) ^
          p.exponent.toReal)

/-- The source-facing concrete negative Besov seminorm.  Its running-scale
weight is evaluated at the descendant scale `Q.scale - j`, rather than frozen
at the parent scale. -/
noncomputable def cubeEuclideanNegativeBesovESeminorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) : ℝ≥0∞ := by
  classical
  exact (∑' j : ℕ,
    ENNReal.ofReal
        (Real.rpow 3
          (s.1 * p.exponent.toReal *
            (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) *
      ((descendantsAtScale Q (Q.scale - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
        (descendantsAtScale Q (Q.scale - (j : ℤ))).attach.sum (fun R =>
          (ENNReal.ofReal ‖cubeAverageVec R.1 F.toField‖) ^
            p.exponent.toReal)) ^ (1 / p.exponent.toReal)

/-- Exact depth decomposition of the source-facing negative Besov seminorm. -/
theorem cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeEuclideanNegativeBesovESeminorm Q s p F =
      (∑' j : ℕ, cubeEuclideanNegativeBesovDepthEnergy Q s p F j) ^
        (p.exponent.toReal)⁻¹ := by
  rw [cubeEuclideanNegativeBesovESeminorm]
  simp only [cubeEuclideanNegativeBesovDepthEnergy, one_div]

theorem cubeEuclideanNegativeBesovDepthEnergy_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) (j : ℕ) :
    0 ≤ cubeEuclideanNegativeBesovDepthEnergy Q s p F j :=
  bot_le

theorem cubeEuclideanNegativeBesovESeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    0 ≤ cubeEuclideanNegativeBesovESeminorm Q s p F :=
  bot_le

theorem cubeEuclideanNegativeBesovDepthEnergy_zero {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeEuclideanNegativeBesovDepthEnergy Q s p F 0 =
      ENNReal.ofReal
          (Real.rpow 3 (s.1 * p.exponent.toReal * (Q.scale : ℝ))) *
        (ENNReal.ofReal ‖cubeAverageVec Q F.toField‖) ^ p.exponent.toReal := by
  classical
  unfold cubeEuclideanNegativeBesovDepthEnergy
  have hzero : Q.scale - ((0 : ℕ) : ℤ) = Q.scale := by omega
  rw [hzero, descendantsAtScale_self]
  let q : {R // R ∈ ({Q} : Finset (TriadicCube d))} := ⟨Q, by simp⟩
  have hattach : ({Q} : Finset (TriadicCube d)).attach = {q} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · simp [q]
    intro R _
    apply Subtype.ext
    simpa [q] using (Finset.mem_singleton.mp R.property)
  rw [hattach]
  simp [q]

theorem cubeEuclideanNegativeBesovESeminorm_congr_ae {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F G : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hFG : F.toField =ᵐ[normalizedCubeMeasure Q] G.toField) :
    cubeEuclideanNegativeBesovESeminorm Q s p F =
      cubeEuclideanNegativeBesovESeminorm Q s p G := by
  have hcube : F.toField =ᵐ[cubeMeasure Q] G.toField :=
    Gagliardo.ae_normalizedCubeMeasure_iff.mp hFG
  rw [cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy,
    cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy]
  congr 1
  apply tsum_congr
  intro j
  unfold cubeEuclideanNegativeBesovDepthEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro R _
  have hscale : Q.scale - (j : ℤ) ≤ Q.scale := by omega
  have hsub : cubeSet R.1 ⊆ cubeSet Q :=
    cubeSet_subset_of_mem_descendantsAtScale hscale R.2
  have hR : F.toField =ᵐ[volume.restrict (cubeSet R.1)] G.toField := by
    rw [cubeMeasure] at hcube
    exact ae_restrict_of_ae_restrict_of_subset hsub hcube
  rw [cubeAverageVec_eq_of_ae_eq_on_cubeSet hR]

end

end ABK26
end Ch03
end Book
end Homogenization
