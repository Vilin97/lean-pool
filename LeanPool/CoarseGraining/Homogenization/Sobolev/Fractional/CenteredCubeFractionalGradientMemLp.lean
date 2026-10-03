/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpBelowTwo

/-!
# Finite-exponent gradient membership for fractional divergence data

This file packages the supplied-solution Calderón--Zygmund estimate as a
literal normalized-cube `L^q` membership witness for the given `H¹₀`
gradient.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A supplied zero-trace centered-cube divergence solution driven by
fractional `L² ∩ L^q` data has a literal normalized-cube `L^q` gradient. -/
theorem centeredCubeH10ScalarDivergence_grad_memLp
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) (m : ℤ) (sigma0 : ℝ)
    (s : FractionalOrder)
    (h : CubeEuclideanWspL2Field (originCube d m) s q)
    (w : H10Function (openCubeSet (originCube d m)))
    (hsigma0 : 0 < sigma0)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 w h.toLpTwo) :
    MemLp (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) q.exponent
      (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCtop, hC⟩ := CubeCalderonZygmund.centeredCubeH10ScalarDivergence_cz d q
  let hField : CubeEuclideanL2LpField (originCube d m) q :=
    { toField := h.toField
      euclideanMemLp := h.euclideanMemLp
      euclideanMemL2 := h.euclideanMemL2 }
  have hgrad_l2 : MemLp (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) 2
      (normalizedCubeMeasure (originCube d m)) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      w.toH1Function.grad_memL2_normalizedCubeMeasure i
  have hbound :
      eLpNorm (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) ≤
        C * (ENNReal.ofReal sigma0)⁻¹ *
          eLpNorm (fun x => HilbertVec.ofVec (h.toField x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) := by
    have hraw := hC m sigma0 hField w hsigma0
      (by simpa only [hField] using! hsolution)
    rw [CubeCalderonZygmund.INTERNAL.normalizedEuclideanLpENorm_eq_hilbert_eLpNorm_for_duality
      (centeredCubeDomain d m) q.exponent _ (by
        simpa only [centeredCubeDomain,
          cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
          using hgrad_l2.aestronglyMeasurable),
      CubeCalderonZygmund.INTERNAL.normalizedEuclideanLpENorm_eq_hilbert_eLpNorm_for_duality
        (centeredCubeDomain d m) q.exponent _ (by
          simpa only [centeredCubeDomain,
            cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
            using hField.euclideanMemLp.aestronglyMeasurable)]
        at hraw
    have hgradField : hilbertifyVecField w.toH1Function.grad =
        (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) := rfl
    have hdataField : hilbertifyVecField h.toField =
        (fun x => HilbertVec.ofVec (h.toField x)) := rfl
    rw [hgradField, hdataField] at hraw
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hField] using hraw
  change eLpNorm (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) q.exponent
    (normalizedCubeMeasure (originCube d m)) < ∞
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hCtop (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0))).lt_top)
    h.euclideanMemLp.eLpNorm_lt_top)

end

end Homogenization
