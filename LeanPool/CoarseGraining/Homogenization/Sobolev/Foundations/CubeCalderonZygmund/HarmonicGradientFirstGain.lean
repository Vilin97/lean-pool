/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicDerivative
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding

/-! # Harmonic Gradient First Gain -/

@[expose] public section

namespace Homogenization

open scoped ENNReal NNReal BigOperators

noncomputable section

/-!
# First Sobolev gain for weak harmonic gradients

The analytic estimate in this file is purely Sobolev-theoretic: a local weak
Hessian makes each gradient coordinate an `H¹` function, and the cube Sobolev
embedding raises that coordinate from `L²` to the critical exponent.  The
weak-harmonic equation is kept out of the estimate itself.
-/

namespace CubeCalderonZygmund

variable {d : ℕ}

private theorem openCubeSet_eq_axisCube (Q : TriadicCube d) :
    openCubeSet Q =
      axisCube
        (fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
        (cubeScaleFactor Q) := by
  have hupper : ∀ j : Fin d,
      ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q + cubeScaleFactor Q =
        ((Q.index j : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    intro j
    ring
  ext x
  simp only [openCubeSet, axisCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo]
  simp_rw [hupper]

/-- The pure Sobolev first gain for a gradient coordinate.  The constant is
chosen before the cube, function, weak-Hessian witness, and coordinate, so it
depends only on the dimension. -/
theorem exists_gradCoord_criticalLp_bound (hd : 3 ≤ d) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
        (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d),
        MeasureTheory.eLpNorm (fun x => u.grad x i) (twoStar d)
            (volumeMeasureOn (openCubeSet Q)) ≤
          (C : ℝ≥0∞) *
            ((∑ j : Fin d,
                MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
                  (volumeMeasureOn (openCubeSet Q))) +
              ENNReal.ofReal (cubeScaleFactor Q)⁻¹ *
                MeasureTheory.eLpNorm (fun x => u.grad x i) 2
                  (volumeMeasureOn (openCubeSet Q))) := by
  obtain ⟨C, hCpos, hC⟩ := cube_sobolev_embedding hd
  refine ⟨C, hCpos, ?_⟩
  intro Q
  let z : Vec d := fun j => ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hset : openCubeSet Q = axisCube z (cubeScaleFactor Q) := by
    simpa [z] using openCubeSet_eq_axisCube Q
  let P : Set (Vec d) → Prop := fun U =>
    ∀ (u : H1Function U) (H : HasWeakHessianOn U u) (i : Fin d),
      MeasureTheory.eLpNorm (fun x => u.grad x i) (twoStar d)
          (volumeMeasureOn U) ≤
        (C : ℝ≥0∞) *
          ((∑ j : Fin d,
              MeasureTheory.eLpNorm (fun x => H.hess i j x) 2 (volumeMeasureOn U)) +
            ENNReal.ofReal (cubeScaleFactor Q)⁻¹ *
              MeasureTheory.eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn U))
  have haxis : P (axisCube z (cubeScaleFactor Q)) := by
    intro v K i
    simpa [P, HasWeakHessianOn.gradCoordH1Function_apply,
      HasWeakHessianOn.gradCoordH1Function_grad_apply] using!
      hC z (cubeScaleFactor Q) hscale_pos (K.gradCoordH1Function i)
  exact hset.symm ▸ haxis

/-- The derivative-harmonic package used by the later regularity engine: the
Sobolev gain remains the pure estimate above, while this thin wrapper records
the homogeneous weak equation available for the same coordinate. -/
theorem exists_harmonic_gradCoord_criticalLp_bound (hd : 3 ≤ d) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
        (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ => 0) →
          WeakPoissonEquationOn (openCubeSet Q) (H.gradCoordH1Function i) (fun _ => 0) ∧
            MeasureTheory.eLpNorm (fun x => u.grad x i) (twoStar d)
                (volumeMeasureOn (openCubeSet Q)) ≤
              (C : ℝ≥0∞) *
                ((∑ j : Fin d,
                    MeasureTheory.eLpNorm (fun x => H.hess i j x) 2
                      (volumeMeasureOn (openCubeSet Q))) +
                  ENNReal.ofReal (cubeScaleFactor Q)⁻¹ *
                    MeasureTheory.eLpNorm (fun x => u.grad x i) 2
                      (volumeMeasureOn (openCubeSet Q))) := by
  obtain ⟨C, hCpos, hbound⟩ := exists_gradCoord_criticalLp_bound hd
  refine ⟨C, hCpos, ?_⟩
  intro Q u H i hweak
  refine ⟨?_, hbound Q u H i⟩
  exact hweak.gradCoordH1Function_harmonic (isOpen_openCubeSet Q) H i

end CubeCalderonZygmund

end

end Homogenization
