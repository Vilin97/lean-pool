/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.GevreyInverseMap
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.Measurability.Init

/-!
# Joint continuity of the spatial jets of an inverse map

The parameter may range over an arbitrary topological space.  Joint
continuity of the map itself and of the prescribed coefficient jets, plus
the actual equation `DY = A ∘ Y`, determines joint continuity of every
spatial derivative of `Y`.
-/

@[expose] public section


noncomputable section

open scoped BigOperators ContDiff

namespace EulerGevreyComposition

variable {K E F : Type*} [TopologicalSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- No continuity of inverse-map derivatives is an input: it follows from
the prescribed differential identity and the coefficient's actual jets. -/
theorem continuous_iteratedFDeriv_of_fderiv_eq_comp
    (Y : K → E → F) (A : K → F → E →L[ℝ] F)
    (hY : Continuous (Function.uncurry Y))
    (hYdiff : ∀ t, Differentiable ℝ (Y t))
    (hA : ∀ t, ContDiff ℝ ∞ (A t))
    (hAjet : ∀ n, Continuous (fun p : K × F => iteratedFDeriv ℝ n (A p.1) p.2))
    (hDY : ∀ t x, fderiv ℝ (Y t) x = A t (Y t x))
    (n : ℕ) :
    Continuous (fun p : K × E => iteratedFDeriv ℝ n (Y p.1) p.2) := by
  have hYs (t : K) : ContDiff ℝ ∞ (Y t) :=
    contDiff_of_fderiv_eq_comp (Y t) (A t) (hYdiff t) (hA t) (hDY t)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp hY
    | succ m =>
      have hsum : Continuous (fun p : K × E =>
          ∑ c : OrderedFinpartition m,
            c.compAlongOrderedFinpartition
              (iteratedFDeriv ℝ c.length (A p.1) (Y p.1 p.2))
              (fun i => iteratedFDeriv ℝ (c.partSize i) (Y p.1) p.2)) := by
        apply continuous_finsetSum
        intro c _
        have hq : Continuous (fun p : K × E =>
            iteratedFDeriv ℝ c.length (A p.1) (Y p.1 p.2)) :=
          (hAjet c.length).comp (continuous_fst.prodMk hY)
        have hp : Continuous (fun p : K × E =>
            fun i : Fin c.length => iteratedFDeriv ℝ (c.partSize i) (Y p.1) p.2) :=
          continuous_pi (fun i => ih (c.partSize i) (Nat.lt_succ_of_le (c.partSize_le i)))
        exact (c.compAlongOrderedFinpartitionL ℝ E F (E →L[ℝ]
            F)).continuous_uncurry_of_multilinear.comp
          (hq.prodMk hp)
      have heq : (fun p : K × E => iteratedFDeriv ℝ (m+1) (Y p.1) p.2) =
          fun p => (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
            (∑ c : OrderedFinpartition m,
              c.compAlongOrderedFinpartition
                (iteratedFDeriv ℝ c.length (A p.1) (Y p.1 p.2))
                (fun i => iteratedFDeriv ℝ (c.partSize i) (Y p.1) p.2)) := by
        funext p
        rw [iteratedFDeriv_succ_eq_comp_right]
        change (continuousMultilinearCurryRightEquiv' ℝ m E F).symm
          (iteratedFDeriv ℝ m (fderiv ℝ (Y p.1)) p.2) = _
        congr 1
        rw [show fderiv ℝ (Y p.1) = A p.1 ∘ Y p.1 from funext (hDY p.1)]
        rw [iteratedFDeriv_comp (hA p.1).contDiffAt (hYs p.1).contDiffAt (by simp)]
        rfl
      rw [heq]
      exact (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.continuous.comp hsum

end EulerGevreyComposition
