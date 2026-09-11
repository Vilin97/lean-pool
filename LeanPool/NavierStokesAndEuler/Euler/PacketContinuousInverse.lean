/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketData
import LeanPool.NavierStokesAndEuler.Euler.ContinuousInverseDerivative
import LeanPool.NavierStokesAndEuler.Euler.PacketInverseFlowGevrey
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanPool.NavierStokesAndEuler.Euler.GevreyInverseMap
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! The actual inverse parent flow needs only continuity as an input.
Its differentiability, smooth spatial slices, and jointly continuous
spatial jets follow from the prescribed Jacobian and inverse identities. -/

section

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

end
end

end

section

/-!
# Joint spatial-jet continuity for the prescribed inverse parent flow

The smooth bounded coefficient paths already carry genuine continuous
spatial jets.  Their evaluation, together with the actual inverse identity,
supplies all inverse-flow continuity hypotheses used by Sobolev transport.
-/

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerMeanCoefficients.SmoothCoefficientPath

open EulerSmoothLimit

theorem jet_joint_continuous {K V : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothCoefficientPath K V) (n : ℕ) :
    Continuous (fun p : K × Space =>
      iteratedFDeriv ℝ n (A.field p.1 : Space → V) p.2) := by
  have heq : (fun p : K × Space =>
      iteratedFDeriv ℝ n (A.field p.1 : Space → V) p.2) =
      fun p => A.jet n p.1 p.2 := by
    funext p
    exact (A.jet_eq n p.1 p.2).symm
  rw [heq]
  fun_prop

end EulerMeanCoefficients.SmoothCoefficientPath

namespace EulerPacketInverseFlowGevrey

open Set EulerSmoothLimit EulerGevreyComposition

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x) = x)
  (hYjoint : Continuous (Function.uncurry Y))

include hX hY hXY hYjoint in
/-- Every spatial inverse-flow jet is jointly continuous in time and space,
derived from the original coefficient path and actual inverse relation. -/
theorem inverseFlow_jet_continuous (n : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) D.T × Space =>
      iteratedFDeriv ℝ n (Y p.1) p.2) := by
  exact continuous_iteratedFDeriv_of_fderiv_eq_comp Y
    (fun t => (D.FInv.field t : Space → Space →L[ℝ] Space)) hYjoint hY
    D.FInv.smooth D.FInv.jet_joint_continuous
    (inverseFlow_fderiv D X Y hX hY hXY) n

end EulerPacketInverseFlowGevrey

end
end

end

@[expose] public section

noncomputable section

open scoped ContDiff

namespace EulerPacketInverseFlowGevrey

open Set EulerSmoothLimit EulerContinuousInverseDerivative

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hXY : ∀ t x, X t (Y t x) = x)
  (hY : Continuous (Function.uncurry Y))

include hX hXY hY in
theorem continuousInverse_hasFDerivAt (t : Icc (0 : ℝ) D.T) (x : Space) :
    HasFDerivAt (Y t) (D.FInv.field t (Y t x)) x :=
  hasFDerivAt_inverse (X t) (Y t) x (D.F.field t (Y t x)) (D.FInv.field t (Y t x))
    (hY.uncurry_left t).continuousAt (hX t (Y t x))
    (Filter.Eventually.of_forall (hXY t)) (D.inverse_left t (Y t x))

include hX hXY hY in
theorem continuousInverse_differentiable (t : Icc (0 : ℝ) D.T) :
    Differentiable ℝ (Y t) :=
  fun x => (continuousInverse_hasFDerivAt D X Y hX hXY hY t x).differentiableAt

include hX hXY hY in
theorem continuousInverse_contDiff (t : Icc (0 : ℝ) D.T) : ContDiff ℝ ∞ (Y t) :=
  inverseFlow_contDiff D X Y hX (continuousInverse_differentiable D X Y hX hXY hY) hXY t

include hX hXY hY in
theorem continuousInverse_jet_continuous (n : ℕ) :
    Continuous (fun p : Icc (0 : ℝ) D.T × Space =>
      iteratedFDeriv ℝ n (Y p.1) p.2) :=
  inverseFlow_jet_continuous D X Y hX
    (continuousInverse_differentiable D X Y hX hXY hY) hXY hY n

end EulerPacketInverseFlowGevrey
