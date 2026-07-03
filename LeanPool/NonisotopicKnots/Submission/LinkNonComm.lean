/-
Copyright (c) 2026 Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sober
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.EckmannHilton
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

import LeanPool.NonisotopicKnots.Submission.Vieta
import LeanPool.NonisotopicKnots.Submission.CuspGeom
import LeanPool.NonisotopicKnots.Submission.Pi1Transport

/-!
# Non-abelian `π₁` of the depressed discriminant complement and the cusp link complement

Starting from `Submission.Vieta.discCompl_pi1_noncomm` (the discriminant complement of *general*
monic cubics `DiscCompl ⊆ ℂ³` has non-abelian `π₁`), we transport non-abelianness to:

* `DC = {(p,q) : 4p³+27q² ≠ 0} ⊆ ℂ²`, the discriminant complement of *depressed* cubics
  `X³ + pX + q`, via the homeomorphism `DiscCompl ≃ₜ DC × ℂ` (depression: translate the roots so
  their sum is `0`; the free coordinate is the first elementary symmetric function `e₁`, living in
  the contractible factor `ℂ`); and
* `Link ⊆ ℂ²`, the cusp link complement on the weighted sphere, via
  `Submission.CuspGeom.dcLinkEquiv : DC ≃ₕ Link`.

These are reusable bricks toward `Submission.Helpers.trefoil_compl_pi1_noncomm`.
-/

namespace Submission.LinkNonComm

open scoped Topology
open Submission.Vieta Submission.CuspGeom

/-
**The depressed-cubic discriminant complement has non-abelian `π₁`.**
-/
theorem DC_pi1_noncomm :
    ∃ (x : ↥DC) (a b : FundamentalGroup (↥DC) x), a * b ≠ b * a := by
  -- Apply `noncomm_of_homeo` to `discCompl_pi1_noncomm` to get non-abelian π₁ of `DC × ℂ`.
  have h_dc_x_c : ∃ (x : ↥DC × ℂ) (a b : FundamentalGroup (↥DC × ℂ) x), a * b ≠ b * a := by
    convert Submission.Pi1Transport.noncomm_of_homeo _ _;
    exact ↥DiscCompl;
    exact inferInstance;
    · refine' Homeomorph.symm _;
      refine' ⟨ _, _, _ ⟩;
      refine' ⟨ _, _, _, _ ⟩;
      refine' fun x => ⟨ ⟨ ( x.val.2.1 - x.val.1 ^ 2 / 3, -2 * x.val.1 ^ 3 / 27 + x.val.1 * x.val.2.1 / 3 - x.val.2.2 ), _ ⟩, x.val.1 ⟩;
      rotate_left;
      use fun x => ⟨ ( x.2, x.1.val.1 + x.2 ^ 2 / 3, -x.1.val.2 - 2 * x.2 ^ 3 / 27 + x.2 * ( x.1.val.1 + x.2 ^ 2 / 3 ) / 3 ), by
        unfold DiscCompl; norm_num [ DC ] ; ring_nf ;
        obtain ⟨a, ha⟩ : ∃ a : Fin 3 → ℂ, Coeff a = (x.2, (x.1.val.1 + x.2 ^ 2 * (1 / 3)), (x.1.val.1 * x.2 * (1 / 3) + (x.2 ^ 3 * (1 / 27) - x.1.val.2))) := by
          obtain ⟨a, b, c, h⟩ : ∃ a b c : ℂ, a + b + c = x.2 ∧ a * b + a * c + b * c = x.1.val.1 + x.2 ^ 2 * (1 / 3) ∧ a * b * c = x.1.val.1 * x.2 * (1 / 3) + (x.2 ^ 3 * (1 / 27) - x.1.val.2) := by
            obtain ⟨a, ha⟩ : ∃ a : ℂ, a ^ 3 - x.2 * a ^ 2 + (x.1.val.1 + x.2 ^ 2 * (1 / 3)) * a - (x.1.val.1 * x.2 * (1 / 3) + (x.2 ^ 3 * (1 / 27) - x.1.val.2)) = 0 := by
              convert ( Complex.exists_root <| show ( Polynomial.degree ( Polynomial.monomial 3 1 - Polynomial.monomial 2 x.2 + Polynomial.monomial 1 ( ( x.1.val.1 + x.2 ^ 2 * ( 1 / 3 ) ) ) - Polynomial.C ( ( x.1.val.1 * x.2 * ( 1 / 3 ) + ( x.2 ^ 3 * ( 1 / 27 ) - x.1.val.2 ) ) ) ) ) > 0 from ?_ ) using 1;
              · norm_num [ Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.eval_C ];
                exact funext fun _ => by ring;
              · rw [ Polynomial.degree_sub_C ] <;> rw [ Polynomial.degree_add_eq_left_of_degree_lt ] <;> rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> by_cases h : x.2 = 0 <;> simp +decide [ h ];
                · exact lt_of_le_of_lt ( Polynomial.degree_monomial_le _ _ ) ( by norm_num );
                · exact lt_of_le_of_lt ( Polynomial.degree_add_le _ _ ) ( max_lt ( lt_of_le_of_lt ( Polynomial.degree_monomial_le _ _ ) ( by norm_num ) ) ( lt_of_le_of_lt ( Polynomial.degree_monomial_le _ _ ) ( by norm_num ) ) );
                · exact lt_of_le_of_lt ( Polynomial.degree_monomial_le _ _ ) ( by norm_num );
                · exact lt_of_le_of_lt ( Polynomial.degree_add_le _ _ ) ( max_lt ( lt_of_le_of_lt ( Polynomial.degree_monomial_le _ _ ) ( by norm_num ) ) ( lt_of_le_of_lt ( Polynomial.degree_monomial_le _ _ ) ( by norm_num ) ) );
            -- Let $b$ and $c$ be the other roots of the polynomial.
            obtain ⟨b, c, hb, hc⟩ : ∃ b c : ℂ, b + c = x.2 - a ∧ b * c = (x.1.val.1 + x.2 ^ 2 * (1 / 3)) - a * (x.2 - a) := by
              exact ⟨ ( x.2 - a ) / 2 - ( ( x.2 - a ) ^ 2 / 4 - ( ( x.1.val.1 + x.2 ^ 2 * ( 1 / 3 ) ) - a * ( x.2 - a ) ) ) ^ ( 1 / 2 : ℂ ), ( x.2 - a ) / 2 + ( ( x.2 - a ) ^ 2 / 4 - ( ( x.1.val.1 + x.2 ^ 2 * ( 1 / 3 ) ) - a * ( x.2 - a ) ) ) ^ ( 1 / 2 : ℂ ), by ring, by ring; rw [ ← Complex.cpow_nat_mul ] ; norm_num; ring ⟩;
            exact ⟨ a, b, c, by linear_combination' hb, by linear_combination' hc + a * hb, by linear_combination' hc * a + ha ⟩;
          use ![a, b, c];
          exact Prod.ext h.1 ( Prod.ext h.2.1 h.2.2 );
        refine' ⟨ a, _, by show Coeff a = _; rw [ha, add_sub_assoc] ⟩;
        have h_distinct : 4 * (x.1.val.1) ^ 3 + 27 * (x.1.val.2) ^ 2 ≠ 0 := by
          exact x.1.2;
        unfold Coeff at ha; simp_all +decide [ Function.Injective, Fin.forall_fin_succ ] ;
        grind +ring ⟩;
      all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
      grobner;
      grobner;
      refine' ⟨ _, _ ⟩;
      fun_prop;
      · fun_prop;
      · fun_prop;
      · obtain ⟨ r, hr ⟩ := x.2;
        unfold DC; norm_num [ ← hr ];
        unfold coeffConf; norm_num [ Coeff ] ; ring_nf;
        grind +suggestions;
    · convert Submission.Vieta.discCompl_pi1_noncomm using 1;
  -- Since ℂ is contractible, DC × ℂ is homotopy equivalent to DC.
  have h_homotopy_equiv : ContinuousMap.HomotopyEquiv (↥DC × ℂ) (↥DC) := by
    refine' ⟨ _, _, _, _ ⟩;
    exact ContinuousMap.mk ( fun x => x.1 ) ( by continuity );
    exact ContinuousMap.mk ( fun x => ( x, 0 ) ) ( by continuity );
    · refine' ⟨ _, _, _ ⟩;
      refine' ⟨ fun p => ( p.2.1, p.1.val • p.2.2 ), _ ⟩;
      fun_prop; all_goals aesop;
    · exact ⟨ ContinuousMap.Homotopy.refl _ ⟩;
  apply_rules [ Submission.Pi1Transport.noncomm_of_homotopyEquiv ];
  exact h_homotopy_equiv.symm

/-- **The cusp link complement has non-abelian `π₁`.**
Transported from `DC_pi1_noncomm` across `Submission.CuspGeom.dcLinkEquiv`. -/
theorem Link_pi1_noncomm :
    ∃ (x : ↥Link) (a b : FundamentalGroup (↥Link) x), a * b ≠ b * a :=
  Submission.Pi1Transport.noncomm_of_homotopyEquiv dcLinkEquiv.symm DC_pi1_noncomm

end Submission.LinkNonComm