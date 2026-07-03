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


/-!
# A regular `S₃`-covering: the ordered configuration space of three points in `ℂ`

This file builds, soundly and axiom-cleanly, the first concrete brick of the covering-space
route toward `Submission.Helpers.trefoil_compl_pi1_noncomm` (the trefoil complement has
non-abelian `π₁`); see `PLAN.md`.

The right-handed trefoil is the `(2,3)` torus knot, equivalently the link of the cusp
singularity `z² + w³ = 0`; its complement is homotopy equivalent to the discriminant
complement of monic cubics, i.e. the **unordered** configuration space of three distinct points
in `ℂ`.  Over that space sits the **ordered** configuration space `Conf` of three distinct
points, and the quotient map `Conf → Conf / S₃` is a regular covering whose deck group is the
symmetric group `S₃ = Equiv.Perm (Fin 3)`.  Its monodromy is the standard surjection
`π₁ ↠ S₃` sending meridian loops to transpositions, which do not commute — this is what would
ultimately witness non-abelianness.

What is built here (complete proofs, standard axioms only):
* `Conf`, the ordered configuration space of three points in `ℂ` (injective triples).
* `isOpen_conf`: it is an open subset of `Fin 3 → ℂ` (hence locally compact, Hausdorff).
* The coordinate-permutation `MulAction` of `Equiv.Perm (Fin 3)` on `Conf`, with continuity,
  freeness (`IsCancelSMul`) and the resulting `ProperlyDiscontinuousSMul` (a finite group on a
  Hausdorff space).
* `conf_covering`: the quotient map `Conf → Conf / (Equiv.Perm (Fin 3))` is an `IsCoveringMap`,
  obtained from Mathlib's `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`.

The two genuinely hard pieces that remain (documented in `PLAN.md`) are:
* exhibiting two explicit loops in `Conf / S₃` whose monodromy are non-commuting transpositions
  (so that `π₁(Conf / S₃)` is non-abelian), and
* a homotopy equivalence between the **specific** trefoil complement and `Conf / S₃` realizing
  the right-handed trefoil as the link of the cusp.
-/

namespace Submission.ConfigCover

open scoped Topology

/-- The ordered configuration space of three points in `ℂ`: injective triples. -/
abbrev Conf := {r : Fin 3 → ℂ // Function.Injective r}

/-- The set of injective triples is open in `Fin 3 → ℂ`. -/
lemma isOpen_conf : IsOpen {r : Fin 3 → ℂ | Function.Injective r} := by
  have hset : {r : Fin 3 → ℂ | Function.Injective r}
      = ⋂ (p : Fin 3 × Fin 3) (_ : p.1 ≠ p.2), {r : Fin 3 → ℂ | r p.1 ≠ r p.2} := by
    ext r; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hr p hp; exact fun h => hp (hr h)
    · intro hr i j hij; by_contra h; exact hr (i, j) h hij
  rw [hset]
  refine isOpen_iInter_of_finite fun p => isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_ne_fun (continuous_apply p.1) (continuous_apply p.2)

/-- `Equiv.Perm (Fin 3)` acts on `Conf` by permuting the three coordinates. -/
noncomputable instance permConf : MulAction (Equiv.Perm (Fin 3)) Conf where
  smul σ r := ⟨r.1 ∘ σ.symm, r.2.comp σ.symm.injective⟩
  one_smul r := by
    apply Subtype.ext; funext i
    show r.1 ((1 : Equiv.Perm (Fin 3)).symm i) = r.1 i
    rfl
  mul_smul σ τ r := by
    apply Subtype.ext; funext i
    show r.1 ((σ * τ).symm i) = r.1 (τ.symm (σ.symm i))
    have hidx : (σ * τ).symm i = τ.symm (σ.symm i) := by
      simp [Equiv.Perm.mul_apply, mul_inv_rev, ← Equiv.Perm.inv_def]
    rw [hidx]

instance : ContinuousConstSMul (Equiv.Perm (Fin 3)) Conf := by
  constructor
  intro σ
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (σ.symm i)).comp continuous_subtype_val

instance : LocallyCompactSpace Conf := isOpen_conf.locallyCompactSpace

/-- The coordinate-permutation action on injective triples is free. -/
instance : IsCancelSMul (Equiv.Perm (Fin 3)) Conf := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro σ r hr
  have h1 : ∀ i, r.1 (σ.symm i) = r.1 i := fun i => congrFun (congrArg Subtype.val hr) i
  have hfix : ∀ i, σ.symm i = i := fun i => r.2 (h1 i)
  refine Equiv.ext (fun i => ?_)
  have hsi : i = σ i := (Equiv.symm_apply_eq σ).mp (hfix i)
  simp only [Equiv.Perm.coe_one, id]
  exact hsi.symm

/-- **The regular `S₃`-covering.** The quotient map from the ordered configuration space of
three points in `ℂ` to its orbit space under the coordinate-permutation action of
`Equiv.Perm (Fin 3)` is a covering map (the deck group is `S₃`). -/
theorem conf_covering :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel (Equiv.Perm (Fin 3)) Conf)) :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul).isCoveringMap

end Submission.ConfigCover
