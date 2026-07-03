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

import LeanPool.NonisotopicKnots.ChallengeDeps
import LeanPool.NonisotopicKnots.Submission.Invariant
import LeanPool.NonisotopicKnots.Submission.CircleZ
import LeanPool.NonisotopicKnots.Submission.Pi1Comm
import LeanPool.NonisotopicKnots.Submission.PuncturedPlane
import LeanPool.NonisotopicKnots.Submission.LineComplement
import LeanPool.NonisotopicKnots.Submission.VanKampen
import LeanPool.NonisotopicKnots.Submission.Sphere
import LeanPool.NonisotopicKnots.Submission.PuncturedSpace
import LeanPool.NonisotopicKnots.Submission.Inversion
import LeanPool.NonisotopicKnots.Submission.PointRemovalApp
import LeanPool.NonisotopicKnots.Submission.ConfigCover
import LeanPool.NonisotopicKnots.Submission.Monodromy

/-!
# Helper infrastructure for `exists_nonisotopic_knots`

This file develops *sound, reusable* infrastructure toward distinguishing two knots.

The first brick (`isotopic_imp_ambient_homeo`) is the necessary condition underlying every
knot invariant: if two knots are ambient-isotopic in the sense of `Knot.Isotopic`, then there
is a homeomorphism of `ℝ³` carrying the image of the first onto the image of the second.  Any
invariant of the pair `(ℝ³, image)` that is preserved by ambient homeomorphisms therefore
descends to an isotopy invariant.
-/

namespace Submission.Helpers

open LeanEval.KnotTheory
open scoped Topology

/-- The time-`1` map of an ambient isotopy, packaged as a homeomorphism of `ℝ³`. -/
noncomputable def timeOne (Φ : AmbientIsotopy) : R3 ≃ₜ R3 where
  toFun := Φ.H 1
  invFun := Φ.Hinv 1
  left_inv := fun x => Φ.inv_left 1 x
  right_inv := fun x => Φ.inv_right 1 x
  continuous_toFun := by
    have h : Continuous (Function.uncurry Φ.H) := Φ.smooth.continuous
    exact h.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := by
    have h : Continuous (Function.uncurry Φ.Hinv) := Φ.smooth_inv.continuous
    exact h.comp (continuous_const.prodMk continuous_id)

@[simp] lemma timeOne_apply (Φ : AmbientIsotopy) (x : R3) : timeOne Φ x = Φ.H 1 x := rfl

/-- A circle reparametrization is surjective on `ℝ`. -/
lemma reparam_surjective (σ : CircleReparam) : Function.Surjective σ.f :=
  fun y => ⟨σ.finv y, σ.right_inv y⟩

/-- **Reduction to an ambient homeomorphism.**
If `K₁` is ambient-isotopic to `K₂`, then some homeomorphism of `ℝ³` maps the image of `K₁`
onto the image of `K₂`. -/
theorem isotopic_imp_ambient_homeo (K₁ K₂ : Knot) (h : K₁.Isotopic K₂) :
    ∃ e : R3 ≃ₜ R3, e '' (Set.range K₁.curve) = Set.range K₂.curve := by
  obtain ⟨Φ, σ, hΦ⟩ := h
  refine ⟨timeOne Φ, ?_⟩
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨x, ⟨t, rfl⟩, rfl⟩
    exact ⟨σ.f t, (hΦ t).symm⟩
  · rintro y ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := reparam_surjective σ s
    exact ⟨K₁.curve t, ⟨t, rfl⟩, hΦ t⟩

/-! ## The unknot: the round unit circle in the `xy`-plane. -/

/-- The standard parametrization of the unknot. -/
noncomputable def unknotCurve (t : ℝ) : R3 :=
  EuclideanSpace.single 0 (Real.cos t) + EuclideanSpace.single 1 (Real.sin t)

lemma unknotCurve_smooth : ContDiff ℝ (⊤ : ℕ∞) unknotCurve := by
  refine' contDiff_iff_contDiffAt.mpr _;
  intro x;
  refine' ContDiffAt.congr_of_eventuallyEq _ _;
  exact fun t => EuclideanSpace.single 0 ( Real.cos t ) + EuclideanSpace.single 1 ( Real.sin t );
  · refine' ContDiffAt.congr_of_eventuallyEq _ _;
    exact fun t => Real.cos t • EuclideanSpace.single 0 1 + Real.sin t • EuclideanSpace.single 1 1;
    · exact ContDiffAt.add ( ContDiffAt.smul ( Real.contDiff_cos.contDiffAt ) ( contDiffAt_const ) ) ( ContDiffAt.smul ( Real.contDiff_sin.contDiffAt ) ( contDiffAt_const ) );
    · filter_upwards [ ] with t using by ext i; fin_cases i <;> simp +decide [ EuclideanSpace.single_apply ] ;
  · rfl

lemma unknotCurve_periodic : ∀ t, unknotCurve (t + 2 * Real.pi) = unknotCurve t := by
  -- By definition of `unknotCurve`, we have `unknotCurve (t + 2 * Real.pi) = EuclideanSpace.single 0 (Real.cos (t + 2 * Real.pi)) + EuclideanSpace.single 1 (Real.sin (t + 2 * Real.pi))`.
  simp [unknotCurve]

lemma unknotCurve_injOn : Set.InjOn unknotCurve (Set.Ico 0 (2 * Real.pi)) := by
  intro t ht t' ht' h_eq;
  have h_coord : Real.cos t = Real.cos t' ∧ Real.sin t = Real.sin t' := by
    replace h_eq := congr_arg ( fun x => ( x 0, x 1 ) ) h_eq ; simp_all +decide [ unknotCurve ];
  have h_eq : Real.cos (t - t') = 1 := by
    rw [ Real.cos_sub, h_coord.1, h_coord.2 ] ; ring;
    norm_num;
  rw [ Real.cos_eq_one_iff ] at h_eq ; obtain ⟨ k, hk ⟩ := h_eq ; rcases k with ⟨ _ | k ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ]

lemma unknotCurve_immersion : ∀ t, deriv unknotCurve t ≠ 0 := by
  intro t;
  have h_deriv : deriv unknotCurve t = EuclideanSpace.single 0 (-Real.sin t) + EuclideanSpace.single 1 (Real.cos t) := by
    fapply HasDerivAt.deriv;
    rw [ hasDerivAt_iff_tendsto ];
    -- We'll use the fact that the derivative of a sum is the sum of derivatives, and the chain rule to compute the derivative.
    have h_deriv : HasDerivAt (fun t => Real.cos t • EuclideanSpace.single 0 1 + Real.sin t • EuclideanSpace.single 1 1 : ℝ → EuclideanSpace ℝ (Fin 3)) (Real.cos t • EuclideanSpace.single 1 1 - Real.sin t • EuclideanSpace.single 0 1) t := by
      convert HasDerivAt.add ( HasDerivAt.smul ( Real.hasDerivAt_cos t ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.smul ( Real.hasDerivAt_sin t ) ( hasDerivAt_const _ _ ) ) using 1 ; norm_num ; ring;
      congr! 1;
      · abel1;
      · infer_instance;
      · infer_instance;
      · infer_instance;
      · infer_instance;
    rw [ hasDerivAt_iff_tendsto ] at h_deriv;
    convert h_deriv using 3 ; norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] ; ring;
    simp +decide [ unknotCurve ] ; ring;
  intro h; have := congr_arg ( fun x => x 0 ) h; norm_num [ h_deriv ] at this; have := congr_arg ( fun x => x 1 ) h; norm_num [ h_deriv ] at this; nlinarith [ Real.sin_sq_add_cos_sq t ] ;

/-- The unknot as a `Knot`. -/
noncomputable def unknot : Knot where
  curve := unknotCurve
  smooth := unknotCurve_smooth
  periodic := unknotCurve_periodic
  injOn := unknotCurve_injOn
  immersion := unknotCurve_immersion

/-! ## The right-handed trefoil. -/

/-- The standard parametrization of the right-handed trefoil:
`t ↦ (sin t + 2 sin 2t, cos t − 2 cos 2t, −sin 3t)`. -/
noncomputable def trefoilCurve (t : ℝ) : R3 :=
  EuclideanSpace.single 0 (Real.sin t + 2 * Real.sin (2 * t))
    + EuclideanSpace.single 1 (Real.cos t - 2 * Real.cos (2 * t))
    + EuclideanSpace.single 2 (-Real.sin (3 * t))

lemma trefoilCurve_smooth : ContDiff ℝ (⊤ : ℕ∞) trefoilCurve := by
  refine' contDiff_iff_contDiffAt.mpr fun x => _;
  refine' ContDiffAt.congr_of_eventuallyEq _ _;
  exact fun t => ( Real.sin t + 2 * Real.sin ( 2 * t ) ) • EuclideanSpace.single 0 1 + ( Real.cos t - 2 * Real.cos ( 2 * t ) ) • EuclideanSpace.single 1 1 + ( -Real.sin ( 3 * t ) ) • EuclideanSpace.single 2 1;
  · fun_prop;
  · filter_upwards [ ] with t using by ext i; fin_cases i <;> simp +decide [ trefoilCurve ] ;

lemma trefoilCurve_periodic : ∀ t, trefoilCurve (t + 2 * Real.pi) = trefoilCurve t := by
  -- By definition of trefoilCurve, we can expand each component and use the periodicity of sine and cosine.
  intro t
  simp [trefoilCurve, Real.sin_add, Real.cos_add, Real.sin_two_mul, Real.cos_two_mul, Real.sin_three_mul];
  grind

lemma trefoilCurve_injOn : Set.InjOn trefoilCurve (Set.Ico 0 (2 * Real.pi)) := by
  -- By definition of trefoilCurve, we know that its coordinates are given by the parametrization.
  intro t ht t' ht' h_eq
  have h_cos : Real.cos t = Real.cos t' := by
    simp_all +decide [ trefoilCurve ];
    have := congr_arg ( fun x => x 0 ) h_eq; norm_num [ Real.sin_two_mul, Real.cos_two_mul, Real.sin_three_mul ] at this; ( have := congr_arg ( fun x => x 1 ) h_eq; norm_num [ Real.sin_two_mul, Real.cos_two_mul, Real.sin_three_mul ] at this; );
    have := congr_arg ( fun x => x 2 ) h_eq; norm_num [ Real.sin_two_mul, Real.cos_two_mul, Real.sin_three_mul ] at this; ( have := Real.sin_sq_add_cos_sq t; ( have := Real.sin_sq_add_cos_sq t'; ( rw [ ← eq_sub_iff_add_eq' ] at *; ring_nf at *; ) ) );
    grind +revert
  have h_sin : Real.sin t = Real.sin t' := by
    unfold trefoilCurve at h_eq;
    simp_all +decide [ Real.sin_two_mul, Real.cos_two_mul, Real.sin_three_mul ];
    have := congr_arg ( fun x => x 0 ) h_eq; norm_num at this; ( have := congr_arg ( fun x => x 2 ) h_eq; norm_num at this; );
    by_cases h : Real.sin t = Real.sin t' <;> simp_all +decide;
    rw [ Real.cos_eq_cos_iff ] at h_cos;
    rcases h_cos with ⟨ k, rfl | rfl ⟩ <;> rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at * <;> try nlinarith [ Real.pi_pos ];
    · norm_num [ show t = 0 by linarith ] at *;
    · exact h ( by nlinarith [ Real.sin_sq_add_cos_sq t, Real.sin_le_one t, Real.cos_le_one t ] );
  have h_eq : Real.cos (t - t') = 1 := by
    rw [ Real.cos_sub, h_cos, h_sin ] ; ring ; norm_num [ Real.cos_sq' ] ;
  rw [ Real.cos_eq_one_iff ] at h_eq ; obtain ⟨ k, hk ⟩ := h_eq ; rcases k with ⟨ _ | k ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ]

lemma trefoilCurve_immersion : ∀ t, deriv trefoilCurve t ≠ 0 := by
  intro t ht
  have h_comp : (Real.cos t + 4 * Real.cos (2 * t)) = 0 ∧ (-Real.sin t + 4 * Real.sin (2 * t)) = 0 ∧ (-3 * Real.cos (3 * t)) = 0 := by
    convert congr_arg ( fun x : R3 => ( x 0, x 1, x 2 ) ) ht using 1;
    rw [ show trefoilCurve = fun t => ( Real.sin t + 2 * Real.sin ( 2 * t ) ) • EuclideanSpace.single 0 1 + ( Real.cos t - 2 * Real.cos ( 2 * t ) ) • EuclideanSpace.single 1 1 + ( -Real.sin ( 3 * t ) ) • EuclideanSpace.single 2 1 from funext fun t => by ext i; fin_cases i <;> simp +decide [ trefoilCurve ] ];
    erw [ HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.smul ( HasDerivAt.add ( Real.hasDerivAt_sin t ) ( HasDerivAt.const_mul 2 ( HasDerivAt.sin ( hasDerivAt_id' t |> HasDerivAt.const_mul 2 ) ) ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.smul ( HasDerivAt.sub ( Real.hasDerivAt_cos t ) ( HasDerivAt.const_mul 2 ( HasDerivAt.cos ( hasDerivAt_id' t |> HasDerivAt.const_mul 2 ) ) ) ) ( hasDerivAt_const _ _ ) ) ) ( HasDerivAt.smul ( HasDerivAt.neg ( HasDerivAt.sin ( hasDerivAt_id' t |> HasDerivAt.const_mul 3 ) ) ) ( hasDerivAt_const _ _ ) ) ) ] ; norm_num [ mul_comm ];
    grind +locals;
  nlinarith [ Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq ( 2 * t ), Real.sin_two_mul t, Real.cos_two_mul t, Real.cos_three_mul t ]

/-- The right-handed trefoil as a `Knot`. -/
noncomputable def trefoil : Knot where
  curve := trefoilCurve
  smooth := trefoilCurve_smooth
  periodic := trefoilCurve_periodic
  injOn := trefoilCurve_injOn
  immersion := trefoilCurve_immersion

/-! ## The distinguishing invariant.

The remaining mathematical content is that the unknot and the trefoil have no ambient
homeomorphism of `ℝ³` carrying one image onto the other.  We isolate this into the two
fundamental-group facts that make the distinction: the complement of the unknot has abelian
π₁, while the complement of the trefoil does not.  The reduction `no_ambient_homeo_unknot_trefoil`
below is proved soundly from these two facts via the bricks in `Submission.Invariant`. -/

/-
The image of the unknot is exactly the round unit circle in the `xy`-plane:
the set of points with `(p 0)^2 + (p 1)^2 = 1` and `p 2 = 0`.  This is the geometric
description a linking-phase map needs in order to be well-defined on the complement.
-/
theorem unknot_range :
    Set.range unknot.curve = {p : R3 | (p 0) ^ 2 + (p 1) ^ 2 = 1 ∧ p 2 = 0} := by
  ext p;
  constructor;
  · rintro ⟨ t, rfl ⟩ ;
    simp +decide [ unknot, unknotCurve ];
  · intro hp
    obtain ⟨t, ht⟩ : ∃ t : ℝ, Real.cos t = p 0 ∧ Real.sin t = p 1 := by
      use ( Complex.arg ( p.ofLp 0 + p.ofLp 1 * Complex.I ) );
      rw [ Complex.cos_arg, Complex.sin_arg ] <;> norm_num [ Complex.ext_iff ];
      · norm_num [ Complex.normSq, Complex.norm_def, ← sq, hp.1 ];
      · rintro h0 h1; have := hp.1; rw [h0, h1] at this; norm_num at this;
    use t; simp_all +decide [ unknot ] ;
    ext i; fin_cases i <;> simp +decide [ *, unknotCurve ] ;

/-- **Unknot side.** The fundamental group of the complement of the unknot image is abelian. -/
theorem unknot_compl_pi1_comm (x : ↥(Set.range unknot.curve)ᶜ)
    (a b : FundamentalGroup _ x) : a * b = b * a := by
  have hset : (Set.range unknot.curve)ᶜ = (Submission.Inversion.C)ᶜ := by
    rw [unknot_range]; rfl
  let e : ↥((Set.range unknot.curve)ᶜ) ≃ₜ ↥((Submission.Inversion.C)ᶜ) :=
    Homeomorph.setCongr hset
  obtain ⟨ψ⟩ := Submission.Invariant.fundamentalGroup_mulEquiv_of_homeo e x
  have hcomm := Submission.PointRemovalApp.C_compl_pi1_comm (e x) (ψ a) (ψ b)
  have hψ : ψ (a * b) = ψ (b * a) := by rw [map_mul, map_mul]; exact hcomm
  exact ψ.injective hψ

-- `trefoil_compl_pi1_noncomm` and `no_ambient_homeo_unknot_trefoil` now live in
-- `Submission/TrefoilNonComm.lean` (same `Submission.Helpers` namespace), where the explicit
-- algebraic equation `Submission.Bridge.Fbridge` of the trefoil is also in scope.

end Submission.Helpers