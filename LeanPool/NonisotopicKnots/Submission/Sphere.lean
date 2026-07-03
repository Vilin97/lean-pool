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

import LeanPool.NonisotopicKnots.Submission.VanKampen

/-!
# `π₁(S²) = 0`: the 2-sphere is simply connected

This is the canonical first application of the simple-connectivity van Kampen theorem
`Submission.VanKampen.loop_nullhomotopic_of_cover`, and the missing prerequisite (recorded as a
`proof_wanted` upstream) for the point-removal step of the unknot side of the benchmark.

We cover the 2-sphere by the complements of two distinct points; each complement is homeomorphic
(via stereographic projection) to the simply connected plane `ℝ²`, and the intersection
(the sphere minus two points) is path-connected.  Van Kampen then forces every loop to be
null-homotopic.
-/

open scoped Topology unitInterval

noncomputable section

namespace Submission.Sphere

/-- The unit `2`-sphere in `ℝ³`, as a topological space. -/
abbrev S2 : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

instance factFin3 : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

/-! ### General bridges between subtype connectivity and `JoinedIn` / loop-nullity. -/

/-
If the subtype `↥S` is path-connected, any two points of `S` are `JoinedIn S`.
-/
theorem joinedIn_of_subtype_pathConnected {X : Type*} [TopologicalSpace X] (S : Set X)
    [PathConnectedSpace ↥S] {x y : X} (hx : x ∈ S) (hy : y ∈ S) : JoinedIn S x y := by
  obtain ⟨ p, hp ⟩ := ‹PathConnectedSpace S›;
  grind +suggestions

/-
If the subtype `↥S` is simply connected, every loop in `X` whose image lies in `S` is
null-homotopic in `X`.
-/
theorem loop_null_of_subtype_simplyConnected {X : Type*} [TopologicalSpace X] (S : Set X)
    [SimplyConnectedSpace ↥S] {x₀ : X} (hx₀ : x₀ ∈ S) (p : Path x₀ x₀)
    (hp : ∀ t, p t ∈ S) : Path.Homotopic p (Path.refl x₀) := by
  -- Corestrict the loop to the subtype. Define `p' : Path (⟨x₀, hx₀⟩ : ↥S) (⟨x₀, hx₀⟩) := ⟨⟨fun t => ⟨p t, hp t⟩, by continuity⟩, by simp, by simp⟩` (continuity from `p.continuous` into the subtype).
  set p' : Path (⟨x₀, hx₀⟩ : S) (⟨x₀, hx₀⟩ : S) := ⟨⟨fun t => ⟨p t, hp t⟩, by
    exact Continuous.subtype_mk p.continuous _⟩, by
    aesop, by
    aesop⟩
  generalize_proofs at *;
  convert Path.Homotopic.map ( show Path.Homotopic p' ( Path.refl ⟨ x₀, hx₀ ⟩ ) from ?_ ) ( ContinuousMap.mk ( Subtype.val : S → X ) continuous_subtype_val ) using 1;
  grind +suggestions

/-
**Strong converter.**
If the subtype `↥S` is simply connected, every loop in `X` whose image lies in `S` is
null-homotopic through a homotopy *whose image also lies in `S`*.  (This records the
`stays-in-`S`` content that `loop_null_of_subtype_simplyConnected` discards by only stating
`Path.Homotopic` in the ambient `X`.)
-/
theorem loop_null_in_set_of_subtype_simplyConnected {X : Type*} [TopologicalSpace X] (S : Set X)
    [SimplyConnectedSpace ↥S] {x₀ : X} (hx₀ : x₀ ∈ S) (p : Path x₀ x₀)
    (hp : ∀ t, p t ∈ S) :
    ∃ H : Path.Homotopy p (Path.refl x₀), ∀ q, H q ∈ S := by
  obtain ⟨H', hH'⟩ : ∃ H' : Path.Homotopy (⟨⟨fun t => ⟨p t, hp t⟩, by
    exact Continuous.subtype_mk p.continuous _⟩, by
    aesop, by
    aesop⟩ : Path (⟨x₀, hx₀⟩ : S) (⟨x₀, hx₀⟩ : S)) (Path.refl (⟨x₀, hx₀⟩ : S)), True := by
    all_goals generalize_proofs at *;
    have := ‹SimplyConnectedSpace S›;
    rw [ simply_connected_iff_paths_homotopic ] at this;
    obtain ⟨H', hH'⟩ : ∃ H' : Path.Homotopic (⟨⟨fun t => ⟨p t, hp t⟩, by
      assumption⟩, by
      assumption, by
      assumption⟩ : Path (⟨x₀, hx₀⟩ : S) (⟨x₀, hx₀⟩ : S)) (Path.refl (⟨x₀, hx₀⟩ : S)), True := by
      have := this.2 (⟨x₀, hx₀⟩ : S) (⟨x₀, hx₀⟩ : S)
      all_goals generalize_proofs at *;
      simp +zetaDelta at *;
      rename_i h₁ h₂ h₃ h₄;
      exact Quotient.eq.mp ( h₄.elim _ _ )
    generalize_proofs at *;
    exact ⟨ H'.some, trivial ⟩
  generalize_proofs at *;
  refine' ⟨ _, _ ⟩;
  refine' { toContinuousMap := ⟨ fun q => ( H' q : X ), _ ⟩, map_zero_left := _, map_one_left := _, prop' := _ } <;> (try simp +decide [ * ]);
  exacts [ continuous_subtype_val.comp H'.continuous, fun q => ( H' q ).2 ]

/-! ### The pieces of the cover. -/

/-- The complement of a point of `S²` is homeomorphic to the plane `ℝ²`. -/
def complPointHomeo (v : S2) : ↥({v}ᶜ : Set S2) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (Homeomorph.setCongr (stereographic'_source v).symm).trans
    ((stereographic' 2 v).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))

/-- The complement of a point of `S²` is simply connected. -/
instance complPoint_simplyConnected (v : S2) : SimplyConnectedSpace ↥({v}ᶜ : Set S2) :=
  (complPointHomeo v).toHomotopyEquiv.simplyConnectedSpace

/-
The complement of a point of `S²` is path-connected.
-/
instance complPoint_pathConnected (v : S2) : PathConnectedSpace ↥({v}ᶜ : Set S2) := by
  grind +suggestions

/-
The complement of two distinct points of `S²` is path-connected.
-/
theorem complTwo_pathConnected (v w : S2) (h : v ≠ w) :
    PathConnectedSpace ↥(({v, w}ᶜ) : Set S2) := by
  -- Let $f := stereographic' 2 v$. Since $w ≠ v$, $w ∈ f.source = {v}ᶜ$. Set $q := f w : EuclideanSpace ℝ (Fin 2)$.
  set f := stereographic' 2 v
  have hw_source : w ∈ f.source := by
    aesop
  set q := f w;
  -- By `isPathConnected_compl_singleton_of_one_lt_rank` (rank of `ℝ²` is `2 > 1`), `IsPathConnected ({q}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))`.
  have hq_compl : IsPathConnected ({q}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    convert isPathConnected_compl_singleton_of_one_lt_rank _ q;
    rw [ ← Module.finrank_eq_rank ];
    norm_num;
  -- The inverse `f.symm` is `ContinuousOn` `f.target = univ`, hence `ContinuousOn f.symm {q}ᶜ`.
  have h_cont_symm : ContinuousOn f.symm (f.target) := by
    exact f.continuousOn_symm;
  -- Apply `IsPathConnected.image'` to get `IsPathConnected (f.symm '' {q}ᶜ)`.
  have h_image : IsPathConnected (f.symm '' {q}ᶜ) := by
    apply_rules [ IsPathConnected.image', hq_compl ];
    exact h_cont_symm.mono ( by aesop_cat );
  -- Show `f.symm '' ({q}ᶜ) = ({v, w}ᶜ : Set S2)`.
  have h_image_eq : f.symm '' {q}ᶜ = {v, w}ᶜ := by
    ext x;
    constructor <;> intro hx;
    · obtain ⟨ y, hy, rfl ⟩ := hx;
      simp +zetaDelta at *;
      constructor <;> intro H;
      · have := f.symm_mapsTo ( show y ∈ f.target from by simp +decide [ f ] ) ; aesop;
      · have := f.right_inv ( show y ∈ f.target from ?_ ) ; aesop;
        grind +suggestions;
    · use f x;
      simp +zetaDelta at *;
      exact ⟨ fun h => hx.2 <| by have := f.injOn ( show x ∈ f.source from by aesop ) ( show w ∈ f.source from by aesop ) h; aesop, by rw [ f.left_inv ( show x ∈ f.source from by aesop ) ] ⟩;
  convert h_image using 1;
  rw [ h_image_eq, isPathConnected_iff_pathConnectedSpace ]

/-
`S²` has at least three points: for any point there are two further distinct points.
-/
theorem exists_two_ne (x : S2) : ∃ v w : S2, v ≠ w ∧ v ≠ x ∧ w ≠ x := by
  by_contra h;
  -- The sphere `S²` is infinite, so there must be at least two points distinct from `x`.
  have h_infinite : Infinite S2 := by
    refine' Infinite.of_injective ( fun n : ℕ => ⟨ EuclideanSpace.single 0 ( Real.cos ( 1 / ( n + 1 ) ) ) + EuclideanSpace.single 1 ( Real.sin ( 1 / ( n + 1 ) ) ), _ ⟩ ) fun m n hmn => _;
    all_goals norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
    · simp +decide;
    · replace hmn := congr_arg ( fun x => x 0 ) hmn ; norm_num at hmn;
      exact_mod_cast ( by apply_fun Real.arccos at hmn; rw [ Real.arccos_cos, Real.arccos_cos ] at hmn <;> nlinarith [ Real.pi_gt_three, inv_pos.mpr ( by linarith : 0 < ( m : ℝ ) + 1 ), inv_pos.mpr ( by linarith : 0 < ( n : ℝ ) + 1 ), mul_inv_cancel₀ ( by linarith : ( m : ℝ ) + 1 ≠ 0 ), mul_inv_cancel₀ ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] : ( m : ℝ ) = n );
  exact h_infinite.not_finite <| Set.finite_univ_iff.mp <| Set.Finite.subset ( Set.toFinite { x } ) fun y _ => Classical.not_not.1 fun hy => h ⟨ y, by
    exact Exists.imp ( by aesop ) ( Set.Infinite.nonempty ( Set.infinite_univ.diff ( Set.finite_singleton x ) |> Set.Infinite.diff <| Set.finite_singleton y ) ) ⟩

/-
**`π₁(S²) = 0`.** Every loop on the `2`-sphere is null-homotopic.
-/
theorem sphere_loop_null (x₀ : S2) (γ : Path x₀ x₀) : Path.Homotopic γ (Path.refl x₀) := by
  -- Apply the van Kampen theorem with the chosen points `v` and `w` to conclude that every loop in `S2` is null-homotopic.
  have := exists_two_ne x₀;
  obtain ⟨v, w, hvw, hvx₀, hwx₀⟩ := this;
  have hUo : IsOpen ({v}ᶜ : Set S2) := by
    exact isOpen_compl_singleton;
  have hVo : IsOpen ({w}ᶜ : Set S2) := by
    exact isOpen_compl_singleton;
  have hcov : ({v}ᶜ : Set S2) ∪ ({w}ᶜ : Set S2) = Set.univ := by
    grind;
  have hxU : x₀ ∈ ({v}ᶜ : Set S2) := by
    exact hvx₀.symm;
  have hxV : x₀ ∈ ({w}ᶜ : Set S2) := by
    grind;
  exact (by
  apply Submission.VanKampen.loop_nullhomotopic_of_cover hUo hVo hcov hxU hxV;
  · exact fun y hy => joinedIn_of_subtype_pathConnected _ hxU hy;
  · exact fun y hy => joinedIn_of_subtype_pathConnected _ hxV hy;
  · have h_path_connected : PathConnectedSpace ↥({v, w}ᶜ : Set S2) := by
      convert complTwo_pathConnected v w hvw using 1;
    intro y hy; exact (by
    convert joinedIn_of_subtype_pathConnected { v, w }ᶜ _ _ using 1;
    · grind;
    · aesop;
    · aesop);
  · convert loop_null_of_subtype_simplyConnected { v }ᶜ hxU using 1;
  · convert loop_null_of_subtype_simplyConnected { w } ᶜ hxV using 1)

/-- On `S²`, any two paths with the same endpoints are homotopic (since every loop is
null-homotopic by `sphere_loop_null`). -/
theorem sphere_paths_homotopic {x y : S2} (p q : Path x y) : p.Homotopic q := by
  have hloop : (p.trans q.symm).Homotopic (Path.refl x) := sphere_loop_null x (p.trans q.symm)
  -- q ≃ (refl x).trans q ≃ (p.trans q.symm).trans q ≃ p.trans (q.symm.trans q) ≃ p.trans (refl y) ≃ p
  have h1 : ((p.trans q.symm).trans q).Homotopic p := by
    refine (Path.Homotopic.trans_assoc p q.symm q).trans ?_
    refine (Path.Homotopic.hcomp (Path.Homotopic.refl p) (Path.Homotopic.symm_trans q)).trans ?_
    exact Path.Homotopic.trans_refl p
  have h2 : q.Homotopic ((p.trans q.symm).trans q) := by
    refine (Path.Homotopic.refl_trans q).symm.trans ?_
    exact Path.Homotopic.hcomp hloop.symm (Path.Homotopic.refl q)
  exact (h2.trans h1).symm

/-
**The `2`-sphere is simply connected.**
-/
instance : SimplyConnectedSpace S2 := by
  have h_path_connected : PathConnectedSpace S2 := by
    obtain ⟨ v, w, hvw, hvx₀, hwx₀ ⟩ := exists_two_ne ( ⟨ EuclideanSpace.single 0 1, by norm_num ⟩ : S2 );
    have h_path_connected :PathConnectedSpace ↥({v}ᶜ : Set S2) ∧PathConnectedSpace ↥({w}ᶜ : Set S2) := by
      exact ⟨ by infer_instance, by infer_instance ⟩;
    have h_path_connected : IsPathConnected ({v}ᶜ : Set S2) ∧ IsPathConnected ({w}ᶜ : Set S2) := by
      grind +suggestions;
    have h_path_connected : IsPathConnected ({v}ᶜ ∪ {w}ᶜ : Set S2) := by
      apply_rules [ IsPathConnected.union, h_path_connected.1, h_path_connected.2 ];
      exact ⟨ ⟨ EuclideanSpace.single 0 1, by norm_num ⟩, by aesop ⟩;
    convert h_path_connected using 1;
    rw [ show ( { v }ᶜ ∪ { w }ᶜ : Set S2 ) = Set.univ from Set.eq_univ_of_forall fun x => by by_cases hx : x = v <;> by_cases hx' : x = w <;> aesop ] ; simp +decide [ pathConnectedSpace_iff_univ ];
  rw [simply_connected_iff_paths_homotopic']
  exact ⟨h_path_connected, fun p q => sphere_paths_homotopic p q⟩

end Submission.Sphere