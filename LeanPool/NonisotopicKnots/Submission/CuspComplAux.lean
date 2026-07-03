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
# Auxiliary topological helpers for the cusp-knot complement

* `Submission.CuspComplAux.complEquiv` — a homeomorphism restricts to the complements of a set and
  its image.
* `Submission.CuspComplAux.isPathConnected_ball_diff_center` — a metric ball with its centre
  removed is path-connected (in dimension `> 1`).
-/

open scoped Topology

namespace Submission.CuspComplAux

/-- A homeomorphism `e : A ≃ₜ B` restricts to a homeomorphism between the complement of a set `S`
and the complement of its image `e '' S`. -/
def complEquiv {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (S : Set A) :
    ↥(Sᶜ) ≃ₜ ↥((e '' S)ᶜ) where
  toFun x := ⟨e x.1, by
    have hx := x.2
    simp only [Set.mem_compl_iff] at *
    intro hc
    obtain ⟨a, ha, hea⟩ := hc
    exact hx (by rwa [e.injective hea] at ha)⟩
  invFun y := ⟨e.symm y.1, by
    have hy := y.2
    simp only [Set.mem_compl_iff] at *
    intro hc
    exact hy ⟨e.symm y.1, hc, by simp⟩⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _

@[simp] lemma complEquiv_apply_coe {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (S : Set A) (x : ↥(Sᶜ)) : ((complEquiv e S x : ↥((e '' S)ᶜ)) : B) = e x.1 := rfl

/-- The double-subtype `{x : ↥A // (x:T) ∈ B}` is homeomorphic to `↥(A ∩ B)`. -/
def subtypeInterHomeo {T : Type*} [TopologicalSpace T] (A B : Set T) :
    ↥({x : ↥A | (x : T) ∈ B}) ≃ₜ ↥(A ∩ B : Set T) where
  toFun x := ⟨(x.1 : T), x.1.2, x.2⟩
  invFun y := ⟨⟨(y : T), y.2.1⟩, y.2.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val) _) _

@[simp] lemma subtypeInterHomeo_apply_coe {T : Type*} [TopologicalSpace T] (A B : Set T)
    (x : ↥({x : ↥A | (x : T) ∈ B})) : ((subtypeInterHomeo A B x : ↥(A ∩ B : Set T)) : T) = x.1 :=
  rfl

/-- A homeomorphism `e : A ≃ₜ B` restricts to a homeomorphism `↥S ≃ₜ ↥(e '' S)`. -/
def imageHomeo {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (S : Set A) :
    ↥S ≃ₜ ↥(e '' S) where
  toFun x := ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
  invFun y := ⟨e.symm y.1, by
    obtain ⟨a, ha, hea⟩ := y.2
    have : e.symm y.1 = a := by rw [← hea, e.symm_apply_apply]
    rwa [this]⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _

@[simp] lemma imageHomeo_apply_coe {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (S : Set A) (x : ↥S) : ((imageHomeo e S x : ↥(e '' S)) : B) = e x.1 := rfl

/-
A metric ball with its centre removed is path-connected, in dimension `> 1`.
-/
theorem isPathConnected_ball_diff_center {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 1 < Module.rank ℝ E) (c : E) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball c r \ {c}) := by
  -- Consider the continuous map `f : (Metric.sphere (0:E) 1) ×ˢ (Set.Ioo (0:ℝ) r) → E` (or on the product type), `f (s, t) = c + t • s`.
  have h_cont : IsPathConnected (Set.image (fun p : ℝ × E => c + p.1 • p.2) ((Set.Ioo 0 r) ×ˢ (Metric.sphere (0 : E) 1))) := by
    apply_rules [ IsPathConnected.image, isConnected_Ioo ];
    · -- The interval $(0, r)$ is path-connected.
      have h_interval : IsPathConnected (Set.Ioo (0 : ℝ) r) := by
        exact convex_Ioo _ _ |> fun h => h.isPathConnected ⟨ r / 2, ⟨ by linarith, by linarith ⟩ ⟩;
      have h_sphere : IsPathConnected (Metric.sphere (0 : E) 1) := by
        apply_rules [ isPathConnected_sphere ];
        norm_num;
      rw [ isPathConnected_iff ] at *;
      simp_all +decide [ JoinedIn ];
      intro a b ha hb hb' c d hc hd hd';
      obtain ⟨ γ₁, hγ₁ ⟩ := h_interval a ha hb c hc hd
      obtain ⟨ γ₂, hγ₂ ⟩ := h_sphere.2 b hb' d hd';
      refine' ⟨ _, _ ⟩;
      exact Path.prod γ₁ γ₂;
      exact fun x hx₁ hx₂ => ⟨ hγ₁ x hx₁ hx₂, hγ₂ x hx₁ hx₂ ⟩;
    · fun_prop;
  convert h_cont using 1;
  ext x; simp [Set.mem_image];
  constructor <;> intro h';
  · refine' ⟨ ‖x - c‖, ‖x - c‖⁻¹ • ( x - c ), _, _ ⟩ <;> simp_all +decide [ norm_smul, sub_eq_iff_eq_add ];
    simpa only [ dist_eq_norm ] using h'.1;
  · rcases h' with ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hb' ⟩, rfl ⟩ ; simp +decide [ dist_eq_norm, ha, hb, hb' ];
    exact ⟨ by rw [ norm_smul, Real.norm_of_nonneg ha.le, hb' ] ; linarith, ha.ne', by rintro rfl; norm_num at hb' ⟩

end Submission.CuspComplAux