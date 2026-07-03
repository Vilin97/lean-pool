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
# Keystone cornerstone: `π₁(S¹) ≅ ℤ` via the `Circle.exp` covering

This file develops the classical computation of the fundamental group of the circle as the
integers, using Mathlib's covering-space and monodromy machinery (`Circle.isCoveringMap_exp`,
`IsCoveringMap.monodromy`, path/homotopy lifting).  It is the keystone the documented route to
the unknot side of `exists_nonisotopic_knots` requires (see `PLAN.md`).

The map `Circle.exp : ℝ → Circle` is a covering map whose fibre over `1 : Circle` is the set of
integer multiples of `2π`.  The *monodromy* of a based loop translates this fibre by a fixed
amount; recording that amount (divided by `2π`) gives a group isomorphism
`FundamentalGroup Circle 1 ≃ ℤ` (additively).
-/

open scoped Topology
open IsCoveringMap

noncomputable section

namespace Submission.CircleZ

/-- The covering map `Circle.exp`. -/
theorem cov : IsCoveringMap (Circle.exp) := Circle.isCoveringMap_exp

/-- The chosen base point `0` of the fibre over `1 : Circle`. -/
def e0 : (Circle.exp ⁻¹' {(1 : Circle)}) := ⟨0, by simp⟩

/-- A point of the fibre over `1` has the form `2π·k` for an integer `k`. -/
theorem fiber_mem (e : (Circle.exp ⁻¹' {(1 : Circle)})) : ∃ k : ℤ, (e : ℝ) = k * (2 * Real.pi) := by
  have : Circle.exp (e : ℝ) = 1 := e.2
  rwa [Circle.exp_eq_one] at this

/-- The integer index of a fibre point: `e ↦ e/(2π)`. -/
def fiberIndex (e : (Circle.exp ⁻¹' {(1 : Circle)})) : ℤ := (fiber_mem e).choose

theorem fiberIndex_spec (e : (Circle.exp ⁻¹' {(1 : Circle)})) :
    (e : ℝ) = (fiberIndex e) * (2 * Real.pi) := (fiber_mem e).choose_spec

/-
**Monodromy is a fixed translation of the fibre.** For any loop class `γ` at `1` and any two
fibre points `e₁ e₂`, the displacement produced by the monodromy is the same.
-/
theorem monodromy_translation (γ : Path.Homotopic.Quotient (1 : Circle) 1)
    (e : (Circle.exp ⁻¹' {(1 : Circle)})) :
    ((cov.monodromy γ e : ℝ)) - (e : ℝ) = ((cov.monodromy γ e0 : ℝ)) - (e0 : ℝ) := by
  -- By definition of monodromy, we have `cov.monodromy γ e = cov.liftPath γ e _ 1`.
  unfold IsCoveringMap.monodromy;
  obtain ⟨ γ, rfl ⟩ := Quotient.exists_rep γ;
  -- Since `e` is in the fiber over `1`, we have `e.val = k * (2 * Real.pi)` for some integer `k`.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (e : ℝ) = k * (2 * Real.pi) := fiber_mem e;
  -- By definition of `cov.liftPath`, we have `cov.liftPath γ e _ = fun t => cov.liftPath γ e0 _ t + k * (2 * Real.pi)`.
  have h_lift : cov.liftPath γ (e : ℝ) (by simp [hk]) = fun t => cov.liftPath γ (e0 : ℝ) (by simp [e0]) t + k * (2 * Real.pi) := by
    have h_lift : Continuous (fun t => (cov.liftPath γ e0 (by simp [e0])) t + k * (2 * Real.pi)) ∧ (cov.liftPath γ e0 (by simp [e0])) 0 + k * (2 * Real.pi) = e := by
      refine' ⟨ _, _ ⟩;
      · fun_prop;
      · erw [ IsCoveringMap.liftPath_zero ] ; aesop;
    have h_lift : (Circle.exp ∘ (fun t => (cov.liftPath γ e0 (by simp [e0])) t + k * (2 * Real.pi))) = γ := by
      convert congr_arg ( fun f => f ∘ ( fun t => t ) ) ( IsCoveringMap.liftPath_lifts ( Circle.isCoveringMap_exp ) γ ( e0 : ℝ ) ( by simp [ e0 ] ) ) using 1;
      ext; simp [Circle.exp_add];
    grind +suggestions;
  simp_all +decide [ e0 ];
  erw [ Quotient.lift_mk, Quotient.lift_mk ] ; aesop

/-- The winding number of a loop class at `1`, as an integer. -/
def winding (γ : Path.Homotopic.Quotient (1 : Circle) 1) : ℤ :=
  fiberIndex (cov.monodromy γ e0)

/-
`winding` is additive with respect to concatenation of loop classes.
-/
theorem winding_trans (γ γ' : Path.Homotopic.Quotient (1 : Circle) 1) :
    winding (γ.trans γ') = winding γ + winding γ' := by
  obtain ⟨ γ₁, rfl ⟩ := Quotient.exists_rep γ
  obtain ⟨ γ₂, rfl ⟩ := Quotient.exists_rep γ';
  convert congr_arg ( fun x : ( Circle.exp ⁻¹' { ( 1 : Circle ) } ) => fiberIndex ( cov.monodromy ( ⟦γ₂⟧ ) x ) ) ( show cov.monodromy ( ⟦γ₁⟧ ) e0 = ⟨ winding ⟦γ₁⟧ * ( 2 * Real.pi ), by
                                                                                                                    simp +decide [ Circle.exp_eq_one ] ⟩ from ?_ ) using 1
  generalize_proofs at *;
  · rw [ ← IsCoveringMap.monodromy_trans_apply ];
    rfl;
  · all_goals generalize_proofs at *;
    have := monodromy_translation ( ⟦γ₂⟧ ) ⟨ winding ⟦γ₁⟧ * ( 2 * Real.pi ), by assumption ⟩ ; simp_all +decide [ fiberIndex_spec ] ;
    simp_all +decide [ e0, winding ];
    simp_all +decide [ e0, fiberIndex ];
    exact_mod_cast ( by nlinarith [ Real.pi_pos ] : ( ( _ : ℤ ) : ℝ ) + ( _ : ℤ ) = ( _ : ℤ ) );
  · exact Subtype.ext ( fiberIndex_spec _ )

/-- `winding` evaluated on an element of the fundamental group of the circle. -/
def W (a : FundamentalGroup Circle 1) : ℤ := winding (FundamentalGroup.toPath a)

/-
The identity loop has winding number `0`.
-/
theorem W_one : W 1 = 0 := by
  unfold W;
  unfold winding;
  erw [ IsCoveringMap.monodromy_refl ] ; norm_num [ e0 ];
  exact Int.le_antisymm ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.pi_pos, fiberIndex_spec ⟨ 0, e0._proof_1 ⟩ ] ) ( Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.pi_pos, fiberIndex_spec ⟨ 0, e0._proof_1 ⟩ ] )

/-
`W` turns the group law into addition of winding numbers.
-/
theorem W_mul (a b : FundamentalGroup Circle 1) : W (a * b) = W a + W b := by
  convert winding_trans ( FundamentalGroup.toPath b ) ( FundamentalGroup.toPath a ) using 1;
  exact add_comm _ _

/-
A loop with winding number `0` is null-homotopic.
-/
theorem winding_eq_zero (a : FundamentalGroup Circle 1) (h : W a = 0) : a = 1 := by
  revert h;
  obtain ⟨ γ, rfl ⟩ := Quotient.exists_rep ( FundamentalGroup.toPath a );
  intro h₀
  obtain ⟨ L, hL ⟩ : ∃ L : Path (0 : ℝ) 0, Circle.exp ∘ L = γ := by
    refine' ⟨ _, _ ⟩;
    exact ⟨ cov.liftPath γ e0 ( by simp +decide [ e0 ] ), by
      convert IsCoveringMap.liftPath_zero _ _ _ _, by
      have h_lift : (cov.liftPath γ e0 (by simp [e0])) 1 = 0 := by
        have h_monodromy : cov.monodromy (⟦γ⟧) e0 = ⟨0, by
          simp +decide [ Circle.exp_eq_one ]⟩ := by
          have := fiberIndex_spec ( cov.monodromy ⟦γ⟧ e0 );
          unfold W at h₀; aesop;
        convert congr_arg Subtype.val h_monodromy using 1
      generalize_proofs at *;
      exact h_lift ⟩
    generalize_proofs at *;
    convert IsCoveringMap.liftPath_lifts ( Circle.isCoveringMap_exp ) γ ( e0 : ℝ ) ( by simp +decide [ e0 ] ) using 1;
  -- Since `ℝ` is simply connected, `L` is homotopic (rel endpoints) to the constant path `Path.refl (0:ℝ)` by `SimplyConnectedSpace.paths_homotopic`.
  obtain ⟨ H, hH ⟩ : ∃ H : Path.Homotopic L (Path.refl 0), True := by
    simp +zetaDelta at *;
    exact?;
  obtain ⟨ H, hH ⟩ := H;
  refine' Quotient.sound ⟨ _, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  exact ⟨ fun p => Circle.exp ( H p ), by continuity ⟩;
  all_goals simp_all +decide [ funext_iff, Path.Homotopy ]

/-
Every integer is realised as a winding number.
-/
theorem W_surjective : Function.Surjective W := by
  intro n;
  -- Define the loop `γ : Path (1:Circle) 1` whose underlying map is `t ↦ Circle.exp (n * (2*Real.pi) * (t:ℝ))`.
  obtain ⟨γ, hγ⟩ : ∃ γ : Path (1 : Circle) 1, ∀ t : ↑unitInterval, γ t = Circle.exp (n * (2 * Real.pi) * (t : ℝ)) := by
    refine' ⟨ _, _ ⟩;
    refine' ⟨ _, _, _ ⟩;
    refine' ⟨ fun t => Circle.exp ( n * ( 2 * Real.pi ) * t ), _ ⟩;
    fun_prop;
    all_goals norm_num [ Circle.exp ];
    · rfl;
    · exact Subtype.ext ( Complex.exp_eq_one_iff.mpr ⟨ n, by ring ⟩ );
  -- By uniqueness of lifts, `L = cov.liftPath γ e0 _`.
  have h_lift : cov.liftPath γ e0 (by simp [e0]) = fun t : ↑unitInterval => n * (2 * Real.pi) * (t : ℝ) := by
    have h_lift : Circle.exp ∘ (fun t : ↑unitInterval => n * (2 * Real.pi) * (t : ℝ)) = γ := by
      exact funext fun t => hγ t ▸ rfl;
    have h_lift_unique : ∀ (L : C(↑unitInterval, ℝ)), Circle.exp ∘ L = γ → L 0 = 0 → L = cov.liftPath γ e0 (by simp [e0]) := by
      intros L hL hL0
      have h_lift_unique : L = cov.liftPath γ e0 (by simp [e0]) := by
        have h_lift_unique : Circle.exp ∘ L = γ ∧ L 0 = e0 := by
          exact ⟨ hL, hL0 ⟩
        grind +suggestions;
      exact h_lift_unique;
    exact h_lift_unique ⟨ fun t => n * ( 2 * Real.pi ) * t, by continuity ⟩ h_lift ( by norm_num ) ▸ rfl;
  -- Therefore, `W a = n`.
  use FundamentalGroup.fromPath ⟦γ⟧
  simp [W, h_lift];
  unfold winding;
  erw [ IsCoveringMap.monodromy ];
  erw [ Quotient.lift_mk ] ; simp_all +decide [ fiberIndex ]

/-- `W` packaged as a monoid homomorphism to `Multiplicative ℤ`. -/
def Whom : FundamentalGroup Circle 1 →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (W a)
  map_one' := by simp [W_one]
  map_mul' a b := by simp [W_mul, ofAdd_add]

theorem Whom_injective : Function.Injective Whom := by
  rw [injective_iff_map_eq_one]
  intro a ha
  apply winding_eq_zero
  simpa [Whom, ofAdd_eq_one] using ha

theorem Whom_surjective : Function.Surjective Whom := by
  intro n
  obtain ⟨a, ha⟩ := W_surjective (Multiplicative.toAdd n)
  exact ⟨a, by simp [Whom, ha]⟩

/-- The fundamental group of the circle is isomorphic to `ℤ` (additively). -/
theorem circle_pi1_iso_int :
    Nonempty (Multiplicative ℤ ≃* FundamentalGroup Circle 1) :=
  ⟨(MulEquiv.ofBijective Whom ⟨Whom_injective, Whom_surjective⟩).symm⟩

end Submission.CircleZ