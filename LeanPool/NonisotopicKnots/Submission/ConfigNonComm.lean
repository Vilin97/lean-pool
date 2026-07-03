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

import LeanPool.NonisotopicKnots.Submission.ConfigCover
import LeanPool.NonisotopicKnots.Submission.Monodromy

/-!
# The configuration-space brick: `π₁(Conf / S₃)` is non-abelian

This file builds, soundly and axiom-cleanly, the deepest genuinely-buildable component of the
covering-space route documented in `PLAN.md`: the orbit space `Conf / S₃` of the ordered
configuration space of three points in `ℂ` has non-abelian fundamental group.

The witness is produced via covering-space monodromy (`Submission.ConfigCover.conf_covering`,
`Submission.Monodromy.noncomm_of_monodromy`): two explicit loops at `⟦r0⟧` whose monodromy
permutations of the `S₃`-fiber are right multiplication by the transpositions `(0 1)` and
`(1 2)`, which do not commute.

This is reusable infrastructure; it does not by itself close the configured trefoil theorem,
which additionally needs a homotopy equivalence between the specific trefoil complement and this
model (the geometric bridge, see `PLAN.md`).
-/

namespace Submission.ConfigNonComm

open scoped Topology
open Submission.ConfigCover Complex

/-- The orbit space `Conf / S₃`. -/
abbrev ConfQuot := Quotient (MulAction.orbitRel (Equiv.Perm (Fin 3)) Conf)

/-- The quotient (covering) map `Conf → Conf / S₃`. -/
noncomputable def qmap : Conf → ConfQuot := Quotient.mk _

lemma continuous_qmap : Continuous qmap := continuous_quotient_mk'

/-- The quotient map as a bundled continuous map. -/
noncomputable def pC : C(Conf, ConfQuot) := ⟨qmap, continuous_qmap⟩

/-- Basepoint: the ordered triple `(0, 1, 2)`. -/
def r0 : Conf := ⟨![0, 1, 2], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The transposition `(0 1)`. -/
abbrev s01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
/-- The transposition `(1 2)`. -/
abbrev s12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

/-- Underlying function of the rotation path swapping coordinates `0,1`. -/
noncomputable def q1fun (s : unitInterval) : Fin 3 → ℂ :=
  ![ (1/2) * (1 - Complex.exp (((Real.pi * (s : ℝ)) : ℂ) * Complex.I)),
     (1/2) * (1 + Complex.exp (((Real.pi * (s : ℝ)) : ℂ) * Complex.I)),
     2 ]

/-- Underlying function of the rotation path swapping coordinates `1,2`. -/
noncomputable def q2fun (s : unitInterval) : Fin 3 → ℂ :=
  ![ 0,
     (1/2) * (3 - Complex.exp (((Real.pi * (s : ℝ)) : ℂ) * Complex.I)),
     (1/2) * (3 + Complex.exp (((Real.pi * (s : ℝ)) : ℂ) * Complex.I)) ]

lemma norm_exp_pi_s_I (s : unitInterval) :
    ‖Complex.exp (((Real.pi * (s : ℝ)) : ℂ) * Complex.I)‖ = 1 := by
  -- The norm of the exponential of a purely imaginary number is 1.
  simp [Complex.norm_exp]

lemma q1fun_inj (s : unitInterval) : Function.Injective (q1fun s) := by
  intro i j h;
  fin_cases i <;> fin_cases j <;> simp +decide [ q1fun ] at h ⊢;
  all_goals norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at *;
  all_goals nlinarith [ Real.sin_sq_add_cos_sq ( Real.pi * s ) ]

lemma q2fun_inj (s : unitInterval) : Function.Injective (q2fun s) := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp +decide [ q2fun ] at h ⊢;
  all_goals norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at *;
  all_goals nlinarith [ Real.sin_sq_add_cos_sq ( Real.pi * s ) ]

/-- The continuous parametrization underlying `Q1`. -/
noncomputable def q1map (s : unitInterval) : Conf := ⟨q1fun s, q1fun_inj s⟩
/-- The continuous parametrization underlying `Q2`. -/
noncomputable def q2map (s : unitInterval) : Conf := ⟨q2fun s, q2fun_inj s⟩

lemma q1map_continuous : Continuous q1map := by
  refine' Continuous.subtype_mk _ _;
  exact continuous_pi_iff.mpr fun i => by fin_cases i <;> continuity;

lemma q2map_continuous : Continuous q2map := by
  refine' Continuous.subtype_mk _ _;
  exact continuous_pi_iff.mpr fun i => by fin_cases i <;> continuity;

lemma q1map_zero : q1map 0 = r0 := by
  ext i ; fin_cases i <;> norm_num [ q1map, q1fun, r0 ]

lemma q2map_zero : q2map 0 = r0 := by
  ext i; fin_cases i <;> norm_num [ q2map, q2fun, r0 ] ;

lemma q1map_one : q1map 1 = s01 • r0 := by
  apply Subtype.ext; funext i
  fin_cases i <;>
    simp only [q1map, q1fun, r0, s01, HSMul.hSMul, SMul.smul, Function.comp_apply,
      Set.Icc.coe_one] <;>
    norm_num [Equiv.swap_apply_def, Complex.exp_pi_mul_I]

lemma q2map_one : q2map 1 = s12 • r0 := by
  ext i;
  convert congr_arg _ ?_;
  · ext i; fin_cases i <;> norm_num [ q2map, q2fun, r0, s12 ] ;
    · rfl;
    · rfl;
    · rfl;
  · rfl

/-- The rotation path in `Conf` from `r0` to `s01 • r0`. -/
noncomputable def Q1 : Path r0 (s01 • r0) where
  toFun := q1map
  continuous_toFun := q1map_continuous
  source' := q1map_zero
  target' := q1map_one

/-- The rotation path in `Conf` from `r0` to `s12 • r0`. -/
noncomputable def Q2 : Path r0 (s12 • r0) where
  toFun := q2map
  continuous_toFun := q2map_continuous
  source' := q2map_zero
  target' := q2map_one

/-
`map` by the identity continuous map is the identity.
-/
lemma map_id {X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path.Homotopic.Quotient x y) : γ.map (ContinuousMap.id X) = γ := by
  obtain ⟨ p, rfl ⟩ := γ.exists_rep;
  convert Path.Homotopic.Quotient.mk_map _ _

/-
`qmap` is invariant under the `S₃`-action.
-/
lemma qmap_smul (ρ : Equiv.Perm (Fin 3)) (c : Conf) : qmap (ρ • c) = qmap c := by
  exact Quotient.sound ⟨ ρ, rfl ⟩

/-- The endpoint identification `qmap (σ • r0) = qmap r0`. -/
lemma qmap_smul_r0 (σ : Equiv.Perm (Fin 3)) : qmap (σ • r0) = qmap r0 :=
  qmap_smul σ r0

/-- The first projected loop at `⟦r0⟧`, as a genuine path. -/
noncomputable def loop1Path : Path (qmap r0) (qmap r0) :=
  (Q1.map continuous_qmap).cast rfl (qmap_smul_r0 s01).symm

/-- The second projected loop at `⟦r0⟧`, as a genuine path. -/
noncomputable def loop2Path : Path (qmap r0) (qmap r0) :=
  (Q2.map continuous_qmap).cast rfl (qmap_smul_r0 s12).symm

/-- The first projected loop at `⟦r0⟧`. -/
noncomputable def loop1 : Path.Homotopic.Quotient (qmap r0) (qmap r0) := ⟦loop1Path⟧

/-- The second projected loop at `⟦r0⟧`. -/
noncomputable def loop2 : Path.Homotopic.Quotient (qmap r0) (qmap r0) := ⟦loop2Path⟧

/-
Freeness: `σ • r0 = τ • r0 → σ = τ`.
-/
lemma smul_r0_inj {σ τ : Equiv.Perm (Fin 3)} (h : σ • r0 = τ • r0) : σ = τ := by
  ext i;
  injection h;
  rename_i h; have := congr_fun h ( σ i ) ; have := congr_fun h ( τ i ) ; simp_all +decide [ funext_iff ] ;
  grind

/-
The fiber over `⟦r0⟧` consists of the orbit points `ρ • r0`.
-/
lemma mem_fiber (ρ : Equiv.Perm (Fin 3)) :
    (Quotient.mk (MulAction.orbitRel (Equiv.Perm (Fin 3)) Conf)) (ρ • r0) = qmap r0 := by
  convert qmap_smul ρ r0 using 1

/-
**Per-point monodromy of `loop1`.**
-/
lemma monodromy_loop1 (ρ : Equiv.Perm (Fin 3)) :
    conf_covering.monodromy loop1 ⟨ρ • r0, mem_fiber ρ⟩
      = ⟨(ρ * s01) • r0, mem_fiber (ρ * s01)⟩ := by
  -- Let's simplify the goal using the fact that multiplication by a constant out of the path results in the same path.
  simp [loop1] at *;
  have hbase : (Path.Homotopic.Quotient.mk (Q1.map (continuous_const_smul ρ))).map ⟨qmap, continuous_qmap⟩ = loop1.cast (qmap_smul ρ r0) ((qmap_smul ρ (s01 • r0)).trans (qmap_smul_r0 s01)) := by
    rw [ show loop1 = ⟦loop1Path⟧ from rfl, show loop1Path = ( Q1.map continuous_qmap ).cast rfl ( qmap_smul_r0 s01 ).symm from rfl ] ; simp +decide [ Path.Homotopic.Quotient.mk_map ] ;
    -- Since the paths are the same, their quotient maps are equal.
    apply congr_arg (fun p => Path.Homotopic.Quotient.mk p);
    ext x; exact qmap_smul ρ (Q1 x);
  have := conf_covering.monodromy_map ( Path.Homotopic.Quotient.mk ( Q1.map ( continuous_const_smul ρ ) ) );
  convert this using 1;
  · congr! 2;
    congr! 1;
    convert qmap_smul_r0 ( ρ * s01 ) |> Eq.symm using 1;
  · congr! 1;
    · exact qmap_smul ρ r0 ▸ rfl;
    · exact qmap_smul_r0 ( ρ * s01 ) ▸ rfl;
    · convert hbase.symm using 1;
      ext; simp [loop1Path, loop1];
      grind +suggestions;
    · congr! 1;
      grind +qlia;
  · congr! 1;
    ext; simp [qmap_smul_r0];
    exact ⟨ fun h => h.trans ( qmap_smul_r0 s01 ▸ qmap_smul ρ _ ▸ rfl ), fun h => h.trans ( qmap_smul_r0 s01 ▸ qmap_smul ρ _ ▸ rfl ) ⟩

/-
**Per-point monodromy of `loop2`.**
-/
lemma monodromy_loop2 (ρ : Equiv.Perm (Fin 3)) :
    conf_covering.monodromy loop2 ⟨ρ • r0, mem_fiber ρ⟩
      = ⟨(ρ * s12) • r0, mem_fiber (ρ * s12)⟩ := by
  simp [loop2] at *;
  have hbase : (Path.Homotopic.Quotient.mk (Q2.map (continuous_const_smul ρ))).map ⟨qmap, continuous_qmap⟩ = loop2.cast (qmap_smul ρ r0) ((qmap_smul ρ (s12 • r0)).trans (qmap_smul_r0 s12)) := by
    rw [ show loop2 = ⟦loop2Path⟧ from rfl, show loop2Path = ( Q2.map continuous_qmap ).cast rfl ( qmap_smul_r0 s12 ).symm from rfl ] ; simp +decide [ Path.Homotopic.Quotient.mk_map ] ;
    apply congr_arg (fun p => Path.Homotopic.Quotient.mk p);
    ext x; exact qmap_smul ρ (Q2 x);
  have := conf_covering.monodromy_map ( Path.Homotopic.Quotient.mk ( Q2.map ( continuous_const_smul ρ ) ) );
  convert this using 1;
  · congr! 2;
    congr! 1;
    convert qmap_smul_r0 ( ρ * s12 ) |> Eq.symm using 1;
  · congr! 1;
    · exact qmap_smul ρ r0 ▸ rfl;
    · exact qmap_smul_r0 ( ρ * s12 ) ▸ rfl;
    · convert hbase.symm using 1;
      ext; simp [loop2Path, loop2];
      grind +suggestions;
    · congr! 1;
      grind +qlia;
  · congr! 1;
    ext; simp [qmap_smul_r0];
    exact ⟨ fun h => h.trans ( qmap_smul_r0 s12 ▸ qmap_smul ρ _ ▸ rfl ), fun h => h.trans ( qmap_smul_r0 s12 ▸ qmap_smul ρ _ ▸ rfl ) ⟩

/-
**The configuration brick.** `π₁(Conf / S₃)` is non-abelian.
-/
theorem confQuot_pi1_noncomm :
    ∃ (x : ConfQuot) (a b : FundamentalGroup ConfQuot x), a * b ≠ b * a := by
  by_contra! h;
  -- Since `s12 * s01 ≠ s01 * s12`, the compositions of the monodromies can't be equal.
  have h_val : (conf_covering.monodromy loop1 ∘ conf_covering.monodromy loop2) ⟨r0, rfl⟩ ≠ (conf_covering.monodromy loop2 ∘ conf_covering.monodromy loop1) ⟨r0, rfl⟩ := by
    have := monodromy_loop1 1; have := monodromy_loop2 1; have := monodromy_loop1 s12; have := monodromy_loop2 s01; simp_all +decide [ Function.comp_apply ] ;
    exact fun h => by have := smul_r0_inj h; contradiction;
  convert Submission.Monodromy.noncomm_of_monodromy conf_covering ( ContinuousMap.id ConfQuot ) ( FundamentalGroup.fromPath loop1 ) ( FundamentalGroup.fromPath loop2 ) _ using 1;
  · simp [h]
  · exact Ne.intro fun a => h_val (congrFun a ⟨r0, rfl⟩)

end Submission.ConfigNonComm