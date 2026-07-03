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

import LeanPool.NonisotopicKnots.Submission.CuspGeom

/-!
# The sphere bridge: `{WN = 1} ∖ {N}` is homeomorphic to `ℝ³`

This file builds the homeomorphism between the punctured weighted sphere
`WS = {(p,q) ∈ ℂ² | ‖p‖³ + ‖q‖² = 1}` (which carries the cusp link `Link` of
`Submission.CuspGeom`) and Euclidean `ℝ³`. This is the geometric half of the bridge toward
`Submission.Helpers.trefoil_compl_pi1_noncomm`.

Route:
* `phi : (ℂ × ℂ) ≃ₜ ℝ⁴`, the coordinate (real-linear) homeomorphism;
* `wsToS3 : ↥WS ≃ₜ ↥S3`, radial projection of the (compact) weighted sphere onto the standard
  unit sphere `S3 ⊆ ℝ⁴` (a continuous bijection from a compact space to a Hausdorff space);
* `stereographic'`, Mathlib's stereographic projection `S3 ∖ {v} ≃ₜ ℝ³`.
-/

namespace Submission.SphereBridge

open scoped Topology
open Metric Submission.CuspGeom

noncomputable section

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)
abbrev S3 : Type := sphere (0 : E4) 1

instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

/-- The coordinate homeomorphism `ℂ² ≃ₜ ℝ⁴`, `(p,q) ↦ (p.re, p.im, q.re, q.im)`. -/
def phi : (ℂ × ℂ) ≃ₜ E4 where
  toFun x := !₂[x.1.re, x.1.im, x.2.re, x.2.im]
  invFun y := (Complex.equivRealProdCLM.symm (y 0, y 1), Complex.equivRealProdCLM.symm (y 2, y 3))
  left_inv x := by
    have e : ∀ a b : ℝ, Complex.equivRealProdCLM.symm (a, b) = Complex.mk a b := by
      intro a b; rw [Complex.equivRealProdCLM_symm_apply]; apply Complex.ext <;> simp
    simp only [e]
    ext <;> simp
  right_inv y := by
    ext i
    fin_cases i <;>
      simp [Complex.equivRealProdCLM_symm_apply]
  continuous_toFun := by
    apply (EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous.comp
    apply continuous_pi; intro i
    fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_ <;>
    · exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)

/-- `phi` is a real-linear map: it commutes with nonnegative real scaling. -/
lemma phi_smul (t : ℝ) (x : ℂ × ℂ) : phi (t • x) = t • phi x := by
  ext i
  fin_cases i <;> simp [phi, Prod.smul_def, Complex.smul_re, Complex.smul_im]

@[simp] lemma phi_symm_smul (t : ℝ) (y : E4) : phi.symm (t • y) = t • phi.symm y := by
  have h := phi_smul t (phi.symm y)
  rw [phi.apply_symm_apply] at h
  rw [← h, phi.symm_apply_apply]

/-- The weighted sphere `{WN = 1} ⊆ ℂ²`. -/
def WS : Set (ℂ × ℂ) := {x | WN x = 1}

lemma WS_compact : IsCompact WS := by
  refine' Metric.isCompact_iff_isClosed_bounded.mpr ⟨ _, _ ⟩;
  · exact isClosed_eq ( continuous_WN ) continuous_const;
  · refine' isBounded_iff_forall_norm_le.mpr ⟨ 1, _ ⟩;
    simp +decide [ WS, Prod.norm_def ];
    intro a b h; constructor <;> contrapose! h;
    · exact ne_of_gt ( lt_add_of_lt_of_nonneg ( one_lt_pow₀ h ( by norm_num ) ) ( by positivity ) );
    · exact ne_of_gt ( lt_add_of_nonneg_of_lt ( by positivity ) ( one_lt_pow₀ h two_ne_zero ) )

instance : CompactSpace ↥WS := isCompact_iff_compactSpace.mp WS_compact

/-
`phi` maps every point of the weighted sphere off the origin in `ℝ⁴`.
-/
lemma phi_ne_zero {x : ℂ × ℂ} (hx : x ∈ WS) : phi x ≠ 0 := by
  intro h; have := congr_arg ( fun y => y 0 ) h; norm_num at this; have := congr_arg ( fun y => y 1 ) h; norm_num at this; have := congr_arg ( fun y => y 2 ) h; norm_num at this; have := congr_arg ( fun y => y 3 ) h; norm_num at this; simp_all +decide [ WS ] ;
  have h_contra : x = 0 := by
    exact phi.injective ( h.trans ( phi.apply_symm_apply 0 |> Eq.symm ) );
  unfold WN at hx; aesop;

/-- The underlying radial projection `↥WS → ℝ⁴`. -/
def radialFun (x : ↥WS) : E4 := (‖phi x.1‖⁻¹ : ℝ) • phi x.1

lemma radialFun_mem (x : ↥WS) : radialFun x ∈ sphere (0 : E4) 1 := by
  simp +decide [ radialFun, norm_smul, phi_ne_zero x.2 ]

/-- Radial projection `↥WS → ↥S3`. -/
def wsToS3Fun (x : ↥WS) : S3 := ⟨radialFun x, radialFun_mem x⟩

lemma continuous_wsToS3Fun : Continuous wsToS3Fun := by
  refine' Continuous.subtype_mk _ _;
  refine' Continuous.smul _ _;
  · refine' Continuous.inv₀ _ _;
    · exact Continuous.norm ( phi.continuous.comp continuous_subtype_val );
    · exact fun x => norm_ne_zero_iff.mpr ( phi_ne_zero x.2 );
  · exact phi.continuous.comp continuous_subtype_val

lemma wsToS3Fun_injective : Function.Injective wsToS3Fun := by
  intro x y hxy;
  obtain ⟨l, hl⟩ : ∃ l : ℝ, 0 < l ∧ x.1 = l • y.1 := by
    have h_eq : ∃ l : ℝ, 0 < l ∧ phi x.1 = l • phi y.1 := by
      use ‖phi x.1‖ / ‖phi y.1‖;
      simp_all +decide [ wsToS3Fun, radialFun ];
      have h_pos : 0 < ‖phi x.1‖ ∧ 0 < ‖phi y.1‖ := by
        exact ⟨ norm_pos_iff.mpr ( phi_ne_zero x.2 ), norm_pos_iff.mpr ( phi_ne_zero y.2 ) ⟩;
      convert congr_arg ( fun z => ‖phi x.val‖ • z ) hxy using 1 ; norm_num [ h_pos.1.ne', h_pos.2.ne', smul_smul ];
      exact ⟨ fun h => h.2, fun h => ⟨ div_pos h_pos.1 h_pos.2, h ⟩ ⟩;
    obtain ⟨ l, hl₀, hl ⟩ := h_eq; use l; have := phi.symm_apply_apply ( x : ℂ × ℂ ) ; have := phi.symm_apply_apply ( y : ℂ × ℂ ) ; aesop;
  have h_eq : l^3 * ‖y.val.1‖^3 + l^2 * ‖y.val.2‖^2 = 1 := by
    convert x.2 using 1;
    simp +decide [ WS, hl.2, norm_smul, mul_pow ];
    unfold WN; simp +decide [ norm_smul, abs_of_pos hl.1 ] ; ring;
  have h_eq : ‖y.val.1‖^3 + ‖y.val.2‖^2 = 1 := by
    exact y.2;
  by_cases h_cases : ‖y.val.1‖^3 = 0;
  · simp_all +decide [ pow_succ ];
    norm_num [ show l = 1 by nlinarith ] at * ; aesop;
  · by_cases h_cases : l < 1;
    · nlinarith [ pow_pos hl.1 3, pow_pos hl.1 2, pow_pos hl.1 1, pow_pos hl.1 0, pow_lt_one₀ hl.1.le h_cases ( by norm_num : ( 3 : ℕ ) ≠ 0 ), pow_lt_one₀ hl.1.le h_cases ( by norm_num : ( 2 : ℕ ) ≠ 0 ), pow_lt_one₀ hl.1.le h_cases ( by norm_num : ( 1 : ℕ ) ≠ 0 ), show 0 < ‖ ( y : ℂ × ℂ ).1‖ ^ 3 from lt_of_le_of_ne ( by positivity ) ( Ne.symm ‹_› ) ];
    · by_cases h_cases : l > 1;
      · nlinarith [ pow_lt_pow_right₀ h_cases ( show 2 > 1 by norm_num ), pow_lt_pow_right₀ h_cases ( show 3 > 2 by norm_num ), show 0 < ‖ ( y : ℂ × ℂ ).1‖ ^ 3 by positivity, show 0 ≤ ‖ ( y : ℂ × ℂ ).2‖ ^ 2 by positivity ];
      · norm_num [ show l = 1 by linarith ] at *;
        exact Subtype.ext hl

lemma wsToS3Fun_surjective : Function.Surjective wsToS3Fun := by
  intro x;
  -- Since $u \neq 0$, we can define $g(t) = t^3 * A + t^2 * B$ where $A = \|phi.symm u\|_1^3$ and $B = \|phi.symm u\|_2^2$.
  set u := x.val
  have hu_ne_zero : u ≠ 0 := by
    exact ne_of_apply_ne Norm.norm ( by aesop )
  set w := phi.symm u
  set A := ‖w.1‖^3
  set B := ‖w.2‖^2;
  -- Since $A + B > 0$, we can choose $T$ large enough such that $g(T) \geq 1$.
  obtain ⟨T, hT⟩ : ∃ T : ℝ, 0 < T ∧ T^3 * A + T^2 * B ≥ 1 := by
    by_cases hA : A = 0;
    · simp +zetaDelta at *;
      use 1 / ‖(phi.symm x.val).2‖;
      by_cases h : ‖ ( phi.symm x.val ).2‖ = 0 <;> simp_all +decide [ pow_succ, mul_assoc ];
      exact hu_ne_zero ( phi.symm.injective ( Prod.ext hA h ) );
    · exact ⟨ 1 / A + 1, by positivity, by nlinarith [ show 0 < A by positivity, show 0 ≤ B by positivity, mul_div_cancel₀ 1 hA, pow_two_nonneg ( 1 / A ), pow_two_nonneg ( 1 / A + 1 ) ] ⟩;
  -- By the intermediate value theorem, there exists $t \in [0, T]$ such that $g(t) = 1$.
  obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc 0 T, t^3 * A + t^2 * B = 1 := by
    apply_rules [ intermediate_value_Icc ] <;> norm_num [ hT ];
    · linarith;
    · exact Continuous.continuousOn ( by continuity );
  -- Set `x := phi.symm (t • u)`. Then `phi x = t • u`.
  use ⟨phi.symm (t • u), by
    have h_norm : WN (t • w) = t^3 * A + t^2 * B := by
      unfold WN; simp +decide [ norm_smul, abs_of_nonneg ht.1.1 ] ; ring;
    aesop⟩
  generalize_proofs at *;
  ext i; simp [wsToS3Fun, radialFun];
  simp +decide [ phi_smul, ht.1.1 ];
  rw [ norm_smul, Real.norm_of_nonneg ht.1.1 ] ; by_cases h : t = 0 <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  simp +zetaDelta at *

/-- The radial projection bundled as an equivalence. -/
def wsToS3Equiv : ↥WS ≃ S3 :=
  Equiv.ofBijective wsToS3Fun ⟨wsToS3Fun_injective, wsToS3Fun_surjective⟩

/-- The radial projection is a homeomorphism (continuous bijection from a compact space to a
Hausdorff space). -/
def wsToS3 : ↥WS ≃ₜ S3 :=
  continuous_wsToS3Fun.homeoOfEquivCompactToT2 (f := wsToS3Equiv)

/-- A homeomorphism restricts to the complements of a point and its image. -/
def punctTransport {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (a : X) :
    ↥(({a}ᶜ) : Set X) ≃ₜ ↥(({e a}ᶜ) : Set Y) where
  toFun x := ⟨e x.1, by
    have hx := x.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at *
    intro h; exact hx (e.injective h)⟩
  invFun y := ⟨e.symm y.1, by
    have hy := y.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at *
    intro h; exact hy ((e.apply_symm_apply y.1).symm.trans (congrArg e h))⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  continuous_toFun := Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (e.symm.continuous.comp continuous_subtype_val) _

/-- The full sphere bridge: for a basepoint `v ∈ S3`, the punctured weighted sphere is
homeomorphic to `ℝ³`. -/
def wsPunctToR3 (v : S3) : ↥(({(wsToS3.symm v)}ᶜ) : Set ↥WS) ≃ₜ R3 := by
  -- transport the puncture across `wsToS3`, then apply stereographic projection
  have h1 : ↥(({(wsToS3.symm v)}ᶜ) : Set ↥WS) ≃ₜ ↥(({v}ᶜ) : Set S3) := by
    have hpt : wsToS3 (wsToS3.symm v) = v := wsToS3.apply_symm_apply v
    have hset : ({wsToS3 (wsToS3.symm v)}ᶜ : Set S3) = {v}ᶜ := by rw [hpt]
    exact (punctTransport wsToS3 (wsToS3.symm v)).trans (Homeomorph.setCongr hset)
  have h2 : ↥(({v}ᶜ) : Set S3) ≃ₜ R3 := by
    have h := (stereographic' 3 v).toHomeomorphSourceTarget
    rw [stereographic'_source, stereographic'_target] at h
    exact h.trans (Homeomorph.Set.univ R3)
  exact h1.trans h2

end

end Submission.SphereBridge