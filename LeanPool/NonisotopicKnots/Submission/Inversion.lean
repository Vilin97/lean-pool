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
import LeanPool.NonisotopicKnots.Submission.LineComplement

/-!
# Sphere inversion: the round circle complement is the line-minus-point complement

Let `C = {p : ℝ³ | (p 0)^2 + (p 1)^2 = 1 ∧ p 2 = 0}` be the round unit circle in the `xy`-plane
(the image of the unknot, see `Submission.Helpers.unknot_range`).  Centre the sphere inversion at
`p₀ = (1,0,0) ∈ C`:

  `inv3 x = p₀ + ‖x - p₀‖⁻² • (x - p₀)`.

This is an involutive homeomorphism of `ℝ³ ∖ {p₀}`.  It maps `C ∖ {p₀}` onto the straight line
`Lline = {p | p 0 = 1/2 ∧ p 2 = 0}`, and `p₀ ∉ Lline`.  Since `p₀ ∈ C`, the complement `Cᶜ` is
contained in `{p₀}ᶜ`, and `inv3` never takes the value `p₀`; hence `inv3` restricts to a
homeomorphism

  `Cᶜ  ≃ₜ  (Lline ∪ {p₀})ᶜ`.

This is the reusable geometric reduction for the unknot side of `exists_nonisotopic_knots`:
`π₁` of the round-circle complement is isomorphic to `π₁` of a line complement with one extra
point removed.
-/

open scoped Topology

namespace Submission.Inversion

open LeanEval.KnotTheory

/-- Centre of the inversion: the point `(1,0,0) ∈ C`. -/
noncomputable def p0 : R3 := EuclideanSpace.single 0 1

/-- The round unit circle in the `xy`-plane (image of the unknot). -/
def C : Set R3 := {p : R3 | (p 0) ^ 2 + (p 1) ^ 2 = 1 ∧ p 2 = 0}

/-- The target straight line `{(1/2, s, 0) : s ∈ ℝ}`. -/
def Lline : Set R3 := {p : R3 | p 0 = 1 / 2 ∧ p 2 = 0}

/-- Sphere inversion centred at `p₀` with radius `1`. -/
noncomputable def inv3 (x : R3) : R3 := p0 + (‖x - p0‖ ^ 2)⁻¹ • (x - p0)

/-
`p₀ ∈ C`.
-/
lemma p0_mem_C : p0 ∈ C := by
  constructor <;> norm_num [ p0 ];
  decide +revert

/-
`p₀ ∉ Lline`.
-/
lemma p0_not_mem_Lline : p0 ∉ Lline := by
  exact fun h => absurd h.1 ( by erw [ EuclideanSpace.single_apply ] ; norm_num )

/-
The inversion never outputs its centre.
-/
lemma inv3_ne_p0 {x : R3} (hx : x ≠ p0) : inv3 x ≠ p0 := by
  exact fun h => hx <| by rw [ inv3 ] at h; exact sub_eq_zero.mp <| smul_eq_zero.mp ( sub_eq_zero.mp <| ( by simpa [ hx ] using h ) ) |> Or.resolve_left <| inv_ne_zero <| pow_ne_zero 2 <| norm_ne_zero_iff.mpr <| sub_ne_zero.mpr hx;

/-
The inversion is an involution off the centre.
-/
lemma inv3_involutive {x : R3} (hx : x ≠ p0) : inv3 (inv3 x) = x := by
  unfold inv3;
  simp +decide [ norm_smul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, sq, sub_eq_iff_eq_add ];
  simp +decide [ ← mul_assoc, ← smul_assoc, ne_of_gt ( norm_pos_iff.mpr ( sub_ne_zero.mpr hx ) ) ]

/-
The inversion is continuous away from the centre.
-/
lemma continuousOn_inv3 : ContinuousOn inv3 {p0}ᶜ := by
  refine' ContinuousOn.add continuousOn_const _;
  exact ContinuousOn.smul ( ContinuousOn.inv₀ ( ContinuousOn.pow ( continuousOn_id.sub continuousOn_const |> ContinuousOn.norm ) _ ) fun x hx => pow_ne_zero _ <| ne_of_gt <| norm_pos_iff.mpr <| sub_ne_zero.mpr hx ) ( continuousOn_id.sub continuousOn_const )

/-
**Key geometric computation.** For `x ≠ p₀`, `x` lies on the circle `C` iff its inversion
lies on the line `Lline`.
-/
lemma mem_C_iff_inv3_mem_Lline {x : R3} (hx : x ≠ p0) :
    x ∈ C ↔ inv3 x ∈ Lline := by
  constructor;
  · intro hx';
    constructor <;> norm_num [ inv3, p0 ];
    · rw [ inv_mul_eq_div, add_div', div_eq_iff ] <;> norm_num [ EuclideanSpace.norm_eq, Fin.sum_univ_three ];
      · rw [ Real.sq_sqrt <| by positivity ] ; norm_num [ Fin.ext_iff ] ; nlinarith [ hx'.1, hx'.2 ];
      · simp_all +decide [ C, p0 ];
        exact ne_of_gt <| Real.sqrt_pos.mpr <| by nlinarith [ mul_self_pos.mpr <| show x.ofLp 0 - 1 ≠ 0 from sub_ne_zero.mpr <| by intro h; exact hx <| by ext i; fin_cases i <;> aesop ] ;
      · simp_all +decide [ C ];
        exact ne_of_gt <| Real.sqrt_pos.mpr <| by nlinarith [ mul_self_pos.mpr <| sub_ne_zero.mpr <| show x.ofLp 0 ≠ 1 from fun h => hx <| by ext i; fin_cases i <;> aesop ] ;
    · have := hx'.2; aesop;
  · unfold C Lline inv3 at *;
    norm_num [ p0, EuclideanSpace.norm_eq, Fin.sum_univ_three ] at *;
    grind

/-- Every point of `Cᶜ` is different from `p₀` (since `p₀ ∈ C`). -/
lemma ne_p0_of_mem_Ccompl {x : R3} (hx : x ∈ Cᶜ) : x ≠ p0 := by
  intro h; exact hx (h ▸ p0_mem_C)

/-- The inversion maps `Cᶜ` into `(Lline ∪ {p₀})ᶜ`. -/
lemma inv3_mapsTo : Set.MapsTo inv3 Cᶜ (Lline ∪ {p0})ᶜ := by
  intro x hx
  have hxp0 : x ≠ p0 := ne_p0_of_mem_Ccompl hx
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, not_or]
  refine ⟨?_, inv3_ne_p0 hxp0⟩
  intro hL
  exact hx ((mem_C_iff_inv3_mem_Lline hxp0).2 hL)

/-- The inversion maps `(Lline ∪ {p₀})ᶜ` into `Cᶜ`. -/
lemma inv3_mapsTo' : Set.MapsTo inv3 (Lline ∪ {p0})ᶜ Cᶜ := by
  intro y hy
  have hyp0 : y ≠ p0 := by
    intro h; exact hy (Or.inr (by simp [h]))
  have hyL : y ∉ Lline := fun h => hy (Or.inl h)
  intro hCy
  -- inv3 y ∈ C, with inv3 y ≠ p0, so by the iff applied at inv3 y, inv3 (inv3 y) ∈ Lline, i.e. y ∈ Lline
  have h1 : inv3 y ≠ p0 := inv3_ne_p0 hyp0
  have := (mem_C_iff_inv3_mem_Lline h1).1 hCy
  rw [inv3_involutive hyp0] at this
  exact hyL this

/-- **The inversion homeomorphism** `Cᶜ ≃ₜ (Lline ∪ {p₀})ᶜ`. -/
noncomputable def invHomeo : ↥(Cᶜ : Set R3) ≃ₜ ↥((Lline ∪ {p0})ᶜ : Set R3) where
  toFun x := ⟨inv3 x, inv3_mapsTo x.2⟩
  invFun y := ⟨inv3 y, inv3_mapsTo' y.2⟩
  left_inv x := by
    apply Subtype.ext
    exact inv3_involutive (ne_p0_of_mem_Ccompl x.2)
  right_inv y := by
    apply Subtype.ext
    have hyp0 : (y : R3) ≠ p0 := by
      intro h; exact y.2 (Or.inr (by simp [h]))
    exact inv3_involutive hyp0
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (continuousOn_inv3.comp_continuous continuous_subtype_val ?_)
    intro x
    exact ne_p0_of_mem_Ccompl x.2
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (continuousOn_inv3.comp_continuous continuous_subtype_val ?_)
    intro y h
    exact y.2 (Or.inr (by simp [h]))

/-
The complement of the affine line `Lline = {(1/2, t, 0)}` has abelian `π₁`.
Proved by transporting `Submission.LineComplement.lineCompl_pi1_comm` (the `z`-axis complement,
`LineCompl = {p // p 0 ≠ 0 ∨ p 1 ≠ 0}`) across the affine homeomorphism `T p = (p 0 - 1/2, p 2,
p 1)` of `ℝ³`, which sends `Lline` onto the `z`-axis `{p | p 0 = 0 ∧ p 1 = 0}`.
-/
theorem LlineCompl_abelian (z : ↥((Lline)ᶜ : Set R3))
    (a b : FundamentalGroup _ z) : a * b = b * a := by
  revert a b;
  -- Apply the homeomorphism `T` to transfer the commutativity result from `LineCompl` to `Llineᶜ`.
  obtain ⟨T, hT⟩ : ∃ T : R3 ≃ₜ R3, T '' Lline = {p : R3 | p 0 = 0 ∧ p 1 = 0} := by
    refine' ⟨ _, _ ⟩;
    fapply Homeomorph.mk;
    refine' ⟨ fun p => WithLp.toLp 2 fun i => if i = 0 then p 0 - 1 / 2 else if i = 1 then p 2 else p 1, fun p => WithLp.toLp 2 fun i => if i = 0 then p 0 + 1 / 2 else if i = 1 then p 2 else p 1, _, _ ⟩;
    all_goals norm_num [ Function.LeftInverse, Function.RightInverse, Set.ext_iff ];
    · exact fun x => by ext i; fin_cases i <;> rfl;
    · exact fun x => by ext i; fin_cases i <;> rfl;
    · refine' Continuous.comp _ _;
      · fun_prop;
      · exact continuous_pi_iff.mpr fun i => by fin_cases i <;> [ exact Continuous.sub ( continuous_apply 0 |> Continuous.comp <| continuous_induced_dom ) continuous_const; exact continuous_apply 2 |> Continuous.comp <| continuous_induced_dom; exact continuous_apply 1 |> Continuous.comp <| continuous_induced_dom ] ;
    · refine' Continuous.comp _ _;
      · fun_prop;
      · refine' continuous_pi_iff.mpr _;
        intro i; split_ifs <;> fun_prop;
    · intro x; constructor <;> intro hx <;> simp_all +decide [ Lline ] ;
      · aesop;
      · refine' ⟨ WithLp.toLp 2 ( fun i => if i = 0 then 2⁻¹ else if i = 1 then x.ofLp 2 else 0 ), _, _ ⟩ <;> simp +decide [ hx ];
        ext i; fin_cases i <;> simp +decide [ hx ] ;
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ↥(Llineᶜ : Set R3) ≃ₜ ↥({p : R3 | p 0 = 0 ∧ p 1 = 0}ᶜ : Set R3), True := by
    exact ⟨ by exact ( Submission.Invariant.compl_homeo_of_image_eq T Lline _ hT ).some, trivial ⟩;
  -- Note that `(zaxis)ᶜ = {p : R3 | p 0 ≠ 0 ∨ p 1 ≠ 0}` (the `LineCompl` type).
  have hzaxis_compl : {p : R3 | p 0 = 0 ∧ p 1 = 0}ᶜ = {p : R3 | p 0 ≠ 0 ∨ p 1 ≠ 0} := by
    ext p; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or];
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : ↥({p : R3 | p 0 = 0 ∧ p 1 = 0}ᶜ : Set R3) ≃ₜ Submission.LineComplement.LineCompl, True := by
    exact ⟨ Homeomorph.setCongr hzaxis_compl, trivial ⟩;
  obtain ⟨ψ, hψ⟩ : ∃ ψ : FundamentalGroup (↑Llineᶜ) z ≃* FundamentalGroup Submission.LineComplement.LineCompl (e₂ (e₁ z)), True := by
    have := Submission.Invariant.fundamentalGroup_mulEquiv_of_homeo ( e₁.trans e₂ ) z; aesop;
  exact fun a b => ψ.injective <| by simpa using Submission.LineComplement.lineCompl_pi1_comm ( e₂ ( e₁ z ) ) ( ψ a ) ( ψ b ) ;

end Submission.Inversion