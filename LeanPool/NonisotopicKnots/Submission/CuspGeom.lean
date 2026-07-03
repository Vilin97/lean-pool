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
# Cusp geometry brick (WORK IN PROGRESS): weighted-flow deformation retraction

This file develops PLAN step 2 of the cusp-link route: the complement of the cusp discriminant
`Δ = {(p,q) | 4p³ + 27q² = 0} ⊂ ℂ²` deformation-retracts, by the EXPLICIT weighted scaling flow
`(p,q) ↦ (μ²p, μ³q)`, onto its link complement in the weighted sphere `{‖p‖³ + ‖q‖² = 1}`.

`Δ` is invariant under `(p,q) ↦ (λ²p, λ³q)` and contains the origin, so this flow is well defined
on the complement and gives a genuine deformation retraction (no deep Milnor theory needed).

Staged: NOT imported by `Submission.lean` until the whole geometric chain is `sorry`-free.
-/

namespace Submission.CuspGeom

open scoped Topology

/-- The weighted "norm" homogeneous of degree 6 under `(p,q) ↦ (λ²p, λ³q)`. -/
noncomputable def WN (x : ℂ × ℂ) : ℝ := ‖x.1‖ ^ 3 + ‖x.2‖ ^ 2

/-- The cusp discriminant complement in `ℂ²`. -/
def DC : Set (ℂ × ℂ) := {x | 4 * x.1 ^ 3 + 27 * x.2 ^ 2 ≠ 0}

/-- The link complement: the cusp discriminant complement intersected with the weighted sphere. -/
def Link : Set (ℂ × ℂ) := {x | WN x = 1 ∧ 4 * x.1 ^ 3 + 27 * x.2 ^ 2 ≠ 0}

lemma continuous_WN : Continuous WN := by
  unfold WN
  fun_prop

/-
A point of the discriminant complement is nonzero, so its weighted norm is positive.
-/
lemma WN_pos {x : ℂ × ℂ} (hx : x ∈ DC) : 0 < WN x := by
  by_cases hx1 : x.1 = 0 <;> by_cases hx2 : x.2 = 0 <;> simp_all +decide [ DC ];
  · unfold WN; aesop;
  · exact add_pos_of_pos_of_nonneg ( pow_pos ( norm_pos_iff.mpr hx1 ) 3 ) ( sq_nonneg _ );
  · exact add_pos_of_pos_of_nonneg ( pow_pos ( norm_pos_iff.mpr hx1 ) 3 ) ( sq_nonneg _ )

/-- The weighted scaling map `(p,q) ↦ (μ²p, μ³q)` for a real factor `μ`. -/
noncomputable def wscale (μ : ℝ) (x : ℂ × ℂ) : ℂ × ℂ :=
  ((μ : ℂ) ^ 2 * x.1, (μ : ℂ) ^ 3 * x.2)

/-- The discriminant value scales by `μ⁶` under `wscale μ`. -/
lemma disc_wscale (μ : ℝ) (x : ℂ × ℂ) :
    4 * (wscale μ x).1 ^ 3 + 27 * (wscale μ x).2 ^ 2
      = (μ : ℂ) ^ 6 * (4 * x.1 ^ 3 + 27 * x.2 ^ 2) := by
  simp only [wscale]
  ring

/-
The weighted norm scales by `μ⁶` (for `μ ≥ 0`).
-/
lemma WN_wscale {μ : ℝ} (hμ : 0 ≤ μ) (x : ℂ × ℂ) :
    WN (wscale μ x) = μ ^ 6 * WN x := by
  norm_num [ WN, wscale ];
  rw [ abs_of_nonneg hμ ] ; ring

/-- The retraction factor `c x = (WN x)^(-1/6)`. -/
noncomputable def cfac (x : ℂ × ℂ) : ℝ := (WN x) ^ (-(1 : ℝ) / 6)

lemma cfac_pos {x : ℂ × ℂ} (hx : x ∈ DC) : 0 < cfac x := by
  exact Real.rpow_pos_of_pos ( WN_pos hx ) _

lemma continuous_cfac_on : ContinuousOn cfac DC := by
  refine' ContinuousOn.rpow_const _ _;
  · exact continuous_WN.continuousOn;
  · exact fun x hx => Or.inl <| ne_of_gt <| WN_pos hx

/-- The retraction onto the weighted sphere (as a self-map of `ℂ²`). -/
noncomputable def retr (x : ℂ × ℂ) : ℂ × ℂ := wscale (cfac x) x

/-
The retraction lands in the link complement.
-/
lemma retr_mem {x : ℂ × ℂ} (hx : x ∈ DC) : retr x ∈ Link := by
  -- We show that the weighted norm of the retraction is 1.
  have h_wNorm : WN (retr x) = 1 := by
    convert WN_wscale ( le_of_lt ( cfac_pos hx ) ) x using 1;
    rw [ show cfac x = ( WN x ) ^ ( - ( 1 : ℝ ) / 6 ) by rfl, ← Real.rpow_natCast, ← Real.rpow_mul ( le_of_lt ( WN_pos hx ) ) ] ; norm_num;
    rw [ Real.rpow_neg_one, inv_mul_cancel₀ ( ne_of_gt ( WN_pos hx ) ) ];
  refine' ⟨ h_wNorm, _ ⟩;
  exact disc_wscale ( cfac x ) x ▸ mul_ne_zero ( by norm_cast; exact pow_ne_zero _ ( ne_of_gt ( cfac_pos hx ) ) ) hx

/-
On the weighted sphere the retraction is the identity.
-/
lemma retr_eq_self {x : ℂ × ℂ} (hx : x ∈ Link) : retr x = x := by
  obtain ⟨ hx₁, hx₂ ⟩ := hx;
  unfold retr wscale;
  unfold cfac; aesop;

/-! ## The deformation-retraction homotopy equivalence `↥DC ≃ₕ ↥Link`. -/

lemma Link_subset_DC : Link ⊆ DC := fun _ hx => hx.2

/-- The scaling factor of the straight-line homotopy from `id` to `retr`. -/
noncomputable def hmScale (t : ℝ) (x : ℂ × ℂ) : ℝ := (1 - t) + t * cfac x

lemma hmScale_pos {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) {x : ℂ × ℂ} (hx : x ∈ DC) :
    0 < hmScale t x := by
  cases lt_or_eq_of_le ht.1 <;> simp_all +decide [ hmScale ];
  · nlinarith [ cfac_pos hx ];
  · subst_vars; norm_num

/-
Continuity of the retraction as a map of subtypes.
-/
lemma continuous_retrMapFun :
    Continuous (fun x : ↥DC => (⟨retr x.1, retr_mem x.2⟩ : ↥Link)) := by
  refine' Continuous.subtype_mk _ _;
  -- Apply the continuity of the components and the fact that the composition of continuous functions is continuous.
  have h_cont : ContinuousOn (fun x : ℂ × ℂ => ((↑(cfac x))^2 * x.1, (↑(cfac x))^3 * x.2)) DC := by
    exact ContinuousOn.prodMk ( ContinuousOn.mul ( ContinuousOn.pow ( Complex.continuous_ofReal.comp_continuousOn continuous_cfac_on ) _ ) continuousOn_fst ) ( ContinuousOn.mul ( ContinuousOn.pow ( Complex.continuous_ofReal.comp_continuousOn continuous_cfac_on ) _ ) continuousOn_snd );
  exact h_cont.comp_continuous ( continuous_subtype_val ) fun x => x.2

/-- The retraction as a continuous map into the link complement. -/
noncomputable def retrMap : C(↥DC, ↥Link) :=
  ⟨fun x => ⟨retr x.1, retr_mem x.2⟩, continuous_retrMapFun⟩

/-- The inclusion of the link complement into the discriminant complement. -/
def inclMap : C(↥Link, ↥DC) :=
  ⟨fun y => ⟨y.1, Link_subset_DC y.2⟩, by fun_prop⟩

/-
The weighted homotopy stays in the discriminant complement.
-/
lemma hmap_mem (p : ↥unitInterval × ↥DC) :
    wscale (hmScale (p.1 : ℝ) p.2.1) p.2.1 ∈ DC := by
  unfold wscale; simp +decide [ DC, disc_wscale ] ;
  convert mul_ne_zero ( pow_ne_zero 6 ( show ( hmScale p.1 p.2 : ℂ ) ≠ 0 from mod_cast hmScale_pos p.1.2 p.2.2 |> ne_of_gt ) ) p.2.2 using 1 ; ring

/-
Continuity of the weighted homotopy map.
-/
lemma continuous_hmapFun :
    Continuous (fun p : ↥unitInterval × ↥DC =>
      (⟨wscale (hmScale (p.1 : ℝ) p.2.1) p.2.1, hmap_mem p⟩ : ↥DC)) := by
  refine' Continuous.subtype_mk _ _;
  refine' Continuous.prodMk _ _;
  · refine' Continuous.mul _ _;
    · refine' Continuous.pow _ _;
      refine' Complex.continuous_ofReal.comp _;
      refine' Continuous.add _ _;
      · exact continuous_const.sub ( continuous_subtype_val.comp continuous_fst );
      · refine' Continuous.mul _ _;
        · exact continuous_subtype_val.comp continuous_fst;
        · refine' Continuous.rpow _ _ _;
          · exact continuous_WN.comp ( continuous_subtype_val.comp continuous_snd );
          · exact continuous_const;
          · exact fun x => Or.inl <| ne_of_gt <| WN_pos x.2.2;
    · exact continuous_subtype_val.comp continuous_snd |> Continuous.fst;
  · refine' Continuous.mul _ _;
    · refine' Continuous.comp ( Complex.continuous_ofReal.pow 3 ) _;
      refine' Continuous.add _ _;
      · exact continuous_const.sub ( continuous_subtype_val.comp continuous_fst );
      · refine' Continuous.mul _ _;
        · exact continuous_subtype_val.comp continuous_fst;
        · refine' Continuous.rpow _ _ _;
          · exact continuous_WN.comp ( continuous_subtype_val.comp continuous_snd );
          · exact continuous_const;
          · exact fun x => Or.inl <| ne_of_gt <| WN_pos x.2.2;
    · exact continuous_subtype_val.snd.comp continuous_snd

/-- The straight-line weighted homotopy map `(t,x) ↦ wscale (hmScale t x) x`. -/
noncomputable def hmap : C(↥unitInterval × ↥DC, ↥DC) :=
  ⟨fun p => ⟨wscale (hmScale (p.1 : ℝ) p.2.1) p.2.1, hmap_mem p⟩, continuous_hmapFun⟩

lemma hmap_zero (x : ↥DC) : hmap (0, x) = x := by
  exact Subtype.ext ( by unfold hmap wscale hmScale; norm_num )

lemma hmap_one (x : ↥DC) : hmap (1, x) = inclMap (retrMap x) := by
  unfold hmap; unfold retrMap; unfold inclMap; unfold wscale; unfold retr; unfold cfac; norm_num; ring;
  unfold hmScale wscale; norm_num;
  unfold cfac; norm_num;

/-- The straight-line homotopy from the identity to `inclMap ∘ retrMap`. -/
noncomputable def retrHomotopy :
    (ContinuousMap.id ↥DC).Homotopy (inclMap.comp retrMap) where
  toContinuousMap := hmap
  map_zero_left := hmap_zero
  map_one_left := hmap_one

lemma retrMap_comp_inclMap : retrMap.comp inclMap = ContinuousMap.id ↥Link := by
  ext y;
  · exact congr_arg Prod.fst ( retr_eq_self y.2 );
  · exact congr_arg ( fun x => x.2 ) ( retr_eq_self y.2 )

/-- **The cusp-geometry homotopy equivalence.** The cusp discriminant complement is homotopy
equivalent to its link complement in the weighted sphere. -/
noncomputable def dcLinkEquiv : ContinuousMap.HomotopyEquiv ↥DC ↥Link where
  toFun := retrMap
  invFun := inclMap
  left_inv := ContinuousMap.Homotopic.symm ⟨retrHomotopy⟩
  right_inv := by rw [retrMap_comp_inclMap]

end Submission.CuspGeom