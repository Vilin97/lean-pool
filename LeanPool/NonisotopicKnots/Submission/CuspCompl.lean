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

import LeanPool.NonisotopicKnots.Submission.CuspKnotMap
import LeanPool.NonisotopicKnots.Submission.CuspParam
import LeanPool.NonisotopicKnots.Submission.CuspComplAux
import LeanPool.NonisotopicKnots.Submission.CurveConn
import LeanPool.NonisotopicKnots.Submission.LinkNonComm
import LeanPool.NonisotopicKnots.Submission.Pi1Iso
import LeanPool.NonisotopicKnots.Submission.Pi1Transport
import LeanPool.NonisotopicKnots.Submission.Sphere
import LeanPool.NonisotopicKnots.ChallengeDeps

/-!
# The cusp-knot complement has non-abelian `π₁`

Assembling the pieces: the cusp link on the weighted sphere `WS` is sent (by stereographic
projection from the puncture `vpt`) to the smooth knot `cuspKnot` in `ℝ³`, and its complement is
homeomorphic to `Link ∖ {N}`.  Non-abelianness of `π₁(Link)` plus a van Kampen point-removal
(`Submission.Pi1Iso.noncomm_of_cover`) then give a non-abelian `π₁` for `ℝ³ ∖ cuspKnot`.
-/

namespace Submission.CuspCompl

open scoped Topology
open Metric Submission.SphereBridge Submission.CuspGeom Submission.CuspKnot Submission.CuspKnotMap
open Submission.CuspParam Submission.CuspComplAux
open LeanEval.KnotTheory

noncomputable section

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The stereographic chart of `S³` with pole `w`, as a total homeomorphism of the complement of
`w` with `ℝ³`. -/
def poleHomeo (w : S3) : ↥(({w}ᶜ) : Set S3) ≃ₜ R3 := by
  have h := (stereographic' 3 w).toHomeomorphSourceTarget
  rw [stereographic'_source, stereographic'_target] at h
  exact h.trans (Homeomorph.Set.univ R3)

lemma poleHomeo_apply (w : S3) (x : ↥(({w}ᶜ) : Set S3)) :
    poleHomeo w x = stereographic' 3 w (x : S3) := by
      simp +decide [ poleHomeo, Homeomorph.trans_apply, OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe, Homeomorph.Set.univ ];
      convert OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe _ _;
      all_goals norm_num [ stereographic'_target, stereographic'_source ];
      all_goals congr! 1;
      all_goals congr! 1;
      all_goals congr! 1;
      all_goals congr! 1;
      all_goals norm_num [ stereographic'_source ];
      · congr! 1;
        ext; simp [stereographic'_source];
      · congr! 1

/-- The cusp curve as a point of `S³`. -/
def uvecS3 (θ : ℝ) : S3 := ⟨uvec θ, uvec_mem θ⟩

/-- The image of the cusp knot on `S³` (the `(2,3)`-torus knot). -/
def knotS : Set S3 := Set.range uvecS3

lemma uvecS3_ne_vpt (θ : ℝ) : uvecS3 θ ≠ vpt := uvec_ne_vpt θ

lemma knotS_subset_compl_vpt : knotS ⊆ ({vpt}ᶜ : Set S3) := by
  exact Set.range_subset_iff.mpr fun θ => uvecS3_ne_vpt θ

lemma vpt_not_knotS : vpt ∉ knotS := by
  rintro ⟨θ, hθ⟩
  exact uvecS3_ne_vpt θ hθ

lemma uvec_periodic (θ : ℝ) : uvec (θ + 2 * Real.pi) = uvec θ := by
  unfold uvec; norm_num [ mul_add, Real.cos_add, Real.sin_add ] ;
  norm_num [ Real.cos_two_mul, Real.sin_two_mul, Real.cos_three_mul, Real.sin_three_mul ]

lemma uvecS3_continuous : Continuous uvecS3 := by
  refine' Continuous.subtype_mk _ _;
  exact uvec_contDiff.continuous

lemma knotS_eq_image_Icc : knotS = uvecS3 '' Set.Icc 0 (2 * Real.pi) := by
  ext x;
  constructor;
  · rintro ⟨ θ, rfl ⟩;
    obtain ⟨ θ', hθ', hθ'' ⟩ := Function.Periodic.exists_mem_Ico₀ ( show Function.Periodic uvecS3 ( 2 * Real.pi ) from fun x => by
                                                                      exact Subtype.ext <| uvec_periodic x ) ( show 0 < 2 * Real.pi by positivity ) θ
    generalize_proofs at *;
    grind;
  · exact fun ⟨ y, hy, hx ⟩ => hx ▸ Set.mem_range_self _

lemma knotS_compact : IsCompact knotS := by
  rw [knotS_eq_image_Icc];
  exact CompactIccSpace.isCompact_Icc.image uvecS3_continuous

lemma knotS_closed : IsClosed knotS := knotS_compact.isClosed

lemma cuspCurve_eq (θ : ℝ) :
    cuspCurve θ = poleHomeo vpt ⟨uvecS3 θ, uvecS3_ne_vpt θ⟩ := by
      rw [ poleHomeo_apply, cuspCurve_stereo ];
      rfl

lemma range_cuspCurve_eq :
    Set.range cuspCurve
      = poleHomeo vpt '' {y : ↥(({vpt}ᶜ) : Set S3) | (y : S3) ∈ knotS} := by
        ext x;
        constructor;
        · rintro ⟨ θ, rfl ⟩;
          use ⟨ uvecS3 θ, uvecS3_ne_vpt θ ⟩;
          exact ⟨ Set.mem_range_self _, cuspCurve_eq θ ▸ rfl ⟩;
        · rintro ⟨ y, hy, rfl ⟩;
          obtain ⟨ θ, hθ ⟩ := hy;
          use θ;
          convert cuspCurve_eq θ using 1;
          exact congr_arg _ ( Subtype.ext hθ.symm )

/-! ## `π₁` of the `S³` knot complement is non-abelian (transport of `Link_pi1_noncomm`). -/

/-- The cusp slice of the weighted sphere, viewed in `↥WS`. -/
def cuspSet : Set ↥WS := {x | (x : ℂ × ℂ) ∉ DC}

lemma Lsub_mem_cuspSet (θ : ℝ) : Lsub θ ∈ cuspSet := by
  convert Set.mem_setOf_eq.mpr _ using 1;
  unfold Lsub; simp +decide [ DC, Lcurve ] ; ring_nf ;
  norm_cast ; norm_num [ aa_cube, bb_sq ] ; ring;
  rw [ ← Complex.exp_nat_mul, ← Complex.exp_nat_mul ] ; ring

lemma cuspSet_eq_range : cuspSet = Set.range Lsub := by
  ext x
  simp [cuspSet, Lsub];
  constructor;
  · intro hx_not_DC
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Lcurve θ = x := by
      apply Submission.CuspParam.cusp_param x.1 x.2;
      exact Classical.not_not.1 hx_not_DC;
    exact ⟨ θ, Subtype.ext hθ ⟩;
  · rintro ⟨ y, rfl ⟩ ; exact Lsub_mem_cuspSet y;

lemma wsToS3_Lsub_eq (θ : ℝ) : wsToS3 (Lsub θ) = uvecS3 θ := by
  exact Subtype.ext ( wsToS3_Lsub θ )

lemma wsToS3_image_cuspSet : wsToS3 '' cuspSet = knotS := by
  ext; simp [knotS, cuspSet_eq_range];
  simp +decide [ wsToS3_Lsub_eq ]

/-
`↥Link` is homeomorphic to the `S³` knot complement `↥(knotSᶜ)`.
-/
lemma nonempty_Link_homeo : Nonempty (↥Link ≃ₜ ↥(knotSᶜ : Set S3)) := by
  refine' ⟨ _ ⟩;
  -- Apply the homeomorphism between `Link` and `WS ∩ DC`.
  have h_homeo : Nonempty (↥Link ≃ₜ ↥(WS ∩ DC)) := by
    refine' ⟨ Homeomorph.setCongr _ ⟩;
    ext; simp [Link, WS, DC];
  refine' h_homeo.some.trans _;
  convert Homeomorph.trans ( Homeomorph.trans ( Homeomorph.trans ( Homeomorph.setCongr ?_ ) ( ( subtypeInterHomeo WS DC ).symm ) ) ( Homeomorph.setCongr ?_ ) ) ( complEquiv wsToS3 cuspSet ) using 1;
  · rw [ wsToS3_image_cuspSet ];
  · congr! 1;
    ext; simp [wsToS3_image_cuspSet];
  · rfl;
  · ext; simp [cuspSet]

theorem X_noncomm :
    ∃ (x : ↥(knotSᶜ : Set S3)) (a b : FundamentalGroup (↥(knotSᶜ : Set S3)) x), a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_Link_homeo
  exact Submission.Pi1Transport.noncomm_of_homeo e.symm Submission.LinkNonComm.Link_pi1_noncomm

/-! ## The point-removal cover at `vpt`. -/

/-- Base space for the point removal: the `S³` knot complement `S³ ∖ knot`. -/
abbrev X : Type := ↥(knotSᶜ : Set S3)

/-- The puncture, as a point of `X`. -/
def vptX : X := ⟨vpt, vpt_not_knotS⟩

lemma vpt_ne_neg : vpt ≠ -vpt := by
  rw [ Ne.eq_def, eq_comm ];
  intro h;
  convert congr_arg Subtype.val h using 1 ; norm_num [ uvec ];
  erw [ neg_eq_iff_add_eq_zero ];
  erw [ show vpt = wsToS3 Nsub from rfl ] ; norm_num [ Nsub, Npt ];
  erw [ show wsToS3 ⟨ ( 0, Complex.I ), _ ⟩ = ⟨ _, _ ⟩ from rfl ] ; norm_num [ Subtype.ext_iff ];
  unfold radialFun; norm_num [ Complex.ext_iff ] ;
  norm_num [ ← two_smul ℝ, phi ]

lemma negvpt_not_knotS : (-vpt) ∉ knotS := by
  intro h_neg_vpt_in_knotS
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, uvecS3 θ = -vpt := h_neg_vpt_in_knotS
  convert congr_arg Subtype.val hθ using 1 ; norm_num [ uvec ];
  unfold uvecS3 vpt; norm_num [ uvec ] ;
  erw [ show wsToS3 Nsub = ⟨ _, _ ⟩ from rfl ] ; norm_num [ Subtype.ext_iff ] ; unfold radialFun; norm_num [ Complex.ext_iff ] ;
  unfold phi Nsub; norm_num [ Complex.ext_iff ] ; ring_nf ; norm_num [ cc_pos.ne', aa_neg.ne, bb_pos.ne' ] ;
  intro h; have := congr_arg ( fun x => x 0 ) h; norm_num [ Npt ] at this; have := congr_arg ( fun x => x 1 ) h; norm_num [ Npt ] at this;
  rcases this with ( h | h | h ) <;> simp_all +decide [ cc_pos.ne', aa_neg.ne ];
  nlinarith [ Real.sin_sq_add_cos_sq ( θ * 2 ) ]

lemma vpt_mem_compl_neg : vpt ∈ ({-vpt}ᶜ : Set S3) := by
  simp [vpt_ne_neg]

/-- The chart centred away from `-vpt`, so `vpt` is in its domain. -/
def gg : ↥(({-vpt}ᶜ) : Set S3) ≃ₜ R3 := poleHomeo (-vpt)

/-- The image of `vpt` in the chart. -/
def c0 : R3 := gg ⟨vpt, vpt_mem_compl_neg⟩

/-- The chart-image of the knot. -/
def knotImg : Set R3 := gg '' {y : ↥(({-vpt}ᶜ) : Set S3) | (y : S3) ∈ knotS}

lemma knotImg_compact : IsCompact knotImg := by
  convert ( isCompact_range ( show Continuous ( fun x : ↥knotS => gg ⟨ x, by
                                exact fun h => negvpt_not_knotS <| by aesop; ⟩ ) from ?_ ) ) using 1
  generalize_proofs at *;
  · ext; simp [knotImg];
    constructor
    · rintro ⟨a, h, hk, _, hgg⟩
      exact ⟨a, h, hk, hgg⟩
    · rintro ⟨a, h, hk, hgg⟩
      exact ⟨a, h, hk, fun heq => negvpt_not_knotS (heq ▸ hk), hgg⟩
  · exact isCompact_iff_compactSpace.mp ( knotS_compact );
  · exact gg.continuous.comp ( continuous_subtype_val.subtype_mk _ )

lemma knotImg_nonempty : knotImg.Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x : S3, x ∈ knotS ∧ x ≠ -vpt := by
    exact ⟨ _, Set.mem_range_self 0, ne_of_mem_of_not_mem ( Set.mem_range_self 0 ) negvpt_not_knotS ⟩;
  exact ⟨ _, ⟨ ⟨ x, by aesop ⟩, by aesop ⟩ ⟩

lemma c0_not_knotImg : c0 ∉ knotImg := by
  simp +decide [ c0, knotImg ];
  -- Apply the lemma that states vpt is not in knotS.
  apply vpt_not_knotS

/-- Radius of the puncture ball in the chart. -/
def rad : ℝ := Metric.infDist c0 knotImg

lemma rad_pos : 0 < rad := by
  simp [rad, Metric.infDist_pos_iff_notMem_closure, knotImg_compact.isClosed, knotImg_nonempty, c0_not_knotImg];
  convert Metric.infDist_pos_iff_notMem_closure knotImg_nonempty |>.2 _;
  rw [ Metric.infDist_pos_iff_notMem_closure ];
  · exact knotImg_nonempty;
  · rw [ Metric.infDist_eq_iInf ];
    -- Since $c0$ is not in the knot image, there exists a positive distance between $c0$ and the knot image.
    have h_dist_pos : ∃ ε > 0, ∀ y ∈ knotImg, ε ≤ dist c0 y := by
      have h_dist_pos : IsClosed knotImg := by
        exact IsCompact.isClosed ( knotImg_compact );
      exact Metric.mem_nhds_iff.mp ( h_dist_pos.isOpen_compl.mem_nhds c0_not_knotImg ) |> fun ⟨ ε, ε_pos, hε ⟩ => ⟨ ε, ε_pos, fun y hy => le_of_not_gt fun h => hε ( Metric.mem_ball'.mpr h ) hy ⟩;
    obtain ⟨ ε, ε_pos, hε ⟩ := h_dist_pos;
    refine' lt_of_lt_of_le ε_pos ( le_csInf _ _ );
    · exact ⟨ _, ⟨ ⟨ knotImg_nonempty.some, by
        exact knotImg_nonempty.choose_spec ⟩, rfl ⟩ ⟩;
    · aesop

/-- The neighbourhood of the puncture in `S³` (a chart ball), automatically inside `knotSᶜ`. -/
def Wset : Set S3 := Subtype.val '' (gg ⁻¹' (Metric.ball c0 rad))

lemma Wset_subset_knotScompl : Wset ⊆ (knotSᶜ : Set S3) := by
  intro s hs; obtain ⟨ y, hy, rfl ⟩ := hs; simp_all +decide [ Set.mem_setOf_eq, Set.mem_compl_iff ] ;
  contrapose! hy; simp_all +decide [ rad ] ;
  exact le_trans ( infDist_le_dist_of_mem ( Set.mem_image_of_mem _ hy ) ) ( by rw [ dist_comm ] )

lemma vpt_mem_Wset : vpt ∈ Wset := by
  exact ⟨ ⟨ vpt, vpt_mem_compl_neg ⟩, by simp +decide [ c0, rad_pos ], rfl ⟩

lemma Wset_open : IsOpen Wset := by
  refine' isOpen_iff_forall_mem_open.mpr _;
  rintro x ⟨ y, hy, rfl ⟩;
  refine' ⟨ Subtype.val '' ( gg ⁻¹' ( Metric.ball c0 rad ) ∩ Set.univ ), _, _, _ ⟩ <;> norm_num [ Set.image_subset_iff ];
  · exact fun x hx => ⟨ x, hx, rfl ⟩;
  · apply_rules [ IsOpen.isOpenMap_subtype_val ];
    · exact isOpen_compl_singleton;
    · exact gg.continuous.isOpen_preimage _ Metric.isOpen_ball;
  · exact ⟨ y.2, hy ⟩

/-- The neighbourhood of the puncture inside `X`. -/
def Vnb : Set X := {x | (x : S3) ∈ Wset}

lemma Vnb_open : IsOpen Vnb := by
  convert IsOpen.preimage ( continuous_subtype_val ) ( Wset_open ) using 1

lemma vptX_mem_Vnb : vptX ∈ Vnb := by
  exact vpt_mem_Wset

/-! ### Homeomorphisms feeding the connectivity hypotheses. -/

lemma nonempty_U_homeo :
    Nonempty (↥(({vptX}ᶜ) : Set X) ≃ₜ ↥((Set.range cuspCurve)ᶜ : Set R3)) := by
      refine' ⟨ _ ⟩;
      -- Apply the homeomorphism `h` to the complement of the range of `cuspCurve`.
      have h_compl : Nonempty (↥((knotSᶜ : Set S3) ∩ ({vpt}ᶜ : Set S3)) ≃ₜ ↥(Set.range cuspCurve)ᶜ) := by
        refine' ⟨ _ ⟩;
        convert Homeomorph.trans ( Homeomorph.setCongr _ ) ( Homeomorph.trans ( ( subtypeInterHomeo ( { vpt }ᶜ : Set S3 ) ( knotSᶜ : Set S3 ) ).symm ) ( complEquiv ( poleHomeo vpt ) { y : ↥ ( { vpt }ᶜ : Set S3 ) | ( y : S3 ) ∈ knotS } ) ) using 1;
        · rw [ range_cuspCurve_eq ];
        · congr! 1;
          ext; simp [range_cuspCurve_eq];
        · exact Set.inter_comm _ _;
      convert Homeomorph.trans ( Homeomorph.setCongr _ ) ( Homeomorph.trans ( subtypeInterHomeo ( knotSᶜ ) { vpt }ᶜ ) h_compl.some ) using 1;
      ext; simp [Subtype.ext_iff];
      rfl

lemma nonempty_V_homeo :
    Nonempty (↥Vnb ≃ₜ ↥(Metric.ball c0 rad : Set R3)) := by
      refine' ⟨ _ ⟩;
      refine' Homeomorph.trans ( Submission.CuspComplAux.subtypeInterHomeo _ _ ) ( _ );
      refine' Homeomorph.trans _ ( Homeomorph.trans ( Homeomorph.setCongr _ ) ( imageHomeo gg.symm ( Metric.ball c0 rad ) |> Homeomorph.symm ) );
      rotate_left;
      exact gg ⁻¹' ball c0 rad;
      · ext; simp [Set.mem_preimage, Set.mem_image];
        exact ⟨ fun h => ⟨ _, h, by simp +decide [ gg ] ⟩, by rintro ⟨ x, hx, rfl ⟩ ; simpa [ gg ] using hx ⟩;
      · refine' Homeomorph.trans ( Homeomorph.setCongr _ ) ( _ );
        exact Wset;
        · exact Set.inter_eq_right.mpr Wset_subset_knotScompl;
        · refine' Homeomorph.symm _;
          convert Topology.IsEmbedding.subtypeVal.homeomorphImage _ using 1

lemma nonempty_UV_homeo :
    Nonempty (↥(({vptX}ᶜ) ∩ Vnb : Set X) ≃ₜ ↥(Metric.ball c0 rad \ {c0} : Set R3)) := by
      -- First, we show that ${vptX}ᶜ ∩ Vnb$ is in bijection with $P$.
      have hHomeo : Nonempty (↥({vptX}ᶜ ∩ Vnb) ≃ₜ ↥(gg ⁻¹' Metric.ball c0 rad \ {⟨vpt, vpt_mem_compl_neg⟩})) := by
        refine' ⟨ _ ⟩;
        refine' Homeomorph.trans _ ( Homeomorph.trans ( subtypeInterHomeo ( knotSᶜ ) ( Wset \ { vpt } ) ) _ );
        · refine' Homeomorph.setCongr _;
          ext; simp [Vnb, vptX];
          exact ⟨ fun h => ⟨ h.2, fun h' => h.1 <| Subtype.ext h' ⟩, fun h => ⟨ fun h' => h.2 <| congr_arg Subtype.val h', h.1 ⟩ ⟩;
        · refine' Homeomorph.trans ( Homeomorph.setCongr _ ) ( _ );
          exact Wset \ { vpt };
          ·
            -- Since $Wset \ {vpt}$ is a subset of $knotSᶜ$, their intersection is just $Wset \ {vpt}$.
            apply Set.inter_eq_right.mpr;
            -- Since $Wset$ is a subset of $knotSᶜ$, removing $vpt$ from $Wset$ still leaves it within $knotSᶜ$.
            apply Set.diff_subset.trans Wset_subset_knotScompl;
          · refine' Homeomorph.trans ( Homeomorph.setCongr _ ) ( Topology.IsEmbedding.subtypeVal.homeomorphImage _ |> Homeomorph.symm );
            ext; simp [Wset];
      refine' ⟨ hHomeo.some.trans _ ⟩;
      refine' Homeomorph.trans _ ( Homeomorph.setCongr _ );
      exact imageHomeo gg ( gg ⁻¹' Metric.ball c0 rad \ { ⟨ vpt, vpt_mem_compl_neg ⟩ } );
      ext; simp [c0];
      constructor;
      · rintro ⟨ a, ha, ha', ⟨ ha'', ha''' ⟩, rfl ⟩ ; exact ⟨ ha'', by aesop ⟩;
      · intro hx;
        obtain ⟨ a, ha ⟩ := gg.surjective ‹_›;
        use a.val; aesop;

/-! ### Connectivity instances. -/

lemma cuspCurve_contDiff : ContDiff ℝ 1 cuspCurve :=
  cuspKnot.smooth.of_le (by exact_mod_cast le_top)

lemma pathConn_rangeComplR3 : PathConnectedSpace ↥((Set.range cuspCurve)ᶜ : Set R3) := by
  convert Submission.CurveConn.compl_curve_isPathConnected cuspCurve cuspCurve_contDiff using 1;
  rw [ isPathConnected_iff_pathConnectedSpace ]

lemma pathConn_U : PathConnectedSpace ↥(({vptX}ᶜ) : Set X) := by
  obtain ⟨ e ⟩ := nonempty_U_homeo;
  obtain ⟨ x, hx ⟩ := pathConn_rangeComplR3;
  refine' ⟨ ⟨ e.symm x.some, _ ⟩, _ ⟩;
  · exact e.symm x.some |>.2;
  · intro x y;
    obtain ⟨ p ⟩ := hx ( e x ) ( e y );
    refine' ⟨ _, _, _ ⟩;
    exact ⟨ fun t => e.symm ( p t ), by continuity ⟩;
    · aesop;
    · simp +decide [ p.target ]

lemma pathConn_V : PathConnectedSpace ↥Vnb := by
  -- Apply the fact that homeomorphisms preserve path-connectedness.
  have h_path_connected : PathConnectedSpace (↥(Metric.ball c0 rad : Set R3)) := by
    convert isPathConnected_iff_pathConnectedSpace.mp ( Metric.isPathConnected_ball rad_pos ) using 1;
    infer_instance;
  convert h_path_connected;
  obtain ⟨ e ⟩ := nonempty_V_homeo;
  constructor <;> intro h <;> have := e.symm.continuous <;> simp_all +decide [ pathConnectedSpace_iff_univ ];
  convert h_path_connected.image this using 1 ; aesop

lemma pathConn_UV : PathConnectedSpace ↥(({vptX}ᶜ) ∩ Vnb : Set X) := by
  obtain ⟨ e ⟩ := nonempty_UV_homeo;
  have h_path_connected : PathConnectedSpace (↥(Metric.ball c0 rad \ {c0} : Set R3)) := by
    convert isPathConnected_iff_pathConnectedSpace.mp ( Submission.CuspComplAux.isPathConnected_ball_diff_center _ c0 rad_pos ) using 1;
    have := Module.finrank_eq_rank ℝ ( EuclideanSpace ℝ ( Fin 3 ) ) ; norm_num at this ; rw [ ← this ] ; exact_mod_cast by norm_num;
  rw [ pathConnectedSpace_iff_univ ] at *;
  convert h_path_connected.image e.symm.continuous using 1 ; aesop

lemma simplyConn_V : SimplyConnectedSpace ↥Vnb := by
  have h_path_connected : ContractibleSpace (↥(Metric.ball c0 rad : Set R3)) := by
    convert Convex.contractibleSpace ( convex_ball c0 rad ) ⟨ c0, Metric.mem_ball_self rad_pos ⟩ using 1;
  convert ( nonempty_V_homeo.some.toHomotopyEquiv ).simplyConnectedSpace

/-! ### Assemble the cover. -/

lemma exists_base : ∃ x₀ : X, x₀ ∈ ({vptX}ᶜ : Set X) ∧ x₀ ∈ Vnb := by
  have := pathConn_UV;
  convert this.nonempty;
  simp +decide [ Set.Nonempty ]

theorem U_noncomm :
    ∃ (x : ↥(({vptX}ᶜ) : Set X)) (a b : FundamentalGroup (↥(({vptX}ᶜ) : Set X)) x),
      a * b ≠ b * a := by
  obtain ⟨x₀, hx₀U, hx₀V⟩ := exists_base
  haveI := pathConn_U
  haveI := pathConn_V
  haveI := pathConn_UV
  haveI := simplyConn_V
  refine Submission.Pi1Iso.noncomm_of_cover isOpen_compl_singleton Vnb_open ?_ hx₀U hx₀V
    ?_ ?_ ?_ ?_ X_noncomm
  · -- cover
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x = vptX
    · exact Or.inr (by rw [hx]; exact vptX_mem_Vnb)
    · exact Or.inl hx
  · intro y hy
    exact Submission.Sphere.joinedIn_of_subtype_pathConnected _ hx₀U hy
  · intro y hy
    exact Submission.Sphere.joinedIn_of_subtype_pathConnected _ hx₀V hy
  · intro y hy
    exact Submission.Sphere.joinedIn_of_subtype_pathConnected _ ⟨hx₀U, hx₀V⟩ hy
  · intro p hp
    exact Submission.Sphere.loop_null_of_subtype_simplyConnected _ hx₀V p hp

/-! ## Final result. -/

theorem cuspKnot_compl_pi1_noncomm :
    ∃ (x : ↥(Set.range cuspKnot.curve)ᶜ) (a b : FundamentalGroup _ x), a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_U_homeo
  exact Submission.Pi1Transport.noncomm_of_homeo e.symm U_noncomm

end

end Submission.CuspCompl