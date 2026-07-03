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

import LeanPool.NonisotopicKnots.Submission.SphereBridge
import LeanPool.NonisotopicKnots.Submission.CuspKnot
import LeanPool.NonisotopicKnots.ChallengeDeps

/-!
# The smooth cusp knot `cuspKnot : Knot`

We realize the `(2,3)`-torus / cusp link curve `Lcurve` on the weighted sphere `WS`, pushed to
`ℝ³` through the sphere bridge `Submission.SphereBridge.wsPunctToR3 vpt`, as a genuine smooth knot.
The puncture point `N = (0, i) ∈ WS` lies off the cusp, so it is a point of `Link`; the cusp curve
avoids `N`.
-/

namespace Submission.CuspKnotMap

open scoped Topology
open Metric Submission.SphereBridge Submission.CuspGeom Submission.CuspKnot Complex
open LeanEval.KnotTheory

noncomputable section

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The (constant) norm of `phi (Lcurve θ)`. -/
def cc : ℝ := Real.sqrt (aa ^ 2 + bb ^ 2)

lemma cc_pos : 0 < cc := by
  exact Real.sqrt_pos.mpr ( by nlinarith [ aa_neg, bb_pos ] )

/-- The explicit unit direction of the cusp curve, as a point of `ℝ⁴`. -/
def uvec (θ : ℝ) : E4 :=
  cc⁻¹ • !₂[aa * Real.cos (2 * θ), aa * Real.sin (2 * θ),
            bb * Real.cos (3 * θ), bb * Real.sin (3 * θ)]

lemma uvec_mem (θ : ℝ) : uvec θ ∈ sphere (0 : E4) 1 := by
  unfold uvec; norm_num [ EuclideanSpace.norm_eq ] ; ring;
  norm_num [ Fin.sum_univ_succ, abs_mul, abs_of_pos, cc_pos, aa_neg, bb_pos ] ; ring ; norm_num [ Real.sin_sq, Real.cos_sq ] ; ring;
  field_simp;
  rw [ div_eq_iff ] <;> norm_num [ cc ];
  · rw [ Real.sq_sqrt ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ];
  · exact ne_of_gt <| Real.sqrt_pos.mpr <| by nlinarith [ aa_neg, bb_pos ]

/-- The puncture point `N = (0, i)` on the weighted sphere. -/
def Npt : ℂ × ℂ := (0, Complex.I)

lemma Npt_mem_WS : Npt ∈ WS := by
  unfold WS Npt; norm_num;
  unfold WN; norm_num [ Complex.normSq, Complex.norm_def ] ;

lemma Npt_mem_Link : Npt ∈ Link := by
  exact ⟨ Npt_mem_WS, by norm_num [ Npt, Complex.ext_iff, pow_three ] ⟩

/-- The puncture as a point of `↥WS`. -/
def Nsub : ↥WS := ⟨Npt, Npt_mem_WS⟩

/-- The image of the puncture on the standard sphere `S³`, used as the stereographic pole. -/
def vpt : S3 := wsToS3 Nsub

lemma symm_vpt : wsToS3.symm vpt = Nsub :=
  wsToS3.symm_apply_apply Nsub

/-- The cusp curve as a point of `↥WS`. -/
def Lsub (θ : ℝ) : ↥WS := ⟨Lcurve θ, Lcurve_mem_WS θ⟩

lemma Lsub_ne_N (θ : ℝ) : Lsub θ ≠ Nsub := by
  unfold Lsub Nsub;
  simp +decide [ Lcurve, Npt ];
  exact fun h => absurd h ( by linarith [ aa_neg ] )

/-- The cusp curve as a point of `↥WS ∖ {N}`. -/
def Lpt (θ : ℝ) : ↥(({wsToS3.symm vpt}ᶜ) : Set ↥WS) :=
  ⟨Lsub θ, by rw [symm_vpt]; exact Lsub_ne_N θ⟩

/-- The cusp knot curve in `ℝ³`. -/
def cuspCurve (θ : ℝ) : R3 := wsPunctToR3 vpt (Lpt θ)

lemma wsToS3_Lsub (θ : ℝ) : (wsToS3 (Lsub θ) : E4) = uvec θ := by
  convert congr_arg ( fun x : E4 => ( cc⁻¹ : ℝ ) • x ) _ using 1;
  rotate_left;
  exact phi ( Lcurve θ );
  · unfold phi Lcurve;
    norm_num [ Complex.exp_re, Complex.exp_im ];
  · convert congr_arg ( fun x : E4 => ( ‖x‖⁻¹ : ℝ ) • x ) _ using 1;
    congr! 1;
    · unfold cc phi Lcurve; norm_num [ EuclideanSpace.norm_eq ] ; ring;
      norm_num [ Fin.sum_univ_succ, Complex.exp_re, Complex.exp_im ] ; ring;
      rw [ Real.sin_sq, Real.sin_sq ] ; ring;
    · rfl

lemma cuspCurve_stereo (θ : ℝ) :
    cuspCurve θ = stereographic' 3 vpt ⟨uvec θ, uvec_mem θ⟩ := by
      -- Unfold `wsToS3_Lsub` and `stereographic'_apply` to rewrite the right-hand side.
      have h2 : stereographic' (3 : ℕ) vpt ⟨uvec θ, uvec_mem θ⟩ = stereographic' (3 : ℕ) vpt (wsToS3 (Lsub θ)) := by
        convert rfl;
        convert wsToS3_Lsub θ using 1
      generalize_proofs at *;
      convert Homeomorph.apply_symm_apply ( Homeomorph.Set.univ R3 ) _ using 1;
      convert h2 using 1;
      simp +decide [ Homeomorph.trans, Homeomorph.setCongr, Homeomorph.Set.univ, punctTransport ];
      convert OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe _ _;
      rotate_right;
      exact ⟨ wsToS3 ( Lsub θ ), by
        simp +decide [ stereographic'_source ];
        exact fun h => Lsub_ne_N θ <| wsToS3.injective <| h.trans <| by simp +decide [ vpt ] ; ⟩
      all_goals generalize_proofs at *;
      · simp +decide [ stereographic', stereographic'_target ];
      · congr! 1;
        all_goals congr! 1;
        all_goals congr! 1;
        all_goals norm_num [ stereographic'_source ];
        · congr! 1;
          ext; simp [stereographic'_source];
        · congr! 1;
      · rfl

lemma uvec_ne_vpt (θ : ℝ) : (⟨uvec θ, uvec_mem θ⟩ : S3) ≠ vpt := by
  unfold uvec vpt;
  simp +decide [ Nsub, wsToS3, radialFun, phi ];
  erw [ Subtype.mk_eq_mk ] ; norm_num [ Npt ];
  unfold radialFun;
  unfold phi; norm_num [ EuclideanSpace.norm_eq ] ; ring;
  intro h; have := congr_arg ( fun x => x 0 ) h; norm_num at this; have := congr_arg ( fun x => x 1 ) h; norm_num at this; have := congr_arg ( fun x => x 2 ) h; norm_num at this; have := congr_arg ( fun x => x 3 ) h; norm_num at this;
  simp_all +decide [ Fin.sum_univ_succ, cc_pos.ne', aa_neg.ne, bb_pos.ne' ];
  nlinarith [ Real.sin_sq_add_cos_sq ( θ * 2 ) ]

/-- The auxiliary `ℝ⁴`-valued inverse-stereographic map, smooth on all of `ℝ³`. -/
def Ginv (x : R3) : E4 := ((stereographic' 3 vpt).symm x : E4)

lemma Ginv_contDiff : ContDiff ℝ (⊤ : ℕ∞) Ginv := by
  -- Apply the fact that the composition of smooth functions is smooth.
  have h_comp : ContDiff ℝ ⊤ (fun x : R3 => stereoInvFunAux (vpt : E4) ((Submodule.subtypeL (ℝ ∙ (vpt : E4))ᗮ) (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere vpt) |>.repr.symm x))) := by
    convert contDiff_stereoInvFunAux.comp _ using 1;
    fun_prop;
  convert h_comp.of_le le_top using 1

lemma Ginv_cuspCurve (θ : ℝ) : Ginv (cuspCurve θ) = uvec θ := by
  have h_left_inv : (stereographic' 3 vpt).symm (stereographic' 3 vpt ⟨uvec θ, uvec_mem θ⟩) = ⟨uvec θ, uvec_mem θ⟩ := by
    convert ( stereographic' 3 vpt ).left_inv' _ using 1;
    rw [stereographic'_source]; exact uvec_ne_vpt θ;
  convert congr_arg Subtype.val h_left_inv using 1;
  exact cuspCurve_stereo θ ▸ rfl

lemma uvec_contDiff : ContDiff ℝ (⊤ : ℕ∞) uvec := by
  convert ContDiff.smul _ _;
  rotate_left;
  exact ℝ;
  all_goals try infer_instance;
  exact fun _ => cc⁻¹;
  exact fun x => !₂[aa * Real.cos (2 * x), aa * Real.sin (2 * x), bb * Real.cos (3 * x), bb * Real.sin (3 * x)];
  · exact contDiff_const;
  · rw [ contDiff_iff_contDiffAt ];
    intro x;
    refine' ContDiffAt.congr_of_eventuallyEq _ _;
    exact fun x => WithLp.toLp 2 ( fun i => if i = 0 then aa * Real.cos ( 2 * x ) else if i = 1 then aa * Real.sin ( 2 * x ) else if i = 2 then bb * Real.cos ( 3 * x ) else bb * Real.sin ( 3 * x ) );
    · refine' ContDiffAt.congr_of_eventuallyEq _ _;
      exact fun x => aa • Real.cos ( 2 * x ) • EuclideanSpace.single 0 1 + aa • Real.sin ( 2 * x ) • EuclideanSpace.single 1 1 + bb • Real.cos ( 3 * x ) • EuclideanSpace.single 2 1 + bb • Real.sin ( 3 * x ) • EuclideanSpace.single 3 1;
      · fun_prop;
      · filter_upwards [ ] with x using by ext i; fin_cases i <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    · filter_upwards [ ] with x using by ext i; fin_cases i <;> rfl;
  · rfl

lemma uvec_deriv_ne (θ : ℝ) : deriv uvec θ ≠ 0 := by
  by_contra h_contra;
  -- From `deriv uvec θ = 0` we get `deriv (fun s => uvec s i) θ = 0` for each `i`.
  have h_deriv_zero : ∀ i : Fin 4, deriv (fun s => uvec s i) θ = 0 := by
    intro i
    have h_eval : (deriv uvec θ) i = deriv (fun s => (uvec s).ofLp i) θ := by
      have h_eval : (fderiv ℝ uvec θ) (1 : ℝ) = deriv uvec θ := by
        rfl;
      convert congr_arg ( fun x => x.ofLp i ) h_eval using 1;
      convert HasDerivAt.deriv ( _ ) using 1;
      convert HasFDerivAt.hasDerivAt ( HasFDerivAt.comp θ ( ContinuousLinearMap.hasFDerivAt ( EuclideanSpace.proj i ) ) ( uvec_contDiff.contDiffAt.differentiableAt ( by norm_num ) |> DifferentiableAt.hasFDerivAt ) ) using 1;
    aesop;
  have := h_deriv_zero 0; have := h_deriv_zero 1; simp_all +decide [ uvec, Fin.sum_univ_succ, EuclideanSpace.norm_eq ] ;
  norm_num [ mul_comm ] at * ; simp_all +decide [ cc_pos.ne', aa_neg.ne, bb_pos.ne' ] ;
  nlinarith [ Real.sin_sq_add_cos_sq ( θ * 2 ) ]

lemma cuspCurve_smooth : ContDiff ℝ (⊤ : ℕ∞) cuspCurve := by
  -- By definition of $cuspCurve$, we have $cuspCurve = (U \circ stereoToFun (vpt : E4)) \circ uvec$.
  have h_def : cuspCurve = (fun x => (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere vpt)).repr (stereoToFun (vpt : E4) x)) ∘ uvec := by
    ext θ; exact (by
    convert congr_arg ( fun x => x.ofLp ‹_› ) ( cuspCurve_stereo θ ) using 1);
  refine' h_def ▸ _;
  refine' contDiff_iff_contDiffAt.mpr _;
  intro x;
  refine' ContDiffAt.comp x _ _;
  · refine' ContDiffAt.comp _ _ _;
    · exact LinearIsometryEquiv.contDiff _ |> ContDiff.contDiffAt;
    · refine' contDiffOn_stereoToFun.contDiffAt _;
      refine' IsOpen.mem_nhds _ _;
      · exact isOpen_ne.preimage ( ContinuousLinearMap.continuous _ );
      · intro h; have := inner_eq_one_iff_of_norm_eq_one ( show ‖( vpt : E4 )‖ = 1 from by simp ) ( show ‖uvec x‖ = 1 from by simpa using uvec_mem x ) |>.1 h; simp_all +decide [ Subtype.ext_iff ] ;
        exact uvec_ne_vpt x ( Subtype.ext this.symm );
  · exact uvec_contDiff.contDiffAt

lemma cuspCurve_periodic : ∀ t, cuspCurve (t + 2 * Real.pi) = cuspCurve t := by
  intro t
  unfold cuspCurve
  simp [Lpt];
  unfold Lsub;
  unfold Lcurve; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ;
  norm_num [ Real.cos_two_mul, Real.sin_two_mul, Real.cos_three_mul, Real.sin_three_mul ]

lemma Lcurve_injOn : Set.InjOn Lcurve (Set.Ico 0 (2 * Real.pi)) := by
  intro θ₁ hθ₁ θ₂ hθ₂ h_eq
  have h_exp : Complex.exp (2 * θ₁ * Complex.I) = Complex.exp (2 * θ₂ * Complex.I) ∧ Complex.exp (3 * θ₁ * Complex.I) = Complex.exp (3 * θ₂ * Complex.I) := by
    unfold Lcurve at h_eq; simp_all +decide [ Complex.ext_iff ] ;
    exact ⟨ h_eq.1.resolve_right ( by linarith [ aa_neg ] ), h_eq.2.resolve_right ( by linarith [ bb_pos ] ) ⟩;
  have h_exp_eq : Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) := by
    simp_all +decide [ Complex.exp_eq_exp_iff_exists_int ];
    obtain ⟨ ⟨ n, hn ⟩, ⟨ m, hm ⟩ ⟩ := h_exp;
    exact ⟨ m - n, by push_cast; linear_combination hm - hn ⟩;
  rw [ Complex.exp_eq_exp_iff_exists_int ] at h_exp_eq ; obtain ⟨ k, hk ⟩ := h_exp_eq ; rcases k with ⟨ _ | k ⟩ <;> norm_num [ Complex.ext_iff ] at hk <;> nlinarith [ Real.pi_pos, hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2 ] ;

lemma cuspCurve_injOn : Set.InjOn cuspCurve (Set.Ico 0 (2 * Real.pi)) := by
  intro θ₁ hθ₁ θ₂ hθ₂ h_eq
  have h_Lpt : Lpt θ₁ = Lpt θ₂ := by
    exact ( wsPunctToR3 vpt ).injective h_eq;
  injection h_Lpt with h_Lpt;
  exact Lcurve_injOn hθ₁ hθ₂ ( by injection h_Lpt )

lemma cuspCurve_immersion : ∀ t, deriv cuspCurve t ≠ 0 := by
  intro θ h_deriv_zero
  have h_uvec_zero : deriv uvec θ = 0 := by
    -- By definition of $uvec$, we know that $uvec = Ginv ∘ cuspCurve$.
    have h_uvec_comp : uvec = Ginv ∘ cuspCurve := by
      exact funext fun x => Ginv_cuspCurve x ▸ rfl;
    rw [ h_uvec_comp, deriv ];
    rw [ fderiv_comp ] <;> norm_num [ h_deriv_zero, Ginv_contDiff.contDiffAt.differentiableAt, cuspCurve_smooth.contDiffAt.differentiableAt ]
  exact uvec_deriv_ne θ h_uvec_zero

/-- The smooth cusp knot. -/
def cuspKnot : Knot where
  curve := cuspCurve
  smooth := cuspCurve_smooth
  periodic := cuspCurve_periodic
  injOn := cuspCurve_injOn
  immersion := cuspCurve_immersion

end

end Submission.CuspKnotMap