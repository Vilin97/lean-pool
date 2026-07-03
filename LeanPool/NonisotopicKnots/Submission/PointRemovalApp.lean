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

import LeanPool.NonisotopicKnots.Submission.Inversion
import LeanPool.NonisotopicKnots.Submission.VanKampenInj
import LeanPool.NonisotopicKnots.Submission.PointRemovalGP
import LeanPool.NonisotopicKnots.Submission.PuncturedSpace
import LeanPool.NonisotopicKnots.Submission.Sphere
import LeanPool.NonisotopicKnots.Submission.LineComplement

/-!
# Geometric application: the line-minus-point complement has abelian π₁

This file discharges `Submission.Inversion.lineWithPoint_compl_pi1_comm` **modulo the single
keystone** `Submission.VanKampenInj.loop_null_in_U_of_null_in_X` (the 2-D van Kampen
amalgamation).  Concretely we apply the abstract codimension-3 point removal
`Submission.VanKampenInj.pi1_comm_of_point_removal` with:

* ambient space `X3 = ↥(Lline)ᶜ` (the line complement; abelian by
  `Submission.Inversion.LlineCompl_abelian`),
* removed point `qpt = ⟨p₀, _⟩`,
* neighbourhood `V = ` open ball of radius `1/2` about `p₀` (contained in `(Lline)ᶜ`).

The simple-connectivity and path-connectivity hypotheses are supplied by the named instances
below (`Vb` ≅ convex ball, `Vb ∖ qpt` ≅ punctured ℝ³, `{qpt}ᶜ` path-connected) via the
converters in `Submission.Sphere`.  Basepoint-independence is handled with
`fundamentalGroupMulEquivOfPathConnected`.
-/

open scoped Topology
open LeanEval.KnotTheory Submission.Inversion

namespace Submission.PointRemovalApp

/-- Ambient space for the point removal: the line complement. -/
abbrev X3 : Type := ↥((Lline)ᶜ : Set R3)

/-- The point to be removed, `p₀ ∈ (Lline)ᶜ`. -/
noncomputable def qpt : X3 := ⟨p0, p0_not_mem_Lline⟩

/-- The open ball of radius `1/2` about `p₀` in `ℝ³`. -/
def Bp0 : Set R3 := {u | dist u p0 < 1 / 2}

/-
The ball lies in the line complement (its radius equals `dist p₀ Lline = 1/2`).
-/
lemma Bp0_subset : Bp0 ⊆ (Lline)ᶜ := by
  intro u hu; simp_all +decide [ Lline ] ;
  intro h₀ h₂; have := hu.out; simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ;
  rw [ Real.sqrt_lt' ] at this <;> norm_num [ Fin.sum_univ_three, p0 ] at * ; nlinarith! [ sq_nonneg ( u.ofLp 1 ) ] ;

lemma p0_mem_Bp0 : p0 ∈ Bp0 := by
  convert Set.mem_setOf.mpr ( show dist p0 p0 < 1 / 2 by norm_num )

/-- The ball as a neighbourhood of `qpt` inside `X3`. -/
def Vb : Set X3 := {y | (y : R3) ∈ Bp0}

lemma Vb_open : IsOpen Vb := by
  refine' isOpen_induced ( Metric.isOpen_ball )

lemma qpt_mem_Vb : qpt ∈ Vb := by
  exact show ( p0 : R3 ) ∈ Bp0 from show dist p0 p0 < 1 / 2 by norm_num [ dist_self ]

lemma x0_aux_mem : (p0 + EuclideanSpace.single 0 (1 / 4) : R3) ∈ (Lline)ᶜ := by
  intro h; have := h.1; norm_num [ p0 ] at this;

/-- A reference base point of `V ∖ {qpt}`: `p₀ + (1/4)·e₀`. -/
noncomputable def x0pt : X3 :=
  ⟨p0 + EuclideanSpace.single 0 (1 / 4), x0_aux_mem⟩

lemma x0pt_ne_qpt : x0pt ≠ qpt := by
  exact ne_of_apply_ne ( fun x => x.val 0 ) ( by norm_num [ x0pt, qpt, p0 ] )

lemma x0pt_mem_Vb : x0pt ∈ Vb := by
  unfold Vb x0pt; norm_num;
  unfold Bp0; norm_num [ p0 ]

/-
`Vb` is homeomorphic to the convex open ball in `ℝ³` (the ball lies in `(Lline)ᶜ`), hence
contractible; `SimplyConnectedSpace`/`PathConnectedSpace` follow automatically.
-/
instance Vb_contractible : ContractibleSpace ↥Vb := by
  -- Build a homeomorphism `h : ↥Vb ≃ₜ ↥(Bp0 : Set R3)`, value-preserving.
  set h : ↥Vb ≃ₜ ↥(Bp0 : Set R3) :=
    { toFun y := ⟨y.val, y.prop⟩
      invFun w := ⟨⟨w.val, Bp0_subset w.prop⟩, w.prop⟩
      left_inv y := by simp [Subtype.ext_iff]
      right_inv w := by simp [Subtype.ext_iff]
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop };
  convert h.contractibleSpace_iff.mpr _;
  convert Convex.contractibleSpace ( convex_ball ( p0 : R3 ) ( 1 / 2 ) ) ?_;
  exact ⟨ p0, Metric.mem_ball_self ( by norm_num ) ⟩

/-
The punctured ball `Vb ∖ {qpt}` is homeomorphic to punctured `ℝ³` (`Punctured`), hence
simply connected (and, automatically, path-connected).
-/
instance Vbminus_simplyConnected :
    SimplyConnectedSpace ↥(({qpt}ᶜ ∩ Vb) : Set X3) := by
      -- Identify the set value-preservingly with the punctured ball
      have h_eq : {qpt}ᶜ ∩ Vb = { y : X3 | (y : R3) ≠ p0 ∧ (y : R3) ∈ Bp0 } := by
        ext; simp [qpt, Vb];
        exact fun _ => by rw [ Subtype.ext_iff ] ;
      -- Build the radial homeomorphism `φ : ↥S ≃ₜ Punctured`
      have h_homeo : Nonempty ({w : R3 | w ≠ p0 ∧ dist w p0 < 1 / 2} ≃ₜ Submission.PuncturedSpace.Punctured) := by
        refine' ⟨ _ ⟩;
        fapply Homeomorph.mk;
        use fun w => ⟨ ( 1 / 2 - ‖w.val - p0‖ ) ⁻¹ • ( w.val - p0 ), by
          simp +zetaDelta at *;
          exact ⟨ sub_ne_zero_of_ne <| ne_of_gt <| by simpa [ dist_eq_norm ] using w.2.2, sub_ne_zero_of_ne <| w.2.1 ⟩ ⟩
        generalize_proofs at *;
        use fun v => ⟨ p0 + ( 2 * ( 1 + ‖v.val‖ ) ) ⁻¹ • v.val, by
          simp +decide [ dist_eq_norm, v.2 ];
          exact ⟨ by positivity, by rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] ; nlinarith [ norm_nonneg ( v : EuclideanSpace ℝ ( Fin 3 ) ), mul_inv_cancel₀ ( by positivity : ( 1 + ‖ ( v : EuclideanSpace ℝ ( Fin 3 ) )‖ ) ≠ 0 ) ] ⟩ ⟩;
        all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
        · intro a ha h'a; simp_all +decide [ norm_smul, dist_eq_norm ];
          ext i
          have hnn : (0:ℝ) ≤ ‖a - p0‖ := norm_nonneg _
          have hpos : (0:ℝ) < 2⁻¹ - ‖a - p0‖ := by linarith [h'a]
          have hne : (2⁻¹ - ‖a - p0‖) ≠ 0 := ne_of_gt hpos
          rw [abs_of_pos hpos]
          have keyv : (1 + (2⁻¹ - ‖a - p0‖)⁻¹ * ‖a - p0‖) = 2⁻¹ * (2⁻¹ - ‖a - p0‖)⁻¹ := by
            linear_combination -inv_mul_cancel₀ hne
          have hc : ((1 + (2⁻¹ - ‖a - p0‖)⁻¹ * ‖a - p0‖)⁻¹ * 2⁻¹) * (2⁻¹ - ‖a - p0‖)⁻¹ = 1 := by
            rw [keyv]
            field_simp
            exact div_self (by linarith : (1 - 2 * ‖a - p0‖ : ℝ) ≠ 0)
          rw [smul_smul, hc, one_smul]
          simp
        · intro a ha; rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] ; ring;
          rw [ ← smul_assoc ] ; norm_num [ ha, show ( 1 + ‖a‖ ) ≠ 0 by positivity ];
          field_simp;
          norm_num;
        · refine' Continuous.subtype_mk _ _;
          refine' Continuous.smul _ _;
          · refine' Continuous.inv₀ _ _;
            · fun_prop;
            · exact fun x => sub_ne_zero_of_ne <| ne_of_gt <| by simpa [ dist_eq_norm ] using x.2.2;
          · fun_prop;
        · refine' Continuous.subtype_mk _ _;
          exact Continuous.add continuous_const <| Continuous.smul ( Continuous.mul ( Continuous.inv₀ ( continuous_const.add <| continuous_norm.comp <| continuous_subtype_val ) fun x => by positivity ) continuous_const ) <| continuous_subtype_val;
      have h_homeo_subtype : Nonempty ({y : X3 | (y : R3) ≠ p0 ∧ (y : R3) ∈ Bp0} ≃ₜ {w : R3 | w ≠ p0 ∧ dist w p0 < 1 / 2}) := by
        refine' ⟨ _, _, _ ⟩;
        refine' ⟨ fun x => ⟨ x.val, x.property.1, x.property.2 ⟩, fun x => ⟨ ⟨ x.val, _ ⟩, x.property.1, x.property.2 ⟩, _, _ ⟩;
        all_goals norm_num [ Function.LeftInverse, Function.RightInverse ];
        exact Bp0_subset x.2.2; all_goals fun_prop;
      convert h_homeo_subtype.some.trans h_homeo.some |> fun h => h.toHomotopyEquiv.simplyConnectedSpace

/-
A straight segment contained in `(Lline ∪ {p0})ᶜ` gives a `JoinedIn`.
-/
lemma seg_joinedIn {x y : R3}
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) • x + t • y ∈ ((Lline ∪ {p0})ᶜ : Set R3)) :
    JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) x y := by
  refine' ⟨ _, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  exact ⟨ fun t => ( 1 - t.val ) • x + t.val • y, by fun_prop ⟩;
  all_goals norm_num;
  exact fun t ht₁ ht₂ => by simpa using h t ht₁ ht₂;

/-
A point with nonzero third coordinate is in `(Lline ∪ {p0})ᶜ`.
-/
lemma mem_W_of_two_ne {u : R3} (h : u 2 ≠ 0) : u ∈ ((Lline ∪ {p0})ᶜ : Set R3) := by
  simp +decide [ Lline, p0, h ];
  exact fun h' => h <| h'.symm ▸ by simp +decide ;

/-
A point with first coordinate `≠ 1/2` and distinct from `p0` is in `(Lline ∪ {p0})ᶜ`.
-/
lemma mem_W_of_zero {u : R3} (h0 : u 0 ≠ 1 / 2) (hp : u ≠ p0) :
    u ∈ ((Lline ∪ {p0})ᶜ : Set R3) := by
      contrapose! h0; simp_all +decide [ Lline ] ;

/-
Coordinate of a segment point.
-/
@[simp] lemma seg_coord (x y : R3) (t : ℝ) (i : Fin 3) :
    ((1 - t) • x + t • y) i = (1 - t) * (x i) + t * (y i) := by
      fin_cases i <;> rfl

/-- A segment whose third coordinate never vanishes lies in `W`. -/
lemma seg_joinedIn_two {x y : R3}
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * (x 2) + t * (y 2) ≠ 0) :
    JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) x y :=
  seg_joinedIn (fun t ht0 ht1 => mem_W_of_two_ne (by rw [seg_coord]; exact h t ht0 ht1))

/-
A segment whose first coordinate is constantly `2` lies in `W`.
-/
lemma seg_joinedIn_zero {x y : R3} (hx : x 0 = 2) (hy : y 0 = 2) :
    JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) x y := by
  refine' seg_joinedIn _;
  intro t ht0 ht1; simp_all +decide [ Lline, p0 ] ;
  exact ⟨ ne_of_apply_ne ( fun z => z.ofLp 0 ) ( by norm_num [ hx, hy ] ; linarith ), fun h => by norm_num at h; linarith ⟩

/-
The upward vertical segment from an in-plane point of `W` lies in `W`.
-/
lemma seg_joinedIn_up {a : R3} (ha : a ∈ ((Lline ∪ {p0})ᶜ : Set R3)) (ha2 : a 2 = 0) :
    JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) a (a + EuclideanSpace.single 2 1) := by
  convert seg_joinedIn _;
  intro t ht0 ht1; contrapose! ha; simp_all +decide [ Lline, p0 ] ;
  by_cases h : t = 0 <;> simp_all +decide [ ← add_assoc ];
  replace ha := congr_arg ( fun x => x.ofLp 2 ) ha ; aesop

instance qcompl_pathConnected : PathConnectedSpace ↥(({qpt}ᶜ) : Set X3) := by
  obtain ⟨c, hc⟩ : ∃ c : R3, c ∈ ((Lline ∪ {p0})ᶜ : Set R3) ∧ ∀ a : R3, a ∈ ((Lline ∪ {p0})ᶜ : Set R3) → JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) c a := by
    use EuclideanSpace.single 2 1;
    refine' ⟨ _, _ ⟩;
    · exact mem_W_of_two_ne ( by norm_num );
    · intro a ha
      by_cases ha2 : a 2 > 0;
      · convert seg_joinedIn_two _ using 1;
        intro t ht ht'; norm_num [ EuclideanSpace.single_apply ] ; cases lt_or_eq_of_le ht <;> cases lt_or_eq_of_le ht' <;> nlinarith;
      · by_cases ha2 : a 2 < 0;
        · -- Let $b₁ = (2, 0, 1)$ and $b₂ = (2, 0, -1)$.
          set b₁ : R3 := EuclideanSpace.single 0 2 + EuclideanSpace.single 2 1
          set b₂ : R3 := EuclideanSpace.single 0 2 + EuclideanSpace.single 2 (-1);
          -- By transitivity of JoinedIn, we can combine the paths from c to b₁, b₁ to b₂, and b₂ to a.
          have h_trans : JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) (EuclideanSpace.single 2 1) b₁ ∧ JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) b₁ b₂ ∧ JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) b₂ a := by
            refine' ⟨ _, _, _ ⟩;
            · convert seg_joinedIn_two _ using 1;
              simp +zetaDelta at *;
            · apply seg_joinedIn_zero; all_goals simp +zetaDelta at *;
            · apply seg_joinedIn_two;
              simp +zetaDelta at *;
              intro t ht₁ ht₂; cases lt_or_eq_of_le ht₁ <;> cases lt_or_eq_of_le ht₂ <;> nlinarith;
          exact h_trans.1.trans ( h_trans.2.1.trans h_trans.2.2 );
        · have h_join : JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) a (a + EuclideanSpace.single 2 1) := by
            apply seg_joinedIn_up ha;
            linarith;
          have h_join : JoinedIn ((Lline ∪ {p0})ᶜ : Set R3) (a + EuclideanSpace.single 2 1) (EuclideanSpace.single 2 1) := by
            apply seg_joinedIn_two;
            intro t ht ht'; norm_num [ EuclideanSpace.single_apply ] ; cases lt_or_eq_of_le ht <;> cases lt_or_eq_of_le ht' <;> nlinarith;
          exact h_join.symm.trans ( ‹JoinedIn ( Lline ∪ { p0 } ) ᶜ a ( a + EuclideanSpace.single 2 1 ) ›.symm );
  have h_path_connected : PathConnectedSpace ↥((Lline ∪ {p0})ᶜ : Set R3) := by
    exact ( isPathConnected_iff_pathConnectedSpace.mp <| ⟨ c, hc.1, hc.2 ⟩ );
  rw [ pathConnectedSpace_iff_univ ] at *;
  convert h_path_connected.image _ using 1;
  rotate_left;
  exact fun x => ⟨ ⟨ x.val, by
    exact fun h => x.2 <| Or.inl h ⟩, by
    exact fun h => by have := x.2; simp_all +decide [ qpt ] ; ⟩
  all_goals generalize_proofs at *;
  · fun_prop;
  · ext ⟨x, hx⟩; simp [Set.mem_image];
    exact ⟨ x, ⟨ by
      exact fun h => hx <| Subtype.ext h, by
      grind ⟩, rfl ⟩

/-
**Superseded by the general-position route.**  The original codimension-3 point-removal step here
went through the abstract 2-D van Kampen amalgamation keystone
(`Submission.VanKampenInj.pi1_comm_of_point_removal`, which depended on the unproved
`loop_null_in_U_of_null_in_X`).  It is now replaced by the fully-proved
`Submission.PointRemovalGP.point_removal_comm` (general position: a contracting disk of a loop
avoiding `q` is pushed off the codimension-3 point `q`).  The two lemmas below
(`qcompl_abelian_at_x0`, `qcompl_abelian`) are kept for the record but commented out, since they
relied on the keystone chain and are no longer used; `lineWithPoint_compl_pi1_comm` below is
reproved directly from `point_removal_comm`.

/-- π₁ of `{qpt}ᶜ` (the punctured line complement) is abelian, at the reference point. -/
theorem qcompl_abelian_at_x0
    (a b : FundamentalGroup (↥(({qpt}ᶜ) : Set X3)) ⟨x0pt, x0pt_ne_qpt⟩) :
    a * b = b * a := by
  refine Submission.VanKampenInj.pi1_comm_of_point_removal
    (X := X3) (fun z u v => LlineCompl_abelian z u v)
    (q := qpt) (V := Vb) Vb_open qpt_mem_Vb x0pt_ne_qpt x0pt_mem_Vb
    (fun y hy => Submission.Sphere.joinedIn_of_subtype_pathConnected
      (({qpt}ᶜ) : Set X3) x0pt_ne_qpt hy)
    (fun y hy => Submission.Sphere.joinedIn_of_subtype_pathConnected Vb x0pt_mem_Vb hy)
    (fun y hy => Submission.Sphere.joinedIn_of_subtype_pathConnected
      (({qpt}ᶜ ∩ Vb) : Set X3) ⟨x0pt_ne_qpt, x0pt_mem_Vb⟩ hy)
    (fun p hp => Submission.Sphere.loop_null_in_set_of_subtype_simplyConnected Vb x0pt_mem_Vb p hp)
    (fun p hp => Submission.Sphere.loop_null_in_set_of_subtype_simplyConnected
      (({qpt}ᶜ ∩ Vb) : Set X3) ⟨x0pt_ne_qpt, x0pt_mem_Vb⟩ p hp)
    a b

/-- π₁ of `{qpt}ᶜ` is abelian at every base point (path-connected transport). -/
theorem qcompl_abelian (y : ↥(({qpt}ᶜ) : Set X3))
    (a b : FundamentalGroup _ y) : a * b = b * a := by
  have e := (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
    (X := ↥(({qpt}ᶜ) : Set X3)) (x₀ := y) (x₁ := ⟨x0pt, x0pt_ne_qpt⟩))
  have h := qcompl_abelian_at_x0 (e a) (e b)
  have : e (a * b) = e (b * a) := by rw [map_mul, map_mul]; exact h
  exact e.injective this
-/

/-
Identification of `(Lline ∪ {p₀})ᶜ ⊆ ℝ³` with `{qpt}ᶜ ⊆ X3`.
-/
def lpt_homeo : ↥((Lline ∪ {p0})ᶜ : Set R3) ≃ₜ ↥(({qpt}ᶜ) : Set X3) where
  toFun x :=
    ⟨⟨x.val, fun h => x.2 (Or.inl h)⟩, fun h => x.2 (Or.inr (Subtype.ext_iff.mp h))⟩
  invFun x :=
    ⟨x.val.val, fun h => h.elim (fun hL => x.val.2 hL) (fun hp => x.2 (Subtype.ext hp))⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- **Unknot point-removal (modulo the keystone).**  The complement of the line `Lline`
together with the off-line point `p₀` has abelian `π₁`. -/
theorem lineWithPoint_compl_pi1_comm (x : ↥((Lline ∪ {p0})ᶜ : Set R3))
    (a b : FundamentalGroup _ x) : a * b = b * a := by
  have hset : ((Lline ∪ {p0})ᶜ : Set R3) = ((Lline)ᶜ \ {p0}) := by
    ext y; simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, Set.mem_diff]
    tauto
  let e : ↥((Lline ∪ {p0})ᶜ : Set R3) ≃ₜ ↥(((Lline)ᶜ \ {p0}) : Set R3) :=
    Homeomorph.setCongr hset
  obtain ⟨ψ⟩ := Submission.Invariant.fundamentalGroup_mulEquiv_of_homeo e x
  have hopen : IsOpen ((Lline)ᶜ : Set R3) := by
    rw [isOpen_compl_iff]
    have h0 : Continuous (fun p : R3 => p 0) := by fun_prop
    have h2 : Continuous (fun p : R3 => p 2) := by fun_prop
    exact (isClosed_eq h0 continuous_const).inter (isClosed_eq h2 continuous_const)
  have hcomm := Submission.PointRemovalGP.point_removal_comm hopen
    (fun z u v => Submission.Inversion.LlineCompl_abelian z u v) (e x) (ψ a) (ψ b)
  have : ψ (a * b) = ψ (b * a) := by rw [map_mul, map_mul]; exact hcomm
  exact ψ.injective this

/-- The complement of the round circle `C` has abelian `π₁`, via the inversion homeomorphism. -/
theorem C_compl_pi1_comm (x : ↥(Cᶜ : Set R3))
    (a b : FundamentalGroup _ x) : a * b = b * a := by
  obtain ⟨ψ⟩ := Submission.Invariant.fundamentalGroup_mulEquiv_of_homeo invHomeo x
  have hcomm := lineWithPoint_compl_pi1_comm (invHomeo x) (ψ a) (ψ b)
  have : ψ (a * b) = ψ (b * a) := by rw [map_mul, map_mul]; exact hcomm
  exact ψ.injective this

end Submission.PointRemovalApp