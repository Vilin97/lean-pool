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
# General position: pushing a 2-disk off a point in `ℝ³`

This file develops the *general-position* route to the codimension-3 point-removal step of the
unknot side, as an alternative to the abstract 2-D van Kampen amalgamation keystone
(`Submission.VanKampenInj.loop_null_in_U_of_null_in_X`).

The geometric content: a continuous square `F : I × I → ℝ³` landing in an open set `Ω`, whose
boundary avoids a point `q ∈ Ω`, can be modified rel boundary to a square `G : I × I → ℝ³` that
still lands in `Ω` but avoids `q` entirely.  (A 2-disk generically misses a codimension-3 point.)

Key Mathlib inputs:
* `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` — the image of a
  null set under a differentiable map is null;
* a hyperplane in `ℝ³` is null;
* `Continuous.exists_contDiff_approx_and_eqOn` — smooth approximation of continuous maps.
-/

open scoped Topology unitInterval
open MeasureTheory

noncomputable section

namespace Submission.GenPos

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-
**Measure-zero of a smooth disk image.**  The image of the hyperplane `{p : p 2 = 0}` (hence
of any 2-dimensional square) under a `C¹` map `g : ℝ³ → ℝ³` has Lebesgue measure zero.
-/
theorem smooth_image_plane_measure_zero (g : R3 → R3) (hg : ContDiff ℝ 1 g) :
    volume (g '' {p : R3 | p 2 = 0}) = 0 := by
  -- The set ${p : R3 | p.ofLp 2 = 0}$ is a 2-dimensional subspace of $R3$, hence it has measure zero.
  have h_measure_zero : MeasureTheory.volume { p : R3 | p.ofLp 2 = 0 } = 0 := by
    -- The set $\{p : \mathbb{R}^3 \mid p 2 = 0\}$ is a hyperplane in $\mathbb{R}^3$, which has Lebesgue measure zero.
    have h_hyperplane : MeasureTheory.volume {p : EuclideanSpace ℝ (Fin 3) | p 2 = 0} = 0 := by
      have : ∀ (v : EuclideanSpace ℝ (Fin 3)), v ≠ 0 → MeasureTheory.volume {p : EuclideanSpace ℝ (Fin 3) | inner ℝ p v = 0} = 0 := by
        intro v hv_ne_zero
        have h_hyperplane : MeasureTheory.volume {p : EuclideanSpace ℝ (Fin 3) | inner ℝ p v = 0} = 0 := by
          have h_submodule : ∀ (s : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), s ≠ ⊤ → MeasureTheory.volume (s : Set (EuclideanSpace ℝ (Fin 3))) = 0 := by
            exact fun s hs => Measure.addHaar_submodule volume s hs
          convert h_submodule ( LinearMap.ker ( innerₛₗ ℝ v ) ) _;
          · simp +decide [ Set.ext_iff, LinearMap.mem_ker, real_inner_comm ];
          · simp +decide [ Submodule.eq_top_iff' ];
            exact ⟨ v, by simp [ hv_ne_zero ] ⟩
        generalize_proofs at *; (
        exact h_hyperplane)
      convert this ( EuclideanSpace.single 2 1 ) ( ne_of_apply_ne ( fun v => v 2 ) ( by norm_num ) ) using 1 ; norm_num [ Fin.sum_univ_three, inner ]
    generalize_proofs at *; (
    exact h_hyperplane);
  convert addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero ( μ := MeasureTheory.MeasureSpace.volume ) ( hg.differentiable ( by norm_num ) |> Differentiable.differentiableOn ) h_measure_zero

/-
**Generic translation avoids a point.**  For a `C¹` map `g : ℝ³ → ℝ³`, the restriction of
`g` to the plane `{p 2 = 0}` (a 2-dimensional disk's worth of points) can be translated by an
arbitrarily small vector `v` so that the translated image misses any prescribed point `q`.
-/
theorem exists_translation_avoiding (g : R3 → R3) (hg : ContDiff ℝ 1 g) (q : R3)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : R3, ‖v‖ < ε ∧ ∀ p : R3, p 2 = 0 → g p + v ≠ q := by
  classical
  -- Let's denote the set of bad translations as T.
  set T := (fun y => q - y) '' (g '' {p : R3 | p 2 = 0}) with hT;
  -- Since $T$ is a null set, the open ball $Metric.ball (0 : R3) ε$ cannot be contained in $T$.
  have h_not_subset : ¬ (Metric.ball (0 : R3) ε ⊆ T) := by
    have hT_null : MeasureTheory.volume T = 0 := by
      convert smooth_image_plane_measure_zero ( fun x => q - g x ) _ using 1;
      · exact congr_arg _ ( by ext; aesop );
      · exact contDiff_const.sub hg;
    intro h; have := hT_null ▸ MeasureTheory.measure_mono h; simp_all +decide ;
    exact absurd ( this.resolve_left hε.not_ge ) ( not_le_of_gt ( by positivity ) );
  exact Exists.elim ( Set.not_subset.mp h_not_subset ) fun x hx => ⟨ x, by simpa using hx.1, fun p hp hq => hx.2 <| by aesop ⟩

/-
**Smooth approximation of a planar map.**  A continuous `F : ℝ×ℝ → ℝ³` admits a `C¹`
map `g` within any prescribed uniform distance `δ > 0`.
-/
theorem exists_smooth_approx (F : ℝ × ℝ → R3) (hF : Continuous F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : ℝ × ℝ → R3, ContDiff ℝ 1 g ∧ ∀ x, dist (g x) (F x) < δ := by
  obtain ⟨g, hg⟩ := hF.exists_contDiff_approx (n := 1) (ε := fun _ => δ) continuous_const (fun _ => hδ);
  exact ⟨ g, hg.1, hg.2.1 ⟩

/-
**Generic translation avoids a point (planar domain).**  For a `C¹` map `g : ℝ×ℝ → ℝ³`, an
arbitrarily small translation makes the image miss any prescribed point `q`.
-/
theorem exists_translation_avoiding₂ (g : ℝ × ℝ → R3) (hg : ContDiff ℝ 1 g) (q : R3)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : R3, ‖v‖ < δ ∧ ∀ x : ℝ × ℝ, g x + v ≠ q := by
  obtain ⟨ v, hv ⟩ := exists_translation_avoiding ( fun p : R3 => g ( p 0, p 1 ) ) ( by
    fun_prop ) q hδ;
  refine' ⟨ v, hv.1, fun x hx => hv.2 ( EuclideanSpace.single 0 x.1 + EuclideanSpace.single 1 x.2 ) _ _ ⟩ <;> simp_all +decide

/-
**Pushing a square off a point, rel boundary.**  A continuous square `F : I×I → ℝ³` landing
in an open set `Ω`, whose boundary avoids a point `q`, can be modified — keeping its boundary
fixed and staying inside `Ω` — to a square `G` that avoids `q` everywhere.
-/
theorem square_pushoff_rel_boundary {Ω : Set R3} (hΩ : IsOpen Ω) {q : R3}
    (F : C(↑unitInterval × ↑unitInterval, R3)) (hFΩ : ∀ p, F p ∈ Ω)
    (hbd : ∀ p : ↑unitInterval × ↑unitInterval,
      (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) → F p ≠ q) :
    ∃ G : C(↑unitInterval × ↑unitInterval, R3), (∀ p, G p ∈ Ω) ∧ (∀ p, G p ≠ q) ∧
      (∀ p : ↑unitInterval × ↑unitInterval,
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) → G p = F p) := by
  -- Let's obtain the necessary constants and approximations.
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ > 0, ∀ p : I × I, (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) → ρ₀ ≤ dist (F p) q := by
    -- The boundary is compact, and $F$ is continuous, so the image of the boundary under $F$ is also compact.
    have h_compact : IsCompact (Set.image F {p : I × I | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1}) := by
      refine' IsCompact.image _ F.continuous;
      exact ( isClosed_eq continuous_fst continuous_const |> IsClosed.union <| isClosed_eq continuous_fst continuous_const |> IsClosed.union <| isClosed_eq continuous_snd continuous_const |> IsClosed.union <| isClosed_eq continuous_snd continuous_const ) |> IsClosed.isCompact;
    have := h_compact.isClosed.isOpen_compl.mem_nhds ( show q ∉ F '' { p : I × I | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1 } from by aesop );
    rcases Metric.mem_nhds_iff.mp this with ⟨ ε, εpos, hε ⟩;
    exact ⟨ ε, εpos, fun p hp => le_of_not_gt fun h => hε ( Metric.mem_ball.mpr h ) ⟨ p, hp, rfl ⟩ ⟩
  obtain ⟨εΩ, hεΩ⟩ : ∃ εΩ > 0, Metric.thickening εΩ (Set.range F) ⊆ Ω := by
    apply_rules [ IsCompact.exists_thickening_subset_open ];
    · exact isCompact_range F.continuous;
    · exact Set.range_subset_iff.mpr hFΩ
  set r := min ρ₀ εΩ / 2 with hr
  have hr_pos : 0 < r := by
    exact div_pos ( lt_min hρ₀.1 hεΩ.1 ) zero_lt_two;
  -- Obtain a smooth approximation `g : ℝ×ℝ → R3` with `ContDiff ℝ 1 g` and `∀ x, dist (g x) (F̄ x) < r/4` (`exists_smooth_approx`, δ = r/4).
  obtain ⟨g, hg⟩ : ∃ g : ℝ × ℝ → R3, ContDiff ℝ 1 g ∧ ∀ x : ℝ × ℝ, dist (g x) (F ⟨Set.projIcc 0 1 (by norm_num) x.1, Set.projIcc 0 1 (by norm_num) x.2⟩) < r / 4 := by
    apply exists_smooth_approx;
    · fun_prop;
    · linarith;
  obtain ⟨v, hv⟩ : ∃ v : R3, ‖v‖ < r / 4 ∧ ∀ x : ℝ × ℝ, g x + v ≠ q := exists_translation_avoiding₂ g hg.1 q (by linarith);
  -- Define the bump `ψ : I×I → ℝ` and the new map `G : C(I×I, R3)`.
  set ψ : I × I → ℝ := fun p => max 0 (min 1 ((r - dist (F p) q) / (r / 2))) with hψ
  set G : C(I × I, R3) := ⟨fun p => F p + ψ p • (g (p.1.val, p.2.val) + v - F p), by
    refine' Continuous.add F.continuous _;
    refine' Continuous.smul _ _;
    · fun_prop;
    · exact Continuous.sub ( Continuous.add ( hg.1.continuous.comp <| Continuous.prodMk ( continuous_subtype_val.comp continuous_fst ) ( continuous_subtype_val.comp continuous_snd ) ) continuous_const ) F.continuous⟩ with hG
  generalize_proofs at *;
  refine' ⟨ G, _, _, _ ⟩;
  · intro p
    have h_dist : dist (G p) (F p) < r / 2 := by
      have h_dist : ‖ψ p • (g (p.1.val, p.2.val) + v - F p)‖ ≤ ‖g (p.1.val, p.2.val) - F p‖ + ‖v‖ := by
        rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ];
        refine' le_trans ( mul_le_of_le_one_left ( norm_nonneg _ ) ( max_le_iff.mpr ⟨ by norm_num, min_le_left _ _ ⟩ ) ) _;
        convert norm_add_le ( g ( p.1.val, p.2.val ) - F p ) v using 2 ; abel_nf;
      simp +zetaDelta at *;
      have := hg.2 p.1.val p.2.val; simp_all +decide [ dist_eq_norm ] ; linarith;
    refine' hεΩ.2 _;
    exact Metric.mem_thickening_iff.mpr ⟨ F p, Set.mem_range_self _, by linarith [ min_le_left ρ₀ εΩ, min_le_right ρ₀ εΩ ] ⟩;
  · intro p
    by_cases hψp : ψ p = 1;
    · simp_all +decide;
    · -- Since `ψ p ≠ 1`, we have `dist (F p) q > r / 2`.
      have h_dist_gt_r_div_2 : dist (F p) q > r / 2 := by
        contrapose! hψp;
        exact max_eq_right ( by cases min_cases ( 1 : ℝ ) ( ( r - dist ( F p ) q ) / ( r / 2 ) ) <;> nlinarith [ mul_div_cancel₀ ( r - dist ( F p ) q ) ( by linarith : ( r / 2 ) ≠ 0 ) ] ) |> fun h => h.trans ( min_eq_left <| by cases min_cases ( 1 : ℝ ) ( ( r - dist ( F p ) q ) / ( r / 2 ) ) <;> nlinarith [ mul_div_cancel₀ ( r - dist ( F p ) q ) ( by linarith : ( r / 2 ) ≠ 0 ) ] );
      -- Since `ψ p ≠ 1`, we have `dist (G p) (F p) < r / 2`.
      have h_dist_G_F_lt_r_div_2 : dist (G p) (F p) < r / 2 := by
        have h_dist_G_F_lt_r_div_2 : dist (G p) (F p) ≤ ‖g (p.1.val, p.2.val) - F p‖ + ‖v‖ := by
          simp [G, hψ];
          rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ];
          refine' le_trans ( mul_le_of_le_one_left ( norm_nonneg _ ) ( max_le_iff.mpr ⟨ by norm_num, min_le_left _ _ ⟩ ) ) _;
          convert norm_add_le ( g ( p.1.val, p.2.val ) - F p ) v using 2 ; abel_nf;
        have := hg.2 ( p.1.val, p.2.val );
        norm_num [ dist_eq_norm ] at *;
        linarith;
      contrapose! h_dist_gt_r_div_2;
      simpa only [ ← h_dist_gt_r_div_2, dist_comm ] using h_dist_G_F_lt_r_div_2.le;
  · simp +zetaDelta at *;
    intro a ha ha' b hb hb' hab; norm_num [ div_le_iff₀, hr_pos ];
    exact Or.inl <| Or.inl <| by linarith [ hρ₀.2 a ha ha' b hb hb' hab ] ;

end Submission.GenPos