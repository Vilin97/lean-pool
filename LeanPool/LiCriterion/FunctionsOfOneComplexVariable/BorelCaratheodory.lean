/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

/-
  Borel–Carathéodory Theorem

  This file scaffolds the proof of the Borel–Carathéodory inequality following the
  handwritten notes.

  **Main Result**:
  If g is holomorphic on the closed disk of radius R and z satisfies ‖z‖ ≤ r < R, then
    ‖g(z)‖ ≤ (2r/(R-r)) * (A - Re(g(0))) + ‖g(0)‖
  where A = sup{Re(g(ζ)) : ‖ζ‖ = R}.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.AbsMax

/-!
# The Borel–Carathéodory inequality

A bound on `‖g‖` on a disk in terms of the supremum of `re g` on a larger disk.
-/

open Complex Real Filter Topology
open scoped BigOperators ComplexConjugate

namespace LZCBorelCaratheodory
noncomputable section

-- Define the boundary supremum using conditionally complete lattice
noncomputable def boundaryRealSup (g : ℂ → ℂ) (R : ℝ) : ℝ :=
  sSup {x | ∃ ζ : ℂ, ‖ζ‖ = R ∧ x = (g ζ).re}

lemma real_part_le_boundaryRealSup (g : ℂ → ℂ) (R : ℝ)
    (h_bdd : BddAbove {x | ∃ ζ : ℂ, ‖ζ‖ = R ∧ x = (g ζ).re})
    {ζ : ℂ} (hζ : ‖ζ‖ = R) :
    (g ζ).re ≤ boundaryRealSup g R := by
  unfold boundaryRealSup
  apply le_csSup h_bdd
  exact ⟨ζ, hζ, rfl⟩

/-- On the closed ball `‖w‖ ≤ R`, the real part of `g` is bounded by the boundary
supremum. This follows from the maximum principle for harmonic functions. -/
lemma real_part_le_boundaryRealSup_closedBall (g : ℂ → ℂ) (R : ℝ)
    (_h_R : 0 < R)
    (h_holo : ∀ w : ℂ, ‖w‖ ≤ R → DifferentiableAt ℂ g w)
    (h_bdd : BddAbove {x | ∃ ζ : ℂ, ‖ζ‖ = R ∧ x = (g ζ).re})
    {w : ℂ} (hw : ‖w‖ ≤ R) :
    (g w).re ≤ boundaryRealSup g R := by
  set A := boundaryRealSup g R with hA_def
  -- Strategy: Apply maximum modulus principle to exp(g)
  -- Since ‖exp(g(z))‖ = exp(Re(g(z))), bounding ‖exp(g)‖ bounds Re(g)
  set f := Complex.exp ∘ g with hf_def
  have hf_diff : ∀ z : ℂ, ‖z‖ < R → DifferentiableAt ℂ f z := by
    intro z hz
    apply DifferentiableAt.comp
    · exact Complex.differentiableAt_exp
    · exact h_holo z (le_of_lt hz)
  have norm_exp_eq : ∀ z, ‖f z‖ = Real.exp (g z).re := by
    intro z
    simp [f, Complex.norm_exp]
  have h_boundary : ∀ ζ : ℂ, ‖ζ‖ = R → ‖f ζ‖ ≤ Real.exp A := by
    intro ζ hζ
    rw [norm_exp_eq]
    apply Real.exp_le_exp.mpr
    exact real_part_le_boundaryRealSup g R h_bdd hζ
  have hf_le : ‖f w‖ ≤ Real.exp A := by
    by_cases hw_strict : ‖w‖ < R
    · -- Case: ‖w‖ < R (interior point)
      set U := Metric.ball (0 : ℂ) R with hU_def
      have hU_bdd : Bornology.IsBounded U := Metric.isBounded_ball
      have hf_diffcont : DiffContOnCl ℂ f U := by
        constructor
        · intro z hz
          have hz_norm : ‖z‖ < R := by
            simpa only [U, Metric.mem_ball, dist_eq_norm, sub_zero] using hz
          exact (hf_diff z hz_norm).differentiableWithinAt
        · intro z hz
          have hz_norm : ‖z‖ ≤ R := by
            apply Metric.closure_ball_subset_closedBall at hz
            simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
          have : DifferentiableAt ℂ f z := by
            apply DifferentiableAt.comp
            · exact Complex.differentiableAt_exp
            · exact h_holo z hz_norm
          exact this.continuousAt.continuousWithinAt
      have hw_closure : w ∈ closure U := by
        apply subset_closure
        simpa only [U, Metric.mem_ball, dist_eq_norm, sub_zero] using hw_strict
      apply Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hf_diffcont _ hw_closure
      intro z hz
      have hz_sphere : ‖z‖ = R := by
        have : z ∈ frontier U → ‖z‖ ≤ R := by
          intro h
          have := frontier_subset_closure h
          have := Metric.closure_ball_subset_closedBall this
          simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using this
        have hz_le : ‖z‖ ≤ R := this hz
        have hz_ge : R ≤ ‖z‖ := by
          by_contra h
          push Not at h
          have : z ∈ U := by
            simpa only [U, Metric.mem_ball, dist_eq_norm, sub_zero] using h
          have hz_interior : z ∈ interior U := by
            rw [Metric.isOpen_ball.interior_eq]
            exact this
          have h_disj : Disjoint (interior U) (frontier U) := disjoint_interior_frontier
          have : z ∉ frontier U := Set.disjoint_left.mp h_disj hz_interior
          contradiction
        exact le_antisymm hz_le hz_ge
      exact h_boundary z hz_sphere
    · -- Case: ‖w‖ = R (boundary point)
      push Not at hw_strict
      have hw_eq : ‖w‖ = R := le_antisymm hw hw_strict
      exact h_boundary w hw_eq
  rw [norm_exp_eq] at hf_le
  exact Real.exp_le_exp.mp hf_le

/-- Möbius transformation used in the Borel-Carathéodory proof.
For a > 0, this maps w ↦ w/(2a - w). -/
def mobius (a : ℝ) (w : ℂ) : ℂ := w / (2 * a - w)

lemma mobius_zero (a : ℝ) : mobius a 0 = 0 := by
  simp [mobius]

/-- If Re(w) < a, then |mobius a w| < 1. -/
lemma mobius_maps_to_unit_ball (a : ℝ) (ha : 0 < a) (w : ℂ)
    (hw : w.re < a) : ‖mobius a w‖ < 1 := by
  unfold mobius
  -- Need to show |w/(2a - w)| < 1, i.e., |w| < |2a - w|
  rw [norm_div]
  rw [div_lt_one]
  · -- Show |w| < |2a - w|
    have norm_sq_ineq : Complex.normSq w < Complex.normSq ((2 * a : ℂ) - w) := by
      rw [Complex.normSq_apply, Complex.normSq_apply]
      simp [sub_re, sub_im, ofReal_re, ofReal_im]
      -- w.re² + w.im² < (2a - w.re)² + w.im²
      nlinarith [sq_nonneg (a - w.re), hw]
    calc ‖w‖
        = Real.sqrt (Complex.normSq w) := by rw [Complex.norm_def]
      _ < Real.sqrt (Complex.normSq ((2 * a : ℂ) - w)) :=
          Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) norm_sq_ineq
      _ = ‖(2 * a : ℂ) - w‖ := by rw [Complex.norm_def]
  · -- Show 2a - w ≠ 0
    exact norm_pos_iff.mpr <| by
      intro h_eq
      have h_re_eq : (2 * a : ℂ).re = w.re := by
        have := congr_arg Complex.re h_eq
        simp [sub_re] at this
        linarith
      have : 2 * a = w.re := by simpa using h_re_eq
      linarith

/-- The Möbius transformation mobius a is differentiable where 2*a - w ≠ 0. -/
lemma mobius_differentiable (a : ℝ) (w : ℂ) (hw : (2 * a : ℂ) - w ≠ 0) :
    DifferentiableAt ℂ (mobius a) w := by
  unfold mobius
  apply DifferentiableAt.div
  · exact differentiableAt_id
  · apply DifferentiableAt.sub
    · exact differentiableAt_const _
    · exact differentiableAt_id
  · exact hw

/-- If w/(2a - w) = y, then |w| = 2a|y|/|1+y|. This is a key algebraic step.
Requires a > 0 to ensure the formula has the right sign. -/
lemma mobius_norm_formula (a : ℝ) (ha : 0 < a) (w y : ℂ)
    (hdenom : (2 * a : ℂ) - w ≠ 0)
    (heq : w / ((2 * a : ℂ) - w) = y)
    (hy_ne : y ≠ -1) :
    ‖w‖ = (2 * a) * ‖y‖ / ‖1 + y‖ := by
  -- From w / (2a - w) = y, derive w = y * (2a - w) by multiplying both sides
  have w_eq : w = y * ((2 * a : ℂ) - w) := by
    rw [div_eq_iff hdenom] at heq
    exact heq
  -- Expand: w = 2ay - yw, so w + yw = 2ay, thus w(1+y) = 2ay
  have w_times_one_plus_y : w * (1 + y) = (2 * a : ℂ) * y := by
    linear_combination w_eq
  -- Divide by (1 + y) to get w = 2ay / (1+y)
  have one_plus_y_ne_zero : (1 : ℂ) + y ≠ 0 := by
    intro h
    have : y = -1 := by
      linear_combination h
    exact hy_ne this
  have w_formula : w = (2 * a : ℂ) * y / (1 + y) := by
    rw [eq_div_iff one_plus_y_ne_zero]
    exact w_times_one_plus_y
  -- Take norms
  calc ‖w‖
      = ‖(2 * a : ℂ) * y / (1 + y)‖ := by rw [w_formula]
    _ = ‖(2 * a : ℂ) * y‖ / ‖1 + y‖ := norm_div _ _
    _ = ‖(2 * a : ℂ)‖ * ‖y‖ / ‖1 + y‖ := by rw [norm_mul]
    _ = (2 * a) * ‖y‖ / ‖1 + y‖ := by
        have h : ‖(2 * a : ℂ)‖ = 2 * a := by
          norm_cast
          exact abs_of_pos (by linarith : 0 < 2 * a)
        rw [h]

/-- Helper lemma: if y = w/(2a - w) and Re(w) < a, then |y| < 1.
This avoids duplicating the proof from mobius_maps_to_unit_ball. -/
lemma norm_lt_one_of_div_eq (a : ℝ) (ha : 0 < a) (w y : ℂ)
    (hw : w.re < a)
    (heq : w / ((2 * a : ℂ) - w) = y) : ‖y‖ < 1 := by
  rw [← heq]
  exact mobius_maps_to_unit_ball a ha w hw

/-- The function t ↦ t/(1-t) is monotonically increasing on [0, 1). -/
lemma div_one_sub_mono {x y : ℝ} (_hx : 0 ≤ x) (hy : y < 1) (hxy : x ≤ y) :
    x / (1 - x) ≤ y / (1 - y) := by
  have hx1 : x < 1 := lt_of_le_of_lt hxy hy
  have h1x : 0 < 1 - x := by linarith
  have h1y : 0 < 1 - y := by linarith
  exact (div_le_div_iff₀ h1x h1y).2 (by nlinarith)

/-- A bundled structure for functions that map ball(0, R) into closedBall(0, 1),
    are holomorphic, and fix the origin. This abstraction prevents
    excessive unfolding when composing functions like Möbius transformations. -/
structure BallToUnitBall (R : ℝ) where
  /-- The underlying function -/
  toFun : ℂ → ℂ
  /-- The function maps the ball of radius R into the closed unit ball -/
  maps_to : Set.MapsTo toFun (Metric.ball 0 R) (Metric.closedBall 0 1)
  /-- The function is holomorphic on the ball -/
  differentiable : DifferentiableOn ℂ toFun (Metric.ball 0 R)
  /-- The function fixes 0 -/
  maps_zero : toFun 0 = 0

namespace BallToUnitBall

instance (R : ℝ) : CoeFun (BallToUnitBall R) (fun _ => ℂ → ℂ) where
  coe := BallToUnitBall.toFun

/-- The Schwarz lemma for bundled ball-to-ball functions -/
theorem schwarz_bound {R : ℝ} (f : BallToUnitBall R) {z : ℂ} (hz : z ∈ Metric.ball 0 R) :
    ‖f.toFun z‖ ≤ ‖z‖ / R := by
  have h_R : 0 < R := Metric.nonempty_ball.mp ⟨z, hz⟩
  -- Apply mathlib's Schwarz lemma
  have h_maps' : Set.MapsTo f.toFun (Metric.ball 0 R) (Metric.closedBall (f.toFun 0) 1) := by
    rw [f.maps_zero]
    exact f.maps_to
  have key : dist (f.toFun z) (f.toFun 0) ≤ 1 / R * dist z 0 :=
    Complex.dist_le_div_mul_dist_of_mapsTo_ball f.differentiable h_maps' hz
  rw [f.maps_zero] at key
  simp only [dist_zero_right] at key
  calc ‖f.toFun z‖ ≤ 1 / R * ‖z‖ := key
    _ = ‖z‖ / R := by ring

end BallToUnitBall

/-- Inversion bound for Möbius transformation: if y = w/(2a - w) and |y| < 1,
then |w| ≤ 2a|y|/(1 - |y|).

This lemma is stated without direct reference to `mobius` to avoid type checking issues. -/
lemma mobius_inversion_bound (a : ℝ) (ha : 0 < a) (w : ℂ)
    (hw_re : w.re < a) (y : ℂ)
    (hdenom : (2 * a : ℂ) - w ≠ 0)
    (heq : w / ((2 * a : ℂ) - w) = y) :
    ‖w‖ ≤ (2 * a) * (‖y‖ / (1 - ‖y‖)) := by
  -- Step 1: Show |y| < 1 using the helper lemma
  have y_bound : ‖y‖ < 1 := norm_lt_one_of_div_eq a ha w y hw_re heq
  -- Step 2: Show y ≠ -1 from |y| < 1
  have y_ne_neg_one : y ≠ -1 := by
    intro h
    have : ‖y‖ = 1 := by simp [h, norm_neg]
    linarith
  -- Step 3: Apply mobius_norm_formula
  have w_norm_eq := mobius_norm_formula a ha w y hdenom heq y_ne_neg_one
  -- Step 4: Reverse triangle inequality: 1 - ‖y‖ ≤ ‖1 + y‖
  -- Direct proof using triangle inequality
  have reverse_triangle : 1 - ‖y‖ ≤ ‖1 + y‖ := by
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    have h2 : (1 : ℂ) = (1 + y) + (-y) := by ring
    have h3 : ‖(1 : ℂ)‖ ≤ ‖1 + y‖ + ‖-y‖ := by
      conv_lhs => rw [h2]
      exact norm_add_le (1 + y) (-y)
    have h4 : ‖-y‖ = ‖y‖ := norm_neg y
    linarith
  -- Step 5: Conclude
  calc ‖w‖
      = (2 * a) * ‖y‖ / ‖1 + y‖ := w_norm_eq
    _ ≤ (2 * a) * ‖y‖ / (1 - ‖y‖) := by
        apply div_le_div_of_nonneg_left
        · exact mul_nonneg (by linarith : 0 ≤ 2 * a) (norm_nonneg y)
        · linarith
        · exact reverse_triangle
    _ = (2 * a) * (‖y‖ / (1 - ‖y‖)) := by rw [mul_div_assoc]

/-- **Borel–Carathéodory Theorem (Point-wise version)**.

If `g : ℂ → ℂ` is holomorphic on the closed disk `‖z‖ ≤ R` and `r < R`, then for any
`z` with `‖z‖ ≤ r`, we have
  `‖g z‖ ≤ (2r/(R-r)) * (A - Re(g(0))) + ‖g(0)‖`
where `A := sup {Re(g(ζ)) : ‖ζ‖ = R}`.

**Proof strategy**:
1. Use maximum modulus principle to show Re(g(w)) ≤ A for all ‖w‖ ≤ R
2. For any ε > 0, construct auxiliary function h_ε mapping ball(0,R) → ball(0,1)
3. Apply Schwarz lemma to h_ε
4. Take ε → 0 to get the final bound
-/
lemma borel_caratheodory_point (g : ℂ → ℂ) (R r : ℝ)
    (h_R : 0 < R) (h_r : r < R)
    (h_holo : ∀ z : ℂ, ‖z‖ ≤ R → DifferentiableAt ℂ g z)
    (h_bdd : BddAbove {x | ∃ ζ : ℂ, ‖ζ‖ = R ∧ x = (g ζ).re}) :
    ∀ z : ℂ, ‖z‖ ≤ r →
      ‖g z‖ ≤
        (2 * r / (R - r)) *
          (boundaryRealSup g R - (g 0).re) + ‖g 0‖ := by
  intro z hz
  -- Define the boundary supremum
  set A : ℝ := boundaryRealSup g R with hA_def
  -- Step 1: Show Re(g(w)) ≤ A for all ‖w‖ ≤ R via maximum modulus principle
  have re_le_A : ∀ w : ℂ, ‖w‖ ≤ R → (g w).re ≤ A := by
    intro w hw
    exact real_part_le_boundaryRealSup_closedBall g R h_R h_holo h_bdd hw
  -- Step 2: For any ε > 0, construct auxiliary map h_ε
  have main_eps : ∀ ε > 0,
      ‖g z‖ ≤ (2 * r / (R - r)) * (A - (g 0).re + ε) + ‖g 0‖ := by
    intro ε hε
    -- Define a := A - Re g(0) + ε > 0
    set a : ℝ := A - (g 0).re + ε with ha_def
    have ha_pos : 0 < a := by
      have h_g0_le_A : (g 0).re ≤ A := re_le_A 0 (by simp [h_R.le] : ‖(0:ℂ)‖ ≤ R)
      linarith
    -- **Bundle the function as a BallToUnitBall to avoid unfolding**
    -- Define v(w) = g(w) - g(0) and hεf = mobius a ∘ v
    let v : ℂ → ℂ := fun w => g w - g 0
    -- Construct hεf as a bundled BallToUnitBall structure
    let hεf : BallToUnitBall R := {
      toFun := mobius a ∘ v

      maps_to := by
        intro w hw
        simp only [Metric.mem_ball, dist_zero_right] at hw
        simp only [Metric.mem_closedBall, dist_zero_right, Function.comp_def]
        apply le_of_lt
        apply mobius_maps_to_unit_ball a ha_pos
        change (g w - g 0).re < a
        have hw_le : ‖w‖ ≤ R := le_of_lt hw
        have : (g w).re ≤ A := re_le_A w hw_le
        calc (g w - g 0).re
            = (g w).re - (g 0).re := by simp [sub_re]
          _ ≤ A - (g 0).re := by linarith
          _ < a := by linarith

      differentiable := by
        intro w hw
        -- v is differentiable
        have h_v_diff : DifferentiableWithinAt ℂ v (Metric.ball 0 R) w := by
          simp only [v]
          apply DifferentiableWithinAt.sub
          · exact (h_holo w (le_of_lt (mem_ball_zero_iff.mp hw))).differentiableWithinAt
          · exact differentiableWithinAt_const (c := g 0)
        -- mobius a is differentiable at v w
        have h_mobius_diff : DifferentiableAt ℂ (mobius a) (v w) := by
          apply mobius_differentiable
          change (2 * a : ℂ) - (g w - g 0) ≠ 0
          intro h_eq
          have hw_le : ‖w‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hw)
          have : (g w).re ≤ A := re_le_A w hw_le
          have v_re_lt : (g w - g 0).re < a := by
            calc (g w - g 0).re
                = (g w).re - (g 0).re := by simp [sub_re]
              _ ≤ A - (g 0).re := by linarith
              _ < a := by linarith
          have h_re_eq : (2 * a : ℂ).re = (g w - g 0).re := by
            have := congr_arg Complex.re h_eq
            simp [sub_re] at this
            linarith
          have : 2 * a = (g w - g 0).re := by simpa using h_re_eq
          linarith
        -- Compose them
        apply DifferentiableWithinAt.comp (s := Metric.ball 0 R) (t := Set.univ)
        · exact h_mobius_diff.differentiableWithinAt
        · exact h_v_diff
        · intros x _; exact Set.mem_univ _
      maps_zero := by simp [v, mobius_zero]
    }
    have hz_mem : z ∈ Metric.ball (0 : ℂ) R := by
      have hz_lt : ‖z‖ < R := lt_of_le_of_lt hz h_r
      simpa [Metric.mem_ball, dist_eq_norm] using hz_lt
    -- **Apply bundled Schwarz lemma - no unfolding needed!**
    have hz_bound : ‖hεf.toFun z‖ ≤ ‖z‖ / R :=
      BallToUnitBall.schwarz_bound hεf hz_mem
    -- **Möbius Transformation Inversion**
    -- We need: ‖g z - g 0‖ ≤ (2*a) * (‖hεf.toFun z‖ / (1 - ‖hεf.toFun z‖))
    -- Since hεf.toFun z = mobius a (v z) where v z = g z - g 0,
    -- we can apply mobius_inversion_bound
    have bound_g_sub : ‖g z - g 0‖ ≤ (2 * a) * (‖hεf.toFun z‖ / (1 - ‖hεf.toFun z‖)) := by
      have v_z_re_lt : (v z).re < a := by
        change (g z - g 0).re < a
        have hz_le : ‖z‖ ≤ R := le_trans hz (le_of_lt h_r)
        have : (g z).re ≤ A := re_le_A z hz_le
        calc (g z - g 0).re
            = (g z).re - (g 0).re := by simp [sub_re]
          _ ≤ A - (g 0).re := by linarith
          _ < a := by linarith
      have v_z_denom_ne_zero : (2 * a : ℂ) - (v z) ≠ 0 := by
        intro h_eq
        have h_re_eq : (2 * a : ℂ).re = (v z).re := by
          have := congr_arg Complex.re h_eq
          simp [sub_re] at this
          linarith
        have : 2 * a = (v z).re := by simpa using h_re_eq
        linarith [v_z_re_lt]
      have v_z_mobius_eq : (v z) / ((2 * a : ℂ) - (v z)) = hεf.toFun z := by
        rfl
      exact
        mobius_inversion_bound
          a ha_pos (v z) v_z_re_lt (hεf.toFun z) v_z_denom_ne_zero v_z_mobius_eq
    -- Substitute the Schwarz bound
    have h_mono_step1 : ‖g z - g 0‖ ≤ (2 * a) * ((‖z‖ / R) / (1 - (‖z‖ / R))) := by
      -- Use monotonicity of x ↦ x/(1-x) and hz_bound
      have h_z_over_R_lt_1 : ‖z‖ / R < 1 := by
        have : ‖z‖ < R := lt_of_le_of_lt hz h_r
        rw [div_lt_one h_R]
        exact this
      -- Monotonicity: if x ≤ y and y < 1, then x/(1-x) ≤ y/(1-y)
      -- For 0 ≤ x ≤ y < 1, the function f(t) = t/(1-t) is increasing
      -- This is a standard result from calculus: f'(t) = 1/(1-t)² > 0
      have mono : ‖hεf.toFun z‖ / (1 - ‖hεf.toFun z‖) ≤ (‖z‖ / R) / (1 - (‖z‖ / R)) := by
        apply div_one_sub_mono
        · exact norm_nonneg _
        · exact h_z_over_R_lt_1
        · exact hz_bound
      calc ‖g z - g 0‖
          ≤ (2 * a) * (‖hεf.toFun z‖ / (1 - ‖hεf.toFun z‖)) := bound_g_sub
        _ ≤ (2 * a) * ((‖z‖ / R) / (1 - (‖z‖ / R))) := by
            gcongr
    -- Use ‖z‖ ≤ r
    have bound_at_r : ‖g z - g 0‖ ≤ (2 * a) * (r / (R - r)) := by
      -- Again use monotonicity: ‖z‖ ≤ r implies (‖z‖/R)/(1-‖z‖/R) ≤ (r/R)/(1-r/R)
      have h_r_over_R_lt_1 : r / R < 1 := by
        rw [div_lt_one h_R]
        exact h_r
      have h_z_over_R_le_r_over_R : ‖z‖ / R ≤ r / R := by
        exact div_le_div_of_nonneg_right hz (le_of_lt h_R)
      -- Simplify (r/R) / (1 - r/R) = r / (R - r)
      have simplify_frac : (r / R) / (1 - r / R) = r / (R - r) := by
        have h_R_ne_zero : R ≠ 0 := ne_of_gt h_R
        have h_R_sub_r_ne_zero : R - r ≠ 0 := by linarith [h_r]
        field_simp
      -- Apply monotonicity again: ‖z‖ ≤ r implies the fractions satisfy the inequality
      -- This is again an application of monotonicity of t ↦ t/(1-t)
      have mono2 : (‖z‖ / R) / (1 - ‖z‖ / R) ≤ (r / R) / (1 - r / R) := by
        apply div_one_sub_mono
        · apply div_nonneg
          · exact norm_nonneg z
          · linarith
        · exact h_r_over_R_lt_1
        · exact h_z_over_R_le_r_over_R
      calc ‖g z - g 0‖
          ≤ (2 * a) * ((‖z‖ / R) / (1 - (‖z‖ / R))) := h_mono_step1
        _ ≤ (2 * a) * ((r / R) / (1 - r / R)) := by
            gcongr
        _ = (2 * a) * (r / (R - r)) := by rw [simplify_frac]
    -- Final triangle inequality
    calc ‖g z‖
        = ‖(g z - g 0) + g 0‖ := by ring_nf
      _ ≤ ‖g z - g 0‖ + ‖g 0‖ := norm_add_le _ _
      _ ≤ (2 * a) * (r / (R - r)) + ‖g 0‖ := by linarith [bound_at_r]
      _ = (2 * r / (R - r)) * a + ‖g 0‖ := by ring
      _ = (2 * r / (R - r)) * (A - (g 0).re + ε) + ‖g 0‖ := by rw [ha_def]
  -- Handle special case r = 0
  by_cases hr0 : r = 0
  · have hz0 : z = 0 := by
      have : ‖z‖ ≤ 0 := by simpa [hr0] using hz
      exact norm_le_zero_iff.mp this
    simp [hz0, hr0]
  -- Take limit as ε → 0
  have h_main : ‖g z‖ ≤ (2 * r / (R - r)) * (A - (g 0).re) + ‖g 0‖ := by
    -- For any δ > 0, ‖g z‖ ≤ base + δ
    have base_le : ∀ δ > 0, ‖g z‖ ≤ (2 * r / (R - r)) * (A - (g 0).re) + ‖g 0‖ + δ := by
      intro δ hδ
      have cpos : 0 < (2 * r / (R - r)) := by
        have : 0 < R - r := sub_pos.mpr h_r
        have hrpos : 0 < r := by
          have hrle : 0 ≤ r := le_trans (norm_nonneg z) hz
          exact lt_of_le_of_ne hrle (Ne.symm hr0)
        exact div_pos (by linarith) this
      set ε := δ / (2 * r / (R - r)) with hε_def
      have hε : 0 < ε := by
        simpa only [hε_def] using div_pos hδ cpos
      have := main_eps ε hε
      have heq : (2 * r / (R - r)) * (A - (g 0).re + ε) + ‖g 0‖
            = (2 * r / (R - r)) * (A - (g 0).re) + ‖g 0‖ + δ := by
        have h_eps_eq : (2 * r / (R - r)) * ε = δ := by
          rw [hε_def]
          exact mul_div_cancel₀ δ (ne_of_gt cpos)
        calc (2 * r / (R - r)) * (A - (g 0).re + ε) + ‖g 0‖
            = (2 * r / (R - r)) * (A - (g 0).re) + (2 * r / (R - r)) * ε + ‖g 0‖ := by ring
          _ = (2 * r / (R - r)) * (A - (g 0).re) + δ + ‖g 0‖ := by rw [h_eps_eq]
          _ = (2 * r / (R - r)) * (A - (g 0).re) + ‖g 0‖ + δ := by ring
      exact heq ▸ this
    -- Deduce ≤ base from ≤ base + δ for all δ > 0
    refine (le_iff_forall_pos_lt_add).2 fun ε hε => ?_
    have h_base : ‖g z‖ ≤ (2 * r / (R - r)) * (A - (g 0).re) + ‖g 0‖ + ε / 2 :=
      base_le (ε / 2) (by linarith)
    linarith [h_base]
  exact h_main

end
end LZCBorelCaratheodory
