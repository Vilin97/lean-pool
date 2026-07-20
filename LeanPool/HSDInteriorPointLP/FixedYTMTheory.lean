/-
Copyright (c) 2026 Makoto Yamashita. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Makoto Yamashita
-/

import LeanPool.HSDInteriorPointLP.LocalNeighborhoodEstimates

/-!
# Fixed YTM convergence ingredients

This file is the fixed part obtained after merging the old `v126` and `v127`
interface.  It exposes the Newton direction, the fixed predictor step, the local
predictor/corrector guarantees, and the contraction/log-bound lemmas used by the
algorithm-level proof.

It deliberately does not contain a user-supplied sequence `w : Nat → HSState n`.
That older interface was removed because the generated-algorithm interface in
`GeneratedConvergence.lean` constructs the iterates recursively and makes the
algorithm dependency clearer.
-/
noncomputable section

open scoped BigOperators

namespace HSDInteriorPointLP

/-!
## Lean tactic reading guide for this file

The mathematical content below is the YTM local analysis.  The short Lean tactics
used in the proofs have the following roles.

* `intro h` turns a goal of the form `P → Q` into the new assumption `h : P`
  and the remaining goal `Q`.  For `∀ x, ...`, it introduces the quantified
  variable.
* `have h : P := by ...` proves an intermediate mathematical fact and gives it
  the name `h` for later use.
* `rcases h with ⟨h1, h2, ...⟩` decomposes a conjunction or existential proof.
  It corresponds to unpacking the components of a theorem such as
  `0 < α ∧ α ≤ 1 ∧ ...`.
* `simp only [...]` rewrites only by the listed definitions and lemmas.  This is
  safer than unrestricted `simp`, because a later change in the imported library
  is less likely to change the proof.
* `simpa [defs] using h` means: simplify the current goal and the type of `h`
  using `defs`, then use `h`.  Most occurrences here only unfold names such as
  `ytmPredictorAlpha` or remove a harmless `1 - 0`.
* `ring` proves polynomial identities over real numbers, for example rearranging
  `(1 - a * (1 - 0))` into `1 - a`.
* `linarith` proves linear inequalities from the hypotheses.  It is used only
  when the remaining goal is linear in the real variables.
* `nlinarith` is the nonlinear version, used when products such as
  `hdim n * ε` or squares appear.
* `field_simp [h₁, h₂]` clears denominators using the supplied nonzero proofs;
  this is used only for algebraic cancellation in positive denominators.
-/


/-! ## Predictor scaled-direction algebra for the remaining v106 obligation -/

/-- Step 1, vector part: the predictor complementarity equation in quotient form. -/
theorem predictor_component_quotient_sum_eq_neg_one {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0) (i : Fin n) :
    d.dx i / w.x i + d.ds i / w.s i = -1 := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have hxne : w.x i ≠ 0 := ne_of_gt (hxpos i)
  have hsne : w.s i ≠ 0 := ne_of_gt (hspos i)
  have hlin : w.x i * d.ds i + w.s i * d.dx i = -(w.x i * w.s i) := by
    have hc := hdir.compl.component_eq i
    simpa using hc
  field_simp [hxne, hsne]
  nlinarith [hlin]

/-- Step 1, scalar part: the predictor scalar complementarity equation in quotient form. -/
theorem predictor_scalar_quotient_sum_eq_neg_one {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0) :
    d.dtau / w.tau + d.dkappa / w.kappa = -1 := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have htne : w.tau ≠ 0 := ne_of_gt htpos
  have hkne : w.kappa ≠ 0 := ne_of_gt hkpos
  have hlin : w.tau * d.dkappa + w.kappa * d.dtau = -(w.tau * w.kappa) := by
    have hc := hdir.compl.scalar_eq
    simpa using hc
  field_simp [htne, hkne]
  nlinarith [hlin]

/-- Step 2: skew orthogonality rewritten in quotient variables. -/
theorem predictor_quotient_weighted_cross_zero {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n,
        (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i)) +
      (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa) = 0 := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have hvec :
      (∑ i : Fin n,
          (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i)) =
        ∑ i : Fin n, d.dx i * d.ds i := by
    apply Finset.sum_congr rfl
    intro i _
    have hxne : w.x i ≠ 0 := ne_of_gt (hxpos i)
    have hsne : w.s i ≠ 0 := ne_of_gt (hspos i)
    field_simp [hxne, hsne]
  have hscalar :
      (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa) =
        d.dtau * d.dkappa := by
    have htne : w.tau ≠ 0 := ne_of_gt htpos
    have hkne : w.kappa ≠ 0 := ne_of_gt hkpos
    field_simp [htne, hkne]
  have hzero : (∑ i : Fin n, d.dx i * d.ds i) + d.dtau * d.dkappa = 0 := by
    simpa [hdot, dot] using hdir.skew.cross_zero
  simp_all

/-- Step 3: the total complementarity product is `hdim n * mu w`. -/
theorem complementarity_total_eq_hdim_mul_mu {n : Nat} (w : HSState n) :
    (∑ i : Fin n, w.x i * w.s i) + w.tau * w.kappa = hdim n * mu w := by
  have hdim_ne : hdim n ≠ 0 := ne_of_gt (hdim_pos n)
  unfold mu gap hdot dot
  field_simp [hdim_ne]

/-- Algebraic identity from `u + v = -1`: it is used componentwise in Step 4. -/
theorem square_sum_eq_one_sub_two_mul_of_sum_eq_neg_one
    {u v : ℝ} (h : u + v = -1) :
    u ^ 2 + v ^ 2 = 1 - 2 * (u * v) := by
  calc
    u ^ 2 + v ^ 2 = (u + v) ^ 2 - 2 * (u * v) := by ring
    _ = 1 - 2 * (u * v) := by
      simp_all

/-- Step 4: weighted norm identity for predictor quotient variables. -/
theorem predictor_weighted_relative_norm_identity {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n,
        (w.x i * w.s i) *
          ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) +
      (w.tau * w.kappa) *
        ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2) =
      hdim n * mu w := by
  let crossVec : Fin n → ℝ := fun i =>
    (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i)
  let crossScalar : ℝ :=
    (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa)
  have hvec_rewrite :
      (∑ i : Fin n,
          (w.x i * w.s i) *
            ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) =
        (∑ i : Fin n, w.x i * w.s i) - 2 * (∑ i : Fin n, crossVec i) := by
    calc
      (∑ i : Fin n,
          (w.x i * w.s i) *
            ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2))
          = ∑ i : Fin n, (w.x i * w.s i) * (1 - 2 *
              ((d.dx i / w.x i) * (d.ds i / w.s i))) := by
              apply Finset.sum_congr rfl
              intro i _
              have hsum := predictor_component_quotient_sum_eq_neg_one
                w d hneigh.1 hdir i
              rw [square_sum_eq_one_sub_two_mul_of_sum_eq_neg_one hsum]
      _ = ∑ i : Fin n, ((w.x i * w.s i) - 2 * crossVec i) := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [crossVec]
              ring
      _ = (∑ i : Fin n, w.x i * w.s i) - 2 * (∑ i : Fin n, crossVec i) := by
              rw [Finset.sum_sub_distrib]
              rw [← Finset.mul_sum]
  have hscalar_rewrite :
      (w.tau * w.kappa) *
          ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2) =
        w.tau * w.kappa - 2 * crossScalar := by
    have hsum := predictor_scalar_quotient_sum_eq_neg_one w d hneigh.1 hdir
    rw [square_sum_eq_one_sub_two_mul_of_sum_eq_neg_one hsum]
    dsimp [crossScalar]
    ring
  have hcross : (∑ i : Fin n, crossVec i) + crossScalar = 0 := by
    dsimp [crossVec, crossScalar]
    exact predictor_quotient_weighted_cross_zero w d hneigh.1 hdir
  have htotal := complementarity_total_eq_hdim_mul_mu w
  calc
    (∑ i : Fin n,
        (w.x i * w.s i) *
          ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) +
      (w.tau * w.kappa) *
        ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)
        = ((∑ i : Fin n, w.x i * w.s i) - 2 * (∑ i : Fin n, crossVec i)) +
            (w.tau * w.kappa - 2 * crossScalar) := by
            rw [hvec_rewrite, hscalar_rewrite]
    _ = ((∑ i : Fin n, w.x i * w.s i) + w.tau * w.kappa) -
          2 * ((∑ i : Fin n, crossVec i) + crossScalar) := by ring
    _ = hdim n * mu w := by
          simp_all

/-- Step 5, vector part: tight-neighborhood lower bound `3μ/4 ≤ xᵢsᵢ`. -/
theorem neighborhood_component_product_lower_tight {n : Nat}
    (w : HSState n) (hneigh : HSDNeighborhood ytmBetaTight w) (i : Fin n) :
    (3 / 4 : ℝ) * mu w ≤ w.x i * w.s i := by
  have hdev := neighborhood_component_dev_sq_le_bound ytmBetaTight w hneigh i
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  unfold ytmBetaTight at hdev
  have hs : 0 ≤ (w.x i * w.s i - (3 / 4 : ℝ) * mu w) ^ 2 := sq_nonneg _
  nlinarith

/-- Step 5, scalar part: tight-neighborhood lower bound `3μ/4 ≤ τκ`. -/
theorem neighborhood_scalar_product_lower_tight {n : Nat}
    (w : HSState n) (hneigh : HSDNeighborhood ytmBetaTight w) :
    (3 / 4 : ℝ) * mu w ≤ w.tau * w.kappa := by
  have hdev := neighborhood_scalar_dev_sq_le_bound ytmBetaTight w hneigh
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  unfold ytmBetaTight at hdev
  have hs : 0 ≤ (w.tau * w.kappa - (3 / 4 : ℝ) * mu w) ^ 2 := sq_nonneg _
  nlinarith


/-- Step 6, vector part: the weighted identity gives componentwise quotient-square bounds. -/
theorem predictor_component_quotient_square_bounds {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) (i : Fin n) :
    (d.dx i / w.x i) ^ 2 ≤ (4 / 3 : ℝ) * hdim n ∧
      (d.ds i / w.s i) ^ 2 ≤ (4 / 3 : ℝ) * hdim n := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  have hweighted := predictor_weighted_relative_norm_identity w d hneigh hdir
  let termVec : Fin n → ℝ := fun j =>
    (w.x j * w.s j) *
      ((d.dx j / w.x j) ^ 2 + (d.ds j / w.s j) ^ 2)
  let termScalar : ℝ :=
    (w.tau * w.kappa) *
      ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)
  have hterm_nonneg : ∀ j : Fin n, 0 ≤ termVec j := by
    intro j
    dsimp [termVec]
    exact mul_nonneg
      (mul_nonneg (le_of_lt (hxpos j)) (le_of_lt (hspos j)))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hscalar_nonneg : 0 ≤ termScalar := by
    dsimp [termScalar]
    exact mul_nonneg
      (mul_nonneg (le_of_lt htpos) (le_of_lt hkpos))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hsingle : termVec i ≤ ∑ j : Fin n, termVec j := by
    exact Finset.single_le_sum (fun j _ => hterm_nonneg j) (by simp)
  have hterm_le_total : termVec i ≤ hdim n * mu w := by
    calc
      termVec i ≤ (∑ j : Fin n, termVec j) + termScalar := by nlinarith
      _ = hdim n * mu w := by
          dsimp [termVec, termScalar]
          exact hweighted
  have hprod_lower := neighborhood_component_product_lower_tight w hneigh i
  have hprod_nonneg : 0 ≤ w.x i * w.s i := by
    exact mul_nonneg (le_of_lt (hxpos i)) (le_of_lt (hspos i))
  have hxpart_le_term :
      (w.x i * w.s i) * (d.dx i / w.x i) ^ 2 ≤ termVec i := by
    dsimp [termVec]
    have hextra : 0 ≤ (w.x i * w.s i) * (d.ds i / w.s i) ^ 2 := by
      exact mul_nonneg hprod_nonneg (sq_nonneg _)
    nlinarith
  have hspart_le_term :
      (w.x i * w.s i) * (d.ds i / w.s i) ^ 2 ≤ termVec i := by
    dsimp [termVec]
    have hextra : 0 ≤ (w.x i * w.s i) * (d.dx i / w.x i) ^ 2 := by
      exact mul_nonneg hprod_nonneg (sq_nonneg _)
    nlinarith
  constructor
  · have hmain :
        ((3 / 4 : ℝ) * mu w) * (d.dx i / w.x i) ^ 2 ≤ hdim n * mu w := by
      have hlow_mul :
          ((3 / 4 : ℝ) * mu w) * (d.dx i / w.x i) ^ 2 ≤
            (w.x i * w.s i) * (d.dx i / w.x i) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hprod_lower (sq_nonneg _)
      exact le_trans hlow_mul (le_trans hxpart_le_term hterm_le_total)
    nlinarith
  · have hmain :
        ((3 / 4 : ℝ) * mu w) * (d.ds i / w.s i) ^ 2 ≤ hdim n * mu w := by
      have hlow_mul :
          ((3 / 4 : ℝ) * mu w) * (d.ds i / w.s i) ^ 2 ≤
            (w.x i * w.s i) * (d.ds i / w.s i) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hprod_lower (sq_nonneg _)
      exact le_trans hlow_mul (le_trans hspart_le_term hterm_le_total)
    nlinarith

/-- Step 6, scalar part: quotient-square bounds for `τ` and `κ`. -/
theorem predictor_scalar_quotient_square_bounds {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (d.dtau / w.tau) ^ 2 ≤ (4 / 3 : ℝ) * hdim n ∧
      (d.dkappa / w.kappa) ^ 2 ≤ (4 / 3 : ℝ) * hdim n := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  have hweighted := predictor_weighted_relative_norm_identity w d hneigh hdir
  let termVec : Fin n → ℝ := fun j =>
    (w.x j * w.s j) *
      ((d.dx j / w.x j) ^ 2 + (d.ds j / w.s j) ^ 2)
  let termScalar : ℝ :=
    (w.tau * w.kappa) *
      ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)
  have hvec_nonneg : 0 ≤ ∑ j : Fin n, termVec j := by
    exact Finset.sum_nonneg (fun j _ => by
      dsimp [termVec]
      exact mul_nonneg
        (mul_nonneg (le_of_lt (hxpos j)) (le_of_lt (hspos j)))
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hscalar_le_total : termScalar ≤ hdim n * mu w := by
    calc
      termScalar ≤ (∑ j : Fin n, termVec j) + termScalar := by nlinarith
      _ = hdim n * mu w := by
          dsimp [termVec, termScalar]
          exact hweighted
  have hprod_lower := neighborhood_scalar_product_lower_tight w hneigh
  have hprod_nonneg : 0 ≤ w.tau * w.kappa := by
    exact mul_nonneg (le_of_lt htpos) (le_of_lt hkpos)
  have htpart_le_term :
      (w.tau * w.kappa) * (d.dtau / w.tau) ^ 2 ≤ termScalar := by
    dsimp [termScalar]
    have hextra : 0 ≤ (w.tau * w.kappa) * (d.dkappa / w.kappa) ^ 2 := by
      exact mul_nonneg hprod_nonneg (sq_nonneg _)
    nlinarith
  have hkpart_le_term :
      (w.tau * w.kappa) * (d.dkappa / w.kappa) ^ 2 ≤ termScalar := by
    dsimp [termScalar]
    have hextra : 0 ≤ (w.tau * w.kappa) * (d.dtau / w.tau) ^ 2 := by
      exact mul_nonneg hprod_nonneg (sq_nonneg _)
    nlinarith
  constructor
  · have hmain :
        ((3 / 4 : ℝ) * mu w) * (d.dtau / w.tau) ^ 2 ≤ hdim n * mu w := by
      have hlow_mul :
          ((3 / 4 : ℝ) * mu w) * (d.dtau / w.tau) ^ 2 ≤
            (w.tau * w.kappa) * (d.dtau / w.tau) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hprod_lower (sq_nonneg _)
      exact le_trans hlow_mul (le_trans htpart_le_term hscalar_le_total)
    nlinarith
  · have hmain :
        ((3 / 4 : ℝ) * mu w) * (d.dkappa / w.kappa) ^ 2 ≤ hdim n * mu w := by
      have hlow_mul :
          ((3 / 4 : ℝ) * mu w) * (d.dkappa / w.kappa) ^ 2 ≤
            (w.tau * w.kappa) * (d.dkappa / w.kappa) ^ 2 := by
        exact mul_le_mul_of_nonneg_right hprod_lower (sq_nonneg _)
      exact le_trans hlow_mul (le_trans hkpart_le_term hscalar_le_total)
    nlinarith

/-- A convenient stronger numerical bound for the fixed YTM constant. -/
theorem ytmStepConstant_le_half : ytmStepConstant ≤ (1 / 2 : ℝ) := by
  unfold ytmStepConstant
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (8 : ℝ) := by
    simp_all
  have hden_pos : 0 < (8 : ℝ) ^ 2 * Real.sqrt (8 : ℝ) := by
    positivity
  rw [div_le_iff₀ hden_pos]
  nlinarith [hsqrt_ge_one]

/-- The fixed alpha cancels the homogenized dimension after squaring. -/
theorem predictor_fixed_alpha_sq_mul_hdim (n : Nat) :
    (predictorFixedAlpha n) ^ 2 * hdim n = ytmStepConstant ^ 2 := by
  unfold predictorFixedAlpha
  have hsqrt_ne : Real.sqrt (hdim n) ≠ 0 := ne_of_gt (sqrt_hdim_pos n)
  have hsqrt_sq : (Real.sqrt (hdim n)) ^ 2 = hdim n := by
    exact Real.sq_sqrt (le_of_lt (hdim_pos n))
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]

/-- Step 7: fixed-alpha constant evaluation used by the scaled bounds. -/
theorem predictor_fixed_alpha_sq_four_thirds_hdim_lt_one (n : Nat) :
    (predictorFixedAlpha n) ^ 2 * ((4 / 3 : ℝ) * hdim n) < 1 := by
  have hcancel := predictor_fixed_alpha_sq_mul_hdim n
  have hc_nonneg : 0 ≤ ytmStepConstant := le_of_lt ytmStepConstant_pos
  have hc_le : ytmStepConstant ≤ (1 / 2 : ℝ) := ytmStepConstant_le_half
  have hc_sq : ytmStepConstant ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith
  calc
    (predictorFixedAlpha n) ^ 2 * ((4 / 3 : ℝ) * hdim n)
        = (4 / 3 : ℝ) * ((predictorFixedAlpha n) ^ 2 * hdim n) := by ring
    _ = (4 / 3 : ℝ) * ytmStepConstant ^ 2 := by rw [hcancel]
    _ ≤ (4 / 3 : ℝ) * ((1 / 2 : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hc_sq (by norm_num)
    _ < 1 := by norm_num

/-- Step 8: square bound plus fixed-alpha constant bound gives an absolute bound. -/
theorem abs_alpha_mul_lt_one_of_square_bound
    (α u B : ℝ) (hu : u ^ 2 ≤ B) (hαB : α ^ 2 * B < 1) :
    |α * u| < 1 := by
  have hsq_le : (α * u) ^ 2 ≤ α ^ 2 * B := by
    calc
      (α * u) ^ 2 = α ^ 2 * u ^ 2 := by ring
      _ ≤ α ^ 2 * B := by
          exact mul_le_mul_of_nonneg_left hu (sq_nonneg α)
  have hsq_lt : (α * u) ^ 2 < 1 := lt_of_le_of_lt hsq_le hαB
  simp_all


/-! ## Predictor center-bound estimates for Steps 9--12 -/

/-- Elementary estimate `|uv| ≤ (u² + v²)/2`. -/
theorem abs_mul_le_half_sq_add_sq (u v : ℝ) :
    |u * v| ≤ (u ^ 2 + v ^ 2) / 2 := by
  rw [abs_mul]
  have hsq : 0 ≤ (|u| - |v|) ^ 2 := sq_nonneg _
  have hu_sq : |u| ^ 2 = u ^ 2 := sq_abs u
  have hv_sq : |v| ^ 2 = v ^ 2 := sq_abs v
  nlinarith [hsq, hu_sq, hv_sq]

/-- Step 9, ℓ₁ version: the sum of absolute second-order predictor products is
bounded by half of the weighted relative norm. -/
theorem predictor_second_order_l1_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa| ≤
      hdim n * mu w / 2 := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  have hweighted := predictor_weighted_relative_norm_identity w d hneigh hdir
  have hvec :
      (∑ i : Fin n, |d.dx i * d.ds i|) ≤
        ∑ i : Fin n,
          ((w.x i * w.s i) *
            ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) / 2 := by
    exact Finset.sum_le_sum (fun i _ => by
      have hxne : w.x i ≠ 0 := ne_of_gt (hxpos i)
      have hsne : w.s i ≠ 0 := ne_of_gt (hspos i)
      have hprod_pos : 0 < w.x i * w.s i := mul_pos (hxpos i) (hspos i)
      have hrepr :
          (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i) =
            d.dx i * d.ds i := by
        field_simp [hxne, hsne]
      calc
        |d.dx i * d.ds i|
            = |(w.x i * w.s i) * ((d.dx i / w.x i) * (d.ds i / w.s i))| := by
                rw [← hrepr]
                ring_nf
        _ = (w.x i * w.s i) * |(d.dx i / w.x i) * (d.ds i / w.s i)| := by
                rw [abs_mul, abs_of_pos hprod_pos]
        _ ≤ (w.x i * w.s i) *
              (((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2) / 2) := by
                exact mul_le_mul_of_nonneg_left
                  (abs_mul_le_half_sq_add_sq (d.dx i / w.x i) (d.ds i / w.s i))
                  (le_of_lt hprod_pos)
        _ = ((w.x i * w.s i) *
              ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) / 2 := by
                ring)
  have hscalar :
      |d.dtau * d.dkappa| ≤
        ((w.tau * w.kappa) *
          ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)) / 2 := by
    have htne : w.tau ≠ 0 := ne_of_gt htpos
    have hkne : w.kappa ≠ 0 := ne_of_gt hkpos
    have hprod_pos : 0 < w.tau * w.kappa := mul_pos htpos hkpos
    have hrepr :
        (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa) =
          d.dtau * d.dkappa := by
      field_simp [htne, hkne]
    calc
      |d.dtau * d.dkappa|
          = |(w.tau * w.kappa) * ((d.dtau / w.tau) * (d.dkappa / w.kappa))| := by
              rw [← hrepr]
              ring_nf
      _ = (w.tau * w.kappa) * |(d.dtau / w.tau) * (d.dkappa / w.kappa)| := by
              rw [abs_mul, abs_of_pos hprod_pos]
      _ ≤ (w.tau * w.kappa) *
            (((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2) / 2) := by
              exact mul_le_mul_of_nonneg_left
                (abs_mul_le_half_sq_add_sq (d.dtau / w.tau) (d.dkappa / w.kappa))
                (le_of_lt hprod_pos)
      _ = ((w.tau * w.kappa) *
            ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)) / 2 := by
              ring
  calc
    (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa|
        ≤ (∑ i : Fin n,
            ((w.x i * w.s i) *
              ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) / 2) +
          ((w.tau * w.kappa) *
            ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)) / 2 := by
            exact add_le_add hvec hscalar
    _ = ((∑ i : Fin n,
            (w.x i * w.s i) *
              ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2) ) +
          (w.tau * w.kappa) *
            ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)) / 2 := by
            rw [← Finset.sum_div]
            ring
    _ = hdim n * mu w / 2 := by
            rw [hweighted]

/-- Step 9: second-order predictor products have the required square-sum bound. -/
theorem predictor_second_order_square_sum_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n, (d.dx i * d.ds i) ^ 2) +
      (d.dtau * d.dkappa) ^ 2 ≤ (hdim n * mu w / 2) ^ 2 := by
  have hl1 := predictor_second_order_l1_bound w d hneigh hdir
  have hsquares := sum_sq_add_sq_le_l1_sq
    (fun i : Fin n => d.dx i * d.ds i) (d.dtau * d.dkappa)
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  have hL_nonneg :
      0 ≤ (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa| := by
    exact add_nonneg
      (Finset.sum_nonneg (fun i _ => abs_nonneg (d.dx i * d.ds i)))
      (abs_nonneg (d.dtau * d.dkappa))
  have hQ_nonneg : 0 ≤ hdim n * mu w / 2 := by
    nlinarith [hdim_pos n, hmu]
  have hsq_l1 :
      ((∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa|) ^ 2 ≤
        (hdim n * mu w / 2) ^ 2 := by
    nlinarith
  exact le_trans hsquares hsq_l1

/-- The old centrality residual, in the sign convention used by the predictor residual,
is bounded by the tight neighborhood radius. -/
theorem predictor_old_residual_square_sum_bound {n : Nat}
    (w : HSState n) (hneigh : HSDNeighborhood ytmBetaTight w) :
    (∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) +
      (w.tau * w.kappa - mu w) ^ 2 ≤ (ytmBetaTight * mu w) ^ 2 := by
  have hcenter := neighborhood_centerSq_le ytmBetaTight w hneigh
  unfold centerSq at hcenter
  exact hcenter

/-- Pointwise two-term square inequality used as a square-sum version of the triangle
estimate for Step 10. -/
theorem sq_add_le_two_sq_add_two_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  nlinarith

/-- Step 10/11: applying the two-term square estimate componentwise to the predictor
residual split.  This is a slightly stronger bookkeeping form than introducing a
separate Euclidean norm object. -/
theorem predictor_residual_split_square_sum_bound {n : Nat}
    (a b : ℝ) (r q : Fin n → ℝ) (ρ η : ℝ) :
    (∑ i : Fin n, (a * r i + b * q i) ^ 2) + (a * ρ + b * η) ^ 2 ≤
      2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
      2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) := by
  have hvec :
      (∑ i : Fin n, (a * r i + b * q i) ^ 2) ≤
        ∑ i : Fin n, (2 * (a * r i) ^ 2 + 2 * (b * q i) ^ 2) := by
    exact Finset.sum_le_sum (fun i _ => sq_add_le_two_sq_add_two_sq (a * r i) (b * q i))
  have hscalar :
      (a * ρ + b * η) ^ 2 ≤ 2 * (a * ρ) ^ 2 + 2 * (b * η) ^ 2 :=
    sq_add_le_two_sq_add_two_sq (a * ρ) (b * η)
  calc
    (∑ i : Fin n, (a * r i + b * q i) ^ 2) + (a * ρ + b * η) ^ 2
        ≤ (∑ i : Fin n, (2 * (a * r i) ^ 2 + 2 * (b * q i) ^ 2)) +
            (2 * (a * ρ) ^ 2 + 2 * (b * η) ^ 2) := by
            exact add_le_add hvec hscalar
    _ = 2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
        2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) := by
            calc
              (∑ i : Fin n, (2 * (a * r i) ^ 2 + 2 * (b * q i) ^ 2)) +
                  (2 * (a * ρ) ^ 2 + 2 * (b * η) ^ 2)
                  = ((∑ i : Fin n, 2 * a ^ 2 * (r i) ^ 2) +
                      (∑ i : Fin n, 2 * b ^ 2 * (q i) ^ 2)) +
                    (2 * a ^ 2 * ρ ^ 2 + 2 * b ^ 2 * η ^ 2) := by
                      rw [Finset.sum_add_distrib]
                      congr 2
                      · apply Finset.sum_congr rfl
                        intro i _
                        simp only [mul_pow]
                        ring
                      · apply Finset.sum_congr rfl
                        intro i _
                        simp only [mul_pow]
                        ring
                      · simp only [mul_pow]
                        ring
                      · simp only [mul_pow]
                        ring
              _ = 2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
                  2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) := by
                      rw [← Finset.mul_sum, ← Finset.mul_sum]
                      ring

/-- The fixed predictor step length is at most one half. -/
theorem predictor_fixed_alpha_le_half (n : Nat) :
    predictorFixedAlpha n ≤ (1 / 2 : ℝ) := by
  unfold predictorFixedAlpha
  have hden : 0 < Real.sqrt (hdim n) := sqrt_hdim_pos n
  rw [div_le_iff₀ hden]
  have hc := ytmStepConstant_le_half
  have hs := one_le_sqrt_hdim n
  nlinarith

/-- Step 12: numerical constant evaluation for the center estimate, in the squared
bookkeeping form used above. -/
theorem predictor_center_two_square_constant_bound {n : Nat} (μ : ℝ)
    (_hμ : 0 ≤ μ) :
    2 * (1 - predictorFixedAlpha n) ^ 2 * ((ytmBetaTight * μ) ^ 2) +
      2 * ((predictorFixedAlpha n) ^ 2) ^ 2 * ((hdim n * μ / 2) ^ 2) ≤
      (ytmBetaWide * ((1 - predictorFixedAlpha n) * μ)) ^ 2 := by
  let α : ℝ := predictorFixedAlpha n
  let c : ℝ := ytmStepConstant
  have hα_le : α ≤ (1 / 2 : ℝ) := by
    dsimp [α]
    exact predictor_fixed_alpha_le_half n
  have hα_nonneg : 0 ≤ α := by
    dsimp [α, predictorFixedAlpha]
    exact le_of_lt (predictor_alpha_fixed_pos n)
  have ha_ge : (1 / 2 : ℝ) ≤ 1 - α := by nlinarith
  have ha_sq_ge : (1 / 4 : ℝ) ≤ (1 - α) ^ 2 := by
    nlinarith [sq_nonneg ((1 - α) - (1 / 2 : ℝ))]
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact le_of_lt ytmStepConstant_pos
  have hc_le : c ≤ (1 / 2 : ℝ) := by
    dsimp [c]
    exact ytmStepConstant_le_half
  have hc_sq_le_quarter : c ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (c - (1 / 2 : ℝ))]
  have hc_four_le : (c ^ 2) ^ 2 ≤ (1 / 16 : ℝ) := by
    nlinarith [sq_nonneg (c ^ 2 - (1 / 4 : ℝ))]
  have hcancel : α ^ 2 * hdim n = c ^ 2 := by
    dsimp [α, c]
    exact predictor_fixed_alpha_sq_mul_hdim n
  have hq_rewrite :
      2 * (α ^ 2) ^ 2 * ((hdim n * μ / 2) ^ 2) =
        ((c ^ 2) ^ 2 * μ ^ 2) / 2 := by
    calc
      2 * (α ^ 2) ^ 2 * ((hdim n * μ / 2) ^ 2)
          = ((α ^ 2 * hdim n) ^ 2 * μ ^ 2) / 2 := by ring
      _ = ((c ^ 2) ^ 2 * μ ^ 2) / 2 := by rw [hcancel]
  unfold ytmBetaTight ytmBetaWide
  dsimp [α] at *
  rw [hq_rewrite]
  have hμsq : 0 ≤ μ ^ 2 := sq_nonneg μ
  have hq_margin : ((c ^ 2) ^ 2 * μ ^ 2) / 2 ≤ ((1 - predictorFixedAlpha n) ^ 2 * μ ^ 2) / 8 := by
    nlinarith
  nlinarith

/-- Steps 9--12 combined: the fixed predictor residual is inside the wide center
radius. -/
theorem predictor_fixed_center_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n, (predictorVecResidualAfter w d i) ^ 2) +
      (predictorScalarResidualAfter w d) ^ 2 ≤
      (ytmBetaWide * ((1 - predictorFixedAlpha n) * mu w)) ^ 2 := by
  let a : ℝ := 1 - predictorFixedAlpha n
  let b : ℝ := (predictorFixedAlpha n) ^ 2
  let r : Fin n → ℝ := fun i => w.x i * w.s i - mu w
  let q : Fin n → ℝ := fun i => d.dx i * d.ds i
  let ρ : ℝ := w.tau * w.kappa - mu w
  let η : ℝ := d.dtau * d.dkappa
  have hsplit := predictor_residual_split_square_sum_bound a b r q ρ η
  have hrold := predictor_old_residual_square_sum_bound w hneigh
  have hqnew := predictor_second_order_square_sum_bound w d hneigh hdir
  have hmu_pos : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  have hcoef_a : 0 ≤ 2 * a ^ 2 := by positivity
  have hcoef_b : 0 ≤ 2 * b ^ 2 := by positivity
  have hsplit' :
      (∑ i : Fin n, (predictorVecResidualAfter w d i) ^ 2) +
        (predictorScalarResidualAfter w d) ^ 2 ≤
        2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
        2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) := by
    simpa [predictorVecResidualAfter, predictorScalarResidualAfter, a, b, r, q, ρ, η]
      using hsplit
  have hbound :
      2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
        2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) ≤
      2 * a ^ 2 * ((ytmBetaTight * mu w) ^ 2) +
        2 * b ^ 2 * ((hdim n * mu w / 2) ^ 2) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (by simpa [r, ρ] using hrold) hcoef_a)
      (mul_le_mul_of_nonneg_left
        (by simpa [q, η] using hqnew) hcoef_b)
  have hconst := predictor_center_two_square_constant_bound (n := n) (mu w)
    (le_of_lt hmu_pos)
  calc
    (∑ i : Fin n, (predictorVecResidualAfter w d i) ^ 2) +
      (predictorScalarResidualAfter w d) ^ 2
        ≤ 2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
          2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) := hsplit'
    _ ≤ 2 * a ^ 2 * ((ytmBetaTight * mu w) ^ 2) +
          2 * b ^ 2 * ((hdim n * mu w / 2) ^ 2) := hbound
    _ ≤ (ytmBetaWide * ((1 - predictorFixedAlpha n) * mu w)) ^ 2 := by
          simpa [a, b] using hconst


/-!
# Active predictor obligation after splitting fixed material

All already-fixed algebra and neighborhood bookkeeping have been moved to
`LocalNeighborhoodEstimates`.  This file starts with the only remaining analytic
predictor estimate, followed by the small wrappers that turn it into the existing
local-theory statements.
-/

/-- Remaining YTM scaled-norm estimate in named core form.

This is the single remaining analytic predictor obligation.  Earlier shifted-square
scaffolding was removed because it was not actually closing this estimate and made
the file hard to maintain. -/
theorem YTM_predictor_fixed_scaled_core_estimate {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    PredictorFixedScaledCoreBounds w d := by
  intro hneigh hdir
  /-
  Steps 1--5 are now exposed as usable Lean lemmas above:
  quotient complementarity, quotient skew orthogonality, total complementarity,
  the weighted relative-norm identity, and the tight product lower bounds.
  The remaining part of this theorem is Step 6 onward: extracting componentwise
  square bounds from the weighted identity, applying the fixed-alpha constant
  estimate, and then proving the center estimate.
  -/
  have hquot_vec : ∀ i : Fin n,
      d.dx i / w.x i + d.ds i / w.s i = -1 := by
    intro i
    exact predictor_component_quotient_sum_eq_neg_one w d hneigh.1 hdir i
  have hquot_scalar :
      d.dtau / w.tau + d.dkappa / w.kappa = -1 := by
    exact predictor_scalar_quotient_sum_eq_neg_one w d hneigh.1 hdir
  have hcross :
      (∑ i : Fin n,
          (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i)) +
        (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa) = 0 := by
    exact predictor_quotient_weighted_cross_zero w d hneigh.1 hdir
  have htotal :
      (∑ i : Fin n, w.x i * w.s i) + w.tau * w.kappa = hdim n * mu w := by
    exact complementarity_total_eq_hdim_mul_mu w
  have hweighted :
      (∑ i : Fin n,
          (w.x i * w.s i) *
            ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) +
        (w.tau * w.kappa) *
          ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2) =
        hdim n * mu w := by
    exact predictor_weighted_relative_norm_identity w d hneigh hdir
  have hlower_vec : ∀ i : Fin n,
      (3 / 4 : ℝ) * mu w ≤ w.x i * w.s i := by
    intro i
    exact neighborhood_component_product_lower_tight w hneigh i
  have hlower_scalar :
      (3 / 4 : ℝ) * mu w ≤ w.tau * w.kappa := by
    exact neighborhood_scalar_product_lower_tight w hneigh
  refine
    { scaled_vec := ?_
      scaled_tau := ?_
      scaled_kappa := ?_
      center := ?_ }
  · intro i
    have hsq := predictor_component_quotient_square_bounds w d hneigh hdir i
    have hα := predictor_fixed_alpha_sq_four_thirds_hdim_lt_one n
    exact ⟨
      by
        simpa [predictorScaledDx] using
          abs_alpha_mul_lt_one_of_square_bound
            (predictorFixedAlpha n) (d.dx i / w.x i)
            ((4 / 3 : ℝ) * hdim n) hsq.1 hα,
      by
        simpa [predictorScaledDs] using
          abs_alpha_mul_lt_one_of_square_bound
            (predictorFixedAlpha n) (d.ds i / w.s i)
            ((4 / 3 : ℝ) * hdim n) hsq.2 hα⟩
  · have hsq := predictor_scalar_quotient_square_bounds w d hneigh hdir
    have hα := predictor_fixed_alpha_sq_four_thirds_hdim_lt_one n
    simpa [predictorScaledDtau] using
      abs_alpha_mul_lt_one_of_square_bound
        (predictorFixedAlpha n) (d.dtau / w.tau)
        ((4 / 3 : ℝ) * hdim n) hsq.1 hα
  · have hsq := predictor_scalar_quotient_square_bounds w d hneigh hdir
    have hα := predictor_fixed_alpha_sq_four_thirds_hdim_lt_one n
    simpa [predictorScaledDkappa] using
      abs_alpha_mul_lt_one_of_square_bound
        (predictorFixedAlpha n) (d.dkappa / w.kappa)
        ((4 / 3 : ℝ) * hdim n) hsq.2 hα
  · exact predictor_fixed_center_bound w d hneigh hdir

/-- Expanded form of the remaining YTM scaled-norm estimate. -/
theorem YTM_predictor_fixed_scaled_norm_estimate {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    PredictorFixedScaledNormBounds w d := by
  intro hneigh hdir
  exact predictor_fixed_scaled_core_to_norm_bounds w d
    (YTM_predictor_fixed_scaled_core_estimate w d hneigh hdir)

/-- Remaining YTM scaled-direction estimate.

All algebraic consequences of the natural scaled-norm estimate are proved below
without placeholders; this theorem only converts those scaled bounds into the existing
relative-step package. -/
theorem YTM_predictor_fixed_scaled_direction_estimate {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    PredictorFixedScaledDirectionBounds w d := by
  intro hneigh hdir
  exact predictor_fixed_scaled_norm_bounds_to_direction_bounds w d hneigh
    (YTM_predictor_fixed_scaled_norm_estimate w d hneigh hdir)

/-- Remaining YTM scaled predictor estimate in relative-step form.

This is a sharper and more usable formulation of the remaining analytic input:
the fixed predictor step is small relative to every positive component, and the
explicit centrality residual is bounded by the `1/2` neighborhood radius.  The
relative bounds imply the cross-product lower bounds used above, so the only
non-algebraic part left is now the standard YTM scaled-direction estimate. -/
theorem YTM_predictor_fixed_relative_step_and_center_bound {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    (∀ i : Fin n,
      |(ytmStepConstant / Real.sqrt (hdim n)) * d.dx i| < w.x i ∧
      |(ytmStepConstant / Real.sqrt (hdim n)) * d.ds i| < w.s i) ∧
      |(ytmStepConstant / Real.sqrt (hdim n)) * d.dtau| < w.tau ∧
      |(ytmStepConstant / Real.sqrt (hdim n)) * d.dkappa| < w.kappa ∧
      (∑ i : Fin n,
        ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
            (w.x i * w.s i - mu w) +
          (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
            (d.dx i * d.ds i)) ^ 2) +
        ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
            (w.tau * w.kappa - mu w) +
          (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
            (d.dtau * d.dkappa)) ^ 2 ≤
        (ytmBetaWide *
          ((1 - ytmStepConstant / Real.sqrt (hdim n)) * mu w)) ^ 2 := by
  intro hneigh hdir
  rcases YTM_predictor_fixed_scaled_direction_estimate w d hneigh hdir with
    ⟨hrel_vec, hrel_tau, hrel_kappa, hcenter⟩
  exact ⟨hrel_vec, hrel_tau, hrel_kappa, hcenter⟩

/-- Explicit fixed-step YTM predictor estimate.

This is the remaining analytic estimate written entirely in terms of the current
point, the predictor direction, and the fixed step length.  The surrounding
lemmas convert this explicit estimate into product positivity and the
`N(1/2)` center bound for `addStep`. -/
theorem YTM_predictor_fixed_explicit_cross_lower_and_center_bound {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    (∀ i : Fin n,
      -((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.x i * w.s i)) <
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dx i * d.ds i)) ∧
      -((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.tau * w.kappa)) <
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dtau * d.dkappa) ∧
      (∑ i : Fin n,
        ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
            (w.x i * w.s i - mu w) +
          (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
            (d.dx i * d.ds i)) ^ 2) +
        ((1 - ytmStepConstant / Real.sqrt (hdim n)) *
            (w.tau * w.kappa - mu w) +
          (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
            (d.dtau * d.dkappa)) ^ 2 ≤
        (ytmBetaWide *
          ((1 - ytmStepConstant / Real.sqrt (hdim n)) * mu w)) ^ 2 := by
  intro hneigh hdir
  rcases YTM_predictor_fixed_relative_step_and_center_bound w d hneigh hdir with
    ⟨hrel_vec, hrel_tau, hrel_kappa, hcenter⟩
  refine ⟨?_, ?_, hcenter⟩
  · intro i
    have hprod :
        0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x i *
          (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s i :=
      predictor_fixed_component_product_pos_of_relative_bounds w d i
        (hrel_vec i).1 (hrel_vec i).2
    exact predictor_fixed_component_cross_lower_of_step_product_pos w d hdir i hprod
  · have hprod :
        0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau *
          (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa :=
      predictor_fixed_scalar_product_pos_of_relative_bounds w d hrel_tau hrel_kappa
    exact predictor_fixed_scalar_cross_lower_of_step_product_pos w d hdir hprod

/-- Remaining fixed-step cross-product lower bounds and centrality estimate.

This is the next isolated YTM analytic input.  Compared with the previous
`YTM_predictor_product_and_center_estimate`, this theorem no longer has to prove
product positivity directly.  It only has to show that each second-order product is
not negative enough to cancel the first-order product term, together with the
`N(1/2)` centrality estimate. -/
theorem YTM_predictor_fixed_cross_lower_and_center_bound {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    (∀ i : Fin n,
      -((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.x i * w.s i)) <
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dx i * d.ds i)) ∧
      -((1 - ytmStepConstant / Real.sqrt (hdim n)) *
          (w.tau * w.kappa)) <
        (ytmStepConstant / Real.sqrt (hdim n)) ^ 2 *
          (d.dtau * d.dkappa) ∧
      centerSq (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa
        (mu (addStep w d (ytmStepConstant / Real.sqrt (hdim n)))) ≤
        (ytmBetaWide *
          mu (addStep w d (ytmStepConstant / Real.sqrt (hdim n)))) ^ 2 := by
  intro hneigh hdir
  rcases YTM_predictor_fixed_explicit_cross_lower_and_center_bound w d hneigh hdir with
    ⟨hcross_vec, hcross_scalar, hcenter_explicit⟩
  refine ⟨hcross_vec, hcross_scalar, ?_⟩
  rw [predictor_fixed_centerSq_step_eq w d hdir, predictor_fixed_mu_step w d hdir]
  exact hcenter_explicit

/-- Product-and-centrality part of the YTM predictor estimate, now reduced to
fixed-step cross-product lower bounds plus the centrality estimate. -/
theorem YTM_predictor_product_and_center_estimate {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    (∀ i : Fin n,
      0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x i *
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s i) ∧
      0 < (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau *
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa ∧
      centerSq (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa
        (mu (addStep w d (ytmStepConstant / Real.sqrt (hdim n)))) ≤
        (ytmBetaWide *
          mu (addStep w d (ytmStepConstant / Real.sqrt (hdim n)))) ^ 2 := by
  intro hneigh hdir
  rcases YTM_predictor_fixed_cross_lower_and_center_bound w d hneigh hdir with
    ⟨hcross_vec, hcross_scalar, hcenter⟩
  refine ⟨?_, ?_, hcenter⟩
  · exact predictor_fixed_component_product_pos_of_cross_lower w d hdir hcross_vec
  · exact predictor_fixed_scalar_product_pos_of_cross_lower w d hdir hcross_scalar


/-- Isolated YTM predictor local estimate for the fixed step length.

This is the only remaining analytic ingredient on the predictor side.  All purely
algebraic bookkeeping has already been separated above: the step length is positive
and at most one, the gap update is given by `predictor_mu_step`, and the new
centrality residual is expanded by `predictor_centerSq_step_eq`.  What remains here
is the YTM scaled-direction estimate that proves both positivity preservation and
the wide-neighborhood centrality bound for the fixed step
`ytmStepConstant / sqrt(n+1)`. -/
theorem YTM_predictor_scaled_estimate {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    Interior (addStep w d (ytmStepConstant / Real.sqrt (hdim n))) ∧
      centerSq (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).x
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).tau
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).s
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))).kappa
        (mu (addStep w d (ytmStepConstant / Real.sqrt (hdim n)))) ≤
        (ytmBetaWide *
          mu (addStep w d (ytmStepConstant / Real.sqrt (hdim n)))) ^ 2 := by
  intro hneigh hdir
  rcases YTM_predictor_product_and_center_estimate w d hneigh hdir with
    ⟨hprod_vec, hprod_scalar, hcenter⟩
  refine ⟨?_, hcenter⟩
  exact predictor_step_interior_of_product_pos
    w d (ytmStepConstant / Real.sqrt (hdim n)) hneigh.1 hdir
    (predictor_alpha_fixed_le_one n) hprod_vec hprod_scalar

/-- Predictor local geometry estimate for the fixed YTM step length.

After isolating `YTM_predictor_scaled_estimate`, this theorem contains only the
wrapping needed to turn the analytic estimate into an `HSDNeighborhood` statement.
The complementarity-gap decrease is not part of this theorem; it is proved below from
`gap_addStep_of_HSDStepDirection` and `γ = 0`. -/
theorem YTM_predictor_fixed_step_local_geometry {n : Nat}
    (w : HSState n) (d : HSDirection n) :
    HSDNeighborhood ytmBetaTight w →
    HSDStepDirection w d 0 →
    0 < ytmStepConstant / Real.sqrt (hdim n) ∧
      ytmStepConstant / Real.sqrt (hdim n) ≤ 1 ∧
      Interior (addStep w d (ytmStepConstant / Real.sqrt (hdim n))) ∧
      HSDNeighborhood ytmBetaWide
        (addStep w d (ytmStepConstant / Real.sqrt (hdim n))) := by
  intro hneigh hdir
  refine ⟨predictor_alpha_fixed_pos n, predictor_alpha_fixed_le_one n, ?_⟩
  rcases YTM_predictor_scaled_estimate w d hneigh hdir with
    ⟨hinterior, hcenter⟩
  refine ⟨hinterior, ?_⟩
  have hbeta_pos : 0 < ytmBetaWide := by
    unfold ytmBetaWide
    norm_num
  have hbeta_lt : ytmBetaWide < 1 := by
    unfold ytmBetaWide
    norm_num
  exact ⟨hinterior, ⟨hbeta_pos, ⟨hbeta_lt, hcenter⟩⟩⟩

/-- Corrector estimate used in the YTM proof.

This packages the corrector half of Theorem 6: starting from the wide neighborhood
`N(1/2)`, the corrector direction with `γ = 1` accepts the full step and returns to the
tight neighborhood `N(1/4)`. -/
structure YTMCorrectorEstimate (n : Nat) : Prop where
  estimate : ∀ (w : HSState n) (d : HSDirection n),
    HSDNeighborhood ytmBetaWide w →
    HSDStepDirection w d 1 →
    CorrectorStepGuarantee ytmBetaTight w d

/-- Predictor half of the YTM local neighborhood analysis. -/
theorem YTM_predictor_estimate_from_paper (n : Nat) :
    YTMPredictorEstimate n := by
  refine ⟨?_⟩
  intro w d hneigh hdir
  let α := ytmStepConstant / Real.sqrt (hdim n)
  refine ⟨α, ?_⟩
  have hlocal : 0 < α ∧ α ≤ 1 ∧ Interior (addStep w d α) ∧
      HSDNeighborhood ytmBetaWide (addStep w d α) := by
    simpa only [α] using YTM_predictor_fixed_step_local_geometry w d hneigh hdir
  rcases hlocal with ⟨halpha_pos, halpha_le_one, hinterior, hneigh_next⟩
  refine
    { alpha_pos := halpha_pos
      alpha_le_one := halpha_le_one
      interior_next := hinterior
      neighborhood_next := hneigh_next
      gap_decrease := ?_ }
  calc
    gap (addStep w d α)
        = (1 - α * (1 - 0)) * gap w := by
            exact gap_addStep_of_HSDStepDirection w d α 0 hdir
    _ = (1 - ytmStepConstant / Real.sqrt (hdim n)) * gap w := by
            simp only [α]
            ring
    _ ≤ (1 - ytmStepConstant / Real.sqrt (hdim n)) * gap w := le_rfl

/-- Corrector half of the YTM local neighborhood analysis. -/
theorem YTM_corrector_estimate_from_paper (n : Nat) :
    YTMCorrectorEstimate n := by
  refine ⟨?_⟩
  intro w d hneigh hdir
  have hlocal := YTM_corrector_full_step_local_estimate w d hneigh hdir
  have hgap : gap (addStep w d 1) = gap w := by
    rw [gap_addStep_of_HSDStepDirection w d 1 1 hdir]
    ring
  exact
    { interior_next := hlocal.1
      neighborhood_next := hlocal.2
      gap_preserve := hgap }

/-- Fixed-parameter YTM local-analysis obligation. -/
theorem YTM_fixed_local_theory_from_paper (n : Nat) :
    YTMFixedLocalTheory n := by
  refine ⟨?_, ?_⟩
  · exact (YTM_predictor_estimate_from_paper n).estimate
  · exact (YTM_corrector_estimate_from_paper n).estimate

/-- Local predictor estimate used in YTM Theorem 6, obtained from the fixed-parameter
local theory. -/
theorem predictor_step_guarantee_fixed {n : Nat}
    (T : YTMFixedLocalTheory n)
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    ∃ α, PredictorStepGuarantee ytmBetaWide ytmStepConstant w d α :=
  T.predictor_estimate_fixed w d hneigh hdir

/-- Local corrector estimate used in YTM Theorem 6, obtained from the fixed-parameter
local theory. -/
theorem corrector_step_guarantee_fixed {n : Nat}
    (T : YTMFixedLocalTheory n)
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    CorrectorStepGuarantee ytmBetaTight w d :=
  T.corrector_estimate_fixed w d hneigh hdir


/-- Canonical Newton direction selected from the full-row-rank HLP linear algebra. -/
noncomputable def HSDNewtonDirection {m n : Nat}
    (P : LPData m n) (std : LPStandardAssumptions P)
    (w : HSState n) (hw : Interior w) (γ : ℝ) : HSDirection n :=
  chooseSearchDirection w γ
    ((HLP_newton_linear_algebra_from_full_row_rank P std).direction_system_solvable
      std w hw γ)

/-- The selected Newton direction satisfies the reduced HSD step-direction equations. -/
theorem HSDNewtonDirection_step {m n : Nat}
    (P : LPData m n) (std : LPStandardAssumptions P)
    (w : HSState n) (hw : Interior w) (γ : ℝ) :
    HSDStepDirection w (HSDNewtonDirection P std w hw γ) γ := by
  unfold HSDNewtonDirection
  exact chosen_step_direction w γ _

/-- Fixed predictor step size used in the YTM estimate. -/
def ytmPredictorAlpha (n : Nat) : ℝ :=
  ytmStepConstant / Real.sqrt (hdim n)


/-- Predictor local guarantee at the fixed YTM step. -/
theorem predictor_step_guarantee_fixed_alpha {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    PredictorStepGuarantee ytmBetaWide ytmStepConstant
      w d (ytmPredictorAlpha n) := by
  unfold ytmPredictorAlpha
  let a := ytmStepConstant / Real.sqrt (hdim n)
  rcases YTM_predictor_fixed_step_local_geometry w d hneigh hdir with
    ⟨ha_pos, ha_le_one, hinterior, hneigh_next⟩
  refine
    { alpha_pos := ha_pos
      alpha_le_one := ha_le_one
      interior_next := hinterior
      neighborhood_next := hneigh_next
      gap_decrease := ?_ }
  calc
    gap (addStep w d a) = (1 - a * (1 - 0)) * gap w := by
      exact gap_addStep_of_HSDStepDirection w d a 0 hdir
    _ = (1 - ytmStepConstant / Real.sqrt (hdim n)) * gap w := by
      simp only [a]
      ring
    _ ≤ (1 - ytmStepConstant / Real.sqrt (hdim n)) * gap w := le_rfl

/-- Corrector local guarantee from the YTM wide-to-tight estimate. -/
theorem corrector_step_guarantee_of_wide {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    CorrectorStepGuarantee ytmBetaTight w d :=
  (YTM_corrector_estimate_from_paper n).estimate w d hneigh hdir


/-- The contraction factor appearing in the two-step YTM estimate. -/
def ytmContraction (n : Nat) : ℝ :=
  1 - ytmStepConstant / Real.sqrt (hdim n)

/-- The two-step contraction factor is nonnegative. -/
theorem ytmContraction_nonneg (n : Nat) :
    0 ≤ ytmContraction n := by
  unfold ytmContraction
  have hα : ytmStepConstant / Real.sqrt (hdim n) ≤ 1 :=
    predictor_alpha_fixed_le_one n
  linarith

/-- The two-step contraction factor is at most one. -/
theorem ytmContraction_le_one (n : Nat) :
    ytmContraction n ≤ 1 := by
  unfold ytmContraction
  have hα_nonneg : 0 ≤ ytmStepConstant / Real.sqrt (hdim n) :=
    le_of_lt (predictor_alpha_fixed_pos n)
  linarith

/-- The two-step contraction factor is strictly less than one. -/
theorem ytmContraction_lt_one (n : Nat) :
    ytmContraction n < 1 := by
  unfold ytmContraction
  have hα_pos : 0 < ytmStepConstant / Real.sqrt (hdim n) :=
    predictor_alpha_fixed_pos n
  linarith

/-- Collected bounds for the two-step contraction factor. -/
theorem ytmContraction_bounds (n : Nat) :
    0 ≤ ytmContraction n ∧ ytmContraction n < 1 := by
  exact ⟨ytmContraction_nonneg n, ytmContraction_lt_one n⟩


/-- The contraction factor is exactly `1 - a_n`, where
`a_n = ytmStepConstant / sqrt(hdim n)`. -/
theorem ytmContraction_eq_one_sub_alpha (n : Nat) :
    ytmContraction n = 1 - ytmStepConstant / Real.sqrt (hdim n) := by
  rfl

/-- The reciprocal scale used in the logarithmic iteration bound cancels the
YTM step coefficient. -/
theorem ytm_alpha_mul_log_scale (n : Nat) (u : ℝ) :
    (ytmStepConstant / Real.sqrt (hdim n)) *
        ((Real.sqrt (hdim n) / ytmStepConstant) * u) = u := by
  have hc_ne : ytmStepConstant ≠ 0 := ne_of_gt ytmStepConstant_pos
  have hs_ne : Real.sqrt (hdim n) ≠ 0 := ne_of_gt (sqrt_hdim_pos n)
  field_simp [hc_ne, hs_ne]

/-- Elementary exponential majorization used for the YTM contraction: if `a ≤ 1`,
then `(1-a)^K ≤ exp(-aK)`. -/
theorem one_sub_pow_le_exp_neg_mul_nat
    {a : ℝ} (ha_le_one : a ≤ 1) :
    ∀ K : Nat, (1 - a) ^ K ≤ Real.exp (-(a * (K : ℝ))) := by
  intro K
  induction K with
  | zero =>
      simp
  | succ K ih =>
      have hbase : 1 - a ≤ Real.exp (-a) := by
        have h := Real.add_one_le_exp (-a)
        linarith
      have hleft_nonneg : 0 ≤ 1 - a := by
        linarith
      have hexp_nonneg : 0 ≤ Real.exp (-(a * (K : ℝ))) :=
        le_of_lt (Real.exp_pos _)
      calc
        (1 - a) ^ (K + 1)
            = (1 - a) ^ K * (1 - a) := by
                rw [pow_succ]
        _ ≤ Real.exp (-(a * (K : ℝ))) * Real.exp (-a) := by
                exact mul_le_mul ih hbase hleft_nonneg hexp_nonneg
        _ = Real.exp (-a) * Real.exp (-(a * (K : ℝ))) := by
                ring
        _ = Real.exp (-(a * ((K + 1 : Nat) : ℝ))) := by
                rw [← Real.exp_add]
                congr 1
                norm_num
                ring

/-- The YTM contraction power is bounded by the corresponding exponential decay. -/
theorem YTM_contraction_power_le_exp {n : Nat} (K : Nat) :
    (ytmContraction n) ^ K ≤
      Real.exp (-(ytmStepConstant / Real.sqrt (hdim n) * (K : ℝ))) := by
  have ha_le_one : ytmStepConstant / Real.sqrt (hdim n) ≤ 1 :=
    predictor_alpha_fixed_le_one n
  simpa [ytmContraction] using
    one_sub_pow_le_exp_neg_mul_nat ha_le_one K

/-- If the real-valued pair count satisfies the logarithmic lower bound, then the
exponential estimate already puts `gap0` below `ε`. -/
theorem ytm_exp_mul_gap_le_of_log_bound {n : Nat}
    (K : Nat) {gap0 ε : ℝ}
    (hgap0 : 0 < gap0) (hε_pos : 0 < ε)
    (hK : (Real.sqrt (hdim n) / ytmStepConstant) * Real.log (gap0 / ε) ≤
      (K : ℝ)) :
    Real.exp (-(ytmStepConstant / Real.sqrt (hdim n) * (K : ℝ))) * gap0 ≤ ε := by
  let a : ℝ := ytmStepConstant / Real.sqrt (hdim n)
  let scale : ℝ := Real.sqrt (hdim n) / ytmStepConstant
  have ha_nonneg : 0 ≤ a := by
    exact le_of_lt (predictor_alpha_fixed_pos n)
  have hlog_le : Real.log (gap0 / ε) ≤ a * (K : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hK ha_nonneg
    calc
      Real.log (gap0 / ε)
          = a * (scale * Real.log (gap0 / ε)) := by
              dsimp [a, scale]
              rw [ytm_alpha_mul_log_scale]
      _ ≤ a * (K : ℝ) := hmul
  have hratio_pos : 0 < gap0 / ε := div_pos hgap0 hε_pos
  have h_exp_le :
      Real.exp (-(a * (K : ℝ))) ≤ ε / gap0 := by
    calc
      Real.exp (-(a * (K : ℝ)))
          ≤ Real.exp (-(Real.log (gap0 / ε))) := by
              exact Real.exp_le_exp.mpr (by linarith)
      _ = ε / gap0 := by
              rw [Real.exp_neg, Real.exp_log hratio_pos]
              field_simp [ne_of_gt hgap0, ne_of_gt hε_pos]
  calc
    Real.exp (-(ytmStepConstant / Real.sqrt (hdim n) * (K : ℝ))) * gap0
        = Real.exp (-(a * (K : ℝ))) * gap0 := by
            rfl
    _ ≤ (ε / gap0) * gap0 := by
            exact mul_le_mul_of_nonneg_right h_exp_le (le_of_lt hgap0)
    _ = ε := by
            field_simp [ne_of_gt hgap0]


/-- Pair bound written using `L = log(gap0 / ε)`. -/
def ytmLogPairBoundL (n : Nat) (L : ℝ) : Nat :=
  Nat.ceil ((Real.sqrt (hdim n) / ytmStepConstant) * L)

/-- Ordinary iteration bound written using `L = log(gap0 / ε)`. -/
def ytmLogIterationBoundL (n : Nat) (L : ℝ) : Nat :=
  2 * ytmLogPairBoundL n L

/-- Gap-based stopping condition used by the formalized iteration bound. -/
def YTMGapStop {n : Nat} (ε : ℝ) (w : HSState n) : Prop :=
  gap w ≤ ε

/-- Duality-measure stopping condition corresponding to the paper's `μ ≤ ε`. -/
def YTMMuStop {n : Nat} (ε : ℝ) (w : HSState n) : Prop :=
  mu w ≤ ε

/-- Gap stopping immediately gives the formal gap-stop predicate. -/
theorem YTMGapStop_of_gap_le {n : Nat} {w : HSState n} {ε : ℝ}
    (hgap : gap w ≤ ε) :
    YTMGapStop ε w :=
  hgap

/-- Since `μ = gap / hdim`, a scaled gap bound gives the `μ ≤ ε` stopping test. -/
theorem YTMMuStop_of_gap_le_hdim_mul {n : Nat} {w : HSState n} {ε : ℝ}
    (hgap : gap w ≤ hdim n * ε) :
    YTMMuStop ε w := by
  unfold YTMMuStop mu
  rw [div_le_iff₀ (hdim_pos n)]
  nlinarith [hgap]

end HSDInteriorPointLP
