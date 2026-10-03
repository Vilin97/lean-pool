/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Convex jet Hessian estimates
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal

open ContinuousLinearMap

namespace ViscositySolns

variable {n : Nat}

/--
For a function convex on a closed ball, the Hessian component of an ordinary
superjet at an interior point of that ball has nonnegative quadratic form in
every direction.

In quantified mathematical form, if `g` is convex on `closedBall x0 r`,
`x ∈ ball x0 r`, `(p, X) ∈ J^{2,+}_{R^n} g(x)`, and `v ∈ R^n`, then
`0 ≤ ⟪Xv, v⟫`.
-/
theorem Superjet.quadraticForm_nonneg_of_convexOn_closedBall
    {g : Point n -> Real} {x x0 : Point n} {r : Real} {J : Jet n}
    (hconv : ConvexOn Real (Metric.closedBall x0 r) g)
    (hx : x ∈ Metric.ball x0 r)
    (hJ : J ∈ Superjet Set.univ g x)
    (v : Point n) :
    0 <= dotProduct (Matrix.mulVec J.hessian v) v := by
  by_cases hv : v = 0
  · simp [hv]
  by_contra hnot
  have hQneg : dotProduct (Matrix.mulVec J.hessian v) v < 0 := lt_of_not_ge hnot
  let Q : Real := dotProduct (Matrix.mulVec J.hessian v) v
  have hQneg' : Q < 0 := hQneg
  rcases hJ with ⟨rho, hrho, hineq⟩
  let linePlus : Real -> Point n := fun t => x + t • v
  let lineMinus : Real -> Point n := fun t => x - t • v
  have hlinePlus_nhds : Filter.Tendsto linePlus (𝓝 (0 : Real)) (𝓝 x) := by
    have hcont :
        ContinuousAt (fun t : Real => x + t • v) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    simpa [linePlus, ContinuousAt] using hcont
  have hlineMinus_nhds : Filter.Tendsto lineMinus (𝓝 (0 : Real)) (𝓝 x) := by
    have hcont :
        ContinuousAt (fun t : Real => x - t • v) 0 :=
      (continuous_const.sub (continuous_id.smul continuous_const)).continuousAt
    simpa [lineMinus, ContinuousAt] using hcont
  have hlinePlus_right : Filter.Tendsto linePlus (𝓝[>] (0 : Real)) (𝓝 x) :=
    hlinePlus_nhds.mono_left nhdsWithin_le_nhds
  have hlineMinus_right : Filter.Tendsto lineMinus (𝓝[>] (0 : Real)) (𝓝 x) :=
    hlineMinus_nhds.mono_left nhdsWithin_le_nhds
  have hplus_mem :
      ∀ᶠ t in 𝓝[>] (0 : Real), linePlus t ∈ Metric.closedBall x0 r :=
    hlinePlus_right.eventually (Metric.closedBall_mem_nhds_of_mem hx)
  have hminus_mem :
      ∀ᶠ t in 𝓝[>] (0 : Real), lineMinus t ∈ Metric.closedBall x0 r :=
    hlineMinus_right.eventually (Metric.closedBall_mem_nhds_of_mem hx)
  have hineq_nhds : ∀ᶠ y in 𝓝 x,
      g y <= quadraticModel x (g x) J.gradient J.hessian y + rho y := by
    simpa [nhdsWithin_univ] using hineq
  have hineqPlus :
      ∀ᶠ t in 𝓝[>] (0 : Real),
        g (linePlus t) <=
          quadraticModel x (g x) J.gradient J.hessian (linePlus t) + rho (linePlus t) :=
    hlinePlus_right.eventually hineq_nhds
  have hineqMinus :
      ∀ᶠ t in 𝓝[>] (0 : Real),
        g (lineMinus t) <=
          quadraticModel x (g x) J.gradient J.hessian (lineMinus t) + rho (lineMinus t) :=
    hlineMinus_right.eventually hineq_nhds
  have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnorm_sq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hnorm_pos
  let c : Real := (-Q) / (4 * ‖v‖ ^ 2)
  have hc : 0 < c := by
    have hnegQpos : 0 < -Q := neg_pos.mpr hQneg'
    have hden : 0 < 4 * ‖v‖ ^ 2 := by positivity
    dsimp [c]
    exact div_pos hnegQpos hden
  have hrho_bound_nhds :
      ∀ᶠ y in 𝓝 x, ‖rho y‖ <= c * ‖y - x‖ ^ 2 := by
    simpa [SemijetRemainder, nhdsWithin_univ] using hrho.bound hc
  have hrhoPlus :
      ∀ᶠ t in 𝓝[>] (0 : Real),
        ‖rho (linePlus t)‖ <= c * ‖linePlus t - x‖ ^ 2 :=
    hlinePlus_right.eventually hrho_bound_nhds
  have hrhoMinus :
      ∀ᶠ t in 𝓝[>] (0 : Real),
        ‖rho (lineMinus t)‖ <= c * ‖lineMinus t - x‖ ^ 2 :=
    hlineMinus_right.eventually hrho_bound_nhds
  have hcontra_event : ∀ᶠ t in 𝓝[>] (0 : Real), False := by
    filter_upwards [self_mem_nhdsWithin, hplus_mem, hminus_mem, hineqPlus, hineqMinus,
      hrhoPlus, hrhoMinus] with
      t htpos hplusBall hminusBall hplus hminus hrhoPlusB hrhoMinusB
    have hplus_sub : linePlus t - x = t • v := by
      ext i
      simp [linePlus]
    have hminus_sub : lineMinus t - x = -t • v := by
      ext i
      simp [lineMinus]
    have hnorm_plus : ‖linePlus t - x‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      rw [hplus_sub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      ring
    have hnorm_minus : ‖lineMinus t - x‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      rw [hminus_sub, norm_smul, Real.norm_eq_abs, abs_of_neg (neg_neg_of_pos htpos)]
      ring
    have hquad_plus :
        quadraticModel x (g x) J.gradient J.hessian (linePlus t) =
          g x + t * dotProduct J.gradient v + (1 / 2 : Real) * t ^ 2 * Q := by
      calc
        quadraticModel x (g x) J.gradient J.hessian (linePlus t)
            = quadraticModel x (g x) J.gradient J.hessian (x + t • v) := rfl
        _ = g x + t * dotProduct J.gradient v + (1 / 2 : Real) * t ^ 2 * Q := by
          simpa [Q] using quadraticModel_line x (g x) t J.gradient v J.hessian
    have hquad_minus :
        quadraticModel x (g x) J.gradient J.hessian (lineMinus t) =
          g x - t * dotProduct J.gradient v + (1 / 2 : Real) * t ^ 2 * Q := by
      calc
        quadraticModel x (g x) J.gradient J.hessian (lineMinus t)
            = quadraticModel x (g x) J.gradient J.hessian (x + (-t) • v) := by
              congr 1
              ext i
              simp [lineMinus]
              ring
        _ = g x + (-t) * dotProduct J.gradient v +
              (1 / 2 : Real) * (-t) ^ 2 * Q := by
          simpa [Q] using quadraticModel_line x (g x) (-t) J.gradient v J.hessian
        _ = g x - t * dotProduct J.gradient v + (1 / 2 : Real) * t ^ 2 * Q := by
          ring
    have hrhoPlus_upper : rho (linePlus t) <= c * t ^ 2 * ‖v‖ ^ 2 := by
      have hρ : rho (linePlus t) <= ‖rho (linePlus t)‖ := by
        simpa [Real.norm_eq_abs] using le_abs_self (rho (linePlus t))
      rw [hnorm_plus] at hrhoPlusB
      linarith only [hρ, hrhoPlusB]
    have hrhoMinus_upper : rho (lineMinus t) <= c * t ^ 2 * ‖v‖ ^ 2 := by
      have hρ : rho (lineMinus t) <= ‖rho (lineMinus t)‖ := by
        simpa [Real.norm_eq_abs] using le_abs_self (rho (lineMinus t))
      rw [hnorm_minus] at hrhoMinusB
      linarith only [hρ, hrhoMinusB]
    have hconv_mid :
        g x <= (1 / 2 : Real) * g (linePlus t) + (1 / 2 : Real) * g (lineMinus t) := by
      have hconv_ineq := hconv.2 hplusBall hminusBall
        (by norm_num : (0 : Real) <= (1 / 2 : Real))
        (by norm_num : (0 : Real) <= (1 / 2 : Real))
        (by norm_num : (1 / 2 : Real) + (1 / 2 : Real) = 1)
      have hmid :
          (1 / 2 : Real) • linePlus t + (1 / 2 : Real) • lineMinus t = x := by
        ext i
        simp [linePlus, lineMinus]
        ring
      rw [hmid] at hconv_ineq
      simpa using hconv_ineq
    have havg_upper :
        (1 / 2 : Real) * g (linePlus t) + (1 / 2 : Real) * g (lineMinus t) <=
          g x + (1 / 2 : Real) * t ^ 2 * Q + c * t ^ 2 * ‖v‖ ^ 2 := by
      have hplus' :
          g (linePlus t) <=
            g x + t * dotProduct J.gradient v + (1 / 2 : Real) * t ^ 2 * Q +
              c * t ^ 2 * ‖v‖ ^ 2 := by
        rw [hquad_plus] at hplus
        linarith only [hplus, hrhoPlus_upper]
      have hminus' :
          g (lineMinus t) <=
            g x - t * dotProduct J.gradient v + (1 / 2 : Real) * t ^ 2 * Q +
              c * t ^ 2 * ‖v‖ ^ 2 := by
        rw [hquad_minus] at hminus
        linarith only [hminus, hrhoMinus_upper]
      linarith only [hplus', hminus']
    have hnonneg :
        0 <= (1 / 2 : Real) * t ^ 2 * Q + c * t ^ 2 * ‖v‖ ^ 2 := by
      linarith only [havg_upper, hconv_mid]
    have hnegative :
        (1 / 2 : Real) * t ^ 2 * Q + c * t ^ 2 * ‖v‖ ^ 2 < 0 := by
      have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos htpos
      calc
        (1 / 2 : ℝ) * t ^ 2 * Q + c * t ^ 2 * ‖v‖ ^ 2 = t ^ 2 * Q / 4 := by
          dsimp [c]
          field_simp [ne_of_gt hnorm_sq_pos]
          ring
        _ < 0 := div_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg ht_sq_pos hQneg') (by norm_num)
    exact not_le_of_gt hnegative hnonneg
  rcases Filter.Eventually.exists hcontra_event with ⟨_, hfalse⟩
  exact hfalse

/--
For a function convex on a closed ball, a Hermitian Hessian component of an
ordinary superjet at an interior point is nonnegative in the Loewner order.
-/
theorem Superjet.hessian_nonneg_of_convexOn_closedBall
    {g : Point n -> Real} {x x0 : Point n} {r : Real} {J : Jet n}
    (hconv : ConvexOn Real (Metric.closedBall x0 r) g)
    (hx : x ∈ Metric.ball x0 r)
    (hJ : J ∈ Superjet Set.univ g x)
    (hHerm : J.hessian.IsHermitian) :
    0 <= J.hessian := by
  rw [Matrix.nonneg_iff_posSemidef]
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    (fun v => by
      simpa [dotProduct_comm v (Matrix.mulVec J.hessian v)] using
        Superjet.quadraticForm_nonneg_of_convexOn_closedBall hconv hx hJ v)

/--
For a convex function, the Hessian component of an ordinary superjet has
nonnegative quadratic form in every direction.

In quantified mathematical form, if `g : R^n -> R` is convex, if `(p, X)`
belongs to `J^{2,+}_{R^n} g(x)`, and if `v ∈ R^n`, then
`0 ≤ ⟪Xv, v⟫`.
-/
theorem Superjet.quadraticForm_nonneg_of_convexOn
    {g : Point n -> Real} {x : Point n} {J : Jet n}
    (hconv : ConvexOn Real Set.univ g) (hJ : J ∈ Superjet Set.univ g x)
    (v : Point n) :
    0 <= dotProduct (Matrix.mulVec J.hessian v) v := by
  exact Superjet.quadraticForm_nonneg_of_convexOn_closedBall
    (hconv.subset (Set.subset_univ _) (convex_closedBall x 1)) (by simp) hJ v

/--
For a convex function, a Hermitian Hessian component of an ordinary superjet is
nonnegative in the Loewner order.
-/
theorem Superjet.hessian_nonneg_of_convexOn
    {g : Point n -> Real} {x : Point n} {J : Jet n}
    (hconv : ConvexOn Real Set.univ g) (hJ : J ∈ Superjet Set.univ g x)
    (hHerm : J.hessian.IsHermitian) :
    0 <= J.hessian := by
  rw [Matrix.nonneg_iff_posSemidef]
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    (fun v => by
      simpa [dotProduct_comm v (Matrix.mulVec J.hessian v)] using
        Superjet.quadraticForm_nonneg_of_convexOn hconv hJ v)

/--
For a convex function, the Hessian component of a closed superjet has
nonnegative quadratic form in every direction.

In quantified mathematical form, if `g : R^n -> R` is convex, if `(p, X)`
belongs to `\overline J^{2,+}_{R^n} g(x)`, and if `v ∈ R^n`, then
`0 ≤ ⟪Xv, v⟫`.
-/
theorem ClosedSuperjet.quadraticForm_nonneg_of_convexOn
    {g : Point n -> Real} {x : Point n} {J : Jet n}
    (hconv : ConvexOn Real Set.univ g) (hJ : J ∈ ClosedSuperjet Set.univ g x)
    (v : Point n) :
    0 <= dotProduct (Matrix.mulVec J.hessian v) v := by
  let S : Set ((Point n × Real) × Jet n) :=
    {z | 0 <= dotProduct (Matrix.mulVec z.2.hessian v) v}
  have hSclosed : IsClosed S := by
    have hconst : Continuous fun _ : ((Point n × Real) × Jet n) => v :=
      continuous_const
    have hH : Continuous fun z : ((Point n × Real) × Jet n) => z.2.hessian :=
      Jet.continuous_hessian.comp continuous_snd
    have hquad : Continuous fun z : ((Point n × Real) × Jet n) =>
        dotProduct (Matrix.mulVec z.2.hessian v) v :=
      (hH.matrix_mulVec hconst).dotProduct hconst
    exact isClosed_Ici.preimage hquad
  have hsubset : SuperjetGraph Set.univ g ⊆ S := by
    intro z hz
    rcases z with ⟨⟨y, r⟩, K⟩
    rcases hz with ⟨_hy, _hr, hK⟩
    exact Superjet.quadraticForm_nonneg_of_convexOn hconv hK v
  exact (closure_minimal hsubset hSclosed) hJ

/--
For a convex function, a Hermitian Hessian component of a closed superjet is
nonnegative in the Loewner order.
-/
theorem ClosedSuperjet.hessian_nonneg_of_convexOn
    {g : Point n -> Real} {x : Point n} {J : Jet n}
    (hconv : ConvexOn Real Set.univ g) (hJ : J ∈ ClosedSuperjet Set.univ g x)
    (hHerm : J.hessian.IsHermitian) :
    0 <= J.hessian := by
  rw [Matrix.nonneg_iff_posSemidef]
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
    (fun v => by
      simpa [dotProduct_comm v (Matrix.mulVec J.hessian v)] using
        ClosedSuperjet.quadraticForm_nonneg_of_convexOn hconv hJ v)

end ViscositySolns
