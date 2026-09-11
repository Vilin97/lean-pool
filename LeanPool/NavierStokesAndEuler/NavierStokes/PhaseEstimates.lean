/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ChartScales
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.TangentProjection
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhaseCalculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.ViscousPropagator
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic
import LeanPool.NavierStokesAndEuler.NavierStokes.TangentODE
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Quantitative estimates for the actual pulse normal

The rounded frequency is used consistently throughout the actual phase.  The
estimates below start from representative data and local base derivative bounds,
rather than assuming that the normal is close to its reference value.
-/

section

/-!
# The actual moving tangent frame

The ambient coordinates are radial, angular, axial.  The two tangent coordinates
are taken in `e_r - ρ K, N`, where `K,N` is an orthonormal frame of the last two
coordinates.  Normal motion, rotation, viscosity and projected forcing are all
retained in the exact equation.
-/

section

/-!
# The actual growing mode stays in a narrow cone

The invariant region is proved using a quadratic boundary function, without
dividing by the growing coordinate or assuming its positivity along the solution.
-/

@[expose] public section

namespace NavierStokes.GrowingMode

open Set Filter
open scoped Topology

/-- State: an abbreviation for `EuclideanSpace ℝ (Fin 2)`. -/
abbrev State := EuclideanSpace ℝ (Fin 2)

/-- The actual two-mode coefficient, including four independent error entries. -/
noncomputable def modalOperator (lam damping e11 e12 e21 e22 : ℝ) : State →L[ℝ] State :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => !₂[(lam - damping + e11) * z 0 + e12 * z 1,
      e21 * z 0 + (-lam - damping + e22) * z 1]
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp <;> ring
    map_smul' := by
      intro c x
      ext i
      fin_cases i <;> simp <;> ring }

@[simp] theorem modalOperator_zero (lam damping e11 e12 e21 e22 : ℝ) (z : State) :
    modalOperator lam damping e11 e12 e21 e22 z 0 =
      (lam - damping + e11) * z 0 + e12 * z 1 := rfl

@[simp] theorem modalOperator_one (lam damping e11 e12 e21 e22 : ℝ) (z : State) :
    modalOperator lam damping e11 e12 e21 e22 z 1 =
      e21 * z 0 + (-lam - damping + e22) * z 1 := rfl

/-- A nonzero solution of a continuous homogeneous linear equation cannot hit zero.
This uses backwards uniqueness, not a positivity assumption on any coordinate. -/
theorem linear_solution_ne_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → H →L[ℝ] H)
    (hA : ContinuousOn A (Icc a b)) {z : ℝ → H}
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (A t (z t)) t) (hinit : z a ≠ 0) :
    ∀ t ∈ Icc a b, z t ≠ 0 := by
  obtain ⟨L, hL⟩ := TangentODE.linear_uniform_lipschitz hab A (fun _ => (0 : H)) hA
  intro t ht hzt
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have huniq : EqOn z (fun _ => (0 : H)) (Icc a t) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := fun s x => A s x) (s := fun _ => Set.univ) (K := L)
    · intro s hs
      simpa only [add_zero] using (hL s (hsub (Ioc_subset_Icc_self hs))).lipschitzOnWith
    · exact fun s hs => (hz s (hsub hs)).continuousAt.continuousWithinAt
    · exact fun s hs => (hz s (hsub (Ioc_subset_Icc_self hs))).hasDerivWithinAt
    · exact fun _ _ => Set.mem_univ _
    · exact continuousOn_const
    · intro s _
      simpa only [map_zero] using (hasDerivAt_const s (0 : H)).hasDerivWithinAt
    · exact fun _ _ => Set.mem_univ _
    · exact hzt
  exact hinit (huniq ⟨le_rfl, ht.1⟩)

/-- The inward algebra at the upper edge of the cone. -/
theorem upper_edge_factor_negative
    {lam lamMin eps r e11 e12 e21 e22 : ℝ}
    (hr : 0 < r) (hlam : lamMin ≤ lam)
    (he11 : |e11| ≤ eps) (he12 : |e12| ≤ eps)
    (he21 : |e21| ≤ eps) (he22 : |e22| ≤ eps)
    (hgap : eps * (1 + r) ^ 2 < 2 * lamMin * r) :
    e21 + r * (e22 - e11) - r ^ 2 * e12 - 2 * lam * r < 0 := by
  have hlin : r * (e22 - e11) ≤ r * (2 * eps) :=
    mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp he11).1, (abs_le.mp he22).2]) hr.le
  have hquad : -(r ^ 2 * e12) ≤ r ^ 2 * eps := by
    have h := mul_le_mul_of_nonneg_left (abs_le.mp he12).1 (sq_nonneg r)
    nlinarith
  have hrate : lamMin * r ≤ lam * r := mul_le_mul_of_nonneg_right hlam hr.le
  nlinarith [(abs_le.mp he21).2]

/-- The inward algebra at the lower edge follows by reversing the off-diagonal signs. -/
theorem lower_edge_factor_negative
    {lam lamMin eps r e11 e12 e21 e22 : ℝ}
    (hr : 0 < r) (hlam : lamMin ≤ lam)
    (he11 : |e11| ≤ eps) (he12 : |e12| ≤ eps)
    (he21 : |e21| ≤ eps) (he22 : |e22| ≤ eps)
    (hgap : eps * (1 + r) ^ 2 < 2 * lamMin * r) :
    -e21 + r * (e22 - e11) + r ^ 2 * e12 - 2 * lam * r < 0 := by
  have h := upper_edge_factor_negative (e12 := -e12) (e21 := -e21)
    hr hlam he11 (by simpa only [abs_neg] using he12)
    (by simpa only [abs_neg] using he21) he22 hgap
  nlinarith

/-- The quadratic cone boundary has strictly negative derivative at every
nonzero boundary point. Scalar damping cancels from this computation. -/
theorem cone_boundary_derivative_negative
    {p q lam damping lamMin eps r e11 e12 e21 e22 : ℝ}
    (hr : 0 < r) (hp : p ≠ 0) (hboundary : q ^ 2 = r ^ 2 * p ^ 2)
    (hlam : lamMin ≤ lam)
    (he11 : |e11| ≤ eps) (he12 : |e12| ≤ eps)
    (he21 : |e21| ≤ eps) (he22 : |e22| ≤ eps)
    (hgap : eps * (1 + r) ^ 2 < 2 * lamMin * r) :
    2 * q * (e21 * p + (-lam - damping + e22) * q) -
      r ^ 2 * (2 * p * ((lam - damping + e11) * p + e12 * q)) < 0 := by
  have hsq : q ^ 2 = (r * p) ^ 2 := by nlinarith [hboundary]
  have hpos : 0 < 2 * r * p ^ 2 := mul_pos (by linarith) (sq_pos_of_ne_zero hp)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hq | hq
  · rw [hq]
    have h := mul_neg_of_pos_of_neg hpos
      (upper_edge_factor_negative hr hlam he11 he12 he21 he22 hgap)
    nlinarith [h]
  · rw [hq]
    have h := mul_neg_of_pos_of_neg hpos
      (lower_edge_factor_negative hr hlam he11 he12 he21 he22 hgap)
    nlinarith [h]

theorem hasDerivAt_coordinate {z : ℝ → State} {z' : State} {t : ℝ}
    (hz : HasDerivAt z z' t) (i : Fin 2) :
    HasDerivAt (fun s => z s i) (z' i) t := by
  exact (PiLp.proj 2 (fun _ : Fin 2 => ℝ) i).hasFDerivAt.comp_hasDerivAt t hz

/-- The actual homogeneous solution stays in the growing cone, and the growing
coordinate is strictly positive. Positivity and nonvanishing are conclusions. -/
theorem positive_invariant_cone
    {a b r eps lamMin : ℝ} (hab : a ≤ b) (hr : 0 < r)
    (hgap : eps * (1 + r) ^ 2 < 2 * lamMin * r)
    (lam damping e11 e12 e21 e22 : ℝ → ℝ) {z : ℝ → State}
    (hA : ContinuousOn (fun t =>
      modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t)) (Icc a b))
    (hode : ∀ t ∈ Icc a b, HasDerivAt z
      (modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t) (z t)) t)
    (hlam : ∀ t ∈ Icc a b, lamMin ≤ lam t)
    (herr : ∀ t ∈ Icc a b,
      |e11 t| ≤ eps ∧ |e12 t| ≤ eps ∧ |e21 t| ≤ eps ∧ |e22 t| ≤ eps)
    (hplus : 0 < z a 0) (hminus : z a 1 = 0) :
    ∀ t ∈ Icc a b, 0 < z t 0 ∧ |z t 1| ≤ r * z t 0 := by
  have hinit : z a ≠ 0 := by
    intro h
    have : z a 0 = 0 := by simp only [h, PiLp.zero_apply]
    linarith
  have hnonzero := linear_solution_ne_zero hab _ hA hode hinit
  have hp (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => z s 0)
      ((lam t - damping t + e11 t) * z t 0 + e12 t * z t 1) t :=
    hasDerivAt_coordinate (hode t ht) 0
  have hq (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => z s 1)
      (e21 t * z t 0 + (-lam t - damping t + e22 t) * z t 1) t :=
    hasDerivAt_coordinate (hode t ht) 1
  let barrier : ℝ → ℝ := fun t => (z t 1) ^ 2 - r ^ 2 * (z t 0) ^ 2
  let barrier' : ℝ → ℝ := fun t =>
    2 * z t 1 * (e21 t * z t 0 + (-lam t - damping t + e22 t) * z t 1) -
      r ^ 2 * (2 * z t 0 * ((lam t - damping t + e11 t) * z t 0 + e12 t * z t 1))
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt barrier (barrier' t) t := by
    convert! ((hq t ht).pow 2).sub (((hp t ht).pow 2).const_mul (r ^ 2)) using 1
    simp [barrier']
  have hbarrier : ∀ t ∈ Icc a b, barrier t ≤ 0 := by
    apply image_le_of_deriv_right_lt_deriv_boundary'
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (B := fun _ => (0 : ℝ)) (B' := fun _ => (0 : ℝ))
    · dsimp [barrier]
      rw [hminus]
      nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg (z a 0))]
    · exact continuousOn_const
    · exact fun t _ => (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt
    · intro t ht heq
      have htc := Ico_subset_Icc_self ht
      have hsq : (z t 1) ^ 2 = r ^ 2 * (z t 0) ^ 2 := by
        dsimp [barrier] at heq
        linarith
      have hpn : z t 0 ≠ 0 := by
        intro hpzero
        have hqzero : z t 1 = 0 := by
          apply sq_eq_zero_iff.mp
          simpa only [hpzero, zero_pow (by decide : 2 ≠ 0), mul_zero] using hsq
        apply hnonzero t htc
        ext i
        fin_cases i <;> simp [hpzero, hqzero]
      rcases herr t htc with ⟨h11, h12, h21, h22⟩
      exact cone_boundary_derivative_negative hr hpn hsq (hlam t htc)
        h11 h12 h21 h22 hgap
  have hpne : ∀ t ∈ Icc a b, z t 0 ≠ 0 := by
    intro t ht hpzero
    have hqsq : (z t 1) ^ 2 ≤ 0 := by simpa [barrier, hpzero] using hbarrier t ht
    have hqzero : z t 1 = 0 := sq_eq_zero_iff.mp (le_antisymm hqsq (sq_nonneg _))
    apply hnonzero t ht
    ext i
    fin_cases i <;> simp [hpzero, hqzero]
  have hpcont : ContinuousOn (fun t => z t 0) (Icc a b) :=
    fun t ht => (hp t ht).continuousAt.continuousWithinAt
  intro t ht
  have hppos : 0 < z t 0 := by
    by_contra! hnpos
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    obtain ⟨s, hs, hszero⟩ :=
      intermediate_value_Icc' ht.1 (hpcont.mono hsub) ⟨hnpos, hplus.le⟩
    exact hpne s (hsub hs) hszero
  refine ⟨hppos, abs_le_of_sq_le_sq ?_ (mul_nonneg hr.le hppos.le)⟩
  have hb := hbarrier t ht
  dsimp [barrier] at hb
  nlinarith

/-- A fixed constant for the manuscript's `O(1/S)` cone width. The added one
allows the same statement when the perturbation bound is zero. -/
noncomputable def coneConstant (lamMin C : ℝ) : ℝ := 4 * (C + 1) / lamMin

/-- An explicit sufficient meaning of "sufficiently large S". -/
theorem scaled_cone_conditions {lamMin C S : ℝ}
    (hlamMin : 0 < lamMin) (hC : 0 ≤ C) (hS : 0 < S)
    (hlarge : 2 * coneConstant lamMin C ≤ S) :
    0 < coneConstant lamMin C / S ∧
      coneConstant lamMin C / S ≤ 1 / 2 ∧
      (C / S) * (1 + coneConstant lamMin C / S) ^ 2 <
        2 * lamMin * (coneConstant lamMin C / S) := by
  have hK : 0 < coneConstant lamMin C :=
    div_pos (mul_pos (by norm_num) (by linarith)) hlamMin
  have hr : 0 < coneConstant lamMin C / S := div_pos hK hS
  have hrhalf : coneConstant lamMin C / S ≤ 1 / 2 := by
    apply (div_le_iff₀ hS).mpr
    linarith
  have hquadratic : (1 + coneConstant lamMin C / S) ^ 2 ≤ 4 := by
    nlinarith
  have hbound : (C / S) * (1 + coneConstant lamMin C / S) ^ 2 ≤ 4 * (C / S) := by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hquadratic (div_nonneg hC hS.le)
  have hscale : lamMin * (coneConstant lamMin C / S) = 4 * (C + 1) / S := by
    unfold coneConstant
    field_simp
  have hstrict : 4 * (C / S) < lamMin * (coneConstant lamMin C / S) := by
    rw [hscale]
    have h := (div_lt_div_iff_of_pos_right hS).mpr (show 4 * C < 4 * (C + 1) by linarith)
    convert! h using 1
    ring
  refine ⟨hr, hrhalf, ?_⟩
  nlinarith [mul_pos hlamMin hr]

/-- The fixed-width result in the exact `K/S` form used in (28). -/
theorem scaled_positive_invariant_cone
    {a b S C lamMin : ℝ} (hab : a ≤ b)
    (hlamMin : 0 < lamMin) (hC : 0 ≤ C) (hS : 0 < S)
    (hlarge : 2 * coneConstant lamMin C ≤ S)
    (lam damping e11 e12 e21 e22 : ℝ → ℝ) {z : ℝ → State}
    (hA : ContinuousOn (fun t =>
      modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t)) (Icc a b))
    (hode : ∀ t ∈ Icc a b, HasDerivAt z
      (modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t) (z t)) t)
    (hlam : ∀ t ∈ Icc a b, lamMin ≤ lam t)
    (herr : ∀ t ∈ Icc a b,
      |e11 t| ≤ C / S ∧ |e12 t| ≤ C / S ∧ |e21 t| ≤ C / S ∧ |e22 t| ≤ C / S)
    (hplus : 0 < z a 0) (hminus : z a 1 = 0) :
    ∀ t ∈ Icc a b, 0 < z t 0 ∧ |z t 1| ≤ (coneConstant lamMin C / S) * z t 0 := by
  obtain ⟨hr, _, hgap⟩ := scaled_cone_conditions hlamMin hC hS hlarge
  exact positive_invariant_cone hab hr hgap lam damping e11 e12 e21 e22
    hA hode hlam herr hplus hminus

/-- Derivative of the scalar integrating factor used for both sides of the comparison. -/
theorem hasDerivAt_weighted_scalar
    {p P : ℝ → ℝ} {p' rate μ a t : ℝ}
    (hp : HasDerivAt p p' t) (hP : HasDerivAt P (rate * P t) t) (hPne : P t ≠ 0) :
    HasDerivAt (fun s => Real.exp (μ * (s - a)) * p s / P s)
      (Real.exp (μ * (t - a)) / P t * (p' + (μ - rate) * p t)) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (μ * (s - a)))
      (Real.exp (μ * (t - a)) * μ) t := by
    simpa only [id, mul_one] using (((hasDerivAt_id t).sub_const a).const_mul μ).exp
  convert! (he.fun_mul hp).fun_div hP hPne using 1
  field_simp; ring

/-- A scalar positive envelope comparison from an actual relative derivative bound.
No lower bound on the unknown scalar solution is assumed. -/
theorem scalar_envelope_comparison
    {a b μ : ℝ} {p p' P rate : ℝ → ℝ} (hab : a ≤ b)
    (hPpos : ∀ t ∈ Icc a b, 0 < P t)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (rate t * P t) t)
    (hp : ∀ t ∈ Icc a b, HasDerivAt p (p' t) t)
    (herror : ∀ t ∈ Icc a b, |p' t - rate t * p t| ≤ μ * p t) :
    ∀ t ∈ Icc a b,
      Real.exp (-μ * (t - a)) * (p a / P a) * P t ≤ p t ∧
      p t ≤ Real.exp (μ * (t - a)) * (p a / P a) * P t := by
  let W : ℝ → ℝ → ℝ := fun m s => Real.exp (m * (s - a)) * p s / P s
  let W' : ℝ → ℝ → ℝ := fun m s =>
    Real.exp (m * (s - a)) / P s * (p' s + (m - rate s) * p s)
  have hd (m t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (W m) (W' m t) t :=
    hasDerivAt_weighted_scalar (hp t ht) (hP t ht) (ne_of_gt (hPpos t ht))
  have hmono : MonotoneOn (W μ) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (fun t ht => (hd μ t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd μ t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    dsimp [W']
    apply mul_nonneg (div_nonneg (Real.exp_pos _).le (hPpos t (interior_subset ht)).le)
    linarith [(abs_le.mp (herror t (interior_subset ht))).1]
  have hanti : AntitoneOn (W (-μ)) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
      (fun t ht => (hd (-μ) t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd (-μ) t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    dsimp [W']
    apply mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (Real.exp_pos _).le (hPpos t (interior_subset ht)).le)
    linarith [(abs_le.mp (herror t (interior_subset ht))).2]
  intro t ht
  have hlo := hmono ⟨le_rfl, hab⟩ ht ht.1
  have hhi := hanti ⟨le_rfl, hab⟩ ht ht.1
  dsimp [W] at hlo hhi
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hlo hhi
  constructor
  · have h := (le_div_iff₀ (hPpos t ht)).mp hlo
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-μ * (t - a))).le
    have he : Real.exp (-μ * (t - a)) * Real.exp (μ * (t - a)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      Real.exp (-μ * (t - a)) * (p a / P a) * P t =
          Real.exp (-μ * (t - a)) * (p a / P a * P t) := by ring
      _ ≤ Real.exp (-μ * (t - a)) * (Real.exp (μ * (t - a)) * p t) := hmul
      _ = p t := by rw [← mul_assoc, he, one_mul]
  · have h := (div_le_iff₀ (hPpos t ht)).mp hhi
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (μ * (t - a))).le
    have he : Real.exp (μ * (t - a)) * Real.exp (-μ * (t - a)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      p t = Real.exp (μ * (t - a)) * (Real.exp (-μ * (t - a)) * p t) := by
        rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (μ * (t - a)) * (p a / P a * P t) := hmul
      _ = Real.exp (μ * (t - a)) * (p a / P a) * P t := by ring

/-- Inside the proved cone, the growing coordinate has a multiplicative
derivative error. This is the only estimate used for its lower envelope. -/
theorem relative_error_of_cone
    {p q lam damping referenceDamping e11 e12 eps δ r : ℝ}
    (hp : 0 < p) (heps : 0 ≤ eps) (hcone : |q| ≤ r * p)
    (h11 : |e11| ≤ eps) (h12 : |e12| ≤ eps)
    (hd : |damping - referenceDamping| ≤ δ) :
    |(lam - damping + e11) * p + e12 * q - (lam - referenceDamping) * p| ≤
      (δ + eps * (1 + r)) * p := by
  have hd' : |referenceDamping - damping| ≤ δ := by
    simpa only [abs_sub_comm] using hd
  have hfirst : |(referenceDamping - damping + e11) * p| ≤ (δ + eps) * p := by
    rw [abs_mul, abs_of_pos hp]
    apply mul_le_mul_of_nonneg_right _ hp.le
    exact (abs_add_le _ _).trans (add_le_add hd' h11)
  have hsecond : |e12 * q| ≤ eps * (r * p) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right h12 (abs_nonneg q)).trans
      (mul_le_mul_of_nonneg_left hcone heps)
  calc
    |(lam - damping + e11) * p + e12 * q - (lam - referenceDamping) * p| =
        |(referenceDamping - damping + e11) * p + e12 * q| := by
      congr 1
      ring
    _ ≤ |(referenceDamping - damping + e11) * p| + |e12 * q| := abs_add_le _ _
    _ ≤ (δ + eps) * p + eps * (r * p) := add_le_add hfirst hsecond
    _ = (δ + eps * (1 + r)) * p := by ring

/-- Positivity, the `K/S` cone, and two-sided bounds by a supplied reference
envelope on a slot of length at most `L*S`. None of these conclusions is assumed.

For the manuscript normalization `z a 0 = P a`, the ratio of initial values is one.
The comparison constants are `exp(±(D+2*C)*L)`, independent of the scale `S`.
-/
theorem scaled_growing_mode_bounds
    {a b S C D L lamMin : ℝ} (hab : a ≤ b)
    (hlamMin : 0 < lamMin) (hC : 0 ≤ C) (hD : 0 ≤ D) (hS : 0 < S)
    (hlarge : 2 * coneConstant lamMin C ≤ S) (hslot : b - a ≤ L * S)
    (lam damping referenceDamping e11 e12 e21 e22 P : ℝ → ℝ) {z : ℝ → State}
    (hA : ContinuousOn (fun t =>
      modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t)) (Icc a b))
    (hode : ∀ t ∈ Icc a b, HasDerivAt z
      (modalOperator (lam t) (damping t) (e11 t) (e12 t) (e21 t) (e22 t) (z t)) t)
    (hlam : ∀ t ∈ Icc a b, lamMin ≤ lam t)
    (herr : ∀ t ∈ Icc a b,
      |e11 t| ≤ C / S ∧ |e12 t| ≤ C / S ∧ |e21 t| ≤ C / S ∧ |e22 t| ≤ C / S)
    (hdamping : ∀ t ∈ Icc a b, |damping t - referenceDamping t| ≤ D / S)
    (hPpos : ∀ t ∈ Icc a b, 0 < P t)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P ((lam t - referenceDamping t) * P t) t)
    (hplus : 0 < z a 0) (hminus : z a 1 = 0) :
    ∀ t ∈ Icc a b,
      0 < z t 0 ∧ |z t 1| ≤ (coneConstant lamMin C / S) * z t 0 ∧
      Real.exp (-(D + 2 * C) * L) * (z a 0 / P a) * P t ≤ z t 0 ∧
      z t 0 ≤ Real.exp ((D + 2 * C) * L) * (z a 0 / P a) * P t := by
  have hcone := scaled_positive_invariant_cone hab hlamMin hC hS hlarge
    lam damping e11 e12 e21 e22 hA hode hlam herr hplus hminus
  have hrhalf := (scaled_cone_conditions hlamMin hC hS hlarge).2.1
  have hmu : D / S + (C / S) * (1 + coneConstant lamMin C / S) ≤ (D + 2 * C) / S := by
    have hmul : (C / S) * (coneConstant lamMin C / S) ≤ C / S := by
      have h := mul_le_mul_of_nonneg_left (show coneConstant lamMin C / S ≤ 1 by linarith)
        (div_nonneg hC hS.le)
      simpa only [mul_one] using h
    calc
      D / S + (C / S) * (1 + coneConstant lamMin C / S) ≤ D / S + 2 * (C / S) := by
        nlinarith
      _ = (D + 2 * C) / S := by ring
  let p' : ℝ → ℝ := fun t => (lam t - damping t + e11 t) * z t 0 + e12 t * z t 1
  have hp (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => z s 0) (p' t) t :=
    hasDerivAt_coordinate (hode t ht) 0
  have he (t : ℝ) (ht : t ∈ Icc a b) :
      |p' t - (lam t - referenceDamping t) * z t 0| ≤ ((D + 2 * C) / S) * z t 0 := by
    rcases herr t ht with ⟨h11, h12, _, _⟩
    have h := relative_error_of_cone (lam := lam t) (hcone t ht).1 (div_nonneg hC hS.le)
      (hcone t ht).2 h11 h12 (hdamping t ht)
    exact h.trans (mul_le_mul_of_nonneg_right hmu (hcone t ht).1.le)
  have hcomparison := scalar_envelope_comparison hab hPpos hP hp he
  have hmu0 : 0 ≤ (D + 2 * C) / S := div_nonneg (by linarith) hS.le
  intro t ht
  have hexponent : ((D + 2 * C) / S) * (t - a) ≤ (D + 2 * C) * L := by
    calc
      ((D + 2 * C) / S) * (t - a) ≤ ((D + 2 * C) / S) * (L * S) :=
        mul_le_mul_of_nonneg_left ((sub_le_sub_right ht.2 a).trans hslot) hmu0
      _ = (D + 2 * C) * L := by
        field_simp
  have hlo : Real.exp (-(D + 2 * C) * L) ≤
      Real.exp (-((D + 2 * C) / S) * (t - a)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hhi : Real.exp (((D + 2 * C) / S) * (t - a)) ≤
      Real.exp ((D + 2 * C) * L) := Real.exp_le_exp.mpr hexponent
  have hratio : 0 ≤ z a 0 / P a := div_nonneg hplus.le (hPpos a ⟨le_rfl, hab⟩).le
  refine ⟨(hcone t ht).1, (hcone t ht).2, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo hratio)
      (hPpos t ht).le).trans (hcomparison t ht).1
  · exact (hcomparison t ht).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhi hratio) (hPpos t ht).le)

/-- Returning from the modal cone to `x=p+q`, `y=h*(p-q)` gives both the
positive radial amplitude and the ratio error used in equation (28). -/
theorem original_coordinate_bounds {p q h r : ℝ}
    (hp : 0 < p) (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hcone : |q| ≤ r * p) :
    p / 2 ≤ p + q ∧ p + q ≤ 3 * p / 2 ∧
      |h * (p - q) / (p + q) - h| ≤ 4 * |h| * r := by
  have hq := abs_le.mp hcone
  have hrp : r * p ≤ p / 2 := by nlinarith
  have hxlower : p / 2 ≤ p + q := by linarith
  have hxupper : p + q ≤ 3 * p / 2 := by linarith
  have hxpos : 0 < p + q := by linarith
  refine ⟨hxlower, hxupper, ?_⟩
  have heq : h * (p - q) / (p + q) - h = (-2 * h * q) / (p + q) := by
    field_simp; ring
  rw [heq, abs_div, abs_of_pos hxpos]
  apply (div_le_iff₀ hxpos).mpr
  have hnum : 2 * |h| * |q| ≤ 2 * |h| * (r * p) :=
    mul_le_mul_of_nonneg_left hcone (mul_nonneg (by norm_num) (abs_nonneg h))
  have hden : 4 * |h| * r * (p / 2) ≤ 4 * |h| * r * (p + q) :=
    mul_le_mul_of_nonneg_left hxlower (by positivity)
  simp only [abs_mul, abs_neg]
  rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  nlinarith

end NavierStokes.GrowingMode

end

end

@[expose] public section

namespace NavierStokes.MovingFrameODE

open scoped InnerProductSpace ContDiff

/-- Plane: an abbreviation for `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-- Space: an abbreviation for `EuclideanSpace ℝ (Fin 3)`. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)
/-- Frame: an abbreviation for `OrthonormalBasis (Fin 2) ℝ Plane`. -/
abbrev Frame := OrthonormalBasis (Fin 2) ℝ Plane

/-- Pack, given by `!₂[r, w 0, w 1]`. -/
noncomputable def pack (r : ℝ) (w : Plane) : Space := !₂[r, w 0, w 1]
/-- Tail, given by `!₂[w 1, w 2]`. -/
noncomputable def tail (w : Space) : Plane := !₂[w 1, w 2]
/-- Unit theta, given by `!₂[1, 0]`. -/
noncomputable def unitTheta : Plane := !₂[1, 0]

@[simp] theorem pack_zero (r : ℝ) (w : Plane) : pack r w 0 = r := rfl
@[simp] theorem pack_one (r : ℝ) (w : Plane) : pack r w 1 = w 0 := rfl
@[simp] theorem pack_two (r : ℝ) (w : Plane) : pack r w 2 = w 1 := rfl
@[simp] theorem tail_pack (r : ℝ) (w : Plane) : tail (pack r w) = w := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem tail_add (u v : Space) : tail (u + v) = tail u + tail v := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem tail_sub (u v : Space) : tail (u - v) = tail u - tail v := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem tail_neg (u : Space) : tail (-u) = -tail u := by
  ext i
  fin_cases i <;> rfl
@[simp] theorem tail_smul (c : ℝ) (u : Space) : tail (c • u) = c • tail u := by
  ext i
  fin_cases i <;> rfl

theorem inner_pack (a b : ℝ) (u v : Plane) :
    ⟪pack a u, pack b v⟫_ℝ = a * b + ⟪u, v⟫_ℝ := by
  simp [pack, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

theorem inner_pack_left (a : ℝ) (u : Plane) (v : Space) :
    ⟪pack a u, v⟫_ℝ = a * v 0 + ⟪u, tail v⟫_ℝ := by
  simp [pack, tail, PiLp.inner_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  ring

@[simp] theorem inner_unitTheta (w : Plane) : ⟪w, unitTheta⟫_ℝ = w 0 := by
  simp [unitTheta, PiLp.inner_apply, Fin.sum_univ_two]

@[simp] theorem frame_inner (B : Frame) (i j : Fin 2) :
    ⟪B i, B j⟫_ℝ = if i = j then 1 else 0 := (orthonormal_iff_ite.mp B.orthonormal) i j

theorem frame_inner00 (B : Frame) : ⟪B 0, B 0⟫_ℝ = 1 := by
  simp only [frame_inner, ite_true]
theorem frame_inner11 (B : Frame) : ⟪B 1, B 1⟫_ℝ = 1 := by
  simp only [frame_inner, ite_true]
theorem frame_inner01 (B : Frame) : ⟪B 0, B 1⟫_ℝ = 0 := by
  exact B.inner_eq_zero (by decide)
theorem frame_inner10 (B : Frame) : ⟪B 1, B 0⟫_ℝ = 0 := by
  exact B.inner_eq_zero (by decide)

theorem frame_expand (B : Frame) (w : Plane) :
    ⟪B 0, w⟫_ℝ • B 0 + ⟪B 1, w⟫_ℝ • B 1 = w := by
  simpa only [Fin.sum_univ_two] using B.sum_repr' w

theorem frame_ext (B : Frame) {u v : Space} (hr : u 0 = v 0)
    (hK : ⟪B 0, tail u⟫_ℝ = ⟪B 0, tail v⟫_ℝ)
    (hN : ⟪B 1, tail u⟫_ℝ = ⟪B 1, tail v⟫_ℝ) : u = v := by
  have ht : tail u = tail v := by
    rw [← frame_expand B (tail u), ← frame_expand B (tail v), hK, hN]
  ext i
  fin_cases i
  · exact hr
  · exact congrArg (fun w : Plane => w 0) ht
  · exact congrArg (fun w : Plane => w 1) ht

/-- Normal, given by `pack (β * ρ) (β • B 0)`. -/
noncomputable def normal (β ρ : ℝ) (B : Frame) : Space :=
  pack (β * ρ) (β • B 0)

/-- Tangent, given by `pack x ((-ρ * x) • B 0 + y • B 1)`. -/
noncomputable def tangent (ρ : ℝ) (B : Frame) (x y : ℝ) : Space :=
  pack x ((-ρ * x) • B 0 + y • B 1)

/-- Normal motion, given by `pack (β' * ρ + β * ρ') (β' • B 0 + (β * rot) • B 1)`. -/
noncomputable def normalMotion (β β' ρ ρ' rot : ℝ) (B : Frame) : Space :=
  pack (β' * ρ + β * ρ') (β' • B 0 + (β * rot) • B 1)

/-- Tangent motion, given by `pack x' (-(ρ' * x + ρ * x' + rot * y) • B 0 + (y' - ρ * rot * x) •
B 1)`. -/
noncomputable def tangentMotion (ρ ρ' rot : ℝ) (B : Frame)
    (x y x' y' : ℝ) : Space :=
  pack x' (-(ρ' * x + ρ * x' + rot * y) • B 0 +
    (y' - ρ * rot * x) • B 1)

/-- The exact zeroth-order ambient matrix from the pulse equation. -/
noncomputable def baseAction (F : ℝ) (g : Plane) (t : Space) : Space :=
  pack (-2 * F * (tail t) 0) ((t 0) • ((2 * F) • unitTheta + g))

theorem normal_ne_zero {β ρ : ℝ} (B : Frame) (hβ : β ≠ 0) : normal β ρ B ≠ 0 := by
  intro hz
  have ht := congrArg tail hz
  have hi := congrArg (fun w : Plane => ⟪B 0, w⟫_ℝ) ht
  simp only [normal, tail_pack, show tail (0 : Space) = 0 by ext i; fin_cases i <;> rfl,
    inner_smul_right, frame_inner, ite_true, mul_one, inner_zero_right] at hi
  exact hβ hi

@[simp] theorem normal_tangent (β ρ : ℝ) (B : Frame) (x y : ℝ) :
    ⟪normal β ρ B, tangent ρ B x y⟫_ℝ = 0 := by
  simp only [normal, tangent, inner_pack, real_inner_smul_left, inner_smul_right, inner_add_right,
    frame_inner00, frame_inner01, mul_one, mul_zero, add_zero]
  ring

theorem normal_self (β ρ : ℝ) (B : Frame) :
    ⟪normal β ρ B, normal β ρ B⟫_ℝ = β ^ 2 * (1 + ρ ^ 2) := by
  simp only [normal, inner_pack, real_inner_smul_left, inner_smul_right,
    frame_inner00, mul_one]
  ring

theorem normalMotion_tangent (β β' ρ ρ' rot : ℝ) (B : Frame) (x y : ℝ) :
    ⟪normalMotion β β' ρ ρ' rot B, tangent ρ B x y⟫_ℝ =
      β * (ρ' * x + rot * y) := by
  simp only [normalMotion, tangent, inner_pack, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, frame_inner00, frame_inner01, frame_inner10,
    frame_inner11, mul_one, mul_zero, add_zero, zero_add]
  ring

theorem normal_tangentMotion (β ρ ρ' rot : ℝ) (B : Frame) (x y x' y' : ℝ) :
    ⟪normal β ρ B, tangentMotion ρ ρ' rot B x y x' y'⟫_ℝ =
      -β * (ρ' * x + rot * y) := by
  simp only [normal, tangentMotion, inner_pack, inner_add_right,
    real_inner_smul_left, inner_smul_right, frame_inner00, frame_inner01, mul_one, mul_zero,
        add_zero]
  ring

theorem normal_inner (β ρ : ℝ) (B : Frame) (v : Space) :
    ⟪normal β ρ B, v⟫_ℝ = β * ρ * v 0 + β * ⟪B 0, tail v⟫_ℝ := by
  rw [normal, inner_pack_left, real_inner_smul_left]

theorem normal_baseAction (β ρ F : ℝ) (B : Frame) (g : Plane) (x y : ℝ) :
    ⟪normal β ρ B, baseAction F g (tangent ρ B x y)⟫_ℝ =
      β * ((2 * F * (1 + ρ ^ 2) * (B 0) 0 + ⟪B 0, g⟫_ℝ) * x -
        2 * F * ρ * (B 1) 0 * y) := by
  simp only [normal, baseAction, tangent, inner_pack, inner_add_right,
    real_inner_smul_left, inner_smul_right, inner_unitTheta, tail_pack, pack_zero, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-- Coefficients before subtracting the scalar viscous damping. -/
noncomputable def coeff11 (ρ ρ' gK : ℝ) : ℝ := ρ * (gK - ρ') / (1 + ρ ^ 2)
/-- Coeff12, given by `(2 * F * Nθ - ρ * rot) / (1 + ρ ^ 2)`. -/
noncomputable def coeff12 (F Nθ ρ rot : ℝ) : ℝ := (2 * F * Nθ - ρ * rot) / (1 + ρ ^ 2)
/-- Coeff21, given by `-(2 * F * Nθ + gN) + ρ * rot`. -/
noncomputable def coeff21 (F Nθ gN ρ rot : ℝ) : ℝ := -(2 * F * Nθ + gN) + ρ * rot

/-- Rhs X, given by `(coeff11 ρ ρ' ⟪B 0, g⟫_ℝ - d) * x + coeff12 F ((B 1) 0) ρ rot * y - (f 0 -
ρ * ⟪B 0, tail f⟫_ℝ) / (1 + ρ ^ 2)`. -/
noncomputable def rhsX (F d ρ ρ' rot : ℝ) (B : Frame) (g : Plane)
    (f : Space) (x y : ℝ) : ℝ :=
  (coeff11 ρ ρ' ⟪B 0, g⟫_ℝ - d) * x + coeff12 F ((B 1) 0) ρ rot * y -
    (f 0 - ρ * ⟪B 0, tail f⟫_ℝ) / (1 + ρ ^ 2)

/-- Rhs Y, given by `coeff21 F ((B 1) 0) ⟪B 1, g⟫_ℝ ρ rot * x - d * y - ⟪B 1, tail f⟫_ℝ`. -/
noncomputable def rhsY (F d ρ rot : ℝ) (B : Frame) (g : Plane)
    (f : Space) (x y : ℝ) : ℝ :=
  coeff21 F ((B 1) 0) ⟪B 1, g⟫_ℝ ρ rot * x - d * y - ⟪B 1, tail f⟫_ℝ

theorem projectedRhs_radial {β : ℝ} (hβ : β ≠ 0)
    (β' ρ ρ' rot F d : ℝ) (B : Frame) (g : Plane) (f : Space) (x y : ℝ) :
    TangentProjection.projectedRhs (normal β ρ B) (normalMotion β β' ρ ρ' rot B)
      (tangent ρ B x y) (baseAction F g (tangent ρ B x y)) f d 0 =
        rhsX F d ρ ρ' rot B g f x y := by
  have hden : 1 + ρ ^ 2 ≠ 0 := by positivity
  rw [TangentProjection.projectedRhs, TangentProjection.tangentProj,
    normal_self, normalMotion_tangent, normal_baseAction, normal_inner]
  simp only [normal, tangent, baseAction, rhsX, coeff11, coeff12, pack_zero, tail_pack,
    PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp; ring

theorem projectedRhs_N (β β' ρ ρ' rot F d : ℝ) (B : Frame) (g : Plane)
    (f : Space) (x y : ℝ) :
    ⟪B 1, tail (TangentProjection.projectedRhs (normal β ρ B)
      (normalMotion β β' ρ ρ' rot B) (tangent ρ B x y)
      (baseAction F g (tangent ρ B x y)) f d)⟫_ℝ =
        rhsY F d ρ rot B g f x y - ρ * rot * x := by
  simp only [TangentProjection.projectedRhs, TangentProjection.tangentProj,
    tail_sub, tail_add, tail_neg, tail_smul, normal, tangent, baseAction, tail_pack,
    pack_zero, rhsY, coeff21, inner_sub_right, inner_add_right, inner_neg_right,
    inner_smul_right, inner_unitTheta, frame_inner10,
    frame_inner11, mul_one, mul_zero, add_zero, zero_add, sub_zero]
  ring

/-- Exact moving-frame reduction of the ambient projected equation. -/
theorem projectedRhs_eq_tangentMotion {β : ℝ} (hβ : β ≠ 0)
    (β' ρ ρ' rot F d : ℝ) (B : Frame) (g : Plane) (f : Space) (x y : ℝ) :
    TangentProjection.projectedRhs (normal β ρ B) (normalMotion β β' ρ ρ' rot B)
      (tangent ρ B x y) (baseAction F g (tangent ρ B x y)) f d =
    tangentMotion ρ ρ' rot B x y
      (rhsX F d ρ ρ' rot B g f x y) (rhsY F d ρ rot B g f x y) := by
  apply frame_ext B
  · exact projectedRhs_radial hβ β' ρ ρ' rot F d B g f x y
  · have hn := TangentProjection.normal_projectedRhs_of_tangent
      (normal_ne_zero B hβ) (normalMotion β β' ρ ρ' rot B) (tangent ρ B x y)
      (baseAction F g (tangent ρ B x y)) f d (normal_tangent β ρ B x y)
    rw [normalMotion_tangent] at hn
    have hm := normal_tangentMotion β ρ ρ' rot B x y
      (rhsX F d ρ ρ' rot B g f x y) (rhsY F d ρ rot B g f x y)
    have heq : ⟪normal β ρ B,
        TangentProjection.projectedRhs (normal β ρ B) (normalMotion β β' ρ ρ' rot B)
          (tangent ρ B x y) (baseAction F g (tangent ρ B x y)) f d⟫_ℝ =
      ⟪normal β ρ B, tangentMotion ρ ρ' rot B x y
        (rhsX F d ρ ρ' rot B g f x y) (rhsY F d ρ rot B g f x y)⟫_ℝ := by
      rw [hn, hm]
      ring
    rw [normal_inner, normal_inner] at heq
    rw [projectedRhs_radial hβ] at heq
    change β * ρ * _ + β * _ = β * ρ * rhsX F d ρ ρ' rot B g f x y + β * _ at heq
    exact (mul_left_cancel₀ hβ) (by linarith [heq])
  · rw [projectedRhs_N]
    simp only [tangentMotion, tail_pack, inner_add_right, inner_smul_right,
      frame_inner10, frame_inner11, mul_zero, mul_one, zero_add]

/-- The moving-coordinate equation has exactly two scalar equations. -/
theorem tangentMotion_eq_projectedRhs_iff {β : ℝ} (hβ : β ≠ 0)
    (β' ρ ρ' rot F d : ℝ) (B : Frame) (g : Plane) (f : Space) (x y x' y' : ℝ) :
    tangentMotion ρ ρ' rot B x y x' y' =
      TangentProjection.projectedRhs (normal β ρ B) (normalMotion β β' ρ ρ' rot B)
        (tangent ρ B x y) (baseAction F g (tangent ρ B x y)) f d ↔
    x' = rhsX F d ρ ρ' rot B g f x y ∧ y' = rhsY F d ρ rot B g f x y := by
  rw [projectedRhs_eq_tangentMotion hβ]
  constructor
  · intro h
    constructor
    · exact congrArg (fun v : Space => v 0) h
    · have hn := congrArg (fun v : Space => ⟪B 1, tail v⟫_ℝ) h
      simp only [tangentMotion, tail_pack, inner_add_right, inner_smul_right,
      frame_inner10, frame_inner11, mul_zero, mul_one, zero_add] at hn
      linarith
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Pack continuous linear map, constructed using `LinearMap.toContinuousLinearMap`. -/
noncomputable def packCLM : (ℝ × Plane) →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap {
    toFun := fun p => pack p.1 p.2
    map_add' := by
      intro u v
      ext i
      fin_cases i <;> simp [pack]
    map_smul' := by
      intro c u
      ext i
      fin_cases i <;> simp [pack] }

/-- Tail continuous linear map, given by `LinearMap.toContinuousLinearMap { toFun := tail
map_add' := tail_add map_smul' := tail_smul }`. -/
noncomputable def tailCLM : Space →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := tail
    map_add' := tail_add
    map_smul' := tail_smul }

theorem hasDerivAt_pack {r : ℝ → ℝ} {w : ℝ → Plane} {r' v : ℝ} {w' : Plane}
    (hr : HasDerivAt r r' v) (hw : HasDerivAt w w' v) :
    HasDerivAt (fun s => pack (r s) (w s)) (pack r' w') v :=
  packCLM.hasFDerivAt.comp_hasDerivAt v (hr.prodMk hw)

/-- Differentiation of the actual normal.  The frame derivative is measured in
the same moving orthonormal basis. -/
theorem hasDerivAt_normal {β ρ : ℝ → ℝ} {B : ℝ → Frame}
    {v β' ρ' rot : ℝ} (hβ : HasDerivAt β β' v) (hρ : HasDerivAt ρ ρ' v)
    (hK : HasDerivAt (fun s => B s 0) (rot • B v 1) v) :
    HasDerivAt (fun s => normal (β s) (ρ s) (B s))
      (normalMotion (β v) β' (ρ v) ρ' rot (B v)) v := by
  convert! hasDerivAt_pack (hβ.mul hρ) (hβ.smul hK) using 1
  ext i
  fin_cases i <;> simp [normalMotion, pack] <;> ring

/-- Differentiation of the actual tangent parametrization. -/
theorem hasDerivAt_tangent {ρ x y : ℝ → ℝ} {B : ℝ → Frame}
    {v ρ' rot x' y' : ℝ} (hρ : HasDerivAt ρ ρ' v)
    (hx : HasDerivAt x x' v) (hy : HasDerivAt y y' v)
    (hK : HasDerivAt (fun s => B s 0) (rot • B v 1) v)
    (hN : HasDerivAt (fun s => B s 1) (-rot • B v 0) v) :
    HasDerivAt (fun s => tangent (ρ s) (B s) (x s) (y s))
      (tangentMotion (ρ v) ρ' rot (B v) (x v) (y v) x' y') v := by
  convert! hasDerivAt_pack hx (((hρ.neg.mul hx).smul hK).add (hy.smul hN)) using 1
  ext i
  fin_cases i <;> simp [tangentMotion, pack] <;> ring

/-- The ambient ODE is equivalent to the two explicit coordinate ODEs, using
actual derivatives of the curve and the moving frame. -/
theorem hasDerivAt_projected_iff {β ρ x y : ℝ → ℝ} {B : ℝ → Frame}
    {v β' ρ' rot x' y' F d : ℝ} {g : Plane} {f : Space}
    (hβ0 : β v ≠ 0) (hρ : HasDerivAt ρ ρ' v)
    (hx : HasDerivAt x x' v) (hy : HasDerivAt y y' v)
    (hK : HasDerivAt (fun s => B s 0) (rot • B v 1) v)
    (hN : HasDerivAt (fun s => B s 1) (-rot • B v 0) v) :
    HasDerivAt (fun s => tangent (ρ s) (B s) (x s) (y s))
      (TangentProjection.projectedRhs (normal (β v) (ρ v) (B v))
        (normalMotion (β v) β' (ρ v) ρ' rot (B v))
        (tangent (ρ v) (B v) (x v) (y v))
        (baseAction F g (tangent (ρ v) (B v) (x v) (y v))) f d) v ↔
    x' = rhsX F d (ρ v) ρ' rot (B v) g f (x v) (y v) ∧
      y' = rhsY F d (ρ v) rot (B v) g f (x v) (y v) := by
  have ht := hasDerivAt_tangent hρ hx hy hK hN
  rw [← tangentMotion_eq_projectedRhs_iff hβ0]
  constructor
  · intro h
    exact ht.unique h
  · intro h
    exact h ▸ ht

/-- Counterclockwise quarter-turn in the angular-axial plane. -/
noncomputable def quarterTurn : Plane →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := fun w => !₂[-w 1, w 0]
    map_add' := by
      intro u v
      ext i
      fin_cases i <;> simp
      ring
    map_smul' := by
      intro c u
      ext i
      fin_cases i <;> simp }

theorem quarterTurn_square (w : Plane) : quarterTurn (quarterTurn w) = -w := by
  ext i
  fin_cases i <;> simp [quarterTurn]

theorem inner_quarterTurn_self (w : Plane) : ⟪w, quarterTurn w⟫_ℝ = 0 := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem quarterTurn_inner (u v : Plane) :
    ⟪quarterTurn u, quarterTurn v⟫_ℝ = ⟪u, v⟫_ℝ := by
  simp [quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem unit_pair_orthonormal (K : Plane) (hK : ‖K‖ = 1) :
    Orthonormal ℝ ![K, quarterTurn K] := by
  apply orthonormal_iff_ite.mpr
  intro i j
  fin_cases i <;> fin_cases j
  · change ⟪K, K⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, hK]
    norm_num
  · change ⟪K, quarterTurn K⟫_ℝ = 0
    exact inner_quarterTurn_self K
  · change ⟪quarterTurn K, K⟫_ℝ = 0
    rw [real_inner_comm, inner_quarterTurn_self]
  · change ⟪quarterTurn K, quarterTurn K⟫_ℝ = 1
    rw [quarterTurn_inner, real_inner_self_eq_norm_sq, hK]
    norm_num

/-- Frame of unit as an element of `Frame`. -/
noncomputable def frameOfUnit (K : Plane) (hK : ‖K‖ = 1) : Frame :=
  (basisOfOrthonormalOfCardEqFinrank (unit_pair_orthonormal K hK) (by
      simp [Plane])).toOrthonormalBasis
    (by simpa using unit_pair_orthonormal K hK)

@[simp] theorem frameOfUnit_zero (K : Plane) (hK : ‖K‖ = 1) : frameOfUnit K hK 0 = K := by
  simp [frameOfUnit]

@[simp] theorem frameOfUnit_one (K : Plane) (hK : ‖K‖ = 1) :
    frameOfUnit K hK 1 = quarterTurn K := by
  simp [frameOfUnit]

/-- Normal scale, given by `‖tail n‖`. -/
noncomputable def normalScale (n : Space) : ℝ := ‖tail n‖
/-- Radial slope, given by `n 0 / normalScale n`. -/
noncomputable def radialSlope (n : Space) : ℝ := n 0 / normalScale n
/-- Normal direction, given by `(normalScale n)⁻¹ • tail n`. -/
noncomputable def normalDirection (n : Space) : Plane := (normalScale n)⁻¹ • tail n

theorem normalScale_pos {n : Space} (hn : tail n ≠ 0) : 0 < normalScale n :=
  norm_pos_iff.mpr hn

theorem normalDirection_unit {n : Space} (hn : tail n ≠ 0) : ‖normalDirection n‖ = 1 := by
  simp only [normalDirection, normalScale, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)

/-- Normal frame, given by `frameOfUnit (normalDirection n) (normalDirection_unit hn)`. -/
noncomputable def normalFrame (n : Space) (hn : tail n ≠ 0) : Frame :=
  frameOfUnit (normalDirection n) (normalDirection_unit hn)

@[simp] theorem normalFrame_zero (n : Space) (hn : tail n ≠ 0) :
    normalFrame n hn 0 = normalDirection n := frameOfUnit_zero _ _

@[simp] theorem normalFrame_one (n : Space) (hn : tail n ≠ 0) :
    normalFrame n hn 1 = quarterTurn (normalDirection n) := frameOfUnit_one _ _

/-- Reconstruction of the given normal, not an independent choice of reference
normal.  Only its tangential part is required to be nonzero. -/
theorem normal_reconstructed {n : Space} (hn : tail n ≠ 0) :
    normal (normalScale n) (radialSlope n) (normalFrame n hn) = n := by
  have hscale : normalScale n ≠ 0 := (normalScale_pos hn).ne'
  simp only [normal, radialSlope, normalFrame_zero, normalDirection,
    smul_smul, mul_inv_cancel₀ hscale, one_smul]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, pack_zero]
    field_simp
  · rfl
  · rfl

section SmoothFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : WithTop ℕ∞} {n : E → Space} {q : E}

theorem contDiffAt_normalScale (hn : ContDiffAt ℝ m n q) (hne : tail (n q) ≠ 0) :
    ContDiffAt ℝ m (fun p => normalScale (n p)) q := by
  exact (tailCLM.contDiff.contDiffAt.comp q hn).norm ℝ hne

theorem contDiffAt_radialSlope (hn : ContDiffAt ℝ m n q) (hne : tail (n q) ≠ 0) :
    ContDiffAt ℝ m (fun p => radialSlope (n p)) q := by
  exact ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0).contDiff.contDiffAt.comp q hn).div
    (contDiffAt_normalScale hn hne) (normalScale_pos hne).ne'

theorem contDiffAt_normalDirection (hn : ContDiffAt ℝ m n q) (hne : tail (n q) ≠ 0) :
    ContDiffAt ℝ m (fun p => normalDirection (n p)) q := by
  exact ((contDiffAt_normalScale hn hne).inv (normalScale_pos hne).ne').smul
    (tailCLM.contDiff.contDiffAt.comp q hn)

theorem contDiffAt_transverseDirection (hn : ContDiffAt ℝ m n q)
    (hne : tail (n q) ≠ 0) :
    ContDiffAt ℝ m (fun p => quarterTurn (normalDirection (n p))) q :=
  quarterTurn.contDiff.contDiffAt.comp q (contDiffAt_normalDirection hn hne)

end SmoothFrame

/-- The reconstructed directions are jointly smooth functions of the actual
phase normal, away from the axis and zeros of its tangential part. -/
theorem phase_frame_smooth (ε p pz x0 : ℝ) (F G : PhaseCalculus.Slow → ℝ)
    (q : PhaseCalculus.Slot) (hR : q.1.1 ≠ 0)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hne : tail (PhaseCalculus.phaseNormal ε p pz x0 F G q) ≠ 0) :
    ContDiffAt ℝ ∞ (fun r => radialSlope (PhaseCalculus.phaseNormal ε p pz x0 F G r)) q ∧
    ContDiffAt ℝ ∞ (fun r => normalDirection (PhaseCalculus.phaseNormal ε p pz x0 F G r)) q ∧
    ContDiffAt ℝ ∞
      (fun r => quarterTurn (normalDirection (PhaseCalculus.phaseNormal ε p pz x0 F G r))) q := by
  have hn := PhaseCalculus.contDiffAt_phaseNormal ε p pz x0 F G q hR hF hG
  exact ⟨contDiffAt_radialSlope hn hne, contDiffAt_normalDirection hn hne,
    contDiffAt_transverseDirection hn hne⟩

/-- A differentiable unit vector has purely rotational derivative in its
orthonormal frame.  The angular speed is computed from the derivative. -/
theorem unit_curve_rotation {K : ℝ → Plane} {K' : Plane} {v : ℝ}
    (hK : HasDerivAt K K' v) (hunit : ∀ᶠ s in nhds v, ‖K s‖ = 1) :
    K' = ⟪quarterTurn (K v), K'⟫_ℝ • quarterTurn (K v) := by
  have hnorm : ‖K v‖ = 1 := Filter.EventuallyEq.eq_of_nhds hunit
  have heq : (fun s => ⟪K s, K s⟫_ℝ) =ᶠ[nhds v] (fun _ => (1 : ℝ)) := by
    filter_upwards [hunit] with s hs
    rw [real_inner_self_eq_norm_sq, hs, one_pow]
  have hd := (hasDerivAt_const v (1 : ℝ)).congr_of_eventuallyEq heq
  have hh := (hK.inner ℝ hK).unique hd
  have horth : ⟪K v, K'⟫_ℝ = 0 := by
    rw [real_inner_comm (K v) K'] at hh
    linarith
  have hb := frame_expand (frameOfUnit (K v) hnorm) K'
  simpa only [frameOfUnit_zero, frameOfUnit_one, horth, zero_smul, zero_add] using hb.symm

/-- Rotation of the second direction is derived, rather than assumed
independently of the first direction. -/
theorem hasDerivAt_quarterTurn_of_rotation {K : ℝ → Plane} {v rot : ℝ}
    (hK : HasDerivAt K (rot • quarterTurn (K v)) v) :
    HasDerivAt (fun s => quarterTurn (K s)) (-rot • K v) v := by
  have h := quarterTurn.hasFDerivAt.comp_hasDerivAt v hK
  simpa only [Function.comp_def, map_smul, quarterTurn_square, smul_neg, neg_smul] using h

/-- Every differentiable normal with nonzero tangential part supplies the
rotating frame needed by the exact coordinate equation. -/
theorem reconstructed_frame_hasDerivAt {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : tail (n v) ≠ 0) :
    ∃ rot : ℝ,
      HasDerivAt (fun s => normalDirection (n s))
        (rot • quarterTurn (normalDirection (n v))) v ∧
      HasDerivAt (fun s => quarterTurn (normalDirection (n s)))
        (-rot • normalDirection (n v)) v := by
  have htail := tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  have hscale : HasDerivAt (fun s => normalScale (n s))
      (⟪tail (n v), tail n'⟫_ℝ / normalScale (n v)) v := by
    have hsq := htail.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm,
      mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] at hsq
    exact hsq
  let Kdot : Plane := (normalScale (n v))⁻¹ • tail n' +
    (-(⟪tail (n v), tail n'⟫_ℝ / normalScale (n v)) / normalScale (n v) ^ 2) • tail (n v)
  have hdir : HasDerivAt (fun s => normalDirection (n s)) Kdot v :=
    (hscale.inv (normalScale_pos hne).ne').smul htail
  have hunit : ∀ᶠ s in nhds v, ‖normalDirection (n s)‖ = 1 := by
    have hne' : ∀ᶠ s in nhds v, tail (n s) ≠ 0 :=
      htail.continuousAt.eventually_ne hne
    filter_upwards [hne'] with s hs
    exact normalDirection_unit hs
  have hrot := unit_curve_rotation hdir hunit
  refine ⟨⟪quarterTurn (normalDirection (n v)), Kdot⟫_ℝ, ?_, ?_⟩
  · exact hrot ▸ hdir
  · exact hasDerivAt_quarterTurn_of_rotation (hrot ▸ hdir)

/-! ## Quantitative coefficient comparison -/

theorem abs_div_le_of_one_le (a d : ℝ) (hd : 1 ≤ d) : |a / d| ≤ |a| := by
  rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hd)]
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).2
    (by nlinarith [abs_nonneg a])

theorem reciprocal_quadratic_difference (r s : ℝ) :
    |1 / (1 + r ^ 2) - 1 / (1 + s ^ 2)| ≤ |r - s| * (|r| + |s|) := by
  have hr : 1 + r ^ 2 ≠ 0 := by positivity
  have hs : 1 + s ^ 2 ≠ 0 := by positivity
  have heq : 1 / (1 + r ^ 2) - 1 / (1 + s ^ 2) =
      (s - r) * (s + r) / ((1 + r ^ 2) * (1 + s ^ 2)) := by
    field_simp; ring
  rw [heq]
  calc
    |(s - r) * (s + r) / ((1 + r ^ 2) * (1 + s ^ 2))| ≤ |(s - r) * (s + r)| :=
      abs_div_le_of_one_le _ _ (by
        nlinarith only [sq_nonneg r, sq_nonneg s, mul_nonneg (sq_nonneg r) (sq_nonneg s)])
    _ ≤ |r - s| * (|r| + |s|) := by
      rw [abs_mul, abs_sub_comm s r]
      exact mul_le_mul_of_nonneg_left (by linarith [abs_add_le s r]) (abs_nonneg _)

theorem product_perturbation_le {F F0 N N0 M η : ℝ}
    (hN : |N| ≤ 1) (hF0 : |F0| ≤ M)
    (hF : |F - F0| ≤ η) (hNd : |N - N0| ≤ η) :
    |F * N - F0 * N0| ≤ (1 + M) * η := by
  have hη : 0 ≤ η := (abs_nonneg _).trans hF
  have hM : 0 ≤ M := (abs_nonneg _).trans hF0
  calc
    |F * N - F0 * N0| = |(F - F0) * N + F0 * (N - N0)| := by congr 1; ring
    _ ≤ |(F - F0) * N| + |F0 * (N - N0)| := abs_add_le _ _
    _ = |F - F0| * |N| + |F0| * |N - N0| := by rw [abs_mul, abs_mul]
    _ ≤ η * 1 + M * η := add_le_add
      (mul_le_mul hF hN (abs_nonneg _) hη)
      (mul_le_mul hF0 hNd (abs_nonneg _) hM)
    _ = (1 + M) * η := by ring

/-- Explicit bounds in geometric coordinates.  The four small quantities are
the normal slope error, rotation, radial slope derivative and projected shear.
No coefficient or propagator estimate is included among the assumptions. -/
theorem scalar_coefficients_close
    {F F0 N N0 ρ s ρ' rot gK gN g0 M η : ℝ}
    (hM : 1 ≤ M) (hη : 0 ≤ η) (hρ : |ρ| ≤ M) (hs : |s| ≤ M)
    (hN : |N| ≤ 1) (hN0 : |N0| ≤ 1) (hF0 : |F0| ≤ M)
    (hF : |F - F0| ≤ η) (hNd : |N - N0| ≤ η) (hρd : |ρ - s| ≤ η)
    (hρ' : |ρ'| ≤ η) (hrot : |rot| ≤ η) (hgK : |gK| ≤ η)
    (hgN : |gN - g0| ≤ η) :
    |coeff11 ρ ρ' gK| ≤ 16 * M ^ 2 * η ∧
    |coeff12 F N ρ rot - 2 * F0 * N0 / (1 + s ^ 2)| ≤ 16 * M ^ 2 * η ∧
    |coeff21 F N gN ρ rot - (-(2 * F0 * N0 + g0))| ≤ 16 * M ^ 2 * η := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hprod := product_perturbation_le hN hF0 hF hNd
  have hrotation : |ρ * rot| ≤ M * η := by
    rw [abs_mul]
    exact mul_le_mul hρ hrot (abs_nonneg _) hM0
  have htwoprod : |2 * F * N - 2 * F0 * N0| ≤ 2 * (1 + M) * η := by
    calc
      |2 * F * N - 2 * F0 * N0| = 2 * |F * N - F0 * N0| := by
        calc
          _ = |2 * (F * N - F0 * N0)| := by congr 1; ring
          _ = _ := by rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      _ ≤ 2 * ((1 + M) * η) := mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = _ := by ring
  have hnum : |2 * F * N - ρ * rot - 2 * F0 * N0| ≤ (2 + 3 * M) * η := by
    calc
      |2 * F * N - ρ * rot - 2 * F0 * N0| =
          |(2 * F * N - 2 * F0 * N0) - ρ * rot| := by congr 1; ring
      _ ≤ |2 * F * N - 2 * F0 * N0| + |ρ * rot| := abs_sub _ _
      _ ≤ 2 * (1 + M) * η + M * η := add_le_add htwoprod hrotation
      _ = _ := by ring
  have hinv : |1 / (1 + ρ ^ 2) - 1 / (1 + s ^ 2)| ≤ 2 * M * η := by
    calc
      _ ≤ |ρ - s| * (|ρ| + |s|) := reciprocal_quadratic_difference ρ s
      _ ≤ η * (M + M) := mul_le_mul hρd (add_le_add hρ hs)
        (add_nonneg (abs_nonneg _) (abs_nonneg _)) hη
      _ = _ := by ring
  have hreference : |2 * F0 * N0| ≤ 2 * M := by
    rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc
      2 * |F0| * |N0| ≤ (2 * M) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hF0 (by norm_num)) hN0 (abs_nonneg _) (by positivity)
      _ = _ := mul_one _
  constructor
  · calc
      |coeff11 ρ ρ' gK| ≤ |ρ * (gK - ρ')| := abs_div_le_of_one_le _ _ (by
          nlinarith only [sq_nonneg ρ])
      _ = |ρ| * |gK - ρ'| := abs_mul _ _
      _ ≤ M * (η + η) := mul_le_mul hρ ((abs_sub _ _).trans (add_le_add hgK hρ'))
        (abs_nonneg _) hM0
      _ ≤ 16 * M ^ 2 * η := by
        have h := mul_le_mul_of_nonneg_right (show 2 * M ≤ 16 * M ^ 2 by
            nlinarith only [hM, sq_nonneg (M - 1)]) hη
        nlinarith only [h]
  constructor
  · have hρden : 1 + ρ ^ 2 ≠ 0 := by positivity
    have hsden : 1 + s ^ 2 ≠ 0 := by positivity
    have heq : coeff12 F N ρ rot - 2 * F0 * N0 / (1 + s ^ 2) =
        (2 * F * N - ρ * rot - 2 * F0 * N0) / (1 + ρ ^ 2) +
        (2 * F0 * N0) * (1 / (1 + ρ ^ 2) - 1 / (1 + s ^ 2)) := by
      unfold coeff12
      field_simp; ring
    rw [heq]
    calc
      _ ≤ |(2 * F * N - ρ * rot - 2 * F0 * N0) / (1 + ρ ^ 2)| +
          |(2 * F0 * N0) * (1 / (1 + ρ ^ 2) - 1 / (1 + s ^ 2))| := abs_add_le _ _
      _ ≤ (2 + 3 * M) * η + (2 * M) * (2 * M * η) := add_le_add
        ((abs_div_le_of_one_le _ _ (by nlinarith only [sq_nonneg ρ])).trans hnum)
        (by rw [abs_mul]; exact mul_le_mul hreference hinv (abs_nonneg _) (by positivity))
      _ ≤ 16 * M ^ 2 * η := by
        have h := mul_le_mul_of_nonneg_right
          (show 2 + 3 * M + 4 * M ^ 2 ≤ 16 * M ^ 2 by nlinarith only [hM, sq_nonneg (M - 1)]) hη
        nlinarith only [h]
  · calc
      |coeff21 F N gN ρ rot - (-(2 * F0 * N0 + g0))| =
          |-(2 * F * N - 2 * F0 * N0) - (gN - g0) + ρ * rot| := by
        unfold coeff21
        congr 1
        ring
      _ ≤ |-(2 * F * N - 2 * F0 * N0) - (gN - g0)| + |ρ * rot| := abs_add_le _ _
      _ ≤ (|2 * F * N - 2 * F0 * N0| + |gN - g0|) + |ρ * rot| := by
        exact add_le_add_left (by
          simpa only [abs_neg] using abs_sub (-(2 * F * N - 2 * F0 * N0)) (gN - g0)) _
      _ ≤ (2 * (1 + M) * η + η) + M * η := add_le_add (add_le_add htwoprod hgN) hrotation
      _ ≤ 16 * M ^ 2 * η := by
        have h := mul_le_mul_of_nonneg_right (show 3 + 3 * M ≤ 16 * M ^ 2 by
            nlinarith only [hM, sq_nonneg (M - 1)]) hη
        nlinarith only [h]

theorem inner_perturbation_le {K K0 g g0 : Plane} {M η : ℝ}
    (hK : ‖K‖ ≤ 1) (hg0 : ‖g0‖ ≤ M)
    (hKd : ‖K - K0‖ ≤ η) (hgd : ‖g - g0‖ ≤ η) :
    |⟪K, g⟫_ℝ - ⟪K0, g0⟫_ℝ| ≤ (1 + M) * η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hKd
  have hM : 0 ≤ M := (norm_nonneg _).trans hg0
  calc
    |⟪K, g⟫_ℝ - ⟪K0, g0⟫_ℝ| = |⟪K, g - g0⟫_ℝ + ⟪K - K0, g0⟫_ℝ| := by
      rw [inner_sub_left, inner_sub_right]
      congr 1
      ring
    _ ≤ |⟪K, g - g0⟫_ℝ| + |⟪K - K0, g0⟫_ℝ| := abs_add_le _ _
    _ ≤ ‖K‖ * ‖g - g0‖ + ‖K - K0‖ * ‖g0‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ 1 * η + η * M := add_le_add
      (mul_le_mul hK hgd (norm_nonneg _) zero_le_one)
      (mul_le_mul hKd hg0 (norm_nonneg _) hη)
    _ = (1 + M) * η := by ring

theorem frame_coordinate_abs_le_one (B : Frame) (i j : Fin 2) : |B i j| ≤ 1 := by
  simpa only [Real.norm_eq_abs, B.norm_eq_one] using PiLp.norm_apply_le (B i) j

theorem frame_coordinate_difference_le {B B0 : Frame} {i j : Fin 2} {η : ℝ}
    (h : ‖B i - B0 i‖ ≤ η) : |B i j - B0 i j| ≤ η := by
  have h' := (PiLp.norm_apply_le (B i - B0 i) j).trans h
  simpa only [PiLp.sub_apply, Real.norm_eq_abs] using h'

/-- Norm bounds on actual geometric data imply the matrix comparison.
Taking `η = C / S` gives the required `O(1/S)` with the displayed constant.
The reference shear is perpendicular to the reference normal direction. -/
theorem frame_coefficients_close {B B0 : Frame} {g g0 : Plane}
    {F F0 ρ s ρ' rot M η : ℝ}
    (hM : 1 ≤ M) (hη : 0 ≤ η) (hρ : |ρ| ≤ M) (hs : |s| ≤ M)
    (hF0 : |F0| ≤ M) (hg0 : ‖g0‖ ≤ M) (horth : ⟪B0 0, g0⟫_ℝ = 0)
    (hF : |F - F0| ≤ η) (hg : ‖g - g0‖ ≤ η)
    (hK : ‖B 0 - B0 0‖ ≤ η) (hN : ‖B 1 - B0 1‖ ≤ η)
    (hρd : |ρ - s| ≤ η) (hρ' : |ρ'| ≤ η) (hrot : |rot| ≤ η) :
    |coeff11 ρ ρ' ⟪B 0, g⟫_ℝ| ≤ (16 * M ^ 2 * (1 + M)) * η ∧
    |coeff12 F ((B 1) 0) ρ rot - 2 * F0 * ((B0 1) 0) / (1 + s ^ 2)| ≤
      (16 * M ^ 2 * (1 + M)) * η ∧
    |coeff21 F ((B 1) 0) ⟪B 1, g⟫_ℝ ρ rot - (-(2 * F0 * ((B0 1) 0) + ⟪B0 1, g0⟫_ℝ))| ≤
      (16 * M ^ 2 * (1 + M)) * η := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have henlarge : η ≤ (1 + M) * η := by nlinarith only [mul_nonneg hM0 hη]
  have hgK := inner_perturbation_le (le_of_eq (B.norm_eq_one 0)) hg0 hK hg
  rw [horth, sub_zero] at hgK
  have hgN := inner_perturbation_le (le_of_eq (B.norm_eq_one 1)) hg0 hN hg
  have h := scalar_coefficients_close hM (hη.trans henlarge) hρ hs
    (frame_coordinate_abs_le_one B 1 0) (frame_coordinate_abs_le_one B0 1 0) hF0
    (hF.trans henlarge) ((frame_coordinate_difference_le (j := 0) hN).trans henlarge)
    (hρd.trans henlarge) (hρ'.trans henlarge) (hrot.trans henlarge) hgK hgN
  simpa only [mul_assoc] using h

/-! ## The moving eigenbasis, including its derivative -/

/-- Modal11, given by `(a + h * b + c / h - rate) / 2`. -/
noncomputable def modal11 (a b c h rate : ℝ) : ℝ := (a + h * b + c / h - rate) / 2
/-- Modal12, given by `(a - h * b + c / h + rate) / 2`. -/
noncomputable def modal12 (a b c h rate : ℝ) : ℝ := (a - h * b + c / h + rate) / 2
/-- Modal21, given by `(a + h * b - c / h + rate) / 2`. -/
noncomputable def modal21 (a b c h rate : ℝ) : ℝ := (a + h * b - c / h + rate) / 2
/-- Modal22, given by `(a - h * b - c / h - rate) / 2`. -/
noncomputable def modal22 (a b c h rate : ℝ) : ℝ := (a - h * b - c / h - rate) / 2

/-- Exact change to `x = p + q`, `y = h (p - q)`, with `h' = rate * h`.
Here the reference off-diagonal entries are `λ/h` and `λ*h`, and `a,b,c`
are the three errors already estimated by `frame_coefficients_close`. -/
theorem modal_equations_iff {h : ℝ} (hh : h ≠ 0)
    (p q p' q' lam damping a b c rate fx fy : ℝ) :
    (p' + q' = (a - damping) * (p + q) + (lam / h + b) * (h * (p - q)) + fx ∧
      rate * h * (p - q) + h * (p' - q') =
        (lam * h + c) * (p + q) - damping * (h * (p - q)) + fy) ↔
    (p' = (lam - damping + modal11 a b c h rate) * p + modal12 a b c h rate * q +
      (fx + fy / h) / 2 ∧
     q' = modal21 a b c h rate * p + (-lam - damping + modal22 a b c h rate) * q +
      (fx - fy / h) / 2) := by
  constructor
  · rintro ⟨hx, hy⟩
    constructor
    · calc
        p' = ((p' + q') + ((rate * h * (p - q) + h * (p' - q')) / h -
            rate * (p - q))) / 2 := by field_simp; ring
        _ = _ := by
          rw [hx, hy]
          unfold modal11 modal12
          field_simp; ring
    · calc
        q' = ((p' + q') - ((rate * h * (p - q) + h * (p' - q')) / h -
            rate * (p - q))) / 2 := by field_simp; ring
        _ = _ := by
          rw [hx, hy]
          unfold modal21 modal22
          field_simp; ring
  · rintro ⟨rfl, rfl⟩
    constructor
    · unfold modal11 modal12 modal21 modal22
      field_simp; ring
    · unfold modal11 modal12 modal21 modal22
      field_simp; ring

/-- Pair continuous linear map, constructed using `LinearMap.toContinuousLinearMap`. -/
noncomputable def pairCLM : (ℝ × ℝ) →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap {
    toFun := fun z => !₂[z.1, z.2]
    map_add' := by intro u v; ext i; fin_cases i <;> simp
    map_smul' := by intro c u; ext i; fin_cases i <;> simp }

/-- Actual differentiation of the moving eigenbasis gives the operator used
by `GrowingMode`; no propagator estimate or cone condition is assumed. -/
theorem hasDerivAt_modal {p q h : ℝ → ℝ}
    {v p' q' lam damping a b c rate fx fy : ℝ}
    (hh0 : h v ≠ 0) (hp : HasDerivAt p p' v) (hq : HasDerivAt q q' v)
    (hh : HasDerivAt h (rate * h v) v)
    (hx : HasDerivAt (fun s => p s + q s)
      ((a - damping) * (p v + q v) + (lam / h v + b) * (h v * (p v - q v)) + fx) v)
    (hy : HasDerivAt (fun s => h s * (p s - q s))
      ((lam * h v + c) * (p v + q v) - damping * (h v * (p v - q v)) + fy) v) :
    HasDerivAt (fun s => !₂[p s, q s])
      (GrowingMode.modalOperator lam damping (modal11 a b c (h v) rate)
        (modal12 a b c (h v) rate) (modal21 a b c (h v) rate)
        (modal22 a b c (h v) rate) !₂[p v, q v] +
          !₂[(fx + fy / h v) / 2, (fx - fy / h v) / 2]) v := by
  have hx' := (hp.add hq).unique hx
  have hy' := (hh.fun_mul (hp.fun_sub hq)).unique hy
  have hsys := (modal_equations_iff hh0 (p v) (q v) p' q' lam damping a b c rate fx fy).mp
    ⟨hx', by nlinarith only [hy']⟩
  have hd : HasDerivAt (fun s => !₂[p s, q s]) !₂[p', q'] v :=
    pairCLM.hasFDerivAt.comp_hasDerivAt v (hp.prodMk hq)
  convert! hd using 1
  ext i
  fin_cases i <;> simp [hsys.1, hsys.2]

theorem abs_four_sum_div_two_le {a b c d A B C D : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D) :
    |(a + b + c + d) / 2| ≤ A + B + C + D := by
  calc
    _ ≤ |a + b + c + d| := abs_div_le_of_one_le _ _ (by norm_num)
    _ ≤ |a + b + c| + |d| := abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |d| := add_le_add_left (abs_add_le _ _) _
    _ ≤ ((|a| + |b|) + |c|) + |d| := add_le_add_left (add_le_add_left (abs_add_le _ _) _) _
    _ ≤ A + B + C + D := add_le_add (add_le_add (add_le_add ha hb) hc) hd

/-- All four modal errors are bounded explicitly.  `rate = h'/h` is the
extra error arising from the time-dependent eigenbasis. -/
theorem modal_errors_le {a b c h rate H δ κ : ℝ}
    (hH : 0 ≤ H)
    (ha : |a| ≤ δ) (hb : |b| ≤ δ) (hc : |c| ≤ δ)
    (hh : |h| ≤ H) (hhi : |1 / h| ≤ H) (hrate : |rate| ≤ κ) :
    |modal11 a b c h rate| ≤ (1 + 2 * H) * δ + κ ∧
    |modal12 a b c h rate| ≤ (1 + 2 * H) * δ + κ ∧
    |modal21 a b c h rate| ≤ (1 + 2 * H) * δ + κ ∧
    |modal22 a b c h rate| ≤ (1 + 2 * H) * δ + κ := by
  have hhb : |h * b| ≤ H * δ := by rw [abs_mul]; exact mul_le_mul hh hb (abs_nonneg _) hH
  have hch : |c / h| ≤ H * δ := by
    calc
      |c / h| = |1 / h| * |c| := by rw [abs_div, abs_div, abs_one]; ring
      _ ≤ H * δ := mul_le_mul hhi hc (abs_nonneg _) hH
  have hsum : δ + H * δ + H * δ + κ = (1 + 2 * H) * δ + κ := by ring
  have hneg (x A : ℝ) (h : |x| ≤ A) : |-x| ≤ A := by simpa only [abs_neg] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [modal11, sub_eq_add_neg, hsum] using abs_four_sum_div_two_le ha hhb hch (hneg _ _
      hrate)
  · simpa only [modal12, sub_eq_add_neg, hsum] using abs_four_sum_div_two_le ha (hneg _ _ hhb) hch
      hrate
  · simpa only [modal21, sub_eq_add_neg, hsum] using abs_four_sum_div_two_le ha hhb (hneg _ _ hch)
      hrate
  · simpa only [modal22, sub_eq_add_neg, hsum] using
      abs_four_sum_div_two_le ha (hneg _ _ hhb) (hneg _ _ hch) (hneg _ _ hrate)

/-- A tangent ambient vector is recovered from its two coordinate values. -/
theorem tangent_reconstructed {β ρ : ℝ} (hβ : β ≠ 0) (B : Frame) (t : Space)
    (ht : ⟪normal β ρ B, t⟫_ℝ = 0) :
    tangent ρ B (t 0) ⟪B 1, tail t⟫_ℝ = t := by
  apply frame_ext B
  · rfl
  · rw [normal_inner] at ht
    have hz : β * (ρ * t 0 + ⟪B 0, tail t⟫_ℝ) = 0 := by nlinarith only [ht]
    have h := (mul_eq_zero.mp hz).resolve_left hβ
    simp only [tangent, tail_pack, inner_add_right, inner_smul_right,
      frame_inner00, frame_inner01, mul_one, mul_zero, add_zero]
    linarith only [h]
  · simp only [tangent, tail_pack, inner_add_right, inner_smul_right,
      frame_inner10, frame_inner11, mul_zero, mul_one, zero_add]

theorem modalOperator_eq_coefficient (lam damping e11 e12 e21 e22 : ℝ) :
    GrowingMode.modalOperator lam damping e11 e12 e21 e22 =
      ViscousPropagator.coefficient lam damping
        (GrowingMode.modalOperator 0 0 e11 e12 e21 e22) := by
  ext z i
  fin_cases i <;> simp [GrowingMode.modalOperator, ViscousPropagator.coefficient,
    ViscousPropagator.diagonal, ViscousPropagator.reflection] <;> ring

theorem plane_norm_le_coordinate_sum (z : Plane) : ‖z‖ ≤ |z 0| + |z 1| := by
  have h := ViscousPropagator.plane_norm_sq z
  nlinarith only [h, norm_nonneg z, sq_abs (z 0), sq_abs (z 1), abs_nonneg (z 0),
    abs_nonneg (z 1), mul_nonneg (abs_nonneg (z 0)) (abs_nonneg (z 1))]

/-- Entrywise control gives a genuine Euclidean operator norm estimate.
The harmless factor four avoids any choice of an equivalent matrix norm. -/
theorem modal_error_opNorm_le {e11 e12 e21 e22 ε : ℝ}
    (he11 : |e11| ≤ ε) (he12 : |e12| ≤ ε) (he21 : |e21| ≤ ε) (he22 : |e22| ≤ ε) :
    ‖GrowingMode.modalOperator 0 0 e11 e12 e21 e22‖ ≤ 4 * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans he11
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by norm_num) hε)
  intro z
  have hz (i : Fin 2) : |z i| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
  have hrow {a b : ℝ} (ha : |a| ≤ ε) (hb : |b| ≤ ε) :
      |a * z 0 + b * z 1| ≤ 2 * ε * ‖z‖ := by
    calc
      _ ≤ |a * z 0| + |b * z 1| := abs_add_le _ _
      _ = |a| * |z 0| + |b| * |z 1| := by rw [abs_mul, abs_mul]
      _ ≤ ε * ‖z‖ + ε * ‖z‖ := add_le_add
        (mul_le_mul ha (hz 0) (abs_nonneg _) hε)
        (mul_le_mul hb (hz 1) (abs_nonneg _) hε)
      _ = _ := by ring
  calc
    _ ≤ |(GrowingMode.modalOperator 0 0 e11 e12 e21 e22 z) 0| +
        |(GrowingMode.modalOperator 0 0 e11 e12 e21 e22 z) 1| := plane_norm_le_coordinate_sum _
    _ = |e11 * z 0 + e12 * z 1| + |e21 * z 0 + e22 * z 1| := by simp
    _ ≤ 2 * ε * ‖z‖ + 2 * ε * ‖z‖ := add_le_add (hrow he11 he12) (hrow he21 he22)
    _ = _ := by ring

/-- This is the exact quadratic-form hypothesis accepted by the weighted
propagator and parameter-jet estimates.  Scalar viscosity keeps its sign. -/
theorem modal_energy_le {lam e11 e12 e21 e22 ε : ℝ} (hlam : 0 ≤ lam) (damping : ℝ)
    (he11 : |e11| ≤ ε) (he12 : |e12| ≤ ε) (he21 : |e21| ≤ ε) (he22 : |e22| ≤ ε)
    (z : Plane) :
    ⟪z, GrowingMode.modalOperator lam damping e11 e12 e21 e22 z⟫_ℝ ≤
      (lam - damping + 4 * ε) * ‖z‖ ^ 2 := by
  rw [modalOperator_eq_coefficient]
  exact (ViscousPropagator.coefficient_energy_le hlam damping _ z).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add_right (modal_error_opNorm_le he11 he12 he21 he22) _) (sq_nonneg _))

end NavierStokes.MovingFrameODE

end

end

@[expose] public section

namespace NavierStokes.PhaseEstimates

open Set Filter
open scoped Topology InnerProductSpace

/-- Plane: an abbreviation for `MovingFrameODE.Plane`. -/
abbrev Plane := MovingFrameODE.Plane
/-- Space: an abbreviation for `MovingFrameODE.Space`. -/
abbrev Space := MovingFrameODE.Space
/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

/-- Rounding in the punctured integer lattice.  The zero floor is replaced by
one; the distance to the input is still at most one. -/
noncomputable def nonzeroRound (x : ℝ) : ℤ := if Int.floor x = 0 then 1 else Int.floor x

theorem nonzeroRound_ne_zero (x : ℝ) : nonzeroRound x ≠ 0 := by
  unfold nonzeroRound
  split_ifs with h
  · norm_num
  · exact h

theorem nonzeroRound_error (x : ℝ) : |(nonzeroRound x : ℝ) - x| ≤ 1 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  unfold nonzeroRound
  split_ifs with h
  · rw [h] at hlo hhi
    norm_num at hlo hhi ⊢
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Rounded frequency, given by `(nonzeroRound (k * target) : ℝ) / k`. -/
noncomputable def roundedFrequency (k target : ℝ) : ℝ := (nonzeroRound (k * target) : ℝ) / k

theorem roundedFrequency_integer {k : ℝ} (hk : k ≠ 0) (target : ℝ) :
    k * roundedFrequency k target = (nonzeroRound (k * target) : ℝ) := by
  unfold roundedFrequency
  field_simp

theorem roundedFrequency_nonzero {k : ℝ} (hk : k ≠ 0) (target : ℝ) :
    ∃ m : ℤ, m ≠ 0 ∧ k * roundedFrequency k target = (m : ℝ) :=
  ⟨nonzeroRound (k * target), nonzeroRound_ne_zero _, roundedFrequency_integer hk target⟩

theorem roundedFrequency_ne_zero {k : ℝ} (hk : k ≠ 0) (target : ℝ) :
    roundedFrequency k target ≠ 0 := by
  apply div_ne_zero _ hk
  exact_mod_cast nonzeroRound_ne_zero (k * target)

theorem roundedFrequency_error {k : ℝ} (hk : 0 < k) (target : ℝ) :
    |roundedFrequency k target - target| ≤ 1 / k := by
  have heq : roundedFrequency k target - target =
      ((nonzeroRound (k * target) : ℝ) - k * target) / k := by
    unfold roundedFrequency
    field_simp
  rw [heq, abs_div, abs_of_pos hk]
  exact div_le_div_of_nonneg_right (nonzeroRound_error _) hk.le

/-- The fixed representative frequency in its two tangential components. -/
noncomputable def representativeFrequency (B sigma u L : ℝ) (K g : Plane) : Plane :=
  B • (K - (sigma * u / (L * ‖g‖ ^ 2)) • g)

theorem representative_slope (B sigma u L : ℝ) (K g : Plane)
    (hg : g ≠ 0) (horth : ⟪K, g⟫_ℝ = 0) :
    ⟪representativeFrequency B sigma u L K g, g⟫_ℝ = -sigma * B * u / L := by
  have hnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  simp only [representativeFrequency, real_inner_smul_left, inner_sub_left,
    real_inner_self_eq_norm_sq, horth]
  by_cases hL : L = 0
  · simp [hL]
  · field_simp
    ring

theorem representative_tilt (B sigma u L : ℝ) (K g : Plane) :
    ‖representativeFrequency B sigma u L K g - B • K‖ =
      |B| * |sigma| * |u| / (|L| * ‖g‖) := by
  by_cases hg : g = 0
  · simp [representativeFrequency, hg]
  have hnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have heq : representativeFrequency B sigma u L K g - B • K =
      -(B * (sigma * u / (L * ‖g‖ ^ 2))) • g := by
    unfold representativeFrequency
    module
  rw [heq, norm_smul]
  simp only [norm_neg, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_norm]
  by_cases hL : L = 0
  · simp [hL]
  · have habsL : |L| ≠ 0 := abs_ne_zero.mpr hL
    field_simp

/-- A bound on the fixed representative frequency follows from its explicit
tilt; its angular component is later multiplied by the representative radius. -/
theorem representative_frequency_bound (B sigma u L : ℝ) (K g : Plane)
    (hK : ‖K‖ = 1) :
    ‖representativeFrequency B sigma u L K g‖ ≤
      |B| + |B| * |sigma| * |u| / (|L| * ‖g‖) := by
  have h := norm_add_le (representativeFrequency B sigma u L K g - B • K) (B • K)
  rw [sub_add_cancel, representative_tilt, norm_smul, Real.norm_eq_abs, hK, mul_one] at h
  linarith only [h]

/-- Signed slot, given by `sigma * (u / 2 + u * v / L)`. -/
noncomputable def signedSlot (sigma u L v : ℝ) : ℝ := sigma * (u / 2 + u * v / L)

/-- The cancellation producing the intended radial slope is exact for the
unrounded representative data. -/
theorem radial_reference_identity (B sigma u L v : ℝ) :
    sigma * B * u / 2 - v * (-sigma * B * u / L) = B * signedSlot sigma u L v := by
  unfold signedSlot
  ring

/-! ## Local C2 control implies the derivative comparison at the representative -/

section LocalBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second derivative controls variation of the first derivative across
a convex chart.  The actual base differs in C1 by the independently supplied
`baseError`, and the chart diameter is `diameter`. -/
theorem local_first_derivative_close {F F0 : E → ℝ} {U : Set E} {q q0 : E}
    {M diameter baseError : ℝ} (hM : 0 ≤ M) (hU : Convex ℝ U)
    (hq : q ∈ U) (hq0 : q0 ∈ U)
    (hC2 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ F0) x)
    (hsecond : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ F0) x‖ ≤ M)
    (hdiameter : ‖q - q0‖ ≤ diameter)
    (hbase : ‖fderiv ℝ F q - fderiv ℝ F0 q‖ ≤ baseError) :
    ‖fderiv ℝ F q - fderiv ℝ F0 q0‖ ≤ M * diameter + baseError := by
  have hlocal := hU.norm_image_sub_le_of_norm_fderiv_le hC2 hsecond hq0 hq
  calc
    _ ≤ ‖fderiv ℝ F q - fderiv ℝ F0 q‖ + ‖fderiv ℝ F0 q - fderiv ℝ F0 q0‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ baseError + M * diameter := add_le_add hbase
      (hlocal.trans (mul_le_mul_of_nonneg_left hdiameter hM))
    _ = _ := by ring

theorem local_directional_derivative_close {F F0 : E → ℝ} {U : Set E} {q q0 e : E}
    {M diameter baseError : ℝ} (hM : 0 ≤ M) (hU : Convex ℝ U)
    (hq : q ∈ U) (hq0 : q0 ∈ U)
    (hC2 : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ F0) x)
    (hsecond : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ F0) x‖ ≤ M)
    (hdiameter : ‖q - q0‖ ≤ diameter)
    (hbase : ‖fderiv ℝ F q - fderiv ℝ F0 q‖ ≤ baseError) (he : ‖e‖ ≤ 1) :
    |fderiv ℝ F q e - fderiv ℝ F0 q0 e| ≤ M * diameter + baseError := by
  have hop := local_first_derivative_close hM hU hq hq0 hC2 hsecond hdiameter hbase
  have hbound : 0 ≤ M * diameter + baseError := (norm_nonneg _).trans hop
  calc
    _ = ‖(fderiv ℝ F q - fderiv ℝ F0 q0) e‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ F q - fderiv ℝ F0 q0‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (M * diameter + baseError) * 1 := mul_le_mul hop he (norm_nonneg _) hbound
    _ = _ := mul_one _

end LocalBase

/-! ## Pointwise error estimates before choosing the band scale -/

theorem radial_frequency_error {p target pz a a0 b b0 M rounding base : ℝ}
    (hp : |p - target| ≤ rounding) (ha : |a| ≤ M)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M)
    (ha0 : |a - a0| ≤ base) (hb0 : |b - b0| ≤ base) :
    |(p * a + pz * b) - (target * a0 + pz * b0)| ≤ M * rounding + 2 * M * base := by
  have hM : 0 ≤ M := (abs_nonneg _).trans ha
  have hr : 0 ≤ rounding := (abs_nonneg _).trans hp
  have hbase : 0 ≤ base := (abs_nonneg _).trans ha0
  calc
    _ = |(p - target) * a + target * (a - a0) + pz * (b - b0)| := by congr 1; ring
    _ ≤ |(p - target) * a + target * (a - a0)| + |pz * (b - b0)| := abs_add_le _ _
    _ ≤ (|(p - target) * a| + |target * (a - a0)|) + |pz * (b - b0)| :=
      add_le_add_left (abs_add_le _ _) _
    _ = (|p - target| * |a| + |target| * |a - a0|) + |pz| * |b - b0| := by
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (rounding * M + M * base) + M * base := add_le_add
      (add_le_add (mul_le_mul hp ha (abs_nonneg _) hr)
        (mul_le_mul htarget ha0 (abs_nonneg _) hM))
      (mul_le_mul hpz hb0 (abs_nonneg _) hM)
    _ = _ := by ring

theorem angular_frequency_error {p target R R0 M rounding diameter : ℝ}
    (hR : R ≠ 0) (hR0 : R0 ≠ 0)
    (hp : |p - target| ≤ rounding) (htarget : |target| ≤ M)
    (hRi : |1 / R| ≤ M) (hR0i : |1 / R0| ≤ M) (hRd : |R - R0| ≤ diameter) :
    |p / R - target / R0| ≤ M * rounding + M ^ 3 * diameter := by
  have hM : 0 ≤ M := (abs_nonneg _).trans htarget
  have hr : 0 ≤ rounding := (abs_nonneg _).trans hp
  have hd : 0 ≤ diameter := (abs_nonneg _).trans hRd
  have htriple : |target * (1 / R) * (1 / R0)| ≤ M ^ 3 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (M * M) * M := mul_le_mul
        (mul_le_mul htarget hRi (abs_nonneg _) hM) hR0i (abs_nonneg _) (mul_nonneg hM hM)
      _ = _ := by ring
  have heq : p / R - target / R0 =
      (p - target) * (1 / R) + (target * (1 / R) * (1 / R0)) * (R0 - R) := by
    field_simp; ring
  rw [heq]
  calc
    _ ≤ |(p - target) * (1 / R)| + |(target * (1 / R) * (1 / R0)) * (R0 - R)| := abs_add_le _ _
    _ = |p - target| * |1 / R| + |target * (1 / R) * (1 / R0)| * |R0 - R| := by
      rw [abs_mul, abs_mul]
    _ ≤ rounding * M + M ^ 3 * diameter := add_le_add
      (mul_le_mul hp hRi (abs_nonneg _) hr)
      (mul_le_mul htriple (by simpa only [abs_sub_comm] using hRd) (abs_nonneg _) (pow_nonneg hM _))
    _ = _ := by ring

theorem axial_frequency_bound {p target pz a b M rounding : ℝ}
    (hM : 1 ≤ M) (hr : rounding ≤ 1) (hp : |p - target| ≤ rounding)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |p * a + pz * b| ≤ 3 * M ^ 2 := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hpp : |p| ≤ 2 * M := by
    have h := (abs_add_le (p - target) target)
    rw [sub_add_cancel] at h
    linarith only [h, hp, hr, htarget, hM]
  calc
    _ ≤ |p * a| + |pz * b| := abs_add_le _ _
    _ = |p| * |a| + |pz| * |b| := by rw [abs_mul, abs_mul]
    _ ≤ (2 * M) * M + M * M := add_le_add
      (mul_le_mul hpp ha (abs_nonneg _) (by positivity))
      (mul_le_mul hpz hb (abs_nonneg _) hM0)
    _ = _ := by ring

/-- Explicit normal, given by `!₂[x0 - v * (p * FR + pz * GR), p / R, pz - ε * v * (p * FZ + pz
* GZ)]`. -/
noncomputable def explicitNormal (ε p pz x0 R v FR GR FZ GZ : ℝ) : Space :=
  !₂[x0 - v * (p * FR + pz * GR), p / R, pz - ε * v * (p * FZ + pz * GZ)]

/-- Reference normal, given by `MovingFrameODE.pack (B * signedSlot sigma u L v) (B • K)`. -/
noncomputable def referenceNormal (B sigma u L v : ℝ) (K : Plane) : Space :=
  MovingFrameODE.pack (B * signedSlot sigma u L v) (B • K)

theorem vec3_norm_le_sum (w : Space) : ‖w‖ ≤ |w 0| + |w 1| + |w 2| := by
  have hs := PhaseCalculus.vec3_norm_sq w
  nlinarith only [hs, norm_nonneg w, sq_abs (w 0), sq_abs (w 1), sq_abs (w 2),
    abs_nonneg (w 0), abs_nonneg (w 1), abs_nonneg (w 2),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 1)),
    mul_nonneg (abs_nonneg (w 0)) (abs_nonneg (w 2)),
    mul_nonneg (abs_nonneg (w 1)) (abs_nonneg (w 2))]

/-- Assembly of the actual normal error from its three independently derived
coefficient errors.  Slot length multiplies only the radial and axial defects. -/
theorem normal_error_from_components
    {ε p pz R v FR GR FZ GZ B sigma u L radial angular axial shear : ℝ} {K : Plane}
    (hRadial : |p * FR + pz * GR - (-sigma * B * u / L)| ≤ radial)
    (hAngular : |p / R - B * K 0| ≤ angular)
    (hAxial : |pz - B * K 1| ≤ axial)
    (hShear : |p * FZ + pz * GZ| ≤ shear) :
    ‖explicitNormal ε p pz (sigma * B * u / 2) R v FR GR FZ GZ -
      referenceNormal B sigma u L v K‖ ≤
      |v| * radial + angular + axial + |ε| * |v| * shear := by
  have hrad : |sigma * B * u / 2 - v * (p * FR + pz * GR) - B * signedSlot sigma u L v| ≤
      |v| * radial := by
    have heq : sigma * B * u / 2 - v * (p * FR + pz * GR) - B * signedSlot sigma u L v =
        -v * (p * FR + pz * GR - (-sigma * B * u / L)) := by
      unfold signedSlot
      ring
    rw [heq, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left hRadial (abs_nonneg _)
  have hz : |pz - ε * v * (p * FZ + pz * GZ) - B * K 1| ≤ axial + |ε| * |v| * shear := by
    calc
      _ = |(pz - B * K 1) - ε * v * (p * FZ + pz * GZ)| := by congr 1; ring
      _ ≤ |pz - B * K 1| + |ε * v * (p * FZ + pz * GZ)| := abs_sub _ _
      _ = |pz - B * K 1| + |ε| * |v| * |p * FZ + pz * GZ| := by rw [abs_mul, abs_mul]
      _ ≤ axial + |ε| * |v| * shear := add_le_add hAxial
        (mul_le_mul_of_nonneg_left hShear (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have h := vec3_norm_le_sum (explicitNormal ε p pz (sigma * B * u / 2) R v FR GR FZ GZ -
    referenceNormal B sigma u L v K)
  change ‖explicitNormal ε p pz (sigma * B * u / 2) R v FR GR FZ GZ -
      referenceNormal B sigma u L v K‖ ≤
    |sigma * B * u / 2 - v * (p * FR + pz * GR) - B * signedSlot sigma u L v| +
    |p / R - B * K 0| + |pz - ε * v * (p * FZ + pz * GZ) - B * K 1| at h
  linarith only [h, hrad, hAngular, hz]

theorem representative_slope_coordinates
    {B sigma u L R0 target pz FR0 GR0 : ℝ} {K g : Plane}
    (hR0 : R0 ≠ 0) (hg : g ≠ 0) (horth : ⟪K, g⟫_ℝ = 0)
    (hgdef : g = !₂[R0 * FR0, GR0])
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g) :
    target * FR0 + pz * GR0 = -sigma * B * u / L := by
  have h := representative_slope B sigma u L K g hg horth
  rw [← hfreq, hgdef] at h
  have hi : ⟪(!₂[target / R0, pz] : Plane), (!₂[R0 * FR0, GR0] : Plane)⟫_ℝ =
      target * FR0 + pz * GR0 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    field_simp
  rwa [hi] at h

theorem representative_coordinate_errors
    {B sigma u L R0 target pz : ℝ} {K g : Plane}
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g) :
    |target / R0 - B * K 0| ≤ |B| * |sigma| * |u| / (|L| * ‖g‖) ∧
    |pz - B * K 1| ≤ |B| * |sigma| * |u| / (|L| * ‖g‖) := by
  have h (i : Fin 2) := PiLp.norm_apply_le (representativeFrequency B sigma u L K g - B • K) i
  rw [representative_tilt, ← hfreq] at h
  constructor
  · simpa using h 0
  · simpa using h 1

/-- The complete finite estimate starts from the chosen representative and
the local derivatives of the actual base. -/
theorem explicit_normal_estimate
    {ε p target pz R R0 v FR GR FZ GZ FR0 GR0 B sigma u L M rounding diameter base : ℝ}
    {K g : Plane}
    (hR : R ≠ 0) (hR0 : R0 ≠ 0) (hg : g ≠ 0) (horth : ⟪K, g⟫_ℝ = 0)
    (hgdef : g = !₂[R0 * FR0, GR0])
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g)
    (hM : 1 ≤ M) (hround : rounding ≤ 1) (hp : |p - target| ≤ rounding)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M)
    (hRi : |1 / R| ≤ M) (hR0i : |1 / R0| ≤ M) (hRd : |R - R0| ≤ diameter)
    (hFR : |FR| ≤ M) (hFZ : |FZ| ≤ M) (hGZ : |GZ| ≤ M)
    (hFR0 : |FR - FR0| ≤ base) (hGR0 : |GR - GR0| ≤ base) :
    ‖explicitNormal ε p pz (sigma * B * u / 2) R v FR GR FZ GZ -
      referenceNormal B sigma u L v K‖ ≤
      |v| * (M * rounding + 2 * M * base) + M * rounding + M ^ 3 * diameter +
      2 * (|B| * |sigma| * |u| / (|L| * ‖g‖)) + |ε| * |v| * (3 * M ^ 2) := by
  have hslope := representative_slope_coordinates hR0 hg horth hgdef hfreq
  have hrad := radial_frequency_error hp hFR htarget hpz hFR0 hGR0
  rw [hslope] at hrad
  have hangle := angular_frequency_error hR hR0 hp htarget hRi hR0i hRd
  obtain ⟨hc0, hc1⟩ := representative_coordinate_errors hfreq
  have hangular : |p / R - B * K 0| ≤ M * rounding + M ^ 3 * diameter +
      |B| * |sigma| * |u| / (|L| * ‖g‖) := by
    calc
      _ ≤ |p / R - target / R0| + |target / R0 - B * K 0| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hangle hc0
  have hshear := axial_frequency_bound hM hround hp htarget hpz hFZ hGZ
  have h := normal_error_from_components (ε := ε) (v := v) hrad hangular hc1 hshear
  linarith only [h]

theorem phaseNormal_eq_explicit (ε p pz x0 : ℝ) (F G : Slow → ℝ)
    (q : PhaseCalculus.Slot) (hε : ε ≠ 0)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    PhaseCalculus.phaseNormal ε p pz x0 F G q =
      explicitNormal ε p pz x0 q.1.1 q.2.2
        (PhaseCalculus.slowR F q.1) (PhaseCalculus.slowR G q.1)
        (PhaseCalculus.slowZ F q.1) (PhaseCalculus.slowZ G q.1) :=
  PhaseCalculus.phaseNormal_formula ε p pz x0 F G q hε hF hG

/-- Phase error, given by `1 / S + S * ε ^ 2 + S / k + ε * S`. -/
noncomputable def phaseError (S ε k : ℝ) : ℝ := 1 / S + S * ε ^ 2 + S / k + ε * S
/-- Phase constant, given by `8 * M ^ 3 + 2 * M ^ 4`. -/
noncomputable def phaseConstant (M : ℝ) : ℝ := 8 * M ^ 3 + 2 * M ^ 4

theorem inverse_cube_bounds {S : ℝ} (hS : 1 ≤ S) :
    1 / S ^ 3 ≤ 1 / S ∧ S * (1 / S ^ 3) ≤ 1 / S := by
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have h2 : S ≤ S ^ 2 := by nlinarith only [hS]
  have h3 : S ^ 2 ≤ S ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hS (sq_nonneg S)
    nlinarith only [h]
  constructor
  · exact one_div_le_one_div_of_le hS0 (h2.trans h3)
  · have heq : S * (1 / S ^ 3) = 1 / S ^ 2 := by field_simp
    rw [heq]
    exact one_div_le_one_div_of_le hS0 h2

theorem representative_tilt_scaled {B sigma u L M S : ℝ} {g : Plane}
    (hM : 0 ≤ M) (hB : |B| ≤ M) (hsigma : |sigma| = 1)
    (hu : |u| ≤ M) (hg : 1 / ‖g‖ ≤ M) (hL : 1 / |L| ≤ M / S) :
    |B| * |sigma| * |u| / (|L| * ‖g‖) ≤ M ^ 4 / S := by
  rw [hsigma, mul_one]
  have hbu : |B| * |u| ≤ M * M := mul_le_mul hB hu (abs_nonneg _) hM
  calc
    _ = (|B| * |u|) * (1 / ‖g‖) * (1 / |L|) := by ring
    _ ≤ (M * M) * M * (M / S) := mul_le_mul
      (mul_le_mul hbu hg (one_div_nonneg.mpr (norm_nonneg _)) (mul_nonneg hM hM)) hL
      (one_div_nonneg.mpr (abs_nonneg _)) (by positivity)
    _ = _ := by ring

/-- A single algebraic estimate displays every long-slot loss. -/
theorem assembled_error_scaled {M S ε k v tilt : ℝ}
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 0 < k) (hε : 0 ≤ ε)
    (hv : |v| ≤ M * S) (htilt : tilt ≤ M ^ 4 / S) :
    |v| * (M * (1 / k) + 2 * M * (M * (1 / S ^ 3 + ε ^ 2))) +
      M * (1 / k) + M ^ 3 * (1 / S ^ 3) + 2 * tilt + |ε| * |v| * (3 * M ^ 2) ≤
      phaseConstant M * phaseError S ε k := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have he0 : 0 ≤ 1 / S := (one_div_pos.mpr hS0).le
  have he1 : 0 ≤ S * ε ^ 2 := mul_nonneg hS0.le (sq_nonneg _)
  have he2 : 0 ≤ S / k := (div_pos hS0 hk).le
  have he3 : 0 ≤ ε * S := mul_nonneg hε hS0.le
  have hE : 0 ≤ phaseError S ε k := by unfold phaseError; positivity
  have hE0 : 1 / S ≤ phaseError S ε k := by unfold phaseError; linarith only [he1, he2, he3]
  have hE01 : 1 / S + S * ε ^ 2 ≤ phaseError S ε k := by unfold phaseError; linarith only [he2, he3]
  have hE2 : S / k ≤ phaseError S ε k := by unfold phaseError; linarith only [he0, he1, he3]
  have hE3 : ε * S ≤ phaseError S ε k := by unfold phaseError; linarith only [he0, he1, he2]
  have hcubes := inverse_cube_bounds hS
  have hround : |v| * (M * (1 / k)) ≤ M ^ 2 * phaseError S ε k := by
    calc
      _ ≤ (M * S) * (M * (1 / k)) := mul_le_mul_of_nonneg_right hv (by positivity)
      _ = M ^ 2 * (S / k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE2 (sq_nonneg M)
  have hbase : |v| * (2 * M * (M * (1 / S ^ 3 + ε ^ 2))) ≤ 2 * M ^ 3 * phaseError S ε k := by
    calc
      _ ≤ (M * S) * (2 * M * (M * (1 / S ^ 3 + ε ^ 2))) := mul_le_mul_of_nonneg_right hv (by
          positivity)
      _ = 2 * M ^ 3 * (S * (1 / S ^ 3) + S * ε ^ 2) := by ring
      _ ≤ 2 * M ^ 3 * (1 / S + S * ε ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hcubes.2 _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hE01 (by positivity)
  have hangle : M * (1 / k) ≤ M * phaseError S ε k := by
    apply mul_le_mul_of_nonneg_left _ hM0
    exact (div_le_div_of_nonneg_right hS hk.le).trans hE2
  have hdiam : M ^ 3 * (1 / S ^ 3) ≤ M ^ 3 * phaseError S ε k :=
    mul_le_mul_of_nonneg_left (hcubes.1.trans hE0) (pow_nonneg hM0 _)
  have htilt' : 2 * tilt ≤ 2 * M ^ 4 * phaseError S ε k := by
    calc
      _ ≤ 2 * (M ^ 4 / S) := mul_le_mul_of_nonneg_left htilt (by norm_num)
      _ = (2 * M ^ 4) * (1 / S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE0 (by positivity)
  have haxial : |ε| * |v| * (3 * M ^ 2) ≤ 3 * M ^ 3 * phaseError S ε k := by
    rw [abs_of_nonneg hε]
    calc
      _ ≤ ε * (M * S) * (3 * M ^ 2) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv hε) (by positivity)
      _ = 3 * M ^ 3 * (ε * S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE3 (by positivity)
  have h2 : M ≤ M ^ 2 := by nlinarith only [hM]
  have h3 : M ^ 2 ≤ M ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hM (sq_nonneg M)
    nlinarith only [h]
  have hcoeff : M ^ 2 + M ≤ 2 * M ^ 3 := by linarith only [h2, h3]
  have hlast := mul_le_mul_of_nonneg_right hcoeff hE
  unfold phaseConstant
  nlinarith only [hround, hbase, hangle, hdiam, htilt', haxial, hlast]

theorem phaseError_le_four_div {S ε k : ℝ} (hS : 0 < S)
    (hε2 : S ^ 2 * ε ^ 2 ≤ 1) (hk2 : S ^ 2 / k ≤ 1) (hε1 : ε * S ^ 2 ≤ 1) :
    phaseError S ε k ≤ 4 / S := by
  have h1 : S * ε ^ 2 ≤ 1 / S := (le_div_iff₀ hS).2 (by nlinarith only [hε2])
  have h2 : S / k ≤ 1 / S := (le_div_iff₀ hS).2 (by
    have heq : S / k * S = S ^ 2 / k := by ring
    rwa [heq])
  have h3 : ε * S ≤ 1 / S := (le_div_iff₀ hS).2 (by nlinarith only [hε1])
  unfold phaseError
  rw [show 4 / S = 4 * (1 / S) by ring]
  linarith only [h1, h2, h3]

/-- Normal velocity, given by `!₂[-(p * FR + pz * GR), 0, -ε * (p * FZ + pz * GZ)]`. -/
noncomputable def normalVelocity (ε p pz FR GR FZ GZ : ℝ) : Space :=
  !₂[-(p * FR + pz * GR), 0, -ε * (p * FZ + pz * GZ)]

/-- The slot derivative is estimated from its exact formula, independently of
the estimate for the normal itself. -/
theorem normalVelocity_bound {ε p pz FR GR FZ GZ slope error shear : ℝ}
    (herror : |p * FR + pz * GR - slope| ≤ error)
    (hshear : |p * FZ + pz * GZ| ≤ shear) :
    ‖normalVelocity ε p pz FR GR FZ GZ‖ ≤ |slope| + error + |ε| * shear := by
  have h := vec3_norm_le_sum (normalVelocity ε p pz FR GR FZ GZ)
  change ‖normalVelocity ε p pz FR GR FZ GZ‖ ≤
    |-(p * FR + pz * GR)| + |(0 : ℝ)| + |-ε * (p * FZ + pz * GZ)| at h
  simp only [abs_neg, abs_zero, add_zero, abs_mul] at h
  have hs : |p * FR + pz * GR| ≤ |slope| + error := by
    have ht := abs_add_le (p * FR + pz * GR - slope) slope
    rw [sub_add_cancel] at ht
    linarith only [ht, herror]
  have hz := mul_le_mul_of_nonneg_left hshear (abs_nonneg ε)
  linarith only [h, hs, hz]

theorem representative_slope_scaled {B sigma u L M S : ℝ}
    (hM : 0 ≤ M) (hB : |B| ≤ M) (hsigma : |sigma| = 1)
    (hu : |u| ≤ M) (hL : 1 / |L| ≤ M / S) :
    |-sigma * B * u / L| ≤ M ^ 3 / S := by
  rw [abs_div, abs_mul, abs_mul, abs_neg, hsigma, one_mul]
  calc
    _ = (|B| * |u|) * (1 / |L|) := by ring
    _ ≤ (M * M) * (M / S) := mul_le_mul
      (mul_le_mul hB hu (abs_nonneg _) hM) hL (one_div_nonneg.mpr (abs_nonneg _))
      (mul_nonneg hM hM)
    _ = _ := by ring

theorem velocity_error_scaled {M S ε k : ℝ}
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 0 < k) (hε : 0 ≤ ε) :
    M ^ 3 / S + (M * (1 / k) + 2 * M * (M * (1 / S ^ 3 + ε ^ 2))) +
      |ε| * (3 * M ^ 2) ≤ phaseConstant M * phaseError S ε k := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hE : 0 ≤ phaseError S ε k := by unfold phaseError; positivity
  have h0 : 1 / S ≤ phaseError S ε k := by
    unfold phaseError
    linarith only [mul_nonneg hS0.le (sq_nonneg ε), div_nonneg hS0.le hk.le, mul_nonneg hε hS0.le]
  have h1 : 1 / S + S * ε ^ 2 ≤ phaseError S ε k := by
    unfold phaseError
    linarith only [div_nonneg hS0.le hk.le, mul_nonneg hε hS0.le]
  have h2 : S / k ≤ phaseError S ε k := by
    unfold phaseError
    linarith only [one_div_nonneg.mpr hS0.le, mul_nonneg hS0.le (sq_nonneg ε), mul_nonneg hε hS0.le]
  have h3 : ε * S ≤ phaseError S ε k := by
    unfold phaseError
    linarith only [one_div_nonneg.mpr hS0.le, mul_nonneg hS0.le (sq_nonneg ε), div_nonneg hS0.le
        hk.le]
  have ha : M ^ 3 / S ≤ M ^ 3 * phaseError S ε k := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h0 (pow_nonneg hM0 3)
  have hb : M * (1 / k) ≤ M * phaseError S ε k :=
    mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right hS hk.le).trans h2) hM0
  have hc : 2 * M * (M * (1 / S ^ 3 + ε ^ 2)) ≤ 2 * M ^ 2 * phaseError S ε k := by
    have hh : 1 / S ^ 3 + ε ^ 2 ≤ phaseError S ε k :=
      (add_le_add (inverse_cube_bounds hS).1
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hS (sq_nonneg ε))).trans h1
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * M ^ 2 by positivity)
    nlinarith only [hh']
  have hd : |ε| * (3 * M ^ 2) ≤ 3 * M ^ 2 * phaseError S ε k := by
    rw [abs_of_nonneg hε]
    have hεle : ε ≤ ε * S := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hS hε
    have hh : ε ≤ phaseError S ε k := hεle.trans h3
    nlinarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ 3 * M ^ 2 by positivity)]
  have hm2 : M ≤ M ^ 2 := by nlinarith only [hM]
  have hm3 : M ^ 2 ≤ M ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_left hM (sq_nonneg M)]
  have hm4 : 0 ≤ M ^ 4 := pow_nonneg hM0 _
  have hcoeff : M ^ 3 + M + 5 * M ^ 2 ≤ phaseConstant M := by
    unfold phaseConstant
    linarith only [hm2, hm3, hm4, pow_nonneg hM0 3]
  nlinarith only [ha, hb, hc, hd, mul_le_mul_of_nonneg_right hcoeff hE]

/-- Quantitative estimates for the actual rounded phase.  The C2 comparison
lemma above supplies the two `M (S⁻³ + ε²)` derivative hypotheses. -/
theorem rounded_normal_estimates
    {ε target pz R R0 v FR GR FZ GZ FR0 GR0 B sigma u L M S k : ℝ} {K g : Plane}
    (hR : R ≠ 0) (hR0 : R0 ≠ 0) (hg : g ≠ 0) (horth : ⟪K, g⟫_ℝ = 0)
    (hgdef : g = !₂[R0 * FR0, GR0])
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g)
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 1 ≤ k) (hε : 0 ≤ ε)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (hB : |B| ≤ M)
    (hsigma : |sigma| = 1) (hu : |u| ≤ M) (hgi : 1 / ‖g‖ ≤ M)
    (hL : 1 / |L| ≤ M / S) (hv : |v| ≤ M * S)
    (hRi : |1 / R| ≤ M) (hR0i : |1 / R0| ≤ M) (hRd : |R - R0| ≤ 1 / S ^ 3)
    (hFR : |FR| ≤ M) (hFZ : |FZ| ≤ M) (hGZ : |GZ| ≤ M)
    (hFR0 : |FR - FR0| ≤ M * (1 / S ^ 3 + ε ^ 2))
    (hGR0 : |GR - GR0| ≤ M * (1 / S ^ 3 + ε ^ 2)) :
    ‖explicitNormal ε (roundedFrequency k target) pz (sigma * B * u / 2) R v FR GR FZ GZ -
      referenceNormal B sigma u L v K‖ ≤ phaseConstant M * phaseError S ε k ∧
    ‖normalVelocity ε (roundedFrequency k target) pz FR GR FZ GZ‖ ≤
      phaseConstant M * phaseError S ε k := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hp := roundedFrequency_error hk0 target
  have hround : 1 / k ≤ 1 := (one_div_le_one_div_of_le zero_lt_one hk).trans_eq (one_div_one)
  have h := explicit_normal_estimate (ε := ε) (v := v) hR hR0 hg horth hgdef hfreq hM hround hp
    htarget hpz hRi hR0i hRd hFR hFZ hGZ hFR0 hGR0
  constructor
  · exact h.trans (assembled_error_scaled hM hS hk0 hε hv
      (representative_tilt_scaled hM0 hB hsigma hu hgi hL))
  · have hslope := representative_slope_coordinates hR0 hg horth hgdef hfreq
    have hrad := radial_frequency_error hp hFR htarget hpz hFR0 hGR0
    rw [hslope] at hrad
    have hz := axial_frequency_bound hM hround hp htarget hpz hFZ hGZ
    have hn := normalVelocity_bound (ε := ε) hrad hz
    have href := representative_slope_scaled hM0 hB hsigma hu hL
    exact (hn.trans (add_le_add_left (add_le_add_left href _) _)).trans
      (velocity_error_scaled hM hS hk0 hε)

/-! ## Quantitative lower bounds and the actual normalized frame -/

theorem tail_norm_le (n : Space) : ‖MovingFrameODE.tail n‖ ≤ ‖n‖ := by
  have h2 := ViscousPropagator.plane_norm_sq (MovingFrameODE.tail n)
  have h3 := PhaseCalculus.vec3_norm_sq n
  change ‖MovingFrameODE.tail n‖ ^ 2 = (n 1) ^ 2 + (n 2) ^ 2 at h2
  nlinarith only [h2, h3, sq_nonneg (n 0), norm_nonneg (MovingFrameODE.tail n), norm_nonneg n]

theorem normalScale_close {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    |MovingFrameODE.normalScale n - B| ≤ δ := by
  have ht := (tail_norm_le (n - MovingFrameODE.pack (B * s) (B • K))).trans hclose
  rw [MovingFrameODE.tail_sub, MovingFrameODE.tail_pack] at ht
  have h := (abs_norm_sub_norm_le (MovingFrameODE.tail n) (B • K)).trans ht
  simpa only [MovingFrameODE.normalScale, norm_smul, Real.norm_eq_abs,
    abs_of_pos hB, hK, mul_one] using h

/-- Closeness derived above controls the tangential normal as well as the full
normal; the weaker full-normal lower bound alone would not build the frame. -/
theorem normal_lower_bounds {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    B / 2 ≤ MovingFrameODE.normalScale n ∧ B / 2 ≤ ‖n‖ ∧
      MovingFrameODE.tail n ≠ 0 ∧ n ≠ 0 := by
  have hc := (abs_le.mp (normalScale_close hB hK hclose)).1
  have hlow : B / 2 ≤ MovingFrameODE.normalScale n := by linarith only [hc, hδ]
  have hnlow : B / 2 ≤ ‖n‖ := hlow.trans (tail_norm_le n)
  refine ⟨hlow, hnlow, ?_, ?_⟩
  · apply norm_pos_iff.mp
    exact lt_of_lt_of_le (half_pos hB) hlow
  · exact norm_pos_iff.mp (lt_of_lt_of_le (half_pos hB) hnlow)

theorem radialSlope_close {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    |MovingFrameODE.radialSlope n - s| ≤ 2 * (1 + |s|) * δ / B := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hclose
  obtain ⟨hlow, _, hne, _⟩ := normal_lower_bounds hB hK hδ hclose
  have hβ : 0 < MovingFrameODE.normalScale n := MovingFrameODE.normalScale_pos hne
  have hscale := normalScale_close hB hK hclose
  have hr := (PiLp.norm_apply_le (n - MovingFrameODE.pack (B * s) (B • K)) 0).trans hclose
  change |n 0 - B * s| ≤ δ at hr
  have heq : MovingFrameODE.radialSlope n - s =
      ((n 0 - B * s) + s * (B - MovingFrameODE.normalScale n)) / MovingFrameODE.normalScale n := by
    unfold MovingFrameODE.radialSlope
    field_simp; ring
  rw [heq, abs_div, abs_of_pos hβ]
  have hnum : |(n 0 - B * s) + s * (B - MovingFrameODE.normalScale n)| ≤ δ + |s| * δ := by
    calc
      _ ≤ |n 0 - B * s| + |s * (B - MovingFrameODE.normalScale n)| := abs_add_le _ _
      _ = |n 0 - B * s| + |s| * |MovingFrameODE.normalScale n - B| := by
        rw [abs_mul, abs_sub_comm B]
      _ ≤ _ := add_le_add hr (mul_le_mul_of_nonneg_left hscale (abs_nonneg _))
  calc
    _ ≤ (δ + |s| * δ) / MovingFrameODE.normalScale n := div_le_div_of_nonneg_right hnum hβ.le
    _ ≤ (δ + |s| * δ) / (B / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hB) hlow
    _ = _ := by ring

theorem normalDirection_close {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    ‖MovingFrameODE.normalDirection n - K‖ ≤ 4 * δ / B := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hclose
  obtain ⟨hlow, _, hne, _⟩ := normal_lower_bounds hB hK hδ hclose
  have hβ : 0 < MovingFrameODE.normalScale n := MovingFrameODE.normalScale_pos hne
  have ht := (tail_norm_le (n - MovingFrameODE.pack (B * s) (B • K))).trans hclose
  rw [MovingFrameODE.tail_sub, MovingFrameODE.tail_pack] at ht
  have hc := normalScale_close hB hK hclose
  have heq : MovingFrameODE.normalDirection n - K =
      (MovingFrameODE.normalScale n)⁻¹ • (MovingFrameODE.tail n - B • K) +
      ((B - MovingFrameODE.normalScale n) / MovingFrameODE.normalScale n) • K := by
    unfold MovingFrameODE.normalDirection
    ext i
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp; ring
  rw [heq]
  have hn := norm_add_le ((MovingFrameODE.normalScale n)⁻¹ • (MovingFrameODE.tail n - B • K))
    (((B - MovingFrameODE.normalScale n) / MovingFrameODE.normalScale n) • K)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hβ), hK, mul_one, abs_div, abs_of_pos hβ,
    abs_sub_comm B] at hn
  have h1 := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hβ.le)
  have h2 := div_le_div_of_nonneg_right hc hβ.le
  have hsum : ‖(MovingFrameODE.normalScale n)⁻¹ • (MovingFrameODE.tail n - B • K) +
      ((B - MovingFrameODE.normalScale n) / MovingFrameODE.normalScale n) • K‖ ≤
      2 * δ / MovingFrameODE.normalScale n := by
    calc
      _ ≤ (MovingFrameODE.normalScale n)⁻¹ * δ + δ / MovingFrameODE.normalScale n :=
        hn.trans (add_le_add h1 h2)
      _ = _ := by ring
  calc
    _ ≤ 2 * δ / MovingFrameODE.normalScale n := hsum
    _ ≤ 2 * δ / (B / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hB) hlow
    _ = _ := by ring

theorem quarterTurn_norm (w : Plane) : ‖MovingFrameODE.quarterTurn w‖ = ‖w‖ := by
  have h := MovingFrameODE.quarterTurn_inner w w
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith only [h, norm_nonneg w, norm_nonneg (MovingFrameODE.quarterTurn w)]

theorem transverseDirection_close {n : Space} {K : Plane} {B s δ : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) :
    ‖MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n) - MovingFrameODE.quarterTurn K‖ ≤
      4 * δ / B := by
  rw [← map_sub, quarterTurn_norm]
  exact normalDirection_close hB hK hδ hclose

/-- Scale derivative, given by `⟪MovingFrameODE.tail n, MovingFrameODE.tail n'⟫_ℝ /
MovingFrameODE.normalScale n`. -/
noncomputable def scaleDerivative (n n' : Space) : ℝ :=
  ⟪MovingFrameODE.tail n, MovingFrameODE.tail n'⟫_ℝ / MovingFrameODE.normalScale n

/-- Slope derivative, given by `(n' 0 - MovingFrameODE.radialSlope n * scaleDerivative n n') /
MovingFrameODE.normalScale n`. -/
noncomputable def slopeDerivative (n n' : Space) : ℝ :=
  (n' 0 - MovingFrameODE.radialSlope n * scaleDerivative n n') / MovingFrameODE.normalScale n

/-- Direction derivative, given by `(MovingFrameODE.normalScale n)⁻¹ • (MovingFrameODE.tail n' -
scaleDerivative n n' • MovingFrameODE.normalDirection n)`. -/
noncomputable def directionDerivative (n n' : Space) : Plane :=
  (MovingFrameODE.normalScale n)⁻¹ •
    (MovingFrameODE.tail n' - scaleDerivative n n' • MovingFrameODE.normalDirection n)

/-- Angular velocity, given by `⟪MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n),
directionDerivative n n'⟫_ℝ`. -/
noncomputable def angularVelocity (n n' : Space) : ℝ :=
  ⟪MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n), directionDerivative n n'⟫_ℝ

theorem hasDerivAt_normalScale {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : MovingFrameODE.tail (n v) ≠ 0) :
    HasDerivAt (fun s => MovingFrameODE.normalScale (n s)) (scaleDerivative (n v) n') v := by
  have ht : HasDerivAt (fun s => MovingFrameODE.tail (n s)) (MovingFrameODE.tail n') v :=
    MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  have h := ht.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  simpa only [MovingFrameODE.normalScale, scaleDerivative, Real.sqrt_sq_eq_abs, abs_norm,
    mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)] using h

theorem hasDerivAt_radialSlope {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : MovingFrameODE.tail (n v) ≠ 0) :
    HasDerivAt (fun s => MovingFrameODE.radialSlope (n s)) (slopeDerivative (n v) n') v := by
  have hβ := MovingFrameODE.normalScale_pos hne
  let pr : Space →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0
  have hr : HasDerivAt (fun s => (n s) 0) (n' 0) v :=
    pr.hasFDerivAt.comp_hasDerivAt v hn
  have heq : slopeDerivative (n v) n' =
      (n' 0 * MovingFrameODE.normalScale (n v) - (n v) 0 * scaleDerivative (n v) n') /
        MovingFrameODE.normalScale (n v) ^ 2 := by
    unfold slopeDerivative MovingFrameODE.radialSlope
    field_simp [hβ.ne']
  rw [heq]
  exact hr.div (hasDerivAt_normalScale hn hne) hβ.ne'

theorem hasDerivAt_normalDirection {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : MovingFrameODE.tail (n v) ≠ 0) :
    HasDerivAt (fun s => MovingFrameODE.normalDirection (n s)) (directionDerivative (n v) n') v :=
        by
  have hβ := MovingFrameODE.normalScale_pos hne
  have ht : HasDerivAt (fun s => MovingFrameODE.tail (n s)) (MovingFrameODE.tail n') v :=
    MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  convert! ((hasDerivAt_normalScale hn hne).fun_inv hβ.ne').smul ht using 1
  unfold directionDerivative MovingFrameODE.normalDirection
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hβ.ne']; ring

/-- The angular speed is computed from the actual normal derivative. -/
theorem hasDerivAt_actual_frame {n : ℝ → Space} {n' : Space} {v : ℝ}
    (hn : HasDerivAt n n' v) (hne : MovingFrameODE.tail (n v) ≠ 0) :
    HasDerivAt (fun s => MovingFrameODE.normalDirection (n s))
      (angularVelocity (n v) n' • MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n
          v))) v ∧
    HasDerivAt (fun s => MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n s)))
      (-angularVelocity (n v) n' • MovingFrameODE.normalDirection (n v)) v := by
  have ht : HasDerivAt (fun s => MovingFrameODE.tail (n s)) (MovingFrameODE.tail n') v :=
    MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  have hunit : ∀ᶠ s in nhds v, ‖MovingFrameODE.normalDirection (n s)‖ = 1 := by
    have he : ∀ᶠ s in nhds v, MovingFrameODE.tail (n s) ≠ 0 := ht.continuousAt.eventually_ne hne
    filter_upwards [he] with s hs
    exact MovingFrameODE.normalDirection_unit hs
  have hd := hasDerivAt_normalDirection hn hne
  have hrot := MovingFrameODE.unit_curve_rotation hd hunit
  have hk : HasDerivAt (fun s => MovingFrameODE.normalDirection (n s))
      (angularVelocity (n v) n' • MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n
          v))) v :=
    hrot ▸ hd
  exact ⟨hk, MovingFrameODE.hasDerivAt_quarterTurn_of_rotation hk⟩

theorem scaleDerivative_bound {n n' : Space} (hne : MovingFrameODE.tail n ≠ 0) :
    |scaleDerivative n n'| ≤ ‖n'‖ := by
  have hβ := MovingFrameODE.normalScale_pos hne
  unfold scaleDerivative
  rw [abs_div, abs_of_pos hβ]
  calc
    _ ≤ (‖MovingFrameODE.tail n‖ * ‖MovingFrameODE.tail n'‖) / MovingFrameODE.normalScale n :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hβ.le
    _ = ‖MovingFrameODE.tail n'‖ := by
      change (MovingFrameODE.normalScale n * ‖MovingFrameODE.tail n'‖) / MovingFrameODE.normalScale
          n = _
      exact mul_div_cancel_left₀ _ hβ.ne'
    _ ≤ ‖n'‖ := tail_norm_le n'

theorem slopeDerivative_bound {n n' : Space} {B η : ℝ}
    (hB : 0 < B) (hlow : B / 2 ≤ MovingFrameODE.normalScale n) (hn' : ‖n'‖ ≤ η) :
    |slopeDerivative n n'| ≤ 2 * (1 + |MovingFrameODE.radialSlope n|) * η / B := by
  have hβ : 0 < MovingFrameODE.normalScale n := lt_of_lt_of_le (half_pos hB) hlow
  have hne : MovingFrameODE.tail n ≠ 0 := norm_pos_iff.mp hβ
  have hη : 0 ≤ η := (norm_nonneg _).trans hn'
  have hr : |n' 0| ≤ η := by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le n' 0).trans hn'
  have hb : |scaleDerivative n n'| ≤ η := (scaleDerivative_bound hne).trans hn'
  unfold slopeDerivative
  rw [abs_div, abs_of_pos hβ]
  calc
    _ ≤ (|n' 0| + |MovingFrameODE.radialSlope n * scaleDerivative n n'|) /
        MovingFrameODE.normalScale n :=
      div_le_div_of_nonneg_right (abs_sub _ _) hβ.le
    _ ≤ (η + |MovingFrameODE.radialSlope n| * η) / MovingFrameODE.normalScale n := by
      rw [abs_mul]
      exact div_le_div_of_nonneg_right
        (add_le_add hr (mul_le_mul_of_nonneg_left hb (abs_nonneg _))) hβ.le
    _ ≤ (η + |MovingFrameODE.radialSlope n| * η) / (B / 2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos hB) hlow
    _ = _ := by ring

theorem directionDerivative_bound {n n' : Space} {B η : ℝ}
    (hB : 0 < B) (hlow : B / 2 ≤ MovingFrameODE.normalScale n) (hn' : ‖n'‖ ≤ η) :
    ‖directionDerivative n n'‖ ≤ 4 * η / B := by
  have hβ : 0 < MovingFrameODE.normalScale n := lt_of_lt_of_le (half_pos hB) hlow
  have hne : MovingFrameODE.tail n ≠ 0 := norm_pos_iff.mp hβ
  have hη : 0 ≤ η := (norm_nonneg _).trans hn'
  have hb : |scaleDerivative n n'| ≤ η := (scaleDerivative_bound hne).trans hn'
  have ht : ‖MovingFrameODE.tail n'‖ ≤ η := (tail_norm_le n').trans hn'
  have hs : ‖MovingFrameODE.tail n' - scaleDerivative n n' • MovingFrameODE.normalDirection n‖ ≤ 2
      * η := by
    have h := norm_sub_le (MovingFrameODE.tail n') (scaleDerivative n n' •
        MovingFrameODE.normalDirection n)
    rw [norm_smul, Real.norm_eq_abs, MovingFrameODE.normalDirection_unit hne, mul_one] at h
    linarith only [h, hb, ht]
  unfold directionDerivative
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
  calc
    _ ≤ (MovingFrameODE.normalScale n)⁻¹ * (2 * η) := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr
        hβ.le)
    _ = 2 * η / MovingFrameODE.normalScale n := by ring
    _ ≤ 2 * η / (B / 2) := div_le_div_of_nonneg_left (by positivity) (half_pos hB) hlow
    _ = _ := by ring

theorem angularVelocity_bound {n n' : Space} {B η : ℝ}
    (hB : 0 < B) (hlow : B / 2 ≤ MovingFrameODE.normalScale n) (hn' : ‖n'‖ ≤ η) :
    |angularVelocity n n'| ≤ 4 * η / B := by
  have hβ : 0 < MovingFrameODE.normalScale n := lt_of_lt_of_le (half_pos hB) hlow
  have hne : MovingFrameODE.tail n ≠ 0 := norm_pos_iff.mp hβ
  unfold angularVelocity
  have h := abs_real_inner_le_norm
    (MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection n)) (directionDerivative n n')
  rw [quarterTurn_norm, MovingFrameODE.normalDirection_unit hne, one_mul] at h
  exact h.trans (directionDerivative_bound hB hlow hn')

/-! ## The actual local base hypotheses -/

/-- Local C1/C2 bounds on the given base and its order-zero limit.  These are
derivative bounds on actual functions, not a normal-comparison hypothesis. -/
structure LocalBaseBounds (F G F0 G0 : Slow → ℝ) (U : Set Slow) (M ε : ℝ) : Prop where
  convex : Convex ℝ U
  actualF : ∀ x ∈ U, DifferentiableAt ℝ F x
  actualG : ∀ x ∈ U, DifferentiableAt ℝ G x
  referenceF : ∀ x ∈ U, DifferentiableAt ℝ F0 x
  referenceG : ∀ x ∈ U, DifferentiableAt ℝ G0 x
  secondF : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ F0) x
  secondG : ∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ G0) x
  secondF_bound : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ F0) x‖ ≤ M
  secondG_bound : ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ G0) x‖ ≤ M
  firstF_bound : ∀ x ∈ U, ‖fderiv ℝ F0 x‖ ≤ M
  valueF_error : ∀ x ∈ U, |F x - F0 x| ≤ M * ε ^ 2
  firstF_error : ∀ x ∈ U, ‖fderiv ℝ F x - fderiv ℝ F0 x‖ ≤ M * ε ^ 2
  firstG_error : ∀ x ∈ U, ‖fderiv ℝ G x - fderiv ℝ G0 x‖ ≤ M * ε ^ 2
  radialF_bound : ∀ x ∈ U, |PhaseCalculus.slowR F x| ≤ M
  axialF_bound : ∀ x ∈ U, |PhaseCalculus.slowZ F x| ≤ M
  axialG_bound : ∀ x ∈ U, |PhaseCalculus.slowZ G x| ≤ M

theorem localBase_derivative_errors {F G F0 G0 : Slow → ℝ} {U : Set Slow}
    {M ε diameter : ℝ} {q q0 : Slow} (h : LocalBaseBounds F G F0 G0 U M ε)
    (hM : 0 ≤ M) (hq : q ∈ U) (hq0 : q0 ∈ U) (hd : ‖q - q0‖ ≤ diameter) :
    |PhaseCalculus.slowR F q - PhaseCalculus.slowR F0 q0| ≤ M * (diameter + ε ^ 2) ∧
    |PhaseCalculus.slowR G q - PhaseCalculus.slowR G0 q0| ≤ M * (diameter + ε ^ 2) := by
  have he : ‖((1, (0, 0)) : Slow)‖ ≤ 1 := by norm_num
  have hF := local_directional_derivative_close hM h.convex hq hq0 h.secondF h.secondF_bound
    hd (h.firstF_error q hq) he
  have hG := local_directional_derivative_close hM h.convex hq hq0 h.secondG h.secondG_bound
    hd (h.firstG_error q hq) he
  simpa only [PhaseCalculus.slowR, mul_add] using And.intro hF hG

theorem localBase_value_error {F G F0 G0 : Slow → ℝ} {U : Set Slow}
    {M ε diameter : ℝ} {q q0 : Slow} (h : LocalBaseBounds F G F0 G0 U M ε)
    (hM : 0 ≤ M) (hq : q ∈ U) (hq0 : q0 ∈ U) (hd : ‖q - q0‖ ≤ diameter) :
    |F q - F0 q0| ≤ M * (diameter + ε ^ 2) := by
  have hlocal := h.convex.norm_image_sub_le_of_norm_fderiv_le h.referenceF h.firstF_bound hq0 hq
  have hloc : |F0 q - F0 q0| ≤ M * diameter := by
    simpa only [Real.norm_eq_abs] using hlocal.trans (mul_le_mul_of_nonneg_left hd hM)
  calc
    _ ≤ |F q - F0 q| + |F0 q - F0 q0| := abs_sub_le _ _ _
    _ ≤ M * ε ^ 2 + M * diameter := add_le_add (h.valueF_error q hq) hloc
    _ = _ := by ring

theorem radius_difference_le {q q0 : Slow} {diameter : ℝ} (hd : ‖q - q0‖ ≤ diameter) :
    |q.1 - q0.1| ≤ diameter := by
  simpa only [Prod.fst_sub, Real.norm_eq_abs] using (norm_fst_le (q - q0)).trans hd

/-- Shear vector, given by `!₂[q.1 * PhaseCalculus.slowR F q, PhaseCalculus.slowR G q]`. -/
noncomputable def shearVector (F G : Slow → ℝ) (q : Slow) : Plane :=
  !₂[q.1 * PhaseCalculus.slowR F q, PhaseCalculus.slowR G q]

theorem localBase_shear_error {F G F0 G0 : Slow → ℝ} {U : Set Slow}
    {M ε diameter : ℝ} {q q0 : Slow} (h : LocalBaseBounds F G F0 G0 U M ε)
    (hM : 1 ≤ M) (hq : q ∈ U) (hq0 : q0 ∈ U) (hd : ‖q - q0‖ ≤ diameter)
    (hR0 : |q0.1| ≤ M) :
    ‖shearVector F G q - shearVector F0 G0 q0‖ ≤ 4 * M ^ 2 * (diameter + ε ^ 2) := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hd0 : 0 ≤ diameter := (norm_nonneg _).trans hd
  obtain ⟨hF, hG⟩ := localBase_derivative_errors h hM0 hq hq0 hd
  have hR := radius_difference_le hd
  have ha : |q.1 * PhaseCalculus.slowR F q - q0.1 * PhaseCalculus.slowR F0 q0| ≤
      M * diameter + M ^ 2 * (diameter + ε ^ 2) := by
    calc
      _ = |(q.1 - q0.1) * PhaseCalculus.slowR F q +
          q0.1 * (PhaseCalculus.slowR F q - PhaseCalculus.slowR F0 q0)| := by congr 1; ring
      _ ≤ |(q.1 - q0.1) * PhaseCalculus.slowR F q| +
          |q0.1 * (PhaseCalculus.slowR F q - PhaseCalculus.slowR F0 q0)| := abs_add_le _ _
      _ = |q.1 - q0.1| * |PhaseCalculus.slowR F q| +
          |q0.1| * |PhaseCalculus.slowR F q - PhaseCalculus.slowR F0 q0| := by rw [abs_mul, abs_mul]
      _ ≤ diameter * M + M * (M * (diameter + ε ^ 2)) := add_le_add
        (mul_le_mul hR (h.radialF_bound q hq) (abs_nonneg _) hd0)
        (mul_le_mul hR0 hF (abs_nonneg _) hM0)
      _ = _ := by ring
  have hn := MovingFrameODE.plane_norm_le_coordinate_sum (shearVector F G q - shearVector F0 G0 q0)
  change ‖shearVector F G q - shearVector F0 G0 q0‖ ≤
    |q.1 * PhaseCalculus.slowR F q - q0.1 * PhaseCalculus.slowR F0 q0| +
    |PhaseCalculus.slowR G q - PhaseCalculus.slowR G0 q0| at hn
  have hm2 : M ≤ M ^ 2 := by nlinarith only [hM]
  have he0 : 0 ≤ diameter + ε ^ 2 := add_nonneg hd0 (sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_right hm2 he0
  have hd' : M * diameter ≤ M * (diameter + ε ^ 2) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) hM0
  nlinarith only [hn, ha, hG, hh, hd', mul_nonneg (sq_nonneg M) he0]

/-- The principal estimate stated for the actual PhaseCalculus normal, with
local C1/C2 hypotheses and the actual punctured-lattice rounded frequency. -/
theorem actual_phase_estimates
    {F G F0 G0 : Slow → ℝ} {U : Set Slow} {q q0 : Slow}
    {ε target pz v θ B sigma u L M S k : ℝ} {K : Plane}
    (hbase : LocalBaseBounds F G F0 G0 U M ε)
    (hq : q ∈ U) (hq0 : q0 ∈ U) (hdiameter : ‖q - q0‖ ≤ 1 / S ^ 3)
    (hR : q.1 ≠ 0) (hR0 : q0.1 ≠ 0)
    (hg : shearVector F0 G0 q0 ≠ 0) (horth : ⟪K, shearVector F0 G0 q0⟫_ℝ = 0)
    (hfreq : (!₂[target / q0.1, pz] : Plane) =
      representativeFrequency B sigma u L K (shearVector F0 G0 q0))
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 1 ≤ k) (hε : 0 < ε)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (hB : |B| ≤ M)
    (hsigma : |sigma| = 1) (hu : |u| ≤ M) (hgi : 1 / ‖shearVector F0 G0 q0‖ ≤ M)
    (hL : 1 / |L| ≤ M / S) (hv : |v| ≤ M * S)
    (hRi : |1 / q.1| ≤ M) (hR0i : |1 / q0.1| ≤ M) :
    ‖PhaseCalculus.phaseNormal ε (roundedFrequency k target) pz (sigma * B * u / 2) F G (q, (θ, v))
        -
      referenceNormal B sigma u L v K‖ ≤ phaseConstant M * phaseError S ε k ∧
    ‖PhaseCalculus.normalSlotDerivative ε (roundedFrequency k target) pz F G q‖ ≤
      phaseConstant M * phaseError S ε k := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  obtain ⟨hFR, hGR⟩ := localBase_derivative_errors hbase hM0 hq hq0 hdiameter
  have h := rounded_normal_estimates hR hR0 hg horth (rfl : shearVector F0 G0 q0 = _)
    hfreq hM hS hk hε.le htarget hpz hB hsigma hu hgi hL hv hRi hR0i
    (radius_difference_le hdiameter) (hbase.radialF_bound q hq) (hbase.axialF_bound q hq)
    (hbase.axialG_bound q hq) hFR hGR
  rw [phaseNormal_eq_explicit ε (roundedFrequency k target) pz (sigma * B * u / 2)
    F G (q, (θ, v)) hε.ne' (hbase.actualF q hq) (hbase.actualG q hq)]
  exact h

/-- Punctured-lattice rounding itself already excludes exact zeros of the
tangential normal; the comparison estimate supplies the uniform lower bound. -/
theorem phase_normal_nonvanishing {ε k target pz x0 : ℝ} {F G : Slow → ℝ}
    {q : PhaseCalculus.Slot} (hε : ε ≠ 0) (hk : k ≠ 0) (hR : q.1.1 ≠ 0)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    MovingFrameODE.tail (PhaseCalculus.phaseNormal ε (roundedFrequency k target) pz x0 F G q) ≠ 0 ∧
    PhaseCalculus.phaseNormal ε (roundedFrequency k target) pz x0 F G q ≠ 0 := by
  rw [phaseNormal_eq_explicit ε (roundedFrequency k target) pz x0 F G q hε hF hG]
  have hp := div_ne_zero (roundedFrequency_ne_zero hk target) hR
  constructor
  · intro hz
    have h := congrArg (fun w : Plane => w 0) hz
    exact hp h
  · intro hz
    have h := congrArg (fun w : Space => w 1) hz
    exact hp h

/-- The phase's actual derivative, uniform lower bounds and every changing
frame quantity needed in `MovingFrameODE`, from local base and band data. -/
theorem actual_phase_geometry
    {F G F0 G0 : Slow → ℝ} {U : Set Slow} {q q0 : Slow}
    {ε target pz v θ B sigma u L M S k : ℝ} {K : Plane}
    (hbase : LocalBaseBounds F G F0 G0 U M ε)
    (hq : q ∈ U) (hq0 : q0 ∈ U) (hdiameter : ‖q - q0‖ ≤ 1 / S ^ 3)
    (hR : q.1 ≠ 0) (hR0 : q0.1 ≠ 0)
    (hg : shearVector F0 G0 q0 ≠ 0) (horth : ⟪K, shearVector F0 G0 q0⟫_ℝ = 0)
    (hfreq : (!₂[target / q0.1, pz] : Plane) =
      representativeFrequency B sigma u L K (shearVector F0 G0 q0))
    (hM : 1 ≤ M) (hS : 1 ≤ S) (hk : 1 ≤ k) (hε : 0 < ε)
    (htarget : |target| ≤ M) (hpz : |pz| ≤ M) (hB : |B| ≤ M)
    (hsigma : |sigma| = 1) (hu : |u| ≤ M) (hgi : 1 / ‖shearVector F0 G0 q0‖ ≤ M)
    (hL : 1 / |L| ≤ M / S) (hv : |v| ≤ M * S)
    (hRi : |1 / q.1| ≤ M) (hR0i : |1 / q0.1| ≤ M)
    (hBpos : 0 < B) (hK : ‖K‖ = 1)
    (hsmall : phaseConstant M * phaseError S ε k ≤ B / 2) :
    let N : ℝ → Space := fun w => PhaseCalculus.phaseNormal ε (roundedFrequency k target) pz
      (sigma * B * u / 2) F G (q, (θ, w))
    let n' := PhaseCalculus.normalSlotDerivative ε (roundedFrequency k target) pz F G q
    let δ := phaseConstant M * phaseError S ε k
    HasDerivAt N n' v ∧
    B / 2 ≤ MovingFrameODE.normalScale (N v) ∧ B / 2 ≤ ‖N v‖ ∧
    MovingFrameODE.tail (N v) ≠ 0 ∧ N v ≠ 0 ∧
    |MovingFrameODE.radialSlope (N v) - signedSlot sigma u L v| ≤
      2 * (1 + |signedSlot sigma u L v|) * δ / B ∧
    ‖MovingFrameODE.normalDirection (N v) - K‖ ≤ 4 * δ / B ∧
    ‖MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (N v)) - MovingFrameODE.quarterTurn
        K‖ ≤
      4 * δ / B ∧
    |slopeDerivative (N v) n'| ≤ 2 * (1 + |MovingFrameODE.radialSlope (N v)|) * δ / B ∧
    |angularVelocity (N v) n'| ≤ 4 * δ / B := by
  dsimp only
  obtain ⟨hc, hd⟩ := actual_phase_estimates (v := v) (θ := θ) hbase hq hq0 hdiameter
    hR hR0 hg horth hfreq hM hS hk hε htarget hpz hB hsigma hu hgi hL hv hRi hR0i
  have hl := normal_lower_bounds (s := signedSlot sigma u L v) hBpos hK hsmall hc
  refine ⟨?_, hl.1, hl.2.1, hl.2.2.1, hl.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact PhaseCalculus.hasDerivAt_phaseNormal_slot ε (roundedFrequency k target) pz
      (sigma * B * u / 2) θ v F G q hε.ne' (hbase.actualF q hq) (hbase.actualG q hq)
  · exact radialSlope_close hBpos hK hsmall hc
  · exact normalDirection_close hBpos hK hsmall hc
  · exact transverseDirection_close hBpos hK hsmall hc
  · exact slopeDerivative_bound hBpos hl.1 hd
  · exact angularVelocity_bound hBpos hl.1 hd

theorem signedSlot_bound {sigma u L v : ℝ}
    (hsigma : |sigma| = 1) (hu : 0 ≤ u) (hL : 0 < L) (hv : 0 ≤ v) (hvL : v ≤ L) :
    |signedSlot sigma u L v| ≤ 3 * u / 2 := by
  have hvdiv : v / L ≤ 1 := (div_le_one hL).2 hvL
  have hnonneg : 0 ≤ u / 2 + u * v / L := by positivity
  unfold signedSlot
  rw [abs_mul, hsigma, one_mul, abs_of_nonneg hnonneg]
  have h := mul_le_mul_of_nonneg_left hvdiv hu
  simp only [mul_one] at h
  rw [mul_div_assoc]
  nlinarith only [h]

theorem radialSlope_uniform_bound {n : Space} {K : Plane} {B s δ A : ℝ}
    (hB : 0 < B) (hK : ‖K‖ = 1) (hδ : δ ≤ B / 2)
    (hclose : ‖n - MovingFrameODE.pack (B * s) (B • K)‖ ≤ δ) (hs : |s| ≤ A) :
    |MovingFrameODE.radialSlope n| ≤ 1 + 2 * A := by
  have hc := radialSlope_close hB hK hδ hclose
  have hscale : 2 * (1 + |s|) * δ / B ≤ 1 + |s| := by
    apply (div_le_iff₀ hB).2
    have h := mul_le_mul_of_nonneg_left hδ (show 0 ≤ 2 * (1 + |s|) by positivity)
    nlinarith only [h]
  have h := abs_add_le (MovingFrameODE.radialSlope n - s) s
  rw [sub_add_cancel] at h
  linarith only [hc, hscale, h, hs]

/-- The representative frequencies are bounded uniformly before rounding;
the bound follows from the specified frequency formula. -/
theorem representative_uniform_frequency_bounds
    {B sigma u L M S R0 target pz : ℝ} {K g : Plane}
    (hR0 : R0 ≠ 0) (hM : 0 ≤ M) (hS : 1 ≤ S)
    (hB : |B| ≤ M) (hsigma : |sigma| = 1) (hu : |u| ≤ M)
    (hg : 1 / ‖g‖ ≤ M) (hL : 1 / |L| ≤ M / S) (hK : ‖K‖ = 1)
    (hRbound : |R0| ≤ M)
    (hfreq : (!₂[target / R0, pz] : Plane) = representativeFrequency B sigma u L K g) :
    |target| ≤ M * (M + M ^ 4) ∧ |pz| ≤ M + M ^ 4 := by
  have htilt := representative_tilt_scaled hM hB hsigma hu hg hL
  have hinv : M ^ 4 / S ≤ M ^ 4 :=
    (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hS)).2 (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hS (pow_nonneg hM 4))
  have hf : ‖representativeFrequency B sigma u L K g‖ ≤ M + M ^ 4 := by
    exact (representative_frequency_bound B sigma u L K g hK).trans
      (add_le_add hB (htilt.trans hinv))
  have h0 := (PiLp.norm_apply_le (representativeFrequency B sigma u L K g) 0).trans hf
  have h1 := (PiLp.norm_apply_le (representativeFrequency B sigma u L K g) 1).trans hf
  rw [← hfreq] at h0 h1
  have htarget : |target / R0| ≤ M + M ^ 4 := by simpa [abs_div] using h0
  constructor
  · have heq : target = R0 * (target / R0) := by field_simp
    calc
      |target| = |R0| * |target / R0| := by nth_rw 1 [heq]; rw [abs_mul]
      _ ≤ M * (M + M ^ 4) := mul_le_mul hRbound htarget (abs_nonneg _) hM
  · simpa using h1

theorem chart_carrier_ge_one (h : ℝ) (n : ℕ) : 1 ≤ (ChartScales.carrier h n : ℝ) := by
  have hk : 0 < (ChartScales.carrier h n : ℝ) :=
    Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h n)
  have hn : 0 < ChartScales.carrier h n := by exact_mod_cast hk
  exact_mod_cast Nat.succ_le_of_lt hn

theorem chart_S_tendsto_atTop : Tendsto ChartScales.S atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The band conditions used in the finite estimate hold on the actual
dyadic scale and actual ceiling-rounded carrier. -/
theorem eventually_band_conditions (h : ℝ) (hh : 0 < h) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ ChartScales.S n ∧
      ChartScales.S n ^ 2 * ChartScales.epsilon h n ^ 2 ≤ 1 ∧
      ChartScales.S n ^ 2 / (ChartScales.carrier h n : ℝ) ≤ 1 ∧
      ChartScales.epsilon h n * ChartScales.S n ^ 2 ≤ 1 := by
  have hS := chart_S_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have h2 := ChartScales.eventually_slow_power_epsilon_lt h hh 2 2 1 (by norm_num) (by norm_num)
  have h1 := ChartScales.eventually_slow_power_epsilon_lt h hh 2 1 1 (by norm_num) (by norm_num)
  have hk := (tendsto_order.1 (ChartScales.slow_power_div_carrier_tendsto_zero h hh 2)).2 1 (by
      norm_num)
  filter_upwards [hS, h2, hk, h1] with n hn hn2 hnk hn1
  refine ⟨hn, ?_, ?_, ?_⟩
  · simpa only [Real.rpow_two] using hn2.le
  · simpa only [Real.rpow_two] using hnk.le
  · simpa only [Real.rpow_two, Real.rpow_one, mul_comm] using hn1.le

theorem eventually_phaseError_le (h : ℝ) (hh : 0 < h) :
    ∀ᶠ n : ℕ in atTop,
      phaseError (ChartScales.S n) (ChartScales.epsilon h n) (ChartScales.carrier h n) ≤
        4 / ChartScales.S n := by
  filter_upwards [eventually_band_conditions h hh] with n hn
  exact phaseError_le_four_div (lt_of_lt_of_le zero_lt_one hn.1) hn.2.1 hn.2.2.1 hn.2.2.2

/-- Any fixed positive representative lower bound eventually dominates the
derived normal error.  This is a cutoff conclusion, not an assumed comparison. -/
theorem eventually_error_small (h : ℝ) (hh : 0 < h) {C B : ℝ} (hC : 0 ≤ C) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop,
      C * phaseError (ChartScales.S n) (ChartScales.epsilon h n) (ChartScales.carrier h n) ≤ B / 2
          := by
  have hS := chart_S_tendsto_atTop.eventually (eventually_ge_atTop (max 1 (8 * C / B)))
  filter_upwards [hS, eventually_phaseError_le h hh] with n hn he
  have hS1 : 1 ≤ ChartScales.S n := (le_max_left _ _).trans hn
  have hS0 : 0 < ChartScales.S n := lt_of_lt_of_le zero_lt_one hS1
  have hthreshold : 8 * C / B ≤ ChartScales.S n := (le_max_right _ _).trans hn
  have hb := (div_le_iff₀ hB).mp hthreshold
  calc
    _ ≤ C * (4 / ChartScales.S n) := mul_le_mul_of_nonneg_left he hC
    _ = (4 * C) / ChartScales.S n := by ring
    _ ≤ B / 2 := (div_le_iff₀ hS0).mpr (by nlinarith only [hb])

end NavierStokes.PhaseEstimates
