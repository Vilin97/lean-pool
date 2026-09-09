/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TangentODE
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaussianEnvelope
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The actual growing mode stays in a narrow cone

The invariant region is proved using a quadratic boundary function, without
dividing by the growing coordinate or assuming its positivity along the solution.
-/

namespace NavierStokes.GrowingMode

open Set Filter
open scoped Topology

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
