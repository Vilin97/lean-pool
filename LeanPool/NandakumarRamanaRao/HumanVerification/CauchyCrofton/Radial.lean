/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.HumanVerification.CauchyCrofton.Basic

/-!
# Radial boundary points of a planar convex body

For a compact convex body `K` in the plane containing the origin in its interior we define

* `rad K θ`, the largest `t ≥ 0` with `t • circleVec θ ∈ K`;
* `radPt K θ = rad K θ • circleVec θ`, the corresponding boundary point.

The main tool of the whole development is the *blocking lemma* `blocking`: if two points of `K`
lie on rays whose directions span at most a half turn, the radial boundary point in any
intermediate direction dominates the corresponding convex combination of linear values.

We also record the planar cross product and the trigonometric identity expressing a direction
lying between two others as a nonnegative combination of them.
-/

open Set MeasureTheory NRR.Geometry
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace HumanVerification.CauchyCrofton

/-! ### Planar cross product -/

/-- The planar cross product. -/
def cross (x y : Point2) : ℝ := x 0 * y 1 - x 1 * y 0

/-- Rotation by a quarter turn. -/
def rot (x : Point2) : Point2 := !₂[-x 1, x 0]

@[simp] theorem inner_rot (x y : Point2) : (inner ℝ y (rot x) : ℝ) = cross x y := by
  simp [rot, cross, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem cross_smul_left (a : ℝ) (x y : Point2) : cross (a • x) y = a * cross x y := by
  simp [cross]; ring

theorem cross_smul_right (a : ℝ) (x y : Point2) : cross x (a • y) = a * cross x y := by
  simp [cross]; ring

theorem cross_add_right (x y z : Point2) : cross x (y + z) = cross x y + cross x z := by
  simp [cross]; ring

theorem cross_add_left (x y z : Point2) : cross (x + y) z = cross x z + cross y z := by
  simp [cross]; ring

theorem cross_self (x : Point2) : cross x x = 0 := by simp [cross]; ring

theorem cross_circleVec (α β : ℝ) : cross (circleVec α) (circleVec β) = Real.sin (β - α) := by
  simp [cross, circleVec, Real.sin_sub]
  ring

theorem rot_ne_zero {x : Point2} (hx : x ≠ 0) : rot x ≠ 0 := by
  intro h
  apply hx
  have h0 : (rot x) 0 = 0 := by rw [h]; simp
  have h1 : (rot x) 1 = 0 := by rw [h]; simp
  simp [rot] at h0 h1
  ext i
  fin_cases i <;> simp [h0, h1]

/-! ### Elementary planar trigonometry -/

/-- The fundamental cone identity: `sin (γ-β) • u α + sin (β-α) • u γ = sin (γ-α) • u β`. -/
theorem circleVec_cone_identity (α β γ : ℝ) :
    Real.sin (γ - β) • circleVec α + Real.sin (β - α) • circleVec γ
      = Real.sin (γ - α) • circleVec β := by
  ext i
  fin_cases i <;> simp [circleVec, Real.sin_sub] <;> ring

/-- Inner product of two circle vectors. -/
theorem inner_circleVec_circleVec (α β : ℝ) :
    (inner ℝ (circleVec α) (circleVec β) : ℝ) = Real.cos (β - α) := by
  simp [circleVec, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]

/-- Every nonzero planar vector is a positive multiple of some `circleVec θ`, and the angle can
be chosen in any half-open period window. -/
theorem exists_angle (x : Point2) (c : ℝ) :
    ∃ θ ∈ Set.Ico c (c + 2 * Real.pi), x = ‖x‖ • circleVec θ := by
  set z : ℂ := ⟨x 0, x 1⟩ with hz
  have hnorm : ‖z‖ = ‖x‖ := by
    rw [Complex.norm_def, Complex.normSq_mk, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, sq_abs]
    ring_nf
  have hxarg : x = ‖x‖ • circleVec z.arg := by
    have h1 := Complex.norm_mul_cos_arg z
    have h2 := Complex.norm_mul_sin_arg z
    rw [hnorm] at h1 h2
    ext i
    fin_cases i <;> simp [circleVec] <;> simp [hz] at h1 h2 <;> linarith
  refine ⟨toIcoMod Real.two_pi_pos c z.arg, toIcoMod_mem_Ico _ _ _, ?_⟩
  have heq : toIcoMod Real.two_pi_pos c z.arg
      = z.arg - (toIcoDiv Real.two_pi_pos c z.arg) • (2 * Real.pi) := by
    have h := toIcoMod_sub_self Real.two_pi_pos c z.arg
    rw [neg_smul] at h
    linarith
  rw [heq, circleVec_periodic.sub_zsmul_eq]
  exact hxarg

/-- A nonnegative combination of two circle vectors spanning less than a half-turn is a
nonnegative multiple of a circle vector with intermediate angle. -/
theorem exists_angle_mem_Icc_of_nonneg_combination
    {α γ : ℝ} (hαγ : α < γ) (hlt : γ - α < Real.pi) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hne : A • circleVec α + B • circleVec γ ≠ 0) :
    ∃ β ∈ Set.Icc α γ, A • circleVec α + B • circleVec γ
      = ‖A • circleVec α + B • circleVec γ‖ • circleVec β := by
  have hsγα : 0 < Real.sin (γ - α) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt
  set y : Point2 := A • circleVec α + B • circleVec γ with hy
  have hynorm : 0 < ‖y‖ := norm_pos_iff.2 hne
  obtain ⟨β, hβmem, hβ⟩ := exists_angle y α
  refine ⟨β, ⟨hβmem.1, ?_⟩, hβ⟩
  -- first cross product : `sin (β - α) ≥ 0`
  have hc1 : cross (circleVec α) y = ‖y‖ * Real.sin (β - α) := by
    conv_lhs => rw [hβ]
    rw [cross_smul_right, cross_circleVec]
  have hc1' : cross (circleVec α) y = B * Real.sin (γ - α) := by
    rw [hy, cross_add_right, cross_smul_right, cross_smul_right, cross_self,
      cross_circleVec]
    ring
  have hs1 : 0 ≤ Real.sin (β - α) := by
    have : 0 ≤ ‖y‖ * Real.sin (β - α) := by
      rw [← hc1, hc1']
      positivity
    nlinarith
  have hβπ : β - α ≤ Real.pi := by
    by_contra hcon
    push Not at hcon
    have h2 : β - α - Real.pi < Real.pi := by
      have := hβmem.2
      simp only [Set.mem_Ico] at *
      linarith
    have hneg : Real.sin (β - α) < 0 := by
      have hpos := Real.sin_pos_of_pos_of_lt_pi (x := β - α - Real.pi) (by linarith) h2
      have : Real.sin (β - α) = -Real.sin (β - α - Real.pi) := by
        rw [show β - α = (β - α - Real.pi) + Real.pi by ring, Real.sin_add_pi]
        ring_nf
      rw [this]
      linarith
    linarith
  -- second cross product : `sin (γ - β) ≥ 0`
  have hc2 : cross y (circleVec γ) = ‖y‖ * Real.sin (γ - β) := by
    conv_lhs => rw [hβ]
    rw [cross_smul_left, cross_circleVec]
  have hc2' : cross y (circleVec γ) = A * Real.sin (γ - α) := by
    rw [hy, cross_add_left, cross_smul_left, cross_smul_left, cross_self,
      cross_circleVec]
    ring
  have hs2 : 0 ≤ Real.sin (γ - β) := by
    have : 0 ≤ ‖y‖ * Real.sin (γ - β) := by
      rw [← hc2, hc2']
      positivity
    nlinarith
  by_contra hcon
  push Not at hcon
  have hneg : Real.sin (γ - β) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  linarith

/-- Two angles with the same circle vector differ by a multiple of a full turn. -/
theorem circleVec_eq_iff_exists {t s : ℝ} (h : circleVec t = circleVec s) :
    ∃ q : ℤ, s = t + q * (2 * Real.pi) := by
  have h1 : Real.cos t = Real.cos s := by
    have := congrArg (fun z : Point2 => z 0) h
    simpa [circleVec] using this
  have h2 : Real.sin t = Real.sin s := by
    have := congrArg (fun z : Point2 => z 1) h
    simpa [circleVec] using this
  have hcos : Real.cos (s - t) = 1 := by
    rw [Real.cos_sub, h1, h2]
    have := Real.sin_sq_add_cos_sq s
    nlinarith
  rw [Real.cos_eq_one_iff] at hcos
  obtain ⟨n, hn⟩ := hcos
  exact ⟨n, by linarith [hn]⟩

/-- The circle parametrization is `1`-Lipschitz. -/
theorem norm_circleVec_sub_le (a b : ℝ) : ‖circleVec a - circleVec b‖ ≤ |a - b| := by
  have hsq : ‖circleVec a - circleVec b‖ ^ 2 = 2 - 2 * Real.cos (a - b) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_circleVec_circleVec]
    rw [show a - a = 0 by ring, show b - b = 0 by ring, Real.cos_zero]
    have : Real.cos (a - b) = Real.cos (b - a) := by
      rw [← Real.cos_neg (b - a)]; ring_nf
    rw [this]
    ring
  have hcos : 2 - 2 * Real.cos (a - b) ≤ (a - b) ^ 2 := by
    rcases eq_or_ne (a - b) 0 with h | h
    · rw [h, Real.cos_zero]; norm_num
    · have := Real.one_sub_sq_div_two_lt_cos h
      nlinarith
  have h1 : ‖circleVec a - circleVec b‖ ^ 2 ≤ |a - b| ^ 2 := by
    rw [hsq, sq_abs]; exact hcos
  have h2 : 0 ≤ ‖circleVec a - circleVec b‖ := norm_nonneg _
  nlinarith [abs_nonneg (a - b)]

/-! ### The radial function -/

/-- The set of admissible radii in direction `circleVec θ`. -/
def radSet (K : Body) (θ : ℝ) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ t • circleVec θ ∈ (K : Set Point2)}

/-- The radial function of `K`: the largest `t ≥ 0` with `t • circleVec θ ∈ K`. -/
def rad (K : Body) (θ : ℝ) : ℝ := sSup (radSet K θ)

/-- The radial boundary point of `K` in direction `circleVec θ`. -/
def radPt (K : Body) (θ : ℝ) : Point2 := rad K θ • circleVec θ

theorem radPt_eq (K : Body) (θ : ℝ) : radPt K θ = rad K θ • circleVec θ := rfl

variable {K : Body}

theorem radSet_nonempty (h0 : (0 : Point2) ∈ (K : Set Point2)) (θ : ℝ) :
    (radSet K θ).Nonempty := ⟨0, by simpa [radSet] using h0⟩

theorem bddAbove_radSet (θ : ℝ) : BddAbove (radSet K θ) := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point2)
  refine ⟨R, fun t ht => ?_⟩
  have := hR ht.2
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_circleVec, mul_one,
    Real.norm_eq_abs, abs_of_nonneg ht.1] at this
  exact this

theorem isClosed_radSet (θ : ℝ) : IsClosed (radSet K θ) := by
  have : radSet K θ = Set.Ici (0 : ℝ) ∩ (fun t : ℝ => t • circleVec θ) ⁻¹' (K : Set Point2) := by
    ext t; simp [radSet, Set.mem_Ici]
  rw [this]
  exact isClosed_Ici.inter (K.isCompact.isClosed.preimage (by fun_prop))

theorem rad_mem_radSet (h0 : (0 : Point2) ∈ (K : Set Point2)) (θ : ℝ) :
    rad K θ ∈ radSet K θ :=
  (isClosed_radSet θ).csSup_mem (radSet_nonempty h0 θ) (bddAbove_radSet θ)

theorem rad_nonneg (h0 : (0 : Point2) ∈ (K : Set Point2)) (θ : ℝ) : 0 ≤ rad K θ :=
  (rad_mem_radSet h0 θ).1

theorem radPt_mem (h0 : (0 : Point2) ∈ (K : Set Point2)) (θ : ℝ) :
    radPt K θ ∈ (K : Set Point2) := (rad_mem_radSet h0 θ).2

/-- Maximality of the radial function. -/
theorem le_rad {t : ℝ} {θ : ℝ} (ht : 0 ≤ t) (htK : t • circleVec θ ∈ (K : Set Point2)) :
    t ≤ rad K θ := le_csSup (bddAbove_radSet θ) ⟨ht, htK⟩

theorem rad_pos (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (θ : ℝ) : 0 < rad K θ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hmem : (ε / 2) • circleVec θ ∈ (K : Set Point2) := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, norm_circleVec, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / 2)]
    linarith
  have := le_rad (by positivity : (0:ℝ) ≤ ε / 2) hmem
  linarith

theorem norm_radPt (h0 : (0 : Point2) ∈ (K : Set Point2)) (θ : ℝ) :
    ‖radPt K θ‖ = rad K θ := by
  rw [radPt, norm_smul, norm_circleVec, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (rad_nonneg h0 θ)]

theorem radPt_ne_zero (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (θ : ℝ) :
    radPt K θ ≠ 0 := by
  intro h
  have := norm_radPt (interior_subset h0) θ
  rw [h, norm_zero] at this
  exact absurd this.symm (rad_pos h0 θ).ne'

/-- The radial boundary point really is a boundary point. -/
theorem radPt_mem_frontier (h0 : (0 : Point2) ∈ interior (K : Set Point2)) (θ : ℝ) :
    radPt K θ ∈ frontier (K : Set Point2) := by
  rw [K.isCompact.isClosed.frontier_eq]
  refine ⟨radPt_mem (interior_subset h0) θ, ?_⟩
  intro hint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ hint
  have hmem : (rad K θ + ε / 2) • circleVec θ ∈ (K : Set Point2) := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, radPt, ← sub_smul, norm_smul, norm_circleVec, mul_one,
      Real.norm_eq_abs]
    have : rad K θ + ε / 2 - rad K θ = ε / 2 := by ring
    rw [this, abs_of_nonneg (by positivity : (0:ℝ) ≤ ε / 2)]
    linarith
  have hnn : (0:ℝ) ≤ rad K θ + ε / 2 := by
    have := rad_nonneg (interior_subset h0) θ
    linarith
  have := le_rad hnn hmem
  linarith

/-- `2π`-periodicity of the radial function. -/
theorem rad_periodic (θ : ℝ) : rad K (θ + 2 * Real.pi) = rad K θ := by
  have : radSet K (θ + 2 * Real.pi) = radSet K θ := by
    simp [radSet, circleVec_periodic θ]
  rw [rad, rad, this]

theorem radPt_periodic (θ : ℝ) : radPt K (θ + 2 * Real.pi) = radPt K θ := by
  rw [radPt, radPt, rad_periodic, circleVec_periodic θ]

/-! ### The blocking lemma -/

/-- **Blocking lemma, basic form.** If a point `x` of `K` lies on the ray with direction
`circleVec β` at positive distance and has nonnegative inner product with `n`, then the radial
boundary point in direction `β` has at least as large an inner product with `n`. -/
theorem inner_le_inner_radPt {β μ : ℝ} (hμ : 0 < μ)
    (hx : μ • circleVec β ∈ (K : Set Point2)) {n : Point2}
    (hn : 0 ≤ (inner ℝ (μ • circleVec β) n : ℝ)) :
    (inner ℝ (μ • circleVec β) n : ℝ) ≤ (inner ℝ (radPt K β) n : ℝ) := by
  have hle : μ ≤ rad K β := le_rad hμ.le hx
  rw [real_inner_smul_left] at hn ⊢
  rw [radPt, real_inner_smul_left]
  have hc : 0 ≤ (inner ℝ (circleVec β) n : ℝ) := nonneg_of_mul_nonneg_right hn hμ
  exact mul_le_mul_of_nonneg_right hle hc

/-- **Blocking lemma.** Let `α < β < γ` with `γ - α ≤ π`, and let `a • circleVec α` and
`c • circleVec γ` be points of `K` (with `a, c > 0`) whose inner products with `n` are both
positive.  Then the radial boundary point in the intermediate direction `β` dominates a strict
convex combination of the two inner products. -/
theorem blocking {α β γ : ℝ} (hαβ : α < β) (hβγ : β < γ) (hlt : γ - α ≤ Real.pi)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hx : a • circleVec α ∈ (K : Set Point2)) (hy : c • circleVec γ ∈ (K : Set Point2))
    {n : Point2}
    (hxn : 0 < (inner ℝ (a • circleVec α) n : ℝ))
    (hyn : 0 < (inner ℝ (c • circleVec γ) n : ℝ)) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧
      (1 - lam) * (inner ℝ (a • circleVec α) n : ℝ)
          + lam * (inner ℝ (c • circleVec γ) n : ℝ)
        ≤ (inner ℝ (radPt K β) n : ℝ) := by
  have hβα : 0 < β - α := by linarith
  have hγβ : 0 < γ - β := by linarith
  have hp : 0 < Real.sin (γ - β) :=
    Real.sin_pos_of_pos_of_lt_pi hγβ (by linarith)
  have hq : 0 < Real.sin (β - α) :=
    Real.sin_pos_of_pos_of_lt_pi hβα (by linarith)
  have hsnn : 0 ≤ Real.sin (γ - α) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) hlt
  have hid := circleVec_cone_identity α β γ
  have hXa : 0 < (inner ℝ (circleVec α) n : ℝ) := by
    rw [real_inner_smul_left] at hxn; nlinarith
  have hYc : 0 < (inner ℝ (circleVec γ) n : ℝ) := by
    rw [real_inner_smul_left] at hyn; nlinarith
  rcases eq_or_lt_of_le hsnn with hs0 | hspos
  · exfalso
    have := congrArg (fun z : Point2 => (inner ℝ z n : ℝ)) hid
    simp only [inner_add_left, real_inner_smul_left, ← hs0, zero_mul] at this
    nlinarith
  · set S : ℝ := Real.sin (γ - β) / a + Real.sin (β - α) / c with hS
    have hSpos : 0 < S := by positivity
    refine ⟨(Real.sin (β - α) / c) / S, by positivity, ?_, ?_⟩
    · rw [div_lt_one hSpos, hS]
      have : 0 < Real.sin (γ - β) / a := by positivity
      linarith
    · set lam : ℝ := (Real.sin (β - α) / c) / S with hlam
      have hlam0 : 0 < lam := by positivity
      have hlam1 : lam < 1 := by
        rw [hlam, div_lt_one hSpos, hS]
        have : 0 < Real.sin (γ - β) / a := by positivity
        linarith
      have hcomb : (1 - lam) • (a • circleVec α) + lam • (c • circleVec γ)
          = (Real.sin (γ - α) / S) • circleVec β := by
        rw [smul_smul, smul_smul]
        have e1 : (1 - lam) * a = Real.sin (γ - β) / S := by
          rw [hlam, hS]; field_simp; ring
        have e2 : lam * c = Real.sin (β - α) / S := by
          rw [hlam, hS]; field_simp
        rw [e1, e2, div_eq_inv_mul (Real.sin (γ - β)), div_eq_inv_mul (Real.sin (β - α)),
          div_eq_inv_mul (Real.sin (γ - α)), ← smul_smul, ← smul_smul, ← smul_smul,
          ← smul_add, hid]
      have hmem : (Real.sin (γ - α) / S) • circleVec β ∈ (K : Set Point2) := by
        rw [← hcomb]
        exact K.convex hx hy (by linarith) hlam0.le (by ring)
      have hμ : 0 < Real.sin (γ - α) / S := by positivity
      have hinner : (inner ℝ ((Real.sin (γ - α) / S) • circleVec β) n : ℝ)
          = (1 - lam) * (inner ℝ (a • circleVec α) n : ℝ)
            + lam * (inner ℝ (c • circleVec γ) n : ℝ) := by
        rw [← hcomb]
        simp [inner_add_left, real_inner_smul_left]
      have hnn : 0 ≤ (inner ℝ ((Real.sin (γ - α) / S) • circleVec β) n : ℝ) := by
        rw [hinner]; nlinarith
      have := inner_le_inner_radPt hμ hmem hnn
      rw [hinner] at this
      exact this

/-- Convenient corollary of `blocking`: the radial point in an intermediate direction strictly
exceeds the smaller of two positive values, when the larger one is strict. -/
theorem lt_inner_radPt_of_blocking {α β γ : ℝ} (hαβ : α < β) (hβγ : β < γ)
    (hlt : γ - α ≤ Real.pi) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hx : a • circleVec α ∈ (K : Set Point2)) (hy : c • circleVec γ ∈ (K : Set Point2))
    {n : Point2} {d : ℝ} (hd : 0 < d)
    (hxn : d ≤ (inner ℝ (a • circleVec α) n : ℝ))
    (hyn : d < (inner ℝ (c • circleVec γ) n : ℝ)) :
    d < (inner ℝ (radPt K β) n : ℝ) := by
  obtain ⟨lam, hlam0, hlam1, hle⟩ :=
    blocking hαβ hβγ hlt ha hc hx hy (lt_of_lt_of_le hd hxn) (lt_trans hd hyn)
  nlinarith

/-- Variant of `lt_inner_radPt_of_blocking` with the strict bound on the left. -/
theorem lt_inner_radPt_of_blocking' {α β γ : ℝ} (hαβ : α < β) (hβγ : β < γ)
    (hlt : γ - α ≤ Real.pi) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hx : a • circleVec α ∈ (K : Set Point2)) (hy : c • circleVec γ ∈ (K : Set Point2))
    {n : Point2} {d : ℝ} (hd : 0 < d)
    (hxn : d < (inner ℝ (a • circleVec α) n : ℝ))
    (hyn : d ≤ (inner ℝ (c • circleVec γ) n : ℝ)) :
    d < (inner ℝ (radPt K β) n : ℝ) := by
  obtain ⟨lam, hlam0, hlam1, hle⟩ :=
    blocking hαβ hβγ hlt ha hc hx hy (lt_trans hd hxn) (lt_of_lt_of_le hd hyn)
  nlinarith

/-- Weak version of `lt_inner_radPt_of_blocking`. -/
theorem le_inner_radPt_of_blocking {α β γ : ℝ} (hαβ : α < β) (hβγ : β < γ)
    (hlt : γ - α ≤ Real.pi) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hx : a • circleVec α ∈ (K : Set Point2)) (hy : c • circleVec γ ∈ (K : Set Point2))
    {n : Point2} {d : ℝ} (hd : 0 < d)
    (hxn : d ≤ (inner ℝ (a • circleVec α) n : ℝ))
    (hyn : d ≤ (inner ℝ (c • circleVec γ) n : ℝ)) :
    d ≤ (inner ℝ (radPt K β) n : ℝ) := by
  obtain ⟨lam, hlam0, hlam1, hle⟩ :=
    blocking hαβ hβγ hlt ha hc hx hy (lt_of_lt_of_le hd hxn) (lt_of_lt_of_le hd hyn)
  nlinarith

end HumanVerification.CauchyCrofton
