/-
Copyright (c) 2026 Dirk Kunert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dirk Kunert
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Aperiodicity of the projected gap sequence for irrational slopes

This file formalizes the aperiodicity proposition of the companion paper
"Period lengths of one-dimensional rational cut-and-project sequences",
Section "The Irrational Case". For positive irrational
slope `a` and window parameter `ω > 0`, the projected gap sequence
on the accepted lattice points has no finite period.

The proof has three steps:
  1. The physical projection `tildeP(x,y) = x + a*y` is injective on `ℤ²`.
  2. A finite period of the gap sequence lifts to a non-zero
     translation `v ∈ ℤ²` that preserves the accepted set `A`.
  3. Such a translation must induce a non-zero internal shift `τ`
     that preserves `W ∩ s(ℤ²)`; Kronecker density on `ℝ` rules
     this out, forcing `v = 0` and contradicting Step 2.
-/

open Set Function

namespace CutAndProject.Irrational

/-! ### Section A. Notation and accepted set -/

variable (a ω : ℝ)

/-- Physical (signed-position) projection used in the irrational
case: `tildeP(x,y) = x + a*y`. -/
def tildeP : ℤ × ℤ → ℝ := fun z => (z.1 : ℝ) + a * (z.2 : ℝ)

/-- Internal coordinate: `s(x,y) = y - a*x`. -/
def sInternal : ℤ × ℤ → ℝ := fun z => (z.2 : ℝ) - a * (z.1 : ℝ)

/-- Internal window `W = [-a*ω, ω]`. -/
def W : Set ℝ := Set.Icc (-(a * ω)) ω

/-- Accepted lattice points: those whose internal coordinate lies in `W`. -/
def acceptedSet : Set (ℤ × ℤ) := {z | sInternal a z ∈ W a ω}

/-! ### Section B. Step 1: `tildeP` is injective on `ℤ²` -/

theorem tildeP_injective (ha : Irrational a) :
    Function.Injective (tildeP a) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  -- h : tildeP a (x₁, y₁) = tildeP a (x₂, y₂)
  -- i.e. (x₁ : ℝ) + a * y₁ = (x₂ : ℝ) + a * y₂
  simp only [tildeP] at h
  by_cases hy : y₁ = y₂
  · -- y₁ = y₂ forces x₁ = x₂
    subst hy
    have hx : (x₁ : ℝ) = (x₂ : ℝ) := by linarith
    exact Prod.ext (by exact_mod_cast hx) rfl
  · -- y₁ ≠ y₂ ⟹ a is rational, contradicting `Irrational a`
    exfalso
    -- Rearrange h to:  a * ((y₁ - y₂ : ℤ) : ℝ) = ((x₂ - x₁ : ℤ) : ℝ)
    have hne : (y₁ : ℝ) - y₂ ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hy
    -- a = (x₂ - x₁) / (y₁ - y₂)
    have ha_eq : a = ((x₂ - x₁ : ℤ) : ℝ) / ((y₁ - y₂ : ℤ) : ℝ) := by
      push_cast
      field_simp [hne]
      linarith
    -- Express a as a rational number
    apply ha
    -- division evaluated in ℚ after push_cast, not as truncated Int division
    refine ⟨(x₂ - x₁ : ℤ) / (y₁ - y₂ : ℤ), ?_⟩
    rw [ha_eq]
    push_cast
    rfl

/-! ### Section C. Kronecker density of `ℤ + a·ℤ` -/

/-- For irrational `a`, the set `{n - a*m : m, n ∈ ℤ}` is dense in `ℝ`. -/
theorem dense_internal_image (ha : Irrational a) :
    Dense (Set.range (sInternal a)) := by
  -- Step 1: the range equals the closure of {-a, 1} as a subgroup of ℝ
  have hrange : Set.range (sInternal a) = (AddSubgroup.closure ({-a, 1} : Set ℝ) : Set ℝ) := by
    ext z
    simp only [Set.mem_range, SetLike.mem_coe, AddSubgroup.mem_closure_pair]
    constructor
    · rintro ⟨⟨m, n⟩, rfl⟩
      -- sInternal a (m, n) = n - a*m = m • (-a) + n • 1
      exact ⟨m, n, by simp only [sInternal, zsmul_eq_mul]; ring⟩
    · rintro ⟨m, n, hmn⟩
      -- m • (-a) + n • 1 = -m*a + n = n - a*m = sInternal a (m, n)
      exact ⟨⟨m, n⟩, by simp only [sInternal, zsmul_eq_mul] at hmn ⊢; linarith⟩
  -- Step 2: density of the closure follows from irrationality via Mathlib's theorem
  rw [hrange, dense_addSubgroupClosure_pair_iff]
  rw [div_one]; rwa [irrational_neg_iff]

/-! ### Section D. Local finiteness of the projected accepted set -/

/-- The preimage in `ℤ²` of any bounded interval, intersected with the
accepted set, is finite.

Proof sketch.  For `(x, y)` in the set we have
`s := y - a*x ∈ [-a*ω, ω]` and `p := x + a*y ∈ [b₁, b₂]`.  Inverting the
linear system gives `x = (p - a*s)/(1+a²)` and `y = (a*p + s)/(1+a²)`,
so both `x` and `y` are bounded by an explicit real constant.  Since
`x, y : ℤ` lie in a bounded subset of `ℝ`, they lie in a finite box. -/
theorem accepted_preimage_finite
    (hω : 0 < ω) (b₁ b₂ : ℝ) :
    Set.Finite {z ∈ acceptedSet a ω | tildeP a z ∈ Set.Icc b₁ b₂} := by
  -- Set up the determinant `D = 1 + a²` and a uniform real bound `B` on `|x|`, `|y|`.
  set D : ℝ := 1 + a ^ 2 with hD_def
  have hD_pos : 0 < D := by
    have h1 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
    linarith
  -- Bound `|s|` by `Bs := |a|*ω + ω` (loose but explicit).
  set Bs : ℝ := |a| * ω + ω with hBs_def
  have hBs_nn : 0 ≤ Bs := by
    have : 0 ≤ |a| * ω := mul_nonneg (abs_nonneg a) hω.le
    linarith
  -- Bound `|p|` by `Bp := |b₁| + |b₂|` (loose but explicit).
  set Bp : ℝ := |b₁| + |b₂| with hBp_def
  have hBp_nn : 0 ≤ Bp := by
    have h1 : 0 ≤ |b₁| := abs_nonneg _
    have h2 : 0 ≤ |b₂| := abs_nonneg _
    linarith
  -- Combined real bound on |x| and |y|.
  set R : ℝ := (1 + |a|) * (Bp + Bs) with hR_def
  have hR_nn : 0 ≤ R := by
    have h1 : 0 ≤ 1 + |a| := by have := abs_nonneg a; linarith
    have h2 : 0 ≤ Bp + Bs := by linarith
    exact mul_nonneg h1 h2
  -- Integer cap for the box.
  set N : ℤ := ⌈R⌉ with hN_def
  -- The set is a subset of `Set.Icc (-N) N ×ˢ Set.Icc (-N) N`.
  apply Set.Finite.subset
    (Set.Finite.prod (Set.finite_Icc (-N) N) (Set.finite_Icc (-N) N))
  rintro ⟨x, y⟩ ⟨hAcc, hP⟩
  -- Unpack hypotheses.
  have hs_mem : sInternal a (x, y) ∈ W a ω := hAcc
  rcases hs_mem with ⟨hs_lo, hs_hi⟩
  -- hs_lo : -(a * ω) ≤ y - a*x
  -- hs_hi : y - a*x ≤ ω
  have hs_lo' : -(a * ω) ≤ (y : ℝ) - a * x := hs_lo
  have hs_hi' : (y : ℝ) - a * x ≤ ω := hs_hi
  rcases hP with ⟨hp_lo, hp_hi⟩
  -- hp_lo : b₁ ≤ x + a*y
  -- hp_hi : x + a*y ≤ b₂
  have hp_lo' : b₁ ≤ (x : ℝ) + a * y := hp_lo
  have hp_hi' : (x : ℝ) + a * y ≤ b₂ := hp_hi
  -- Bound |s| by Bs.
  have habs_s : |(y : ℝ) - a * x| ≤ Bs := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · -- -Bs ≤ y - a*x
      have h1 : -(|a| * ω) ≤ -(a * ω) := by
        have : a * ω ≤ |a| * ω := by
          have habs : a ≤ |a| := le_abs_self a
          exact mul_le_mul_of_nonneg_right habs hω.le
        linarith
      have h2 : -(|a| * ω) - ω ≤ -(a * ω) := by linarith
      have h3 : -Bs = -(|a| * ω) - ω := by simp only [hBs_def]; ring
      linarith
    · -- y - a*x ≤ Bs
      have : ω ≤ Bs := by
        have : 0 ≤ |a| * ω := mul_nonneg (abs_nonneg a) hω.le
        simp only [hBs_def]; linarith
      linarith
  -- Bound |p| by Bp.
  have habs_p : |(x : ℝ) + a * y| ≤ Bp := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · -- -Bp ≤ x + a*y
      have h1 : -|b₁| ≤ b₁ := neg_abs_le b₁
      have h2 : -|b₂| ≤ 0 := neg_nonpos_of_nonneg (abs_nonneg b₂)
      have : -Bp = -|b₁| + -|b₂| := by simp only [hBp_def]; ring
      linarith
    · -- x + a*y ≤ Bp
      have h1 : b₂ ≤ |b₂| := le_abs_self b₂
      have h2 : 0 ≤ |b₁| := abs_nonneg b₁
      have : Bp = |b₁| + |b₂| := rfl
      linarith
  -- Identity: D * x = p - a * s, hence |x| ≤ (Bp + |a|*Bs)/D ≤ R.
  have hDx : D * (x : ℝ) = ((x : ℝ) + a * y) - a * ((y : ℝ) - a * x) := by
    simp only [hD_def]; ring
  have hDy : D * (y : ℝ) = a * ((x : ℝ) + a * y) + ((y : ℝ) - a * x) := by
    simp only [hD_def]; ring
  -- From these identities, real-value bound on |x| and |y|.
  have habs_Dx : |D * (x : ℝ)| ≤ Bp + |a| * Bs := by
    rw [hDx]
    have htri : |((x : ℝ) + a * y) - a * ((y : ℝ) - a * x)|
              ≤ |((x : ℝ) + a * y)| + |a * ((y : ℝ) - a * x)| := by
      have h := abs_add_le ((x : ℝ) + a * y) (-(a * ((y : ℝ) - a * x)))
      have heq : ((x : ℝ) + a * y) + -(a * ((y : ℝ) - a * x))
              = ((x : ℝ) + a * y) - a * ((y : ℝ) - a * x) := by ring
      rw [heq] at h
      have habs_neg : |-(a * ((y : ℝ) - a * x))| = |a * ((y : ℝ) - a * x)| := abs_neg _
      rw [habs_neg] at h
      exact h
    have hmulabs : |a * ((y : ℝ) - a * x)| = |a| * |(y : ℝ) - a * x| := abs_mul _ _
    have h2 : |a| * |(y : ℝ) - a * x| ≤ |a| * Bs :=
      mul_le_mul_of_nonneg_left habs_s (abs_nonneg a)
    linarith
  have habs_Dy : |D * (y : ℝ)| ≤ |a| * Bp + Bs := by
    rw [hDy]
    have htri : |a * ((x : ℝ) + a * y) + ((y : ℝ) - a * x)|
              ≤ |a * ((x : ℝ) + a * y)| + |((y : ℝ) - a * x)| :=
      abs_add_le _ _
    have hmulabs : |a * ((x : ℝ) + a * y)| = |a| * |((x : ℝ) + a * y)| := abs_mul _ _
    have h1 : |a| * |((x : ℝ) + a * y)| ≤ |a| * Bp :=
      mul_le_mul_of_nonneg_left habs_p (abs_nonneg a)
    linarith
  -- D ≥ 1 since a² ≥ 0
  have hD_ge_one : (1 : ℝ) ≤ D := by
    change 1 ≤ 1 + a ^ 2; linarith [sq_nonneg a]
  -- Algebraic fact: both `Bp + |a|*Bs` and `|a|*Bp + Bs` are ≤ R = (1+|a|)*(Bp+Bs).
  have hbound_x : Bp + |a| * Bs ≤ R := by
    have h1 : 0 ≤ |a| * Bp := mul_nonneg (abs_nonneg _) hBp_nn
    simp only [hR_def]; nlinarith
  have hbound_y : |a| * Bp + Bs ≤ R := by
    have h1 : 0 ≤ |a| * Bs := mul_nonneg (abs_nonneg _) hBs_nn
    simp only [hR_def]; nlinarith
  -- |x| ≤ R, |y| ≤ R.
  have habs_x : |(x : ℝ)| ≤ R := by
    have hx1 : |D * (x : ℝ)| = D * |(x : ℝ)| := by
      rw [abs_mul, abs_of_pos hD_pos]
    have hx2 : D * |(x : ℝ)| ≤ Bp + |a| * Bs := by rw [← hx1]; exact habs_Dx
    have hx3 : 1 * |(x : ℝ)| ≤ D * |(x : ℝ)| :=
      mul_le_mul_of_nonneg_right hD_ge_one (abs_nonneg _)
    have hx4 : |(x : ℝ)| ≤ Bp + |a| * Bs := by
      have : 1 * |(x : ℝ)| = |(x : ℝ)| := one_mul _
      linarith
    linarith
  have habs_y : |(y : ℝ)| ≤ R := by
    have hy1 : |D * (y : ℝ)| = D * |(y : ℝ)| := by
      rw [abs_mul, abs_of_pos hD_pos]
    have hy2 : D * |(y : ℝ)| ≤ |a| * Bp + Bs := by rw [← hy1]; exact habs_Dy
    have hy3 : 1 * |(y : ℝ)| ≤ D * |(y : ℝ)| :=
      mul_le_mul_of_nonneg_right hD_ge_one (abs_nonneg _)
    have hy4 : |(y : ℝ)| ≤ |a| * Bp + Bs := by
      have : 1 * |(y : ℝ)| = |(y : ℝ)| := one_mul _
      linarith
    linarith
  -- Now turn real |x| ≤ R into integer |x| ≤ N (= ⌈R⌉).
  have hRN : R ≤ (N : ℝ) := Int.le_ceil R
  have habs_x_int : |(x : ℝ)| ≤ (N : ℝ) := le_trans habs_x hRN
  have habs_y_int : |(y : ℝ)| ≤ (N : ℝ) := le_trans habs_y hRN
  -- Convert real abs bounds back to integer bounds.
  have habs_x_int' : |x| ≤ N := by
    have : |((x : ℝ))| = ((|x| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
    rw [this] at habs_x_int
    exact_mod_cast habs_x_int
  have habs_y_int' : |y| ≤ N := by
    have : |((y : ℝ))| = ((|y| : ℤ) : ℝ) := by
      rw [Int.cast_abs]
    rw [this] at habs_y_int
    exact_mod_cast habs_y_int
  -- Both coordinates are in [-N, N].
  refine Set.mk_mem_prod ?_ ?_
  · -- x ∈ Set.Icc (-N) N
    simp only [Set.mem_Icc]
    have := abs_le.mp habs_x_int'
    exact this
  · -- y ∈ Set.Icc (-N) N
    simp only [Set.mem_Icc]
    have := abs_le.mp habs_y_int'
    exact this

/-! ### Section E. Bi-infinite unboundedness -/

/-- Auxiliary lemma: for any `ε > 0`, there exist integers `p, q`
with `0 < |sInternal a (p,q)| < ε` and `0 < tildeP a (p,q)`.  Density of
`Set.range (sInternal a)` (Section C) on `Ioo 0 ε` produces `(p, q)` with
`s ∈ (0, ε)`; flipping sign of `(p, q)` if necessary forces `tildeP > 0`. -/
private lemma exists_internal_pos_tildeP_pos
    (ha : Irrational a) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℤ, 0 < |sInternal a (p, q)| ∧ |sInternal a (p, q)| < ε ∧
              0 < tildeP a (p, q) := by
  have hd : Dense (Set.range (sInternal a)) := dense_internal_image a ha
  have hopen : IsOpen (Set.Ioo (0 : ℝ) ε) := isOpen_Ioo
  have hne : (Set.Ioo (0 : ℝ) ε).Nonempty := ⟨ε / 2, by constructor <;> linarith⟩
  obtain ⟨t, ⟨pq, hpq⟩, ht_mem⟩ := hd.exists_mem_open hopen hne
  rcases pq with ⟨p, q⟩
  rcases ht_mem with ⟨ht_pos, ht_lt⟩
  have hs_pos : 0 < sInternal a (p, q) := by rw [hpq]; exact ht_pos
  have hs_lt : sInternal a (p, q) < ε := by rw [hpq]; exact ht_lt
  have habs_s_pos : 0 < |sInternal a (p, q)| := by rw [abs_of_pos hs_pos]; exact hs_pos
  have habs_s_lt : |sInternal a (p, q)| < ε := by rw [abs_of_pos hs_pos]; exact hs_lt
  -- (p, q) ≠ (0, 0) because s(p, q) > 0.
  have hnonzero : (p, q) ≠ (0, 0) := by
    intro heq; apply (ne_of_lt habs_s_pos).symm; rw [heq]; simp [sInternal]
  -- tildeP a (p, q) ≠ 0, else a is rational.
  have hP_ne : tildeP a (p, q) ≠ 0 := by
    intro hP0
    simp only [tildeP] at hP0
    by_cases hq : q = 0
    · subst hq
      have hp0 : (p : ℝ) = 0 := by simpa using hP0
      have hpz : p = 0 := by exact_mod_cast hp0
      exact hnonzero (by simp [hpz])
    · have hq_real : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      apply ha
      refine ⟨-p / q, ?_⟩
      have ha_eq : a = -((p : ℝ) / q) := by field_simp at hP0 ⊢; linarith
      rw [ha_eq]; push_cast; field_simp
  rcases lt_or_gt_of_ne hP_ne with hP_neg | hP_pos
  · refine ⟨-p, -q, ?_, ?_, ?_⟩
    · have h1 : sInternal a (-p, -q) = -sInternal a (p, q) := by
        simp only [sInternal]; push_cast; ring
      rw [h1, abs_neg]; exact habs_s_pos
    · have h1 : sInternal a (-p, -q) = -sInternal a (p, q) := by
        simp only [sInternal]; push_cast; ring
      rw [h1, abs_neg]; exact habs_s_lt
    · have h1 : tildeP a (-p, -q) = -tildeP a (p, q) := by
        simp only [tildeP]; push_cast; ring
      rw [h1]; linarith
  · exact ⟨p, q, habs_s_pos, habs_s_lt, hP_pos⟩

/-- Auxiliary lemma packaging the algebraic core for both the unbounded-above
and unbounded-below theorems.  Given any target `M : ℝ`, returns a positive
integer `K` and a lattice point `(p₀, q₀)` such that `K * tildeP a (p₀, q₀) > M`
and `K * |sInternal a (p₀, q₀)| ≤ min (a * ω) ω`. -/
private lemma exists_scaled_witness
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (M : ℝ) :
    ∃ (K : ℕ) (p₀ q₀ : ℤ), 0 < K ∧
      M < (K : ℝ) * tildeP a (p₀, q₀) ∧
      (K : ℝ) * |sInternal a (p₀, q₀)| ≤ min (a * ω) ω := by
  set δ : ℝ := min (a * ω) ω with hδ_def
  have hδ_pos : 0 < δ := lt_min (mul_pos ha_pos hω) hω
  -- c₀ := 1 + a² - |a| > 0.
  set c₀ : ℝ := 1 + a ^ 2 - |a| with hc₀_def
  have hc₀_pos : 0 < c₀ := by
    have h4 : c₀ = (|a| - 1/2) ^ 2 + 3/4 := by
      have ha_sq : |a| ^ 2 = a ^ 2 := sq_abs a
      simp only [hc₀_def]; rw [← ha_sq]; ring
    rw [h4]; positivity
  -- Choose ε small.
  have hM_abs_nn : 0 ≤ |M| := abs_nonneg _
  set ε : ℝ := min 1 (c₀ * δ / (|M| + 2 * c₀ + 1)) with hε_def
  have hε_pos : 0 < ε := by
    refine lt_min zero_lt_one (div_pos (mul_pos hc₀_pos hδ_pos) ?_)
    positivity
  have hε_le : ε ≤ 1 := min_le_left _ _
  -- Apply density helper.
  obtain ⟨p₀, q₀, h_s_pos, h_s_lt, h_P_pos⟩ :=
    exists_internal_pos_tildeP_pos a ha hε_pos
  set c : ℝ := tildeP a (p₀, q₀) with hc_def
  set s₀ : ℝ := |sInternal a (p₀, q₀)| with hs₀_def
  -- p₀ ≠ 0.
  have hp_ne : p₀ ≠ 0 := by
    intro hp_eq
    have h_s_eq : sInternal a (p₀, q₀) = (q₀ : ℝ) := by simp [sInternal, hp_eq]
    have hq_lt_one : |(q₀ : ℝ)| < 1 := by
      calc |(q₀ : ℝ)| = s₀ := by rw [hs₀_def, h_s_eq]
        _ < ε := h_s_lt
        _ ≤ 1 := hε_le
    have hq_zero : q₀ = 0 := by
      have h_int : (|q₀| : ℝ) = |(q₀ : ℝ)| := by rfl
      have h1 : (|q₀| : ℝ) < 1 := by rw [h_int]; exact hq_lt_one
      have h2 : |q₀| < (1 : ℤ) := by exact_mod_cast h1
      have habs_nn : 0 ≤ |q₀| := abs_nonneg _
      have h3 : |q₀| = 0 := by linarith
      exact abs_eq_zero.mp h3
    have h_s_eq' : sInternal a (p₀, q₀) = 0 := by rw [h_s_eq, hq_zero]; simp
    have : s₀ = 0 := by rw [hs₀_def, h_s_eq']; simp
    linarith
  -- Lower bound c ≥ c₀.
  have hP_decomp : c = (1 + a ^ 2) * (p₀ : ℝ) + a * sInternal a (p₀, q₀) := by
    simp only [hc_def, tildeP, sInternal]; ring
  have habs_p_ge_one : (1 : ℝ) ≤ |(p₀ : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |p₀| := Int.one_le_abs hp_ne
    have h_cast : (|p₀| : ℝ) = |(p₀ : ℝ)| := by rfl
    have h2 : (1 : ℝ) ≤ (|p₀| : ℝ) := by exact_mod_cast h1
    rw [h_cast] at h2; exact h2
  have hc_ge : c₀ ≤ c := by
    -- |c - a*s| = |(1+a²)*p₀| ≥ 1+a²; so c ≥ (1+a²) - |a*s| ≥ 1+a² - |a|.
    have h1 : (1 + a ^ 2) * (p₀ : ℝ) = c - a * sInternal a (p₀, q₀) := by linarith [hP_decomp]
    have h2 : |(1 + a ^ 2) * (p₀ : ℝ)| = (1 + a ^ 2) * |(p₀ : ℝ)| := by
      rw [abs_mul, abs_of_pos]; linarith [sq_nonneg a]
    have h3 : (1 + a ^ 2) ≤ |(1 + a ^ 2) * (p₀ : ℝ)| := by
      rw [h2]
      have h4 : (1 + a ^ 2) * 1 ≤ (1 + a ^ 2) * |(p₀ : ℝ)| :=
        mul_le_mul_of_nonneg_left habs_p_ge_one (by linarith [sq_nonneg a])
      linarith
    have h4 : |c - a * sInternal a (p₀, q₀)| = |(1 + a ^ 2) * (p₀ : ℝ)| := by rw [h1]
    have h5 : (1 + a ^ 2) ≤ |c - a * sInternal a (p₀, q₀)| := h4 ▸ h3
    -- |c - a*s| ≤ |c| + |a|*|s|.
    have h6 : |c - a * sInternal a (p₀, q₀)| ≤ |c| + |a| * s₀ := by
      have h := abs_sub (c) (a * sInternal a (p₀, q₀))
      have h7 : |a * sInternal a (p₀, q₀)| = |a| * s₀ := by rw [abs_mul, hs₀_def]
      linarith [h7 ▸ h]
    -- |a|*s₀ ≤ |a|*1.
    have h7 : |a| * s₀ ≤ |a| := by
      have := mul_le_mul_of_nonneg_left (h_s_lt.le.trans hε_le) (abs_nonneg a)
      linarith
    have h8 : |c| ≥ (1 + a ^ 2) - |a| * s₀ := by linarith
    have h9 : |c| ≥ c₀ - (|a| - |a| * s₀) := by simp only [hc₀_def]; linarith
    rw [abs_of_pos h_P_pos] at h8
    linarith
  -- Choose K.
  set K : ℕ := (⌈M / c⌉.toNat) + 1 with hK_def
  have hK_pos : 0 < K := Nat.succ_pos _
  have hc_pos : 0 < c := h_P_pos
  -- K * c > M.
  have hK_c_gt : M < (K : ℝ) * c := by
    have h_ceil : M / c ≤ ⌈M / c⌉ := Int.le_ceil _
    have h_K_eq : (K : ℝ) = (⌈M / c⌉.toNat : ℝ) + 1 := by
      rw [hK_def]; push_cast; ring
    have h_toNat_ge : ((⌈M / c⌉.toNat : ℤ) : ℝ) ≥ ⌈M / c⌉ := by
      by_cases h : 0 ≤ ⌈M / c⌉
      · rw [Int.toNat_of_nonneg h]
      · push Not at h
        rw [Int.toNat_of_nonpos h.le]
        push_cast
        have hh : ((⌈M/c⌉ : ℤ) : ℝ) < 0 := by exact_mod_cast h
        linarith
    have h_K_real : (K : ℝ) > M / c := by
      have hK_int : (K : ℝ) > (⌈M / c⌉ : ℝ) := by
        rw [h_K_eq]
        have : (⌈M / c⌉.toNat : ℝ) = ((⌈M / c⌉.toNat : ℤ) : ℝ) := by push_cast; rfl
        rw [this]; linarith
      linarith
    rwa [gt_iff_lt, div_lt_iff₀ hc_pos] at h_K_real
  -- K * s₀ ≤ δ.
  have hK_s_le : (K : ℝ) * s₀ ≤ δ := by
    -- K ≤ |M|/c₀ + 2 (since K = ⌈M/c⌉.toNat + 1 ≤ |M/c| + 2 ≤ |M|/c₀ + 2).
    have hK_le_real : (K : ℝ) ≤ |M| / c₀ + 2 := by
      rw [hK_def]; push_cast
      have h_toNat_le : ((⌈M / c⌉.toNat : ℤ) : ℝ) ≤ |M / c| + 1 := by
        by_cases h0 : 0 ≤ ⌈M / c⌉
        · rw [Int.toNat_of_nonneg h0]
          have h_ceil_lt : (⌈M / c⌉ : ℝ) < M / c + 1 := Int.ceil_lt_add_one _
          have h_le_abs : M / c ≤ |M / c| := le_abs_self _
          linarith
        · push Not at h0
          rw [Int.toNat_of_nonpos h0.le]
          push_cast; linarith [abs_nonneg (M / c)]
      have h_abs_div : |M / c| ≤ |M| / c₀ := by
        rw [abs_div, abs_of_pos hc_pos]
        exact div_le_div_of_nonneg_left (abs_nonneg _) hc₀_pos hc_ge
      have h_step : ((⌈M / c⌉.toNat : ℤ) : ℝ) = (⌈M / c⌉.toNat : ℝ) := by push_cast; rfl
      rw [← h_step]
      linarith
    -- s₀ ≤ c₀*δ/(|M|+2c₀+1).
    have h_s₀_le : s₀ ≤ c₀ * δ / (|M| + 2 * c₀ + 1) :=
      le_trans h_s_lt.le (min_le_right _ _)
    -- Combine: K * s₀ ≤ (|M|/c₀ + 2) * (c₀*δ/(|M|+2c₀+1)) = (|M|+2c₀)*δ/(|M|+2c₀+1) ≤ δ.
    have h_denom_pos : 0 < |M| + 2 * c₀ + 1 := by positivity
    have h_K_nn : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
    have h_s₀_nn : 0 ≤ s₀ := h_s_pos.le
    calc (K : ℝ) * s₀
        ≤ (|M| / c₀ + 2) * s₀ := mul_le_mul_of_nonneg_right hK_le_real h_s₀_nn
      _ ≤ (|M| / c₀ + 2) * (c₀ * δ / (|M| + 2 * c₀ + 1)) := by
          apply mul_le_mul_of_nonneg_left h_s₀_le
          have h1 : 0 ≤ |M| / c₀ := div_nonneg hM_abs_nn hc₀_pos.le
          linarith
      _ = (|M| + 2 * c₀) * δ / (|M| + 2 * c₀ + 1) := by
          field_simp
      _ ≤ δ := by
          rw [div_le_iff₀ h_denom_pos]
          nlinarith [hδ_pos.le, hM_abs_nn, hc₀_pos.le]
  refine ⟨K, p₀, q₀, hK_pos, hK_c_gt, ?_⟩
  -- Goal: (K : ℝ) * |sInternal a (p₀, q₀)| ≤ min (a*ω) ω.
  -- Equivalently: (K : ℝ) * s₀ ≤ δ.
  show (K : ℝ) * |sInternal a (p₀, q₀)| ≤ δ
  rw [show |sInternal a (p₀, q₀)| = s₀ from rfl]
  exact hK_s_le

/-- The unboundedness-above main theorem. -/
theorem tildeP_image_unbounded_above
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (M : ℝ) :
    ∃ z ∈ acceptedSet a ω, M < tildeP a z := by
  obtain ⟨K, p₀, q₀, _, hK_c_gt, h_K_s_abs⟩ :=
    exists_scaled_witness a ω ha ha_pos hω M
  refine ⟨((K : ℤ) * p₀, (K : ℤ) * q₀), ?_, ?_⟩
  · -- Show sInternal a (K*p₀, K*q₀) ∈ W.
    change sInternal a ((K : ℤ) * p₀, (K : ℤ) * q₀) ∈ W a ω
    have h_s_eq : sInternal a ((K : ℤ) * p₀, (K : ℤ) * q₀)
                = (K : ℝ) * sInternal a (p₀, q₀) := by
      simp only [sInternal]; push_cast; ring
    rw [h_s_eq]
    have h_abs : |(K : ℝ) * sInternal a (p₀, q₀)| ≤ min (a * ω) ω := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg K)]
      exact h_K_s_abs
    refine ⟨?_, ?_⟩
    · have := abs_le.mp (le_trans h_abs (min_le_left _ _)); exact this.1
    · have := abs_le.mp (le_trans h_abs (min_le_right _ _)); exact this.2
  · have h_P_eq : tildeP a ((K : ℤ) * p₀, (K : ℤ) * q₀)
              = (K : ℝ) * tildeP a (p₀, q₀) := by
      simp only [tildeP]; push_cast; ring
    rw [h_P_eq]; exact hK_c_gt

/-- The unboundedness-below main theorem. -/
theorem tildeP_image_unbounded_below
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (M : ℝ) :
    ∃ z ∈ acceptedSet a ω, tildeP a z < M := by
  obtain ⟨K, p₀, q₀, _, hK_c_gt, h_K_s_abs⟩ :=
    exists_scaled_witness a ω ha ha_pos hω (-M)
  refine ⟨((-(K : ℤ)) * p₀, (-(K : ℤ)) * q₀), ?_, ?_⟩
  · change sInternal a ((-(K : ℤ)) * p₀, (-(K : ℤ)) * q₀) ∈ W a ω
    have h_s_eq : sInternal a ((-(K : ℤ)) * p₀, (-(K : ℤ)) * q₀)
                = -((K : ℝ) * sInternal a (p₀, q₀)) := by
      simp only [sInternal]; push_cast; ring
    rw [h_s_eq]
    have h_abs : |(K : ℝ) * sInternal a (p₀, q₀)| ≤ min (a * ω) ω := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg K)]
      exact h_K_s_abs
    have h_abs_neg : |-((K : ℝ) * sInternal a (p₀, q₀))| ≤ min (a * ω) ω := by
      rw [abs_neg]; exact h_abs
    refine ⟨?_, ?_⟩
    · have := abs_le.mp (le_trans h_abs_neg (min_le_left _ _)); exact this.1
    · have := abs_le.mp (le_trans h_abs_neg (min_le_right _ _)); exact this.2
  · have h_P_eq : tildeP a ((-(K : ℤ)) * p₀, (-(K : ℤ)) * q₀)
              = -((K : ℝ) * tildeP a (p₀, q₀)) := by
      simp only [tildeP]; push_cast; ring
    rw [h_P_eq]; linarith

/-! ### Section F. ℤ-enumeration of the projected accepted set -/

/-! API lemmas for unfolding the Section A definitions. -/

@[simp]
lemma tildeP_apply (m n : ℤ) :
    tildeP a (m, n) = (m : ℝ) + a * (n : ℝ) := rfl

@[simp]
lemma sInternal_apply (m n : ℤ) :
    sInternal a (m, n) = (n : ℝ) - a * (m : ℝ) := rfl

@[simp]
lemma mem_W_iff (x : ℝ) :
    x ∈ W a ω ↔ -(a * ω) ≤ x ∧ x ≤ ω := by
  simp [W, Set.mem_Icc]

@[simp]
lemma mem_acceptedSet_iff (z : ℤ × ℤ) :
    z ∈ acceptedSet a ω ↔ sInternal a z ∈ W a ω := Iff.rfl

/-- The image of the accepted set under the projection. -/
def projectedSet : Set ℝ := tildeP a '' acceptedSet a ω

/-- Bi-infinite enumeration of the projected accepted set.
    The forward map `enumerate i` is the i-th projected lattice point. -/
noncomputable def enumerate
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) :
    ℤ ≃o (projectedSet a ω) := by
  -- LocallyFiniteOrder via the Task-5 finiteness theorem
  letI : LocallyFiniteOrder (projectedSet a ω) :=
    LocallyFiniteOrder.ofFiniteIcc (fun (u v : projectedSet a ω) => by
      -- Show finiteness of `Set.Icc u v` on the subtype.
      -- Step 1: the subtype Icc is finite iff its image under `Subtype.val` is finite,
      -- because `Subtype.val` is injective.
      apply Set.Finite.of_finite_image (f := Subtype.val)
        (hi := Subtype.val_injective.injOn)
      -- Step 2: bound the image by a finite set.
      -- Each `p` in the image equals `tildeP a z` for some `z ∈ acceptedSet`,
      -- with `p ∈ Set.Icc u.val v.val`. Use `accepted_preimage_finite`.
      refine Set.Finite.subset
        ((accepted_preimage_finite a ω hω u.val v.val).image (tildeP a)) ?_
      rintro p ⟨q, hq_mem, rfl⟩
      -- q : projectedSet a ω, hq_mem : q ∈ Set.Icc u v
      -- q.val ∈ projectedSet a ω = tildeP a '' acceptedSet a ω
      obtain ⟨z, hz_acc, hz_eq⟩ := q.property
      refine ⟨z, ⟨hz_acc, ?_⟩, hz_eq⟩
      -- Need: tildeP a z ∈ Set.Icc u.val v.val.
      rw [hz_eq]
      exact ⟨hq_mem.1, hq_mem.2⟩)
  letI : SuccOrder (projectedSet a ω) :=
    LinearLocallyFiniteOrder.succOrder _
  letI : PredOrder (projectedSet a ω) :=
    LinearLocallyFiniteOrder.predOrder _
  -- NoMaxOrder via Section E
  haveI : NoMaxOrder (projectedSet a ω) := ⟨fun u => by
    obtain ⟨z, hz, hp⟩ := tildeP_image_unbounded_above a ω ha ha_pos hω u.val
    refine ⟨⟨tildeP a z, ⟨z, hz, rfl⟩⟩, ?_⟩
    exact hp⟩
  -- NoMinOrder via Section E
  haveI : NoMinOrder (projectedSet a ω) := ⟨fun u => by
    obtain ⟨z, hz, hp⟩ := tildeP_image_unbounded_below a ω ha ha_pos hω u.val
    refine ⟨⟨tildeP a z, ⟨z, hz, rfl⟩⟩, ?_⟩
    exact hp⟩
  -- Nonempty: (0, 0) is accepted because sInternal (0,0) = 0 ∈ W
  haveI : Nonempty (projectedSet a ω) := by
    refine ⟨⟨tildeP a (0, 0), ⟨(0, 0), ?_, rfl⟩⟩⟩
    -- Show (0, 0) ∈ acceptedSet a ω, i.e. 0 ∈ W a ω = [-a*ω, ω]
    rw [mem_acceptedSet_iff, mem_W_iff]
    refine ⟨?_, ?_⟩
    · have : 0 ≤ a * ω := mul_nonneg ha_pos.le hω.le
      simp only [sInternal_apply, Int.cast_zero, mul_zero, sub_zero]
      linarith
    · simp only [sInternal_apply, Int.cast_zero, mul_zero, sub_zero]
      linarith
  -- Final assembly
  exact (orderIsoIntOfLinearSuccPredArch).symm

/-! ### Section G. Gap sequence and periodicity -/

/-- The i-th projected point (= ℓ_i in the paper). -/
noncomputable def ell (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (i : ℤ) : ℝ :=
  ((enumerate a ω ha ha_pos hω) i).val

/-- The i-th gap g_i := ℓ_{i+1} - ℓ_i. -/
noncomputable def gap (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (i : ℤ) : ℝ :=
  ell a ω ha ha_pos hω (i + 1) - ell a ω ha ha_pos hω i

/-- The gap sequence has period λ. -/
def IsGapPeriod (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (lam : ℕ) : Prop :=
  0 < lam ∧ ∀ i : ℤ, gap a ω ha ha_pos hω (i + lam) = gap a ω ha ha_pos hω i

/-- The enumeration is strictly monotone, so ℓ is strictly increasing. -/
lemma ell_strictMono (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) :
    StrictMono (ell a ω ha ha_pos hω) := by
  intro i j hij
  have := (enumerate a ω ha ha_pos hω).strictMono hij
  exact this

/-- Each gap is strictly positive. -/
lemma gap_pos (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (i : ℤ) :
    0 < gap a ω ha ha_pos hω i := by
  unfold gap
  have hlt : i < i + 1 := by linarith
  linarith [ell_strictMono a ω ha ha_pos hω hlt]

/-! ### Section H. Step 2: a finite period lifts to a lattice translation -/

/-- The partial sum of `λ` consecutive gaps starting at `i` is independent of `i`. -/
private lemma telescoping_sum
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (lam : ℕ)
    (hp : IsGapPeriod a ω ha ha_pos hω lam) (i : ℤ) :
    ell a ω ha ha_pos hω (i + lam) - ell a ω ha ha_pos hω i =
      ell a ω ha ha_pos hω (0 + lam) - ell a ω ha ha_pos hω 0 := by
  -- Define the abbreviation `F i := ell(i + lam) - ell i` (locally).
  -- Equivalently, prove `F i = F 0` by induction on `i : ℤ`.
  set F : ℤ → ℝ := fun j => ell a ω ha ha_pos hω (j + lam) - ell a ω ha ha_pos hω j with hF_def
  change F i = F 0
  -- Key step: `F (j + 1) = F j` for all `j : ℤ`, using `gap (j + lam) = gap j`.
  have hstep : ∀ j : ℤ, F (j + 1) = F j := by
    intro j
    have hgap_eq : gap a ω ha ha_pos hω (j + lam) = gap a ω ha ha_pos hω j := hp.2 j
    -- Unfold gap: gap k = ell (k+1) - ell k.
    have h1 : ell a ω ha ha_pos hω (j + lam + 1) - ell a ω ha ha_pos hω (j + lam)
            = ell a ω ha ha_pos hω (j + 1) - ell a ω ha ha_pos hω j := by
      have := hgap_eq
      simp only [gap] at this
      exact this
    -- Now compute F (j+1) - F j and show it is 0.
    simp only [hF_def]
    have hassoc : (j + 1 : ℤ) + (lam : ℤ) = (j + lam) + 1 := by ring
    rw [hassoc]
    linarith
  -- Key step backward: `F (j - 1) = F j` (equivalently `F j = F (j+1)` applied at j-1).
  have hstep' : ∀ j : ℤ, F (j - 1) = F j := by
    intro j
    have := hstep (j - 1)
    have heq : (j - 1 : ℤ) + 1 = j := by ring
    rw [heq] at this
    linarith
  -- Now induct on i.
  induction i with
  | zero => rfl
  | succ n ih =>
    have h := hstep ((n : ℤ))
    -- h : F ((n : ℤ) + 1) = F ((n : ℤ))
    change F ((n : ℤ) + 1) = F 0
    rw [h]; exact ih
  | pred n ih =>
    have h := hstep' (-(n : ℤ))
    -- h : F (-(n : ℤ) - 1) = F (-(n : ℤ))
    change F (-(n : ℤ) - 1) = F 0
    rw [h]; exact ih

/-- Linearity of `tildeP` under addition of lattice points. -/
private lemma tildeP_add (z w : ℤ × ℤ) :
    tildeP a (z + w) = tildeP a z + tildeP a w := by
  rcases z with ⟨m, n⟩
  rcases w with ⟨m', n'⟩
  simp only [Prod.mk_add_mk, tildeP_apply]
  push_cast
  ring

/-- Linearity of `tildeP` under subtraction of lattice points. -/
private lemma tildeP_sub (z w : ℤ × ℤ) :
    tildeP a (z - w) = tildeP a z - tildeP a w := by
  rcases z with ⟨m, n⟩
  rcases w with ⟨m', n'⟩
  simp only [Prod.mk_sub_mk, tildeP_apply]
  push_cast
  ring

/-- The origin lies in the accepted set. -/
private lemma origin_mem_acceptedSet (ha_pos : 0 < a) (hω : 0 < ω) :
    ((0 : ℤ), (0 : ℤ)) ∈ acceptedSet a ω := by
  rw [mem_acceptedSet_iff, mem_W_iff]
  refine ⟨?_, ?_⟩
  · have : 0 ≤ a * ω := mul_nonneg ha_pos.le hω.le
    simp only [sInternal_apply, Int.cast_zero, mul_zero, sub_zero]
    linarith
  · simp only [sInternal_apply, Int.cast_zero, mul_zero, sub_zero]
    linarith

/-- `ell i` lies in the projected set. -/
private lemma ell_mem_projectedSet
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (i : ℤ) :
    ell a ω ha ha_pos hω i ∈ projectedSet a ω :=
  ((enumerate a ω ha ha_pos hω) i).property

/-- **Step 2 of Proposition 1.** If the gap sequence has finite period λ, there is a
non-zero lattice translation `v` with `tildeP v > 0` that preserves `acceptedSet`. -/
theorem period_lifts_to_lattice_translation
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω)
    (lam : ℕ) (hp : IsGapPeriod a ω ha ha_pos hω lam) :
    ∃ v : ℤ × ℤ, v ≠ 0 ∧
      0 < tildeP a v ∧
      ∀ z ∈ acceptedSet a ω, z + v ∈ acceptedSet a ω := by
  -- Step 1: σ := ell (0 + lam) - ell 0 > 0.
  set σ : ℝ := ell a ω ha ha_pos hω (0 + lam) - ell a ω ha ha_pos hω 0 with hσ_def
  have hlam_pos : (0 : ℤ) < (lam : ℤ) := by exact_mod_cast hp.1
  have hσ_pos : 0 < σ := by
    have hlt : (0 : ℤ) < 0 + (lam : ℤ) := by linarith
    have := ell_strictMono a ω ha ha_pos hω hlt
    linarith
  -- Step 2: Base point z₀ = (0, 0) ∈ acceptedSet.
  set z₀ : ℤ × ℤ := (0, 0) with hz₀_def
  have hz₀_acc : z₀ ∈ acceptedSet a ω := origin_mem_acceptedSet a ω ha_pos hω
  -- Step 3: tildeP z₀ ∈ projectedSet, so it equals ell i₀ for some i₀ : ℤ.
  have hP_z₀ : tildeP a z₀ ∈ projectedSet a ω := ⟨z₀, hz₀_acc, rfl⟩
  set i₀ : ℤ := (enumerate a ω ha ha_pos hω).symm ⟨tildeP a z₀, hP_z₀⟩ with hi₀_def
  have h_ell_i₀ : ell a ω ha ha_pos hω i₀ = tildeP a z₀ := by
    -- ell i₀ = ((enumerate ...) i₀).val = ((enumerate ...) ((enumerate ...).symm _)).val
    simp only [ell, hi₀_def, OrderIso.apply_symm_apply]
  -- Step 4: ell (i₀ + lam) = ell i₀ + σ.
  have h_ell_shift : ell a ω ha ha_pos hω (i₀ + lam) = ell a ω ha ha_pos hω i₀ + σ := by
    have h := telescoping_sum a ω ha ha_pos hω lam hp i₀
    linarith
  -- Step 5: Get z₁ ∈ acceptedSet with tildeP z₁ = ell (i₀ + lam).
  have h_in_proj : ell a ω ha ha_pos hω (i₀ + lam) ∈ projectedSet a ω :=
    ell_mem_projectedSet a ω ha ha_pos hω (i₀ + lam)
  obtain ⟨z₁, hz₁_acc, hz₁_eq⟩ := h_in_proj
  -- hz₁_eq : tildeP a z₁ = ell (i₀ + lam)
  -- Step 6: Set v := z₁ - z₀. Then tildeP v = σ.
  set v : ℤ × ℤ := z₁ - z₀ with hv_def
  have h_tildeP_v : tildeP a v = σ := by
    rw [hv_def, tildeP_sub]
    rw [hz₁_eq, h_ell_shift, h_ell_i₀]
    ring
  -- Step 7: The witness.
  refine ⟨v, ?_, ?_, ?_⟩
  · -- v ≠ 0: else tildeP v = 0, contradicting tildeP v = σ > 0.
    intro hv0
    have : tildeP a v = 0 := by rw [hv0]; simp [tildeP]
    rw [h_tildeP_v] at this
    linarith
  · -- 0 < tildeP a v
    rw [h_tildeP_v]; exact hσ_pos
  · -- ∀ z ∈ acceptedSet, z + v ∈ acceptedSet.
    intro z hz_acc
    -- For any z ∈ acceptedSet, tildeP z ∈ projectedSet.
    have hP_z : tildeP a z ∈ projectedSet a ω := ⟨z, hz_acc, rfl⟩
    set i : ℤ := (enumerate a ω ha ha_pos hω).symm ⟨tildeP a z, hP_z⟩ with hi_def
    have h_ell_i : ell a ω ha ha_pos hω i = tildeP a z := by
      simp only [ell, hi_def, OrderIso.apply_symm_apply]
    have h_ell_shift_i : ell a ω ha ha_pos hω (i + lam) = ell a ω ha ha_pos hω i + σ := by
      have h := telescoping_sum a ω ha ha_pos hω lam hp i
      linarith
    -- ell (i + lam) ∈ projectedSet, so equals tildeP z' for some z' ∈ acceptedSet.
    have h_in_proj_i : ell a ω ha ha_pos hω (i + lam) ∈ projectedSet a ω :=
      ell_mem_projectedSet a ω ha ha_pos hω (i + lam)
    obtain ⟨z', hz'_acc, hz'_eq⟩ := h_in_proj_i
    -- tildeP z' = tildeP z + σ.
    have h_P_z' : tildeP a z' = tildeP a z + σ := by
      rw [hz'_eq, h_ell_shift_i, h_ell_i]
    -- tildeP (z + v) = tildeP z + tildeP v = tildeP z + σ = tildeP z'.
    have h_eq : tildeP a (z + v) = tildeP a z' := by
      rw [tildeP_add, h_tildeP_v, h_P_z']
    -- By injectivity, z + v = z', so z + v ∈ acceptedSet.
    have : z + v = z' := tildeP_injective a ha h_eq
    rw [this]
    exact hz'_acc

/-! ### Section I. Step 3: a non-trivial lattice translation cannot
    preserve the accepted set -/

/-- Linearity of `sInternal` under addition of lattice points. -/
private lemma sInternal_add (z w : ℤ × ℤ) :
    sInternal a (z + w) = sInternal a z + sInternal a w := by
  rcases z with ⟨m, n⟩
  rcases w with ⟨m', n'⟩
  simp only [Prod.mk_add_mk, sInternal_apply]
  push_cast
  ring

/-- Linearity of `sInternal` under subtraction of lattice points. -/
private lemma sInternal_sub (z w : ℤ × ℤ) :
    sInternal a (z - w) = sInternal a z - sInternal a w := by
  rcases z with ⟨m, n⟩
  rcases w with ⟨m', n'⟩
  simp only [Prod.mk_sub_mk, sInternal_apply]
  push_cast
  ring

/-- **Step 3 of Proposition 1.** If `v ∈ ℤ²` preserves `acceptedSet` under
addition, then `v = 0`. -/
theorem lattice_translation_must_be_zero
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) (v : ℤ × ℤ)
    (hv_inv : ∀ z ∈ acceptedSet a ω, z + v ∈ acceptedSet a ω) :
    v = 0 := by
  obtain ⟨m, n⟩ := v
  set τ : ℝ := sInternal a (m, n) with hτ_def
  -- Density of `sInternal a` ranges in ℝ.
  have hd : Dense (Set.range (sInternal a)) := dense_internal_image a ha
  -- Step 3a: τ = 0.
  have hτ_zero : τ = 0 := by
    by_contra hτ_ne
    rcases lt_or_gt_of_ne hτ_ne with hτ_neg | hτ_pos
    · -- τ < 0 case: pick t ∈ (-(a*ω), min ω (-(a*ω) - τ)) ∩ range sInternal.
      -- Then t ∈ W but t + τ < -(a*ω), contradicting hv_inv.
      set ub : ℝ := min ω (-(a * ω) - τ) with hub_def
      have hlb_lt_ub : -(a * ω) < ub := by
        have h1 : -(a * ω) < ω := by
          have hpos : 0 < a * ω := mul_pos ha_pos hω
          linarith
        have h2 : -(a * ω) < -(a * ω) - τ := by linarith
        exact lt_min h1 h2
      obtain ⟨t, ⟨z', hz'_eq⟩, ht_lo, ht_hi⟩ := hd.exists_between hlb_lt_ub
      -- ht_lo : -(a*ω) < t
      -- ht_hi : t < ub = min ω (-(a*ω) - τ)
      have ht_lt_ω : t < ω := lt_of_lt_of_le ht_hi (min_le_left _ _)
      have ht_lt_bd : t < -(a * ω) - τ := lt_of_lt_of_le ht_hi (min_le_right _ _)
      -- z' ∈ acceptedSet (since sInternal z' = t ∈ [-(a*ω), ω]).
      have hz'_acc : z' ∈ acceptedSet a ω := by
        rw [mem_acceptedSet_iff, mem_W_iff, hz'_eq]
        exact ⟨ht_lo.le, ht_lt_ω.le⟩
      -- Apply hv_inv: z' + (m, n) ∈ acceptedSet.
      have hsum_acc : z' + (m, n) ∈ acceptedSet a ω := hv_inv z' hz'_acc
      rw [mem_acceptedSet_iff, mem_W_iff, sInternal_add, hz'_eq, ← hτ_def] at hsum_acc
      -- hsum_acc.1 : -(a*ω) ≤ t + τ
      -- but t + τ < -(a*ω) by ht_lt_bd
      have : t + τ < -(a * ω) := by linarith
      linarith [hsum_acc.1]
    · -- τ > 0 case: pick t ∈ (max(-(a*ω), ω - τ), ω) ∩ range sInternal.
      -- Then t ∈ W and t + τ > ω, contradicting hv_inv.
      set lb : ℝ := max (-(a * ω)) (ω - τ) with hlb_def
      have hlb_lt_ub : lb < ω := by
        have h1 : -(a * ω) < ω := by
          have hpos : 0 < a * ω := mul_pos ha_pos hω
          linarith
        have h2 : ω - τ < ω := by linarith
        exact max_lt h1 h2
      obtain ⟨t, ⟨z', hz'_eq⟩, ht_lo, ht_hi⟩ := hd.exists_between hlb_lt_ub
      have ht_gt_neg_aω : -(a * ω) < t := lt_of_le_of_lt (le_max_left _ _) ht_lo
      have ht_gt_ω_sub : ω - τ < t := lt_of_le_of_lt (le_max_right _ _) ht_lo
      have hz'_acc : z' ∈ acceptedSet a ω := by
        rw [mem_acceptedSet_iff, mem_W_iff, hz'_eq]
        exact ⟨ht_gt_neg_aω.le, ht_hi.le⟩
      have hsum_acc : z' + (m, n) ∈ acceptedSet a ω := hv_inv z' hz'_acc
      rw [mem_acceptedSet_iff, mem_W_iff, sInternal_add, hz'_eq, ← hτ_def] at hsum_acc
      -- hsum_acc.2 : t + τ ≤ ω
      -- but t + τ > ω
      have : ω < t + τ := by linarith
      linarith [hsum_acc.2]
  -- Step 3b: from τ = 0, derive m = n = 0.
  have hn_eq : (n : ℝ) = a * (m : ℝ) := by
    have h := hτ_zero
    simp only [hτ_def, sInternal_apply] at h
    linarith
  by_cases hm : m = 0
  · subst hm
    have h0 : (n : ℝ) = 0 := by simpa using hn_eq
    have hn : n = 0 := by exact_mod_cast h0
    simp [hn]
  · exfalso
    apply ha
    refine ⟨(n : ℚ) / (m : ℚ), ?_⟩
    have hm_real : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    push_cast
    field_simp
    linarith

/-! ### Section J. Main theorem: aperiodicity for irrational slope -/

/-- **Aperiodicity (paper: `prop:irrational`, Section "The Irrational Case").**
For `a ∈ ℝ_{>0} ∖ ℚ` and `ω > 0`, the projected gap sequence has
no finite period. -/
theorem prop_irrational
    (ha : Irrational a) (ha_pos : 0 < a) (hω : 0 < ω) :
    ¬ ∃ lam : ℕ, IsGapPeriod a ω ha ha_pos hω lam := by
  rintro ⟨lam, hp⟩
  obtain ⟨v, hv_ne, _, hv_inv⟩ :=
    period_lifts_to_lattice_translation a ω ha ha_pos hω lam hp
  exact hv_ne (lattice_translation_must_be_zero a ω ha ha_pos hω v hv_inv)

/-- **Companion injectivity claim (`prop:irrational`).**  Because `tildeP` is injective on
`ℤ²` (Step 1, `tildeP_injective`), it is in particular injective when
restricted to `acceptedSet`.  This formalizes the paper's remark that
"the multiset and set conventions coincide" in the irrational case:
the projected accepted points have no duplicates. -/
theorem tildeP_injOn_acceptedSet (ha : Irrational a) :
    Set.InjOn (tildeP a) (acceptedSet a ω) :=
  (tildeP_injective a ha).injOn

end CutAndProject.Irrational
