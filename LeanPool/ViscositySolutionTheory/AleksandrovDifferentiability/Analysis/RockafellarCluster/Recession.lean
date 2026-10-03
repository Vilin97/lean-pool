/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.RockafellarCluster.Exposed

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Recession directions and no-line facts for subgradient sets

This module contains the recession-direction computations used to match Rockafellar's observation
that interior-point subdifferentials contain no affine lines.
-/

@[expose] public noncomputable section

namespace AleksandrovDifferentiability

open scoped Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A line direction is in particular a recession direction. -/
theorem lineDirectionsAt.subset_recessionDirectionsAt {s : Set E} {p : E} :
    lineDirectionsAt s p ⊆ recessionDirectionsAt s p := by
  intro q hq t _ht
  exact hq t

omit [CompleteSpace E] in
/-- A nonzero recession direction at an exposed point pairs strictly negatively with the exposing
normal. -/
theorem ExposesPoint.inner_recessionDirection_neg
    {s : Set E} {normal p q : E}
    (hexposed : ExposesPoint s normal p)
    (hqrec : q ∈ recessionDirectionsAt s p) (hq_ne : q ≠ 0) :
    inner ℝ normal q < 0 := by
  have hpq_mem : p + q ∈ s := by
    simpa using hqrec (t := 1) zero_le_one
  have hpq_ne : p + q ≠ p := by
    intro h
    apply hq_ne
    calc
      q = (p + q) - p := by abel
      _ = 0 := by rw [h]; abel
  have hlt : inner ℝ normal (p + q) < inner ℝ normal p :=
    hexposed.2 hpq_mem hpq_ne
  rw [inner_add_right] at hlt
  linarith

omit [CompleteSpace E] in
/-- Any recession direction at an exposed point pairs nonpositively with the exposing normal. -/
theorem ExposesPoint.inner_recessionDirection_nonpos
    {s : Set E} {normal p q : E}
    (hexposed : ExposesPoint s normal p)
    (hqrec : q ∈ recessionDirectionsAt s p) :
    inner ℝ normal q ≤ 0 := by
  by_cases hq : q = 0
  · simp [hq]
  · exact (hexposed.inner_recessionDirection_neg hqrec hq).le

/-- If `a + t*b ≤ c` for every nonnegative `t`, then `b ≤ 0`. -/
lemma slope_nonpos_of_forall_nonneg_add_mul_le {a b c : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → a + t * b ≤ c) :
    b ≤ 0 := by
  by_contra hb_nonpos
  have hb_pos : 0 < b := lt_of_not_ge hb_nonpos
  rcases exists_nat_gt ((c - a) / b) with ⟨n, hn⟩
  have hmul : c - a < (n : ℝ) * b := by
    have hmul' := (div_lt_iff₀ hb_pos).mp hn
    simpa [mul_comm] using hmul'
  have hbig : c < a + (n : ℝ) * b := by
    linarith
  have hle : a + (n : ℝ) * b ≤ c := h (n : ℝ) (Nat.cast_nonneg n)
  exact (not_le_of_gt hbig) hle

omit [CompleteSpace E] in
/-- A recession direction of the subdifferential gives a normal-cone inequality for the domain.

This is the local real-valued version of the Rockafellar 25.6 step identifying the recession cone
of `∂f(y)` with the normal cone to the effective domain at `y`. -/
theorem inner_recessionDirection_subgradientSet_nonpos
    {domain : Set E} {u : E → ℝ} {y p q z : E}
    (_hp : SubgradientOn domain u y p)
    (hqrec : q ∈ recessionDirectionsAt {r : E | SubgradientOn domain u y r} p)
    (hz : z ∈ domain) :
    inner ℝ q (z - y) ≤ 0 := by
  have hineq : ∀ t : ℝ, 0 ≤ t →
      u y + inner ℝ p (z - y) + t * inner ℝ q (z - y) ≤ u z := by
    intro t ht
    have hpt : SubgradientOn domain u y (p + t • q) := hqrec ht
    have hsupport := hpt.supporting_inequality hz
    simpa [inner_add_left, real_inner_smul_left, add_assoc] using hsupport
  exact slope_nonpos_of_forall_nonneg_add_mul_le hineq

omit [CompleteSpace E] in
/-- A normal-cone inequality for the domain gives a recession direction of the subdifferential.

This is the reverse implication in the local real-valued form of Rockafellar's identification
`K(y) = rec (∂u(y))`. -/
theorem recessionDirection_subgradientSet_of_forall_inner_sub_nonpos
    {domain : Set E} {u : E → ℝ} {y p q : E}
    (hp : SubgradientOn domain u y p)
    (hnormal : ∀ z ∈ domain, inner ℝ q (z - y) ≤ 0) :
    q ∈ recessionDirectionsAt {r : E | SubgradientOn domain u y r} p := by
  intro t ht
  refine ⟨hp.mem, ?_⟩
  intro z hz
  have hpz : u y + inner ℝ p (z - y) ≤ u z := hp.supporting_inequality hz
  have hqz : t * inner ℝ q (z - y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht (hnormal z hz)
  calc
    u y + inner ℝ (p + t • q) (z - y)
        = u y + inner ℝ p (z - y) + t * inner ℝ q (z - y) := by
          rw [inner_add_left, real_inner_smul_left]
          ring
    _ ≤ u z + 0 := add_le_add hpz hqz
    _ = u z := by ring

omit [CompleteSpace E] in
/-- Recession directions of a subdifferential are exactly the domain normal-cone directions.

This packages the finite-valued local quantifier shape needed from Rockafellar 25.6. -/
theorem recessionDirection_subgradientSet_iff_forall_inner_sub_nonpos
    {domain : Set E} {u : E → ℝ} {y p q : E}
    (hp : SubgradientOn domain u y p) :
    q ∈ recessionDirectionsAt {r : E | SubgradientOn domain u y r} p ↔
      ∀ z ∈ domain, inner ℝ q (z - y) ≤ 0 :=
  ⟨fun hq _z hz => inner_recessionDirection_subgradientSet_nonpos hp hq hz,
    recessionDirection_subgradientSet_of_forall_inner_sub_nonpos hp⟩

omit [CompleteSpace E] in
/-- If the domain is a neighborhood of the base point, every normal-cone direction is zero. -/
theorem eq_zero_of_forall_inner_sub_nonpos_of_mem_nhds
    {domain : Set E} {y q : E}
    (hdomain : domain ∈ 𝓝 y)
    (hnormal : ∀ z ∈ domain, inner ℝ q (z - y) ≤ 0) :
    q = 0 := by
  by_contra hq_ne
  have hpos_norm : 0 < ‖q‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hq_ne)
  have hpre : {t : ℝ | y + t • q ∈ domain} ∈ 𝓝 (0 : ℝ) := by
    have hcont : ContinuousAt (fun t : ℝ => y + t • q) 0 := by fun_prop
    have hdomain0 : domain ∈ 𝓝 ((fun t : ℝ => y + t • q) 0) := by
      simpa using hdomain
    change ((fun t : ℝ => y + t • q) ⁻¹' domain) ∈ 𝓝 0
    exact hcont hdomain0
  rw [Metric.mem_nhds_iff] at hpre
  rcases hpre with ⟨ε, hε_pos, hε_sub⟩
  let t : ℝ := ε / 2
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith
  have ht_ball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    have ht_nonneg : 0 ≤ t := ht_pos.le
    rw [abs_of_nonneg ht_nonneg]
    dsimp [t]
    linarith
  have ht_domain : y + t • q ∈ domain := hε_sub ht_ball
  have hnormal_t : inner ℝ q ((y + t • q) - y) ≤ 0 :=
    hnormal (y + t • q) ht_domain
  have hpositive : 0 < inner ℝ q ((y + t • q) - y) := by
    have ht : 0 < t := ht_pos
    rw [add_sub_cancel_left, real_inner_smul_right]
    simpa [real_inner_self_eq_norm_sq] using mul_pos ht hpos_norm
  exact (not_le_of_gt hpositive) hnormal_t

omit [CompleteSpace E] in
/-- At an interior point of the domain, the subdifferential has no nonzero recession direction. -/
theorem recessionDirection_subgradientSet_eq_zero_of_mem_nhds
    {domain : Set E} {u : E → ℝ} {y p q : E}
    (hdomain : domain ∈ 𝓝 y)
    (hp : SubgradientOn domain u y p)
    (hqrec : q ∈ recessionDirectionsAt {r : E | SubgradientOn domain u y r} p) :
    q = 0 :=
  eq_zero_of_forall_inner_sub_nonpos_of_mem_nhds hdomain
    (fun _ hz => inner_recessionDirection_subgradientSet_nonpos hp hqrec hz)

omit [CompleteSpace E] in
/-- At an interior point of the domain, the based recession directions of the subdifferential are
only the zero direction. -/
theorem recessionDirectionsAt_subgradientSet_eq_singleton_zero_of_mem_nhds
    {domain : Set E} {u : E → ℝ} {y p : E}
    (hdomain : domain ∈ 𝓝 y)
    (hp : SubgradientOn domain u y p) :
    recessionDirectionsAt {r : E | SubgradientOn domain u y r} p = {0} := by
  ext q
  constructor
  · intro hqrec
    rw [Set.mem_singleton_iff]
    exact recessionDirection_subgradientSet_eq_zero_of_mem_nhds hdomain hp hqrec
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    intro t _ht
    simpa using hp

omit [CompleteSpace E] in
/-- At an interior point of the domain, the subdifferential contains no nonzero affine line
through a subgradient. -/
theorem lineDirection_subgradientSet_eq_zero_of_mem_nhds
    {domain : Set E} {u : E → ℝ} {y p q : E}
    (hdomain : domain ∈ 𝓝 y)
    (hp : SubgradientOn domain u y p)
    (hqline : q ∈ lineDirectionsAt {r : E | SubgradientOn domain u y r} p) :
    q = 0 :=
  recessionDirection_subgradientSet_eq_zero_of_mem_nhds hdomain hp
    (lineDirectionsAt.subset_recessionDirectionsAt hqline)

omit [CompleteSpace E] in
/-- At an interior point of the domain, the based affine-line directions in the subdifferential
are only the zero direction. This is the local Lean form of Rockafellar's no-lines observation. -/
theorem lineDirectionsAt_subgradientSet_eq_singleton_zero_of_mem_nhds
    {domain : Set E} {u : E → ℝ} {y p : E}
    (hdomain : domain ∈ 𝓝 y)
    (hp : SubgradientOn domain u y p) :
    lineDirectionsAt {r : E | SubgradientOn domain u y r} p = {0} := by
  ext q
  constructor
  · intro hqline
    rw [Set.mem_singleton_iff]
    exact lineDirection_subgradientSet_eq_zero_of_mem_nhds hdomain hp hqline
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    intro t
    simpa using hp

omit [CompleteSpace E] in
/-- At an interior point of the domain, the subdifferential contains no nontrivial affine line. -/
theorem subgradientSet_hasNoAffineLines_of_mem_nhds
    {domain : Set E} {u : E → ℝ} {y : E}
    (hdomain : domain ∈ 𝓝 y) :
    HasNoAffineLines {r : E | SubgradientOn domain u y r} := by
  intro p q hp hqline
  exact lineDirection_subgradientSet_eq_zero_of_mem_nhds hdomain hp hqline

omit [CompleteSpace E] in
/-- Open-domain version of `subgradientSet_hasNoAffineLines_of_mem_nhds`. -/
theorem subgradientSet_hasNoAffineLines_of_isOpen
    {domain : Set E} {u : E → ℝ} {y : E}
    (hopen : IsOpen domain) :
    HasNoAffineLines {r : E | SubgradientOn domain u y r} := by
  intro p q hp hqline
  exact lineDirection_subgradientSet_eq_zero_of_mem_nhds
    (hopen.mem_nhds hp.mem) hp hqline

end AleksandrovDifferentiability
