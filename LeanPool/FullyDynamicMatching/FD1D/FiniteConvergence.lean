/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Expectations

/-! # Finite Convergence -/

namespace FD1D

noncomputable section

open Filter
open scoped BigOperators Topology

namespace FiniteKernel

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

private noncomputable def reachTime
    (K : FiniteKernel α) (hirr : K.Irreducible) (x y : α) : ℕ :=
  Classical.choose (hirr x y)

omit [Nonempty α] in
private theorem reachTime_spec
    (K : FiniteKernel α) (hirr : K.Irreducible) (x y : α) :
    0 < K.pow (reachTime K hirr x y) x y :=
  Classical.choose_spec (hirr x y)

omit [Nonempty α] in
private theorem pow_loop_pos
    (K : FiniteKernel α) (hloop : K.HasPositiveLoops)
    (x : α) (n : ℕ) :
    0 < K.pow n x x := by
  induction n with
  | zero =>
      simp [FiniteKernel.pow_zero]
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, K.pow_add]
      have hterm : 0 < K.pow n x x * K.pow 1 x x := by
        simpa using mul_pos ih (hloop x)
      exact lt_of_lt_of_le hterm
        (Finset.single_le_sum
          (fun y _ =>
            mul_nonneg (K.pow_nonneg n x y) (K.pow_nonneg 1 y x))
          (Finset.mem_univ x))

omit [Nonempty α] in
/-- Irreducibility and positive one-step loops make one common kernel power
strictly positive in every entry. -/
theorem exists_pow_pos
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops) :
    ∃ N : ℕ, 0 < N ∧ ∀ x y, 0 < K.pow N x y := by
  let N : ℕ := 1 + ∑ x, ∑ y, reachTime K hirr x y
  refine ⟨N, by simp [N], ?_⟩
  intro x y
  let n := reachTime K hirr x y
  have hnInner : n ≤ ∑ z, reachTime K hirr x z := by
    exact Finset.single_le_sum
      (fun z _ => Nat.zero_le (reachTime K hirr x z))
      (Finset.mem_univ y)
  have hnSum :
      (∑ z, reachTime K hirr x z) ≤
        ∑ w, ∑ z, reachTime K hirr w z := by
    exact Finset.single_le_sum
      (fun w _ => Nat.zero_le (∑ z, reachTime K hirr w z))
      (Finset.mem_univ x)
  have hnN : n ≤ N := by
    dsimp [N]
    omega
  have hsplit : n + (N - n) = N := Nat.add_sub_of_le hnN
  rw [← hsplit, K.pow_add]
  exact lt_of_lt_of_le
    (mul_pos (reachTime_spec K hirr x y)
      (pow_loop_pos K hloop y (N - n)))
    (Finset.single_le_sum
      (fun z _ =>
        mul_nonneg (K.pow_nonneg n x z) (K.pow_nonneg (N - n) z y))
      (Finset.mem_univ y))

/-- The `ℓ¹` distance between two finite probability laws. -/
def lawL1 (μ ν : FiniteLaw α) : ℝ :=
  ∑ x, |μ.mass x - ν.mass x|

omit [DecidableEq α] [Nonempty α] in
private theorem lawL1_nonneg (μ ν : FiniteLaw α) :
    0 ≤ lawL1 μ ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [Nonempty α] in
private theorem mass_iterate_sub
    (K : FiniteKernel α) (n : ℕ) (μ ν : FiniteLaw α) (y : α) :
    (K.iterate n μ).mass y - (K.iterate n ν).mass y =
      ∑ x, (μ.mass x - ν.mass x) * K.pow n x y := by
  rw [K.mass_iterate, K.mass_iterate, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Nonempty α] [DecidableEq α] in
private theorem lawL1_iterate_le
    (K : FiniteKernel α) (n : ℕ) (μ ν : FiniteLaw α) :
    lawL1 (K.iterate n μ) (K.iterate n ν) ≤ lawL1 μ ν := by
  classical
  unfold lawL1
  simp_rw [mass_iterate_sub]
  calc
    (∑ y, |∑ x, (μ.mass x - ν.mass x) * K.pow n x y|) ≤
        ∑ y, ∑ x, |(μ.mass x - ν.mass x) * K.pow n x y| := by
      exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ∑ y, |μ.mass x - ν.mass x| * K.pow n x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (K.pow_nonneg n x y)]
    _ = ∑ x, |μ.mass x - ν.mass x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, K.sum_pow, mul_one]

private theorem exists_minorization
    (K : FiniteKernel α) {N : ℕ}
    (hpos : ∀ x y, 0 < K.pow N x y) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x y, ε ≤ K.pow N x y) ∧
      (Fintype.card α : ℝ) * ε ≤ 1 := by
  obtain ⟨p, _, hp⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (α × α))
      (fun p => K.pow N p.1 p.2) Finset.univ_nonempty
  let ε := K.pow N p.1 p.2
  refine ⟨ε, hpos p.1 p.2, ?_, ?_⟩
  · intro x y
    exact hp (x, y) (Finset.mem_univ _)
  · let x₀ : α := Classical.arbitrary α
    calc
      (Fintype.card α : ℝ) * ε = ∑ _y : α, ε := by
        simp
      _ ≤ ∑ y, K.pow N x₀ y := by
        exact Finset.sum_le_sum fun y _ => hp (x₀, y) (Finset.mem_univ _)
      _ = 1 := K.sum_pow N x₀

omit [DecidableEq α] [Nonempty α] in
private theorem sum_mass_sub (μ ν : FiniteLaw α) :
    ∑ x, (μ.mass x - ν.mass x) = 0 := by
  rw [Finset.sum_sub_distrib, μ.sum_mass, ν.sum_mass, sub_self]

omit [Nonempty α] in
private theorem mass_iterate_sub_eq_residual
    (K : FiniteKernel α) (N : ℕ) (ε : ℝ)
    (μ ν : FiniteLaw α) (y : α) :
    (K.iterate N μ).mass y - (K.iterate N ν).mass y =
      ∑ x, (μ.mass x - ν.mass x) * (K.pow N x y - ε) := by
  rw [mass_iterate_sub]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_mass_sub, zero_mul, sub_zero]

omit [Nonempty α] in
private theorem lawL1_block_contraction
    (K : FiniteKernel α) (N : ℕ) (ε : ℝ)
    (hε : ∀ x y, ε ≤ K.pow N x y)
    (μ ν : FiniteLaw α) :
    lawL1 (K.iterate N μ) (K.iterate N ν) ≤
      (1 - (Fintype.card α : ℝ) * ε) * lawL1 μ ν := by
  unfold lawL1
  simp_rw [mass_iterate_sub_eq_residual K N ε]
  calc
    (∑ y, |∑ x, (μ.mass x - ν.mass x) * (K.pow N x y - ε)|) ≤
        ∑ y, ∑ x,
          |(μ.mass x - ν.mass x) * (K.pow N x y - ε)| := by
      exact Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, ∑ y,
        |μ.mass x - ν.mass x| * (K.pow N x y - ε) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hε x y))]
    _ = ∑ x, |μ.mass x - ν.mass x| *
        (1 - (Fintype.card α : ℝ) * ε) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_sub_distrib, K.sum_pow]
      simp
    _ = (1 - (Fintype.card α : ℝ) * ε) *
        ∑ x, |μ.mass x - ν.mass x| := by
      rw [← Finset.sum_mul]
      ring

omit [Nonempty α] in
private theorem lawL1_blocks_le
    (K : FiniteKernel α) (π μ : FiniteLaw α)
    (hπ : K.IsStationary π)
    (N : ℕ) (ε : ℝ)
    (hε : ∀ x y, ε ≤ K.pow N x y)
    (hq : 0 ≤ 1 - (Fintype.card α : ℝ) * ε)
    (k : ℕ) :
    lawL1 (K.iterate (k * N) μ) π ≤
      (1 - (Fintype.card α : ℝ) * ε) ^ k * lawL1 μ π := by
  let q := 1 - (Fintype.card α : ℝ) * ε
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hcontract :=
        lawL1_block_contraction K N ε hε (K.iterate (k * N) μ) π
      rw [hπ.iterate N] at hcontract
      have hstep :
          lawL1 (K.iterate N (K.iterate (k * N) μ)) π ≤
            q ^ (k + 1) * lawL1 μ π := by
        calc
          lawL1 (K.iterate N (K.iterate (k * N) μ)) π ≤
              q * lawL1 (K.iterate (k * N) μ) π := hcontract
          _ ≤ q * (q ^ k * lawL1 μ π) :=
            mul_le_mul_of_nonneg_left ih hq
          _ = q ^ (k + 1) * lawL1 μ π := by
            rw [pow_succ]
            ring
      rw [← K.iterate_add] at hstep
      simpa [q, Nat.succ_mul, Nat.add_comm] using hstep

omit [Nonempty α] in
private theorem lawL1_iterate_geometric
    (K : FiniteKernel α) (π μ : FiniteLaw α)
    (hπ : K.IsStationary π)
    (N : ℕ)
    (ε : ℝ) (hε : ∀ x y, ε ≤ K.pow N x y)
    (hc : (Fintype.card α : ℝ) * ε ≤ 1)
    (n : ℕ) :
    lawL1 (K.iterate n μ) π ≤
      (1 - (Fintype.card α : ℝ) * ε) ^ (n / N) * lawL1 μ π := by
  let q := 1 - (Fintype.card α : ℝ) * ε
  have hq : 0 ≤ q := sub_nonneg.mpr hc
  have hdecomp : n % N + (n / N) * N = n := by
    rw [mul_comm, Nat.mod_add_div]
  calc
    lawL1 (K.iterate n μ) π =
        lawL1
          (K.iterate (n % N) (K.iterate ((n / N) * N) μ))
          (K.iterate (n % N) π) := by
      rw [← K.iterate_add, hdecomp, hπ.iterate]
    _ ≤ lawL1 (K.iterate ((n / N) * N) μ) π :=
      lawL1_iterate_le K (n % N) _ _
    _ ≤ q ^ (n / N) * lawL1 μ π :=
      lawL1_blocks_le K π μ hπ N ε hε hq (n / N)

private theorem tendsto_lawL1_zero
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) :
    Tendsto (fun n => lawL1 (K.iterate n μ) π) atTop (𝓝 0) := by
  obtain ⟨N, hN, hpow⟩ := exists_pow_pos K hirr hloop
  obtain ⟨ε, hεpos, hε, hc⟩ := exists_minorization K hpow
  let q := 1 - (Fintype.card α : ℝ) * ε
  have hq0 : 0 ≤ q := sub_nonneg.mpr hc
  have hcard : 0 < (Fintype.card α : ℝ) := by positivity
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith
  have hpowlim :
      Tendsto (fun n : ℕ => q ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (Nat.tendsto_div_const_atTop hN.ne')
  refine squeeze_zero (fun n => lawL1_nonneg (K.iterate n μ) π)
    (fun n => lawL1_iterate_geometric K π μ hπ N ε hε hc n) ?_
  simpa [q] using hpowlim.mul_const (lawL1 μ π)

/-- Ordinary iterates of a finite irreducible kernel with positive loops
converge, pointwise in mass, to any stationary law. -/
theorem tendsto_iterate_mass
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) :
    Tendsto (fun n => (K.iterate n μ).mass) atTop (𝓝 π.mass) := by
  rw [tendsto_pi_nhds]
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hL1 := tendsto_lawL1_zero K hirr hloop π hπ μ
  refine squeeze_zero (fun n => dist_nonneg)
    (fun n => ?_) hL1
  rw [Real.dist_eq]
  exact Finset.single_le_sum
    (fun y _ => abs_nonneg ((K.iterate n μ).mass y - π.mass y))
    (Finset.mem_univ x)

/-- A finite irreducible kernel with positive loops has one stationary law,
and every initial law converges ordinarily to it. -/
theorem existsUnique_stationary_and_tendsto
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops) :
    ∃! π : FiniteLaw α,
      K.IsStationary π ∧
        ∀ μ : FiniteLaw α,
          Tendsto (fun n => (K.iterate n μ).mass) atTop (𝓝 π.mass) := by
  obtain ⟨π, hπ⟩ := K.exists_stationary
  refine ⟨π, ⟨hπ, fun μ => tendsto_iterate_mass K hirr hloop π hπ μ⟩, ?_⟩
  intro ν hν
  exact K.stationary_unique hirr hν.1 hπ

/-- Expectations of every real observable converge along the ordinary
iterates to their value under the unique stationary law. -/
theorem tendsto_expect_iterate
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops)
    (π : FiniteLaw α) (hπ : K.IsStationary π)
    (μ : FiniteLaw α) (f : α → ℝ) :
    Tendsto (fun n => (K.iterate n μ).expect f) atTop (𝓝 (π.expect f)) := by
  have hmass := tendsto_iterate_mass K hirr hloop π hπ μ
  rw [tendsto_pi_nhds] at hmass
  unfold FiniteLaw.expect
  apply tendsto_finsetSum
  intro x _
  exact (hmass x).mul_const (f x)

end FiniteKernel

end

end FD1D
