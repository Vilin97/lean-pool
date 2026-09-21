/-
Copyright (c) 2026 Dhyey Dharmendrakumar Mavani, Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyey Dharmendrakumar Mavani, Nathan Pflueger
-/
import LeanPool.ChipFiring.ChipFiringWithLean.Basic


open Multiset Finset

/-!
## The rank function

The *rank* of a divisor $D$ is the integer $r(D) \in \{-1, 0, 1, \ldots\}$ defined by
$r(D) \geq k$ if and only if $D - E$ is winnable for every effective divisor $E$ of degree $k$.
Equivalently, $r(D) \geq 0$ if and only if $D$ is winnable, and $r(D) = -1$ if and
only if $D$ is unwinnable.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Section 5.1.

The rank is well-defined (`rank_exists`, `rank_unique`) and realized by the noncomputable
`rank` function. Key properties established here include:
- `rank_neg_one_iff_unwinnable`: $r(D) = -1 \iff D$ is unwinnable.
- `rank_nonneg_iff_winnable`: $r(D) \geq 0 \iff D$ is winnable.
- `rank_le_degree`: $r(D) \leq \deg(D)$ for $r(D) \geq 0$.
- `zero_divisor_rank`: $r(0) = 0$.

A divisor $D$ is *maximal unwinnable* if it is unwinnable but $D + \delta_v$ is winnable
for every vertex $v$. Such divisors arise in the proof of the Riemann-Roch theorem.
-/

/-- Winnability is preserved under linear equivalence. -/
lemma winnable_equiv_winnable (G : CFGraph) (D1 D2 : CFDiv G) :
  winnable G D1 → linear_equiv G D1 D2 → winnable G D2 := by
  rintro ⟨D1', h_D1'_eff, h_lequiv1⟩ h_lequiv
  exact ⟨D1', h_D1'_eff, h_lequiv.symm.trans h_lequiv1⟩


/-- A divisor is maximal unwinnable if it is unwinnable but adding a chip to any vertex
makes it winnable. -/
def maximal_unwinnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ¬winnable G D ∧ ∀ v : G.V, winnable G (D + one_chip v)

/-- Being maximal unwinnable is preserved under linear equivalence. -/
lemma maximal_unwinnable_preserved (G : CFGraph) (D1 D2 : CFDiv G) :
  maximal_unwinnable G D1 → linear_equiv G D1 D2 → maximal_unwinnable G D2 := by
  rintro ⟨h_unwin_D1, h_winnable_add⟩ h_lequiv
  refine ⟨?_, ?_⟩
  · intro h_win_D2
    exact h_unwin_D1 <| winnable_equiv_winnable G D2 D1 h_win_D2 h_lequiv.symm
  · intro v
    exact winnable_equiv_winnable G (D1 + one_chip v) (D2 + one_chip v) (h_winnable_add v) <| by
      unfold linear_equiv at *
      simpa only [add_sub_add_right_eq_sub] using h_lequiv

/-- The set of effective divisors of degree $k$.

This is used to define `rank_geq`: the relation $r(D) \ge k$ means that $D-E$ is
winnable for every effective divisor $E$ of degree $k$. -/
def eff_of_degree (G : CFGraph) (k : ℤ) : Set (CFDiv G) :=
  {E | effective E ∧ deg E = k}

/-- For any nonnegative integer $k$, the set of effective divisors of degree $k$ is nonempty. -/
private lemma eff_of_degree_nonempty (G : CFGraph) {k : ℤ} (h_nonneg : 0 ≤ k) :
  (eff_of_degree G k).Nonempty := by
  let v : G.V := Classical.arbitrary G.V
  refine ⟨k.toNat • one_chip v, ?_, ?_⟩
  · exact (Eff G).nsmul_mem (eff_one_chip v) k.toNat
  · simpa only [nsmul_eq_mul, deg_one_chip, Int.toNat_of_nonneg h_nonneg, mul_one] using
      (AddMonoidHom.map_nsmul deg k.toNat (one_chip v))

/-- The relation $r(D) \ge k$: the game remains winnable after removing any effective
divisor of degree $k$. -/
def rank_geq (G : CFGraph) (D : CFDiv G) (k : ℤ) : Prop :=
  ∀ E ∈ eff_of_degree G k, winnable G (D-E)

/-- The relation $r(D)=r$: `rank_geq G D r` holds, but `rank_geq G D (r+1)` does not. -/
def rank_eq (G : CFGraph) (D : CFDiv G) (r : ℤ) : Prop :=
  rank_geq G D r ∧ ¬(rank_geq G D (r+1))

/-- The relation `rank_geq G D k` holds vacuously for $k < 0$, since there are no effective
divisors of negative degree. -/
private lemma rank_geq_neg (G : CFGraph) (D : CFDiv G) (k : ℤ): (k < 0) → rank_geq G D k := by
  intro k_neg E ⟨h_eff_E, h_deg_E⟩
  have := deg_of_eff_nonneg E h_eff_E
  linarith

/-- A winnable divisor has nonnegative degree.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 1.16. -/
private lemma deg_winnable_nonneg (G : CFGraph) (D : CFDiv G) (h_winnable : winnable G D) : deg D ≥ 0 := by
  rcases h_winnable with ⟨D', h_D'_eff, h_lequiv⟩
  have same_deg: deg D = deg D' := linear_equiv_preserves_deg G D D' h_lequiv
  rw [same_deg]
  exact deg_of_eff_nonneg D' h_D'_eff

/-- Every effective divisor is winnable (take $D' = D$ in the definition). -/
lemma winnable_of_effective (G : CFGraph) (D : CFDiv G) (h_eff : effective D) : winnable G D := by
  exact ⟨D, h_eff, by
    unfold linear_equiv
    rw [sub_self]
    exact AddSubgroup.zero_mem (principal_divisors G)⟩

/-- The sum of two winnable divisors is winnable. -/
lemma winnable_add_winnable (G : CFGraph) (D1 D2 : CFDiv G)
    (h_winnable1 : winnable G D1) (h_winnable2 : winnable G D2) : winnable G (D1 + D2) := by
  rcases h_winnable1 with ⟨D1', h_D1'_eff, h_lequiv1⟩
  rcases h_winnable2 with ⟨D2', h_D2'_eff, h_lequiv2⟩
  use D1' + D2'
  refine ⟨(Eff G).add_mem h_D1'_eff h_D2'_eff, ?_⟩
  ·
    unfold linear_equiv at *
    have : D1' + D2' - (D1 + D2) = (D1' - D1) + (D2' - D2) := by
      rw [sub_add_sub_comm]
    rw [this]
    exact AddSubgroup.add_mem (principal_divisors G) h_lequiv1 h_lequiv2

/-- If $r(D) \ge r$ for some $r \ge 0$, then $r \le \deg(D)$.

In particular, `rank G D ≤ deg D` when `rank G D ≥ 0`. -/
lemma rank_le_degree (G : CFGraph) (D : CFDiv G) : ∀ (r : ℤ), r ≥ 0 → rank_geq G D r → r ≤ deg D := by
  intro r r_nonneg h_rank
  contrapose! h_rank
  unfold rank_geq; push Not
  rcases eff_of_degree_nonempty G r_nonneg with ⟨E, h_E_eff, h_E_deg⟩
  use E
  constructor
  -- First conjunct: show that E is effecitive of the correct degree
  exact ⟨h_E_eff, h_E_deg⟩
  -- Second conjunct: show that D-E is not winnable
  contrapose! h_rank
  have deg_nonneg := deg_winnable_nonneg G (D-E) h_rank
  simp only [map_sub, Int.sub_nonneg] at deg_nonneg
  rw [h_E_deg] at deg_nonneg
  exact deg_nonneg

/-- The relation `rank_geq` is downward closed: if $r(D)\ge r_1$ and $r_2 \le r_1$,
then $r(D)\ge r_2$. -/
private lemma rank_geq_trans (G : CFGraph) (D : CFDiv G) (r1 r2 : ℤ) :
  rank_geq G D r1 → r2 ≤ r1 → rank_geq G D r2 := by
  intro h_r1 h_leq
  unfold rank_geq at *
  contrapose! h_r1
  rcases h_r1 with ⟨E, ⟨h_E_eff,h_E_nonwin⟩⟩
  rcases eff_of_degree_nonempty G (sub_nonneg.mpr h_leq) with ⟨E_diff, h_Ediff_eff, h_Ediff_deg⟩
  use E + E_diff
  constructor
  · -- Show that E + E_diff is effective of degree r2
    constructor
    apply (Eff G).add_mem
    exact h_E_eff.left
    exact h_Ediff_eff
    -- Show degree
    have E_deg := h_E_eff.right
    simp only [_root_.map_add] at E_deg h_Ediff_deg ⊢
    linarith
  . -- Show that D - (E + E_diff) is not winnable
    contrapose! h_E_nonwin
    have E_diff_winnable := winnable_of_effective G E_diff h_Ediff_eff
    have sum_winnable := winnable_add_winnable G _ _ h_E_nonwin E_diff_winnable
    simpa only [sub_eq_add_neg, neg_add_rev, add_comm, add_left_comm, add_neg_cancel_comm_assoc]
        using sum_winnable

/-- If $r(D) \ge r_1$ holds but $r(D) \ge r_2$ does not, then $r_1 < r_2$. -/
lemma lt_of_rank_geq_not (G : CFGraph) (D : CFDiv G) (r1 r2 : ℤ) :
  rank_geq G D r1 → ¬(rank_geq G D r2) → r1 < r2 := by
  intro h_r1 h_r2
  contrapose! h_r2
  exact rank_geq_trans G D r1 r2 h_r1 h_r2

private lemma rank_eq_neg_one_iff_unwinnable  (G : CFGraph) (D : CFDiv G) :
  rank_eq G D (-1) ↔ ¬(winnable G D) := by
  constructor
  · intro h
    rcases h with ⟨_, h_rank⟩
    contrapose! h_rank
    simp only [Int.reduceNeg, neg_add_cancel]
    intro E h_E
    rcases h_E with ⟨h_eff_E, h_deg_E⟩
    have E_zero := eff_degree_zero _ h_eff_E h_deg_E
    simpa only [E_zero, sub_zero] using h_rank
  · intro h_unwinnable
    refine ⟨rank_geq_neg G D (-1) (by norm_num), ?_⟩
    intro h_rank_geq
    specialize h_rank_geq 0
    apply h_unwinnable
    rw [sub_zero] at h_rank_geq
    apply h_rank_geq
    constructor
    · dsimp only [effective, Pi.zero_apply]
      norm_num
    · simp only [_root_.map_zero, Int.reduceNeg, neg_add_cancel]

/-- The inequality $r(D)\ge 0$ holds if and only if $D$ is winnable. -/
lemma rank_nonneg_iff_winnable (G : CFGraph) (D : CFDiv G) :
  rank_geq G D 0 ↔ winnable G D := by
  constructor
  · intro h_rank
    specialize h_rank 0
    rw [sub_zero] at h_rank
    exact h_rank <| by
      simp only [eff_of_degree, effective, ge_iff_le, Set.mem_ofPred_eq, Pi.zero_apply, Std.le_refl,
          implies_true, _root_.map_zero, and_self]
  · intro h_winnable E ⟨h_eff_E, h_deg_E⟩
    have E_zero := eff_degree_zero _ h_eff_E h_deg_E
    simpa only [E_zero, sub_zero] using h_winnable

/-- If $r(D) \ge m$ fails for some natural number $m$, then there exists an exact rank
$r < m$. -/
private lemma rank_exists_helper (G : CFGraph) (D : CFDiv G) (m : ℕ):  ¬ (rank_geq G D m) → ∃ r < (m:ℤ), rank_eq G D r := by
  induction m with
  | zero =>
  · intro h_rank_geq
    exact ⟨-1, by norm_num, rank_geq_neg G D (-1) (by norm_num), h_rank_geq⟩
  | succ m ih =>
    intro h_rank_geq
    by_cases h_rank_m : rank_geq G D m
    · exact ⟨m, by norm_num, h_rank_m, h_rank_geq⟩
    ·
      specialize ih h_rank_m
      rcases ih with ⟨r, h_r_lt, h_rank_eq⟩
      have r_le : r < m + 1 := by
        linarith [h_r_lt]
      exact ⟨r, r_le, h_rank_eq⟩

/-- Every divisor has a well-defined rank: there exists an integer $r$ with $r(D)=r$. -/
lemma rank_exists (G : CFGraph) (D : CFDiv G) :
  ∃ r : ℤ, rank_eq G D r := by
  let m := (deg D).toNat + 1
  have h_not_geq : ¬(rank_geq G D m) := by
    intro h_rank_geq
    have h_le := rank_le_degree G D m (by linarith) h_rank_geq
    have m_ge : m ≥ deg D + 1:= by
      dsimp only [Int.natCast_add, Int.cast_ofNat_Int, m]
      simp only [Int.ofNat_toNat, ge_iff_le, add_le_add_iff_right, le_sup_left]
    linarith
  rcases rank_exists_helper G D m h_not_geq with ⟨r, _, h_rank_eq⟩
  exact ⟨r, h_rank_eq⟩

/-- The rank of a divisor is unique: if $r(D)=r_1$ and $r(D)=r_2$, then $r_1=r_2$.  This is not
  explicitly needed elsewhere, but is included for context. -/
private lemma rank_unique (G : CFGraph) (D : CFDiv G) :
  ∀ r1 r2 : ℤ, rank_eq G D r1 → rank_eq G D r2 → r1 = r2 := by
  rintro r1 r2 ⟨h_r1_geq, h_r1_not_geq⟩ ⟨h_r2_geq, h_r2_not_geq⟩
  have ineq1 : r1 < r2 + 1 := lt_of_rank_geq_not G D r1 (r2+1) h_r1_geq h_r2_not_geq
  have ineq2 : r2 < r1 + 1 := lt_of_rank_geq_not G D r2 (r1+1) h_r2_geq h_r1_not_geq
  linarith

/-- The rank function for divisors. -/
noncomputable def rank (G : CFGraph) (D : CFDiv G) : ℤ :=
  Classical.choose (rank_exists G D)

/-- The defining property of `rank`: it satisfies the relation `rank_eq`. -/
private lemma rank_spec (G : CFGraph) (D : CFDiv G) : rank_eq G D (rank G D) :=
  Classical.choose_spec (rank_exists G D)

/-- The relation `rank_geq G D k` is equivalent to the inequality `rank G D ≥ k`. -/
lemma rank_geq_iff (G : CFGraph) (D : CFDiv G) (k : ℤ) :
  rank_geq G D k ↔ rank G D ≥ k := by
  constructor
  · -- Forward direction
    intro h_rank_geq
    have := lt_of_rank_geq_not G D k (rank G D + 1) h_rank_geq (rank_spec G D).right
    linarith
  · -- Backward direction
    intro h_rank_leq
    exact rank_geq_trans G D (rank G D) k (rank_spec G D).left h_rank_leq

/-- The relation `rank_eq G D r` is equivalent to the equality `rank G D = r`. -/
private lemma rank_eq_iff (G : CFGraph) (D : CFDiv G) (r : ℤ) :
  rank_eq G D r ↔ rank G D = r := by
  dsimp only [rank_eq]
  have split_eq x: x = r ↔ (x ≥ r ∧ ¬(x ≥ r + 1)) := by
    rw [not_le]
    rw [Int.lt_add_one_iff]
    have helper := @le_antisymm_iff _ _ x r
    rw [helper, and_comm]
  rw [split_eq (rank G D)]
  rw [rank_geq_iff G D r, rank_geq_iff G D (r+1)]

/-- A divisor is winnable if and only if it is linearly equivalent to an effective divisor. -/
lemma winnable_iff_exists_effective (G : CFGraph) (D : CFDiv G) :
  winnable G D ↔ ∃ D' : CFDiv G, effective D' ∧ linear_equiv G D D' := by
  simp only [winnable, mem_Eff]


/-- There is an effective divisor $E$ of degree $r(D)+1$ such that $D-E$ is not winnable. -/
lemma rank_get_effective (G : CFGraph) (D : CFDiv G) :
  ∃ E : CFDiv G, effective E ∧ deg E = rank G D + 1 ∧ ¬(winnable G (D-E)) := by
  obtain ⟨_, h_r_not_geq⟩ := rank_spec G D
  dsimp only [rank_geq] at h_r_not_geq
  push Not at h_r_not_geq
  rcases h_r_not_geq with ⟨E, ⟨h_E_eff, h_E_deg⟩, h_E_not_winnable⟩
  exact ⟨E, h_E_eff, h_E_deg, h_E_not_winnable⟩

/-- A divisor has rank $-1$ if and only if it is not winnable. -/
lemma rank_neg_one_iff_unwinnable (G : CFGraph) (D : CFDiv G) :
  rank G D = -1 ↔ ¬(winnable G D) := by
  rw [← rank_eq_iff]
  exact rank_eq_neg_one_iff_unwinnable G D

/-- A divisor of negative degree has rank $-1$, i.e. is unwinnable. -/
lemma rank_neg_one_of_deg_neg (G : CFGraph) (D : CFDiv G) (h_deg : deg D < 0) :
  rank G D = -1 := by
  rw [rank_neg_one_iff_unwinnable]
  intro h_win
  linarith [deg_winnable_nonneg G D h_win]

/-- The rank of a divisor is at least $-1$. -/
lemma rank_geq_neg_one (G : CFGraph) (D : CFDiv G) : rank G D ≥ -1 :=
  (rank_geq_iff G D (-1)).mp (rank_geq_neg G D (-1) (by norm_num))

/-- If the rank is not nonnegative, then it is $-1$. -/
lemma rank_neg_one_of_not_nonneg (G : CFGraph) (D : CFDiv G)
  (h_not_nonneg : ¬(rank G D ≥ 0)) : rank G D = -1 := by
  have := rank_geq_neg_one G D
  omega

/-- The rank of the zero divisor is zero. -/
lemma zero_divisor_rank (G : CFGraph) : rank G (0:CFDiv G) = 0 := by
  rw [← rank_eq_iff]
  constructor
  have h_eff : effective (0:CFDiv G) := by
    simp only [effective, Pi.zero_apply, ge_iff_le, Std.le_refl, implies_true]
  rw [rank_nonneg_iff_winnable G (0:CFDiv G)]
  exact winnable_of_effective G (0:CFDiv G) h_eff
  have ineq := rank_le_degree G (0:CFDiv G) 1 (by norm_num)
  simp only [deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply, sum_const_zero, Int.reduceLE,
      imp_false] at ineq
  exact ineq

theorem one_le_apply_of_q_reduced_of_rank_geq_one {G : CFGraph} {q : G.V}
    {D : CFDiv G} (hred : q_reduced G q D) (hrank : rank G D ≥ 1) :
    1 ≤ D q := by
  classical
  have hval : ∀ v : G.V, v ≠ q → (D - one_chip q) v = D v := by
    intro v hv
    simp [Pi.sub_apply, one_chip_apply_other' q v hv]
  have hwin : winnable G (D - one_chip q) :=
    (rank_geq_iff G D 1).mpr hrank (one_chip q) ⟨eff_one_chip q, deg_one_chip q⟩
  have hred' : q_reduced G q (D - one_chip q) := by
    refine ⟨fun v hv => by rw [hval v hv]; exact hred.1 v hv, ?_⟩
    intro S hq hSne hlegal
    apply hred.2 S hq hSne
    intro v hvS
    rw [← hval v (fun hvq => hq (hvq ▸ hvS))]
    exact hlegal v hvS
  have heff : effective (D - one_chip q) :=
    effective_of_winnable_and_q_reduced G q _ hwin hred'
  have hq := heff q
  simp only [Pi.sub_apply, one_chip_apply_v] at hq
  omega
