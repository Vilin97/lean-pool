/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.RRGHelpers

/-! # Riemann Roch -/

@[expose] public section
universe u

open Multiset Finset

/-!
# Riemann-Roch for graphs

The Riemann-Roch theorem for graphs and its main corollaries.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Chapter 5.
-/

/-- **Riemann-Roch theorem for graphs:** $r(D) - r(K_G - D) = \deg(D) + 1 - g$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Theorem 5.9. -/
theorem riemann_roch_for_graphs {G : CFGraph} (h_conn : graphConnected G) (D : CFDiv G) :
  rank G D - rank G (canonicalDivisor G - D) = deg D - genus G + 1 := by
  set K := canonicalDivisor G with K_eq
  have h_ineq := rank_degree_inequality h_conn D
  have h_ineq_rev : deg (K-D) - genus G < rank G (K-D) - rank G D := by
    convert rank_degree_inequality h_conn (K-D)
    abel
  have deg_sub : deg (K-D) = deg K - deg D := by rw [deg.map_sub]
  have h_deg_K : deg (canonicalDivisor G) = 2 * genus G - 2 := degree_of_canonical_divisor G
  linarith

/-- $D$ is maximal unwinnable if and only if $K_G - D$ is maximal unwinnable.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 5.11. -/
theorem maximal_unwinnable_symmetry
    {G : CFGraph} (h_conn : graphConnected G) (D : CFDiv G) :
  maximalUnwinnable G D ↔ maximalUnwinnable G (canonicalDivisor G - D) := by
  set K := canonicalDivisor G with K_def
  suffices ∀ (D : CFDiv G), maximalUnwinnable G D → maximalUnwinnable G (canonicalDivisor G - D) by
    constructor
    exact this D
    intro h
    apply this (K-D) at h
    rw [sub_sub_self] at h
    exact h
  -- Now we can just prove the forward direction
  intro D h_max_unwin
  -- Get rank = -1 from maximal unwinnable
  have h_rank_neg : rank G D = -1 := by
    rw [rank_neg_one_iff_unwinnable]
    exact h_max_unwin.1
  -- Get degree = g-1 from maximal unwinnable
  have h_deg : deg D = genus G - 1 := maximal_unwinnable_deg h_conn D h_max_unwin
  -- Use Riemann-Roch
  have h_RR := riemann_roch_for_graphs h_conn D
  rw [h_rank_neg] at h_RR
  -- Get degree of K-D
  have h_deg_K := degree_of_canonical_divisor G
  have h_deg_KD : deg (canonicalDivisor G - D) = genus G - 1 := by
    rw [deg.map_sub]
    rw [h_deg_K, h_deg]
    linarith
  constructor
  · -- K-D is unwinnable
    rw [←rank_neg_one_iff_unwinnable]
    linarith
  · -- Adding chip makes K-D winnable
    intro v -- Goal: winnable G ((K-D) + δᵥ)
    -- Let E = (K-D) + δᵥ
    set E : CFDiv G := (canonicalDivisor G - D) + oneChip v with E_def
    suffices winnable G E by
      exact this
    -- To show E is winnable, we will use Riemann-Roch on E
    have h_deg_E : deg E = genus G := by
      rw [E_def, deg.map_add, deg_one_chip, h_deg_KD]
      linarith
    apply (rank_nonneg_iff_winnable G E).mp
    rw [rank_geq_iff G E]
    calc
      rank G E = rank G (K-E) + deg E +1 - genus G := by
        linarith [riemann_roch_for_graphs h_conn E]
      _ ≥ deg E - genus G := by
        linarith [rank_geq_neg_one G (K - E)]
      _ = 0 := by linarith[h_deg_E]

/-- The rank function is subadditive:
$$
r(D_1+D_2) \ge r(D_1)+r(D_2).
$$
-/
private lemma rank_subadditive (G : CFGraph) (D D' : CFDiv G)
    (h_D : rank G D ≥ 0) (h_D' : rank G D' ≥ 0) :
    rank G (D+D') ≥ rank G D + rank G D' := by
  -- Express the two (nonnegative) ranks as natural numbers
  obtain ⟨k₁, h_k₁⟩ : ∃ k : ℕ, (k : ℤ) = rank G D := ⟨_, Int.toNat_of_nonneg h_D⟩
  obtain ⟨k₂, h_k₂⟩ : ∃ k : ℕ, (k : ℤ) = rank G D' := ⟨_, Int.toNat_of_nonneg h_D'⟩
  -- Show rank is ≥ k₁ + k₂ by proving rankGeq
  have h_rank_geq : rankGeq G (D + D') (k₁ + k₂) := by
    -- Take any effective divisor E'' of degree k₁ + k₂
    rintro E'' ⟨h_eff, h_deg⟩
    -- Decompose E'' into E₁ and E₂ of degrees k₁ and k₂
    obtain ⟨E₁, E₂, h_E₁_eff, h_E₂_eff, h_E₁_deg, h_E₂_deg, h_sum⟩ :=
      effective_divisor_decomposition G E'' k₁ k₂ h_eff h_deg
    -- Apply rankGeq to get winnability for both parts
    have h_D_win := (rank_geq_iff G D k₁).mpr (le_of_eq h_k₁) E₁ ⟨h_E₁_eff, h_E₁_deg⟩
    have h_D'_win := (rank_geq_iff G D' k₂).mpr (le_of_eq h_k₂) E₂ ⟨h_E₂_eff, h_E₂_deg⟩
    -- Show winnability of sum
    rw [h_sum]
    have h := winnable_add_winnable G (D-E₁) (D'-E₂) h_D_win h_D'_win
    rw [show D - E₁ + (D' - E₂) = (D + D') - (E₁ + E₂) by abel] at h
    exact h
  have h_final := (rank_geq_iff G (D+D') (k₁+k₂)).mp h_rank_geq
  linarith

/-- **Clifford's theorem:** If $r(D) \geq 0$ and $r(K_G - D) \geq 0$, then
$r(D) \leq \frac12 \deg(D)$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 5.13. -/
theorem clifford_theorem
    {G : CFGraph} (h_conn : graphConnected G) (D : CFDiv G)
    (h_D : rank G D ≥ 0)
    (h_KD : rank G (canonicalDivisor G - D) ≥ 0) :
    (rank G D : ℚ) ≤ (deg D : ℚ) / 2 := by
  -- Get canonical divisor K's rank using Riemann-Roch
  have h_K_rank : rank G (canonicalDivisor G) = genus G - 1 := by
    -- Apply Riemann-Roch with D = K
    have h_rr := riemann_roch_for_graphs h_conn (canonicalDivisor G)
    -- For K-K = 0, rank is 0
    have h_K_minus_K : rank G (canonicalDivisor G - canonicalDivisor G) = 0 := by
      -- Show that this divisor is the zero divisor
      have h1 : (canonicalDivisor G - canonicalDivisor G) = 0 := by
        simp only [sub_self]
      -- Show that the zero divisor has rank 0
      have h2 : rank G 0 = 0 := zero_divisor_rank G
      -- Substitute back
      rw [h1, h2]
    -- Substitute into Riemann-Roch
    rw [h_K_minus_K] at h_rr
    -- Use degree_of_canonical_divisor
    rw [degree_of_canonical_divisor] at h_rr
    -- Solve for rank G K
    linarith
  -- Apply rank subadditivity
  have h_subadd := rank_subadditive G D (canonicalDivisor G - D) h_D h_KD
  -- The sum D + (K-D) = K
  have h_sum : (D + (canonicalDivisor G - D)) = canonicalDivisor G := by
    funext v
    simp only [Pi.add_apply, Pi.sub_apply, add_sub_cancel]
  rw [h_sum] at h_subadd
  rw [h_K_rank] at h_subadd
  -- Use Riemann-Roch to get r(K-D) in terms of r(D)
  have h_rr := riemann_roch_for_graphs h_conn D
  -- Combining subadditivity and Riemann-Roch gives 2 r(D) ≤ deg D; conclude in ℚ
  have h_two : 2 * rank G D ≤ deg D := by linarith
  have h_two' : (2 : ℚ) * (rank G D : ℚ) ≤ (deg D : ℚ) := by exact_mod_cast h_two
  linarith

/-- The rank of a divisor in terms of its degree:
  - $\deg(D) < 0 \Rightarrow r(D) = -1$
  - $0 \leq \deg(D) \leq 2g-2 \Rightarrow r(D) \leq \deg(D)/2$
  - $\deg(D) > 2g-2 \Rightarrow r(D) = \deg(D) - g$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 5.14. -/
theorem rank_nonspecial_range
  {G : CFGraph} (h_conn : graphConnected G) (D : CFDiv G) :
  -- Part 1
  (deg D < 0 → rank G D = -1) ∧
  -- Part 2
  (0 ≤ (deg D : ℚ) ∧ (deg D : ℚ) ≤ 2 * (genus G : ℚ) - 2 → (rank G D : ℚ) ≤ (deg D : ℚ) / 2) ∧
  -- Part 3
  (deg D > 2 * genus G - 2 → rank G D = deg D - genus G) := by
  constructor
  · -- Part 1: deg(D) < 0 implies r(D) = -1
    exact rank_neg_one_of_deg_neg G D
  constructor
  · -- Part 2: 0 ≤ deg(D) ≤ 2g-2 implies r(D) ≤ deg(D)/2
    intro ⟨h_deg_nonneg, h_deg_upper⟩
    by_cases h_rank : rank G D ≥ 0
    · -- Case where r(D) ≥ 0
      let K := canonicalDivisor G
      by_cases h_rankKD : rank G (K - D) ≥ 0
      · -- Case where r(K-D) ≥ 0: use Clifford's theorem
        exact clifford_theorem h_conn D h_rank h_rankKD
      · -- Case where r(K-D) = -1: use Riemann-Roch
        have h_rr := riemann_roch_for_graphs h_conn D
        rw [rank_neg_one_of_not_nonneg G (K - D) h_rankKD] at h_rr
        -- So r(D) = deg D - g, which is at most deg D / 2 since deg D ≤ 2g - 2
        have h_rank_eq : rank G D = deg D - genus G := by linarith
        rw [h_rank_eq]
        push_cast
        linarith
    · -- Case where r(D) < 0
      rw [rank_neg_one_of_not_nonneg G D h_rank]
      push_cast
      linarith
  · -- Part 3: deg(D) > 2g-2 implies r(D) = deg(D) - g
    intro h_deg_large
    -- K-D has negative degree, hence rank -1
    have h_rankKD : rank G (canonicalDivisor G - D) = -1 := by
      apply rank_neg_one_of_deg_neg
      rw [deg.map_sub, degree_of_canonical_divisor]
      linarith
    -- Apply Riemann-Roch to get r(D) = deg(D) - g
    have h_rr := riemann_roch_for_graphs h_conn D
    rw [h_rankKD] at h_rr
    linarith

/-!
## Gonality

The Riemann-Roch theorem provides some basic information about the *(divisorial) gonality*
of a graph.
-/

/-- The relation $\operatorname{gon}(G) \le k$: there exists a divisor of degree $k$
with rank at least $1$. -/
def gonalityLeq (G : CFGraph) (k : ℤ) : Prop := ∃ D : CFDiv G, rank G D ≥ 1 ∧ deg D = k

/-- The relation $\operatorname{gon}(G) \ge k$: no divisor of degree less than $k$
has rank at least $1$. -/
def gonalityGeq (G : CFGraph) (k : ℤ) : Prop :=
  ∀ l : ℤ, l < k → ¬ gonalityLeq G l

/-- A connected graph has gonality at most $g+1$, where $g$ is its genus. -/
theorem gonality_leq_genus_add_one
    {G : CFGraph} (h_conn : graphConnected G) : gonalityLeq G (genus G + 1) := by
  let q : G.V := Classical.arbitrary G.V
  let D : CFDiv G := (genus G + 1) • oneChip q
  have h_deg_D : deg D = genus G + 1 := by
    dsimp only [D]
    rw [map_zsmul, deg_one_chip, zsmul_one]
    simp only [Int.cast_add, Int.cast_eq, Int.cast_one]
  have h_rank_geq : rankGeq G D 1 := by
    intro E hE
    dsimp only [effOfDegree, Set.mem_ofPred_eq] at hE
    rcases hE with ⟨hE_eff, hE_deg⟩
    have h_deg_sub : deg (D - E) = genus G := by
      rw [deg.map_sub, h_deg_D, hE_deg]
      ring
    apply winnable_of_deg_ge_genus h_conn (D - E)
    rw [h_deg_sub]
  refine ⟨D, (rank_geq_iff G D 1).mp h_rank_geq, h_deg_D⟩

private theorem one_le_of_gonality_leq {G : CFGraph} {k : ℤ} (h_gon : gonalityLeq G k) : 1 ≤ k := by
  rcases h_gon with ⟨D, h_rank, h_deg⟩
  have h_rank_geq : rankGeq G D 1 := (rank_geq_iff G D 1).mpr h_rank
  have h_deg_lower : (1 : ℤ) ≤ deg D := rank_le_degree G D 1 (by norm_num) h_rank_geq
  simpa only [ge_iff_le, h_deg] using h_deg_lower

/-- The *(divisorial) gonality* of a connected graph is the smallest degree of a divisor
of rank at least one. -/
noncomputable def gonality {G : CFGraph} (_h_conn : graphConnected G) : ℤ :=
  sInf {k : ℤ | gonalityLeq G k}

/-- A connected graph has gonality at most $g+1$, where $g$ is its genus. -/
private lemma gonality_le_genus_add_one {G : CFGraph} (h_conn : graphConnected G) :
    gonality h_conn ≤ genus G + 1 := by
  let S : Set ℤ := {k : ℤ | gonalityLeq G k}
  have h_bdd : BddBelow S := by
    refine ⟨1, ?_⟩
    intro k hk
    exact one_le_of_gonality_leq hk
  dsimp only [gonality]
  exact csInf_le h_bdd (gonality_leq_genus_add_one h_conn)

/-- The gonality of a connected graph is at least $1$. -/
private lemma gonality_ge_one {G : CFGraph} (h_conn : graphConnected G) : 1 ≤ gonality h_conn := by
  let S : Set ℤ := {k : ℤ | gonalityLeq G k}
  have h_nonempty : S.Nonempty := by
    refine ⟨genus G + 1, ?_⟩
    exact gonality_leq_genus_add_one h_conn
  dsimp only [gonality]
  refine le_csInf h_nonempty ?_
  intro k hk
  exact one_le_of_gonality_leq hk

/-- The relation `gonalityGeq G k` is equivalent to the inequality `gonality h_conn ≥ k`. -/
@[simp] theorem gonality_geq_iff {G : CFGraph} (h_conn : graphConnected G) (k : ℤ) :
    gonalityGeq G k ↔ gonality h_conn ≥ k := by
  let S : Set ℤ := {l : ℤ | gonalityLeq G l}
  have h_nonempty : S.Nonempty := by
    refine ⟨genus G + 1, ?_⟩
    exact gonality_leq_genus_add_one h_conn
  have h_bdd : BddBelow S := by
    refine ⟨1, ?_⟩
    intro l hl
    exact one_le_of_gonality_leq hl
  constructor
  · intro h_geq
    dsimp only [gonality]
    refine le_csInf h_nonempty ?_
    intro l hl
    by_contra hlt
    have hlt' : l < k := by linarith
    exact h_geq l hlt' hl
  · intro h_gon l hl h_leq
    have h_inf_le : gonality h_conn ≤ l := by
      dsimp only [gonality]
      exact csInf_le h_bdd h_leq
    linarith

/-!
## Conjectures

This section records conjectures and theorems about gonality and Brill-Noether theory for
graphs that have not been formalized here.
-/

/-- The existence of graphs with maximum gonality: for every $g \ge 0$, there exists
a connected graph of genus $g$ with gonality exactly $\lfloor (g+3)/2 \rfloor$.

Posed by M. Baker in
[Specialization of linear systems from curves to graphs](https://doi.org/10.2140/ant.2008.2.613),
Conjecture 3.10(2). This is proved by Cools-Draisma-Payne-Robeva in
[A tropical proof of the Brill-Noether theorem](https://doi.org/10.1016/j.aim.2012.02.019),
and via a different construction by Hendrey in
[Sparse graphs of high gonality](https://doi.org/10.1137/16M1095329). We are not aware
of a formalization of this result. -/
def maxGonalityExistence (g : ℕ) : Prop :=
  ∃ (G : CFGraph.{u}) (h_conn : graphConnected G) (_g_eq : genus G = g),
    gonality h_conn = (g + 3) / 2

/-- The statement that in a given genus $g$, there exists a Brill-Noether general graph:
a graph with no divisor of degree $d$ and rank at least $r$ whenever
$$
\rho = g - (r+1)(g-d+r) < 0.
$$

The statement below uses the Riemann-Roch-equivalent form
$$
(r(D)+1)(r(K_G-D)+1) \le g
$$
for all divisors $D$, to avoid coercions between natural numbers and integers.

This is a slightly strengthened form of a conjecture posed in M. Baker,
[Specialization of linear systems from curves to graphs](https://doi.org/10.2140/ant.2008.2.613),
namely Conjecture 3.9(2). It was proved by Cools-Draisma-Payne-Robeva in
[A tropical proof of the Brill-Noether theorem](https://doi.org/10.1016/j.aim.2012.02.019),
but we are not aware of a formalization of this result. -/
def brillNoetherGeneralExistence (g : ℤ) : Prop :=
  ∃ (G : CFGraph.{u}) (_h_conn : graphConnected G) (_g_eq : genus G = g),
    ∀ (D : CFDiv G), (rank G D + 1) * (rank G (canonicalDivisor G - D) + 1) ≤ g

/-- The gonality conjecture for finite graphs: every connected graph of genus $g$ has gonality
at most $\lfloor (g+3)/2 \rfloor$.

This is an open problem, posed by Baker in
[Specialization of linear systems from curves to graphs](https://doi.org/10.2140/ant.2008.2.613),
Conjecture 3.10(1). -/
def gonalityConjecture {G : CFGraph} (h_conn : graphConnected G) : Prop :=
  gonality h_conn ≤ (genus G + 3) / 2

/-- The Brill-Noether conjecture for finite graphs: for every connected graph of genus $g$
and integers $r,d$ with
$$
\rho = g - (r+1)(g-d+r) \ge 0,
$$
there exists a divisor of degree $d$ and rank at least $r$.

This is an open problem, posed in slightly different form by Baker in
[Specialization of linear systems from curves to graphs](https://doi.org/10.2140/ant.2008.2.613),
Conjecture 3.9(1). -/
def brillNoetherConjecture {G : CFGraph} (_h_conn : graphConnected G) (r d : ℤ) : Prop :=
  let g := genus G
  let ρ := g - (r + 1) * (g - d + r)
  0 ≤ ρ → ∃ (D : CFDiv G), rank G D ≥ r ∧ deg D = d
