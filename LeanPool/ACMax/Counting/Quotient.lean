/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Cuts.Ind2K2

/-!
# The quotient (class-vector) master certificate

The opening move of the quotient program for the mid-range
`19 ≤ n ≤ 598 693`: by Haemers interlacing, for *any* partition of the vertex
set into `m` classes, `λ₂(G)` is at most the second eigenvalue of the `m×m`
quotient matrix — and for the *second* eigenvalue specifically, the quotient
bound is witnessed by a **class-constant test vector**, so it follows from the
universal single-vector certificate.  The value of the packaging is that the
Rayleigh data reduces to *aggregate* quantities: class sizes and inter-class
edge counts, exactly what the campaign's counting machinery produces.

* `classSize c i` — the size of class `i`;
* `interEdges G c i j` — the number of **ordered** adjacent pairs `(u,v)` with
  `u` in class `i` and `v` in class `j` (`interEdges i j = interEdges j i`;
  the diagonal counts internal edges twice but is killed by `(x i − x i)² = 0`);
* `algConn_le_two_of_class_vector` — the master: a class-valued vector `x`
  with `Σᵢ nᵢ xᵢ = 0` and

    `Σᵢⱼ Eᵢⱼ (xᵢ − xⱼ)² ≤ 4·Σᵢ nᵢ xᵢ²`

  certifies `algConn G ≤ 2`  (the `4` is `2 × 2`: one factor because ordered
  pairs double-count edges, one from the target `λ₂ ≤ 2`);
* `algConn_le_two_of_sparse_cut` — the classical Fiedler cut bound as the
  `m = 2` instance: `n·e(S, Sᶜ) ≤ 2·|S|·|Sᶜ|` certifies `algConn ≤ 2`
  (stated with the ordered cross count: `n·E ≤ 4·|S|·|Sᶜ|`);
* degree-class handshake identities on the residual cell, expressing the
  quotient data of the degree partition `{3}/{4}/{≥5}` in ledger terms.
-/

@[expose] public section

namespace ACMax

open Finset

variable {V : Type*} [Fintype V]

/-! ## Quotient data -/

open Classical in
/-- The size of class `i` under the class map `c`. -/
noncomputable def classSize {m : ℕ} (c : V → Fin m) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun v => c v = i)).card

open Classical in
/-- The number of **ordered** adjacent pairs from class `i` to class `j`. -/
noncomputable def interEdges {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) : ℕ :=
  ((Finset.univ.filter (fun v => c v = i)) ×ˢ
    (Finset.univ.filter (fun v => c v = j))).filter
      (fun p => G.Adj p.1 p.2) |>.card

open Classical in
/-- Fiberwise decomposition of a vertex sum by classes. -/
theorem sum_classes {m : ℕ} {M : Type*} [AddCommMonoid M]
    (c : V → Fin m) (f : V → M) :
    ∑ v : V, f v
      = ∑ i : Fin m, ∑ v ∈ Finset.univ.filter (fun v => c v = i), f v :=
  (Finset.sum_fiberwise Finset.univ c f).symm

open Classical in
/-- A class-constant square sum aggregates to class sizes. -/
theorem sum_sq_classes {m : ℕ} (c : V → Fin m) (x : Fin m → ℝ) :
    ∑ v : V, x (c v) ^ 2
      = ∑ i : Fin m, (classSize c i : ℝ) * x i ^ 2 := by
  rw [sum_classes c (fun v => x (c v) ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (fun v hv => by
    rw [(Finset.mem_filter.mp hv).2]), Finset.sum_const, nsmul_eq_mul]
  rfl

open Classical in
/-- The inter-class count as a double indicator sum over the fibers. -/
theorem interEdges_eq_sum {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) :
    (interEdges G c i j : ℝ)
      = ∑ u ∈ Finset.univ.filter (fun v => c v = i),
          ∑ v ∈ Finset.univ.filter (fun v => c v = j),
          (if G.Adj u v then (1 : ℝ) else 0) := by
  classical
  rw [interEdges, Finset.card_filter]
  push_cast
  rw [Finset.sum_product]

open Classical in
/-- The edge quadratic form aggregates to inter-class counts. -/
theorem sum_edge_sq_classes {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (x : Fin m → ℝ) :
    ∑ u : V, ∑ v : V,
        (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
      = ∑ i : Fin m, ∑ j : Fin m,
          (interEdges G c i j : ℝ) * (x i - x j) ^ 2 := by
  classical
  -- fiberwise in `u`, then in `v`
  rw [sum_classes c (fun u => ∑ v : V,
    (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hswap : ∑ u ∈ Finset.univ.filter (fun v => c v = i), ∑ v : V,
      (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
      = ∑ j : Fin m, ∑ u ∈ Finset.univ.filter (fun v => c v = i),
          ∑ v ∈ Finset.univ.filter (fun v => c v = j),
          (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0) := by
    have h1 : ∀ u : V, ∑ v : V,
        (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)
        = ∑ j : Fin m, ∑ v ∈ Finset.univ.filter (fun v => c v = j),
            (if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0) := fun u =>
      (Finset.sum_fiberwise Finset.univ c
        (fun v => if G.Adj u v then (x (c u) - x (c v)) ^ 2 else 0)).symm
    rw [Finset.sum_congr rfl fun u _ => h1 u]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [interEdges_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2]
  split <;> ring

/-! ## The master certificate -/

open Classical in
/-- **The quotient master certificate** (Haemers interlacing for `λ₂`).
Given a partition into `m` classes and a class-valued vector `x` with

* balance: `Σᵢ nᵢ·xᵢ = 0`,
* some class of nonzero value is inhabited, and
* the aggregate Rayleigh bound `Σᵢⱼ Eᵢⱼ·(xᵢ − xⱼ)² ≤ 4·Σᵢ nᵢ·xᵢ²`
  (`Eᵢⱼ` the ordered inter-class adjacency counts),

we get `algConn G ≤ 2`.  All data is aggregate: sizes and edge counts. -/
theorem algConn_le_two_of_class_vector [Nonempty V]
    (G : SimpleGraph V) {m : ℕ} (c : V → Fin m) (x : Fin m → ℝ)
    (hbal : ∑ i : Fin m, (classSize c i : ℝ) * x i = 0)
    (hne : ∃ v : V, x (c v) ≠ 0)
    (hQ : ∑ i : Fin m, ∑ j : Fin m,
        (interEdges G c i j : ℝ) * (x i - x j) ^ 2
      ≤ 4 * ∑ i : Fin m, (classSize c i : ℝ) * x i ^ 2) :
    algConn G ≤ 2 := by
  classical
  have hbal' : ∑ v : V, x (c v) = 0 := by
    have h1 : ∑ v : V, x (c v) = ∑ i : Fin m, (classSize c i : ℝ) * x i := by
      rw [sum_classes c (fun v => x (c v))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [(Finset.mem_filter.mp hv).2]), Finset.sum_const, nsmul_eq_mul]
      rfl
    rw [h1, hbal]
  apply algConn_le_two_of_testvector G (fun v => x (c v)) hbal' hne
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']
  rw [sum_edge_sq_classes G c x, sum_sq_classes c x]
  linarith [hQ]

/-! ## The classical sparse-cut instance (`m = 2`) -/

open Classical in
/-- **The Fiedler sparse-cut bound.**  For a nonempty proper `S ⊆ V` with cut
count `e(S,Sᶜ)` (each cross edge counted once, as a pair in `S ×ˢ Sᶜ`)
satisfying the classical `n·e(S,Sᶜ) ≤ 2·|S|·|Sᶜ|`, we get `algConn ≤ 2`. -/
theorem algConn_le_two_of_sparse_cut [Nonempty V]
    (G : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (hcut : (Fintype.card V)
        * ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card
      ≤ 2 * S.card * Sᶜ.card) :
    algConn G ≤ 2 := by
  classical
  set c : V → Fin 2 := fun v => if v ∈ S then 0 else 1 with hc
  set x : Fin 2 → ℝ := fun i => if i = 0 then (Sᶜ.card : ℝ) else -(S.card : ℝ)
    with hx
  have hfib0 : Finset.univ.filter (fun v => c v = 0) = S := by
    ext v
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hc]
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv]
      exact ⟨fun _ => hv, fun _ => rfl⟩
    · rw [ite_eq_right hv]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h hv⟩
  have hfib1 : Finset.univ.filter (fun v => c v = 1) = Sᶜ := by
    ext v
    rw [Finset.mem_filter, Finset.mem_compl]
    simp only [Finset.mem_univ, true_and, hc]
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv]
      exact ⟨fun h => absurd h (by decide), fun h => absurd hv h⟩
    · rw [ite_eq_right hv]
      exact ⟨fun _ => hv, fun _ => rfl⟩
  have hcs0 : classSize c 0 = S.card := by rw [classSize, hfib0]
  have hcs1 : classSize c 1 = Sᶜ.card := by rw [classSize, hfib1]
  have hx0 : x 0 = (Sᶜ.card : ℝ) := by rw [hx]; norm_num
  have hx1 : x 1 = -(S.card : ℝ) := by rw [hx]; norm_num
  -- inter-class counts: the two cross entries are the ordered cut count
  have hE01 : interEdges G c 0 1
      = ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
    rw [interEdges, hfib0, hfib1]
  have hE10 : interEdges G c 1 0
      = ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
    rw [interEdges, hfib1, hfib0]
    -- transpose bijection
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩
    · intro p hp q hq hpq
      exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩
  obtain ⟨s₀, hs₀⟩ := hS
  refine algConn_le_two_of_class_vector G c x ?_ ⟨s₀, ?_⟩ ?_
  · -- balance
    rw [Fin.sum_univ_two, hcs0, hcs1, hx0, hx1]
    ring
  · -- nonzero at a vertex of `S`
    have : c s₀ = 0 := by
      rw [hc]
      simp [hs₀]
    rw [this, hx0]
    have : 0 < Sᶜ.card := Finset.card_pos.mpr hSc
    positivity
  · -- the aggregate Rayleigh bound
    simp only [Fin.sum_univ_two]
    rw [hE01, hE10, hcs0, hcs1, hx0, hx1]
    have hVn : (Fintype.card V : ℝ) = (S.card : ℝ) + (Sᶜ.card : ℝ) := by
      have := Finset.card_add_card_compl S
      exact_mod_cast this.symm
    have hcutR : (Fintype.card V : ℝ)
        * (((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card : ℝ)
        ≤ 2 * (S.card : ℝ) * (Sᶜ.card : ℝ) := by
      have h1 : ((Fintype.card V
          * ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card : ℕ) : ℝ)
          ≤ ((2 * S.card * Sᶜ.card : ℕ) : ℝ) := Nat.cast_le.mpr hcut
      push_cast at h1
      linarith
    have hcS : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hcSc : (0 : ℝ) ≤ (Sᶜ.card : ℝ) := Nat.cast_nonneg _
    have hEc : (0 : ℝ)
        ≤ (((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card : ℝ) :=
      Nat.cast_nonneg _
    have hsum0 : (0 : ℝ) ≤ (S.card : ℝ) + (Sᶜ.card : ℝ) := by linarith
    rw [hVn] at hcutR
    nlinarith [mul_le_mul_of_nonneg_left hcutR hsum0, hcS, hcSc, hEc]

/-! ## Handshake identities for the quotient data -/

open Classical in
/-- Inter-class counts are symmetric. -/
theorem interEdges_symm {m : ℕ} (G : SimpleGraph V) (c : V → Fin m)
    (i j : Fin m) : interEdges G c i j = interEdges G c j i := by
  classical
  rw [interEdges, interEdges]
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩
  · intro p _ q _ hpq
    exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
  · intro p hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, G.adj_symm hp.2⟩

/-! ## The two-cluster law (`m = 3`) -/

open Classical in
/-- **The two-cluster law.**  Two disjoint nonempty vertex sets with *no*
edges between them and boundaries `∂₁, ∂₂` (ordered counts of edges leaving
each cluster) satisfying

  `∂₁·|S₂|² + ∂₂·|S₁|² ≤ 2·|S₁|·|S₂|·(|S₁| + |S₂|)`

certify `algConn ≤ 2`.  For equal sizes `s` this reads `∂₁ + ∂₂ ≤ 4s` —
e.g. two disjoint `M`-edges with no cross edges fire at the exact tie
(`∂ = 4` each, `s = 2`), recovering the cell's `2K₂` exclusion. -/
theorem algConn_le_two_of_two_clusters [Nonempty V]
    (G : SimpleGraph V) (S₁ S₂ : Finset V)
    (hS₁ : S₁.Nonempty) (hS₂ : S₂.Nonempty) (hdisj : Disjoint S₁ S₂)
    (hnc : ∀ u ∈ S₁, ∀ v ∈ S₂, ¬G.Adj u v)
    (hcut : ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
          * S₂.card ^ 2
        + ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
          * S₁.card ^ 2
      ≤ 2 * S₁.card * S₂.card * (S₁.card + S₂.card)) :
    algConn G ≤ 2 := by
  classical
  set c : V → Fin 3 := fun v => if v ∈ S₁ then 0 else if v ∈ S₂ then 1 else 2
    with hc
  set x : Fin 3 → ℝ := fun i =>
    if i = 0 then (S₂.card : ℝ) else if i = 1 then -(S₁.card : ℝ) else 0
    with hx
  have hfib0 : Finset.univ.filter (fun v => c v = 0) = S₁ := by
    ext v
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hc]
    by_cases h1 : v ∈ S₁
    · rw [ite_eq_left h1]
      exact ⟨fun _ => h1, fun _ => rfl⟩
    · rw [ite_eq_right h1]
      by_cases h2 : v ∈ S₂
      · rw [ite_eq_left h2]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
      · rw [ite_eq_right h2]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  have hfib1 : Finset.univ.filter (fun v => c v = 1) = S₂ := by
    ext v
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, hc]
    by_cases h1 : v ∈ S₁
    · rw [ite_eq_left h1]
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      exact absurd (Finset.disjoint_left.mp hdisj h1) (fun hh => hh h)
    · rw [ite_eq_right h1]
      by_cases h2 : v ∈ S₂
      · rw [ite_eq_left h2]
        exact ⟨fun _ => h2, fun _ => rfl⟩
      · rw [ite_eq_right h2]
        exact ⟨fun h => absurd h (by decide), fun h => absurd h h2⟩
  have hfib2 : Finset.univ.filter (fun v => c v = 2) = (S₁ ∪ S₂)ᶜ := by
    ext v
    rw [Finset.mem_filter, Finset.mem_compl, Finset.mem_union]
    simp only [Finset.mem_univ, true_and, hc]
    by_cases h1 : v ∈ S₁
    · rw [ite_eq_left h1]
      exact ⟨fun h => absurd h (by decide), fun h => absurd (Or.inl h1) h⟩
    · rw [ite_eq_right h1]
      by_cases h2 : v ∈ S₂
      · rw [ite_eq_left h2]
        exact ⟨fun h => absurd h (by decide), fun h => absurd (Or.inr h2) h⟩
      · rw [ite_eq_right h2]
        exact ⟨fun _ => fun h => h.elim (fun hh => h1 hh) (fun hh => h2 hh),
          fun _ => rfl⟩
  have hx0 : x 0 = (S₂.card : ℝ) := by simp [hx]
  have hx1 : x 1 = -(S₁.card : ℝ) := by simp [hx]
  have hx2 : x 2 = 0 := by simp [hx]
  obtain ⟨s₀, hs₀⟩ := hS₁
  refine algConn_le_two_of_class_vector G c x ?_ ⟨s₀, ?_⟩ ?_
  · -- balance
    rw [Fin.sum_univ_three, classSize, classSize, classSize,
      hfib0, hfib1, hfib2, hx0, hx1, hx2]
    ring
  · -- nonzero at a vertex of `S₁`
    have hcs : c s₀ = 0 := by
      rw [hc]
      simp [hs₀]
    rw [hcs, hx0]
    have : 0 < S₂.card := Finset.card_pos.mpr hS₂
    exact ne_of_gt (by exact_mod_cast this)
  · -- the aggregate Rayleigh bound
    simp only [Fin.sum_univ_three]
    rw [classSize, classSize, classSize, hfib0, hfib1, hfib2]
    -- the S₁–S₂ blocks vanish
    have hE01 : interEdges G c 0 1 = 0 := by
      rw [interEdges, hfib0, hfib1, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      intro p hp
      rw [Finset.mem_product] at hp
      exact hnc p.1 hp.1 p.2 hp.2
    have hE10 : interEdges G c 1 0 = 0 := by
      rw [interEdges_symm, hE01]
    -- the boundary blocks
    have hE02 : interEdges G c 0 2
        = ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [interEdges, hfib0, hfib2]
    have hE12 : interEdges G c 1 2
        = ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [interEdges, hfib1, hfib2]
    have hE20 : interEdges G c 2 0
        = ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [interEdges_symm, hE02]
    have hE21 : interEdges G c 2 1
        = ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [interEdges_symm, hE12]
    rw [hE01, hE10, hE02, hE12, hE20, hE21, hx0, hx1, hx2]
    -- cast the cut hypothesis and close
    set e₁ : ℕ := ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
    set e₂ : ℕ := ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
    have hcutR : (e₁ : ℝ) * (S₂.card : ℝ) ^ 2 + (e₂ : ℝ) * (S₁.card : ℝ) ^ 2
        ≤ 2 * (S₁.card : ℝ) * (S₂.card : ℝ)
          * ((S₁.card : ℝ) + (S₂.card : ℝ)) := by
      have h1 : ((e₁ * S₂.card ^ 2 + e₂ * S₁.card ^ 2 : ℕ) : ℝ)
          ≤ ((2 * S₁.card * S₂.card * (S₁.card + S₂.card) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcut
      push_cast at h1
      linarith
    ring_nf
    nlinarith [hcutR]

/-! ## The degree-class partition on the residual cell -/

variable {n : ℕ}

/-! ## The two-hub block cut (the endgame seed) -/

open Classical in
/-- **The single-hub block cut.**  A hub `g` with `k` degree-3 twins forms a
block `{g} ∪ K` of size `k+1` whose boundary is at most `d_g + k` (the hub
leaks its non-twin degree `d−k`; each twin leaks its two non-`g` neighbours).
Under `n·(d_g + k) ≤ 2·(k+1)·(n−k−1)` — asymptotically `d_g ≤ k + 2`, the
capped-class condition as an exact tie — the block fires `algConn ≤ 2`. -/
theorem algConn_le_two_of_hub_block [Nonempty V] (G : SimpleGraph V)
    (g : V) (K : Finset V) (hgK : g ∉ K)
    (hK : ∀ t ∈ K, G.Adj g t) (hK3 : ∀ t ∈ K, G.degree t = 3)
    (hSc : ((insert g K) : Finset V)ᶜ.Nonempty)
    (hcut : Fintype.card V * (G.degree g + K.card)
      ≤ 2 * (K.card + 1) * (((insert g K) : Finset V)ᶜ).card) :
    algConn G ≤ 2 := by
  classical
  set S : Finset V := insert g K with hS
  have hScard : S.card = K.card + 1 := by
    rw [hS, Finset.card_insert_of_notMem hgK]
  have hext : ∀ (x : V) (W : Finset V), W ⊆ G.neighborFinset x ∩ S →
      (G.neighborFinset x ∩ Sᶜ).card ≤ G.degree x - W.card := by
    intro x W hW
    have h1 : G.neighborFinset x ∩ Sᶜ = G.neighborFinset x \ S := by
      ext v
      simp [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
    have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset x) S
    have h3 : W.card ≤ (G.neighborFinset x ∩ S).card := Finset.card_le_card hW
    have h4 := G.card_neighborFinset_eq_degree x
    rw [h1]
    omega
  have hcount : ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card
      ≤ G.degree g + K.card := by
    have hsum : ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card
        = ∑ s ∈ S, (G.neighborFinset s ∩ Sᶜ).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hset : G.neighborFinset s ∩ Sᶜ
          = Sᶜ.filter (fun v => G.Adj s v) := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_filter,
          SimpleGraph.mem_neighborFinset]
        exact and_comm
      rw [hset, Finset.card_filter]
    rw [hsum]
    have hdec : ∑ s ∈ S, (G.neighborFinset s ∩ Sᶜ).card
        = (G.neighborFinset g ∩ Sᶜ).card
          + ∑ t ∈ K, (G.neighborFinset t ∩ Sᶜ).card := by
      rw [hS, Finset.sum_insert hgK]
    have hKN : K ⊆ G.neighborFinset g ∩ S := by
      intro t ht
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hK t ht, by
        rw [hS]
        exact Finset.mem_insert_of_mem ht⟩
    have hgext := hext g K hKN
    have htext : ∀ t ∈ K, (G.neighborFinset t ∩ Sᶜ).card ≤ 2 := by
      intro t ht
      have hpair : ({g} : Finset V) ⊆ G.neighborFinset t ∩ S := by
        intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨(hK t ht).symm, by
          rw [hS]
          exact Finset.mem_insert_self _ _⟩
      have h5 := hext t ({g}) hpair
      rw [Finset.card_singleton, hK3 t ht] at h5
      omega
    have hKsum : ∑ t ∈ K, (G.neighborFinset t ∩ Sᶜ).card ≤ 2 * K.card := by
      calc ∑ t ∈ K, (G.neighborFinset t ∩ Sᶜ).card
          ≤ ∑ _t ∈ K, 2 := Finset.sum_le_sum htext
        _ = 2 * K.card := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have hkd : K.card ≤ G.degree g := by
      calc K.card ≤ (G.neighborFinset g ∩ S).card := Finset.card_le_card hKN
        _ ≤ (G.neighborFinset g).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree g := G.card_neighborFinset_eq_degree g
    omega
  refine algConn_le_two_of_sparse_cut G S ?_ hSc ?_
  · exact ⟨g, by
      rw [hS]
      exact Finset.mem_insert_self _ _⟩
  · calc Fintype.card V * ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card
        ≤ Fintype.card V * (G.degree g + K.card) :=
          Nat.mul_le_mul_left _ hcount
      _ ≤ 2 * (K.card + 1) * Sᶜ.card := hcut
      _ = 2 * S.card * Sᶜ.card := by rw [hScard]

open Classical in
/-- Instance-free form of the single-hub block cut: the statement mentions
only cardinalities, so it applies verbatim from any `DecidableEq` context. -/
theorem algConn_le_two_of_hub_block' [Nonempty V] (G : SimpleGraph V)
    (g : V) (K : Finset V) (hgK : g ∉ K)
    (hK : ∀ t ∈ K, G.Adj g t) (hK3 : ∀ t ∈ K, G.degree t = 3)
    (hn : K.card + 1 < Fintype.card V)
    (hcut : Fintype.card V * (G.degree g + K.card)
      ≤ 2 * (K.card + 1) * (Fintype.card V - (K.card + 1))) :
    algConn G ≤ 2 := by
  classical
  have hcompl : (((insert g K) : Finset V)ᶜ).card
      = Fintype.card V - (K.card + 1) := by
    rw [Finset.card_compl, Finset.card_insert_of_notMem hgK]
  refine algConn_le_two_of_hub_block G g K hgK hK hK3 ?_ ?_
  · rw [← Finset.card_pos, hcompl]
    omega
  · rw [hcompl]
    exact hcut

open Classical in
/-- **The double-star cut** (the v66 tie-breaker).  Two non-adjacent hubs with
disjoint, mutually non-adjacent twin blocks `{gᵢ} ∪ Kᵢ` fire the two-cluster
law under the exact condition

  `(d₁+k₁)(k₂+1)² + (d₂+k₂)(k₁+1)² ≤ 2(k₁+1)(k₂+1)(k₁+k₂+2)`

— equivalently `(ε₁−2)(k₂+1)² + (ε₂−2)(k₁+1)² ≤ 0` for `εᵢ = dᵢ − kᵢ`, which
holds for EVERY DS-unblocked intDeg-pattern once `k₁ ≥ k₂`.  No largeness of
`n` is required. -/
theorem algConn_le_two_of_double_star [Nonempty V] (G : SimpleGraph V)
    (g₁ g₂ : V) (K₁ K₂ : Finset V) (hg₁K₁ : g₁ ∉ K₁) (hg₂K₂ : g₂ ∉ K₂)
    (hK₁a : ∀ t ∈ K₁, G.Adj g₁ t) (hK₁3 : ∀ t ∈ K₁, G.degree t = 3)
    (hK₂a : ∀ t ∈ K₂, G.Adj g₂ t) (hK₂3 : ∀ t ∈ K₂, G.degree t = 3)
    (hdisj : Disjoint (insert g₁ K₁ : Finset V) (insert g₂ K₂ : Finset V))
    (hnc : ∀ u ∈ (insert g₁ K₁ : Finset V), ∀ v ∈ (insert g₂ K₂ : Finset V),
      ¬G.Adj u v)
    (hcond : (G.degree g₁ + K₁.card) * (K₂.card + 1) ^ 2
        + (G.degree g₂ + K₂.card) * (K₁.card + 1) ^ 2
      ≤ 2 * (K₁.card + 1) * (K₂.card + 1) * (K₁.card + K₂.card + 2)) :
    algConn G ≤ 2 := by
  classical
  set S₁ : Finset V := insert g₁ K₁ with hS₁def
  set S₂ : Finset V := insert g₂ K₂ with hS₂def
  have hS₁card : S₁.card = K₁.card + 1 := by
    rw [hS₁def, Finset.card_insert_of_notMem hg₁K₁]
  have hS₂card : S₂.card = K₂.card + 1 := by
    rw [hS₂def, Finset.card_insert_of_notMem hg₂K₂]
  -- generic external-count against the union
  have hext : ∀ (x : V) (W : Finset V), W ⊆ G.neighborFinset x ∩ (S₁ ∪ S₂) →
      (G.neighborFinset x ∩ (S₁ ∪ S₂)ᶜ).card ≤ G.degree x - W.card := by
    intro x W hW
    have h1 : G.neighborFinset x ∩ (S₁ ∪ S₂)ᶜ
        = G.neighborFinset x \ (S₁ ∪ S₂) := by
      ext v
      simp [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
    have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset x) (S₁ ∪ S₂)
    have h3 : W.card ≤ (G.neighborFinset x ∩ (S₁ ∪ S₂)).card :=
      Finset.card_le_card hW
    have h4 := G.card_neighborFinset_eq_degree x
    rw [h1]
    omega
  -- per-cluster cut counts
  have hcount : ∀ (g : V) (K : Finset V), g ∉ K → (∀ t ∈ K, G.Adj g t) →
      (∀ t ∈ K, G.degree t = 3) → (insert g K : Finset V) ⊆ S₁ ∪ S₂ →
      (((insert g K : Finset V) ×ˢ (S₁ ∪ S₂)ᶜ).filter
          (fun p => G.Adj p.1 p.2)).card
        ≤ G.degree g + K.card := by
    intro g K hgK hKa hK3 hsub
    have hsum : (((insert g K : Finset V) ×ˢ (S₁ ∪ S₂)ᶜ).filter
          (fun p => G.Adj p.1 p.2)).card
        = ∑ s ∈ (insert g K : Finset V),
            (G.neighborFinset s ∩ (S₁ ∪ S₂)ᶜ).card := by
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hset : G.neighborFinset s ∩ (S₁ ∪ S₂)ᶜ
          = (S₁ ∪ S₂)ᶜ.filter (fun v => G.Adj s v) := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_filter,
          SimpleGraph.mem_neighborFinset]
        exact and_comm
      rw [hset, Finset.card_filter]
    rw [hsum, Finset.sum_insert hgK]
    have hKN : K ⊆ G.neighborFinset g ∩ (S₁ ∪ S₂) := by
      intro t ht
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hKa t ht, hsub (Finset.mem_insert_of_mem ht)⟩
    have hgext := hext g K hKN
    have htext : ∀ t ∈ K, (G.neighborFinset t ∩ (S₁ ∪ S₂)ᶜ).card ≤ 2 := by
      intro t ht
      have hpair : ({g} : Finset V) ⊆ G.neighborFinset t ∩ (S₁ ∪ S₂) := by
        intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨(hKa t ht).symm, hsub (Finset.mem_insert_self _ _)⟩
      have h5 := hext t ({g}) hpair
      rw [Finset.card_singleton, hK3 t ht] at h5
      omega
    have hKsum : ∑ t ∈ K, (G.neighborFinset t ∩ (S₁ ∪ S₂)ᶜ).card
        ≤ 2 * K.card := by
      calc ∑ t ∈ K, (G.neighborFinset t ∩ (S₁ ∪ S₂)ᶜ).card
          ≤ ∑ _t ∈ K, 2 := Finset.sum_le_sum htext
        _ = 2 * K.card := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have hkd : K.card ≤ G.degree g := by
      calc K.card ≤ (G.neighborFinset g ∩ (S₁ ∪ S₂)).card :=
            Finset.card_le_card hKN
        _ ≤ (G.neighborFinset g).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree g := G.card_neighborFinset_eq_degree g
    omega
  have hc₁ := hcount g₁ K₁ hg₁K₁ hK₁a hK₁3 Finset.subset_union_left
  have hc₂ := hcount g₂ K₂ hg₂K₂ hK₂a hK₂3 Finset.subset_union_right
  refine algConn_le_two_of_two_clusters G S₁ S₂
    ⟨g₁, by
      rw [hS₁def]
      exact Finset.mem_insert_self _ _⟩
    ⟨g₂, by
      rw [hS₂def]
      exact Finset.mem_insert_self _ _⟩
    hdisj hnc ?_
  calc ((S₁ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card * S₂.card ^ 2
        + ((S₂ ×ˢ (S₁ ∪ S₂)ᶜ).filter (fun p => G.Adj p.1 p.2)).card
          * S₁.card ^ 2
      ≤ (G.degree g₁ + K₁.card) * S₂.card ^ 2
        + (G.degree g₂ + K₂.card) * S₁.card ^ 2 :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hc₁) (Nat.mul_le_mul_right _ hc₂)
    _ = (G.degree g₁ + K₁.card) * (K₂.card + 1) ^ 2
        + (G.degree g₂ + K₂.card) * (K₁.card + 1) ^ 2 := by
        rw [hS₁card, hS₂card]
    _ ≤ 2 * (K₁.card + 1) * (K₂.card + 1) * (K₁.card + K₂.card + 2) := hcond
    _ = 2 * S₁.card * S₂.card * (S₁.card + S₂.card) := by
        rw [hS₁card, hS₂card]
        ring

open Classical in
/-- Pointwise form of the double-star cut: all hypotheses are adjacency
statements and cardinalities, so it applies verbatim from any `DecidableEq`
context. -/
theorem algConn_le_two_of_double_star' [Nonempty V] (G : SimpleGraph V)
    (g₁ g₂ : V) (K₁ K₂ : Finset V) (hg₁K₁ : g₁ ∉ K₁) (hg₂K₂ : g₂ ∉ K₂)
    (hK₁a : ∀ t ∈ K₁, G.Adj g₁ t) (hK₁3 : ∀ t ∈ K₁, G.degree t = 3)
    (hK₂a : ∀ t ∈ K₂, G.Adj g₂ t) (hK₂3 : ∀ t ∈ K₂, G.degree t = 3)
    (hne : g₁ ≠ g₂) (hg₁K₂ : g₁ ∉ K₂) (hg₂K₁ : g₂ ∉ K₁)
    (hKdisj : Disjoint K₁ K₂)
    (hgg : ¬G.Adj g₁ g₂)
    (hgt₂ : ∀ t ∈ K₂, ¬G.Adj g₁ t) (hgt₁ : ∀ t ∈ K₁, ¬G.Adj g₂ t)
    (htt : ∀ t₁ ∈ K₁, ∀ t₂ ∈ K₂, ¬G.Adj t₁ t₂)
    (hcond : (G.degree g₁ + K₁.card) * (K₂.card + 1) ^ 2
        + (G.degree g₂ + K₂.card) * (K₁.card + 1) ^ 2
      ≤ 2 * (K₁.card + 1) * (K₂.card + 1) * (K₁.card + K₂.card + 2)) :
    algConn G ≤ 2 := by
  classical
  refine algConn_le_two_of_double_star G g₁ g₂ K₁ K₂ hg₁K₁ hg₂K₂
    hK₁a hK₁3 hK₂a hK₂3 ?_ ?_ hcond
  · rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with h1 | h1
      · exact hne h1
      · exact hg₁K₂ h1
    · rcases hb with rfl | hb
      · exact hg₂K₁ ha
      · exact (Finset.disjoint_left.mp hKdisj ha) hb
  · intro u hu v hv
    rw [Finset.mem_insert] at hu hv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact hgg
      · exact hgt₂ v hv
    · rcases hv with rfl | hv
      · exact fun hA => hgt₁ u hu hA.symm
      · exact htt u hu v hv

open Classical in
/-- **The cherry-centre fire** (the per-`n` `CaseCherry` machinery, lifted):
a degree-3 vertex with two degree-3 neighbours fires the block cut at every
`n ≥ 18` — the centre plus its two twins form a `{y} ∪ K`-block of boundary
`5` against `2·3·(n−3)/n`.  The `M`-cherry dispatch branches of the per-`n`
proofs are instances of this statement. -/
theorem cherry_centre_fires (n : ℕ) [Nonempty (Fin n)] (hn : 18 ≤ n)
    (G : SimpleGraph (Fin n)) (y x z : Fin n) (hxz : x ≠ z)
    (hyx : G.Adj y x) (hyz : G.Adj y z)
    (hy3 : G.degree y = 3) (hx3 : G.degree x = 3) (hz3 : G.degree z = 3) :
    algConn G ≤ 2 := by
  classical
  have hyK : y ∉ ({x, z} : Finset (Fin n)) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact G.irrefl hyx
    · exact G.irrefl hyz
  have hKcard : ({x, z} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by
      rw [Finset.mem_singleton]
      exact hxz), Finset.card_singleton]
  have hcardV : Fintype.card (Fin n) = n := Fintype.card_fin n
  refine algConn_le_two_of_hub_block' G y ({x, z} : Finset (Fin n)) hyK
    ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hyx
    · exact hyz
  · intro t ht
    rw [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hx3
    · exact hz3
  · rw [hKcard, hcardV]
    omega
  · rw [hKcard, hcardV, hy3]
    -- `n·5 ≤ 6(n−3)` for `n ≥ 18`
    omega

open Classical in
/-- **The two-`M`-edge fire** (the `hmin` branch, lifted): two disjoint
degree-3 edges fire at every `n ≥ 18` — any cross adjacency creates a cherry
centre, and otherwise the four vertices induce a `2K₂` of degree sum `12`.
On the cell, more than one `M`-edge is fatal at every size. -/
theorem two_medges_fire (n : ℕ) [Nonempty (Fin n)] (hn : 18 ≤ n)
    (G : SimpleGraph (Fin n)) (t₁ t₂ t₃ t₄ : Fin n)
    (h12ne : t₁ ≠ t₂) (h13ne : t₁ ≠ t₃) (h14ne : t₁ ≠ t₄)
    (h23ne : t₂ ≠ t₃) (h24ne : t₂ ≠ t₄) (h34ne : t₃ ≠ t₄)
    (h12 : G.Adj t₁ t₂) (h34 : G.Adj t₃ t₄)
    (h1 : G.degree t₁ = 3) (h2 : G.degree t₂ = 3)
    (h3 : G.degree t₃ = 3) (h4 : G.degree t₄ = 3) :
    algConn G ≤ 2 := by
  classical
  by_cases h13 : G.Adj t₁ t₃
  · exact cherry_centre_fires n hn G t₁ t₂ t₃ h23ne h12 h13 h1 h2 h3
  by_cases h14 : G.Adj t₁ t₄
  · exact cherry_centre_fires n hn G t₁ t₂ t₄ h24ne h12 h14 h1 h2 h4
  by_cases h23 : G.Adj t₂ t₃
  · exact cherry_centre_fires n hn G t₂ t₁ t₃ h13ne h12.symm h23 h2 h1 h3
  by_cases h24 : G.Adj t₂ t₄
  · exact cherry_centre_fires n hn G t₂ t₁ t₄ h14ne h12.symm h24 h2 h1 h4
  · have hcard4 : ∀ (inst : DecidableEq (Fin n)),
        (@insert _ _ (@Finset.instInsert _ inst) t₁
          (@insert _ _ (@Finset.instInsert _ inst) t₂
            (@insert _ _ (@Finset.instInsert _ inst) t₃
              ({t₄} : Finset (Fin n))))).card = 4 := by
      intro inst
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨h12ne, h13ne, h14ne⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨h23ne, h24ne⟩),
        Finset.card_insert_of_notMem (by
          rw [Finset.mem_singleton]
          exact h34ne),
        Finset.card_singleton]
    exact algConn_le_two_of_ind_2K2 G t₁ t₂ t₃ t₄ (hcard4 _) h12 h34
      h13 h14 h23 h24 (by omega)

open Classical in
/-- **The `M`-dichotomy** (the counting cascade's re-armer): at every `n ≥ 18`,
either the graph fires or all `M`-edges coincide — two sharing edges make a
cherry centre, two disjoint ones a `2K₂`-or-cherry. -/
theorem medges_or_single (n : ℕ) [Nonempty (Fin n)] (hn : 18 ≤ n)
    (G : SimpleGraph (Fin n)) :
    algConn G ≤ 2 ∨
      ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
        G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
        G.degree t₄ = 3 →
        ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n)) := by
  classical
  by_cases hcherry : ∃ y x z : Fin n, x ≠ z ∧ G.Adj y x ∧ G.Adj y z
      ∧ G.degree y = 3 ∧ G.degree x = 3 ∧ G.degree z = 3
  · obtain ⟨y, x, z, hxz, hyx, hyz, hy, hx, hz⟩ := hcherry
    exact Or.inl (cherry_centre_fires n hn G y x z hxz hyx hyz hy hx hz)
  push Not at hcherry
  by_cases htwo : ∃ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ ∧ G.Adj t₃ t₄
      ∧ G.degree t₁ = 3 ∧ G.degree t₂ = 3 ∧ G.degree t₃ = 3
      ∧ G.degree t₄ = 3
      ∧ ({t₁, t₂} : Finset (Fin n)) ≠ ({t₃, t₄} : Finset (Fin n))
  · refine Or.inl ?_
    obtain ⟨t₁, t₂, t₃, t₄, h12, h34, hd1, hd2, hd3, hd4, hne⟩ := htwo
    by_cases e13 : t₁ = t₃
    · subst e13
      by_cases e24 : t₂ = t₄
      · subst e24
        exact absurd rfl hne
      · exact absurd h34 (by
          have := hcherry t₁ t₂ t₄ e24 h12
          tauto)
    by_cases e14 : t₁ = t₄
    · subst e14
      by_cases e23 : t₂ = t₃
      · subst e23
        exact absurd (Finset.pair_comm t₁ t₂) (by
          rw [Finset.pair_comm t₂ t₁] at hne
          exact fun h => hne (by rw [Finset.pair_comm]))
      · exact absurd h34.symm (by
          have := hcherry t₁ t₂ t₃ e23 h12
          tauto)
    by_cases e23 : t₂ = t₃
    · subst e23
      exact absurd h34 (by
        have := hcherry t₂ t₁ t₄ e14 h12.symm
        tauto)
    by_cases e24 : t₂ = t₄
    · subst e24
      exact absurd h34.symm (by
        have := hcherry t₂ t₁ t₃ e13 h12.symm
        tauto)
    · exact two_medges_fire n hn G t₁ t₂ t₃ t₄ (G.ne_of_adj h12) e13 e14
        e23 e24 (G.ne_of_adj h34) h12 h34 hd1 hd2 hd3 hd4
  · push Not at htwo
    refine Or.inr fun t₁ t₂ t₃ t₄ h12 h34 hd1 hd2 hd3 hd4 => ?_
    by_contra hne
    exact hne (htwo t₁ t₂ t₃ t₄ h12 h34 hd1 hd2 hd3 hd4)

end ACMax
