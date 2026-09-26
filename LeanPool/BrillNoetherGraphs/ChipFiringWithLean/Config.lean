/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Basic

/-! # Config -/

@[expose] public section
open Multiset Finset

/-!
## Configurations and superstable configurations

Fix a vertex $q \in V(G)$. A *configuration* (`Config G q`) is a nonnegative integer assignment
to the vertices $V(G) \setminus \{q\}$, extended by zero at $q$. This corresponds to what
Corry-Perkinson call a *nonnegative configuration*; we use "configuration"
to mean "nonnegative configuration" throughout this library.

A configuration $c$ is *superstable* if for every nonempty
$S \subseteq V(G) \setminus \{q\}$, some vertex in $S$ has fewer chips than its
out-degree to $V(G) \setminus S$. Equivalently, the associated divisor is $q$-reduced.
A *maximal superstable* configuration is one that is not dominated by any other
superstable configuration.

The quantity `outdegreeSet G S v` counts edges from $v$ to vertices outside $S$, and is the
relevant threshold for the superstability condition.
-/

/-- The set of vertices other than $q$: $\widetilde V = V(G) \setminus \{q\}$. -/
abbrev Vtilde {G : CFGraph} (q : G.V) : Finset G.V :=
  univ.filter (fun v => v ≠ q)

/-- A *configuration* on $G$ with respect to distinguished vertex $q$ is a nonnegative integer
assignment to all vertices, with the convention that $q$ holds zero chips. This is what
Corry-Perkinson call a *nonnegative configuration*.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 2.9. -/
structure Config (G : CFGraph) (q : G.V) where
  /-- The divisor recording the chip count at each vertex. -/
  (chips : CFDiv G)
  /-- The distinguished vertex $q$ has no chips. -/
  (q_zero : chips q = 0)
  /-- All chip counts are nonnegative. -/
  (non_negative : ∀ v : G.V, chips v ≥ 0)

/-- The degree of a configuration is the sum of all values away from $q$:
$$
\deg(c) = \sum_{v \in V(G)\setminus\{q\}} c(v).
$$
Since $c(q)=0$, this is implemented as the degree of the underlying divisor. -/
def configDegree {G : CFGraph} {q : G.V} (c : Config G q) : ℤ :=
  deg (c.chips)

/-- Converts a configuration $c$ to a divisor of prescribed degree $d$ by placing
$d-\deg(c)$ chips at $q$. -/
def toDiv {G : CFGraph} {q : G.V} (d : ℤ) (c : Config G q) : CFDiv G :=
  c.chips + (d - configDegree c) • (oneChip q)

/-- Two configurations are equal if their chip counts agree at every vertex. -/
@[ext] lemma Config.ext {q : G.V} {c₁ c₂ : Config G q}
    (h : ∀ v : G.V, c₁.chips v = c₂.chips v) : c₁ = c₂ := by
  obtain ⟨vd₁, _, _⟩ := c₁
  obtain ⟨vd₂, _, _⟩ := c₂
  simp only [mk.injEq]
  exact funext h

/-- Two configurations are equal if and only if their underlying divisors agree. -/
lemma eq_config_iff_eq_chips {q : G.V} (c₁ c₂ : Config G q) :
  c₁ = c₂ ↔ c₁.chips = c₂.chips :=
  ⟨fun h => by rw [h], fun h => Config.ext (congrFun h)⟩

/-- Two configurations are equal if and only if their images under `toDiv d` agree. -/
lemma eq_config_iff_eq_div {q : G.V} (d : ℤ) (c₁ c₂ : Config G q) : c₁ = c₂ ↔ toDiv d c₁ = toDiv d
    c₂ := by
  constructor
  -- Forward direction is clear
  intro h_eq
  rw [h_eq]
  -- Reverse direction takes more
  intro h_eq
  apply congrFun at h_eq
  ext v
  specialize h_eq v
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul] at h_eq
  by_cases h_v : q = v
  · -- Case v = q
    rw [← h_v]
    rw [c₁.q_zero, c₂.q_zero]
  · -- Case v ≠ q
    simp only [ne_eq, h_v, not_false_eq_true, one_chip_apply_other, mul_zero, add_zero] at h_eq
    exact h_eq

/-- Converts a configuration $c$ to the $q$-effective divisor `toDiv d c`,
bundled with its proof of $q$-effectivity. -/
def toQEffectiveDivisor {q : G.V} (d : ℤ) (c : Config G q) : qEffectiveDivisor G q :=
  {
    D := toDiv d c,
    h_eff := by
      intro v h_v
      dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
      simp only [ne_eq, h_v, not_false_eq_true, one_chip_apply_other', mul_zero, add_zero,
          ge_iff_le]
      exact c.non_negative v
  }
/-- Converts a $q$-effective divisor to a configuration by zeroing out the chip count at $q$. -/
def toConfig {q : G.V} (D : qEffectiveDivisor G q) : Config G q := {
  chips := D.D - (D.D q) • (oneChip q)
  q_zero := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [oneChip]
    simp only [↓reduceIte, mul_one, sub_self]
  non_negative := by
    intro v
    by_cases h_v : v = q
    · -- Case v = q
      simp only [zsmul_eq_mul, h_v, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq,
          one_chip_apply_v, mul_one, sub_self, ge_iff_le, Std.le_refl]
    · -- Case v ≠ q
      simp only [zsmul_eq_mul, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq, ne_eq,
          h_v, not_false_eq_true, one_chip_apply_other', mul_zero, sub_zero, ge_iff_le]
      exact D.h_eff v h_v
}

/-- The degree of a $q$-effective divisor equals its value at $q$ plus the configuration degree. -/
lemma config_degree_div_degree {q : G.V} (D : qEffectiveDivisor G q) : deg D.D = D.D q +
    configDegree (toConfig D) := by
  simp only [configDegree, toConfig, map_sub, map_zsmul, deg_one_chip, smul_eq_mul, mul_one]
  ring

/-- Shifting the prescribed degree by $k$ adds $k$ chips at $q$. -/
@[simp] lemma toDiv_config_degree_add {q : G.V} (c : Config G q) (k : ℤ) :
  toDiv (configDegree c + k) c = c.chips + k • oneChip q := by
  dsimp only [toDiv]
  rw [show configDegree c + k - configDegree c = k by ring]

/-- Prescribing degree $\deg(c)-1$ gives the divisor $c-q$. -/
@[simp] private lemma toDiv_config_degree_sub_one {q : G.V} (c : Config G q) :
  toDiv (configDegree c - 1) c = c.chips - oneChip q := by
  rw [show configDegree c - 1 = configDegree c + (-1) by ring]
  rw [toDiv_config_degree_add]
  simp only [Int.reduceNeg, neg_smul, one_smul, sub_eq_add_neg]

/-- The divisor $c-q$ has degree $\deg(c)-1$. -/
@[simp] lemma deg_chips_sub_one_chip {q : G.V} (c : Config G q) :
  deg (c.chips - oneChip q) = configDegree c - 1 := by
  rw [map_sub, configDegree, deg_one_chip]

/-- `toConfig` is a left inverse of `toQEffectiveDivisor`: converting a configuration to a
$q$-effective
divisor and back recovers the original configuration. -/
private lemma config_of_div_of_config (c : Config G q) (d : ℤ)  :
  toConfig (toQEffectiveDivisor d c) = c := by
  rcases c with ⟨chips, q_zero, non_negative⟩
  dsimp only [toQEffectiveDivisor, toConfig]
  simp only [zsmul_eq_mul, Config.mk.injEq]
  apply funext
  intro v
  by_cases h_v : v = q
  · -- Case v = q
    simp only [h_v, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq, one_chip_apply_v,
        mul_one, sub_self]
    rw [q_zero]
  · -- Case v ≠ q
    dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, oneChip, Int.zsmul_eq_mul, Pi.sub_apply,
        Pi.mul_apply, Pi.intCast_apply, Int.cast_eq]
    simp only [h_v, ↓reduceIte, mul_zero, add_zero, mul_one, sub_zero]

/-- `toQEffectiveDivisor` is a left inverse of `toConfig` at the correct degree: converting a
$q$-effective
divisor to a configuration and back via `toDiv (deg D.D)` recovers the original divisor. -/
lemma div_of_config_of_div (D : qEffectiveDivisor G q) :
  toDiv (deg D.D) (toConfig D) = D.D := by
  funext v
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  by_cases h: v ∈ Vtilde q
  · -- Case v ∈ Vtilde q
    dsimp only [toConfig, Pi.sub_apply, Pi.smul_apply, Int.zsmul_eq_mul]
    have : v ≠ q := by
      intro h_eq_q
      rw [h_eq_q] at h
      simp only [Finset.mem_filter, mem_univ, ne_eq, not_true_eq_false, and_false] at h
    simp only [ne_eq, this, not_false_eq_true, one_chip_apply_other', mul_zero, sub_zero,
        zsmul_eq_mul, add_zero]
  · -- Case v ∉ Vtilde q
    have : v = q := by
      contrapose! h
      simp only [Finset.mem_filter, mem_univ, ne_eq, h, not_false_eq_true, and_self]
    rw [this]
    simp only [(toConfig D).q_zero, oneChip, ite_true, mul_one, zero_add]
    linarith [config_degree_div_degree D]

/-- A $q$-reduced divisor is recovered by converting to its canonical configuration and back. -/
@[simp] lemma q_reduced_toDiv_toConfig (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : qReduced G q D) :
    toDiv (deg D) (toConfig ⟨D, h_qred.1⟩) = D :=
  div_of_config_of_div ⟨D, h_qred.1⟩

/-- A $q$-reduced divisor is its canonical configuration plus its chips at $q$. -/
lemma q_reduced_eq_chips_add_q (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : qReduced G q D) :
    D = (toConfig ⟨D, h_qred.1⟩).chips + D q • oneChip q := by
  let c : Config G q := toConfig ⟨D, h_qred.1⟩
  have h_deg : deg D = configDegree c + D q := by
    simpa only [add_comm] using (config_degree_div_degree ⟨D, h_qred.1⟩)
  calc
    D = toDiv (deg D) c := by
      exact (q_reduced_toDiv_toConfig G q D h_qred).symm
    _ = toDiv (configDegree c + D q) c := by rw [h_deg]
    _ = c.chips + D q • oneChip q := toDiv_config_degree_add c (D q)

/-- If a $q$-reduced divisor has value $-1$ at $q$, it is exactly $c-q$ for its
canonical configuration $c$. -/
lemma q_reduced_eq_chips_sub_one_chip (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : qReduced G q D) (h_q : D q = -1) :
    D = (toConfig ⟨D, h_qred.1⟩).chips - oneChip q := by
  calc
    D = (toConfig ⟨D, h_qred.1⟩).chips + D q • oneChip q :=
      q_reduced_eq_chips_add_q G q D h_qred
    _ = (toConfig ⟨D, h_qred.1⟩).chips + (-1 : ℤ) • oneChip q := by rw [h_q]
    _ = (toConfig ⟨D, h_qred.1⟩).chips - oneChip q := by
      simp only [Int.reduceNeg, neg_smul, one_smul, sub_eq_add_neg]

@[simp] private lemma eval_toDiv_q {q : G.V} (d : ℤ) (c : Config G q) :
  toDiv d c q = d - configDegree c := by
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  simp only [c.q_zero, one_chip_apply_v, mul_one, zero_add]

@[simp] private lemma eval_toDiv_ne_q {q v : G.V} (d : ℤ) (c : Config G q) (h_v : v ≠ q) :
  toDiv d c v = c.chips v := by
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  simp only [ne_eq, h_v, not_false_eq_true, one_chip_apply_other', mul_zero, add_zero]


/-- The divisor `toDiv d c` is effective if and only if $d \ge \deg(c)$, i.e. there are
enough chips at $q$ to cover any debt. -/
lemma config_eff {q : G.V} (d : ℤ) (c : Config G q) : effective (toDiv d c) ↔ d ≥ configDegree c :=
    by
  constructor
  -- Effective implies d ≥ configDegree
  intro h_eff
  have h := h_eff q
  rw [eval_toDiv_q] at h
  linarith
  -- d ≥ configDegree implies effective
  intro h_deg v
  by_cases h_v : v = q
  · -- Case v = q
    simp only [h_v, eval_toDiv_q, Int.sub_nonneg, h_deg]
  · -- Case v ≠ q
    simp only [ne_eq, h_v, not_false_eq_true, eval_toDiv_ne_q, ge_iff_le]
    exact c.non_negative v

instance : PartialOrder (Config G q) := {
  le := fun c₁ c₂ => c₁.chips ≤ c₂.chips,
  le_refl := by
    intro _
    simp only [Std.le_refl],
  le_trans := by
    intro _ _ _ c1_le_c2 c2_le_c3
    exact le_trans c1_le_c2 c2_le_c3,
  le_antisymm := by
    intro c1 c2 h_le h_ge
    have h_eq := le_antisymm h_le h_ge
    exact (eq_config_iff_eq_chips c1 c2).mpr h_eq
}

/-- The configuration degree is monotone: if $c \le c'$ pointwise, then
$\deg(c) \le \deg(c')$. -/
lemma config_degree_mono {q : G.V} {c c' : Config G q} (h_le : c ≤ c') :
  configDegree c ≤ configDegree c' := by
  dsimp only [configDegree, deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact Finset.sum_le_sum fun v _ => h_le v

/-- Two configurations are equal if one is pointwise bounded above by the other and they have
the same degree. -/
lemma config_eq_of_le_and_degree {q : G.V} {c1 c2 : Config G q} (h_le : c2 ≤ c1)
    (h_deg : configDegree c1 = configDegree c2) : c1 = c2 := by
  apply (eq_config_iff_eq_chips c1 c2).mpr
  dsimp only [configDegree, deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h_deg
  have h_le' : ∀ v : G.V, c2.chips v ≤ c1.chips v := by
    intro v
    exact h_le v
  suffices ∀ v : G.V, c1.chips v = c2.chips v by
    funext v
    exact this v
  contrapose! h_deg with h_ne
  rcases h_ne with ⟨v, h_v_ne⟩
  have h_gt : c2.chips v < c1.chips v := by
    specialize h_le' v
    apply lt_of_le_of_ne h_le'
    contrapose! h_v_ne
    simp only [h_v_ne]
  suffices configDegree c2 < configDegree c1 by
    exact ne_of_gt this
  dsimp only [configDegree, deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  refine Finset.sum_lt_sum ?_ ?_
  · intro i _
    exact h_le' i
  · use v
    simp only [mem_univ, h_gt, and_self]

/-- A configuration $c$ is *superstable* if for every nonempty
$S \subseteq V(G) \setminus \{q\}$, some vertex in $S$ has fewer chips than its
out-degree to $V(G) \setminus S$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Definition 3.12. -/
def superstable (G : CFGraph) (q : G.V) (c : Config G q) : Prop :=
  ∀ S ⊆  Vtilde q, S.Nonempty →
    ∃ v ∈ S, c.chips v < outdegreeSet G S v

/-- A configuration $c$ is superstable if and only if `toDiv d c` is $q$-reduced,
for any prescribed degree $d$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Remark 3.14. -/
lemma superstable_iff_q_reduced (G : CFGraph) (q : G.V) (d : ℤ) (c : Config G q) :
  superstable G q c ↔ qReduced G q (toDiv d c) := by
  dsimp only [superstable, ne_eq]
  constructor
  -- Forward direction
  intro h_superstable
  constructor
  -- Show c is nonnegative away from v
  intro v hv_ne_q
  dsimp only [toDiv, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul]
  simp only [ne_eq, hv_ne_q, not_false_eq_true, one_chip_apply_other', mul_zero, add_zero,
      ge_iff_le]
  exact c.non_negative v
  -- Show there is no nonempty legal set avoiding q
  intro S hq hS_nonempty hlegal
  have hS_subset : S ⊆ Vtilde q := by
    intro v hv_in_S
    simp only [Vtilde, Finset.mem_filter, mem_univ, true_and]
    exact fun hvq => hq (hvq ▸ hv_in_S)
  obtain ⟨v, hv_in_S, hv_outdeg⟩ := h_superstable S hS_subset hS_nonempty
  have h_v_ne_q : v ≠ q := by
    exact fun hvq => hq (hvq ▸ hv_in_S)
  have hge := hlegal v hv_in_S
  rw [eval_toDiv_ne_q d c h_v_ne_q] at hge
  omega
  -- Reverse direction
  intro h_q_reduced S hS_subset hS_nonempty
  have hq : q ∉ S := by
    intro hq_in_S
    have := hS_subset hq_in_S
    simp only [Vtilde, Finset.mem_filter, mem_univ, ne_eq, not_true_eq_false,
      and_false] at this
  obtain ⟨v, hv_in_S, hv_outdeg⟩ :=
    h_q_reduced.exists_lt_outdeg hq hS_nonempty
  use v
  refine ⟨hv_in_S, ?_⟩
  have h_v_neq_q : v ≠ q := fun hvq => hq (hvq ▸ hv_in_S)
  rw [eval_toDiv_ne_q d c h_v_neq_q] at hv_outdeg
  exact hv_outdeg

/-- The canonical configuration of a $q$-reduced divisor is superstable. -/
lemma q_reduced_toConfig_superstable (G : CFGraph) (q : G.V) (D : CFDiv G)
    (h_qred : qReduced G q D) :
    superstable G q (toConfig ⟨D, h_qred.1⟩) := by
  rw [superstable_iff_q_reduced G q (deg D) (toConfig ⟨D, h_qred.1⟩)]
  simpa only [q_reduced_toDiv_toConfig G q D h_qred] using h_qred

/-- A divisor is $q$-reduced if and only if it corresponds to a superstable configuration with
  respect to $q$. -/
lemma q_reduced_superstable_correspondence (G : CFGraph) (q : G.V) (D : CFDiv G) :
  qReduced G q D ↔ ∃ c : Config G q, superstable G q c ∧
  D = toDiv (deg D) c := by
  constructor
  · -- Forward direction (qReduced → ∃ c, superstable ∧ D = c - δ_q)
    intro h_qred
    refine ⟨toConfig ⟨D, h_qred.1⟩, q_reduced_toConfig_superstable G q D h_qred, ?_⟩
    exact (q_reduced_toDiv_toConfig G q D h_qred).symm
  -- Backward direction (∃ c, superstable ∧ D = c - δ_q → qReduced)
  · intro h_exists
    rcases h_exists with ⟨c, h_super, D_eq⟩
    rw [D_eq]
    rw [← superstable_iff_q_reduced G q (deg D) c]
    exact h_super


/-- A maximal superstable configuration is not strictly dominated by any other superstable
configuration. -/
def maximalSuperstable (G : CFGraph) {q : G.V} (c : Config G q) : Prop :=
  superstable G q c ∧ ∀ c' : Config G q, superstable G q c' → c ≤ c' → c' = c


/-- Subtracting a chip at $q$ from a superstable configuration gives an unwinnable
divisor. -/
lemma superstable_sub_chip_unwinnable {G : CFGraph} (q : G.V) (c : Config G q) :
  superstable G q c →
  ¬winnable G (c.chips - oneChip q) := by
  intro h_superstable
  let D := c.chips - oneChip q
  have h_red : qReduced G q D := by
    apply (q_reduced_superstable_correspondence G q D).mpr
    refine ⟨c, h_superstable, ?_⟩
    -- Prove D = c - δ_q
    have h_deg_D : deg D = configDegree c - 1 := by
      dsimp only [D]
      exact deg_chips_sub_one_chip (c := c)
    rw [h_deg_D]
    dsimp only [D]
    exact (toDiv_config_degree_sub_one (c := c)).symm
  -- A winnable q-reduced divisor is effective, but D has -1 chips at q.
  intro h_winnable
  have h_nonneg_q := effective_of_winnable_and_q_reduced G q D h_winnable h_red q
  dsimp only [Pi.sub_apply, D] at h_nonneg_q
  simp only [c.q_zero, one_chip_apply_v, zero_sub, Int.reduceNeg, Int.neg_nonneg,
      Int.reduceLE] at h_nonneg_q


/-!
## Burn lists and Dhar's burning algorithm

A *burn list* for a configuration $c$ is an ordered list of distinct vertices ending at $q$.
The list is stored in reverse burn order: starting from $[q]$, each new burnable vertex is
prepended to the list. A vertex is burnable when its number of chips is less than its
out-degree into the vertices that have already burned. The key property is that a
configuration is superstable if and only if a complete burn list, one containing all
vertices, exists (`superstable_burn_list`).

The `burnFlow` function extracts an orientation from a burn list by directing each edge
toward the vertex that appears earlier in the list. This is used to construct the bijection
between maximal superstable configurations and acyclic orientations with unique source $q$
(see `Orientation.lean`).
-/


/-- A burn list for a configuration $c$ is a list $[v_1,v_2,\ldots,v_n,q]$ of distinct
vertices ending at $q$, stored in reverse burn order.

For each $i$, let
$$
S_i = V(G) \setminus \{v_{i+1},\ldots,v_n,q\}.
$$
Then $v_i \in S_i$, and the out-degree of $v_i$ with respect to $S_i$, equivalently the
number of edges from $v_i$ to the later vertices $\{v_{i+1},\ldots,v_n,q\}$, is greater
than the number of chips at $v_i$. -/
def isBurnList (G : CFGraph) {q : G.V} (c : Config G q) (L : List G.V) : Prop :=
  match L with
  | [] => False
  | [x] => (x = q)
  | v :: w :: rest =>
      outdegreeSet G (univ \ (w :: rest).toFinset) v > c.chips v
      -- v isn't in the set made out of w :: rest
      ∧ ¬ (w :: rest).contains v
      ∧ isBurnList G c (w :: rest)

/-- Every burn list contains $q$, since the base case of a burn list is $[q]$. -/
private lemma burn_list_contains_q (G : CFGraph) {q : G.V} (c : Config G q) (L : List G.V) (h_bl :
    isBurnList G c L) :
  L.contains q := by
  induction L with
  | nil =>
    dsimp only [isBurnList] at h_bl
  | cons v rest ih =>
    cases rest with
    | nil =>
      dsimp only [isBurnList] at h_bl
      rw [h_bl]
      simp only [List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_true]
    | cons w rest' =>
      dsimp only [isBurnList] at h_bl
      rcases h_bl with ⟨h_outdeg, h_not_in_rest, h_rest_burn_list⟩
      specialize ih h_rest_burn_list
      simp only [List.contains_eq_mem, List.mem_cons, Bool.decide_or, Bool.or_eq_true,
          decide_eq_true_eq]
      simp only [List.contains_eq_mem, List.mem_cons, Bool.decide_or, Bool.or_eq_true,
          decide_eq_true_eq] at ih
      simp only [ih, or_true]

/-- If $c$ is superstable and a burn list $L$ does not yet contain all vertices, it can be
extended by prepending a new vertex. This corresponds to the next edge burning in Dhar's
burning algorithm; superstability implies that the entire graph will burn. -/
private lemma extend_burn_list (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c)
    (L : List G.V) : isBurnList G c L → (∃ v : G.V, ¬ L.contains v) → (∃ w : G.V, w ∉ L.toFinset ∧
    isBurnList G c (w :: L)) := by
  intro h_bl h_exists_v
  let S := univ \ L.toFinset
  have h_S_ne : S.Nonempty := by
    rcases h_exists_v with ⟨v, h_v_not_in_L⟩
    use v
    dsimp only [S]
    simp only [mem_sdiff, mem_univ, List.mem_toFinset, true_and]
    contrapose! h_v_not_in_L with h_raa
    simp only [List.contains_eq_mem, h_raa, decide_true]
  have h_S_Vtilde : S ⊆ Vtilde q := by
    intro v h_v_in_S
    dsimp only [Vtilde, ne_eq]
    simp only [Finset.mem_filter, mem_univ, true_and]
    contrapose! h_v_in_S with h_eq
    rw [h_eq]
    dsimp only [S]
    simp only [mem_sdiff, mem_univ, List.mem_toFinset, true_and, Decidable.not_not]
    -- Goal is not: q ∈ L
    have := burn_list_contains_q G c L h_bl
    simp only [List.contains_eq_mem, decide_eq_true_eq] at this
    exact this
  specialize h_ss S h_S_Vtilde h_S_ne
  rcases h_ss with ⟨v, hv_in_S, hv_outdeg⟩
  use v
  dsimp only [S] at hv_outdeg hv_in_S -- To get L to simplify after matching
  match L with
  | [] =>
    exfalso
    dsimp only [isBurnList] at h_bl
  | h :: t =>
    dsimp only [isBurnList]
    -- Unpack all the conjunctions and use hypotheses one by one
    constructor
    · simp only [List.toFinset_cons, mem_sdiff, mem_univ, mem_insert, List.mem_toFinset, not_or,
        true_and] at hv_in_S
      simp only [List.toFinset_cons, mem_insert, List.mem_toFinset, not_or]
      exact hv_in_S
    constructor
    · exact hv_outdeg
    constructor
    simp only [List.contains_eq_mem, List.mem_cons, Bool.decide_or, Bool.or_eq_true,
        decide_eq_true_eq, not_or]
    constructor
    intro h
    rw [h] at hv_in_S
    simp only [List.toFinset_cons, mem_sdiff, mem_univ, mem_insert, List.mem_toFinset, true_or,
        not_true_eq_false, and_false] at hv_in_S
    simp only [List.toFinset_cons, mem_sdiff, mem_univ, mem_insert, List.mem_toFinset, not_or,
        true_and] at hv_in_S
    exact hv_in_S.2
    exact h_bl

/-- A bundled burn list: a list $L$ of vertices together with a proof that it satisfies the
`isBurnList` conditions for configuration $c$. -/
structure burnList (G : CFGraph) {q : G.V} (c : Config G q) where
  /-- The ordered vertices satisfying the burning-list conditions for the configuration. -/
  (list : List G.V)
  (h_burn_list : isBurnList G c list)

/-- For each $n < |V(G)|$, there exists a burn list of size $n+1$. This is the inductive step for
`superstable_burn_list`. -/
private lemma burn_list_helper (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c)
    (n : ℕ) : (n < Finset.card (univ : Finset G.V))→ ∃ (L : List G.V), L.toFinset.card = n+1 ∧
    isBurnList G c L := by
  intro h_n_lt_card_V
  induction n with
  | zero =>
    use [q]
    constructor
    simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.card_singleton,
        zero_add]
    dsimp only [isBurnList]
  | succ n ih =>
    have ih_L : n < (univ : Finset G.V).card := by
      linarith
    apply ih at ih_L
    rcases ih_L with ⟨L, h_L_length, h_L_burn_list⟩
    have h_exists_v : ∃ v : G.V, ¬ L.contains v := by
      have h_card_L_le : L.toFinset.card < (univ : Finset G.V).card := by
        rw [← h_L_length] at h_n_lt_card_V
        linarith
      obtain ⟨v, -, h_v_not_in_L⟩ := Finset.exists_mem_notMem_of_card_lt_card h_card_L_le
      exact ⟨v, by simpa only [List.contains_eq_mem, decide_eq_true_eq, List.mem_toFinset]
          using h_v_not_in_L⟩
    have := extend_burn_list G c h_ss L h_L_burn_list h_exists_v
    rcases this with ⟨w, h_w_burn_list⟩
    use w :: L
    constructor
    · -- Show cardinality is n+2
      rw [List.toFinset_cons]
      rw [card_insert_eq_ite]
      -- Need: w ∉ L.toFinset
      simp only [h_w_burn_list.1, ↓reduceIte, Nat.add_right_cancel_iff]
      rw [h_L_length]
    · -- Show the tail is a burn list
      exact h_w_burn_list.2

/-- A superstable configuration admits a complete burn list containing every vertex of $G$.
This is the key output of Dhar's burning algorithm: in a superstable configuration, the
whole graph burns. -/
lemma superstable_burn_list (G : CFGraph) {q : G.V} (c : Config G q) (h_ss : superstable G q c) : ∃
    L : burnList G c, ∀ v : G.V, v ∈ L.list := by
  have h_card_V : (univ : Finset G.V).card ≥ 1 := by
    have h_nonempty : Nonempty G.V := by infer_instance
    have h_card_pos : (univ : Finset G.V).card > 0 := Fintype.card_pos_iff.mpr h_nonempty
    linarith
  have : (univ : Finset G.V).card - 1 < (univ : Finset G.V).card := by
    simp only [card_univ, tsub_lt_self_iff, Order.lt_one_iff, and_true]
    -- Now show `Fintype.card G.V > 0`, so that the subtraction makes sense.
    apply Fintype.card_pos_iff.mpr
    infer_instance
  have h_burn_list := burn_list_helper G c h_ss ((univ : Finset G.V).card - 1) this
  rcases h_burn_list with ⟨L, h_L_length, h_L_burn_list⟩
  have h_L_card : L.toFinset.card = (univ : Finset G.V).card := by
    simp only [h_L_length, card_univ]
    apply Nat.sub_add_cancel
    exact h_card_V
  use burnList.mk L h_L_burn_list
  have h_toFinset_eq : L.toFinset = (univ : Finset G.V) := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    simp only [card_univ, h_L_card, Std.le_refl]
  intro v
  have : v ∈ L.toFinset := by simp only [h_toFinset_eq, mem_univ]
  simpa only [List.mem_toFinset] using this

-- The following lemmas establish the necessary properties of the orientation to be defined
-- from the burn order.

/-- The orientation induced by a burn list: for each edge $(u,v)$, direct it from $u$ to $v$
(i.e. assign nonzero flow) if $u$ appears in the list and $v$ appears before $u$. In other
words, the orientation indicates the direction of the spreading fire in Dhar's burning
algorithm. -/
def burnFlow {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) : (G.V × G.V) → ℕ :=
  fun e => if (e.1 ∈ L.list) ∧ (L.list.idxOf e.2 < L.list.idxOf e.1) then numEdges G e.1 e.2 else 0

/-- The `burnFlow` of a complete burn list is a valid orientation: for every edge
$\{u,v\}$, exactly `numEdges G u v` units of flow are directed in one of the two
directions. -/
lemma burn_flow_reverse {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) (h_full : ∀ v :
    G.V, v ∈ L.list) : ∀ (u v : G.V), (burnFlow L ⟨u, v⟩) + (burnFlow L ⟨v, u⟩) = numEdges G u v :=
    by
  intro u v
  dsimp only [burnFlow]
  by_cases h_uv : L.list.idxOf v < L.list.idxOf u
  · -- Case: indexOf v < indexOf u
    simp only [h_full u, h_uv, and_self, ↓reduceIte, h_full v, true_and, Nat.add_eq_left,
        ite_eq_right_iff]
    intro h
    linarith
  · -- Case: indexOf v ≥ indexOf u
    by_cases h_eq : L.list.idxOf u = L.list.idxOf v
    · -- Subcase: indexOf u < indexOf v
      simp only [h_eq, lt_self_iff_false, and_false, ↓reduceIte, add_zero]
      have : u = v := (List.idxOf_inj (h_full u)).mp h_eq
      rw [this, num_edges_self_zero G v]
    · -- Subcase: indexOf u > indexOf v
      have h_uv' : L.list.idxOf u < L.list.idxOf v := by
        simp only [not_lt] at h_uv h_eq
        exact lt_of_le_of_ne h_uv h_eq
      simp only [h_uv, and_false, ↓reduceIte, h_full v, h_uv', and_self, zero_add]
      exact num_edges_symmetric G v u

/-- The `burnFlow` of a complete burn list is directed: for every pair $(u,v)$, flow goes
in at most one direction. -/
lemma burn_flow_directed {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) (h_full : ∀ v :
    G.V, v ∈ L.list) : ∀ (u v : G.V), burnFlow L ⟨u,v⟩ = 0 ∨ burnFlow L ⟨v,u⟩ = 0 := by
  intro u v
  dsimp only [burnFlow]
  by_cases h_uv : L.list.idxOf v < L.list.idxOf u
  · -- Case: indexOf v < indexOf u
    simp only [h_full u, h_uv, and_self, ↓reduceIte, h_full v, true_and, ite_eq_right_iff]
    right
    intro h
    linarith
  · -- Case: indexOf v ≥ indexOf u
    by_cases h_eq : L.list.idxOf u = L.list.idxOf v
    · -- Subcase: indexOf u = indexOf v
      simp only [h_eq, lt_self_iff_false, and_false, ↓reduceIte, or_self]
    · -- Subcase: indexOf u > indexOf v
      have h_uv' : L.list.idxOf u < L.list.idxOf v := by
        simp only [not_lt] at h_uv h_eq
        exact lt_of_le_of_ne h_uv h_eq
      simp only [h_uv, and_false, ↓reduceIte, h_full v, h_uv', and_self, true_or]

/-- For any vertex $v \ne q$ in a burn list, the in-flow into $v$ exceeds the number of
chips at $v$. This is the key inequality used to construct an acyclic orientation from a
superstable configuration. -/
lemma burnin_degree {G : CFGraph} {q : G.V} {c : Config G q} (L : burnList G c) (v : G.V) (h_pres :
    v ∈ L.list) (h_ne : v ≠ q): ∑ (w : G.V), burnFlow L ⟨w,v⟩ > c.chips v := by
  let h_bl := L.h_burn_list
  cases h: L.list with
  | nil =>
    rw [h] at h_bl
    dsimp only [isBurnList] at h_bl
  | cons x rest =>
    cases h' : rest with
    | nil =>
      rw [h'] at h
      rw [h] at h_bl
      dsimp only [isBurnList] at h_bl
      -- So x = q
      simp only [h, List.mem_cons, List.not_mem_nil, or_false] at h_pres
      rw [h_pres, ← h_bl] at h_ne
      contradiction
    | cons y rest' =>
      rw [h'] at h
      rw [h] at h_bl
      dsimp only [isBurnList] at h_bl
      -- Need to analyze the position of v in the list
      by_cases h_vx : v = x
      · -- Case: v = x
        rw [← h_vx] at h_bl
        suffices ∑ (w : G.V), burnFlow L ⟨w,v⟩ ≥ outdegreeSet G (univ \ (y :: rest').toFinset) v by
          linarith [this, h_bl.1]
        dsimp only [burnFlow]
        have ind_v : L.list.idxOf v = 0 := by
          rw [h_vx,h]
          simp only [List.idxOf_cons_self]
        simp only [ind_v]
        have h_ineq := h_bl.1
        have h_above : ∀ (x : G.V), x ∈ L.list ∧ 0 < List.idxOf x L.list ↔ x ∈ rest := by
          intro w
          rw [← h'] at h
          rw [h]
          simp only [List.mem_cons]
          have : 0 < List.idxOf w (x :: rest) ↔ 0 ≠ List.idxOf w (x :: rest) := by
            constructor
            · intro h_pos h_eq
              rw [h_eq] at h_pos
              linarith
            · intro h_neq
              simp only [ne_eq] at h_neq
              apply Nat.zero_lt_of_ne_zero
              contrapose! h_neq with h_eq_zero
              rw [h_eq_zero]
          rw [this]
          have : 0 ≠ List.idxOf w (x :: rest) ↔ w ≠ x := by
            constructor
            · intro h_neq
              contrapose! h_neq with h_eq
              rw [h_eq]
              simp only [List.idxOf_cons_self]
            · intro h_neq
              rw [List.idxOf_cons_ne _ (Ne.symm h_neq)]
              simp only [Nat.succ_eq_add_one, ne_eq, Nat.right_eq_add, Nat.add_eq_zero_iff,
                  one_ne_zero, and_false, not_false_eq_true]
          rw [this]
          constructor
          · -- Forward direction
            intro h_w
            by_contra!
            simp only [this, or_false, ne_eq, and_not_self] at h_w
          · -- Reverse direction
            intro h_w_in_rest
            simp only [h_w_in_rest, or_true, ne_eq, true_and]
            by_contra!
            rw [this] at h_w_in_rest
            have := h_bl.2.1
            rw [h_vx] at this
            rw [← h'] at this
            absurd this
            simp only [List.contains_eq_mem, h_w_in_rest, decide_true]
        simp only [h_above]
        dsimp only [outdegreeSet]
        rw [← h']
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        simp only [Nat.cast_sum, sdiff_sdiff_right_self, subset_univ, inf_of_le_right, ge_iff_le]
        have : Finset.filter (Membership.mem rest) univ = rest.toFinset := by
          ext w
          simp only [Finset.mem_filter, mem_univ, true_and, List.mem_toFinset]
        rw [this]
        apply sum_le_sum
        intro i _
        rw [num_edges_symmetric G i v]
      · -- Case: v ≠ x
        let L' := burnList.mk (y :: rest') (h_bl.2.2)
        have h_v_in_L' : v ∈ L'.list := by
          dsimp only [L']
          rw [← h']
          rw [← h'] at h
          rw [h] at h_pres
          simp only [List.mem_cons, h_vx, false_or] at h_pres
          exact h_pres
        have h_step : ∀ (w : G.V), burnFlow L ⟨w,v⟩ = burnFlow L' ⟨w,v⟩ := by
          have h_x_nin_rest: x ∉ rest := by
            have := L.h_burn_list
            rw [h] at this
            have := this.2.1
            rw [h']
            simp only [List.contains_eq_mem, List.mem_cons, Bool.decide_or, Bool.or_eq_true,
                decide_eq_true_eq, not_or] at this
            simp only [List.mem_cons, this, or_self, not_false_eq_true]
          intro w
          dsimp only [burnFlow, L']
          rw [h]
          rw [List.idxOf_cons_ne _ (Ne.symm h_vx)]
          by_cases h_wx : w = x
          · -- Subcase: w = x
            rw [h_wx]
            have h0 : (x :: y :: rest').idxOf x = 0 := List.idxOf_cons_self
            rw [h0, ite_eq_right (fun ⟨_, h⟩ => Nat.not_lt_zero _ h),
               ite_eq_right (fun ⟨h_mem, _⟩ => (h' ▸ h_x_nin_rest) h_mem)]
          · -- Subcase: w ≠ x
            simp only [List.mem_cons, h_wx, false_or]
            rw [List.idxOf_cons_ne (y :: rest') (Ne.symm h_wx)]
            simp only [Nat.succ_lt_succ_iff]
        simp only [h_step]
        have h_ind := burnin_degree L' v h_v_in_L' h_ne
        exact h_ind
termination_by L.list.length
decreasing_by
  rw [h,h']
  simp only [List.length_cons, lt_add_iff_pos_right, Order.lt_one_iff]
