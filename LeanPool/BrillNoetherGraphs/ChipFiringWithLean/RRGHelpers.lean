/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Orientation
public import LeanPool.BrillNoetherGraphs.ChipFiringWithLean.Rank

/-! # RRGHelpers -/

@[expose] public section
open Multiset Finset

/-!
## Maximal superstable configurations and maximal unwinnable divisors

This section establishes the correspondence between maximal superstable configurations and
maximal unwinnable divisors:

- A superstable configuration $c$ is maximal if and only if $\deg(c) = g$
  (`maximal_superstable_config_prop`).
- A divisor $D$ is maximal unwinnable if and only if its canonical $q$-reduced representative
  has the form $c-q$, with $c$ the associated maximal superstable configuration
  (`maximal_unwinnable_char`).
- Every maximal unwinnable divisor has degree $g - 1$ (`maximal_unwinnable_deg`).
-/

/-- The chosen unique $q$-reduced representative of the linear equivalence class of $D$. -/
noncomputable def qReducedRep {G : CFGraph}
    (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) : CFDiv G :=
  Classical.choose (unique_q_reduced h_conn q D)

/-- The canonical representative is linearly equivalent to $D$ and is $q$-reduced. -/
private lemma qReducedRep_spec {G : CFGraph}
    (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) :
    linearEquiv G D (qReducedRep h_conn q D) ∧ qReduced G q (qReducedRep h_conn q D) :=
  (Classical.choose_spec (unique_q_reduced h_conn q D)).1

/-- The configuration obtained from the canonical $q$-reduced representative of $D$ by
zeroing out the chips at $q$. -/
noncomputable def qReducedConfig {G : CFGraph}
    (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) : Config G q :=
  toConfig ⟨qReducedRep h_conn q D, by exact (qReducedRep_spec h_conn q D).2.1⟩

/-- The canonical configuration attached to $D$ is superstable. -/
private lemma qReducedConfig_superstable {G : CFGraph}
    (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) :
    superstable G q (qReducedConfig h_conn q D) := by
  exact q_reduced_toConfig_superstable G q (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).2

/-- Every divisor $D$ is linearly equivalent to $c+kq$ for some superstable configuration
$c$ and integer $k$.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Remark 3.14. -/
lemma superstable_of_divisor {G : CFGraph} (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) :
  ∃ (c : Config G q) (k : ℤ),
    linearEquiv G D (c.chips + k • (oneChip q)) ∧
    superstable G q c := by
  let D' := qReducedRep h_conn q D
  let c := qReducedConfig h_conn q D
  use c, D' q
  constructor
  ·
    have h := (qReducedRep_spec h_conn q D).1
    rw [q_reduced_eq_chips_add_q G q (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).2] at h
    exact h
  ·
    simpa only using qReducedConfig_superstable h_conn q D

/-- If $D$ is unwinnable and $D \sim c + k \cdot q$ for a superstable $c$, then $k < 0$. -/
lemma superstable_of_divisor_negative_k (G : CFGraph) (q : G.V) (D : CFDiv G) :
  ¬(winnable G D) →
  ∀ (c : Config G q) (k : ℤ),
    linearEquiv G D (c.chips + k • (oneChip q)) →
    superstable G q c →
    k < 0 := by
  intro h_not_winnable c k h_equiv h_super
  contrapose! h_not_winnable with k_nonneg
  let D' := c.chips + k • (oneChip q)
  have D'_eff : effective D' := by
    rw [show D' = toDiv (configDegree c + k) c by
      dsimp only [D']
      rw [toDiv_config_degree_add]]
    exact (config_eff (configDegree c + k) c).2 (by linarith)
  have h_winnable_D' : winnable G D' := winnable_of_effective G D' D'_eff
  exact winnable_equiv_winnable G D' D h_winnable_D' h_equiv.symm


/-- If $D$ is maximal unwinnable and $q$-reduced, then $D(q) = -1$. -/
private lemma maximal_unwinnable_q_reduced_chips_at_q (G : CFGraph) (q : G.V) (D : CFDiv G) :
  maximalUnwinnable G D → qReduced G q D → D q = -1 := by
  intro h_max_unwin h_qred
  have h_neg : D q < 0 := by
    contrapose! h_max_unwin
    unfold maximalUnwinnable
    push Not
    intro h_unwin
    absurd h_unwin
    suffices effective D by
      exact winnable_of_effective G D this
    intro v
    by_cases hv : v = q
    · rw [hv]
      exact h_max_unwin
    · exact h_qred.1 v (by simp only [ne_eq, hv, not_false_eq_true])
  have h_add_win : winnable G (D + oneChip q) := by exact (h_max_unwin.2 q)
  have h_eff : effective (D + oneChip q) := by
    apply effective_of_winnable_and_q_reduced G q (D + oneChip q) h_add_win
    -- Prove q-reducedness of D + oneChip q
    constructor
    · intro v hv
      have h_v_ne_q : v ≠ q := by
        exact Set.mem_ofPred.mp hv
      rw [Pi.add_apply]
      simp only [ne_eq, h_v_ne_q, not_false_eq_true, one_chip_apply_other', add_zero, ge_iff_le]
      apply h_qred.1 v hv
    · intro S hq hS_nonempty hlegal
      apply h_qred.2 S hq hS_nonempty
      intro v hv_in_S
      have hvq : v ≠ q := fun hvq => hq (hvq ▸ hv_in_S)
      simpa only [Pi.add_apply, one_chip_apply_other' q v hvq, add_zero] using
        hlegal v hv_in_S
  have h_nonneg : D q + 1 ≥ 0 := by
    have h := h_eff q
    rw [Pi.add_apply] at h
    simp only [one_chip_apply_v, ge_iff_le] at h
    exact h
  linarith

/-- A maximal superstable configuration has degree equal to the genus.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(1),
"only if" direction. -/
private lemma degree_max_superstable {G : CFGraph} {q : G.V} (c : Config G q) (h_max :
    maximalSuperstable G c): configDegree c = genus G := by
  have := maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, hO, h_orient_eq⟩
  rw [← h_orient_eq]
  exact config_degree_from_O O hO

/-- If $D$ is maximal unwinnable and $q$-reduced, then any configuration $c$ satisfying
`D = toDiv (deg D) c` must realize $D$ as $c-q$. This is the $q$-reduced core of the
cited statement.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(2),
"only if" direction. -/
private lemma maximal_unwinnable_q_reduced_form (G : CFGraph) (q : G.V) (D : CFDiv G) (c : Config G
    q) :
  maximalUnwinnable G D → qReduced G q D → D = toDiv (deg D) c → D = c.chips - oneChip q := by
  intro h_max_unwinnable h_qred h_toDeg
  have h_c_eq : c = toConfig ⟨D, h_qred.1⟩ := by
    apply (eq_config_iff_eq_div (deg D) c (toConfig ⟨D, h_qred.1⟩)).mpr
    exact h_toDeg.symm.trans (q_reduced_toDiv_toConfig G q D h_qred).symm
  calc
    D = (toConfig ⟨D, h_qred.1⟩).chips - oneChip q := by
      exact q_reduced_eq_chips_sub_one_chip G q D h_qred
        (maximal_unwinnable_q_reduced_chips_at_q G q D h_max_unwinnable h_qred)
    _ = c.chips - oneChip q := by rw [h_c_eq]

/-- The degree of a superstable configuration is bounded above by the genus. -/
private lemma superstable_degree_le_genus (G : CFGraph) (q : G.V) (c : Config G q) :
  superstable G q c → configDegree c ≤ genus G := by
  intro h_super
  rcases maximal_superstable_exists G q c h_super with ⟨c_max, h_maximal, h_ge_c⟩
  rw [← degree_max_superstable c_max h_maximal]
  exact config_degree_mono h_ge_c

/-- If a superstable configuration has degree equal to the genus, then it is maximal.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(1),
"if" direction. -/
private lemma maximal_superstable_of_degree_eq_genus (G : CFGraph) (q : G.V) (c : Config G q) :
  superstable G q c → configDegree c = genus G → maximalSuperstable G c := by
  intro h_super h_deg_eq
  -- Choose a maximal above c (we'll show it's equal to c)
  have := maximal_superstable_exists G q c h_super
  rcases this with ⟨c_max, h_maximal, h_ge_c⟩
  have c_max_deg : configDegree c_max = genus G := by
    exact degree_max_superstable c_max h_maximal
  let E := c_max.chips - c.chips
  have E_eff : E ≥ 0 := by
    intro v
    specialize h_ge_c v
    dsimp only [Pi.zero_apply, Pi.sub_apply, E]
    linarith
  have E_deg : deg E = 0 := by
    dsimp only [E]
    rw [map_sub]
    dsimp only [configDegree] at h_deg_eq c_max_deg
    rw [h_deg_eq, c_max_deg]
    simp only [sub_self]
  have E_0 : E = 0 := eff_degree_zero E E_eff E_deg
  dsimp only [E] at E_0
  have : c_max.chips = c.chips := by
    rw [← sub_eq_zero, E_0]
  have : c_max = c := (eq_config_iff_eq_chips c_max c).mpr this
  rw [← this]
  exact h_maximal

/-- A superstable configuration is maximal if and only if its degree equals the genus.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(1). -/
private theorem maximal_superstable_config_prop (G : CFGraph) (q : G.V) (c : Config G q) :
  superstable G q c → (maximalSuperstable G c ↔ configDegree c = genus G) := by
  intro h_super
  constructor
  { -- Forward direction: maximalSuperstable → degree = g
    intro h_max
    exact degree_max_superstable c h_max
  }
  { -- Reverse direction: degree = g → maximalSuperstable
    intro h_deg
    -- Apply the lemma that degree g implies maximality
    exact maximal_superstable_of_degree_eq_genus G q c h_super h_deg }


/-- A divisor of degree at least $g$ is winnable. -/
lemma winnable_of_deg_ge_genus {G : CFGraph} (h_conn : graphConnected G) (D : CFDiv G) : deg D ≥
    genus G → winnable G D := by
  intro h_deg_ge_g
  let q := Classical.arbitrary G.V
  rcases (exists_q_reduced_representative h_conn q D) with ⟨D_qred, h_equiv, h_qred⟩
  rcases (q_reduced_superstable_correspondence G q D_qred).mp h_qred with ⟨c, h_super, h_D_eq⟩
  have h_deg_c : configDegree c ≤ genus G := superstable_degree_le_genus G q c h_super
  have D_deg : deg D = deg D_qred := linear_equiv_preserves_deg G D D_qred h_equiv
  refine ⟨D_qred, ?_, h_equiv⟩
  -- D_qred = toDiv (deg D_qred) c is effective: there are enough chips at q, since
  -- deg D_qred ≥ g ≥ configDegree c
  rw [h_D_eq]
  exact (config_eff _ c).mpr (by linarith)

/-- Adding a chip anywhere to $c'-q$ makes it winnable when $c'$ is maximal superstable. -/
private lemma maximal_superstable_chip_winnable {G : CFGraph} (h_conn : graphConnected G) (q : G.V)
    (c' : Config G q) :
  maximalSuperstable G c' →
  ∀ (v : G.V), winnable G (c'.chips- (oneChip q) + (oneChip v)) := by
  intro h_max_superstable v
  let D' := c'.chips - oneChip q + oneChip v
  have deg_ineq : deg D' ≥ genus G := by
    calc
      deg D' = configDegree c' := by
        dsimp only [D']
        simp only [_root_.map_add, deg_chips_sub_one_chip, configDegree, deg_one_chip,
            sub_add_cancel]
      _ = genus G := degree_max_superstable c' h_max_superstable
      _ ≥ genus G := by rfl
  exact winnable_of_deg_ge_genus h_conn D' deg_ineq

/-- A maximal unwinnable $q$-reduced divisor is its canonical configuration minus one chip
at $q$. -/
private lemma maximal_unwinnable_q_reduced_toConfig_form {G : CFGraph} (q : G.V) (D : CFDiv G)
    (h_max : maximalUnwinnable G D) (h_qred : qReduced G q D) :
    D = (toConfig ⟨D, h_qred.1⟩).chips - oneChip q := by
  exact q_reduced_eq_chips_sub_one_chip G q D h_qred
    (maximal_unwinnable_q_reduced_chips_at_q G q D h_max h_qred)

/-- A divisor of the form $c-q$ is maximal unwinnable when $c$ is maximal superstable. -/
private lemma maximal_unwinnable_of_maximal_superstable_form {G : CFGraph}
    (h_conn : graphConnected G) (q : G.V) (c : Config G q) :
    maximalSuperstable G c → maximalUnwinnable G (c.chips - oneChip q) := by
  intro h_max_c
  refine ⟨superstable_sub_chip_unwinnable q c h_max_c.1, ?_⟩
  intro v
  exact maximal_superstable_chip_winnable h_conn q c h_max_c v

/-- For a $q$-reduced divisor, maximal unwinnability is equivalent to the maximal
superstability of its canonical configuration together with the canonical $c-q$ form. -/
private lemma maximal_unwinnable_q_reduced_toConfig_iff {G : CFGraph}
    (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) (h_qred : qReduced G q D) :
    maximalUnwinnable G D ↔
    maximalSuperstable G (toConfig ⟨D, h_qred.1⟩) ∧
    D = (toConfig ⟨D, h_qred.1⟩).chips - oneChip q := by
  constructor
  · intro h_max
    constructor
    · let c : Config G q := toConfig ⟨D, h_qred.1⟩
      have h_super_c : superstable G q c := q_reduced_toConfig_superstable G q D h_qred
      have h_form_D : D = c.chips - oneChip q := by
        exact maximal_unwinnable_q_reduced_toConfig_form q D h_max h_qred
      by_contra h_not_max_c
      rcases maximal_superstable_exists G q c h_super_c with ⟨c', h_max_c', h_ge⟩
      have h_ne : c' ≠ c := by
        intro h_eq
        apply h_not_max_c
        simpa only [h_eq] using h_max_c'
      have h_strict : ∃ v : G.V, c.chips v + 1 ≤ c'.chips v := by
        by_contra h_no
        push Not at h_no
        have h_c'_le_c : c' ≤ c := by
          intro v
          linarith [h_no v]
        exact h_ne ((le_antisymm h_ge h_c'_le_c).symm)
      rcases h_strict with ⟨v, h_v_strict⟩
      have h_H_eff : effective (c'.chips - c.chips - oneChip v) := by
        intro w
        by_cases h_wv : w = v
        · rw [h_wv]
          simp only [Pi.sub_apply, oneChip, ↓reduceIte, Int.sub_nonneg]
          linarith [h_ge v, h_v_strict]
        · simp only [Pi.sub_apply, oneChip, h_wv, ↓reduceIte, sub_zero, Int.sub_nonneg]
          linarith [h_ge w]
      have h_D''_eq :
          c'.chips - oneChip q =
            (c'.chips - c.chips - oneChip v) + (D + oneChip v) := by
        rw [h_form_D]
        funext w
        simp only [Pi.sub_apply, sub_eq_add_neg, Pi.add_apply, Pi.neg_apply]
        abel_nf
      have h_D''_unwin : ¬winnable G (c'.chips - oneChip q) :=
        superstable_sub_chip_unwinnable q c' h_max_c'.1
      apply h_D''_unwin
      rw [h_D''_eq]
      exact winnable_add_winnable G (c'.chips - c.chips - oneChip v) (D + oneChip v)
        (winnable_of_effective G _ h_H_eff) (h_max.2 v)
    · exact maximal_unwinnable_q_reduced_toConfig_form q D h_max h_qred
  · rintro ⟨h_max_c, h_form⟩
    rw [h_form]
    exact maximal_unwinnable_of_maximal_superstable_form h_conn q _ h_max_c


/-- A divisor $D$ is maximal unwinnable if and only if its canonical $q$-reduced
representative has the form $c-q$, with $c$ the associated maximal superstable
configuration.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(2),
in canonical form. -/
theorem maximal_unwinnable_char {G : CFGraph} (h_conn : graphConnected G) (q : G.V) (D : CFDiv G) :
  maximalUnwinnable G D ↔
    maximalSuperstable G (qReducedConfig h_conn q D) ∧
    qReducedRep h_conn q D =
      (qReducedConfig h_conn q D).chips - oneChip q := by
  let D' := qReducedRep h_conn q D
  have h_qred_D' : qReduced G q D' := (qReducedRep_spec h_conn q D).2
  have h_core := maximal_unwinnable_q_reduced_toConfig_iff h_conn q D' h_qred_D'
  constructor
  · intro h_max_unwinnable_D
    have h_max_D' : maximalUnwinnable G D' :=
      maximal_unwinnable_preserved G D D' h_max_unwinnable_D (qReducedRep_spec h_conn q D).1
    simpa only [qReducedConfig] using h_core.mp h_max_D'
  · intro h_can
    have h_max_D' : maximalUnwinnable G D' := by
      simpa only using h_core.mpr h_can
    exact maximal_unwinnable_preserved G D' D h_max_D' (qReducedRep_spec h_conn q D).1.symm

/-- A maximal unwinnable divisor has degree $g - 1$, computed from its canonical
$q$-reduced representative and canonical configuration.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(4). -/
theorem maximal_unwinnable_deg
  {G : CFGraph} (h_conn : graphConnected G) (D : CFDiv G) :
  maximalUnwinnable G D → deg D = genus G - 1 := by
  intro h_max_unwin

  let q := Classical.arbitrary G.V

  have h_char := maximal_unwinnable_char h_conn q D
  have h_max_cfg : maximalSuperstable G (qReducedConfig h_conn q D) := (h_char.mp h_max_unwin).1
  have h_rep_form :
      qReducedRep h_conn q D =
        (qReducedConfig h_conn q D).chips - oneChip q := (h_char.mp h_max_unwin).2
  have h_deg_D' : deg (qReducedRep h_conn q D) = genus G - 1 := calc
    deg (qReducedRep h_conn q D) =
        deg ((qReducedConfig h_conn q D).chips - oneChip q) := by rw [h_rep_form]
    _ = configDegree (qReducedConfig h_conn q D) - 1 :=
        deg_chips_sub_one_chip (c := qReducedConfig h_conn q D)
    _ = genus G - 1 := by rw [degree_max_superstable (qReducedConfig h_conn q D) h_max_cfg]
  have h_deg_eq : deg D = deg (qReducedRep h_conn q D) :=
    linear_equiv_preserves_deg G D (qReducedRep h_conn q D) (qReducedRep_spec h_conn q D).1
  rw [h_deg_eq, h_deg_D']

/-- The map sending an acyclic orientation with source $q$ to the divisor
$v \mapsto \operatorname{indeg}(v) - \delta_{v,q}$ is injective, and every maximal
unwinnable divisor has degree $g - 1$. The divisor used here differs from
$D(\mathcal{O})$ by a fixed divisor, so injectivity is equivalent.

See: [Corry-Perkinson](https://pubs.ams.org/ebooks/mbk/114), Corollary 4.9(3)
for the injectivity claim. -/
theorem acyclic_orientation_maximal_unwinnable_correspondence_and_degree
    {G : CFGraph} (h_conn : graphConnected G) (q : G.V) :
    (Function.Injective (λ (O : {O : CFOrientation G // isAcyclic G O ∧ isSource G O q}) =>
      λ v => (indeg G O.val v) - if v = q then 1 else 0)) ∧
    (∀ D : CFDiv G, maximalUnwinnable G D → deg D = genus G - 1) := by
  constructor
  { -- Part 1: Injection proof
    intros O₁ O₂ h_eq
    have h_indeg : ∀ v : G.V, indeg G O₁.val v = indeg G O₂.val v := by
      intro v
      have := congr_fun h_eq v
      by_cases hv : v = q
      · have h₁ := O₁.prop.2; have h₂ := O₂.prop.2
        dsimp only [isSource] at h₁ h₂
        rw [hv, h₁, h₂]
      · simp only [hv, ↓reduceIte, tsub_zero] at this
        exact this
    exact Subtype.ext (orientation_determined_by_indegrees O₁.val O₂.val O₁.prop.1 O₂.prop.1
      h_indeg)
  }
  { -- Part 2: Degree characterization
    -- This now correctly refers to the theorem defined above
    intro D hD
    exact maximal_unwinnable_deg h_conn D hD
  }

/-!
## Moderator divisors

Following terminology of [Mikhalkin and Zharkov](https://arxiv.org/abs/math/0612267), a
*moderator* is the divisor $D(\mathcal{O})$ of an acyclic orientation $\mathcal{O}$. Moderators
encapsulate the key duality in the proof of Riemann-Roch: reversing the orientation carries
$D(\mathcal{O})$ to $K_G - D(\mathcal{O})$.
-/

/-- A *moderator* is a divisor of the form $D(\mathcal{O})$ for some acyclic orientation
$\mathcal{O}$. -/
def isModerator {G : CFGraph} (D : CFDiv G) : Prop :=
  ∃ (O : CFOrientation G), isAcyclic G O ∧ D = ordiv G O

/-- If $D$ is a moderator, then so is $K_G - D$ (via the reverse orientation). This is the
key duality in the proof of Riemann-Roch. -/
lemma moderator_symmetry {G : CFGraph} (D : CFDiv G) :
  isModerator D → isModerator (canonicalDivisor G - D) := by
  rintro ⟨O, hO, h_D⟩
  use O.reverse
  constructor
  · exact is_acyclic_reverse_of_is_acyclic G O hO
  · rw [h_D]
    rw [← divisor_reverse_orientation O]
    abel

/-- Moderators have degree $g-1$. -/
lemma moderator_degree {G : CFGraph} {D : CFDiv G} (h : isModerator D) : deg D = genus G - 1 := by
  rcases h with ⟨O, hO, rfl⟩
  exact degree_ordiv O

/-- Moderators are unwinnable. -/
lemma unwinnable_of_moderator {G : CFGraph} {D : CFDiv G} (h : isModerator D) : ¬ winnable G D := by
  rcases h with ⟨O, hO, rfl⟩
  exact ordiv_unwinnable G O hO

/-- For every unwinnable divisor $D$, there exist a moderator $M$ and an effective divisor
$H$ with $M \sim D + H$. -/
lemma moderator_of_unwinnable {G : CFGraph} (h_conn: graphConnected G) (D : CFDiv G) (unwin : ¬
    winnable G D) :
  ∃ (M H : CFDiv G), isModerator M ∧ effective H ∧ linearEquiv G M (D+H) := by
  let q := Classical.arbitrary G.V
  rcases superstable_of_divisor h_conn q D with ⟨c, k, h_equiv, h_super⟩
  have h_k_neg : k < 0 := superstable_of_divisor_negative_k G q D unwin c k h_equiv h_super
  rcases maximal_superstable_exists G q c h_super with ⟨c', h_max', h_ge⟩
  rcases maximal_superstable_orientation G q c' h_max' with ⟨O, hO, h_orient_eq_c'⟩
  let H : CFDiv G := -(k+1) • (oneChip q) + c'.chips - c.chips
  have h_H_eff : effective H := by
    have diff_eff : effective (c'.chips - c.chips) := by
      rwa [sub_eff_iff_geq]
    have src_eff : effective (-(k+1) • oneChip q)  := by
      intro v
      rw [Pi.smul_apply, smul_eq_mul]
      apply mul_nonneg
      · -- Prove -(k + 1) ≥ 0
        linarith [h_k_neg]
      · -- Prove oneChip q v ≥ 0
        exact eff_one_chip q v
    have := (Eff G).add_mem src_eff diff_eff
    rwa [← add_sub_assoc] at this
  let M := c'.chips - oneChip q
  have M_eq : linearEquiv G M (D + H) := by
    simp only [linearEquiv, principal_iff_eq_prin, H, M] at ⊢ h_equiv
    rcases h_equiv with ⟨σ, eq_σ⟩
    use (-σ)
    rw [map_neg, ← eq_σ]
    funext v; simp only [neg_add_rev, Int.reduceNeg, zsmul_eq_mul, Int.cast_add, Int.cast_neg,
        Int.cast_one, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.one_apply,
        Pi.intCast_apply, Int.cast_eq, neg_sub]; ring

  have h_M_O : M = ordiv G O := by
    have c'_eq : c' = toConfig (orqed O hO) := by
      rw [← h_orient_eq_c']
      exact config_and_divisor_from_O O hO

    have : toDiv (genus G - 1) (toConfig (orqed O hO)) = ordiv G O := by
      calc
        toDiv (genus G - 1) (toConfig (orqed O hO))
            = toDiv (deg (orqed O hO).D) (toConfig (orqed O hO)) := by
                have h_deg_orqed : deg (orqed O hO).D = genus G - 1 := by
                  simpa only [orqed] using degree_ordiv O
                rw [h_deg_orqed]
        _ = (orqed O hO).D := div_of_config_of_div (orqed O hO)
        _ = ordiv G O := rfl
    rw [← this]
    dsimp only [toDiv, M]
    rw [c'_eq]
    have : (genus G - 1 - configDegree (toConfig (orqed O hO))) = -1 := by
      have h_cfg_deg : configDegree (toConfig (orqed O hO)) = genus G := by
        rw [← config_and_divisor_from_O O hO]
        exact config_degree_from_O O hO
      rw [h_cfg_deg]
      ring
    simp only [this, Int.reduceNeg, neg_smul, one_smul]
    rw [sub_eq_add_neg]
  have h_M_moderator : isModerator M := by
    exact ⟨O, ⟨hO.1, h_M_O⟩⟩
  use M, H

/-!
## The main Riemann-Roch inequality

`rank_degree_inequality` establishes the strict inequality
$$\deg(D) - g < r(D) - r(K_G - D),$$
which is the main step toward the Riemann-Roch theorem for graphs. The proof chooses an
effective divisor $E$ of degree $r(D)+1$ with $D-E$ unwinnable, writes $M \sim (D-E)+F$
for a moderator $M$ and effective divisor $F$ (`moderator_of_unwinnable`), and then
dualizes via `moderator_symmetry` to bound $r(K_G - D)$ by $\deg(F)$.
-/

/-- The strict Riemann-Roch inequality: $\deg(D) - g < r(D) - r(K_G - D)$. -/
theorem rank_degree_inequality
    {G : CFGraph} (h_conn : graphConnected G) (D : CFDiv G) :
    deg D - genus G < rank G D - rank G (canonicalDivisor G - D) := by
  rcases rank_get_effective G D with ⟨E, E_eff, E_deg, D_E_unwin⟩
  rcases moderator_of_unwinnable h_conn (D - E) D_E_unwin with ⟨M, F, M_moderator, F_eff, M_equiv⟩
  set M' := canonicalDivisor G - M with M'_eq
  have M'_moderator : isModerator M' := moderator_symmetry M M_moderator

  set D' := canonicalDivisor G - D with D'_eq
  have M'_equiv : linearEquiv G (D' - F + E) M' := by
    rw [M'_eq]
    dsimp only [linearEquiv, D']
    dsimp only [linearEquiv] at M_equiv
    rw [principal_iff_eq_prin] at M_equiv ⊢
    rcases M_equiv with ⟨σ, eq_σ⟩
    use σ
    rw [← eq_σ]
    abel

  have h_D'_F : ¬ winnable G (D' - F) := by
    by_contra!
    have := winnable_add_winnable G (D' - F) E this (winnable_of_effective G E E_eff)
    apply unwinnable_of_moderator M'_moderator
    apply winnable_equiv_winnable G (D' - F + E) M' this M'_equiv

  have ineq : deg F > rank G D' := by
      contrapose! h_D'_F
      apply (rank_geq_iff G D' (deg F)).mpr at h_D'_F
      dsimp only [rankGeq] at h_D'_F
      specialize h_D'_F F ⟨F_eff, rfl⟩
      exact h_D'_F

  -- Finally, degree calculations to finish the inequality
  have degF : deg F = - deg D + deg E + deg M := by
    rw [linear_equiv_preserves_deg G M (D - E + F) M_equiv]
    simp only [_root_.map_add, map_sub]
    linarith
  linarith [degF, moderator_degree M_moderator]
