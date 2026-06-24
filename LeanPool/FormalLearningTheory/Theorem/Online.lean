/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.GameInfra

/-!
# Online Learning Characterization Theorems

Characterization proofs for online learnability via the Littlestone dimension.
Game-theoretic infrastructure (LTree, isShattered, LittlestoneDim, SOA, versionSpace)
lives in `FLT_Proofs.Complexity.GameInfra`.

Main results:
- `forward_direction`: OnlineLearnable → LittlestoneDim < ⊤
- `backward_direction`: LittlestoneDim < ⊤ → OnlineLearnable
- `littlestone_characterization`: equivalence of the above
- `optimal_mistake_bound_eq_ldim`: OptimalMistakeBound = LittlestoneDim (for nonempty C)
-/

-- ============================================================
-- FORWARD DIRECTION: OnlineLearnable → LittlestoneDim < ⊤
-- ============================================================

/-- Forward direction: OnlineLearnable → LittlestoneDim < ⊤ -/
theorem forward_direction (X : Type) (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C → LittlestoneDim X C < ⊤ := by
  intro ⟨M, L, hL⟩
  by_contra hge
  push Not at hge
  have htop : LittlestoneDim X C = ⊤ := le_antisymm le_top hge
  have hunbounded : ∃ n, n > M ∧ ∃ T : LTree X n, T.isShattered C := by
    by_contra hc
    push Not at hc
    have hbound : LittlestoneDim X C ≤ ↑(↑M : WithTop ℕ) := by
      unfold LittlestoneDim
      apply iSup₂_le
      intro n ⟨T, hT⟩
      by_cases hmn : n ≤ M
      · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by exact_mod_cast hmn))
      · exact (hc n (by omega) T hT).elim
    rw [htop] at hbound; simp at hbound
  obtain ⟨n, hn, T, hTshat⟩ := hunbounded
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hne : C.Nonempty := T.nonempty_of_isShattered hTshat
  obtain ⟨seq, c, hcC, hcount⟩ := adversary_core L L.init T hTshat hne
  have hbound : L.mistakes c seq ≤ M := hL c hcC seq
  rw [← mistakesFrom_init_eq] at hbound; omega

-- ============================================================
-- BACKWARD DIRECTION: LittlestoneDim < ⊤ → OnlineLearnable
-- ============================================================

/-- In `WithBot (WithTop ℕ)`, `a < ↑↑(n+1) → a ≤ ↑↑n`. Reusable lattice fact. -/
private theorem WithBot_WithTop_lt_succ_le {a : WithBot (WithTop ℕ)} {n : ℕ}
    (h : a < ↑(↑(n + 1) : WithTop ℕ)) : a ≤ ↑(↑n : WithTop ℕ) := by
  cases a with
  | bot => exact bot_le
  | coe v =>
    cases v with
    | top => simp at h
    | coe m =>
      exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr
        (Nat.le_of_lt_succ (WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp h))))

-- ============================================================
-- INFRASTRUCTURE LEMMAS (all compile)
-- ============================================================

/-- Build a tree of depth k+1 from shattered subtrees on both sides.
    Parametrized over b : Bool so we don't need to case-split in the caller. -/
private theorem ldim_branch_lower_bound {X : Type} {V : ConceptClass X Bool}
    {x : X} {k : ℕ} {b : Bool}
    (hb : ∃ Tb : LTree X k, Tb.isShattered {c ∈ V | c x = b})
    (hnb : ∃ Tnb : LTree X k, Tnb.isShattered {c ∈ V | c x = !b})
    (hwb : ∃ c ∈ V, c x = b) (hwnb : ∃ c ∈ V, c x = !b) :
    LittlestoneDim X V ≥ ↑(↑(k + 1) : WithTop ℕ) := by
  obtain ⟨Tb, hTb⟩ := hb
  obtain ⟨Tnb, hTnb⟩ := hnb
  cases b
  · -- b = false: true-side = !b, false-side = b
    exact le_iSup₂_of_le (k + 1) ⟨.branch x Tnb Tb, hwnb, hwb, hTnb, hTb⟩ le_rfl
  · -- b = true: true-side = b, false-side = !b
    exact le_iSup₂_of_le (k + 1) ⟨.branch x Tb Tnb, hwb, hwnb, hTb, hTnb⟩ le_rfl

/-- SOA predicts the label whose side has higher Ldim. -/
private theorem soa_predict_spec {X : Type} (C : ConceptClass X Bool)
    (history : List (X × Bool)) (x : X) :
    let V := versionSpace C history
    let b := (SOA X C).predict history x
    LittlestoneDim X {c ∈ V | c x = b} ≥
    LittlestoneDim X {c ∈ V | c x = !b} := by
  simp only [SOA]
  split
  · simp only [Bool.not_true, ge_iff_le]
    assumption
  · simp only [Bool.not_false, ge_iff_le]
    rename_i h
    exact le_of_lt (not_le.mp h)

/-- Truncate a complete tree to a smaller depth. -/
def LTree.truncate {X : Type} {n m : ℕ} : (h : n ≤ m) → LTree X m → LTree X n := by
  intro h T; induction n generalizing m with
  | zero => exact .leaf
  | succ k ih =>
    match m, T, h with
    | _ + 1, .branch x l r, h =>
      exact .branch x (ih (Nat.le_of_succ_le_succ h) l) (ih (Nat.le_of_succ_le_succ h) r)

/-- A truncated tree is shattered if the original is. -/
theorem LTree.isShattered_truncate {X : Type} {C : ConceptClass X Bool}
    {m : ℕ} (T : LTree X m) (hT : T.isShattered C) {n : ℕ} (h : n ≤ m) :
    (T.truncate h).isShattered C := by
  induction n generalizing m C with
  | zero => exact T.nonempty_of_isShattered hT
  | succ k ih =>
    match m, T, h, hT with
    | _ + 1, .branch x l r, h, hT =>
      simp only [LTree.isShattered] at hT
      obtain ⟨hwt, hwf, hsl, hsr⟩ := hT
      simp only [LTree.truncate]
      exact ⟨hwt, hwf, ih l hsl (Nat.le_of_succ_le_succ h),
             ih r hsr (Nat.le_of_succ_le_succ h)⟩

/-- From Ldim ≥ d, extract a shattered tree of depth exactly d. -/
private theorem exists_shattered_of_ldim_ge {X : Type} {C : ConceptClass X Bool}
    {d : ℕ} (h : LittlestoneDim X C ≥ ↑(↑d : WithTop ℕ)) :
    ∃ T : LTree X d, T.isShattered C := by
  match d with
  | 0 =>
    -- Need C.Nonempty. From h: Ldim ≥ ↑↑0 > ⊥. If C empty, Ldim = ⊥. Contradiction.
    by_contra hall; push Not at hall
    have hne : ¬ C.Nonempty := hall .leaf
    have hle : LittlestoneDim X C ≤ ⊥ := by
      apply iSup₂_le; intro n ⟨T, hT⟩
      exact absurd (T.nonempty_of_isShattered hT) hne
    have : LittlestoneDim X C = ⊥ := le_antisymm hle bot_le
    rw [this] at h
    exact absurd h (by simp)
  | d + 1 =>
    by_contra hall; push Not at hall
    -- All trees of depth d+1 are not shattered. So Ldim ≤ d.
    have hle : LittlestoneDim X C ≤ ↑(↑d : WithTop ℕ) := by
      apply iSup₂_le; intro n ⟨T, hT⟩
      by_cases hnd : n ≤ d
      · exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by exact_mod_cast hnd))
      · push Not at hnd
        have hnd' : d + 1 ≤ n := hnd
        exact absurd (T.isShattered_truncate hT hnd') (hall _)
    -- But h says Ldim ≥ d + 1 > d. Contradiction.
    have hle' : (↑(↑(d + 1) : WithTop ℕ) : WithBot (WithTop ℕ)) ≤ ↑(↑d : WithTop ℕ) :=
      le_trans h hle
    exact absurd hle' (by norm_cast; omega)

-- ============================================================
-- KEY LEMMA: SOA mistake → Ldim strictly decreases
-- ============================================================

/-- When Ldim(V) = 0 (↑↑0), all concepts in V agree on every point.
    Key lemma for M-VersionSpaceCollapse. -/
private theorem ldim_zero_all_agree {X : Type} {V : ConceptClass X Bool}
    (hd : LittlestoneDim X V = ↑(↑0 : WithTop ℕ)) (_hne : V.Nonempty)
    (x : X) (c₁ c₂ : X → Bool) (hc₁ : c₁ ∈ V) (hc₂ : c₂ ∈ V) :
    c₁ x = c₂ x := by
  by_contra hdis
  -- c₁ x ≠ c₂ x, so one is true and the other false
  have hct : ∃ ct ∈ V, ct x = true := by
    cases h1 : c₁ x <;> cases h2 : c₂ x
    · exact absurd (h1.trans h2.symm) hdis  -- ff: contradiction
    · exact ⟨c₂, hc₂, h2⟩  -- ft
    · exact ⟨c₁, hc₁, h1⟩  -- tf
    · exact absurd (h1.trans h2.symm) hdis  -- tt: contradiction
  have hcf : ∃ cf ∈ V, cf x = false := by
    cases h1 : c₁ x <;> cases h2 : c₂ x
    · exact absurd (h1.trans h2.symm) hdis
    · exact ⟨c₁, hc₁, h1⟩
    · exact ⟨c₂, hc₂, h2⟩
    · exact absurd (h1.trans h2.symm) hdis
  -- Build a depth-1 shattered tree
  obtain ⟨ct, hctV, hctx⟩ := hct
  obtain ⟨cf, hcfV, hcfx⟩ := hcf
  have hge : LittlestoneDim X V ≥ ↑(↑1 : WithTop ℕ) :=
    le_iSup₂_of_le 1 ⟨.branch x .leaf .leaf,
      ⟨ct, hctV, hctx⟩, ⟨cf, hcfV, hcfx⟩,
      ⟨ct, ⟨hctV, hctx⟩⟩, ⟨cf, ⟨hcfV, hcfx⟩⟩⟩ le_rfl
  rw [hd] at hge
  exact absurd hge (by norm_cast)

/-- On an SOA mistake, the Ldim of the version space strictly decreases. -/
private theorem ldim_strict_decrease_on_mistake {X : Type}
    {C : ConceptClass X Bool} {history : List (X × Bool)} {x : X} {c : X → Bool}
    (hc_vs : c ∈ versionSpace C history)
    (hpred : (SOA X C).predict history x ≠ c x)
    (hfin : LittlestoneDim X (versionSpace C history) < ⊤) :
    LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) <
    LittlestoneDim X (versionSpace C history) := by
  -- Setup
  let V := versionSpace C history
  let b := (SOA X C).predict history x
  have hcx_ne_b : c x ≠ b := fun h => hpred (h ▸ rfl)
  -- New version space ⊆ {c' ∈ V | c' x = c x}
  have hvs_sub : versionSpace C (history ++ [(x, c x)]) ⊆ {c' ∈ V | c' x = c x} := by
    intro c' ⟨hc'C, hcons⟩
    exact ⟨⟨hc'C, fun p hp => hcons p (List.mem_append_left _ hp)⟩,
           hcons (x, c x) (List.mem_append_right _ (List.mem_singleton.mpr rfl))⟩
  have hle_side : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) ≤
      LittlestoneDim X {c' ∈ V | c' x = c x} := by
    apply iSup₂_le; intro n ⟨T, hT⟩
    exact le_iSup₂_of_le n ⟨T, T.isShattered_mono hvs_sub hT⟩ le_rfl
  -- Get finite Ldim
  obtain ⟨d, hd⟩ : ∃ d : ℕ, LittlestoneDim X V = ↑(↑d : WithTop ℕ) := by
    cases hc : LittlestoneDim X V with
    | bot => -- Ldim = ⊥ means empty. But c ∈ V, contradiction.
      have : V.Nonempty := ⟨c, hc_vs⟩
      have hge : LittlestoneDim X V ≥ ↑(↑0 : WithTop ℕ) :=
        le_iSup₂_of_le 0 ⟨.leaf, this⟩ le_rfl
      rw [hc] at hge; exact absurd hge (by simp)
    | coe v =>
      cases v with
      | top => -- ⊤ case: contradicts hfin
        have : LittlestoneDim X V = ⊤ := hc
        rw [this] at hfin; exact absurd hfin (lt_irrefl _)
      | coe n => exact ⟨n, rfl⟩
  -- c x = !b (since c x ≠ b and Bool has exactly two values)
  have hcx_eq_notb : c x = !b := by
    change c x = !(SOA X C).predict history x
    cases hcx : c x <;> cases hbv : (SOA X C).predict history x <;> simp_all
  -- Handle d = 0: Path B dissolves Γ₂₁ (M-CaseElimination)
  -- When Ldim(V)=0, all concepts agree → SOA predicts correctly → no mistake possible
  cases hd0 : d with
  | zero =>
    rw [hd0] at hd
    have hne : V.Nonempty := ⟨c, hc_vs⟩
    -- All concepts in V agree on x with c
    have hagree : ∀ c' ∈ V, c' x = c x :=
      fun c' hc' => ldim_zero_all_agree hd hne x c' c hc' hc_vs
    -- SOA sides: {c' ∈ V | c' x = c x} = V, {c' ∈ V | c' x = !(c x)} = ∅
    -- So Ldim of c x side ≥ 0, Ldim of !(c x) side = ⊥
    -- SOA picks the c x side → predicts c x → no mistake
    have h_cx_side_eq_V : {c' ∈ V | c' x = c x} = V := by
      ext c'; simp only [Set.mem_sep_iff]; exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hagree c' h⟩⟩
    have h_notcx_empty : ¬ ({c' ∈ V | c' x = !(c x)}).Nonempty := by
      intro ⟨c', hc'V, hc'x⟩
      have := hagree c' hc'V
      cases hcx : c x <;> simp_all
    have h_notcx_ldim : LittlestoneDim X {c' ∈ V | c' x = !(c x)} = ⊥ := by
      apply le_antisymm _ bot_le
      apply iSup₂_le; intro n ⟨T, hT⟩
      exact absurd (T.nonempty_of_isShattered hT) h_notcx_empty
    -- Now show SOA predicts c x:
    -- If c x = true: Ldim(true side) = Ldim(V) ≥ 0 > ⊥ = Ldim(false side) → SOA picks true = c x
    -- If c x = false: Ldim(true side) = ⊥ < Ldim(false side) = Ldim(V) → SOA picks false = c x
    exfalso; apply hpred
    show (SOA X C).predict history x = c x
    simp only [SOA]
    cases hcx : c x
    · -- c x = false
      simp only [hcx, Bool.not_false] at h_notcx_ldim h_cx_side_eq_V
      -- true side is empty (Ldim = ⊥), false side = V
      simp only [ite_eq_right_iff]
      intro hge_contra
      -- hge_contra : Ldim(true side) ≥ Ldim(false side)
      -- But Ldim(true side) = ⊥ and Ldim(false side) ≥ 0
      rw [h_notcx_ldim] at hge_contra
      have : LittlestoneDim X {c' ∈ V | c' x = false} ≥ ↑(↑0 : WithTop ℕ) := by
        rw [h_cx_side_eq_V]
        exact le_iSup₂_of_le 0 ⟨.leaf, hne⟩ le_rfl
      exact absurd (le_trans this hge_contra) (by simp)
    · -- c x = true
      simp only [hcx, Bool.not_true] at h_notcx_ldim h_cx_side_eq_V
      -- false side is empty, true side = V
      simp only [ite_eq_left_iff]
      intro hlt_contra
      -- hlt_contra says ¬(Ldim(true) ≥ Ldim(false)), i.e., Ldim(true) < Ldim(false)
      -- But Ldim(false) = ⊥ < Ldim(true) ≥ 0. Contradiction.
      push Not at hlt_contra
      rw [h_notcx_ldim] at hlt_contra
      have : LittlestoneDim X {c' ∈ V | c' x = true} ≥ ↑(↑0 : WithTop ℕ) := by
        rw [h_cx_side_eq_V]
        exact le_iSup₂_of_le 0 ⟨.leaf, hne⟩ le_rfl
      exact absurd hlt_contra not_lt_bot
  | succ d' =>
  -- d ≥ 1. Use suffices + by_contra + both-side extraction.
  rw [hd0] at hd -- hd : LittlestoneDim X V = ↑(↑(d' + 1) : WithTop ℕ)
  suffices hsuff : LittlestoneDim X {c' ∈ V | c' x = c x} < ↑(↑(d' + 1) : WithTop ℕ) by
    calc LittlestoneDim X (versionSpace C (history ++ [(x, c x)]))
        ≤ LittlestoneDim X {c' ∈ V | c' x = c x} := hle_side
      _ < ↑(↑(d' + 1) : WithTop ℕ) := hsuff
      _ = LittlestoneDim X V := hd.symm
  by_contra hge; push Not at hge
  have hsoa := soa_predict_spec C history x
  have hnb_ge : LittlestoneDim X {c' ∈ V | c' x = !b} ≥ ↑(↑(d' + 1) : WithTop ℕ) := by
    rwa [show (c x) = !b from hcx_eq_notb] at hge
  have hb_ge : LittlestoneDim X {c' ∈ V | c' x = b} ≥ ↑(↑(d' + 1) : WithTop ℕ) :=
    le_trans hnb_ge hsoa
  obtain ⟨Tb, hTb⟩ := exists_shattered_of_ldim_ge hb_ge
  obtain ⟨Tnb, hTnb⟩ := exists_shattered_of_ldim_ge hnb_ge
  have hwnb : ∃ c' ∈ V, c' x = !b := ⟨c, hc_vs, hcx_eq_notb⟩
  -- d' + 1 ≥ 1: extract b-side witness from the depth-(d'+1) shattered tree
  have hwb : ∃ c' ∈ V, c' x = b := by
    match Tb, hTb with
    | .branch y l r, hTb =>
      simp only [LTree.isShattered] at hTb
      obtain ⟨⟨c', hc'mem, _⟩, _⟩ := hTb
      exact ⟨c', hc'mem.1, hc'mem.2⟩
  have hge_dp : LittlestoneDim X V ≥ ↑(↑(d' + 1 + 1) : WithTop ℕ) :=
    ldim_branch_lower_bound ⟨Tb, hTb⟩ ⟨Tnb, hTnb⟩ hwb hwnb
  rw [hd] at hge_dp
  exact absurd hge_dp (by norm_cast; omega)

-- ============================================================
-- BACKWARD DIRECTION (M-Potential)
-- ============================================================

/-- Extending a consistent history by `(x, c x)` keeps it consistent with `c`. -/
private theorem cons_history_append {X : Type} {c : X → Bool} {history : List (X × Bool)}
    {x : X} (hcons : ∀ p ∈ history, c p.1 = p.2) :
    ∀ p ∈ history ++ [(x, c x)], c p.1 = p.2 := by
  intro p hp
  cases List.mem_append.mp hp with
  | inl h => exact hcons p h
  | inr h => have hp_eq : p = (x, c x) := by simpa using h
             rw [hp_eq]

/-- The Ldim of the version space is monotone under appending to the history. -/
private theorem ldim_versionSpace_append_le {X : Type} {C : ConceptClass X Bool}
    {history : List (X × Bool)} {p : X × Bool} :
    LittlestoneDim X (versionSpace C (history ++ [p])) ≤
    LittlestoneDim X (versionSpace C history) := by
  apply iSup₂_le; intro n ⟨T, hT⟩
  exact le_iSup₂_of_le n ⟨T, T.isShattered_mono versionSpace_append hT⟩ le_rfl

/-- SOA mistakes from a given state are bounded by the Ldim of the version space.
    This is the core M-Potential argument. -/
private theorem soa_mistakes_bounded {X : Type} {C : ConceptClass X Bool}
    (c : X → Bool) (hcC : c ∈ C)
    (history : List (X × Bool))
    (hcons : ∀ p ∈ history, c p.1 = p.2)
    (d : ℕ) (hd : LittlestoneDim X (versionSpace C history) ≤ ↑(↑d : WithTop ℕ))
    (hfin : LittlestoneDim X (versionSpace C history) < ⊤)
    (seq : List X) :
    (SOA X C).mistakesFrom history c seq ≤ d := by
  induction seq generalizing history d with
  | nil => simp [OnlineLearner.mistakesFrom]
  | cons x xs ih =>
    -- Use interface lemma to unfold one step (Inv-stable: doesn't expose SOA internals)
    rw [SOA_mistakesFrom_cons]
    by_cases hmistake : (SOA X C).predict history x ≠ c x
    · -- SOA makes a mistake: Ldim strictly decreases (M-Potential: φ decreases)
      rw [if_pos hmistake]
      have hc_vs : c ∈ versionSpace C history := target_in_versionSpace hcC hcons
      have hdecrease := ldim_strict_decrease_on_mistake hc_vs hmistake hfin
      have hcons' := cons_history_append (c := c) (x := x) hcons
      -- d must be ≥ 1 (Ldim decreases, so d > 0)
      cases d with
      | zero =>
        -- Ldim(V) ≤ 0 but Ldim decreases → Ldim(V') < Ldim(V) ≤ 0.
        -- But c ∈ V', so V' nonempty, so Ldim(V') ≥ 0. Contradiction.
        have hc_vs' : c ∈ versionSpace C (history ++ [(x, c x)]) :=
          target_in_versionSpace hcC hcons'
        have hge0 : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) ≥
            ↑(↑0 : WithTop ℕ) :=
          le_iSup₂_of_le 0 ⟨.leaf, ⟨c, hc_vs'⟩⟩ le_rfl
        have hlt := lt_of_lt_of_le hdecrease hd
        exact absurd hlt (not_lt.mpr hge0)
      | succ d' =>
        -- Ldim of new VS ≤ d' (reusable lattice fact: a < ↑↑(d'+1) → a ≤ ↑↑d')
        have hd_new : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) ≤
            ↑(↑d' : WithTop ℕ) :=
          WithBot_WithTop_lt_succ_le (lt_of_lt_of_le hdecrease hd)
        have hfin_new : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) < ⊤ :=
          lt_of_lt_of_le hdecrease (le_of_lt hfin)
        have ih_result := ih (history ++ [(x, c x)]) hcons' d' hd_new hfin_new
        omega
    · -- SOA predicts correctly: no mistake, φ doesn't decrease but bound holds
      rw [if_neg hmistake]; simp only [Nat.zero_add]
      have hcons' := cons_history_append (c := c) (x := x) hcons
      have hle_new : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) ≤
          ↑(↑d : WithTop ℕ) := ldim_versionSpace_append_le.trans hd
      have hfin_new : LittlestoneDim X (versionSpace C (history ++ [(x, c x)])) < ⊤ :=
        lt_of_le_of_lt ldim_versionSpace_append_le hfin
      exact ih (history ++ [(x, c x)]) hcons' d hle_new hfin_new

/-- The version space on the empty history is all of `C`. -/
private theorem versionSpace_nil {X : Type} (C : ConceptClass X Bool) :
    versionSpace C [] = C := by ext c'; simp [versionSpace]

/-- Backward direction: LittlestoneDim < ⊤ → OnlineLearnable. -/
theorem backward_direction (X : Type) (C : ConceptClass X Bool) :
    LittlestoneDim X C < ⊤ → OnlineLearnable X Bool C := by
  intro h
  -- Extract finite Ldim bound
  obtain ⟨d, hd⟩ : ∃ d : ℕ, LittlestoneDim X C ≤ ↑(↑d : WithTop ℕ) := by
    cases hc : LittlestoneDim X C with
    | bot => exact ⟨0, bot_le⟩
    | coe v =>
      cases v with
      | top => simp [hc] at h
      | coe n => exact ⟨n, le_rfl⟩
  refine ⟨d, SOA X C, fun c hcC seq => ?_⟩
  -- SOA makes at most d mistakes (M-Potential)
  have hle : LittlestoneDim X (versionSpace C []) ≤ ↑(↑d : WithTop ℕ) := by
    rw [versionSpace_nil]; exact hd
  have hfin : LittlestoneDim X (versionSpace C []) < ⊤ := by
    rw [versionSpace_nil]
    exact lt_of_le_of_lt hd (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (a := d)))
  have hmf := soa_mistakes_bounded c hcC [] (by simp) d hle hfin seq
  rwa [show (SOA X C).mistakesFrom [] c seq = (SOA X C).mistakesFrom (SOA X C).init c seq
    from by rw [SOA_init_eq],
    mistakesFrom_init_eq] at hmf

-- ============================================================
-- MAIN THEOREMS
-- ============================================================

/-- Littlestone characterization: C is online-learnable iff LittlestoneDim(C) < ∞. -/
theorem littlestone_characterization (X : Type)
    (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C ↔ LittlestoneDim X C < ⊤ :=
  ⟨forward_direction X C, backward_direction X C⟩

/-- Adversary lower bound (M-InfSup reusable primitive):
    If a tree of depth n is shattered by C, then any mistake-bounded learner
    must allow at least n mistakes. This is the "inf ≥ sup" half of minimax. -/
private theorem adversary_lower_bound {X : Type} {C : ConceptClass X Bool}
    {n : ℕ} (T : LTree X n) (hT : T.isShattered C)
    {M : ℕ} (hM : MistakeBounded X Bool C M) : n ≤ M := by
  obtain ⟨L, hL⟩ := hM
  have hne : C.Nonempty := T.nonempty_of_isShattered hT
  obtain ⟨seq, c, hcC, hcount⟩ := adversary_core L L.init T hT hne
  have hbound := hL c hcC seq
  rw [← mistakesFrom_init_eq] at hbound
  omega

/-- The optimal mistake bound equals the Littlestone dimension (for nonempty C).
    Path B: OptimalMistakeBound : WithTop ℕ, LittlestoneDim : WithBot (WithTop ℕ).
    For nonempty C, LittlestoneDim ≥ 0, so the coercion ↑(OptimalMistakeBound) works. -/
theorem optimal_mistake_bound_eq_ldim (X : Type)
    (C : ConceptClass X Bool) (hne : C.Nonempty) :
    (↑(OptimalMistakeBound X C) : WithBot (WithTop ℕ)) = LittlestoneDim X C := by
  apply le_antisymm
  · -- ≤ direction: OptimalMistakeBound ≤ Ldim
    -- If Ldim = ⊤, then OptimalMistakeBound ≤ ⊤ trivially (anything ≤ ↑⊤)
    -- If Ldim = ↑↑d, then SOA achieves d mistakes → MistakeBounded d → OptimalMistakeBound ≤ d
    cases hc : LittlestoneDim X C with
    | bot =>
      -- Ldim = ⊥ for nonempty C → impossible (C.Nonempty gives shattered leaf)
      have hge : LittlestoneDim X C ≥ ↑(↑0 : WithTop ℕ) :=
        le_iSup₂_of_le 0 ⟨.leaf, hne⟩ le_rfl
      rw [hc] at hge; exact absurd hge (by simp)
    | coe v =>
      cases v with
      | top => -- Ldim = ⊤ → ↑OptimalMistakeBound ≤ ↑⊤ = ⊤
        exact le_top
      | coe d => -- Ldim = ↑↑d; use SOA directly (mistake bound d)
        have hfin : LittlestoneDim X C < ⊤ := by
          rw [hc]; exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top (a := d))
        have hMB_d : MistakeBounded X Bool C d := by
          refine ⟨SOA X C, fun c' hc'C seq => ?_⟩
          have hle : LittlestoneDim X (versionSpace C []) ≤ ↑(↑d : WithTop ℕ) := by
            rw [versionSpace_nil]; exact le_of_eq hc
          have hfin' : LittlestoneDim X (versionSpace C []) < ⊤ := by
            rw [versionSpace_nil]; exact hfin
          have hmf := soa_mistakes_bounded c' hc'C [] (by simp) d hle hfin' seq
          rwa [show (SOA X C).mistakesFrom [] c' seq = (SOA X C).mistakesFrom (SOA X C).init c' seq
            from by rw [SOA_init_eq], mistakesFrom_init_eq] at hmf
        exact WithBot.coe_le_coe.mpr (iInf₂_le d hMB_d)
  · -- ≥ direction: Ldim ≤ OptimalMistakeBound
    -- For each shattered tree of depth n, adversary forces n mistakes → OptimalMistakeBound ≥ n
    apply iSup₂_le; intro n ⟨T, hT⟩
    -- Any learner makes ≥ n mistakes against the adversary from T
    -- So MistakeBounded M → M ≥ n → OptimalMistakeBound ≥ n
    suffices h : (↑(↑n : WithTop ℕ) : WithBot (WithTop ℕ)) ≤ ↑(OptimalMistakeBound X C) by
      exact h
    apply WithBot.coe_le_coe.mpr
    -- Need: ↑n ≤ OptimalMistakeBound X C, i.e., ↑n ≤ ⨅ M (_ : MistakeBounded), ↑M
    -- Equivalently: ∀ M, MistakeBounded M → n ≤ M
    apply le_iInf₂; intro M hM
    -- Use the reusable adversary lower bound (M-InfSup primitive)
    exact WithTop.coe_le_coe.mpr (adversary_lower_bound T hT hM)
