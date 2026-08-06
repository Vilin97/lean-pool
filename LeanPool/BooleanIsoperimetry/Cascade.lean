/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Nat.Choose.Sum
import LeanPool.BooleanIsoperimetry.Cube

/-!
# Binomial cascade arithmetic

This file develops binomial-prefix and Macaulay-cascade infrastructure for
simplicial initial segments in the Boolean cube, including the slice recurrence
for the Harper boundary function `H`.
-/

open scoped BigOperators

namespace BooleanIsoperimetry

/--
`IsBinomialCascade n k r t` is the canonical layer decomposition of `k`
in the `n`-cube: all layers of sizes `< r` are full, and `t` points are
taken from layer `r`.

The final disjunct makes the decomposition canonical at layer boundaries:
when a layer is completely full, we move to the next layer with residual `0`.
-/
def IsBinomialCascade (n k r t : ℕ) : Prop :=
  r ≤ n + 1 ∧
  t ≤ Nat.choose n r ∧
  k = binomPrefix n r + t ∧
  (t < Nat.choose n r ∨ r = n + 1)

/-- The lower-slice size determined by cascade parameters `n`, `r`, and `t`. -/
def cascadeSlice0Value (n r t : ℕ) : ℕ :=
  binomPrefix n r + (t - choosePred n r)

/-- The upper-slice size determined by cascade parameters `n`, `r`, and `t`. -/
def cascadeSlice1Value (n r t : ℕ) : ℕ :=
  binomPrefix n (r - 1) + min t (choosePred n r)

/--
The algebraic lower/upper split for the canonical cascade of `k` in dimension
`n + 1`. It is independent of `slice0`, `slice1`, `rank`, and neighborhoods.
-/
def CascadeSplit (n k p q : ℕ) : Prop :=
  ∃ r t, IsBinomialCascade (n + 1) k r t ∧
    p = cascadeSlice0Value n r t ∧
    q = cascadeSlice1Value n r t


/--
Abel summation majorization over ℤ: if `v` is majorized by `u` in prefix sums,
and `w` is antitone, then the `w`-weighted sum of `v` is ≤ that of `u`.
-/
lemma int_sum_mul_le_of_prefix_le_of_antitone_weight
    (M : ℕ) (u v w : ℕ → ℤ)
    (hpref : ∀ r ≤ M, ∑ i ∈ Finset.range r, v i ≤ ∑ i ∈ Finset.range r, u i)
    (htot : ∑ i ∈ Finset.range M, u i = ∑ i ∈ Finset.range M, v i)
    (_ : ∀ i, i < M → 0 ≤ w i)
    (hwanti : ∀ i, i + 1 < M → w (i + 1) ≤ w i) :
    ∑ i ∈ Finset.range M, w i * v i ≤ ∑ i ∈ Finset.range M, w i * u i := by
  have H : ∑ i ∈ Finset.range M, w i * (u i - v i) ≥ 0 := by
    by_cases hM : M = 0
    · simp [hM]
    have hM_pos : 0 < M := Nat.pos_of_ne_zero hM
    have h_sum_parts := Finset.sum_range_by_parts (n := M) (f := w) (g := fun i => u i - v i)
    have htot_sub : ∑ i ∈ Finset.range M, (u i - v i) = 0 := by
      rw [Finset.sum_sub_distrib, htot, sub_self]
    rw [htot_sub, smul_zero, zero_sub] at h_sum_parts
    have h_rw : ∀ i, w i * (u i - v i) = w i • (u i - v i) := fun i => rfl
    simp_rw [h_rw]
    rw [h_sum_parts]
    have h_sum_nonpos :
        ∑ i ∈ Finset.range (M - 1), (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1),
          (u j - v j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      rw [Finset.mem_range] at hi
      have hw_diff : w (i + 1) - w i ≤ 0 := by
        have : i + 1 < M := by omega
        linarith [hwanti i this]
      have h_S : 0 ≤ ∑ j ∈ Finset.range (i + 1), (u j - v j) := by
        rw [Finset.sum_sub_distrib, sub_nonneg]
        apply hpref (i + 1) (by omega)
      have H_smul : (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), (u j - v j) =
        (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), (u j - v j) := rfl
      rw [H_smul]
      exact mul_nonpos_of_nonpos_of_nonneg hw_diff h_S
    linarith
  have H2 : ∑ i ∈ Finset.range M, w i * u i - ∑ i ∈ Finset.range M, w i * v i ≥ 0 := by
    calc ∑ i ∈ Finset.range M, w i * u i - ∑ i ∈ Finset.range M, w i * v i
      _ = ∑ i ∈ Finset.range M, (w i * u i - w i * v i) := by rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ Finset.range M, w i * (u i - v i) := by { congr; ext i; ring }
      _ ≥ 0 := H
  linarith

-- ==========================================
-- Arithmetic helpers for binomPrefix
-- ==========================================

lemma binomPrefix_zero (n : ℕ) : binomPrefix n 0 = 0 := by
  simp [binomPrefix]

lemma binomPrefix_succ (n r : ℕ) :
    binomPrefix n (r + 1) = binomPrefix n r + Nat.choose n r := by
  simp [binomPrefix, Finset.sum_range_succ]

lemma binomPrefix_mono (n : ℕ) {r s : ℕ} (h : r ≤ s) :
    binomPrefix n r ≤ binomPrefix n s := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

lemma binomPrefix_full (n : ℕ) : binomPrefix n (n + 1) = 2 ^ n := by
  simpa [binomPrefix] using Nat.sum_range_choose n

lemma choose_eq_zero_of_gt {n r : ℕ} (h : n < r) : Nat.choose n r = 0 := by
  exact Nat.choose_eq_zero_of_lt h

lemma binomPrefix_le_two_pow (n r : ℕ) : binomPrefix n r ≤ 2 ^ n := by
  by_cases hr : r ≤ n + 1
  · exact le_trans (binomPrefix_mono n hr) (by rw [binomPrefix_full])
  · rw [← binomPrefix_full]
    unfold binomPrefix
    rw [← Finset.sum_range_add_sum_Ico _ (by linarith : n + 1 ≤ r)]
    simp +zetaDelta only [not_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero,
      Finset.sum_eq_zero_iff, Finset.mem_Ico, Order.add_one_le_iff, and_imp] at *
    exact fun i hi₁ hi₂ => Nat.choose_eq_zero_of_lt hi₁

lemma binomPrefix_eq_two_pow_of_ge (n r : ℕ) (h : n + 1 ≤ r) :
    binomPrefix n r = 2 ^ n := by
  apply le_antisymm
  · exact binomPrefix_le_two_pow n r
  · rw [← binomPrefix_full n]
    exact binomPrefix_mono n h

/-
Pascal's identity at the level of binomial prefixes.
-/
lemma binomPrefix_pascal (n r : ℕ) :
    binomPrefix (n + 1) r = binomPrefix n r + binomPrefix n (r - 1) := by
  simp +arith +decide only [binomPrefix]
  rcases r with (_ | r) <;> simp +arith +decide only [Finset.range_zero, Finset.sum_empty,
    zero_tsub, add_zero, Finset.sum_range_succ', Nat.choose_succ_succ, Nat.succ_eq_add_one,
    Nat.choose_zero_right, add_tsub_cancel_right]
  rw [Finset.sum_add_distrib]

/-- `Nat.choose (n+1) r` splits as `Nat.choose n r + choosePred n r`. -/
lemma choose_succ_dim (n r : ℕ) :
    Nat.choose (n + 1) r = Nat.choose n r + choosePred n r := by
  rcases r with _ | r
  · simp [choosePred]
  · simp [choosePred, Nat.choose_succ_succ, Nat.add_comm]

/-- `binomPrefix n (r-1) + choosePred n r = binomPrefix n r`. -/
lemma binomPrefix_pred_add_choosePred (n r : ℕ) :
    binomPrefix n (r - 1) + choosePred n r = binomPrefix n r := by
  rcases r with _ | r
  · simp [choosePred, binomPrefix_zero]
  · simp only [Nat.add_sub_cancel, choosePred, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    rw [binomPrefix_succ]

/-
Existence of the canonical binomial cascade decomposition.
-/
lemma exists_isBinomialCascade (n k : ℕ) (hk : k ≤ 2 ^ (n + 1)) :
    ∃ r t, IsBinomialCascade (n + 1) k r t := by
  by_contra! h_contra
  -- Let $r$ be the largest integer such that $binomPrefix (n+1) r \leq k$.
  obtain ⟨r, hr⟩ : ∃ r, r ≤ n + 2 ∧ binomPrefix (n + 1) r ≤ k ∧
      ∀ s, r < s → s ≤ n + 2 → k < binomPrefix (n + 1) s := by
    have hne : (Finset.filter (fun r => binomPrefix (n + 1) r ≤ k) (Finset.Iic (n + 2))).Nonempty :=
      ⟨0, by simp [binomPrefix_zero]⟩
    obtain ⟨hle, hbk⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    exact ⟨_, Finset.mem_Iic.mp hle, hbk, fun s hs₁ hs₂ => not_le.mp fun hs₃ =>
      hs₁.not_ge (Finset.le_max' _ s (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hs₂, hs₃⟩))⟩
  refine h_contra r (k - binomPrefix (n + 1) r) ⟨ hr.1, ?_, ?_, ?_ ⟩
  · by_cases hr' : r = n + 2
    · simp_all +decide [binomPrefix_full]
    · have := hr.2.2 (r + 1) (Nat.lt_succ_self r) (Nat.succ_le_of_lt (lt_of_le_of_ne hr.1 hr'))
      simp_all +decide [binomPrefix_succ]
      linarith
  · rw [Nat.add_sub_of_le hr.2.1]
  · by_cases hr_eq : r = n + 2
    · aesop
    · have := hr.2.2 (r + 1) (Nat.lt_succ_self r) (Nat.succ_le_of_lt (lt_of_le_of_ne hr.1 hr_eq))
      simp_all +decide [binomPrefix_succ]
      omega

/-- The two cascade slice values sum to `k`. -/
lemma cascade_slice_add {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice0Value n r t + cascadeSlice1Value n r t = k := by
  obtain ⟨_, ht, hk, _⟩ := h
  have hp := binomPrefix_pascal n r
  unfold cascadeSlice0Value cascadeSlice1Value
  omega

/-- The lower cascade slice value is at most `2^n`. -/
lemma cascadeSlice0Value_le {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice0Value n r t ≤ 2 ^ n := by
  obtain ⟨_, ht, _, _⟩ := h
  have hd := choose_succ_dim n r
  have hsucc := binomPrefix_succ n r
  have hle := binomPrefix_le_two_pow n (r + 1)
  unfold cascadeSlice0Value
  omega

/-- The upper cascade slice value is at most `2^n`. -/
lemma cascadeSlice1Value_le {n k r t : ℕ} (_ : IsBinomialCascade (n + 1) k r t) :
    cascadeSlice1Value n r t ≤ 2 ^ n := by
  have hadd := binomPrefix_pred_add_choosePred n r
  have hle := binomPrefix_le_two_pow n r
  unfold cascadeSlice1Value
  omega

/--
Every integer `k ≤ 2^(n+1)` admits a valid cascade split `(p, q)`
bounded by `2^n`.
-/
lemma exists_cascade_split (n k : ℕ) (hk : k ≤ 2 ^ (n + 1)) :
    ∃ p q, p ≤ 2 ^ n ∧ q ≤ 2 ^ n ∧ p + q = k ∧ CascadeSplit n k p q := by
  obtain ⟨r, t, hcasc⟩ := exists_isBinomialCascade n k hk
  refine ⟨cascadeSlice0Value n r t, cascadeSlice1Value n r t,
    cascadeSlice0Value_le hcasc, cascadeSlice1Value_le hcasc,
    cascade_slice_add hcasc, r, t, hcasc, rfl, rfl⟩

/-- **Uniqueness of the canonical binomial cascade decomposition.**  For a fixed
total `k` and dimension `m`, the canonical cascade `(r, t)` with all layers below
`r` full and `t` points of layer `r` is unique.  Standard fact: if `r < r'` then
the full prefix `binomPrefix m (r+1)` already exceeds the partial sum, forcing
`t = Nat.choose m r` and (via the canonical boundary disjunct) `r = m`, which is
incompatible with `r < r' ≤ m`. -/
lemma isBinomialCascade_unique {m k r t r' t' : ℕ}
    (h : IsBinomialCascade m k r t) (h' : IsBinomialCascade m k r' t') :
    r = r' ∧ t = t' := by
  obtain ⟨hr, ht, hk, hdisj⟩ := h
  obtain ⟨hr', ht', hk', hdisj'⟩ := h'
  -- The strict case `a < b` for two valid cascade pairs of the same `k` is impossible.
  have key : ∀ a b ta tb, a < b → b ≤ m + 1 → ta ≤ Nat.choose m a →
      (ta < Nat.choose m a ∨ a = m + 1) →
      binomPrefix m a + ta = binomPrefix m b + tb → False := by
    intro a b ta tb hab hbm hta hdisj_a hsum
    have h1 : binomPrefix m (a + 1) ≤ binomPrefix m b :=
      binomPrefix_mono m (Nat.succ_le_of_lt hab)
    rw [binomPrefix_succ] at h1
    rcases hdisj_a with hlt | heq
    · omega
    · omega
  have hrr : r = r' := by
    rcases lt_trichotomy r r' with hlt | heq | hgt
    · exact (key r r' t t' hlt hr' ht hdisj (hk.symm.trans hk')).elim
    · exact heq
    · exact (key r' r t' t hgt hr ht' hdisj' (hk'.symm.trans hk)).elim
  subst hrr
  exact ⟨rfl, by omega⟩

/-- **Uniqueness of the canonical cascade split.**  Because the underlying
binomial cascade `(r, t)` is unique, the canonical split `(p, q)` of a fixed total
`k` in dimension `n + 1` is uniquely determined.  This is what lets the
Frankl–Füredi terminal family be identified with *the* canonical cascade pair. -/
lemma cascadeSplit_unique {n k p q p' q' : ℕ}
    (h : CascadeSplit n k p q) (h' : CascadeSplit n k p' q') :
    p = p' ∧ q = q' := by
  obtain ⟨r, t, hbc, hp, hq⟩ := h
  obtain ⟨r', t', hbc', hp', hq'⟩ := h'
  obtain ⟨hrr, htt⟩ := isBinomialCascade_unique hbc hbc'
  subst hrr; subst htt
  exact ⟨hp.trans hp'.symm, hq.trans hq'.symm⟩

-- ==========================================
-- Layer structure of the simplicial order
-- ==========================================

/-- The number of vertices of the `n`-cube with cardinality exactly `c` is `C(n,c)`. -/
lemma card_filter_card_eq (n c : ℕ) :
    (Finset.univ.filter (fun w : Cube n => w.card = c)).card = Nat.choose n c := by
  rw [show (Finset.univ.filter (fun w : Cube n => w.card = c))
        = Finset.powersetCard c (Finset.univ : Finset (Fin n)) by
      ext w; simp [Finset.mem_powersetCard]]
  rw [Finset.card_powersetCard]; simp

/-- The number of vertices of the `n`-cube with cardinality `< c` is `binomPrefix n c`. -/
lemma card_filter_card_lt (n c : ℕ) :
    (Finset.univ.filter (fun w : Cube n => w.card < c)).card = binomPrefix n c := by
  induction c with
  | zero => simp [binomPrefix_zero]
  | succ c ih =>
    have hsplit : (Finset.univ.filter (fun w : Cube n => w.card < c + 1))
        = (Finset.univ.filter (fun w : Cube n => w.card < c))
          ∪ (Finset.univ.filter (fun w : Cube n => w.card = c)) := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    rw [hsplit, Finset.card_union_of_disjoint, ih, card_filter_card_eq, binomPrefix_succ]
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    omega

/-- The set of low-cardinality vertices is exactly an initial segment. -/
lemma lowCard_eq_initSeg (n c : ℕ) :
    Finset.univ.filter (fun w : Cube n => w.card < c)
      = simplicialInitSeg n (binomPrefix n c) := by
  have hdc : ∀ x y, simplicialLe x y →
      y ∈ Finset.univ.filter (fun w : Cube n => w.card < c) →
      x ∈ Finset.univ.filter (fun w : Cube n => w.card < c) := by
    intro x y hxy hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have : x.card ≤ y.card := by rcases hxy with h | ⟨h, _⟩ <;> omega
    omega
  have h := downwardClosed_eq_initSeg hdc
  rw [card_filter_card_lt] at h
  exact h

/-- `rank` versus cardinality: `rank w < binomPrefix n c ↔ w.card < c`. -/
lemma rank_lt_binomPrefix_iff {n c : ℕ} (w : Cube n) :
    rank w < binomPrefix n c ↔ w.card < c := by
  have h := lowCard_eq_initSeg n c
  have hmem : w ∈ Finset.univ.filter (fun w : Cube n => w.card < c)
      ↔ w ∈ simplicialInitSeg n (binomPrefix n c) := by rw [h]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, simplicialInitSeg] at hmem
  exact hmem.symm

/-- Layer lower bound on `rank`. -/
lemma binomPrefix_card_le_rank {n : ℕ} (w : Cube n) :
    binomPrefix n w.card ≤ rank w := by
  by_contra hlt
  push Not at hlt
  exact absurd ((rank_lt_binomPrefix_iff w).mp hlt) (lt_irrefl _)

/-- Layer upper bound on `rank`. -/
lemma rank_lt_binomPrefix_card_succ {n : ℕ} (w : Cube n) :
    rank w < binomPrefix n (w.card + 1) := by
  exact (rank_lt_binomPrefix_iff w).mpr (Nat.lt_succ_self _)

/-- `cubeToNat` of any vertex of the `n`-cube is `< 2^n`. -/
lemma cubeToNat_lt {n : ℕ} (u : Cube n) : cubeToNat u < 2 ^ n := by
  exact cubeToNat_lt_two_pow (fun i _ => i.isLt)

/-- `embed1` reflects (and preserves) the strict simplicial order. -/
lemma simplicialLt_embed1_embed1 {n : ℕ} (u w : Cube n) :
    simplicialLt (embed1 u) (embed1 w) ↔ simplicialLt u w := by
  unfold simplicialLt simplicialLe
  rw [embed1_card, embed1_card, embed1_cubeToNat, embed1_cubeToNat]
  omega

/-- Comparing an `embed0` vertex with an `embed1` vertex reduces to cardinalities. -/
lemma simplicialLt_embed0_embed1 {n : ℕ} (u w : Cube n) :
    simplicialLt (embed0 u) (embed1 w) ↔ u.card < w.card + 1 := by
  have h0 := cubeToNat_lt u
  unfold simplicialLt simplicialLe
  rw [embed0_card, embed1_card, embed0_cubeToNat, embed1_cubeToNat]
  omega

/-
Rank decomposition of `embed1`: the upper-slice embedding.
-/
lemma rank_embed1 {n : ℕ} (w : Cube n) :
    rank (embed1 w) = rank w + binomPrefix n (w.card + 1) := by
  classical
  unfold rank
  have h_partition : Finset.univ.filter (fun v : Cube (n + 1) => simplicialLt v (embed1 w)) =
      (Finset.univ.filter (fun u : Cube n => simplicialLt (embed0 u) (embed1 w))).image embed0 ∪
      (Finset.univ.filter (fun u : Cube n => simplicialLt (embed1 u) (embed1 w))).image embed1 := by
    ext v
    simp [Finset.mem_image, Finset.mem_union]
    by_cases hv : Fin.last n ∈ v
    · -- Since `Fin.last n ∈ v`, we can write `v` as `embed1 u` for some `u : Cube n`.
      obtain ⟨u, hu⟩ : ∃ u : Cube n, v = embed1 u := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ v)
        ext i; simp [embed1]
        induction i using Fin.lastCases <;> aesop
      grind
    · -- Since $Fin.last n \notin v$, we can write $v$ as $embed0 u$ for some $u \in Cube n$.
      obtain ⟨u, hu⟩ : ∃ u : Cube n, v = embed0 u := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ v)
        ext i; simp [embed0]
        induction i using Fin.lastCases <;> aesop
      grind
  rw [h_partition, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective, Finset.card_image_of_injective]
    · rw [show (Finset.univ.filter fun u : Cube n => simplicialLt (embed0 u) (embed1 w)) =
          Finset.univ.filter fun u : Cube n => u.card < w.card + 1 from ?_,
        show (Finset.univ.filter fun u : Cube n => simplicialLt (embed1 u) (embed1 w)) =
          Finset.univ.filter fun u : Cube n => simplicialLt u w from ?_]
      · rw [add_comm, card_filter_card_lt]
      · ext u; simp [simplicialLt_embed1_embed1]
      · ext u; simp [simplicialLt_embed0_embed1]
    · intro x y; simp +decide only [embed1]
      intro h; ext i; replace h := Finset.ext_iff.mp h (Fin.castSucc i) ; aesop
    · intro x y; simp +decide only [embed0]
      exact fun h => Finset.image_injective (Fin.castSucc_injective _) h
  · norm_num [Finset.disjoint_left, embed0, embed1]
    intro a ha x hx H; replace H := Finset.ext_iff.mp H (Fin.last n) ; aesop

/-- The upper slice of an initial segment as an explicit filter. -/
lemma slice1_eq_filter {n k : ℕ} :
    slice1 (simplicialInitSeg (n + 1) k)
      = Finset.univ.filter
          (fun w : Cube n => rank w + binomPrefix n (w.card + 1) < k) := by
  ext w
  simp only [slice1, Finset.mem_filter, Finset.mem_univ, true_and, simplicialInitSeg,
    rank_embed1]

/-
The arithmetic heart of the upper-slice count: for a vertex of cardinality `c`
and rank `rho` confined to its layer (`binomPrefix n c ≤ rho < binomPrefix n (c+1)`),
the `embed1`-membership condition is equivalent to `rho < cascadeSlice1Value`.
-/
lemma cascade_pred_iff {n r t c rho : ℕ}
    (ht : t ≤ Nat.choose (n + 1) r)
    (hlo : binomPrefix n c ≤ rho)
    (hhi : rho < binomPrefix n (c + 1)) :
    rho + binomPrefix n (c + 1) < binomPrefix (n + 1) r + t
      ↔ rho < binomPrefix n (r - 1) + min t (choosePred n r) := by
  by_cases hge : r ≤ c
  · constructor <;> intro <;>
      simp_all +decide only [choose_succ_dim, binomPrefix_succ, binomPrefix_pascal]
    · have := binomPrefix_pred_add_choosePred n r
      have := binomPrefix_mono n hge
      have := binomPrefix_mono n (by omega : r + 1 ≤ c + 1)
      norm_num [binomPrefix_succ n r, binomPrefix_succ n c] at *
      omega
    · rcases r with (_ | r) <;> simp_all +decide [binomPrefix_succ, choosePred]
      · linarith [show binomPrefix n 0 = 0 from by rfl]
      · have h_mono : binomPrefix n c ≥ binomPrefix n (r + 1) := by
          exact binomPrefix_mono n (by linarith)
        simp_all +decide [binomPrefix_succ]
        grind
  · rcases Nat.lt_or_ge c (r - 1) with h2 | h2 <;>
      simp_all +decide only [not_le, ge_iff_le, tsub_le_iff_right, add_comm]
    · rw [min_def]
      split_ifs <;> constructor <;> intros <;>
        linarith [binomPrefix_mono n (by omega : c + 1 ≤ r - 1),
          binomPrefix_mono n (by omega : r - 1 ≤ r), binomPrefix_pascal n r,
          binomPrefix_pred_add_choosePred n r, choose_succ_dim n r]
    · cases h2.eq_or_lt <;> first | linarith | simp_all +decide [Nat.choose_succ_succ, add_comm]
      simp_all +decide [binomPrefix_pascal, binomPrefix_succ, choosePred]
      grind

/-- The upper slice cardinality matches the cascade value. -/
lemma slice1_card_eq_cascade {n k r t : ℕ} (h : IsBinomialCascade (n + 1) k r t) :
    (slice1 (simplicialInitSeg (n + 1) k)).card = cascadeSlice1Value n r t := by
  have ht : t ≤ Nat.choose (n + 1) r := h.2.1
  have hkeq : k = binomPrefix (n + 1) r + t := h.2.2.1
  have hset : slice1 (simplicialInitSeg (n + 1) k)
      = simplicialInitSeg n (cascadeSlice1Value n r t) := by
    rw [slice1_eq_filter]
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, simplicialInitSeg]
    rw [hkeq]
    have hlo := binomPrefix_card_le_rank w
    have hhi := rank_lt_binomPrefix_card_succ w
    have hiff := cascade_pred_iff (n := n) (r := r) (t := t)
      (c := w.card) (rho := rank w) ht hlo hhi
    simpa [cascadeSlice1Value] using hiff
  rw [hset, card_simplicialInitSeg, min_eq_left (cascadeSlice1Value_le h)]

/--
The actual Lean slice sizes of the simplicial initial segment match
the components of the cascade split.
-/
lemma slice_card_eq_cascade {n k p q : ℕ} (h : CascadeSplit n k p q) :
    (slice0 (simplicialInitSeg (n + 1) k)).card = p ∧
    (slice1 (simplicialInitSeg (n + 1) k)).card = q := by
  obtain ⟨r, t, hcasc, hp, hq⟩ := h
  have hq' : (slice1 (simplicialInitSeg (n + 1) k)).card = q := by
    rw [slice1_card_eq_cascade hcasc, hq]
  refine ⟨?_, hq'⟩
  have hpq : p + q = k := by rw [hp, hq]; exact cascade_slice_add hcasc
  -- k ≤ 2^(n+1), so the initial segment has cardinality exactly k
  obtain ⟨_, ht, hkeq, _⟩ := hcasc
  have hk_le : k ≤ 2 ^ (n + 1) := by
    have h2 := binomPrefix_le_two_pow (n + 1) (r + 1)
    have h3 := binomPrefix_succ (n + 1) r
    omega
  have hcard : (simplicialInitSeg (n + 1) k).card = k := by
    rw [card_simplicialInitSeg, min_eq_left hk_le]
  have hadd := slice_card_add (simplicialInitSeg (n + 1) k)
  omega

/-- The two components of a cascade split add back to the split mass. -/
lemma cascade_split_add {n k p q : ℕ} (h : CascadeSplit n k p q) : p + q = k := by
  obtain ⟨r, t, hcasc, hp, hq⟩ := h
  rw [hp, hq]
  exact cascade_slice_add hcasc

/-- In a cascade split the lower slice is at least as large as the upper slice. -/
lemma cascade_q_le_p {n k p q : ℕ} (h : CascadeSplit n k p q) : q ≤ p := by
  obtain ⟨r, t, _, hp, hq⟩ := h
  have hadd := binomPrefix_pred_add_choosePred n r
  rw [hp, hq]
  unfold cascadeSlice0Value cascadeSlice1Value
  omega

/-- The strictly-increasing "mass" function `H n x + x` is monotone. -/
lemma H_add_self_mono {n x y : ℕ} (h : x ≤ y) : H n x + x ≤ H n y + y :=
  Nat.add_le_add (H_mono h) h

/-- Comparing an `embed1` vertex with an `embed0` vertex reduces to cardinalities. -/
lemma simplicialLt_embed1_embed0 {n : ℕ} (u w : Cube n) :
    simplicialLt (embed1 u) (embed0 w) ↔ u.card + 1 ≤ w.card := by
  have h0 := cubeToNat_lt w
  unfold simplicialLt simplicialLe
  rw [embed1_card, embed0_card, embed1_cubeToNat, embed0_cubeToNat]
  omega

/-- The empty vertex lies in every nonempty initial segment. -/
lemma empty_mem_initSeg {n k : ℕ} (hk : 1 ≤ k) :
    (∅ : Cube n) ∈ simplicialInitSeg n k := by
  simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and]
  have hb : binomPrefix n 1 = 1 := by simp [binomPrefix_succ, binomPrefix_zero]
  have hr : rank (∅ : Cube n) < 1 := by
    have h := (rank_lt_binomPrefix_iff (n := n) (c := 1) (∅ : Cube n)).mpr (by simp)
    rwa [hb] at h
  omega

/-
Compression property of the canonical split: the lower slice is contained in the
neighborhood of the upper slice, hence `p ≤ H n q` (when the upper slice is nonempty).
-/
lemma cascade_p_le_H_q {n k p q : ℕ} (h : CascadeSplit n k p q) (hq : 1 ≤ q) :
    p ≤ H n q := by
  -- By `slice_card_eq_cascade h`, we know that `slice0 (simplicialInitSeg (n + 1) k).card = p`
  -- and `slice1 (simplicialInitSeg (n + 1) k).card = q`.
  obtain ⟨h_slice0, h_slice1⟩ := slice_card_eq_cascade h
  -- We need to show that
  -- `slice0 (simplicialInitSeg (n + 1) k) ⊆ neighborhood 1 (slice1 (simplicialInitSeg (n + 1) k))`.
  have h_subset : slice0 (simplicialInitSeg (n + 1) k) ⊆
      neighborhood 1 (slice1 (simplicialInitSeg (n + 1) k)) := by
    intro x hx; by_cases hx' : x = ∅ <;> simp_all +decide only [mem_neighborhood_iff]
    · exact ⟨_, empty_mem_initSeg (by linarith) |> fun h => slice1_initSeg_eq ▸ h,
        by simp +decide [hDist]⟩
    · refine ⟨ gShift x, ?_, ?_ ⟩ <;>
        simp_all +decide only [slice0, slice1, Finset.mem_filter, Finset.mem_univ, true_and]
      · -- Since $x \neq \emptyset$, we have
        -- $gShift x \in \text{slice1} (\text{simplicialInitSeg} (n + 1) k)$.
        have h_gShift_mem : simplicialLt (embed1 (gShift x)) (embed0 x) := by
          rw [simplicialLt_embed1_embed0]
          rw [card_gShift]
          exact Nat.succ_le_of_lt
            (Nat.sub_lt (Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hx')) zero_lt_one)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_lt_of_le (rank_strictMono h_gShift_mem) (Finset.mem_filter.mp hx |>.2.le)⟩
      · exact hDist_gShift_le x
  have h_card_subset : (neighborhood 1 (slice1 (simplicialInitSeg (n + 1) k))).card ≤ H n q := by
    rw [slice1_initSeg_eq, h_slice1]
    rfl
  exact h_slice0 ▸ le_trans (Finset.card_le_card h_subset) h_card_subset

/-- `gShift` on the 0-slice commutes with the embedding. -/
lemma gShift_embed0 {n : ℕ} (v : Cube n) :
    gShift (embed0 v) = embed0 (gShift v) := by
  unfold gShift
  by_cases h : v.Nonempty
  · have h0 : (embed0 v).Nonempty := by unfold embed0; simp [h]
    simp only [h, h0, dif_pos]
    have hmin : (embed0 v).min' h0 = Fin.castSucc (v.min' h) := by
      apply le_antisymm
      · apply Finset.min'_le
        unfold embed0
        exact Finset.mem_image_of_mem _ (Finset.min'_mem _ _)
      · apply Finset.le_min'
        intro y hy
        unfold embed0 at hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
        have : v.min' h ≤ x := Finset.min'_le _ _ hx
        exact Fin.castSucc_le_castSucc_iff.mpr this
    have herase : (embed0 v).erase (Fin.castSucc (v.min' h)) = embed0 (v.erase (v.min' h)) := by
      unfold embed0
      ext x
      simp only [Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨h1, ⟨y, hy, rfl⟩⟩
        use y
        refine ⟨?_, rfl⟩
        refine ⟨?_, hy⟩
        intro heq
        subst heq
        exact h1 rfl
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, ⟨y, hy.2, rfl⟩⟩
        intro heq
        exact hy.1 (Fin.castSucc_inj.mp heq)
    rw [hmin, herase]
  · simp_all [embed0]

/-- `gShift` on the 1-slice stays in the 1-slice, except for `{n}` which maps to `∅`
in the 0-slice. -/
lemma gShift_embed1 {n : ℕ} (v : Cube n) :
    gShift (embed1 v) = if v.Nonempty then embed1 (gShift v) else embed0 ∅ := by
  by_cases h : v.Nonempty
  · have h1 : (embed1 v).Nonempty := by
      unfold embed1
      exact Finset.insert_nonempty _ _
    unfold gShift
    simp only [h, h1, dif_pos, if_pos]
    have hmin : (embed1 v).min' h1 = Fin.castSucc (v.min' h) := by
      apply le_antisymm
      · apply Finset.min'_le
        unfold embed1
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.min'_mem _ _))
      · apply Finset.le_min'
        intro y hy
        unfold embed1 at hy
        rcases Finset.mem_insert.mp hy with (rfl | hy)
        · exact le_of_lt (Fin.castSucc_lt_last _)
        · rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          have : v.min' h ≤ x := Finset.min'_le _ _ hx
          exact Fin.castSucc_le_castSucc_iff.mpr this
    have herase : (embed1 v).erase (Fin.castSucc (v.min' h)) = embed1 (v.erase (v.min' h)) := by
      unfold embed1
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_image]
      constructor
      · rintro ⟨h1, (rfl | ⟨y, hy, rfl⟩)⟩
        · exact Or.inl rfl
        · right
          use y
          refine ⟨⟨?_, hy⟩, rfl⟩
          intro heq
          subst heq
          exact h1 rfl
      · rintro (rfl | ⟨y, hy, rfl⟩)
        · refine ⟨?_, Or.inl rfl⟩
          intro heq
          have : (Fin.castSucc (v.min' h) : ℕ) < (Fin.last n : ℕ) := by
            have := Fin.castSucc_lt_last (v.min' h)
            exact this
          have heq_nat : (Fin.castSucc (v.min' h) : ℕ) = (Fin.last n : ℕ) := by rw [heq]
          linarith
        · refine ⟨?_, Or.inr ⟨y, hy.2, rfl⟩⟩
          intro heq
          exact hy.1 (Fin.castSucc_inj.mp heq)
    rw [hmin, herase]
  · simp_all [embed1, embed0, gShift]

/-- Explicit boundary count: `H n k` counts vertices whose `gShift` lands in the segment. -/
lemma H_eq_gShift_count (n k : ℕ) :
    H n k = (Finset.univ.filter (fun v : Cube n => rank (gShift v) < k)).card := by
  unfold H
  congr 1
  ext v
  rw [mem_neighborhood_initSeg_iff]
  simp

/-- Recursion for `H` in terms of the canonical cascade split. -/
lemma H_succ_cascade {n k p q : ℕ} (h : CascadeSplit n k p q) :
    H (n + 1) k = max (H n p) q + max (H n q) p := by
  obtain ⟨h0, h1⟩ := slice_card_eq_cascade h
  rw [H_succ_slice, h0, h1]

/-- The canonical cascade split of the singleton initial segment is `(1, 0)`. -/
lemma cascadeSplit_one (n : ℕ) : CascadeSplit n 1 1 0 := by
  refine ⟨1, 0, ⟨by omega, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [Nat.choose]
  · simp [binomPrefix, Nat.choose]
  · exact Or.inl (by simp [Nat.choose])
  · simp [cascadeSlice0Value, binomPrefix, choosePred]
  · simp [cascadeSlice1Value, binomPrefix, choosePred]

/-- The boundary of the singleton initial segment: `H n 1 = n + 1`. -/
lemma H_one (n : ℕ) : H n 1 = n + 1 := by
  induction n with
  | zero =>
      have h1 : 1 ≤ H 0 1 := H_ge_self 0 1 (by norm_num)
      have h2 : H 0 1 ≤ 2 ^ 0 := H_le_cube 0 1
      omega
  | succ n ih =>
      rw [H_succ_cascade (cascadeSplit_one n), H_zero, ih]
      simp

/-
For a nonempty vertex `w` of the `n`-cube, its simplicial rank and its smallest
active coordinate together are at least `n`.

This is the combinatorial heart of the lower bound on `H`-increments below:
the smaller the rank of `w`, the larger its minimal coordinate must be.  It is
verified computationally for all `n ≤ 5`, and is non-circular (it depends only on
the simplicial order `rank`, not on `H` or any later result).
-/
lemma rank_add_min_ge {n : ℕ} (w : Cube n) (h : w.Nonempty) :
    n ≤ rank w + (w.min' h : ℕ) := by
  classical
  -- By definition of $f$, we know that for any $c$ in the set
  -- $\{c : Fin n \mid (w.min' h : ℕ) \leq c\}$, $f(c)$ is in the set $\{y \mid simplicialLt y w\}$.
  have h_f_image : Finset.image
      (fun c => if c ∈ w then w.erase c else insert c (w.erase (w.min' h)))
      (Finset.filter (fun c => (w.min' h : ℕ) ≤ c) Finset.univ) ⊆
      Finset.univ.filter (fun y => simplicialLt y w) := by
    intro
    simp +zetaDelta only [Fin.val_fin_le, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, forall_exists_index, and_imp] at *
    rintro x hx rfl; split_ifs <;> simp_all +decide only [simplicialLt]
    · simp +decide [simplicialLe, *]
      grind +qlia
    · constructor <;>
        simp_all +decide only [simplicialLe, Finset.mem_erase, ne_eq, and_false,
          not_false_eq_true, Finset.card_insert_of_notMem, Order.lt_add_one_iff, not_or, not_le,
          not_and]
      · refine Or.inr ⟨ ?_, ?_ ⟩
        · rw [Finset.card_erase_add_one (Finset.min'_mem _ h)]
        · rw [cubeToNat, cubeToNat]
          rw [← Finset.sum_erase_add _ _ (Finset.min'_mem _ h), add_comm]
          rw [Finset.sum_insert] <;> norm_num
          · exact pow_le_pow_right₀ (by decide) hx
          · tauto
      · constructor
        · exact Finset.card_lt_card (Finset.erase_ssubset (Finset.min'_mem _ h) )
        · intro h_card
          have h_cubeToNat : cubeToNat w = cubeToNat (w.erase (w.min' h)) + 2 ^ (w.min' h : ℕ) := by
            exact cubeToNat_erase (Finset.min'_mem _ h)
          have h_cubeToNat_insert : cubeToNat (insert x (w.erase (w.min' h))) =
              cubeToNat (w.erase (w.min' h)) + 2 ^ (x : ℕ) := by
            unfold cubeToNat; simp +decide [*, Finset.sum_insert]
            ring
          cases lt_or_eq_of_le hx <;> simp_all +decide [pow_lt_pow_iff_right₀]
  have h_f_card : Finset.card (Finset.image
      (fun c => if c ∈ w then w.erase c else insert c (w.erase (w.min' h)))
      (Finset.filter (fun c => (w.min' h : ℕ) ≤ c) Finset.univ)) ≥ n - (w.min' h : ℕ) := by
    rw [Finset.card_image_of_injOn]
    · simp_all +decide [Finset.filter_le_eq_Ici]
    · intro x hx y hy; simp_all +decide only [Fin.val_fin_le, Finset.coe_filter,
        Finset.mem_univ, true_and, Set.mem_ofPred_eq, Finset.ext_iff]
      intro h; have := h x; have := h y
      split_ifs at * <;> simp_all +decide [Finset.mem_erase, Finset.mem_insert]
      grind
  have := Finset.card_le_card h_f_image; simp_all +decide [rank]
  grind

/-
Lower bound on the discrete increment of the boundary function `H`: passing from
an initial segment of size `p` to one of size `p + 1` enlarges the closed
neighbourhood by at least `n - p` (stated additively to avoid truncated
subtraction).

Proof idea: `H n (p+1) = H n p + |gShift⁻¹(w)|` where `w` is the unique rank-`p`
vertex (via `H_eq_gShift_count`); and `gShift⁻¹(w)` contains the `n - p`
vertices `w ∪ {j}` for `j` below `w.min'` (which number at least `n - p` by
`rank_add_min_ge`), since `gShift (w ∪ {j}) = w` whenever `j < w.min'`.  This is
the first explicit piece of `H`-increment infrastructure addressing the
Macaulay/cascade-layer obstruction; it is non-circular (it uses only `rank`,
`gShift`, and `H_eq_gShift_count`).
-/
/--
The exact increment of `H`: passing from an initial segment of size `p` to `p + 1`
enlarges the closed neighbourhood by exactly the number of vertices whose `gShift`
is the unique rank-`p` vertex `w`.

This provides the exact layer-profile increment structure for `H`, upgrading the
lower bound in `H_increment_lower` to a full structural equality.
-/
lemma H_increment_eq_gShift_inv (n p : ℕ) (w : Cube n) (hw : rank w = p) :
    H n (p + 1) =
      H n p + (Finset.filter (fun v => gShift v = w) (Finset.univ : Finset (Cube n))).card := by
  rw [H_eq_gShift_count n (p + 1), H_eq_gShift_count n p]
  have h_split : Finset.filter (fun v : Cube n => rank (gShift v) < p + 1) Finset.univ =
      Finset.filter (fun v : Cube n => rank (gShift v) < p) Finset.univ ∪
      Finset.filter (fun v : Cube n => rank (gShift v) = p) Finset.univ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  rw [h_split]
  have h_disjoint : Disjoint (Finset.filter (fun v : Cube n => rank (gShift v) < p) Finset.univ)
      (Finset.filter (fun v : Cube n => rank (gShift v) = p) Finset.univ) := by
    rw [Finset.disjoint_filter]
    simp only [Finset.mem_univ, true_implies]
    intro v
    omega
  rw [Finset.card_union_of_disjoint h_disjoint]
  congr 1
  apply congr_arg
  apply Finset.filter_congr
  intro v _
  constructor
  · intro h
    have hr : rank (gShift v) = rank w := by rw [h, hw]
    exact rank_injective hr
  · intro h
    rw [h, hw]

lemma H_increment_lower (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    H n p + n ≤ H n (p + 1) + p := by
  obtain ⟨w, hw⟩ : ∃ w : Cube n, rank w = p := by
    have := rank_image_eq (n := n)
    exact Finset.mem_image.mp (this.symm ▸ Finset.mem_range.mpr (Nat.lt_of_succ_le hp)) |>
      Exists.imp fun x hx => hx.2
  -- Consider two cases: `w` is nonempty or `w` is empty.
  by_cases hw_nonempty : w.Nonempty
  · -- If `w` is nonempty, then `gShift⁻¹(w)` contains the `n - p` vertices
    -- `w ∪ {j}` for `j` below `w.min'`.
    have h_inv_w :
        Finset.card (Finset.filter (fun v => gShift v = w)
          (Finset.univ : Finset (Cube n))) ≥ n - p := by
      have h_inv_w : Finset.card (Finset.image (fun j => insert j w)
          (Finset.filter (fun j => (j : ℕ) < w.min' hw_nonempty)
            (Finset.univ : Finset (Fin n)))) ≥ n - p := by
        rw [Finset.card_image_of_injOn]
        · have := rank_add_min_ge w hw_nonempty
          simp_all only [Order.add_one_le_iff, Fin.val_fin_lt, Finset.lt_min'_iff, ge_iff_le,
            tsub_le_iff_right]
          rw [show Finset.filter (fun j => ∀ y ∈ w, j < y) Finset.univ =
              Finset.Iio (Finset.min' w hw_nonempty) from ?_]
          · simp +arith +decide at *; linarith
          · ext; simp [Finset.mem_Iio]
        · intro x hx y hy; simp_all +decide [Fin.ext_iff, Finset.ext_iff]
          grind +extAll
      refine le_trans h_inv_w <| Finset.card_le_card ?_
      intro v hv
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_fin_lt] at hv
      obtain ⟨a, ha, rfl⟩ := hv
      have ha_lt : ∀ y ∈ w, a < y := fun y hy => lt_of_lt_of_le ha (Finset.min'_le w y hy)
      have ha_notMem : a ∉ w := fun h => absurd (ha_lt a h) (lt_irrefl a)
      have hmin : (insert a w).min' (Finset.insert_nonempty a w) = a :=
        le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self a w))
          (Finset.le_min' _ _ _ fun y hy =>
            (Finset.mem_insert.mp hy).elim ge_of_eq fun hy => (ha_lt y hy).le)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      unfold gShift
      rw [dif_pos (Finset.insert_nonempty a w), hmin, Finset.erase_insert ha_notMem]
    -- Since `gShift⁻¹(w)` is a subset of `filter (rank (gShift ·) = p)`, we have
    -- `H n (p + 1) ≥ H n p + |gShift⁻¹(w)|`.
    have h_filter :
        Finset.card (Finset.filter (fun v => rank (gShift v) < p + 1)
            (Finset.univ : Finset (Cube n))) ≥
          Finset.card (Finset.filter (fun v => rank (gShift v) < p)
              (Finset.univ : Finset (Cube n))) +
            Finset.card (Finset.filter (fun v => gShift v = w)
              (Finset.univ : Finset (Cube n))) := by
      rw [← Finset.card_union_of_disjoint]
      · refine Finset.card_le_card ?_
        grind
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop
    rw [H_eq_gShift_count, H_eq_gShift_count]
    omega
  · -- Since `w` is empty, we have `p = 0`.
    have hp_zero : p = 0 := by
      rw [← hw, show w = ∅ by aesop]; simp +decide [rank]
      simp +decide only [simplicialLt, not_and, not_not]
      simp +decide [simplicialLe]
    simp_all +decide only [zero_add, Finset.not_nonempty_iff_eq_empty, H_one, add_zero, ge_iff_le]
    rw [H_zero]; linarith

end BooleanIsoperimetry
