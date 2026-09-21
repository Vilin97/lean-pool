/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Tactic

/-!
# PdtPisotLadder — the general Pisot ladder

The general Pisot ladder — the analytic half of Salem's construction;
Salem-ness of the roots is NOT proved here (that is `PdtSalemArith`).

For a real polynomial `P = (X − C α)·G` with `α > 1` and `G > 0` on
`[1, ∞)` (so `α` is the unique root of `P` in `[1, ∞)`), and a
companion polynomial `Q`, the family `R_m = X^m·P + Q` is studied on
`[c, α]` and `[α, ∞)`:

* **the ladder** (`pisot_ladder_family`): if `1 < c < α` and `Q > 0`
  on `[c, α]`, then for `m` large the family `R_m` has a canonical
  root `lam m ∈ (c, α)`, the largest root below `α`; the sequence is
  strictly increasing in `m`; and it tends to `α`;
* **eventual positivity above `α`** (`pisot_ladder_pos_eventually`):
  if moreover `P` is monic, `Q(α) > 0` and `natDegree Q ≤ natDegree P`,
  then for `m` large `R_m > 0` on all of `[α, ∞)` — uniformly in `x`.
  (`Q` may be negative somewhere above `α`, so the positivity is
  genuinely eventual in `m`.)

The proof skeleton: the scalar recurrence
`R_{m+1}(y) = y·R_m(y) + (1 − y)·Q(y)`, the endpoint identity
`R_m(α) = Q(α)`, base negativity by power blow-up, sSup root
canonicity, the one-line monotone step, and the order-topology limit —
plus the uniform tail bound for the second theorem (a coefficient-sum
growth bound for `Q` against a positive lower bound for `P` on
`[s, ∞)`).

Remark: in `pisot_ladder_family` the hypothesis `halpha : 1 < alpha`
is mathematically redundant (it follows from `hc : 1 < c` and
`hca : c < alpha`); it is kept for interface symmetry with
`pisot_ladder_pos_eventually`, where it is essential.
-/

namespace PDT
namespace PisotLadder

noncomputable section
open Filter Set Polynomial

/-! ### Eval basics — the family at scalar level -/

lemma eval_family (P Q : Polynomial ℝ) (m : ℕ) (x : ℝ) :
    (X ^ m * P + Q).eval x = x ^ m * P.eval x + Q.eval x := by
  simp [eval_add, eval_mul, eval_pow, eval_X]

/-- The scalar recurrence `R_{m+1}(y) = y·R_m(y) + (1 − y)·Q(y)`. -/
lemma family_rec (P Q : Polynomial ℝ) (m : ℕ) (y : ℝ) :
    (X ^ (m + 1) * P + Q).eval y
      = y * ((X ^ m * P + Q).eval y) + (1 - y) * Q.eval y := by
  simp only [eval_family]
  ring

/-! ### Sign facts from the factorization `P = (X − C α)·G` -/

lemma eval_P_eq (P G : Polynomial ℝ) (alpha : ℝ)
    (hfac : P = (X - C alpha) * G) (x : ℝ) :
    P.eval x = (x - alpha) * G.eval x := by
  rw [hfac]
  simp [eval_mul, eval_sub, eval_X, eval_C]

lemma eval_P_alpha (P G : Polynomial ℝ) (alpha : ℝ)
    (hfac : P = (X - C alpha) * G) :
    P.eval alpha = 0 := by
  rw [eval_P_eq P G alpha hfac]
  ring

/-- Below `α` (and at least 1), `P` is strictly negative. -/
lemma eval_P_neg (P G : Polynomial ℝ) (alpha : ℝ)
    (hfac : P = (X - C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    {x : ℝ} (hx1 : 1 ≤ x) (hxa : x < alpha) :
    P.eval x < 0 := by
  rw [eval_P_eq P G alpha hfac]
  exact mul_neg_of_neg_of_pos (by linarith) (hG x hx1)

/-- The endpoint identity: `R_m(α) = Q(α)` for every `m`. -/
lemma family_at_alpha (P G Q : Polynomial ℝ) (alpha : ℝ)
    (hfac : P = (X - C alpha) * G) (m : ℕ) :
    (X ^ m * P + Q).eval alpha = Q.eval alpha := by
  rw [eval_family, eval_P_alpha P G alpha hfac, mul_zero, zero_add]

lemma family_at_alpha_pos (P G Q : Polynomial ℝ) (alpha : ℝ)
    (hfac : P = (X - C alpha) * G) (hQa : 0 < Q.eval alpha) (m : ℕ) :
    0 < (X ^ m * P + Q).eval alpha := by
  rw [family_at_alpha P G Q alpha hfac m]
  exact hQa

/-! ### Base negativity below `α`, for `m` large (power blow-up) -/

/-- At any point `t ∈ (1, α)` the family is eventually negative in `m`:
`t^m·P(t)` blows down past the fixed value `Q(t)`. -/
lemma exists_eval_neg (P G Q : Polynomial ℝ) (alpha t : ℝ)
    (ht1 : 1 < t) (hta : t < alpha)
    (hfac : P = (X - C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x) :
    ∃ M0 : ℕ, ∀ m, M0 ≤ m → (X ^ m * P + Q).eval t < 0 := by
  have hPt : P.eval t < 0 := eval_P_neg P G alpha hfac hG (le_of_lt ht1) hta
  have hA : 0 < -P.eval t := by linarith
  have hblow : Tendsto (fun m : ℕ => t ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt ht1
  have hev := hblow.eventually_gt_atTop (Q.eval t / (-P.eval t))
  rw [eventually_atTop] at hev
  obtain ⟨M0, hM0⟩ := hev
  refine ⟨M0, fun m hm => ?_⟩
  rw [eval_family]
  have key : Q.eval t < t ^ m * (-P.eval t) := (div_lt_iff₀ hA).mp (hM0 m hm)
  nlinarith [key]

/-! ### The canonical root — `sSup` of the root set in `[c, α]` -/

/-- The roots of `R_m` in `[c, α]`. -/
def rootSet (P Q : Polynomial ℝ) (alpha c : ℝ) (m : ℕ) : Set ℝ :=
  {x | x ∈ Icc c alpha ∧ (X ^ m * P + Q).eval x = 0}

/-- The canonical root: the largest root of `R_m` in `[c, α]`. -/
def lam (P Q : Polynomial ℝ) (alpha c : ℝ) (m : ℕ) : ℝ :=
  sSup (rootSet P Q alpha c m)

lemma rootSet_isCompact (P Q : Polynomial ℝ) (alpha c : ℝ) (m : ℕ) :
    IsCompact (rootSet P Q alpha c m) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := c) (b := alpha))
  · have hrw : rootSet P Q alpha c m
        = Icc c alpha ∩ (fun x : ℝ => (X ^ m * P + Q).eval x) ⁻¹' {0} := rfl
    rw [hrw]
    exact isClosed_Icc.inter
      (isClosed_singleton.preimage (Polynomial.continuous _))
  · intro x hx
    exact hx.1

lemma rootSet_nonempty (P Q : Polynomial ℝ) (alpha c : ℝ)
    (hca : c ≤ alpha) (m : ℕ)
    (hbase : (X ^ m * P + Q).eval c < 0)
    (hpos : 0 < (X ^ m * P + Q).eval alpha) :
    (rootSet P Q alpha c m).Nonempty := by
  have hcont : Continuous fun x : ℝ => (X ^ m * P + Q).eval x :=
    Polynomial.continuous _
  have hsub := intermediate_value_Icc hca hcont.continuousOn
  have h0 : (0 : ℝ) ∈ Icc ((X ^ m * P + Q).eval c) ((X ^ m * P + Q).eval alpha) :=
    ⟨le_of_lt hbase, le_of_lt hpos⟩
  obtain ⟨x, hx, hfx⟩ := hsub h0
  exact ⟨x, hx, hfx⟩

lemma lam_mem (P Q : Polynomial ℝ) (alpha c : ℝ) (m : ℕ)
    (hne : (rootSet P Q alpha c m).Nonempty) :
    lam P Q alpha c m ∈ rootSet P Q alpha c m :=
  (rootSet_isCompact P Q alpha c m).sSup_mem hne

lemma lam_gt_c (P Q : Polynomial ℝ) (alpha c : ℝ) (m : ℕ)
    (hne : (rootSet P Q alpha c m).Nonempty)
    (hbase : (X ^ m * P + Q).eval c < 0) :
    c < lam P Q alpha c m := by
  have hmem := lam_mem P Q alpha c m hne
  rcases eq_or_lt_of_le hmem.1.1 with h | h
  · exfalso
    rw [h, hmem.2] at hbase
    exact lt_irrefl 0 hbase
  · exact h

lemma lam_lt_alpha (P Q : Polynomial ℝ) (alpha c : ℝ) (m : ℕ)
    (hne : (rootSet P Q alpha c m).Nonempty)
    (hpos : 0 < (X ^ m * P + Q).eval alpha) :
    lam P Q alpha c m < alpha := by
  have hmem := lam_mem P Q alpha c m hne
  rcases eq_or_lt_of_le hmem.1.2 with h | h
  · exfalso
    rw [← h, hmem.2] at hpos
    exact lt_irrefl 0 hpos
  · exact h

/-- Maximality: no roots of `R_m` strictly between `lam m` and `α`. -/
lemma lam_max (P Q : Polynomial ℝ) (alpha c : ℝ) (m : ℕ)
    (hne : (rootSet P Q alpha c m).Nonempty)
    {y : ℝ} (h1 : lam P Q alpha c m < y) (h2 : y < alpha) :
    (X ^ m * P + Q).eval y ≠ 0 := by
  intro hy
  have hmem := lam_mem P Q alpha c m hne
  have hymem : y ∈ rootSet P Q alpha c m :=
    ⟨⟨le_trans hmem.1.1 (le_of_lt h1), le_of_lt h2⟩, hy⟩
  exact absurd (le_csSup (rootSet_isCompact P Q alpha c m).bddAbove hymem)
    (not_le.mpr h1)

/-! ### Strict monotonicity -/

/-- The heart: at a root of `R_m`, the next member is negative —
`R_{m+1}(y) = (1 − y)·Q(y) < 0` when `y > 1` and `Q(y) > 0`. -/
lemma family_succ_at_root (P Q : Polynomial ℝ) (m : ℕ) {y : ℝ}
    (h1 : 1 < y) (hQy : 0 < Q.eval y)
    (hy : (X ^ m * P + Q).eval y = 0) :
    (X ^ (m + 1) * P + Q).eval y < 0 := by
  rw [family_rec P Q m y, hy, mul_zero, zero_add]
  nlinarith [mul_pos (sub_pos.mpr h1) hQy]

lemma lam_strictMono (P G Q : Polynomial ℝ) (alpha c : ℝ)
    (hc : 1 < c) (hca : c < alpha)
    (hfac : P = (X - C alpha) * G)
    (hQ : ∀ x : ℝ, c ≤ x → x ≤ alpha → 0 < Q.eval x)
    (m : ℕ) (hbase : (X ^ m * P + Q).eval c < 0) :
    lam P Q alpha c m < lam P Q alpha c (m + 1) := by
  have hQa : 0 < Q.eval alpha := hQ alpha (le_of_lt hca) le_rfl
  have hne : (rootSet P Q alpha c m).Nonempty :=
    rootSet_nonempty P Q alpha c (le_of_lt hca) m hbase
      (family_at_alpha_pos P G Q alpha hfac hQa m)
  have hmem := lam_mem P Q alpha c m hne
  have hgec : c ≤ lam P Q alpha c m := hmem.1.1
  have hlea : lam P Q alpha c m ≤ alpha := hmem.1.2
  have h1 : 1 < lam P Q alpha c m := lt_of_lt_of_le hc hgec
  have hneg : (X ^ (m + 1) * P + Q).eval (lam P Q alpha c m) < 0 :=
    family_succ_at_root P Q m h1 (hQ _ hgec hlea) hmem.2
  have hcont : Continuous fun x : ℝ => (X ^ (m + 1) * P + Q).eval x :=
    Polynomial.continuous _
  have hsub := intermediate_value_Icc hlea hcont.continuousOn
  have h0 : (0 : ℝ) ∈ Icc ((X ^ (m + 1) * P + Q).eval (lam P Q alpha c m))
      ((X ^ (m + 1) * P + Q).eval alpha) :=
    ⟨le_of_lt hneg, le_of_lt (family_at_alpha_pos P G Q alpha hfac hQa (m + 1))⟩
  obtain ⟨y, hy, hfy⟩ := hsub h0
  have hyne : lam P Q alpha c m ≠ y := by
    intro h
    rw [← h] at hfy
    linarith
  have hylt : lam P Q alpha c m < y := lt_of_le_of_ne hy.1 hyne
  have hymem : y ∈ rootSet P Q alpha c (m + 1) :=
    ⟨⟨le_trans hgec (le_of_lt hylt), hy.2⟩, hfy⟩
  exact lt_of_lt_of_le hylt
    (le_csSup (rootSet_isCompact P Q alpha c (m + 1)).bddAbove hymem)

/-! ### The limit -/

/-- The canonical roots tend to `α`: below any `y < α` the base
negativity plus the intermediate value theorem plants a root above `y`
eventually, and `lam m < α` always (for `m` past the base index). -/
lemma lam_tendsto (P G Q : Polynomial ℝ) (alpha c : ℝ)
    (hc : 1 < c) (hca : c < alpha)
    (hfac : P = (X - C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hQ : ∀ x : ℝ, c ≤ x → x ≤ alpha → 0 < Q.eval x) :
    Tendsto (fun m => lam P Q alpha c m) atTop (nhds alpha) := by
  have hQa : 0 < Q.eval alpha := hQ alpha (le_of_lt hca) le_rfl
  obtain ⟨M0, hM0⟩ := exists_eval_neg P G Q alpha c hc hca hfac hG
  rw [tendsto_order]
  constructor
  · intro y hy
    rcases le_or_gt y c with hyc | hcy
    · filter_upwards [eventually_ge_atTop M0] with m hm
      have hbase := hM0 m hm
      have hne : (rootSet P Q alpha c m).Nonempty :=
        rootSet_nonempty P Q alpha c (le_of_lt hca) m hbase
          (family_at_alpha_pos P G Q alpha hfac hQa m)
      exact lt_of_le_of_lt hyc (lam_gt_c P Q alpha c m hne hbase)
    · obtain ⟨M1, hM1⟩ :=
        exists_eval_neg P G Q alpha y (lt_trans hc hcy) hy hfac hG
      filter_upwards [eventually_ge_atTop M1] with m hm1
      have hyneg := hM1 m hm1
      have hcont : Continuous fun x : ℝ => (X ^ m * P + Q).eval x :=
        Polynomial.continuous _
      have hsub := intermediate_value_Icc (le_of_lt hy) hcont.continuousOn
      have h0 : (0 : ℝ) ∈ Icc ((X ^ m * P + Q).eval y) ((X ^ m * P + Q).eval alpha) :=
        ⟨le_of_lt hyneg, le_of_lt (family_at_alpha_pos P G Q alpha hfac hQa m)⟩
      obtain ⟨z, hz, hfz⟩ := hsub h0
      have hzne : y ≠ z := by
        intro h
        rw [← h] at hfz
        linarith
      have hyz : y < z := lt_of_le_of_ne hz.1 hzne
      have hzmem : z ∈ rootSet P Q alpha c m :=
        ⟨⟨le_of_lt (lt_trans hcy hyz), hz.2⟩, hfz⟩
      exact lt_of_lt_of_le hyz
        (le_csSup (rootSet_isCompact P Q alpha c m).bddAbove hzmem)
  · intro y hy
    filter_upwards [eventually_ge_atTop M0] with m hm
    have hbase := hM0 m hm
    have hne : (rootSet P Q alpha c m).Nonempty :=
      rootSet_nonempty P Q alpha c (le_of_lt hca) m hbase
        (family_at_alpha_pos P G Q alpha hfac hQa m)
    exact lt_trans (lam_lt_alpha P Q alpha c m hne
      (family_at_alpha_pos P G Q alpha hfac hQa m)) hy

/-! ### The first theorem: the general Pisot ladder -/

/-- **The general Pisot ladder.** For `P = (X − C α)·G` with
`G > 0` on `[1, ∞)`, and `Q > 0` on `[c, α]` with `1 < c < α`: for `m`
large the family `R_m = X^m·P + Q` has a canonical root
`lam m ∈ (c, α)`, the largest root below `α`; the sequence is strictly
increasing; and it tends to `α`.

`halpha` is derivable from `hc` and `hca` (see the module docstring);
the hypothesis is retained for interface symmetry with the other ladder result. -/
theorem pisot_ladder_family
    (P G Q : Polynomial ℝ) (alpha c : ℝ)
    (_halpha : 1 < alpha) (hc : 1 < c) (hca : c < alpha)
    (hfac : P = (X - C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hQ : ∀ x : ℝ, c ≤ x → x ≤ alpha → 0 < Q.eval x) :
    ∃ M : ℕ, ∃ lam : ℕ → ℝ,
      (∀ m, M ≤ m →
        (c < lam m ∧ lam m < alpha) ∧
        (X ^ m * P + Q).eval (lam m) = 0 ∧
        (∀ y, lam m < y → y < alpha → (X ^ m * P + Q).eval y ≠ 0) ∧
        lam m < lam (m + 1)) ∧
      Tendsto lam atTop (nhds alpha) := by
  have hQa : 0 < Q.eval alpha := hQ alpha (le_of_lt hca) le_rfl
  obtain ⟨M0, hM0⟩ := exists_eval_neg P G Q alpha c hc hca hfac hG
  refine ⟨M0, fun m => lam P Q alpha c m, fun m hm => ?_,
    lam_tendsto P G Q alpha c hc hca hfac hG hQ⟩
  have hbase := hM0 m hm
  have hpos := family_at_alpha_pos P G Q alpha hfac hQa m
  have hne : (rootSet P Q alpha c m).Nonempty :=
    rootSet_nonempty P Q alpha c (le_of_lt hca) m hbase hpos
  exact ⟨⟨lam_gt_c P Q alpha c m hne hbase, lam_lt_alpha P Q alpha c m hne hpos⟩,
    (lam_mem P Q alpha c m hne).2,
    fun y h1 h2 => lam_max P Q alpha c m hne h1 h2,
    lam_strictMono P G Q alpha c hc hca hfac hQ m hbase⟩

/-! ### Eventual uniform positivity on `[α, ∞)` -/

/-- The `δ`-window: `Q(α) > 0` extends to a closed window
`[α, s]` with `α < s` by continuity. -/
lemma exists_window (Q : Polynomial ℝ) (alpha : ℝ) (hQa : 0 < Q.eval alpha) :
    ∃ s : ℝ, alpha < s ∧ ∀ x ∈ Icc alpha s, 0 < Q.eval x := by
  have hopen : IsOpen {x : ℝ | 0 < Q.eval x} :=
    isOpen_lt continuous_const (Polynomial.continuous Q)
  have hmem : alpha ∈ {x : ℝ | 0 < Q.eval x} := hQa
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen alpha hmem
  refine ⟨alpha + r / 2, by linarith, fun x hx => ?_⟩
  have hxball : x ∈ Metric.ball alpha r := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x - alpha)]
    have h2 := hx.2
    linarith
  exact hball hxball

/-- On the window `[α, s]` every member of the family is positive:
`x^m·P(x) ≥ 0` there and `Q > 0` there. -/
lemma family_pos_on_window (P G Q : Polynomial ℝ) (alpha : ℝ)
    (halpha : 1 < alpha)
    (hfac : P = (X - C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (s : ℝ) (hwin : ∀ x ∈ Icc alpha s, 0 < Q.eval x)
    (m : ℕ) {x : ℝ} (hx : x ∈ Icc alpha s) :
    0 < (X ^ m * P + Q).eval x := by
  rw [eval_family]
  have hxa : alpha ≤ x := hx.1
  have hP : 0 ≤ P.eval x := by
    rw [eval_P_eq P G alpha hfac]
    exact mul_nonneg (by linarith) (le_of_lt (hG x (by linarith)))
  have h1 : 0 ≤ x ^ m * P.eval x :=
    mul_nonneg (pow_nonneg (by linarith) m) hP
  linarith [hwin x hx]

lemma P_natDegree_eq (P G : Polynomial ℝ) (alpha : ℝ)
    (hfac : P = (X - C alpha) * G) (hGne : G ≠ 0) :
    P.natDegree = 1 + G.natDegree := by
  rw [hfac, (monic_X_sub_C alpha).natDegree_mul' hGne, natDegree_X_sub_C]

/-- The uniform positive lower bound for `P` on `[s, ∞)`, `s > α`:
`P → ∞` at infinity, and `P` is continuous and positive on the
compact remainder. -/
lemma exists_eta (P G : Polynomial ℝ) (alpha : ℝ)
    (halpha : 1 < alpha) (hmonic : P.Monic)
    (hfac : P = (X - C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    {s : ℝ} (hs : alpha < s) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ x : ℝ, s ≤ x → eta ≤ P.eval x := by
  have hGne : G ≠ 0 := by
    intro h
    have h1 := hG 1 le_rfl
    rw [h, eval_zero] at h1
    exact lt_irrefl 0 h1
  have hdegpos : 0 < P.degree := by
    rw [← natDegree_pos_iff_degree_pos, P_natDegree_eq P G alpha hfac hGne]
    omega
  have htend : Tendsto (fun x : ℝ => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg hdegpos
      (by rw [hmonic.leadingCoeff]; norm_num)
  have hev := htend.eventually_ge_atTop 1
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  obtain ⟨x0, hx0mem, hx0min⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (le_max_right N s))
      (Polynomial.continuous P).continuousOn
  have hx0pos : 0 < P.eval x0 := by
    rw [eval_P_eq P G alpha hfac]
    exact mul_pos (by linarith [hx0mem.1] : (0 : ℝ) < x0 - alpha)
      (hG x0 (by linarith [hx0mem.1]))
  refine ⟨min 1 (P.eval x0), lt_min one_pos hx0pos, fun x hx => ?_⟩
  rcases le_or_gt x (max N s) with hxN | hxN
  · have hmin := isMinOn_iff.mp hx0min x ⟨hx, hxN⟩
    exact le_trans (min_le_right _ _) hmin
  · have hxge : N ≤ x := le_trans (le_max_left N s) (le_of_lt hxN)
    exact le_trans (min_le_left _ _) (hN x hxge)

/-- The coefficient-sum growth bound: for `x ≥ 1`,
`|Q(x)| ≤ (∑ |coeff|)·x^(natDegree Q)`. -/
lemma abs_eval_le (Q : Polynomial ℝ) (x : ℝ) (hx : 1 ≤ x) :
    |Q.eval x| ≤ (∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|)
      * x ^ Q.natDegree := by
  rw [eval_eq_sum_range]
  calc |∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * x ^ i|
      ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i| * x ^ Q.natDegree := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ x) i)]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hx (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
          (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|) * x ^ Q.natDegree := by
        rw [Finset.sum_mul]

/-! ### The second theorem: eventual uniform positivity above `α` -/

/-- **Eventual uniform positivity on `[α, ∞)`.** For monic
`P = (X − C α)·G` with `G > 0` on `[1, ∞)`, `Q(α) > 0`, and
`natDegree Q ≤ natDegree P`: for `m` large, `R_m = X^m·P + Q` is
strictly positive on all of `[α, ∞)`. Near `α` the window positivity
of `Q` carries every member; past the window the term `x^m·P(x)`
dominates the coefficient-sum bound on `|Q(x)|` once
`m ≥ natDegree P + K` with `s^K·η > ∑|coeff Q|`. -/
theorem pisot_ladder_pos_eventually
    (P G Q : Polynomial ℝ) (alpha : ℝ)
    (halpha : 1 < alpha) (hmonic : P.Monic)
    (hfac : P = (X - C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hQa : 0 < Q.eval alpha)
    (hdeg : Q.natDegree ≤ P.natDegree) :
    ∃ M : ℕ, ∀ m, M ≤ m → ∀ x : ℝ, alpha ≤ x → 0 < (X ^ m * P + Q).eval x := by
  obtain ⟨s, hs_gt, hwin⟩ := exists_window Q alpha hQa
  have hs1 : 1 < s := lt_trans halpha hs_gt
  obtain ⟨eta, heta, hetaP⟩ := exists_eta P G alpha halpha hmonic hfac hG hs_gt
  obtain ⟨CQ, hCQ0, hCQbound⟩ :
      ∃ CQ : ℝ, 0 ≤ CQ ∧ ∀ x : ℝ, 1 ≤ x → |Q.eval x| ≤ CQ * x ^ Q.natDegree :=
    ⟨∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|,
     Finset.sum_nonneg fun i _ => abs_nonneg _,
     fun x hx => abs_eval_le Q x hx⟩
  have hblow : Tendsto (fun k : ℕ => s ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hs1
  obtain ⟨K, hK⟩ := (hblow.eventually_gt_atTop (CQ / eta)).exists
  have hcore : CQ < s ^ K * eta := (div_lt_iff₀ heta).mp hK
  refine ⟨P.natDegree + K, fun m hm x hx => ?_⟩
  rcases le_or_gt x s with hxs | hsx
  · exact family_pos_on_window P G Q alpha halpha hfac hG s hwin m ⟨hx, hxs⟩
  · have hsx' : s ≤ x := le_of_lt hsx
    have hx1 : 1 ≤ x := le_trans (le_of_lt hs1) hsx'
    have hpk : P.natDegree ≤ m := le_trans (Nat.le_add_right _ _) hm
    obtain ⟨k, hk_eq⟩ := Nat.exists_eq_add_of_le hpk
    have hkK : K ≤ k := by omega
    have hpowp : 0 < x ^ P.natDegree := pow_pos (by linarith) _
    have hpowk : 0 < x ^ k := pow_pos (by linarith) _
    have hQb : -(CQ * x ^ P.natDegree) ≤ Q.eval x := by
      have h1 := hCQbound x hx1
      have h2 : x ^ Q.natDegree ≤ x ^ P.natDegree := pow_le_pow_right₀ hx1 hdeg
      have h3 : CQ * x ^ Q.natDegree ≤ CQ * x ^ P.natDegree :=
        mul_le_mul_of_nonneg_left h2 hCQ0
      have h4 := neg_abs_le (Q.eval x)
      linarith
    have hxk : s ^ K ≤ x ^ k :=
      le_trans (pow_le_pow_right₀ (le_of_lt hs1) hkK)
        (pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ s) hsx' k)
    have hPx : eta ≤ P.eval x := hetaP x hsx'
    rw [eval_family, hk_eq, pow_add]
    have step1 : x ^ P.natDegree * (s ^ K * eta)
        ≤ x ^ P.natDegree * (x ^ k * P.eval x) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hpowp)
      calc s ^ K * eta ≤ x ^ k * eta :=
            mul_le_mul_of_nonneg_right hxk (le_of_lt heta)
        _ ≤ x ^ k * P.eval x :=
            mul_le_mul_of_nonneg_left hPx (le_of_lt hpowk)
    have step2 : CQ * x ^ P.natDegree < s ^ K * eta * x ^ P.natDegree :=
      mul_lt_mul_of_pos_right hcore hpowp
    nlinarith [step1, step2, hQb]

end
end PisotLadder
end PDT

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
