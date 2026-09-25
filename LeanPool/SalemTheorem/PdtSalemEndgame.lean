/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module

public import Mathlib.Tactic
public import LeanPool.SalemTheorem.PdtPisotLadder
public import LeanPool.SalemTheorem.PdtSalemCircle
public import LeanPool.SalemTheorem.PdtSalemArith
public import LeanPool.SalemTheorem.PdtSalemMinus

/-!
# PdtSalemEndgame — the two-sided assembly

The two-sided assembly of Salem's construction: for every monic integer polynomial with the
Pisot pattern and `P(1/alpha) ≠ 0` (the nondegeneracy — it fails
exactly when `1/alpha` is a root of `P`, i.e. when `X² − rX + 1`
divides `P`, by the reduction lemma of `PdtSalemQuadUnit`; there the
construction itself degenerates), Salem numbers approach `alpha` from
both sides.  Assembles `PdtPisotLadder` (below-ladder), the
above-ladder, `PdtSalemCircle`/`PdtSalemMinus` (circle counts +
trichotomies through the certificates), and `PdtSalemArith`
(certificates + reverse bridge).

Structure:

* **the bridges** — the cast triangle `ℤ → ℝ → ℂ`, the real/complex
  evaluation transfer, and the reflect-evaluation identity
  `Q(α) = α^p·P(1/α)` that turns the nondegeneracy hypothesis into the
  sign fork of the assembly;
* **the quotient and the windows** — the real quotient `G` with
  `P = (X − C α)·G` and `G > 0` on `[1, ∞)` (nonvanishing by transfer
  to the complex factorization, positivity by blow-up + IVT), plus the
  two one-sided sign windows around `α`;
* **the above-ladder** — `pisot_ladder_above`, the `sInf` mirror
  of `PdtPisotLadder.pisot_ladder_family`: for a companion negative on
  a window `[α, w]`, the family `X^m·P + Q` has a smallest root above
  `α`, strictly decreasing in `m` and tending to `α`;
* **the finiteness discharge** — along any injective ladder tail
  bounded in `(1, B)`, the two integer degeneracies (`τ ∈ ℤ`,
  `τ + 1/τ ∈ ℤ`) fail eventually: the bad set is finite (integer
  branch inside a finite cast interval; trace branch inside finitely
  many quadratic root sets);
* **the assembly** — `salem_two_sided`: the sign of
  `Q(α) = α^p·P(1/α)` routes the PLUS family (`X^m·P + Q`, certificate
  `PdtSalemArith.salem_certificate`) to one side of `α` and the MINUS
  family (`X^m·P − Q`, certificate
  `PdtSalemMinus.salem_certificate_minus`) to the other, and both
  ladders deliver Salem numbers in `(α − ε, α)` and `(α, α + ε)`.

`salem_two_sided` carries the single nondegeneracy hypothesis
`P(1/α) ≠ 0`; the conjugation closure of `inside` is retained as a
hypothesis although it follows from the integer coefficients.
-/

@[expose] public section

namespace PDT
namespace SalemEndgame

noncomputable section
open Filter Set Polynomial

/-- A Salem number: a real algebraic integer `tau > 1` whose other
conjugates all lie in the closed unit disk, at least one ON the unit
circle, with `1/tau` among them. -/
def IsSalem (tau : ℝ) : Prop :=
  1 < tau ∧ IsIntegral ℤ tau ∧
  (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 → z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
  (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
  (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0

/-! ### Cast bridges -/

/-- The ℤ-cast triangle through ℝ: ring homs out of ℤ are unique. -/
lemma map_int_real_complex (W : Polynomial ℤ) :
    (W.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ) = W.map (Int.castRingHom ℂ) := by
  rw [Polynomial.map_map,
    show (algebraMap ℝ ℂ).comp (Int.castRingHom ℝ) = Int.castRingHom ℂ from
      RingHom.ext_int _ _]

/-- Evaluation of a mapped real polynomial at a real point, over ℂ. -/
lemma eval_map_ofReal (W : Polynomial ℝ) (x : ℝ) :
    (W.map (algebraMap ℝ ℂ)).eval ((x : ℂ)) = ((W.eval x : ℝ) : ℂ) := by
  rw [Polynomial.eval_map, show ((x : ℂ)) = algebraMap ℝ ℂ x from rfl,
    Polynomial.eval₂_at_apply]
  rfl

/-- The real-to-complex evaluation transfer for integer polynomials. -/
lemma eval_int_transfer (W : Polynomial ℤ) (x : ℝ) :
    (W.map (Int.castRingHom ℂ)).eval ((x : ℂ))
      = (((W.map (Int.castRingHom ℝ)).eval x : ℝ) : ℂ) := by
  rw [← map_int_real_complex W, eval_map_ofReal]

/-- The reflect-evaluation identity over ℝ:
`(reflect p W)(α) = α^p·W(1/α)` for `α ≠ 0`. -/
lemma reflect_eval_eq (W : Polynomial ℝ) {alpha : ℝ} (ha : alpha ≠ 0) (p : ℕ)
    (hdeg : W.natDegree ≤ p) :
    (W.reflect p).eval alpha = alpha ^ p * W.eval alpha⁻¹ := by
  have hainv : (alpha⁻¹ : ℝ) ≠ 0 := inv_ne_zero ha
  let : Invertible (alpha⁻¹ : ℝ) := invertibleOfNonzero hainv
  have key := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℝ) alpha⁻¹ p W hdeg
  rw [Polynomial.eval₂_id, Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at key
  have hp1 : (alpha⁻¹ : ℝ) ^ p * alpha ^ p = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ ha, one_pow]
  calc (W.reflect p).eval alpha
      = (W.reflect p).eval alpha * ((alpha⁻¹ : ℝ) ^ p * alpha ^ p) := by
        rw [hp1, mul_one]
    _ = ((W.reflect p).eval alpha * (alpha⁻¹ : ℝ) ^ p) * alpha ^ p := by ring
    _ = W.eval alpha⁻¹ * alpha ^ p := by rw [key]
    _ = alpha ^ p * W.eval alpha⁻¹ := by ring

/-! ### The real quotient and the windows -/

/-- Positivity of the quotient on `[1, ∞)`: its complex image is the
product of the inside factors, so it cannot vanish at any real
`x ≥ 1`; a monic polynomial positive at infinity and nonvanishing on
the connected set `[1, ∞)` is positive there. -/
lemma G_pos (G : Polynomial ℝ) (hGmonic : G.Monic)
    (inside : Multiset ℂ) (hin : ∀ r ∈ inside, ‖r‖ < 1)
    (hGmapC : G.map (algebraMap ℝ ℂ) = (inside.map fun r => X - Polynomial.C r).prod) :
    ∀ x : ℝ, 1 ≤ x → 0 < G.eval x := by
  have hne : ∀ x : ℝ, 1 ≤ x → G.eval x ≠ 0 := by
    intro x hx h0
    have h1 : (G.map (algebraMap ℝ ℂ)).eval ((x : ℂ)) = 0 := by
      rw [eval_map_ofReal, h0, Complex.ofReal_zero]
    rw [hGmapC] at h1
    simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
    rw [Multiset.prod_eq_zero_iff] at h1
    obtain ⟨r, hr, hr0⟩ := Multiset.mem_map.mp h1
    have hrx : r = ((x : ℂ)) := (sub_eq_zero.mp hr0).symm
    have hnorm := hin r hr
    rw [hrx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hnorm
    linarith
  intro x hx
  rcases Nat.eq_zero_or_pos G.natDegree with hd0 | hdpos
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hGmonic hd0, Polynomial.eval_one]
    norm_num
  · have hdegpos : 0 < G.degree := Polynomial.natDegree_pos_iff_degree_pos.mp hdpos
    have htend : Tendsto (fun t : ℝ => G.eval t) atTop atTop :=
      G.tendsto_atTop_of_leadingCoeff_nonneg hdegpos
        (by rw [hGmonic.leadingCoeff]; norm_num)
    have hev := htend.eventually_ge_atTop 1
    rw [eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    by_contra hle
    have hxb : x ≤ max N x := le_max_right _ _
    have hGb : 1 ≤ G.eval (max N x) := hN _ (le_max_left _ _)
    have hsub := intermediate_value_Icc hxb (Polynomial.continuous G).continuousOn
    have h0 : (0 : ℝ) ∈ Icc (G.eval x) (G.eval (max N x)) :=
      ⟨not_lt.mp hle, by linarith⟩
    obtain ⟨z, hz, hfz⟩ := hsub h0
    exact hne z (le_trans hx hz.1) hfz

/-- The window below `α`: positivity of `W` at `α` extends to a closed
window `[c, α]` with `1 < c < α`. -/
lemma window_below (W : Polynomial ℝ) {alpha : ℝ} (halpha : 1 < alpha)
    (hWa : 0 < W.eval alpha) :
    ∃ c : ℝ, 1 < c ∧ c < alpha ∧ ∀ x : ℝ, c ≤ x → x ≤ alpha → 0 < W.eval x := by
  have hopen : IsOpen {x : ℝ | 0 < W.eval x} :=
    isOpen_lt continuous_const (Polynomial.continuous W)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen alpha hWa
  refine ⟨max ((1 + alpha) / 2) (alpha - r / 2), ?_, ?_, ?_⟩
  · exact lt_max_iff.mpr (Or.inl (by linarith))
  · exact max_lt (by linarith) (by linarith)
  · intro x hcx hxa
    have hxball : x ∈ Metric.ball alpha r := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_nonpos (by linarith : x - alpha ≤ 0)]
      have h1 : alpha - r / 2 ≤ x := le_trans (le_max_right _ _) hcx
      linarith
    exact hball hxball

/-- The window above `α`: negativity of `W` at `α` extends to a closed
window `[α, w]` with `α < w ≤ α + 1/2`. -/
lemma window_above (W : Polynomial ℝ) (alpha : ℝ) (hWa : W.eval alpha < 0) :
    ∃ w : ℝ, alpha < w ∧ w ≤ alpha + 1 / 2 ∧
      ∀ x : ℝ, alpha ≤ x → x ≤ w → W.eval x < 0 := by
  have hopen : IsOpen {x : ℝ | W.eval x < 0} :=
    isOpen_lt (Polynomial.continuous W) continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen alpha hWa
  have hmin : (0 : ℝ) < min (r / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
  refine ⟨alpha + min (r / 2) (1 / 2), by linarith, ?_, ?_⟩
  · have := min_le_right (r / 2) (1 / 2 : ℝ)
    linarith
  · intro x hax hxw
    have hxball : x ∈ Metric.ball alpha r := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - alpha)]
      have h1 : min (r / 2) (1 / 2 : ℝ) ≤ r / 2 := min_le_left _ _
      linarith
    exact hball hxball

/-! ### The above-ladder — the `sInf` mirror of `PdtPisotLadder` -/

/-- At any point `t > α` (hence `t > 1`) the family is eventually
positive in `m`: `t^m·P(t)` blows up past the fixed value `Q(t)`. -/
lemma exists_eval_pos_above (P G Q : Polynomial ℝ) (alpha t : ℝ)
    (ht1 : 1 < t) (hat : alpha < t)
    (hfac : P = (X - Polynomial.C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x) :
    ∃ M0 : ℕ, ∀ m, M0 ≤ m → 0 < (X ^ m * P + Q).eval t := by
  have hPt : 0 < P.eval t := by
    rw [PisotLadder.eval_P_eq P G alpha hfac]
    exact mul_pos (by linarith) (hG t (by linarith))
  have hblow : Tendsto (fun m : ℕ => t ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt ht1
  have hev := hblow.eventually_gt_atTop ((-Q.eval t) / P.eval t)
  rw [eventually_atTop] at hev
  obtain ⟨M0, hM0⟩ := hev
  refine ⟨M0, fun m hm => ?_⟩
  rw [PisotLadder.eval_family]
  have key : -Q.eval t < t ^ m * P.eval t := (div_lt_iff₀ hPt).mp (hM0 m hm)
  linarith

/-- The roots of `R_m` in `[α, w]`. -/
def rootSetA (P Q : Polynomial ℝ) (alpha w : ℝ) (m : ℕ) : Set ℝ :=
  {x | x ∈ Icc alpha w ∧ (X ^ m * P + Q).eval x = 0}

/-- The canonical root above: the smallest root of `R_m` in `[α, w]`. -/
def muA (P Q : Polynomial ℝ) (alpha w : ℝ) (m : ℕ) : ℝ :=
  sInf (rootSetA P Q alpha w m)

lemma rootSetA_isCompact (P Q : Polynomial ℝ) (alpha w : ℝ) (m : ℕ) :
    IsCompact (rootSetA P Q alpha w m) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := alpha) (b := w))
  · have hrw : rootSetA P Q alpha w m
        = Icc alpha w ∩ (fun x : ℝ => (X ^ m * P + Q).eval x) ⁻¹' {0} := rfl
    rw [hrw]
    exact isClosed_Icc.inter
      (isClosed_singleton.preimage (Polynomial.continuous _))
  · intro x hx
    exact hx.1

lemma rootSetA_nonempty (P Q : Polynomial ℝ) (alpha w : ℝ)
    (haw : alpha ≤ w) (m : ℕ)
    (hneg : (X ^ m * P + Q).eval alpha < 0)
    (hpos : 0 < (X ^ m * P + Q).eval w) :
    (rootSetA P Q alpha w m).Nonempty := by
  have hcont : Continuous fun x : ℝ => (X ^ m * P + Q).eval x :=
    Polynomial.continuous _
  have hsub := intermediate_value_Icc haw hcont.continuousOn
  have h0 : (0 : ℝ) ∈ Icc ((X ^ m * P + Q).eval alpha) ((X ^ m * P + Q).eval w) :=
    ⟨le_of_lt hneg, le_of_lt hpos⟩
  obtain ⟨x, hx, hfx⟩ := hsub h0
  exact ⟨x, hx, hfx⟩

lemma muA_mem (P Q : Polynomial ℝ) (alpha w : ℝ) (m : ℕ)
    (hne : (rootSetA P Q alpha w m).Nonempty) :
    muA P Q alpha w m ∈ rootSetA P Q alpha w m :=
  (rootSetA_isCompact P Q alpha w m).sInf_mem hne

lemma muA_gt_alpha (P Q : Polynomial ℝ) (alpha w : ℝ) (m : ℕ)
    (hne : (rootSetA P Q alpha w m).Nonempty)
    (hneg : (X ^ m * P + Q).eval alpha < 0) :
    alpha < muA P Q alpha w m := by
  have hmem := muA_mem P Q alpha w m hne
  rcases eq_or_lt_of_le hmem.1.1 with h | h
  · exfalso
    rw [h, hmem.2] at hneg
    exact lt_irrefl 0 hneg
  · exact h

lemma muA_lt_w (P Q : Polynomial ℝ) (alpha w : ℝ) (m : ℕ)
    (hne : (rootSetA P Q alpha w m).Nonempty)
    (hpos : 0 < (X ^ m * P + Q).eval w) :
    muA P Q alpha w m < w := by
  have hmem := muA_mem P Q alpha w m hne
  rcases eq_or_lt_of_le hmem.1.2 with h | h
  · exfalso
    rw [← h, hmem.2] at hpos
    exact lt_irrefl 0 hpos
  · exact h

/-- Minimality: no roots of `R_m` strictly between `α` and `muA m`. -/
lemma muA_min (P Q : Polynomial ℝ) (alpha w : ℝ) (m : ℕ)
    (hne : (rootSetA P Q alpha w m).Nonempty)
    {y : ℝ} (h1 : alpha < y) (h2 : y < muA P Q alpha w m) :
    (X ^ m * P + Q).eval y ≠ 0 := by
  intro hy
  have hmem := muA_mem P Q alpha w m hne
  have hymem : y ∈ rootSetA P Q alpha w m :=
    ⟨⟨le_of_lt h1, le_trans (le_of_lt h2) hmem.1.2⟩, hy⟩
  exact absurd (csInf_le (rootSetA_isCompact P Q alpha w m).bddBelow hymem)
    (not_le.mpr h2)

/-- The heart of the strict decrease: at the root `muA m`, the next
member is positive — `R_{m+1}(y) = (1 − y)·Q(y) > 0` when `y > 1` and
`Q(y) < 0` — so the IVT plants a smaller root of `R_{m+1}`. -/
lemma muA_strictAnti (P G Q : Polynomial ℝ) (alpha w : ℝ)
    (halpha : 1 < alpha) (haw : alpha < w)
    (hfac : P = (X - Polynomial.C alpha) * G)
    (hwin : ∀ x : ℝ, alpha ≤ x → x ≤ w → Q.eval x < 0)
    (m : ℕ) (hpos : 0 < (X ^ m * P + Q).eval w) :
    muA P Q alpha w (m + 1) < muA P Q alpha w m := by
  have hQa : Q.eval alpha < 0 := hwin alpha le_rfl (le_of_lt haw)
  have hneg : (X ^ m * P + Q).eval alpha < 0 := by
    rw [PisotLadder.family_at_alpha P G Q alpha hfac m]
    exact hQa
  have hne : (rootSetA P Q alpha w m).Nonempty :=
    rootSetA_nonempty P Q alpha w (le_of_lt haw) m hneg hpos
  have hmem := muA_mem P Q alpha w m hne
  have hya : alpha ≤ muA P Q alpha w m := hmem.1.1
  have hyw : muA P Q alpha w m ≤ w := hmem.1.2
  have hygt : alpha < muA P Q alpha w m := muA_gt_alpha P Q alpha w m hne hneg
  have hnext : 0 < (X ^ (m + 1) * P + Q).eval (muA P Q alpha w m) := by
    rw [PisotLadder.family_rec P Q m (muA P Q alpha w m), hmem.2, mul_zero, zero_add]
    exact mul_pos_of_neg_of_neg (by linarith) (hwin _ hya hyw)
  have hnega : (X ^ (m + 1) * P + Q).eval alpha < 0 := by
    rw [PisotLadder.family_at_alpha P G Q alpha hfac (m + 1)]
    exact hQa
  have hcont : Continuous fun x : ℝ => (X ^ (m + 1) * P + Q).eval x :=
    Polynomial.continuous _
  have hsub := intermediate_value_Icc (le_of_lt hygt) hcont.continuousOn
  have h0 : (0 : ℝ) ∈ Icc ((X ^ (m + 1) * P + Q).eval alpha)
      ((X ^ (m + 1) * P + Q).eval (muA P Q alpha w m)) :=
    ⟨le_of_lt hnega, le_of_lt hnext⟩
  obtain ⟨z, hz, hfz⟩ := hsub h0
  have hza : alpha < z := by
    rcases eq_or_lt_of_le hz.1 with h | h
    · exfalso
      rw [← h] at hfz
      linarith
    · exact h
  have hzy : z < muA P Q alpha w m := by
    rcases eq_or_lt_of_le hz.2 with h | h
    · exfalso
      rw [h] at hfz
      linarith
    · exact h
  have hzmem : z ∈ rootSetA P Q alpha w (m + 1) :=
    ⟨⟨le_of_lt hza, le_trans (le_of_lt hzy) hyw⟩, hfz⟩
  calc muA P Q alpha w (m + 1)
      ≤ z := csInf_le (rootSetA_isCompact P Q alpha w (m + 1)).bddBelow hzmem
    _ < muA P Q alpha w m := hzy

/-- The canonical roots above tend to `α`. -/
lemma muA_tendsto (P G Q : Polynomial ℝ) (alpha w : ℝ)
    (halpha : 1 < alpha) (haw : alpha < w)
    (hfac : P = (X - Polynomial.C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hwin : ∀ x : ℝ, alpha ≤ x → x ≤ w → Q.eval x < 0)
    (M0 : ℕ) (hM0 : ∀ m, M0 ≤ m → 0 < (X ^ m * P + Q).eval w) :
    Tendsto (fun m => muA P Q alpha w m) atTop (nhds alpha) := by
  have hQa : Q.eval alpha < 0 := hwin alpha le_rfl (le_of_lt haw)
  have hnegat : ∀ m : ℕ, (X ^ m * P + Q).eval alpha < 0 := fun m => by
    rw [PisotLadder.family_at_alpha P G Q alpha hfac m]
    exact hQa
  rw [tendsto_order]
  constructor
  · intro y hy
    filter_upwards [eventually_ge_atTop M0] with m hm
    have hne : (rootSetA P Q alpha w m).Nonempty :=
      rootSetA_nonempty P Q alpha w (le_of_lt haw) m (hnegat m) (hM0 m hm)
    exact lt_of_lt_of_le hy (muA_mem P Q alpha w m hne).1.1
  · intro y hy
    rcases le_or_gt w y with hwy | hyw
    · filter_upwards [eventually_ge_atTop M0] with m hm
      have hne : (rootSetA P Q alpha w m).Nonempty :=
        rootSetA_nonempty P Q alpha w (le_of_lt haw) m (hnegat m) (hM0 m hm)
      exact lt_of_lt_of_le (muA_lt_w P Q alpha w m hne (hM0 m hm)) hwy
    · obtain ⟨M1, hM1⟩ :=
        exists_eval_pos_above P G Q alpha y (lt_trans halpha hy) hy hfac hG
      filter_upwards [eventually_ge_atTop M1] with m hm
      have hyneg := hnegat m
      have hypos := hM1 m hm
      have hcont : Continuous fun x : ℝ => (X ^ m * P + Q).eval x :=
        Polynomial.continuous _
      have hsub := intermediate_value_Icc (le_of_lt hy) hcont.continuousOn
      have h0 : (0 : ℝ) ∈ Icc ((X ^ m * P + Q).eval alpha) ((X ^ m * P + Q).eval y) :=
        ⟨le_of_lt hyneg, le_of_lt hypos⟩
      obtain ⟨z, hz, hfz⟩ := hsub h0
      have hzy : z < y := by
        rcases eq_or_lt_of_le hz.2 with h | h
        · exfalso
          rw [h] at hfz
          linarith
        · exact h
      have hzmem : z ∈ rootSetA P Q alpha w m :=
        ⟨⟨hz.1, le_trans (le_of_lt hzy) (le_of_lt hyw)⟩, hfz⟩
      exact lt_of_le_of_lt
        (csInf_le (rootSetA_isCompact P Q alpha w m).bddBelow hzmem) hzy

/-- **The above-ladder.** For `P = (X − C α)·G` with `α > 1` and
`G > 0` on `[1, ∞)`, and a companion `Q` with `Q(α) < 0`: for `m` large
the family `R_m = X^m·P + Q` has a canonical root `mu m ∈ (α, α + 1)`,
the smallest root above `α`; the sequence is strictly decreasing; and
it tends to `α`.  The `sInf` mirror of
`PDT.PisotLadder.pisot_ladder_family`. -/
theorem pisot_ladder_above (P G Q : Polynomial ℝ) (alpha : ℝ)
    (halpha : 1 < alpha)
    (hfac : P = (X - Polynomial.C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hQa : Q.eval alpha < 0) :
    ∃ M : ℕ, ∃ mu : ℕ → ℝ,
      (∀ m, M ≤ m →
        (alpha < mu m ∧ mu m < alpha + 1) ∧
        (X ^ m * P + Q).eval (mu m) = 0 ∧
        (∀ y, alpha < y → y < mu m → (X ^ m * P + Q).eval y ≠ 0) ∧
        mu (m + 1) < mu m) ∧
      Tendsto mu atTop (nhds alpha) := by
  obtain ⟨w, hw_gt, hw_le, hwin⟩ := window_above Q alpha hQa
  have hw1 : 1 < w := lt_trans halpha hw_gt
  obtain ⟨M0, hM0⟩ := exists_eval_pos_above P G Q alpha w hw1 hw_gt hfac hG
  have hnegat : ∀ m : ℕ, (X ^ m * P + Q).eval alpha < 0 := fun m => by
    rw [PisotLadder.family_at_alpha P G Q alpha hfac m]
    exact hwin alpha le_rfl (le_of_lt hw_gt)
  refine ⟨M0, fun m => muA P Q alpha w m, fun m hm => ?_,
    muA_tendsto P G Q alpha w halpha hw_gt hfac hG hwin M0 hM0⟩
  have hpos := hM0 m hm
  have hne : (rootSetA P Q alpha w m).Nonempty :=
    rootSetA_nonempty P Q alpha w (le_of_lt hw_gt) m (hnegat m) hpos
  refine ⟨⟨muA_gt_alpha P Q alpha w m hne (hnegat m), ?_⟩,
    (muA_mem P Q alpha w m hne).2,
    fun y h1 h2 => muA_min P Q alpha w m hne h1 h2,
    muA_strictAnti P G Q alpha w halpha hw_gt hfac hwin m hpos⟩
  have := muA_lt_w P Q alpha w m hne hpos
  linarith

/-! ### The finiteness discharge -/

/-- The degeneracy set: points of `(1, B)` that are integers or have
integer trace `x + 1/x`. -/
def badSet (B : ℝ) : Set ℝ :=
  {x : ℝ | 1 < x ∧ x < B ∧
    ((∃ n : ℤ, x = (n : ℝ)) ∨ (∃ n : ℤ, x + x⁻¹ = (n : ℝ)))}

lemma mem_badSet {B x : ℝ} :
    x ∈ badSet B ↔ 1 < x ∧ x < B ∧
      ((∃ n : ℤ, x = (n : ℝ)) ∨ (∃ n : ℤ, x + x⁻¹ = (n : ℝ))) :=
  Iff.rfl

/-- The degeneracy set is finite: the integer branch lies in the cast
of `[1, ⌈B⌉]`; the trace branch lies in the (finite) root sets of the
quadratics `X² − n·X + 1` for the finitely many integers
`n ∈ [2, ⌈B+1⌉]`. -/
lemma badSet_finite (B : ℝ) : (badSet B).Finite := by
  have hint : {x : ℝ | 1 < x ∧ x < B ∧ ∃ n : ℤ, x = (n : ℝ)}.Finite := by
    apply Set.Finite.subset ((Set.finite_Icc (1 : ℤ) ⌈B⌉).image fun n : ℤ => (n : ℝ))
    rintro x ⟨hx1, hxB, n, rfl⟩
    refine Set.mem_image_of_mem _ (Set.mem_Icc.mpr ⟨?_, ?_⟩)
    · exact_mod_cast hx1.le
    · exact_mod_cast le_trans hxB.le (Int.le_ceil B)
  have htrace : {x : ℝ | 1 < x ∧ x < B ∧ ∃ n : ℤ, x + x⁻¹ = (n : ℝ)}.Finite := by
    have hsub : {x : ℝ | 1 < x ∧ x < B ∧ ∃ n : ℤ, x + x⁻¹ = (n : ℝ)} ⊆
        ⋃ n ∈ Set.Icc (2 : ℤ) ⌈B + 1⌉,
          {x : ℝ | (X ^ 2 - Polynomial.C ((n : ℝ)) * X + 1).IsRoot x} := by
      rintro x ⟨hx1, hxB, n, hn⟩
      have hx0 : x ≠ 0 := by intro h; rw [h] at hx1; linarith
      have hxinv1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx1
      have hxinvpos : (0 : ℝ) < x⁻¹ := inv_pos.mpr (by linarith)
      have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
      have hlow : (2 : ℝ) < x + x⁻¹ := by
        nlinarith [mul_pos (show (0 : ℝ) < x - 1 by linarith)
          (show (0 : ℝ) < 1 - x⁻¹ by linarith)]
      have hhigh : x + x⁻¹ < B + 1 := by linarith
      have hn2 : (2 : ℤ) ≤ n := by
        have h1 : (2 : ℝ) < (n : ℝ) := hn ▸ hlow
        exact_mod_cast h1.le
      have hnB : n ≤ ⌈B + 1⌉ := by
        have h1 : (n : ℝ) < B + 1 := hn ▸ hhigh
        exact_mod_cast le_trans h1.le (Int.le_ceil (B + 1))
      refine Set.mem_biUnion (Set.mem_Icc.mpr ⟨hn2, hnB⟩) ?_
      change (X ^ 2 - Polynomial.C ((n : ℝ)) * X + 1).eval x = 0
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
      linear_combination x * hn - hxx
    apply Set.Finite.subset
      (Set.Finite.biUnion (Set.finite_Icc (2 : ℤ) ⌈B + 1⌉) fun n _ => ?_) hsub
    apply Polynomial.finite_setOfPred_isRoot
    intro hzero
    have h1 := congrArg (fun q : Polynomial ℝ => q.eval 0) hzero
    simp at h1
  apply Set.Finite.subset (hint.union htrace)
  intro x hx
  obtain ⟨hx1, hxB, hcase⟩ := mem_badSet.mp hx
  rcases hcase with h | h
  · exact Set.mem_union_left _ ⟨hx1, hxB, h⟩
  · exact Set.mem_union_right _ ⟨hx1, hxB, h⟩

/-- Injectivity on a tail from a strictly increasing step. -/
lemma injOn_of_strict_mono_step (lam : ℕ → ℝ) (M : ℕ)
    (hstep : ∀ m, M ≤ m → lam m < lam (m + 1)) :
    Set.InjOn lam (Set.Ici M) := by
  have hmono : ∀ m1 m2 : ℕ, M ≤ m1 → m1 < m2 → lam m1 < lam m2 := by
    intro m1 m2 hm1 h12
    have key : ∀ k : ℕ, m1 + 1 ≤ k → lam m1 < lam k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hstep m1 hm1
      | succ n hn ih => exact lt_trans ih (hstep n (by omega))
    exact key m2 h12
  intro a ha b hb hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (ne_of_lt (hmono a b (Set.mem_Ici.mp ha) h))
  · exact h
  · exact absurd hab (ne_of_gt (hmono b a (Set.mem_Ici.mp hb) h))

/-- Injectivity on a tail from a strictly decreasing step. -/
lemma injOn_of_strict_anti_step (mu : ℕ → ℝ) (M : ℕ)
    (hstep : ∀ m, M ≤ m → mu (m + 1) < mu m) :
    Set.InjOn mu (Set.Ici M) := by
  have hanti : ∀ m1 m2 : ℕ, M ≤ m1 → m1 < m2 → mu m2 < mu m1 := by
    intro m1 m2 hm1 h12
    have key : ∀ k : ℕ, m1 + 1 ≤ k → mu k < mu m1 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hstep m1 hm1
      | succ n hn ih => exact lt_trans (hstep n (by omega)) ih
    exact key m2 h12
  intro a ha b hb hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (ne_of_gt (hanti a b (Set.mem_Ici.mp ha) h))
  · exact h
  · exact absurd hab (ne_of_lt (hanti b a (Set.mem_Ici.mp hb) h))

/-- **The finiteness discharge.**  Along any injective tail of a ladder
bounded in `(1, B)`, the two integer degeneracies eventually fail:
past some index, `lam m` is not an integer and `lam m + (lam m)⁻¹` is
not an integer. -/
lemma eventually_nondegenerate (lam : ℕ → ℝ) (M : ℕ) (B : ℝ)
    (hinj : Set.InjOn lam (Set.Ici M))
    (hbounds : ∀ m, M ≤ m → 1 < lam m ∧ lam m < B) :
    ∃ M' : ℕ, M ≤ M' ∧ ∀ m, M' ≤ m →
      (∀ n : ℤ, lam m ≠ (n : ℝ)) ∧ (∀ n : ℤ, lam m + (lam m)⁻¹ ≠ (n : ℝ)) := by
  classical
  have hinjg : Function.Injective fun k : ℕ => lam (M + k) := by
    intro k1 k2 hk
    have h1 : M + k1 ∈ Set.Ici M := Set.mem_Ici.mpr (Nat.le_add_right M k1)
    have h2 : M + k2 ∈ Set.Ici M := Set.mem_Ici.mpr (Nat.le_add_right M k2)
    have := hinj h1 h2 hk
    omega
  have hpre : {k : ℕ | lam (M + k) ∈ badSet B}.Finite := by
    have hrw : {k : ℕ | lam (M + k) ∈ badSet B}
        = (fun k : ℕ => lam (M + k)) ⁻¹' badSet B := rfl
    rw [hrw]
    exact (badSet_finite B).preimage hinjg.injOn
  obtain ⟨K, hK⟩ := hpre.bddAbove
  refine ⟨M + K + 1, by omega, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = M + k := ⟨m - M, by omega⟩
  have hnotbad : lam (M + k) ∉ badSet B := by
    intro hbad
    have hkK : k ≤ K := hK hbad
    omega
  have hb := hbounds (M + k) (by omega)
  constructor
  · intro n hn
    exact hnotbad (mem_badSet.mpr ⟨hb.1, hb.2, Or.inl ⟨n, hn⟩⟩)
  · intro n hn
    exact hnotbad (mem_badSet.mpr ⟨hb.1, hb.2, Or.inr ⟨n, hn⟩⟩)

/-! ### The certificates and the assembly -/

/-- The PLUS-family certificate, packaged: a nondegenerate root
`tau > 1` of `X^m·Pz + Pz.reverse` (over ℝ) is a Salem number. -/
lemma isSalem_of_plus_root
    (Pz : Polynomial ℤ) (hmonic : Pz.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ r ∈ inside, ‖r‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (m : ℕ) (hm : 2 ≤ m)
    (tau : ℝ) (htau : 1 < tau)
    (hroot : (X ^ m * (Pz.map (Int.castRingHom ℝ))
        + Pz.reverse.map (Int.castRingHom ℝ)).eval tau = 0)
    (hτZ : ∀ n : ℤ, tau ≠ (n : ℝ))
    (hτtr : ∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) :
    IsSalem tau := by
  have hQmapC : Pz.reverse.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside :=
    SalemArith.reverse_bridge Pz hmonic alpha inside hfacC
  have hroot' : ((X ^ m * Pz + Pz.reverse).map (Int.castRingHom ℝ)).eval tau = 0 := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    exact hroot
  obtain ⟨hint, hdisk, hcirc, hinv⟩ :=
    SalemArith.salem_certificate Pz hmonic alpha halpha inside hin hconj hfacC
      Pz.reverse hQmapC m (by omega) (by omega) tau htau hroot' hτZ hτtr
  exact ⟨htau, hint, hdisk, hcirc, hinv⟩

/-- The MINUS-family certificate, packaged: a nondegenerate root
`tau > 1` of `X^m·Pz − Pz.reverse` (over ℝ) is a Salem number. -/
lemma isSalem_of_minus_root
    (Pz : Polynomial ℤ) (hmonic : Pz.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ r ∈ inside, ‖r‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (m : ℕ) (hm : 2 ≤ m)
    (tau : ℝ) (htau : 1 < tau)
    (hroot : (X ^ m * (Pz.map (Int.castRingHom ℝ))
        - Pz.reverse.map (Int.castRingHom ℝ)).eval tau = 0)
    (hτZ : ∀ n : ℤ, tau ≠ (n : ℝ))
    (hτtr : ∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) :
    IsSalem tau := by
  have hQmapC : Pz.reverse.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside :=
    SalemArith.reverse_bridge Pz hmonic alpha inside hfacC
  have hroot' : ((X ^ m * Pz - Pz.reverse).map (Int.castRingHom ℝ)).eval tau = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
    exact hroot
  obtain ⟨hint, hdisk, hcirc, hinv⟩ :=
    SalemMinus.salem_certificate_minus Pz hmonic alpha halpha inside hin hconj hfacC
      Pz.reverse hQmapC m (by omega) (by omega) tau htau hroot' hτZ hτtr
  exact ⟨htau, hint, hdisk, hcirc, hinv⟩

/-- The BELOW half, abstract in the companion: the below-ladder plus
the finiteness discharge plus a certificate deliver a Salem number in
`(α − ε, α)`. -/
lemma exists_salem_below (alpha : ℝ) (halpha : 1 < alpha)
    (Pr G Qc : Polynomial ℝ)
    (hfacR : Pr = (X - Polynomial.C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hQca : 0 < Qc.eval alpha)
    (cert : ∀ m : ℕ, 2 ≤ m → ∀ tau : ℝ, 1 < tau →
      (X ^ m * Pr + Qc).eval tau = 0 →
      (∀ n : ℤ, tau ≠ (n : ℝ)) → (∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) → IsSalem tau)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ tau : ℝ, IsSalem tau ∧ alpha - eps < tau ∧ tau < alpha := by
  obtain ⟨c, hc1, hca, hwin⟩ := window_below Qc halpha hQca
  obtain ⟨M, lam, hprops, htend⟩ :=
    PisotLadder.pisot_ladder_family Pr G Qc alpha c halpha hc1 hca hfacR hG hwin
  have hstep : ∀ m, M ≤ m → lam m < lam (m + 1) := fun m hm => (hprops m hm).2.2.2
  have hinj : Set.InjOn lam (Set.Ici M) := injOn_of_strict_mono_step lam M hstep
  have hbounds : ∀ m, M ≤ m → 1 < lam m ∧ lam m < alpha := fun m hm =>
    ⟨lt_trans hc1 (hprops m hm).1.1, (hprops m hm).1.2⟩
  obtain ⟨M', _hMM', hnd⟩ := eventually_nondegenerate lam M alpha hinj hbounds
  have hev1 : ∀ᶠ m : ℕ in atTop, alpha - eps < lam m :=
    (tendsto_order.mp htend).1 (alpha - eps) (by linarith)
  obtain ⟨m, hm1, hm2⟩ := (hev1.and (eventually_ge_atTop (max M (max M' 2)))).exists
  have hmM : M ≤ m := le_trans (le_max_left _ _) hm2
  have hmM' : M' ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hm2' : 2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  obtain ⟨⟨hgtc, hlta⟩, hroot, -, -⟩ := hprops m hmM
  obtain ⟨hτZ, hτtr⟩ := hnd m hmM'
  exact ⟨lam m, cert m hm2' (lam m) (lt_trans hc1 hgtc) hroot hτZ hτtr, hm1, hlta⟩

/-- The ABOVE half, abstract in the companion: the above-ladder plus
the finiteness discharge plus a certificate deliver a Salem number in
`(α, α + ε)`. -/
lemma exists_salem_above (alpha : ℝ) (halpha : 1 < alpha)
    (Pr G Qc : Polynomial ℝ)
    (hfacR : Pr = (X - Polynomial.C alpha) * G)
    (hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x)
    (hQca : Qc.eval alpha < 0)
    (cert : ∀ m : ℕ, 2 ≤ m → ∀ tau : ℝ, 1 < tau →
      (X ^ m * Pr + Qc).eval tau = 0 →
      (∀ n : ℤ, tau ≠ (n : ℝ)) → (∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) → IsSalem tau)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ tau : ℝ, IsSalem tau ∧ alpha < tau ∧ tau < alpha + eps := by
  obtain ⟨M, mu, hprops, htend⟩ := pisot_ladder_above Pr G Qc alpha halpha hfacR hG hQca
  have hstep : ∀ m, M ≤ m → mu (m + 1) < mu m := fun m hm => (hprops m hm).2.2.2
  have hinj : Set.InjOn mu (Set.Ici M) := injOn_of_strict_anti_step mu M hstep
  have hbounds : ∀ m, M ≤ m → 1 < mu m ∧ mu m < alpha + 1 := fun m hm =>
    ⟨lt_trans halpha (hprops m hm).1.1, (hprops m hm).1.2⟩
  obtain ⟨M', _hMM', hnd⟩ := eventually_nondegenerate mu M (alpha + 1) hinj hbounds
  have hev1 : ∀ᶠ m : ℕ in atTop, mu m < alpha + eps :=
    (tendsto_order.mp htend).2 (alpha + eps) (by linarith)
  obtain ⟨m, hm1, hm2⟩ := (hev1.and (eventually_ge_atTop (max M (max M' 2)))).exists
  have hmM : M ≤ m := le_trans (le_max_left _ _) hm2
  have hmM' : M' ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm2
  have hm2' : 2 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm2
  obtain ⟨⟨hgta, _⟩, hroot, -, -⟩ := hprops m hmM
  obtain ⟨hτZ, hτtr⟩ := hnd m hmM'
  exact ⟨mu m, cert m hm2' (mu m) (lt_trans halpha hgta) hroot hτZ hτtr, hgta, hm1⟩

/-- **The two-sided assembly.**  Every Pisot-pattern polynomial —
monic over ℤ, complex factorization `(X − C α)·∏ (X − C r)` with
`α > 1` and the conjugation-closed inside roots strictly inside the
unit circle — with the nondegeneracy `P(1/α) ≠ 0` has Salem
numbers approaching `α` from BOTH sides: for every `ε > 0` there are
Salem numbers in `(α − ε, α)` and in `(α, α + ε)`.

The sign of `Q(α) = α^p·P(1/α)` (the reverse polynomial at `α`) routes
the plus family `X^m·P + Q` to one side and the minus family
`X^m·P − Q` to the other; each ladder's roots are nondegenerate
eventually (the finiteness discharge), and the certificates of
`PdtSalemArith` and `PdtSalemMinus` promote them to Salem numbers. -/
theorem salem_two_sided
    (Pz : Polynomial ℤ) (hmonic : Pz.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ r ∈ inside, ‖r‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (hnondeg : (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ ≠ 0)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ tau : ℝ, IsSalem tau ∧ alpha - eps < tau ∧ tau < alpha) ∧
    (∃ tau : ℝ, IsSalem tau ∧ alpha < tau ∧ tau < alpha + eps) := by
  classical
  have ha0 : alpha ≠ 0 := ne_of_gt (by linarith)
  -- monicity, degree, and the root `α` of the real image
  have hPrMonic : (Pz.map (Int.castRingHom ℝ)).Monic := hmonic.map _
  have hPrDeg : (Pz.map (Int.castRingHom ℝ)).natDegree = inside.card + 1 := by
    rw [hmonic.natDegree_map]
    exact SalemArith.Pz_natDegree Pz hmonic alpha inside hfacC
  have hPrAlpha : (Pz.map (Int.castRingHom ℝ)).eval alpha = 0 := by
    have h1 : ((((Pz.map (Int.castRingHom ℝ)).eval alpha : ℝ)) : ℂ)
        = (Pz.map (Int.castRingHom ℂ)).eval ((alpha : ℂ)) :=
      (eval_int_transfer Pz alpha).symm
    rw [hfacC, SalemCircle.eval_P, sub_self, zero_mul] at h1
    exact_mod_cast h1
  -- the sign scalar `e = Q(α) = α^p·P(1/α) ≠ 0`
  have hQrRev : Pz.reverse.map (Int.castRingHom ℝ)
      = (Pz.map (Int.castRingHom ℝ)).reflect (inside.card + 1) := by
    rw [← hPrDeg, Polynomial.reflect_map]
    congr 1
    rw [hmonic.natDegree_map]
    rfl
  have heId : (Pz.reverse.map (Int.castRingHom ℝ)).eval alpha
      = alpha ^ (inside.card + 1) * (Pz.map (Int.castRingHom ℝ)).eval alpha⁻¹ := by
    rw [hQrRev]
    exact reflect_eval_eq (Pz.map (Int.castRingHom ℝ)) ha0 (inside.card + 1)
      (le_of_eq hPrDeg)
  have he_ne : (Pz.reverse.map (Int.castRingHom ℝ)).eval alpha ≠ 0 := by
    rw [heId]
    exact mul_ne_zero (pow_ne_zero _ ha0) hnondeg
  -- the quotient `G` and its positivity on `[1, ∞)`
  obtain ⟨G, hfacR⟩ : ∃ G : Polynomial ℝ,
      Pz.map (Int.castRingHom ℝ) = (X - Polynomial.C alpha) * G :=
    ⟨_, (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hPrAlpha).symm⟩
  have hGmonic : G.Monic :=
    (Polynomial.monic_X_sub_C alpha).of_mul_monic_left (hfacR ▸ hPrMonic)
  have hGmapC : G.map (algebraMap ℝ ℂ) = (inside.map fun r => X - Polynomial.C r).prod := by
    apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero ((alpha : ℂ)))
    calc (X - Polynomial.C ((alpha : ℂ))) * G.map (algebraMap ℝ ℂ)
        = ((X - Polynomial.C alpha) * G).map (algebraMap ℝ ℂ) := by
          rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
            Polynomial.map_C, Complex.coe_algebraMap]
      _ = (Pz.map (Int.castRingHom ℝ)).map (algebraMap ℝ ℂ) := by rw [← hfacR]
      _ = Pz.map (Int.castRingHom ℂ) := map_int_real_complex Pz
      _ = SalemCircle.P alpha inside := hfacC
      _ = (X - Polynomial.C ((alpha : ℂ)))
          * (inside.map fun r => X - Polynomial.C r).prod := rfl
  have hG : ∀ x : ℝ, 1 ≤ x → 0 < G.eval x := G_pos G hGmonic inside hin hGmapC
  -- the two packaged certificates
  have certP : ∀ m : ℕ, 2 ≤ m → ∀ tau : ℝ, 1 < tau →
      (X ^ m * (Pz.map (Int.castRingHom ℝ))
        + Pz.reverse.map (Int.castRingHom ℝ)).eval tau = 0 →
      (∀ n : ℤ, tau ≠ (n : ℝ)) → (∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) → IsSalem tau :=
    fun m hm tau htau hroot hτZ hτtr =>
      isSalem_of_plus_root Pz hmonic alpha halpha inside hin hconj hfacC
        m hm tau htau hroot hτZ hτtr
  have certM : ∀ m : ℕ, 2 ≤ m → ∀ tau : ℝ, 1 < tau →
      (X ^ m * (Pz.map (Int.castRingHom ℝ))
        + -(Pz.reverse.map (Int.castRingHom ℝ))).eval tau = 0 →
      (∀ n : ℤ, tau ≠ (n : ℝ)) → (∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) → IsSalem tau := by
    intro m hm tau htau hroot hτZ hτtr
    have hroot' : (X ^ m * (Pz.map (Int.castRingHom ℝ))
        - Pz.reverse.map (Int.castRingHom ℝ)).eval tau = 0 := by
      rw [sub_eq_add_neg]
      exact hroot
    exact isSalem_of_minus_root Pz hmonic alpha halpha inside hin hconj hfacC
      m hm tau htau hroot' hτZ hτtr
  -- the sign fork: each case produces BOTH sides
  rcases lt_or_lt_iff_ne.mpr he_ne with hneg | hpos
  · -- `Q(α) < 0`: BELOW via the minus family, ABOVE via the plus family
    have hnegneg : 0 < (-(Pz.reverse.map (Int.castRingHom ℝ))).eval alpha := by
      rw [Polynomial.eval_neg]
      linarith
    exact ⟨exists_salem_below alpha halpha (Pz.map (Int.castRingHom ℝ)) G
        (-(Pz.reverse.map (Int.castRingHom ℝ))) hfacR hG hnegneg certM eps heps,
      exists_salem_above alpha halpha (Pz.map (Int.castRingHom ℝ)) G
        (Pz.reverse.map (Int.castRingHom ℝ)) hfacR hG hneg certP eps heps⟩
  · -- `Q(α) > 0`: BELOW via the plus family, ABOVE via the minus family
    have hnegneg : (-(Pz.reverse.map (Int.castRingHom ℝ))).eval alpha < 0 := by
      rw [Polynomial.eval_neg]
      linarith
    exact ⟨exists_salem_below alpha halpha (Pz.map (Int.castRingHom ℝ)) G
        (Pz.reverse.map (Int.castRingHom ℝ)) hfacR hG hpos certP eps heps,
      exists_salem_above alpha halpha (Pz.map (Int.castRingHom ℝ)) G
        (-(Pz.reverse.map (Int.castRingHom ℝ))) hfacR hG hnegneg certM eps heps⟩

end
end SalemEndgame
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
