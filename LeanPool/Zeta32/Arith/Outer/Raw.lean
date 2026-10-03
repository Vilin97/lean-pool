/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Outer.Classes

/-! the proof notes section 4, Lemma 5: the Vandermonde bound for the actual `Q r n`.

Rows `a` with `a + 2n + 2 > p` are multiplied by `p` (`rowScale`); then the polynomial-part matrix
`W_{ab} = U_r(q_{a+b})` is `p`-integral (its moments have degree `≤ a + 2n - 1`, and `U_r(t^e)` is
`p`-integral for `e ≤ p - 3` and has `v_p ≥ -1` always), and `rank_one_GV_rows` gives
  `v_p(∏ rowScale · Q r n) ≥ Σ_c Scl n p c`.
The rank-one part follows the Li₂ proof `parameter_raw_Q_GV`
(dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Positive/Packed/P045.lean). -/

public section

open Zeta32.Arith.Local

open Polynomial
open scoped BigOperators
namespace Zeta32.Outer
noncomputable section

/-- Row scaling: `p` on the last `r_p` rows. -/
def rowScale (n p : ℕ) (a : ℕ) : ℚ := if a + 2*n + 2 ≤ p then 1 else p

section Val
variable {p : ℕ} [hp : Fact p.Prime]

lemma prime_VG_one : VG p (p:ℚ) 1 := by
  right
  rw [padicValRat.self hp.out.one_lt]
  norm_num

omit hp in
lemma rowScale_VG (n a : ℕ) : VG p (rowScale n p a) 0 := by
  unfold rowScale
  split_ifs
  · exact VG.one
  · exact VG.natCast p

lemma W_row_GV (hp2 : p ≠ 2) {r : ℚ} (hr : VG p r 0) (n : ℕ) (a b : Fin (3 * n)) :
    GV p (C (rowScale n p a) * C (polynomialMoment r (polynomialPart n (a.val + b.val)))) 0 := by
  rw [← C_mul]
  apply GV.C
  unfold rowScale
  split_ifs with ha
  · rw [one_mul]
    apply polynomialMoment_VG_small hp2 hr (polynomialPart_GV p n _)
    have := polynomialPart_natDegree_le n (a.val + b.val)
    have hb := b.isLt
    omega
  · simpa using (prime_VG_one (p := p)).mul
      (polynomialMoment_VG hr (polynomialPart_GV p n (a.val + b.val)))

omit hp in
/-- `H = W + Σ_c Σ_t γ v vᵀ` after regrouping the poles by classes. -/
theorem H_regroup (r : ℚ) (n : ℕ) (hp0 : 0 < p) (a b : Fin (3 * n)) :
    ((X : ℚ[X]) • (B n).map C + (A r n).map C) a b =
      C (polynomialMoment r (polynomialPart n (a.val + b.val))) +
      ∑ c : Fin p, ∑ t ∈ Finset.range (Ccl p (5*n) c),
        gam r n (jn p (5*n) c t) *
          C ((-(jn p (5*n) c t : ℚ))^(a:ℕ) * (-(jn p (5*n) c t : ℚ))^(b:ℕ)) := by
  rw [entry_eq, regroup p (5*n) hp0,
    ← Fin.sum_univ_eq_sum_range
      (fun c => ∑ t ∈ Finset.range (Ccl p (5*n) c),
        gam r n (jn p (5*n) c t) *
        C ((-(jn p (5*n) c t : ℚ))^(a:ℕ) * (-(jn p (5*n) c t : ℚ))^(b:ℕ))) p]

theorem scaled_Q_GV (hp2 : p ≠ 2) {r : ℚ} (hr : VG p r 0) (n : ℕ) (hK : 5 * n < p ^ 2) :
    GV p (C (∏ a : Fin (3*n), rowScale n p a) * Q r n) (∑ c : Fin p, Scl n p c) := by
  have hp0 : 0 < p := hp.out.pos
  have hdet : C (∏ a : Fin (3*n), rowScale n p a) * Q r n =
      (Matrix.of fun a b : Fin (3*n) => C (rowScale n p a) *
        (C (polynomialMoment r (polynomialPart n (a.val + b.val))) +
        ∑ c : Fin p, ∑ t ∈ Finset.range (Ccl p (5*n) c),
          gam r n (jn p (5*n) c t) *
            C ((-(jn p (5*n) c t : ℚ))^(a:ℕ) * (-(jn p (5*n) c t : ℚ))^(b:ℕ)))).det := by
    have hm := Matrix.det_mul_column (fun a : Fin (3*n) => C (rowScale n p a))
      ((X : ℚ[X]) • (B n).map C + (A r n).map C)
    rw [Q, map_prod, ← hm]
    congr 2
    ext a b
    rw [H_regroup r n hp0 a b]
  rw [hdet]
  apply rank_one_GV_rows
    (fun c : Fin p => Ccl p (5*n) c)
    (fun c t => -(jn p (5*n) c t : ℚ))
    (fun c t => gam r n (jn p (5*n) c t))
    p (fun c t => wv n p (jn p (5*n) c t))
    (fun a => rowScale n p a) (fun a => rowScale_VG n a)
    (fun a b => C (polynomialMoment r (polynomialPart n (a.val + b.val))))
  · intro a b
    exact W_row_GV hp2 hr n a b
  · intro c t
    exact (VG.natCast _).neg
  · intro c s t hs ht hst
    have key : ∀ u v : ℕ, u ≤ v → v < Ccl p (5*n) c →
        (jn p (5*n) c u : ℚ) = jn p (5*n) c v + (p:ℚ) * ((v-u:ℕ):ℚ) := by
      intro u v huv hv
      have hN : jn p (5*n) c u = jn p (5*n) c v + p * (v-u) := by
        unfold jn
        rw [show Ccl p (5*n) c - 1 - u = (Ccl p (5*n) c - 1 - v) + (v-u) by omega, Nat.mul_add]
        ring
      rw [hN]
      push_cast
      ring
    rcases lt_or_gt_of_ne hst with h | h
    · rw [key s t h.le ht]
      have := (prime_VG_one (p := p)).mul (VG.natCast (p := p) (t-s))
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using! this
    · rw [key t s h.le hs]
      have := ((prime_VG_one (p := p)).mul (VG.natCast (p := p) (s-t))).neg
      simpa [sub_eq_add_neg, add_comm, add_left_comm] using! this
  · intro c t ht
    exact gam_GV hr (by unfold jn; omega) (jn_le p (5*n) ht) hK
  · intro c s t hst ht
    by_cases hjt : jn p (5*n) c t ≤ n
    · have := wv_le_big (p := p) (n := n)
        (jn_le p (5*n) (lt_of_le_of_lt hst ht))
      simp only [wv, ite_eq_left hjt]
      exact this
    · have e : jn p (5*n) c s = jn p (5*n) c t + p * (t-s) := by
        unfold jn
        rw [show Ccl p (5*n) c - 1 - s = (Ccl p (5*n) c - 1 - t) + (t-s) by omega, Nat.mul_add]
        ring
      change wv n p (jn p (5*n) c s) ≤ wv n p (jn p (5*n) c t)
      rw [e]
      exact wv_step hp0 (by omega : n < jn p (5*n) c t)
        (e ▸ jn_le p (5*n) (lt_of_le_of_lt hst ht))

end Val

end
end Zeta32.Outer

end
