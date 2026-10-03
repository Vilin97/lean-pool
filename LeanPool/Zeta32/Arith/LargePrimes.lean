/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Outer.Norm

/-! the proof notes end of §4 (used as range R3 in §8): for a prime `p > 5n` with `p ∤ den r`,
every coefficient
of `Qtilde r n` is `p`-integral. Every Hankel entry is `p`-integral (the polynomial-part moments
have degree
`≤ 5n - 2 ≤ p - 3`; for `j ≤ 5n < p` the residue `ρ_j` and `β_j` are `p`-integral), and the
normalizer
`S_n^{3n}/F_n` is a `p`-adic unit. -/

public section

open Zeta32.Arith.Local
namespace Zeta32.Outer
open Polynomial

lemma wv_nonneg_large {n p j : ℕ} (hj : j ≤ 5 * n) (h5 : 5 * n < p) : 0 ≤ wv n p j := by
  unfold wv
  split_ifs
  · positivity
  · rw [Nat.div_eq_of_lt (by omega : j - 1 < p), Nat.div_eq_of_lt (by omega : j - 1 - n < p),
      Nat.div_eq_of_lt (by omega : 5 * n - j < p)]
    unfold betaWt
    rw [ite_eq_left (by omega)]
    norm_num

lemma normVal_large {n p : ℕ} (h5 : 5 * n < p) : normVal p n = 0 := by
  unfold normVal
  rw [Nat.div_eq_of_lt h5, Nat.div_eq_of_lt (by omega : n < p)]
  rw [Finset.sum_eq_zero fun i hi => by
    rw [Nat.div_eq_of_lt (by have := Finset.mem_range.mp hi; omega), Nat.cast_zero]]
  norm_num

theorem Q_GV_large {r : ℚ} {n p : ℕ} [hp : Fact p.Prime] (h5 : 5 * n < p) (hr : VG p r 0) :
    GV p (Q r n) 0 := by
  have hK : 5 * n < p^2 := lt_of_lt_of_le h5 (Nat.le_self_pow (by norm_num) p)
  have h := det_GV (p := p) ((X : ℚ[X]) • (B n).map C + (A r n).map C) (fun _ => 0) (fun _ => 0)
    (fun a b => by
      have hn : 0 < n := by have := a.isLt; omega
      have hp2 : p ≠ 2 := by omega
      rw [entry_eq]
      simp only [add_zero]
      apply GV.add
      · apply GV.C
        apply polynomialMoment_VG_small hp2 hr (polynomialPart_GV p n _)
        have := polynomialPart_natDegree_le n (a.val + b.val)
        have ha := a.isLt
        have hb := b.isLt
        omega
      · apply GV.sum
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
        have hg := (gam_GV hr hj1 hj2 hK).mono (wv_nonneg_large hj2 h5)
        have hv : VG p ((-(j:ℚ))^(a:ℕ) * (-(j:ℚ))^(b:ℕ)) 0 := by
          have h1 := ((VG.natCast (p := p) j).neg.pow (a:ℕ)).mul ((VG.natCast (p := p)
            j).neg.pow (b:ℕ))
          simpa using h1
        simpa using hg.mul (GV.C hv))
  simpa [Q] using h

end Zeta32.Outer

namespace Zeta32.Arith

open Polynomial Zeta32.Outer

/-- the proof notes, §4, last paragraph: for `p > 5n`, `p ∤ den r`, every nonzero coefficient of
`Qtilde r n`
has nonnegative `p`-adic valuation. -/
theorem large_prime_integrality (r : ℚ) (n p : ℕ) : p.Prime → 5 * n < p → ¬ p ∣ r.den → ∀ k,
    (Qtilde r n).coeff k ≠ 0 → 0 ≤ padicValRat p ((Qtilde r n).coeff k) := by
  intro hp h5 hden k hk
  have := Fact.mk hp
  have hK : 5 * n < p^2 := lt_of_lt_of_le h5 (Nat.le_self_pow (by norm_num) p)
  have hs : VG p (scale n) 0 := by
    have := scale_VG p hK
    rwa [normVal_large h5] at this
  have hQt := GV.C_mul hs (Q_GV_large h5 (VG_of_not_dvd_den hden) (r := r))
  change GV p (Qtilde r n) _ at hQt
  have := (hQt k).resolve_left hk
  norm_num at this
  exact_mod_cast this

end Zeta32.Arith
end
