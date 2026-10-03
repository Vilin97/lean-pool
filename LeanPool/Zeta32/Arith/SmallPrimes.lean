/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Profiles
public import LeanPool.Zeta32.Arith.Small.Entry

/-! the proof notes, §7, Lemma 7: crude all-prime coefficient valuation bound.
`Qtilde r n = det (binomGram r n)` (Small/Gram), every entry has Gauss valuation
`≥ -3⌊log_p(10n+2)⌋ - v_p(den r)` (Small/Entry), and the determinant of a `3n × 3n` matrix loses
at most
`3n` times the entry bound (`det_GV`). Here `D = 2h + sn + 2 = 10n + 2`. -/

public section

open Zeta32.Arith.Local
namespace Zeta32.Arith

theorem small_prime_crude_bound (r : ℚ) (n p : ℕ) :
    p.Prime → ∀ k, (Zeta32.Qtilde r n).coeff k ≠ 0 →
    padicValRat p ((Zeta32.Qtilde r n).coeff k) ≥
      -3*(3*n)*Nat.log p (10*n+2) - (3*n)*padicValNat p r.den := by
  intro hp k hk
  have : Fact p.Prime := ⟨hp⟩
  set β : ℚ := -3 * (Nat.log p (10*n+2) : ℚ) - (padicValNat p r.den : ℚ) with hβ
  have hdet := Zeta32.Arith.Local.det_GV (Small.binomGram r n) (fun _ => β / 2) (fun _ => β / 2)
    (fun a b => by
      have := Small.binomGram_GV p r n a b
      refine this.mono (le_of_eq ?_)
      ring)
  rw [← Small.Qtilde_eq_binomGram_det] at hdet
  have hk' := (hdet k).resolve_left hk
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hk'
  have hq : ((-3*(3*n)*Nat.log p (10*n+2) - (3*n)*padicValNat p r.den : ℤ) : ℚ) ≤
      (padicValRat p ((Zeta32.Qtilde r n).coeff k) : ℚ) := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast,
      Nat.cast_mul, Nat.cast_ofNat] at hk' ⊢
    rw [hβ] at hk'
    linarith
  exact_mod_cast hq

end Zeta32.Arith
end
