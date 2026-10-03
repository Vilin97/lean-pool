/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Congruence

/-! the proof notes, §6 Proposition 6. `exceptional` is defined in `Zeta32.PrimeEdge.Reference`
(same name, same value). the proof is the S5 assembly (primitive reduction). -/

public section
namespace Zeta32.PrimeEdge

open Polynomial Zeta32.Arith.Local

lemma isPrimitive_neg {f : ℤ[X]} (hf : f.IsPrimitive) : (-f).IsPrimitive :=
  Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr fun c hc => hf c ((dvd_neg).mp hc)

lemma P_isPrimitive (r : ℚ) (n : ℕ) (hQ : Zeta32.Q r n ≠ 0) : (Zeta32.P r n).IsPrimitive := by
  unfold Zeta32.P
  split_ifs
  · exact Zeta32.primitiveQ_isPrimitive r n hQ
  · exact isPrimitive_neg (Zeta32.primitiveQ_isPrimitive r n hQ)

lemma P_map_eq (r : ℚ) (n : ℕ) :
    (Zeta32.P r n).map (Int.castRingHom ℚ) =
      C (Zeta32.dtilde r n * Zeta32.scale n) * Zeta32.Q r n := by
  rw [← algebraMap_int_eq, Zeta32.P_eq_dtilde_Qtilde, Zeta32.Qtilde, ← mul_assoc, ← C_mul]

theorem prime_edge (r : ℚ) (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p)
    (hE : p ∉ exceptional) (hden : ¬ p ∣ r.den) :
    ∃ c : ZMod p, c ≠ 0 ∧
      (Zeta32.P r (p-1)).map (Int.castRingHom (ZMod p)) = Polynomial.C c := by
  obtain ⟨s, c, hs, hc, hcv, hcong⟩ := scaled_Q_congruence r hp hE hden
  have hQ : Zeta32.Q r (p - 1) ≠ 0 := by
    intro hz
    have hzero : VG p (-c) 1 := by
      simpa [hz] using hcong 0
    rcases hzero with hz | hv
    · exact hc (neg_eq_zero.mp hz)
    · rw [padicValRat.neg, hcv] at hv
      norm_num at hv
  exact primitive_constant_reduction_of_scaled_congruence (Zeta32.P r (p - 1))
    (P_isPrimitive r (p - 1) hQ) (Zeta32.Q r (p - 1))
    (Zeta32.dtilde r (p - 1) * Zeta32.scale (p - 1)) s c
    (mul_ne_zero (Zeta32.dtilde_pos r (p - 1)).ne' (Zeta32.scale_pos (p - 1)).ne') hs
    (P_map_eq r (p - 1)) hc hcv hcong

end Zeta32.PrimeEdge
end
