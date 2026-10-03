/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Small.Gram

/-! the proof notes, §7, Lemma 7, one entry. With `K = 5n`, `N = 4n + a + b` and
`p_ab = binom(t+n,n)^4 binom(t,a) binom(t,b)` (integer-valued), `S_n D_n^4 E_a E_b = K!·p_ab`;
(b) the polynomial part is `Σ_{K≤k≤N} c_k/binom(k,K)·binom(t,k-K)` with integer Newton coefficients
`c_k`, so its integer values have `v_p ≥ -⌊log_p N⌋`; (a) the residues are integers and
`v_p(β_j) ≥ -3⌊log_p j⌋ - v_p(den r)`; (c) `polynomialMoment_VG`. Every entry of `binomGram r n`
has Gauss valuation `≥ -3⌊log_p(10n+2)⌋ - v_p(den r)`. -/

public section

open Zeta32.Arith.Local

-- adapted from dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/DecayQuotient.lean
-- (`gramNum_divByMonic`, `gramQuot_eval_VG`, `gramQuot_natDegree_le`) and
-- .../Base/DecayResidue.lean (`gramRes_VG`). layout (4,5,3), and the new
-- bound on the pole values `β_j` and the entry bound for `U_r`.

open Polynomial
open scoped BigOperators
namespace Zeta32.Arith.Small
open Zeta32
noncomputable section

/-- binom(t+n,n)^4 binom(t,a) binom(t,b). -/
def pab (n a b : ℕ) : ℚ[X] := shiftBinom n ^ 4 * binomPoly a * binomPoly b

/-- The literal binomial Gram numerator. -/
def gramNum (n a b : ℕ) : ℚ[X] := C (Sn n) * (D n)^4 * binomPoly a * binomPoly b

lemma gramNum_eq (n a b : ℕ) :
    gramNum n a b = C ((5*n).factorial : ℚ) * pab n a b := by
  have hs : Sn n * ((n.factorial : ℚ))^4 = ((5*n).factorial : ℚ) := by
    rw [Sn]; field_simp
  rw [gramNum, pab, D_eq_shiftBinom, mul_pow, ← C_pow, ← hs, C_mul]
  ring

lemma pab_eval_int (p : ℕ) [Fact p.Prime] (n a b : ℕ) (m : ℤ) :
    VG p ((pab n a b).eval (m:ℚ)) 0 := by
  rw [pab, eval_mul, eval_mul, eval_pow]
  have h := (((shiftBinom_eval_int p n m).pow 4).mul (binomPoly_eval_int_VG p a m)).mul
    (binomPoly_eval_int_VG p b m)
  simpa using h

lemma pab_natDegree_le (n a b : ℕ) : (pab n a b).natDegree ≤ 4*n + a + b := by
  unfold pab
  refine (natDegree_mul_le).trans ?_
  refine add_le_add ((natDegree_mul_le).trans (add_le_add ((natDegree_pow_le).trans ?_) ?_)) ?_
  · rw [shiftBinom_natDegree]
  · rw [binomPoly_natDegree]
  · rw [binomPoly_natDegree]

/-- Newton coefficients of p_ab at -K. -/
def quotCoeff (n a b k : ℕ) : ℚ := newtonCoeff (pab n a b) (-(((5*n : ℕ)) : ℚ)) k

/-- The literal polynomial part of the binomial Gram entry. -/
theorem gramNum_divByMonic (n a b : ℕ) :
    gramNum n a b /ₘ D (5*n) = ∑ k ∈ Finset.Ico (5*n) (4*n+a+b+1),
      C (quotCoeff n a b k * ((k.choose (5*n) : ℚ))⁻¹) * binomPoly (k - 5*n) := by
  set K := 5*n with hK
  set N := 4*n+a+b with hN
  have hexp := newton_expansion (pab_natDegree_le n a b) (-((K : ℕ) : ℚ))
  have hshift : (X - C (-((K:ℕ):ℚ)) : ℚ[X]) = X + C (K:ℚ) := by
    rw [map_neg, sub_neg_eq_add]
  simp only [hshift] at hexp
  set g : ℕ → ℚ[X] := fun k => C (quotCoeff n a b k) *
    (C (K.factorial : ℚ) * (binomPoly k).comp (X + C (K:ℚ))) with hg
  have hF : gramNum n a b = ∑ k ∈ Finset.range (N+1), g k := by
    rw [gramNum_eq, hexp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hg, quotCoeff]
    ring
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N+1)) (fun k => k < K)] at hF
  have hhigh : (Finset.range (N+1)).filter (fun k => ¬ k < K) = Finset.Ico K (N+1) := by
    ext k; simp; omega
  rw [hhigh] at hF
  set r := ∑ k ∈ (Finset.range (N+1)).filter (fun k => k < K), g k with hr
  refine (div_modByMonic_unique _ r (D_monic K) ⟨?_, ?_⟩).1
  · rw [hF, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : K ≤ k := (Finset.mem_Ico.mp hk).1
    simp only [hg]
    rw [shifted_binom_ratio hk', C_mul]
    ring
  · rw [degree_eq_natDegree (D_monic K).ne_zero, D_natDegree]
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · have : (Finset.range (N+1)).filter (fun k => k < K) = ∅ := by
        ext k; simp; omega
      rw [hr, this, Finset.sum_empty, degree_zero, h0]
      exact WithBot.bot_lt_coe _
    · have hnat : r.natDegree ≤ K - 1 := by
        apply natDegree_sum_le_of_forall_le
        intro k hk
        have hkK : k < K := (Finset.mem_filter.mp hk).2
        simp only [hg]
        refine (natDegree_C_mul_le _ _).trans ((natDegree_C_mul_le _ _).trans ?_)
        rw [natDegree_comp, binomPoly_natDegree, natDegree_X_add_C, mul_one]
        omega
      refine (degree_le_of_natDegree_le hnat).trans_lt ?_
      exact_mod_cast (by omega : K - 1 < K)

lemma quotCoeff_VG (p : ℕ) [Fact p.Prime] (n a b k : ℕ) : VG p (quotCoeff n a b k) 0 :=
  newtonCoeff_VG p _ 0 k fun i _ => by
    have := pab_eval_int p n a b (-((5*n : ℕ) : ℤ) + i)
    push_cast at this ⊢
    exact this

/-- Every integer value of the quotient has v_p >= -log_p N. -/
theorem gramQuot_eval_VG (p : ℕ) [Fact p.Prime] (n a b : ℕ) (m : ℤ) :
    VG p ((gramNum n a b /ₘ D (5*n)).eval (m:ℚ)) (-(Nat.log p (4*n+a+b) : ℚ)) := by
  rw [gramNum_divByMonic, eval_finsetSum]
  apply VG.sum
  intro k hk
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  rw [eval_mul, eval_C]
  have h := ((quotCoeff_VG p n a b k).mul (inv_choose_VG p hk1 (by omega : k ≤ 4*n+a+b))).mul
    (binomPoly_eval_int_VG p (k - 5*n) m)
  simpa using h

theorem gramQuot_natDegree_le (n a b : ℕ) :
    (gramNum n a b /ₘ D (5*n)).natDegree ≤ 4*n+a+b - 5*n := by
  rw [gramNum_divByMonic]
  apply natDegree_sum_le_of_forall_le
  intro k hk
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [binomPoly_natDegree]
  omega

theorem gramRes_VG (p : ℕ) [Fact p.Prime] (n a b : ℕ) {j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ 5 * n) :
    VG p ((gramNum n a b).eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 (5*n)).erase j, ((l:ℚ)-(j:ℚ))) 0 := by
  have e : (gramNum n a b).eval (-(j:ℚ)) / ∏ l ∈ (Finset.Icc 1 (5*n)).erase j, ((l:ℚ)-(j:ℚ)) =
      ((5*n).factorial : ℚ) / eraseProd (5*n) j * (pab n a b).eval (((-(j:ℤ)) : ℤ) : ℚ) := by
    rw [gramNum_eq, eval_mul, eval_C, ← eraseProd]
    push_cast
    ring
  rw [e]
  simpa using (residueScale_VG p hj hjK).mul (pab_eval_int p n a b (-(j:ℤ)))

/-! ### The pole values `β_j` -/

lemma H_VG (p : ℕ) [Fact p.Prime] (e j : ℕ) :
    VG p (H e j) (-(e : ℚ) * (Nat.log p j : ℚ)) := by
  unfold H
  apply VG.sum
  intro a ha
  obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
  rw [one_div, ← inv_pow]
  have h := (VG.inv_nat (p := p) ha1 ha2).pow e
  refine h.mono (le_of_eq ?_)
  ring

theorem beta_VG (p : ℕ) [Fact p.Prime] (r : ℚ) (j : ℕ) :
    VG p (beta r j) (-3 * (Nat.log p j : ℚ) - (padicValNat p r.den : ℚ)) := by
  unfold beta
  have hL : (0 : ℚ) ≤ Nat.log p j := Nat.cast_nonneg _
  have hv : (0 : ℚ) ≤ padicValNat p r.den := Nat.cast_nonneg _
  have h1 := VG_two_mul_rat p r
  have h2 : VG p (2 * (j:ℚ) * H 3 j) (-3 * (Nat.log p j : ℚ)) := by
    have := ((VG.natCast (p := p) 2).mul (VG.natCast (p := p) j)).mul (H_VG p 3 j)
    refine this.mono (le_of_eq ?_)
    push_cast; ring
  have h3 : VG p (2 * r * (j:ℚ) * H 2 j)
      (-(padicValNat p r.den : ℚ) - 2 * (Nat.log p j : ℚ)) := by
    have := ((VG_two_mul_rat p r).mul (VG.natCast (p := p) j)).mul (H_VG p 2 j)
    refine this.mono (le_of_eq ?_)
    push_cast; ring
  refine ((h1.mono ?_).sub (h2.mono ?_)).add (h3.mono ?_)
  · linarith
  · linarith
  · linarith

/-! ### The entry bound -/

/-- the proof notes, §7: every entry of the binomial Gram matrix has Gauss valuation
`≥ -3⌊log_p(10n+2)⌋ - v_p(den r)`. -/
theorem binomGram_GV (p : ℕ) [Fact p.Prime] (r : ℚ) (n : ℕ) (a b : Fin (3 * n)) :
    GV p (binomGram r n a b)
      (-3 * (Nat.log p (10*n+2) : ℚ) - (padicValNat p r.den : ℚ)) := by
  set Λ : ℚ := (Nat.log p (10*n+2) : ℚ) with hΛ
  have hΛ0 : (0 : ℚ) ≤ Λ := Nat.cast_nonneg _
  have hv0 : (0 : ℚ) ≤ padicValNat p r.den := Nat.cast_nonneg _
  have ha := a.isLt
  have hb := b.isLt
  change GV p (Ufun r n (gramNum n a b)) _
  unfold Ufun
  apply GV.add
  · -- polynomial part
    apply GV.C
    have hq := polynomialMoment_VG p r (gramQuot_natDegree_le n a b)
      (-(Nat.log p (4*n+a+b) : ℚ)) (gramQuot_eval_VG p n a b)
    refine hq.mono ?_
    have l1 : (Nat.log p (4*n+a+b) : ℚ) ≤ Λ := by
      rw [hΛ]; exact_mod_cast Nat.log_mono_right (by omega)
    have l2 : (Nat.log p (4*n+a+b - 5*n + 2) : ℚ) ≤ Λ := by
      rw [hΛ]; exact_mod_cast Nat.log_mono_right (by omega)
    linarith
  · -- simple poles
    apply GV.sum
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hres := gramRes_VG p n a b hj1 hj2
    have hpole : GV p (C (2*(j:ℚ)) * X + C (beta r j))
        (-3 * Λ - (padicValNat p r.den : ℚ)) := by
      apply GV.add
      · have h2j : VG p (2*(j:ℚ)) 0 := by
          have := (VG.natCast (p := p) 2).mul (VG.natCast (p := p) j)
          simpa using this
        exact ((GV.C h2j).mul GV.X).mono (by linarith)
      · apply GV.C
        refine (beta_VG p r j).mono ?_
        have : (Nat.log p j : ℚ) ≤ Λ := by
          rw [hΛ]; exact_mod_cast Nat.log_mono_right (by omega)
        linarith
    have := (GV.C hres).mul hpole
    simpa using this

end
end Zeta32.Arith.Small

end
