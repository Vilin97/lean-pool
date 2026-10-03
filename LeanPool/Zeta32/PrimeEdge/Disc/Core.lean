/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Disc.Factor

/-! the proof notes, §2 Lemma 3 for truncated scaled numerators, and the coefficients
of `seriesPart` when `dissectNum = p^E u^E R`: the coefficient of `u^e` vanishes for `e < E` and
has valuation `≥ e`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

lemma VG_pow_nat [Fact p.Prime] (E : ℕ) : VG p ((p : ℚ) ^ E) E := by
  have h := VG.primePow (p := p) (E : ℤ)
  rw [zpow_natCast] at h
  exact_mod_cast h

/-- **Lemma 3 (local integrality), scaled form.** If the coefficient of `u^e` in `S` has
valuation `≥ e` and vanishes for `e < E₀`, then `V(S / ∏_{m ∈ M} (u + m))` has valuation
`≥ E₀`, provided `E₀ ≤ |M| + 2p - 2`. -/
theorem VG_locValue_scaled [Fact p.Prime] (hp : 5 ≤ p) {s : ℚ} (hs : VG p s 1) {M : Finset ℕ}
    (hM : M ⊆ Finset.range 5) {S : ℚ[X]} {E₀ : ℕ} (hS : ∀ e, VG p (S.coeff e) e)
    (hz : ∀ e < E₀, S.coeff e = 0) (hE : E₀ + 2 ≤ M.card + 2 * p) :
    VG p (locValue s S M) E₀ := by
  rw [locValue_eq_sum s S M (Nat.lt_succ_self S.natDegree)]
  refine VG.sum _ fun e _ => ?_
  by_cases he : e < E₀
  · rw [hz e he, zero_mul]; exact VG.zero _
  · have he' : (E₀ : ℚ) ≤ e := by exact_mod_cast (not_lt.mp he)
    by_cases he2 : e + 2 ≤ M.card + 2 * p
    · have := (hS e).mul (VG_locValue_X_pow_zero hp hs hM he2)
      exact this.mono (by linarith)
    · have := (hS e).mul (VG_locValue_X_pow hp hs hM e)
      have h1 : ((E₀ + 1 : ℕ) : ℚ) ≤ e := by exact_mod_cast (by omega : E₀ + 1 ≤ e)
      push_cast at h1
      exact this.mono (by linarith)

/-- The regular part `R / farProd` as a power series. -/
noncomputable def regPart (n p b : ℕ) (R : ℚ[X]) : PowerSeries ℚ :=
  (R : PowerSeries ℚ) * (farProd n p b : PowerSeries ℚ)⁻¹

lemma coeff_seriesPart {n b : ℕ} {A R : ℚ[X]} {E : ℕ}
    (hA : dissectNum p b A = C ((p : ℚ) ^ E) * X ^ E * R) (e : ℕ) :
    (seriesPart n p b A).coeff e = if e < truncOrder n then
      (if E ≤ e then (p : ℚ) ^ E * PowerSeries.coeff (e - E) (regPart n p b R) else 0) else 0 := by
  unfold seriesPart
  rw [PowerSeries.coeff_trunc, hA, series_eq]
  by_cases h : e < truncOrder n
  · rw [ite_eq_left h, ite_eq_left h, mul_assoc, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow_mul']
    unfold regPart
    split_ifs <;> simp
  · rw [ite_eq_right h, ite_eq_right h]

lemma seriesPart_coeff_VG [Fact p.Prime] {n b : ℕ} {A R : ℚ[X]} {E : ℕ}
    (hA : dissectNum p b A = C ((p : ℚ) ^ E) * X ^ E * R) (hK : ScaledPS p (regPart n p b R))
    (e : ℕ) : VG p ((seriesPart n p b A).coeff e) e := by
  rw [coeff_seriesPart hA]
  split_ifs with h1 h2
  · have := (VG_pow_nat (p := p) E).mul (hK (e - E))
    refine this.mono ?_
    rw [Nat.cast_sub h2]; linarith
  · exact VG.zero _
  · exact VG.zero _

lemma seriesPart_coeff_lt {n b : ℕ} {A R : ℚ[X]} {E : ℕ}
    (hA : dissectNum p b A = C ((p : ℚ) ^ E) * X ^ E * R) {e : ℕ} (he : e < E) :
    (seriesPart n p b A).coeff e = 0 := by
  rw [coeff_seriesPart hA]
  split_ifs with h1 h2
  · omega
  · rfl
  · rfl

lemma seriesPart_coeff_self {n b : ℕ} {A R : ℚ[X]} {E : ℕ}
    (hA : dissectNum p b A = C ((p : ℚ) ^ E) * X ^ E * R) (hE : E < truncOrder n) :
    (seriesPart n p b A).coeff E = (p : ℚ) ^ E * PowerSeries.coeff 0 (regPart n p b R) := by
  rw [coeff_seriesPart hA, ite_eq_left hE, ite_eq_left le_rfl, Nat.sub_self]

lemma regPart_scaled [Fact p.Prime] {n b : ℕ} (hb : b < p) {R : ℚ[X]} (hR : Scaled p R)
    (hR0 : IsUnitV p (R.coeff 0)) :
    ScaledPS p (regPart n p b R) ∧ IsUnitV p (PowerSeries.coeff 0 (regPart n p b R)) := by
  have hF := farProd_scaled (n := n) hb
  refine ⟨scaledPS_div hR hF.1 hF.2, ?_⟩
  unfold regPart
  rw [coeff_zero_div]
  exact hR0.mul hF.2.inv

lemma VG_rp [hp : Fact p.Prime] {r : ℚ} (hr : VG p r 0) : VG p (r * p) 1 := by
  have h1 : VG p (p : ℚ) 1 := by
    have := VG.primePow (p := p) 1
    simpa using this
  have := hr.mul h1
  simpa using this

end Zeta32.PrimeEdge

end
