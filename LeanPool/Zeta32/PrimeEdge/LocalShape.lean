/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Disc.Core

/-! **S2b-2 / S2b-3**: the proof notes, §6 "Local shapes" and "Scaling", for the
entries of one class block, on its own disc and on the other discs (`n = p - 1`).

Local shape of `seriesPart / nearProd` on the disc `b` for `a = ⟨b, i⟩`, `c = ⟨b, k⟩`
(`κ(u) = (unit) (1 + O(p u))`, `κ(0) ≡ w_b`):
* low (`1 ≤ b ≤ p-5`, `nearSet = {0,…,4}`): `p^{4+i+k} u^{i+k} r_L(u) κ(u)`;
* high (`p-4 ≤ b`, `nearSet = {0,…,3}`): `p^{4+i+k} u^{i+k} r_H(u) κ(u)`;
* zero (`b = 0`, `nearSet = {1,…,4}`): `p^{1+i+k} u^{i+k} r_0(u) κ(u)`.
With the `p^{-|near|}` of `discLocal` and the `p^{-2}` of Corollary 2 the power is `p^{c_b+i+k}`.
Modulo one more power of `p` the local functional is `V⁰` (the `2rp` moments are `≡ 0`, a moment of
valuation `-1` needs degree `≥ 2p-1`, and each extra power of `p` in `κ` raises the degree by at
most one). Expected unit weight (hint only, not checked; not needed in the statement):
`w_b = (-b)·∏_{b'≠b}(b'-b)^{2m_{b'}}·∏_{1≤i'≤p-1, i'≠b}(i'-b)^4 / ∏_{j∈[1,5(p-1)], j≢b}(j-b)`
for `b ≠ 0`, and the same without the factor `(-b)` for `b = 0`.

Proof (files in `Disc/`): `Factor` writes `dissectNum` on the disc `d` as `p^E u^E R(u)` with `R`
scaled (`u^e`-coefficient of valuation `≥ e`) and `R(0)` a unit, so the coefficient of `u^e` in
`seriesPart` vanishes for `e < E` and has valuation `≥ e` (`Core`). `Core.VG_locValue_scaled` is
Lemma 3 for such numerators (`LocValue`, `Bernoulli`: von Staudt). Other disc: `E - |near| - 2 ≥ 2`.
Own disc: `w_b = K(0)` for `K = R_b / farProd`; subtracting `p^E K(0) u^E` leaves a numerator
vanishing to order `E + 1`, and `V_{rp}(u^E) ≡ V⁰(u^E) mod p` (degree `E ≤ |near| + p - 2`). -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

lemma card_1234 : ({1, 2, 3, 4} : Finset ℕ).card = 4 := by decide
lemma card_01234 : ({0, 1, 2, 3, 4} : Finset ℕ).card = 5 := by decide
lemma card_0123 : ({0, 1, 2, 3} : Finset ℕ).card = 4 := by decide

/-- Exponent bookkeeping on another disc `d`: `E = 2 m_d + (1 or 4)`, `|near| ∈ {4, 5}`. -/
lemma other_data [Fact p.Prime] (hp : 5 ≤ p) {d : ℕ} (hd : d < p) (a c : Idx p) (hac : a.1 = c.1)
    (hdb : d ≠ a.1.val) :
    ∃ E : ℕ, ∃ R : ℚ[X], dissectNum p d (Aent p a c) = C ((p : ℚ) ^ E) * X ^ E * R ∧
      Scaled p R ∧ IsUnitV p (R.coeff 0) ∧
      E + 2 ≤ (nearSet (p - 1) p d).card + 2 * p ∧ (nearSet (p - 1) p d).card + 4 ≤ E := by
  obtain ⟨R, hR, hRs, hRu⟩ := good_other hd a c hac hdb
  refine ⟨_, R, hR, hRs, hRu, ?_⟩
  by_cases h0 : d = 0
  · subst h0
    have hm : mult p 0 = 4 := by simp [mult]
    rw [nearSet_zero hp, card_1234, hm, ite_eq_left rfl]
    omega
  · by_cases hL : d + 5 ≤ p
    · have hm : mult p d = 3 := by simp [mult, h0, hL]
      rw [nearSet_low (by omega) hL, card_01234, hm, ite_eq_right h0]
      omega
    · have hm : mult p d = 2 := by simp [mult, h0, hL]
      rw [nearSet_high hp (by omega) hd (by omega), card_0123, hm, ite_eq_right h0]
      omega

/-- Exponent bookkeeping on the own disc `b`, and `blockMoment` as `V⁰(u^E / nearProd)`. -/
lemma same_data (hp : 5 ≤ p) {b i k : ℕ} (hb : b < p) (hi : i < mult p b) (hk : k < mult p b) :
    blockMoment p b (i + k) = locValue 0 (X ^ (ownExp b + i + k)) (nearSet (p - 1) p b) ∧
    colBase p b + i + k = ((ownExp b + i + k : ℕ) : ℤ) - 2 - (nearSet (p - 1) p b).card ∧
    ownExp b + i + k + 1 + 2 ≤ (nearSet (p - 1) p b).card + 2 * p ∧
    ownExp b + i + k + 2 ≤ (nearSet (p - 1) p b).card + p ∧
    ownExp b + i + k < truncOrder (p - 1) := by
  unfold truncOrder
  by_cases h0 : b = 0
  · subst h0
    have hm : mult p 0 = 4 := by simp [mult]
    have hoe : ownExp 0 = 1 := by simp [ownExp]
    rw [hm] at hi hk
    rw [nearSet_zero hp, card_1234, hoe]
    refine ⟨?_, ?_, by omega, by omega, by omega⟩
    · rw [blockMoment, ite_eq_left rfl, show 1 + i + k = i + k + 1 by ring]
    · rw [colBase, ite_eq_left rfl]; push_cast; ring
  · have hoe : ownExp b = 4 := by simp [ownExp, h0]
    by_cases hL : b + 5 ≤ p
    · have hm : mult p b = 3 := by simp [mult, h0, hL]
      rw [hm] at hi hk
      rw [nearSet_low (by omega) hL, card_01234, hoe]
      refine ⟨?_, ?_, by omega, by omega, by omega⟩
      · rw [blockMoment, ite_eq_right h0, ite_eq_left hL, show 4 + i + k = (i + k + 3) + 1 by
        ring, pow_succ' (X : ℚ[X]) (i + k + 3),
          locValue_X_mul_insert_zero (M := {1, 2, 3, 4}) _ _ (by decide)]
      · rw [colBase, ite_eq_right h0, ite_eq_left hL]; push_cast; ring
    · have hm : mult p b = 2 := by simp [mult, h0, hL]
      rw [hm] at hi hk
      rw [nearSet_high hp (by omega) hb (by omega), card_0123, hoe]
      refine ⟨?_, ?_, by omega, by omega, by omega⟩
      · rw [blockMoment, ite_eq_right h0, ite_eq_right hL, show 4 + i + k = (i + k + 3) + 1 by
        ring, pow_succ' (X : ℚ[X]) (i + k + 3),
          locValue_X_mul_insert_zero (M := {1, 2, 3}) _ _ (by decide)]
      · rw [colBase, ite_eq_right h0, ite_eq_right hL]; push_cast; ring

/-- The own-disc estimate, abstractly: `P` has `u^e`-coefficients of valuation `≥ e`, vanishing
below `E`, with `u^E`-coefficient `p^E K₀`. -/
lemma same_core [Fact p.Prime] (hp : 5 ≤ p) {s : ℚ} (hs : VG p s 1) {N : Finset ℕ}
    (hN : N ⊆ Finset.range 5) {P : ℚ[X]} {E : ℕ} {K0 : ℚ} (hK0 : VG p K0 0)
    (hPc : ∀ e, VG p (P.coeff e) e) (hPz : ∀ e < E, P.coeff e = 0)
    (hPE : P.coeff E = (p : ℚ) ^ E * K0) (hE3 : E + 1 + 2 ≤ N.card + 2 * p)
    (hE2 : E + 2 ≤ N.card + p) {c : ℤ} (hc : c = (E : ℤ) - 2 - N.card) {B : ℚ}
    (hB : B = locValue 0 (X ^ E) N) :
    VG p ((p : ℚ) ^ (-2 : ℤ) * ((p : ℚ) ^ (-(N.card : ℤ)) * locValue s P N) -
      (p : ℚ) ^ c * K0 * B) ((c : ℚ) + 1) := by
  obtain ⟨S, hSdef⟩ : ∃ S : ℚ[X], S = P - C ((p : ℚ) ^ E * K0) * X ^ E := ⟨_, rfl⟩
  have hS : ∀ e, VG p (S.coeff e) e := fun e => by
    rw [hSdef, coeff_sub, coeff_C_mul_X_pow]
    split_ifs with he
    · rw [he, hPE, sub_self]; exact VG.zero _
    · rw [sub_zero]; exact hPc e
  have hSz : ∀ e < E + 1, S.coeff e = 0 := fun e he => by
    rw [hSdef, coeff_sub, coeff_C_mul_X_pow]
    split_ifs with h
    · rw [h, hPE, sub_self]
    · rw [hPz e (by omega), sub_zero]
  have hL := VG_locValue_scaled hp hs hN hS hSz hE3
  have hD := VG_locValue_X_pow_sub hp hs hN hE2
  have hsplit : locValue s P N = locValue s S N + ((p : ℚ) ^ E * K0) * locValue s (X ^ E) N := by
    rw [← locValue_C_mul, ← locValue_add, hSdef, sub_add_cancel]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpow : (p : ℚ) ^ c = (p : ℚ) ^ (-2 : ℤ) * ((p : ℚ) ^ (-(N.card : ℤ)) * (p : ℚ) ^ E) := by
    rw [hc, ← zpow_natCast, ← zpow_add₀ hp0, ← zpow_add₀ hp0]
    congr 1
    ring
  have key : (p : ℚ) ^ (-2 : ℤ) * ((p : ℚ) ^ (-(N.card : ℤ)) * locValue s P N) -
      (p : ℚ) ^ c * K0 * B =
      (p : ℚ) ^ (-2 : ℤ) * ((p : ℚ) ^ (-(N.card : ℤ)) * locValue s S N) +
        (p : ℚ) ^ c * (K0 * (locValue s (X ^ E) N - locValue 0 (X ^ E) N)) := by
    rw [hsplit, hB, hpow]
    ring
  rw [key]
  refine VG.add ?_ ?_
  · refine ((VG.primePow (p := p) (-2)).mul
      ((VG.primePow (p := p) (-(N.card : ℤ))).mul hL)).mono ?_
    rw [hc]
    push_cast
    linarith
  · refine ((VG.primePow (p := p) c).mul (hK0.mul hD)).mono ?_
    linarith

lemma rho_le_half (a : Idx p) : rho p a ≤ 1 / 2 := by
  unfold rho
  have h : (level p a : ℚ) ≤ 1 := by exact_mod_cast level_le_one a
  linarith

/-- **S2b-2 (own disc).** For two vectors of the same class `b`, the disc-`b` local term is
`p^{c_b+i+k} · w_b · V⁰(u^{i+k} r_type)` modulo `p^{c_b+i+k+1}`, with `p`-unit weights `w_b`
depending only on the class. -/
theorem disc_same_class [Fact p.Prime] (hp7 : 7 ≤ p) {r : ℚ} (hr : VG p r 0) :
    ∃ w : ℕ → ℚ, (∀ b < p, w b ≠ 0 ∧ padicValRat p (w b) = 0) ∧
      ∀ a c : Idx p, a.1 = c.1 →
        VG p ((p : ℚ) ^ (-2 : ℤ) * discLocal r (p - 1) p a.1.val (Aent p a c) -
            (p : ℚ) ^ (colBase p a.1.val + a.2.val + c.2.val) * w a.1.val *
              blockMoment p a.1.val (a.2.val + c.2.val))
          (rho p a + rho p c + 1) := by
  have hp5 : 5 ≤ p := by omega
  classical
  let Rb : ℕ → ℚ[X] := fun b =>
    if hb : b < p then Classical.choose (dissect_same (p := p) hb) else 1
  have hRb : ∀ b (hb : b < p), Scaled p (Rb b) ∧ IsUnitV p ((Rb b).coeff 0) ∧
      ∀ a c : Idx p, a.1.val = b → c.1.val = b →
        dissectNum p b (Aent p a c) =
          C ((p : ℚ) ^ (ownExp b + a.2.val + c.2.val)) * X ^ (ownExp b + a.2.val + c.2.val) *
            Rb b := by
    intro b hb
    simp only [Rb, dite_eq_left hb]
    exact Classical.choose_spec (dissect_same hb)
  refine ⟨fun b => PowerSeries.coeff 0 (regPart (p - 1) p b (Rb b)), fun b hb => ?_,
    fun a c hac => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hRb b hb
    exact (regPart_scaled hb h1 h2).2
  · have hb : a.1.val < p := a.1.isLt
    have hcb : c.1.val = a.1.val := by rw [hac]
    have hk : c.2.val < mult p a.1.val := by
      have h := c.2.isLt
      have e : mult p c.1.val = mult p a.1.val := by rw [hac]
      omega
    obtain ⟨hRs, hRu, hR⟩ := hRb a.1.val hb
    have hdis := hR a c rfl hcb
    obtain ⟨hK, hK0⟩ := regPart_scaled (n := p - 1) hb hRs hRu
    obtain ⟨hBM, hcol, hE3, hE2, hET⟩ := same_data hp5 hb a.2.isLt hk
    unfold discLocal
    rw [rho_add_of_same a c hac]
    exact same_core hp5 (VG_rp hr) (nearSet_subset hb) hK0.VG (seriesPart_coeff_VG hdis hK)
      (fun e he => seriesPart_coeff_lt hdis he) (seriesPart_coeff_self hdis hET) hE3 hE2 hcol hBM

/-- **S2b-3 (other discs).** For two vectors of the same class `b`, every other disc `d ≠ b`
contributes with excess `≥ 1`: by Lemma 3 (local integrality; the degree condition holds since at
most `10` near zeros occur and `10 ≤ |near| + 2p - 2`) the term has valuation
`≥ c_d + 2 m_d ≥ 2 ≥ ρ_a + ρ_c + 1`. -/
theorem disc_other_class [Fact p.Prime] (hp7 : 7 ≤ p) {r : ℚ} (hr : VG p r 0) (a c : Idx p)
    (hac : a.1 = c.1) (d : ℕ) (hd : d < p) (hdb : d ≠ a.1.val) :
    VG p ((p : ℚ) ^ (-2 : ℤ) * discLocal r (p - 1) p d (Aent p a c))
      (rho p a + rho p c + 1) := by
  have hp5 : 5 ≤ p := by omega
  obtain ⟨E, R, hdis, hRs, hRu, hE1, hE2⟩ := other_data hp5 hd a c hac hdb
  have hK := (regPart_scaled (n := p - 1) hd hRs hRu).1
  have hL := VG_locValue_scaled hp5 (VG_rp hr) (nearSet_subset hd) (seriesPart_coeff_VG hdis hK)
    (fun e he => seriesPart_coeff_lt hdis he) hE1
  unfold discLocal
  refine ((VG.primePow (p := p) (-2)).mul
    ((VG.primePow (p := p) (-((nearSet (p - 1) p d).card : ℤ))).mul hL)).mono ?_
  have hra := rho_le_half a
  have hrc := rho_le_half c
  have hE2' : ((nearSet (p - 1) p d).card : ℚ) + 4 ≤ (E : ℚ) := by exact_mod_cast hE2
  push_cast
  linarith

end Zeta32.PrimeEdge

end
