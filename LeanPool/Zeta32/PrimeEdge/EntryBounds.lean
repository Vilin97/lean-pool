/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Gram
public import LeanPool.Zeta32.Arith.Local.Alloc

/-! the proof notes, §3 Lemma 4 bounds for the CRT-basis entries (`n = p - 1`),
and the slope (X-coefficient) bound of the Remark after Lemma 4.

Conventions of `Arith/Local`: `Adm p A e` bounds the Gauss valuation of `A(m + p x)` by `e (m
mod p)`;
the poles of `Lfun` are `-j`, `j ∈ [1, 5n]`, and the class `γ : ZMod p` of the pole `-j` corresponds
to the disc `d = (-γ).val = j mod p`. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

/-- `Adm` exponent of `Aent a c = φ_a φ_c D_{p-1}^4` at the class `γ` (disc `d = (-γ).val`):
`4 [d ≠ 0]` from `D_{p-1}^4` plus the basis multiplicities. -/
def entExp (p : ℕ) (a c : Idx p) (γ : ZMod p) : ℤ :=
  (if (-γ).val = 0 then 0 else 4) + (kmul p a (-γ).val : ℤ) + (kmul p c (-γ).val : ℤ)

/-- Number of poles `j ∈ [1, 5(p-1)]` with `j ≡ d (mod p)`. -/
def poleCount (p d : ℕ) : ℕ := if d = 0 then 4 else if d + 5 ≤ p then 5 else 4

lemma five_mul_lt_sq (hp : 5 ≤ p) : 5 * (p - 1) < p ^ 2 := by
  rw [sq]
  have := Nat.mul_le_mul_right p hp
  omega

/-- **S2-Adm.** Class-wise Gauss valuations of the entry numerator. -/
theorem Adm_Aent [Fact p.Prime] (hp : 5 ≤ p) (a c : Idx p) :
    Adm p (Aent p a c) (entExp p a c) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- each basis vector: exponent `kmul` at the disc `(-γ).val`
  have hB : ∀ a : Idx p, Adm p (crtBasis p a) (fun γ => (kmul p a (-γ).val : ℤ)) := by
    intro a
    have heq : crtBasis p a = ∏ b ∈ Finset.range p, (X + C (b : ℚ)) ^ kmul p a b := by
      rw [← Finset.mul_prod_erase (Finset.range p) _ (Finset.mem_range.mpr a.1.isLt)]
      unfold crtBasis kmul
      congr 1
      · simp
      · refine Finset.prod_congr rfl fun b hb => ?_
        rw [ite_eq_right (Finset.ne_of_mem_erase hb).symm]
    rw [heq]
    have h := Adm.prod (Finset.range p) (fun b => (X + C (b : ℚ)) ^ kmul p a b)
      (fun b γ => (kmul p a b : ℤ) * if (((-(b : ℤ)) : ℤ) : ZMod p) = γ then 1 else 0)
      (fun b _ => (Adm.X_add_C (p := p) b).pow _)
    refine h.mono fun γ => ?_
    have hmem := neg_val_lt (p := p) γ
    have hle := Finset.single_le_sum (f := fun b => (kmul p a b : ℤ) *
        if (((-(b : ℤ)) : ℤ) : ZMod p) = γ then 1 else 0)
      (fun b _ => by positivity) hmem
    refine le_trans (le_of_eq ?_) hle
    have : (((-(((-γ).val : ℕ) : ℤ)) : ℤ) : ZMod p) = γ := by
      rw [neg_class_iff]
      exact Nat.mod_eq_of_lt (ZMod.val_lt _)
    simp only [this, ite_true, mul_one]
  have hD := (Adm_D (p := p) (p - 1)).pow 4
  refine (((hB a).mul (hB c)).mul hD).mono fun γ => ?_
  simp only [Pi.add_apply]
  unfold entExp
  have hcard : (-γ).val ≠ 0 →
      1 ≤ ((Finset.Icc 1 (p - 1)).filter fun j : ℕ => j % p = (-γ).val).card := by
    intro h0
    apply Finset.card_pos.mpr
    refine ⟨(-γ).val, ?_⟩
    have hlt : (-γ).val < p := ZMod.val_lt _
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, Nat.mod_eq_of_lt hlt⟩
  split_ifs with h0
  · push_cast
    omega
  · have := hcard h0
    push_cast
    omega

/-- **S2-count (pure ℕ).** `#{j ∈ [1, 5(p-1)] : j ≡ d (mod p)}` is `4, 5, 4` for
`d = 0`, `1 ≤ d ≤ p-5`, `d ≥ p-4` (`j = d + p t`; cf. `Nat.Ico_filter_modEq_card`). -/
lemma card_residue_of_iff {d : ℕ} (hdp : d < p) (T : Finset ℕ)
    (hT : ∀ t, (1 ≤ d + p * t ∧ d + p * t ≤ 5 * (p - 1)) ↔ t ∈ T) :
    ((Finset.Icc 1 (5 * (p - 1))).filter fun j : ℕ => j % p = d).card = T.card := by
  have hp0 : 0 < p := by omega
  have himg : ((Finset.Icc 1 (5 * (p - 1))).filter fun j : ℕ => j % p = d) =
      T.image fun t => d + p * t := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨hj, hjd⟩
      have he := Nat.mod_add_div j p
      rw [hjd] at he
      refine ⟨j / p, (hT _).mp ?_, he⟩
      rw [he]; exact hj
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(hT t).mpr ht, ?_⟩
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdp]
  rw [himg, Finset.card_image_of_injective]
  intro t1 t2 h
  have h' : p * t1 = p * t2 := by simpa using h
  exact Nat.eq_of_mul_eq_mul_left hp0 h'

theorem card_residue_Icc (hp : 5 ≤ p) {d : ℕ} (hd : d < p) :
    ((Finset.Icc 1 (5 * (p - 1))).filter fun j : ℕ => j % p = d).card = poleCount p d := by
  unfold poleCount
  split_ifs with h0 hL
  · subst h0
    rw [card_residue_of_iff hd (Finset.Icc 1 4)]
    · rfl
    intro t
    rw [Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Nat.pos_of_ne_zero fun ht => by simp [ht] at h1, ?_⟩
      by_contra ht
      have := Nat.mul_le_mul_left p (show 5 ≤ t by omega)
      omega
    · rintro ⟨h1, h2⟩
      interval_cases t <;> omega
  · rw [card_residue_of_iff hd (Finset.range 5)]
    · rfl
    intro t
    rw [Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra ht
      have := Nat.mul_le_mul_left p (show 5 ≤ t by omega)
      omega
    · intro ht
      interval_cases t <;> omega
  · rw [card_residue_of_iff hd (Finset.range 4)]
    · rfl
    intro t
    rw [Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra ht
      have := Nat.mul_le_mul_left p (show 4 ≤ t by omega)
      omega
    · intro ht
      interval_cases t <;> omega

/-- Pole count per class (reduction adapted from `card_plc_Pl5` in Zeta32/Arith/Greedy.lean). -/
theorem card_plc_Pl5 [Fact p.Prime] (hp : 5 ≤ p) (γ : ZMod p) :
    (plc p (Pl5 (p - 1)) γ).card = poleCount p (-γ).val := by
  unfold plc Pl5
  rw [Finset.filter_image, Finset.card_image_of_injective _ neg_natCast_injective, card_class]
  exact card_residue_Icc hp (Finset.mem_range.mp (neg_val_lt γ))

/-- The Lemma 4 hypothesis of `Lfun_GV` in terms of `discExp`. -/
lemma entExp_hβ [Fact p.Prime] (hp : 5 ≤ p) (a c : Idx p) (β : ℚ)
    (hβ : ∀ d < p, β ≤ (discExp p a c d : ℚ)) (γ : ZMod p) :
    β + 2 ≤ (entExp p a c γ : ℚ) + (if γ = 0 then 1 else 0) -
      ((plc p (Pl5 (p - 1)) γ).card : ℚ) := by
  have hd : (-γ).val < p := Finset.mem_range.mp (neg_val_lt γ)
  have h := hβ _ hd
  rw [card_plc_Pl5 hp γ]
  have hz : γ = 0 ↔ (-γ).val = 0 := (neg_val_eq_zero_iff γ).symm
  unfold entExp poleCount
  unfold discExp colBase at h
  by_cases h0 : (-γ).val = 0
  · rw [ite_eq_left (hz.mpr h0)]
    simp only [h0, ite_true] at h ⊢
    push_cast at h ⊢
    linarith
  · rw [ite_eq_right (fun h' => h0 (hz.mp h'))]
    simp only [h0, ite_false] at h ⊢
    split_ifs at h ⊢ <;> push_cast at h ⊢ <;> linarith

/-- **Lemma 4 for one entry** (from `Lfun_GV`): `v(G_{ac}) ≥ min_d discExp a c d`. -/
theorem entry_GV [Fact p.Prime] (hp : 5 ≤ p) {r : ℚ} (hr : VG p r 0) (a c : Idx p) (β : ℚ)
    (hβ : ∀ d < p, β ≤ (discExp p a c d : ℚ)) : GV p (G r p a c) β := by
  have h := Lfun_GV hr (five_mul_lt_sq hp) (Adm_Aent hp a c) (Aent_natDegree hp a c) (β + 2)
    (entExp_hβ hp a c β hβ)
  rw [G_apply]
  simpa using h

/-- **S2c.** Entries between two different classes have excess `≥ 1/2` (no tie). -/
theorem cross_VG [Fact p.Prime] (hp : 5 ≤ p) {r : ℚ} (hr : VG p r 0) (a c : Idx p)
    (hac : a.1 ≠ c.1) : GV p (G r p a c) (rho p a + rho p c + 1/2) :=
  entry_GV hp hr a c _ (fun d _ => rho_add_half_le_discExp a c hac d)

/-- **S2a.** The coefficient of `X` has excess `≥ 3` (Remark after Lemma 4): it is
`Σ_j res_j · 2j`, and `VG_res` with `Adm_Aent`, `card_plc_Pl5` gives
`v(res_j · 2j) ≥ discExp a c d + 3` for the disc `d ≡ j`. -/
theorem slope_VG [Fact p.Prime] (hp : 5 ≤ p) (r : ℚ) (a c : Idx p) :
    VG p ((G r p a c).coeff 1) (rho p a + rho p c + 3) := by
  have hsep := sep_Pl5 (p := p) (five_mul_lt_sq hp)
  have hcoeff : (G r p a c).coeff 1 = ∑ j ∈ Finset.Icc 1 (5 * (p - 1)),
      resP (Aent p a c) (Pl5 (p - 1)) (-(j : ℤ)) * (2 * (j : ℚ)) := by
    rw [G_apply]; unfold Lfun
    rw [coeff_add, coeff_C_mul_X, coeff_C, ite_eq_left rfl, ite_eq_right (by omega), add_zero]
  rw [hcoeff]
  refine VG.sum _ fun j hj => ?_
  have hmem : -(j : ℤ) ∈ Pl5 (p - 1) := Finset.mem_image_of_mem _ hj
  have h1 := VG_res (Adm_Aent hp a c) (Pl5 (p - 1)) hsep hmem
  have h2 := entExp_hβ hp a c (rho p a + rho p c) (fun d _ => rho_add_le_discExp a c d)
    (((-(j : ℤ)) : ℤ) : ZMod p)
  by_cases hpj : p ∣ j
  · rw [ite_eq_left ((class_neg_eq_zero_iff j).mpr hpj)] at h2
    have h2j : VG p (2 * (j : ℚ)) 1 := by
      have := VG_int_one (p := p) (z := 2 * (j : ℤ)) (dvd_mul_of_dvd_right (by exact_mod_cast
        hpj) _)
      simpa using this
    exact (h1.mul h2j).mono (by linarith)
  · rw [ite_eq_right (fun h => hpj ((class_neg_eq_zero_iff j).mp h))] at h2
    have h2j : VG p (2 * (j : ℚ)) 0 := by simpa using VG.natCast (p := p) (2 * j)
    exact (h1.mul h2j).mono (by linarith)

lemma Lfun_coeff_of_two_le (r : ℚ) (n : ℕ) (A : ℚ[X]) {k : ℕ} (hk : 2 ≤ k) :
    (Lfun r n A).coeff k = 0 := by
  unfold Lfun
  rw [coeff_add, coeff_C_mul_X, coeff_C, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

lemma GV_Lfun_sub_C {r : ℚ} {n : ℕ} {A : ℚ[X]} {q β : ℚ}
    (h0 : VG p ((Lfun r n A).coeff 0 - q) β) (h1 : VG p ((Lfun r n A).coeff 1) β) :
    GV p (Lfun r n A - C q) β := by
  intro k
  rcases k with _ | _ | k
  · simpa [coeff_sub, coeff_C] using h0
  · simpa [coeff_sub, coeff_C] using h1
  · rw [coeff_sub, Lfun_coeff_of_two_le r n A (by omega), coeff_C, ite_eq_right (by omega),
    sub_zero]
    exact VG.zero _

end Zeta32.PrimeEdge

end
