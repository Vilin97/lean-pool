/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffPeriodSeparation

/-!
# Period separation for the corrected cross-one-off block, without a length
hypothesis

`crossOneOff_cutoff_le_torsionOrder` (`Bananas/CrossOneOffPeriodSeparation.lean`)
proves `crossOneOffCutoff g (B.length beta) ≤ k` for the near-opposite marking
`(v_{α,1}, v_{β,n_β-1})` only under the extra hypothesis
`hBetaLong : g + 1 ≤ B.length beta`.  This file removes that hypothesis: the
sharp bound holds for every torsion witness whenever the two strand lengths
are not *both* equal to two.

The argument (`Bananas/FORMALIZATION_NOTES.md`, "the short-strand period separation is
provable — closed-form torsion order") extracts from the slope framework of
`Bananas/BananaTorsionSlopes.lean` the exact identity `m = p + r + Σ_γ q_γ`
where `p := d/a`, `r := d/b` (`d` a common multiple of the two marked
lengths) and each `q_γ` a common-multiple share of `|rise|` over the other
strands, then a ray/primitivity argument on the two integers
`D := lcm(a,b) - a/gcd(a,b) - b/gcd(a,b)` and `E := L + Σ_γ L/n_γ`
(`L := lcm` of the other lengths).
-/

@[expose] public section

namespace Bananas

open Utilities
open scoped BigOperators

/-! ## Generic finite-sum helpers -/

private theorem sum_ge_card_of_pos {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hpos : ∀ x ∈ s, 0 < f x) : (s.card : ℤ) ≤ ∑ x ∈ s, f x := by
  calc (s.card : ℤ) = ∑ _x ∈ s, (1 : ℤ) := by simp
    _ ≤ ∑ x ∈ s, f x :=
      Finset.sum_le_sum (fun x hx => by have := hpos x hx; omega)

private theorem sum_split_doubleErase {g : ℕ} (alpha beta : Fin (g + 1))
    (hab : alpha ≠ beta) (f : Fin (g + 1) → ℤ) :
    ∑ x, f x = f alpha + f beta +
      ∑ x ∈ (Finset.univ.erase alpha).erase beta, f x := by
  have h1 : f alpha + ∑ x ∈ Finset.univ.erase alpha, f x = ∑ x, f x :=
    Finset.add_sum_erase _ _ (Finset.mem_univ alpha)
  have hbmem : beta ∈ Finset.univ.erase alpha :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ beta⟩
  have h2 : f beta + ∑ x ∈ (Finset.univ.erase alpha).erase beta, f x =
      ∑ x ∈ Finset.univ.erase alpha, f x :=
    Finset.add_sum_erase _ _ hbmem
  linarith [h1, h2]

private theorem card_doubleErase {g : ℕ} (alpha beta : Fin (g + 1))
    (hab : alpha ≠ beta) :
    ((Finset.univ.erase alpha).erase beta).card = g - 1 := by
  have h1 : (Finset.univ.erase alpha).card = g := by simp
  have hbmem : beta ∈ Finset.univ.erase alpha :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ beta⟩
  have h2 := Finset.card_erase_of_mem hbmem
  omega

/-! ## Pure arithmetic lemmas -/

/-- `D := lcm(a,b) - a' - b' ≥ 1` whenever `a, b ≥ 2` are not both `2`,
where `a' := a / gcd(a,b)`, `b' := b / gcd(a,b)`. -/
private theorem crossOneOff_D_pos (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hnb : ¬ (a = 2 ∧ b = 2)) :
    a / Nat.gcd a b + b / Nat.gcd a b + 1 ≤ Nat.lcm a b := by
  set e := Nat.gcd a b with he
  have hepos : 0 < e := Nat.gcd_pos_of_pos_left _ (by omega)
  set a' := a / e with ha'
  set b' := b / e with hb'
  have hae : e * a' = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hbe : e * b' = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hlcm : e * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
  have hcase : 3 ≤ a ∨ 3 ≤ b := by omega
  have hprod : 2 ≤ (a - 1) * (b - 1) := by
    rcases hcase with h | h
    · have h1 : 2 ≤ a - 1 := by omega
      have h2 : 1 ≤ b - 1 := by omega
      calc 2 = 2 * 1 := by ring
        _ ≤ (a - 1) * (b - 1) := Nat.mul_le_mul h1 h2
    · have h1 : 1 ≤ a - 1 := by omega
      have h2 : 2 ≤ b - 1 := by omega
      calc 2 = 1 * 2 := by ring
        _ ≤ (a - 1) * (b - 1) := Nat.mul_le_mul h1 h2
  have hidZ : (e : ℤ) * ((Nat.lcm a b : ℤ) - (a' : ℤ) - (b' : ℤ)) =
      ((a : ℤ) - 1) * ((b : ℤ) - 1) - 1 := by
    have hae' : (e : ℤ) * (a' : ℤ) = (a : ℤ) := by exact_mod_cast hae
    have hbe' : (e : ℤ) * (b' : ℤ) = (b : ℤ) := by exact_mod_cast hbe
    have hlcm' : (e : ℤ) * (Nat.lcm a b : ℤ) = (a : ℤ) * (b : ℤ) := by
      exact_mod_cast hlcm
    nlinarith [hae', hbe', hlcm']
  have hprodZ : (2 : ℤ) ≤ ((a : ℤ) - 1) * ((b : ℤ) - 1) := by
    zify [show 1 ≤ a by omega, show 1 ≤ b by omega] at hprod
    exact hprod
  have hepos' : (0 : ℤ) < (e : ℤ) := by exact_mod_cast hepos
  have hDnonneg : (0 : ℤ) ≤ (Nat.lcm a b : ℤ) - (a' : ℤ) - (b' : ℤ) := by
    nlinarith [hidZ, hprodZ, hepos']
  have hDZ : (1 : ℤ) ≤ (Nat.lcm a b : ℤ) - (a' : ℤ) - (b' : ℤ) := by
    rcases (by omega : (Nat.lcm a b : ℤ) - (a' : ℤ) - (b' : ℤ) = 0 ∨
        1 ≤ (Nat.lcm a b : ℤ) - (a' : ℤ) - (b' : ℤ)) with h0 | h1
    · exfalso; rw [h0] at hidZ; nlinarith [hidZ, hprodZ, hepos']
    · exact h1
  have : (a' : ℤ) + (b' : ℤ) + 1 ≤ (Nat.lcm a b : ℤ) := by linarith
  exact_mod_cast this

/-- The polynomial inequality feeding the second (short-block) case of the
closed-form torsion bound. -/
private theorem crossOneOff_poly_ineq (a' b' bm1 g : ℤ) (ha' : 1 ≤ a')
    (hb' : 1 ≤ b') (hbm1 : 1 ≤ bm1) (hg : a' * bm1 ≤ g) :
    (a' * bm1 - b') * (g + bm1) ≤ g * (a' + b') * bm1 := by
  have hb'0 : (0 : ℤ) ≤ b' := by linarith
  have hbm10 : (0 : ℤ) ≤ bm1 := by linarith
  have ha'0 : (0 : ℤ) ≤ a' := by linarith
  have hb'10 : (0 : ℤ) ≤ b' - 1 := by linarith
  have hgea'bm1 : (0 : ℤ) ≤ g - a' * bm1 := by linarith
  have T1 : 0 ≤ b' * (bm1 + 1) * (g - a' * bm1) :=
    mul_nonneg (mul_nonneg hb'0 (by linarith)) hgea'bm1
  have T2 : 0 ≤ bm1 * (a' * (bm1 + 1)) * (b' - 1) :=
    mul_nonneg (mul_nonneg hbm10 (mul_nonneg ha'0 (by linarith))) hb'10
  have T3 : 0 ≤ bm1 * (a' + b') := mul_nonneg hbm10 (by linarith)
  nlinarith [T1, T2, T3]

/-- The "hard" case of the closed-form torsion bound: when the reduced
lengths `a' + b'` do not already exceed `F := g / (b - 1)`, the ray identity
`t * D = w * E` forces `t * (a' + b') ≥ F + 1`. -/
private theorem crossOneOff_case2_bound
    (a' b' bm1 g F D t w E : ℕ) (ha' : 1 ≤ a') (hb' : 1 ≤ b')
    (hbm1 : 1 ≤ bm1) (hF : F = g / bm1) (hcase : a' + b' ≤ F)
    (ht1 : 1 ≤ t) (hw1 : 1 ≤ w) (hD1 : 1 ≤ D)
    (hDdef : (D : ℤ) = (a' : ℤ) * (bm1 : ℤ) - (b' : ℤ)) (hE : g ≤ E)
    (htD : t * D = w * E) :
    F + 1 ≤ t * (a' + b') := by
  have hFmul : F * bm1 ≤ g := by rw [hF]; exact Nat.div_mul_le_self g bm1
  have hgge : (a' + b') * bm1 ≤ g :=
    le_trans (Nat.mul_le_mul_right bm1 hcase) hFmul
  have hFsucc : (F + 1) * bm1 ≤ g + bm1 := by
    have : (F + 1) * bm1 = F * bm1 + bm1 := by ring
    omega
  have htDgeE : E ≤ t * D := by
    calc E ≤ w * E := Nat.le_mul_of_pos_left E hw1
      _ = t * D := htD.symm
  have htDgeg : g ≤ t * D := le_trans hE htDgeE
  have hggeZ : ((a' : ℤ) + b') * (bm1 : ℤ) ≤ (g : ℤ) := by exact_mod_cast hgge
  have hFsuccZ : ((F : ℤ) + 1) * (bm1 : ℤ) ≤ (g : ℤ) + (bm1 : ℤ) := by
    exact_mod_cast hFsucc
  have htDggZ : (g : ℤ) ≤ (t : ℤ) * (D : ℤ) := by exact_mod_cast htDgeg
  have ha'Z : (1 : ℤ) ≤ (a' : ℤ) := by exact_mod_cast ha'
  have hb'Z : (1 : ℤ) ≤ (b' : ℤ) := by exact_mod_cast hb'
  have hbm1Z : (1 : ℤ) ≤ (bm1 : ℤ) := by exact_mod_cast hbm1
  have hpoly := crossOneOff_poly_ineq (a' : ℤ) (b' : ℤ) (bm1 : ℤ) (g : ℤ)
    ha'Z hb'Z hbm1Z (by nlinarith [hggeZ, hb'Z, hbm1Z])
  have hDZ1 : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD1
  have htZ1 : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast ht1
  have hchain : (D : ℤ) * ((F : ℤ) + 1) * (bm1 : ℤ) ≤
      (t : ℤ) * ((a' : ℤ) + (b' : ℤ)) * (D : ℤ) * (bm1 : ℤ) := by
    have step1 : (D : ℤ) * ((F : ℤ) + 1) * (bm1 : ℤ) ≤
        (D : ℤ) * ((g : ℤ) + (bm1 : ℤ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hFsuccZ (le_trans zero_le_one hDZ1)]
    have step2 : (D : ℤ) * ((g : ℤ) + (bm1 : ℤ)) ≤
        (g : ℤ) * ((a' : ℤ) + (b' : ℤ)) * (bm1 : ℤ) := by
      rw [hDdef]; exact hpoly
    have step3 : (g : ℤ) * ((a' : ℤ) + (b' : ℤ)) * (bm1 : ℤ) ≤
        (t : ℤ) * (D : ℤ) * ((a' : ℤ) + (b' : ℤ)) * (bm1 : ℤ) := by
      have hnn : (0 : ℤ) ≤ ((a' : ℤ) + (b' : ℤ)) * (bm1 : ℤ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right htDggZ hnn]
    calc (D : ℤ) * ((F : ℤ) + 1) * (bm1 : ℤ) ≤ (D : ℤ) * ((g : ℤ) + (bm1 : ℤ)) := step1
      _ ≤ (g : ℤ) * ((a' : ℤ) + (b' : ℤ)) * (bm1 : ℤ) := step2
      _ ≤ (t : ℤ) * (D : ℤ) * ((a' : ℤ) + (b' : ℤ)) * (bm1 : ℤ) := step3
      _ = (t : ℤ) * ((a' : ℤ) + (b' : ℤ)) * (D : ℤ) * (bm1 : ℤ) := by ring
  have hDb1pos : (0 : ℤ) < (D : ℤ) * (bm1 : ℤ) := by nlinarith [hDZ1, hbm1Z]
  have hfinalZ : (F : ℤ) + 1 ≤ (t : ℤ) * ((a' : ℤ) + (b' : ℤ)) := by
    have hrw1 : (D : ℤ) * ((F : ℤ) + 1) * (bm1 : ℤ) =
        ((F : ℤ) + 1) * ((D : ℤ) * (bm1 : ℤ)) := by ring
    have hrw2 : (t : ℤ) * ((a' : ℤ) + (b' : ℤ)) * (D : ℤ) * (bm1 : ℤ) =
        ((t : ℤ) * ((a' : ℤ) + (b' : ℤ))) * ((D : ℤ) * (bm1 : ℤ)) := by ring
    rw [hrw1, hrw2] at hchain
    exact le_of_mul_le_mul_right hchain hDb1pos
  exact_mod_cast hfinalZ

/-! ## The Banana-specific extraction and assembly -/
private theorem crossOneOff_otherStrand_data
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1)) (hab : alpha ≠ beta)
    (rise : ℤ) (slope : Fin (g + 1) → ℤ) (hrise_neg : rise < 0)
    (hsum : ∑ γ, slope γ = 0)
    (hOther : ∀ γ, γ ≠ alpha → γ ≠ beta → (B.length γ : ℤ) * slope γ = rise) :
    ∃ L w T : ℕ, 0 < L ∧ 1 ≤ w ∧ g - 1 ≤ T ∧
      (L : ℤ) * (w : ℤ) = -rise ∧ slope alpha + slope beta = (w : ℤ) * (T : ℤ) := by
  set s2 := (Finset.univ.erase alpha).erase beta with hs2_def
  have hs2card : s2.card = g - 1 := card_doubleErase alpha beta hab
  have hOtherMem : ∀ γ ∈ s2, γ ≠ alpha ∧ γ ≠ beta := by
    intro γ hγ
    have h1 := Finset.mem_erase.mp hγ
    have h2 := Finset.mem_erase.mp h1.2
    exact ⟨h2.1, h1.1⟩
  -- the double-erase splitting of the zero-sum equation
  have hsumSplit : slope alpha + slope beta + ∑ γ ∈ s2, slope γ = 0 := by
    have := sum_split_doubleErase alpha beta hab slope
    rw [hs2_def]
    linarith [this, hsum]
  -- the "other strands" divisor data
  set nRise : ℕ := (-rise).toNat with hnRise_def
  have hnRiseZ : (nRise : ℤ) = -rise := Int.toNat_of_nonneg (by omega)
  have hDvdOther : ∀ γ ∈ s2, B.length γ ∣ nRise := by
    intro γ hγ
    obtain ⟨hγα, hγβ⟩ := hOtherMem γ hγ
    have heq := hOther γ hγα hγβ
    have hZ : (B.length γ : ℤ) ∣ (nRise : ℤ) := by
      rw [hnRiseZ]
      exact ⟨-slope γ, by rw [mul_neg, heq]⟩
    exact_mod_cast hZ
  set L : ℕ := s2.lcm (fun γ => B.length γ) with hL_def
  have hLpos : 0 < L := by
    have hne : L ≠ 0 := by
      rw [hL_def, Finset.lcm_ne_zero_iff]
      intro γ _hγ
      exact (B.length_pos γ).ne'
    omega
  have hDvdL : ∀ γ ∈ s2, B.length γ ∣ L := by
    intro γ hγ; rw [hL_def]; exact Finset.dvd_lcm hγ
  have hLdvdNRise : L ∣ nRise := by
    rw [hL_def]; exact Finset.lcm_dvd hDvdOther
  set w : ℕ := nRise / L with hw_def
  have hwLeq : L * w = nRise := Nat.mul_div_cancel' hLdvdNRise
  have hnRisePos : 0 < nRise := by
    have : (0 : ℤ) < (nRise : ℤ) := by rw [hnRiseZ]; omega
    exact_mod_cast this
  have hw1 : 1 ≤ w := by
    rcases Nat.eq_zero_or_pos w with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at hwLeq; omega
    · exact h1
  set T : ℕ := ∑ γ ∈ s2, (L / B.length γ) with hT_def
  have hquot_ge1 : ∀ γ ∈ s2, 1 ≤ L / B.length γ := by
    intro γ hγ
    have hdvd := hDvdL γ hγ
    have heq : B.length γ * (L / B.length γ) = L := Nat.mul_div_cancel' hdvd
    rcases Nat.eq_zero_or_pos (L / B.length γ) with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at heq; omega
    · exact h1
  have hTge : g - 1 ≤ T := by
    have h1 : ∑ _γ ∈ s2, 1 ≤ ∑ γ ∈ s2, (L / B.length γ) :=
      Finset.sum_le_sum hquot_ge1
    simpa [hT_def, hs2card] using h1
  have hslope_eq : ∀ γ ∈ s2, slope γ = -(w : ℤ) * ((L / B.length γ : ℕ) : ℤ) := by
    intro γ hγ
    obtain ⟨hγα, hγβ⟩ := hOtherMem γ hγ
    have heq := hOther γ hγα hγβ
    have hlenpos : (0 : ℤ) < B.length γ := by exact_mod_cast B.length_pos γ
    have hdvd := hDvdL γ hγ
    have hquot : (B.length γ : ℤ) * ((L / B.length γ : ℕ) : ℤ) = (L : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hdvd
    have hLw : (L : ℤ) * (w : ℤ) = (nRise : ℤ) := by exact_mod_cast hwLeq
    have hriseval : rise = -(nRise : ℤ) := by rw [hnRiseZ]; ring
    apply mul_left_cancel₀ (ne_of_gt hlenpos)
    rw [heq, hriseval, ← hLw, ← hquot]
    ring
  have hSslope : ∑ γ ∈ s2, slope γ = -(w : ℤ) * (T : ℤ) := by
    have heq : ∑ γ ∈ s2, slope γ =
        ∑ γ ∈ s2, (-(w : ℤ) * ((L / B.length γ : ℕ) : ℤ)) :=
      Finset.sum_congr rfl hslope_eq
    rw [heq, ← Finset.mul_sum]
    congr 1
    rw [hT_def]; push_cast; ring
  have hsplitSum : slope alpha + slope beta = (w : ℤ) * (T : ℤ) := by
    have := hsumSplit; rw [hSslope] at this; linarith [this]
  refine ⟨L, w, T, hLpos, hw1, hTge, ?_, hsplitSum⟩
  exact (by exact_mod_cast hwLeq : (L : ℤ) * (w : ℤ) = (nRise : ℤ)).trans hnRiseZ

private theorem crossOneOff_cutoff_of_negativeRise
    (g a b m : ℕ) (rise slopeAlpha slopeBeta : ℤ)
    (hAlpha : 1 < a) (hBeta : 1 < b) (hNotBoth : ¬ (a = 2 ∧ b = 2))
    (hm0 : 0 < m) (hrise_neg : rise < 0)
    (hAlphaEq : (a : ℤ) * slopeAlpha = rise + ((a : ℤ) - 1) * m)
    (hBetaEq : (b : ℤ) * slopeBeta = rise - (m : ℤ))
    (L w T : ℕ) (hLpos : 0 < L) (hw1 : 1 ≤ w) (hTge : g - 1 ≤ T)
    (hLw : (L : ℤ) * (w : ℤ) = -rise)
    (hsplitSum : slopeAlpha + slopeBeta = (w : ℤ) * (T : ℤ)) :
    crossOneOffCutoff g b ≤ m := by
  -- divisibility data for the marked strands
  set d : ℤ := (m : ℤ) - rise with hd_def
  have hdpos : 0 < d := by rw [hd_def]; omega
  set p : ℤ := (m : ℤ) - slopeAlpha with hp_def
  set r : ℤ := -slopeBeta with hr_def
  have hda : (a : ℤ) * p = d := by
    rw [hp_def, hd_def]; linear_combination -hAlphaEq
  have hdb : (b : ℤ) * r = d := by
    rw [hr_def, hd_def]; linear_combination -hBetaEq
  set nd : ℕ := d.toNat with hnd_def
  have hndZ : (nd : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hdpos)
  have hadvd : a ∣ nd := by
    have h1 : (a : ℤ) ∣ d := ⟨p, hda.symm⟩
    rw [← hndZ] at h1
    exact_mod_cast h1
  have hbdvd : b ∣ nd := by
    have h1 : (b : ℤ) ∣ d := ⟨r, hdb.symm⟩
    rw [← hndZ] at h1
    exact_mod_cast h1
  set e := Nat.gcd a b with he_def
  set a' := a / e with ha'_def
  set b' := b / e with hb'_def
  have hepos : 0 < e := Nat.gcd_pos_of_pos_left _ (by omega)
  have hae : e * a' = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hbe : e * b' = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have ha'1 : 1 ≤ a' := by
    rcases Nat.eq_zero_or_pos a' with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at hae; omega
    · exact h1
  have hb'1 : 1 ≤ b' := by
    rcases Nat.eq_zero_or_pos b' with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at hbe; omega
    · exact h1
  set ℓ := Nat.lcm a b with hℓ_def
  have hℓpos : 0 < ℓ := Nat.lcm_pos (by omega) (by omega)
  have hab'_eq : ℓ = a * b' := by
    have h1 : e * ℓ = a * b := Nat.gcd_mul_lcm a b
    have h2 : e * (a * b') = a * b := by rw [← hbe]; ring
    exact Nat.eq_of_mul_eq_mul_left hepos (h1.trans h2.symm)
  have ha'b_eq : ℓ = a' * b := by
    have h1 : e * ℓ = a * b := Nat.gcd_mul_lcm a b
    have h2 : e * (a' * b) = a * b := by rw [← hae]; ring
    exact Nat.eq_of_mul_eq_mul_left hepos (h1.trans h2.symm)
  have hℓdvd : ℓ ∣ nd := Nat.lcm_dvd hadvd hbdvd
  set t := nd / ℓ with ht_def
  have htdef : ℓ * t = nd := Nat.mul_div_cancel' hℓdvd
  have hndpos : 0 < nd := by
    have : (0 : ℤ) < (nd : ℤ) := by rw [hndZ]; exact hdpos
    exact_mod_cast this
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h1
    · exfalso; rw [h0, Nat.mul_zero] at htdef; omega
    · exact h1
  have hpeq : p = (b' : ℤ) * (t : ℤ) := by
    have h1 : (a : ℤ) * p = (a : ℤ) * ((b' : ℤ) * (t : ℤ)) := by
      rw [hda, ← hndZ]
      have : (nd : ℤ) = (ℓ : ℤ) * (t : ℤ) := by exact_mod_cast htdef.symm
      rw [this, hab'_eq]; push_cast; ring
    have haZ : (a : ℤ) ≠ 0 := by positivity
    exact mul_left_cancel₀ haZ h1
  have hreq : r = (a' : ℤ) * (t : ℤ) := by
    have h1 : (b : ℤ) * r = (b : ℤ) * ((a' : ℤ) * (t : ℤ)) := by
      rw [hdb, ← hndZ]
      have : (nd : ℤ) = (ℓ : ℤ) * (t : ℤ) := by exact_mod_cast htdef.symm
      rw [this, ha'b_eq]; push_cast; ring
    have hbZ : (b : ℤ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hbZ h1
  have hmZ : (m : ℤ) = (t : ℤ) * ((a' : ℤ) + (b' : ℤ)) + (w : ℤ) * (T : ℤ) := by
    have h1 : p + r = (m : ℤ) - (slopeAlpha + slopeBeta) := by
      rw [hp_def, hr_def]; ring
    rw [hpeq, hreq, hsplitSum] at h1
    linarith [h1]
  have hm_eq : m = t * (a' + b') + w * T := by exact_mod_cast hmZ
  set bm1 := b - 1 with hbm1_def
  have hbm1_1 : 1 ≤ bm1 := by omega
  set D := ℓ - a' - b' with hD_def
  have hDsum_ineq : a' + b' + 1 ≤ ℓ :=
    crossOneOff_D_pos a b (by omega) (by omega) hNotBoth
  have hDsum : D + a' + b' = ℓ := by omega
  have hD1 : 1 ≤ D := by omega
  have hDsum2 : D + a' + b' = a' * b := by rw [hDsum, ha'b_eq]
  have hDcast : (D : ℤ) = (a' : ℤ) * (bm1 : ℤ) - (b' : ℤ) := by
    have h1Z : (D : ℤ) + (a' : ℤ) + (b' : ℤ) = (a' : ℤ) * (b : ℤ) := by
      exact_mod_cast hDsum2
    have hbm1Z : (bm1 : ℤ) = (b : ℤ) - 1 := by
      have : bm1 + 1 = b := by omega
      have hc : ((bm1 + 1 : ℕ) : ℤ) = (b : ℤ) := by exact_mod_cast this
      push_cast at hc; linarith [hc]
    linear_combination h1Z - (a' : ℤ) * hbm1Z
  set E := L + T with hE_def
  have hEgeG : g ≤ E := by omega
  set F := g / bm1 with hF_def
  have hnd_eq1 : nd = m + L * w := by
    have h1 : (nd : ℤ) = (m : ℤ) + (L : ℤ) * (w : ℤ) := by
      rw [hndZ, hd_def]
      rw [hLw]; ring
    exact_mod_cast h1
  have hnd_eq2 : (nd : ℤ) = ((D : ℤ) + (a' : ℤ) + (b' : ℤ)) * (t : ℤ) := by
    have h1 : (nd : ℤ) = (ℓ : ℤ) * (t : ℤ) := by exact_mod_cast htdef.symm
    have h2 : (ℓ : ℤ) = (D : ℤ) + (a' : ℤ) + (b' : ℤ) := by exact_mod_cast hDsum.symm
    rw [h1, h2]
  have htDeqwE : t * D = w * E := by
    have hgoalZ : (t : ℤ) * (D : ℤ) = (w : ℤ) * (E : ℤ) := by
      have h1Z : (nd : ℤ) = (m : ℤ) + (L : ℤ) * (w : ℤ) := by exact_mod_cast hnd_eq1
      have hEZ : (E : ℤ) = (L : ℤ) + (T : ℤ) := by
        have : E = L + T := hE_def
        exact_mod_cast this
      linear_combination h1Z - hnd_eq2 + hmZ - (w : ℤ) * hEZ
    exact_mod_cast hgoalZ
  have hFbound : F + 1 ≤ t * (a' + b') := by
    rcases (by omega : a' + b' ≤ F ∨ F < a' + b') with hcase | hcase
    · exact crossOneOff_case2_bound a' b' bm1 g F D t w E ha'1 hb'1 hbm1_1
        hF_def hcase ht1 hw1 hD1 hDcast hEgeG htDeqwE
    · have h1 : a' + b' ≤ t * (a' + b') := Nat.le_mul_of_pos_left _ ht1
      omega
  have hwTge : g - 1 ≤ w * T := by
    have h1 : T ≤ w * T := Nat.le_mul_of_pos_left T hw1
    omega
  change crossOneOffCutoff g b ≤ m
  unfold crossOneOffCutoff
  rw [show b - 1 = bm1 from hbm1_def, ← hF_def]
  omega

/-- Core lemma: every torsion witness of the near-opposite cross-one-off
marking satisfies the closed-form cutoff bound, without any hypothesis
relating the two marked strand lengths beyond the two lengths not both
being `2`. -/
theorem crossOneOff_cutoff_le_torsionWitness_of_not_both_two
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hNotBoth : ¬ (B.length alpha = 2 ∧ B.length beta = 2))
    (m : ℕ) (hm : TorsionWitness
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) m) :
    crossOneOffCutoff g (B.length beta) ≤ m := by
  have hi : B.IsInteriorPosition alpha ⟨1, by omega⟩ := by
    change 0 < (1 : ℕ) ∧ 1 < B.length alpha
    exact ⟨by omega, hAlpha⟩
  have hj : B.IsInteriorPosition beta ⟨B.length beta - 1, by omega⟩ := by
    change 0 < B.length beta - 1 ∧ B.length beta - 1 < B.length beta
    omega
  obtain ⟨script, rise, slope, hrise, hsum, hAlphaEq0, hBetaEq0, hOther⟩ :=
    torsion_interior_initialSlope_equations B alpha beta
      ⟨1, by omega⟩ ⟨B.length beta - 1, by omega⟩ hi hj hab hm
  have hm0 : 0 < m := hm.1
  set a := B.length alpha with ha_def
  set b := B.length beta with hb_def
  have hAlphaEq0' : (a : ℤ) * slope alpha = rise + ((a - 1 : ℕ) : ℤ) * m :=
    hAlphaEq0
  have hBetaEq0' : (b : ℤ) * slope beta =
      rise - ((b - (b - 1) : ℕ) : ℤ) * m := hBetaEq0
  have hAlphaEq : (a : ℤ) * slope alpha = rise + ((a : ℤ) - 1) * m := by
    rw [show ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 from by omega] at hAlphaEq0'
    exact hAlphaEq0'
  have hBetaEq : (b : ℤ) * slope beta = rise - (m : ℤ) := by
    rw [show ((b - (b - 1) : ℕ) : ℤ) = 1 from by omega] at hBetaEq0'
    linarith [hBetaEq0']
  rcases lt_trichotomy rise 0 with hrise_neg | hrise_zero | hrise_pos
  · -- the hard case: `rise < 0`.
    obtain ⟨L, w, T, hLpos, hw1, hTge, hLw, hsplitSum⟩ :=
      crossOneOff_otherStrand_data B alpha beta hab rise slope hrise_neg hsum hOther
    exact crossOneOff_cutoff_of_negativeRise g a b m rise (slope alpha) (slope beta)
      hAlpha hBeta hNotBoth hm0 hrise_neg hAlphaEq hBetaEq
      L w T hLpos hw1 hTge hLw hsplitSum
  · -- `rise = 0` forces both strands to length two, contradicting `hNotBoth`.
    exfalso
    apply hNotBoth
    have hA0 : (a : ℤ) * slope alpha = ((a - 1 : ℕ) : ℤ) * m := by
      rw [hAlphaEq0, hrise_zero]; ring
    have hB0 : (b : ℤ) * slope beta = -((b - (b - 1) : ℕ) : ℤ) * m := by
      rw [hBetaEq0, hrise_zero]; ring
    have hOther0 : ∀ γ, γ ≠ alpha → γ ≠ beta → (B.length γ : ℤ) * slope γ = 0 := by
      intro γ h1 h2
      have := hOther γ h1 h2
      rw [hrise_zero] at this; exact this
    have hjval : (b - 1) + 1 = B.length beta := by rw [← hb_def]; omega
    exact zero_rise_cross_oneOff_forces_both_length_two B alpha beta
      ⟨1, by omega⟩ ⟨b - 1, by omega⟩ hab rfl hjval hi hj hm0 slope hsum
      hA0 hB0 hOther0
  · -- the easy case: `rise > 0` gives a much stronger bound directly.
    have hposOther : ∀ γ, γ ≠ beta → 0 < slope γ := by
      intro γ hγβ
      by_cases hγα : γ = alpha
      · subst γ
        have hlen : (0 : ℤ) < a := by exact_mod_cast (by omega : 0 < a)
        nlinarith [hAlphaEq, hrise_pos]
      · have hEq := hOther γ hγα hγβ
        have hlen : (0 : ℤ) < B.length γ := by exact_mod_cast B.length_pos γ
        nlinarith [hEq, hrise_pos]
    have hErase := sum_ge_card_of_pos (Finset.univ.erase beta) slope
      (fun x hx => hposOther x (Finset.ne_of_mem_erase hx))
    have hcard : (Finset.univ.erase beta).card = g := by simp
    rw [hcard] at hErase
    have hsplit : ∑ γ, slope γ = slope beta +
        ∑ γ ∈ Finset.univ.erase beta, slope γ :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ beta)).symm
    rw [hsplit] at hsum
    have hbetaLe : slope beta ≤ -(g : ℤ) := by linarith [hsum, hErase]
    have hbgZ : (b : ℤ) * (g : ℤ) ≤ m := by
      have hbpos : (0 : ℤ) ≤ b := by positivity
      nlinarith [hBetaEq, mul_le_mul_of_nonneg_left hbetaLe hbpos]
    have hbg : b * g ≤ m := by exact_mod_cast hbgZ
    change crossOneOffCutoff g b ≤ m
    unfold crossOneOffCutoff
    have hdiv : g / (b - 1) ≤ g := Nat.div_le_self g (b - 1)
    have h2g : g + g ≤ b * g := by
      have : 2 * g ≤ b * g := Nat.mul_le_mul_right g (by omega)
      omega
    omega

/-- Corollary: the closed-form period-separation bound for the exact torsion
order, replacing the long-second-strand hypothesis `hBetaLong` of
`crossOneOff_cutoff_le_torsionOrder` by the weaker `hNotBoth`. -/
theorem crossOneOff_cutoff_le_torsionOrder_of_not_both_two
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hNotBoth : ¬ (B.length alpha = 2 ∧ B.length beta = 2))
    (hTO : IsTorsionOrder
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k) :
    crossOneOffCutoff g (B.length beta) ≤ k :=
  crossOneOff_cutoff_le_torsionWitness_of_not_both_two B alpha beta hg hab
    hAlpha hBeta hNotBoth k hTO.1

end Bananas
