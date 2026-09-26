/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.Definitions

/-! # Theta Arithmetic -/

@[expose] public section

namespace Bananas

open Utilities

/-! Paper source: the period equality in `cor:evenlyMarkedKGT` and the gcd
calculation preceding `eq:multDiffMarkedPts`.

The arithmetic in this file is deliberately independent of the divisor-rank
and transmission APIs.  It isolates the number-theoretic content of the
evenly-marked condition. -/

/-- A positive length divided by the gcd with a positive interior coordinate
is positive. -/
theorem nat_div_gcd_pos_of_pos
    {a i : ℕ} (ha : 0 < a) (_hi : 0 < i) :
    0 < a / Nat.gcd a i := by
  exact Nat.div_pos (Nat.gcd_le_left _ ha)
    (Nat.gcd_pos_of_pos_left _ ha)

/-- The Euclidean decomposition used by the theta multiple calculation. -/
theorem nat_mul_eq_div_mul_add_mod
    (m n d : ℕ) :
    m * n = (m * n / d) * d + (m * n) % d := by
  simpa [Nat.mul_comm] using (Nat.div_add_mod (m * n) d).symm

/-- The remainder in the preceding decomposition is strictly below a positive
modulus. -/
theorem nat_mul_mod_lt_of_pos
    (m n d : ℕ) (hd : 0 < d) :
    (m * n) % d < d := by
  exact Nat.mod_lt _ hd

/-- If two positive pairs represent the same positive rational ratio, their
lengths have the same quotient after each pair is reduced by its gcd. -/
theorem nat_gcd_quotient_eq_of_cross_mul
    {a b i j : ℕ}
    (ha : 0 < a) (hb : 0 < b) (_hi : 0 < i) (_hj : 0 < j)
    (hcross : i * b = j * a) :
    a / Nat.gcd a i = b / Nat.gcd b j := by
  let d := Nat.gcd a i
  let e := Nat.gcd b j
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left _ ha
  have he : 0 < e := by
    dsimp [e]
    exact Nat.gcd_pos_of_pos_left _ hb
  have hA : Nat.Coprime (a / d) (i / d) := by
    dsimp [d]
    exact Nat.gcd_div_gcd_div_gcd_of_pos_left ha
  have hB : Nat.Coprime (b / e) (j / e) := by
    dsimp [e]
    exact Nat.gcd_div_gcd_div_gcd_of_pos_left hb
  have ha_expand : a = (a / d) * d := by
    dsimp [d]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left a i)).symm
  have hi_expand : i = (i / d) * d := by
    dsimp [d]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right a i)).symm
  have hb_expand : b = (b / e) * e := by
    dsimp [e]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left b j)).symm
  have hj_expand : j = (j / e) * e := by
    dsimp [e]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right b j)).symm
  have hReduced : (i / d) * (b / e) = (j / e) * (a / d) := by
    have hExpanded :
        ((i / d) * d) * ((b / e) * e) =
          ((j / e) * e) * ((a / d) * d) := by
      calc
        ((i / d) * d) * ((b / e) * e) = i * b := by
          rw [← hi_expand, ← hb_expand]
        _ = j * a := hcross
        _ = ((j / e) * e) * a := congrArg (fun x => x * a) hj_expand
        _ = ((j / e) * e) * ((a / d) * d) :=
          congrArg (fun x => ((j / e) * e) * x) ha_expand
    have hCancelled :
        (d * e) * ((i / d) * (b / e)) =
          (d * e) * ((j / e) * (a / d)) := by
      calc
        (d * e) * ((i / d) * (b / e)) =
          ((i / d) * d) * ((b / e) * e) := by ac_rfl
        _ = ((j / e) * e) * ((a / d) * d) := hExpanded
        _ = (d * e) * ((j / e) * (a / d)) := by ac_rfl
    exact Nat.mul_left_cancel (Nat.mul_pos hd he) hCancelled
  have hA_dvd_B : a / d ∣ b / e := by
    apply hA.dvd_of_dvd_mul_left
    rw [hReduced]
    exact ⟨j / e, by ac_rfl⟩
  have hB_dvd_A : b / e ∣ a / d := by
    apply hB.dvd_of_dvd_mul_left
    rw [← hReduced]
    exact ⟨i / d, by ac_rfl⟩
  exact Nat.dvd_antisymm hA_dvd_B hB_dvd_A

/-- The gcd quotient in the paper's period formula is positive for an evenly
marked theta. -/
/- TeX label: `defn:evenlyMarked` / arithmetic positivity helper. -/
theorem evenlyMarkedTheta_k_pos
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) :
    0 < B.length α / Nat.gcd (B.length α) i.val := by
  rcases hEven with ⟨_hαβ, hi, _hiLt, _hj, _hjLt, _hcross⟩
  exact nat_div_gcd_pos_of_pos (B.length_pos α) hi

/-- The two candidate gcd periods agree under the evenly-marked ratio. -/
/- TeX label: `cor:evenlyMarkedKGT` (equal reduced quotients). -/
theorem evenlyMarkedTheta_gcd_quotients_eq
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) :
    B.length α / Nat.gcd (B.length α) i.val =
      B.length β / Nat.gcd (B.length β) j.val := by
  rcases hEven with ⟨_hαβ, hi, _hiLt, hj, _hjLt, hcross⟩
  exact nat_gcd_quotient_eq_of_cross_mul
    (B.length_pos α) (B.length_pos β) hi hj hcross

/-! The reduced numerator is the common multiplier of the endpoint
relation.  This is the companion arithmetic identity needed when the
one-strand prefix theorem is scaled to an evenly marked pair. -/
/- TeX label: `cor:evenlyMarkedKGT` (reduced-coordinate identity). -/
theorem evenlyMarkedTheta_reduced_coordinates_eq
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) :
    i.val / Nat.gcd (B.length α) i.val =
      j.val / Nat.gcd (B.length β) j.val := by
  rcases hEven with ⟨_hαβ, hi, _hiLt, hj, _hjLt, hcross⟩
  have hcross' : B.length α * j.val = B.length β * i.val := by
    simpa [Nat.mul_comm] using hcross.symm
  have h' := nat_gcd_quotient_eq_of_cross_mul
    hi hj (B.length_pos α) (B.length_pos β) hcross'
  simpa [Nat.gcd_comm] using h'

/-! ## Quotients and residues of evenly-marked multiples

The following lemmas make explicit a step that is implicit in the paper's
residue calculation: every multiple of the two marked coordinates crosses
the two right endpoints the same number of times.  Below the gcd period,
neither residue is zero and multiplication by either marked coordinate is
injective modulo its strand length. -/

/-- Equal positive rational ratios have equal floor quotients after both
numerators are multiplied by the same natural number. -/
theorem nat_mul_div_eq_of_cross_mul
    {a b i j m : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j)
    (hcross : i * b = j * a) :
    m * i / a = m * j / b := by
  let d := Nat.gcd a i
  let e := Nat.gcd b j
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left _ ha
  have he : 0 < e := by
    dsimp [e]
    exact Nat.gcd_pos_of_pos_left _ hb
  have ha_expand : a = (a / d) * d := by
    dsimp [d]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left a i)).symm
  have hi_expand : i = (i / d) * d := by
    dsimp [d]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right a i)).symm
  have hb_expand : b = (b / e) * e := by
    dsimp [e]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left b j)).symm
  have hj_expand : j = (j / e) * e := by
    dsimp [e]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right b j)).symm
  have hk : a / d = b / e :=
    nat_gcd_quotient_eq_of_cross_mul ha hb hi hj hcross
  have hq : i / d = j / e := by
    have hcross' : a * j = b * i := by
      simpa [Nat.mul_comm] using hcross.symm
    simpa [d, e, Nat.gcd_comm] using
      (nat_gcd_quotient_eq_of_cross_mul hi hj ha hb hcross')
  rw [hi_expand, ha_expand, hj_expand, hb_expand]
  rw [show m * ((i / d) * d) = (m * (i / d)) * d by ac_rfl]
  rw [show m * ((j / e) * e) = (m * (j / e)) * e by ac_rfl]
  rw [Nat.mul_div_mul_right _ _ hd, Nat.mul_div_mul_right _ _ he, hk, hq]

/-- Multiplication by `i` modulo `a` is injective on the fundamental range
`0, ..., a / gcd a i - 1`. -/
theorem nat_mul_mod_injective_below_gcd_quotient
    {a i m n : ℕ} (ha : 0 < a)
    (hm : m < a / Nat.gcd a i) (hn : n < a / Nat.gcd a i)
    (hmod : m * i % a = n * i % a) :
    m = n := by
  let d := Nat.gcd a i
  let k := a / d
  let q := i / d
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left _ ha
  have ha_expand : a = d * k := by
    dsimp [d, k]
    simpa [Nat.mul_comm] using
      (Nat.div_mul_cancel (Nat.gcd_dvd_left a i)).symm
  have hi_expand : i = d * q := by
    dsimp [d, q]
    simpa [Nat.mul_comm] using
      (Nat.div_mul_cancel (Nat.gcd_dvd_right a i)).symm
  have hcop : Nat.Coprime k q := by
    dsimp [k, q, d]
    exact Nat.gcd_div_gcd_div_gcd_of_pos_left ha
  have aux : ∀ {m n : ℕ}, m < k → n < k → m ≤ n →
      m * i % a = n * i % a → m = n := by
    intro m n hm hn hmn hmod
    have hcong : m * i ≡ n * i [MOD a] := hmod
    have hdvd : a ∣ n * i - m * i :=
      (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right i hmn)).mp hcong
    have hsub : n * i - m * i = d * ((n - m) * q) := by
      rw [hi_expand, ← Nat.sub_mul]
      ac_rfl
    rw [ha_expand, hsub] at hdvd
    have hk_dvd : k ∣ (n - m) * q :=
      (Nat.mul_dvd_mul_iff_left hd).mp hdvd
    have hk_dvd_sub : k ∣ n - m :=
      hcop.dvd_of_dvd_mul_right hk_dvd
    have hsub_lt : n - m < k := by omega
    have hzero : n - m = 0 := by
      by_contra hne
      have hk_le : k ≤ n - m :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hk_dvd_sub
      omega
    omega
  have hm' : m < k := by simpa [k, d] using hm
  have hn' : n < k := by simpa [k, d] using hn
  rcases le_total m n with hmn | hnm
  · exact aux hm' hn' hmn hmod
  · exact (aux hn' hm' hnm hmod.symm).symm

/-- A nonzero multiplier strictly below the gcd quotient has nonzero
residue. -/
theorem nat_mul_mod_ne_zero_below_gcd_quotient
    {a i m : ℕ} (ha : 0 < a) (hm0 : 0 < m)
    (hmk : m < a / Nat.gcd a i) :
    m * i % a ≠ 0 := by
  intro hzero
  have hzero' : m * i % a = 0 * i % a := by simpa using hzero
  have := nat_mul_mod_injective_below_gcd_quotient ha hmk
    (by
      have hkpos : 0 < a / Nat.gcd a i := by omega
      omega)
    hzero'
  omega

/-- Evenly-marked multiples have a common endpoint-crossing quotient. -/
theorem evenlyMarkedTheta_common_quotient
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) (m : ℕ) :
    m * i.val / B.length α = m * j.val / B.length β := by
  rcases hEven with ⟨_hαβ, hi, _hiLt, hj, _hjLt, hcross⟩
  exact nat_mul_div_eq_of_cross_mul
    (B.length_pos α) (B.length_pos β) hi hj hcross

/-- Euclidean decompositions of the two marked multiples use the same
quotient. -/
theorem evenlyMarkedTheta_mul_residue_decompositions
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) (m : ℕ) :
    m * i.val = (m * i.val / B.length α) * B.length α +
        (m * i.val) % B.length α ∧
      m * j.val = (m * i.val / B.length α) * B.length β +
        (m * j.val) % B.length β := by
  constructor
  · exact nat_mul_eq_div_mul_add_mod m i.val (B.length α)
  · calc
      m * j.val = (m * j.val / B.length β) * B.length β +
          (m * j.val) % B.length β :=
        nat_mul_eq_div_mul_add_mod m j.val (B.length β)
      _ = (m * i.val / B.length α) * B.length β +
          (m * j.val) % B.length β := by
        rw [evenlyMarkedTheta_common_quotient B α β i j hEven m]

/-- The first residue coordinate is injective throughout one gcd period. -/
theorem evenlyMarkedTheta_alpha_residue_injective
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (_hEven : EvenlyMarkedTheta B α β i j)
    {m n : ℕ}
    (hm : m < B.length α / Nat.gcd (B.length α) i.val)
    (hn : n < B.length α / Nat.gcd (B.length α) i.val)
    (hres : (m * i.val) % B.length α =
      (n * i.val) % B.length α) :
    m = n := by
  exact nat_mul_mod_injective_below_gcd_quotient
    (B.length_pos α) hm hn hres

/-- The second residue coordinate is injective throughout the same period. -/
theorem evenlyMarkedTheta_beta_residue_injective
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j)
    {m n : ℕ}
    (hm : m < B.length α / Nat.gcd (B.length α) i.val)
    (hn : n < B.length α / Nat.gcd (B.length α) i.val)
    (hres : (m * j.val) % B.length β =
      (n * j.val) % B.length β) :
    m = n := by
  have hk := evenlyMarkedTheta_gcd_quotients_eq B α β i j hEven
  apply nat_mul_mod_injective_below_gcd_quotient (i := j.val)
    (B.length_pos β) (by simpa [← hk] using hm) (by simpa [← hk] using hn)
  exact hres

/-- In the nonzero part of one gcd period, neither residue is an endpoint. -/
theorem evenlyMarkedTheta_residues_ne_zero
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j)
    {m : ℕ} (hm0 : 0 < m)
    (hm : m < B.length α / Nat.gcd (B.length α) i.val) :
    (m * i.val) % B.length α ≠ 0 ∧
      (m * j.val) % B.length β ≠ 0 := by
  constructor
  · exact nat_mul_mod_ne_zero_below_gcd_quotient
      (B.length_pos α) hm0 hm
  · have hk := evenlyMarkedTheta_gcd_quotients_eq B α β i j hEven
    exact nat_mul_mod_ne_zero_below_gcd_quotient
      (B.length_pos β) hm0 (by simpa [← hk] using hm)

end Bananas
