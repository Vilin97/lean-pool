/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

/-!
# H3 for Thakur's hypotheses on power sums
-/

namespace ZetaH123.H3

/-
# Problem Description

Fix a prime number `p` and a prime power `q = p ^ f` where `f ≥ 1` is an integer.

## Definition 1 (Carry-free addition in base `p`)
For nonnegative integers `x_1, ..., x_r`, the addition `x_1 + ... + x_r` *has no
carries in base `p`* if, at every base-`p` digit position, the corresponding
base-`p` digits of `x_1, ..., x_r` sum to at most `p - 1`. Writing
`x_j = ∑_{t ≥ 0} a_{j,t} p ^ t` with `0 ≤ a_{j,t} ≤ p - 1`, the condition is
`∑_{j=1} ^ r a_{j,t} ≤ p - 1` for every `t ≥ 0`.

## Definition 2 (The set `T_{d,j}`)
For `d ≥ 1` and `j ≥ 0`, `T_{d,j}` is the set of all `d`-tuples `(m_1, ..., m_d)`
of integers with: (1) `m_i > 0`; (2) `(q - 1) ∣ m_i`; (3) the addition
`j + m_1 + ... + m_d` has no carries in base `p` (applied to the `r = d + 1`
summands `j, m_1, ..., m_d`).

## Definition 3 (The quantities `M_d(j)` and `s_d(k)`)
The set `T_{d,j}` is nonempty, so the minimum
`M_d(j) := min_{(m_1,...,m_d) ∈ T_{d,j}} (m_1 + 2 m_2 + ... + d m_d)`
exists and is attained. For `d ≥ 1` and `k > 0`, `s_d(k) := d k + M_d(k - 1)`.

## Main Statement (Theorem)
Let `p` be a prime, `q = p ^ f` a prime power (`f ≥ 1`), and `d ≥ 1`, `k > 0`
integers. If `p ∤ k`, then `s_d(k) < s_d(k + 1)`.

## Remarks
`T_{d,j}` is nonempty: choosing `m_i = (q - 1) p ^ {f e_i}` for distinct large
exponents `e_i` gives a carry-free sum, so `M_d(j)` is well defined. The proof
of the theorem uses that `p ∤ k` implies passing from `k` to `k - 1` only
decreases the units digit, so `T_{d,k} ⊆ T_{d,k-1}` and hence
`M_d(k) ≥ M_d(k - 1)`, giving `s_d(k + 1) - s_d(k) ≥ d ≥ 1 > 0`.
-/

open Finset

-- Main Definition(s)

/-- Definition 1: the addition `j + m_1 + ... + m_d` (the `r = d + 1` summands
`j, m_1, ..., m_d`) has no carries in base `p`: at every base-`p` digit position
`t`, the digits sum to at most `p - 1`. We read off the `t`-th base-`p` digit of
a number `n` as `(Nat.digits p n).getD t 0`. -/
def NoCarry (p : ℕ) (j : ℕ) (d : ℕ) (m : Fin d → ℕ) : Prop :=
  ∀ t : ℕ, (Nat.digits p j).getD t 0 + ∑ i, (Nat.digits p (m i)).getD t 0 ≤ p - 1

/-- Definition 2: the set `T_{d,j}` of `d`-tuples `(m_1, ..., m_d)` (encoded as a
function `Fin d → ℕ`) with each `m_i > 0`, `(q - 1) ∣ m_i`, and `j + m_1 + ... +
m_d` carry-free in base `p`. -/
def Tset (p q d j : ℕ) : Set (Fin d → ℕ) :=
  {m | (∀ i, 0 < m i) ∧ (∀ i, (q - 1) ∣ m i) ∧ NoCarry p j d m}

/-- The objective `m_1 + 2 m_2 + ... + d m_d = ∑_{i} i · m_i` (with `1`-based
weights; the `i`-th coordinate `m i` is weighted by `i + 1` under `0`-based
`Fin d` indexing). -/
def objective (d : ℕ) (m : Fin d → ℕ) : ℕ := ∑ i : Fin d, (i.val + 1) * m i

/-- Definition 3: `M_d(j)` is the minimum of the objective over `T_{d,j}`,
realized as the infimum of the image of `T_{d,j}` under the objective. Since
`T_{d,j}` is nonempty (see Remarks) and `ℕ` is well-ordered, this minimum is
attained. -/
noncomputable def Md (p q d j : ℕ) : ℕ := sInf (objective d '' Tset p q d j)

/-- Definition 3: `s_d(k) := d k + M_d(k - 1)`. -/
noncomputable def sd (p q d k : ℕ) : ℕ := d * k + Md p q d (k - 1)

-- Helper lemmas (digit manipulation in base `p`).

/-- The `t`-th base-`p` digit of `n`. -/
private def dig (p n t : ℕ) : ℕ := n / p ^ t % p

private lemma getD_eq_dig {p : ℕ} (hp : 2 ≤ p) (n t : ℕ) :
    (Nat.digits p n).getD t 0 = dig p n t :=
  Nat.getD_digits n t hp

private lemma dig_le {p : ℕ} (hp : 1 ≤ p) (n t : ℕ) : dig p n t ≤ p - 1 := by
  have := Nat.mod_lt (n / p ^ t) (show 0 < p by omega)
  unfold dig; omega

private lemma dig_mul_pow_lt {p : ℕ} (hp : 2 ≤ p) (n c t : ℕ) (ht : t < c) :
    dig p (n * p ^ c) t = 0 := by
  unfold dig
  have hdvd : p ^ (t + 1) ∣ n * p ^ c := Dvd.dvd.mul_left (pow_dvd_pow p (by omega)) n
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_succ, mul_assoc, Nat.mul_div_cancel_left _ (by positivity),
    Nat.mul_mod_right]

private lemma dig_mul_pow_ge {p : ℕ} (hp : 2 ≤ p) (n c t : ℕ) (ht : c ≤ t) :
    dig p (n * p ^ c) t = dig p n (t - c) := by
  unfold dig
  have h1 : p ^ t = p ^ c * p ^ (t - c) := by rw [← pow_add]; congr 1; omega
  rw [h1, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (by positivity)]

private lemma dig_pred_pow_ge {p : ℕ} (hp : 2 ≤ p) (f t : ℕ) (ht : f ≤ t) :
    dig p (p ^ f - 1) t = 0 := by
  unfold dig
  have hlt : p ^ f - 1 < p ^ t := by
    have h1 : p ^ f ≤ p ^ t := Nat.pow_le_pow_right (by omega) ht
    have h2 : 1 ≤ p ^ f := Nat.one_le_pow _ _ (by omega)
    omega
  rw [Nat.div_eq_of_lt hlt]; simp

private lemma dig_pred_pow_lt {p : ℕ} (hp : 2 ≤ p) (f t : ℕ) (ht : t < f) :
    dig p (p ^ f - 1) t = p - 1 := by
  unfold dig
  have hdiv : (p ^ f - 1) / p ^ t = p ^ (f - t) - 1 := by
    have heq : p ^ f = p ^ (f - t) * p ^ t := by rw [← pow_add]; congr 1; omega
    have hpft : 1 ≤ p ^ (f - t) := Nat.one_le_pow _ _ (by omega)
    have hpt : 1 ≤ p ^ t := Nat.one_le_pow _ _ (by omega)
    have hge : p ^ t ≤ p ^ (f - t) * p ^ t := Nat.le_mul_of_pos_left _ (by omega)
    have hsplit : p ^ f - 1 = (p ^ t - 1) + (p ^ (f - t) - 1) * p ^ t := by
      rw [heq, Nat.sub_one_mul]; omega
    rw [hsplit, Nat.add_mul_div_right _ _ (by positivity : 0 < p ^ t),
      Nat.div_eq_of_lt (by omega : p ^ t - 1 < p ^ t), zero_add]
  rw [hdiv]
  have hd : p ∣ p ^ (f - t) := dvd_pow_self p (by omega : f - t ≠ 0)
  obtain ⟨k, hk⟩ := hd
  have hpk : 1 ≤ p ^ (f - t) := Nat.one_le_pow _ _ (by omega)
  have hk1 : 1 ≤ k := by nlinarith [hk, hpk]
  have hpkmul : p * (k - 1) = p * k - p := by rw [Nat.mul_sub]; ring_nf
  have hge2 : p ≤ p * k := Nat.le_mul_of_pos_right _ (by omega)
  rw [hk, show p * k - 1 = (p - 1) + p * (k - 1) by rw [hpkmul]; omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : p - 1 < p)]

/-- Digit of the building block `(p ^ f - 1) * p ^ c`: it is `p-1` inside the block
`[c, c+f)` and `0` outside. -/
private lemma dig_block {p : ℕ} (hp : 2 ≤ p) (f c t : ℕ) :
    dig p ((p ^ f - 1) * p ^ c) t = if c ≤ t ∧ t < c + f then p - 1 else 0 := by
  rcases lt_or_ge t c with hlt | hge
  · rw [dig_mul_pow_lt hp _ _ _ hlt, if_neg (by omega)]
  · rw [dig_mul_pow_ge hp _ _ _ hge]
    rcases lt_or_ge (t - c) f with hin | hout
    · rw [dig_pred_pow_lt hp _ _ hin, if_pos (by omega)]
    · rw [dig_pred_pow_ge hp _ _ hout, if_neg (by omega)]

/-- When `p ∤ k` and `k ≥ 1`, every base-`p` digit of `k - 1` is `≤` the
corresponding digit of `k`. -/
private lemma dig_pred_le {p : ℕ} (hp : 2 ≤ p) {k : ℕ} (hk : 1 ≤ k)
    (hpk : ¬ p ∣ k) (t : ℕ) : dig p (k - 1) t ≤ dig p k t := by
  unfold dig
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · subst ht0
    simp only [pow_zero, Nat.div_one]
    have hkp : k % p ≠ 0 := fun h => hpk (Nat.dvd_of_mod_eq_zero h)
    have hmod : (k - 1) % p = k % p - 1 := by
      conv_lhs => rw [show k - 1 = (k % p - 1) + p * (k / p) by
        have := Nat.div_add_mod k p; omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
      have := Nat.mod_lt k (show 0 < p by omega); omega
    omega
  · have hnd : ¬ p ^ t ∣ k := fun h =>
      hpk (dvd_trans (dvd_pow_self p (by omega : t ≠ 0)) h)
    have heq : k / p ^ t = (k - 1) / p ^ t := by
      have hkk : k = (k - 1) + 1 := by omega
      rw [hkk, Nat.succ_div, if_neg (by rw [← hkk]; exact hnd)]; simp
    rw [heq]

/-- Auxiliary: nonemptiness of `T_{d,j}`, used by both `main_theorem` and the
public `Tset_nonempty`. -/
private lemma Tset_nonempty_aux (p q d j f : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (hq : q = p ^ f) (_hd : 1 ≤ d) : (Tset p q d j).Nonempty := by
  have hp2 : 2 ≤ p := hp.two_le
  set L := (Nat.digits p j).length with hL
  -- witness: m i = (p ^ f - 1) * p ^ (f*(L+i))
  refine ⟨fun i => (p ^ f - 1) * p ^ (f * (L + i.val)), ?_, ?_, ?_⟩
  · -- positivity
    intro i
    have h1 : 1 ≤ p ^ f - 1 := by
      have : p ^ 1 ≤ p ^ f := Nat.pow_le_pow_right (by omega) hf
      simp only [pow_one] at this; omega
    have h2 : 0 < p ^ (f * (L + i.val)) := by positivity
    exact Nat.mul_pos (by omega) h2
  · -- divisibility by q - 1 = p ^ f - 1
    intro i
    rw [hq]
    exact Dvd.intro _ rfl
  · -- NoCarry
    intro t
    rw [getD_eq_dig hp2]
    have hblock : ∀ i : Fin d,
        (Nat.digits p ((p ^ f - 1) * p ^ (f * (L + i.val)))).getD t 0
          = if f * (L + i.val) ≤ t ∧ t < f * (L + i.val) + f then p - 1 else 0 := by
      intro i
      rw [getD_eq_dig hp2, dig_block hp2]
    rw [Finset.sum_congr rfl (fun i _ => hblock i)]
    -- the sum is ≤ p-1 (at most one block contains t)
    have hsum : ∑ i : Fin d,
        (if f * (L + i.val) ≤ t ∧ t < f * (L + i.val) + f then p - 1 else 0) ≤ p - 1 := by
      by_cases h : ∃ i : Fin d, f * (L + i.val) ≤ t ∧ t < f * (L + i.val) + f
      · obtain ⟨i0, hi0⟩ := h
        rw [Finset.sum_eq_single i0]
        · rw [if_pos hi0]
        · intro b _ hb
          rw [if_neg]
          rintro ⟨hb1, hb2⟩
          have hfpos : 0 < f := by omega
          have hle1 : L + b.val ≤ L + i0.val := by
            by_contra hcon
            push Not at hcon
            have : f * (L + i0.val) + f ≤ f * (L + b.val) := by
              calc f * (L + i0.val) + f = f * (L + i0.val + 1) := by ring
              _ ≤ f * (L + b.val) := Nat.mul_le_mul_left f (by omega)
            omega
          have hle2 : L + i0.val ≤ L + b.val := by
            by_contra hcon
            push Not at hcon
            have : f * (L + b.val) + f ≤ f * (L + i0.val) := by
              calc f * (L + b.val) + f = f * (L + b.val + 1) := by ring
              _ ≤ f * (L + i0.val) := Nat.mul_le_mul_left f (by omega)
            omega
          exact hb (Fin.ext (by omega))
        · intro h'; simp at h'
      · have hz : ∑ i : Fin d,
            (if f * (L + i.val) ≤ t ∧ t < f * (L + i.val) + f then p - 1 else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          rw [if_neg]
          rintro ⟨h1, h2⟩
          exact h ⟨i, h1, h2⟩
        rw [hz]; omega
    -- combine with the j-digit term
    rcases lt_or_ge t L with htL | htL
    · -- t < L: all blocks vanish, sum = 0
      have hzero : ∑ i : Fin d,
          (if f * (L + i.val) ≤ t ∧ t < f * (L + i.val) + f then p - 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg]
        rintro ⟨h1, h2⟩
        -- c i = f*(L+i) ≥ f*L ≥ L > t
        have : L ≤ f * (L + i.val) := by
          calc L ≤ f * L := Nat.le_mul_of_pos_left L (by omega)
          _ ≤ f * (L + i.val) := Nat.mul_le_mul_left f (by omega)
        omega
      rw [hzero, add_zero]
      exact dig_le (by omega) j t
    · -- t ≥ L: j-digit is 0
      have hj0 : dig p j t = 0 := by
        have hgd : (Nat.digits p j).getD t 0 = 0 := by
          rw [List.getD_eq_default]; omega
        rw [getD_eq_dig hp2] at hgd
        exact hgd
      rw [hj0, zero_add]
      exact hsum

-- Main Statement(s)

/-- **Theorem.** Let `p` be a prime, `q = p ^ f` (`f ≥ 1`), and `d ≥ 1`, `k > 0`.
If `p ∤ k`, then `s_d(k) < s_d(k + 1)`. -/
theorem main_theorem (p q d k f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hq : q = p ^ f)
    (hd : 1 ≤ d) (hk : 0 < k) (hpk : ¬ p ∣ k) :
    sd p q d k < sd p q d (k + 1) := by
  have hp2 : 2 ≤ p := hp.two_le
  -- Tset p q d k ⊆ Tset p q d (k - 1)
  have hsubset : Tset p q d k ⊆ Tset p q d (k - 1) := by
    rintro m ⟨hpos, hdvd, hnc⟩
    refine ⟨hpos, hdvd, ?_⟩
    intro t
    have hkey := hnc t
    rw [getD_eq_dig hp2] at hkey ⊢
    have hdle : dig p (k - 1) t ≤ dig p k t := dig_pred_le hp2 hk hpk t
    rw [Finset.sum_congr rfl (fun i _ => getD_eq_dig hp2 (m i) t)] at hkey
    rw [Finset.sum_congr rfl (fun i _ => getD_eq_dig hp2 (m i) t)]
    omega
  -- image inclusion
  have himg : objective d '' Tset p q d k ⊆ objective d '' Tset p q d (k - 1) :=
    Set.image_mono hsubset
  -- nonempty image for k
  have hnek : (objective d '' Tset p q d k).Nonempty :=
    (Tset_nonempty_aux p q d k f hp hf hq hd).image _
  -- Md (k - 1) ≤ Md k
  have hMd : Md p q d (k - 1) ≤ Md p q d k := by
    obtain ⟨v, hv, hval⟩ := Nat.sInf_mem hnek
    change sInf (objective d '' Tset p q d (k - 1)) ≤ sInf (objective d '' Tset p q d k)
    rw [← hval]
    exact Nat.sInf_le (himg ⟨v, hv, rfl⟩)
  -- conclude
  unfold sd
  simp only [Nat.add_sub_cancel]
  have hdk : d * k < d * (k + 1) := by
    have : 0 < d := by omega
    nlinarith [this]
  omega

-- Correctness statements characterizing `M_d(j)` as the attained minimum.

/-- Nonemptiness of `T_{d,j}` (Remarks): the minimization defining `M_d(j)` is
over a nonempty set. -/
theorem Tset_nonempty (p q d j f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hq : q = p ^ f)
    (hd : 1 ≤ d) : (Tset p q d j).Nonempty :=
  Tset_nonempty_aux p q d j f hp hf hq hd

/-- `M_d(j)` is attained: there is a tuple in `T_{d,j}` achieving the objective
value `M_d(j)`. -/
theorem Md_attained (p q d j f : ℕ) (hp : p.Prime) (hf : 1 ≤ f) (hq : q = p ^ f)
    (hd : 1 ≤ d) :
    ∃ m ∈ Tset p q d j, objective d m = Md p q d j := by
  have hne : (Tset p q d j).Nonempty := Tset_nonempty_aux p q d j f hp hf hq hd
  have himg : (objective d '' Tset p q d j).Nonempty := hne.image _
  have hmem : Md p q d j ∈ objective d '' Tset p q d j := Nat.sInf_mem himg
  obtain ⟨m, hm, hval⟩ := hmem
  exact ⟨m, hm, hval⟩

/-- `M_d(j)` is a lower bound for the objective on `T_{d,j}`. -/
theorem Md_le (p q d j f : ℕ) (_hp : p.Prime) (_hf : 1 ≤ f) (_hq : q = p ^ f)
    (_hd : 1 ≤ d) {m : Fin d → ℕ} (hm : m ∈ Tset p q d j) :
    Md p q d j ≤ objective d m := by
  apply Nat.sInf_le
  exact ⟨m, hm, rfl⟩

end ZetaH123.H3
