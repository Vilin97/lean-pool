/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
module

public import LeanPool.Champernowne.DigitCount
public import Mathlib.Data.List.GetD

/-!
# Exact digit counts and further occurrence-counting inequalities

The append, take, drop, and flatten bounds extend the occurrence-counting API.
The exact periodic count and `digitEquiv` relate integer intervals to digit
strings. Exact counts distinguish the head position, where a positive integer
cannot start with zero, from interior positions; their sum gives a closed
formula for occurrences inside a complete cohort of equal-length numbers.

These results are exported by the project entry module as reusable infrastructure.
The normality proof itself needs only the lower bounds in `DigitCount`.
-/

@[expose] public section

namespace Champernowne

/-- Sanity bridge to `List.count`: single-letter blocks are `List.count`. -/
theorem countOccurrences_singleton (d : ℕ) (l : List ℕ) :
    countOccurrences [d] l = l.count d := by
  induction l with
  | nil => simp [countOccurrences, List.isPrefixOf]
  | cons x xs ih =>
    rw [countOccurrences_cons, ih, List.count_cons]
    by_cases h : x = d
    · subst h
      simp [List.isPrefixOf]
    · have h' : ¬d = x := fun hdx => h hdx.symm
      simp [h, h', List.isPrefixOf]

/-- A prefix short enough to fit inside `a` is a prefix of `a`. -/
theorem prefix_of_prefix_append {α : Type*} {w a c : List α}
    (h : w <+: a ++ c) (hl : w.length ≤ a.length) : w <+: a := by
  obtain ⟨t, ht⟩ := h
  have h1 : (a ++ c).take w.length = w := by
    rw [← ht]
    exact List.take_left ..
  have h2 : w = a.take w.length :=
    h1.symm.trans (List.take_append_of_le_length hl)
  rw [h2]
  exact List.take_prefix _ _

theorem countOccurrences_le_cons (w l : List ℕ) (x : ℕ) :
    countOccurrences w l ≤ countOccurrences w (x :: l) := by
  rw [countOccurrences_cons]
  omega

/-- Append sandwich, upper bound: at most `min w.length a.length`
occurrences straddle the seam (they must start within `w.length − 1`
slots of the end of `a`, and there are only `a.length` interior start
slots). -/
theorem countOccurrences_append_le_min (w a b : List ℕ) :
    countOccurrences w (a ++ b)
      ≤ countOccurrences w a + countOccurrences w b
        + min w.length a.length := by
  induction a with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.min_zero, Nat.add_zero]
    exact Nat.le_add_left _ _
  | cons x a' ih =>
    rw [List.cons_append, countOccurrences_cons, countOccurrences_cons]
    have hlc : (x :: a').length = a'.length + 1 := by simp
    by_cases h : w.isPrefixOf (x :: (a' ++ b))
    · by_cases h' : w.isPrefixOf (x :: a')
      · simp only [h, h']
        omega
      · -- straddling window: `w` overhangs the end of `x :: a'`
        have hlen : (x :: a').length < w.length := by
          rcases Nat.lt_or_ge (x :: a').length w.length with hlt | hge
          · exact hlt
          · refine absurd ?_ h'
            rw [List.isPrefixOf_iff_prefix] at h ⊢
            exact prefix_of_prefix_append
              (by rwa [← List.cons_append] at h) hge
        simp only [h, h', ite_true]
        omega
    · have h' : ¬ w.isPrefixOf (x :: a') := by
        intro hc
        apply h
        rw [← List.cons_append]
        exact isPrefixOf_append_of_isPrefixOf b hc
      simp only [h, h']
      omega

/-- The seam bound with the word length as an upper bound. -/
theorem countOccurrences_append_le (w a b : List ℕ) :
    countOccurrences w (a ++ b)
      ≤ countOccurrences w a + countOccurrences w b + w.length :=
  (countOccurrences_append_le_min w a b).trans
    (Nat.add_le_add_left (Nat.min_le_left _ _) _)

theorem countOccurrences_le_append_left (w a b : List ℕ) :
    countOccurrences w b ≤ countOccurrences w (a ++ b) := by
  induction a with
  | nil => simp
  | cons x a' ih =>
    rw [List.cons_append]
    exact ih.trans (countOccurrences_le_cons w _ x)

/-- The whole-list window contributes to the count. -/
theorem if_isPrefixOf_le_countOccurrences (w l : List ℕ) :
    (if w.isPrefixOf l then 1 else 0) ≤ countOccurrences w l := by
  rcases l with _ | ⟨x, xs⟩
  · rw [countOccurrences_nil']
  · rw [countOccurrences_cons]
    omega

theorem countOccurrences_le_append_right (w a b : List ℕ) :
    countOccurrences w a ≤ countOccurrences w (a ++ b) := by
  induction a with
  | nil =>
    simp only [List.nil_append]
    rw [countOccurrences_nil']
    by_cases hw0 : w.isPrefixOf []
    · have hwnil : w = [] := by
        simpa [List.isPrefixOf_iff_prefix, List.prefix_nil] using hw0
      subst hwnil
      have h := if_isPrefixOf_le_countOccurrences [] b
      simpa [List.isPrefixOf_iff_prefix, List.nil_prefix, hw0] using h
    · simp [hw0]
  | cons x a' ih =>
    rw [List.cons_append, countOccurrences_cons, countOccurrences_cons]
    have hmono : (if w.isPrefixOf (x :: a') then 1 else 0)
        ≤ if w.isPrefixOf (x :: (a' ++ b)) then 1 else 0 := by
      by_cases h : w.isPrefixOf (x :: a')
      · have h2 : w.isPrefixOf (x :: (a' ++ b)) := by
          rw [← List.cons_append]
          exact isPrefixOf_append_of_isPrefixOf b h
        simp [h, h2]
      · simp [h]
    omega

theorem countOccurrences_take_le (w l : List ℕ) (n : ℕ) :
    countOccurrences w (l.take n) ≤ countOccurrences w l := by
  conv_rhs => rw [← List.take_append_drop n l]
  exact countOccurrences_le_append_right ..

theorem countOccurrences_drop_le (w l : List ℕ) (n : ℕ) :
    countOccurrences w (l.drop n) ≤ countOccurrences w l := by
  conv_rhs => rw [← List.take_append_drop n l]
  exact countOccurrences_le_append_left ..

/-- Cutting at `n` loses at most `w.length` (seam) occurrences. -/
theorem countOccurrences_le_take_add_drop (w l : List ℕ) (n : ℕ) :
    countOccurrences w l
      ≤ countOccurrences w (l.take n) + countOccurrences w (l.drop n)
        + w.length := by
  conv_lhs => rw [← List.take_append_drop n l]
  exact countOccurrences_append_le ..

/-- Cutting at `n` never gains occurrences (for `w ≠ []`). -/
theorem take_add_drop_countOccurrences_le {w : List ℕ} (hw : w ≠ [])
    (l : List ℕ) (n : ℕ) :
    countOccurrences w (l.take n) + countOccurrences w (l.drop n)
      ≤ countOccurrences w l := by
  conv_rhs => rw [← List.take_append_drop n l]
  exact add_countOccurrences_le_append hw ..

/-- Per-block occurrences survive flattening. -/
theorem sum_countOccurrences_le_flatten {w : List ℕ} (hw : w ≠ [])
    (L : List (List ℕ)) :
    (L.map (countOccurrences w)).sum ≤ countOccurrences w L.flatten := by
  induction L with
  | nil => simp [countOccurrences_nil hw]
  | cons l L' ih =>
    rw [List.flatten_cons, List.map_cons, List.sum_cons]
    calc countOccurrences w l + (L'.map (countOccurrences w)).sum
        ≤ countOccurrences w l + countOccurrences w L'.flatten :=
          Nat.add_le_add_left ih _
    _ ≤ countOccurrences w (l ++ L'.flatten) :=
          add_countOccurrences_le_append hw _ _

/-- No occurrences of `w` in a list shorter than `w`. -/
theorem countOccurrences_eq_zero_of_length_lt {w l : List ℕ}
    (h : l.length < w.length) : countOccurrences w l = 0 := by
  rw [countOccurrences_eq_card_filter_range, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro j hj
  rw [Finset.mem_range] at hj
  intro hpre
  have hle := (List.isPrefixOf_iff_prefix.mp hpre).length_le
  rw [List.length_drop] at hle
  omega

/-! ### Exact interval ↔ digit-string counting

Superseded on the main path by the lower-bound-only layer in
`DigitCount.lean`; see the module docstring above. -/

/-- Exact periodic counting: over an interval whose endpoints are multiples
of `p * q`, the value `n / p % q` hits a fixed `d < q` exactly `p` times
per period `p * q`. Only the lower bound `le_card_Ico_filter_div_mod`
(proved directly in `DigitCount.lean`) feeds `champernowne_normal`. -/
theorem card_Ico_filter_div_mod {A B p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : d < q) (hA : p * q ∣ A) (hB : p * q ∣ B) :
    ((Finset.Ico A B).filter (fun n => n / p % q = d)).card
      = (B / (p * q) - A / (p * q)) * p := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hdpr : ∀ r < p, d * p + r < p * q := by
    intro r hr
    calc d * p + r < (d + 1) * p := by rw [Nat.succ_mul]; omega
    _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
    _ = p * q := Nat.mul_comm q p
  rw [show (B / (p * q) - A / (p * q)) * p
      = ((Finset.Ico (A / (p * q)) (B / (p * q))) ×ˢ Finset.range p).card by
    rw [Finset.card_product, Nat.card_Ico, Finset.card_range]]
  apply Finset.card_nbij' (i := fun n => (n / (p * q), n % p))
    (j := fun x => x.1 * (p * q) + d * p + x.2)
  · -- forward map lands in the box
    intro n hn
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hn
    obtain ⟨⟨h1, h2⟩, _⟩ := hn
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico,
      Finset.mem_range]
    refine ⟨⟨Nat.div_le_div_right h1, ?_⟩, Nat.mod_lt n hp⟩
    rw [Nat.div_lt_iff_lt_mul hpq, Nat.div_mul_cancel hB]
    exact h2
  · -- inverse map lands in the filtered interval
    rintro ⟨h, r⟩ hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico,
      Finset.mem_range] at hx
    obtain ⟨⟨hh1, hh2⟩, hr⟩ := hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc A = A / (p * q) * (p * q) := (Nat.div_mul_cancel hA).symm
      _ ≤ h * (p * q) := Nat.mul_le_mul_right _ hh1
      _ ≤ h * (p * q) + d * p + r := by
          exact le_add_right (le_add_right le_rfl)
    · calc h * (p * q) + d * p + r
          = h * (p * q) + (d * p + r) := by rw [Nat.add_assoc]
      _ < h * (p * q) + p * q := Nat.add_lt_add_left (hdpr r hr) _
      _ = (h + 1) * (p * q) := by rw [Nat.succ_mul]
      _ ≤ B / (p * q) * (p * q) := Nat.mul_le_mul_right _ (by omega)
      _ = B := Nat.div_mul_cancel hB
    · have hrew : h * (p * q) + d * p + r = r + p * (q * h + d) := by ring
      rw [hrew, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add,
        Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
  · -- left inverse on the filtered interval
    intro n hn
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hn
    obtain ⟨-, hd'⟩ := hn
    change n / (p * q) * (p * q) + d * p + n % p = n
    rw [← hd']
    calc n / (p * q) * (p * q) + n / p % q * p + n % p
        = (q * (n / p / q) + n / p % q) * p + n % p := by
          rw [← Nat.div_div_eq_div_mul]; ring
    _ = n / p * p + n % p := by rw [Nat.div_add_mod]
    _ = n := by rw [Nat.mul_comm]; exact Nat.div_add_mod n p
  · -- right inverse on the box
    rintro ⟨h, r⟩ hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico,
      Finset.mem_range] at hx
    obtain ⟨-, hr⟩ := hx
    have h1 : (h * (p * q) + d * p + r) / (p * q) = h := by
      have hrew : h * (p * q) + d * p + r = d * p + r + (p * q) * h := by ring
      rw [hrew, Nat.add_mul_div_left _ _ hpq, Nat.div_eq_of_lt (hdpr r hr),
        Nat.zero_add]
    have h2 : (h * (p * q) + d * p + r) % p = r := by
      have hrew : h * (p * q) + d * p + r = p * (h * q + d) + r := by ring
      rw [hrew, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    exact Prod.ext h1 h2

/-- Every digit of a base-`b` expansion is `< b`. -/
theorem lt_of_mem_bigDigits {b n d : ℕ} (hb : 1 < b)
    (hd : d ∈ bigDigits b n) : d < b :=
  Nat.digits_lt_base hb (List.mem_reverse.mp hd)

/-- The leading digit of a nonzero number is nonzero. -/
theorem head_bigDigits_ne_zero {b n : ℕ} (hn : n ≠ 0) :
    (bigDigits b n).head? ≠ some 0 := by
  have hnil : Nat.digits b n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  change (Nat.digits b n).reverse.head? ≠ some 0
  rw [← List.getLast?_eq_head?_reverse, List.getLast?_eq_getLast_of_ne_nil hnil]
  simpa using Nat.getLast_digit_ne_zero b hn

/-- Round-trip 1: reading the digits of `n` back yields `n`.
Together with the converse, this gives `digitEquiv`. -/
theorem ofDigits_reverse_bigDigits (b n : ℕ) :
    Nat.ofDigits b (bigDigits b n).reverse = n := by
  simp [bigDigits, Nat.ofDigits_digits]

/-- Little-endian form of round-trip 2. -/
theorem digits_ofDigits_reverse {b : ℕ} (hb : 1 < b) {l : List ℕ}
    (hlt : ∀ d ∈ l, d < b) (hhead : l.head? ≠ some 0) :
    Nat.digits b (Nat.ofDigits b l.reverse) = l.reverse := by
  refine Nat.digits_ofDigits b hb l.reverse
    (fun d hd => hlt d (List.mem_reverse.mp hd)) ?_
  intro h hgl0
  apply hhead
  have h? : l.reverse.getLast? = l.head? := by
    rw [List.getLast?_eq_head?_reverse, List.reverse_reverse]
  rw [← h?, List.getLast?_eq_getLast_of_ne_nil h, hgl0]

/-- Round-trip 2: a digit string with nonzero head is the digit expansion of
the number it denotes. (Also holds for `l = []`.) -/
theorem bigDigits_ofDigits_reverse {b : ℕ} (hb : 1 < b) {l : List ℕ}
    (hlt : ∀ d ∈ l, d < b) (hhead : l.head? ≠ some 0) :
    bigDigits b (Nat.ofDigits b l.reverse) = l := by
  simp only [bigDigits, digits_ofDigits_reverse hb hlt hhead,
    List.reverse_reverse]

/-- A length-`m` digit string with nonzero head denotes an `m`-digit number. -/
theorem ofDigits_reverse_mem_Ico {b m : ℕ} (hb : 1 < b) (hm : 0 < m)
    {l : List ℕ} (hlen : l.length = m) (hlt : ∀ d ∈ l, d < b)
    (hhead : l.head? ≠ some 0) :
    Nat.ofDigits b l.reverse ∈ Finset.Ico (b ^ (m - 1)) (b ^ m) := by
  have hlength : (Nat.digits b (Nat.ofDigits b l.reverse)).length = m := by
    rw [digits_ofDigits_reverse hb hlt hhead, List.length_reverse, hlen]
  rw [Finset.mem_Ico]
  exact ⟨(Nat.lt_digits_length_iff hb _).mp (by omega),
    (Nat.digits_length_le_iff hb _).mp (by omega)⟩

/-- Big-endian digit extraction: position `j` of an `m`-digit number `n` is
`n / b^(m-1-j) % b`. -/
theorem getElemOption_bigDigits {b m n : ℕ} (hb : 1 < b)
    (hlen : (bigDigits b n).length = m) {j : ℕ} (hj : j < m) :
    (bigDigits b n)[j]? = some (n / b ^ (m - 1 - j) % b) := by
  have hlen' : (Nat.digits b n).length = m := by
    simpa [bigDigits] using hlen
  change (Nat.digits b n).reverse[j]? = _
  rw [List.getElem?_reverse (by omega), hlen',
    List.getElem?_eq_getElem (by omega)]
  have hgd := Nat.getD_digits n (m - 1 - j) (show 2 ≤ b from hb)
  rw [List.getD_eq_getElem _ _ (by omega)] at hgd
  exact congrArg some hgd

/-- `m`-digit numbers ≃ length-`m` digit strings with nonzero head.
Forward map `bigDigits b`; inverse `Nat.ofDigits b ∘ List.reverse`.
The normality proof uses only lower-bound cardinality consequences. -/
def digitEquiv {b : ℕ} (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    Finset.Ico (b ^ (m - 1)) (b ^ m) ≃
    {l : List ℕ // l.length = m ∧ (∀ d ∈ l, d < b) ∧ l.head? ≠ some 0} where
  toFun n :=
    have hn := Finset.mem_Ico.mp n.2
    ⟨bigDigits b n, length_bigDigits_eq hb hn.1 hn.2,
      fun _ hd => lt_of_mem_bigDigits hb hd,
      head_bigDigits_ne_zero (by
        have hP : 0 < b ^ (m - 1) := pow_pos (by omega) _
        have h1 := hn.1
        omega)⟩
  invFun l := ⟨Nat.ofDigits b l.1.reverse,
    ofDigits_reverse_mem_Ico hb hm l.2.1 l.2.2.1 l.2.2.2⟩
  left_inv n := Subtype.ext (ofDigits_reverse_bigDigits b n)
  right_inv l := Subtype.ext (bigDigits_ofDigits_reverse hb l.2.2.1 l.2.2.2)

/-- Interior positions: block `w` occurs at position `0 < j` in exactly
`(b-1)·b^(m - w.length - 1)` of the `m`-digit numbers, independently of
`j` and of `w` itself. -/
theorem card_blockAt {b : ℕ} (hb : 1 < b) (m j : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hj : 0 < j) (hjk : j + w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card
      = (b - 1) * b ^ (m - w.length - 1) := by
  have hD : Nat.ofDigits b w.reverse < b ^ w.length := by
    have h := Nat.ofDigits_lt_base_pow_length hb
      (fun d hd => hw d (List.mem_reverse.mp hd))
    rwa [List.length_reverse] at h
  have hcongr : (Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)
      = (Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => n / b ^ (m - j - w.length) % b ^ w.length
        = Nat.ofDigits b w.reverse) := by
    apply Finset.filter_congr
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact block_eq_iff hb (length_bigDigits_eq hb hn.1 hn.2) hw hjk
  have hpq : b ^ (m - j - w.length) * b ^ w.length = b ^ (m - j) := by
    rw [← pow_add]; congr 1; omega
  rw [hcongr, card_Ico_filter_div_mod (pow_pos (by omega) _)
    (pow_pos (by omega) _) hD (hpq ▸ pow_dvd_pow b (by omega))
    (hpq ▸ pow_dvd_pow b (by omega)), hpq,
    Nat.pow_div (by omega) (by omega), Nat.pow_div (by omega) (by omega)]
  have h1 : b ^ (m - (m - j)) = b * b ^ (m - 1 - (m - j)) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : b ^ (m - 1 - (m - j)) * b ^ (m - j - w.length)
      = b ^ (m - w.length - 1) := by
    rw [← pow_add]; congr 1; omega
  have hbr : (b - 1) * b ^ (m - 1 - (m - j)) + b ^ (m - 1 - (m - j))
      = b * b ^ (m - 1 - (m - j)) := by
    have hb1 : b - 1 + 1 = b := by omega
    calc (b - 1) * b ^ (m - 1 - (m - j)) + b ^ (m - 1 - (m - j))
        = (b - 1 + 1) * b ^ (m - 1 - (m - j)) := by ring
    _ = b * b ^ (m - 1 - (m - j)) := by rw [hb1]
  rw [h1, show b * b ^ (m - 1 - (m - j)) - b ^ (m - 1 - (m - j))
      = (b - 1) * b ^ (m - 1 - (m - j)) by omega,
    Nat.mul_assoc, h2]

/-- Head position: a block with nonzero head occurs at position `0` in
exactly `b^(m - w.length)` of the `m`-digit numbers. -/
theorem card_blockAt_head {b : ℕ} (hb : 1 < b) (m : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hw0 : w.head? ≠ some 0)
    (hk : w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop 0).take w.length = w)).card
      = b ^ (m - w.length) := by
  have hkpos : 0 < w.length := List.length_pos_of_ne_nil hwne
  have hmem := ofDigits_reverse_mem_Ico hb hkpos rfl hw hw0
  rw [Finset.mem_Ico] at hmem
  have hP : 0 < b ^ (m - w.length) := pow_pos (by omega) _
  have hbm : b ^ w.length * b ^ (m - w.length) = b ^ m := by
    rw [← pow_add]; congr 1; omega
  have hbm1 : b ^ (w.length - 1) * b ^ (m - w.length) = b ^ (m - 1) := by
    rw [← pow_add]; congr 1; omega
  have hset : (Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop 0).take w.length = w)
      = Finset.Ico (Nat.ofDigits b w.reverse * b ^ (m - w.length))
        ((Nat.ofDigits b w.reverse + 1) * b ^ (m - w.length)) := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, hblk⟩
      rw [block_eq_iff hb (length_bigDigits_eq hb h1 h2) hw (by omega),
        show m - 0 - w.length = m - w.length from rfl] at hblk
      have hdiv : n / b ^ (m - w.length) < b ^ w.length := by
        rw [Nat.div_lt_iff_lt_mul hP]
        omega
      rw [Nat.mod_eq_of_lt hdiv] at hblk
      constructor
      · rw [← hblk]
        exact (Nat.le_div_iff_mul_le hP).mp le_rfl
      · rw [← hblk]
        exact (Nat.div_lt_iff_lt_mul hP).mp (by omega)
    · rintro ⟨hlo, hhi⟩
      have hmem1 : b ^ (m - 1) ≤ n := by
        calc b ^ (m - 1) = b ^ (w.length - 1) * b ^ (m - w.length) :=
            hbm1.symm
        _ ≤ Nat.ofDigits b w.reverse * b ^ (m - w.length) :=
            Nat.mul_le_mul_right _ hmem.1
        _ ≤ n := hlo
      have hmem2 : n < b ^ m := by
        calc n < (Nat.ofDigits b w.reverse + 1) * b ^ (m - w.length) := hhi
        _ ≤ b ^ w.length * b ^ (m - w.length) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = b ^ m := hbm
      have hdiv : n / b ^ (m - w.length) = Nat.ofDigits b w.reverse := by
        have hlow := (Nat.le_div_iff_mul_le hP).mpr hlo
        have hhigh := (Nat.div_lt_iff_lt_mul hP).mpr hhi
        omega
      refine ⟨⟨hmem1, hmem2⟩, ?_⟩
      rw [block_eq_iff hb (length_bigDigits_eq hb hmem1 hmem2) hw (by omega),
        show m - 0 - w.length = m - w.length from rfl, hdiv,
        Nat.mod_eq_of_lt (by omega)]
  rw [hset, Nat.card_Ico, Nat.succ_mul]
  omega

/-- Past the end: no window of length `w.length` starts after `m - w.length`. -/
theorem card_blockAt_past_end {b : ℕ} (hb : 1 < b) (m j : ℕ) {w : List ℕ}
    (hwne : w ≠ []) (hj : m < j + w.length) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop j).take w.length = w)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n hn
  rw [Finset.mem_Ico] at hn
  have hlen := length_bigDigits_eq hb hn.1 hn.2
  intro heq
  have hlw := congrArg List.length heq
  rw [List.length_take, List.length_drop, hlen] at hlw
  have hkpos := List.length_pos_of_ne_nil hwne
  omega

/-- Head position, leading zero: a block with head `0` never occurs at
position `0` of an `m`-digit number. -/
theorem card_blockAt_head_zero {b : ℕ} (hb : 1 < b) (m : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hw0 : w.head? = some 0) (hk : w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop 0).take w.length = w)).card = 0 := by
  rcases w with _ | ⟨d, w'⟩
  · simp at hw0
  · simp only [List.head?_cons, Option.some_inj] at hw0
    subst hw0
    have hlc : (0 :: w').length = w'.length + 1 := rfl
    have hD : Nat.ofDigits b (0 :: w').reverse < b ^ w'.length := by
      rw [List.reverse_cons, Nat.ofDigits_append]
      have h := Nat.ofDigits_lt_base_pow_length hb
        (fun d hd => hw d (List.mem_cons_of_mem _ (List.mem_reverse.mp hd)))
      rw [List.length_reverse] at h
      simpa [Nat.ofDigits] using h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [block_eq_iff hb (length_bigDigits_eq hb hn.1 hn.2) hw (by omega)]
    intro hcontra
    have hP : 0 < b ^ (m - 0 - (0 :: w').length) := pow_pos (by omega) _
    have hup : b ^ (0 :: w').length * b ^ (m - 0 - (0 :: w').length)
        = b ^ m := by
      rw [← pow_add]; congr 1
      simp only [List.length_cons]
      omega
    have hdiv : n / b ^ (m - 0 - (0 :: w').length)
        < b ^ (0 :: w').length := by
      rw [Nat.div_lt_iff_lt_mul hP]
      omega
    have hlo1 : b ^ ((0 :: w').length - 1) * b ^ (m - 0 - (0 :: w').length)
        = b ^ (m - 1) := by
      rw [← pow_add]; congr 1
      simp only [List.length_cons]
      omega
    have hdivlo : b ^ ((0 :: w').length - 1)
        ≤ n / b ^ (m - 0 - (0 :: w').length) := by
      rw [Nat.le_div_iff_mul_le hP]
      omega
    rw [Nat.mod_eq_of_lt hdiv] at hcontra
    have hlen1 : (0 :: w').length - 1 = w'.length := by
      omega
    rw [hlen1] at hdivlo
    omega

/-- Split a cohort occurrence count into its head contribution and interior windows. -/
theorem sum_countOccurrences_cohort_eq_head {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), countOccurrences w (bigDigits b n)
      = ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
          (fun n => ((bigDigits b n).drop 0).take w.length = w)).card
        + (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by
  have hstep : ∀ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
      countOccurrences w (bigDigits b n)
        = ∑ j ∈ Finset.range (m + 1),
            if ((bigDigits b n).drop j).take w.length = w then 1 else 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hpred : ∀ j ∈ Finset.range (m + 1),
        (w.isPrefixOf ((bigDigits b n).drop j) = true)
          ↔ ((bigDigits b n).drop j).take w.length = w := fun j _ => by
      rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take, eq_comm]
    rw [countOccurrences_eq_card_filter_range,
      length_bigDigits_eq hb hn.1 hn.2, Finset.filter_congr hpred,
      Finset.card_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hswap : ∀ j ∈ Finset.range (m + 1),
      (∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
        if ((bigDigits b n).drop j).take w.length = w then 1 else 0)
      = ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
          (fun n => ((bigDigits b n).drop j).take w.length = w)).card := by
    intro j _
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl hswap, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m - w.length + 1))
      (by omega : m - w.length + 1 ≤ m + 1)]
  have htail : ∑ j ∈ Finset.Ico (m - w.length + 1) (m + 1),
      ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
        (fun n => ((bigDigits b n).drop j).take w.length = w)).card = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    exact card_blockAt_past_end hb m j hwne (by omega)
  rw [htail, Nat.add_zero, ← Finset.range_eq_Ico, Finset.sum_range_succ']
  have hint : ∀ i ∈ Finset.range (m - w.length),
      ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
        (fun n => ((bigDigits b n).drop (i + 1)).take w.length = w)).card
      = (b - 1) * b ^ (m - w.length - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact card_blockAt hb m (i + 1) hw (Nat.succ_pos i) (by omega)
  rw [Finset.sum_congr rfl hint, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  exact Nat.add_comm _ _

/-- Block `w` with nonzero head occurs
`b^(m-k) + (m-k)·(b-1)·b^(m-k-1)` times inside the digit strings of all
`m`-digit numbers (`k := w.length`). -/
theorem sum_countOccurrences_cohort {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ [])
    (hw0 : w.head? ≠ some 0) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
        countOccurrences w (bigDigits b n)
      = b ^ (m - w.length)
        + (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by
  rw [sum_countOccurrences_cohort_eq_head hb m hw hwne hk,
    card_blockAt_head hb m hw hwne hw0 hk]

/-- Block `w` with head `0` occurs `(m-k)·(b-1)·b^(m-k-1)` times inside the
digit strings of all `m`-digit numbers. -/
theorem sum_countOccurrences_cohort_zero {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ [])
    (hw0 : w.head? = some 0) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
        countOccurrences w (bigDigits b n)
      = (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by
  rw [sum_countOccurrences_cohort_eq_head hb m hw hwne hk,
    card_blockAt_head_zero hb m hw hw0 hk, Nat.zero_add]

end Champernowne
