/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import LeanPool.BooleanIsoperimetry.Cascade

/-!
# Macaulay increment arithmetic

This file develops the increment profile of the Harper boundary function and
the nested-cascade inequalities used by the final minimization argument.
-/

open scoped BigOperators

namespace BooleanIsoperimetry

/--
The first forward difference of the closed-neighborhood profile of the
simplicial initial segments.  It is stated with truncated subtraction because
`H` is monotone but the project mostly uses additive inequalities over `ℕ`.
-/
noncomputable def HIncrement (n p : ℕ) : ℕ :=
  H n (p + 1) - H n p

lemma H_eq_sum_HIncrement (n k : ℕ) :
    H n k = ∑ p ∈ Finset.range k, HIncrement n p := by
  induction k with
  | zero => simp [H_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold HIncrement
    have hmono : H n k ≤ H n (k + 1) := H_mono (by omega)
    omega

/--
Additive form of the one-step lower bound: the new point contributes at least
`n - p` new neighborhood vertices.  This is a direct corollary of
`H_increment_lower`, but the shape is easier to reuse in cascade-layer
arguments.
-/
lemma H_increment_lower_dim_sub (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    H n p + (n - p) ≤ H n (p + 1) := by
  have h := H_increment_lower n p hp
  have hmono : H n p ≤ H n (p + 1) := H_mono (by omega)
  by_cases hpn : p ≤ n
  · omega
  · have hzero : n - p = 0 := by omega
    rw [hzero]
    exact hmono

/--
First-difference form of `H_increment_lower`: as long as `p + 1` is inside the
`n`-cube, the `p`-th increment of `H n` is at least `n - p`.
-/
lemma HIncrement_lower (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    n - p ≤ HIncrement n p := by
  unfold HIncrement
  have hmono : H n p ≤ H n (p + 1) := H_mono (by omega)
  have h := H_increment_lower_dim_sub n p hp
  omega


/--
The exact first difference of `H` is the number of preimages of the rank-`p` vertex
under `gShift`. This exactly captures the Kruskal-Katona binomial layer profile.
-/
lemma HIncrement_eq_gShift_inv (n p : ℕ) (w : Cube n) (hw : rank w = p) :
    HIncrement n p =
      (Finset.filter (fun v => gShift v = w) (Finset.univ : Finset (Cube n))).card := by
  unfold HIncrement
  rw [H_increment_eq_gShift_inv n p w hw]
  exact Nat.add_sub_cancel_left (H n p) _

/--
**Exact `gShift`-preimage structure of a nonempty vertex.**
For a nonempty vertex `w`, the vertices `v` with `gShift v = w` are *exactly* the
vertices `insert j w` obtained by adding a new minimum coordinate `j` strictly
below `w.min'`.  (Adding such a `j` makes it the new minimum, and `gShift`
removes it again.)  This is the set-level Kruskal–Katona/Macaulay layer
structure: the `gShift`-fibre of `w` is an interval of "lower extensions".

This refines `H_increment_lower` (which only established the `⊇` inclusion and a
cardinality lower bound) to a full equality of fibres, and is the reusable input
for the exact increment-profile value `HIncrement_eq_min'`. -/
lemma gShift_preimage_eq_insert_below_min {n : ℕ} (w : Cube n) (h : w.Nonempty) :
    Finset.univ.filter (fun v : Cube n => gShift v = w)
      = (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' h : ℕ))).image
          (fun j => insert j w) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hgv
    have hv : v.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      rw [gShift, dite_eq_right (by rw [hcon]; exact Finset.not_nonempty_empty)] at hgv
      rw [hcon] at hgv
      exact (h.ne_empty hgv.symm)
    have hg : gShift v = v.erase (v.min' hv) := by unfold gShift; rw [dite_eq_left hv]
    rw [hg] at hgv
    set m := v.min' hv with hm
    refine ⟨m, ?_, ?_⟩
    · -- (m : ℕ) < (w.min' h : ℕ)
      have hmem : (w.min' h) ∈ w := Finset.min'_mem w h
      have hwsub : w ⊆ v := by rw [← hgv]; exact Finset.erase_subset _ _
      have hmin_le : m ≤ w.min' h := Finset.min'_le v (w.min' h) (hwsub hmem)
      have hmnotw : m ∉ w := by rw [← hgv]; exact Finset.notMem_erase _ _
      have hneq : m ≠ w.min' h := by
        intro hc
        exact hmnotw (by rw [hc]; exact hmem)
      have hlt : m < w.min' h := lt_of_le_of_ne hmin_le hneq
      exact hlt
    · -- insert m w = v
      rw [← hgv]
      exact Finset.insert_erase (Finset.min'_mem v hv)
  · rintro ⟨j, hj, rfl⟩
    have hjw : j ∉ w := by
      intro hjmem
      have := Finset.min'_le w j hjmem
      omega
    have hne : (insert j w).Nonempty := ⟨j, Finset.mem_insert_self _ _⟩
    have hmin : (insert j w).min' hne = j := by
      apply le_antisymm
      · exact Finset.min'_le _ j (Finset.mem_insert_self _ _)
      · apply Finset.le_min'
        intro y hy
        rcases Finset.mem_insert.mp hy with h1 | h1
        · rw [h1]
        · have := Finset.min'_le w y h1
          omega
    rw [gShift, dite_eq_left hne, hmin, Finset.erase_insert hjw]

/--
**Exact Macaulay increment profile (minimum-coordinate form).**
The `p`-th first difference of the closed-neighbourhood profile `H` equals the
smallest active coordinate of the (unique) rank-`p` vertex `w`.  Equivalently,
the number of `gShift`-preimages of `w` is `w.min'`.

This is the exact Kruskal–Katona/Macaulay layer-increment value, upgrading the
lower bound `HIncrement_lower` (`n - p ≤ HIncrement n p`, via
`rank_add_min_ge`) to a closed form.  It is reusable, non-circular `H`-increment
theory: it mentions only `H`, `rank`, `gShift`, and `Finset.min'`, and sits well
below the cascade/Macaulay-window leaves in the dependency order. -/
lemma HIncrement_eq_min' {n : ℕ} (p : ℕ) (w : Cube n) (hw : rank w = p) (hne : w.Nonempty) :
    HIncrement n p = (w.min' hne : ℕ) := by
  have hinj : Set.InjOn (fun j : Fin n => insert j w)
      (↑(Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' hne : ℕ)))) := by
    intro j hj j' hj' hjj'
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj hj'
    have hjw : j ∉ w := fun hc => by have := Finset.min'_le w j hc; omega
    simp only at hjj'
    have : j ∈ insert j' w := hjj' ▸ Finset.mem_insert_self j w
    rcases Finset.mem_insert.mp this with h1 | h1
    · exact h1
    · exact absurd h1 hjw
  rw [HIncrement_eq_gShift_inv n p w hw, gShift_preimage_eq_insert_below_min w hne,
      Finset.card_image_of_injOn hinj]
  have himg : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' hne : ℕ))).image (Fin.val)
      = Finset.range (w.min' hne : ℕ) := by
    ext k
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hk; exact ⟨⟨k, by have := (w.min' hne).2; omega⟩, hk, rfl⟩
  calc (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' hne : ℕ))).card
      = ((Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' hne : ℕ))).image (Fin.val)).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ = (Finset.range (w.min' hne : ℕ)).card := by rw [himg]
    _ = (w.min' hne : ℕ) := Finset.card_range _

/-- The empty-rank first difference: adding the empty vertex exposes the whole
closed unit ball around it. -/
lemma HIncrement_zero (n : ℕ) : HIncrement n 0 = n + 1 := by
  unfold HIncrement
  rw [H_one, H_zero]
  omega

/--
The exact Macaulay shadow weight of a rank vertex.  Nonempty vertices contribute
their smallest active coordinate; the empty vertex contributes the `n + 1`
vertices in its closed unit ball.
-/
noncomputable def macaulayShadowWeight {n : ℕ} (w : Cube n) : ℕ :=
  if h : w.Nonempty then (w.min' h : ℕ) else n + 1

lemma rank_eq_zero_of_not_nonempty {n p : ℕ} (w : Cube n) (hw : rank w = p)
    (hempty : ¬ w.Nonempty) : p = 0 := by
  have hwempty : w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [← hw]
  rw [hwempty]
  simp [rank, simplicialLt, simplicialLe]

/--
Uniform exact first-difference formula, including the empty vertex.  This is the
rank-indexed layer profile used to turn a Macaulay shadow window into an
ordinary sum over vertices in the corresponding rank interval.
-/
lemma HIncrement_eq_macaulayShadowWeight {n : ℕ} (p : ℕ) (w : Cube n)
    (hw : rank w = p) :
    HIncrement n p = macaulayShadowWeight w := by
  unfold macaulayShadowWeight
  by_cases h : w.Nonempty
  · simp [h, HIncrement_eq_min' p w hw h]
  · rw [dite_eq_right h]
    have hp0 : p = 0 := rank_eq_zero_of_not_nonempty w hw h
    rw [hp0]
    exact HIncrement_zero n

/-!
### Macaulay layer increment-profile bounds

Reusable upper bounds for the `HIncrement`/min-coordinate layer profile.  The
existing `HIncrement_lower` (`n - p ≤ HIncrement n p`) gives a *global* lower
bound; the lemmas below give the *per-layer upper* bound `HIncrement n j ≤ n - r`
for every rank `j` in Macaulay layer `r` (the cardinality-`r` band
`[binomPrefix n r, binomPrefix n (r+1))`).  This is the increment-profile theory
flagged by the Aristotle obstruction: it pins the increment of a layer-`r` vertex
between `n - (binomPrefix n (r+1) - 1)` and `n - r`, and is exactly the
upper-shadow-window bound used by the Frankl–Füredi/Macaulay window comparisons.

The combinatorial core is the elementary `cube_min'_add_card_le`: a `card`-`r`
subset of `Fin n` has its smallest coordinate plus its cardinality bounded by `n`
(its `r` coordinates all lie in `[min', n)`, an interval of size `n - min'`).
-/

/-- A nonempty vertex of the `n`-cube satisfies `min' + card ≤ n`: its `card`
active coordinates all lie in `[min', n)`, an interval of size `n - min'`.  A
pure `Finset.min'` bound, used for the per-layer increment upper bound. -/
lemma cube_min'_add_card_le {n : ℕ} (w : Cube n) (h : w.Nonempty) :
    (w.min' h : ℕ) + w.card ≤ n := by
  have hsub : w ⊆ Finset.Ici (w.min' h) := fun x hx =>
    Finset.mem_Ici.mpr (Finset.min'_le w x hx)
  have hcard : w.card ≤ (Finset.Ici (w.min' h)).card := Finset.card_le_card hsub
  have hIci : (Finset.Ici (w.min' h)).card = n - (w.min' h : ℕ) := by simp [Fin.card_Ici]
  omega

/-- Every rank below `2 ^ n` is realised by some vertex of the `n`-cube
(`rank` is a bijection onto `range (2 ^ n)`). -/
lemma exists_rank_eq {n j : ℕ} (hj : j < 2 ^ n) : ∃ w : Cube n, rank w = j := by
  have hmem : j ∈ Finset.image (@rank n) Finset.univ := by
    rw [rank_image_eq]; exact Finset.mem_range.mpr hj
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hmem
  exact ⟨w, hw⟩

/-- **Per-layer increment upper bound.**  For a rank `j` in Macaulay layer `r`
(i.e. `binomPrefix n r ≤ j < binomPrefix n (r+1)`, the cardinality-`r` band), the
increment `HIncrement n j` (the min coordinate of the rank-`j` vertex) is at most
`n - r`.  This is the upper companion of `HIncrement_lower`. -/
lemma HIncrement_le_of_mem_layer {n r j : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ j) (hhi : j < binomPrefix n (r + 1)) :
    HIncrement n j ≤ n - r := by
  have hj2 : j < 2 ^ n := lt_of_lt_of_le hhi (binomPrefix_le_two_pow n (r + 1))
  obtain ⟨w, hw⟩ := exists_rank_eq hj2
  have hcard_le : w.card ≤ r := by
    have := (rank_lt_binomPrefix_iff (c := r + 1) w).mp (by rw [hw]; exact hhi); omega
  have hcard_ge : r ≤ w.card := by
    by_contra hlt; push Not at hlt
    have : rank w < binomPrefix n r := (rank_lt_binomPrefix_iff (c := r) w).mpr hlt
    rw [hw] at this; omega
  have hcard : w.card = r := le_antisymm hcard_le hcard_ge
  have hne : w.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  rw [HIncrement_eq_min' j w hw hne]
  have hmc := cube_min'_add_card_le w hne; omega

/-- **Per-layer increment window bound.**  A length-`L` rank window contained in a
single Macaulay layer `r` has total `HIncrement` mass at most `L * (n - r)`.  This
is the reusable upper-shadow-window bound for a window confined to one layer; it
follows by summing `HIncrement_le_of_mem_layer` over the window. -/
lemma HIncrement_window_le_of_layer {n r a L : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ a) (hhi : a + L ≤ binomPrefix n (r + 1)) :
    (∑ i ∈ Finset.Ico a (a + L), HIncrement n i) ≤ L * (n - r) := by
  have hbound : ∀ i ∈ Finset.Ico a (a + L), HIncrement n i ≤ n - r := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact HIncrement_le_of_mem_layer hr (le_trans hlo hi.1) (lt_of_lt_of_le hi.2 hhi)
  calc (∑ i ∈ Finset.Ico a (a + L), HIncrement n i)
      ≤ ∑ _i ∈ Finset.Ico a (a + L), (n - r) := Finset.sum_le_sum hbound
    _ = L * (n - r) := by rw [Finset.sum_const, Nat.card_Ico]; simp

/--
Exact interval form of the Macaulay layer profile: a rank window of
`HIncrement` is the sum of the explicit shadow weights of the vertices whose
ranks lie in the same interval.  The endpoint bound `hi ≤ 2^n` is the natural
cube-capacity condition used by all Harper windows.
-/
lemma HIncrement_window_eq_macaulayShadowWeight_sum
    (n lo hi : ℕ) (hhi : hi ≤ 2 ^ n) :
    (∑ i ∈ Finset.Ico lo hi, HIncrement n i) =
      ∑ w ∈ (Finset.univ.filter (fun w : Cube n => lo ≤ rank w ∧ rank w < hi)),
        macaulayShadowWeight w := by
  let S : Finset (Cube n) :=
    Finset.univ.filter (fun w : Cube n => lo ≤ rank w ∧ rank w < hi)
  have himage : S.image rank = Finset.Ico lo hi := by
    ext i
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Ico]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hiI
      have hi_range : i ∈ Finset.range (2 ^ n) :=
        Finset.mem_range.mpr (lt_of_lt_of_le hiI.2 hhi)
      obtain ⟨w, _hwuniv, hrank⟩ :=
        Finset.mem_image.mp (by
          simpa [rank_image_eq] using hi_range :
            i ∈ Finset.univ.image (@rank n))
      exact ⟨w, by simpa [hrank] using hiI, hrank⟩
  rw [← himage]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w _hwS
    exact HIncrement_eq_macaulayShadowWeight (rank w) w rfl
  · intro x _hx y _hy hxy
    exact rank_injective hxy

/--
Strictness consequence of the increment lower bound: before rank `n`, extending
the initial segment by one strictly enlarges its closed neighborhood.
-/
lemma H_strictMono_on_initial_layer {n p : ℕ} (hp : p + 1 ≤ 2 ^ n) (hpn : p < n) :
    H n p < H n (p + 1) := by
  have h := H_increment_lower_dim_sub n p hp
  omega

/--
The genuine inductive content of Harper's inequality, isolated as a single
statement with the induction hypothesis `ih` supplied explicitly.  This is the
*sole remaining open step*: it is exactly the inductive step of Harper's
vertex-isoperimetric theorem ("the canonical cascade split minimises the cross
boundary expression"), which is not currently in Mathlib.

Given the canonical cascade split `(p, q)` of `a + b` (so
`H (n+1) (a+b) = max (H n p) q + max (H n q) p` by `H_succ_cascade`), and given
Harper's inequality at all strictly smaller dimensions (`ih`), the canonical
split has boundary value no larger than the value of any other split `(a, b)`.

It is stated non-circularly: it refers only to `H`, `CascadeSplit`, and the
induction hypothesis `ih`, never to `boundaryCost`, `CascadeInterleaves`,
`H_inequality_core`, or any later result that ultimately depends on it.

WHAT IS KNOWN (verified by computation for `n ≤ 4`):  after reducing the left
side to `H n p + H n q` (using `q ≤ p ≤ H n q` from the cascade), and taking
`a ≥ b` by symmetry, the goal splits into
  * Case I (`a ≤ H n b`):  `H n p + H n q ≤ H n a + H n b`;
  * Case II (`a > H n b`): `H n p + H n q ≤ H n a + a`.
Both are true; closing them is the missing combinatorial heart (a compression /
nested-cascade interleaving argument using `ih`).
-/
lemma canonical_boundaryCost_eq_H_add
    {n k p q : ℕ} (hp : p ≤ 2 ^ n) (_hq : q ≤ 2 ^ n) (hq_pos : 1 ≤ q)
    (h_casc : CascadeSplit n k p q) :
    max (H n p) q + max (H n q) p = H n p + H n q := by
  have h1 : q ≤ p := cascade_q_le_p h_casc
  have h2 : p ≤ H n p := H_ge_self n p hp
  have h3 : q ≤ H n p := le_trans h1 h2
  have h4 : p ≤ H n q := cascade_p_le_H_q h_casc hq_pos
  have max1 : max (H n p) q = H n p := max_eq_left h3
  have max2 : max (H n q) p = H n q := max_eq_left h4
  rw [max1, max2]

lemma boundaryCost_comm (n a b : ℕ) :
    max (H n a) b + max (H n b) a =
    max (H n b) a + max (H n a) b := by
  omega

lemma boundaryCost_eq_case_le
    {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb_le_a : b ≤ a) (hcase : a ≤ H n b) :
    max (H n a) b + max (H n b) a = H n a + H n b := by
  have h1 : a ≤ H n a := H_ge_self n a ha
  have h2 : b ≤ H n a := le_trans hb_le_a h1
  have max1 : max (H n a) b = H n a := max_eq_left h2
  have max2 : max (H n b) a = H n b := max_eq_left hcase
  rw [max1, max2]

lemma boundaryCost_eq_case_gt
    {n a b : ℕ} (ha : a ≤ 2 ^ n) (hb_le_a : b ≤ a) (hcase : H n b < a) :
    max (H n a) b + max (H n b) a = H n a + a := by
  have h1 : a ≤ H n a := H_ge_self n a ha
  have h2 : b ≤ H n a := le_trans hb_le_a h1
  have max1 : max (H n a) b = H n a := max_eq_left h2
  have max2 : max (H n b) a = a := max_eq_right (le_of_lt hcase)
  rw [max1, max2]

lemma harper_bc_min_q_zero_core (n : ℕ) {a b p : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit n (a + b) p 0) :
    H n p + p ≤ max (H n a) b + max (H n b) a := by
  rcases hcasc with ⟨ r, t, hr, rfl, ht ⟩;
  rcases r with ( _ | r ) <;>
    simp +arith +decide only [cascadeSlice1Value, zero_tsub, add_tsub_cancel_right] at ht ⊢;
  · cases hr; norm_num [ binomPrefix, choosePred ] at *;
    aesop;
  · rcases r with ( _ | r ) <;>
    simp +arith +decide only [binomPrefix_succ, choosePred, zero_add] at ht ⊢;
    · rcases t with ( _ | _ | t ) <;>
      simp +arith +decide only [binomPrefix_zero, ↓reduceIte, tsub_self,
        Nat.choose_zero_right, zero_le, inf_of_le_left, add_zero, zero_add,
        zero_ne_one, le_add_iff_nonneg_left, inf_of_le_right] at ht ⊢;
      simp +arith +decide only [cascadeSlice0Value, binomPrefix, zero_add,
        Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, zero_tsub,
        add_zero, Order.add_one_le_iff] at hpq ⊢;
      rcases a with ( _ | _ | a ) <;> rcases b with ( _ | _ | b ) <;> simp +arith +decide at *;
    · rw [ eq_comm ] at ht; simp_all +arith +decide [ binomPrefix ];
      grind +suggestions

lemma harper_bc_min_q_zero (n : ℕ)
    (_ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit n (a + b) p 0) :
    H n p + p ≤ max (H n a) b + max (H n b) a :=
  harper_bc_min_q_zero_core n ha hb hp hb_le_a hpq hcasc

lemma cascade_max_eq_right {n x x0 x1 : ℕ} (hx : CascadeSplit n x x0 x1) :
    max (H n x1) x0 = if 1 ≤ x1 then H n x1 else x0 := by
  split_ifs with h
  · apply max_eq_left
    exact cascade_p_le_H_q hx h
  · have h0 : x1 = 0 := by omega
    subst h0
    rw [H_zero]
    exact max_eq_right (Nat.zero_le _)

lemma H_succ_cascade_expand {n x x0 x1 : ℕ} (hx : CascadeSplit n x x0 x1) (hx0 : x0 ≤ 2 ^ n) :
    max (H n x0) x1 + max (H n x1) x0 = H n x0 + if 1 ≤ x1 then H n x1 else x0 := by
  have h1 : max (H n x0) x1 = H n x0 := by
    apply max_eq_left
    exact le_trans (cascade_q_le_p hx) (H_ge_self n x0 hx0)
  rw [h1, cascade_max_eq_right hx]

/--
The level-`n` Harper extremal inequality, extracted from the induction
hypothesis `ih` (at `m = n`) and packaged for canonical cascade splits.

Given the canonical cascade split `(p, q)` of `a + b` at level `n`, its cross
boundary cost is no larger than that of the arbitrary split `(a, b)`.  This is
exactly `ih n` rewritten through `H_succ_cascade`; it is the *one-dimension-lower*
Macaulay/Harper extremal statement, used as a tool for the genuine
`n → n+1` inductive step below.
-/
lemma harper_extremal_n (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (hcasc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  rw [← H_succ_cascade hcasc]
  exact ih n (Nat.lt_succ_self n) a b ha hb

lemma cascade_p_le {n k p q : ℕ} (h : CascadeSplit n k p q) : p ≤ 2 ^ n := by
  obtain ⟨r, t, ht, h1, h2⟩ := h
  exact h1 ▸ cascadeSlice0Value_le ht

lemma cascade_q_le {n k p q : ℕ} (h : CascadeSplit n k p q) : q ≤ 2 ^ n := by
  obtain ⟨r, t, ht, h1, h2⟩ := h
  exact h2 ▸ cascadeSlice1Value_le ht

/--
The degenerate top-level branch of the nested extremal step.  When the canonical
upper slice `q` is empty, the statement reduces to the already-proved
`harper_bc_min_q_zero` in dimension `n + 1` (with a symmetric `a,b` branch).
-/
lemma harper_extremal_step_nested_q_zero (n : ℕ)
    (_ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_zero : q = 0)
    (_hp0 : p0 ≤ 2 ^ n) (_hp1 : p1 ≤ 2 ^ n)
    (_hq0 : q0 ≤ 2 ^ n) (_hq1 : q1 ≤ 2 ^ n)
    (_ha0 : a0 ≤ 2 ^ n) (_ha1 : a1 ≤ 2 ^ n)
    (_hb0 : b0 ≤ 2 ^ n) (_hb1 : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    max (max (H n p0) p1 + max (H n p1) p0) q +
    max (max (H n q0) q1 + max (H n q1) q0) p ≤
    max (max (H n a0) a1 + max (H n a1) a0) b +
    max (max (H n b0) b1 + max (H n b1) b0) a := by
  subst q
  have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hpq : p = a + b := by
    have hsum := cascade_split_add hcasc
    omega
  rw [← H_succ_cascade hp_split, ← H_succ_cascade hq_split,
      ← H_succ_cascade ha_split, ← H_succ_cascade hb_split]
  simp only [H_zero, Nat.max_zero, Nat.zero_max]
  by_cases hba : b ≤ a
  · exact harper_bc_min_q_zero_core (n + 1) ha hb hp hba hpq hcasc
  · have hab : a ≤ b := le_of_not_ge hba
    have hcasc_comm : CascadeSplit (n + 1) (b + a) p 0 := by
      simpa [Nat.add_comm] using hcasc
    have hpq_comm : p = b + a := by omega
    have h := harper_bc_min_q_zero_core (n + 1) hb ha hp hab hpq_comm hcasc_comm
    rwa [boundaryCost_comm (n + 1) a b]

/--
Monotonicity of the canonical cascade slices.  If `x ≤ y` then both canonical
slice values of `x` are dominated by those of `y`.  This is because the lower
(resp. upper) slice of a simplicial initial segment is monotone in the segment
size (initial segments are nested), and `slice_card_eq_cascade` identifies these
slice cardinalities with the cascade split values.
-/
lemma cascade_slice_mono {n x x0 x1 y y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) (hxy : x ≤ y) :
    x0 ≤ y0 ∧ x1 ≤ y1 := by
  obtain ⟨hx0, hx1⟩ := slice_card_eq_cascade hx
  obtain ⟨hy0, hy1⟩ := slice_card_eq_cascade hy
  have hsub : simplicialInitSeg (n + 1) x ⊆ simplicialInitSeg (n + 1) y :=
    initSeg_nested hxy
  constructor
  · rw [← hx0, ← hy0]
    apply Finset.card_le_card
    intro v hv
    simp only [slice0, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hsub hv
  · rw [← hx1, ← hy1]
    apply Finset.card_le_card
    intro v hv
    simp only [slice1, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hsub hv

/--
In the GT regime of the inductive step (the larger part `a` exceeds the
neighbourhood `H (n+1) b` of the smaller part `b`), the canonical lower slice
`p` of `a + b` is at most `a`.

Proof: if `a < p` then, since `p + q = a + b`, the upper slice satisfies
`q < b`; but the canonical compression gives `p ≤ H (n+1) q ≤ H (n+1) b < a`,
contradicting `a < p`.  This is a clean structural consequence of
`cascade_p_le_H_q`, `H_mono`, and `cascade_split_add`; it is non-circular
(it does not use any later Harper result).
-/
lemma cascade_lower_le_of_neighbor_lt {n a b p q : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q) (hq_pos : 1 ≤ q)
    (hcase : H (n + 1) b < a) : p ≤ a := by
  by_contra h
  push Not at h
  have hsum : p + q = a + b := cascade_split_add hcasc
  have hqb : q < b := by omega
  have hpHq : p ≤ H (n + 1) q := cascade_p_le_H_q hcasc hq_pos
  have hmono : H (n + 1) q ≤ H (n + 1) b := H_mono (le_of_lt hqb)
  omega

/-- Every positive canonical split with empty upper subslice has mass exactly one. -/
lemma one_le_binomPrefix_succ (n r : ℕ) : 1 ≤ binomPrefix n (r + 1) := by
  induction r with
  | zero => simp [binomPrefix_succ, binomPrefix_zero]
  | succ r ih =>
      exact le_trans ih (binomPrefix_mono n (Nat.succ_le_succ (Nat.le_succ r)))

/--
If the upper slice in a canonical split is zero but the split mass is positive,
then the split mass is the singleton initial segment.
-/
lemma cascade_upper_zero_eq_one {n q q0 q1 : ℕ}
    (h : CascadeSplit n q q0 q1) (hq_pos : 1 ≤ q) (hq1_zero : q1 = 0) :
    q = 1 := by
  rcases h with ⟨r, t, hr, _hq0, hq1⟩
  rcases hr with ⟨_hrle, _ht, hqeq, hcanon⟩
  rw [hq1] at hq1_zero
  unfold cascadeSlice1Value at hq1_zero
  rcases r with _ | r
  · simp [binomPrefix_zero] at hq1_zero
    simp [binomPrefix_zero] at hqeq
    have hcanon' : t < 1 := by
      rcases hcanon with hcanon | hcanon
      · simpa using hcanon
      · omega
    omega
  · rcases r with _ | r
    · simp [binomPrefix_zero, choosePred] at hq1_zero
      simp [binomPrefix_succ, binomPrefix_zero] at hqeq
      omega
    · have hpos := one_le_binomPrefix_succ n r
      simp [choosePred] at hq1_zero
      omega

/--
If the upper slice in a canonical split is zero, then the split mass is in the
bottom layer: it is either empty or the singleton initial segment.
-/
lemma cascade_upper_zero_eq_zero_or_one {n q q0 q1 : ℕ}
    (h : CascadeSplit n q q0 q1) (hq1_zero : q1 = 0) :
    q = 0 ∨ q = 1 := by
  by_cases hq_pos : 1 ≤ q
  · exact Or.inr (cascade_upper_zero_eq_one h hq_pos hq1_zero)
  · exact Or.inl (by omega)

/-- In the same situation, the lower slice is the whole split mass. -/
lemma cascade_upper_zero_lower_eq {n q q0 q1 : ℕ}
    (h : CascadeSplit n q q0 q1) (hq1_zero : q1 = 0) :
    q0 = q := by
  have hsum := cascade_split_add h
  omega

/--
A full binomial prefix `binomPrefix (n+1) r` splits canonically into the corresponding
full layers `binomPrefix n r` and `binomPrefix n (r-1)` in the lower dimensions.
-/
lemma cascade_split_binomPrefix (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n + 1) :
    CascadeSplit n (binomPrefix (n + 1) r) (binomPrefix n r) (binomPrefix n (r - 1)) := by
  have _hr_used : 1 ≤ r := hr
  refine ⟨r, 0, ?_, ?_, ?_⟩
  · refine ⟨by omega, by simp, by simp, ?_⟩
    left
    exact Nat.choose_pos hrn
  · unfold cascadeSlice0Value
    simp
  · unfold cascadeSlice1Value
    simp

/--
The boundary of a full binomial prefix (a complete collection of layers) is exactly
the next full binomial prefix, evaluated algebraically on `H`.
-/
lemma H_binomPrefix (n r : ℕ) (hr : 1 ≤ r) :
    H n (binomPrefix n r) = binomPrefix n (r + 1) := by
  induction n generalizing r with
  | zero =>
      rw [binomPrefix_eq_two_pow_of_ge 0 r (by omega),
          binomPrefix_eq_two_pow_of_ge 0 (r + 1) (by omega),
          H_full]
  | succ n ih =>
      by_cases hrn : r ≤ n + 1
      · have hcasc := cascade_split_binomPrefix n r hr hrn
        rw [H_succ_cascade hcasc]
        by_cases hr_one : r = 1
        · subst r
          have hbp1 : binomPrefix n 1 = 1 := by
            simp [binomPrefix_succ, binomPrefix_zero]
          rw [hbp1, binomPrefix_zero, H_one, H_zero]
          simp [binomPrefix_succ, binomPrefix_zero, binomPrefix_pascal]
          omega
        · have hr_pred : 1 ≤ r - 1 := by omega
          have hHr := ih r hr
          have hHpred := ih (r - 1) hr_pred
          rw [hHr, hHpred]
          rw [show r - 1 + 1 = r by omega]
          have hmono₁ : binomPrefix n (r - 1) ≤ binomPrefix n (r + 1) :=
            binomPrefix_mono n (by omega)
          rw [max_eq_left hmono₁, max_eq_left (le_rfl : binomPrefix n r ≤ binomPrefix n r)]
          rw [binomPrefix_pascal n (r + 1)]
          rw [show r + 1 - 1 = r by omega]
      · have hfull : binomPrefix (n + 1) r = 2 ^ (n + 1) :=
          binomPrefix_eq_two_pow_of_ge (n + 1) r (by omega)
        have hfull_next : binomPrefix (n + 1) (r + 1) = 2 ^ (n + 1) :=
          binomPrefix_eq_two_pow_of_ge (n + 1) (r + 1) (by omega)
        rw [hfull, hfull_next, H_full]

/--
The first full binomial-prefix jump of `H`: the closed neighbourhood of the
singleton initial segment contains both the empty layer and the first layer.
-/
lemma H_binomPrefix_first_diff (n : ℕ) :
    H n (binomPrefix n 1) - H n (binomPrefix n 0) =
      Nat.choose n 0 + Nat.choose n 1 := by
  rw [H_binomPrefix n 1 (by omega), binomPrefix_zero, H_zero]
  simp [binomPrefix_zero, binomPrefix_succ]

/--
Layer-precise increment behavior away from the empty-prefix edge case: the
total increment of `H` across the `r`-th positive binomial layer is exactly its
size `Nat.choose n r`. This is required because `H` is not concave across layer
boundaries.
-/
lemma H_binomPrefix_diff (n r : ℕ) (hr : 2 ≤ r) :
    H n (binomPrefix n r) - H n (binomPrefix n (r - 1)) = Nat.choose n r := by
  have hr_pos : 1 ≤ r := by omega
  have hr_pred : 1 ≤ r - 1 := by omega
  rw [H_binomPrefix n r hr_pos, H_binomPrefix n (r - 1) hr_pred]
  rw [show r - 1 + 1 = r by omega]
  rw [binomPrefix_succ]
  omega

/--
Adjacent full-binomial-prefix form of the same layer calculation.  This avoids
subtraction from `r - 1` and is often the cleaner statement for induction over
cascade layers.
-/
lemma H_binomPrefix_succ_diff (n r : ℕ) (hr : 1 ≤ r) :
    H n (binomPrefix n (r + 1)) - H n (binomPrefix n r) =
      Nat.choose n (r + 1) := by
  simpa [Nat.succ_eq_add_one] using H_binomPrefix_diff n (r + 1) (by omega)

/--
Additive full-layer form of `H_binomPrefix_succ_diff`.  This avoids truncated
subtraction and is the shape needed when comparing sums of whole
Kruskal-Katona/Macaulay layers.
-/
lemma H_binomPrefix_add_layer (n r : ℕ) (hr : 1 ≤ r) :
    H n (binomPrefix n r) + Nat.choose n (r + 1) =
      H n (binomPrefix n (r + 1)) := by
  rw [H_binomPrefix n r hr, H_binomPrefix n (r + 1) (by omega)]
  rw [binomPrefix_succ n (r + 1)]

/--
Additive window form for complete binomial layers: moving `H` from the full
prefix below layer `r` to the full prefix below layer `s` adds exactly the
whole layers `r+1, ..., s`.  This is a reusable whole-block version of the
increment-window profile behind the positive-cascade obstruction.
-/
lemma H_binomPrefix_window (n r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    H n (binomPrefix n r) +
        (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i) =
      H n (binomPrefix n s) := by
  rw [H_binomPrefix n r hr, H_binomPrefix n s (by omega)]
  exact Finset.sum_range_add_sum_Ico (fun i => Nat.choose n i) (by omega : r + 1 ≤ s + 1)

/--
Partial-layer upper bound for `H` on complete binomial prefixes.  If only `t`
points of the next Macaulay layer are available, with `t` no larger than the
whole next layer, then adding `t` to the boundary of the lower full prefix
stays below the boundary of the next full prefix.

This is the inequality form of `H_binomPrefix_add_layer`, useful when a cascade
comparison cuts through a layer rather than moving by a whole binomial block.
-/
lemma H_binomPrefix_partial_layer_le (n r t : ℕ) (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose n (r + 1)) :
    H n (binomPrefix n r) + t ≤ H n (binomPrefix n (r + 1)) := by
  rw [← H_binomPrefix_add_layer n r hr]
  omega

/--
Partial-window upper bound for `H` on complete binomial prefixes.  Any amount
`t` bounded by the total size of the complete layers from `r+1` through `s`
can be added to `H` at the lower full prefix without exceeding `H` at the upper
full prefix.

This packages the full-window equality in the one-sided form needed for
partial-window majorization and nested-cascade interleaving arguments.
-/
lemma H_binomPrefix_partial_window_le (n r s t : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s)
    (ht : t ≤ (Finset.Ico (r + 1) (s + 1)).sum (fun i => Nat.choose n i)) :
    H n (binomPrefix n r) + t ≤ H n (binomPrefix n s) := by
  rw [← H_binomPrefix_window n r s hr hrs]
  omega

lemma H_add_le_H_add_of_le_telescope (n a b c d : ℕ) (hab : a + b = c + d) (hac : a ≤ c)
    (hinc : ∀ i < c - a, H (n + 1) (a + i + 1) + H (n + 1) (b - i - 1) ≤
      H (n + 1) (a + i) + H (n + 1) (b - i)) :
    H (n + 1) c + H (n + 1) d ≤ H (n + 1) a + H (n + 1) b := by
  generalize hd : c - a = delta
  have hc : c = a + delta := by omega
  have hd2 : d = b - delta := by omega
  subst hc hd2
  clear hab hac hd
  induction delta with
  | zero =>
    simp
  | succ delta ih =>
    have h1 : H (n + 1) (a + (delta + 1)) + H (n + 1) (b - (delta + 1)) ≤
        H (n + 1) (a + delta) + H (n + 1) (b - delta) := by
      have hinc_d := hinc delta (by omega)
      have hrw1 : a + (delta + 1) = a + delta + 1 := by omega
      have hrw2 : b - (delta + 1) = b - delta - 1 := by omega
      rw [hrw1, hrw2]
      exact hinc_d
    have h2 : H (n + 1) (a + delta) + H (n + 1) (b - delta) ≤ H (n + 1) a + H (n + 1) b :=
      ih (fun i hi => hinc i (by omega))
    omega

lemma H_add_le_H_add_of_ge_telescope (n a b c d : ℕ) (hab : a + b = c + d) (hca : c ≤ a)
    (hinc : ∀ i < a - c, H (n + 1) (c + i) + H (n + 1) (d - i) ≤
      H (n + 1) (c + i + 1) + H (n + 1) (d - i - 1)) :
    H (n + 1) c + H (n + 1) d ≤ H (n + 1) a + H (n + 1) b := by
  generalize hd : a - c = delta
  have ha : a = c + delta := by omega
  have hd2 : b = d - delta := by omega
  subst ha hd2
  clear hab hca hd
  induction delta with
  | zero =>
    simp
  | succ delta ih =>
    have h1 : H (n + 1) (c + delta) + H (n + 1) (d - delta) ≤
        H (n + 1) (c + (delta + 1)) + H (n + 1) (d - (delta + 1)) := by
      have hinc_d := hinc delta (by omega)
      have hrw1 : c + (delta + 1) = c + delta + 1 := by omega
      have hrw2 : d - (delta + 1) = d - delta - 1 := by omega
      rw [hrw1, hrw2]
      exact hinc_d
    have h2 : H (n + 1) c + H (n + 1) d ≤ H (n + 1) (c + delta) + H (n + 1) (d - delta) :=
      ih (fun i hi => hinc i (by omega))
    omega

/--
In Case GT, the canonical split `p` is at most as large as `a`.
This is the structural half of the GT branch: if `a` is already larger than
the neighbourhood of `b`, then the positive canonical split of `a+b` cannot put
more than `a` vertices in its lower slice.  The proof uses only the earlier
canonical compression lemma `cascade_p_le_H_q` and monotonicity of `H`.
-/
lemma harper_case_gt_a_ge_p (n : ℕ) {a b p q : ℕ}
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) : p ≤ a :=
  cascade_lower_le_of_neighbor_lt hcasc hq_pos hcase

/--
Structural "central compression" invariant of the GT regime of the positive
Macaulay step.  When the larger part `a` already dominates the neighbourhood of
the smaller part (`H (n+1) b < a`), the canonical cascade split `(p, q)` of
`a + b` is sandwiched between the two parts: `b ≤ q ≤ p ≤ a`.

This records that, in the slack regime, passing to the canonical split moves
mass strictly inward (from the `a`-side toward the `b`-side) without crossing
either endpoint.  It depends only on the level-`n+1` cascade structure
(`harper_case_gt_a_ge_p`, `cascade_q_le_p`, `cascade_split_add`) and the case
hypothesis, so it is non-circular and reusable in any GT-regime argument.
-/
lemma harper_gt_split_between (n : ℕ) {a b p q : ℕ}
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    b ≤ q ∧ q ≤ p ∧ p ≤ a := by
  have hpa : p ≤ a := harper_case_gt_a_ge_p n hq_pos hcase hcasc
  have hqp : q ≤ p := cascade_q_le_p hcasc
  have hsum : p + q = a + b := cascade_split_add hcasc
  exact ⟨by omega, hqp, hpa⟩

/--
The two-slice boundary expression produced by the cascade recursion one
dimension up.  This is the local algebraic boundary cost of a nested split
`x = x0 + x1` before rewriting it back to `H (n+1) x`.
-/
noncomputable def cascadeBoundary (n x0 x1 : ℕ) : ℕ :=
  max (H n x0) x1 + max (H n x1) x0

/-- A nested cascade boundary is exactly the corresponding `H (n+1)` value. -/
lemma cascadeBoundary_eq_H_succ {n x x0 x1 : ℕ} (hx : CascadeSplit n x x0 x1) :
    cascadeBoundary n x0 x1 = H (n + 1) x := by
  unfold cascadeBoundary
  rw [H_succ_cascade hx]

/--
The paired nested boundary expression for two level-`n` cascade splits.  The
remaining positive Macaulay step compares this profile for the canonical split
`(p,q)` against the profile for an arbitrary split `(a,b)`.
-/
noncomputable def pairedCascadeBoundary (n x0 x1 y0 y1 : ℕ) : ℕ :=
  cascadeBoundary n x0 x1 + cascadeBoundary n y0 y1

/--
Paired nested boundaries rewrite to the sum of the two `H (n+1)` boundary
values.  This packages the four-block expression that occurs in the two open
positive-cascade leaves.
-/
lemma pairedCascadeBoundary_eq_H_add {n x y x0 x1 y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) :
    pairedCascadeBoundary n x0 x1 y0 y1 = H (n + 1) x + H (n + 1) y := by
  unfold pairedCascadeBoundary
  rw [cascadeBoundary_eq_H_succ hx, cascadeBoundary_eq_H_succ hy]

/--
Componentwise monotonicity of the nested two-slice boundary profile.  This is
the local monotonicity tool available before the genuine Macaulay interleaving
argument starts: if both exposed cascade slices grow, then the corresponding
two-slice boundary cost grows.
-/
lemma cascadeBoundary_mono {n x0 x1 y0 y1 : ℕ} (h0 : x0 ≤ y0) (h1 : x1 ≤ y1) :
    cascadeBoundary n x0 x1 ≤ cascadeBoundary n y0 y1 := by
  unfold cascadeBoundary
  exact Nat.add_le_add (max_le_max (H_mono h0) h1) (max_le_max (H_mono h1) h0)

/--
Paired version of `cascadeBoundary_mono`, used when comparing the four exposed
blocks in a nested cascade profile.
-/
lemma pairedCascadeBoundary_mono {n x0 x1 y0 y1 z0 z1 w0 w1 : ℕ}
    (hx0 : x0 ≤ z0) (hx1 : x1 ≤ z1) (hy0 : y0 ≤ w0) (hy1 : y1 ≤ w1) :
    pairedCascadeBoundary n x0 x1 y0 y1 ≤ pairedCascadeBoundary n z0 z1 w0 w1 := by
  unfold pairedCascadeBoundary
  exact Nat.add_le_add (cascadeBoundary_mono hx0 hx1) (cascadeBoundary_mono hy0 hy1)

/--
Monotonicity of `cascadeBoundary` along canonical cascade splits.  It packages
`cascade_slice_mono` with the local boundary monotonicity above.
-/
lemma cascadeBoundary_mono_of_cascade_le {n x x0 x1 y y0 y1 : ℕ}
    (hx : CascadeSplit n x x0 x1) (hy : CascadeSplit n y y0 y1) (hxy : x ≤ y) :
    cascadeBoundary n x0 x1 ≤ cascadeBoundary n y0 y1 := by
  obtain ⟨h0, h1⟩ := cascade_slice_mono hx hy hxy
  exact cascadeBoundary_mono h0 h1

/--
Mass conservation for the two nested cascade decompositions under a common
top-level split.  This is the algebraic form of the fact that the four exposed
level-`n` pieces of `(p,q)` and `(a,b)` occupy the same total window.
-/
lemma nested_cascade_mass_conservation {n a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    (p0 + p1) + (q0 + q1) = (a0 + a1) + (b0 + b1) := by
  have hpadd : p0 + p1 = p := cascade_split_add hp_split
  have hqadd : q0 + q1 = q := cascade_split_add hq_split
  have haadd : a0 + a1 = a := cascade_split_add ha_split
  have hbadd : b0 + b1 = b := cascade_split_add hb_split
  have htop : p + q = a + b := cascade_split_add hcasc
  omega

/--
The same conservation statement in flattened form, often more convenient for
linear arithmetic over component-wise interleaving inequalities.
-/
lemma nested_cascade_flat_mass_conservation {n a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    p0 + p1 + q0 + q1 = a0 + a1 + b0 + b1 := by
  have h := nested_cascade_mass_conservation hcasc hp_split hq_split ha_split hb_split
  omega

/--
Capped prefix mass: the number of elements in the first `k` vertices of the
`n`-cube that belong to layers `< l`.
-/
def cappedPrefixMass (n k l : ℕ) : ℕ :=
  min k (binomPrefix n l)

/--
The combined prefix mass of a split `(a, b)` up to layer `l`.
The 0-slice contributes layers `< l + 1`, while the 1-slice contributes
layers `< l` after adding the last coordinate.
-/
def splitPrefixMass (n a b l : ℕ) : ℕ :=
  cappedPrefixMass n a (l + 1) + cappedPrefixMass n b l

/--
Structural majorization relation for splits. A split `(p, q)` interleaves
`(a, b)` when `(p, q)` is the canonical cascade split of the common total
`a + b` and, in addition, `(p, q)` is at least as bottom-heavy as `(a, b)` at
every binomial prefix layer.

The relation is purely structural: the first conjunct records the cascade
profile of `(p, q)` and the second is the prefix-mass (Macaulay) majorization.
It mentions neither `boundaryCost` nor `H_inequality_core`.

The prefix-mass conjunct alone is *not* enough to force the boundary-cost
inequality (two different splits can have identical prefix masses but distinct
boundary costs), which is why the cascade profile of `(p, q)` is recorded as
well.
-/
def CascadeInterleaves (n p q a b : ℕ) : Prop :=
  CascadeSplit n (a + b) p q ∧
  ∀ l, splitPrefixMass n a b l ≤ splitPrefixMass n p q l

/-- A pointwise upper bound on the prefix mass of an arbitrary split. -/
lemma splitPrefixMass_le_min (n a b l : ℕ) :
    splitPrefixMass n a b l ≤
      min (a + b) (binomPrefix n (l + 1) + binomPrefix n l) := by
  unfold splitPrefixMass cappedPrefixMass
  omega

/--
The canonical cascade split saturates the prefix-mass bound at every layer.
-/
lemma cascade_splitPrefixMass_eq {n k p q : ℕ} (h : CascadeSplit n k p q) (l : ℕ) :
    splitPrefixMass n p q l =
      min k (binomPrefix n (l + 1) + binomPrefix n l) := by
  rcases h with ⟨r, t, hCascade, hp, hq⟩
  have hBr : binomPrefix n (r - 1) + choosePred n r = binomPrefix n r :=
    binomPrefix_pred_add_choosePred n r
  have hCr1 : binomPrefix n (r + 1) = binomPrefix n r + Nat.choose n r := by
    exact binomPrefix_succ n r
  generalize_proofs at *
  obtain ⟨hr, ht, hk, h⟩ := hCascade
  generalize_proofs at *
  have htC : t ≤ Nat.choose n r + choosePred n r := by
    exact ht.trans (by rw [choose_succ_dim])
  generalize_proofs at *
  rcases lt_trichotomy l r with (hl | rfl | hr) <;>
    simp_all +decide only [splitPrefixMass, cascadeSlice0Value, cascadeSlice1Value]
  · unfold cappedPrefixMass
    simp +decide only [binomPrefix_pascal]
    rw [min_eq_right, min_eq_right, min_eq_right]
    · exact le_add_of_le_of_nonneg
        (add_le_add (binomPrefix_mono _ (by omega)) (binomPrefix_mono _ (by omega)))
        (Nat.zero_le _)
    · exact le_add_of_le_of_nonneg (binomPrefix_mono _ (Nat.le_sub_one_of_lt hl))
        (Nat.zero_le _)
    · exact le_add_right (binomPrefix_mono _ (by linarith))
  · rcases l with (_ | l)
    · unfold cappedPrefixMass
      simp only [binomPrefix_pascal]
      omega
    · unfold cappedPrefixMass
      simp only [binomPrefix_pascal]
      omega
  · have h_binomPrefix_ge :
        binomPrefix n (l + 1) ≥ binomPrefix n (r + 1) ∧
          binomPrefix n l ≥ binomPrefix n r := by
      exact ⟨binomPrefix_mono _ (by linarith), binomPrefix_mono _ (by linarith)⟩
    generalize_proofs at *
    unfold cappedPrefixMass
    simp_all +decide only [binomPrefix_pascal, ge_iff_le]
    grind

/--
The canonical cascade split of `a + b` maximizes prefix mass, hence interleaves
any other split `(a, b)`.
-/
lemma canonicalSplit_interleaves
    {n a b p q : ℕ} (_ha : a ≤ 2 ^ n) (_hb : b ≤ 2 ^ n)
    (h_casc : CascadeSplit n (a + b) p q) :
    CascadeInterleaves n p q a b := by
  refine ⟨h_casc, fun l => ?_⟩
  have hub := splitPrefixMass_le_min n a b l
  have heq := cascade_splitPrefixMass_eq h_casc l
  rw [heq]
  exact hub

lemma cappedPrefixMass_succ_of_cascadeSplit
    {n k k0 k1 : ℕ} (hk : CascadeSplit n k k0 k1) (l : ℕ) :
    cappedPrefixMass (n + 1) k (l + 1)
      = cappedPrefixMass n k0 (l + 1) + cappedPrefixMass n k1 l := by
  unfold cappedPrefixMass
  have h_pascal : binomPrefix (n + 1) (l + 1) = binomPrefix n (l + 1) + binomPrefix n l := by
    have h := binomPrefix_pascal n (l + 1)
    rw [Nat.add_sub_cancel] at h
    exact h
  rw [h_pascal]
  have h_eq := cascade_splitPrefixMass_eq hk l
  unfold splitPrefixMass at h_eq
  exact h_eq.symm

lemma splitPrefixMass_succ_of_cascadeSplits
    (ha : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1) (l : ℕ) :
    splitPrefixMass (n + 1) a b (l + 1)
      = splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l := by
  unfold splitPrefixMass
  rw [cappedPrefixMass_succ_of_cascadeSplit ha, cappedPrefixMass_succ_of_cascadeSplit hb]
  omega

lemma CascadeInterleaves.lower_succ
    {n a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (h_inter : CascadeInterleaves (n + 1) p q a b)
    (hp : CascadeSplit n p p0 p1) (hq : CascadeSplit n q q0 q1)
    (ha : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1) :
    ∀ l, splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l
        ≤ splitPrefixMass n p0 q0 (l + 1) + splitPrefixMass n p1 q1 l := by
  intro l
  have h_ineq := h_inter.2 (l + 1)
  rw [splitPrefixMass_succ_of_cascadeSplits ha hb] at h_ineq
  rw [splitPrefixMass_succ_of_cascadeSplits hp hq] at h_ineq
  exact h_ineq

end BooleanIsoperimetry
