/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SymFun.BinomialDet

/-!
# Nonvanishing of the binomial Toeplitz determinant

The binomial Toeplitz determinant `det [C(m, s+j−i)]_{s × s}` is
nonzero for `1 ≤ s ≤ m`, discharging `SquareBinomialDetPos` of
`BinomialDet.lean`.

The proof is the Lindström–Gessel–Viennot involution: the Leibniz
expansion of the determinant is a signed count of tuples
`(σ, F)` where `F i` is an `(s + σ(i) − i)`-subset of `Fin m`
(the E-step heights of a lattice path).  Crossing tuples cancel in
pairs under the tail-swap involution at the first crossing; the
noncrossing tuples all have `σ = 1` and count with sign `+1`, and at
least one exists.
-/



namespace RS

open Finset Matrix

/-! ## 1. Sign extraction -/

/-- `(-1)^(s+j-i) = (-1)^s * (-1)^i * (-1)^j` when `i ≤ s + j`. -/
private theorem neg_one_pow_split (s i j : ℕ) (h : i ≤ s + j) :
    ((-1 : ℂ)) ^ (s + j - i) = (-1) ^ s * (-1) ^ i * (-1) ^ j := by
  suffices ((-1 : ℂ)) ^ (s + j - i) = (-1) ^ (s + i + j) by
    rw [this, pow_add, pow_add]
  have hmod : (s + j - i) % 2 = (s + i + j) % 2 := by omega
  have h1 := (Nat.div_add_mod (s + j - i) 2).symm
  have h2 := (Nat.div_add_mod (s + i + j) 2).symm
  rw [h1, h2, hmod, pow_add, pow_add, pow_mul, pow_mul, neg_one_sq,
    one_pow, one_pow]

/-- `(-1)^a` only depends on the parity of `a`. -/
private theorem neg_one_pow_congr (a b : ℕ) (h : a % 2 = b % 2) :
    ((-1 : ℂ)) ^ a = (-1) ^ b := by
  have h1 := (Nat.div_add_mod a 2).symm
  have h2 := (Nat.div_add_mod b 2).symm
  rw [h1, h2, h, pow_add, pow_add, pow_mul, pow_mul, neg_one_sq,
    one_pow, one_pow]

/-- The sign product equals `(-1)^s`. Uses `∏ a^f(i) = a^(∑ f(i))`. -/
private theorem sign_product (s : ℕ) :
    (∏ i : Fin s, ((-1 : ℂ)) ^ (s + (i : ℕ))) *
      ∏ j : Fin s, ((-1 : ℂ)) ^ (j : ℕ) = (-1) ^ s := by
  -- Combine using ∏ a^f = a^(∑f)
  simp only [Finset.prod_pow_eq_pow_sum]
  rw [← pow_add]
  apply neg_one_pow_congr
  -- ∑_{i : Fin s} (s + i) = s*s + ∑ i
  have hsum1 : ∑ i : Fin s, (s + (i : ℕ)) =
      s * s + ∑ i : Fin s, (i : ℕ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hsum1]
  -- (s*s + ∑i + ∑j) % 2 = s % 2 because s*s ≡ s (mod 2)
  have hpar : s * s % 2 = s % 2 := by
    rcases Nat.mod_two_eq_zero_or_one s with h | h <;>
      rw [Nat.mul_mod, h]
  omega

/-- Sign extraction: `diagramSchur(sq_s, -(m)) = (-1)^s * det[C(m, s+j-i)]`. -/
theorem diagramSchur_neg_eq_sign_mul_binomDet (s m : ℕ) (hs : 1 ≤ s)
    (hm : s ≤ m) :
    diagramSchur (squareDiagram s) (fun _ => -(m : ℂ)) =
    (-1 : ℂ) ^ s *
      (Matrix.of fun i j : Fin s =>
        (Nat.choose m (s + (j : ℕ) - (i : ℕ)) : ℂ)).det := by
  have hL : (squareDiagram s).rowLens.length = s := square_rowLens_length s
  have hm1 : 1 ≤ m := le_trans hs hm
  rw [diagramSchur, schurDet]
  -- Entrywise: newtonHZ(-(m), s+j-i) = (-1)^{s+i} * (-1)^j * C(m, s+j-i)
  have hmat : (Matrix.of fun (i j : Fin (squareDiagram s).rowLens.length) =>
      newtonHZ (fun _ => -(m : ℂ))
        (↑((squareDiagram s).rowLens.get i) + ↑↑j - ↑↑i)) =
    Matrix.of fun (i j : Fin (squareDiagram s).rowLens.length) =>
      ((-1 : ℂ)) ^ (s + (i : ℕ)) *
        (((-1 : ℂ)) ^ (j : ℕ) *
          (Nat.choose m (s + (j : ℕ) - (i : ℕ)) : ℂ)) := by
    ext i j; simp only [Matrix.of_apply]
    have hi : (i : ℕ) < s := by have := i.isLt; omega
    have hj : (j : ℕ) < s := by have := j.isLt; omega
    rw [List.get_eq_getElem, YoungDiagram.get_rowLens, rowLen_squareDiagram hi]
    rw [newtonHZ, ite_eq_left (show (0 : ℤ) ≤ (s : ℤ) + ↑↑j - ↑↑i by omega)]
    rw [show ((s : ℤ) + ↑↑j - ↑↑i).toNat = s + (j : ℕ) - (i : ℕ) from by omega]
    rw [newtonH_neg_const m hm1, neg_one_pow_split s (i : ℕ) (j : ℕ) (by omega)]
    ring
  rw [hmat]
  -- Extract row signs via det_mul_column, then column signs via det_mul_row.
  have h_det_step : ∀ (n : ℕ) (v : Fin n → ℂ)
      (A : Fin n → Fin n → ℂ),
      (Matrix.of fun i j => v i * A i j).det =
        (∏ i, v i) * (Matrix.of A).det := by
    intro n v A; exact det_mul_column v (Matrix.of A)
  have h_det_step' : ∀ (n : ℕ) (v : Fin n → ℂ)
      (A : Fin n → Fin n → ℂ),
      (Matrix.of fun i j => v j * A i j).det =
        (∏ j, v j) * (Matrix.of A).det := by
    intro n v A; exact det_mul_row v (Matrix.of A)
  rw [h_det_step _ (fun i => (-1 : ℂ) ^ (s + (i : ℕ)))
    (fun i j => (-1) ^ (j : ℕ) * (Nat.choose m (s + (j : ℕ) - (i : ℕ)) : ℂ))]
  rw [h_det_step' _ (fun j => (-1 : ℂ) ^ (j : ℕ))
    (fun i j => (Nat.choose m (s + (j : ℕ) - (i : ℕ)) : ℂ))]
  rw [← mul_assoc, hL, sign_product s]

/-! ## 2. The LGV path model

For a permutation `σ`, the Leibniz term `∏ i C(m, s+σ(i)−i)` counts
tuples `F : Fin s → Finset (Fin m)` with `(F i).card = s + σ(i) − i`.
Path `i` has x-coordinate `x_i(h) = i + #{a ∈ F i | a < h}` at
height `h`. -/

/-- The column degree `s + σ(i) − i` of the Leibniz term. -/
private def ddeg (s : ℕ) (σ : Equiv.Perm (Fin s)) (i : Fin s) : ℕ :=
  s + (σ i : ℕ) - (i : ℕ)

/-- The set of families counted by the Leibniz term of `σ`. -/
private def famSet (s m : ℕ) (σ : Equiv.Perm (Fin s)) :
    Finset (Fin s → Finset (Fin m)) :=
  Fintype.piFinset fun i =>
    (Finset.univ : Finset (Fin m)).powersetCard (ddeg s σ i)

private theorem card_of_mem_famSet {s m : ℕ} {σ : Equiv.Perm (Fin s)}
    {F : Fin s → Finset (Fin m)} (hmem : F ∈ famSet s m σ) (i : Fin s) :
    (F i).card = ddeg s σ i :=
  (Finset.mem_powersetCard.mp (Fintype.mem_piFinset.mp hmem i)).2

/-- x-coordinate of path `i` at height `h`. -/
private def xcoord {s m : ℕ} (F : Fin s → Finset (Fin m)) (i : Fin s)
    (h : ℕ) : ℕ :=
  (i : ℕ) + ((F i).filter fun a : Fin m => (a : ℕ) < h).card

private theorem xcoord_zero {s m : ℕ} (F : Fin s → Finset (Fin m))
    (i : Fin s) : xcoord F i 0 = (i : ℕ) := by
  rw [xcoord, Finset.filter_false_of_mem (fun a _ => Nat.not_lt_zero _)]
  simp

private theorem xcoord_top {s m : ℕ} {σ : Equiv.Perm (Fin s)}
    {F : Fin s → Finset (Fin m)} (hmem : F ∈ famSet s m σ) (i : Fin s) :
    xcoord F i m = s + (σ i : ℕ) := by
  rw [xcoord, Finset.filter_true_of_mem (fun a _ => a.isLt),
    card_of_mem_famSet hmem i, ddeg]
  have := i.isLt
  omega

/-- Each path moves by `0` or `1` per height step. -/
private theorem xcoord_step {s m : ℕ} (F : Fin s → Finset (Fin m))
    (i : Fin s) (h : ℕ) :
    xcoord F i h ≤ xcoord F i (h + 1) ∧
      xcoord F i (h + 1) ≤ xcoord F i h + 1 := by
  constructor
  · rw [xcoord, xcoord]
    have hsub : (F i).filter (fun a : Fin m => (a : ℕ) < h) ⊆
        (F i).filter (fun a : Fin m => (a : ℕ) < h + 1) := by
      intro a ha
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨ha.1, by omega⟩
    have := Finset.card_le_card hsub
    omega
  · rw [xcoord, xcoord]
    have hsub : (F i).filter (fun a : Fin m => (a : ℕ) < h + 1) ⊆
        (F i).filter (fun a : Fin m => (a : ℕ) < h) ∪
          (F i).filter (fun a : Fin m => (a : ℕ) = h) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases ha with ⟨hmem, hlt⟩
      by_cases hae : (a : ℕ) = h
      · exact Or.inr ⟨hmem, hae⟩
      · exact Or.inl ⟨hmem, by omega⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      ((F i).filter (fun a : Fin m => (a : ℕ) < h))
      ((F i).filter (fun a : Fin m => (a : ℕ) = h))
    have h3 : ((F i).filter (fun a : Fin m => (a : ℕ) = h)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact Fin.ext (by omega)
    omega

/-- Two paths cross at height `h`. -/
private def CrossingAt {s m : ℕ} (F : Fin s → Finset (Fin m))
    (h : ℕ) : Prop :=
  ∃ i i' : Fin s, i < i' ∧ xcoord F i h = xcoord F i' h

/-- Two paths cross somewhere. -/
private def Crossing {s m : ℕ} (F : Fin s → Finset (Fin m)) : Prop :=
  ∃ h, CrossingAt F h

/-! ## 3. Canonical crossing data -/

/-- Paths that participate in a crossing at height `h` (as the lower
index). -/
private def crossSet {s m : ℕ} (F : Fin s → Finset (Fin m))
    (h : ℕ) : Finset (Fin s) :=
  Finset.univ.filter fun i =>
    ∃ i', i < i' ∧ xcoord F i h = xcoord F i' h

/-- Partners of `i0` in a crossing at height `h`. -/
private def partnerSet {s m : ℕ} (F : Fin s → Finset (Fin m))
    (h : ℕ) (i0 : Fin s) : Finset (Fin s) :=
  Finset.univ.filter fun i' =>
    i0 < i' ∧ xcoord F i0 h = xcoord F i' h

open scoped Classical in
/-- Least crossing height. -/
private noncomputable def cH {s m : ℕ} (F : Fin s → Finset (Fin m))
    (hc : Crossing F) : ℕ :=
  Nat.find hc

open scoped Classical in
private theorem crossSet_nonempty {s m : ℕ} (F : Fin s → Finset (Fin m))
    (hc : Crossing F) : (crossSet F (cH F hc)).Nonempty := by
  obtain ⟨i, i', hlt, heq⟩ := Nat.find_spec hc
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i', hlt, heq⟩⟩

/-- Least lower index of a crossing at the least crossing height. -/
private noncomputable def cI0 {s m : ℕ} (F : Fin s → Finset (Fin m))
    (hc : Crossing F) : Fin s :=
  (crossSet F (cH F hc)).min' (crossSet_nonempty F hc)

private theorem partnerSet_nonempty {s m : ℕ}
    (F : Fin s → Finset (Fin m)) (hc : Crossing F) :
    (partnerSet F (cH F hc) (cI0 F hc)).Nonempty := by
  have hmem := Finset.min'_mem (crossSet F (cH F hc))
    (crossSet_nonempty F hc)
  obtain ⟨i', hlt, heq⟩ := (Finset.mem_filter.mp hmem).2
  exact ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, heq⟩⟩

/-- Least partner index. -/
private noncomputable def cI1 {s m : ℕ} (F : Fin s → Finset (Fin m))
    (hc : Crossing F) : Fin s :=
  (partnerSet F (cH F hc) (cI0 F hc)).min' (partnerSet_nonempty F hc)

private theorem cI1_spec {s m : ℕ} (F : Fin s → Finset (Fin m))
    (hc : Crossing F) :
    cI0 F hc < cI1 F hc ∧
      xcoord F (cI0 F hc) (cH F hc) = xcoord F (cI1 F hc) (cH F hc) :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (partnerSet_nonempty F hc))).2

private theorem min'_congr_of_eq {α : Type*} [LinearOrder α]
    {S T : Finset α} (h : S = T) (hS : S.Nonempty) (hT : T.Nonempty) :
    S.min' hS = T.min' hT := by
  subst h; rfl

/-! ## 4. The tail-swap involution on families -/

/-- Swap the tails (elements `≥ h`) of paths `i` and `i'`. -/
private def swapFam {s m : ℕ} (F : Fin s → Finset (Fin m)) (h : ℕ)
    (i i' : Fin s) : Fin s → Finset (Fin m) :=
  fun j =>
    if j = i then
      ((F i).filter fun a : Fin m => (a : ℕ) < h) ∪
        ((F i').filter fun a : Fin m => ¬ (a : ℕ) < h)
    else if j = i' then
      ((F i').filter fun a : Fin m => (a : ℕ) < h) ∪
        ((F i).filter fun a : Fin m => ¬ (a : ℕ) < h)
    else F j

private theorem swapFam_apply_other {s m : ℕ}
    (F : Fin s → Finset (Fin m)) (h : ℕ) (i i' j : Fin s)
    (hj : j ≠ i) (hj' : j ≠ i') : swapFam F h i i' j = F j := by
  rw [swapFam, ite_eq_right hj, ite_eq_right hj']

/-- Prefixes below `h' ≤ h` are unchanged by the tail swap. -/
private theorem swapFam_prefix {s m : ℕ} (F : Fin s → Finset (Fin m))
    (h : ℕ) (i i' : Fin s) (hne : i ≠ i') (j : Fin s) (h' : ℕ)
    (hh : h' ≤ h) :
    ((swapFam F h i i' j).filter fun a : Fin m => (a : ℕ) < h') =
      (F j).filter fun a : Fin m => (a : ℕ) < h' := by
  have key : ∀ (A B : Finset (Fin m)),
      ((A.filter (fun a : Fin m => (a : ℕ) < h) ∪
        B.filter (fun a : Fin m => ¬ (a : ℕ) < h)).filter
          fun a : Fin m => (a : ℕ) < h') =
          A.filter fun a : Fin m => (a : ℕ) < h' := by
    intro A B
    rw [Finset.filter_union, Finset.filter_filter, Finset.filter_filter]
    have h1 : B.filter (fun a : Fin m => ¬ (a : ℕ) < h ∧ (a : ℕ) < h') = ∅ :=
      Finset.filter_false_of_mem (fun a _ => by omega)
    have h2 : A.filter (fun a : Fin m => (a : ℕ) < h ∧ (a : ℕ) < h') =
        A.filter fun a : Fin m => (a : ℕ) < h' :=
      Finset.filter_congr (fun a _ => by constructor <;> intro <;> omega)
    rw [h1, h2, Finset.union_empty]
  by_cases hji : j = i
  · subst hji; rw [swapFam, ite_eq_left rfl]; exact key _ _
  · by_cases hji' : j = i'
    · subst hji'; rw [swapFam, ite_eq_right hji, ite_eq_left rfl]; exact key _ _
    · rw [swapFam_apply_other F h i i' j hji hji']

private theorem swapFam_xcoord {s m : ℕ} (F : Fin s → Finset (Fin m))
    (h : ℕ) (i i' : Fin s) (hne : i ≠ i') (j : Fin s) (h' : ℕ)
    (hh : h' ≤ h) :
    xcoord (swapFam F h i i') j h' = xcoord F j h' := by
  rw [xcoord, xcoord, swapFam_prefix F h i i' hne j h' hh]

/-- Cardinality bookkeeping for the swapped path at `i`. -/
private theorem swapFam_card_left {s m : ℕ}
    (F : Fin s → Finset (Fin m)) (h : ℕ) (i i' : Fin s) :
    (swapFam F h i i' i).card +
        ((F i').filter fun a : Fin m => (a : ℕ) < h).card =
      ((F i).filter fun a : Fin m => (a : ℕ) < h).card + (F i').card := by
  rw [swapFam, ite_eq_left rfl,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter_not (F i) (F i')
        (fun a : Fin m => (a : ℕ) < h))]
  have := Finset.card_filter_add_card_filter_not (s := F i')
    (fun a : Fin m => (a : ℕ) < h)
  omega

/-- Cardinality bookkeeping for the swapped path at `i'`. -/
private theorem swapFam_card_right {s m : ℕ}
    (F : Fin s → Finset (Fin m)) (h : ℕ) (i i' : Fin s) (hne : i ≠ i') :
    (swapFam F h i i' i').card +
        ((F i).filter fun a : Fin m => (a : ℕ) < h).card =
      ((F i').filter fun a : Fin m => (a : ℕ) < h).card + (F i).card := by
  rw [swapFam, ite_eq_right (Ne.symm hne), ite_eq_left rfl,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter_not (F i') (F i)
        (fun a : Fin m => (a : ℕ) < h))]
  have := Finset.card_filter_add_card_filter_not (s := F i)
    (fun a : Fin m => (a : ℕ) < h)
  omega

/-- The tail swap is an involution on families. -/
private theorem swapFam_involutive {s m : ℕ}
    (F : Fin s → Finset (Fin m)) (h : ℕ) (i i' : Fin s) (hne : i ≠ i') :
    swapFam (swapFam F h i i') h i i' = F := by
  funext j
  have keyPre : ∀ (A B : Finset (Fin m)),
      ((A.filter (fun a : Fin m => (a : ℕ) < h) ∪
        B.filter (fun a : Fin m => ¬ (a : ℕ) < h)).filter
          fun a : Fin m => (a : ℕ) < h) =
          A.filter fun a : Fin m => (a : ℕ) < h := by
    intro A B
    rw [Finset.filter_union, Finset.filter_filter, Finset.filter_filter]
    have h1 : B.filter (fun a : Fin m => ¬ (a : ℕ) < h ∧ (a : ℕ) < h) = ∅ :=
      Finset.filter_false_of_mem (fun a _ => by omega)
    have h2 : A.filter (fun a : Fin m => (a : ℕ) < h ∧ (a : ℕ) < h) =
        A.filter fun a : Fin m => (a : ℕ) < h :=
      Finset.filter_congr (fun a _ => by constructor <;> intro <;> omega)
    rw [h1, h2, Finset.union_empty]
  have keySuf : ∀ (A B : Finset (Fin m)),
      ((A.filter (fun a : Fin m => (a : ℕ) < h) ∪
        B.filter (fun a : Fin m => ¬ (a : ℕ) < h)).filter
          fun a : Fin m => ¬ (a : ℕ) < h) =
        B.filter fun a : Fin m => ¬ (a : ℕ) < h := by
    intro A B
    rw [Finset.filter_union, Finset.filter_filter, Finset.filter_filter]
    have h1 : A.filter (fun a : Fin m => (a : ℕ) < h ∧ ¬ (a : ℕ) < h) = ∅ :=
      Finset.filter_false_of_mem (fun a _ => by omega)
    have h2 : B.filter (fun a : Fin m => ¬ (a : ℕ) < h ∧ ¬ (a : ℕ) < h) =
        B.filter fun a : Fin m => ¬ (a : ℕ) < h :=
      Finset.filter_congr (fun a _ => by constructor <;> intro <;> omega)
    rw [h1, h2, Finset.empty_union]
  have hGi : swapFam F h i i' i =
      ((F i).filter fun a : Fin m => (a : ℕ) < h) ∪
        ((F i').filter fun a : Fin m => ¬ (a : ℕ) < h) := by
    rw [swapFam, ite_eq_left rfl]
  have hGi' : swapFam F h i i' i' =
      ((F i').filter fun a : Fin m => (a : ℕ) < h) ∪
        ((F i).filter fun a : Fin m => ¬ (a : ℕ) < h) := by
    rw [swapFam, ite_eq_right (Ne.symm hne), ite_eq_left rfl]
  by_cases hji : j = i
  · rw [hji]
    rw [swapFam, ite_eq_left rfl]
    rw [hGi, hGi', keyPre, keySuf, Finset.filter_union_filter_not_eq]
  · by_cases hji' : j = i'
    · rw [hji']
      rw [swapFam, ite_eq_right (Ne.symm hne), ite_eq_left rfl]
      rw [hGi, hGi', keyPre, keySuf, Finset.filter_union_filter_not_eq]
    · rw [swapFam_apply_other _ h i i' j hji hji',
        swapFam_apply_other F h i i' j hji hji']

/-! ## 5. Invariance of the canonical crossing data -/

open scoped Classical in
/-- If `G` agrees with `F` in all x-coordinates up to the first
crossing height of `F`, then `G` has the same canonical crossing
data. -/
private theorem choices_eq {s m : ℕ} (F G : Fin s → Finset (Fin m))
    (hcF : Crossing F) (hcG : Crossing G)
    (hagree : ∀ (j : Fin s) (h' : ℕ), h' ≤ cH F hcF →
      xcoord G j h' = xcoord F j h') :
    cH G hcG = cH F hcF ∧ cI0 G hcG = cI0 F hcF ∧
      cI1 G hcG = cI1 F hcF := by
  have hcAtF : CrossingAt F (cH F hcF) := Nat.find_spec hcF
  have hcAtG : CrossingAt G (cH F hcF) := by
    obtain ⟨i, i', hlt, heq⟩ := hcAtF
    exact ⟨i, i', hlt, by
      rw [hagree i _ le_rfl, hagree i' _ le_rfl]; exact heq⟩
  have hH : cH G hcG = cH F hcF := by
    have h1 : cH G hcG ≤ cH F hcF := Nat.find_min' hcG hcAtG
    rcases Nat.lt_or_ge (cH G hcG) (cH F hcF) with hlt | hge
    · exfalso
      obtain ⟨i, i', hlt', heq⟩ := Nat.find_spec hcG
      exact Nat.find_min hcF hlt ⟨i, i', hlt', by
        rw [← hagree i _ (le_of_lt hlt), ← hagree i' _ (le_of_lt hlt)]
        exact heq⟩
    · omega
  have hxeq : ∀ j : Fin s, xcoord G j (cH G hcG) = xcoord F j (cH F hcF) := by
    intro j; rw [hH]; exact hagree j _ le_rfl
  have hset : crossSet G (cH G hcG) = crossSet F (cH F hcF) := by
    rw [crossSet, crossSet]
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨i', hlt, heq⟩
      exact ⟨i', hlt, by rw [← hxeq x, ← hxeq i']; exact heq⟩
    · rintro ⟨i', hlt, heq⟩
      exact ⟨i', hlt, by rw [hxeq x, hxeq i']; exact heq⟩
  have hI0 : cI0 G hcG = cI0 F hcF :=
    min'_congr_of_eq hset (crossSet_nonempty G hcG)
      (crossSet_nonempty F hcF)
  have hset' : partnerSet G (cH G hcG) (cI0 G hcG) =
      partnerSet F (cH F hcF) (cI0 F hcF) := by
    rw [partnerSet, partnerSet, hI0]
    apply Finset.filter_congr
    intro x _
    constructor
    · rintro ⟨hlt, heq⟩
      exact ⟨hlt, by rw [← hxeq (cI0 F hcF), ← hxeq x]; exact heq⟩
    · rintro ⟨hlt, heq⟩
      exact ⟨hlt, by rw [hxeq (cI0 F hcF), hxeq x]; exact heq⟩
  have hI1 : cI1 G hcG = cI1 F hcF :=
    min'_congr_of_eq hset' (partnerSet_nonempty G hcG)
      (partnerSet_nonempty F hcF)
  exact ⟨hH, hI0, hI1⟩

/-! ## 6. The involution kills the crossing terms -/

/-- The swapped family lies in the family set of `σ * swap i₀ i₁`. -/
private theorem swapFam_mem_famSet {s m : ℕ} {σ : Equiv.Perm (Fin s)}
    {F : Fin s → Finset (Fin m)} (hmem : F ∈ famSet s m σ)
    (hc : Crossing F) :
    swapFam F (cH F hc) (cI0 F hc) (cI1 F hc) ∈
      famSet s m (σ * Equiv.swap (cI0 F hc) (cI1 F hc)) := by
  obtain ⟨hlt, hxeq⟩ := cI1_spec F hc
  have hne : cI0 F hc ≠ cI1 F hc := ne_of_lt hlt
  rw [famSet, Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_powersetCard]
  refine ⟨Finset.subset_univ _, ?_⟩
  by_cases hj0 : j = cI0 F hc
  · rw [hj0]
    have hcard := swapFam_card_left F (cH F hc) (cI0 F hc) (cI1 F hc)
    have hx : (cI0 F hc : ℕ) +
        ((F (cI0 F hc)).filter fun a : Fin m =>
          (a : ℕ) < cH F hc).card =
        (cI1 F hc : ℕ) +
          ((F (cI1 F hc)).filter fun a : Fin m =>
            (a : ℕ) < cH F hc).card := hxeq
    have hc1 : (F (cI1 F hc)).card = ddeg s σ (cI1 F hc) :=
      card_of_mem_famSet hmem _
    have hperm : (σ * Equiv.swap (cI0 F hc) (cI1 F hc)) (cI0 F hc) =
        σ (cI1 F hc) := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    rw [ddeg, hperm]
    rw [ddeg] at hc1
    have hb1 := (cI1 F hc).isLt
    have hb2 := (σ (cI1 F hc)).isLt
    have hb3 := (cI0 F hc).isLt
    omega
  · by_cases hj1 : j = cI1 F hc
    · rw [hj1]
      have hcard := swapFam_card_right F (cH F hc) (cI0 F hc)
        (cI1 F hc) hne
      have hx : (cI0 F hc : ℕ) +
          ((F (cI0 F hc)).filter fun a : Fin m =>
            (a : ℕ) < cH F hc).card =
        (cI1 F hc : ℕ) +
          ((F (cI1 F hc)).filter fun a : Fin m =>
            (a : ℕ) < cH F hc).card := hxeq
      have hc0 : (F (cI0 F hc)).card = ddeg s σ (cI0 F hc) :=
        card_of_mem_famSet hmem _
      have hperm : (σ * Equiv.swap (cI0 F hc) (cI1 F hc)) (cI1 F hc) =
          σ (cI0 F hc) := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      rw [ddeg, hperm]
      rw [ddeg] at hc0
      have hb1 := (cI0 F hc).isLt
      have hb2 := (σ (cI0 F hc)).isLt
      have hb3 := (cI1 F hc).isLt
      omega
    · rw [swapFam_apply_other F _ _ _ j hj0 hj1]
      have hperm : (σ * Equiv.swap (cI0 F hc) (cI1 F hc)) j = σ j := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hj0 hj1]
      rw [ddeg, hperm, ← ddeg]
      exact card_of_mem_famSet hmem j

/-- The swapped family still crosses (at the same height). -/
private theorem swapFam_crossing {s m : ℕ}
    (F : Fin s → Finset (Fin m)) (hc : Crossing F) :
    Crossing (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc)) := by
  obtain ⟨hlt, hxeq⟩ := cI1_spec F hc
  have hne : cI0 F hc ≠ cI1 F hc := ne_of_lt hlt
  exact ⟨cH F hc, cI0 F hc, cI1 F hc, hlt, by
    rw [swapFam_xcoord F _ _ _ hne _ _ le_rfl,
      swapFam_xcoord F _ _ _ hne _ _ le_rfl]
    exact hxeq⟩

/-! ## 7. Noncrossing families force the identity permutation -/

/-- A strictly monotone permutation of `Fin s` is the identity. -/
private theorem perm_eq_one_of_strictMono {s : ℕ}
    (σ : Equiv.Perm (Fin s))
    (hmono : ∀ i i' : Fin s, i < i' → σ i < σ i') : σ = 1 := by
  have le_apply : ∀ (f : Equiv.Perm (Fin s)),
      (∀ i i' : Fin s, i < i' → f i < f i') →
      ∀ (k : ℕ) (hk : k < s), k ≤ (f ⟨k, hk⟩ : ℕ) := by
    intro f hf k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ n ih =>
      intro hk
      have hn : n < s := Nat.lt_of_succ_lt hk
      have h1 : f ⟨n, hn⟩ < f ⟨n + 1, hk⟩ :=
        hf _ _ (by rw [Fin.mk_lt_mk]; omega)
      have h2 := ih hn
      have h3 : (f ⟨n, hn⟩ : ℕ) < (f ⟨n + 1, hk⟩ : ℕ) := h1
      omega
  have hmono' : ∀ a b : Fin s, a < b → σ⁻¹ a < σ⁻¹ b := by
    intro a b hab
    rcases lt_trichotomy (σ⁻¹ a) (σ⁻¹ b) with h | h | h
    · exact h
    · exfalso
      have : a = b := by
        have := congrArg σ h
        rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply] at this
      exact absurd this (ne_of_lt hab)
    · exfalso
      have := hmono _ _ h
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply] at this
      exact absurd hab (lt_asymm this)
  apply Equiv.ext
  intro i
  have h1 : (i : ℕ) ≤ (σ i : ℕ) := by
    have := le_apply σ hmono (i : ℕ) i.isLt
    rwa [Fin.eta] at this
  have h2 : (σ i : ℕ) ≤ (i : ℕ) := by
    have := le_apply σ⁻¹ hmono' ((σ i : ℕ)) (σ i).isLt
    rwa [Fin.eta, Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
  have : σ i = i := Fin.ext (by omega)
  simpa using this

/-- Discrete intermediate value theorem for ±1-step sequences. -/
private theorem exists_zero_of_steps (D : ℕ → ℤ) (M : ℕ)
    (hstep : ∀ h, D (h + 1) - D h ≤ 1 ∧ D h - D (h + 1) ≤ 1)
    (h0 : 0 < D 0) (hM : D M ≤ 0) : ∃ h, D h = 0 := by
  have hex : ∃ h, D h ≤ 0 := ⟨M, hM⟩
  have hk : D (Nat.find hex) ≤ 0 := Nat.find_spec hex
  have hkpos : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hk
    omega
  have hprev : ¬ D (Nat.find hex - 1) ≤ 0 :=
    Nat.find_min hex (by omega)
  have hs := hstep (Nat.find hex - 1)
  rw [show Nat.find hex - 1 + 1 = Nat.find hex from by omega] at hs
  exact ⟨Nat.find hex, by omega⟩

/-- A noncrossing family forces `σ = 1`. -/
private theorem noncross_perm_eq_one {s m : ℕ}
    {σ : Equiv.Perm (Fin s)} {F : Fin s → Finset (Fin m)}
    (hmem : F ∈ famSet s m σ) (hnc : ¬ Crossing F) : σ = 1 := by
  apply perm_eq_one_of_strictMono
  intro i i' hlt
  by_contra hge
  -- Then σ i' ≤ σ i; injectivity gives σ i' < σ i: an inversion.
  have hne : σ i ≠ σ i' := fun h =>
    absurd (σ.injective h) (ne_of_lt hlt)
  have hinv : (σ i' : ℕ) < (σ i : ℕ) := by
    rw [not_lt] at hge
    have h1 : (σ i' : ℕ) ≤ (σ i : ℕ) := hge
    have h2 : (σ i' : ℕ) ≠ (σ i : ℕ) := fun h =>
      hne (Fin.ext h.symm)
    omega
  -- Discrete IVT on D h = x_{i'}(h) − x_i(h).
  have hstep : ∀ h : ℕ,
      ((xcoord F i' (h + 1) : ℤ) - xcoord F i (h + 1)) -
        ((xcoord F i' h : ℤ) - xcoord F i h) ≤ 1 ∧
      ((xcoord F i' h : ℤ) - xcoord F i h) -
        ((xcoord F i' (h + 1) : ℤ) - xcoord F i (h + 1)) ≤ 1 := by
    intro h
    have h1 := xcoord_step F i h
    have h2 := xcoord_step F i' h
    omega
  have h0 : 0 < (xcoord F i' 0 : ℤ) - xcoord F i 0 := by
    rw [xcoord_zero, xcoord_zero]
    have : (i : ℕ) < (i' : ℕ) := hlt
    omega
  have hM : (xcoord F i' m : ℤ) - xcoord F i m ≤ 0 := by
    rw [xcoord_top hmem, xcoord_top hmem]
    omega
  obtain ⟨h, hzero⟩ := exists_zero_of_steps
    (fun h => (xcoord F i' h : ℤ) - xcoord F i h) m hstep h0 hM
  exact hnc ⟨h, i, i', hlt, by omega⟩

/-! ## 8. The signed count -/

/-- One full involution step returns the original tuple. -/
private theorem swap_step_involutive {s m : ℕ} (σ : Equiv.Perm (Fin s))
    (F : Fin s → Finset (Fin m)) (hc : Crossing F)
    (hcG : Crossing (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc))) :
    (⟨σ * Equiv.swap (cI0 F hc) (cI1 F hc) *
        Equiv.swap
          (cI0 (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc)) hcG)
          (cI1 (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc)) hcG),
      swapFam (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc))
        (cH (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc)) hcG)
        (cI0 (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc)) hcG)
        (cI1 (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc)) hcG)⟩ :
      (_ : Equiv.Perm (Fin s)) × (Fin s → Finset (Fin m))) = ⟨σ, F⟩ := by
  obtain ⟨hlt, hxeq⟩ := cI1_spec F hc
  have hne : cI0 F hc ≠ cI1 F hc := ne_of_lt hlt
  have hagree : ∀ (j : Fin s) (h' : ℕ), h' ≤ cH F hc →
      xcoord (swapFam F (cH F hc) (cI0 F hc) (cI1 F hc)) j h' =
        xcoord F j h' :=
    fun j h' hh => swapFam_xcoord F _ _ _ hne j h' hh
  obtain ⟨hH, hI0, hI1⟩ := choices_eq F _ hc hcG hagree
  rw [hH, hI0, hI1, mul_assoc, Equiv.swap_mul_self, mul_one,
    swapFam_involutive F (cH F hc) (cI0 F hc) (cI1 F hc) hne]

/-- The determinant as a signed count over `(σ, F)` tuples. -/
private theorem det_eq_signed_count (s m : ℕ) :
    (Matrix.of fun i j : Fin s =>
      (Nat.choose m (s + (j : ℕ) - (i : ℕ)) : ℂ)).det =
    ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (Fin s))).sigma
        (famSet s m),
      ((Equiv.Perm.sign p.1 : ℤ) : ℂ) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rw [← Finset.sum_sigma' Finset.univ (famSet s m)
    (fun σ _ => ((Equiv.Perm.sign σ : ℤ) : ℂ))]
  apply Finset.sum_congr rfl
  intro σ _
  have hprod : (∏ i, (Matrix.of fun i j : Fin s =>
      (Nat.choose m (s + (j : ℕ) - (i : ℕ)) : ℂ))ᵀ (σ i) i) =
      ((famSet s m σ).card : ℂ) := by
    have hcard : (famSet s m σ).card =
        ∏ i, Nat.choose m (ddeg s σ i) := by
      rw [famSet, Fintype.card_piFinset]
      apply Finset.prod_congr rfl
      intro i _
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hcard, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Matrix.transpose_apply, Matrix.of_apply, ddeg]
  rw [hprod, Finset.sum_const, nsmul_eq_mul, mul_comm]

open scoped Classical in
/-- The crossing terms cancel. -/
private theorem sum_crossing_zero (s m : ℕ) :
    ∑ p ∈ ((Finset.univ : Finset (Equiv.Perm (Fin s))).sigma
        (famSet s m)).filter (fun p => Crossing p.2),
      ((Equiv.Perm.sign p.1 : ℤ) : ℂ) = 0 := by
  have hcross : ∀ (p : (_ : Equiv.Perm (Fin s)) ×
      (Fin s → Finset (Fin m))),
      p ∈ ((Finset.univ : Finset (Equiv.Perm (Fin s))).sigma
        (famSet s m)).filter (fun p => Crossing p.2) →
      Crossing p.2 := fun p hp => (Finset.mem_filter.mp hp).2
  refine Finset.sum_involution
    (fun p hp =>
      ⟨p.1 * Equiv.swap (cI0 p.2 (hcross p hp)) (cI1 p.2 (hcross p hp)),
        swapFam p.2 (cH p.2 (hcross p hp)) (cI0 p.2 (hcross p hp))
          (cI1 p.2 (hcross p hp))⟩)
    ?_ ?_ ?_ ?_
  · -- signs cancel
    intro p hp
    have hne : cI0 p.2 (hcross p hp) ≠ cI1 p.2 (hcross p hp) :=
      ne_of_lt (cI1_spec p.2 (hcross p hp)).1
    have hsign : Equiv.Perm.sign
        (p.1 * Equiv.swap (cI0 p.2 (hcross p hp))
          (cI1 p.2 (hcross p hp))) = - Equiv.Perm.sign p.1 := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, mul_neg_one]
    rw [hsign]
    push_cast
    ring
  · -- the involution moves every point
    intro p hp _ heq
    have h1 : p.1 * Equiv.swap (cI0 p.2 (hcross p hp))
        (cI1 p.2 (hcross p hp)) = p.1 := congrArg Sigma.fst heq
    have h2 : Equiv.swap (cI0 p.2 (hcross p hp))
        (cI1 p.2 (hcross p hp)) = 1 := by
      have := congrArg (fun τ => p.1⁻¹ * τ) h1
      simpa [← mul_assoc] using this
    have h3 := congrArg (fun τ => τ (cI0 p.2 (hcross p hp))) h2
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h3
    exact absurd h3 (ne_of_gt (cI1_spec p.2 (hcross p hp)).1)
  · -- membership
    intro p hp
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_sigma]
      exact ⟨Finset.mem_univ _,
        swapFam_mem_famSet
          ((Finset.mem_sigma.mp (Finset.mem_filter.mp hp).1).2)
          (hcross p hp)⟩
    · exact swapFam_crossing p.2 (hcross p hp)
  · -- involution property
    intro p hp
    exact swap_step_involutive p.1 p.2 (hcross p hp) _

/-- The constant family never crosses. -/
private theorem const_fam_noncross {s m : ℕ} (S : Finset (Fin m)) :
    ¬ Crossing (fun _ : Fin s => S) := by
  rintro ⟨h, i, i', hlt, heq⟩
  rw [xcoord, xcoord] at heq
  have hval : (i : ℕ) = (i' : ℕ) := by omega
  exact absurd (Fin.ext hval) (ne_of_lt hlt)

open scoped Classical in
/-- The noncrossing terms count a nonempty set with sign `+1`. -/
private theorem sum_noncrossing_pos (s m : ℕ) (_ : s ≤ m) :
    ∑ p ∈ ((Finset.univ : Finset (Equiv.Perm (Fin s))).sigma
        (famSet s m)).filter (fun p => ¬ Crossing p.2),
      ((Equiv.Perm.sign p.1 : ℤ) : ℂ) =
    ((((Finset.univ : Finset (Equiv.Perm (Fin s))).sigma
        (famSet s m)).filter (fun p => ¬ Crossing p.2)).card : ℂ) := by
  rw [Finset.sum_congr rfl (fun p hp => ?_), Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hp' := Finset.mem_filter.mp hp
  have hmem := (Finset.mem_sigma.mp hp'.1).2
  have h1 : p.1 = 1 := noncross_perm_eq_one hmem hp'.2
  rw [h1, Equiv.Perm.sign_one]
  norm_num

open scoped Classical in
/-- The constant family: every path uses the same `s`-subset. -/
private theorem noncross_witness (s m : ℕ) (hm : s ≤ m) :
    (⟨1, fun _ => (Finset.univ : Finset (Fin s)).map
        (Fin.castLEEmb hm)⟩ :
      (_ : Equiv.Perm (Fin s)) × (Fin s → Finset (Fin m))) ∈
    ((Finset.univ : Finset (Equiv.Perm (Fin s))).sigma
        (famSet s m)).filter (fun p => ¬ Crossing p.2) := by
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [famSet, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, ddeg,
      Equiv.Perm.one_apply]
    omega
  · exact const_fam_noncross _

/-! ## 9. Core nonvanishing -/

open scoped Classical in
/-- The determinant `det[C(m, s+j-i)]` is nonzero for `1 ≤ s ≤ m`. -/
theorem det_binomial_upper_ne_zero (s m : ℕ) (_ : 1 ≤ s) (hm : s ≤ m) :
    (Matrix.of fun i j : Fin s =>
      (Nat.choose m (s + (j : ℕ) - (i : ℕ)) : ℂ)).det ≠ 0 := by
  rw [det_eq_signed_count s m,
    ← Finset.sum_filter_add_sum_filter_not
      ((Finset.univ : Finset (Equiv.Perm (Fin s))).sigma (famSet s m))
      (fun p => Crossing p.2),
    sum_crossing_zero s m, zero_add, sum_noncrossing_pos s m hm]
  exact_mod_cast Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero_of_mem (noncross_witness s m hm))

/-! ## 10. Glue -/

/-- The binomial Toeplitz determinant is nonzero, discharging the
hypothesis of the determinant development. -/
theorem squareBinomialDetPos : SquareBinomialDetPos := by
  intro s m hs hm
  rw [diagramSchur_neg_eq_sign_mul_binomDet s m hs hm]
  exact mul_ne_zero
    (pow_ne_zero s (neg_ne_zero.mpr one_ne_zero))
    (det_binomial_upper_ne_zero s m hs hm)

end RS
