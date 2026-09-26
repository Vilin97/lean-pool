/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ScalarBraiding
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperVectSchur

/-!
# Slot labellings and the Koszul sign of a permutation

The combinatorial half of the transport.  A word `Fin n → Bool`
records which slots of a tensor power carry the odd line, a
permutation reindexes it, and the induced permutation of the odd
slots alone has a sign — the sign a symmetric category produces
when the letters of the word are permuted, one factor of `−1` per
crossing of two odd letters.  Nothing here mentions a category; the
categorical side consumes it in [Letters.lean](Letters.lean).

* `permIndex`: the reindexing of a slot labelling by a
  permutation, with its two functoriality laws.
* `trueSet`, `popCount_eq_card`: the odd slots of a word.
* `oddPerm`, `parSign`: the induced permutation of the odd slots
  and its sign, with `oddPerm_mul` and `parSign_mul`, and the value
  `parSign_swap` on an adjacent transposition.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

/-! ## Reindexing slot labellings

A permutation routes the factor in slot `i` to slot `σ i`
(`permMor`); the labelling of the slots follows along. -/

/-- Reindexing a slot labelling along a permutation: the label of
slot `i` moves to slot `σ i`. -/
def permIndex {K : Type*} {n : ℕ} (σ : Equiv.Perm (Fin n))
    (c : Fin n → K) : Fin n → K :=
  c ∘ ⇑σ⁻¹

/-- The identity permutation does not move labels. -/
@[simp]
theorem permIndex_one {K : Type*} {n : ℕ} (c : Fin n → K) :
    permIndex 1 c = c := rfl

/-- The label a slot receives under reindexing. -/
theorem permIndex_apply {K : Type*} {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (c : Fin n → K) (i : Fin n) :
    permIndex σ c i = c (σ⁻¹ i) := rfl

/-- The label of the image slot is the original label. -/
theorem permIndex_apply_self {K : Type*} {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (c : Fin n → K) (i : Fin n) :
    permIndex σ c (σ i) = c i := by
  rw [permIndex_apply]
  exact congrArg c (σ.symm_apply_apply i)

/-! ## The odd slots of a word and the Koszul sign

For a parity word `w : Fin n → Bool` the `true` slots are the odd
ones.  A permutation induces a bijection from the odd slots of `w`
to those of the shuffled word; conjugating by the monotone
enumerations gives a permutation of `Fin (popCount w)` whose sign
is the Koszul sign of the shuffle. -/

/-- The set of `true` slots of a word. -/
def trueSet {n : ℕ} (w : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => w i = true

/-- Membership in the `true` slots. -/
theorem mem_trueSet {n : ℕ} {w : Fin n → Bool} {i : Fin n} :
    i ∈ trueSet w ↔ w i = true := by
  simp [trueSet]

/-- `popCount` is the size of the set of `true` slots. -/
theorem popCount_eq_card {n : ℕ} (w : Fin n → Bool) :
    popCount w = (trueSet w).card := rfl

/-- Reindexing maps the `true` slots along the permutation. -/
theorem trueSet_permIndex {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) :
    trueSet (permIndex σ w) = (trueSet w).map σ.toEmbedding := by
  ext j
  simp only [mem_trueSet, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro hj
    exact ⟨σ⁻¹ j, hj, σ.apply_symm_apply j⟩
  · rintro ⟨i, hi, rfl⟩
    rw [permIndex_apply_self]
    exact hi

/-- Reindexing preserves the number of `true` slots. -/
theorem popCount_permIndex {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) :
    popCount (permIndex σ w) = popCount w := by
  rw [popCount_eq_card, popCount_eq_card, trueSet_permIndex,
    Finset.card_map]

/-- The monotone enumeration of the `true` slots. -/
noncomputable def trueEnum {n : ℕ} (w : Fin n → Bool) :
    Fin (popCount w) ≃o {i // i ∈ trueSet w} :=
  (trueSet w).orderIsoOfFin rfl

/-- A permutation carries the `true` slots of a word bijectively
onto the `true` slots of the shuffled word. -/
def trueShift {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : Fin n → Bool) :
    {i // i ∈ trueSet w} ≃ {i // i ∈ trueSet (permIndex σ w)} :=
  (σ : Fin n ≃ Fin n).subtypeEquiv fun i => by
    rw [mem_trueSet, mem_trueSet]
    change w i = true ↔ permIndex σ w (σ i) = true
    rw [permIndex_apply_self]

/-- The shift, applied. -/
theorem trueShift_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) (i : {i // i ∈ trueSet w}) :
    (trueShift σ w i : Fin n) = σ i := rfl

/-- **The induced permutation on the odd slots**: conjugate the
shift by the monotone enumerations. -/
noncomputable def oddPerm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) : Equiv.Perm (Fin (popCount w)) :=
  (trueEnum w).toEquiv.trans ((trueShift σ w).trans
    ((trueEnum (permIndex σ w)).toEquiv.symm.trans
      (finCongr (popCount_permIndex σ w))))

/-- The induced permutation, applied. -/
theorem oddPerm_apply {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) (x : Fin (popCount w)) :
    oddPerm σ w x =
      finCongr (popCount_permIndex σ w)
        ((trueEnum (permIndex σ w)).toEquiv.symm
          (trueShift σ w (trueEnum w x))) := rfl

/-- **The Koszul sign of a shuffle**: the sign of the induced
permutation of the odd slots. -/
noncomputable def parSign {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) : ℂ :=
  ((Equiv.Perm.sign (oddPerm σ w) : ℤ) : ℂ)

/-- The identity shuffles nothing: its Koszul sign is `1`. -/
@[simp]
theorem parSign_one {n : ℕ} (w : Fin n → Bool) :
    parSign 1 w = 1 := by
  have h : oddPerm 1 w = 1 := by
    refine Equiv.ext fun x => ?_
    rw [oddPerm_apply]
    have hmk : trueShift 1 w (trueEnum w x) = trueEnum w x := by
      refine Subtype.ext ?_
      rw [trueShift_apply]
      rfl
    rw [hmk]
    have hsymm : (trueEnum (permIndex 1 w)).toEquiv.symm
        (trueEnum w x) = x :=
      (trueEnum w).toEquiv.symm_apply_apply x
    rw [hsymm]
    exact Fin.ext rfl
  rw [parSign, h, Equiv.Perm.sign_one]
  norm_num

/-- A permutation acting strictly monotonically is the identity. -/
private theorem perm_eq_one_of_strictMono {k : ℕ}
    (π : Equiv.Perm (Fin k)) (h : StrictMono ⇑π) : π = 1 := by
  have hinv : StrictMono ⇑π⁻¹ := by
    intro a b hab
    by_contra hle
    have h1 : π⁻¹ b ≤ π⁻¹ a := not_lt.mp hle
    have h2 : π (π⁻¹ b) ≤ π (π⁻¹ a) := h.monotone h1
    have e1 : π (π⁻¹ b) = b := π.apply_symm_apply b
    have e2 : π (π⁻¹ a) = a := π.apply_symm_apply a
    rw [e1, e2] at h2
    exact absurd hab (not_lt.mpr h2)
  refine Equiv.ext fun x => ?_
  have h1 : x ≤ π x := h.le_apply
  have h2 : π x ≤ π⁻¹ (π x) := hinv.le_apply
  have e3 : π⁻¹ (π x) = x := π.symm_apply_apply x
  rw [e3] at h2
  exact le_antisymm h2 h1

/-- The value of the induced permutation, as a slot number. -/
theorem oddPerm_val {n : ℕ} (σ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) (x : Fin (popCount w)) :
    (oddPerm σ w x : ℕ) =
      ((trueEnum (permIndex σ w)).toEquiv.symm
        (trueShift σ w (trueEnum w x)) : Fin (popCount (permIndex σ w))).val
      := rfl

/-- **The induced permutation is multiplicative**, up to transport
of the count equality. -/
theorem oddPerm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) :
    oddPerm (σ * τ) w =
      ((finCongr (popCount_permIndex τ w)).permCongr
        (oddPerm σ (permIndex τ w))) * oddPerm τ w := by
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.mul_apply, Equiv.permCongr_apply]
  have hcast : (finCongr (popCount_permIndex τ w)).symm
      (oddPerm τ w x) =
      (trueEnum (permIndex τ w)).toEquiv.symm
        (trueShift τ w (trueEnum w x)) := by
    rw [oddPerm_apply]
    exact (finCongr (popCount_permIndex τ w)).symm_apply_apply _
  rw [hcast, oddPerm_apply, oddPerm_apply]
  have henum : (trueEnum (permIndex τ w))
      ((trueEnum (permIndex τ w)).toEquiv.symm
        (trueShift τ w (trueEnum w x))) =
      trueShift τ w (trueEnum w x) :=
    (trueEnum (permIndex τ w)).toEquiv.apply_symm_apply _
  rw [henum]
  rfl

/-- **The Koszul sign is a cocycle** for the shuffle action. -/
theorem parSign_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (w : Fin n → Bool) :
    parSign (σ * τ) w =
      parSign σ (permIndex τ w) * parSign τ w := by
  rw [parSign, parSign, parSign, oddPerm_mul, map_mul,
    Equiv.Perm.sign_permCongr]
  push_cast
  ring

/-! ### The Koszul sign of an adjacent transposition

An adjacent swap crosses exactly one pair of letters: its Koszul
sign is `−1` when both are odd and `1` otherwise. -/

/-- Evaluating the enumeration inverse across an equality of
words. -/
private theorem enumSymm_val_congr {n : ℕ} {w w' : Fin n → Bool}
    (h : w = w') (a : {i // i ∈ trueSet w}) (b : {i // i ∈ trueSet w'})
    (hab : (a : Fin n) = (b : Fin n)) :
    ((trueEnum w).toEquiv.symm a : ℕ) =
      ((trueEnum w').toEquiv.symm b : ℕ) := by
  subst h
  rw [Subtype.ext hab]

/-- An adjacent swap of two `true` slots fixes the parity word. -/
private theorem permIndex_swap_of_both {n : ℕ} {w : Fin (n + 1) → Bool}
    {i : Fin n} (ha : w i.castSucc = true) (hb : w i.succ = true) :
    permIndex (Equiv.swap i.castSucc i.succ) w = w := by
  funext j
  rw [permIndex_apply, Equiv.swap_inv]
  rcases eq_or_ne j i.castSucc with rfl | hja
  · rw [Equiv.swap_apply_left, hb, ha]
  · rcases eq_or_ne j i.succ with rfl | hjb
    · rw [Equiv.swap_apply_right, ha, hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]

/-- A swap of two `true` slots preserves the set of `true` slots. -/
private theorem swap_mem_trueSet {n : ℕ} {w : Fin (n + 1) → Bool}
    {i : Fin n} (ha : w i.castSucc = true) (hb : w i.succ = true)
    {j : Fin (n + 1)} (hj : j ∈ trueSet w) :
    Equiv.swap i.castSucc i.succ j ∈ trueSet w := by
  rw [mem_trueSet] at hj ⊢
  rcases eq_or_ne j i.castSucc with rfl | hja
  · rwa [Equiv.swap_apply_left]
  · rcases eq_or_ne j i.succ with rfl | hjb
    · rwa [Equiv.swap_apply_right]
    · rwa [Equiv.swap_apply_of_ne_of_ne hja hjb]

/-- **An adjacent swap of two odd slots induces a transposition**
of the corresponding enumeration indices. -/
private theorem oddPerm_swap_of_both {n : ℕ} {w : Fin (n + 1) → Bool}
    {i : Fin n} (ha : w i.castSucc = true) (hb : w i.succ = true) :
    oddPerm (Equiv.swap i.castSucc i.succ) w =
      Equiv.swap
        ((trueEnum w).toEquiv.symm ⟨i.castSucc, mem_trueSet.mpr ha⟩)
        ((trueEnum w).toEquiv.symm ⟨i.succ, mem_trueSet.mpr hb⟩) := by
  set s := Equiv.swap i.castSucc i.succ with hs
  set xa := (trueEnum w).toEquiv.symm ⟨i.castSucc, mem_trueSet.mpr ha⟩
    with hxa
  set xb := (trueEnum w).toEquiv.symm ⟨i.succ, mem_trueSet.mpr hb⟩
    with hxb
  have hww : permIndex s w = w := permIndex_swap_of_both ha hb
  refine Equiv.ext fun x => Fin.ext ?_
  have hval : (oddPerm s w x : ℕ) =
      ((trueEnum w).toEquiv.symm
        ⟨s ((trueEnum w x : Fin (n + 1))),
          swap_mem_trueSet ha hb (trueEnum w x).2⟩ : ℕ) := by
    rw [oddPerm_val]
    exact enumSymm_val_congr hww _ _ (trueShift_apply s w (trueEnum w x))
  rw [hval]
  rcases eq_or_ne x xa with rfl | hxa'
  · have hEa : trueEnum w xa = ⟨i.castSucc, mem_trueSet.mpr ha⟩ := by
      rw [hxa]
      exact (trueEnum w).toEquiv.apply_symm_apply _
    have harg : (⟨s ((trueEnum w xa : Fin (n + 1))),
        swap_mem_trueSet ha hb (trueEnum w xa).2⟩ :
          {j // j ∈ trueSet w}) = ⟨i.succ, mem_trueSet.mpr hb⟩ := by
      refine Subtype.ext ?_
      change s ((trueEnum w xa : Fin (n + 1))) = i.succ
      have hv : (trueEnum w xa : Fin (n + 1)) = i.castSucc :=
        congrArg Subtype.val hEa
      rw [hv]
      exact Equiv.swap_apply_left _ _
    rw [harg, Equiv.swap_apply_left]
  · rcases eq_or_ne x xb with rfl | hxb'
    · have hEb : trueEnum w xb = ⟨i.succ, mem_trueSet.mpr hb⟩ := by
        rw [hxb]
        exact (trueEnum w).toEquiv.apply_symm_apply _
      have harg : (⟨s ((trueEnum w xb : Fin (n + 1))),
          swap_mem_trueSet ha hb (trueEnum w xb).2⟩ :
            {j // j ∈ trueSet w}) = ⟨i.castSucc, mem_trueSet.mpr ha⟩ := by
        refine Subtype.ext ?_
        change s ((trueEnum w xb : Fin (n + 1))) = i.castSucc
        have hv : (trueEnum w xb : Fin (n + 1)) = i.succ :=
          congrArg Subtype.val hEb
        rw [hv]
        exact Equiv.swap_apply_right _ _
      rw [harg, Equiv.swap_apply_right]
    · have hja : (trueEnum w x : Fin (n + 1)) ≠ i.castSucc := by
        intro h
        have hEx : trueEnum w x = ⟨i.castSucc, mem_trueSet.mpr ha⟩ :=
          Subtype.ext h
        refine hxa' ?_
        rw [hxa, ← hEx]
        exact ((trueEnum w).toEquiv.symm_apply_apply x).symm
      have hjb : (trueEnum w x : Fin (n + 1)) ≠ i.succ := by
        intro h
        have hEx : trueEnum w x = ⟨i.succ, mem_trueSet.mpr hb⟩ :=
          Subtype.ext h
        refine hxb' ?_
        rw [hxb, ← hEx]
        exact ((trueEnum w).toEquiv.symm_apply_apply x).symm
      have harg : (⟨s ((trueEnum w x : Fin (n + 1))),
          swap_mem_trueSet ha hb (trueEnum w x).2⟩ :
            {j // j ∈ trueSet w}) = trueEnum w x := by
        refine Subtype.ext ?_
        change s ((trueEnum w x : Fin (n + 1))) =
          ((trueEnum w x : {j // j ∈ trueSet w}) : Fin (n + 1))
        exact Equiv.swap_apply_of_ne_of_ne hja hjb
      rw [harg, Equiv.swap_apply_of_ne_of_ne hxa' hxb']
      exact congrArg Fin.val ((trueEnum w).symm_apply_apply x)

/-- An adjacent swap with at most one `true` endpoint is strictly
monotone on the `true` slots. -/
private theorem swap_strictMono_on {n : ℕ} {w : Fin (n + 1) → Bool}
    {i : Fin n} (hnot : ¬(w i.castSucc = true ∧ w i.succ = true))
    {j j' : Fin (n + 1)} (hj : w j = true) (hj' : w j' = true)
    (hjj : j < j') :
    Equiv.swap i.castSucc i.succ j < Equiv.swap i.castSucc i.succ j'
    := by
  have hba : (i.succ : ℕ) = (i.castSucc : ℕ) + 1 := by simp
  rcases eq_or_ne j i.castSucc with rfl | hja
  · rw [Equiv.swap_apply_left]
    rcases eq_or_ne j' i.succ with rfl | h'b
    · exact absurd ⟨hj, hj'⟩ hnot
    · rcases eq_or_ne j' i.castSucc with rfl | h'a
      · exact absurd hjj (lt_irrefl _)
      · rw [Equiv.swap_apply_of_ne_of_ne h'a h'b]
        rw [Fin.lt_def] at hjj ⊢
        simp only [ne_eq, Fin.ext_iff] at h'a h'b
        omega
  · rcases eq_or_ne j i.succ with rfl | hjb
    · rw [Equiv.swap_apply_right]
      rcases eq_or_ne j' i.castSucc with rfl | h'a
      · exfalso
        rw [Fin.lt_def] at hjj
        omega
      · rcases eq_or_ne j' i.succ with rfl | h'b
        · exact absurd hjj (lt_irrefl _)
        · rw [Equiv.swap_apply_of_ne_of_ne h'a h'b]
          rw [Fin.lt_def] at hjj ⊢
          omega
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
      rcases eq_or_ne j' i.castSucc with rfl | h'a
      · rw [Equiv.swap_apply_left]
        rw [Fin.lt_def] at hjj ⊢
        omega
      · rcases eq_or_ne j' i.succ with rfl | h'b
        · rw [Equiv.swap_apply_right]
          rw [Fin.lt_def] at hjj ⊢
          simp only [ne_eq, Fin.ext_iff] at hja
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne h'a h'b]
          exact hjj

/-- **An adjacent swap with at most one odd endpoint induces the
identity** on the enumeration indices. -/
private theorem oddPerm_swap_of_not {n : ℕ} {w : Fin (n + 1) → Bool}
    {i : Fin n} (hnot : ¬(w i.castSucc = true ∧ w i.succ = true)) :
    oddPerm (Equiv.swap i.castSucc i.succ) w = 1 := by
  set s := Equiv.swap i.castSucc i.succ with hs
  refine perm_eq_one_of_strictMono _ ?_
  intro x y hxy
  rw [Fin.lt_def, oddPerm_val, oddPerm_val]
  have h1 : trueShift s w (trueEnum w x) < trueShift s w (trueEnum w y)
      := by
    rw [Subtype.mk_lt_mk, trueShift_apply, trueShift_apply]
    refine swap_strictMono_on hnot
      (mem_trueSet.mp (trueEnum w x).2)
      (mem_trueSet.mp (trueEnum w y).2) ?_
    exact Subtype.coe_lt_coe.mpr ((trueEnum w).lt_iff_lt.mpr hxy)
  have h2 : (trueEnum (permIndex s w)).toEquiv.symm
        (trueShift s w (trueEnum w x)) <
      (trueEnum (permIndex s w)).toEquiv.symm
        (trueShift s w (trueEnum w y)) :=
    (trueEnum (permIndex s w)).symm.lt_iff_lt.mpr h1
  exact h2

/-- **The Koszul sign of an adjacent transposition**: `−1` when
both crossed letters are odd, `1` otherwise. -/
theorem parSign_swap {n : ℕ} (i : Fin n) (w : Fin (n + 1) → Bool) :
    parSign (Equiv.swap i.castSucc i.succ) w =
      if w i.castSucc = true ∧ w i.succ = true then -1 else 1 := by
  by_cases hab : w i.castSucc = true ∧ w i.succ = true
  · rw [ite_eq_left hab, parSign, oddPerm_swap_of_both hab.1 hab.2,
      Equiv.Perm.sign_swap]
    · norm_num
    · intro h
      have h1 := (trueEnum w).toEquiv.symm.injective h
      have h2 : i.castSucc = i.succ := congrArg Subtype.val h1
      exact absurd h2 (Fin.castSucc_lt_succ (i := i)).ne
  · rw [ite_eq_right hab, parSign, oddPerm_swap_of_not hab,
      Equiv.Perm.sign_one]
    norm_num

end RS
