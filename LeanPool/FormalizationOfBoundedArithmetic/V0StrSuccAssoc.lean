/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/
import LeanPool.FormalizationOfBoundedArithmetic.V0

-- This file proves:
-- ∀ {X Y : str}, X + succ Y = succ (X + Y)
-- However, the proof was done using leanstral and is very verbose
-- Please see V0.lean for the manually written foundations.

variable {num str : Type} [M : V0ExtModel num str]
open V0ExtModel V0Model BASICModel
open FirstOrder Language
open HasTypes_is
open HasEmptySet
open HasLen
open HasSucc

namespace Xor'

lemma true1 {P Q R : Prop} : P -> (Xor' (Xor' P Q) R <-> ¬ Xor' Q R) := by
  unfold Xor'
  tauto

lemma true2 {P Q R : Prop} : Q -> (Xor' (Xor' P Q) R <-> ¬ Xor' P R) := by
  unfold Xor'
  tauto

end Xor'

lemma len_le_len_succ : ∀ {X : str}, (len X : num) ≤ len (succ X) := by
  intro X
  false_or_by_contra
  rename_i h
  rw [not_le] at h
  obtain ⟨p, px, ps, p_eq⟩ := exists_of_len_lt h
  rw [ax_succ] at ps
  simp only [not_and, not_or, not_exists, not_not, not_forall] at ps
  specialize ps (by
    rw [<- p_eq]
    exact le_self_add
  )
  have aux : (p + 1) ∈ succ X := by
    rw [ax_succ]
    constructor
    · rw [p_eq]
    · right
      constructor
      · intro hp
        apply (L1 hp).2
        exact _root_.le_of_eq (id (Eq.symm p_eq))
      · intro j jp
        by_cases hj : j = p
        · rw [hj]
          exact px
        · apply ps.1
          · exact px
          · constructor
            · rw [B11]
              exact jp
            · rw [<- B11] at jp
              intro contr
              apply hj
              apply _root_.le_antisymm <;> assumption
  have aux2 : p + 1 ≤ len (succ X) := (L1 aux).1
  rw [p_eq] at aux2
  have aux3 : len X < len X := lt_of_le_of_lt aux2 h
  apply aux3.2
  rfl

lemma len_succ_le_succ : ∀ {X : str}, len (succ X) ≤ (len X : num) + (1 : num) := by
  intro X
  by_contra h
  have h_lt : len X + (1 : num) < len (succ X) := lt_of_not_ge h
  obtain ⟨z, h_z_in, h_z_ge, _⟩ := exists_of_len_lt' (X := succ X) (i := len X + (1 : num)) h_lt
  have h_len_X_lt_z : len X < z := lt_of_lt_of_le (lt_succ (len X)) h_z_ge
  rw [ax_succ] at h_z_in
  exact not_lt_self (len X) (lt_of_lt_of_le h_len_X_lt_z h_z_in.1)

lemma in_iff_not_notin {X : str} {j : num} : j ∈ X ↔ ¬ j ∉ X := by
  rw [not_not]

/-- `m` is the least position below the string length where `X` has no bit. -/
def LowestOrderZero (X : str) (m : num) := m ≤ len X ∧ m ∉ X ∧ ∀ j < m, j ∈ X

lemma exists_lowest_order_zero (X : str) : ∃ m : num, LowestOrderZero X m := by
  obtain ⟨X', hX'⟩ := comp10 X (len X + (1 : num))
  have len_X'_ne_zero : (0 : num) < len X' := by
    have lenX_in_X' : (len X) ∈ X' := by
      rw [hX'.2]
      · exact len_not_in
      · exact lt_succ (len X)
    apply @lt_of_le_of_lt _ _ _ (len X)
    · exact B9 (len X)
    · exact L1 lenX_in_X'
  obtain ⟨min, hmin⟩ := xmin len_X'_ne_zero
  exists min
  have min_le_lenx : min <= len X := by
    rw [B11]
    apply lt_of_lt_of_le
    · exact hmin.1
    · exact hX'.1
  constructor
  · exact min_le_lenx
  · constructor
    · rw [<- hX'.2]
      · exact hmin.2.1
      · rw [<- B11]
        exact min_le_lenx
    · intro j hj
      rw [@in_iff_not_notin]
      rw [<- hX'.2]
      · apply hmin.2.2
        exact hj
      · rw [<- B11]
        apply le_of_lt
        apply lt_of_lt_of_le
        · exact hj
        · exact min_le_lenx

/-- `m` is the least position below the string length where `X` has a bit. -/
def LowestOrderOne (X : str) (m : num) := m ≤ len X ∧ m ∈ X ∧ ∀ j < m, j ∉ X

lemma exists_lowest_order_one {X : str} : (0 : num) < len X -> ∃ m : num, LowestOrderOne X m := by
  intro len_ne_zero
  obtain ⟨min, hmin⟩ := xmin len_ne_zero
  exists min
  constructor
  · apply le_of_lt
    exact hmin.1
  · exact hmin.2


lemma succ_bit_eq {X : str} {m : num} : LowestOrderZero X m -> m ∈ succ X := by
  intro h
  rw [ax_succ]
  exact ⟨h.1, Or.inr ⟨h.2.1, h.2.2⟩⟩

lemma succ_bit_lt {X : str} {m : num} : LowestOrderZero X m -> ∀ i < m, i ∉ succ X := by
  intro h i hi his
  rw [ax_succ] at his
  rcases his with ⟨_, hcases⟩
  rcases hcases with hcase | hcase
  · rcases hcase.2 with ⟨j, hj, hnot⟩
    exact hnot (h.2.2 j (lt_trans hj hi))
  · exact hcase.1 (h.2.2 i hi)

lemma succ_bit_gt {X : str} {m : num} : LowestOrderZero X m -> ∀ i > m, i ∈ succ X ↔ i ∈ X := by
  intro h i hi
  constructor
  · intro his
    rw [ax_succ] at his
    rcases his with ⟨_, hcases⟩
    rcases hcases with hcase | hcase
    · exact hcase.1
    · exact False.elim (h.2.1 (hcase.2 m hi))
  · intro hix
    rw [ax_succ]
    exact ⟨le_of_lt (L1 hix), Or.inl ⟨hix, ⟨m, hi, h.2.1⟩⟩⟩

lemma aux1 : ∀ {X : str}, ∀ {y min : num},
    LowestOrderZero X min -> y < min -> y ∈ X := by
  intro X y min h hy
  exact h.2.2 y hy

lemma len_succ_pos : ∀ {X : str}, len (succ X) > (0 : num) := by
  intro X
  obtain ⟨min, hmin⟩ := exists_lowest_order_zero X (num := num)
  have min_X := succ_bit_eq hmin
  apply len_pos_of_exists min_X

lemma lsb_not_succ : ∀ {X : str}, 0 ∈ X <-> 0 ∉ (succ X) := by
  intro X
  constructor
  · intro h contr
    rw [ax_succ] at contr
    rcases contr with ⟨hlen, hcases⟩
    rcases hcases with hbad | hgood
    · rcases hbad with ⟨hin, j, hj_lt, hj_notin⟩
      apply not_lt_zero (x := j)
      assumption
    · apply hgood.1; assumption
  · intro h
    by_contra h0
    apply h
    rw [ax_succ]
    constructor
    · exact zero_le (len X)
    · right
      constructor
      · exact h0
      · intro j hj
        exact False.elim (not_lt_zero (x := j) hj)

lemma all_lt_mem_of_not_mem_of_mem_succ :
    ∀ {X : str} {i : num}, i ∉ X -> i ∈ succ X -> ∀ j < i, j ∈ X := by
  intro X i h_i_notX h_i_SX
  rw [ax_succ] at h_i_SX
  rcases h_i_SX with ⟨h_i_le, ⟨h_i_X, ex⟩ | ⟨h_i_notX, all⟩⟩
  · exact fun j a ↦ False.elim (h_i_notX h_i_X)
  · exact all

lemma all_lt_not_mem_of_not_carry_of_all_lt_mem :
    ∀ {X Y : str} {i : num},
      ¬ Carry i X Y ->
      (∀ j < i, j ∈ Y) ->
      ∀ j < i, j ∉ X := by
  intro X Y i h_Carry h_all_lt_mem_Y
  unfold Carry at h_Carry
  rw [not_exists] at h_Carry
  intro j
  specialize h_Carry j
  rw [not_and_or] at h_Carry
  rcases h_Carry with contr | h_Carry
  · intro contr'
    contradiction
  · intro h_j_lt_i h_j_X
    rw [not_and] at h_Carry
    specialize h_Carry h_j_X
    rw [not_and] at h_Carry
    specialize h_Carry (h_all_lt_mem_Y j h_j_lt_i)
    apply h_Carry; clear h_Carry; intro z z_lt j_lt
    right
    exact h_all_lt_mem_Y z z_lt

lemma all_lt_not_carry_of_not_carry_of_all_lt_mem :
    ∀ {X Y : str} {i : num}, ¬ Carry i X Y -> (∀ j < i, j ∈ Y) -> ∀ j < i, ¬ Carry j X Y := by
  intro X Y i h_notC h_all_lt_mem_Y j h_j_lt h_jC
  unfold Carry at h_jC
  obtain ⟨k, h_k_lt_j, h_k_X, _, _⟩ := h_jC
  have h_k_lt_i : k < i := lt_trans h_k_lt_j h_j_lt
  exact all_lt_not_mem_of_not_carry_of_all_lt_mem h_notC h_all_lt_mem_Y k h_k_lt_i h_k_X

lemma all_lt_not_mem_of_all_lt_mem_add_of_all_lt_mem :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ Y) ->
      (∀ j < i, j ∈ X + Y) ->
      ∀ j < i, j ∉ X := by
  intro X Y i h_all_lt_mem_Y h_all_lt_mem_add j h_j_lt_i h_jX
  have h_len_X_pos : (0 : num) < len X := len_pos_of_exists h_jX
  obtain ⟨m, hm⟩ := exists_lowest_order_one (X := X) h_len_X_pos
  have h_m_le_j : m ≤ j := by
    by_contra h_m_gt_j
    exact hm.2.2 j (lt_of_not_ge h_m_gt_j) h_jX
  have h_m_lt_i : m < i := lt_of_le_of_lt h_m_le_j h_j_lt_i
  have h_mY : m ∈ Y := h_all_lt_mem_Y m h_m_lt_i
  have h_m_notCarry : ¬ Carry m X Y := by
    intro hC
    unfold Carry at hC
    obtain ⟨c, h_c_lt_m, h_cX, _, _⟩ := hC
    exact hm.2.2 c h_c_lt_m h_cX
  have h_m_in_add := h_all_lt_mem_add m h_m_lt_i
  rw [ax_add] at h_m_in_add
  have h_m_xor := h_m_in_add.2
  rw [xor3_split] at h_m_xor
  rcases h_m_xor with h1 | h2 | h3 | h4
  · exact h1.2.1 h_mY
  · exact h2.1 hm.2.1
  · exact h3.1 hm.2.1
  · exact h_m_notCarry h4.2.2

lemma not_carry_of_all_lt_mem_add_of_all_lt_mem :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ Y) ->
      (∀ j < i, j ∈ X + Y) ->
      ¬ Carry i X Y := by
  intro X Y i h_all_lt_mem_Y h_all_lt_mem_add hC
  unfold Carry at hC
  obtain ⟨k, h_k_lt_i, h_kX, _, _⟩ := hC
  exact all_lt_not_mem_of_all_lt_mem_add_of_all_lt_mem h_all_lt_mem_Y h_all_lt_mem_add k
    h_k_lt_i h_kX

lemma not_carry_of_all_lt_mem_add :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ X + Y) ->
      ¬ Carry i X Y := by
  intro X Y i h_all_lt_mem_add hC
  obtain ⟨I, h_I_le, h_I⟩ := comp11 X Y i
  unfold Carry at hC
  obtain ⟨k, h_k_lt_i, h_kX, h_kY, _⟩ := hC
  have h_kI : k ∈ I := by
    rw [h_I k h_k_lt_i]
    exact ⟨h_kX, h_kY⟩
  have h_len_I_pos : (0 : num) < len I := len_pos_of_exists h_kI
  obtain ⟨c, h_c_lt_len_I, h_cI, h_cmin⟩ := xmin h_len_I_pos
  have h_c_lt_i : c < i := lt_of_lt_of_le h_c_lt_len_I h_I_le
  have h_cX : c ∈ X := (h_I c h_c_lt_i).1 h_cI |>.1
  have h_cY : c ∈ Y := (h_I c h_c_lt_i).1 h_cI |>.2
  have h_c_notCarry : ¬ Carry c X Y := by
    intro h_cC
    unfold Carry at h_cC
    obtain ⟨d, h_d_lt_c, h_dX, h_dY, _⟩ := h_cC
    have h_dI : d ∈ I := by
      rw [h_I d (lt_trans h_d_lt_c h_c_lt_i)]
      exact ⟨h_dX, h_dY⟩
    exact h_cmin d h_d_lt_c h_dI
  have h_c_in_add : c ∈ X + Y := h_all_lt_mem_add c h_c_lt_i
  rw [ax_add] at h_c_in_add
  rw [xor3_split] at h_c_in_add
  rcases h_c_in_add.2 with h1 | h2 | h3 | h4
  · exact h1.2.1 h_cY
  · exact h2.1 h_cX
  · exact h3.1 h_cX
  · exact h_c_notCarry h4.2.2

lemma all_lt_not_carry_of_all_lt_mem_add :
    ∀ {X Y : str} {i : num},
      (∀ j < i, j ∈ X + Y) ->
      ∀ j < i, ¬ Carry j X Y := by
  intro X Y i h_all_lt_mem_add j h_j_lt_i
  apply not_carry_of_all_lt_mem_add
  intro z h_z_lt_j
  exact h_all_lt_mem_add z (lt_trans h_z_lt_j h_j_lt_i)

lemma carry_succ_of_all_lt_mem_add_of_lowest_zero_lt :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      m < i ->
      (∀ j < i, j ∈ X + Y) ->
      Carry i X (succ Y) := by
  intro X Y m i hm h_m_lt_i h_all_lt_mem_add
  have h_all_lt_not_carry : ∀ j < i, ¬ Carry j X Y :=
    all_lt_not_carry_of_all_lt_mem_add h_all_lt_mem_add
  have h_before_m : ∀ j < m, j ∈ X + Y := by
    intro j h_j_lt_m
    exact h_all_lt_mem_add j (lt_trans h_j_lt_m h_m_lt_i)
  have h_m_notCarry : ¬ Carry m X Y :=
    not_carry_of_all_lt_mem_add_of_all_lt_mem hm.2.2 h_before_m
  have h_m_in_add : m ∈ X + Y := h_all_lt_mem_add m h_m_lt_i
  have h_mX : m ∈ X := by
    rw [ax_add] at h_m_in_add
    have h_m_xor := h_m_in_add.2
    rw [xor3_split] at h_m_xor
    rcases h_m_xor with h1 | h2 | h3 | h4
    · exact h1.1
    · exact False.elim (hm.2.1 h2.2.1)
    · exact False.elim (h_m_notCarry h3.2.2)
    · exact False.elim (hm.2.1 h4.2.1)
  have h_or_after_m : ∀ j, m < j -> j < i -> j ∈ X ∨ j ∈ Y := by
    intro j h_m_lt_j h_j_lt_i
    have h_j_in_add : j ∈ X + Y := h_all_lt_mem_add j h_j_lt_i
    have h_j_notCarry : ¬ Carry j X Y := h_all_lt_not_carry j h_j_lt_i
    rw [ax_add] at h_j_in_add
    have h_j_xor := h_j_in_add.2
    rw [xor3_split] at h_j_xor
    rcases h_j_xor with h1 | h2 | h3 | h4
    · exact Or.inl h1.1
    · exact Or.inr h2.2.1
    · exact False.elim (h_j_notCarry h3.2.2)
    · exact False.elim (h_j_notCarry h4.2.2)
  unfold Carry
  refine ⟨m, h_m_lt_i, h_mX, succ_bit_eq hm, ?_⟩
  intro j h_j_lt_i h_m_lt_j
  rcases h_or_after_m j h_m_lt_j h_j_lt_i with h_jX | h_jY
  · exact Or.inl h_jX
  · exact Or.inr ((succ_bit_gt hm j h_m_lt_j).2 h_jY)


lemma prefix_zero_contradiction_of_not_carry_of_all_lt_mem :
    ∀ {X Y : str} {i : num},
      i < len X + len Y ->
      (∃ j < i, j ∉ X + Y) ->
      ¬ Carry i X Y ->
      (∀ j < i, j ∈ Y) ->
      False := by
  intro X Y i h_i_lt h_prefix_zero h_notC h_all_lt_mem_Y
  have h_X_prefix_zero := all_lt_not_mem_of_not_carry_of_all_lt_mem h_notC h_all_lt_mem_Y
  have h_Carry_prefix_zero := all_lt_not_carry_of_not_carry_of_all_lt_mem h_notC h_all_lt_mem_Y
  obtain ⟨contr, h_contr_lt, h_contr_notXY⟩ := h_prefix_zero
  apply h_contr_notXY
  rw [ax_add]
  constructor
  · exact lt_trans h_contr_lt h_i_lt
  · rw [Xor'.true2 (h_all_lt_mem_Y contr h_contr_lt)]
    rw [not_xor]
    rw [<- not_iff_not, iff_true_left]
    · exact h_Carry_prefix_zero contr h_contr_lt
    · exact h_X_prefix_zero contr h_contr_lt

lemma not_lt_lowest_zero_of_prefix_zero_of_not_carry :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      i < len X + len Y ->
      (∃ j < i, j ∉ X + Y) ->
      ¬ Carry i X Y ->
      ¬ i < m := by
  intro X Y m i hm h_i_lt h_prefix_zero h_notC h_i_lt_m
  apply prefix_zero_contradiction_of_not_carry_of_all_lt_mem h_i_lt h_prefix_zero h_notC
  intro j h_j_lt
  exact hm.2.2 j (lt_trans h_j_lt h_i_lt_m)

lemma not_carry_succ_of_lowest_zero_ge :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      i ≤ m ->
      ¬ Carry i X (succ Y) := by
  intro X Y m i hm h_i_le h_Carry
  unfold Carry at h_Carry
  obtain ⟨k, h_k_lt_i, _, h_k_SY, _⟩ := h_Carry
  exact (succ_bit_lt hm k (lt_of_lt_of_le h_k_lt_i h_i_le)) h_k_SY

lemma carry_succ_of_carry_of_lowest_zero_lt :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      m < i ->
      Carry i X Y ->
      Carry i X (succ Y) := by
  intro X Y m i hm h_m_lt_i h_Carry
  unfold Carry at h_Carry ⊢
  obtain ⟨k, h_k_lt_i, h_k_X, h_k_Y, h_k_prop⟩ := h_Carry
  rcases lt_trichotomy k m with h_k_lt_m | h_k_eq_m | h_m_lt_k
  · have h_m_X : m ∈ X := by
      rcases h_k_prop m h_m_lt_i h_k_lt_m with h_m_X | h_m_Y
      · exact h_m_X
      · exact False.elim (hm.2.1 h_m_Y)
    refine ⟨m, h_m_lt_i, h_m_X, succ_bit_eq hm, ?_⟩
    intro j h_j_lt_i h_m_lt_j
    rcases h_k_prop j h_j_lt_i (lt_trans h_k_lt_m h_m_lt_j) with h_j_X | h_j_Y
    · exact Or.inl h_j_X
    · exact Or.inr ((succ_bit_gt hm j h_m_lt_j).2 h_j_Y)
  · exact False.elim (hm.2.1 (by simpa [h_k_eq_m] using h_k_Y))
  · refine ⟨k, h_k_lt_i, h_k_X, (succ_bit_gt hm k h_m_lt_k).2 h_k_Y, ?_⟩
    intro j h_j_lt_i h_k_lt_j
    rcases h_k_prop j h_j_lt_i h_k_lt_j with h_j_X | h_j_Y
    · exact Or.inl h_j_X
    · exact Or.inr ((succ_bit_gt hm j (lt_trans h_m_lt_k h_k_lt_j)).2 h_j_Y)

lemma not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt :
    ∀ {X Y : str} {m i : num},
      LowestOrderZero Y m ->
      m < i ->
      (∃ j < i, j ∉ X + Y) ->
      ¬ Carry i X Y ->
      ¬ Carry i X (succ Y) := by
  intro X Y m i hm h_m_lt_i h_prefix_zero h_notC h_Carry
  unfold Carry at h_Carry
  obtain ⟨k, h_k_lt_i, h_k_X, h_k_SY, h_k_prop⟩ := h_Carry
  have h_m_le_k : m ≤ k := by
    by_contra h_mk
    exact (succ_bit_lt hm k (lt_of_not_ge h_mk)) h_k_SY
  have h_k_le_m : k ≤ m := by
    by_contra h_km
    have h_m_lt_k : m < k := lt_of_not_ge h_km
    have h_k_Y : k ∈ Y := (succ_bit_gt hm k h_m_lt_k).1 h_k_SY
    apply h_notC
    refine ⟨k, h_k_lt_i, h_k_X, h_k_Y, ?_⟩
    intro j h_j_lt_i h_k_lt_j
    rcases h_k_prop j h_j_lt_i h_k_lt_j with h_j_X | h_j_SY
    · exact Or.inl h_j_X
    · exact Or.inr ((succ_bit_gt hm j (lt_trans h_m_lt_k h_k_lt_j)).1 h_j_SY)
  have h_k_eq_m : k = m := by
    apply _root_.le_antisymm <;> assumption
  have h_m_X : m ∈ X := by
    simpa [h_k_eq_m] using h_k_X
  have h_or_after_m : ∀ j, m < j -> j < i -> j ∈ X ∨ j ∈ Y := by
    intro j h_m_lt_j h_j_lt_i
    rcases h_k_prop j h_j_lt_i (by simpa [h_k_eq_m] using h_m_lt_j) with h_j_X | h_j_SY
    · exact Or.inl h_j_X
    · exact Or.inr ((succ_bit_gt hm j h_m_lt_j).1 h_j_SY)
  have h_X_prefix_zero : ∀ j < m, j ∉ X := by
    intro j h_j_lt_m h_j_X
    apply h_notC
    refine ⟨j, lt_trans h_j_lt_m h_m_lt_i, h_j_X, hm.2.2 j h_j_lt_m, ?_⟩
    intro z h_z_lt_i h_j_lt_z
    by_cases h_z_lt_m : z < m
    · exact Or.inr (hm.2.2 z h_z_lt_m)
    · have h_m_le_z : m ≤ z := le_of_not_gt h_z_lt_m
      rcases eq_or_lt_of_le h_m_le_z with h_z_eq_m | h_m_lt_z
      · exact Or.inl (by simpa [h_z_eq_m] using h_m_X)
      · exact h_or_after_m z h_m_lt_z h_z_lt_i
  have h_Carry_le_m_zero : ∀ j ≤ m, ¬ Carry j X Y := by
    intro j h_j_le_m h_jC
    unfold Carry at h_jC
    obtain ⟨c, h_c_lt_j, h_c_X, _, _⟩ := h_jC
    exact h_X_prefix_zero c (lt_of_lt_of_le h_c_lt_j h_j_le_m) h_c_X
  have carry_to_i_from_after_m :
      ∀ {j : num}, m < j -> j < i -> Carry j X Y -> Carry i X Y := by
    intro j h_m_lt_j h_j_lt_i h_jC
    unfold Carry at h_jC ⊢
    obtain ⟨c, h_c_lt_j, h_c_X, h_c_Y, h_c_prop⟩ := h_jC
    refine ⟨c, lt_trans h_c_lt_j h_j_lt_i, h_c_X, h_c_Y, ?_⟩
    intro z h_z_lt_i h_c_lt_z
    by_cases h_z_lt_j : z < j
    · exact h_c_prop z h_z_lt_j h_c_lt_z
    · have h_j_le_z : j ≤ z := le_of_not_gt h_z_lt_j
      exact h_or_after_m z (lt_of_lt_of_le h_m_lt_j h_j_le_z) h_z_lt_i
  obtain ⟨contr, h_contr_lt, h_contr_notXY⟩ := h_prefix_zero
  apply h_contr_notXY
  rw [ax_add]
  constructor
  · rcases lt_trichotomy contr m with h_contr_lt_m | h_contr_eq_m | h_m_lt_contr
    · exact lt_of_lt_of_le (L1 (hm.2.2 contr h_contr_lt_m)) (by
        rw [_root_.add_comm]
        exact B8)
    · rw [h_contr_eq_m]
      exact lt_of_lt_of_le (L1 h_m_X) (show len X ≤ len X + len Y from B8)
    · rcases h_or_after_m contr h_m_lt_contr h_contr_lt with h_contr_X | h_contr_Y
      · exact lt_of_lt_of_le (L1 h_contr_X) (show len X ≤ len X + len Y from B8)
      · exact lt_of_lt_of_le (L1 h_contr_Y) (by
          rw [_root_.add_comm]
          exact B8)
  · rcases lt_trichotomy contr m with h_contr_lt_m | h_contr_eq_m | h_m_lt_contr
    · rw [xor3_split]
      right
      left
      exact ⟨h_X_prefix_zero contr h_contr_lt_m, hm.2.2 contr h_contr_lt_m,
        h_Carry_le_m_zero contr (le_of_lt h_contr_lt_m)⟩
    · rw [h_contr_eq_m, xor3_split]
      left
      exact ⟨h_m_X, hm.2.1, h_Carry_le_m_zero m le_rfl⟩
    · have h_contr_or : contr ∈ X ∨ contr ∈ Y := h_or_after_m contr h_m_lt_contr h_contr_lt
      have h_contr_notboth : ¬ (contr ∈ X ∧ contr ∈ Y) := by
        intro h_both
        apply h_notC
        refine ⟨contr, h_contr_lt, h_both.1, h_both.2, ?_⟩
        intro z h_z_lt_i h_contr_lt_z
        exact h_or_after_m z (lt_trans h_m_lt_contr h_contr_lt_z) h_z_lt_i
      have h_contr_notCarry : ¬ Carry contr X Y := by
        intro h_contr_Carry
        apply h_notC
        exact carry_to_i_from_after_m h_m_lt_contr h_contr_lt h_contr_Carry
      rcases h_contr_or with h_contr_X | h_contr_Y
      · rw [xor3_split]
        left
        exact ⟨h_contr_X, fun h_Y => h_contr_notboth ⟨h_contr_X, h_Y⟩, h_contr_notCarry⟩
      · rw [xor3_split]
        right
        left
        exact ⟨fun h_X => h_contr_notboth ⟨h_X, h_contr_Y⟩, h_contr_Y, h_contr_notCarry⟩

lemma not_mem_add_succ_of_not_mem_add_of_prefix_zero :
    ∀ {X Y : str} {y : num},
      y ∉ X + Y ->
      (∃ j < y, j ∉ X + Y) ->
      y ∉ X + succ Y := by
  intro X Y y h_notAdd h_prefix_zero h_new
  obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
  rw [ax_add] at h_new
  rcases h_new with ⟨_, h_y_xor⟩
  rw [xor3_split] at h_y_xor
  rcases lt_trichotomy y m with h_y_lt_m | h_y_eq_m | h_m_lt_y
  · rcases h_y_xor with h1 | h2 | h3 | h4
    · have h_yY : y ∈ Y := aux1 hm h_y_lt_m
      have h_notC : ¬ Carry y X Y := by
        intro hC
        apply h_notAdd
        rw [ax_add]
        constructor
        · exact carry_lt_add_len hC
        · rw [xor3_split]
          right
          right
          right
          exact ⟨h1.1, h_yY, hC⟩
      have h_y_lt_old : y < len X + len Y := by
        exact lt_of_lt_of_le (L1 h_yY) (by
          rw [_root_.add_comm]
          exact B8)
      exact prefix_zero_contradiction_of_not_carry_of_all_lt_mem h_y_lt_old h_prefix_zero h_notC
        (fun j h_j_lt ↦ hm.2.2 j (lt_trans h_j_lt h_y_lt_m))
    · exact (succ_bit_lt hm y h_y_lt_m) h2.2.1
    · exact (not_carry_succ_of_lowest_zero_ge hm (le_of_lt h_y_lt_m)) h3.2.2
    · exact (succ_bit_lt hm y h_y_lt_m) h4.2.1
  · subst y
    rcases h_y_xor with h1 | h2 | h3 | h4
    · exact h1.2.1 (succ_bit_eq hm)
    · have h_notC : ¬ Carry m X Y := by
        intro hC
        apply h_notAdd
        rw [ax_add]
        constructor
        · exact carry_lt_add_len hC
        · rw [xor3_split]
          right
          right
          left
          exact ⟨h2.1, hm.2.1, hC⟩
      obtain ⟨j, h_j_lt_m, h_j_notAdd⟩ := h_prefix_zero
      have h_jY : j ∈ Y := hm.2.2 j h_j_lt_m
      apply h_j_notAdd
      rw [ax_add]
      constructor
      · exact lt_of_lt_of_le (L1 h_jY) (by
          rw [_root_.add_comm]
          exact B8)
      · rw [xor3_split]
        right
        left
        exact ⟨all_lt_not_mem_of_not_carry_of_all_lt_mem h_notC hm.2.2 j h_j_lt_m,
          h_jY,
          all_lt_not_carry_of_not_carry_of_all_lt_mem h_notC hm.2.2 j h_j_lt_m⟩
    · exact (not_carry_succ_of_lowest_zero_ge hm le_rfl) h3.2.2
    · exact (not_carry_succ_of_lowest_zero_ge hm le_rfl) h4.2.2
  · by_cases h_yY : y ∈ Y
    · have h_ySY : y ∈ succ Y := (succ_bit_gt hm y h_m_lt_y).2 h_yY
      rcases h_y_xor with h1 | h2 | h3 | h4
      · exact h1.2.1 h_ySY
      · have h_oldC : Carry y X Y := by
          by_contra h_notC
          apply h_notAdd
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h_yY) (by
              rw [_root_.add_comm]
              exact B8)
          · rw [xor3_split]
            right
            left
            exact ⟨h2.1, h_yY, h_notC⟩
        exact h2.2.2 (carry_succ_of_carry_of_lowest_zero_lt hm h_m_lt_y h_oldC)
      · exact h3.2.1 h_ySY
      · have h_notC : ¬ Carry y X Y := by
          intro hC
          apply h_notAdd
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h_yY) (by
              rw [_root_.add_comm]
              exact B8)
          · rw [xor3_split]
            right
            right
            right
            exact ⟨h4.1, h_yY, hC⟩
        exact (not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt hm h_m_lt_y
          h_prefix_zero h_notC) h4.2.2
    · have h_notSY : y ∉ succ Y := by
        intro h_SY
        exact h_yY ((succ_bit_gt hm y h_m_lt_y).1 h_SY)
      rcases h_y_xor with h1 | h2 | h3 | h4
      · have h_oldC : Carry y X Y := by
          by_contra h_notC
          apply h_notAdd
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h1.1) (show len X ≤ len X + len Y from B8)
          · rw [xor3_split]
            left
            exact ⟨h1.1, h_yY, h_notC⟩
        exact h1.2.2 (carry_succ_of_carry_of_lowest_zero_lt hm h_m_lt_y h_oldC)
      · exact h_notSY h2.2.1
      · have h_notC : ¬ Carry y X Y := by
          intro hC
          apply h_notAdd
          rw [ax_add]
          constructor
          · exact carry_lt_add_len hC
          · rw [xor3_split]
            right
            right
            left
            exact ⟨h3.1, h_yY, hC⟩
        exact (not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt hm h_m_lt_y
          h_prefix_zero h_notC) h3.2.2
      · exact h_notSY h4.2.1

lemma not_mem_add_succ_of_mem_add_of_prefix_one :
    ∀ {X Y : str} {y : num},
      y ∈ X + Y ->
      (∀ j < y, j ∈ X + Y) ->
      y ∉ X + succ Y := by
  intro X Y y h_add h_prefix_one hy
  have h_notCarry_old : ¬ Carry y X Y := not_carry_of_all_lt_mem_add h_prefix_one
  have hy_add := hy
  rw [ax_add] at hy_add
  have hy_xor := hy_add.2
  rw [xor3_split] at hy_xor
  have h_new_X_SY_notCarry :
      y ∈ X -> y ∈ succ Y -> ¬ Carry y X (succ Y) -> False := by
    intro h_X h_SY h_notCarry
    rcases hy_xor with hy1 | hy2 | hy3 | hy4
    · exact hy1.2.1 h_SY
    · exact hy2.1 h_X
    · exact hy3.1 h_X
    · exact h_notCarry hy4.2.2
  have h_new_X_notSY_Carry :
      y ∈ X -> y ∉ succ Y -> Carry y X (succ Y) -> False := by
    intro h_X h_notSY h_Carry
    rcases hy_xor with hy1 | hy2 | hy3 | hy4
    · exact hy1.2.2 h_Carry
    · exact hy2.1 h_X
    · exact hy3.1 h_X
    · exact h_notSY hy4.2.1
  have h_new_notX_notSY_notCarry :
      y ∉ X -> y ∉ succ Y -> ¬ Carry y X (succ Y) -> False := by
    intro h_notX h_notSY h_notCarry
    rcases hy_xor with hy1 | hy2 | hy3 | hy4
    · exact h_notX hy1.1
    · exact h_notSY hy2.2.1
    · exact h_notCarry hy3.2.2
    · exact h_notX hy4.1
  have h_new_notX_SY_Carry :
      y ∉ X -> y ∈ succ Y -> Carry y X (succ Y) -> False := by
    intro h_notX h_SY h_Carry
    rcases hy_xor with hy1 | hy2 | hy3 | hy4
    · exact h_notX hy1.1
    · exact hy2.2.2 h_Carry
    · exact hy3.2.1 h_SY
    · exact h_notX hy4.1
  have h_old := h_add
  rw [ax_add] at h_old
  have h_old_xor := h_old.2
  rw [xor3_split] at h_old_xor
  rcases h_old_xor with h1 | h2 | h3 | h4
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    have hm_le_y : m ≤ y := by
      by_contra h
      exact h1.2.1 (aux1 hm (lt_of_not_ge h))
    rcases eq_or_lt_of_le hm_le_y with h_my | hm_lt_y
    · have h_SY : y ∈ succ Y := by
        simpa [h_my] using succ_bit_eq hm
      have h_notCarry_new : ¬ Carry y X (succ Y) := by
        simpa [h_my] using (not_carry_succ_of_lowest_zero_ge hm le_rfl)
      exact h_new_X_SY_notCarry h1.1 h_SY h_notCarry_new
    · have h_notSY : y ∉ succ Y := by
        intro h_SY
        exact h1.2.1 ((succ_bit_gt hm y hm_lt_y).1 h_SY)
      have h_Carry_new : Carry y X (succ Y) :=
        carry_succ_of_all_lt_mem_add_of_lowest_zero_lt hm hm_lt_y h_prefix_one
      exact h_new_X_notSY_Carry h1.1 h_notSY h_Carry_new
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    rcases lt_trichotomy y m with h_y_lt_m | h_y_eq_m | h_m_lt_y
    · have h_notSY : y ∉ succ Y := succ_bit_lt hm y h_y_lt_m
      have h_notCarry_new : ¬ Carry y X (succ Y) :=
        not_carry_succ_of_lowest_zero_ge hm (le_of_lt h_y_lt_m)
      exact h_new_notX_notSY_notCarry h2.1 h_notSY h_notCarry_new
    · exfalso
      apply hm.2.1
      simpa [h_y_eq_m] using h2.2.1
    · have h_SY : y ∈ succ Y := (succ_bit_gt hm y h_m_lt_y).2 h2.2.1
      have h_Carry_new : Carry y X (succ Y) :=
        carry_succ_of_all_lt_mem_add_of_lowest_zero_lt hm h_m_lt_y h_prefix_one
      exact h_new_notX_SY_Carry h2.1 h_SY h_Carry_new
  · exact h_notCarry_old h3.2.2
  · exact h_notCarry_old h4.2.2


lemma add_succ_of_succ_add_zero :
    ∀ {X Y : str} {y : num}, y = 0 -> y ∈ succ (X + Y) -> y ∈ X + succ Y := by
  intro X Y y h hy
  rw [h] at hy
  rw [ax_succ] at hy
  cases hy.2 with
  | inl hy =>
    exfalso
    obtain ⟨j, hj⟩ := hy.2
    apply not_lt_zero (num := num) (x := j)
    apply hj.1
  | inr hy_not =>
    rw [h, ax_add]
    constructor
    · by_cases X = 0
      · rename_i X0
        rw [X0, len_empty, V0Model.zero_add]
        apply len_succ_pos
      · refine add_pos_of_nonneg_of_pos ?_ ?_
        · exact B9 (len X)
        · apply len_succ_pos
    · rw [xor_comm]
      rw [<- xor_not_not]
      left
      constructor
      · apply carry_rec.1
        assumption
      · rw [not_not]
        rw [@xor_iff_iff_not]
        rw [ax_add] at hy_not
        simp only [not_and, not_xor] at hy_not
        rw [iff_false_right (carry_rec (i := y)).1] at hy_not
        constructor
        · intro X0
          have h_not_xor :=
            hy_not.1 (add_pos_of_pos_of_nonneg (L1 X0) (B9 (len Y)))
          simp only [not_xor] at h_not_xor
          rw [<- lsb_not_succ]
          rw [<- h_not_xor]
          assumption
        · intro succY0
          have hY0 : 0 ∈ Y := lsb_not_succ.mpr succY0
          have h_not_xor :=
            hy_not.1 (add_pos_of_nonneg_of_pos (B9 (len X)) (L1 hY0))
          simp only [not_xor] at h_not_xor
          rw [h_not_xor]
          exact hY0


lemma add_succ_of_succ_add_of_mem_add :
    ∀ {X Y : str} {y pred_y : num},
      pred_y + 1 = y ->
      y ∈ X + Y ->
      (∃ j < y, j ∉ X + Y) ->
      y ∈ X + succ Y := by
  intro X Y y pred_y hpred_y_eq h_y_in_add h_prefix_zero
  rw [ax_add]
  constructor
  · rw [ax_add] at h_y_in_add
    apply lt_of_lt_of_le h_y_in_add.1
    apply V0Model.add_le_add_left
    exact len_le_len_succ
  conv at h_y_in_add =>
    rw [<- hpred_y_eq]
    rw [ax_add]
    rw [hpred_y_eq]
  rcases h_y_in_add with ⟨h_y_lt, hxor⟩
  rw [xor3_split] at hxor
  rcases hxor with
    ⟨h_X, h_notY, h_notC⟩ | ⟨h_notX, h_Y, h_notC⟩ |
    ⟨h_notX, h_notY, h_C⟩ | ⟨h_X, h_Y, h_C⟩
  · rw [Xor'.true1 h_X]
    rw [not_xor]
    constructor
    · intro h_SY
      exfalso
      exact prefix_zero_contradiction_of_not_carry_of_all_lt_mem h_y_lt h_prefix_zero h_notC
        (all_lt_mem_of_not_mem_of_mem_succ h_notY h_SY)
    · intro h_Carry
      obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
      have hm_le_y : m ≤ y := by
        exact le_of_not_gt
          (not_lt_lowest_zero_of_prefix_zero_of_not_carry hm h_y_lt h_prefix_zero h_notC)
      rcases eq_or_lt_of_le hm_le_y with rfl | hm_lt_y
      · exact succ_bit_eq hm
      · exfalso
        exact not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt hm hm_lt_y
          h_prefix_zero h_notC h_Carry
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    have hm_le_y : m ≤ y := by
      exact le_of_not_gt
        (not_lt_lowest_zero_of_prefix_zero_of_not_carry hm h_y_lt h_prefix_zero h_notC)
    have hm_ne_y : m ≠ y := by
      intro h_my
      apply hm.2.1
      simpa [h_my] using h_Y
    have hm_lt_y : m < y := lt_of_le_of_ne hm_le_y hm_ne_y
    have h_SY : y ∈ succ Y := (succ_bit_gt hm y hm_lt_y).2 h_Y
    have h_notCarry_new : ¬ Carry y X (succ Y) :=
      not_carry_succ_of_prefix_zero_of_not_carry_of_lowest_zero_lt hm hm_lt_y h_prefix_zero h_notC
    rw [xor3_split]
    right
    left
    exact ⟨h_notX, h_SY, h_notCarry_new⟩
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    have hm_le_y : m ≤ y := by
      by_contra h
      exact h_notY (aux1 hm (lt_of_not_ge h))
    rcases eq_or_lt_of_le hm_le_y with rfl | hm_lt_y
    · rw [xor3_split]
      right
      left
      exact ⟨h_notX, succ_bit_eq hm, not_carry_succ_of_lowest_zero_ge hm le_rfl⟩
    · have h_notSY : y ∉ succ Y := by
        intro h_SY
        exact h_notY ((succ_bit_gt hm y hm_lt_y).1 h_SY)
      have h_Carry_new : Carry y X (succ Y) :=
        carry_succ_of_carry_of_lowest_zero_lt hm hm_lt_y h_C
      rw [xor3_split]
      right
      right
      left
      exact ⟨h_notX, h_notSY, h_Carry_new⟩
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    rcases lt_trichotomy y m with h_y_lt_m | h_y_eq_m | h_m_lt_y
    · have h_notSY : y ∉ succ Y := succ_bit_lt hm y h_y_lt_m
      have h_notCarry_new : ¬ Carry y X (succ Y) :=
        not_carry_succ_of_lowest_zero_ge hm (le_of_lt h_y_lt_m)
      rw [xor3_split]
      left
      exact ⟨h_X, h_notSY, h_notCarry_new⟩
    · exfalso
      apply hm.2.1
      simpa [h_y_eq_m] using h_Y
    · have h_SY : y ∈ succ Y := (succ_bit_gt hm y h_m_lt_y).2 h_Y
      have h_Carry_new : Carry y X (succ Y) :=
        carry_succ_of_carry_of_lowest_zero_lt hm h_m_lt_y h_C
      rw [xor3_split]
      right
      right
      right
      exact ⟨h_X, h_SY, h_Carry_new⟩


lemma add_succ_of_succ_add : ∀ {X Y : str}, ∀ {y : num}, y ∈ succ (X + Y) -> y ∈ X + succ Y := by
  intro X Y y hy
  by_cases y = 0
  · rename_i h
    exact add_succ_of_succ_add_zero h hy
  rename_i y_ne_zero
  obtain ⟨pred_y, hpred_y_le, hpred_y_eq⟩ := B12 y_ne_zero
  rw [ax_succ] at hy
  obtain ⟨_t, y_or⟩ := hy
  clear _t
  rcases y_or with ⟨h_y_in_add, h_prefix_zero⟩ | ⟨h_y_notin_add, h_prefix_one⟩
  · exact add_succ_of_succ_add_of_mem_add hpred_y_eq h_y_in_add h_prefix_zero
  · obtain ⟨m, hm⟩ := exists_lowest_order_zero Y (num := num)
    have h_notCarry_prefix : ∀ j ≤ y, ¬ Carry j X Y := by
      intro j h_j_le_y
      rcases eq_or_lt_of_le h_j_le_y with rfl | h_j_lt_y
      · exact not_carry_of_all_lt_mem_add h_prefix_one
      · exact all_lt_not_carry_of_all_lt_mem_add h_prefix_one j h_j_lt_y
    rcases lt_trichotomy y m with h_y_lt_m | h_y_eq_m | h_m_lt_y
    · have h_yY : y ∈ Y := aux1 hm h_y_lt_m
      have h_notC : ¬ Carry y X Y := not_carry_of_all_lt_mem_add h_prefix_one
      have h_X : y ∈ X := by
        by_contra h_notX
        apply h_y_notin_add
        rw [ax_add]
        constructor
        · exact lt_of_lt_of_le (L1 h_yY) (by
            simp only [le_add_iff_nonneg_left, zero_le]
            -- simpa [_root_.add_comm] using (show len Y ≤ len Y + len X from B8)
          )
        · rw [xor3_split]
          right
          left
          exact ⟨h_notX, h_yY, h_notC⟩
      have h_notSY : y ∉ succ Y := succ_bit_lt hm y h_y_lt_m
      have h_notCarry_new : ¬ Carry y X (succ Y) :=
        not_carry_succ_of_lowest_zero_ge hm (le_of_lt h_y_lt_m)
      rw [ax_add]
      constructor
      · exact lt_of_lt_of_le (L1 h_X) (show len X ≤ len X + len (succ Y) from B8)
      · rw [xor3_split]
        left
        exact ⟨h_X, h_notSY, h_notCarry_new⟩
    · have h_notC : ¬ Carry y X Y := not_carry_of_all_lt_mem_add h_prefix_one
      have h_notY : y ∉ Y := by
        simpa [h_y_eq_m] using hm.2.1
      have h_notX : y ∉ X := by
        intro h_yX
        apply h_y_notin_add
        rw [ax_add]
        constructor
        · exact lt_of_lt_of_le (L1 h_yX) (show len X ≤ len X + len Y from B8)
        · rw [xor3_split]
          left
          exact ⟨h_yX, h_notY, h_notC⟩
      have h_SY : y ∈ succ Y := by
        simpa [h_y_eq_m] using succ_bit_eq hm
      have h_notCarry_new : ¬ Carry y X (succ Y) := by
        simpa [h_y_eq_m] using (not_carry_succ_of_lowest_zero_ge hm le_rfl)
      rw [ax_add]
      constructor
      · exact lt_of_lt_of_le (L1 h_SY) (by
          simp only [le_add_iff_nonneg_left, zero_le]
          -- simpa [_root_.add_comm] using (show len (succ Y) ≤ len (succ Y) + len X from B8)
          )
      · rw [xor3_split]
        right
        left
        exact ⟨h_notX, h_SY, h_notCarry_new⟩
    · have h_m_in_add : m ∈ X + Y := h_prefix_one m h_m_lt_y
      have h_m_notC : ¬ Carry m X Y := h_notCarry_prefix m (le_of_lt h_m_lt_y)
      have h_mX : m ∈ X := by
        rw [ax_add] at h_m_in_add
        have h_m_xor := h_m_in_add.2
        rw [xor3_split] at h_m_xor
        rcases h_m_xor with h1 | h2 | h3 | h4
        · exact h1.1
        · exact False.elim (hm.2.1 h2.2.1)
        · exact False.elim (h_m_notC h3.2.2)
        · exact False.elim (hm.2.1 h4.2.1)
      have h_or_after_m : ∀ j, m < j -> j < y -> j ∈ X ∨ j ∈ Y := by
        intro j h_m_lt_j h_j_lt_y
        have h_j_in_add : j ∈ X + Y := h_prefix_one j h_j_lt_y
        have h_j_notC : ¬ Carry j X Y := h_notCarry_prefix j (le_of_lt h_j_lt_y)
        rw [ax_add] at h_j_in_add
        have h_j_xor := h_j_in_add.2
        rw [xor3_split] at h_j_xor
        rcases h_j_xor with h1 | h2 | h3 | h4
        · exact Or.inl h1.1
        · exact Or.inr h2.2.1
        · exact False.elim (h_j_notC h3.2.2)
        · exact False.elim (h_j_notC h4.2.2)
      have h_Carry_new : Carry y X (succ Y) := by
        unfold Carry
        refine ⟨m, h_m_lt_y, h_mX, succ_bit_eq hm, ?_⟩
        intro j h_j_lt_y h_m_lt_j
        rcases h_or_after_m j h_m_lt_j h_j_lt_y with h_jX | h_jY
        · exact Or.inl h_jX
        · exact Or.inr ((succ_bit_gt hm j h_m_lt_j).2 h_jY)
      have h_notC : ¬ Carry y X Y := not_carry_of_all_lt_mem_add h_prefix_one
      have h_X_pos : (0 : num) < len X := len_pos_of_exists h_mX
      have h_y_lt_new : y < len X + len (succ Y) := by
        have h_pred_or : pred_y ∈ X ∨ pred_y ∈ succ Y := by
          have h_y_maj : Maj (Carry pred_y X (succ Y)) (pred_y ∈ X) (pred_y ∈ succ Y) := by
            have h_y_carry : Carry (pred_y + 1) X (succ Y) := by
              simpa [hpred_y_eq] using h_Carry_new
            exact (carry_rec (i := pred_y) (X := X) (Y := succ Y)).2.1 h_y_carry
          unfold Maj at h_y_maj
          rcases h_y_maj with h1 | h2 | h3 | h4
          · exact Or.inl h1.2.1
          · exact Or.inr h2.2.2
          · exact Or.inl h3.2.1
          · exact Or.inl h4.2.1
        rcases h_pred_or with h_predX | h_predSY
        · have h_y_le_lenX : y ≤ len X := by
            rw [<- hpred_y_eq, B11]
            exact (add_lt_add_iff_right 1).mpr (L1 h_predX)
          exact lt_of_le_of_lt h_y_le_lenX (lt_add_of_pos_right (len X) len_succ_pos)
        · have h_y_le_lenSY : y ≤ len (succ Y) := by
            rw [<- hpred_y_eq, B11]
            exact (add_lt_add_iff_right 1).mpr (L1 h_predSY)
          exact lt_of_le_of_lt h_y_le_lenSY (by
            simpa [_root_.add_comm] using (lt_add_of_pos_right (len (succ Y)) h_X_pos))
      by_cases h_yY : y ∈ Y
      · have h_X : y ∈ X := by
          by_contra h_notX
          apply h_y_notin_add
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h_yY) (by
              simp only [le_add_iff_nonneg_left, zero_le]
              -- simpa [_root_.add_comm] using (show len Y ≤ len Y + len X from B8)
              )
          · rw [xor3_split]
            right
            left
            exact ⟨h_notX, h_yY, h_notC⟩
        have h_SY : y ∈ succ Y := (succ_bit_gt hm y h_m_lt_y).2 h_yY
        rw [ax_add]
        constructor
        · exact h_y_lt_new
        · rw [xor3_split]
          right
          right
          right
          exact ⟨h_X, h_SY, h_Carry_new⟩
      · have h_notX : y ∉ X := by
          intro h_X
          apply h_y_notin_add
          rw [ax_add]
          constructor
          · exact lt_of_lt_of_le (L1 h_X) (show len X ≤ len X + len Y from B8)
          · rw [xor3_split]
            left
            exact ⟨h_X, h_yY, h_notC⟩
        have h_notSY : y ∉ succ Y := by
          intro h_SY
          exact h_yY ((succ_bit_gt hm y h_m_lt_y).1 h_SY)
        rw [ax_add]
        constructor
        · exact h_y_lt_new
        · rw [xor3_split]
          right
          right
          left
          exact ⟨h_notX, h_notSY, h_Carry_new⟩





lemma succ_len_eq : ∀ {X Y : str}, len (X + succ Y) = (len (succ (X + Y)) : num) := by
  intro X Y
  have h_new_le : len (X + succ Y) ≤ len (X + Y) + (1 : num) := by
    by_contra h
    have h_lt : len (X + Y) + (1 : num) < len (X + succ Y) := lt_of_not_ge h
    obtain ⟨z, h_z_in, h_len_le_z, _⟩ :=
      exists_of_len_lt' (X := X + succ Y) (i := len (X + Y) + (1 : num)) h_lt
    have h_len_lt_z : len (X + Y) < z := lt_of_lt_of_le (lt_succ (len (X + Y))) h_len_le_z
    have h_z_notAdd : z ∉ X + Y := by
      intro h_z_add
      exact not_lt_self (len (X + Y)) (lt_trans h_len_lt_z (L1 h_z_add))
    exact not_mem_add_succ_of_not_mem_add_of_prefix_zero h_z_notAdd
      ⟨len (X + Y), h_len_lt_z, len_not_in⟩ h_z_in
  have h_top_iff :
      len (X + Y) ∈ X + succ Y ↔ ∀ j < len (X + Y), j ∈ X + Y := by
    constructor
    · intro h_top
      by_contra h_not_prefix
      have h_prefix_zero : ∃ j < len (X + Y), j ∉ X + Y := by
        by_contra h_no
        apply h_not_prefix
        intro j h_j_lt
        by_contra h_j_not
        exact h_no ⟨j, h_j_lt, h_j_not⟩
      exact not_mem_add_succ_of_not_mem_add_of_prefix_zero len_not_in h_prefix_zero h_top
    · intro h_prefix_one
      apply add_succ_of_succ_add
      rw [ax_succ]
      constructor
      · exact le_rfl
      · right
        constructor
        · exact len_not_in
        · exact h_prefix_one
  have h_succ_le_new : (len (succ (X + Y)) : num) ≤ len (X + succ Y) := by
    by_contra h
    have h_lt : len (X + succ Y) < len (succ (X + Y)) := lt_of_not_ge h
    obtain ⟨z, h_z_in, h_z_notin, _⟩ := exists_of_len_lt h_lt
    exact h_z_notin (add_succ_of_succ_add h_z_in)
  by_cases h_top : len (X + Y) ∈ X + succ Y
  · have h_top_succ : len (X + Y) ∈ succ (X + Y) := by
      rw [ax_succ]
      constructor
      · exact le_rfl
      · right
        constructor
        · exact len_not_in
        · exact h_top_iff.mp h_top
    have h_new_eq : len (X + succ Y) = len (X + Y) + (1 : num) := by
      apply _root_.le_antisymm
      · exact h_new_le
      · rw [B11]
        exact (add_lt_add_iff_right (1 : num)).mpr (L1 h_top)
    have h_succ_eq : len (succ (X + Y)) = len (X + Y) + (1 : num) := by
      apply _root_.le_antisymm
      · exact len_succ_le_succ
      · rw [B11]
        exact (add_lt_add_iff_right (1 : num)).mpr (L1 h_top_succ)
    rw [h_new_eq, h_succ_eq]
  · have h_not_top_succ : len (X + Y) ∉ succ (X + Y) := by
      intro h_top_succ
      exact h_top (add_succ_of_succ_add h_top_succ)
    have h_succ_eq : len (succ (X + Y)) = (len (X + Y) : num) := by
      have h_succ_le_old : len (succ (X + Y)) ≤ (len (X + Y) : num) := by
        by_contra h
        have h_lt : len (X + Y) < len (succ (X + Y)) := lt_of_not_ge h
        have h_ge : len (X + Y) + (1 : num) ≤ len (succ (X + Y)) := by
          rw [B11]
          exact (add_lt_add_iff_right (1 : num)).mpr h_lt
        have h_eq : len (succ (X + Y)) = len (X + Y) + (1 : num) :=
          _root_.le_antisymm len_succ_le_succ h_ge
        apply h_not_top_succ
        apply L2
        exact h_eq.symm
      exact _root_.le_antisymm h_succ_le_old len_le_len_succ
    have h_new_eq : len (X + succ Y) = (len (X + Y) : num) := by
      have h_old_le_new : (len (X + Y) : num) ≤ len (X + succ Y) := by
        rw [<- h_succ_eq]
        exact h_succ_le_new
      have h_new_le_old : len (X + succ Y) ≤ (len (X + Y) : num) := by
        by_contra h
        have h_lt : len (X + Y) < len (X + succ Y) := lt_of_not_ge h
        have h_ge : len (X + Y) + (1 : num) ≤ len (X + succ Y) := by
          rw [B11]
          exact (add_lt_add_iff_right (1 : num)).mpr h_lt
        have h_eq : len (X + succ Y) = len (X + Y) + (1 : num) := _root_.le_antisymm h_new_le h_ge
        apply h_top
        apply L2
        exact h_eq.symm
      exact _root_.le_antisymm h_new_le_old h_old_le_new
    rw [h_new_eq, h_succ_eq]


lemma succ_add_of_add_succ : ∀ {X Y : str}, ∀ {y : num}, y ∈ X + succ Y -> y ∈ succ (X + Y) := by
  intro X Y y hy
  have h_y_lt_succ_old : y < len (succ (X + Y)) := by
    have h := L1 hy
    rw [succ_len_eq] at h
    exact h
  have h_y_le_old : y ≤ len (X + Y) := by
    rw [B11]
    exact lt_of_lt_of_le h_y_lt_succ_old len_succ_le_succ
  rw [ax_succ]
  constructor
  · exact h_y_le_old
  · by_cases h_add : y ∈ X + Y
    · left
      constructor
      · exact h_add
      · by_contra h_no_zero
        have h_prefix_one : ∀ j < y, j ∈ X + Y := by
          intro j h_j_lt
          by_contra h_j_not
          exact h_no_zero ⟨j, h_j_lt, h_j_not⟩
        exact (not_mem_add_succ_of_mem_add_of_prefix_one h_add h_prefix_one) hy
    · right
      constructor
      · exact h_add
      · by_contra h_not_prefix
        have h_prefix_zero : ∃ j < y, j ∉ X + Y := by
          by_contra h_no
          apply h_not_prefix
          intro j h_j_lt
          by_contra h_j_not
          exact h_no ⟨j, h_j_lt, h_j_not⟩
        exact (not_mem_add_succ_of_not_mem_add_of_prefix_zero h_add h_prefix_zero) hy

theorem str_succ_assoc : ∀ {X Y : str}, X + succ Y = succ (X + Y) := by
  intro X Y
  apply M.SE
  · exact succ_len_eq
  · intro y y_lt
    exact ⟨succ_add_of_add_succ, add_succ_of_succ_add⟩

/-- Named alias emphasizing that this theorem is conditional on the strengthened V0 extension. -/
theorem str_succ_assoc_strengthened_v0 : ∀ {X Y : str}, X + succ Y = succ (X + Y) :=
  str_succ_assoc
