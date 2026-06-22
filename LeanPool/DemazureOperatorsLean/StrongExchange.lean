/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/

import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.Algebra.Group.NatPowAssoc
import Init.Data.List.Lemmas

/-!
# LeanPool.DemazureOperatorsLean.StrongExchange
-/

namespace CoxeterSystem
noncomputable section

variable {B : Type}
variable {W : Type} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "len" => cs.length

instance instDecidableEqLeanPool : DecidableEq W := Classical.typeDecidableEq W

/-- The subtype of reflections in a Coxeter system. -/
def Reflection : Type := {t : W // IsReflection cs t}

/-- The number of times a reflection appears in the left inversion sequence of a word. -/
def reflectionMemLeftInvSeqCount (l : List B) (t : cs.Reflection) : ℕ :=
  (cs.leftInvSeq l).count t.1

/-- The parity of the number of occurrences of a reflection in a left inversion sequence. -/
def reflectionMemLeftInvSeqParity (l : List B) (t : cs.Reflection) : ZMod 2 :=
  (reflectionMemLeftInvSeqCount cs l t : ZMod 2)

/-- Conjugate a reflection and keep its reflection witness. -/
def conjOfReflection (t : cs.Reflection) (w : W) : cs.Reflection :=
  ⟨w * t.1 * w⁻¹, IsReflection.conj t.2 w⟩

/-- The parity contribution of a simple reflection to the permutation action. -/
def eta (i : B) (t : cs.Reflection) : ZMod 2 :=
  if (s i = t.1) then 1 else 0

lemma eta_eq_eta_of_simpleConj (i : B) (t : cs.Reflection) :
    cs.eta i t = cs.eta i (cs.conjOfReflection t (s i)) := by
  rw [eta, eta]
  rcases t with ⟨t, ht⟩
  have : s i = t ↔ s i * t = 1 := by
    constructor
    · intro h'
      rw [h']
      exact IsReflection.mul_self ht
    · intro h'
      apply (mul_left_inj t).mp
      simpa [IsReflection.mul_self ht] using h'
  by_cases h : s i = t
  · simp [h, conjOfReflection]
  · simp [this, conjOfReflection]

/-- The permutation action associated to a simple reflection. -/
def permutationMap (i : B) : cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2 :=
  fun (t , z) => (cs.conjOfReflection t (s i), z + cs.eta i t)

theorem permutationMap_orderTwo (i : B) : cs.permutationMap i ∘ cs.permutationMap i = id := by
  funext ⟨t, z⟩
  simp only [permutationMap, Function.comp_apply, id_eq]
  apply Prod.ext
  · simp[conjOfReflection, mul_assoc]
  · rw [← cs.eta_eq_eta_of_simpleConj i t]
    ring_nf
    rw [show (2 : ZMod 2) = 0 by decide]
    simp

lemma leftInvSeq_repeats : ∀ (k : ℕ) (h : k < M i j),
    (cs.leftInvSeq (alternatingWord i j (2 * M i j)))[M i j + k]'(by
      simp
      linarith) =
    (cs.leftInvSeq (alternatingWord i j (2 * M i j)))[k]'(by
      simp
      linarith) := by
  intro k h'
  rw [getElem_leftInvSeq_alternatingWord cs i j (M i j) k (by omega)]
  rw [getElem_leftInvSeq_alternatingWord cs i j (M i j) (M i j + k) (by omega)]
  rw[cs.prod_alternatingWord_eq_mul_pow]
  rw[cs.prod_alternatingWord_eq_mul_pow]
  have h_odd : Odd (2 * k + 1) := by
    simp
  have h_odd' : Odd (2 * ((M i j) + k) + 1) := by
    simp
  simp only [Nat.not_even_bit1, ↓reduceIte, mul_right_inj]
  have two_gt_0 : 2 > 0 := by linarith
  have h_exp : (2 * k + 1) / 2 = k := by
    rw[add_comm]
    rw[Nat.add_mul_div_left 1 k two_gt_0]
    simp
  have h_exp' : (2 * ((M i j) + k) + 1) / 2 = (M i j) + k := by
    rw[add_comm]
    rw[Nat.add_mul_div_left 1 ((M i j)+k) two_gt_0]
    simp
  rw[h_exp, h_exp']
  rw[NatPowAssoc.npow_add]
  simp

lemma leftInvSeq_repeats' : ∀ (k : ℕ) (h : k < M i j),
    (cs.leftInvSeq (alternatingWord i j (2 * M i j)))[M i j + k]'(by
      simp
      linarith) =
    (cs.leftInvSeq (alternatingWord i j (2 * M i j)))[k]'(by
      simp
      linarith) := by
  intro k h'
  exact leftInvSeq_repeats cs k h'

lemma nReflectionOccurrences_even_braidWord (t : cs.Reflection) :
  Even (reflectionMemLeftInvSeqCount cs (alternatingWord i j (2 * M i j)) t) := by
  suffices
      reflectionMemLeftInvSeqCount cs (alternatingWord i j (2 * M i j)) t =
        2 * List.count t.1
          (List.take (M.M i j)
            (cs.leftInvSeq (alternatingWord i j (M.M i j * 2)))) from by
    simp[this]
  rw [reflectionMemLeftInvSeqCount]
  suffices
      cs.leftInvSeq (alternatingWord i j (2 * M i j)) =
        List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j))) ++
          List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j))) from by
    rw[this]
    simp
    ring_nf
  have m_le_two_m : M i j ≤ 2 * M i j := by linarith
  have length_eq :
      (cs.leftInvSeq (alternatingWord i j (2 * M i j))).length =
        (List.take (M i j) (cs.leftInvSeq (alternatingWord i j (2 * M i j))) ++
          List.take (M i j)
            (cs.leftInvSeq (alternatingWord i j (2 * M i j)))).length := by
    simp[m_le_two_m]
    ring_nf
  apply List.ext_getElem length_eq
  intro k hk hk'
  by_cases h : k < M i j
  · have :
        k <
          (List.take (M.M i j)
            (cs.leftInvSeq (alternatingWord i j (2 * M.M i j)))).length := by
      simp[h, m_le_two_m]
    rw[List.getElem_append_left this]
    rw[List.getElem_take']
    exact h
  · have h_k_le : k - M i j < M i j := by
      have hk_bound : k < 2 * M i j := by
        simpa using hk
      have h_ge : M i j ≤ k := Nat.le_of_not_gt h
      omega
    have :
        (List.take (M.M i j)
          (cs.leftInvSeq (alternatingWord i j (2 * M.M i j)))).length ≤ k := by
      simp[m_le_two_m]
      linarith
    rw[List.getElem_append_right this]
    rw[List.getElem_take]
    have take_length :
        (List.take (M.M i j)
          (cs.leftInvSeq (alternatingWord i j (2 * M.M i j)))).length = M.M i j := by
      simp[m_le_two_m]
    simp only [take_length]
    rw[← leftInvSeq_repeats' cs (k - M i j) h_k_le]
    have : M.M i j + (k - M.M i j) = k := by
      exact Nat.add_sub_of_le (Nat.le_of_not_gt h)
    simp[this]

lemma parityReflectionOccurrences_braidWord (t : cs.Reflection) :
  reflectionMemLeftInvSeqParity cs (alternatingWord i j (2 * M i j)) t = 0 := by
  suffices Even (reflectionMemLeftInvSeqCount cs (alternatingWord i j (2 * M i j)) t) from by
    rw [reflectionMemLeftInvSeqParity]
    apply ZMod.natCast_eq_zero_iff_even.mpr this
  exact nReflectionOccurrences_even_braidWord cs t

lemma alternatingWord_reverse :
    (alternatingWord i j (2 * p)).reverse = alternatingWord j i (2 * p) := by
  induction p with
  | zero =>
    simp[alternatingWord]
  | succ p h =>
    rw [show 2 * (p + 1) = 2 * p + 1 + 1 by ring_nf]
    rw [alternatingWord_succ]
    rw [alternatingWord_succ]
    simp only [List.concat_eq_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append]
    rw [h]
    simp only [alternatingWord_succ', Nat.not_even_bit1, even_two_mul, if_false, if_true]

instance instMul : Mul (cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2) where
  mul := fun f g => f ∘ g

lemma mulDef (f g : cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2) : f * g = f ∘ g := rfl

instance : Monoid (cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2) where
  one := id
  mul := (instMul cs).mul
  one_mul := by
    intro f
    funext x
    suffices (id ∘ f) x = f x from by
      rw[← this]
      rfl
    simp
  mul_one := by
    intro f
    funext x
    suffices (f ∘ id) x = f x from by
      rw[← this]
      rfl
    simp
  mul_assoc := by
    intro f g h
    funext x
    repeat rw[mulDef]
    rfl

/-- The permutation map associated to a word, built by composing simple permutation maps. -/
def permutationMapOfList (l : List B) : cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2 :=
  match l with
  | [] => id
  | a :: t => cs.permutationMap a * permutationMapOfList t

lemma isReflection_conj_inv_mul_mul (ht : cs.IsReflection t) (w : W) :
  cs.IsReflection (w⁻¹ * t * w) := by
  have : w = w⁻¹⁻¹ := by simp
  nth_rewrite 2 [this]
  apply IsReflection.conj ht w⁻¹

lemma permutationMap_ofList_mk_1 (l : List B) :
  (permutationMapOfList cs l ⟨t,z⟩).1 = cs.conjOfReflection t (π l) := by
  induction l with
  | nil =>
    simp[permutationMapOfList, conjOfReflection]
  | cons a l h =>
    calc
      (permutationMapOfList cs (a :: l) (t, z)).1 =
          ((cs.permutationMap a * permutationMapOfList cs l) (t, z)).1 := by
        simp[permutationMapOfList]
      _ = (cs.permutationMap a (permutationMapOfList cs l (t, z))).1 := by rfl
      _ = cs.conjOfReflection t (π (a :: l)) := by
        simp[permutationMap, conjOfReflection, h, cs.wordProd_cons, mul_assoc]

lemma permutationMap_ofList_mk_2 (l : List B) :
    (permutationMapOfList cs l ⟨t,z⟩).2 =
      z + reflectionMemLeftInvSeqParity cs l.reverse t := by
  induction l with
  | nil =>
    simp[permutationMapOfList, reflectionMemLeftInvSeqParity, reflectionMemLeftInvSeqCount]
  | cons i l h =>
    rw[permutationMapOfList, mulDef]
    change (cs.permutationMap i (permutationMapOfList cs l (t, z))).2 =
      z + reflectionMemLeftInvSeqParity cs (i :: l).reverse t
    rw [permutationMap]
    change (permutationMapOfList cs l (t, z)).2 +
        cs.eta i (permutationMapOfList cs l (t, z)).1 =
      z + reflectionMemLeftInvSeqParity cs (i :: l).reverse t
    rw [h]
    simp only [reflectionMemLeftInvSeqParity, reflectionMemLeftInvSeqCount,
      List.reverse_cons]
    rw[← List.concat_eq_append]
    rw[leftInvSeq_concat]
    simp only [wordProd_reverse, inv_inv, List.concat_eq_append, List.count_append,
      Nat.cast_add]
    suffices
        cs.eta i (permutationMapOfList cs l (t, z)).1 =
          if (cs.wordProd l)⁻¹ * cs.simple i * cs.wordProd l = t.1 then 1 else 0 from by
      rw[this]
      simp[add_assoc, List.count_singleton]
    simp only [eta, permutationMap_ofList_mk_1, conjOfReflection]
    by_cases h' : (cs.wordProd l)⁻¹ * cs.simple i * cs.wordProd l = t.1
    · have lhs : cs.simple i = cs.wordProd l * t.1 * (cs.wordProd l)⁻¹ := by
        rw [← h']
        simp [mul_assoc]
      rw [if_pos lhs, if_pos h']
    · have lhs_ne : ¬cs.simple i = cs.wordProd l * t.1 * (cs.wordProd l)⁻¹ := by
        intro h''
        apply h'
        rw [h'']
        simp [mul_assoc]
      rw [if_neg lhs_ne, if_neg h']

lemma permutationMap_ofList_mk (l : List B) (t : cs.Reflection) (z : ZMod 2) :
  (permutationMapOfList cs l ⟨t,z⟩) = ⟨cs.conjOfReflection t (π l),
   z + reflectionMemLeftInvSeqParity cs l.reverse t⟩ := by
  rw[← permutationMap_ofList_mk_1, ← permutationMap_ofList_mk_2]

theorem permutationMap_isLiftable : M.IsLiftable (cs.permutationMap) := by
  intro i j
  have h (p : ℕ) :
      (cs.permutationMap i * cs.permutationMap j) ^ p =
        permutationMapOfList cs (alternatingWord i j (2 * p)) := by
    induction p with
    | zero =>
      rfl
    | succ p h =>
      rw[pow_succ']
      rw[h]
      have : 2 * (p + 1) = 2 * p + 1 + 1 := by ring_nf
      rw[this]
      rw[alternatingWord_succ']
      rw [if_neg (Nat.not_even_bit1 p)]
      rw[permutationMapOfList]
      rw[alternatingWord_succ']
      rw [if_pos (even_two_mul p)]
      rw[permutationMapOfList]
      simp[mul_assoc]
  rw[h (M i j)]
  funext ⟨t, z⟩
  change permutationMapOfList cs (alternatingWord i j (2 * M.M i j)) (t, z) = ⟨t,z⟩
  rw[permutationMap_ofList_mk]
  apply Prod.ext
  · simp[conjOfReflection, cs.prod_alternatingWord_eq_mul_pow]
  · rw[alternatingWord_reverse]
    rw[M.symmetric]
    simp [parityReflectionOccurrences_braidWord (M := M) cs (i := j) (j := i) t]

/-- The homomorphic lift of the simple permutation maps to the Coxeter group. -/
def permutationMapLift : W →* cs.Reflection × ZMod 2 → cs.Reflection × ZMod 2 :=
  cs.lift ⟨cs.permutationMap, permutationMap_isLiftable cs⟩

theorem permutationMap_lift_mk_ofList (l : List B) (t : cs.Reflection) (z : ZMod 2) :
  permutationMapLift cs (cs.wordProd l) ⟨t,z⟩ = permutationMapOfList cs l ⟨t,z⟩ := by
  induction l with
  | nil =>
    simp[permutationMapLift, cs.wordProd_nil, permutationMapOfList]
    rfl
  | cons i l h =>
    rw[cs.wordProd_cons]
    rw[permutationMapOfList]
    simp only [mulDef, map_mul, Function.comp_apply]
    rw[← h]
    simp[permutationMapLift]

theorem permutationMap_ext (l l' : List B) (t : cs.Reflection) (z : ZMod 2) (h : π l = π l') :
  permutationMapOfList cs l ⟨t,z⟩ = permutationMapOfList cs l' ⟨t,z⟩ := by
  rw[← permutationMap_lift_mk_ofList]
  rw[← permutationMap_lift_mk_ofList]
  simp[h]

/-- The parity of reflection occurrences defined using the lifted permutation action. -/
def parityReflectionOccurrencesLift (w : W) (t : cs.Reflection) : ZMod 2 :=
  (permutationMapLift cs w⁻¹ ⟨t,0⟩).2

theorem parityReflectionOccurrences_lift_mk (l : List B) (t : cs.Reflection) :
    parityReflectionOccurrencesLift cs (cs.wordProd l) t =
      reflectionMemLeftInvSeqParity cs l t := by
  rw[parityReflectionOccurrencesLift]
  rw[← wordProd_reverse]
  rw[permutationMap_lift_mk_ofList cs l.reverse t 0]
  rw[permutationMap_ofList_mk cs l.reverse t 0]
  simp

theorem permutationMap_lift_mk (w : W) (t : cs.Reflection) (z : ZMod 2) :
    permutationMapLift cs w ⟨t,z⟩ =
      ⟨⟨w * t.1 * w⁻¹, IsReflection.conj t.2 w⟩,
        z + parityReflectionOccurrencesLift cs w⁻¹ t⟩ := by
  obtain ⟨l, _, rfl⟩ := cs.exists_isReduced w
  apply Prod.ext
  · simp[permutationMap_lift_mk_ofList, permutationMap_ofList_mk, conjOfReflection]
  · simp only [parityReflectionOccurrencesLift, inv_inv]
    rw[permutationMap_lift_mk_ofList cs l t 0]
    rw[permutationMap_lift_mk_ofList cs l t z]
    simp[permutationMap_ofList_mk]


theorem parityReflectionOccurrences_ext (l l' : List B) (t : cs.Reflection) (h : π l = π l') :
  reflectionMemLeftInvSeqParity cs l t = reflectionMemLeftInvSeqParity cs l' t := by
  calc
    reflectionMemLeftInvSeqParity cs l t =
        parityReflectionOccurrencesLift cs (cs.wordProd l) t := by
      rw[parityReflectionOccurrences_lift_mk]
    _ = parityReflectionOccurrencesLift cs (cs.wordProd l') t := by rw[h]
    _ = reflectionMemLeftInvSeqParity cs l' t := by rw[parityReflectionOccurrences_lift_mk]

lemma odd_iff_parity_eq_one (n : ℕ) : Odd n ↔ (n : ZMod 2) = 1 := by
  simpa [eq_comm] using (ZMod.natCast_eq_one_iff_odd (n := n)).symm

lemma gt_one_of_odd (n : ℕ) : Odd n → n > 0 := by
  intro h
  rcases h with ⟨m, rfl⟩
  suffices m ≥ 0 from by linarith
  exact Nat.zero_le m

lemma isInLeftInvSeq_of_parityReflectionOccurrences_eq_one
    (l : List B) (t : cs.Reflection)
    (h : reflectionMemLeftInvSeqParity cs l t = 1) :
    t.1 ∈ cs.leftInvSeq l := by
  rw [reflectionMemLeftInvSeqParity] at h
  rw [← @odd_iff_parity_eq_one (reflectionMemLeftInvSeqCount cs l t)] at h
  apply gt_one_of_odd (reflectionMemLeftInvSeqCount cs l t) at h
  rw[reflectionMemLeftInvSeqCount] at h
  exact List.count_pos_iff.mp h

lemma isLeftInversion_of_parityReflectionOccurrences_eq_one (l : List B) (t : cs.Reflection) :
  reflectionMemLeftInvSeqParity cs l t = 1 → cs.IsLeftInversion (cs.wordProd l) t.1 := by
  intro h
  rcases cs.exists_isReduced (π l) with ⟨u, u_reduced, hu⟩
  rw[hu]
  apply cs.isLeftInversion_of_mem_leftInvSeq u_reduced
  rw[cs.parityReflectionOccurrences_ext l u t hu] at h
  exact isInLeftInvSeq_of_parityReflectionOccurrences_eq_one cs u t h

lemma isLeftInversion_of_parityReflectionOccurrences_lift_eq_one (w : W) (t : cs.Reflection) :
  parityReflectionOccurrencesLift cs w t = 1 → cs.IsLeftInversion w t.1 := by
  intro h
  obtain ⟨l, _, rfl⟩ := cs.exists_isReduced w
  rw[parityReflectionOccurrences_lift_mk] at h
  apply isLeftInversion_of_parityReflectionOccurrences_eq_one cs l t h

lemma eraseIdx_of_mul_leftInvSeq (l : List B) (t : cs.Reflection) (h : t.1 ∈ cs.leftInvSeq l) :
  ∃ (k : Fin l.length), t.1 * π l = π (l.eraseIdx k) := by
    have : ∃ (k : Fin (cs.leftInvSeq l).length), (cs.leftInvSeq l).get k = t.1 := List.get_of_mem h
    rcases this with ⟨k, hk⟩
    use ⟨k, by rw[← length_leftInvSeq cs l]; exact k.2⟩
    rw[← hk]
    rw[← getD_leftInvSeq_mul_wordProd cs l k]
    simp [List.getElem?_eq_getElem k.2]

lemma permutationMap_lift_simple (p : B) :
  permutationMapLift cs (cs.simple p) = cs.permutationMap p := by
  simp[permutationMapLift]

lemma permutationMap_lift_of_reflection (t : cs.Reflection) : ∀ (z : ZMod 2),
  permutationMapLift cs t.1 (t, z) = ⟨t, z + 1⟩ := by
  rcases t with ⟨t, t_refl⟩
  rcases t_refl with ⟨w, p, rfl⟩
  obtain ⟨l, _, rfl⟩ := cs.wordProd_surjective w
  have : IsReflection cs (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) :=
    IsReflection.conj (isReflection_simple cs p) (cs.wordProd l)
  induction l with
  | nil =>
    simp[permutationMapLift, permutationMap, conjOfReflection, eta]
  | cons i l h =>
    intro z
    simp_rw[wordProd_cons cs i l]
    simp_rw[mul_inv_rev]
    simp_rw[inv_simple]
    simp only [permutationMap_lift_simple, mulDef, map_mul, Function.comp_apply]
    simp only [permutationMap_lift_simple, mulDef, map_mul, Function.comp_apply] at h
    nth_rewrite 3 [permutationMap]
    conv_lhs => simp [conjOfReflection, ← mul_assoc]
    have :
        IsReflection cs
          (cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ * cs.simple i) := by
      nth_rewrite 3 [← inv_simple]
      have : IsReflection cs (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) :=
        IsReflection.conj (isReflection_simple cs p) (cs.wordProd l)
      convert_to
        IsReflection cs
          (cs.simple i * (cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹) *
            (cs.simple i)⁻¹)
      · simp[inv_simple, mul_assoc]
      exact IsReflection.conj this (s i)
    rw[h (IsReflection.conj (isReflection_simple cs p) (cs.wordProd l))
      (z + cs.eta i
        ⟨cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ * cs.simple i,
          this⟩)]
    rw[permutationMap]
    apply Prod.ext
    · simp[conjOfReflection, mul_assoc]
    · simp only [eta, add_assoc]
      by_cases h': cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ = 1
      · have first_eq :
            cs.simple i =
              cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ *
                cs.simple i := by
          rw [h']
          simp
        rw [if_pos first_eq]
        have : cs.simple i = cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ := by
          apply (mul_right_inj (cs.simple i)).mpr at h'
          simp only[mul_assoc, mul_one] at h'
          rw[← h']
          simp[mul_assoc]
        rw [if_pos this]
        simp[ZMod]
        rfl
      · have first_ne :
            ¬cs.simple i =
              cs.simple i * cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ *
                cs.simple i := by
          intro h''
          apply h'
          have hmul := congrArg (fun x => x * cs.simple i) h''
          simpa [mul_assoc, cs.simple_mul_simple_self] using hmul.symm
        have second_ne : ¬cs.simple i = cs.wordProd l * cs.simple p * (cs.wordProd l)⁻¹ := by
          intro h''
          apply h'
          have hmul := congrArg (fun x => cs.simple i * x) h''
          simpa [mul_assoc, cs.simple_mul_simple_self] using hmul.symm
        rw [if_neg first_ne, if_neg second_ne]
        simp

lemma isLeftInversion_iff_parityReflectionOccurrences_eq_one (l : List B) (t : cs.Reflection) :
  cs.IsLeftInversion (cs.wordProd l) t.1 ↔ reflectionMemLeftInvSeqParity cs l t = 1 := by
  constructor
  · intro h
    by_contra h'
    have h'' : reflectionMemLeftInvSeqParity cs l t = 0 := by
      rw [reflectionMemLeftInvSeqParity]
      rw [ZMod.natCast_eq_zero_iff_even]
      rw[reflectionMemLeftInvSeqParity] at h'
      rw[ZMod.natCast_eq_one_iff_odd] at h'
      exact Nat.not_odd_iff_even.mp h'
    suffices cs.IsLeftInversion (t.1 * π l) t.1 from by
      rw[IsLeftInversion] at this
      rw[← mul_assoc] at this
      rcases this with ⟨_, ht⟩
      rw[IsReflection.mul_self t.2] at ht
      simp at ht
      simp[IsLeftInversion] at h
      linarith
    suffices
        permutationMapLift cs (t.1 * π l)⁻¹ ⟨t, 0⟩ =
          ⟨cs.conjOfReflection t (π l)⁻¹, 1⟩ from by
      apply isLeftInversion_of_parityReflectionOccurrences_lift_eq_one cs (t.1 * π l) t
      rw[permutationMap_lift_mk cs (t.1 * π l)⁻¹ t 0] at this
      simp at this
      simp[this.2]
    calc
      permutationMapLift cs (t.1 * π l)⁻¹ ⟨t, 0⟩ =
          permutationMapLift cs (π l)⁻¹ (permutationMapLift cs t.1 ⟨t, 0⟩) := by
          simp[IsReflection.inv t.2]
          rfl
      _ = permutationMapLift cs (π l)⁻¹ ⟨t, 1⟩ := by
          rw[permutationMap_lift_of_reflection cs t 0]
          simp[permutationMap_lift_mk]
      _ = ⟨cs.conjOfReflection t (π l)⁻¹, 1 + parityReflectionOccurrencesLift cs (π l) t⟩ := by
        simp[permutationMap_lift_mk, conjOfReflection]
      _ = (cs.conjOfReflection t (cs.wordProd l)⁻¹, 1) := by
        simp
        simp[parityReflectionOccurrences_lift_mk, h'']
  · exact isLeftInversion_of_parityReflectionOccurrences_eq_one cs l t


theorem strongExchangeProperty (l : List B) (t : cs.Reflection)
(h' : cs.IsLeftInversion (cs.wordProd l) t.1) :
  ∃ (k : Fin l.length), t.1 * π l = π (l.eraseIdx k) := by
  suffices t.1 ∈ cs.leftInvSeq l from eraseIdx_of_mul_leftInvSeq cs l t this
  rw [isLeftInversion_iff_parityReflectionOccurrences_eq_one cs l t] at h'
  exact isInLeftInvSeq_of_parityReflectionOccurrences_eq_one cs l t h'

end

end CoxeterSystem
