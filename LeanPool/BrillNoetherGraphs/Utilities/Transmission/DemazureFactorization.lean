/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionWedgeDemazure
public import LeanPool.BrillNoetherGraphs.Demazure.Transpositions

/-!
# Finite Demazure factorizations

Finite ASP permutations admit Demazure factorizations at every prescribed
inversion-length cut.  This supplies the combinatorial input needed for
unconditional opposite-side vertex-wedge transmission gluing.
-/

@[expose] public section

namespace AspPerm

private theorem singleton_noConsecutive (i : ℤ) :
    Transpositions.NoConsecutive ({i} : Set ℤ) := by
  intro n hn hsucc
  simp only [Set.mem_singleton_iff] at hn hsucc
  omega

/-- The adjacent reflection interchanging positions `i` and `i + 1`. -/
noncomputable def simpleReflection (i : ℤ) : AspPerm :=
  Transpositions.sigma {i} (by exact singleton_noConsecutive i)

@[simp] theorem simpleReflection_chi (i : ℤ) : (simpleReflection i).χ = 0 := by
  exact Transpositions.sigma_chi {i} (singleton_noConsecutive i)

@[simp] theorem simpleReflection_apply (i n : ℤ) :
    simpleReflection i n =
      if n = i then i + 1 else if n = i + 1 then i else n := by
  simp only [simpleReflection, Transpositions.sigma, Transpositions.sigmaFun,
    Set.mem_singleton_iff]
  split_ifs <;> omega

@[simp] theorem simpleReflection_involutive (i n : ℤ) :
    simpleReflection i (simpleReflection i n) = n := by
  rw [simpleReflection_apply, simpleReflection_apply]
  split_ifs <;> omega

@[simp] theorem simpleReflection_inv_set (i : ℤ) :
    invSet (simpleReflection i) = {⟨i, i + 1⟩} := by
  ext p
  rcases p with ⟨a, b⟩
  simp only [invSet, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [simpleReflection_apply, simpleReflection_apply]
  constructor
  · rintro ⟨hab, hlt⟩
    split_ifs at hlt <;> omega
  · rintro ⟨rfl, rfl⟩
    norm_num

private theorem simpleReflection_lt_of_lt_of_ne
    (i a b : ℤ) (hab : a < b) (hne : (a, b) ≠ (i, i + 1)) :
    simpleReflection i a < simpleReflection i b := by
  rw [simpleReflection_apply, simpleReflection_apply]
  split_ifs <;> try omega
  all_goals
    exfalso
    apply hne
    apply Prod.ext <;> omega

/-- Apply the adjacent reflection to both coordinates of an inversion pair. -/
noncomputable def swapPair (i : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (simpleReflection i p.1, simpleReflection i p.2)

@[simp] private theorem swapPair_involutive (i : ℤ) (p : ℤ × ℤ) :
    swapPair i (swapPair i p) = p := by
  rcases p with ⟨a, b⟩
  apply Prod.ext
  · exact simpleReflection_involutive i a
  · exact simpleReflection_involutive i b

private theorem swapPair_ne_exceptional_of_lt
    (i a b : ℤ) (hab : a < b) : swapPair i (a, b) ≠ (i, i + 1) := by
  intro h
  have hs := congrArg (swapPair i) h
  simp only [swapPair_involutive] at hs
  rw [show swapPair i (i, i + 1) = (i + 1, i) by
    simp [swapPair, simpleReflection_apply]] at hs
  rw [Prod.mk.injEq] at hs
  omega

private theorem mul_simple_apply (τ : AspPerm) (i n : ℤ) :
    AspPerm.mul τ (simpleReflection i) n = τ (simpleReflection i n) := rfl

/-- The nonexceptional inversions before and after right multiplication by an
adjacent reflection are in canonical bijection. -/
noncomputable def invSetEraseSimpleEquiv (τ : AspPerm) (i : ℤ) :
    {p // p ∈ invSet (AspPerm.mul τ (simpleReflection i)) \
      ({(i, i + 1)} : Set (ℤ × ℤ))} ≃
      {p // p ∈ invSet τ \ ({(i, i + 1)} : Set (ℤ × ℤ))} where
  toFun p := ⟨swapPair i p.val, by
    rcases p with ⟨⟨a, b⟩, hp⟩
    rcases hp with ⟨⟨hab, hτ⟩, hne⟩
    constructor
    · refine ⟨simpleReflection_lt_of_lt_of_ne i a b hab ?_, ?_⟩
      · simpa only [Set.mem_singleton_iff] using hne
      · simpa only [mul_simple_apply] using hτ
    · simpa only [Set.mem_singleton_iff] using
        swapPair_ne_exceptional_of_lt i a b hab⟩
  invFun p := ⟨swapPair i p.val, by
    rcases p with ⟨⟨a, b⟩, hp⟩
    rcases hp with ⟨⟨hab, hτ⟩, hne⟩
    constructor
    · refine ⟨simpleReflection_lt_of_lt_of_ne i a b hab ?_, ?_⟩
      · simpa only [Set.mem_singleton_iff] using hne
      · change τ (simpleReflection i (simpleReflection i b)) <
          τ (simpleReflection i (simpleReflection i a))
        simpa only [simpleReflection_involutive] using hτ
    · simpa only [Set.mem_singleton_iff] using
        swapPair_ne_exceptional_of_lt i a b hab⟩
  left_inv p := by
    apply Subtype.ext
    exact swapPair_involutive i p.1
  right_inv p := by
    apply Subtype.ext
    exact swapPair_involutive i p.1

/-- Right multiplication by an adjacent reflection preserves finiteness of the
inversion set. -/
theorem finite_invSet_mul_simple_iff (τ : AspPerm) (i : ℤ) :
    (invSet (AspPerm.mul τ (simpleReflection i))).Finite ↔
      (invSet τ).Finite := by
  let A : Set (ℤ × ℤ) := invSet (AspPerm.mul τ (simpleReflection i))
  let B : Set (ℤ × ℤ) := invSet τ
  let e : Set (ℤ × ℤ) := {(i, i + 1)}
  have hdiff : (A \ e).Finite ↔ (B \ e).Finite := by
    rw [Set.finite_def, Set.finite_def]
    constructor
    · rintro ⟨hA⟩
      let _ := hA
      have : Finite ↥(B \ e) :=
        Finite.of_equiv ↥(A \ e) (invSetEraseSimpleEquiv τ i)
      exact ⟨Fintype.ofFinite ↥(B \ e)⟩
    · rintro ⟨hB⟩
      let _ := hB
      have : Finite ↥(A \ e) :=
        Finite.of_equiv ↥(B \ e) (invSetEraseSimpleEquiv τ i).symm
      exact ⟨Fintype.ofFinite ↥(A \ e)⟩
  constructor
  · intro hA
    apply Set.Finite.of_sdiff (hd := (hdiff.mp hA.sdiff))
    exact Set.finite_singleton _
  · intro hB
    apply Set.Finite.of_sdiff (hd := (hdiff.mpr hB.sdiff))
    exact Set.finite_singleton _

/-- Finite inversion length. -/
noncomputable def invLength (τ : AspPerm) : ℕ := (invSet τ).ncard

private theorem exceptional_mem_invSet_mul_simple_iff (τ : AspPerm) (i : ℤ) :
    (i, i + 1) ∈ invSet (AspPerm.mul τ (simpleReflection i)) ↔
      τ i < τ (i + 1) := by
  simp only [invSet, Set.mem_ofPred_eq, mul_simple_apply]
  simp [simpleReflection_apply]

private theorem exceptional_mem_invSet_iff (τ : AspPerm) (i : ℤ) :
    (i, i + 1) ∈ invSet τ ↔ τ (i + 1) < τ i := by
  simp [invSet]

private theorem ncard_invSet_delete_simple_eq (τ : AspPerm) (i : ℤ) :
    (invSet (AspPerm.mul τ (simpleReflection i)) \
      ({(i, i + 1)} : Set (ℤ × ℤ))).ncard =
      (invSet τ \ ({(i, i + 1)} : Set (ℤ × ℤ))).ncard := by
  exact Set.ncard_congr' (invSetEraseSimpleEquiv τ i)

/-- Right multiplication by an adjacent reflection adds one inversion at an
ascent. -/
theorem invLength_mul_simple_of_ascent (τ : AspPerm) (i : ℤ)
    (hfin : (invSet τ).Finite) (hasc : τ i < τ (i + 1)) :
    invLength (AspPerm.mul τ (simpleReflection i)) = invLength τ + 1 := by
  let A : Set (ℤ × ℤ) := invSet (AspPerm.mul τ (simpleReflection i))
  let B : Set (ℤ × ℤ) := invSet τ
  let e : ℤ × ℤ := (i, i + 1)
  have hAfin : A.Finite := (finite_invSet_mul_simple_iff τ i).2 hfin
  have heA : e ∈ A := (exceptional_mem_invSet_mul_simple_iff τ i).2 hasc
  have heB : e ∉ B := by
    rw [exceptional_mem_invSet_iff]
    omega
  have herase := ncard_invSet_delete_simple_eq τ i
  change A.ncard = B.ncard + 1
  calc
    A.ncard = (A \ {e}).ncard + 1 :=
      (Set.ncard_sdiff_singleton_add_one heA hAfin).symm
    _ = (B \ {e}).ncard + 1 := by rw [herase]
    _ = B.ncard + 1 := by simp [heB]

/-- Right multiplication by an adjacent reflection removes one inversion at a
descent, stated additively to avoid truncated subtraction. -/
theorem invLength_mul_simple_add_one_of_descent (τ : AspPerm) (i : ℤ)
    (hfin : (invSet τ).Finite) (hdesc : τ (i + 1) < τ i) :
    invLength (AspPerm.mul τ (simpleReflection i)) + 1 = invLength τ := by
  let A : Set (ℤ × ℤ) := invSet (AspPerm.mul τ (simpleReflection i))
  let B : Set (ℤ × ℤ) := invSet τ
  let e : ℤ × ℤ := (i, i + 1)
  have heA : e ∉ A := by
    rw [exceptional_mem_invSet_mul_simple_iff]
    omega
  have heB : e ∈ B := (exceptional_mem_invSet_iff τ i).2 hdesc
  have herase := ncard_invSet_delete_simple_eq τ i
  change A.ncard + 1 = B.ncard
  calc
    A.ncard + 1 = (A \ {e}).ncard + 1 := by simp [heA]
    _ = (B \ {e}).ncard + 1 := by rw [herase]
    _ = B.ncard := Set.ncard_sdiff_singleton_add_one heB hfin

private theorem exists_adjacent_descent_nat
    (f : ℤ → ℤ) (hf : Function.Injective f) (a : ℤ) :
    ∀ n : ℕ, f (a + n) < f a →
      ∃ k : ℕ, k < n ∧ f (a + k + 1) < f (a + k) := by
  intro n
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      intro hlast
      by_cases hfirst : f (a + 1) < f a
      · exact ⟨0, Nat.zero_lt_succ n, by simpa⟩
      · have hne : f (a + 1) ≠ f a := by
          intro h
          have := hf h
          omega
        have hrise : f a < f (a + 1) := by omega
        have htail : f ((a + 1) + n) < f (a + 1) := by
          have heq : a + (n.succ : ℤ) = (a + 1) + (n : ℤ) := by
            push_cast
            omega
          rw [← heq]
          exact lt_trans hlast hrise
        rcases ih (a + 1) htail with ⟨k, hk, hdrop⟩
        refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
        have hleft : a + (k + 1 : ℕ) + 1 = (a + 1) + (k : ℤ) + 1 := by
          push_cast
          omega
        have hright : a + (k + 1 : ℕ) = (a + 1) + (k : ℤ) := by
          push_cast
          omega
        rw [hleft, hright]
        exact hdrop

/-- Every inversion contains an adjacent descent. -/
theorem exists_adjacent_descent_of_mem_invSet (τ : AspPerm) {a b : ℤ}
    (hab : (a, b) ∈ invSet τ) :
    ∃ i : ℤ, a ≤ i ∧ i < b ∧ τ (i + 1) < τ i := by
  rcases hab with ⟨hab, hinv⟩
  let n := (b - a).toNat
  have hncast : (n : ℤ) = b - a := by
    exact Int.toNat_of_nonneg (by omega)
  have hend : τ (a + n) < τ a := by
    have heq : a + (n : ℤ) = b := by omega
    rw [heq]
    exact hinv
  rcases exists_adjacent_descent_nat τ τ.injective a n hend with ⟨k, hk, hdrop⟩
  refine ⟨a + k, by omega, ?_, ?_⟩
  · omega
  · simpa only [add_assoc] using hdrop

/-- Positive finite inversion length gives an adjacent descent. -/
theorem exists_adjacent_descent_of_invLength_pos (τ : AspPerm)
    (hfin : (invSet τ).Finite) (hpos : 0 < invLength τ) :
    ∃ i : ℤ, τ (i + 1) < τ i := by
  have hnonempty : (invSet τ).Nonempty :=
    (Set.ncard_pos hfin).mp hpos
  rcases hnonempty with ⟨⟨a, b⟩, hab⟩
  rcases exists_adjacent_descent_of_mem_invSet τ hab with ⟨i, -, -, hi⟩
  exact ⟨i, hi⟩

private theorem star_simple_of_ascent (τ : AspPerm) (i : ℤ)
    (hasc : τ i < τ (i + 1)) :
    τ ⋆ simpleReflection i = AspPerm.mul τ (simpleReflection i) := by
  rw [Transpositions.star_simple τ (simpleReflection i) i
    (simpleReflection_chi i) (simpleReflection_inv_set i), ite_eq_left hasc]
  rfl

private theorem star_simple_of_descent (τ : AspPerm) (i : ℤ)
    (hdesc : τ (i + 1) < τ i) :
    τ ⋆ simpleReflection i = τ := by
  rw [Transpositions.star_simple τ (simpleReflection i) i
    (simpleReflection_chi i) (simpleReflection_inv_set i)]
  rw [ite_eq_right (by omega)]

/-- A positive-length finite ASP permutation is a shorter permutation
Demazure-multiplied on the right by one adjacent reflection. -/
theorem exists_right_simple_factor_of_invLength_pos (τ : AspPerm)
    (hfin : (invSet τ).Finite) (hpos : 0 < invLength τ) :
    ∃ τ' i,
      τ = τ' ⋆ simpleReflection i ∧
      (invSet τ').Finite ∧
      invLength τ' + 1 = invLength τ := by
  rcases exists_adjacent_descent_of_invLength_pos τ hfin hpos with ⟨i, hi⟩
  let τ' := AspPerm.mul τ (simpleReflection i)
  have hτ'fin : (invSet τ').Finite :=
    (finite_invSet_mul_simple_iff τ i).2 hfin
  have hlen : invLength τ' + 1 = invLength τ :=
    invLength_mul_simple_add_one_of_descent τ i hfin hi
  have hτ'ascent : τ' i < τ' (i + 1) := by
    simp only [τ', mul_simple_apply]
    simp [simpleReflection_apply, hi]
  refine ⟨τ', i, ?_, hτ'fin, hlen⟩
  rw [star_simple_of_ascent τ' i hτ'ascent]
  apply (AspPerm.ext).2
  funext n
  change τ n = τ (simpleReflection i (simpleReflection i n))
  rw [simpleReflection_involutive]

/-- Peel exactly `k` inversions into a zero-shift right factor. -/
theorem exists_star_factorization_right_length (τ : AspPerm)
    (hfin : (invSet τ).Finite) (k : ℕ) (hk : k ≤ invLength τ) :
    ∃ α β : AspPerm,
      τ = α ⋆ β ∧
      (invSet α).Finite ∧
      (invSet β).Finite ∧
      invLength α = invLength τ - k ∧
      invLength β = k ∧
      β.χ = 0 := by
  induction k generalizing τ with
  | zero =>
      refine ⟨τ, AspPerm.id, AspPerm.star_id τ |>.symm, hfin, ?_, ?_, ?_, ?_⟩
      · rw [AspPerm.inv_set_id]
        exact Set.finite_empty
      · omega
      · simp [invLength, AspPerm.inv_set_id]
      · simp
  | succ k ih =>
      have hpos : 0 < invLength τ := lt_of_lt_of_le (Nat.zero_lt_succ k) hk
      rcases exists_right_simple_factor_of_invLength_pos τ hfin hpos with
        ⟨τ', i, hτ, hτ'fin, hlen⟩
      have hk' : k ≤ invLength τ' := by omega
      rcases ih τ' hτ'fin hk' with
        ⟨α, β', hfac, hαfin, hβ'fin, hαlen, hβ'len, hβchi⟩
      have hτne : τ ≠ τ' := by
        intro heq
        rw [heq] at hlen
        omega
      have hβascent : β' i < β' (i + 1) := by
        by_contra hnot
        have hne : β' i ≠ β' (i + 1) := by
          intro heq
          have := β'.injective heq
          omega
        have hdesc : β' (i + 1) < β' i := by omega
        have habsorb := star_simple_of_descent β' i hdesc
        apply hτne
        calc
          τ = τ' ⋆ simpleReflection i := hτ
          _ = (α ⋆ β') ⋆ simpleReflection i := by rw [← hfac]
          _ = α ⋆ (β' ⋆ simpleReflection i) := AspPerm.star_assoc α β' _
          _ = α ⋆ β' := by rw [habsorb]
          _ = τ' := hfac.symm
      have hβstar := star_simple_of_ascent β' i hβascent
      let β := β' ⋆ simpleReflection i
      have hβfin : (invSet β).Finite := by
        change (invSet (β' ⋆ simpleReflection i)).Finite
        rw [hβstar]
        exact (finite_invSet_mul_simple_iff β' i).2 hβ'fin
      have hβlen : invLength β = k + 1 := by
        change invLength (β' ⋆ simpleReflection i) = k + 1
        rw [hβstar, invLength_mul_simple_of_ascent β' i hβ'fin hβascent,
          hβ'len]
      refine ⟨α, β, ?_, hαfin, hβfin, ?_, hβlen, ?_⟩
      · calc
          τ = τ' ⋆ simpleReflection i := hτ
          _ = (α ⋆ β') ⋆ simpleReflection i := by rw [← hfac]
          _ = α ⋆ (β' ⋆ simpleReflection i) := AspPerm.star_assoc α β' _
          _ = α ⋆ β := rfl
      · omega
      · change (β' ⋆ simpleReflection i).χ = 0
        rw [AspPerm.chi_star, hβchi, simpleReflection_chi]
        omega

/-- Split a finite ASP permutation at every prescribed inversion-length cut. -/
theorem exists_star_factorization_invLength (τ : AspPerm)
    (hfin : (invSet τ).Finite) (m : ℕ) :
    ∃ α β : AspPerm,
      τ = α ⋆ β ∧
      (invSet α).Finite ∧
      (invSet β).Finite ∧
      invLength α = min m (invLength τ) ∧
      invLength β = invLength τ - min m (invLength τ) ∧
      β.χ = 0 := by
  let k := invLength τ - min m (invLength τ)
  have hk : k ≤ invLength τ := Nat.sub_le _ _
  rcases exists_star_factorization_right_length τ hfin k hk with
    ⟨α, β, hfac, hαfin, hβfin, hαlen, hβlen, hβchi⟩
  refine ⟨α, β, hfac, hαfin, hβfin, ?_, ?_, hβchi⟩
  · omega
  · simpa only [k] using hβlen

end AspPerm

namespace Utilities

open AspPerm

/-- Every pair of nonnegative budgets has the required bounded finite
Demazure-factorization property. -/
theorem hasBoundedDemazureFactorizations_of_nonneg
    (gG gH : ℤ) (hG : 0 ≤ gG) (hH : 0 ≤ gH) :
    HasBoundedDemazureFactorizations gG gH := by
  intro τ hFinite hLength
  let L := invLength τ
  let m := min gG.toNat L
  rcases exists_star_factorization_invLength τ hFinite m with
    ⟨α, β, hfac, hαfin, hβfin, hαlen, hβlen, -⟩
  refine ⟨α, β, hfac, hαfin, ?_, hβfin, ?_⟩
  · have hGcast : (gG.toNat : ℤ) = gG := Int.toNat_of_nonneg hG
    change (invLength α : ℤ) ≤ gG
    rw [hαlen]
    have hm : min gG.toNat L ≤ gG.toNat := min_le_left _ _
    omega
  · have hGcast : (gG.toNat : ℤ) = gG := Int.toNat_of_nonneg hG
    have htotal : (L : ℤ) ≤ gG + gH := by
      simpa only [L, invLength] using hLength
    change (invLength β : ℤ) ≤ gH
    rw [hβlen]
    omega

/-- Opposite-side transmission existence is closed under vertex wedges. -/
theorem transmissionExistence_vertexWedge_opposite
    (G : CFGraph) (H : CFGraph) (x : G.V) (y : H.V)
    (u : G.V) (v : H.V)
    (hTG : TransmissionExistence G u x)
    (hTH : TransmissionExistence H y v)
    (hGenusG : 0 ≤ genus G) (hGenusH : 0 ≤ genus H) :
    TransmissionExistence (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) := by
  apply transmissionExistence_vertexWedge_opposite_of_factorizations
    G H x y u v hTG hTH
  exact hasBoundedDemazureFactorizations_of_nonneg
    (genus G : ℤ) (genus H : ℤ) hGenusG hGenusH

end Utilities
