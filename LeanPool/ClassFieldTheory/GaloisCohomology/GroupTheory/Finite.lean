/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.Sylow
/-!
# Finite group theory for the splitting corollaries

This file isolates the finite-group inputs for prime-power and normal-closure
splitting arguments.

For the prime-power subgroup reduction, a proper subgroup of a finite group of order `p ^ v` is
contained in a subgroup of index `p`.  The proof below gives the
slightly stronger statement for arbitrary finite `p`-groups.  In the
cyclic case the resulting subgroup is normal, hence produces the
degree-`p` quotient used to choose the intermediate field.

For the normal-closure splitting argument, the normal closure is encoded by a core-free subgroup
`H`.  The canonical map from left cosets to double cosets is
surjective.  If it does not decrease cardinality, its right subgroup
is contained in the normal core of `H`; therefore it is trivial when
`H` is core-free.
-/

noncomputable section

universe uG

section PrimePower

variable {G : Type uG} [Group G] [Finite G]

/-- A proper subgroup of a finite group of prime-power order is
contained in a subgroup of index `p`.

This is the group-theoretic step in the prime-power subgroup reduction.  Mathlib's Sylow
extension theorem proves the stronger result without a cyclicity
assumption. -/
theorem exists_index_prime_supergroup_of_card_prime_power
    {p v : ℕ}
    (hp : p.Prime)
    (hv : 0 < v)
    (hGcard : Nat.card G = p ^ v)
    (D : Subgroup G)
    (hD : D ≠ ⊤) :
    ∃ P : Subgroup G, D ≤ P ∧ P.index = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hGp : IsPGroup p G :=
    IsPGroup.of_card hGcard
  have hDp : IsPGroup p D :=
    hGp.to_subgroup D
  obtain ⟨m, hDcard⟩ :=
    IsPGroup.exists_card_eq hDp
  have hmv : m < v := by
    have hmle : m ≤ v := by
      apply
        (Nat.pow_le_pow_iff_right hp.one_lt).mp
      rw [← hDcard, ← hGcard]
      exact D.card_le_card_group
    have hmne : m ≠ v := by
      intro hmv
      apply hD
      apply
        (Subgroup.card_eq_iff_eq_top D).mp
      rw [hDcard, hmv, hGcard]
    exact lt_of_le_of_ne hmle hmne
  have hmPred : m ≤ v - 1 :=
    Nat.le_sub_one_of_lt hmv
  have hpowDvd :
      p ^ (v - 1) ∣ Nat.card G := by
    rw [hGcard]
    exact
      pow_dvd_pow p (Nat.sub_le v 1)
  obtain ⟨P, hPcard, hDP⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le
      p hpowDvd D hDcard hmPred
  refine ⟨P, hDP, ?_⟩
  have hmul :
      p ^ (v - 1) * P.index = p ^ v := by
    simpa [hPcard, hGcard] using
      P.card_mul_index
  have hvPred : v - 1 + 1 = v :=
    Nat.sub_add_cancel hv
  rw [← hvPred, pow_succ] at hmul
  exact
    Nat.mul_left_cancel (pow_pos hp.pos _) hmul

/-- In a cyclic finite group of prime-power order, the index-`p`
supergroup is normal and its quotient has order `p`. -/
theorem cyclic_exists_normal_index_prime_supergroup
    [IsCyclic G]
    {p v : ℕ}
    (hp : p.Prime)
    (hv : 0 < v)
    (hGcard : Nat.card G = p ^ v)
    (D : Subgroup G)
    (hD : D ≠ ⊤) :
    ∃ P : Subgroup G,
      D ≤ P ∧
      P.index = p ∧
      P.Normal ∧
      Nat.card (G ⧸ P) = p := by
  obtain ⟨P, hDP, hPindex⟩ :=
    exists_index_prime_supergroup_of_card_prime_power
      hp hv hGcard D hD
  have hPnormal : P.Normal :=
    inferInstance
  refine
    ⟨P, hDP, hPindex, hPnormal, ?_⟩
  rw [← P.index_eq_card]
  exact hPindex

omit [Finite G] in
/-- In a cyclic group of finite prime-power cardinality, every proper
subgroup is contained in every subgroup of index `p`. -/
theorem subgroup_le_index_prime_subgroup_of_ne_top_cyclic_prime_power
    [IsCyclic G]
    {p exponent : ℕ}
    (hp : p.Prime)
    (hcard : Nat.card G = p ^ exponent)
    (P D : Subgroup G)
    (hPindex : P.index = p)
    (hD : D ≠ ⊤) :
    D ≤ P := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgtop : Subgroup.zpowers g = ⊤ :=
    (Subgroup.eq_top_iff' (Subgroup.zpowers g)).2 hg
  obtain ⟨n, hn⟩ :=
    (Subgroup.le_zpowers_iff g D).1 (by
      rw [hgtop]
      exact le_top)
  have hgorder : orderOf g = p ^ exponent :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcard
  have hngcd : n.gcd (orderOf g) ≠ 1 := by
    intro hngcd
    apply hD
    rw [hn]
    apply top_unique
    rw [← hgtop, Subgroup.zpowers_le]
    exact mem_zpowers_pow_iff.mpr hngcd
  have hpdiv : p ∣ n := by
    by_contra hpnot
    apply hngcd
    rw [hgorder]
    exact
      (((hp.coprime_iff_not_dvd).2 hpnot).symm.pow_right
        exponent).gcd_eq_one
  obtain ⟨k, rfl⟩ := hpdiv
  rw [hn]
  apply (Subgroup.zpowers_le).2
  have hpow := P.pow_index_mem (g ^ k)
  rw [hPindex] at hpow
  have heq : (g ^ k) ^ p = g ^ (p * k) := by
    simp only [← pow_mul, Nat.mul_comm]
  rw [← heq]
  exact hpow

end PrimePower

section PrimeOrder

variable (G : Type uG) [Group G] [Finite G] [Nontrivial G]

/-- Every nontrivial finite group contains an element of prime order.
This supplies the cyclic prime-degree subgroup used after passing to a
normal closure. -/
theorem exists_element_of_prime_order :
    ∃ (p : ℕ) (g : G),
      p.Prime ∧ orderOf g = p := by
  obtain ⟨p, hp, hpDvd⟩ :=
    Nat.exists_prime_and_dvd
      (ne_of_gt (Finite.one_lt_card :
        1 < Nat.card G))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := G) p hpDvd
  exact ⟨p, g, hp, hg⟩

/-- Every nontrivial finite group contains an actual cyclic subgroup
of prime cardinality. -/
theorem exists_cyclic_subgroup_of_prime_card :
    ∃ (p : ℕ) (P : Subgroup G),
      p.Prime ∧ Nat.card P = p ∧ IsCyclic P := by
  obtain ⟨p, g, hp, hg⟩ :=
    exists_element_of_prime_order G
  refine
    ⟨p, Subgroup.zpowers g, hp, ?_, inferInstance⟩
  rw [Nat.card_zpowers, hg]

end PrimeOrder

section DoubleCosets

variable {G : Type uG} [Group G]

/-- The canonical projection
`H \ G = H \ G / 1 → H \ G / D`. -/
def doubleCosetRightProjection
    (H D : Subgroup G) :
    DoubleCoset.Quotient
        (H : Set G) (⊥ : Subgroup G) →
      DoubleCoset.Quotient (H : Set G) D :=
  Quotient.map' id fun a b hab ↦ by
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨h, hh, k, hk, hab⟩ := hab
    have hkOne : k = 1 :=
      Subgroup.mem_bot.mp hk
    subst k
    exact
      ⟨h, hh, 1, D.one_mem, by simpa using hab⟩

@[simp]
theorem doubleCosetRightProjection_mk
    (H D : Subgroup G)
    (g : G) :
    doubleCosetRightProjection H D
        (DoubleCoset.mk H (⊥ : Subgroup G) g) =
      DoubleCoset.mk H D g :=
  Quotient.map'_mk'' _ _ _

/-- The projection from left cosets to double cosets is onto. -/
theorem doubleCosetRightProjection_surjective
    (H D : Subgroup G) :
    Function.Surjective
      (doubleCosetRightProjection H D) := by
  intro q
  refine
    ⟨DoubleCoset.mk H (⊥ : Subgroup G) q.out, ?_⟩
  rw [doubleCosetRightProjection_mk]
  exact DoubleCoset.out_eq' q

/-- If the left-coset to double-coset projection is injective, then
the right subgroup lies in the normal core of the left subgroup. -/
theorem rightSubgroup_le_normalCore_of_doubleCoset_projection_injective
    (H D : Subgroup G)
    (hinj : Function.Injective
      (doubleCosetRightProjection H D)) :
    D ≤ H.normalCore := by
  intro d hd g
  have hdouble :
      DoubleCoset.mk H D g =
        DoubleCoset.mk H D (g * d) := by
    rw [DoubleCoset.eq]
    exact
      ⟨1, H.one_mem, d, hd, by simp⟩
  have hleft :
      DoubleCoset.mk H (⊥ : Subgroup G) g =
        DoubleCoset.mk H (⊥ : Subgroup G)
          (g * d) := by
    apply hinj
    simpa only
      [doubleCosetRightProjection_mk]
      using hdouble
  rw [DoubleCoset.eq] at hleft
  obtain ⟨h, hh, k, hk, heq⟩ := hleft
  have hkOne : k = 1 :=
    Subgroup.mem_bot.mp hk
  subst k
  simp only [mul_one] at heq
  have hconj : g * d * g⁻¹ = h := by
    calc
      g * d * g⁻¹ =
          (g * d) * g⁻¹ := rfl
      _ = (h * g) * g⁻¹ := by
        rw [heq]
      _ = h := by simp
  rw [hconj]
  exact hh

/-- Equality between the number of left cosets and the number of
double cosets forces the right subgroup into the normal core. -/
theorem rightSubgroup_le_normalCore_of_doubleCoset_card_eq
    [Finite G]
    (H D : Subgroup G)
    (hcard :
      Nat.card
          (DoubleCoset.Quotient (H : Set G) D) =
        Nat.card
          (DoubleCoset.Quotient (H : Set G)
            (⊥ : Subgroup G))) :
    D ≤ H.normalCore := by
  let :
      Finite
        (DoubleCoset.Quotient (H : Set G)
          (⊥ : Subgroup G)) :=
    Finite.of_surjective
      (DoubleCoset.mk H (⊥ : Subgroup G))
      (by
        intro q
        exact
          ⟨q.out,
            DoubleCoset.out_eq' q⟩)
  have hbij :
      Function.Bijective
        (doubleCosetRightProjection H D) :=
    Function.Surjective.bijective_of_nat_card_le
      (doubleCosetRightProjection_surjective H D)
      hcard.symm.le
  exact
    rightSubgroup_le_normalCore_of_doubleCoset_projection_injective
      H D hbij.injective

/-- For a core-free subgroup `H`, the double-coset count equals the
left-coset count exactly when the right subgroup is trivial.

This is the finite-group content of the normal-closure reduction. -/
theorem doubleCoset_card_eq_leftCoset_iff_of_normalCore_eq_bot
    [Finite G]
    (H D : Subgroup G)
    (hcore : H.normalCore = ⊥) :
    Nat.card
          (DoubleCoset.Quotient (H : Set G) D) =
        Nat.card
          (DoubleCoset.Quotient (H : Set G)
            (⊥ : Subgroup G)) ↔
      D = ⊥ := by
  constructor
  · intro hcard
    apply le_bot_iff.mp
    rw [← hcore]
    exact
      rightSubgroup_le_normalCore_of_doubleCoset_card_eq
        H D hcard
  · rintro rfl
    rfl

end DoubleCosets
