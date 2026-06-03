/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.NSubring
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Order.CompletePartialOrder

/-!
# Transfinite Union of A-extensions

A well-ordered ascending chain of A-extensions has union that is
again an N-subring: the UFD property and prime preservation pass
to the colimit.

Heitmann, "Characterization of completions of UFDs", 1993, Lemma 6
Loepp, "Constructing local generic formal fibers", 1997, Lemmas 14--15.
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Chain of N-subrings

A well-ordered ascending chain of N-subrings where each successor step
is an A-extension and limit steps are unions.
-/

/-- A well-ordered ascending chain of N-subrings indexed by a linearly ordered type.
Prime elements are preserved along the chain (A-extension property). -/
structure NSubringChain (T : Type*) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsDomain T] (ι : Type*) [Preorder ι] where
  /-- The N-subring at each index -/
  ring : ι → NSubring T
  /-- The chain is ascending -/
  mono : ∀ ⦃α β : ι⦄, α ≤ β → (ring α).carrier ≤ (ring β).carrier
  /-- Prime elements are preserved along the chain -/
  primes_preserved : ∀ ⦃α β : ι⦄ (h : α ≤ β) (r : (ring α).carrier),
    Prime r → Prime (⟨r.1, mono h r.2⟩ : (ring β).carrier)

variable {ι : Type*} [LinearOrder ι]

namespace NSubringChain

/-- The family of carriers is directed (since ι is linearly ordered). -/
lemma directed_carriers (chain : NSubringChain T ι) :
    Directed (· ≤ ·) (fun α => (chain.ring α).carrier) :=
  fun α β => ⟨max α β, chain.mono (le_max_left α β), chain.mono (le_max_right α β)⟩

/-- The union of all subrings in the chain. -/
def unionSubring (chain : NSubringChain T ι) : Subring T :=
  ⨆ (α : ι), (chain.ring α).carrier

/-- Every chain member is contained in the union. -/
lemma le_union (chain : NSubringChain T ι) (α : ι) :
    (chain.ring α).carrier ≤ chain.unionSubring :=
  le_iSup (fun α => (chain.ring α).carrier) α

/-- An element is in the union iff it's in some chain member. -/
lemma mem_union_iff [Nonempty ι] (chain : NSubringChain T ι) {x : T} :
    x ∈ chain.unionSubring ↔ ∃ α, x ∈ (chain.ring α).carrier := by
  exact Subring.mem_iSup_of_directed chain.directed_carriers

end NSubringChain

/-- Prime elements of any R_α remain prime in the union. -/
theorem transfinite_union_primes_preserved
    [Nonempty ι]
    (chain : NSubringChain T ι)
    (S : Subring T)
    (hS : ∀ (α : ι), (chain.ring α).carrier ≤ S)
    (hS_union : ∀ (x : S), ∃ (α : ι),
      (x : T) ∈ (chain.ring α).carrier)
    (α : ι)
    (p : (chain.ring α).carrier) (hp : Prime p) :
    Prime (⟨(p : T), hS α p.2⟩ : S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hp.ne_zero
    ext
    exact congrArg (fun (x : ↥S) => (x : T)) h
  · intro hu
    set q : ↥S := ↑(hu.unit⁻¹)
    obtain ⟨β, hβ⟩ := hS_union q
    have hp' := chain.primes_preserved (le_max_left α β) p hp
    apply hp'.not_unit
    have hpq : (p : T) * (q : T) = 1 := by
      have h1 := congrArg (fun (x : ↥S) => (x : T)) hu.unit.val_inv
      simp only [Subring.coe_mul, Subring.coe_one] at h1
      rwa [show ((hu.unit : ↥S) : T) = (p : T) from
        congrArg Subtype.val (IsUnit.unit_spec hu)] at h1
    exact .of_mul_eq_one
      (⟨(q : T), chain.mono (le_max_right α β) hβ⟩ :
        (chain.ring (max α β)).carrier)
      (Subtype.ext hpq)
  · intro a b ⟨c, hc⟩
    obtain ⟨βa, ha'⟩ := hS_union a
    obtain ⟨βb, hb'⟩ := hS_union b
    obtain ⟨βc, hc'⟩ := hS_union c
    set δ := max α (max βa (max βb βc))
    have hαδ : α ≤ δ := le_max_left _ _
    have haδ : βa ≤ δ :=
      le_trans (le_max_left _ _) (le_max_right α _)
    have hbδ : βb ≤ δ :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
        (le_max_right α _)
    have hcδ : βc ≤ δ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
        (le_max_right α _)
    set p' : (chain.ring δ).carrier :=
      ⟨(p : T), chain.mono hαδ p.2⟩
    set a' : (chain.ring δ).carrier :=
      ⟨(a : T), chain.mono haδ ha'⟩
    set b' : (chain.ring δ).carrier :=
      ⟨(b : T), chain.mono hbδ hb'⟩
    set c' : (chain.ring δ).carrier :=
      ⟨(c : T), chain.mono hcδ hc'⟩
    have hp' := chain.primes_preserved hαδ p hp
    have hmul : a' * b' = p' * c' :=
      Subtype.ext (show (a : T) * (b : T) = (p : T) * (c : T)
        from congrArg Subtype.val hc)
    rcases hp'.dvd_or_dvd ⟨c', hmul⟩ with ⟨d, hd⟩ | ⟨d, hd⟩
    · left
      exact ⟨⟨(d : T), hS δ d.2⟩, Subtype.ext (by
        have := congrArg Subtype.val hd
        simp only [a', Subring.coe_mul] at this
        exact this)⟩
    · right
      exact ⟨⟨(d : T), hS δ d.2⟩, Subtype.ext (by
        have := congrArg Subtype.val hd
        simp only [b', Subring.coe_mul] at this
        exact this)⟩

/-- The union of A-extensions is a UFD.
If x is irreducible in ⋃ R_α, then x ∈ R_β for some β, and x is prime
in R_β (since R_β is a UFD), hence x | a or x | b in R_β ⊆ ⋃ R_α. -/
theorem transfinite_union_isUFD
    [Nonempty ι]
    (chain : NSubringChain T ι)
    (S : Subring T)
    (hS : ∀ (α : ι), (chain.ring α).carrier ≤ S)
    (hS_union : ∀ (x : S), ∃ (α : ι),
      (x : T) ∈ (chain.ring α).carrier) :
    UniqueFactorizationMonoid S := by
  apply UniqueFactorizationMonoid.of_exists_prime_factors
  intro a ha
  obtain ⟨α, hα⟩ := hS_union a
  let incl : (chain.ring α).carrier →+* ↥S :=
    Subring.inclusion (hS α)
  set a_α : (chain.ring α).carrier := ⟨(a : T), hα⟩
  have ha_α : a_α ≠ 0 := by
    intro h
    apply ha
    ext
    exact congrArg (fun (x : ↥(chain.ring α).carrier) => (x : T)) h
  obtain ⟨f, hf_prime, hf_assoc⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors a_α ha_α
  refine ⟨f.map incl, ?_, ?_⟩
  · intro b hb
    rw [Multiset.mem_map] at hb
    obtain ⟨b₀, hb₀_mem, rfl⟩ := hb
    exact transfinite_union_primes_preserved chain S hS hS_union
      α b₀ (hf_prime b₀ hb₀_mem)
  · rw [← map_multiset_prod incl f]
    have : incl a_α = a := Subtype.ext rfl
    rw [← this]
    exact hf_assoc.map incl

/-- Heitmann Lemma 6: The union of a well-ordered ascending chain of
A-extensions is an N-subring (modulo cardinality bound).

Key properties preserved:
- UFD: factors in some R_α
irreducibles are prime.
- N-subring conditions (2) and (3) pass to unions.
- Cardinality: |⋃ R_α| ≤ sup(ℵ₀, |R₀|, |α|). -/
theorem transfinite_union_isNSubring
    {ι' : Type u_1} [LinearOrder ι'] [Nonempty ι']
    (chain : NSubringChain T ι')
    (h_card : ∀ (α : ι'),
      Cardinal.mk (chain.ring α).carrier ≤
        max Cardinal.aleph0
          (Cardinal.mk (IsLocalRing.ResidueField T)))
    (h_ι_card : Cardinal.mk ι' ≤
      max Cardinal.aleph0
        (Cardinal.mk (IsLocalRing.ResidueField T))) :
    ∃ S : NSubring T,
      (∀ (α : ι'), (chain.ring α).carrier ≤ S.carrier) := by
  set S := chain.unionSubring with hS_def
  have hS_le : ∀ α, (chain.ring α).carrier ≤ S := chain.le_union
  have hS_union : ∀ x : ↥S, ∃ α, (x : T) ∈ (chain.ring α).carrier :=
    fun x => chain.mem_union_iff.mp x.2
  haveI hIsLocal : IsLocalRing S := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro a
    obtain ⟨α, hα⟩ := hS_union a
    have hloc := IsLocalRing.isUnit_or_isUnit_one_sub_self
      (⟨(a : T), hα⟩ : (chain.ring α).carrier)
    let incl := Subring.inclusion (hS_le α)
    rcases hloc with hu | hu
    · left
      exact hu.map incl
    · right
      have : incl (1 - ⟨(a : T), hα⟩) = 1 - a :=
        Subtype.ext rfl
      rw [← this]
      exact hu.map incl
  refine ⟨⟨S, ?_, ?_, ?_, ?_, ?_⟩, hS_le⟩
  · exact transfinite_union_isUFD chain S hS_le hS_union
  · exact hIsLocal
  · have hS_eq : (S : Set T) = ⋃ α, ↑(chain.ring α).carrier := by
      rw [hS_def, NSubringChain.unionSubring]
      exact Subring.coe_iSup_of_directed chain.directed_carriers
    set κ := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
    have h1 : Cardinal.mk ↥S ≤ Cardinal.mk ι' *
        ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) := by
      have := Cardinal.mk_iUnion_le (fun α => ((chain.ring α).carrier : Set T))
      rwa [← hS_eq] at this
    have h2 : ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) ≤ κ :=
      ciSup_le fun α => h_card α
    have h3 : Cardinal.mk ι' * κ ≤ κ := by
      calc Cardinal.mk ι' * κ ≤ κ * κ :=
            mul_le_mul_left h_ι_card κ
        _ ≤ max κ κ := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
        _ = κ := max_self κ
    calc Cardinal.mk ↥S
        ≤ Cardinal.mk ι' *
          ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) := h1
      _ ≤ Cardinal.mk ι' * κ := mul_le_mul_right h2 _
      _ ≤ κ := h3
  · ext ⟨a, ha⟩
    simp only [Ideal.mem_comap, Subring.coe_subtype]
    constructor
    · intro hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu_T
      obtain ⟨α, hα⟩ := hS_union ⟨a, ha⟩
      have hmem_Rα : (⟨a, hα⟩ : (chain.ring α).carrier) ∉
          IsLocalRing.maximalIdeal (chain.ring α).carrier := by
        intro hmem
        have : (⟨a, hα⟩ : (chain.ring α).carrier) ∈
            (IsLocalRing.maximalIdeal T).comap (chain.ring α).carrier.subtype := by
          rw [← (chain.ring α).maximal_ideal_eq]
          exact hmem
        simp only [Ideal.mem_comap, Subring.coe_subtype] at this
        exact (IsLocalRing.mem_maximalIdeal _).mp this hu_T
      have hu_Rα : IsUnit (⟨a, hα⟩ : (chain.ring α).carrier) := by
        by_contra h
        exact hmem_Rα ((IsLocalRing.mem_maximalIdeal _).mpr h)
      exact (IsLocalRing.mem_maximalIdeal _).mp hx
        (hu_Rα.map (Subring.inclusion (hS_le α)))
    · intro hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu_S
      exact (IsLocalRing.mem_maximalIdeal _).mp hx (hu_S.map S.subtype)
  · -- height_bound: for t ≠ 0, P ∈ Ass(T/tT), ht(P ∩ S) ≤ 1
    -- If q ≠ ⊥ is prime, q < P∩S, find γ with q∩Rγ ⊊ P∩Rγ,
    -- contradicting ht(P∩Rγ) ≤ 1 in Rγ.
    intro t ht P hP
    have hP_prime : P.IsPrime := hP.isPrime
    haveI hPS : (Ideal.comap S.subtype P).IsPrime :=
      hP_prime.comap _
    change (Ideal.comap S.subtype P).height ≤ ↑(1 : ℕ)
    rw [Ideal.height_le_iff]
    intro q hq_prime hq_lt
    suffices hq_bot : q = ⊥ by
      rw [hq_bot, Ideal.height_bot]
      norm_cast
    by_contra hq_ne
    have ⟨s, hs_q, hs_ne⟩ : ∃ s : ↥S, s ∈ q ∧ s ≠ 0 := by
      by_contra h
      push Not at h
      exact hq_ne ((Submodule.eq_bot_iff q).mpr fun x hx => h x hx)
    have ⟨x, hx_PS, hx_nq⟩ := Set.exists_of_ssubset hq_lt
    obtain ⟨αs, hαs⟩ := hS_union s
    obtain ⟨αx, hαx⟩ := hS_union x
    set γ := max αs αx
    set inclγ := Subring.inclusion (hS_le γ)
    haveI : (Ideal.comap inclγ q).IsPrime :=
      hq_prime.comap _
    set s' : (chain.ring γ).carrier :=
      ⟨(s : T), chain.mono (le_max_left ..) hαs⟩
    have hs'_q : s' ∈ Ideal.comap inclγ q := by
      change inclγ s' ∈ q
      have : inclγ s' = s := Subtype.ext rfl
      rw [this]
      exact hs_q
    have hs'_ne : s' ≠ 0 := by
      intro h
      apply hs_ne
      exact Subtype.ext (congrArg
        (fun (x : (chain.ring γ).carrier) => (x : T)) h)
    have hq'_ne : Ideal.comap inclγ q ≠ ⊥ := by
      intro h
      rw [h] at hs'_q
      exact hs'_ne (by simpa using hs'_q)
    -- x ∈ P ∩ Rγ but x ∉ q ∩ Rγ → strict containment
    set x' : (chain.ring γ).carrier :=
      ⟨(x : T), chain.mono (le_max_right ..) hαx⟩
    have hx'_P : x' ∈
        Ideal.comap (chain.ring γ).carrier.subtype P :=
      (hx_PS : (x : T) ∈ P)
    have hx'_nq : x' ∉ Ideal.comap inclγ q := by
      intro h
      have h' : inclγ x' ∈ q := h
      have : inclγ x' = x := Subtype.ext rfl
      rw [this] at h'
      exact hx_nq h'
    have hq'_lt :
        Ideal.comap inclγ q <
          Ideal.comap (chain.ring γ).carrier.subtype P := by
      refine lt_of_le_of_ne ?_ ?_
      · intro r hr
        change (r : T) ∈ P
        have : inclγ r ∈ q := hr
        have := hq_lt.le this
        exact (this : (inclγ r : T) ∈ P)
      · exact fun h => hx'_nq (h ▸ hx'_P)
    -- ht(P ∩ Rγ) ≤ 1 by NSubring height bound
    have hht := (chain.ring γ).height_bound t ht P hP
    haveI :
        (Ideal.comap (chain.ring γ).carrier.subtype P).IsPrime :=
      hP_prime.comap _
    have hq'_ht :=
      (Ideal.height_le_iff (n := 1)).mp hht _ inferInstance hq'_lt
    -- height < 1 for nonzero prime in domain → contradiction
    haveI : IsDomain (chain.ring γ).carrier := inferInstance
    have h0 : (Ideal.comap inclγ q).height ≤ ↑(0 : ℕ) := by
      have hne_top := ne_top_of_lt hq'_ht
      lift (Ideal.comap inclγ q).height to ℕ
        using hne_top with n hn
      simp only [Nat.cast_lt] at hq'_ht
      simp only [Nat.cast_le]
      omega
    exact absurd
      ((Ideal.height_le_iff (n := 0)).mp h0 ⊥
        Ideal.isPrime_bot (bot_lt_iff_ne_bot.mpr hq'_ne))
      not_lt_bot

end
