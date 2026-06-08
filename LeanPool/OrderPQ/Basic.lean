/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/

import Mathlib.GroupTheory.Sylow
import LeanPool.OrderPQ.MulZMod
import LeanPool.OrderPQ.SemidirectProduct

/-!
# LeanPool.OrderPQ.Basic
-/

/-

## OrderPQ

-/

lemma Nat.pow_factorization_dvd {n : ℕ} (hn : n ≠ 0) {p : ℕ} (hp : p.Prime) :
    p ^ n.factorization p ∣ n := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp hn]

lemma Nat.Prime.mem_self_primeFactors {p : ℕ} (hp : p.Prime) : p ∈ p.primeFactors := by
  rw [hp.primeFactors, Finset.mem_singleton]

lemma Nat.Prime.mem_self_primeFactorsList {p : ℕ} (hp : p.Prime) : p ∈ p.primeFactorsList :=
  Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp.mem_self_primeFactors

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
variable {G : Type*} [Group G]

lemma exists_monoidHom_ne_one (h : p ∣ q - 1) :
    ∃ φ : MulZMod p →* MulAut (MulZMod q), φ ≠ 1 := by
  rw [← card_mulAut_mulZMod q] at h
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card p h
  use Subgroup.topEquiv.toMonoidHom
    |>.comp (Subgroup.inclusion (H := Subgroup.zpowers f) le_top)
    |>.comp <| MulEquiv.ofPrimeCardEq nat_card_mulZMod (hf ▸ Nat.card_zpowers f)
  refine ((IsSimpleGroup.of_prime_card nat_card_mulZMod).monoidHom_ne_one_iff_injective _).mpr ?_
  exact Subgroup.topEquiv.injective.comp <|
    (Subgroup.inclusion_injective le_top).comp <|
      (MulEquiv.ofPrimeCardEq nat_card_mulZMod (hf ▸ Nat.card_zpowers f)).injective

lemma monoidHom_eq_one (h : ¬p ∣ q - 1) :
    ∀ φ : MulZMod p →* MulAut (MulZMod q), φ = 1 := by
  revert h
  contrapose
  push Not
  intro ⟨φ, hφ⟩
  convert Subgroup.card_subgroup_dvd_card φ.range using 1
  · have hφinj :=
      ((IsSimpleGroup.of_prime_card nat_card_mulZMod).monoidHom_ne_one_iff_injective φ).mp hφ
    exact nat_card_mulZMod (n := p) ▸ MonoidHom.nat_card_range_of_injective hφinj |>.symm
  · exact nat_card_mulAut_mulZMod q |>.symm

section Lemma2

lemma Nat.card_eq_mul_card_fiber {α β : Type*} (f : α → β) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ b : β, Nat.card {a // f a = b} = n) :
    Nat.card α = Nat.card β * n := by
  let φ (b : β) : {a // f a = b} ≃ Fin n := h b ▸ Nat.equivFinOfCardPos (h b ▸ hn)
  let F : α ≃ β × Fin n := {
    toFun := fun a => (f a, φ (f a) ⟨a, rfl⟩)
    invFun := fun (b, m) => ((φ b).symm m).val
    left_inv := fun a => by simp only [Equiv.symm_apply_apply]
    right_inv := fun (b, m) => by
      rw [Prod.mk.injEq]
      have := ((φ b).invFun m).property
      use this
      have : (φ b) ((φ b).symm m) = m := (φ b).right_inv m
      convert this using 6
  }
  convert Nat.card_congr F using 1
  rw [Nat.card_prod, Nat.card_fin]

open scoped Pointwise in
lemma Subgroup.card_prod_mul_card_meet [Finite G] (H K : Subgroup G) :
    Nat.card H * Nat.card K = Nat.card (H * K : Set G) * Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Nat.card_prod]
  let f : H × K → (H * K : Set G) := fun (h, k) => ⟨h.1 * k.1, Set.mul_mem_mul h.2 k.2⟩
  refine Nat.card_eq_mul_card_fiber f ?_ ?_
  · exact Nat.ne_zero_iff_zero_lt.mpr Nat.card_pos
  · intro ⟨x, hx⟩
    obtain ⟨h, hh, k, hk, hhk⟩ := Set.mem_mul.mp hx
    exact Nat.card_congr {
      toFun := fun a => by
        use h⁻¹ * a.val.1.val
        refine mem_inf.mpr ⟨?_, ?_⟩
        · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) a.val.1.property
        · convert Subgroup.mul_mem _ hk (Subgroup.inv_mem _ a.val.2.property) using 1
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, hhk]
          exact Subtype.mk.injEq .. ▸ a.property
      invFun := fun i => by
        refine ⟨⟨⟨h * i.val, ?_⟩, ⟨i.val⁻¹ * k, ?_⟩⟩, ?_⟩
        · exact Subgroup.mul_mem _ hh (mem_inf.mp i.property).left
        · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (mem_inf.mp i.property).right) hk
        · rw [Subtype.mk.injEq]
          convert hhk using 1
          group
      left_inv := fun a => by
        rw [Subtype.mk.injEq, Prod.mk.injEq, Subtype.mk.injEq, Subtype.mk.injEq,
          mul_inv_cancel_left, mul_inv_rev, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul, hhk]
        exact ⟨rfl, Subtype.mk.injEq .. ▸ a.property.symm⟩
      right_inv := fun i => by simp
    }

open scoped Pointwise in
lemma Subgroup.prod_eq_of_inf_eq_bot_and_card [Finite G]
    {H K : Subgroup G} (h1 : H ⊓ K = ⊥) (h2 : (Nat.card H) * (Nat.card K) = Nat.card G) :
    H * K = (⊤ : Set G) := by
  rw [Subgroup.card_prod_mul_card_meet H K, h1, Subgroup.card_bot, mul_one] at h2
  exact Set.eq_top_of_card_le_of_finite (Nat.le_of_eq h2.symm)

variable (p G) in
lemma Sylow.exists_of_max_dvd_card [Finite G] :
    ∃ P : Sylow p G, Nat.card P = p ^ (Nat.card G).factorization p := by
  obtain ⟨P, hP⟩ := exists_subgroup_card_pow_prime (G := G) p <|
    Nat.pow_factorization_dvd (Nat.card_ne_zero.mpr ⟨One.instNonempty, by infer_instance⟩) hp.elim
  use ofCard P hP
  simp only [coe_ofCard, hP]

lemma Subgroup.meet_eq_bot_of_coprime_card
    {H K : Subgroup G} (h : Nat.Coprime (Nat.card H) (Nat.card K)) :
    H ⊓ K = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ <| Nat.eq_one_of_dvd_coprimes h
    (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right)

private lemma factorization_mul_left {p q : ℕ} (hp : p.Prime) (hpq : p.Coprime q) :
    (Nat.factorization (p * q)) p = 1 := by
  rw [Nat.factorization_eq_of_coprime_left hpq hp.mem_self_primeFactorsList]
  exact hp.factorization_self

lemma nonempty_mulEquiv_semidirectProduct_of_card_eq_prime_mul_prime
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p < q) (h : Nat.card G = p * q) :
    ∃ φ : MulZMod p →* MulAut (MulZMod q), Nonempty (G ≃* MulZMod q ⋊[φ] MulZMod p) := by
  have : Finite G := Finite.of_card_eq_neZero h
  have h_coprime := Nat.coprime_primes hp.elim hq.elim |>.mpr <| ne_of_lt hpq
  obtain ⟨P, hP⟩ := Sylow.exists_of_max_dvd_card p G
  rw [h, factorization_mul_left hp.elim h_coprime, pow_one] at hP
  have zP : P ≃* MulZMod p := MulEquiv.ofPrimeCardEq hP (by simp)
  obtain ⟨Q, hQ⟩ := Sylow.exists_of_max_dvd_card q G
  rw [h, mul_comm, factorization_mul_left hq.elim h_coprime.symm, pow_one] at hQ
  have zQ : Q ≃* MulZMod q := MulEquiv.ofPrimeCardEq hQ (by simp)
  have hQ_normal : Subgroup.Normal (Q : Subgroup G) := by
    rw [← Subgroup.normalizer_eq_top_iff, ← Subgroup.index_eq_one]
    trans Nat.card (Sylow q G)
    · convert Q.card_eq_index_normalizer.symm using 1
    refine (Nat.Prime.eq_one_or_self_of_dvd (hp.elim) (Nat.card (Sylow q G)) ?_).resolve_right ?_
    · convert Sylow.card_dvd_index Q using 1; symm
      rw [← Nat.mul_left_cancel_iff (Nat.zero_lt_of_ne_zero hq.elim.ne_zero), mul_comm]
      convert Subgroup.index_mul_card (Q : Subgroup G) using 2
      · exact hQ.symm
      · exact mul_comm q p ▸ h.symm
    · refine fun h => hp.elim.ne_one ?_
      -- add lemma for `Nat.ModEq`
      rw [← Nat.mod_eq_of_lt hq.elim.one_lt, ← Nat.mod_eq_of_lt hpq, ← Nat.ModEq, ← h]
      exact card_sylow_modEq_one q G
  let φ : P →* MulAut Q := MonoidHom.restrict MulAut.conjNormal P
  use MonoidHom.comp (MulAut.congr zQ) (φ.comp zP.symm)
  refine Nonempty.intro <| MulEquiv.trans ?_ <| SemidirectProduct.congr' zQ zP
  symm at hP hQ h
  have inf_eq_bot := Subgroup.meet_eq_bot_of_coprime_card (hP ▸ hQ ▸ h_coprime.symm)
  refine mulEquivSemidirectProduct hQ_normal inf_eq_bot (Subgroup.coe_eq_univ.mp ?_) rfl
  rw [Subgroup.normal_mul]
  exact Subgroup.prod_eq_of_inf_eq_bot_and_card inf_eq_bot
    (hP ▸ hQ ▸ Nat.mul_comm .. ▸ h)

end Lemma2

lemma nonempty_mulEquiv_mulZMod_prime_semidirectProduct_mulZMod_prime
    {φ1 φ2 : MulZMod p →* MulAut (MulZMod q)} (hφ1 : φ1 ≠ 1) (hφ2 : φ2 ≠ 1) :
    Nonempty (MulZMod q ⋊[φ1] MulZMod p ≃* MulZMod q ⋊[φ2] MulZMod p) := by
  set P := MulZMod p; set Q := MulZMod q; set A := MulAut Q
  have hP_card : Nat.card P = p := nat_card_mulZMod
  have hR {φ : P →* A} (hφ : φ ≠ 1) : Nat.card φ.range = p := by
    convert hP_card using 1
    refine Nat.card_eq_of_bijective _ (MonoidHom.ofInjective ?_).symm.bijective
    exact ((IsSimpleGroup.of_prime_card hP_card).monoidHom_ne_one_iff_injective _).mp hφ
  have hA : IsCyclic A := mulAut_MulZMod_isCyclic q
  let B := @Subgroup.torsionBy' A (IsCyclic.commGroup) p
  have hB_card : Nat.card B = p :=
    IsCyclic.card_torsionBy' ((hR hφ2).symm ▸ Subgroup.card_subgroup_dvd_card φ2.range)
  have hB (B' : Subgroup A) (h : Nat.card B' = p) : B' = B :=
    IsCyclic.subgroup_eq_of_card_eq B' B (hB_card ▸ h)
  obtain ⟨b, hb_generator⟩ := (Subgroup.isCyclic B).exists_generator
  have hb : (b : A) ≠ (1 : A) := by
    intro hyp
    absurd hp.elim.ne_one
    have : Fintype B := Fintype.ofFinite B
    rw [← orderOf_one (G := A), ← hyp, ← hB_card]
    simp [orderOf_eq_card_of_forall_mem_zpowers hb_generator]
  have hg_exists {φ : P →* A} (hφ : φ ≠ 1) : ∃ g : P, φ g = b := by
    have hb_range : (b : A) ∈ φ.range := by
      rw [hB φ.range (hR hφ)]
      exact b.property
    exact MonoidHom.mem_range.mp hb_range
  have hg_gen {φ : P →* A} {g : P} (hg : φ g = b) := Subgroup.zpowers_eq_top_of_ne_one
    nat_card_mulZMod (ne_one_of_map (hg.symm ▸ hb)) ▸ Subgroup.mem_top
  obtain ⟨g1, hg1⟩ := hg_exists hφ1
  obtain ⟨g2, hg2⟩ := hg_exists hφ2
  obtain ⟨f, hf⟩ := IsCyclic.exists_mulEquiv_of_generators_and_card_eq (hg_gen hg1) (hg_gen hg2) rfl
  have hcompat (x : P) : φ1 x = φ2 (f x) := by
    rw [← (Subgroup.mem_zpowers_iff.mp (hg_gen hg1 x)).choose_spec]
    rw [map_zpow, map_zpow, map_zpow]
    rw [hf, hg1, hg2]
  refine Nonempty.intro (SemidirectProduct.congr (MulEquiv.refl Q) f (fun x => ?_))
  ext y
  change (φ1 x) y = (φ2 (f x)) y
  exact congrArg (fun e : MulAut Q => e y) (hcompat x)

lemma exists_monoidHom_ne_one_and_nonempty_mulEquiv_semidirectProduct
    (hpq : p < q) (h : Nat.card G = p * q) (h' : ¬IsCyclic G) :
    ∃ φ : MulZMod p →* MulAut (MulZMod q), φ ≠ 1 ∧ Nonempty (G ≃* MulZMod q ⋊[φ] MulZMod p) := by
  obtain ⟨φ1, hne⟩ := nonempty_mulEquiv_semidirectProduct_of_card_eq_prime_mul_prime (G := G) hpq h
  refine hne.elim fun ψ => ⟨φ1, ⟨?_, Nonempty.intro ψ⟩⟩
  contrapose h'
  refine @isCyclic_of_surjective _ _ _ _ _ ?_ _ _ ψ.symm ψ.symm.surjective
  have f := h' ▸ SemidirectProduct.mulEquivProd
  refine @isCyclic_of_surjective _ _ _ _ _ ?_ _ _ f.symm f.symm.surjective
  refine IsCyclic.isCyclic_prod_iff_coprime_card.mp ?_
  simp [Nat.coprime_primes hq.elim hp.elim, ne_of_gt hpq]

theorem exists_group_card_eq_prime_mul_prime_and_not_isCyclic (h : p ∣ q - 1) :
    ∃ (G : Type) (_ : Group G), Nat.card G = p * q ∧ ¬IsCyclic G := by
  obtain ⟨φ, hφ⟩ := exists_monoidHom_ne_one h
  let G := MulZMod q ⋊[φ] MulZMod p
  have h1 : Nat.card G = p * q := by
    rw [mul_comm, SemidirectProduct.card]
    simp
  have h2 : ¬IsCyclic G := fun h => by
    absurd hφ
    ext x y
    change (φ x) y = y
    apply SemidirectProduct.inl_injective (φ := φ)
    calc
      SemidirectProduct.inl ((φ x) y) =
          SemidirectProduct.inr x * SemidirectProduct.inl y * SemidirectProduct.inr x⁻¹ :=
        SemidirectProduct.inl_aut (φ := φ) x y
      _ = SemidirectProduct.inl y := by simp [IsCyclic.commGroup.mul_comm]
  exact ⟨G, _, h1, h2⟩

theorem isCyclic_of_card_eq_prime_mul_prime
    (hpq : p < q) (h : ¬p ∣ q - 1) (hG : Nat.card G = p * q) :
    IsCyclic G := by
  apply monoidHom_eq_one at h
  contrapose h
  push Not
  obtain ⟨φ, hφ, _⟩ := exists_monoidHom_ne_one_and_nonempty_mulEquiv_semidirectProduct hpq hG h
  exact ⟨φ, hφ⟩

theorem isCyclic_of_card_eq_prime_mul_prime' (h1 : Nat.card G = p * q)
    (h2 : p ≠ q ∧ ¬p ∣ q - 1 ∧ ¬q ∣ p - 1) :
    IsCyclic G := by
  obtain (hpq | hqp) : p < q ∨ q < p := Nat.lt_or_gt.mp h2.1
  · exact isCyclic_of_card_eq_prime_mul_prime hpq h2.2.1 h1
  · exact isCyclic_of_card_eq_prime_mul_prime hqp h2.2.2 (mul_comm p q ▸ h1)

theorem nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic' (hpq : p < q)
    {G1 : Type*} [Group G1] (h1 : Nat.card G1 = p * q) (h1' : ¬IsCyclic G1)
    {G2 : Type*} [Group G2] (h2 : Nat.card G2 = p * q) (h2' : ¬IsCyclic G2) :
    Nonempty (G1 ≃* G2) := by
  have ⟨_, hφ1, hn1⟩ := exists_monoidHom_ne_one_and_nonempty_mulEquiv_semidirectProduct hpq h1 h1'
  have ⟨_, hφ2, hn2⟩ := exists_monoidHom_ne_one_and_nonempty_mulEquiv_semidirectProduct hpq h2 h2'
  refine hn1.elim fun ψ1 => ?_
  refine hn2.elim fun ψ2 => ?_
  exact (nonempty_mulEquiv_mulZMod_prime_semidirectProduct_mulZMod_prime hφ1 hφ2).elim
    fun ψ => ⟨MulEquiv.trans ψ1 (MulEquiv.trans ψ ψ2.symm)⟩

/-

## OrderPSquared

-/

lemma nonempty_mulEquiv_prod_of_card_eq_prime_pow_two_of_not_isCyclic
    {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] (h : Nat.card G = p ^ 2) (h' : ¬IsCyclic G) :
    Nonempty (G ≃* (MulZMod p) × (MulZMod p)) := by
  have : Finite G := Finite.of_card_eq_neZero h
  have : Nontrivial G := by
    rw [← Finite.one_lt_card_iff_nontrivial, h, Nat.one_lt_pow_iff (by norm_num1)]
    exact hp.elim.one_lt
  have ho : ∀ x ≠ (1 : G), orderOf x = p := by
    rwa [← Monoid.exponent_eq_prime_iff hp.elim, ← not_isCyclic_iff_exponent_eq_prime hp.elim h]
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  set P : Subgroup G := Subgroup.zpowers x
  have hP : Nat.card P = p := Nat.card_zpowers x ▸ ho x hx
  have h_exists_not_mem : ∃ y, y ∉ P := by
    by_contra hP'
    push Not at hP'
    rw [← Subgroup.eq_top_iff', ← Subgroup.card_eq_iff_eq_top, eq_comm, h, hP, pow_two,
      Nat.mul_eq_left hp.elim.ne_zero] at hP'
    exact (Nat.Prime.ne_one hp.elim) hP'
  obtain ⟨y, hyP⟩ := h_exists_not_mem
  set Q : Subgroup G := Subgroup.zpowers y
  have hy : y ≠ 1 := fun hy => hyP <| hy ▸ Subgroup.one_mem _
  have hQ : Nat.card Q = p := Nat.card_zpowers y ▸ ho y hy
  let fPQ : P × Q ≃* MulZMod p × MulZMod p := MulEquiv.prodCongr
    (MulEquiv.ofPrimeCardEq hP nat_card_mulZMod) (MulEquiv.ofPrimeCardEq hQ nat_card_mulZMod)
  refine ⟨MulEquiv.trans ?_ fPQ⟩
  let _ := IsPGroup.commGroupOfCardEqPrimeSq h
  have inf_eq_bot : P ⊓ Q = (⊥ : Subgroup G) := by
    rw [Subgroup.eq_bot_iff_card]
    have : Nat.card (P ⊓ Q : Subgroup G) ∣ p := hP ▸ Subgroup.card_dvd_of_le inf_le_left
    refine Nat.Prime.eq_one_or_self_of_dvd hp.elim _ this |>.resolve_right (fun hinf => ?_)
    have hPQ : P ⊓ Q = Q := Subgroup.eq_of_le_of_card_ge inf_le_right (Nat.le_of_eq (hinf ▸ hQ))
    exact hyP <| (inf_eq_right.mp hPQ) <| Subgroup.mem_zpowers y
  have sup_eq_top : P ⊔ Q = (⊤ : Subgroup G) := by
    rw [← Subgroup.coe_eq_univ, Subgroup.normal_mul]
    refine Subgroup.prod_eq_of_inf_eq_bot_and_card inf_eq_bot ?_
    rw [hP, hQ, h, pow_two]
  exact mulEquivProd P.normal_of_isMulCommutative Q.normal_of_isMulCommutative inf_eq_bot sup_eq_top
