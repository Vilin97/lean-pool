/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur F. Ramos, Ruy J. G. B. de Queiroz, Anjolina G. de Oliveira
-/
module

public import LeanPool.NagataFactoriality.NagataFactoriality.Localization.Properties
public import LeanPool.NagataFactoriality.NagataFactoriality.Localization.IsLocalization
public import LeanPool.NagataFactoriality.NagataFactoriality.Basic.UFD


/-!
# Lemmas

Supporting results for Nagata’s factoriality theorem.
-/

@[expose] public section

namespace NagataFactoriality

/-- An element avoids a multiplicative set when it divides none of its members. -/
def Avoids {α : Type*} [CommRing α] (S : Submonoid α) (p : α) : Prop :=
  ∀ s : α, s ∈ S → ¬ p ∣ s

/-- A submonoid is prime-generated if each of its elements is a finite product of prime elements. -/
def PrimeGenerated {α : Type*} [CommRing α] (S : Submonoid α) : Prop :=
  ∀ s : α, s ∈ S → ∃ f : Multiset α, (∀ q ∈ f, q ∈ S ∧ Prime q) ∧ f.prod = s

private theorem submonoidZeroNotMemFact {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) : Fact ((0 : α) ∉ S) :=
  ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩

theorem multiset_prod_ne_zero_of_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) : f.prod ≠ 0 := by
  revert hf
  refine Multiset.induction_on f ?_ ?_
  · intro _
    exact one_ne_zero
  · intro q qs ih hqs
    have hq : Prime q := hqs q (by simp)
    have htail : ∀ r ∈ qs, Prime r := by
      intro r hr
      exact hqs r (by simp [hr])
    simpa using mul_ne_zero hq.ne_zero (ih htail)

theorem zero_notMem_of_primeGenerated {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : PrimeGenerated S) : (0 : α) ∉ S := by
  intro hs
  rcases hS 0 hs with ⟨f, hf, hprod⟩
  exact (multiset_prod_ne_zero_of_prime_factors (fun q hq => (hf q hq).2)) hprod

theorem primeGenerated_powers {α : Type*} [CommRing α] {p : α} (hp : Prime p) :
    PrimeGenerated (Submonoid.powers p) := by
  intro s hs
  rcases hs with ⟨n, rfl⟩
  refine ⟨Multiset.replicate n p, ?_, by simp⟩
  intro q hq
  have hqp : q = p := by
    exact Multiset.eq_of_mem_replicate hq
  subst hqp
  refine ⟨⟨1, by simp⟩, hp⟩

theorem primeGenerated_closure_of_primes {α : Type*} [CommRing α] {s : Set α}
    (hs : ∀ q ∈ s, Prime q) : PrimeGenerated (Submonoid.closure s) := by
  intro x hx
  induction hx using Submonoid.closure_induction (s := s) with
  | mem x hx =>
      refine ⟨{x}, ?_, by simp⟩
      intro q hq
      have hqx : q = x := Multiset.mem_singleton.mp hq
      subst q
      exact ⟨Submonoid.subset_closure hx, hs x hx⟩
  | one =>
      exact ⟨0, by simp⟩
  | mul x y hx hy ihx ihy =>
      rcases ihx with ⟨fx, hfx, hprodx⟩
      rcases ihy with ⟨fy, hfy, hprody⟩
      refine ⟨fx + fy, ?_, by simp [hprodx, hprody, Multiset.prod_add]⟩
      intro q hq
      rcases Multiset.mem_add.mp hq with hq | hq
      · exact hfx q hq
      · exact hfy q hq

theorem primeGenerated_closure_finset_of_primes {α : Type*} [CommRing α] (s : Finset α)
    (hs : ∀ q ∈ s, Prime q) : PrimeGenerated (Submonoid.closure (↑s : Set α)) :=
  primeGenerated_closure_of_primes (s := (↑s : Set α)) (fun q hq => hs q hq)

theorem prime_of_irreducible_of_dvd_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p : α}
    (hp : Irreducible p) (hdiv : p ∣ f.prod) : Prime p := by
  revert hf hdiv
  refine Multiset.induction_on f ?_ ?_
  · intro _ hdiv
    exact False.elim (hp.not_isUnit (isUnit_of_dvd_one (by simpa using hdiv)))
  · intro q qs ih hqs hdiv
    have hq : Prime q := hqs q (by simp)
    have htail : ∀ r ∈ qs, Prime r := by
      intro r hr
      exact hqs r (by simp [hr])
    rcases hdiv with ⟨d, hd⟩
    have hq_dvd : q ∣ p * d := by
      refine ⟨qs.prod, ?_⟩
      simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hd.symm
    rcases hq.2.2 p d hq_dvd with hqp | hqd
    · have hqIrred : Irreducible q := prime_irreducible hq
      have hassoc : Associated q p := associated_of_irreducible_of_dvd hqIrred hp hqp
      exact prime_of_associated hq hassoc
    · rcases hqd with ⟨e, hde⟩
      have hcancel : qs.prod = p * e := by
        apply mul_left_cancel₀ hq.ne_zero
        calc
          q * qs.prod = p * d := by
            simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hd
          _ = p * (q * e) := by rw [hde]
          _ = q * (p * e) := by ac_rfl
      exact ih htail ⟨e, hcancel⟩

theorem prime_of_irreducible_of_dvd_mem_primeGenerated {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : PrimeGenerated S) {p s : α}
    (hp : Irreducible p) (hs : s ∈ S) (hdiv : p ∣ s) : Prime p := by
  rcases hS s hs with ⟨f, hf, hprod⟩
  rw [← hprod] at hdiv
  exact prime_of_irreducible_of_dvd_prime_factors (fun q hq => (hf q hq).2) hp hdiv

theorem dvd_of_mul_eq_prime_factors {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p a c : α} (hp : Irreducible p)
    (hnot : ∀ q ∈ f, ¬ p ∣ q) (hEq : f.prod * a = p * c) : p ∣ a := by
  have hmain :
      ∀ g : Multiset α, (∀ q ∈ g, Prime q) → (∀ q ∈ g, ¬ p ∣ q) →
        ∀ {d : α}, g.prod * a = p * d → p ∣ a := by
    intro g
    refine Multiset.induction_on g ?_ ?_
    · intro hg hnotg d hEqg
      refine ⟨d, ?_⟩
      simpa using hEqg
    · intro q qs ih hqs hnotqs d hEqqs
      have hq : Prime q := hqs q (by simp)
      have htail : ∀ r ∈ qs, Prime r := by
        intro r hr
        exact hqs r (by simp [hr])
      have htailNot : ∀ r ∈ qs, ¬ p ∣ r := by
        intro r hr
        exact hnotqs r (by simp [hr])
      have hqNot : ¬ p ∣ q := hnotqs q (by simp)
      have hq_dvd : q ∣ p * d := by
        refine ⟨qs.prod * a, ?_⟩
        simpa [mul_assoc] using hEqqs.symm
      rcases hq.2.2 p d hq_dvd with hqp | hqc
      · have hqIrred : Irreducible q := prime_irreducible hq
        have hassoc : Associated q p := associated_of_irreducible_of_dvd hqIrred hp hqp
        exact False.elim (hqNot (dvd_of_associated (associated_symm hassoc)))
      · rcases hqc with ⟨e, hd⟩
        have hq0 : q ≠ 0 := hq.ne_zero
        have hEq' : q * (qs.prod * a) = q * (p * e) := by
          calc
            q * (qs.prod * a) = (q ::ₘ qs).prod * a := by simp [mul_assoc]
            _ = p * d := hEqqs
            _ = p * (q * e) := by rw [hd]
            _ = q * (p * e) := by ac_rfl
        have hcancel : qs.prod * a = p * e := mul_left_cancel₀ hq0 hEq'
        exact ih htail htailNot hcancel
  exact hmain f hf hnot hEq

theorem dvd_of_localization_dvd_primeGenerated_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β]
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) {p a : α} (hp : Irreducible p)
    (havoid : Avoids S p) (hdiv : algebraMap α β p ∣ algebraMap α β a) : p ∣ a := by
  let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  rcases (NagataFactoriality.IsLocalization.dvd_map_iff
    (S := S) (β := β) (a := p) (b := a)).1 hdiv with
    ⟨s, hs, hsa⟩
  rcases hsa with ⟨c, hc⟩
  rcases hS s hs with ⟨f, hf, hprod⟩
  have hnot : ∀ q ∈ f, ¬ p ∣ q := by
    intro q hq hpq
    have hq_dvd_prod : q ∣ f.prod := Multiset.dvd_prod hq
    have hp_dvd_s : p ∣ s := by
      rw [← hprod]
      exact dvd_trans hpq hq_dvd_prod
    exact havoid s hs hp_dvd_s
  have hEq : f.prod * a = p * c := by
    simpa [hprod] using hc
  exact dvd_of_mul_eq_prime_factors (fun q hq => (hf q hq).2) hp hnot hEq

theorem dvd_of_localization_dvd_primeGenerated {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : PrimeGenerated S) {p a : α} (hp : Irreducible p)
    (havoid : Avoids S p)
    (hdiv : Localization.of (S := S) p ∣ Localization.of (S := S) a) : p ∣ a := by
  let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  let : IsDomain (Localization S) := by infer_instance
  simpa [Localization.of] using
    (dvd_of_localization_dvd_primeGenerated_isLocalization
      (β := Localization S) (S := S) hS hp havoid hdiv)

theorem multiset_prod_mem_of_factors {α : Type*} [CommMonoid α] {S : Submonoid α} {f : Multiset α}
    (hf : ∀ q ∈ f, q ∈ S) : f.prod ∈ S := by
  revert hf
  refine Multiset.induction_on f ?_ ?_
  · intro _
    simp
  · intro q qs ih hqs
    have hq : q ∈ S := hqs q (by simp)
    have htail : ∀ r ∈ qs, r ∈ S := by
      intro r hr
      exact hqs r (by simp [hr])
    simpa using S.mul_mem hq (ih htail)

theorem split_prime_factors_of_mul_eq {α : Type*} [CommRing α] [IsDomain α]
    {f : Multiset α} (hf : ∀ q ∈ f, Prime q) {p a b : α} (_hp : Irreducible p)
    (hEq : p * f.prod = a * b) :
    ∃ f₁ f₂ : Multiset α, ∃ a' b' : α,
      f₁ + f₂ = f ∧
      a = f₁.prod * a' ∧
      b = f₂.prod * b' ∧
      p = a' * b' := by
  have hmain :
      ∀ (g : Multiset α) (a b : α), (∀ q ∈ g, Prime q) → p * g.prod = a * b →
        ∃ f₁ f₂ : Multiset α, ∃ a' b' : α,
          f₁ + f₂ = g ∧
          a = f₁.prod * a' ∧
          b = f₂.prod * b' ∧
          p = a' * b' := by
    intro g
    refine Multiset.induction_on g ?_ ?_
    · intro a b _ hEq
      refine ⟨0, 0, a, b, rfl, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hEq
    · intro q qs ih a b hqs hEq
      have hq : Prime q := hqs q (by simp)
      have htail : ∀ r ∈ qs, Prime r := by
        intro r hr
        exact hqs r (by simp [hr])
      have hq_dvd_ab : q ∣ a * b := by
        refine ⟨p * qs.prod, ?_⟩
        calc
          a * b = p * (q * qs.prod) := by
            simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq.symm
          _ = q * (p * qs.prod) := by ac_rfl
      rcases hq.2.2 a b hq_dvd_ab with hqa | hqb
      · rcases hqa with ⟨a₁, ha₁⟩
        have hEq' : p * qs.prod = a₁ * b := by
          have haux : q * (p * qs.prod) = q * (a₁ * b) := by
            calc
              q * (p * qs.prod) = p * (q * qs.prod) := by ac_rfl
              _ = a * b := by
                simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq
              _ = (q * a₁) * b := by rw [ha₁]
              _ = q * (a₁ * b) := by ac_rfl
          exact mul_left_cancel₀ hq.ne_zero haux
        rcases ih (a := a₁) (b := b) htail hEq' with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
        refine ⟨q ::ₘ f₁, f₂, a', b', ?_, ?_, hb, hpab⟩
        · simp [hpart]
        · calc
            a = q * a₁ := ha₁
            _ = q * (f₁.prod * a') := by rw [ha]
            _ = (q ::ₘ f₁).prod * a' := by simp [mul_assoc]
      · rcases hqb with ⟨b₁, hb₁⟩
        have hEq' : p * qs.prod = a * b₁ := by
          have haux : q * (p * qs.prod) = q * (a * b₁) := by
            calc
              q * (p * qs.prod) = p * (q * qs.prod) := by ac_rfl
              _ = a * b := by
                simpa [Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using hEq
              _ = a * (q * b₁) := by rw [hb₁]
              _ = q * (a * b₁) := by ac_rfl
          exact mul_left_cancel₀ hq.ne_zero haux
        rcases ih (a := a) (b := b₁) htail hEq' with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
        refine ⟨f₁, q ::ₘ f₂, a', b', ?_, ha, ?_, hpab⟩
        · simp [hpart]
        · calc
            b = q * b₁ := hb₁
            _ = q * (f₂.prod * b') := by rw [hb]
            _ = (q ::ₘ f₂).prod * b' := by simp [mul_assoc]
  exact hmain f a b hf hEq

theorem localization_irreducible_of_irreducible_primeGenerated_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β]
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) : Irreducible (algebraMap α β p) := by
  let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdiv : algebraMap α β p ∣ (1 : β) := by
      rcases isUnit_iff_exists_inv.mp hunit with ⟨x, hx⟩
      exact ⟨x, hx.symm⟩
    have hdiv' : algebraMap α β p ∣ algebraMap α β (1 : α) := by
      simpa using hdiv
    rcases (NagataFactoriality.IsLocalization.dvd_map_iff
      (S := S) (β := β) (a := p) (b := 1)).1 hdiv' with ⟨s, hs, hps⟩
    exact havoid s hs (by simpa using hps)
  · intro x y hxy
    obtain ⟨a, s, hs, rfl⟩ := NagataFactoriality.IsLocalization.surj (S := S) (β := β) x
    obtain ⟨b, t, ht, rfl⟩ := NagataFactoriality.IsLocalization.surj (S := S) (β := β) y
    have hEq :
        p * (s * t) = a * b := by
      have hloc :
          algebraMap α β p =
            _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
        calc
          algebraMap α β p =
              _root_.IsLocalization.mk' β a ⟨s, hs⟩ * _root_.IsLocalization.mk' β b ⟨t, ht⟩ := hxy
          _ = _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
              simpa using (_root_.IsLocalization.mk'_mul
                (M := S) (S := β) a b ⟨s, hs⟩ ⟨t, ht⟩).symm
      have hmk :
          _root_.IsLocalization.mk' β p ⟨1, S.one_mem⟩ =
            _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
        calc
          _root_.IsLocalization.mk' β p ⟨1, S.one_mem⟩ = algebraMap α β p := by
            convert (_root_.IsLocalization.mk'_one (S := β) p) using 1
          _ = _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := hloc
      simpa [mul_one] using
        (NagataFactoriality.IsLocalization.mk'_eq_iff
          (S := S) (β := β) (a := p) (b := a * b)
          (s := 1) (t := s * t) S.one_mem (S.mul_mem hs ht)).1 hmk
    rcases hS (s * t) (S.mul_mem hs ht) with ⟨f, hf, hfprod⟩
    rcases split_prime_factors_of_mul_eq (fun q hq => (hf q hq).2) hp (by simpa [hfprod] using hEq)
        with ⟨f₁, f₂, a', b', hpart, ha, hb, hpab⟩
    rcases hp.isUnit_or_isUnit hpab with haUnit | hbUnit
    · left
      have hf₁mem : ∀ q ∈ f₁, q ∈ S := by
        intro q hq
        exact (hf q (by rw [← hpart]; exact Multiset.mem_add.mpr (Or.inl hq))).1
      have hprodMem : f₁.prod ∈ S := multiset_prod_mem_of_factors hf₁mem
      have hx_eq :
          _root_.IsLocalization.mk' β a ⟨s, hs⟩ =
            algebraMap α β f₁.prod * _root_.IsLocalization.mk' β a' ⟨s, hs⟩ := by
        rw [ha]
        symm
        exact NagataFactoriality.IsLocalization.map_mul_mk' (S := S) (β := β) f₁.prod a' s hs
      rw [hx_eq]
      exact isUnit_mul
        (NagataFactoriality.IsLocalization.isUnit_map_of_mem (S := S) (β := β) hprodMem)
        (NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (S := S) (β := β) haUnit hs)
    · right
      have hf₂mem : ∀ q ∈ f₂, q ∈ S := by
        intro q hq
        exact (hf q (by rw [← hpart]; exact Multiset.mem_add.mpr (Or.inr hq))).1
      have hprodMem : f₂.prod ∈ S := multiset_prod_mem_of_factors hf₂mem
      have hy_eq :
          _root_.IsLocalization.mk' β b ⟨t, ht⟩ =
            algebraMap α β f₂.prod * _root_.IsLocalization.mk' β b' ⟨t, ht⟩ := by
        rw [hb]
        symm
        exact NagataFactoriality.IsLocalization.map_mul_mk' (S := S) (β := β) f₂.prod b' t ht
      rw [hy_eq]
      exact isUnit_mul
        (NagataFactoriality.IsLocalization.isUnit_map_of_mem (S := S) (β := β) hprodMem)
        (NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (S := S) (β := β) hbUnit ht)

theorem localization_irreducible_of_irreducible_primeGenerated {α : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} (hS : PrimeGenerated S) {p : α}
    (hp : Irreducible p) (havoid : Avoids S p) : Irreducible (Localization.of (S := S) p) := by
  let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  let : IsDomain (Localization S) := by infer_instance
  simpa [Localization.of] using
    (localization_irreducible_of_irreducible_primeGenerated_isLocalization
      (β := Localization S) (S := S) hS hp havoid)

theorem prime_of_localization_prime_primeGenerated_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β]
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) (hploc : Prime (algebraMap α β p)) : Prime p := by
  let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  refine ⟨hp.ne_zero, hp.not_isUnit, ?_⟩
  intro a b hdiv
  have hlocdiv : algebraMap α β p ∣ algebraMap α β (a * b) := by
    rcases hdiv with ⟨c, hc⟩
    exact ⟨algebraMap α β c, by simp [map_mul, hc]⟩
  rcases hploc.2.2 (algebraMap α β a) (algebraMap α β b)
      (by simpa [map_mul] using hlocdiv) with hpa | hpb
  · left
    exact dvd_of_localization_dvd_primeGenerated_isLocalization
      (β := β) (S := S) hS hp havoid hpa
  · right
    exact dvd_of_localization_dvd_primeGenerated_isLocalization
      (β := β) (S := S) hS hp havoid hpb

theorem prime_of_localization_prime_primeGenerated {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : PrimeGenerated S) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) (hploc : Prime (Localization.of (S := S) p)) : Prime p := by
  let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  let : IsDomain (Localization S) := by infer_instance
  simpa [Localization.of] using
    (prime_of_localization_prime_primeGenerated_isLocalization
      (β := Localization S) (S := S) hS hp havoid hploc)

theorem nagata_key_lemma_primeGenerated_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β]
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) [UniqueFactorizationMonoid β]
    {p : α} (hp : Irreducible p) : Prime p := by
  let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  by_cases hmem : ∃ s : α, s ∈ S ∧ p ∣ s
  · rcases hmem with ⟨s, hs, hdiv⟩
    exact prime_of_irreducible_of_dvd_mem_primeGenerated hS hp hs hdiv
  · have havoid : Avoids S p := by
      intro s hs hdiv
      exact hmem ⟨s, hs, hdiv⟩
    have hlocIrred : Irreducible (algebraMap α β p) :=
      localization_irreducible_of_irreducible_primeGenerated_isLocalization
        (β := β) (S := S) hS hp havoid
    have hlocPrime : Prime (algebraMap α β p) :=
      (UniqueFactorizationMonoid.irreducible_iff_prime).mp hlocIrred
    exact prime_of_localization_prime_primeGenerated_isLocalization
      (β := β) (S := S) hS hp havoid hlocPrime

theorem nagata_key_lemma_primeGenerated {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : PrimeGenerated S)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance))
    {p : α} (hp : Irreducible p) : Prime p := by
  let : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  let : IsDomain (Localization S) := by infer_instance
  let : UniqueFactorizationMonoid (Localization S) := hUFD
  simpa [Localization.of] using
    (nagata_key_lemma_primeGenerated_isLocalization
      (β := Localization S) (S := S) hS hp)

theorem prime_of_irreducible_of_dvd_mem {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p s : α}
    (hp : Irreducible p) (hs : s ∈ S) (hdiv : p ∣ s) : Prime p := by
  rcases hS s hs with hsPrime | hsUnit
  · have hsIrred : Irreducible s := prime_irreducible hsPrime
    have hassoc : Associated p s := associated_of_irreducible_of_dvd hp hsIrred hdiv
    exact prime_of_associated hsPrime (associated_symm hassoc)
  · exact False.elim (hp.not_isUnit (isUnit_of_dvd_unit hdiv hsUnit))

theorem localization_irreducible_of_irreducible_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β]
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α}
    (hp : Irreducible p) (havoid : Avoids S p) : Irreducible (algebraMap α β p) := by
  let : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  refine ⟨?_, ?_⟩
  · intro hunit
    have hdiv : algebraMap α β p ∣ (1 : β) := by
      rcases isUnit_iff_exists_inv.mp hunit with ⟨x, hx⟩
      exact ⟨x, hx.symm⟩
    have hdiv' : algebraMap α β p ∣ algebraMap α β (1 : α) := by
      simpa using hdiv
    rcases (NagataFactoriality.IsLocalization.dvd_map_iff
      (S := S) (β := β) (a := p) (b := 1)).1 hdiv' with ⟨s, hs, hps⟩
    exact havoid s hs (by simpa using hps)
  · intro x y hxy
    obtain ⟨a, s, hs, rfl⟩ := NagataFactoriality.IsLocalization.surj (S := S) (β := β) x
    obtain ⟨b, t, ht, rfl⟩ := NagataFactoriality.IsLocalization.surj (S := S) (β := β) y
    have hprod : p * (s * t) = a * b := by
      have hEq :
          algebraMap α β p =
            _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
        calc
          algebraMap α β p =
              _root_.IsLocalization.mk' β a ⟨s, hs⟩ * _root_.IsLocalization.mk' β b ⟨t, ht⟩ := hxy
          _ = _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
              simpa using (_root_.IsLocalization.mk'_mul
                (M := S) (S := β) a b ⟨s, hs⟩ ⟨t, ht⟩).symm
      have hEq' :
          _root_.IsLocalization.mk' β p ⟨1, S.one_mem⟩ =
            _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := by
        calc
          _root_.IsLocalization.mk' β p ⟨1, S.one_mem⟩ = algebraMap α β p := by
            convert (_root_.IsLocalization.mk'_one (S := β) p) using 1
          _ = _root_.IsLocalization.mk' β (a * b) ⟨s * t, S.mul_mem hs ht⟩ := hEq
      simpa [mul_one] using
        (NagataFactoriality.IsLocalization.mk'_eq_iff
          (S := S) (β := β) (a := p) (b := a * b)
          (s := 1) (t := s * t) S.one_mem (S.mul_mem hs ht)).1 hEq'
    rcases hS (s * t) (S.mul_mem hs ht) with hstPrime | hstUnit
    · have hstdiv : s * t ∣ a * b := by
        refine ⟨p, ?_⟩
        calc
          a * b = p * (s * t) := hprod.symm
          _ = (s * t) * p := by ac_rfl
      rcases hstPrime.2.2 a b hstdiv with hdiva | hdivb
      · rcases hdiva with ⟨d, hd⟩
        have hst0 : s * t ≠ 0 := hstPrime.ne_zero
        have hp_eq : p = d * b := by
          apply mul_left_cancel₀ hst0
          calc
            (s * t) * p = p * (s * t) := by ac_rfl
            _ = a * b := hprod
            _ = ((s * t) * d) * b := by rw [hd]
            _ = (s * t) * (d * b) := by ac_rfl
        rcases hp.isUnit_or_isUnit hp_eq with hdUnit | hbUnit
        · left
          have hx_eq_mk :
              _root_.IsLocalization.mk' β a ⟨s, hs⟩ =
                _root_.IsLocalization.mk' β (t * d) ⟨1, S.one_mem⟩ := by
            apply (NagataFactoriality.IsLocalization.mk'_eq_iff
              (S := S) (β := β) (a := a) (b := t * d)
              (s := s) (t := 1) hs S.one_mem).2
            calc
              a * 1 = a := by simp
              _ = s * t * d := by rw [hd]
              _ = (t * d) * s := by ac_rfl
          have hx_eq : _root_.IsLocalization.mk' β a ⟨s, hs⟩ = algebraMap α β (t * d) := by
            calc
              _root_.IsLocalization.mk' β a ⟨s, hs⟩ =
                  _root_.IsLocalization.mk' β (t * d) ⟨1, S.one_mem⟩ := hx_eq_mk
              _ = algebraMap α β (t * d) := by
                  convert (_root_.IsLocalization.mk'_one (S := β) (t * d)) using 1
          rw [hx_eq]
          have htUnitLoc : IsUnit (algebraMap α β t) :=
            NagataFactoriality.IsLocalization.isUnit_map_of_mem (S := S) (β := β) ht
          have hdUnitLoc : IsUnit (algebraMap α β d) :=
            NagataFactoriality.IsLocalization.isUnit_map_of_isUnit (β := β) hdUnit
          simpa [map_mul] using isUnit_mul htUnitLoc hdUnitLoc
        · right
          exact NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit
            (S := S) (β := β) hbUnit ht
      · rcases hdivb with ⟨d, hd⟩
        have hst0 : s * t ≠ 0 := hstPrime.ne_zero
        have hp_eq : p = a * d := by
          apply mul_left_cancel₀ hst0
          calc
            (s * t) * p = p * (s * t) := by ac_rfl
            _ = a * b := hprod
            _ = a * ((s * t) * d) := by rw [hd]
            _ = (s * t) * (a * d) := by ac_rfl
        rcases hp.isUnit_or_isUnit hp_eq with haUnit | hdUnit
        · left
          exact NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit
            (S := S) (β := β) haUnit hs
        · right
          have hy_eq_mk :
              _root_.IsLocalization.mk' β b ⟨t, ht⟩ =
                _root_.IsLocalization.mk' β (s * d) ⟨1, S.one_mem⟩ := by
            apply (NagataFactoriality.IsLocalization.mk'_eq_iff
              (S := S) (β := β) (a := b) (b := s * d)
              (s := t) (t := 1) ht S.one_mem).2
            calc
              b * 1 = b := by simp
              _ = s * t * d := by rw [hd]
              _ = (s * d) * t := by ac_rfl
          have hy_eq : _root_.IsLocalization.mk' β b ⟨t, ht⟩ = algebraMap α β (s * d) := by
            calc
              _root_.IsLocalization.mk' β b ⟨t, ht⟩ =
                  _root_.IsLocalization.mk' β (s * d) ⟨1, S.one_mem⟩ := hy_eq_mk
              _ = algebraMap α β (s * d) := by
                  convert (_root_.IsLocalization.mk'_one (S := β) (s * d)) using 1
          rw [hy_eq]
          have hsUnitLoc : IsUnit (algebraMap α β s) :=
            NagataFactoriality.IsLocalization.isUnit_map_of_mem (S := S) (β := β) hs
          have hdUnitLoc : IsUnit (algebraMap α β d) :=
            NagataFactoriality.IsLocalization.isUnit_map_of_isUnit (β := β) hdUnit
          simpa [map_mul] using isUnit_mul hsUnitLoc hdUnitLoc
    · have hassoc : Associated p (a * b) := by
        simpa [hprod] using associated_mul_unit_right p (s * t) hstUnit
      have habIrred : Irreducible (a * b) := hassoc.irreducible hp
      exact (habIrred.isUnit_or_isUnit rfl).elim
        (fun haUnit => Or.inl <|
          NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (S := S) (β := β) haUnit hs)
        (fun hbUnit => Or.inr <|
          NagataFactoriality.IsLocalization.isUnit_mk'_of_isUnit (S := S) (β := β) hbUnit ht)

theorem localization_irreducible_of_irreducible {α : Type*} [CommRing α] [IsDomain α]
    {S : Submonoid α} (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α} (hp : Irreducible p)
    (havoid : Avoids S p) : Irreducible (Localization.of (S := S) p) := by
  let : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  let : IsDomain (Localization S) := by infer_instance
  simpa [Localization.of] using
    (localization_irreducible_of_irreducible_isLocalization
      (β := Localization S) (S := S) hS hp havoid)

theorem dvd_of_localization_dvd_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β]
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p a : α}
    (hp : Irreducible p) (havoid : Avoids S p) (hdiv : algebraMap α β p ∣ algebraMap α β a) :
    p ∣ a := by
  let : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  rcases (NagataFactoriality.IsLocalization.dvd_map_iff
    (S := S) (β := β) (a := p) (b := a)).1 hdiv with ⟨s, hs, hsa⟩
  rcases hsa with ⟨c, hc⟩
  rcases hS s hs with hsPrime | hsUnit
  · have hsdiv : s ∣ p * c := ⟨a, hc.symm⟩
    rcases hsPrime.2.2 p c hsdiv with hsp | hsc
    · have hsIrred : Irreducible s := prime_irreducible hsPrime
      have hassoc : Associated s p := associated_of_irreducible_of_dvd hsIrred hp hsp
      exact False.elim (havoid s hs (dvd_of_associated (associated_symm hassoc)))
    · rcases hsc with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      have hs0 : s ≠ 0 := hsPrime.ne_zero
      have hcancel : s * a = s * (p * d) := by
        calc
          s * a = p * c := hc
          _ = p * (s * d) := by rw [hd]
          _ = s * (p * d) := by ac_rfl
      exact mul_left_cancel₀ hs0 hcancel
  · rcases hsUnit with ⟨u, rfl⟩
    refine ⟨(↑u⁻¹ : α) * c, ?_⟩
    calc
      a = (↑u⁻¹ : α) * ((u : α) * a) := by simp
      _ = (↑u⁻¹ : α) * (p * c) := by rw [hc]
      _ = p * ((↑u⁻¹ : α) * c) := by ac_rfl

theorem dvd_of_localization_dvd {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p a : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hdiv : Localization.of (S := S) p ∣ Localization.of (S := S) a) : p ∣ a := by
  let : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  let : IsDomain (Localization S) := by infer_instance
  simpa [Localization.of] using
    (dvd_of_localization_dvd_isLocalization
      (β := Localization S) (S := S) hS hp havoid hdiv)

theorem prime_of_localization_prime_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β]
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α}
    (hp : Irreducible p) (havoid : Avoids S p) (hploc : Prime (algebraMap α β p)) : Prime p := by
  let : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  refine ⟨hp.ne_zero, hp.not_isUnit, ?_⟩
  intro a b hdiv
  have hlocdiv : algebraMap α β p ∣ algebraMap α β (a * b) := by
    rcases hdiv with ⟨c, hc⟩
    exact ⟨algebraMap α β c, by simp [map_mul, hc]⟩
  rcases hploc.2.2 (algebraMap α β a) (algebraMap α β b)
      (by simpa [map_mul] using hlocdiv) with hpa | hpb
  · left
    exact dvd_of_localization_dvd_isLocalization (β := β) (S := S) hS hp havoid hpa
  · right
    exact dvd_of_localization_dvd_isLocalization (β := β) (S := S) hS hp havoid hpb

theorem prime_of_localization_prime {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p : α} (hp : Irreducible p) (havoid : Avoids S p)
    (hploc : Prime (Localization.of (S := S) p)) : Prime p := by
  let : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  let : IsDomain (Localization S) := by infer_instance
  simpa [Localization.of] using
    (prime_of_localization_prime_isLocalization
      (β := Localization S) (S := S) hS hp havoid hploc)

theorem nagata_key_lemma_isLocalization {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β]
    [_root_.IsLocalization S β] (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    [UniqueFactorizationMonoid β] {p : α} (hp : Irreducible p) : Prime p := by
  let : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  by_cases hmem : ∃ s : α, s ∈ S ∧ p ∣ s
  · rcases hmem with ⟨s, hs, hdiv⟩
    exact prime_of_irreducible_of_dvd_mem hS hp hs hdiv
  · have havoid : Avoids S p := by
      intro s hs hdiv
      exact hmem ⟨s, hs, hdiv⟩
    have hlocIrred : Irreducible (algebraMap α β p) :=
      localization_irreducible_of_irreducible_isLocalization
        (β := β) (S := S) hS hp havoid
    have hlocPrime : Prime (algebraMap α β p) :=
      (UniqueFactorizationMonoid.irreducible_iff_prime).mp hlocIrred
    exact prime_of_localization_prime_isLocalization
      (β := β) (S := S) hS hp havoid hlocPrime

theorem nagata_key_lemma {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          let : Fact ((0 : α) ∉ S) := ⟨Submonoid.zero_notMem_of_prime_or_unit hS⟩
          infer_instance))
    {p : α} (hp : Irreducible p) : Prime p := by
  let : Fact ((0 : α) ∉ S) := submonoidZeroNotMemFact hS
  let : IsDomain (Localization S) := by infer_instance
  let : UniqueFactorizationMonoid (Localization S) := hUFD
  simpa [Localization.of] using
    (nagata_key_lemma_isLocalization
      (β := Localization S) (S := S) hS hp)

end NagataFactoriality
