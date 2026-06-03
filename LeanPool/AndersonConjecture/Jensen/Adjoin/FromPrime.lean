/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Adjoin.Transcendental
import LeanPool.AndersonConjecture.Jensen.Avoidance
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Adjoining from a Prime Ideal

Given an N-subring R and a nonzero prime q of the ambient complete
local domain, construct an N-subring S containing R such that
q meets S nontrivially.

Jensen, "Completions of UFDs with semi-local formal fibers",
2006, Lemma 2.1 (case P = (0)).
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Jensen's Lemma 2.1 for P = (0)

Given N-subring R and nonzero prime q of T, find an N-subring S ⊇ R
with q ∩ S ≠ (0). This uses avoidance to find a transcendental element in q.
-/

/-- Jensen Lemma 2.1 (P = (0) case):
Given an N-subring R and a nonzero prime ideal q of T,
there exists an N-subring S ⊇ R with q ∩ S ≠ {0},
|S| = sup(ℵ₀, |R|), and primes of R remain prime in S.

Proof idea: Use avoidance (Lemma 3) to find t ∈ q that is transcendental
over R modulo all relevant primes. Then S = R[t]_{R[t] ∩ M}. -/
private def adjoin_from_prime_proof
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (q : Ideal T) (hq_prime : q.IsPrime) (hq_ne_bot : q ≠ ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) : PLift (
    ∃ S : NSubring T,
      IsAExtension R S ∧
      ∃ (t : S.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0 ) := ⟨by
  -- Case split on q ∩ R
  by_cases hqR : q.comap R.carrier.subtype = ⊥
  swap
  · -- q ∩ R ≠ (0): take S = R
    have hne : ∃ r : R.carrier, r ∈ q.comap R.carrier.subtype ∧ r ≠ 0 := by
      by_contra h
      push Not at h
      exact hqR ((Submodule.eq_bot_iff _).mpr fun x hx => h x hx)
    obtain ⟨r, hr_comap, hr_ne⟩ := hne
    rw [Ideal.mem_comap] at hr_comap
    exact ⟨R, ⟨le_refl _, fun s hs => hs, le_max_right _ _⟩,
      ⟨r, hr_comap, fun h => hr_ne (Subtype.ext h)⟩⟩
  -- q ∩ R = (0): find transcendental element via avoidance
  let C : Set (Ideal T) := ⋃ (r : R.carrier) (_ : (r : T) ≠ 0),
    associatedPrimes T (T ⧸ Ideal.span {(r : T)})
  have hx_trans : ∃ (t : T), t ∈ q ∧ t ≠ 0 ∧
      Transcendental R.carrier t ∧
      (∀ (P : Ideal T), P.IsPrime → P.height ≤ 1 →
        P.comap R.carrier.subtype ≠ ⊥ →
        ∀ (f : Polynomial R.carrier),
          (aeval t f : T) ∈ (P : Set T) →
          ∀ i, f.coeff i ∈ P.comap R.carrier.subtype) := by
    have hC_mem : ∀ P ∈ C, ∃ (r : R.carrier), (r : T) ≠ 0 ∧
        P ∈ associatedPrimes T (T ⧸ Ideal.span {(r : T)}) := by
      intro P hP
      rw [mem_iUnion] at hP
      obtain ⟨r, hP'⟩ := hP
      rw [mem_iUnion] at hP'
      obtain ⟨hr_ne, hP_assoc⟩ := hP'
      exact ⟨r, hr_ne, hP_assoc⟩
    have hC_prime : ∀ P ∈ C, P.IsPrime := by
      intro P hP
      obtain ⟨r, _, hP_assoc⟩ := hC_mem P hP
      exact hP_assoc.isPrime
    have hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T := by
      intro P hP hPM
      obtain ⟨r, hr_ne, hP_assoc⟩ := hC_mem P hP
      subst hPM
      exact hM_not_assoc (r : T) hr_ne hP_assoc
    -- q ⊄ P for P ∈ C: height argument
    have hq_not_le : ∀ P ∈ C, ¬(q ≤ P) := by
      intro P hP hle
      obtain ⟨r, hr_ne, hP_assoc⟩ := hC_mem P hP
      have hP_ht := hAss_ht (r : T) hr_ne P hP_assoc
      haveI : P.IsPrime := hC_prime P hP
      rcases eq_or_lt_of_le hle with rfl | hlt
      · -- q = P: r ∈ q via associated prime, contradicts q ∩ R = ⊥
        have hr_mem_q : (r : T) ∈ q := by
          obtain ⟨_, m, hann⟩ := hP_assoc
          rw [hann]
          apply Ideal.le_radical
          rw [Submodule.mem_colon_singleton]
          change (r : T) • m ∈ (⊥ : Submodule T (T ⧸ Ideal.span {(r : T)}))
          rw [Submodule.mem_bot]
          obtain ⟨m', rfl⟩ := Ideal.Quotient.mk_surjective m
          change (Ideal.Quotient.mk (Ideal.span {(r : T)})) ((r : T) * m') = 0
          exact Ideal.Quotient.eq_zero_iff_mem.mpr
            (Ideal.mul_mem_right m' _ (Ideal.subset_span rfl))
        have hr_comap : r ∈ q.comap R.carrier.subtype := Ideal.mem_comap.mpr hr_mem_q
        rw [hqR] at hr_comap
        have := (Submodule.mem_bot _).mp hr_comap
        exact hr_ne (congrArg Subtype.val this)
      · -- q < P: height chain ⊥ < q < P gives ht(P) ≥ 2, contradiction
        have h_bot_lt_q : (⊥ : Ideal T) < q := bot_lt_iff_ne_bot.mpr hq_ne_bot
        have h1 := @Ideal.height_add_one_le_of_lt_of_isPrime T _ ⊥ q Ideal.isPrime_bot
          hq_prime h_bot_lt_q
        have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        have h4 : (2 : ℕ∞) ≤ P.height :=
          calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
            _ ≤ (⊥ : Ideal T).height + 1 + 1 := by
              gcongr
              exact zero_le
            _ ≤ q.height + 1 := by gcongr
            _ ≤ P.height := h2
        exact not_lt.mpr h4 (by exact_mod_cast hP_ht.trans_lt (by norm_num))
    -- Augment C with ⊥ to ensure t ≠ 0
    let C' : Set (Ideal T) := C ∪ {⊥}
    have hC'_prime : ∀ P ∈ C', P.IsPrime := by
      intro P hP
      rcases hP with hP | hP
      · exact hC_prime P hP
      · rw [mem_singleton_iff.mp hP]
        exact Ideal.isPrime_bot
    have hC'_ne_max : ∀ P ∈ C', P ≠ IsLocalRing.maximalIdeal T := by
      intro P hP hPM
      rcases hP with hP | hP
      · exact hC_ne_max P hP hPM
      · -- ⊥ = M implies T is a field, contradicting q ≠ ⊥
        rw [mem_singleton_iff.mp hP] at hPM
        have hM_bot : IsLocalRing.maximalIdeal T = ⊥ := hPM.symm
        have : q = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro x hx
          by_contra hx_ne
          have : x ∈ IsLocalRing.maximalIdeal T :=
            (IsLocalRing.mem_maximalIdeal _).mpr
              (fun hu => hq_prime.ne_top (q.eq_top_of_isUnit_mem hx hu))
          rw [hM_bot, Ideal.mem_bot] at this
          exact hx_ne this
        exact hq_ne_bot this
    have hq_not_le' : ∀ P ∈ C', ¬(q ≤ P) := by
      intro P hP hle
      rcases hP with hP | hP
      · exact hq_not_le P hP hle
      · rw [mem_singleton_iff.mp hP] at hle
        exact hq_ne_bot (le_bot_iff.mp hle)
    let φ : (P : Ideal T) → R.carrier →+* T ⧸ P :=
      fun P => (Ideal.Quotient.mk P).comp R.carrier.subtype
    let liftQ : (P : Ideal T) → T ⧸ P → T :=
      fun P α => (Ideal.Quotient.mk_surjective α).choose
    have hliftQ : ∀ (P : Ideal T) (α : T ⧸ P),
        Ideal.Quotient.mk P (liftQ P α) = α :=
      fun P α => (Ideal.Quotient.mk_surjective α).choose_spec
    let D_mod : Set T := {0} ∪
      ⋃ (P : Ideal T) (_ : P ∈ C) (f : (R.carrier)[X]) (_ : f.map (φ P) ≠ 0),
        liftQ P '' { α : T ⧸ P | (f.map (φ P)).IsRoot α }
    have h0_in_D : (0 : T) ∈ D_mod := Set.mem_union_left _ rfl
    have hCD'_bound : Cardinal.mk (C' × D_mod) <
        Cardinal.mk (IsLocalRing.ResidueField T) ∨
        (C'.Countable ∧ D_mod.Countable) := by
      by_cases hR_le : Cardinal.mk R.carrier ≤ Cardinal.aleph0
      · -- R countable: use countable avoidance
        haveI : Countable R.carrier := Cardinal.mk_le_aleph0_iff.mp hR_le
        have hC_countable : C.Countable := by
          apply Set.countable_iUnion
          intro r
          apply Set.countable_iUnion
          intro _
          exact (associatedPrimes.finite T _).countable
        haveI : Countable (Polynomial R.carrier) := by
          haveI : Countable (AddMonoidAlgebra R.carrier ℕ) := by
            change Countable (ℕ →₀ R.carrier)
            infer_instance
          exact Countable.of_equiv _ (Polynomial.toFinsuppIso R.carrier).symm.toEquiv
        right
        exact ⟨Set.Countable.union hC_countable (Set.countable_singleton _),
          Set.Countable.union (Set.countable_singleton _)
            (Set.Countable.biUnion hC_countable fun P hPC => by
              apply Set.countable_iUnion
              intro f
              apply Set.countable_iUnion
              intro hfne
              apply Set.Finite.countable
              apply Set.Finite.image
              haveI : P.IsPrime := hC_prime P hPC
              haveI : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
              letI : DecidableEq (T ⧸ P) := Classical.decEq _
              apply Set.Finite.subset (f.map (φ P)).roots.toFinset.finite_toSet
              intro α hα
              exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hfne).mpr hα))⟩
      · -- R uncountable: use cardinality bound
        left
        push Not at hR_le
        have hR_inf : Cardinal.aleph0 ≤ Cardinal.mk R.carrier := le_of_lt hR_le
        have hC_le : Cardinal.mk C ≤ Cardinal.mk R.carrier := by
          calc Cardinal.mk C
              ≤ Cardinal.mk R.carrier *
                  ⨆ (r : R.carrier), Cardinal.mk ↑(⋃ (_ : (r : T) ≠ 0),
                    associatedPrimes T (T ⧸ Ideal.span {(r : T)})) :=
                  Cardinal.mk_iUnion_le _
            _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
                  gcongr
                  apply ciSup_le'
                  intro r
                  apply Cardinal.mk_le_aleph0_iff.mpr
                  by_cases hr : (r : T) = 0
                  · exact Set.Countable.to_subtype (by simp [hr])
                  · exact (Set.Finite.subset (associatedPrimes.finite T _)
                      (Set.iUnion_subset fun _ => le_refl _)).countable.to_subtype
            _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
        have hC'_le : Cardinal.mk C' ≤ Cardinal.mk R.carrier := by
          calc Cardinal.mk C'
              ≤ Cardinal.mk C + Cardinal.mk ↑({⊥} : Set (Ideal T)) :=
                  Cardinal.mk_union_le _ _
            _ ≤ Cardinal.mk R.carrier + Cardinal.mk R.carrier := by
                  gcongr
                  exact (Cardinal.mk_le_one_iff_set_subsingleton.mpr
                    Set.subsingleton_singleton).trans (one_le_aleph0.trans hR_inf)
            _ = Cardinal.mk R.carrier := Cardinal.add_eq_left hR_inf le_rfl
        have hD_le : Cardinal.mk D_mod ≤ Cardinal.mk R.carrier := by
          have h_biUnion : Cardinal.mk ↑(⋃ P ∈ C, ⋃ (f : Polynomial R.carrier),
              ⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                liftQ P '' {α | (Polynomial.map (φ P) f).IsRoot α}) ≤
              Cardinal.mk R.carrier := by
            apply (Cardinal.mk_biUnion_le _ _).trans
            have h_inner : ∀ (x : ↑C), Cardinal.mk ↑(⋃ (f : Polynomial R.carrier),
                ⋃ (_ : Polynomial.map (φ x.1) f ≠ 0),
                  liftQ x.1 '' {α | (Polynomial.map (φ x.1) f).IsRoot α}) ≤
                Cardinal.mk R.carrier := by
              intro ⟨P, hP⟩
              calc Cardinal.mk ↑(⋃ (f : Polynomial R.carrier),
                        ⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                          liftQ P '' {α | (Polynomial.map (φ P) f).IsRoot α})
                    ≤ Cardinal.mk (Polynomial R.carrier) *
                        ⨆ (f : Polynomial R.carrier),
                          Cardinal.mk ↑(⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                            liftQ P '' {α | (Polynomial.map (φ P) f).IsRoot α}) :=
                        Cardinal.mk_iUnion_le _
                  _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
                        gcongr
                        · exact Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf)
                        · apply ciSup_le'
                          intro f
                          apply Cardinal.mk_le_aleph0_iff.mpr
                          by_cases hfne : Polynomial.map (φ P) f = 0
                          · exact Set.Countable.to_subtype (by simp [hfne])
                          · haveI : P.IsPrime := hC_prime P hP
                            haveI : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
                            exact (Set.Finite.subset
                              ((Polynomial.rootSet_finite (Polynomial.map (φ P) f) (T ⧸ P)).image
                                (liftQ P))
                              (Set.iUnion_subset fun _ => Set.image_mono fun α hα =>
                                Polynomial.mem_rootSet.mpr ⟨hfne, hα⟩)).countable.to_subtype
                  _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
            exact (mul_le_mul' hC_le (ciSup_le' h_inner)).trans (Cardinal.mul_eq_self hR_inf).le
          exact (Cardinal.mk_union_le _ _).trans (le_trans (add_le_add
            ((Cardinal.mk_le_one_iff_set_subsingleton.mpr
              Set.subsingleton_singleton).trans (one_le_aleph0.trans hR_inf))
            h_biUnion) (Cardinal.add_eq_left hR_inf le_rfl).le)
        calc Cardinal.mk (↑C' × ↑D_mod)
            = Cardinal.mk C' * Cardinal.mk D_mod := (Cardinal.mul_def _ _).symm
          _ ≤ Cardinal.mk R.carrier * Cardinal.mk R.carrier := mul_le_mul' hC'_le hD_le
          _ = Cardinal.mk R.carrier := Cardinal.mul_eq_self hR_inf
          _ < Cardinal.mk T := hR_card
          _ = Cardinal.mk (IsLocalRing.ResidueField T) := hT_card
    -- Apply avoidance to get t ∈ q avoiding all P + d for P ∈ C', d ∈ D_mod
    obtain ⟨t, ht_q, ht_avoid⟩ := avoidance hC'_prime hC'_ne_max hCD'_bound hq_not_le'
    have ht_ne : t ≠ 0 := by
      intro h
      subst h
      exact ht_avoid ⊥ (mem_union_right C (mem_singleton ⊥)) 0 h0_in_D
        ⟨0, Ideal.zero_mem ⊥, 0, rfl, by simp⟩
    have ht_avoid_assoc : ∀ (r : R.carrier), (r : T) ≠ 0 →
        ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {(r : T)}), t ∉ (P : Set T) := by
      intro r hr_ne P hP ht_in_P
      have hP_in_C' : P ∈ C' := mem_union_left {⊥}
        (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr_ne, hP⟩⟩)
      exact ht_avoid P hP_in_C' 0 h0_in_D
        ⟨t, ht_in_P, 0, rfl, by simp⟩
    -- Transcendence by induction on natDegree: f.coeff 0 ∈ q ∩ R = ⊥, then divide by X
    have ht_trans : Transcendental R.carrier t := by
      rw [Transcendental]
      intro ⟨p, hp_ne, hp_eval⟩
      apply hp_ne
      clear hp_ne
      suffices hinj : ∀ n, ∀ f : (R.carrier)[X],
          f.natDegree ≤ n → aeval t f = 0 → f = 0 from
        hinj p.natDegree p le_rfl hp_eval
      intro n
      induction n with
      | zero =>
        intro f hf_deg hf_eval
        rw [Polynomial.eq_C_of_natDegree_le_zero hf_deg] at hf_eval ⊢
        simp only [aeval_C] at hf_eval
        rw [Polynomial.C_eq_zero]
        exact Subtype.val_injective hf_eval
      | succ n ih =>
        intro f hf_deg hf_eval
        -- f.coeff 0 ∈ q ∩ R = ⊥, then f = X * f.divX, apply IH
        have hc0 : f.coeff 0 = 0 := by
          have hdecomp := Polynomial.X_mul_divX_add f
          have heval_decomp : aeval t f =
              t * aeval t f.divX + algebraMap R.carrier T (f.coeff 0) := by
            conv_lhs => rw [← hdecomp, map_add, map_mul, aeval_X, aeval_C]
          have hc_in_q : algebraMap R.carrier T (f.coeff 0) ∈ q := by
            have heq : algebraMap R.carrier T (f.coeff 0) = -(t * aeval t f.divX) := by
              have h0 := hf_eval
              rw [heval_decomp] at h0
              exact eq_neg_of_add_eq_zero_right h0
            rw [heq]
            exact q.neg_mem (q.mul_mem_right _ ht_q)
          have hc_comap : f.coeff 0 ∈ q.comap R.carrier.subtype :=
            Ideal.mem_comap.mpr hc_in_q
          rw [hqR] at hc_comap
          exact (Submodule.mem_bot _).mp hc_comap
        have hf_eq : f = X * f.divX := by
          have := Polynomial.X_mul_divX_add f
          rw [hc0, map_zero, add_zero] at this
          exact this.symm
        have hdivX_eval : aeval t f.divX = 0 := by
          have : aeval t f = t * aeval t f.divX := by
            conv_lhs => rw [hf_eq]
            rw [map_mul, aeval_X]
          rw [hf_eval] at this
          exact (mul_eq_zero.mp this.symm).resolve_left ht_ne
        have hdivX_deg : f.divX.natDegree ≤ n := by
          have := @Polynomial.natDegree_divX_eq_natDegree_tsub_one _ _ f
          omega
        rw [hf_eq, ih f.divX hdivX_deg hdivX_eval, mul_zero]
    -- Modular transcendence: f(t) ∈ P implies all coefficients in P ∩ R
    have ht_mod_trans : ∀ (P : Ideal T), P.IsPrime → P.height ≤ 1 →
        P.comap R.carrier.subtype ≠ ⊥ →
        ∀ (f : Polynomial R.carrier),
          (aeval t f : T) ∈ (P : Set T) →
          ∀ i, f.coeff i ∈ P.comap R.carrier.subtype := by
      intro P hP_prime hP_ht hPR_ne f hf_in i
      by_contra h_neg
      have hf_bar_ne : f.map (φ P) ≠ 0 := by
        intro h_eq
        apply h_neg
        have h := congr_fun (congr_arg Polynomial.coeff h_eq) i
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
        exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h)
      -- P ∈ C: find nonzero r₀ ∈ P ∩ R, show P is minimal over (r₀)
      have hP_in_C : P ∈ C := by
        obtain ⟨r₀, hr₀_mem, hr₀_ne⟩ : ∃ r₀ : R.carrier,
            r₀ ∈ P.comap R.carrier.subtype ∧ r₀ ≠ 0 := by
          by_contra h
          push Not at h
          exact hPR_ne ((Submodule.eq_bot_iff _).mpr fun x hx => h x hx)
        have hr₀T_ne : (r₀ : T) ≠ 0 := fun h => hr₀_ne (Subtype.val_injective h)
        have hr₀_in_P : (r₀ : T) ∈ P := Ideal.mem_comap.mp hr₀_mem
        -- P minimal over (r₀): ht ≤ 1 prevents strictly smaller primes
        have hP_minimal : P ∈ (Ideal.span {(r₀ : T)}).minimalPrimes := by
          refine ⟨⟨hP_prime,
            Ideal.span_le.mpr
              (Set.singleton_subset_iff.mpr hr₀_in_P)⟩, ?_⟩
          intro Q ⟨hQ_prime, hQ_le_span⟩ hQ_le_P
          by_contra hPQ
          have hQ_ne_P : Q ≠ P := fun h => hPQ (h ▸ le_refl _)
          have hQ_ne_bot : Q ≠ ⊥ := by
            intro h
            rw [h] at hQ_le_span
            exact hr₀T_ne (Ideal.mem_bot.mp
              (hQ_le_span (Ideal.subset_span (Set.mem_singleton _))))
          have hQ_lt_P : Q < P := lt_of_le_of_ne hQ_le_P hQ_ne_P
          have h_bot_lt_Q : (⊥ : Ideal T) < Q := bot_lt_iff_ne_bot.mpr hQ_ne_bot
          have h1 := @Ideal.height_add_one_le_of_lt_of_isPrime T _ ⊥ Q
            Ideal.isPrime_bot hQ_prime h_bot_lt_Q
          have h2 := @Ideal.height_add_one_le_of_lt_of_isPrime T _ Q P
            hQ_prime hP_prime hQ_lt_P
          have h4 : (2 : ℕ∞) ≤ P.height :=
            calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
              _ ≤ (⊥ : Ideal T).height + 1 + 1 := by
                gcongr
                exact zero_le
              _ ≤ Q.height + 1 := by gcongr
              _ ≤ P.height := h2
          exact not_lt.mpr h4 (by exact_mod_cast hP_ht.trans_lt (by norm_num))
        -- Minimal primes of principal ⊆ associated primes of quotient
        have hP_assoc : P ∈ associatedPrimes T (T ⧸ Ideal.span {(r₀ : T)}) := by
          have hsub := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
            T (T ⧸ Ideal.span {(r₀ : T)})
          rw [Ideal.annihilator_quotient] at hsub
          exact hsub hP_minimal
        exact mem_iUnion.mpr ⟨r₀, mem_iUnion.mpr ⟨hr₀T_ne, hP_assoc⟩⟩
      haveI := hP_prime
      have ht_root : (f.map (φ P)).IsRoot (Ideal.Quotient.mk P t) := by
        rw [Polynomial.IsRoot, Polynomial.eval_map]
        rw [show φ P = (Ideal.Quotient.mk P).comp R.carrier.subtype from rfl,
            ← Polynomial.hom_eval₂ f R.carrier.subtype (Ideal.Quotient.mk P) t]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hf_in
      have hlift_in_D : liftQ P (Ideal.Quotient.mk P t) ∈ D_mod :=
        Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP_in_C,
          Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf_bar_ne,
            ⟨Ideal.Quotient.mk P t, ht_root, rfl⟩⟩⟩⟩⟩)
      -- t ≡ liftQ P (mk P t) mod P, contradicting avoidance
      have hlift_in_P : t - liftQ P (Ideal.Quotient.mk P t) ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hliftQ]
        exact sub_self _
      exact absurd ⟨t - liftQ P (Ideal.Quotient.mk P t), hlift_in_P,
          liftQ P (Ideal.Quotient.mk P t), rfl, by ring⟩
        (ht_avoid P (mem_union_left _ hP_in_C) _ hlift_in_D)
    exact ⟨t, ht_q, ht_ne, ht_trans, ht_mod_trans⟩
  -- Apply adjoin_transcendental_isNSubring to get S ⊇ R with t ∈ S
  obtain ⟨t, ht_q, ht_ne, ht_trans, ht_mod_trans⟩ := hx_trans
  obtain ⟨S, hext, ht_mem⟩ := adjoin_transcendental_isNSubring R t ht_trans
    hAss_ht ht_mod_trans
  exact ⟨S, hext, ⟨⟨t, ht_mem⟩, ht_q, ht_ne⟩⟩
⟩

theorem adjoin_from_prime
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (q : Ideal T) (hq_prime : q.IsPrime) (hq_ne_bot : q ≠ ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      ∃ (t : S.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0 := by
  exact
    (adjoin_from_prime_proof
      R q hq_prime hq_ne_bot hM_not_assoc hAss_ht hR_card hT_card
    ).down
end
