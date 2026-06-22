/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Adjoin.FromPrime
import LeanPool.AndersonConjecture.Jensen.Avoidance
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Adjoining Elements to N-Subrings

Three adjunction lemmas for the Jensen--Heitmann construction:
transcendental adjunction preserving N-subring axioms (Loepp),
adjunction from a prime ideal (Jensen), and the surjectivity
step ensuring R → T/M² stays surjective (Heitmann Lemma 5).
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Surjectivity Step (Heitmann Lemma 5)

Given N-subring R and u ∈ T, find an A-extension S containing
some c with u - c ∈ M².
-/

/-- Heitmann Lemma 5: Given an N-subring R and u ∈ T,
there exists an A-extension S of R with some c ∈ S satisfying u - c ∈ M².

Proof: Choose t ∈ M² via avoidance so that u + t is transcendental
over R modulo relevant primes. Set S = R[u + t] ∩ M. Then c = u + t. -/
private def adjoin_surjectivity_proof
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (u : T)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥) : PLift (
    ∃ S : NSubring T,
      IsAExtension R S ∧
      ∃ (c : S.carrier), (u - (c : T)) ∈ IsLocalRing.maximalIdeal T ^ 2 ) := ⟨by
  have hfind : ∃ (t : T), t ∈ IsLocalRing.maximalIdeal T ^ 2 ∧
      Transcendental R.carrier (u + t) ∧
      (∀ (P : Ideal T), P.IsPrime → P.height ≤ 1 →
        P.comap R.carrier.subtype ≠ ⊥ →
        ∀ (f : Polynomial R.carrier),
          (aeval (u + t) f : T) ∈ (P : Set T) →
          ∀ i, f.coeff i ∈ P.comap R.carrier.subtype) := by
    let C : Set (Ideal T) := ⋃ (r : R.carrier) (_ : (r : T) ≠ 0),
      associatedPrimes T (T ⧸ Ideal.span {(r : T)})
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
    have hM2_not_le : ∀ P ∈ C, ¬(IsLocalRing.maximalIdeal T ^ 2 ≤ P) := by
      intro P hP hle
      have hP_prime := hC_prime P hP
      have hM_le_P : IsLocalRing.maximalIdeal T ≤ P := by
        intro x hx
        have hx2 : x * x ∈ IsLocalRing.maximalIdeal T ^ 2 := by
          rw [sq]
          exact Ideal.mul_mem_mul hx hx
        exact (hP_prime.mem_or_mem (hle hx2)).elim id id
      exact hC_ne_max P hP (le_antisymm (IsLocalRing.le_maximalIdeal hP_prime.ne_top) hM_le_P)
    have hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥ := hM_ne_bot
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
      · exact hM_ne_bot ((mem_singleton_iff.mp hP) ▸ hPM.symm)
    have hM2_not_le' : ∀ P ∈ C', ¬(IsLocalRing.maximalIdeal T ^ 2 ≤ P) := by
      intro P hP hle
      rcases hP with hP | hP
      · exact hM2_not_le P hP hle
      · rw [mem_singleton_iff.mp hP] at hle
        apply hM_ne_bot
        rw [eq_bot_iff]
        intro x hx
        have hx2 : x * x ∈ IsLocalRing.maximalIdeal T ^ 2 := by
          rw [sq]
          exact Ideal.mul_mem_mul hx hx
        exact (mul_self_eq_zero.mp (Ideal.mem_bot.mp (hle hx2))) ▸ Ideal.zero_mem _
    let φ : (P : Ideal T) → R.carrier →+* T ⧸ P :=
      fun P => (Ideal.Quotient.mk P).comp R.carrier.subtype
    let liftQ : (P : Ideal T) → T ⧸ P → T :=
      fun P α => (Ideal.Quotient.mk_surjective α).choose
    have hliftQ : ∀ (P : Ideal T) (α : T ⧸ P),
        Ideal.Quotient.mk P (liftQ P α) = α :=
      fun P α => (Ideal.Quotient.mk_surjective α).choose_spec
    let AlgLocus : Set T := {y : T | ∃ (f : Polynomial R.carrier),
      f ≠ 0 ∧ (Polynomial.aeval y f : T) = 0}
    let D'_base : Set T := {-u} ∪ ((fun y => y - u) '' AlgLocus)
    let D_mod_shifted : Set T := ⋃ P ∈ C,
      ⋃ (f : (R.carrier)[X]) (_ : f.map (φ P) ≠ 0),
        (fun α => liftQ P α - u) '' { α : T ⧸ P | (f.map (φ P)).IsRoot α }
    let D' : Set T := D'_base ∪ D_mod_shifted
    have hC'D'_bound : Cardinal.mk (C' × D') <
        Cardinal.mk (IsLocalRing.ResidueField T) ∨
        (C'.Countable ∧ D'.Countable) := by
      by_cases hR_le : Cardinal.mk R.carrier ≤ Cardinal.aleph0
      · haveI : Countable R.carrier := Cardinal.mk_le_aleph0_iff.mp hR_le
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
        have hD'_countable : D'.Countable := by
          apply Set.Countable.union
          · apply Set.Countable.union (Set.countable_singleton _)
            apply Set.Countable.image
            apply Set.Countable.mono
              (show AlgLocus ⊆
                ⋃ (f : Polynomial R.carrier), f.rootSet T from
                fun _ ⟨f, hf, hy⟩ =>
                  mem_iUnion.mpr
                    ⟨f, Polynomial.mem_rootSet.mpr ⟨hf, hy⟩⟩)
            apply Set.countable_iUnion
            intro f
            exact (Polynomial.rootSet_finite f T).countable
          · apply Set.Countable.biUnion hC_countable
            intro P hPC
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
            exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hfne).mpr hα)
        right
        exact ⟨Set.Countable.union hC_countable (Set.countable_singleton _), hD'_countable⟩
      · left
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
        have hD'_base_le : Cardinal.mk D'_base ≤ Cardinal.mk R.carrier := by
          calc Cardinal.mk D'_base
              ≤ Cardinal.mk ↑({-u} : Set T) +
                  Cardinal.mk ↑((fun y => y - u) '' AlgLocus) :=
                  Cardinal.mk_union_le _ _
            _ ≤ Cardinal.mk R.carrier + Cardinal.mk R.carrier := by
                  gcongr
                  · exact (Cardinal.mk_le_one_iff_set_subsingleton.mpr
                      Set.subsingleton_singleton).trans (one_le_aleph0.trans hR_inf)
                  · calc Cardinal.mk ↑((fun y => y - u) '' AlgLocus)
                        ≤ Cardinal.mk AlgLocus := Cardinal.mk_image_le
                      _ ≤ Cardinal.mk ↑(⋃ (f : Polynomial R.carrier), f.rootSet T) :=
                          Cardinal.mk_le_mk_of_subset (fun _ ⟨f, hf, hy⟩ =>
                            mem_iUnion.mpr ⟨f, Polynomial.mem_rootSet.mpr ⟨hf, hy⟩⟩)
                      _ ≤ Cardinal.mk (Polynomial R.carrier) *
                            ⨆ (f : Polynomial R.carrier), Cardinal.mk ↑(f.rootSet T) :=
                          Cardinal.mk_iUnion_le _
                      _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
                          gcongr
                          · exact Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf)
                          · apply ciSup_le'
                            intro f
                            exact Cardinal.mk_le_aleph0_iff.mpr
                              (Polynomial.rootSet_finite f T).countable.to_subtype
                      _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
            _ = Cardinal.mk R.carrier := Cardinal.add_eq_left hR_inf le_rfl
        have hD_mod_shifted_le : Cardinal.mk D_mod_shifted ≤ Cardinal.mk R.carrier := by
          have h_biUnion : Cardinal.mk ↑(⋃ P ∈ C, ⋃ (f : Polynomial R.carrier),
              ⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                (fun α => liftQ P α - u) '' {α | (Polynomial.map (φ P) f).IsRoot α}) ≤
              Cardinal.mk R.carrier := by
            apply (Cardinal.mk_biUnion_le _ _).trans
            have h_inner : ∀ (x : ↑C), Cardinal.mk ↑(⋃ (f : Polynomial R.carrier),
                ⋃ (_ : Polynomial.map (φ x.1) f ≠ 0),
                  (fun α => liftQ x.1 α - u) '' {α | (Polynomial.map (φ x.1) f).IsRoot α}) ≤
                Cardinal.mk R.carrier := by
              intro ⟨P, hP⟩
              calc Cardinal.mk ↑(⋃ (f : Polynomial R.carrier),
                        ⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                          (fun α => liftQ P α - u) '' {α | (Polynomial.map (φ P) f).IsRoot α})
                    ≤ Cardinal.mk (Polynomial R.carrier) *
                        ⨆ (f : Polynomial R.carrier),
                          Cardinal.mk ↑(⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                            (fun α => liftQ P α - u) ''
                              {α | (Polynomial.map (φ P) f).IsRoot α}) :=
                        Cardinal.mk_iUnion_le _
                  _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
                        gcongr
                        · exact Polynomial.cardinalMk_le_max.trans
                            (max_le le_rfl hR_inf)
                        · apply ciSup_le'
                          intro f
                          apply Cardinal.mk_le_aleph0_iff.mpr
                          by_cases hfne : Polynomial.map (φ P) f = 0
                          · exact Set.Countable.to_subtype (by simp [hfne])
                          · haveI : P.IsPrime := hC_prime P hP
                            haveI : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
                            apply Set.Countable.to_subtype
                            apply Set.Finite.countable
                            apply Set.Finite.subset
                              (((Polynomial.rootSet_finite
                                (Polynomial.map (φ P) f)
                                (T ⧸ P)).image
                                (liftQ P)).image
                                (fun x => x - u))
                            apply Set.iUnion_subset
                            intro _ x hx
                            obtain ⟨α, hα, rfl⟩ := hx
                            exact ⟨liftQ P α,
                              ⟨α, Polynomial.mem_rootSet.mpr
                                ⟨hfne, hα⟩, rfl⟩, rfl⟩
                  _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
            exact (mul_le_mul' hC_le (ciSup_le' h_inner)).trans (Cardinal.mul_eq_self hR_inf).le
          exact h_biUnion
        have hD'_le : Cardinal.mk D' ≤ Cardinal.mk R.carrier := by
          calc Cardinal.mk D'
              ≤ Cardinal.mk D'_base + Cardinal.mk D_mod_shifted :=
                  Cardinal.mk_union_le _ _
            _ ≤ Cardinal.mk R.carrier + Cardinal.mk R.carrier :=
                  add_le_add hD'_base_le hD_mod_shifted_le
            _ = Cardinal.mk R.carrier := Cardinal.add_eq_left hR_inf le_rfl
        calc Cardinal.mk (↑C' × ↑D')
            = Cardinal.mk C' * Cardinal.mk D' := (Cardinal.mul_def _ _).symm
          _ ≤ Cardinal.mk R.carrier * Cardinal.mk R.carrier := mul_le_mul' hC'_le hD'_le
          _ = Cardinal.mk R.carrier := Cardinal.mul_eq_self hR_inf
          _ < Cardinal.mk T := hR_card
          _ = Cardinal.mk (IsLocalRing.ResidueField T) := hT_card
    obtain ⟨t, ht_M2, ht_avoid⟩ := avoidance hC'_prime hC'_ne_max hC'D'_bound hM2_not_le'
    have hut_avoid : ∀ (r : R.carrier), (r : T) ≠ 0 →
        ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {(r : T)}),
          (u + t) ∉ (P : Set T) := by
      intro r hr_ne P hP hut_in_P
      have hP_in_C' : P ∈ C' :=
        mem_union_left {⊥} (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr_ne, hP⟩⟩)
      have h_neg_u_in_D : (-u : T) ∈ D' :=
        Set.mem_union_left _ (Set.mem_union_left _ rfl)
      exact ht_avoid P hP_in_C' (-u) h_neg_u_in_D
        ⟨u + t, hut_in_P, -u, rfl, by ring⟩
    have hut_trans : Transcendental R.carrier (u + t) := by
      intro ⟨f, hf_ne, hf_eval⟩
      have hd_in_D' : t ∈ D' := Set.mem_union_left _
        (Set.mem_union_right {-u} ⟨u + t, ⟨f, hf_ne, hf_eval⟩, by ring⟩)
      exact ht_avoid ⊥ (mem_union_right C rfl) t hd_in_D'
        ⟨0, Ideal.zero_mem ⊥, t, rfl, by ring⟩
    have hut_mod_trans : ∀ (P : Ideal T), P.IsPrime → P.height ≤ 1 →
        P.comap R.carrier.subtype ≠ ⊥ →
        ∀ (f : Polynomial R.carrier),
          (aeval (u + t) f : T) ∈ (P : Set T) →
          ∀ i, f.coeff i ∈ P.comap R.carrier.subtype := by
      intro P hP_prime hP_ht hPR_ne f hf_in i
      by_contra h_neg
      have hf_bar_ne : f.map (φ P) ≠ 0 := by
        intro h_eq
        apply h_neg
        have h := congr_fun (congr_arg Polynomial.coeff h_eq) i
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
        exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h)
      have hP_in_C : P ∈ C := by
        obtain ⟨r₀, hr₀_mem, hr₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPR_ne
        have hr₀T_ne : (r₀ : T) ≠ 0 := fun h => hr₀_ne (Subtype.val_injective h)
        have hr₀_in_P : (r₀ : T) ∈ P := Ideal.mem_comap.mp hr₀_mem
        have hP_minimal :
            P ∈ (Ideal.span {(r₀ : T)}).minimalPrimes := by
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
          have h2 := @Ideal.height_add_one_le_of_lt_of_isPrime T _ Q P hQ_prime hP_prime hQ_lt_P
          have h4 : (2 : ℕ∞) ≤ P.height :=
            calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
              _ ≤ (⊥ : Ideal T).height + 1 + 1 := by
                gcongr
                exact zero_le
              _ ≤ Q.height + 1 := by
                  gcongr
                  exact @Ideal.height_add_one_le_of_lt_of_isPrime T _ ⊥ Q
                    Ideal.isPrime_bot hQ_prime h_bot_lt_Q
              _ ≤ P.height := h2
          exact not_lt.mpr h4 (by exact_mod_cast hP_ht.trans_lt (by norm_num))
        have hP_assoc : P ∈ associatedPrimes T (T ⧸ Ideal.span {(r₀ : T)}) := by
          have hsub := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
            T (T ⧸ Ideal.span {(r₀ : T)})
          rw [Ideal.annihilator_quotient] at hsub
          exact hsub hP_minimal
        exact mem_iUnion.mpr ⟨r₀, mem_iUnion.mpr ⟨hr₀T_ne, hP_assoc⟩⟩
      haveI := hP_prime
      have ht_root : (f.map (φ P)).IsRoot (Ideal.Quotient.mk P (u + t)) := by
        rw [Polynomial.IsRoot, Polynomial.eval_map,
            show φ P = (Ideal.Quotient.mk P).comp R.carrier.subtype from rfl,
            ← Polynomial.hom_eval₂ f R.carrier.subtype (Ideal.Quotient.mk P) (u + t)]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hf_in
      have hlift_shifted_in_D : liftQ P (Ideal.Quotient.mk P (u + t)) - u ∈ D' :=
        Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP_in_C,
          Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf_bar_ne,
            ⟨Ideal.Quotient.mk P (u + t), ht_root, rfl⟩⟩⟩⟩⟩)
      have hlift_in_P : t - (liftQ P (Ideal.Quotient.mk P (u + t)) - u) ∈ P := by
        have hmem : (u + t) - liftQ P (Ideal.Quotient.mk P (u + t)) ∈ P := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hliftQ]
          exact sub_self _
        convert hmem using 1
        ring
      exact absurd ⟨t - (liftQ P (Ideal.Quotient.mk P (u + t)) - u), hlift_in_P,
          liftQ P (Ideal.Quotient.mk P (u + t)) - u, rfl, by ring⟩
        (ht_avoid P (mem_union_left _ hP_in_C) _ hlift_shifted_in_D)
    exact ⟨t, ht_M2, hut_trans, hut_mod_trans⟩
  obtain ⟨t, ht_M2, hut_trans, hut_mod_trans⟩ := hfind
  obtain ⟨S, hext, hut_mem⟩ :=
    adjoin_transcendental_isNSubring R (u + t) hut_trans hAss_ht hut_mod_trans
  refine ⟨S, hext, ⟨⟨u + t, hut_mem⟩, ?_⟩⟩
  change u - (u + t) ∈ IsLocalRing.maximalIdeal T ^ 2
  rw [sub_add_cancel_left]
  exact neg_mem ht_M2
⟩

theorem adjoin_surjectivity
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (u : T)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      ∃ (c : S.carrier), (u - (c : T)) ∈ IsLocalRing.maximalIdeal T ^ 2 := by
  exact
    (adjoin_surjectivity_proof
      R u hM_not_assoc hAss_ht hR_card hT_card hM_ne_bot
    ).down
end
