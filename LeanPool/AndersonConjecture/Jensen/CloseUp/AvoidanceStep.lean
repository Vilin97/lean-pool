/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Adjoin.Adjoin
import LeanPool.AndersonConjecture.Jensen.CloseUp.NoCommonFactor
import LeanPool.AndersonConjecture.Jensen.CloseUp.TwoGen

/-!
# Close-up: avoidance step

The prime-avoidance step in the general close-up construction.
Given generators {a} union s' with c in their T-span, if no
common prime factor of the elements of s' divides both a and c,
one obtains the required A-extension by applying prime avoidance
(Heitmann, Lemma 4).
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

private def close_up_avoidance_step_proof
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    {m : ℕ}
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ m) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    (R : NSubring T) (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (a : R.carrier) (s' : Finset R.carrier) (hs'_card : s'.card ≤ m)
    (c : R.carrier)
    (hc : (c : T) ∈ Ideal.map R.carrier.subtype
      (span (insert (a : R.carrier) (↑s' : Set R.carrier))))
    (h_no_common : ∀ (q : R.carrier), Prime q → ¬(∀ x ∈ s', q ∣ x)) : PLift (
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c : T), hle c.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle)
          (span (insert (a : R.carrier) (↑s' : Set R.carrier))) ) := ⟨by
  haveI : DecidableEq R.carrier := Classical.decEq _
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  rw [Ideal.span_insert, Ideal.map_sup] at hc
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hc
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht_eq⟩ := hu
  by_cases ha_zero : (a : T) = 0
  · have hu_zero : u = 0 := by
      rw [ht_eq]
      change (a : T) * t = 0
      rw [ha_zero, zero_mul]
    have hc_s' : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) := by
      rw [← huv, hu_zero, zero_add]
      exact hv
    obtain ⟨S, hAext, hle, hmem⟩ := ih R hR_card s' hs'_card c hc_s'
    exact ⟨S, hAext, hle, Ideal.map_mono (Ideal.span_mono
      (Set.subset_insert a ↑s')) hmem⟩
  · -- a ≠ 0
    by_cases hI_bot : Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier)) = ⊥
    · have hv_zero : v = 0 := (Submodule.mem_bot T).mp (hI_bot ▸ hv)
      have hc_aT : (c : T) ∈ span {(a : T)} := by
        rw [← huv, hv_zero, add_zero, ht_eq]
        exact Ideal.mem_span_singleton.mpr ⟨t, rfl⟩
      refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, ?_⟩
      have h_id : Subring.inclusion (le_refl R.carrier) =
          RingHom.id R.carrier := RingHom.ext fun x => Subtype.ext rfl
      have hcR := close_up_dvd R a c hc_aT
      change (⟨(c : T), _⟩ : R.carrier) ∈
        Ideal.map (Subring.inclusion (le_refl R.carrier))
          (span (insert (a : R.carrier) (↑s' : Set R.carrier)))
      rw [h_id, Ideal.map_id]
      exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert a _)) hcR
    · -- I_s' ≠ 0
      by_cases hM_bot : IsLocalRing.maximalIdeal T = ⊥
      · -- M = 0: T is a field, a is a unit
        refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, ?_⟩
        have h_id : Subring.inclusion (le_refl R.carrier) =
            RingHom.id R.carrier := RingHom.ext fun x => Subtype.ext rfl
        change (⟨(c : T), _⟩ : R.carrier) ∈
          Ideal.map (Subring.inclusion (le_refl R.carrier))
            (span (insert (a : R.carrier) (↑s' : Set R.carrier)))
        rw [h_id, Ideal.map_id]
        have ha_unit : IsUnit a := by
          by_contra h
          have hmem := (IsLocalRing.mem_maximalIdeal _).mpr h
          rw [R.maximal_ideal_eq, Ideal.mem_comap, hM_bot, Submodule.mem_bot] at hmem
          exact ha_zero hmem
        rw [Ideal.eq_top_of_isUnit_mem _
          (Ideal.subset_span (Set.mem_insert a _)) ha_unit]
        exact Submodule.mem_top
      · -- M ≠ ⊥: main avoidance argument
        have hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥ := hM_bot
        set I_s' := Ideal.map R.carrier.subtype (span (↑s' : Set R.carrier))
        -- C_good: associated primes where I_s' ⊄ P, plus ⊥
        set C_good : Set (Ideal T) :=
          (⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
            {P ∈ associatedPrimes T (T ⧸ span {(r : T)}) | ¬(I_s' ≤ P)}) ∪ {⊥}
        let φ : (P : Ideal T) → R.carrier →+* T ⧸ P :=
          fun P => (Ideal.Quotient.mk P).comp R.carrier.subtype
        let liftQ : (P : Ideal T) → T ⧸ P → T :=
          fun P α => (Ideal.Quotient.mk_surjective α).choose
        have hliftQ : ∀ (P : Ideal T) (α : T ⧸ P),
            Ideal.Quotient.mk P (liftQ P α) = α :=
          fun P α => (Ideal.Quotient.mk_surjective α).choose_spec
        -- D_base: absolute transcendence obstacles
        let D_base : Set T :=
          {-t} ∪ ⋃ (f : Polynomial R.carrier), ⋃ (_ : f ≠ 0),
            (fun x => x - t) '' {x : T | Polynomial.aeval x f = 0}
        -- D_mod: modular transcendence obstacles (lifts of roots of f mod P)
        let D_mod : Set T :=
          ⋃ P ∈ C_good, ⋃ (f : Polynomial R.carrier),
            ⋃ (_ : Polynomial.map (φ P) f ≠ 0),
              (fun α => liftQ P α - t) ''
                {α : T ⧸ P | (Polynomial.map (φ P) f).IsRoot α}
        set D : Set T := D_base ∪ D_mod
        have hC_good_prime : ∀ P ∈ C_good, P.IsPrime := by
          intro P hP
          rcases (Set.mem_union _ _ _).mp hP with h | h
          · rw [Set.mem_iUnion] at h
            obtain ⟨r, h⟩ := h
            rw [Set.mem_iUnion] at h
            obtain ⟨_, hPmem⟩ := h
            exact hPmem.1.isPrime
          · exact Set.mem_singleton_iff.mp h ▸ Ideal.isPrime_bot
        have hC_good_ne_max : ∀ P ∈ C_good, P ≠ IsLocalRing.maximalIdeal T := by
          intro P hP
          rcases (Set.mem_union _ _ _).mp hP with h | h
          · rw [Set.mem_iUnion] at h
            obtain ⟨r, h⟩ := h
            rw [Set.mem_iUnion] at h
            obtain ⟨hr, hPmem⟩ := h
            exact fun heq => hM_not_assoc (r : T) hr (heq ▸ hPmem.1)
          · rw [Set.mem_singleton_iff.mp h]
            exact fun h => hM_ne_bot h.symm
        have hD_root_countable : ∀ (f : Polynomial R.carrier), f ≠ 0 →
            ((fun x => x - t) '' {x : T | Polynomial.aeval x f = 0}).Countable := by
          intro f hf
          apply Set.Countable.image
          have hmap_ne : Polynomial.map R.carrier.subtype f ≠ 0 := by
            rw [Ne, ← Polynomial.map_zero R.carrier.subtype]
            exact (Polynomial.map_injective R.carrier.subtype
              Subtype.val_injective).ne hf
          have h_eq : {x : T | Polynomial.aeval x f = 0} =
              {x : T | (Polynomial.map R.carrier.subtype f).IsRoot x} := by
            ext x
            simp [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval_map,
              show algebraMap R.carrier T = R.carrier.subtype from rfl]
          rw [h_eq]
          exact (Polynomial.finite_setOf_isRoot hmap_ne).countable
        -- Avoidance bound: countable or cardinal bound (Adjoin.lean pattern)
        have hCD_good_bound : Cardinal.mk (↑C_good × ↑D) <
            Cardinal.mk (IsLocalRing.ResidueField T) ∨
            (C_good.Countable ∧ D.Countable) := by
          by_cases hR_le : Cardinal.mk R.carrier ≤ Cardinal.aleph0
          · -- R countable: both C_good and D are countable
            haveI : Countable R.carrier := Cardinal.mk_le_aleph0_iff.mp hR_le
            haveI : Countable (Polynomial R.carrier) := by
              letI : Countable (AddMonoidAlgebra R.carrier ℕ) := instCountableFinsupp
              exact Polynomial.toFinsupp_injective.countable
            have hC_good_countable : C_good.Countable :=
              Set.Countable.union (Set.countable_iUnion fun r =>
                Set.countable_iUnion fun _ =>
                  ((associatedPrimes.finite T (T ⧸ span {(r : T)})).subset
                    fun P hP => hP.1).countable) (Set.countable_singleton _)
            have hD_base_countable : D_base.Countable :=
              Set.Countable.union (Set.countable_singleton _)
                (Set.countable_iUnion fun f => Set.countable_iUnion fun hf =>
                  hD_root_countable f hf)
            have hD_mod_countable : D_mod.Countable := by
              apply Set.Countable.biUnion hC_good_countable
              intro P hP
              apply Set.countable_iUnion
              intro f
              apply Set.countable_iUnion
              intro hfne
              apply Set.Countable.image
              haveI : P.IsPrime := hC_good_prime P hP
              haveI : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
              exact (Polynomial.finite_setOf_isRoot hfne).countable
            right
            exact ⟨hC_good_countable,
              Set.Countable.union hD_base_countable hD_mod_countable⟩
          · -- R uncountable: use cardinal bound #(C_good × D) < #(ResidueField T)
            left
            push Not at hR_le
            have hR_inf : Cardinal.aleph0 ≤ Cardinal.mk R.carrier := le_of_lt hR_le
            -- #C_good ≤ #R
            have hC_le : Cardinal.mk C_good ≤ Cardinal.mk R.carrier := by
              calc Cardinal.mk C_good
                  ≤ Cardinal.mk ↑(⋃ (r : R.carrier), ⋃ (_ : (r : T) ≠ 0),
                      {P ∈ associatedPrimes T (T ⧸ span {(r : T)}) | ¬(I_s' ≤ P)}) +
                    Cardinal.mk ↑({⊥} : Set (Ideal T)) := Cardinal.mk_union_le _ _
                _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 +
                    Cardinal.mk R.carrier := by
                    gcongr
                    · exact (Cardinal.mk_iUnion_le _).trans
                        (mul_le_mul_right (ciSup_le' fun r => by
                        exact Cardinal.mk_le_aleph0_iff.mpr
                          ((Set.Finite.subset (associatedPrimes.finite T _)
                            (Set.iUnion_subset fun _ => fun P hP => hP.1)).countable.to_subtype)) _)
                    · exact (Cardinal.mk_le_one_iff_set_subsingleton.mpr
                        Set.subsingleton_singleton).trans (one_le_aleph0.trans hR_inf)
                _ = Cardinal.mk R.carrier := by
                    rw [Cardinal.mul_aleph0_eq hR_inf, Cardinal.add_eq_left hR_inf le_rfl]
            -- #D_base ≤ #R
            have hD_base_le : Cardinal.mk D_base ≤ Cardinal.mk R.carrier := by
              calc Cardinal.mk D_base
                  ≤ Cardinal.mk ↑({-t} : Set T) +
                    Cardinal.mk ↑(⋃ (f : Polynomial R.carrier), ⋃ (_ : f ≠ 0),
                      (fun x => x - t) '' {x : T | Polynomial.aeval x f = 0}) :=
                    Cardinal.mk_union_le _ _
                _ ≤ Cardinal.mk R.carrier + Cardinal.mk R.carrier := by
                    gcongr
                    · exact (Cardinal.mk_le_one_iff_set_subsingleton.mpr
                        Set.subsingleton_singleton).trans (one_le_aleph0.trans hR_inf)
                    · exact (Cardinal.mk_iUnion_le _).trans ((mul_le_mul'
                        (Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf))
                        (ciSup_le' fun f => Cardinal.mk_le_aleph0_iff.mpr (by
                          by_cases hf : f = 0
                          · exact Set.Countable.to_subtype (by simp [hf])
                          · exact (Set.countable_iUnion fun _ =>
                              hD_root_countable f hf).to_subtype))).trans
                        (Cardinal.mul_aleph0_eq hR_inf).le)
                _ = Cardinal.mk R.carrier := Cardinal.add_eq_left hR_inf le_rfl
            -- #D_mod ≤ #R (following Adjoin.lean D_mod_shifted pattern)
            have hD_mod_le : Cardinal.mk D_mod ≤ Cardinal.mk R.carrier := by
              apply (Cardinal.mk_biUnion_le _ _).trans
              have h_inner : ∀ (x : ↑C_good), Cardinal.mk ↑(⋃ (f : Polynomial R.carrier),
                  ⋃ (_ : Polynomial.map (φ x.1) f ≠ 0),
                    (fun α => liftQ x.1 α - t) ''
                      {α : T ⧸ x.1 | (Polynomial.map (φ x.1) f).IsRoot α}) ≤
                  Cardinal.mk R.carrier := by
                intro ⟨P, hP⟩
                calc Cardinal.mk ↑(⋃ (f : Polynomial R.carrier),
                          ⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                            (fun α => liftQ P α - t) ''
                              {α : T ⧸ P | (Polynomial.map (φ P) f).IsRoot α})
                      ≤ Cardinal.mk (Polynomial R.carrier) *
                          ⨆ (f : Polynomial R.carrier),
                            Cardinal.mk ↑(⋃ (_ : Polynomial.map (φ P) f ≠ 0),
                              (fun α => liftQ P α - t) ''
                              {α : T ⧸ P | (Polynomial.map (φ P) f).IsRoot α}) :=
                          Cardinal.mk_iUnion_le _
                    _ ≤ Cardinal.mk R.carrier * Cardinal.aleph0 := by
                          gcongr
                          · exact Polynomial.cardinalMk_le_max.trans (max_le le_rfl hR_inf)
                          · apply ciSup_le'
                            intro f
                            apply Cardinal.mk_le_aleph0_iff.mpr
                            by_cases hfne : Polynomial.map (φ P) f = 0
                            · exact Set.Countable.to_subtype (by simp [hfne])
                            · haveI : P.IsPrime := hC_good_prime P hP
                              haveI : IsDomain (T ⧸ P) := Ideal.Quotient.isDomain P
                              apply Set.Countable.to_subtype
                              apply Set.Finite.countable
                              apply Set.Finite.subset
                                (((Polynomial.rootSet_finite
                                  (Polynomial.map (φ P) f) (T ⧸ P)).image
                                  (liftQ P)).image (fun x => x - t))
                              apply Set.iUnion_subset
                              intro _ x hx
                              obtain ⟨α, hα, rfl⟩ := hx
                              exact ⟨liftQ P α,
                                ⟨α, Polynomial.mem_rootSet.mpr ⟨hfne, hα⟩, rfl⟩, rfl⟩
                    _ = Cardinal.mk R.carrier := Cardinal.mul_aleph0_eq hR_inf
              exact (mul_le_mul' hC_le (ciSup_le' h_inner)).trans (Cardinal.mul_eq_self hR_inf).le
            -- #D ≤ #R
            have hD_le : Cardinal.mk D ≤ Cardinal.mk R.carrier := by
              calc Cardinal.mk D
                  ≤ Cardinal.mk D_base + Cardinal.mk D_mod := Cardinal.mk_union_le _ _
                _ ≤ Cardinal.mk R.carrier + Cardinal.mk R.carrier :=
                    add_le_add hD_base_le hD_mod_le
                _ = Cardinal.mk R.carrier := Cardinal.add_eq_left hR_inf le_rfl
            calc Cardinal.mk (↑C_good × ↑D)
                = Cardinal.mk C_good * Cardinal.mk D := (Cardinal.mul_def _ _).symm
              _ ≤ Cardinal.mk R.carrier * Cardinal.mk R.carrier := mul_le_mul' hC_le hD_le
              _ = Cardinal.mk R.carrier := Cardinal.mul_eq_self hR_inf
              _ < Cardinal.mk T := hR_card
              _ = Cardinal.mk (IsLocalRing.ResidueField T) := hT_card
        have hI_not_le_good : ∀ P ∈ C_good, ¬(I_s' ≤ P) := by
          intro P hP hle
          rcases (Set.mem_union _ _ _).mp hP with h | h
          · rw [Set.mem_iUnion] at h
            obtain ⟨r, h⟩ := h
            rw [Set.mem_iUnion] at h
            obtain ⟨_, hPmem⟩ := h
            exact hPmem.2 hle
          · rw [Set.mem_singleton_iff.mp h] at hle
            exact hI_bot (le_antisymm hle bot_le)
        -- I_s' ⊄ P for ALL associated primes (not just C_good ones).
        -- This follows from h_no_common: if I_s' ≤ P with P∩R ≠ ⊥,
        -- then P∩R = span{q_P} for some prime q_P, so q_P | all of s',
        -- contradicting h_no_common.
        have hI_s'_not_le_assoc : ∀ (r : R.carrier) (_ : (r : T) ≠ 0)
            (P : Ideal T) (_ : P ∈ associatedPrimes T (T ⧸ span {(r : T)})),
            ¬(I_s' ≤ P) := by
          intro r hr P hP_mem hle
          have hht := R.height_bound (r : T) hr P hP_mem
          by_cases hcomap : P.comap R.carrier.subtype = ⊥
          · -- P ∩ R = ⊥: all s' zero, I_s' = ⊥
            exact hI_bot (le_antisymm (by
              apply Ideal.map_le_iff_le_comap.mpr
              apply Ideal.span_le.mpr
              intro x hx
              have h1 : x ∈ P.comap R.carrier.subtype :=
                Ideal.mem_comap.mpr (hle (Ideal.mem_map_of_mem _
                  (Ideal.subset_span (Finset.mem_coe.mpr hx))))
              have h1' : x ∈ (⊥ : Ideal R.carrier) := hcomap ▸ h1
              have hx_zero : x = 0 := (Submodule.mem_bot _).mp h1'
              change R.carrier.subtype x ∈ (⊥ : Ideal T)
              rw [hx_zero, map_zero]
              exact (Submodule.mem_bot T).mpr rfl) bot_le)
          · -- P ∩ R ≠ ⊥: find q_P, contradiction from h_no_common
            haveI : (P.comap R.carrier.subtype).IsPrime := hP_mem.isPrime.comap _
            obtain ⟨q_P, hqP_prime, hqP_in⟩ :=
              exists_prime_mem_of_ne_bot_closeup (P.comap R.carrier.subtype) hcomap
            have hQ_eq : Ideal.span {q_P} = P.comap R.carrier.subtype :=
              @eq_of_prime_le_prime_height_le_one R.carrier _ (NSubring.isDomain R) _ _
                ((Ideal.span_singleton_prime hqP_prime.ne_zero).mpr hqP_prime)
                (hP_mem.isPrime.comap _)
                (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqP_in))
                (mt (Ideal.span_singleton_eq_bot (α := R.carrier)).mp hqP_prime.ne_zero) hht
            have hqP_dvd_s' : ∀ x ∈ s', q_P ∣ x := fun x hx =>
              (Ideal.mem_span_singleton (α := R.carrier)).mp
                (hQ_eq ▸ Ideal.mem_comap.mpr (hle (Ideal.mem_map_of_mem _
                  (Ideal.subset_span (Finset.mem_coe.mpr hx)))))
            exact h_no_common q_P hqP_prime hqP_dvd_s'
        -- Apply unified avoidance (handles both countable and uncountable R)
        obtain ⟨δ, hδ_mem, hδ_avoid⟩ :=
          avoidance hC_good_prime hC_good_ne_max hCD_good_bound hI_not_le_good
        -- t' = t + δ satisfies transcendence, avoidance, remainder
        have ht'_trans : Transcendental R.carrier (t + δ) := by
          rw [Transcendental]
          intro ⟨p, hp_ne, hp_eval⟩
          have hδ_in_D : δ ∈ D := Set.mem_union_left _
            (Set.mem_union_right _
              (Set.mem_iUnion.mpr
                ⟨p, Set.mem_iUnion.mpr
                  ⟨hp_ne, ⟨t + δ, hp_eval, by ring⟩⟩⟩))
          open scoped Pointwise in
          have h_absurd : δ ∈ ((⊥ : Ideal T) : Set T) + ({δ} : Set T) := by
            have := Set.add_mem_add (⊥ : Ideal T).zero_mem
              (show δ ∈ ({δ} : Set T) from rfl)
            rwa [zero_add] at this
          exact absurd h_absurd
            (hδ_avoid ⊥ (Set.mem_union_right _ rfl) δ hδ_in_D)
        have ht'_avoid : ∀ (r : R.carrier), (r : T) ≠ 0 →
            ∀ P ∈ associatedPrimes T (T ⧸ span {(r : T)}),
            (t + δ) ∉ (P : Set T) := by
          intro r hr P hP hmem
          by_cases hle_P : I_s' ≤ P
          · -- Bad prime: impossible by h_no_common
            exact absurd hle_P (hI_s'_not_le_assoc r hr P hP)
          · -- Good prime: use avoidance result
            open scoped Pointwise in
            have h_in_sum : δ ∈ (P : Set T) + ({-t} : Set T) := by
              have := Set.add_mem_add hmem (show -t ∈ ({-t} : Set T) from rfl)
              rwa [show (t + δ) + -t = δ from by ring] at this
            exact absurd h_in_sum
              (hδ_avoid P (Set.mem_union_left _
                (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ⟨hP, hle_P⟩⟩⟩))
                (-t) (Set.mem_union_left _ (Set.mem_union_left _ rfl)))
        have hrem_T : ((c : T) - (t + δ) * (a : T)) ∈ I_s' := by
          suffices hrw : (↑c : T) - (t + δ) * (↑a : T) = v - δ * (↑a : T) by
            rw [hrw]
            exact Submodule.sub_mem _ hv (Ideal.mul_mem_right _ _ hδ_mem)
          have h_c_eq : (↑c : T) = (↑a : T) * t + v := by
            rw [← huv, ht_eq]
            simp
          rw [h_c_eq]
          ring
        -- Adjoin t+δ to R → S₁
        obtain ⟨S₁, hAext₁, ht'_S₁⟩ :=
          adjoin_transcendental_isNSubring R (t + δ) ht'_trans
            hAss_ht (fun P hP_prime hP_ht hPR_ne f hf_in i => by
              -- Modular transcendence: show coeff f i ∈ P∩R.
              -- By contradiction, show P ∈ C_good, use modular avoidance from D_mod.
              by_contra h_neg
              -- f.map (φ P) ≠ 0 (some coefficient doesn't vanish mod P)
              have hf_bar_ne : f.map (φ P) ≠ 0 := by
                intro h_eq
                apply h_neg
                have h := congr_fun (congr_arg Polynomial.coeff h_eq) i
                simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
                exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h)
              -- P is an associated prime of some T/(r₀)
              obtain ⟨r₀, hr₀T_ne, hP_assoc⟩ :=
                prime_height_le_one_mem_assoc P hP_prime hP_ht hPR_ne
              -- Show P ∈ C_good: need ¬(I_s' ≤ P).
              -- By hI_s'_not_le_assoc (from h_no_common): I_s' ⊄ P for all
              -- associated primes P with P ∩ R ≠ ⊥.
              have hP_in_C_good : P ∈ C_good := by
                apply Set.mem_union_left
                exact Set.mem_iUnion.mpr ⟨r₀, Set.mem_iUnion.mpr
                  ⟨hr₀T_ne, hP_assoc, hI_s'_not_le_assoc r₀ hr₀T_ne P hP_assoc⟩⟩
              -- mk P (t+δ) is a root of f.map (φ P) in T/P
              haveI := hP_prime
              have ht_root : (f.map (φ P)).IsRoot
                  (Ideal.Quotient.mk P (t + δ)) := by
                rw [Polynomial.IsRoot, Polynomial.eval_map,
                  show φ P = (Ideal.Quotient.mk P).comp R.carrier.subtype
                    from rfl,
                  ← Polynomial.hom_eval₂ f R.carrier.subtype
                    (Ideal.Quotient.mk P) (t + δ)]
                exact Ideal.Quotient.eq_zero_iff_mem.mpr hf_in
              -- liftQ P (mk P (t+δ)) - t ∈ D_mod ⊆ D
              have hlift_shifted_in_D :
                  liftQ P (Ideal.Quotient.mk P (t + δ)) - t ∈ D :=
                Set.mem_union_right _
                  (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr
                    ⟨hP_in_C_good, Set.mem_iUnion.mpr ⟨f,
                      Set.mem_iUnion.mpr ⟨hf_bar_ne,
                        ⟨Ideal.Quotient.mk P (t + δ), ht_root,
                          rfl⟩⟩⟩⟩⟩)
              -- δ - (liftQ - t) = (t + δ) - liftQ ∈ P
              have hlift_in_P : δ -
                  (liftQ P (Ideal.Quotient.mk P (t + δ)) - t) ∈ P := by
                have hmem : (t + δ) -
                    liftQ P (Ideal.Quotient.mk P (t + δ)) ∈ P := by
                  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hliftQ]
                  exact sub_self _
                convert hmem using 1
                ring
              -- δ ∈ P + {liftQ - t}, contradicting avoidance
              open scoped Pointwise in
              exact absurd
                ⟨δ - (liftQ P (Ideal.Quotient.mk P (t + δ)) - t),
                  hlift_in_P,
                  liftQ P (Ideal.Quotient.mk P (t + δ)) - t, rfl,
                  by ring⟩
                (hδ_avoid P hP_in_C_good
                  (liftQ P (Ideal.Quotient.mk P (t + δ)) - t)
                  hlift_shifted_in_D))
        have hle₁ := hAext₁.le
        have hrem_in_S₁ : (c : T) - (t + δ) * (a : T) ∈ S₁.carrier :=
          S₁.carrier.sub_mem (hle₁ c.2) (S₁.carrier.mul_mem ht'_S₁ (hle₁ a.2))
        let rem₁ : S₁.carrier := ⟨(c : T) - (t + δ) * (a : T), hrem_in_S₁⟩
        haveI : DecidableEq S₁.carrier := Classical.decEq _
        let liftR₁ := Subring.inclusion hle₁
        let s₁ : Finset S₁.carrier := s'.image liftR₁
        have hs₁_card : s₁.card ≤ m := Finset.card_image_le.trans hs'_card
        have hcomp : S₁.carrier.subtype.comp liftR₁ = R.carrier.subtype :=
          RingHom.ext fun _ => rfl
        have hrem₁_span : (rem₁ : T) ∈
            Ideal.map S₁.carrier.subtype (span (↑s₁ : Set S₁.carrier)) := by
          change (c : T) - (t + δ) * (a : T) ∈ _
          change _ ∈ Ideal.map S₁.carrier.subtype
            (span (↑(s'.image liftR₁) : Set S₁.carrier))
          rw [Finset.coe_image, ← Ideal.map_span, Ideal.map_map, hcomp]
          exact hrem_T
        have hS₁_card : Cardinal.mk S₁.carrier < Cardinal.mk T :=
          lt_of_le_of_lt hAext₁.card_le (max_lt hT_aleph0 hR_card)
        obtain ⟨S₂, hAext₂, hle₂, hrem₂⟩ :=
          ih S₁ hS₁_card s₁ hs₁_card rem₁ hrem₁_span
        refine ⟨S₂, isAExtension_trans' hAext₁ hAext₂,
          le_trans hle₁ hle₂, ?_⟩
        rw [Ideal.span_insert, Ideal.map_sup]
        refine Submodule.mem_sup.mpr
          ⟨⟨t + δ, hle₂ ht'_S₁⟩ * ⟨(a : T), (le_trans hle₁ hle₂) a.2⟩, ?_,
           ⟨(c : T) - (t + δ) * (a : T), hle₂ hrem_in_S₁⟩, ?_, ?_⟩
        · rw [Ideal.map_span, Set.image_singleton]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
        · have hcomp₂ : (Subring.inclusion hle₂).comp liftR₁ =
              Subring.inclusion (le_trans hle₁ hle₂) :=
            RingHom.ext fun _ => rfl
          change ⟨(rem₁ : T), hle₂ rem₁.2⟩ ∈
            Ideal.map (Subring.inclusion hle₂)
              (span (↑(s'.image liftR₁) : Set S₁.carrier)) at hrem₂
          rw [Finset.coe_image, ← Ideal.map_span, Ideal.map_map, hcomp₂] at hrem₂
          exact hrem₂
        · exact Subtype.ext (by
                               simp only [Subring.coe_add, Subring.coe_mul]
                               ring)
⟩

lemma close_up_avoidance_step
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    {m : ℕ}
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ m) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    (R : NSubring T) (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (a : R.carrier) (s' : Finset R.carrier) (hs'_card : s'.card ≤ m)
    (c : R.carrier)
    (hc : (c : T) ∈ Ideal.map R.carrier.subtype
      (span (insert (a : R.carrier) (↑s' : Set R.carrier))))
    (h_no_common : ∀ (q : R.carrier), Prime q → ¬(∀ x ∈ s', q ∣ x)) :
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c : T), hle c.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle)
          (span (insert (a : R.carrier) (↑s' : Set R.carrier))) := by
  exact
    (close_up_avoidance_step_proof
      (m := m) hM_not_assoc hAss_ht ih R hR_card hT_card hT_aleph0 a s' hs'_card c hc
      h_no_common
    ).down
end
