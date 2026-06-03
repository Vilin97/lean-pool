/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.CloseUp.FactorDivisibility
import LeanPool.AndersonConjecture.Jensen.CloseUp.IntersectionStep

/-!
# Close-up: factor theorem

Combines the divisibility, intersection, and no-common-factor
sub-cases into the main factor theorem for the close-up
induction (Heitmann, Lemma 4, case n >= 3).
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

private def close_up_aux_factor_proof
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (n'' : ℕ)
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ n'' + 1 + 1) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    (m : ℕ)
    (ih_m : ∀ m_1, m_1 < m →
      ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T),
      letI : IsDomain R.carrier := NSubring.isDomain R
      letI : UniqueFactorizationMonoid R.carrier := R.isUFD
      ∀ (a : R.carrier) (s : Finset R.carrier),
      gcdComplexity s ≤ m_1 →
      s.card = n'' + 1 + 1 + 1 → a ∈ s → ∀ (c : R.carrier),
      (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)) →
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    {R : NSubring T} (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    [DecidableEq R.carrier]
    {a : R.carrier}
    (ih_a : ∀ (y : R.carrier), DvdNotUnit y a →
      ∀ (s : Finset R.carrier),
      gcdComplexity s ≤ m →
      s.card = n'' + 1 + 1 + 1 → y ∈ s → ∀ (c : R.carrier),
      (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)) →
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    {s : Finset R.carrier}
    (hs_gcd : gcdComplexity s ≤ m)
    (hs_eq : s.card = n'' + 1 + 1 + 1) (ha_mem : a ∈ s)
    {c : R.carrier}
    (hc : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)))
    (s' : Finset R.carrier) (hs'_def : s' = s.erase a)
    (hs_insert : s = insert a s')
    (hs'_card : s'.card ≤ n'' + 1 + 1)
    (_hgcd : ∃ p : R.carrier, Prime p ∧ ∀ x ∈ s', p ∣ x)
    {p : R.carrier} (_hp : Prime p) (_hp_dvd : ∀ x ∈ s', p ∣ x)
    (hpa : ¬p ∣ a)
    (hgcd_factor : ∃ q : R.carrier, Prime q ∧ (∀ x ∈ s', q ∣ x) ∧ (q ∣ a ∨ q ∣ c)) : PLift (
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c : T), hle c.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)) ) := ⟨by
  obtain ⟨q, hq, hq_dvd_s', hq_ac⟩ := hgcd_factor
  by_cases hqa : q ∣ a
  · -- Sub-case A: q | a. Factor out q from ALL of s, use ih_a.
    have hq_dvd_all : ∀ x ∈ s, q ∣ x := by
      intro x hx
      rw [hs_insert, Finset.mem_insert] at hx
      rcases hx with rfl | hx'
      · exact hqa
      · exact hq_dvd_s' x hx'
    have h_span_le : span (↑s : Set R.carrier) ≤ span {q} :=
      Ideal.span_le.mpr fun x hx =>
        Ideal.mem_span_singleton.mpr (hq_dvd_all x (Finset.mem_coe.mp hx))
    have hc_qT : (c : T) ∈ span {(q : T)} := by
      have := Ideal.map_mono h_span_le hc
      rwa [Ideal.map_span, Set.image_singleton] at this
    have hcR := close_up_dvd R q c hc_qT
    obtain ⟨c', hcc'⟩ := Ideal.mem_span_singleton.mp hcR
    classical
    -- Build divided set t_set = {x/q | x ∈ s}
    let div_q : R.carrier → R.carrier := fun x =>
      if h : q ∣ x then Classical.choose h else x
    have hdiv_spec : ∀ x ∈ s, x = q * div_q x := by
      intro x hx
      simp only [div_q, dif_pos (hq_dvd_all x hx)]
      exact Classical.choose_spec (hq_dvd_all x hx)
    let t_set := s.image div_q
    have h_ideal_eq : span (↑s : Set R.carrier) =
        span {q} * span (↑t_set : Set R.carrier) :=
      span_eq_mul_span_image_div q s hq_dvd_all div_q hdiv_spec
    rw [h_ideal_eq, Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hc
    rw [Ideal.mem_span_singleton_mul] at hc
    obtain ⟨z, hz, hqz⟩ := hc
    have hq_ne : (q : T) ≠ 0 := fun h => hq.ne_zero (Subtype.val_injective h)
    have hqc_val : (q : T) * (c' : T) = (c : T) := by
      have := congr_arg R.carrier.subtype hcc'
      simp only [map_mul] at this
      exact this.symm
    have hz_eq : z = (c' : T) := mul_left_cancel₀ hq_ne (hqz.trans hqc_val.symm)
    have hc'_mem : (c' : T) ∈ Ideal.map R.carrier.subtype
        (span (↑t_set : Set R.carrier)) := hz_eq ▸ hz
    -- Reduce: find S with c' ∈ span(t_set) in S, then convert back
    suffices hsuff : ∃ S : NSubring T, IsAExtension R S ∧
        ∃ (hle : R.carrier ≤ S.carrier),
          (⟨(c' : T), hle c'.2⟩ : S.carrier) ∈
            Ideal.map (Subring.inclusion hle)
              (span (↑t_set : Set R.carrier)) by
      obtain ⟨S, hAext, hle, hc'_S⟩ := hsuff
      refine ⟨S, hAext, hle, ?_⟩
      rw [h_ideal_eq, Ideal.map_mul]
      have hc_eq : (⟨(c : T), hle c.2⟩ : S.carrier) =
          ⟨(q : T), hle q.2⟩ * ⟨(c' : T), hle c'.2⟩ := by
        ext
        simp only [Subring.coe_mul]
        exact hqc_val.symm
      rw [hc_eq]
      exact Ideal.mul_mem_mul
        (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)) hc'_S
    -- Handle sub-cases for div_q(a)
    have ha'_mem : div_q a ∈ t_set :=
      Finset.mem_image.mpr ⟨a, ha_mem, rfl⟩
    by_cases ha'_zero : div_q a = 0
    · have ha_zero : a = 0 := by
        rw [hdiv_spec a ha_mem, ha'_zero, mul_zero]
      set t₀ := t_set.erase (div_q a) with ht₀_def
      have ht₀_card : t₀.card ≤ n'' + 1 + 1 := by
        have h1 : t_set.card ≤ n'' + 1 + 1 + 1 :=
          (Finset.card_image_le (f := div_q) (s := s)).trans (le_of_eq hs_eq)
        simp only [ht₀_def, Finset.card_erase_of_mem ha'_mem]
        omega
      have hspan_eq : span (↑t_set : Set R.carrier) =
          span (↑t₀ : Set R.carrier) := by
        apply le_antisymm
        · apply Ideal.span_le.mpr
          intro x hx
          rcases eq_or_ne x (div_q a) with rfl | hne
          · rw [ha'_zero]
            exact zero_mem _
          · exact Ideal.subset_span (Finset.mem_coe.mpr
              (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hx⟩))
        · exact Ideal.span_mono (Finset.coe_subset.mpr
            (Finset.erase_subset _ _))
      have hc'_t₀ : (c' : T) ∈ Ideal.map R.carrier.subtype
          (span (↑t₀ : Set R.carrier)) := hspan_eq ▸ hc'_mem
      obtain ⟨S, hAext, hle, hmem⟩ := ih R hR_card t₀ ht₀_card c' hc'_t₀
      exact ⟨S, hAext, hle, Ideal.map_mono
        (Ideal.span_mono (Finset.coe_subset.mpr
          (Finset.erase_subset _ _))) hmem⟩
    · by_cases ha'_unit : IsUnit (div_q a)
      · refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩,
            le_refl _, ?_⟩
        have h_id : Subring.inclusion (le_refl R.carrier) =
            RingHom.id R.carrier :=
          RingHom.ext fun x => Subtype.ext rfl
        change (⟨(c' : T), le_refl R.carrier c'.2⟩ : R.carrier) ∈
          Ideal.map (Subring.inclusion (le_refl R.carrier))
            (span (↑t_set : Set R.carrier))
        rw [h_id, Ideal.map_id,
          Ideal.eq_top_of_isUnit_mem _
            (Ideal.subset_span (Finset.mem_coe.mpr ha'_mem)) ha'_unit]
        exact Submodule.mem_top
      · have hdvd : DvdNotUnit (div_q a) a :=
          ⟨ha'_zero, ⟨q, hq.not_unit,
            (hdiv_spec a ha_mem).trans (mul_comm q (div_q a))⟩⟩
        have ht_card : t_set.card = n'' + 1 + 1 + 1 := by
          have hinj : Set.InjOn div_q ↑s := fun x hx y hy hxy => by
            have hx_eq := hdiv_spec x (Finset.mem_coe.mp hx)
            have hy_eq := hdiv_spec y (Finset.mem_coe.mp hy)
            calc x = q * div_q x := hx_eq
              _ = q * div_q y := by rw [hxy]
              _ = y := hy_eq.symm
          rw [show t_set = s.image div_q from rfl,
            Finset.card_image_of_injOn hinj, hs_eq]
        have ht_gcd : gcdComplexity t_set ≤ m := le_trans (by
          change gcdComplexity t_set ≤ gcdComplexity s
          have hinj : Set.InjOn div_q ↑s := fun x hx y hy hxy => by
            have hx_eq := hdiv_spec x (Finset.mem_coe.mp hx)
            have hy_eq := hdiv_spec y (Finset.mem_coe.mp hy)
            calc x = q * div_q x := hx_eq
              _ = q * div_q y := by rw [hxy]
              _ = y := hy_eq.symm
          exact gcdComplexity_div_le q hq s hq_dvd_all div_q hdiv_spec hinj) hs_gcd
        exact ih_a (div_q a) hdvd t_set
          ht_gcd ht_card ha'_mem c' hc'_mem
  · -- Sub-case B1: q does not divide a, q | c. Factor out q from s' and c.
    have hqc : q ∣ c := by
      rcases hq_ac with h | h
      · exact absurd h hqa
      · exact h
    have h_span_le_q : span (↑s' : Set R.carrier) ≤ span {q} :=
      Ideal.span_le.mpr fun x hx =>
        Ideal.mem_span_singleton.mpr (hq_dvd_s' x (Finset.mem_coe.mp hx))
    obtain ⟨c', hcc'⟩ := hqc
    have hq_ne : (q : T) ≠ 0 := fun h => hq.ne_zero (Subtype.val_injective h)
    have hqc_val : (c : T) = (q : T) * (c' : T) := by
      have := congr_arg Subtype.val hcc'
      simp only [Subring.coe_mul] at this
      exact this
    classical
    let div_q' : R.carrier → R.carrier :=
      fun x => if h : q ∣ x then Classical.choose h else x
    have hdiv_spec' : ∀ x ∈ s', x = q * div_q' x := by
      intro x hx
      simp only [div_q', dif_pos (hq_dvd_s' x hx)]
      exact Classical.choose_spec (hq_dvd_s' x hx)
    let t_set' := s'.image div_q'
    have h_ideal_eq_q : span (↑s' : Set R.carrier) =
        span {q} * span (↑t_set' : Set R.carrier) :=
      span_eq_mul_span_image_div q s' hq_dvd_s' div_q' hdiv_spec'
    have h_mul_le : span {q} * span (↑(insert a t_set') : Set R.carrier) ≤
        span (↑s : Set R.carrier) :=
      hs_insert ▸ prime_mul_span_insert_le q a s' div_q' hdiv_spec'
    -- Suffices to show c' ∈ span(insert a t_set') in some extension S
    suffices h_red : ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c' : T), hle c'.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑(insert a t_set') : Set R.carrier)) by
      obtain ⟨S, hAext, hle, hc'S⟩ := h_red
      refine ⟨S, hAext, hle, ?_⟩
      have hc_eq : (⟨(c : T), hle c.2⟩ : S.carrier) =
          ⟨(q : T), hle q.2⟩ * ⟨(c' : T), hle c'.2⟩ := by
        ext
        simp only [Subring.coe_mul]
        exact hqc_val
      rw [hc_eq]
      have hmul := Ideal.mul_mem_mul
        (Ideal.mem_map_of_mem (Subring.inclusion hle)
          (Ideal.subset_span (show q ∈ ({q} : Set R.carrier) from rfl))) hc'S
      rw [← Ideal.map_mul] at hmul
      exact Ideal.map_mono h_mul_le hmul
    have hc_B1 := hc
    rw [hs_insert, Finset.coe_insert, Ideal.span_insert, Ideal.map_sup] at hc_B1
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hc_B1
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hu
    obtain ⟨t_val, ht_eq⟩ := hu
    have hv_qT : v ∈ Ideal.span {(q : T)} := by
      have h1 := Ideal.map_mono h_span_le_q hv
      rw [Ideal.map_span, Set.image_singleton] at h1
      exact h1
    obtain ⟨w, hw_eq⟩ := Ideal.mem_span_singleton.mp hv_qT
    -- a*t_val = q*(c' - w) from the decomposition c = u + v
    have h_at : (a : T) * t_val = (q : T) * ((c' : T) - w) := by
      have h3 : u + v = (q : T) * (c' : T) :=
        huv.trans hqc_val
      rw [ht_eq, hw_eq] at h3
      have h4 := eq_sub_of_add_eq h3
      rw [← mul_sub] at h4
      exact h4
    -- a is nzd on T/(q) since q prime and q ∤ a, so t_val ∈ (q)·T
    have ht_qT : ∃ t' : T, t_val = (q : T) * t' :=
      nzd_element_in_span_prime R q a hq hqa hM_not_assoc t_val (by
        rw [h_at]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    obtain ⟨t', ht'⟩ := ht_qT
    have hc'_eq : (c' : T) = (a : T) * t' + w := by
      have h := h_at
      rw [ht'] at h
      have h' : (q : T) * ((a : T) * t') = (q : T) * ((c' : T) - w) := by
        rw [← h]
        ring
      exact eq_add_of_sub_eq (mul_left_cancel₀ hq_ne h').symm
    have hw_span : w ∈ Ideal.map R.carrier.subtype (span (↑t_set' : Set R.carrier)) := by
      have hv' := hv
      rw [h_ideal_eq_q, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
        Ideal.mem_span_singleton_mul] at hv'
      obtain ⟨z, hz, hqz⟩ := hv'
      have : z = w := mul_left_cancel₀ hq_ne (hqz.trans hw_eq)
      exact this ▸ hz
    have hc'_mem : (c' : T) ∈
        Ideal.map R.carrier.subtype (span (↑(insert a t_set') : Set R.carrier)) := by
      rw [hc'_eq]
      apply add_mem
      · exact Ideal.map_mono
          (Ideal.span_mono
            (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr (Finset.mem_insert_self a t_set'))))
          (by rw [Ideal.map_span, Set.image_singleton]
              exact Ideal.mem_span_singleton.mpr ⟨t', rfl⟩)
      · exact Ideal.map_mono
          (Ideal.span_mono (Finset.coe_subset.mpr (Finset.subset_insert a t_set'))) hw_span
    -- Recursive close_up for (R, insert a t_set', c')
    by_cases ha_t : a ∈ t_set'
    · -- a ∈ t_set': use ih directly since card ≤ n''+2
      have h_eq : insert a t_set' = t_set' := Finset.insert_eq_of_mem ha_t
      rw [h_eq] at hc'_mem ⊢
      exact ih R hR_card t_set' (Finset.card_image_le.trans hs'_card) c' hc'_mem
    · -- a ∉ t_set': card = n''+3, use nested WF
      have hs'_ne : s'.Nonempty :=
        Finset.card_pos.mp (by
          rw [hs'_def, Finset.card_erase_of_mem ha_mem, hs_eq]
          omega)
      have ht_ne : t_set'.Nonempty :=
        ⟨div_q' hs'_ne.choose, Finset.mem_image.mpr ⟨hs'_ne.choose, hs'_ne.choose_spec, rfl⟩⟩
      obtain ⟨b₀, hb₀⟩ := ht_ne
      suffices h_nested : ∀ (b : R.carrier) (rest : Finset R.carrier),
          rest.card ≤ n'' + 1 + 1 → a ∉ rest → b ∈ rest →
          gcdComplexity (insert a rest) ≤ gcdComplexity s → ∀ (c_n : R.carrier),
          (c_n : T) ∈ Ideal.map R.carrier.subtype
            (span (↑(insert a rest) : Set R.carrier)) →
          ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
            (⟨(c_n : T), hle c_n.2⟩ : S.carrier) ∈
              Ideal.map (Subring.inclusion hle) (span (↑(insert a rest) : Set R.carrier)) from by
        refine h_nested b₀ t_set' (Finset.card_image_le.trans hs'_card) ha_t hb₀ ?_ c' hc'_mem
        -- gcdComplexity (insert a t_set') ≤ gcdComplexity s
        show gcdComplexity (insert a t_set') ≤ gcdComplexity s
        letI : NormalizationMonoid R.carrier :=
          UniqueFactorizationMonoid.normalizationMonoid
        have ha_not_s' : a ∉ s' := by
          rw [hs'_def]
          simp [Finset.mem_erase]
        unfold gcdComplexity
        rw [hs_insert, Finset.sum_insert ha_not_s',
            Finset.sum_insert ha_t]
        apply Nat.add_le_add_left
        rw [show t_set' = s'.image div_q' from rfl]
        have hinj_q' : Set.InjOn div_q' ↑s' := fun x hx y hy hxy => by
          have hx_eq := hdiv_spec' x (Finset.mem_coe.mp hx)
          have hy_eq := hdiv_spec' y (Finset.mem_coe.mp hy)
          calc x = q * div_q' x := hx_eq
            _ = q * div_q' y := by rw [hxy]
            _ = y := hy_eq.symm
        rw [Finset.sum_image hinj_q']
        apply Finset.sum_le_sum
        intro x hx
        by_cases hx0 : x = 0
        · subst hx0
          have : div_q' 0 = 0 := by
            have h := hdiv_spec' 0 hx
            exact (mul_eq_zero.mp h.symm).resolve_left hq.ne_zero
          simp [this]
        · have hdvd_x : div_q' x ∣ x :=
            ⟨q, (hdiv_spec' x hx).trans (mul_comm q (div_q' x))⟩
          by_cases hfx : div_q' x = 0
          · simp [hfx, UniqueFactorizationMonoid.normalizedFactors_zero]
          · exact Multiset.card_le_card
              ((UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
                hfx hx0).mp hdvd_x)
      -- Proof by WF on b
      intro b
      apply wellFounded_dvdNotUnit.induction b
      intro b ih_b rest hrest_card ha_rest
        hb_rest hgcd_rest c_n hc_n
      -- Case: common prime of rest dividing a or c_n?
      by_cases h_factor : ∃ q' : R.carrier, Prime q' ∧ (∀ x ∈ rest, q' ∣ x) ∧ (q' ∣ a ∨ q' ∣ c_n)
      · obtain ⟨q', hq', hq'_dvd, hq'_ac⟩ := h_factor
        by_cases hq'a : q' ∣ a
        · exact close_up_aux_factor_dvd_a
            n'' ih m hR_card ih_a hs_gcd rest hrest_card ha_rest hgcd_rest
            hq' hq'_dvd hq'a hc_n
        · exact close_up_aux_factor_dvd_c
            hM_not_assoc n'' ih hR_card rest hrest_card ha_rest hb_rest hgcd_rest
            ih_b hq' hq'_dvd hq'a hc_n (hq'_ac.resolve_left hq'a)
      · -- No common prime dividing a or c_n: avoidance or intersection
        push Not at h_factor
        exact close_up_aux_factor_no_factor
          hM_not_assoc hAss_ht hT_card hT_aleph0 n'' ih m ih_m
          hR_card ih_a hs_gcd rest hrest_card ha_rest hb_rest hgcd_rest
          h_factor hc_n
⟩

theorem close_up_aux_factor
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (n'' : ℕ)
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ n'' + 1 + 1) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    (m : ℕ)
    (ih_m : ∀ m_1, m_1 < m →
      ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T),
      letI : IsDomain R.carrier := NSubring.isDomain R
      letI : UniqueFactorizationMonoid R.carrier := R.isUFD
      ∀ (a : R.carrier) (s : Finset R.carrier),
      gcdComplexity s ≤ m_1 →
      s.card = n'' + 1 + 1 + 1 → a ∈ s → ∀ (c : R.carrier),
      (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)) →
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    {R : NSubring T} (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    [DecidableEq R.carrier]
    {a : R.carrier}
    (ih_a : ∀ (y : R.carrier), DvdNotUnit y a →
      ∀ (s : Finset R.carrier),
      gcdComplexity s ≤ m →
      s.card = n'' + 1 + 1 + 1 → y ∈ s → ∀ (c : R.carrier),
      (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)) →
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    {s : Finset R.carrier}
    (hs_gcd : gcdComplexity s ≤ m)
    (hs_eq : s.card = n'' + 1 + 1 + 1) (ha_mem : a ∈ s)
    {c : R.carrier}
    (hc : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)))
    (s' : Finset R.carrier) (hs'_def : s' = s.erase a)
    (hs_insert : s = insert a s')
    (hs'_card : s'.card ≤ n'' + 1 + 1)
    (_hgcd : ∃ p : R.carrier, Prime p ∧ ∀ x ∈ s', p ∣ x)
    {p : R.carrier} (_hp : Prime p) (_hp_dvd : ∀ x ∈ s', p ∣ x)
    (hpa : ¬p ∣ a)
    (hgcd_factor : ∃ q : R.carrier, Prime q ∧ (∀ x ∈ s', q ∣ x) ∧ (q ∣ a ∨ q ∣ c)) :
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c : T), hle c.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)) := by
  exact
    (close_up_aux_factor_proof
      (R := R) (a := a) (s := s) (c := c) (p := p) hM_not_assoc hAss_ht hT_card hT_aleph0
      n'' ih m ih_m hR_card ih_a hs_gcd hs_eq ha_mem hc s' hs'_def hs_insert hs'_card _hgcd
      _hp _hp_dvd hpa hgcd_factor
    ).down
end
