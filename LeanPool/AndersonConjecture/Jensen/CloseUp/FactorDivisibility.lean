/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.CloseUp.GcdComplexity

/-!
# Close-up: divisibility sub-cases

Sub-cases of the well-founded induction for the close-up
construction where a common prime factor p of the generators
s' divides either the distinguished generator a or the witness
c. Dividing out p reduces the GCD complexity.
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

theorem close_up_aux_factor_dvd_a
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (n'' : ℕ)
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ n'' + 1 + 1) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    (m : ℕ)
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
    (rest : Finset R.carrier)
    (hrest_card : rest.card ≤ n'' + 1 + 1)
    (ha_rest : a ∉ rest)
    (hgcd_rest : gcdComplexity (insert a rest) ≤ gcdComplexity s)
    {q' : R.carrier} (hq' : Prime q')
    (hq'_dvd : ∀ x ∈ rest, q' ∣ x)
    (hq'a : q' ∣ a)
    {c_n : R.carrier}
    (hc_n : (c_n : T) ∈ Ideal.map R.carrier.subtype
      (span (↑(insert a rest) : Set R.carrier))) :
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c_n : T), hle c_n.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle)
          (span (↑(insert a rest) : Set R.carrier)) := by
  classical
  have hq'_dvd_all : ∀ x ∈ insert a rest, q' ∣ x := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx'
    · exact hq'a
    · exact hq'_dvd x hx'
  have h_sl : span (↑(insert a rest) : Set R.carrier) ≤ span {q'} :=
    Ideal.span_le.mpr fun x hx =>
      Ideal.mem_span_singleton.mpr (hq'_dvd_all x (Finset.mem_coe.mp hx))
  have hc_q'T : (c_n : T) ∈ span {(q' : T)} := by
    have := Ideal.map_mono h_sl hc_n
    rwa [Ideal.map_span, Set.image_singleton] at this
  have hcR := close_up_dvd R q' c_n hc_q'T
  obtain ⟨c_n', hcc_n'⟩ := Ideal.mem_span_singleton.mp hcR
  let div_q_a : R.carrier → R.carrier :=
    fun x => if h : q' ∣ x then Classical.choose h else x
  have hdiv_a : ∀ x ∈ insert a rest, x = q' * div_q_a x := by
    intro x hx
    simp only [div_q_a, dif_pos (hq'_dvd_all x hx)]
    exact Classical.choose_spec (hq'_dvd_all x hx)
  let t_q' := (insert a rest).image div_q_a
  have h_ie : span (↑(insert a rest) : Set R.carrier) =
      span {q'} * span (↑t_q' : Set R.carrier) :=
    span_eq_mul_span_image_div q' (insert a rest) hq'_dvd_all div_q_a hdiv_a
  rw [h_ie, Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hc_n
  rw [Ideal.mem_span_singleton_mul] at hc_n
  obtain ⟨z, hz, hq'z⟩ := hc_n
  have hq'_ne : (q' : T) ≠ 0 := fun h => hq'.ne_zero (Subtype.val_injective h)
  have hq'c : (q' : T) * (c_n' : T) = (c_n : T) := by
    have := congr_arg R.carrier.subtype hcc_n'
    simp only [map_mul] at this
    exact this.symm
  have hz_eq : z = (c_n' : T) := mul_left_cancel₀ hq'_ne (hq'z.trans hq'c.symm)
  have hc_n'_mem : (c_n' : T) ∈
      Ideal.map R.carrier.subtype (span (↑t_q' : Set R.carrier)) := hz_eq ▸ hz
  suffices hsuff : ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c_n' : T), hle c_n'.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle) (span (↑t_q' : Set R.carrier)) by
    obtain ⟨S, hAext, hle, hc'_S⟩ := hsuff
    refine ⟨S, hAext, hle, ?_⟩
    rw [h_ie, Ideal.map_mul]
    have hc_eq : (⟨(c_n : T), hle c_n.2⟩ : S.carrier) =
        ⟨(q' : T), hle q'.2⟩ * ⟨(c_n' : T), hle c_n'.2⟩ := by
      ext
      simp only [Subring.coe_mul]
      exact hq'c.symm
    rw [hc_eq]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)) hc'_S
  by_cases ht_card : t_q'.card ≤ n'' + 1 + 1
  · exact ih R hR_card t_q' ht_card c_n' hc_n'_mem
  · have ha'_mem : div_q_a a ∈ t_q' :=
      Finset.mem_image.mpr ⟨a, Finset.mem_insert_self a rest, rfl⟩
    by_cases ha'_zero : div_q_a a = 0
    · have ha_zero : a = 0 := by
        rw [hdiv_a a (Finset.mem_insert_self a rest), ha'_zero, mul_zero]
      have ht_q'_bound : t_q'.card ≤ n'' + 1 + 1 + 1 :=
        Finset.card_image_le.trans
          (by rw [Finset.card_insert_of_notMem ha_rest]
              omega)
      have : (t_q'.erase (div_q_a a)).card ≤ n'' + 1 + 1 := by
        rw [Finset.card_erase_of_mem ha'_mem]
        omega
      have hspan_eq : span (↑t_q' : Set R.carrier) =
          span (↑(t_q'.erase (div_q_a a)) : Set R.carrier) := by
        apply le_antisymm
        · apply Ideal.span_le.mpr
          intro x hx
          rcases eq_or_ne x (div_q_a a)
            with rfl | hne
          · rw [ha'_zero]
            exact zero_mem _
          · exact Ideal.subset_span
              (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hx⟩))
        · exact Ideal.span_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
      rw [hspan_eq] at hc_n'_mem
      obtain ⟨S, hA, hl, hm⟩ := ih R hR_card _ this c_n' hc_n'_mem
      exact ⟨S, hA, hl,
        Ideal.map_mono (Ideal.span_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))) hm⟩
    · by_cases ha'_unit : IsUnit (div_q_a a)
      · refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, ?_⟩
        have h_id : Subring.inclusion (le_refl R.carrier) = RingHom.id R.carrier :=
          RingHom.ext fun x => Subtype.ext rfl
        change (⟨(c_n' : T), le_refl R.carrier c_n'.2⟩ : R.carrier) ∈
          Ideal.map (Subring.inclusion (le_refl R.carrier)) (span (↑t_q' : Set R.carrier))
        rw [h_id, Ideal.map_id,
          Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Finset.mem_coe.mpr ha'_mem))
            ha'_unit]
        exact Submodule.mem_top
      · have hdvd : DvdNotUnit (div_q_a a) a :=
          ⟨ha'_zero, ⟨q', hq'.not_unit,
            (hdiv_a a (Finset.mem_insert_self a rest)).trans (mul_comm q' (div_q_a a))⟩⟩
        have ht_card_eq : t_q'.card = n'' + 1 + 1 + 1 := by
          push Not at ht_card
          have hins_card : (insert a rest).card =
              n'' + 1 + 1 + 1 := by
            rw [Finset.card_insert_of_notMem ha_rest]
            have : rest.card = n'' + 1 + 1 := by
              have h_le : t_q'.card ≤ (insert a rest).card :=
                Finset.card_image_le
              rw [Finset.card_insert_of_notMem ha_rest] at h_le
              omega
            omega
          have h1 : t_q'.card ≤ n'' + 1 + 1 + 1 :=
            Finset.card_image_le.trans
              (by rw [hins_card])
          omega
        have ht_gcd : gcdComplexity t_q' ≤ m := le_trans (by
          change gcdComplexity t_q' ≤ gcdComplexity s
          apply le_trans _ hgcd_rest
          have hinj_qa : Set.InjOn div_q_a ↑(insert a rest) :=
            fun x hx y hy hxy => by
              have hx_eq := hdiv_a x (Finset.mem_coe.mp hx)
              have hy_eq := hdiv_a y (Finset.mem_coe.mp hy)
              calc x = q' * div_q_a x := hx_eq
                _ = q' * div_q_a y := by rw [hxy]
                _ = y := hy_eq.symm
          exact gcdComplexity_div_le q' hq' (insert a rest)
            hq'_dvd_all div_q_a hdiv_a hinj_qa) hs_gcd
        exact ih_a (div_q_a a) hdvd t_q' ht_gcd ht_card_eq ha'_mem c_n' hc_n'_mem


theorem close_up_aux_factor_dvd_c
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (n'' : ℕ)
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ n'' + 1 + 1) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)))
    {R : NSubring T} (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    [DecidableEq R.carrier]
    {a : R.carrier}
    {s : Finset R.carrier}
    (rest : Finset R.carrier)
    (hrest_card : rest.card ≤ n'' + 1 + 1)
    (ha_rest : a ∉ rest)
    {b : R.carrier} (hb_rest : b ∈ rest)
    (hgcd_rest : gcdComplexity (insert a rest) ≤ gcdComplexity s)
    (ih_b : ∀ (y : R.carrier), DvdNotUnit y b →
      ∀ (rest : Finset R.carrier),
      rest.card ≤ n'' + 1 + 1 → a ∉ rest → y ∈ rest →
      gcdComplexity (insert a rest) ≤ gcdComplexity s →
      ∀ (c_n : R.carrier),
      (c_n : T) ∈ Ideal.map R.carrier.subtype
        (span (↑(insert a rest) : Set R.carrier)) →
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c_n : T), hle c_n.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle)
            (span (↑(insert a rest) : Set R.carrier)))
    {q' : R.carrier} (hq' : Prime q')
    (hq'_dvd : ∀ x ∈ rest, q' ∣ x)
    (hq'a : ¬q' ∣ a)
    {c_n : R.carrier}
    (hc_n : (c_n : T) ∈ Ideal.map R.carrier.subtype
      (span (↑(insert a rest) : Set R.carrier)))
    (hq'c : q' ∣ c_n) :
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c_n : T), hle c_n.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle)
          (span (↑(insert a rest) : Set R.carrier)) := by
  classical
  obtain ⟨c_n', hcc_n'⟩ := hq'c
  have hq'_ne : (q' : T) ≠ 0 := fun h => hq'.ne_zero (Subtype.val_injective h)
  have hq'c_val : (c_n : T) = (q' : T) * (c_n' : T) := by
    have := congr_arg Subtype.val hcc_n'
    simp only [Subring.coe_mul] at this
    exact this
  let div_q_b : R.carrier → R.carrier :=
    fun x => if h : q' ∣ x then Classical.choose h else x
  have hdiv_b : ∀ x ∈ rest, x = q' * div_q_b x := by
    intro x hx
    simp only [div_q_b, dif_pos (hq'_dvd x hx)]
    exact Classical.choose_spec (hq'_dvd x hx)
  let rest' := rest.image div_q_b
  have h_ie_b : span (↑rest : Set R.carrier) =
      span {q'} * span (↑rest' : Set R.carrier) :=
    span_eq_mul_span_image_div q' rest hq'_dvd div_q_b hdiv_b
  have h_ml_b : span {q'} * span (↑(insert a rest') : Set R.carrier) ≤
      span (↑(insert a rest) : Set R.carrier) :=
    prime_mul_span_insert_le q' a rest div_q_b hdiv_b
  suffices h_suff_b : ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c_n' : T), hle c_n'.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle) (span (↑(insert a rest') : Set R.carrier)) by
    obtain ⟨S, hAext, hle, hc'_S⟩ := h_suff_b
    refine ⟨S, hAext, hle, ?_⟩
    have hc_eq : (⟨(c_n : T), hle c_n.2⟩ : S.carrier) =
        ⟨(q' : T), hle q'.2⟩ * ⟨(c_n' : T), hle c_n'.2⟩ := by
      ext
      simp only [Subring.coe_mul]
      exact hq'c_val
    rw [hc_eq]
    have hmul := Ideal.mul_mem_mul
      (Ideal.mem_map_of_mem (Subring.inclusion hle)
        (Ideal.subset_span (show q' ∈ ({q'} : Set R.carrier) from rfl))) hc'_S
    rw [← Ideal.map_mul] at hmul
    exact Ideal.map_mono h_ml_b hmul
  -- NZD argument: a is regular on T/q'T since q' ∤ a
  have hc_n_B1 := hc_n
  rw [Finset.coe_insert, Ideal.span_insert, Ideal.map_sup] at hc_n_B1
  obtain ⟨u_b, hu_b, v_b, hv_b, huv_b⟩ := Submodule.mem_sup.mp hc_n_B1
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hu_b
  obtain ⟨t_val_b, ht_eq_b⟩ := hu_b
  have hv_b_q'T : v_b ∈ Ideal.span {(q' : T)} := by
    have h1 := Ideal.map_mono
      (Ideal.span_le.mpr fun x hx =>
        Ideal.mem_span_singleton.mpr
          (hq'_dvd x (Finset.mem_coe.mp hx))) hv_b
    rwa [Ideal.map_span, Set.image_singleton] at h1
  obtain ⟨w_b, hw_b_eq⟩ := Ideal.mem_span_singleton.mp hv_b_q'T
  have h_at_b : (a : T) * t_val_b = (q' : T) * ((c_n' : T) - w_b) := by
    have h3 : u_b + v_b = (q' : T) * (c_n' : T) := huv_b.trans hq'c_val
    rw [ht_eq_b, hw_b_eq] at h3
    have h4 := eq_sub_of_add_eq h3
    rw [← mul_sub] at h4
    exact h4
  have ht_b_q'T : ∃ t'_b : T, t_val_b = (q' : T) * t'_b :=
    nzd_element_in_span_prime R q' a hq' hq'a hM_not_assoc t_val_b (by
      rw [h_at_b]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  obtain ⟨t'_b, ht'_b⟩ := ht_b_q'T
  have hc_n'_eq : (c_n' : T) = (a : T) * t'_b + w_b := by
    have h := h_at_b
    rw [ht'_b] at h
    have h' : (q' : T) * ((a : T) * t'_b) = (q' : T) * ((c_n' : T) - w_b) := by
      rw [← h]
      ring
    exact eq_add_of_sub_eq (mul_left_cancel₀ hq'_ne h').symm
  have hw_b_span : w_b ∈ Ideal.map R.carrier.subtype (span (↑rest' : Set R.carrier)) := by
    have hv' := hv_b
    rw [h_ie_b, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton_mul] at hv'
    obtain ⟨z, hz, hq'z⟩ := hv'
    have : z = w_b := mul_left_cancel₀ hq'_ne (hq'z.trans hw_b_eq)
    exact this ▸ hz
  have hc_n'_mem : (c_n' : T) ∈
      Ideal.map R.carrier.subtype (span (↑(insert a rest') : Set R.carrier)) := by
    rw [hc_n'_eq]
    apply add_mem
    · exact Ideal.map_mono
        (Ideal.span_mono
          (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr (Finset.mem_insert_self a rest'))))
        (by rw [Ideal.map_span, Set.image_singleton]
            exact Ideal.mem_span_singleton.mpr ⟨t'_b, rfl⟩)
    · exact Ideal.map_mono
        (Ideal.span_mono (Finset.coe_subset.mpr (Finset.subset_insert a rest'))) hw_b_span
  by_cases ha_rest' : a ∈ rest'
  · have h_eq : insert a rest' = rest' := Finset.insert_eq_of_mem ha_rest'
    rw [h_eq] at hc_n'_mem ⊢
    exact ih R hR_card rest' (Finset.card_image_le.trans (by omega)) c_n' hc_n'_mem
  · by_cases hrest'_card : rest'.card ≤ n'' + 1
    · have h_ins_card : (insert a rest').card ≤ n'' + 1 + 1 := by
        rw [Finset.card_insert_of_notMem ha_rest']
        omega
      exact ih R hR_card (insert a rest') h_ins_card c_n' hc_n'_mem
    · push Not at hrest'_card
      have hrest'_card_eq : rest'.card = n'' + 1 + 1 := by
        have h_le : rest'.card ≤ n'' + 1 + 1 := Finset.card_image_le.trans hrest_card
        omega
      have hb_rest' : div_q_b b ∈ rest' := Finset.mem_image.mpr ⟨b, hb_rest, rfl⟩
      by_cases hdb_zero : div_q_b b = 0
      · have hspan_eq_b : span (↑rest' : Set R.carrier) =
            span (↑(rest'.erase (div_q_b b)) : Set R.carrier) := by
          apply le_antisymm
          · apply Ideal.span_le.mpr
            intro x hx
            rcases eq_or_ne x
                (div_q_b b) with
              rfl | hne
            · rw [hdb_zero]
              exact zero_mem _
            · exact Ideal.subset_span
                (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hx⟩))
          · exact Ideal.span_mono (Finset.coe_subset.mpr (Finset.erase_subset _ _))
        have h_erase_card : (rest'.erase (div_q_b b)).card ≤ n'' + 1 := by
          rw [Finset.card_erase_of_mem hb_rest', hrest'_card_eq]
          omega
        have h_ins_card2 : (insert a (rest'.erase (div_q_b b))).card ≤ n'' + 1 + 1 := by
          rw [Finset.card_insert_of_notMem (fun h => ha_rest' ((Finset.erase_subset _ _) h))]
          omega
        have hc_n'_mem2 : (c_n' : T) ∈ Ideal.map R.carrier.subtype
            (span (↑(insert a (rest'.erase (div_q_b b))) : Set R.carrier)) := by
          have hspan_le : span (↑(insert a rest') : Set R.carrier) ≤
              span (↑(insert a (rest'.erase (div_q_b b))) : Set R.carrier) := by
            apply Ideal.span_le.mpr
            intro x hx
            rw [Finset.mem_coe, Finset.mem_insert] at hx
            rcases hx with hxa | hx'
            · rw [hxa]
              exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
            · rcases eq_or_ne x (div_q_b b)
                with rfl | hne
              · rw [hdb_zero]
                exact zero_mem _
              · exact Ideal.subset_span
                  (Finset.mem_coe.mpr
                    (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hx'⟩)))
          exact Ideal.map_mono hspan_le hc_n'_mem
        obtain ⟨S, hA, hl, hm⟩ :=
          ih R hR_card (insert a (rest'.erase (div_q_b b))) h_ins_card2 c_n' hc_n'_mem2
        exact ⟨S, hA, hl,
          Ideal.map_mono
            (Ideal.span_mono
              (Finset.coe_subset.mpr (Finset.insert_subset_insert _ (Finset.erase_subset _ _))))
            hm⟩
      · by_cases hdb_unit : IsUnit (div_q_b b)
        · refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, ?_⟩
          have h_id : Subring.inclusion (le_refl R.carrier) = RingHom.id R.carrier :=
            RingHom.ext fun x => Subtype.ext rfl
          change (⟨(c_n' : T), le_refl R.carrier c_n'.2⟩ : R.carrier) ∈
            Ideal.map (Subring.inclusion (le_refl R.carrier))
              (span (↑(insert a rest') : Set R.carrier))
          rw [h_id, Ideal.map_id,
            Ideal.eq_top_of_isUnit_mem _
              (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hb_rest')))
              hdb_unit]
          exact Submodule.mem_top
        · -- General: DvdNotUnit, use ih_b
          have hdvd_b : DvdNotUnit (div_q_b b) b :=
            ⟨hdb_zero, ⟨q', hq'.not_unit,
              (hdiv_b b hb_rest).trans (mul_comm q' (div_q_b b))⟩⟩
          have hgcd_rest' : gcdComplexity (insert a rest') ≤ gcdComplexity s := by
            apply le_trans _ hgcd_rest
            unfold gcdComplexity
            rw [Finset.sum_insert ha_rest', Finset.sum_insert ha_rest]
            apply Nat.add_le_add_left
            have hinj_qb : Set.InjOn div_q_b ↑rest :=
              fun x hx y hy hxy => by
                have hx_eq := hdiv_b x (Finset.mem_coe.mp hx)
                have hy_eq := hdiv_b y (Finset.mem_coe.mp hy)
                calc x = q' * div_q_b x := hx_eq
                  _ = q' * div_q_b y := by rw [hxy]
                  _ = y := hy_eq.symm
            exact gcdComplexity_div_le q' hq' rest hq'_dvd div_q_b hdiv_b hinj_qb
          exact ih_b (div_q_b b) hdvd_b rest' hrest'_card_eq.le ha_rest' hb_rest' hgcd_rest'
            c_n' hc_n'_mem


end
