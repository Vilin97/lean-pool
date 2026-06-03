/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.CloseUp.AvoidanceStep
import LeanPool.AndersonConjecture.Jensen.CloseUp.IntersectionHelpers

/-!
# Close-up: intersection theorems

Main intersection-related results for the close-up induction.
When a common prime p divides the generators s' but neither a
nor c, the ideal of s' meets a height-one prime
the close-up
is obtained by passing to an A-extension where the intersection
has been resolved.
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

private def close_up_aux_factor_intersection_proof
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
    {s : Finset R.carrier}
    (hs_gcd : gcdComplexity s ≤ m)
    (rest : Finset R.carrier)
    (hrest_card : rest.card ≤ n'' + 1 + 1)
    (ha_rest : a ∉ rest)
    {b : R.carrier} (hb_rest : b ∈ rest)
    (hgcd_rest : gcdComplexity (insert a rest) ≤ gcdComplexity s)
    {q' : R.carrier} (hq' : Prime q')
    (hq'_dvd : ∀ x ∈ rest, q' ∣ x)
    (hq'_na : ¬q' ∣ a)
    {c_n : R.carrier}
    (_hq'_nc : ¬q' ∣ c_n)
    (hrest_le_q' : span (↑rest : Set R.carrier) ≤ span {q'})
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ a ∧ p ∣ q'))
    (hM_bot : IsLocalRing.maximalIdeal T ≠ ⊥)
    (ha_zero : (a : T) ≠ 0)
    (hc_n : (c_n : T) ∈ Ideal.map R.carrier.subtype
      (span (↑(insert a rest) : Set R.carrier))) : PLift (
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c_n : T), hle c_n.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle)
          (span (↑(insert a rest) : Set R.carrier)) ) := ⟨by
  classical
  -- Derive c_n ∈ span{a, q'}·T
  have hspan_le_aq' : span (↑(insert a rest) : Set R.carrier) ≤ span {a} ⊔ span {q'} := by
    rw [Finset.coe_insert, Ideal.span_insert]
    exact sup_le_sup_left hrest_le_q' _
  have hc_n_aq'T : (c_n : T) ∈ Ideal.span {(a : T), (q' : T)} := by
    have h1 := Ideal.map_mono hspan_le_aq' hc_n
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton,
      Set.image_singleton, ← Ideal.span_insert,
      show insert (R.carrier.subtype a) ({R.carrier.subtype q'} : Set T) =
        {(a : T), (q' : T)} from rfl] at h1
    exact h1
  have hq'_ne : (q' : T) ≠ 0 := by
    intro h
    exact hq'.ne_zero (Subtype.val_injective h)
  -- Apply intersection_close_up
  obtain ⟨S₁, hAext₁, hle₁, x₁, hrem⟩ :=
    intersection_close_up R a q' c_n hc_n_aq'T hcoprime ha_zero hq'_ne hM_bot hM_not_assoc
      hAss_ht hR_card hT_card
  haveI : IsDomain S₁.carrier := NSubring.isDomain S₁
  haveI : UniqueFactorizationMonoid S₁.carrier := S₁.isUFD
  obtain ⟨w, hw_eq⟩ := Ideal.mem_span_singleton.mp hrem
  have hS₁_card : Cardinal.mk S₁.carrier < Cardinal.mk T :=
    lt_of_le_of_lt hAext₁.card_le (max_lt hT_aleph0 hR_card)
  -- Build divided set rest'2 = rest / q'
  let div_q_b2 : R.carrier → R.carrier :=
    fun x => if h : q' ∣ x then Classical.choose h else x
  have hdiv_b2 : ∀ x ∈ rest, x = q' * div_q_b2 x := by
    intro x hx
    simp only [div_q_b2, dif_pos (hq'_dvd x hx)]
    exact Classical.choose_spec (hq'_dvd x hx)
  let rest'2 := rest.image div_q_b2
  have h_ie_b2 : span (↑rest : Set R.carrier) =
      span {q'} * span (↑rest'2 : Set R.carrier) :=
    span_eq_mul_span_image_div q' rest hq'_dvd div_q_b2 hdiv_b2
  have h_ml_b2 : span {q'} * span (↑(insert a rest'2) : Set R.carrier) ≤
      span (↑(insert a rest) : Set R.carrier) :=
    prime_mul_span_insert_le q' a rest div_q_b2 hdiv_b2
  have hc_n_B2 := hc_n
  rw [Finset.coe_insert, Ideal.span_insert, Ideal.map_sup] at hc_n_B2
  obtain ⟨u_b2, hu_b2, v_b2, hv_b2, huv_b2⟩ := Submodule.mem_sup.mp hc_n_B2
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hu_b2
  obtain ⟨t_val_b2, ht_eq_b2⟩ := hu_b2
  have hv_b2_q'T : v_b2 ∈ Ideal.span {(q' : T)} := by
    have h1 := Ideal.map_mono hrest_le_q' hv_b2
    rwa [Ideal.map_span, Set.image_singleton] at h1
  obtain ⟨w_b2, hw_b2_eq⟩ := Ideal.mem_span_singleton.mp hv_b2_q'T
  have hw_b2_span : w_b2 ∈ Ideal.map R.carrier.subtype (span (↑rest'2 : Set R.carrier)) := by
    have hv' := hv_b2
    rw [h_ie_b2, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton_mul] at hv'
    obtain ⟨z, hz, hq'z⟩ := hv'
    have : z = w_b2 := mul_left_cancel₀ hq'_ne (hq'z.trans hw_b2_eq)
    exact this ▸ hz
  -- Cross-ring regularity: a*(x₁ - t_val_b2) ∈ span{q'} → x₁ - t_val_b2 ∈ span{q'}
  have h_eq_T : (a : T) * (↑x₁ : T) + (q' : T) * (↑w : T) =
      (a : T) * t_val_b2 + (q' : T) * w_b2 := by
    have h1 : (c_n : T) = (↑x₁ : T) * (a : T) + (q' : T) * (↑w : T) := by
      have := congr_arg Subtype.val hw_eq
      simp only [Subring.coe_mul, AddSubgroupClass.coe_sub] at this
      linear_combination this
    have h2 : (c_n : T) = (a : T) * t_val_b2 + (q' : T) * w_b2 := by
      have heq := huv_b2
      rw [ht_eq_b2, hw_b2_eq] at heq
      exact heq.symm
    linear_combination h2 - h1
  have h_diff_mem : (a : T) * ((↑x₁ : T) - t_val_b2) ∈ Ideal.span {(q' : T)} := by
    have : (a : T) * ((↑x₁ : T) - t_val_b2) = (q' : T) * (w_b2 - (↑w : T)) := by
      linear_combination h_eq_T
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  obtain ⟨t'_b2, ht'_b2⟩ := nzd_element_in_span_prime R q' a hq' hq'_na hM_not_assoc
    ((↑x₁ : T) - t_val_b2) h_diff_mem
  have hw_decomp : (↑w : T) = w_b2 - (a : T) * t'_b2 := by
    have h1 : (q' : T) * (w_b2 - (↑w : T)) = (a : T) * ((↑x₁ : T) - t_val_b2) := by
      linear_combination -h_eq_T
    rw [ht'_b2] at h1
    have h2 : (q' : T) * (w_b2 - (↑w : T)) = (q' : T) * ((a : T) * t'_b2) := by
      linear_combination h1
    have h3 : w_b2 - (↑w : T) = (a : T) * t'_b2 := mul_left_cancel₀ hq'_ne h2
    linear_combination -h3
  -- w ∈ span(insert a rest'2)·T
  have hw_mem_T : (↑w : T) ∈
      Ideal.map R.carrier.subtype (span (↑(insert a rest'2) : Set R.carrier)) := by
    rw [hw_decomp]
    apply sub_mem
    · exact Ideal.map_mono
        (Ideal.span_mono (Finset.coe_subset.mpr (Finset.subset_insert a rest'2))) hw_b2_span
    · exact Ideal.map_mono
        (Ideal.span_mono
          (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr (Finset.mem_insert_self a rest'2))))
        (by rw [Ideal.map_span, Set.image_singleton]
            exact Ideal.mem_span_singleton.mpr ⟨t'_b2, rfl⟩)
  suffices h_suff_main : ∃ S₂ : NSubring T, IsAExtension S₁ S₂ ∧
      ∃ (hle₂ : S₁.carrier ≤ S₂.carrier), (⟨(↑w : T), hle₂ w.2⟩ : S₂.carrier) ∈
        Ideal.map (Subring.inclusion hle₂)
          (Ideal.map (Subring.inclusion hle₁) (span (↑(insert a rest'2) : Set R.carrier))) by
    obtain ⟨S₂, hAext₂, hle₂, hw_S₂⟩ := h_suff_main
    have hle_comp : R.carrier ≤ S₂.carrier := le_trans hle₁ hle₂
    refine ⟨S₂, isAExtension_trans' hAext₁ hAext₂, hle_comp, ?_⟩
    have hc_n_eq : (⟨(c_n : T), hle_comp c_n.2⟩ : S₂.carrier) =
        ⟨(↑x₁ : T), hle₂ x₁.2⟩ * ⟨(a : T), hle_comp a.2⟩ +
        ⟨(q' : T), hle_comp q'.2⟩ * ⟨(↑w : T), hle₂ w.2⟩ := by
      ext
      simp only [Subring.coe_mul, Subring.coe_add]
      have := congr_arg Subtype.val hw_eq
      simp only [Subring.coe_mul, AddSubgroupClass.coe_sub] at this
      linear_combination this
    rw [hc_n_eq]
    apply add_mem
    · apply Ideal.mul_mem_left
      exact Ideal.map_mono
        (Ideal.span_mono
          (Set.singleton_subset_iff.mpr (Finset.mem_coe.mpr (Finset.mem_insert_self a rest))))
        (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl))
    · have hw_comp : (⟨(↑w : T), hle₂ w.2⟩ : S₂.carrier) ∈
          Ideal.map (Subring.inclusion hle_comp)
            (span (↑(insert a rest'2) : Set R.carrier)) := by
        rw [show Subring.inclusion hle_comp =
          (Subring.inclusion hle₂).comp (Subring.inclusion hle₁) from
          RingHom.ext fun _ => rfl, ← Ideal.map_map]
        exact hw_S₂
      have hmul := Ideal.mul_mem_mul
        (Ideal.mem_map_of_mem (Subring.inclusion hle_comp)
          (Ideal.subset_span (show q' ∈ ({q'} : Set R.carrier) from rfl))) hw_comp
      rw [← Ideal.map_mul] at hmul
      exact Ideal.map_mono h_ml_b2 hmul
  by_cases ha_rest'2 : a ∈ rest'2
  · -- a ∈ rest'2: insert = rest'2
    have h_eq2 : insert a rest'2 = rest'2 := Finset.insert_eq_of_mem ha_rest'2
    rw [h_eq2] at hw_mem_T ⊢
    have hrest'2_card : rest'2.card ≤ n'' + 1 + 1 := Finset.card_image_le.trans hrest_card
    let liftR₁ := Subring.inclusion hle₁
    let s₁ := rest'2.image liftR₁
    have hs₁_card : s₁.card ≤ n'' + 1 + 1 := Finset.card_image_le.trans hrest'2_card
    have hw_s₁ : (↑w : T) ∈
        Ideal.map S₁.carrier.subtype (span (↑s₁ : Set S₁.carrier)) := by
      change (↑w : T) ∈ Ideal.map S₁.carrier.subtype
        (span (↑(rest'2.image liftR₁) : Set S₁.carrier))
      rw [Finset.coe_image, ← Ideal.map_span, Ideal.map_map,
        show S₁.carrier.subtype.comp liftR₁ = R.carrier.subtype from
          RingHom.ext fun _ => rfl]
      exact hw_mem_T
    obtain ⟨S₂, hAext₂, hle₂, hw_S₂⟩ := ih S₁ hS₁_card s₁ hs₁_card w hw_s₁
    refine ⟨S₂, hAext₂, hle₂, ?_⟩
    convert hw_S₂ using 1
    congr 1
    rw [Ideal.map_span, ← Finset.coe_image]
  · -- a ∉ rest'2
    by_cases hrest'2_card : rest'2.card ≤ n'' + 1
    · have h_ins_card3 : (insert a rest'2).card ≤ n'' + 1 + 1 := by
        rw [Finset.card_insert_of_notMem ha_rest'2]
        omega
      let liftR₁ := Subring.inclusion hle₁
      let s₁ := (insert a rest'2).image liftR₁
      have hs₁_card : s₁.card ≤ n'' + 1 + 1 := Finset.card_image_le.trans h_ins_card3
      have hw_s₁ : (↑w : T) ∈
          Ideal.map S₁.carrier.subtype (span (↑s₁ : Set S₁.carrier)) := by
        change (↑w : T) ∈ Ideal.map S₁.carrier.subtype
          (span (↑((insert a rest'2).image liftR₁) : Set S₁.carrier))
        rw [Finset.coe_image, ← Ideal.map_span, Ideal.map_map,
          show S₁.carrier.subtype.comp liftR₁ = R.carrier.subtype from
            RingHom.ext fun _ => rfl]
        exact hw_mem_T
      obtain ⟨S₂, hAext₂, hle₂, hw_S₂⟩ := ih S₁ hS₁_card s₁ hs₁_card w hw_s₁
      refine ⟨S₂, hAext₂, hle₂, ?_⟩
      convert hw_S₂ using 1
      congr 1
      rw [Ideal.map_span, ← Finset.coe_image]
    · -- rest'2.card = n''+2
      push Not at hrest'2_card
      have hrest'2_card_eq : rest'2.card = n'' + 1 + 1 := by
        have h_le : rest'2.card ≤ n'' + 1 + 1 :=
          Finset.card_image_le.trans hrest_card
        omega
      have hb_rest'2 : div_q_b2 b ∈ rest'2 :=
        Finset.mem_image.mpr ⟨b, hb_rest, rfl⟩
      exact close_up_aux_factor_intersection_large
        n'' ih m ih_m hs_gcd rest hrest_card ha_rest hb_rest hgcd_rest
        hq' hq'_dvd hAext₁ hle₁ hS₁_card w
        div_q_b2 hdiv_b2 rest'2 rfl h_ml_b2 hw_mem_T
        ha_rest'2 hrest'2_card_eq hb_rest'2
⟩

theorem close_up_aux_factor_intersection
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
    {s : Finset R.carrier}
    (hs_gcd : gcdComplexity s ≤ m)
    (rest : Finset R.carrier)
    (hrest_card : rest.card ≤ n'' + 1 + 1)
    (ha_rest : a ∉ rest)
    {b : R.carrier} (hb_rest : b ∈ rest)
    (hgcd_rest : gcdComplexity (insert a rest) ≤ gcdComplexity s)
    {q' : R.carrier} (hq' : Prime q')
    (hq'_dvd : ∀ x ∈ rest, q' ∣ x)
    (hq'_na : ¬q' ∣ a)
    {c_n : R.carrier}
    (_hq'_nc : ¬q' ∣ c_n)
    (hrest_le_q' : span (↑rest : Set R.carrier) ≤ span {q'})
    (hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ a ∧ p ∣ q'))
    (hM_bot : IsLocalRing.maximalIdeal T ≠ ⊥)
    (ha_zero : (a : T) ≠ 0)
    (hc_n : (c_n : T) ∈ Ideal.map R.carrier.subtype
      (span (↑(insert a rest) : Set R.carrier))) :
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c_n : T), hle c_n.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle)
          (span (↑(insert a rest) : Set R.carrier)) := by
  exact
    (close_up_aux_factor_intersection_proof
      (R := R) (a := a) (s := s) (b := b) (q' := q') (c_n := c_n) hM_not_assoc hAss_ht
      hT_card hT_aleph0 n'' ih m ih_m hR_card hs_gcd rest hrest_card ha_rest hb_rest
      hgcd_rest hq' hq'_dvd hq'_na _hq'_nc hrest_le_q' hcoprime hM_bot ha_zero hc_n
    ).down
theorem close_up_aux_factor_no_factor
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
    (rest : Finset R.carrier)
    (hrest_card : rest.card ≤ n'' + 1 + 1)
    (ha_rest : a ∉ rest)
    {b : R.carrier} (hb_rest : b ∈ rest)
    (hgcd_rest : gcdComplexity (insert a rest) ≤ gcdComplexity s)
    {c_n : R.carrier}
    (h_factor : ∀ (q' : R.carrier), Prime q' →
      (∀ x ∈ rest, q' ∣ x) → ¬q' ∣ a ∧ ¬q' ∣ c_n)
    (hc_n : (c_n : T) ∈ Ideal.map R.carrier.subtype
      (span (↑(insert a rest) : Set R.carrier))) :
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c_n : T), hle c_n.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle)
          (span (↑(insert a rest) : Set R.carrier)) := by
  classical
  by_cases h_common :
      ∃ q' : R.carrier, Prime q' ∧
        ∀ x ∈ rest, q' ∣ x
  · -- common prime q divides all of rest, but q ∤ a and q ∤ c_n (from h_factor)
    obtain ⟨q', hq', hq'_dvd⟩ := h_common
    have hq'_na_nc := h_factor q' hq' hq'_dvd
    have hq'_na : ¬q' ∣ a := hq'_na_nc.1
    have hq'_nc : ¬q' ∣ c_n := hq'_na_nc.2
    have hrest_le_q' : span (↑rest : Set R.carrier) ≤ span {q'} := by
      apply Ideal.span_le.mpr
      intro x hx
      exact Ideal.mem_span_singleton.mpr (hq'_dvd x (Finset.mem_coe.mp hx))
    have hspan_le_aq' : span (↑(insert a rest) : Set R.carrier) ≤ span {a} ⊔ span {q'} := by
      rw [Finset.coe_insert, Ideal.span_insert]
      exact sup_le_sup_left hrest_le_q' _
    have hc_n_aq'T : (c_n : T) ∈ Ideal.span {(a : T), (q' : T)} := by
      have h1 := Ideal.map_mono hspan_le_aq' hc_n
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton,
        Set.image_singleton, ← Ideal.span_insert,
        show insert (R.carrier.subtype a) ({R.carrier.subtype q'} : Set T) =
          {(a : T), (q' : T)} from rfl] at h1
      exact h1
    have hcoprime : ∀ p : R.carrier, Prime p → ¬(p ∣ a ∧ p ∣ q') := by
      intro p hp ⟨hpa, hpq'⟩
      have hassoc : Associated p q' := (hp.dvd_prime_iff_associated hq').mp hpq'
      exact hq'_na (hassoc.symm.dvd.trans hpa)
    by_cases hM_bot : IsLocalRing.maximalIdeal T = ⊥
    · -- T is a field (M = ⊥): R is also a field,
      exfalso
      have hq'_unit : IsUnit q' := by
        by_contra h
        have hmem := (IsLocalRing.mem_maximalIdeal _).mpr h
        rw [R.maximal_ideal_eq, Ideal.mem_comap, hM_bot, Submodule.mem_bot] at hmem
        exact hq'.ne_zero (Subtype.val_injective hmem)
      exact hq'.not_unit hq'_unit
    · -- M ≠ ⊥: use intersection_close_up
      by_cases ha_zero : (a : T) = 0
      · have ha_zero_R : a = 0 := by
          exact Subtype.val_injective ha_zero
        have hc_n_rest : (c_n : T) ∈
            Ideal.map R.carrier.subtype (span (↑rest : Set R.carrier)) := by
          have hle_span : span (↑(insert a rest) : Set R.carrier) ≤
              span (↑rest : Set R.carrier) := by
            apply Ideal.span_le.mpr
            intro x hx
            rw [Finset.mem_coe, Finset.mem_insert] at hx
            rcases hx with rfl | hx'
            · rw [ha_zero_R]
              exact zero_mem _
            · exact Ideal.subset_span (Finset.mem_coe.mpr hx')
          exact Ideal.map_mono hle_span hc_n
        obtain ⟨S, hAext, hle, hmem⟩ := ih R hR_card rest hrest_card c_n hc_n_rest
        exact ⟨S, hAext, hle,
          Ideal.map_mono
            (Ideal.span_mono (Finset.coe_subset.mpr (Finset.subset_insert a rest))) hmem⟩
      · -- a ≠ 0 and M ≠ ⊥: main case
        exact close_up_aux_factor_intersection
          hM_not_assoc hAss_ht hT_card hT_aleph0 n'' ih m ih_m
          hR_card hs_gcd rest hrest_card ha_rest hb_rest hgcd_rest
          hq' hq'_dvd hq'_na hq'_nc hrest_le_q' hcoprime hM_bot ha_zero
          hc_n
  · -- Negative case: no common prime divides all of rest
    have h_no_common : ∀ (q : R.carrier), Prime q →
        ¬(∀ x ∈ rest, q ∣ x) := by
      intro q hq hall
      exact h_common ⟨q, hq, hall⟩
    have hc_n' : (c_n : T) ∈
        Ideal.map R.carrier.subtype (span (insert (a : R.carrier) (↑rest : Set R.carrier))) := by
      rw [← Finset.coe_insert]
      exact hc_n
    obtain ⟨S, hAext, hle, hmem⟩ :=
      close_up_avoidance_step hM_not_assoc hAss_ht ih R hR_card hT_card hT_aleph0 a rest
        hrest_card c_n hc_n' h_no_common
    exact ⟨S, hAext, hle, by
      rw [Finset.coe_insert]
      exact hmem⟩


end
