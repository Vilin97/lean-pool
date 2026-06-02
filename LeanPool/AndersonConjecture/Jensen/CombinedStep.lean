/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Adjoin.Adjoin
import LeanPool.AndersonConjecture.Jensen.CloseUp.CloseUp
import LeanPool.AndersonConjecture.Jensen.TransfiniteUnion

/-!
# Combined Construction Step

Given an N-subring R, produce an A-extension S lifting a given
element of T/M² and meeting a given nonzero prime, while closing
all finitely generated ideals (Heitmann, 1993, Lemma 7).
-/

noncomputable section

open Cardinal Ideal

universe u
variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/- Transitivity of A-extensions: if R → S and S → U are A-extensions, so is R → U. -/
include T in theorem isAExtension_trans {R S U : NSubring T}
    (h₁ : IsAExtension R S) (h₂ : IsAExtension S U) : IsAExtension R U where
  le := le_trans h₁.le h₂.le
  -- Primality lifts through each link of the chain R ≤ S ≤ U
  primes_preserved r hr :=
    h₂.primes_preserved ⟨r.1, h₁.le r.2⟩ (h₁.primes_preserved r hr)
  card_le := by
    -- max(ℵ₀, #U) ≤ max(ℵ₀, max(ℵ₀, #R)) = max(ℵ₀, #R) by idempotence
    calc Cardinal.mk U.carrier
        ≤ max Cardinal.aleph0 (Cardinal.mk S.carrier) := h₂.card_le
      _ ≤ max Cardinal.aleph0 (max Cardinal.aleph0 (Cardinal.mk R.carrier)) :=
          max_le_max_left _ h₁.card_le
      _ = max Cardinal.aleph0 (Cardinal.mk R.carrier) := by
          rw [← max_assoc, max_self]

include T in lemma card_lt_of_aext' (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    {A B : NSubring T} (hAB : IsAExtension A B)
    (hA : Cardinal.mk A.carrier < Cardinal.mk T) :
    Cardinal.mk B.carrier < Cardinal.mk T :=
  lt_of_le_of_lt hAB.card_le (max_lt hT_aleph0 hA)

/- Build an NSubring from a chain with explicit carrier = unionSubring.
Unlike `transfinite_union_isNSubring`, the carrier is accessible (not opaque via .choose). -/
include T in theorem build_union_isNSubring
    {ι' : Type u} [LinearOrder ι'] [Nonempty ι']
    (chain : NSubringChain T ι')
    (h_card : ∀ (α : ι'),
      Cardinal.mk (chain.ring α).carrier ≤
        max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)))
    (h_ι_card : Cardinal.mk ι' ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))) :
    ∃ (S : NSubring T),
      S.carrier = chain.unionSubring ∧
      (∀ (α : ι'), (chain.ring α).carrier ≤ S.carrier) := by
  set U := chain.unionSubring
  have hU_le : ∀ α, (chain.ring α).carrier ≤ U := chain.le_union
  have hU_mem : ∀ x : U, ∃ α, (x : T) ∈ (chain.ring α).carrier :=
    fun x => chain.mem_union_iff.mp x.2
  -- Locality of the union: each element lives in some chain.ring α, which is local
  haveI hU_local : IsLocalRing U := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro a
    obtain ⟨α, hα⟩ := hU_mem a
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      (⟨(a : T), hα⟩ : (chain.ring α).carrier) with hu | hu
    · left
      exact hu.map (Subring.inclusion (hU_le α))
    · right
      exact (show Subring.inclusion (hU_le α) (1 - ⟨(a : T), hα⟩) = 1 - a
        from Subtype.ext rfl) ▸ hu.map (Subring.inclusion (hU_le α))
  -- UFD, locality established; now verify card bound, maximal ideal, and height bound
  refine ⟨⟨U, transfinite_union_isUFD chain U hU_le hU_mem, hU_local, ?_, ?_, ?_⟩,
    rfl, hU_le⟩
  · -- Cardinality: #U ≤ #ι' · sup_α(#R_α) ≤ κ² ≤ κ
    set κ := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
    have hU_eq : (U : Set T) = ⋃ α, ↑(chain.ring α).carrier :=
      Subring.coe_iSup_of_directed chain.directed_carriers
    have h1 : Cardinal.mk U ≤ Cardinal.mk ι' *
        ⨆ α, Cardinal.mk ↑((chain.ring α).carrier : Set T) := by
      have := Cardinal.mk_iUnion_le (fun α => ((chain.ring α).carrier : Set T))
      rwa [← hU_eq] at this
    have h2 : ⨆ α, Cardinal.mk ↑((chain.ring α).carrier : Set T) ≤ κ :=
      ciSup_le fun α => h_card α
    calc Cardinal.mk U ≤ Cardinal.mk ι' * κ := le_trans h1 (mul_le_mul_right h2 _)
      _ ≤ κ * κ := mul_le_mul_left h_ι_card κ
      _ ≤ max κ κ := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
      _ = κ := max_self κ
  · -- Maximal ideal of U = pullback of maximal ideal of T
    ext ⟨a, ha⟩
    simp only [Ideal.mem_comap, Subring.coe_subtype]
    constructor
    · -- (⊆) Non-unit in U implies non-unit at some stage R_α, hence in M_T
      intro hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu_T
      obtain ⟨α, hα⟩ := hU_mem ⟨a, ha⟩
      by_contra h_nu
      have : ¬IsUnit (⟨a, hα⟩ : (chain.ring α).carrier) :=
        fun hu => h_nu ((IsLocalRing.mem_maximalIdeal _).mp hx
          (hu.map (Subring.inclusion (hU_le α))))
      have hmem := (IsLocalRing.mem_maximalIdeal _).mpr this
      rw [(chain.ring α).maximal_ideal_eq] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem) hu_T
    · -- (⊇) Non-unit in T is non-unit in any subring
      intro hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu_S
      exact (IsLocalRing.mem_maximalIdeal _).mp hx (hu_S.map U.subtype)
  · -- Height bound: any prime of U lying over (t) has height ≤ 1
    intro t ht P hP
    have hP_prime := hP.isPrime
    haveI : (Ideal.comap U.subtype P).IsPrime := hP_prime.comap _
    change (Ideal.comap U.subtype P).height ≤ ↑(1 : ℕ)
    -- Suffices to show every prime q ⊊ P∩U is zero
    rw [Ideal.height_le_iff]
    intro q hq_prime hq_lt
    suffices q = ⊥ by rw [this, Ideal.height_bot]
                      norm_cast
    by_contra hq_ne
    -- Pick nonzero s ∈ q and x ∈ P \ q
    obtain ⟨s, hs_q, hs_ne⟩ : ∃ s : U, s ∈ q ∧ s ≠ 0 := by
      by_contra h
      push Not at h
      exact hq_ne ((Submodule.eq_bot_iff q).mpr fun x hx => h x hx)
    obtain ⟨x, hx_P, hx_nq⟩ := Set.exists_of_ssubset hq_lt
    -- Pull s and x back to a common stage γ = max(αs, αx)
    obtain ⟨αs, hαs⟩ := hU_mem s
    obtain ⟨αx, hαx⟩ := hU_mem x
    set γ := max αs αx
    set inclγ := Subring.inclusion (hU_le γ)
    haveI : (Ideal.comap inclγ q).IsPrime := hq_prime.comap _
    set s' : (chain.ring γ).carrier := ⟨(s : T), chain.mono (le_max_left ..) hαs⟩
    have hs'_ne : s' ≠ 0 := fun h => hs_ne (Subtype.ext (congrArg
      (fun (x : (chain.ring γ).carrier) => (x : T)) h))
    have hs'_q : s' ∈ Ideal.comap inclγ q :=
      show inclγ s' ∈ q from (show inclγ s' = s from Subtype.ext rfl) ▸ hs_q
    have hq'_ne : Ideal.comap inclγ q ≠ ⊥ := fun h => by
      rw [h] at hs'_q
      exact hs'_ne (Ideal.mem_bot.mp hs'_q)
    set x' : (chain.ring γ).carrier :=
      ⟨(x : T), chain.mono (le_max_right ..) hαx⟩
    have hx'_nq : x' ∉ Ideal.comap inclγ q := fun h => by
      have h' : inclγ x' ∈ q := h
      rw [show inclγ x' = x from Subtype.ext rfl] at h'
      exact hx_nq h'
    -- At stage γ the pullback of q is a nonzero prime strictly below P∩R_γ
    have hq'_lt : Ideal.comap inclγ q <
        Ideal.comap (chain.ring γ).carrier.subtype P :=
      lt_of_le_of_ne
        (fun r hr => (hq_lt.le (show inclγ r ∈ q from hr) : (inclγ r : T) ∈ P))
        (fun h => hx'_nq (h ▸ (hx_P : (x : T) ∈ P)))
    haveI : (Ideal.comap (chain.ring γ).carrier.subtype P).IsPrime := hP_prime.comap _
    -- R_γ is an NSubring so ht(P∩R_γ) ≤ 1, forcing ht(q∩R_γ) = 0, contradicting q ≠ 0
    have hq'_ht := (Ideal.height_le_iff (n := 1)).mp
      ((chain.ring γ).height_bound t ht P hP) _ inferInstance hq'_lt
    haveI : IsDomain (chain.ring γ).carrier := inferInstance
    exact absurd ((Ideal.height_le_iff (n := 0)).mp (by
      lift (Ideal.comap inclγ q).height to ℕ using ne_top_of_lt hq'_ht with n hn
      simp only [Nat.cast_lt] at hq'_ht
      simp only [Nat.cast_le]
      omega
    ) ⊥ Ideal.isPrime_bot (bot_lt_iff_ne_bot.mpr hq'_ne)) not_lt_bot

/- Process one (gens, c) pair: given NSubring Sk with R' ≤ Sk and #Sk < #T,
produce an A-extension Sk1 that closes the pair if c ∈ I·T. -/
include T in private theorem close_up_all_mk_next
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (R' Sk : NSubring T) (hCk : Cardinal.mk Sk.carrier < Cardinal.mk T)
    (hle_k : R'.carrier ≤ Sk.carrier)
    (gens : Finset R'.carrier) (c_R' : R'.carrier) :
    ∃ (Sk1 : NSubring T), IsAExtension Sk Sk1 ∧
      Cardinal.mk Sk1.carrier < Cardinal.mk T ∧
      R'.carrier ≤ Sk1.carrier ∧
      ((c_R' : T) ∈ Ideal.map R'.carrier.subtype (Ideal.span ↑gens) →
        ∃ (hle : R'.carrier ≤ Sk1.carrier),
          (⟨(c_R' : T), hle c_R'.2⟩ : Sk1.carrier) ∈
            Ideal.map (Subring.inclusion hle) (Ideal.span ↑gens)) := by
  haveI : DecidableEq Sk.carrier := Classical.decEq _
  -- Reindex the generators from R' into Sk via the inclusion R' ≤ Sk
  set inclR'Sk := Subring.inclusion hle_k
  set I_Sk := Ideal.span (↑(gens.image inclR'Sk) : Set Sk.carrier)
  set c_Sk : Sk.carrier := ⟨(c_R' : T), hle_k c_R'.2⟩
  have hI_eq : I_Sk = Ideal.map inclR'Sk (Ideal.span ↑gens) := by
    simp only [I_Sk, Ideal.map_span, Finset.coe_image]
  -- Split on whether c actually belongs to I·T; if not, Sk itself works
  by_cases hcond : (c_R' : T) ∈ Ideal.map R'.carrier.subtype (Ideal.span ↑gens)
  · -- c ∈ I·T: apply close_up to produce Sk₊₁ catching c into the extended ideal
    have hc_Sk : (c_Sk : T) ∈ Ideal.map Sk.carrier.subtype I_Sk := by
      rw [hI_eq, Ideal.map_map,
        show Sk.carrier.subtype.comp inclR'Sk = R'.carrier.subtype from
          RingHom.ext fun _ => rfl]
      exact hcond
    obtain ⟨S', hAext', hle', hc'⟩ := close_up Sk I_Sk ⟨_, rfl⟩ c_Sk hc_Sk
      hM_not_assoc hAss_ht hCk hT_card hT_aleph0
    refine ⟨S', hAext', card_lt_of_aext' hT_aleph0 hAext' hCk,
      le_trans hle_k hAext'.le, fun _ => ⟨le_trans hle_k hAext'.le, ?_⟩⟩
    have hmm : Ideal.map (Subring.inclusion hle') I_Sk =
        Ideal.map (Subring.inclusion (le_trans hle_k hAext'.le)) (Ideal.span ↑gens) := by
      rw [hI_eq, Ideal.map_map]
      congr 1
    rw [hmm] at hc'
    exact hc'
  · -- c ∉ I·T: vacuously satisfied; Sk is already the desired A-extension
    exact ⟨Sk, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, hCk, hle_k,
      fun h => absurd h hcond⟩

/- Cardinality bound for a union of NSubrings in a chain. -/
-- #(⋃_α R_α) ≤ #ι · sup(#R_α) ≤ κ² = κ where κ = max(ℵ₀, #R')
include T in private theorem union_card_le_max
    {ι : Type u} [LinearOrder ι] [Nonempty ι]
    (R' : NSubring T)
    (chain : NSubringChain T ι)
    (hι_card : Cardinal.mk ι ≤ max Cardinal.aleph0 (Cardinal.mk R'.carrier))
    (hfq_card : ∀ (α : ι),
        Cardinal.mk (chain.ring α).carrier ≤ max Cardinal.aleph0 (Cardinal.mk R'.carrier)) :
    Cardinal.mk chain.unionSubring ≤ max Cardinal.aleph0 (Cardinal.mk R'.carrier) := by
  set κ := max Cardinal.aleph0 (Cardinal.mk R'.carrier)
  have hU_eq : (chain.unionSubring : Set T) =
      ⋃ α, ↑(chain.ring α).carrier :=
    Subring.coe_iSup_of_directed chain.directed_carriers
  have h1 := Cardinal.mk_iUnion_le
    (fun (α : ι) => ((chain.ring α).carrier : Set T))
  rw [← hU_eq] at h1
  calc Cardinal.mk chain.unionSubring
      ≤ Cardinal.mk ι *
        (⨆ α, Cardinal.mk ↑((chain.ring α).carrier : Set T)) := h1
    _ ≤ κ * κ := mul_le_mul' hι_card (ciSup_le fun α => hfq_card α)
    _ ≤ max κ κ := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
    _ = κ := max_self κ

/-- Build the transfinite recursion and prove its invariant for close_up_all. -/
private def close_up_all_one_pass_aux_proof
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (R' : NSubring T) (hR' : Cardinal.mk R'.carrier < Cardinal.mk T) : PLift (
    ∃ S : NSubring T, IsAExtension R' S ∧ Cardinal.mk S.carrier < Cardinal.mk T ∧
      (∀ (I : Ideal R'.carrier) (_ : I.FG) (c : R'.carrier),
        (c : T) ∈ Ideal.map R'.carrier.subtype I →
        ∃ (hle : R'.carrier ≤ S.carrier),
          (⟨(c : T), hle c.2⟩ : S.carrier) ∈
            Ideal.map (Subring.inclusion hle) I) ) := ⟨by
  -- Instantiate the one-step close-up lemma for R'
  have mk_next := close_up_all_mk_next hM_not_assoc hAss_ht hT_card hT_aleph0 R'
  -- Index the transfinite recursion by pairs (generators, element) from R'
  set Pairs := Finset R'.carrier × R'.carrier with Pairs_def
  haveI cdec : ∀ (p : Prop), Decidable p := Classical.propDecidable
  letI pairLO : LinearOrder Pairs := IsWellOrder.linearOrder WellOrderingRel
  letI pairWF : WellFoundedLT Pairs := ⟨WellOrderingRel.isWellOrder.wf⟩
  -- #Pairs ≤ max(ℵ₀, #R'): for infinite R', #(Finset R' × R') = #R'
  have hPairs_card : Cardinal.mk Pairs ≤ max Cardinal.aleph0 (Cardinal.mk R'.carrier) := by
    by_cases hfin : Finite R'.carrier
    · exact le_trans Cardinal.mk_le_aleph0 (le_max_left ..)
    · haveI : Infinite R'.carrier := not_finite_iff_infinite.mp hfin
      change Cardinal.mk (Finset R'.carrier × R'.carrier) ≤ _
      calc Cardinal.mk (Finset R'.carrier × R'.carrier)
          ≤ Cardinal.mk R'.carrier * Cardinal.mk R'.carrier := by
            rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
            gcongr
            exact Cardinal.mk_finset_of_infinite R'.carrier ▸ le_rfl
        _ = Cardinal.mk R'.carrier := Cardinal.mul_eq_self
            (Cardinal.aleph0_le_mk R'.carrier)
        _ ≤ max Cardinal.aleph0 (Cardinal.mk R'.carrier) := le_max_right ..
  have hPairs_card_res : Cardinal.mk Pairs ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) :=
    le_trans hPairs_card (max_le (le_max_left ..) R'.card_le)
  let build_union := @build_union_isNSubring T _ _ _ _
  -- Define f by well-founded recursion: f(p) closes the pair p over the union of all f(q), q < p
  let f : Pairs → NSubring T := WellFounded.fix pairWF.wf (fun p IH =>
    if hmono : ∀ q₁ q₂ (h₁ : q₁ < p) (h₂ : q₂ < p), q₁ ≤ q₂ →
        (IH q₁ h₁).carrier ≤ (IH q₂ h₂).carrier then
      if hprimes : ∀ q₁ q₂ (h₁ : q₁ < p) (h₂ : q₂ < p) (h12 : q₁ ≤ q₂)
          (r : (IH q₁ h₁).carrier), Prime r →
          Prime (⟨r.1, hmono q₁ q₂ h₁ h₂ h12 r.2⟩ : (IH q₂ h₂).carrier) then
        if hrest : (∀ q (hq : q < p), R'.carrier ≤ (IH q hq).carrier) ∧
            (∀ q (hq : q < p),
              Cardinal.mk (IH q hq).carrier ≤
                max Cardinal.aleph0 (Cardinal.mk R'.carrier)) ∧
            (∀ q (hq : q < p),
              Cardinal.mk (IH q hq).carrier < Cardinal.mk T) then
          -- If p has predecessors, take their union, then close the pair over it
          if hne : ∃ q, q < p then
            haveI : Nonempty {q // q < p} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
            let ichain : NSubringChain T {q // q < p} :=
              { ring := fun x => IH x.1 x.2
                mono := fun x y h12 => hmono x.1 y.1 x.2 y.2 h12
                primes_preserved := fun x y h12 => hprimes x.1 y.1 x.2 y.2 h12 }
            let prevNSub := (build_union ichain
              (fun (x : {q // q < p}) =>
                le_trans (hrest.2.1 x.1 x.2) (max_le (le_max_left ..) R'.card_le))
              (le_trans (Cardinal.mk_subtype_le _) hPairs_card_res)).choose
            let hprev_spec := (build_union ichain
              (fun (x : {q // q < p}) =>
                le_trans (hrest.2.1 x.1 x.2) (max_le (le_max_left ..) R'.card_le))
              (le_trans (Cardinal.mk_subtype_le _) hPairs_card_res)).choose_spec
            let hprev_card : Cardinal.mk prevNSub.carrier < Cardinal.mk T := by
              rw [hprev_spec.1]
              exact lt_of_le_of_lt
                (union_card_le_max R' ichain
                  (le_trans (Cardinal.mk_subtype_le _) hPairs_card)
                  (fun α => hrest.2.1 α.1 α.2))
                (max_lt hT_aleph0 hR')
            let hprev_le : R'.carrier ≤ prevNSub.carrier :=
              le_trans (hrest.1 hne.choose hne.choose_spec)
                (hprev_spec.2 ⟨hne.choose, hne.choose_spec⟩)
            (mk_next prevNSub hprev_card hprev_le p.1 p.2).choose
          else
            -- p is the minimum element: close the pair starting from R' itself
            (mk_next R' hR' (le_refl _) p.1 p.2).choose
        else R'
      else R'
    else R')
  -- Invariant: each f(p) extends R', has controlled cardinality, and closes pair p
  have hGood : ∀ p : Pairs,
      (∃ (hle : R'.carrier ≤ (f p).carrier),
        ∀ (r : R'.carrier), Prime r → Prime (⟨r.1, hle r.2⟩ : (f p).carrier)) ∧
      Cardinal.mk (f p).carrier ≤ max Cardinal.aleph0 (Cardinal.mk R'.carrier) ∧
      (∀ q (hq : q < p), ∃ (hle : (f q).carrier ≤ (f p).carrier),
        ∀ (r : (f q).carrier), Prime r →
          Prime (⟨r.1, hle r.2⟩ : (f p).carrier)) ∧
      ((p.2 : T) ∈ Ideal.map R'.carrier.subtype (Ideal.span ↑p.1) →
        ∃ (hle : R'.carrier ≤ (f p).carrier),
          (⟨(p.2 : T), hle p.2.2⟩ : (f p).carrier) ∈
            Ideal.map (Subring.inclusion hle) (Ideal.span ↑p.1)) := by
    intro p
    induction p using pairWF.wf.induction with
    | h p IHGood =>
    have hfq_R'_le : ∀ q (hq : q < p), R'.carrier ≤ (f q).carrier :=
      fun q hq => (IHGood q hq).1.choose
    have hfq_R'_primes : ∀ q (hq : q < p) (r : R'.carrier), Prime r →
        Prime (⟨r.1, (hfq_R'_le q hq) r.2⟩ : (f q).carrier) := by
      intro q hq r hr
      exact (IHGood q hq).1.choose_spec r hr
    have hfq_card : ∀ q (hq : q < p),
        Cardinal.mk (f q).carrier ≤ max Cardinal.aleph0 (Cardinal.mk R'.carrier) :=
      fun q hq => (IHGood q hq).2.1
    have hfq_card_res : ∀ q (hq : q < p),
        Cardinal.mk (f q).carrier ≤
          max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) :=
      fun q hq => le_trans (hfq_card q hq) (max_le (le_max_left ..) R'.card_le)
    have hfq_card_lt : ∀ q (hq : q < p),
        Cardinal.mk (f q).carrier < Cardinal.mk T :=
      fun q hq => lt_of_le_of_lt (hfq_card q hq) (max_lt hT_aleph0 hR')
    have hfq_mono : ∀ q₁ q₂ (h₁ : q₁ < p) (h₂ : q₂ < p), q₁ ≤ q₂ →
        (f q₁).carrier ≤ (f q₂).carrier := by
      intro q₁ q₂ h₁ h₂ h12
      rcases eq_or_lt_of_le h12 with rfl | hlt
      · exact le_refl _
      · exact ((IHGood q₂ h₂).2.2.1 q₁ hlt).choose
    have hfq_primes : ∀ q₁ q₂ (h₁ : q₁ < p) (h₂ : q₂ < p) (h12 : q₁ ≤ q₂)
        (r : (f q₁).carrier), Prime r →
        Prime (⟨r.1, hfq_mono q₁ q₂ h₁ h₂ h12 r.2⟩ : (f q₂).carrier) := by
      intro q₁ q₂ h₁ h₂ h12 r hr
      rcases eq_or_lt_of_le h12 with rfl | hlt
      · exact hr
      · exact ((IHGood q₂ h₂).2.2.1 q₁ hlt).choose_spec r hr
    have hcheck1 := hfq_mono
    have hcheck2 : ∀ q₁ q₂ (h₁ : q₁ < p) (h₂ : q₂ < p) (h12 : q₁ ≤ q₂)
        (r : (f q₁).carrier), Prime r →
        Prime (⟨r.1, hcheck1 q₁ q₂ h₁ h₂ h12 r.2⟩ : (f q₂).carrier) := by
      intro q₁ q₂ h₁ h₂ h12 r hr
      exact hfq_primes q₁ q₂ h₁ h₂ h12 r hr
    have hcheck3 : (∀ q (hq : q < p), R'.carrier ≤ (f q).carrier) ∧
        (∀ q (hq : q < p),
          Cardinal.mk (f q).carrier ≤
            max Cardinal.aleph0 (Cardinal.mk R'.carrier)) ∧
        (∀ q (hq : q < p),
          Cardinal.mk (f q).carrier < Cardinal.mk T) :=
      ⟨hfq_R'_le, hfq_card, hfq_card_lt⟩
    -- Unfold the well-founded recursion at p and discharge the guard conditions
    change (∃ (hle : R'.carrier ≤ (f p).carrier), _) ∧ _
    rw [show f p = _ from WellFounded.fix_eq _ _ p,
      dif_pos hcheck1, dif_pos hcheck2, dif_pos hcheck3]
    by_cases hne : ∃ q, q < p
    · -- p has predecessors: build the union of all f(q) for q < p, then extend
      rw [dif_pos hne]
      haveI hne_inst : Nonempty {q // q < p} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
      let ichain : NSubringChain T {q // q < p} :=
        { ring := fun x => f x.1
          mono := fun x y h12 => hcheck1 x.1 y.1 x.2 y.2 h12
          primes_preserved := fun x y h12 => hcheck2 x.1 y.1 x.2 y.2 h12 }
      let bu := build_union ichain
          (fun x => le_trans (hfq_card_res x.1 x.2) le_rfl)
          (le_trans (Cardinal.mk_subtype_le _) hPairs_card_res)
      have hbu_carrier : bu.choose.carrier = ichain.unionSubring := bu.choose_spec.1
      have hbu_le : ∀ (q : Pairs) (hq : q < p),
          (f q).carrier ≤ bu.choose.carrier := fun q hq => bu.choose_spec.2 ⟨q, hq⟩
      have hbu_card_le : Cardinal.mk bu.choose.carrier ≤
          max Cardinal.aleph0 (Cardinal.mk R'.carrier) := by
        rw [hbu_carrier]
        exact union_card_le_max R' ichain
          (le_trans (Cardinal.mk_subtype_le _) hPairs_card) (fun α => hfq_card α.1 α.2)
      have hbu_card : Cardinal.mk bu.choose.carrier < Cardinal.mk T :=
        lt_of_le_of_lt hbu_card_le (max_lt hT_aleph0 hR')
      have hbu_R'_le : R'.carrier ≤ bu.choose.carrier :=
        le_trans (hfq_R'_le hne.choose hne.choose_spec) (hbu_le hne.choose hne.choose_spec)
      have hbu_mem : ∀ (x : bu.choose.carrier), ∃ (α : {q // q < p}),
          (x : T) ∈ (ichain.ring α).carrier := by
        intro x
        exact ichain.mem_union_iff.mp ((SetLike.ext_iff.mp hbu_carrier (x : T)).mp x.2)
      have primes_to_bu : ∀ (α : {q // q < p}) (r : (f α.1).carrier),
          Prime r → Prime (⟨r.1, hbu_le α.1 α.2 r.2⟩ : bu.choose.carrier) :=
        fun α r hr => transfinite_union_primes_preserved ichain bu.choose.carrier
          (fun β => bu.choose_spec.2 β) hbu_mem α r hr
      let mk_res := mk_next bu.choose hbu_card hbu_R'_le p.1 p.2
      have hAext : IsAExtension bu.choose mk_res.choose := mk_res.choose_spec.1
      have hR'_le_res : R'.carrier ≤ mk_res.choose.carrier := mk_res.choose_spec.2.2.1
      -- Verify: R' ≤ result, primes preserved, cardinality bounded, pair closed
      refine ⟨⟨hR'_le_res, ?_⟩, ?_, ?_, mk_res.choose_spec.2.2.2⟩
      · -- Primes from R' lift through the union to bu, then through the A-extension
        intro r hr
        exact hAext.primes_preserved
          ⟨(r : T), hbu_le hne.choose hne.choose_spec
            (hfq_R'_le hne.choose hne.choose_spec r.2)⟩
          (primes_to_bu ⟨hne.choose, hne.choose_spec⟩
            ⟨(r : T), hfq_R'_le hne.choose hne.choose_spec r.2⟩
            (hfq_R'_primes hne.choose hne.choose_spec r hr))
      · calc Cardinal.mk mk_res.choose.carrier
            ≤ max Cardinal.aleph0 (Cardinal.mk bu.choose.carrier) := hAext.card_le
          _ ≤ max Cardinal.aleph0 (max Cardinal.aleph0 (Cardinal.mk R'.carrier)) :=
            max_le_max_left _ hbu_card_le
          _ = max Cardinal.aleph0 (Cardinal.mk R'.carrier) := by rw [← max_assoc, max_self]
      · intro q hq
        refine ⟨le_trans (hbu_le q hq) hAext.le, ?_⟩
        intro r hr
        exact hAext.primes_preserved ⟨(r : T), hbu_le q hq r.2⟩
          (primes_to_bu ⟨q, hq⟩ r hr)
    · -- p is minimal: close directly over R'
      rw [dif_neg hne]
      let mk_res := mk_next R' hR' (le_refl _) p.1 p.2
      have hAext : IsAExtension R' mk_res.choose := mk_res.choose_spec.1
      refine ⟨⟨mk_res.choose_spec.2.2.1, fun r hr => hAext.primes_preserved r hr⟩,
        hAext.card_le, fun q hq => absurd ⟨q, hq⟩ hne, mk_res.choose_spec.2.2.2⟩
  -- Assembly: form the full chain {f(p)} indexed by Pairs and take its union
  haveI : Nonempty Pairs := ⟨⟨∅, ⟨0, R'.carrier.zero_mem⟩⟩⟩
  have hf_mono : ∀ ⦃a b : Pairs⦄, a ≤ b → (f a).carrier ≤ (f b).carrier := by
    intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · exact ((hGood b).2.2.1 a hlt).choose
  have hf_primes : ∀ ⦃a b : Pairs⦄ (h : a ≤ b) (r : (f a).carrier),
      Prime r → Prime (⟨r.1, hf_mono h r.2⟩ : (f b).carrier) := by
    intro a b hab r hr
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact hr
    · exact ((hGood b).2.2.1 a hlt).choose_spec r hr
  -- The family f forms an NSubringChain; its union S is the desired one-pass output
  let fchain : NSubringChain T Pairs :=
    { ring := f, mono := hf_mono, primes_preserved := hf_primes }
  obtain ⟨S, hS_carrier, hS_le⟩ := build_union fchain
    (fun p => le_trans (hGood p).2.1 (max_le (le_max_left ..) R'.card_le))
    hPairs_card_res
  have hS_mem : ∀ (x : S.carrier), ∃ (α : Pairs), (x : T) ∈ (f α).carrier := by
    intro x
    exact fchain.mem_union_iff.mp (hS_carrier ▸ x.2)
  -- R' ≤ f(p₀) ≤ S for any base pair p₀
  let p₀ : Pairs := ⟨∅, ⟨0, R'.carrier.zero_mem⟩⟩
  have hR'_le_S : R'.carrier ≤ S.carrier := le_trans (hGood p₀).1.choose (hS_le p₀)
  refine ⟨S, ?_, ?_, ?_⟩
  · -- S is an A-extension of R': primes preserved via transfinite union lemma
    exact {
      le := hR'_le_S
      primes_preserved := by
        intro r hr
        exact transfinite_union_primes_preserved fchain S.carrier (fun α => hS_le α)
          hS_mem p₀ ⟨(r : T), (hGood p₀).1.choose r.2⟩ ((hGood p₀).1.choose_spec r hr)
      card_le := by
        rw [hS_carrier]
        exact union_card_le_max R' fchain hPairs_card (fun α => (hGood α).2.1) }
  · calc Cardinal.mk S.carrier
        ≤ max Cardinal.aleph0 (Cardinal.mk R'.carrier) := by
          rw [hS_carrier]
          exact union_card_le_max R' fchain hPairs_card (fun α => (hGood α).2.1)
      _ < Cardinal.mk T := max_lt hT_aleph0 hR'
  · -- Each (I, c) pair was closed at stage f(gens, c); lift into S via inclusion
    intro I hI c hc
    obtain ⟨gens, hgens⟩ := hI
    subst hgens
    obtain ⟨hle_fp, hc_fp⟩ := (hGood (gens, c)).2.2.2 hc
    refine ⟨le_trans hle_fp (hS_le (gens, c)), ?_⟩
    rw [show Ideal.map (Subring.inclusion (le_trans hle_fp (hS_le (gens, c))))
          (Ideal.span ↑gens) =
        Ideal.map (Subring.inclusion (hS_le (gens, c)))
          (Ideal.map (Subring.inclusion hle_fp) (Ideal.span ↑gens)) from by
      rw [Ideal.map_map]
      congr 1]
    exact Ideal.mem_map_of_mem _ hc_fp
⟩

include T in private theorem close_up_all_one_pass_aux
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (R' : NSubring T) (hR' : Cardinal.mk R'.carrier < Cardinal.mk T) :
    ∃ S : NSubring T, IsAExtension R' S ∧ Cardinal.mk S.carrier < Cardinal.mk T ∧
      (∀ (I : Ideal R'.carrier) (_ : I.FG) (c : R'.carrier),
        (c : T) ∈ Ideal.map R'.carrier.subtype I →
        ∃ (hle : R'.carrier ≤ S.carrier),
          (⟨(c : T), hle c.2⟩ : S.carrier) ∈
            Ideal.map (Subring.inclusion hle) I) := by
  exact
    (close_up_all_one_pass_aux_proof
      hM_not_assoc hAss_ht hT_card hT_aleph0 R' hR'
    ).down
/- One-pass transfinite close-up: given NSubring R' with #R' < #T, produce an A-extension S
such that every (I, c) pair from R' with c ∈ IT is closed in S. -/
include T in theorem close_up_all_one_pass
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (R' : NSubring T) (hR' : Cardinal.mk R'.carrier < Cardinal.mk T) :
    ∃ S : NSubring T, IsAExtension R' S ∧ Cardinal.mk S.carrier < Cardinal.mk T ∧
      (∀ (I : Ideal R'.carrier) (_ : I.FG) (c : R'.carrier),
        (c : T) ∈ Ideal.map R'.carrier.subtype I →
        ∃ (hle : R'.carrier ≤ S.carrier),
          (⟨(c : T), hle c.2⟩ : S.carrier) ∈
            Ideal.map (Subring.inclusion hle) I) :=
  close_up_all_one_pass_aux hM_not_assoc hAss_ht hT_card hT_aleph0 R' hR'

/- Build an NSubring from an ℕ-indexed chain (cross-universe: ℕ : Type 0, T : Type u).
Returns the NSubring with carrier = unionSubring. -/
include T in theorem build_union_isNSubring_nat
    (chain : NSubringChain T ℕ)
    (h_card : ∀ (n : ℕ),
      Cardinal.mk (chain.ring n).carrier ≤
        max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))) :
    ∃ (S : NSubring T),
      S.carrier = chain.unionSubring ∧
      (∀ (n : ℕ), (chain.ring n).carrier ≤ S.carrier) := by
  -- Same construction as build_union_isNSubring but for ℕ-indexed chains (universe 0)
  set U := chain.unionSubring
  have hU_le : ∀ n, (chain.ring n).carrier ≤ U := chain.le_union
  have hU_mem : ∀ x : U, ∃ n, (x : T) ∈ (chain.ring n).carrier :=
    fun x => chain.mem_union_iff.mp x.2
  -- Locality: lift the unit/non-unit dichotomy from each stage to the union
  haveI hU_local : IsLocalRing U := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro a
    obtain ⟨α, hα⟩ := hU_mem a
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      (⟨(a : T), hα⟩ : (chain.ring α).carrier) with hu | hu
    · left
      exact hu.map (Subring.inclusion (hU_le α))
    · right
      exact (show Subring.inclusion (hU_le α) (1 - ⟨(a : T), hα⟩) = 1 - a
        from Subtype.ext rfl) ▸ hu.map (Subring.inclusion (hU_le α))
  refine ⟨⟨U, transfinite_union_isUFD chain U hU_le hU_mem, hU_local, ?_, ?_, ?_⟩,
    rfl, hU_le⟩
  · -- Card bound: #U ≤ ℵ₀ · sup_n(#R_n) ≤ κ² = κ
    set κ := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
    have hU_eq : (U : Set T) = ⋃ n, ↑(chain.ring n).carrier :=
      Subring.coe_iSup_of_directed chain.directed_carriers
    have h_lift := Cardinal.mk_iUnion_le_lift
      (fun n => ((chain.ring n).carrier : Set T))
    rw [← hU_eq] at h_lift
    simp only [Cardinal.lift_id'] at h_lift
    rw [show Cardinal.lift #ℕ = Cardinal.aleph0 from by
      rw [Cardinal.mk_nat, Cardinal.lift_aleph0]] at h_lift
    have hsup : ⨆ n, Cardinal.mk ((chain.ring n).carrier : Set T) ≤ κ :=
      ciSup_le fun n => h_card n
    calc Cardinal.mk U
        ≤ Cardinal.aleph0 * ⨆ n, Cardinal.mk ((chain.ring n).carrier : Set T) := h_lift
      _ ≤ Cardinal.aleph0 * κ := by gcongr
      _ ≤ κ * κ := by gcongr
                      exact le_max_left ..
      _ ≤ max κ κ := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
      _ = κ := max_self κ
  · -- Maximal ideal: same argument as build_union_isNSubring, adapted for ℕ index
    ext ⟨a, ha⟩
    simp only [Ideal.mem_comap, Subring.coe_subtype]
    constructor
    · intro hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu_T
      obtain ⟨α, hα⟩ := hU_mem ⟨a, ha⟩
      by_contra h_nu
      have : ¬IsUnit (⟨a, hα⟩ : (chain.ring α).carrier) :=
        fun hu => h_nu ((IsLocalRing.mem_maximalIdeal _).mp hx
          (hu.map (Subring.inclusion (hU_le α))))
      have hmem := (IsLocalRing.mem_maximalIdeal _).mpr this
      rw [(chain.ring α).maximal_ideal_eq] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem) hu_T
    · intro hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu_S
      exact (IsLocalRing.mem_maximalIdeal _).mp hx (hu_S.map U.subtype)
  · -- Height bound: pull q ⊊ P back to a finite stage γ and use the NSubring property there
    intro t ht P hP
    have hP_prime := hP.isPrime
    haveI : (Ideal.comap U.subtype P).IsPrime := hP_prime.comap _
    change (Ideal.comap U.subtype P).height ≤ ↑(1 : ℕ)
    rw [Ideal.height_le_iff]
    intro q hq_prime hq_lt
    suffices q = ⊥ by rw [this, Ideal.height_bot]
                      norm_cast
    by_contra hq_ne
    obtain ⟨s, hs_q, hs_ne⟩ : ∃ s : U, s ∈ q ∧ s ≠ 0 := by
      by_contra h
      push Not at h
      exact hq_ne ((Submodule.eq_bot_iff q).mpr fun x hx => h x hx)
    obtain ⟨x, hx_P, hx_nq⟩ := Set.exists_of_ssubset hq_lt
    obtain ⟨αs, hαs⟩ := hU_mem s
    obtain ⟨αx, hαx⟩ := hU_mem x
    set γ := max αs αx
    set inclγ := Subring.inclusion (hU_le γ)
    haveI : (Ideal.comap inclγ q).IsPrime := hq_prime.comap _
    set s' : (chain.ring γ).carrier := ⟨(s : T), chain.mono (le_max_left ..) hαs⟩
    have hs'_ne : s' ≠ 0 := fun h => hs_ne (Subtype.ext (congrArg
      (fun (x : (chain.ring γ).carrier) => (x : T)) h))
    have hs'_q : s' ∈ Ideal.comap inclγ q :=
      show inclγ s' ∈ q from (show inclγ s' = s from Subtype.ext rfl) ▸ hs_q
    have hq'_ne : Ideal.comap inclγ q ≠ ⊥ := fun h => by
      rw [h] at hs'_q
      exact hs'_ne (Ideal.mem_bot.mp hs'_q)
    set x' : (chain.ring γ).carrier :=
      ⟨(x : T), chain.mono (le_max_right ..) hαx⟩
    have hx'_nq : x' ∉ Ideal.comap inclγ q := fun h => by
      have h' : inclγ x' ∈ q := h
      rw [show inclγ x' = x from Subtype.ext rfl] at h'
      exact hx_nq h'
    have hq'_lt : Ideal.comap inclγ q <
        Ideal.comap (chain.ring γ).carrier.subtype P :=
      lt_of_le_of_ne
        (fun r hr => (hq_lt.le (show inclγ r ∈ q from hr) : (inclγ r : T) ∈ P))
        (fun h => hx'_nq (h ▸ (hx_P : (x : T) ∈ P)))
    haveI : (Ideal.comap (chain.ring γ).carrier.subtype P).IsPrime := hP_prime.comap _
    have hq'_ht := (Ideal.height_le_iff (n := 1)).mp
      ((chain.ring γ).height_bound t ht P hP) _ inferInstance hq'_lt
    haveI : IsDomain (chain.ring γ).carrier := inferInstance
    exact absurd ((Ideal.height_le_iff (n := 0)).mp (by
      lift (Ideal.comap inclγ q).height to ℕ using ne_top_of_lt hq'_ht with n hn
      simp only [Nat.cast_lt] at hq'_ht
      simp only [Nat.cast_le]
      omega
    ) ⊥ Ideal.isPrime_bot (bot_lt_iff_ne_bot.mpr hq'_ne)) not_lt_bot

/- ω-iteration: given a one-pass close-up procedure, iterate it to close all f.g. ideals. -/
include T in theorem close_up_all_omega
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (_hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (_hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (one_pass : ∀ (R' : NSubring T), Cardinal.mk R'.carrier < Cardinal.mk T →
      ∃ S : NSubring T, IsAExtension R' S ∧ Cardinal.mk S.carrier < Cardinal.mk T ∧
        (∀ (I : Ideal R'.carrier) (_ : I.FG) (c : R'.carrier),
          (c : T) ∈ Ideal.map R'.carrier.subtype I →
          ∃ (hle : R'.carrier ≤ S.carrier),
            (⟨(c : T), hle c.2⟩ : S.carrier) ∈
              Ideal.map (Subring.inclusion hle) I)) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      (∀ (I : Ideal S.carrier), I.FG →
        ∀ (c : S.carrier), (c : T) ∈ Ideal.map S.carrier.subtype I →
          c ∈ I) := by
    -- Build the ω-chain: pass(0) = R, pass(n+1) = one_pass(pass(n))
    let passAux : ℕ → Σ' (S : NSubring T), Cardinal.mk S.carrier < Cardinal.mk T :=
      Nat.rec ⟨R, hR_card⟩ fun _ p =>
        ⟨(one_pass p.1 p.2).choose, (one_pass p.1 p.2).choose_spec.2.1⟩
    let pass := fun n => (passAux n).1
    have hpass_aext : ∀ n, IsAExtension (pass n) (pass (n + 1)) :=
      fun n => (one_pass (passAux n).1 (passAux n).2).choose_spec.1
    -- Key property: each pass closes all (I, c) pairs from its predecessor
    have hpass_close : ∀ n (I : Ideal (pass n).carrier) (_ : I.FG) (c : (pass n).carrier),
        (c : T) ∈ Ideal.map (pass n).carrier.subtype I →
        ∃ (hle : (pass n).carrier ≤ (pass (n + 1)).carrier),
          (⟨(c : T), hle c.2⟩ : (pass (n + 1)).carrier) ∈
            Ideal.map (Subring.inclusion hle) I :=
      fun n => (one_pass (passAux n).1 (passAux n).2).choose_spec.2.2
    have hpass_mono : ∀ ⦃a b : ℕ⦄, a ≤ b → (pass a).carrier ≤ (pass b).carrier := by
      intro a b hab
      induction hab with
      | refl => exact le_refl _
      | step _ ih => exact le_trans ih (hpass_aext _).le
    have hpass_primes : ∀ ⦃a b : ℕ⦄ (h : a ≤ b) (r : (pass a).carrier),
        Prime r → Prime (⟨r.1, hpass_mono h r.2⟩ : (pass b).carrier) := by
      intro a b hab
      induction hab with
      | refl => intro r hr
                exact (Subtype.ext rfl : (⟨r.1, _⟩ : (pass a).carrier) = r) ▸ hr
      | @step m hle ih =>
        intro r hr
        exact (hpass_aext m).primes_preserved ⟨r.1, hpass_mono hle r.2⟩ (ih r hr)
    let pchain : NSubringChain T ℕ := ⟨pass, hpass_mono, hpass_primes⟩
    -- Card bounds: each pass(n) has #pass(n) ≤ max(ℵ₀, #R)
    have hpass_card_le_R : ∀ n, Cardinal.mk (pass n).carrier ≤
        max Cardinal.aleph0 (Cardinal.mk R.carrier) := by
      intro n
      induction n with
      | zero => exact le_max_right _ _
      | succ n ih =>
        calc Cardinal.mk (pass (n + 1)).carrier
            ≤ max Cardinal.aleph0 (Cardinal.mk (pass n).carrier) := (hpass_aext n).card_le
          _ ≤ max Cardinal.aleph0 (max Cardinal.aleph0 (Cardinal.mk R.carrier)) :=
            max_le_max_left _ ih
          _ = max Cardinal.aleph0 (Cardinal.mk R.carrier) := by rw [← max_assoc, max_self]
    -- Build S = ⋃_n pass(n) as an NSubring via the ℕ-indexed union lemma
    have hpass_card_res : ∀ n, Cardinal.mk (pass n).carrier ≤
        max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) :=
      fun n => le_trans (hpass_card_le_R n) (max_le (le_max_left ..) R.card_le)
    obtain ⟨S, hS_carrier, hS_le⟩ := build_union_isNSubring_nat pchain hpass_card_res
    have hpS_mem' : ∀ (x : S.carrier), ∃ n, (x : T) ∈ (pass n).carrier := by
      intro x
      exact pchain.mem_union_iff.mp (hS_carrier ▸ x.2)
    refine ⟨S, ?_, ?_⟩
    · -- R = pass(0) ≤ S and primes are preserved through the ω-union
      exact {
        le := hS_le 0
        primes_preserved := fun r hr =>
          transfinite_union_primes_preserved pchain S.carrier
            (fun n => hS_le n) hpS_mem' 0 r hr
        card_le := by
          rw [hS_carrier]
          set κ := max Cardinal.aleph0 (Cardinal.mk R.carrier)
          have h_lift := Cardinal.mk_iUnion_le_lift
            (fun n => ((pass n).carrier : Set T))
          rw [← Subring.coe_iSup_of_directed pchain.directed_carriers] at h_lift
          simp only [Cardinal.lift_id'] at h_lift
          rw [show Cardinal.lift #ℕ = Cardinal.aleph0 from by
            rw [Cardinal.mk_nat, Cardinal.lift_aleph0]] at h_lift
          have hsup : ⨆ n, Cardinal.mk ((pass n).carrier : Set T) ≤ κ :=
            ciSup_le fun n => hpass_card_le_R n
          calc Cardinal.mk pchain.unionSubring
              ≤ Cardinal.aleph0 * ⨆ n, Cardinal.mk ((pass n).carrier : Set T) := h_lift
            _ ≤ Cardinal.aleph0 * κ := by gcongr
            _ ≤ κ * κ := by gcongr
                            exact le_max_left ..
            _ ≤ max κ κ := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
            _ = κ := max_self κ }
    · -- Closing-up: given f.g. I ⊆ S and c ∈ I·T, show c ∈ I
      intro I hI c hc
      obtain ⟨gens, hgens⟩ := hI
      -- All generators and c appear at finite stages; take N = max of all indices
      have h_gens_in : ∀ g ∈ gens, ∃ n, (g : T) ∈ (pass n).carrier :=
        fun g _ => hpS_mem' (⟨(g : T), g.2⟩ : S.carrier)
      obtain ⟨nc, hnc⟩ := hpS_mem' c
      let idxOf : {g // g ∈ gens} → ℕ := fun ⟨g, hg⟩ => (h_gens_in g hg).choose
      let N := gens.attach.sup idxOf ⊔ nc
      have hN_idx : ∀ g (hg : g ∈ gens), (g : T) ∈ (pass N).carrier := by
        intro g hg
        have h1 : idxOf ⟨g, hg⟩ ≤ gens.attach.sup idxOf :=
          Finset.le_sup (f := idxOf) (Finset.mem_attach gens ⟨g, hg⟩)
        exact hpass_mono (le_trans h1 le_sup_left) (h_gens_in g hg).choose_spec
      have hc_N : (c : T) ∈ (pass N).carrier := hpass_mono le_sup_right hnc
      haveI : ∀ (x : T), Decidable (x ∈ (pass N).carrier) := fun _ => Classical.dec _
      haveI : DecidableEq (pass N).carrier := Classical.decEq _
      -- Pull the generators down to pass(N) and form the ideal J there
      let toPassN : S.carrier → (pass N).carrier := fun g =>
        if h : (g : T) ∈ (pass N).carrier then ⟨(g : T), h⟩
        else ⟨0, (pass N).carrier.zero_mem⟩
      let gens_N := gens.image toPassN
      let J : Ideal (pass N).carrier := Ideal.span (↑gens_N : Set (pass N).carrier)
      let c_N : (pass N).carrier := ⟨(c : T), hc_N⟩
      -- The image of J in S equals I: generators match under inclusion
      have hJ_map_I : Ideal.map (Subring.inclusion (hS_le N)) J = I := by
        rw [← hgens]
        apply le_antisymm
        · apply Ideal.map_le_iff_le_comap.mpr
          apply Ideal.span_le.mpr
          intro x hx
          rw [SetLike.mem_coe, Ideal.mem_comap]
          simp only [gens_N, Finset.coe_image, Set.mem_image] at hx
          obtain ⟨g, hg, rfl⟩ := hx
          have heq : Subring.inclusion (hS_le N) (toPassN g) = g := by
            apply Subtype.ext
            change (toPassN g : T) = (g : T)
            exact congrArg Subtype.val (dif_pos (hN_idx g hg))
          rw [heq]
          exact Ideal.subset_span (Finset.mem_coe.mpr hg)
        · rw [Ideal.span_le]
          intro g hg
          rw [Finset.mem_coe] at hg
          have h_in_J : toPassN g ∈ J :=
            Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem toPassN hg))
          have heq : Subring.inclusion (hS_le N) (toPassN g) = g := by
            apply Subtype.ext
            change (toPassN g : T) = (g : T)
            exact congrArg Subtype.val (dif_pos (hN_idx g hg))
          rw [SetLike.mem_coe]
          exact heq ▸ Ideal.mem_map_of_mem _ h_in_J
      have hc_J : (c_N : T) ∈ Ideal.map (pass N).carrier.subtype J := by
        rw [show Ideal.map (pass N).carrier.subtype J = Ideal.map S.carrier.subtype I from by
          rw [← hJ_map_I, Ideal.map_map]
          rfl]
        exact hc
      -- Apply the one-pass closing property at stage N to get c ∈ J in pass(N+1)
      obtain ⟨hle_step, hc_step⟩ := hpass_close N J ⟨gens_N, rfl⟩ c_N hc_J
      -- Lift from pass(N+1) to S: J maps into I, so c ∈ I
      have h_le : Ideal.map (Subring.inclusion hle_step) J ≤
          Ideal.comap (Subring.inclusion (hS_le (N + 1))) I := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        change Subring.inclusion (hS_le (N + 1)) (Subring.inclusion hle_step x) ∈ I
        rw [← hJ_map_I]
        exact Ideal.mem_map_of_mem _ hx
      exact h_le hc_step

/- Transfinite close-up: given NSubring R with #R < #T, produce an A-extension S
with IT ∩ S = I for all f.g. ideals I of S. -/
include T in theorem close_up_all
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      (∀ (I : Ideal S.carrier), I.FG →
        ∀ (c : S.carrier), (c : T) ∈ Ideal.map S.carrier.subtype I →
          c ∈ I) :=
  close_up_all_omega R hR_card hT_card hT_aleph0
    (fun R' hR' => close_up_all_one_pass hM_not_assoc hAss_ht hT_card hT_aleph0 R' hR')

/- Heitmann Lemma 7 (adapted for Jensen P = (0)). -/
include T in theorem combined_step
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (ℓ : T ⧸ IsLocalRing.maximalIdeal T ^ 2)
    (q : Ideal T) (hq_prime : q.IsPrime) (hq_ne_bot : q ≠ ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      (∃ (c : S.carrier), Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = ℓ) ∧
      (∃ (t : S.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) ∧
      (∀ (I : Ideal S.carrier), I.FG →
        ∀ (c : S.carrier), (c : T) ∈ Ideal.map S.carrier.subtype I →
          c ∈ I) := by
  -- M ≠ 0: if M = 0 then q contains a unit, contradicting q prime and proper
  have hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥ := by
    intro h
    have ⟨r, hr_mem, hr_ne⟩ : ∃ r ∈ q, r ≠ (0 : T) := by
      by_contra hall
      push Not at hall
      exact hq_ne_bot ((Submodule.eq_bot_iff q).mpr hall)
    have hr_unit : IsUnit r := by
      by_contra h_not
      have := (IsLocalRing.mem_maximalIdeal _).mpr h_not
      rw [h] at this
      exact hr_ne (by simpa using this)
    exact hq_prime.ne_top (q.eq_top_of_isUnit_mem hr_mem hr_unit)
  -- Step 1: Adjoin a nonzero element of q to R, producing A-extension R₀ that catches q
  obtain ⟨R₀, hAext₀, t₀, ht₀_mem, ht₀_ne⟩ := adjoin_from_prime R q hq_prime hq_ne_bot
    hM_not_assoc hAss_ht hR_card hT_card
  -- Step 2: Lift ℓ ∈ T/M² to a representative u, then adjoin a preimage mod M² to R₀
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective ℓ
  have hR₀_card : Cardinal.mk R₀.carrier < Cardinal.mk T :=
    card_lt_of_aext' hT_aleph0 hAext₀ hR_card
  obtain ⟨R₁, hAext₁, c₁, hc₁⟩ := adjoin_surjectivity R₀ u
    hM_not_assoc hAss_ht hR₀_card hT_card hM_ne_bot
  have hR₁_card : Cardinal.mk R₁.carrier < Cardinal.mk T :=
    card_lt_of_aext' hT_aleph0 hAext₁ hR₀_card
  -- Step 3: Close up all f.g. ideals of R₁ to get S with IT ∩ S = I
  obtain ⟨S, hAext_S, hclose⟩ :=
    close_up_all R₁ hM_not_assoc hAss_ht hR₁_card hT_card hT_aleph0
  -- Compose: R → R₀ → R₁ → S is an A-extension by transitivity
  refine ⟨S, isAExtension_trans (isAExtension_trans hAext₀ hAext₁) hAext_S,
    ⟨⟨(c₁ : T), hAext_S.le c₁.2⟩, ?_⟩,
    ⟨⟨(t₀ : T), (le_trans hAext₁.le hAext_S.le) t₀.2⟩, ht₀_mem, ht₀_ne⟩,
    hclose⟩
  · -- c₁ covers ℓ: c₁ ≡ u mod M², so their images in T/M² agree
    rw [← hu, Ideal.Quotient.eq,
      show ((⟨(c₁ : T), hAext_S.le c₁.2⟩ : S.carrier) : T) - u =
        -(u - (c₁ : T)) from by ring, neg_mem_iff]
    exact hc₁

/- Variant without the prime-catching requirement, just surjectivity + closing up. -/
include T in theorem combined_step_surj
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (ℓ : T ⧸ IsLocalRing.maximalIdeal T ^ 2)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      (∃ (c : S.carrier), Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = ℓ) ∧
      (∀ (I : Ideal S.carrier), I.FG →
        ∀ (c : S.carrier), (c : T) ∈ Ideal.map S.carrier.subtype I →
          c ∈ I) := by
  -- Lift ℓ to u ∈ T, then adjoin a preimage mod M² to get R₀ covering ℓ
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective ℓ
  obtain ⟨R₀, hAext₀, c₀, hc₀⟩ := adjoin_surjectivity R u
    hM_not_assoc hAss_ht hR_card hT_card hM_ne_bot
  have hR₀_card : Cardinal.mk R₀.carrier < Cardinal.mk T :=
    card_lt_of_aext' hT_aleph0 hAext₀ hR_card
  -- Close up all f.g. ideals and compose the two A-extensions
  obtain ⟨S, hAext_S, hclose⟩ :=
    close_up_all R₀ hM_not_assoc hAss_ht hR₀_card hT_card hT_aleph0
  refine ⟨S, isAExtension_trans hAext₀ hAext_S,
    ⟨⟨(c₀ : T), hAext_S.le c₀.2⟩, ?_⟩, hclose⟩
  · rw [← hu, Ideal.Quotient.eq,
      show ((⟨(c₀ : T), hAext_S.le c₀.2⟩ : S.carrier) : T) - u =
        -(u - (c₀ : T)) from by ring, neg_mem_iff]
    exact hc₀

end
