/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.CombinedStep

/-!
# Chain Helpers for the Transfinite Construction

Cardinal arithmetic wrappers and cardinality bounds on chain
unions needed for the ordinal-indexed iteration in Jensen's
construction of UFDs with prescribed completions.

Jensen, "Completions of UFDs with semi-local formal fibers",
2006, Theorem 2.2.
-/

universe u

noncomputable section

open Cardinal Ideal

variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]


/-!
## Main Construction: Jensen's Corollary 2.4 for P = (0)

For T a complete local domain with depth ≥ 2, |T/M| = |T|, char 0,
construct a local UFD A with Â ≅ T and HasTrivialGenericFormalFiber A.

Construction:
1. Start with R₀ = initial N-subring (≅ ℚ).
2. Well-order V = {nonzero primes of T} × T/M² with |V| = |T/M|.
3. At successor α: use combined_step with q_α and ℓ_α.
4. At limit α: take transfinite union.
5. A = ⋃ R_α satisfies Prop 1 conditions ⟹ A is Noetherian, Â ≅ T.
6. A is a UFD (transfinite union preserves UFD).
7. For every nonzero prime q: q ∩ A ≠ (0) (handled at step for q).
8. Therefore HasTrivialGenericFormalFiber A.
-/

/-! ## Cardinal-parameter versions of the combined step

Versions of the combined step that use cardinal bounds `#R < #T` and
`ℵ₀ < #T` instead of countability of R. These are the forms needed
by the transfinite iteration, where intermediate subrings grow beyond
countable but remain strictly smaller than T.
-/

/-- Cardinal-param version of `combined_step`: given `#R < #T` and `ℵ₀ < #T`,
produce an A-extension S with coverage for ℓ, catching for q, closedness,
and `#S < #T`. -/
theorem combined_step_card
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (ℓ : T ⧸ IsLocalRing.maximalIdeal T ^ 2)
    (q : Ideal T) (hq_prime : q.IsPrime) (hq_ne_bot : q ≠ ⊥)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      (∃ (c : S.carrier),
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = ℓ) ∧
      (∃ (t : S.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) ∧
      (∀ (I : Ideal S.carrier), I.FG →
        ∀ (c : S.carrier), (c : T) ∈ Ideal.map S.carrier.subtype I → c ∈ I) ∧
      (Cardinal.mk S.carrier < Cardinal.mk T) := by
  obtain ⟨S, hAext, hℓ, hq, hclose⟩ := combined_step R ℓ q hq_prime hq_ne_bot
    hM_not_assoc hAss_ht hR_card hT_card hT_aleph0
  exact ⟨S, hAext, hℓ, hq, hclose,
    lt_of_le_of_lt hAext.card_le (max_lt hT_aleph0 hR_card)⟩

/-- Cardinal-param version of `combined_step_surj`: surjectivity-only step. -/
theorem combined_step_surj_card
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (ℓ : T ⧸ IsLocalRing.maximalIdeal T ^ 2)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      (∃ (c : S.carrier),
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = ℓ) ∧
      (∀ (I : Ideal S.carrier), I.FG →
        ∀ (c : S.carrier), (c : T) ∈ Ideal.map S.carrier.subtype I → c ∈ I) ∧
      (Cardinal.mk S.carrier < Cardinal.mk T) := by
  obtain ⟨S, hAext, hℓ, hclose⟩ := combined_step_surj R ℓ
    hM_not_assoc hAss_ht hR_card hT_card hT_aleph0 hM_ne_bot
  exact ⟨S, hAext, hℓ, hclose,
    lt_of_le_of_lt hAext.card_le (max_lt hT_aleph0 hR_card)⟩

/-- Cardinality bound at limit steps of ordinal recursion:
the union of a chain of NSubrings indexed by ι' with #ι' < #T and
each #R(α) bounded by #ι' has #(⋃R) < #T.
The hypothesis `h_card_bound` (each #R_α ≤ #ι') is satisfied in the recursion
because finitely generated operations preserve cardinality of infinite rings,
so #R(β) ≤ #R(0) · #β ≤ #λ for β < λ. -/
theorem chain_union_card_lt
    {ι' : Type u} [LinearOrder ι'] [Nonempty ι']
    (chain : NSubringChain T ι')
    (h_card_bound : ∀ (α : ι'), Cardinal.mk (chain.ring α).carrier ≤ Cardinal.mk ι')
    (h_ι_card : Cardinal.mk ι' < Cardinal.mk T)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T)) :
    ∃ S : NSubring T,
      (∀ (α : ι'), (chain.ring α).carrier ≤ S.carrier) ∧
      (Cardinal.mk S.carrier < Cardinal.mk T) := by
  set U := chain.unionSubring with hU_def
  have hU_le : ∀ α, (chain.ring α).carrier ≤ U := chain.le_union
  have hU_mem : ∀ x : ↥U, ∃ α, (x : T) ∈ (chain.ring α).carrier :=
    fun x => chain.mem_union_iff.mp x.2
  -- U is local: each element lives in some R_α which is local, so unit-or-complement lifts
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
  -- #U ≤ max(aleph0, #(T/M)): bound via #U ≤ #ι' * sup_α #R_α ≤ κ²= κ
  have hU_card_le : Cardinal.mk ↥U ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) := by
    have hU_eq : (U : Set T) = ⋃ α, ↑(chain.ring α).carrier := by
      rw [hU_def, NSubringChain.unionSubring]
      exact Subring.coe_iSup_of_directed chain.directed_carriers
    have h1 : Cardinal.mk ↥U ≤ Cardinal.mk ι' *
        ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) := by
      have := Cardinal.mk_iUnion_le (fun α => ((chain.ring α).carrier : Set T))
      rwa [← hU_eq] at this
    set κ := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
    have h2 : ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) ≤ κ :=
      ciSup_le fun α => le_trans (h_card_bound α) (le_trans (le_of_lt h_ι_card)
        (hT_card ▸ le_max_right _ _))
    have h3 : Cardinal.mk ι' ≤ κ :=
      le_trans (le_of_lt h_ι_card) (hT_card ▸ le_max_right _ _)
    calc Cardinal.mk ↥U
        ≤ Cardinal.mk ι' *
          ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) := h1
      _ ≤ Cardinal.mk ι' * κ := mul_le_mul_right h2 _
      _ ≤ κ * κ := mul_le_mul_left h3 κ
      _ ≤ max κ κ := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
      _ = κ := max_self κ
  -- M_U = M_T ∩ U: an element of U is a non-unit in U iff it is a non-unit in T
  have hU_maximal : IsLocalRing.maximalIdeal ↥U =
      (IsLocalRing.maximalIdeal T).comap U.subtype := by
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
  -- Height bound transfers: for t ≠ 0, associated primes of T/(t) pull back to height ≤ 1 in U
  have hU_height : ∀ (t : T), t ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {t}),
        Ideal.height (P.comap U.subtype) ≤ 1 := by
    intro t ht P hP
    have hP_prime := hP.isPrime
    haveI : (Ideal.comap U.subtype P).IsPrime := hP_prime.comap _
    change (Ideal.comap U.subtype P).height ≤ ↑(1 : ℕ)
    rw [Ideal.height_le_iff]
    intro q hq_prime hq_lt
    -- Any prime q strictly below P ∩ U must be zero (height ≤ 1 forces this)
    suffices q = ⊥ by rw [this, Ideal.height_bot]
                      norm_cast
    by_contra hq_ne
    obtain ⟨s, hs_q, hs_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hq_ne
    obtain ⟨x, hx_P, hx_nq⟩ := Set.exists_of_ssubset hq_lt
    obtain ⟨αs, hαs⟩ := hU_mem s
    obtain ⟨αx, hαx⟩ := hU_mem x
    -- Pull back to a single ring R_γ containing both witnesses s ∈ q and x ∈ P \ q
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
    -- Use the height bound in R_γ to get ht(q ∩ R_γ) = 0, contradicting q ∩ R_γ ≠ ⊥
    haveI : (Ideal.comap (chain.ring γ).carrier.subtype P).IsPrime :=
      hP_prime.comap _
    have hq'_ht := (Ideal.height_le_iff (n := 1)).mp
      ((chain.ring γ).height_bound t ht P hP) _ inferInstance hq'_lt
    haveI : IsDomain (chain.ring γ).carrier := inferInstance
    exact absurd ((Ideal.height_le_iff (n := 0)).mp (by
      lift (Ideal.comap inclγ q).height to ℕ using ne_top_of_lt hq'_ht with n hn
      simp only [Nat.cast_lt] at hq'_ht
      simp only [Nat.cast_le]
      omega
    ) ⊥ Ideal.isPrime_bot (bot_lt_iff_ne_bot.mpr hq'_ne)) not_lt_bot
  let S : NSubring T :=
    { carrier := U
      isUFD := transfinite_union_isUFD chain U hU_le hU_mem
      isLocalRing := hU_local
      card_le := hU_card_le
      maximal_ideal_eq := hU_maximal
      height_bound := hU_height }
  refine ⟨S, hU_le, ?_⟩
  -- #U ≤ #ι' · #ι' < #T by cardinal arithmetic (since #ι' < #T and #T > aleph0)
  have hU_eq : (U : Set T) = ⋃ α, ↑(chain.ring α).carrier := by
    rw [hU_def, NSubringChain.unionSubring]
    exact Subring.coe_iSup_of_directed chain.directed_carriers
  have h1 : Cardinal.mk ↥U ≤ Cardinal.mk ι' *
      ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) := by
    have := Cardinal.mk_iUnion_le (fun α => ((chain.ring α).carrier : Set T))
    rwa [← hU_eq] at this
  have h2 : ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) ≤
      Cardinal.mk ι' :=
    ciSup_le fun α => h_card_bound α
  calc Cardinal.mk ↥U
      ≤ Cardinal.mk ι' *
        ⨆ (α : ι'), Cardinal.mk ↑((chain.ring α).carrier : Set T) := h1
    _ ≤ Cardinal.mk ι' * Cardinal.mk ι' := mul_le_mul_right h2 _
    _ < Cardinal.mk T :=
        Cardinal.mul_lt_of_lt (le_of_lt hT_aleph0) h_ι_card h_ι_card


end
