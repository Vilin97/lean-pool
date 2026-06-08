/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Construction.ChainHelpers
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Transfinite Construction

The ordinal-indexed iteration that builds an ascending chain of
N-subrings, ensuring at each successor step that one more prime
is caught and one more element of T/M^2 is covered.

Jensen, "Completions of UFDs with semi-local formal fibers",
2006, Theorem 2.2.
-/

universe u

noncomputable section

open Cardinal Ideal

/-- For `i : (Cardinal.ord c).ToType`, the cardinality of the initial segment
below `i` is strictly less than `c`. -/
private def mk_Iio_ord_lt_proof {c : Cardinal} (i : c.ord.ToType) :
    PLift ( #(Set.Iio i) < c ) := ⟨by
  have hlt := mk_Iio_lt i (h := by rw [mk_ord_toType, Ordinal.type_toType])
  rwa [mk_ord_toType] at hlt
⟩

variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]
/-! ## Ordinal-indexed transfinite construction

Replace the Zorn approach (which needs `hk_countable`) with ordinal recursion
over V = {nonzero primes of T} × T/M². This eliminates the countability
assumption, using `ℵ₀ < #T` and `#R < #T` propagation instead.

### Architecture
- **Index set**: V = {q : Ideal T // q.IsPrime ∧ q ≠ ⊥} × (T ⧸ M²)
- **Ordinal**: κ = Cardinal.ord (#V)
- **Base**: R₀ = initial_NSubring (from NSubring.lean), closed up
- **Successor at α**: combined_step_card R(α) (q_α, ℓ_α)
- **Limit at λ**: transfinite union of R(β) for β < λ
- **Result**: A = R(κ) satisfies surjectivity, closedness, prime coverage
-/

/-! ### Helper lemma: build an NSubring from a union of predecessors

Extracted from the main transfinite construction to stay within the default
heartbeat budget. Given a family of NSubrings indexed by predecessors of `α`,
builds the union as an NSubring with cardinal bounds and prime preservation. -/

private noncomputable def mk_union_nsub_aux
    {ι : Type u} [LinearOrder ι] [IsWellOrder ι (· < ·)]
    (α : ι) (rings : ∀ β, β < α → NSubring T)
    (hne : ∃ β₀ : ι, β₀ < α)
    (hmono : ∀ ⦃β₁ β₂ : ι⦄ (hβ₁ : β₁ < α) (hβ₂ : β₂ < α),
      β₁ ≤ β₂ → (rings β₁ hβ₁).carrier ≤ (rings β₂ hβ₂).carrier)
    (hprimes : ∀ ⦃β₁ β₂ : ι⦄ (hβ₁ : β₁ < α) (hβ₂ : β₂ < α) (_ : β₁ ≤ β₂)
      (r : (rings β₁ hβ₁).carrier) (hmem : (r : T) ∈ (rings β₂ hβ₂).carrier),
      Prime r → Prime (⟨(r : T), hmem⟩ : (rings β₂ hβ₂).carrier))
    (hIH_cb : ∀ β (hβ : β < α), Cardinal.mk (rings β hβ).carrier ≤
      max Cardinal.aleph0 (Cardinal.mk {γ : ι // γ ≤ β}))
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (h_idx_lt_T : Cardinal.mk {β : ι // β < α} < Cardinal.mk T) :
    Σ' (U : NSubring T),
      (Cardinal.mk U.carrier < Cardinal.mk T) ∧
      (Cardinal.mk U.carrier ≤ max Cardinal.aleph0
        (Cardinal.mk {γ : ι // γ < α})) ∧
      (∀ β (hβ : β < α), (rings β hβ).carrier ≤ U.carrier) ∧
      (∀ β (hβ : β < α) (r : (rings β hβ).carrier),
        Prime r → ∀ (hmem : (r : T) ∈ U.carrier),
          Prime (⟨(r : T), hmem⟩ : U.carrier)) := by
  haveI : Nonempty {β : ι // β < α} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let lc : NSubringChain T {β : ι // β < α} :=
    { ring := fun ⟨β, hβ⟩ => rings β hβ
      mono := fun ⟨_, hβ₁⟩ ⟨_, hβ₂⟩ hle => hmono hβ₁ hβ₂ hle
      primes_preserved := fun ⟨_, hβ₁⟩ ⟨_, hβ₂⟩ hle r hr =>
        hprimes hβ₁ hβ₂ hle r ((hmono hβ₁ hβ₂ hle) r.2) hr }
  set U := lc.unionSubring with hU_def
  have hU_le := lc.le_union
  have hU_mem : ∀ x : ↥U, ∃ β : {β : ι // β < α},
      (x : T) ∈ (lc.ring β).carrier := fun x => lc.mem_union_iff.mp x.2
  haveI hU_local : IsLocalRing U := by
    apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    intro a
    obtain ⟨⟨β, hβ⟩, hβm⟩ := hU_mem a
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self
      (⟨(a : T), hβm⟩ : (rings β hβ).carrier) with hu | hu
    · left
      exact hu.map (Subring.inclusion (hU_le ⟨β, hβ⟩))
    · right
      exact (show Subring.inclusion (hU_le ⟨β, hβ⟩)
        (1 - ⟨(a : T), hβm⟩) = 1 - a from Subtype.ext rfl) ▸
        hu.map (Subring.inclusion (hU_le ⟨β, hβ⟩))
  refine ⟨⟨U,
    transfinite_union_isUFD lc U hU_le hU_mem,
    hU_local, ?_, ?_, ?_⟩, ?_, ?_, fun β hβ => hU_le ⟨β, hβ⟩, ?_⟩
  · set κ' := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
    have hU_eq : (U : Set T) = ⋃ β : {β : ι // β < α},
        ↑(lc.ring β).carrier := by
      rw [hU_def, NSubringChain.unionSubring]
      exact Subring.coe_iSup_of_directed lc.directed_carriers
    have h1 : Cardinal.mk ↥U ≤ Cardinal.mk {β : ι // β < α} *
        ⨆ (β : {β : ι // β < α}),
          Cardinal.mk ↑((lc.ring β).carrier : Set T) := by
      have := Cardinal.mk_iUnion_le
        (fun β : {β : ι // β < α} => ((lc.ring β).carrier : Set T))
      rwa [← hU_eq] at this
    have h2 : ⨆ (β : {β : ι // β < α}),
        Cardinal.mk ↑((lc.ring β).carrier : Set T) ≤ κ' :=
      ciSup_le fun ⟨β, hβ⟩ => (rings β hβ).card_le
    have h3 : Cardinal.mk {β : ι // β < α} ≤ κ' := by
      calc Cardinal.mk {β : ι // β < α}
          ≤ Cardinal.mk T := le_of_lt h_idx_lt_T
        _ = Cardinal.mk (IsLocalRing.ResidueField T) := hcard
        _ ≤ max Cardinal.aleph0 _ := le_max_right _ _
    calc Cardinal.mk ↥U
        ≤ Cardinal.mk {β : ι // β < α} *
          ⨆ (β : {β : ι // β < α}),
            Cardinal.mk ↑((lc.ring β).carrier : Set T) := h1
      _ ≤ Cardinal.mk {β : ι // β < α} * κ' :=
          mul_le_mul_right h2 _
      _ ≤ κ' * κ' := mul_le_mul_left h3 κ'
      _ ≤ max κ' κ' := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
      _ = κ' := max_self κ'
  · ext ⟨a, ha⟩
    simp only [Ideal.mem_comap, Subring.coe_subtype]
    constructor
    · intro hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu_T
      obtain ⟨⟨β, hβ⟩, hβm⟩ := hU_mem ⟨a, ha⟩
      by_contra h_nu
      have : ¬IsUnit (⟨a, hβm⟩ : (rings β hβ).carrier) :=
        fun hu => h_nu ((IsLocalRing.mem_maximalIdeal _).mp hx
          (hu.map (Subring.inclusion (hU_le ⟨β, hβ⟩))))
      have hmem' := (IsLocalRing.mem_maximalIdeal _).mpr this
      rw [(rings β hβ).maximal_ideal_eq] at hmem'
      exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem') hu_T
    · intro hx
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu_S
      exact (IsLocalRing.mem_maximalIdeal _).mp hx (hu_S.map U.subtype)
  · -- Height ≤ 1 for primes in the chain ring
    intro t ht P hP
    have hP_prime := hP.isPrime
    haveI : (Ideal.comap U.subtype P).IsPrime := hP_prime.comap _
    change (Ideal.comap U.subtype P).height ≤ ↑(1 : ℕ)
    rw [Ideal.height_le_iff]
    intro q hq_prime hq_lt
    suffices q = ⊥ by rw [this, Ideal.height_bot]
                      norm_cast
    by_contra hq_ne
    obtain ⟨s, hs_q, hs_ne⟩ : ∃ s : ↥U, s ∈ q ∧ s ≠ 0 := by
      by_contra h
      push Not at h
      exact hq_ne ((Submodule.eq_bot_iff q).mpr fun x hx => h x hx)
    obtain ⟨x, hx_P, hx_nq⟩ := Set.exists_of_ssubset hq_lt
    obtain ⟨⟨αs, hαs_lt⟩, hαs⟩ := hU_mem s
    obtain ⟨⟨αx, hαx_lt⟩, hαx⟩ := hU_mem x
    set γ := max αs αx
    have hγ_lt : γ < α := max_lt hαs_lt hαx_lt
    set inclγ := Subring.inclusion (hU_le ⟨γ, hγ_lt⟩)
    haveI : (Ideal.comap inclγ q).IsPrime := hq_prime.comap _
    set s' : (rings γ hγ_lt).carrier :=
      ⟨(s : T), hmono hαs_lt hγ_lt (le_max_left ..) hαs⟩
    have hs'_ne : s' ≠ 0 := fun h => hs_ne (Subtype.ext (congrArg
      (fun (x : (rings γ hγ_lt).carrier) => (x : T)) h))
    have hs'_q : s' ∈ Ideal.comap inclγ q :=
      show inclγ s' ∈ q from (show inclγ s' = s from Subtype.ext rfl) ▸ hs_q
    have hq'_ne : Ideal.comap inclγ q ≠ ⊥ := fun h => by
      rw [h] at hs'_q
      exact hs'_ne (Ideal.mem_bot.mp hs'_q)
    set x' : (rings γ hγ_lt).carrier :=
      ⟨(x : T), hmono hαx_lt hγ_lt (le_max_right ..) hαx⟩
    have hx'_nq : x' ∉ Ideal.comap inclγ q := fun h => by
      have h' : inclγ x' ∈ q := h
      rw [show inclγ x' = x from Subtype.ext rfl] at h'
      exact hx_nq h'
    have hq'_lt : Ideal.comap inclγ q <
        Ideal.comap (rings γ hγ_lt).carrier.subtype P :=
      lt_of_le_of_ne
        (fun r hr => (hq_lt.le (show inclγ r ∈ q from hr) : (inclγ r : T) ∈ P))
        (fun h => hx'_nq (h ▸ (hx_P : (x : T) ∈ P)))
    haveI : (Ideal.comap (rings γ hγ_lt).carrier.subtype P).IsPrime :=
      hP_prime.comap _
    have hq'_ht := (Ideal.height_le_iff (n := 1)).mp
      ((rings γ hγ_lt).height_bound t ht P hP) _ inferInstance hq'_lt
    haveI : IsDomain (rings γ hγ_lt).carrier := inferInstance
    exact absurd ((Ideal.height_le_iff (n := 0)).mp (by
      lift (Ideal.comap inclγ q).height to ℕ using ne_top_of_lt hq'_ht with n hn
      simp only [Nat.cast_lt] at hq'_ht
      simp only [Nat.cast_le]
      omega
    ) ⊥ Ideal.isPrime_bot (bot_lt_iff_ne_bot.mpr hq'_ne)) not_lt_bot
  · set n := Cardinal.mk {γ : ι // γ < α}
    have h_each_le : ∀ (β : ι) (hβ : β < α),
        Cardinal.mk (rings β hβ).carrier ≤ max Cardinal.aleph0 n := by
      intro β hβ
      exact le_trans (hIH_cb β hβ)
        (max_le_max_left _ (Cardinal.mk_subtype_mono (fun γ hγ => lt_of_le_of_lt hγ hβ)))
    have h_sup_le : ⨆ (β : {β : ι // β < α}),
        Cardinal.mk ↑((lc.ring β).carrier : Set T) ≤ max Cardinal.aleph0 n := by
      apply ciSup_le
      intro ⟨β, hβ⟩
      exact le_trans (le_of_eq rfl) (h_each_le β hβ)
    have hU_eq : (U : Set T) = ⋃ β : {β : ι // β < α},
        ↑(lc.ring β).carrier := by
      rw [hU_def, NSubringChain.unionSubring]
      exact Subring.coe_iSup_of_directed lc.directed_carriers
    have h1 : Cardinal.mk ↥U ≤ n *
        ⨆ (β : {β : ι // β < α}),
          Cardinal.mk ↑((lc.ring β).carrier : Set T) := by
      have := Cardinal.mk_iUnion_le
        (fun β : {β : ι // β < α} => ((lc.ring β).carrier : Set T))
      rwa [← hU_eq] at this
    have h_tight : Cardinal.mk ↥U ≤ max Cardinal.aleph0 n := by
      calc Cardinal.mk ↥U
          ≤ n * ⨆ (β : {β : ι // β < α}),
              Cardinal.mk ↑((lc.ring β).carrier : Set T) := h1
        _ ≤ n * max Cardinal.aleph0 n := mul_le_mul_right h_sup_le _
        _ ≤ max Cardinal.aleph0 n * max Cardinal.aleph0 n := by
            exact mul_le_mul_left (le_max_right _ _) _
        _ ≤ max (max Cardinal.aleph0 n) (max Cardinal.aleph0 n) :=
            Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
        _ = max Cardinal.aleph0 n := max_self _
    exact lt_of_le_of_lt h_tight (max_lt hT_aleph0 h_idx_lt_T)
  · set n := Cardinal.mk {γ : ι // γ < α}
    have h_each_le : ∀ (β : ι) (hβ : β < α),
        Cardinal.mk (rings β hβ).carrier ≤ max Cardinal.aleph0 n := by
      intro β hβ
      exact le_trans (hIH_cb β hβ)
        (max_le_max_left _ (Cardinal.mk_subtype_mono (fun γ hγ => lt_of_le_of_lt hγ hβ)))
    have h_sup_le : ⨆ (β : {β : ι // β < α}),
        Cardinal.mk ↑((lc.ring β).carrier : Set T) ≤ max Cardinal.aleph0 n := by
      apply ciSup_le
      intro ⟨β, hβ⟩
      exact le_trans (le_of_eq rfl) (h_each_le β hβ)
    have hU_eq : (U : Set T) = ⋃ β : {β : ι // β < α},
        ↑(lc.ring β).carrier := by
      rw [hU_def, NSubringChain.unionSubring]
      exact Subring.coe_iSup_of_directed lc.directed_carriers
    have h1 : Cardinal.mk ↥U ≤ n *
        ⨆ (β : {β : ι // β < α}),
          Cardinal.mk ↑((lc.ring β).carrier : Set T) := by
      have := Cardinal.mk_iUnion_le
        (fun β : {β : ι // β < α} => ((lc.ring β).carrier : Set T))
      rwa [← hU_eq] at this
    calc Cardinal.mk ↥U
        ≤ n * ⨆ (β : {β : ι // β < α}),
            Cardinal.mk ↑((lc.ring β).carrier : Set T) := h1
      _ ≤ n * max Cardinal.aleph0 n := mul_le_mul_right h_sup_le _
      _ ≤ max Cardinal.aleph0 n * max Cardinal.aleph0 n := by
          exact mul_le_mul_left (le_max_right _ _) _
      _ ≤ max (max Cardinal.aleph0 n) (max Cardinal.aleph0 n) :=
          Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
      _ = max Cardinal.aleph0 n := max_self _
  · intro β hβ r hr hmem
    exact transfinite_union_primes_preserved lc U hU_le hU_mem ⟨β, hβ⟩ r hr

/-- The transfinite construction via ordinal recursion: iterate `combined_step`
over all (prime, residue) pairs indexed by ordinals, building an N-subring A
of T that is surjective onto T/M², has every nonzero prime of T meeting A
nontrivially, and satisfies the closedness condition IT ∩ A = I.

This replaces the Zorn-based `transfinite_construction_zorn` which required
`hk_countable : #k ≤ ℵ₀` (false for our T). Instead takes `hT_aleph0 : ℵ₀ < #T`
and propagates cardinal bounds `#R < #T` through the chain. -/
private def transfinite_construction_proof
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) : PLift (
    ∃ (A : NSubring T),
      (Function.Surjective (fun r : A.carrier =>
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T))) ∧
      (∀ (I : Ideal A.carrier), I.FG →
        ∀ (c : A.carrier), (c : T) ∈ Ideal.map A.carrier.subtype I → c ∈ I) ∧
      (∀ (q : Ideal T), q.IsPrime → q ≠ ⊥ →
        ∃ (t : A.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) ) := ⟨by
  obtain ⟨R₀, hR₀_count⟩ := initial_NSubring hchar
  have hR₀_card : Cardinal.mk R₀.carrier < Cardinal.mk T :=
    lt_of_le_of_lt hR₀_count hT_aleph0
  have hM_ne_bot : IsLocalRing.maximalIdeal T ≠ ⊥ := by
    intro h
    obtain ⟨a, _, ha_mem, _, hreg⟩ := hdepth
    rw [h] at ha_mem
    simp only [Ideal.mem_bot] at ha_mem
    rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
    have hreg0 : IsSMulRegular T (0 : T) := ha_mem ▸ hreg.1
    exact one_ne_zero (hreg0 (show (0 : T) • (0 : T) = 0 • 1 by simp)).symm
  obtain ⟨S₀, hS₀_ext, hS₀_closed⟩ :=
    combined_step_surj_card R₀ 0 hM_not_assoc hAss_ht hR₀_card hT_aleph0 hcard hM_ne_bot
  obtain ⟨_, hS₀_closed, hS₀_card⟩ := hS₀_closed
  let V := {q : Ideal T // q.IsPrime ∧ q ≠ ⊥} × (T ⧸ IsLocalRing.maximalIdeal T ^ 2)
  -- #V ≤ #T: product of two sets each bounded by #T
  have hV_card : Cardinal.mk V ≤ Cardinal.mk T := by
    have hT_inf : Infinite T := Cardinal.infinite_iff.mpr (le_of_lt hT_aleph0)
    have h_primes_le : Cardinal.mk {q : Ideal T // q.IsPrime ∧ q ≠ ⊥} ≤ Cardinal.mk T := by
      calc Cardinal.mk {q : Ideal T // q.IsPrime ∧ q ≠ ⊥}
          ≤ Cardinal.mk (Ideal T) := Cardinal.mk_subtype_le _
        _ ≤ Cardinal.mk (Finset T) :=
            Cardinal.mk_le_of_surjective fun I =>
              IsNoetherian.noetherian (I : Ideal T)
        _ = Cardinal.mk T := Cardinal.mk_finset_of_infinite T
    have h_quot_le : Cardinal.mk (T ⧸ IsLocalRing.maximalIdeal T ^ 2) ≤ Cardinal.mk T :=
      Cardinal.mk_quotient_le
    have : Cardinal.mk V = Cardinal.mk {q : Ideal T // q.IsPrime ∧ q ≠ ⊥} *
        Cardinal.mk (T ⧸ IsLocalRing.maximalIdeal T ^ 2) := by
      show Cardinal.mk V = _
      simp only [V, Cardinal.mk_prod, Cardinal.lift_id]
    calc Cardinal.mk V
        = _ := this
      _ ≤ Cardinal.mk T * Cardinal.mk T := mul_le_mul' h_primes_le h_quot_le
      _ = Cardinal.mk T := Cardinal.mul_eq_self (le_of_lt hT_aleph0)
  suffices ∃ (A : NSubring T),
      (∀ ℓ : T ⧸ IsLocalRing.maximalIdeal T ^ 2,
        ∃ a : A.carrier, Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (a : T) = ℓ) ∧
      (∀ (I : Ideal A.carrier), I.FG →
        ∀ (c : A.carrier), (c : T) ∈ Ideal.map A.carrier.subtype I → c ∈ I) ∧
      (∀ (q : Ideal T), q.IsPrime → q ≠ ⊥ →
        ∃ (t : A.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) by
    obtain ⟨A, hA_surj, hA_closed, hA_primes⟩ := this
    exact ⟨A, fun ℓ => hA_surj ℓ, hA_closed, hA_primes⟩
  let κ := Cardinal.ord (Cardinal.mk V)
  haveI : Nonempty V :=
    ⟨⟨⟨IsLocalRing.maximalIdeal T,
       (IsLocalRing.maximalIdeal.isMaximal (R := T)).isPrime, hM_ne_bot⟩, 0⟩⟩
  haveI : Nonempty κ.ToType := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
    exact Cardinal.mk_ne_zero V
  obtain ⟨enum⟩ := Cardinal.eq.mp (Cardinal.mk_ord_toType (Cardinal.mk V))
  suffices h_chain : ∃ (chain : NSubringChain T κ.ToType) (A : NSubring T),
      (∀ α : κ.ToType, (chain.ring α).carrier ≤ A.carrier) ∧
      (∀ x : A.carrier, ∃ α : κ.ToType, (x : T) ∈ (chain.ring α).carrier) ∧
      (∀ α : κ.ToType, ∀ (I : Ideal (chain.ring α).carrier), I.FG →
        ∀ (c : (chain.ring α).carrier),
          (c : T) ∈ Ideal.map (chain.ring α).carrier.subtype I → c ∈ I) ∧
      (∀ ℓ : T ⧸ IsLocalRing.maximalIdeal T ^ 2, ∃ α : κ.ToType,
        ∃ (c : (chain.ring α).carrier),
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = ℓ) ∧
      (∀ (q : Ideal T), q.IsPrime → q ≠ ⊥ → ∃ α : κ.ToType,
        ∃ (t : (chain.ring α).carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) by
    obtain ⟨chain, A, hA_le, hA_mem, hclosed, hsurj, hcatch⟩ := h_chain
    refine ⟨A, ?_, ?_, ?_⟩
    · intro ℓ
      obtain ⟨α, c, hc⟩ := hsurj ℓ
      exact ⟨⟨(c : T), hA_le α c.2⟩, hc⟩
    · -- Closedness: lift f.g. ideal membership from A to some chain.ring(γ)
      intro I hI_fg c hc_mem
      classical
      have hfin_cover : ∀ (F : Finset A.carrier), ∃ α : κ.ToType,
          ∀ x ∈ F, (x : T) ∈ (chain.ring α).carrier := by
        intro F
        induction F using Finset.induction with
        | empty =>
          exact ⟨Classical.arbitrary _, fun _ h => absurd h (by simp)⟩
        | @insert a F' _ha ih =>
          obtain ⟨α₁, hα₁⟩ := ih
          obtain ⟨α₂, hα₂⟩ := hA_mem a
          exact ⟨max α₁ α₂, fun x hx => by
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact chain.mono (le_max_right α₁ α₂) hα₂
            · exact chain.mono (le_max_left α₁ α₂) (hα₁ x hx)⟩
      obtain ⟨s, hs⟩ := hI_fg
      obtain ⟨γ, hγ⟩ := hfin_cover (insert c s)
      have hgens_γ : ∀ g ∈ s, (g : T) ∈ (chain.ring γ).carrier :=
        fun g hg => hγ g (Finset.mem_insert_of_mem hg)
      have hc_γ : (c : T) ∈ (chain.ring γ).carrier :=
        hγ c (Finset.mem_insert_self c s)
      set c_γ : (chain.ring γ).carrier := ⟨(c : T), hc_γ⟩
      let s_γ : Finset (chain.ring γ).carrier :=
        s.attach.image (fun ⟨g, hg⟩ =>
          (⟨(g : T), hgens_γ g hg⟩ : (chain.ring γ).carrier))
      let J := Ideal.span (↑s_γ : Set (chain.ring γ).carrier)
      have hc_in_JT :
          (c_γ : T) ∈ Ideal.map (chain.ring γ).carrier.subtype J := by
        suffices h : Ideal.map A.carrier.subtype I ≤
            Ideal.map (chain.ring γ).carrier.subtype J by
          exact h hc_mem
        rw [← hs, Ideal.map_span, Ideal.map_span]
        apply Ideal.span_mono
        rintro t ⟨g, hg_mem, rfl⟩
        have hg := Finset.mem_coe.mp hg_mem
        exact ⟨⟨(g : T), hgens_γ g hg⟩,
          Finset.mem_coe.mpr (Finset.mem_image.mpr
            ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩), rfl⟩
      have hc_in_J : c_γ ∈ J :=
        hclosed γ J ⟨s_γ, rfl⟩ c_γ hc_in_JT
      let incl := Subring.inclusion (hA_le γ)
      have hJ_le_I : Ideal.map incl J ≤ I := by
        rw [← hs, Ideal.map_span]
        apply Ideal.span_mono
        rintro t ⟨x, hx_mem, rfl⟩
        simp only [Finset.mem_coe] at hx_mem
        rw [Finset.mem_image] at hx_mem
        obtain ⟨⟨g, hg⟩, _, rfl⟩ := hx_mem
        change (Subring.inclusion (hA_le γ)
          ⟨(g : T), hgens_γ g hg⟩ : A.carrier) ∈ (↑s : Set _)
        rw [show (Subring.inclusion (hA_le γ)
          ⟨(g : T), hgens_γ g hg⟩ : A.carrier) = g
          from Subtype.ext rfl]
        exact Finset.mem_coe.mpr hg
      have h_mem := hJ_le_I (Ideal.mem_map_of_mem incl hc_in_J)
      rwa [show incl c_γ = c from Subtype.ext rfl] at h_mem
    · intro q hq hq_ne
      obtain ⟨α, t, ht_q, ht_ne⟩ := hcatch q hq hq_ne
      exact ⟨⟨(t : T), hA_le α t.2⟩, ht_q, ht_ne⟩
  -- Bundled return type for WellFounded.fix: ring + predecessor + properties
  let RD := fun (α : κ.ToType) => Σ' (R : NSubring T) (prev : NSubring T),
    IsAExtension prev R ∧
    (Cardinal.mk R.carrier < Cardinal.mk T) ∧
    (∀ (I : Ideal R.carrier), I.FG →
      ∀ c : R.carrier, (c : T) ∈ Ideal.map R.carrier.subtype I → c ∈ I) ∧
    (∃ c : R.carrier,
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (c : T) = (enum α).2) ∧
    (∃ t : R.carrier, (t : T) ∈ (enum α).1.1 ∧ (t : T) ≠ 0) ∧
    (Cardinal.mk R.carrier ≤ max Cardinal.aleph0
      (Cardinal.mk {γ : κ.ToType // γ ≤ α}))
  -- IH_good: monotonicity + prime preservation for predecessors
  let IH_good := fun (α : κ.ToType) (IH : ∀ β, β < α → RD β) =>
    (∀ ⦃β₁ β₂ : κ.ToType⦄ (hβ₁ : β₁ < α) (hβ₂ : β₂ < α),
      β₁ ≤ β₂ → (IH β₁ hβ₁).1.carrier ≤ (IH β₂ hβ₂).1.carrier) ∧
    (∀ ⦃β₁ β₂ : κ.ToType⦄ (hβ₁ : β₁ < α) (hβ₂ : β₂ < α) (hle : β₁ ≤ β₂)
      (r : (IH β₁ hβ₁).1.carrier) (hmem : (r : T) ∈ (IH β₂ hβ₂).1.carrier),
      Prime r → Prime (⟨(r : T), hmem⟩ : (IH β₂ hβ₂).1.carrier))
  have mk_union_nsub : ∀ (α : κ.ToType) (IH : ∀ β, β < α → RD β)
      (_ : ∃ β₀ : κ.ToType, β₀ < α) (_ : IH_good α IH)
      (_ : ∀ β (hβ : β < α), Cardinal.mk (IH β hβ).1.carrier ≤
        max Cardinal.aleph0 (Cardinal.mk {γ : κ.ToType // γ ≤ β})),
      Σ' (U : NSubring T),
        (Cardinal.mk U.carrier < Cardinal.mk T) ∧
        (Cardinal.mk U.carrier ≤ max Cardinal.aleph0
          (Cardinal.mk {γ : κ.ToType // γ < α})) ∧
        (∀ β (hβ : β < α), (IH β hβ).1.carrier ≤ U.carrier) ∧
        (∀ β (hβ : β < α) (r : (IH β hβ).1.carrier),
          Prime r → ∀ (hmem : (r : T) ∈ U.carrier),
            Prime (⟨(r : T), hmem⟩ : U.carrier)) := by
    intro α IH hne hgood hIH_cb
    exact mk_union_nsub_aux α (fun β hβ => (IH β hβ).1) hne hgood.1 hgood.2
      hIH_cb hcard hT_aleph0
        (lt_of_lt_of_le ((mk_Iio_ord_lt_proof (c := Cardinal.mk V) α).down) hV_card)
  -- prevF: predecessor ring (min→S₀, limit→union, successor→ring(γ))
  let prevF : (α : κ.ToType) → (∀ β, β < α → RD β) → NSubring T :=
    fun α IH =>
    @dite _ (IsMin α) (Classical.dec _)
      (fun _ => S₀)
      (fun hmin =>
        @dite _ (Order.IsSuccLimit α) (Classical.dec _)
          (fun hlim =>
            @dite _ (IH_good α IH) (Classical.dec _)
              (fun hgood =>
                (mk_union_nsub α IH (not_isMin_iff.mp hmin) hgood
                  (fun β hβ => (IH β hβ).2.2.2.2.2.2.2)).1)
              (fun _ => S₀))
          (fun hlim =>
            let hprelim := (Order.not_isSuccLimit_iff.mp hlim).resolve_left hmin
            let hγ_ex := Order.not_isSuccPrelimit_iff_succ_eq.mp hprelim
            let hγ_lt := lt_of_lt_of_eq (Order.lt_succ_of_not_isMax hγ_ex.choose_spec.1)
              hγ_ex.choose_spec.2
            (IH hγ_ex.choose hγ_lt).1))
  have hprevF_card : ∀ (α : κ.ToType) (IH : ∀ β, β < α → RD β),
      Cardinal.mk (prevF α IH).carrier < Cardinal.mk T := by
    intro α IH
    simp only [prevF]
    split_ifs with hmin hlim hgood
    · exact hS₀_card
    · exact (mk_union_nsub α IH (not_isMin_iff.mp hmin) hgood
        (fun β hβ => (IH β hβ).2.2.2.2.2.2.2)).2.1
    · exact hS₀_card
    · exact (IH _ _).2.2.2.1
  have hprevF_cb : ∀ (α : κ.ToType) (IH : ∀ β, β < α → RD β),
      Cardinal.mk (prevF α IH).carrier ≤
        max Cardinal.aleph0 (Cardinal.mk {γ : κ.ToType // γ ≤ α}) := by
    intro α IH
    simp only [prevF]
    split_ifs with hmin hlim hgood
    · exact le_trans (le_trans hS₀_ext.card_le
        (max_le (le_refl _) hR₀_count)) (le_max_left ..)
    · exact le_trans
        (mk_union_nsub α IH (not_isMin_iff.mp hmin) hgood
          (fun β hβ => (IH β hβ).2.2.2.2.2.2.2)).2.2.1
        (max_le_max_left _ (Cardinal.mk_subtype_mono (fun γ hγ => le_of_lt hγ)))
    · exact le_trans (le_trans hS₀_ext.card_le
        (max_le (le_refl _) hR₀_count)) (le_max_left ..)
    · let hprelim := (Order.not_isSuccLimit_iff.mp hlim).resolve_left hmin
      let hγ_ex := Order.not_isSuccPrelimit_iff_succ_eq.mp hprelim
      let hγ_lt := lt_of_lt_of_eq (Order.lt_succ_of_not_isMax hγ_ex.choose_spec.1)
        hγ_ex.choose_spec.2
      exact le_trans (IH hγ_ex.choose hγ_lt).2.2.2.2.2.2.2
        (max_le_max_left _ (Cardinal.mk_subtype_mono (fun δ hδ =>
          le_trans hδ (le_of_lt hγ_lt))))
  let hbuildF : ∀ (α : κ.ToType), (∀ β, β < α → RD β) → RD α :=
    fun α IH =>
    let prev := prevF α IH
    let h := combined_step_card prev (enum α).2 (enum α).1.1
      (enum α).1.2.1 (enum α).1.2.2
      hM_not_assoc hAss_ht (hprevF_card α IH) hT_aleph0 hcard
    ⟨h.choose, prev, h.choose_spec.1, h.choose_spec.2.2.2.2,
      h.choose_spec.2.2.2.1, h.choose_spec.2.1, h.choose_spec.2.2.1,
      le_trans h.choose_spec.1.card_le
        (max_le (le_max_left ..) (hprevF_cb α IH))⟩
  let data : ∀ α : κ.ToType, RD α :=
    fun α => @WellFounded.fix κ.ToType RD (· < ·) wellFounded_lt hbuildF α
  let ring : κ.ToType → NSubring T := fun α => (data α).1
  -- prevF agrees with (data α).2.1 by WellFounded.fix_eq
  have hprevF_eq : ∀ (α : κ.ToType),
      (data α).2.1 = prevF α (fun γ hγ => data γ) :=
    fun α => congrArg (fun d => d.2.1) (WellFounded.fix_eq wellFounded_lt hbuildF α)
  -- Joint WF induction: monotonicity + prime preservation avoids circularity
  have hcombined : ∀ (α : κ.ToType),
      (∀ β, β < α → (ring β).carrier ≤ (data α).2.1.carrier) ∧
      (∀ ⦃β₁ β₂⦄, β₁ ≤ β₂ → β₂ ≤ α →
        ∀ (r : (ring β₁).carrier) (hmem : (r : T) ∈ (ring β₂).carrier),
          Prime r → Prime (⟨(r : T), hmem⟩ : (ring β₂).carrier)) := by
    refine fun α => WellFounded.induction wellFounded_lt α (C := fun α =>
      (∀ β, β < α → (ring β).carrier ≤ (data α).2.1.carrier) ∧
      (∀ ⦃β₁ β₂⦄, β₁ ≤ β₂ → β₂ ≤ α →
        ∀ (r : (ring β₁).carrier) (hmem : (r : T) ∈ (ring β₂).carrier),
          Prime r → Prime (⟨(r : T), hmem⟩ : (ring β₂).carrier))) ?_
    intro α IH_wf
    have hmono_lt : ∀ ⦃β₁ β₂ : κ.ToType⦄, β₁ ≤ β₂ → β₂ < α →
        (ring β₁).carrier ≤ (ring β₂).carrier := by
      intro β₁ β₂ hle hβ₂
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact le_refl _
      · exact ((IH_wf β₂ hβ₂).1 β₁ hlt).trans (data β₂).2.2.1.le
    have hprimes_lt : ∀ ⦃β₁ β₂ : κ.ToType⦄, β₁ ≤ β₂ → β₂ < α →
        ∀ (r : (ring β₁).carrier) (hmem : (r : T) ∈ (ring β₂).carrier),
          Prime r → Prime (⟨(r : T), hmem⟩ : (ring β₂).carrier) := by
      intro β₁ β₂ hle hβ₂ r hmem hr
      exact (IH_wf β₂ hβ₂).2 hle (le_refl _) r hmem hr
    have hgood_α : IH_good α (fun γ hγ => data γ) := by
      constructor
      · intro β₁ β₂ hβ₁ hβ₂ hle
        exact hmono_lt hle hβ₂
      · intro β₁ β₂ hβ₁ hβ₂ hle r hmem hr
        exact hprimes_lt hle hβ₂ r hmem hr
    have hring_le_prev_α : ∀ β, β < α →
        (ring β).carrier ≤ (data α).2.1.carrier := by
      intro β hβ
      rw [hprevF_eq α]
      by_cases hmin : IsMin α
      · exact absurd (hmin (le_of_lt hβ)) (not_le.mpr hβ)
      · simp only [prevF, dif_neg hmin]
        by_cases hlim : Order.IsSuccLimit α
        · simp only [dif_pos hlim, dif_pos hgood_α]
          exact (mk_union_nsub α (fun γ hγ => data γ) (not_isMin_iff.mp hmin) hgood_α
            (fun β hβ => (data β).2.2.2.2.2.2.2)).2.2.2.1 β hβ
        · simp only [dif_neg hlim]
          let hprelim := (Order.not_isSuccLimit_iff.mp hlim).resolve_left hmin
          let hγ_ex := Order.not_isSuccPrelimit_iff_succ_eq.mp hprelim
          let hγ_lt := lt_of_lt_of_eq
            (Order.lt_succ_of_not_isMax hγ_ex.choose_spec.1) hγ_ex.choose_spec.2
          rcases eq_or_lt_of_le (Order.lt_succ_iff_of_not_isMax
            hγ_ex.choose_spec.1 |>.mp (hγ_ex.choose_spec.2 ▸ hβ)) with rfl | hlt
          · exact le_refl _
          · exact ((IH_wf hγ_ex.choose hγ_lt).1 β hlt).trans
              (data hγ_ex.choose).2.2.1.le
    refine ⟨hring_le_prev_α, ?_⟩
    -- Prime transfer: β₁ ≤ β₂ ≤ α, key case is β₂ = α via prev(α)
    intro β₁ β₂ hle hle_α r hmem hr
    rcases eq_or_lt_of_le hle with rfl | hlt
    · convert hr using 1
    · rcases eq_or_lt_of_le hle_α with heq_α | hlt_α
      · have hβ₁_lt_α : β₁ < α := heq_α ▸ hlt
        have hmem_prevF : (r : T) ∈ (prevF α (fun γ hγ => data γ)).carrier := by
          have := hring_le_prev_α β₁ hβ₁_lt_α r.2
          rwa [hprevF_eq α] at this
        have hmem_prev : (r : T) ∈ (data α).2.1.carrier :=
          hring_le_prev_α β₁ hβ₁_lt_α r.2
        have h_nsub_eq := hprevF_eq α
        have prime_transport : ∀ (S₁ S₂ : NSubring T) (h : S₁ = S₂) (x : T) (hx : x ∈ S₁.carrier),
            Prime (⟨x, hx⟩ : S₁.carrier) → Prime (⟨x, h ▸ hx⟩ : S₂.carrier) := by
          intro S₁ S₂ h x hx hp
          cases h
          exact hp
        have prime_transport' : ∀ (S₁ S₂ : NSubring T) (h : S₂ = S₁) (x : T) (hx : x ∈ S₁.carrier),
            Prime (⟨x, hx⟩ : S₁.carrier) → Prime (⟨x, h ▸ hx⟩ : S₂.carrier) := by
          intro S₁ S₂ h x hx hp
          cases h
          exact hp
        have hmem_prevF_carrier : (r : T) ∈ (prevF α (fun γ hγ => data γ)).carrier := by
          rwa [← h_nsub_eq]
        have hprime_prevF : Prime (⟨(r : T), hmem_prevF_carrier⟩ :
            (prevF α (fun γ hγ => data γ)).carrier) := by
          by_cases hmin : IsMin α
          · exact absurd (hmin (le_of_lt hβ₁_lt_α)) (not_le.mpr hβ₁_lt_α)
          · by_cases hlim : Order.IsSuccLimit α
            · have h_prevF_eq : prevF α (fun γ hγ => data γ) =
                  (mk_union_nsub α (fun γ hγ => data γ) (not_isMin_iff.mp hmin) hgood_α
                    (fun β hβ => (data β).2.2.2.2.2.2.2)).1 := by
                simp only [prevF, dif_neg hmin, dif_pos hlim, dif_pos hgood_α]
              have hmem_u : (r : T) ∈
                  (mk_union_nsub α (fun γ hγ => data γ) (not_isMin_iff.mp hmin) hgood_α
                    (fun β hβ => (data β).2.2.2.2.2.2.2)).1.carrier := by
                rwa [← h_prevF_eq]
              exact prime_transport' _ _ h_prevF_eq _ hmem_u
                ((mk_union_nsub α (fun γ hγ => data γ) (not_isMin_iff.mp hmin) hgood_α
                    (fun β hβ => (data β).2.2.2.2.2.2.2)).2.2.2.2
                  β₁ hβ₁_lt_α r hr hmem_u)
            · have h_prevF_eq : prevF α (fun γ hγ => data γ) = ring
                  ((Order.not_isSuccPrelimit_iff_succ_eq.mp
                    ((Order.not_isSuccLimit_iff.mp hlim).resolve_left hmin)).choose) := by
                simp only [prevF, dif_neg hmin, dif_neg hlim]
                rfl
              let hprelim := (Order.not_isSuccLimit_iff.mp hlim).resolve_left hmin
              let hγ_ex := Order.not_isSuccPrelimit_iff_succ_eq.mp hprelim
              let hγ_lt := lt_of_lt_of_eq
                (Order.lt_succ_of_not_isMax hγ_ex.choose_spec.1) hγ_ex.choose_spec.2
              have hmem_ring_γ : (r : T) ∈ (ring hγ_ex.choose).carrier := by
                rwa [← h_prevF_eq]
              rcases eq_or_lt_of_le (Order.lt_succ_iff_of_not_isMax
                hγ_ex.choose_spec.1 |>.mp (hγ_ex.choose_spec.2 ▸ hβ₁_lt_α)) with rfl | hlt'
              · exact prime_transport' _ _ h_prevF_eq _ hmem_ring_γ hr
              · exact prime_transport' _ _ h_prevF_eq _ hmem_ring_γ
                  (hprimes_lt (le_of_lt hlt') hγ_lt r
                    (((IH_wf hγ_ex.choose hγ_lt).1 β₁ hlt').trans
                      (data hγ_ex.choose).2.2.1.le r.2) hr)
        have hprime_prev : Prime (⟨(r : T), hmem_prev⟩ : (data α).2.1.carrier) :=
          prime_transport _ _ h_nsub_eq.symm _ hmem_prevF_carrier hprime_prevF
        have hext := (data α).2.2.1
        have hprime_ring := hext.primes_preserved ⟨(r : T), hmem_prev⟩ hprime_prev
        cases heq_α
        convert hprime_ring using 1
      · exact hprimes_lt hle hlt_α r hmem hr
  have hring_le_prev : ∀ (α β : κ.ToType), β < α →
      (ring β).carrier ≤ (data α).2.1.carrier :=
    fun α => (hcombined α).1
  have hmono : ∀ ⦃β₁ β₂ : κ.ToType⦄, β₁ ≤ β₂ →
      (ring β₁).carrier ≤ (ring β₂).carrier := by
    intro β₁ β₂ hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_refl _
    · exact (hring_le_prev β₂ β₁ hlt).trans (data β₂).2.2.1.le
  have hprimes_pres : ∀ ⦃β₁ β₂ : κ.ToType⦄ (h : β₁ ≤ β₂)
      (r : (ring β₁).carrier), Prime r →
      Prime (⟨r.1, hmono h r.2⟩ : (ring β₂).carrier) := by
    intro β₁ β₂ hle r hr
    rcases eq_or_lt_of_le hle with rfl | hlt
    · convert hr using 1
    · exact (hcombined β₂).2 hle (le_refl β₂) r (hmono hle r.2) hr
  let chain : NSubringChain T κ.ToType :=
    { ring := ring
      mono := hmono
      primes_preserved := hprimes_pres }
  set U := chain.unionSubring with hU_def
  have hU_le : ∀ α, (chain.ring α).carrier ≤ U := chain.le_union
  have hU_mem : ∀ x : ↥U, ∃ α, (x : T) ∈ (chain.ring α).carrier :=
    fun x => chain.mem_union_iff.mp x.2
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
  have hU_card_le : Cardinal.mk ↥U ≤
      max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T)) := by
    have hU_eq : (U : Set T) = ⋃ α, ↑(chain.ring α).carrier := by
      rw [hU_def, NSubringChain.unionSubring]
      exact Subring.coe_iSup_of_directed chain.directed_carriers
    set κ' := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField T))
    have h1 : Cardinal.mk ↥U ≤ Cardinal.mk κ.ToType *
        ⨆ (α : κ.ToType), Cardinal.mk ↑((chain.ring α).carrier : Set T) := by
      have := Cardinal.mk_iUnion_le (fun α => ((chain.ring α).carrier : Set T))
      rwa [← hU_eq] at this
    have h2 : ⨆ (α : κ.ToType), Cardinal.mk ↑((chain.ring α).carrier : Set T) ≤ κ' :=
      ciSup_le fun α => (chain.ring α).card_le
    have h3 : Cardinal.mk κ.ToType ≤ κ' := by
      rw [Cardinal.mk_ord_toType]
      calc Cardinal.mk V ≤ Cardinal.mk T := hV_card
        _ = Cardinal.mk (IsLocalRing.ResidueField T) := hcard
        _ ≤ max Cardinal.aleph0 _ := le_max_right _ _
    calc Cardinal.mk ↥U
        ≤ Cardinal.mk κ.ToType *
          ⨆ (α : κ.ToType), Cardinal.mk ↑((chain.ring α).carrier : Set T) := h1
      _ ≤ Cardinal.mk κ.ToType * κ' := mul_le_mul_right h2 _
      _ ≤ κ' * κ' := mul_le_mul_left h3 κ'
      _ ≤ max κ' κ' := Cardinal.mul_le_max_of_aleph0_le_left (le_max_left ..)
      _ = κ' := max_self κ'
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
  have hU_height : ∀ (t : T), t ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {t}),
        Ideal.height (P.comap U.subtype) ≤ 1 := by
    intro t ht P hP
    have hP_prime := hP.isPrime
    haveI : (Ideal.comap U.subtype P).IsPrime := hP_prime.comap _
    change (Ideal.comap U.subtype P).height ≤ ↑(1 : ℕ)
    rw [Ideal.height_le_iff]
    intro q hq_prime hq_lt
    suffices q = ⊥ by rw [this, Ideal.height_bot]
                      norm_cast
    by_contra hq_ne
    obtain ⟨s, hs_q, hs_ne⟩ : ∃ s : ↥U, s ∈ q ∧ s ≠ 0 := by
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
  let A : NSubring T :=
    { carrier := U
      isUFD := transfinite_union_isUFD chain U hU_le hU_mem
      isLocalRing := hU_local
      card_le := hU_card_le
      maximal_ideal_eq := hU_maximal
      height_bound := hU_height }
  refine ⟨chain, A, chain.le_union, fun x => chain.mem_union_iff.mp x.2, ?_, ?_, ?_⟩
  · intro α I hI c hc
    exact (data α).2.2.2.2.1 I hI c hc
  · -- Surjectivity: use enum to find α covering each residue class ℓ
    intro ℓ
    have hq₀ : (IsLocalRing.maximalIdeal T).IsPrime :=
      (IsLocalRing.maximalIdeal.isMaximal (R := T)).isPrime
    let v : V := (⟨IsLocalRing.maximalIdeal T, hq₀, hM_ne_bot⟩, ℓ)
    let α := enum.symm v
    obtain ⟨c, hc⟩ := (data α).2.2.2.2.2.1
    have : (enum α).2 = ℓ := by simp [α, v]
    exact ⟨α, c, this ▸ hc⟩
  · -- Prime catching: use enum to find α covering each nonzero prime q
    intro q hq hq_ne
    let v : V := (⟨q, hq, hq_ne⟩, 0)
    let α := enum.symm v
    obtain ⟨t, ht_q, ht_ne⟩ := (data α).2.2.2.2.2.2.1
    have : (enum α).1.1 = q := by simp [α, v]
    exact ⟨α, t, this ▸ ht_q, ht_ne⟩
⟩

include T in theorem transfinite_construction
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) :
    ∃ (A : NSubring T),
      (Function.Surjective (fun r : A.carrier =>
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T))) ∧
      (∀ (I : Ideal A.carrier), I.FG →
        ∀ (c : A.carrier), (c : T) ∈ Ideal.map A.carrier.subtype I → c ∈ I) ∧
      (∀ (q : Ideal T), q.IsPrime → q ≠ ⊥ →
        ∃ (t : A.carrier), (t : T) ∈ q ∧ (t : T) ≠ 0) := by
  exact
    (transfinite_construction_proof
      hdepth hcard hchar hM_not_assoc hAss_ht hT_aleph0
    ).down
end
