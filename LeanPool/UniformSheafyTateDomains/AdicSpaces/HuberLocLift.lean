/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafTateStructure
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpvAITopology

/-!
# The restriction-map existence theorem at full Huber generality (Wedhorn Prop 7.52 → 8.2)

This file proves `HasLocLiftPowerBounded A` — the two facts Wedhorn's Lemma 8.1 derives
from Proposition 7.52 to construct the presheaf restriction maps ("This implies
`ϕ(s) ∈ B×` by Proposition 7.52. … This implies `ϕ(t)/ϕ(s) ∈ B⁺` by Proposition 7.52",
wedhorn.txt:3701-3706) — for **every** complete Huber ring with `A⁺` a ring of integral
elements. No Tate hypothesis, no noetherian hypothesis.

It sits **upstream of `StructureSheaf.lean`** so that `IsSheafy` (Wedhorn Def 8.26/9.31)
needs no `[HasLocLiftPowerBounded A]` parameter: the class is synthesized here, mirroring
the source's own layering (§7.52 before §8). The Tate-specialised legacy chain remains in
`FaithfulLocLift.lean`.

Contents (M8, plan artifact `decomposition-m8-huber-loclift.md`):
* the Huber [Hu2] 3.3(i) localization infrastructure (domination + place extension);
* `presheafValue_isAdicComplete`, `comap_canonicalMap_mem_rationalOpen` (relocated);
* `mem_plus_of_forall_spa_vle_one_huber` ([Hu2] Lemma 3.3(i), substantive direction);
* `isUnit_canonicalMap_s_huber` (Wedhorn 7.52(2) at `𝒪(V)`);
* `locLift_divByS_isPowerBounded_huber` (Wedhorn 7.52(1)/7.18 at `𝒪(V)`);
* `hasLocLiftPowerBounded_huber` + the priority-1150 instance.
-/

open ValuationSpectrum

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **Huber [Hu2] 3.3(i) localization step (huber2.txt:635-637).** If `x` is not integral over the
base `R` of an `R`-algebra `B`, then in a localization `Bx` of `B` away from `x` the canonical
inverse `IsLocalization.Away.invSelf x` is not a unit of the subalgebra
`R[x⁻¹] = Algebra.adjoin R {x⁻¹}`. *Proof.* If `invSelf x` were a unit of the subalgebra, its
inverse — which (by `x · invSelf x = 1` and uniqueness of inverses in `Bx`) is the image of `x` —
would lie in `adjoin R {invSelf x}`; then `isIntegral_of_isIntegral_adjoin_of_mul_eq_one` gives
`IsIntegral R (algebraMap B Bx x)`, and `IsLocalization.Away.isIntegral_of_isIntegral_map` descends
it to `IsIntegral R x`, contradicting the hypothesis. -/
theorem not_isUnit_invSelf_of_not_isIntegral
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (x : B)
    {Bx : Type*} [CommRing Bx] [Algebra B Bx] [IsLocalization.Away x Bx]
    [Algebra R Bx] [IsScalarTower R B Bx]
    (hx : ¬ IsIntegral R x) :
    ¬ IsUnit (⟨(IsLocalization.Away.invSelf x : Bx),
        Algebra.subset_adjoin (Set.mem_singleton _)⟩ :
      Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)}) := by
  intro hunit
  have hmul : IsLocalization.Away.invSelf x * algebraMap B Bx x = 1 := by
    rw [mul_comm]; exact IsLocalization.Away.mul_invSelf x
  -- `algebraMap B Bx x` lies in the subalgebra (it is the unique inverse of the unit `invSelf x`).
  have hx_mem : algebraMap B Bx x ∈ Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)} := by
    obtain ⟨w, hw⟩ := hunit.exists_right_inv
    have hcoe : IsLocalization.Away.invSelf x * (w : Bx) = 1 := by
      have h := congrArg
        (fun z : Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)} => (z : Bx)) hw
      simpa [Subalgebra.coe_mul, Subalgebra.coe_one] using h
    have hval : (w : Bx) = algebraMap B Bx x :=
      left_inv_eq_right_inv (by rw [mul_comm]; exact hcoe) hmul
    exact hval ▸ w.2
  have hint_adjoin : IsIntegral (Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)})
      (algebraMap B Bx x) := by
    have : (algebraMap (Algebra.adjoin R {(IsLocalization.Away.invSelf x : Bx)}) Bx)
        ⟨algebraMap B Bx x, hx_mem⟩ = algebraMap B Bx x := rfl
    exact this ▸ isIntegral_algebraMap
  exact hx (IsLocalization.Away.isIntegral_of_isIntegral_map x
    (isIntegral_of_isIntegral_adjoin_of_mul_eq_one (algebraMap B Bx x)
      (IsLocalization.Away.invSelf x) hmul hint_adjoin))

universe uL in
/-- **Field-case place extension (sub-ticket T-L4-EXT-FIELD).** A valuation `v` on a field `F`
extends along any field homomorphism `ι : F → L` to a valuation `w` on `L` with `v ≈ comap ι w`.
*Proof.* `v`'s valuation subring `O ⊆ F` maps (via the injective `ι`) to a local subring of `L`;
extend it to a valuation subring `V ⊆ L` dominating it (`LocalSubring.exists_le_valuationSubring`);
since `V` dominates the valuation ring `ι(O)` of the subfield `ι(F)`, `ι⁻¹(V) = O`, so
`comap ι V.valuation` has integer ring `O = v.valuationSubring`, hence is equivalent to `v`.

**Status: `sorry`** (T-L4-EXT-FIELD, parent T-L4-EXT). The classical place-extension theorem;
mathlib has the ingredients (`LocalSubring.exists_le_valuationSubring`, `ValuationSubring.valuation`)
but not the assembled existence. -/
theorem exists_comap_isEquiv_of_field_hom
    {F : Type*} {L : Type uL} [Field F] [Field L] (ι : F →+* L)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) :
    ∃ (Γ' : Type uL) (_ : LinearOrderedCommGroupWithZero Γ') (w : Valuation L Γ'),
      v.IsEquiv (Valuation.comap ι w) := by
  -- Extend `v`'s valuation subring `O` (mapped into `L`) to a valuation subring `V` of `L`
  -- dominating it, and take `w := V.valuation`.
  obtain ⟨V, hV⟩ :=
    LocalSubring.exists_le_valuationSubring (LocalSubring.map ι v.valuationSubring.toLocalSubring)
  refine ⟨V.ValueGroup, inferInstance, V.valuation, ?_⟩
  rw [Valuation.isEquiv_iff_valuationSubring]
  -- `(comap ι V.valuation).valuationSubring = V.comap ι`.
  have hVeq : V.valuation.valuationSubring = V := ValuationSubring.valuationSubring_valuation V
  have h1 : (Valuation.comap ι V.valuation).valuationSubring = V.comap ι := by
    ext x
    rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply,
      ← Valuation.mem_valuationSubring_iff, hVeq, ValuationSubring.mem_comap]
  rw [h1]
  -- Contraction `v.valuationSubring = V.comap ι`: `O := v.valuationSubring` maps into `V` (`hV`),
  -- and `O.toLocalSubring` is a maximal local subring (`isMax_toLocalSubring`); `V.comap ι` dominates
  -- `O`, so by maximality they are equal.
  have hsubF : v.valuationSubring.toLocalSubring.toSubring ≤ (V.comap ι).toLocalSubring.toSubring := by
    intro x hx
    have hιx : ι x ∈ V := by
      obtain ⟨hsub, -⟩ := LocalSubring.le_def.mp hV
      apply hsub
      rw [LocalSubring.map_toSubring]
      exact Subring.mem_map.mpr ⟨x, hx, rfl⟩
    exact ValuationSubring.mem_comap.mpr hιx
  have hle : v.valuationSubring.toLocalSubring ≤ (V.comap ι).toLocalSubring := by
    rw [LocalSubring.le_def]
    refine ⟨hsubF, ?_⟩
    -- Domination transfer: a unit of `V.comap ι` lying in `O` is a unit of `O`, pulled back from
    -- `hV`'s `IsLocalHom (ι(O) ↪ V)`.
    obtain ⟨hsub_L, hlocal_L⟩ := LocalSubring.le_def.mp hV
    refine ⟨fun a ha => ?_⟩
    -- `(↑a)⁻¹ = ↑b ∈ V.comap ι` from `ha`.
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    have hab : (a : F) * (b : F) = 1 := by
      have := congrArg (Subring.subtype (V.comap ι).toLocalSubring.toSubring) hb
      simpa using this
    have hιab : ι (a : F) * ι (b : F) = 1 := by rw [← map_mul, hab, map_one]
    have hιbV : ι (b : F) ∈ V := ValuationSubring.mem_comap.mp b.2
    have hmem_map : ι (a : F) ∈ (LocalSubring.map ι v.valuationSubring.toLocalSubring).toSubring := by
      rw [LocalSubring.map_toSubring]; exact Subring.mem_map.mpr ⟨a, a.2, rfl⟩
    -- `⟨ι ↑a, _⟩ : ι(O)` maps to a unit of `V`; `hlocal_L` ⟹ it is a unit of `ι(O)`.
    have haunit_L : IsUnit (Subring.inclusion hsub_L ⟨ι (a : F), hmem_map⟩) :=
      isUnit_iff_exists_inv.mpr ⟨⟨ι (b : F), hιbV⟩, Subtype.ext hιab⟩
    obtain ⟨c, hc⟩ := (hlocal_L.1 _ haunit_L).exists_right_inv
    have hιc : ι (a : F) * (c : L) = 1 := by
      have := congrArg (Subring.subtype _) hc
      simpa using this
    have hc_eq : (c : L) = ι (b : F) :=
      mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hιc) (hιc.trans hιab.symm)
    -- `ι (↑b) = ↑c ∈ ι(O)`, so `↑b ∈ O` (ι injective), hence `a` is a unit of `O`.
    have hb_mem_O : (b : F) ∈ v.valuationSubring := by
      have hcmem : (c : L) ∈ (LocalSubring.map ι v.valuationSubring.toLocalSubring).toSubring := c.2
      rw [hc_eq, LocalSubring.map_toSubring, Subring.mem_map] at hcmem
      obtain ⟨y, hy, hyeq⟩ := hcmem
      rwa [ι.injective hyeq] at hy
    exact isUnit_iff_exists_inv.mpr ⟨⟨(b : F), hb_mem_O⟩, Subtype.ext hab⟩
  exact ValuationSubring.toLocalSubring_injective
    (le_antisymm hle (ValuationSubring.isMax_toLocalSubring v.valuationSubring hle))

universe uS in
/-- **HU-d infrastructure (T-L4-EXT): Chevalley valuation extension along a ring inclusion.**
Given an `R`-algebra `S` with injective structure map and a valuation `s` on `R`, there is a
valuation `t` on `S` extending `s` (`s ≈ comap (algebraMap R S) t`). Huber [Hu2] 3.3(i)
(huber2.txt:641-643) uses this to extend the dominating valuation from the subring `R[x⁻¹]` to the
localization `Bx`. mathlib has the field-case ingredients (`LocalSubring.exists_le_valuationSubring`,
`IsLocalRing.exists_factor_valuationRing`) + the `Valuation.HasExtension` predicate, but no
constructive ring-case extension; assembled here via the support→fraction-field→Chevalley route.

**Status: `sorry`** (sub-ticket T-L4-EXT, parent T-L4 / Huber 3.3(i) HU-d). Standard commutative
algebra (Chevalley's extension theorem for rings), in mathlib's scope.

⚠ The lying-over prime `q'` (with `comap q' = supp s`) is a **necessary** hypothesis, not a
work-dodge: the bare-injective form is FALSE (a valuation need not extend if no prime of `S` lies
over `supp s` — the generic-fibre obstruction). Huber uses exactly this ("there exists a prime
ideal of A_a lying over q", huber2.txt:641); HU-d supplies `q'` from its minimal-prime setting. -/
theorem exists_valuation_extension_of_prime_over
    {R : Type*} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (s : Valuation R Γ)
    (q' : Ideal S) [q'.IsPrime] (hq' : Ideal.comap (algebraMap R S) q' = s.supp)
    (F : Type*) [Field F] [Algebra (R ⧸ s.supp) F] [IsFractionRing (R ⧸ s.supp) F]
    (L : Type uS) [Field L] [Algebra (S ⧸ q') L] [IsFractionRing (S ⧸ q') L] :
    ∃ (Γ' : Type uS) (_ : LinearOrderedCommGroupWithZero Γ') (t : Valuation S Γ'),
      s.IsEquiv (Valuation.comap (algebraMap R S) t) := by
  -- Step 1: `s` descends to a valuation on the domain `R ⧸ supp s` (Chevalley, ring case).
  haveI : (s.supp).IsPrime := inferInstance
  haveI : IsDomain (R ⧸ s.supp) := Ideal.Quotient.isDomain s.supp
  let sQuot : Valuation (R ⧸ s.supp) Γ := s.onQuot le_rfl
  -- Step 2: `sQuot` (support `0`) extends to the fraction field `F = Frac(R⧸supp s)`.
  have hsupp : sQuot.supp = ⊥ := s.supp_quot_supp
  have hS : nonZeroDivisors (R ⧸ s.supp) ≤ sQuot.supp.primeCompl := by
    intro x hx
    show x ∉ sQuot.supp
    intro hxsupp
    rw [hsupp] at hxsupp
    exact mem_nonZeroDivisors_iff_ne_zero.mp hx (Ideal.mem_bot.mp hxsupp)
  let sF : Valuation F Γ := sQuot.extendToLocalization hS F
  -- Step 3: embed `F ↪ L = Frac(S⧸q')` via the injective `R⧸supp ↪ S⧸q'` (from `hq'`).
  haveI : IsDomain (S ⧸ q') := Ideal.Quotient.isDomain q'
  let φRS : (R ⧸ s.supp) →+* (S ⧸ q') := Ideal.quotientMap q' (algebraMap R S) (le_of_eq hq'.symm)
  have hφRS_inj : Function.Injective φRS := Ideal.quotientMap_injective' (le_of_eq hq')
  have hgRL_inj : Function.Injective ((algebraMap (S ⧸ q') L).comp φRS) :=
    (IsFractionRing.injective (S ⧸ q') L).comp hφRS_inj
  let ι : F →+* L := IsFractionRing.lift hgRL_inj
  -- Step 4: extend `sF` across the field hom `ι` (place extension, T-L4-EXT-FIELD), then `comap`
  -- the resulting valuation of `L` down to `S` via `S → S⧸q' → L`.
  obtain ⟨Γ', _, w, hw⟩ := exists_comap_isEquiv_of_field_hom ι sF
  refine ⟨Γ', ‹LinearOrderedCommGroupWithZero Γ'›,
    Valuation.comap ((algebraMap (S ⧸ q') L).comp (Ideal.Quotient.mk q')) w, ?_⟩
  -- IsEquiv chase: `s ≈ comap (R→S) (comap (S→L) w)` via the commuting square + the `onQuot`/
  -- `extendToLocalization` equivalences and `hw` (light now that `F` is an `IsFractionRing` param).
  have h2 : ι.comp (algebraMap (R ⧸ s.supp) F) = (algebraMap (S ⧸ q') L).comp φRS := by
    ext x; exact IsFractionRing.lift_algebraMap hgRL_inj x
  have hsq : ((algebraMap (S ⧸ q') L).comp (Ideal.Quotient.mk q')).comp (algebraMap R S)
      = (ι.comp (algebraMap (R ⧸ s.supp) F)).comp (Ideal.Quotient.mk s.supp) :=
    calc ((algebraMap (S ⧸ q') L).comp (Ideal.Quotient.mk q')).comp (algebraMap R S)
        = (algebraMap (S ⧸ q') L).comp ((Ideal.Quotient.mk q').comp (algebraMap R S)) :=
          RingHom.comp_assoc _ _ _
      _ = (algebraMap (S ⧸ q') L).comp (φRS.comp (Ideal.Quotient.mk s.supp)) := by
          rw [(Ideal.quotientMap_comp_mk (le_of_eq hq'.symm)).symm]
      _ = ((algebraMap (S ⧸ q') L).comp φRS).comp (Ideal.Quotient.mk s.supp) :=
          (RingHom.comp_assoc _ _ _).symm
      _ = (ι.comp (algebraMap (R ⧸ s.supp) F)).comp (Ideal.Quotient.mk s.supp) := by rw [← h2]
  have hcomm : (Valuation.comap ((algebraMap (S ⧸ q') L).comp (Ideal.Quotient.mk q')) w).comap
        (algebraMap R S)
      = ((Valuation.comap ι w).comap (algebraMap (R ⧸ s.supp) F)).comap (Ideal.Quotient.mk s.supp) := by
    rw [← Valuation.comap_comp, ← Valuation.comap_comp, ← Valuation.comap_comp, hsq,
      RingHom.comp_assoc]
  have he2 : sF.comap (algebraMap (R ⧸ s.supp) F) = sQuot :=
    Valuation.ext fun y => Valuation.extendToLocalization_apply_map_apply sQuot hS F y
  have he1 : sQuot.comap (Ideal.Quotient.mk s.supp) = s := Valuation.ext fun _ => rfl
  clear_value ι sF sQuot
  have hchain := (hw.comap (algebraMap (R ⧸ s.supp) F)).comap (Ideal.Quotient.mk s.supp)
  rw [he2, he1] at hchain
  rw [hcomm]; exact hchain

universe uR in
/-- **Dominating valuation from a minimal prime below a prime** (Huber [Hu2] 3.3(i),
`huber2.txt:644-646`: "Choosing a valuation ring of `Frac(G[a⁻¹]/q)` which dominates the local ring
`(G[a⁻¹]/q)_{p/q}` we obtain a valuation `s` of `G[a⁻¹]` with `q = supp(s)`, `s(g) ≤ 1` for all
`g`, and `s(x) < 1` for all `x ∈ p`"). For a commutative ring `R`, a prime `p`, and a minimal prime
`q ≤ p`, there is a valuation `s` on `R` with support `q`, with `s ≤ 1` everywhere (the dominating
valuation of the local ring `(R/q)_{p/q}` has `R/q` inside its valuation ring), and `s < 1` on `p`.
-- INFRASTRUCTURE (general valuation/localization fact; mirrors Huber's domination step). -/
theorem exists_dominating_valuation_of_minimalPrime_le {R : Type uR} [CommRing R]
    {p : Ideal R} [hp : p.IsPrime] {q : Ideal R} (hq : q ∈ minimalPrimes R) (hqp : q ≤ p) :
    ∃ (Γ : Type uR) (_ : LinearOrderedCommGroupWithZero Γ) (s : Valuation R Γ),
      s.supp = q ∧ (∀ r, s r ≤ 1) ∧ (∀ y ∈ p, s y < 1) := by
  haveI : q.IsPrime := hq.1.1
  haveI : IsDomain (R ⧸ q) := Ideal.Quotient.isDomain q
  haveI hp'prime : (p.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hqp)
  -- Localize the domain `R/q` at the prime `p/q` (a local ring); dominate it by a valuation
  -- subring `V` of its fraction field `K`.
  set Dp := Localization.AtPrime (p.map (Ideal.Quotient.mk q)) with hDp
  obtain ⟨V, hVle, hVloc⟩ :=
    IsLocalRing.exists_factor_valuationRing (algebraMap Dp (FractionRing Dp))
  -- The composite `R → R/q → Dp → K` and the pulled-back valuation `s := V.valuation.comap f_R`.
  set f_R : R →+* FractionRing Dp :=
    (algebraMap Dp (FractionRing Dp)).comp ((algebraMap (R ⧸ q) Dp).comp (Ideal.Quotient.mk q))
    with hf_R
  refine ⟨_, _, V.valuation.comap f_R, ?_, ?_, ?_⟩
  · -- supp: `s r = 0 ↔ f_R r = 0 ↔ r ∈ q` (the composite `R/q → Dp → K` is injective on the domain)
    ext r
    rw [Valuation.comap_supp, Ideal.mem_comap, Valuation.mem_supp_iff, V.valuation.zero_iff, hf_R]
    have hinj1 : Function.Injective (algebraMap (R ⧸ q) Dp) :=
      IsLocalization.injective Dp (Ideal.primeCompl_le_nonZeroDivisors (Ideal.map (Ideal.Quotient.mk q) p))
    have hinj2 : Function.Injective (algebraMap Dp (FractionRing Dp)) :=
      IsFractionRing.injective Dp (FractionRing Dp)
    simp only [RingHom.comp_apply, map_eq_zero_iff _ hinj2, map_eq_zero_iff _ hinj1,
      Ideal.Quotient.eq_zero_iff_mem]
  · -- `s r ≤ 1`: `f_R r = algebraMap Dp K d` lies in `V` by `hVle`
    intro r
    exact (V.valuation_le_one_iff _).mpr (hVle _)
  · -- `s y < 1` for `y ∈ p`: `d = image of y` lies in the maximal ideal of `Dp`, dominated into `V`
    intro y hy
    rw [Valuation.comap_apply, hf_R]
    simp only [RingHom.comp_apply]
    have hd_max : (algebraMap (R ⧸ q) Dp) (Ideal.Quotient.mk q y) ∈ IsLocalRing.maximalIdeal Dp := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff Dp (Ideal.map (Ideal.Quotient.mk q) p)]
      exact Ideal.mem_map_of_mem _ hy
    have hc_nu : ¬ IsUnit (((algebraMap Dp (FractionRing Dp)).codRestrict V.toSubring hVle)
        ((algebraMap (R ⧸ q) Dp) (Ideal.Quotient.mk q y))) :=
      fun h => ((IsLocalRing.mem_maximalIdeal _).mp hd_max) (hVloc.map_nonunit _ h)
    exact (V.valuation_lt_one_iff _).mp ((IsLocalRing.mem_maximalIdeal _).mpr hc_nu)


omit [PlusSubring A] in
/-- **`IsAdicComplete` for the concrete pair of definition on `presheafValue C.base`.**

Derived from `IsAdic.isAdicComplete_iff` applied to the subspace uniformity
on `presheafValue_ringOfDef C.base` (the closed subring that is the topological
closure of the image of `locSubring`). The required ingredients:
- `IsAdic`: `presheafValue_isAdic` (`PresheafTateStructure.lean:804`).
- `CompleteSpace`: closed subset of complete `presheafValue C.base`.
- `T2Space`: subspace of T2 `presheafValue C.base`.

This unblocks the application of `Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime`
to the pair `presheafValue_pairOfDefinition_concrete P C.base`, which is the
foundation of the non-open prime case in `hSpa_points`. -/
theorem presheafValue_isAdicComplete
    [T2Space A]
    (D₀ : RationalLocData A) :
    IsAdicComplete (presheafValue_idealOfDef D₀) (presheafValue_ringOfDef D₀) := by
  have hadic : IsAdic (presheafValue_idealOfDef D₀) := presheafValue_isAdic D₀
  -- Equip `presheafValue_ringOfDef D₀` with the subspace UniformSpace structure
  -- inherited from `presheafValue D₀` (whose UniformSpace is the completion uniformity).
  letI : UniformSpace (presheafValue_ringOfDef D₀) :=
    UniformSpace.comap Subtype.val inferInstance
  -- Inherit `IsUniformAddGroup` from the ambient `presheafValue D₀`.
  haveI : IsUniformAddGroup (presheafValue_ringOfDef D₀) :=
    AddSubgroup.isUniformAddGroup (presheafValue_ringOfDef D₀).toAddSubgroup
  -- The ring of definition is closed, hence complete (subspace of complete space).
  haveI : CompleteSpace (presheafValue_ringOfDef D₀) :=
    (Subring.isClosed_topologicalClosure
      (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range).completeSpace_coe
  -- T2 inherited from ambient T2.
  haveI : T2Space (presheafValue_ringOfDef D₀) := inferInstance
  -- Apply the iff: IsAdic ⇒ (IsAdicComplete ↔ CompleteSpace ∧ T2Space).
  exact hadic.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

omit [PlusSubring A] [IsHuberRing A] in
/-- The `A`-shadow `comap D.canonicalMap w` of a Spa point `w` of `O_X(D)` lies in
`rationalOpen D.T D.s`. (The `supp`-free part of `exists_rationalOpen_of_completion_spa`.)
Uses `comap_mem_spa` + `D.comap_canonicalMap_vle` (the `t/s` bounds) + `D.s` unit-ness. -/
theorem comap_canonicalMap_mem_rationalOpen (D : RationalLocData A) [PlusSubring A]
    (hcont : Continuous D.canonicalMap)
    {w : Spv (presheafValue D)} (hw : w ∈ Spa (presheafValue D) (presheafValue D)⁺) :
    comap D.canonicalMap w ∈ rationalOpen D.T D.s := by
  refine ⟨comap_mem_spa hcont D.canonicalMap_integral hw, ?_, ?_⟩
  · intro t ht
    rw [comap_vle]
    exact D.comap_canonicalMap_vle hw.2 ht
  · exact @RationalLocData.comap_canonicalMap_not_vle_s_zero A _ _ _ D w.toValuativeRel

/-! ### Full-Huber (non-Tate) LL chain — Wedhorn Prop 8.2 / Lemma 8.1 via Prop 7.52 at
general complete f-adic base (M8 campaign). The Tate hypothesis entered the faithful
chain at exactly two points: `IsHuberRing (presheafValue D')` via
`presheafValue_isTateRing_concrete`, and the principal-pair continuity engine
`isContinuous_of_isInSpvAI_of_lt_one_principal` + `restrictIdealSingle` (which needs the
nonvanishing unit `π`). Both are replaced: `presheafValue_isHuberRing_huber` and the
`A°°`-form general engine `isContinuous_of_isInSpvAI_of_lt_one_AOO` +
the characteristic restriction `restrictIdeal · ⊥` (Huber's own `v = u|cΓ_u`). -/

/-- **Huber [Hu2] Lemma 3.3(i), substantive direction — general complete Huber base**
(huber2.txt:633-658; hypothesis-free in the source: NO Tate, NO noetherian, NO domain).
If `x ∈ presheafValue D'` has `w(x) ≤ 1` at every Spa point `w`, then `x ∈ B⁺`.
De-Tate'd `mem_plus_of_forall_spa_vle_one`: the witness valuation is
`restrictIdeal (t.comap algB) ⊥` (Huber's `v = u|cΓ_u`), continuous by
`isContinuous_of_isInSpvAI_of_lt_one_AOO` at `presheafValue_concretePair D'`. -/
theorem mem_plus_of_forall_spa_vle_one_huber
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (D' : RationalLocData A) (x : presheafValue D')
    (hx : ∀ w : Spv (presheafValue D'),
      w ∈ Spa (presheafValue D') (presheafValue D')⁺ → w.vle x 1) :
    x ∈ (presheafValue D')⁺ := by
  by_contra hxnot
  obtain ⟨w, hw_spa, hw⟩ :
      ∃ w : Spv (presheafValue D'),
        w ∈ Spa (presheafValue D') (presheafValue D')⁺ ∧ ¬ w.vle x 1 := by
    -- HU-a (huber2.txt:635-637): `x ∉ B⁺` ⟹ `x` is NOT integral over `B⁺` (contrapositive of
    -- `B⁺` integrally closed). This is what makes `x⁻¹` a non-unit of `B⁺[x⁻¹]`, opening Huber's
    -- localization argument. (v4.33: the subtype algebra is no longer instance-automatic —
    -- registered before first use.)
    letI : Algebra ↥(presheafValue D')⁺ (presheafValue D') := (presheafValue D')⁺.subtype.toAlgebra
    have hx_not_integral : ¬ IsIntegral ((presheafValue D')⁺) x := fun hint =>
      hxnot (IsRingOfIntegralElements.isIntegrallyClosed (B := (presheafValue D')⁺) x hint)
    -- HU-b: `x⁻¹` is a non-unit of `B⁺[x⁻¹] := adjoin B⁺ {x⁻¹} ⊆ B_x := Localization.Away x`.
    have hnonunit := not_isUnit_invSelf_of_not_isIntegral (Bx := Localization.Away x) x hx_not_integral
    -- HU-b': a maximal ideal `𝔪` of `B⁺[x⁻¹]` containing `x⁻¹` (proper since `x⁻¹` is a non-unit).
    obtain ⟨𝔪, h𝔪max, h𝔪ge⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hnonunit)
    have hxinv𝔪 : (⟨IsLocalization.Away.invSelf x, Algebra.subset_adjoin (Set.mem_singleton _)⟩ :
        Algebra.adjoin ↥(presheafValue D')⁺ {(IsLocalization.Away.invSelf x : Localization.Away x)})
        ∈ 𝔪 := h𝔪ge (Ideal.mem_span_singleton_self _)
    -- HU-c (huber2.txt:644-646): a minimal prime `q ⊆ 𝔪`; the dominating valuation `s` of
    -- `R := B⁺[x⁻¹]` with `supp s = q`, `s ≤ 1` on `R` (so on `B⁺` and at `x⁻¹`), `s < 1` on `𝔪`
    -- (so `s(x⁻¹) < 1`, since `x⁻¹ ∈ 𝔪`).
    haveI : 𝔪.IsPrime := h𝔪max.isPrime
    obtain ⟨q, hq_min, hq_le⟩ := Ideal.exists_minimalPrimes_le (J := 𝔪) bot_le
    obtain ⟨Γs, _, s, hs_supp, hs_le, hs_lt⟩ :=
      exists_dominating_valuation_of_minimalPrime_le hq_min hq_le
    -- HU-d (huber2.txt:646-648): a prime `q'` of `B_x` lying over `q = supp s` (Stacks 00FK, minimal
    -- prime under the injective inclusion `R := B⁺[x⁻¹] ↪ B_x`); extend `s` to a valuation `t` of
    -- `B_x` (`exists_valuation_extension_of_prime_over`); set `v := comap (B → B_x) (ofValuation t)`.
    set Radj := Algebra.adjoin ↑(presheafValue D')⁺ {(IsLocalization.Away.invSelf x : Localization.Away x)}
      with hRadj
    letI : Algebra ↑Radj (Localization.Away x) := Radj.val.toRingHom.toAlgebra
    have hinj : Function.Injective (algebraMap ↑Radj (Localization.Away x)) := Subtype.val_injective
    obtain ⟨q', hq'prime, hq'eq⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj q hq_min
    haveI := hq'prime
    obtain ⟨Γt, _, t, ht_equiv⟩ := exists_valuation_extension_of_prime_over s q'
      (hq'eq.trans hs_supp.symm) (FractionRing (↑Radj ⧸ s.supp)) (FractionRing (Localization.Away x ⧸ q'))
    -- ▸ Pre-extracted facts about the comap valuation `W a := t(algebraMap a)` (Huber's properties
    --   (b)(c)(d)), for the restricted-witness continuity wiring (T-SPVAI-4).
    have hW_le : ∀ f : presheafValue D', f ∈ (presheafValue D')⁺ →
        t (algebraMap (presheafValue D') (Localization.Away x) f) ≤ 1 := by
      intro f hf
      have hg_mem : algebraMap (presheafValue D') (Localization.Away x) f ∈ Radj := by
        rw [hRadj]
        exact (Algebra.adjoin (↥(presheafValue D')⁺)
          {(IsLocalization.Away.invSelf x : Localization.Away x)}).algebraMap_mem ⟨f, hf⟩
      have hkey := (ht_equiv
        (⟨algebraMap (presheafValue D') (Localization.Away x) f, hg_mem⟩ : ↥Radj) 1).mp
        (by rw [map_one]; exact hs_le _)
      rw [Valuation.comap_apply, Valuation.comap_apply, map_one, map_one] at hkey
      exact hkey
    have ht_inv : t (IsLocalization.Away.invSelf x) < 1 := by
      rw [← not_le]
      intro hge
      have h2 : s (1 : ↑Radj) ≤
          s ⟨IsLocalization.Away.invSelf x, Algebra.subset_adjoin (Set.mem_singleton _)⟩ := by
        refine (ht_equiv 1 _).mpr ?_
        simp only [Valuation.comap_apply, map_one]
        exact hge
      rw [map_one] at h2
      exact absurd h2 (not_le.mpr (hs_lt _ hxinv𝔪))
    -- Huber's continuity argument (c): `v < 1` on topologically nilpotent elements.
    have hW_lt_AOO : ∀ a : presheafValue D', IsTopologicallyNilpotent a →
        t (algebraMap (presheafValue D') (Localization.Away x) a) < 1 := by
      intro a ha
      obtain ⟨n, hn, hn1⟩ : ∃ n : ℕ, a ^ n * x ∈ (presheafValue D')⁺ ∧ 1 ≤ n := by
        have htend : Filter.Tendsto (fun n : ℕ => a ^ n * x) Filter.atTop (nhds 0) := by
          simpa using ha.mul_const x
        have hopen : IsOpen ((presheafValue D')⁺ : Set (presheafValue D')) :=
          IsRingOfIntegralElements.isOpen
        have hev := (htend.eventually (hopen.mem_nhds (Subring.zero_mem _))).and
          (Filter.eventually_ge_atTop 1)
        exact hev.exists
      have halg : algebraMap (presheafValue D') (Localization.Away x) (a ^ n) =
          algebraMap (presheafValue D') (Localization.Away x) (a ^ n * x) *
            IsLocalization.Away.invSelf x := by
        rw [map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
      have ht2 : t (algebraMap (presheafValue D') (Localization.Away x) (a ^ n)) < 1 := by
        rw [halg, map_mul]
        calc t (algebraMap (presheafValue D') (Localization.Away x) (a ^ n * x)) *
              t (IsLocalization.Away.invSelf x)
            ≤ 1 * t (IsLocalization.Away.invSelf x) := by gcongr; exact hW_le _ hn
          _ = t (IsLocalization.Away.invSelf x) := one_mul _
          _ < 1 := ht_inv
      rw [map_pow, map_pow] at ht2
      by_contra hge
      rw [not_lt] at hge
      exact absurd ht2 (not_lt.mpr (one_le_pow₀ hge))
    have hW_x : 1 < t (algebraMap (presheafValue D') (Localization.Away x) x) := by
      by_contra hle
      rw [not_lt] at hle
      have hprod : t (algebraMap (presheafValue D') (Localization.Away x) x) *
          t (IsLocalization.Away.invSelf x) = 1 := by
        rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      have hlt : t (algebraMap (presheafValue D') (Localization.Away x) x) *
          t (IsLocalization.Away.invSelf x) < 1 := by
        calc t (algebraMap (presheafValue D') (Localization.Away x) x) *
              t (IsLocalization.Away.invSelf x)
            ≤ 1 * t (IsLocalization.Away.invSelf x) := by gcongr
          _ = t (IsLocalization.Away.invSelf x) := one_mul _
          _ < 1 := ht_inv
      rw [hprod] at hlt; exact lt_irrefl 1 hlt
    -- ▸ General-Huber witness (Huber [Hu2] 3.3(i): `v = u|cΓ_u`): restrict
    --   `W := t.comap algB` by its characteristic subgroup, encoded as
    --   `restrictIdealSingle W 1` (`(W 1)⁻¹ = 1 ∈ cΓ_W`). No topologically nilpotent
    --   unit is involved — this is the non-Tate replacement for the principal-pair
    --   `restrictIdealSingle g` witness.
    set algB := algebraMap (presheafValue D') (Localization.Away x) with halgB_def
    have hW1 : (t.comap algB) 1 ≠ 0 := by
      rw [Valuation.comap_apply, map_one, map_one]
      exact one_ne_zero
    set rs := (t.comap algB).restrictIdealSingle 1 hW1 with hrs_def
    -- Bridge: `(ofValuation rs).vle a b ↔ rs a ≤ rs b`.
    have hbr : ∀ a b : presheafValue D', (ValuationSpectrum.ofValuation rs).vle a b ↔ rs a ≤ rs b := by
      intro a b
      letI : ValuativeRel (presheafValue D') := (ValuationSpectrum.ofValuation rs).toValuativeRel
      haveI : rs.Compatible := Valuation.Compatible.ofValuation rs
      exact Valuation.Compatible.vle_iff_le (v := rs) a b
    -- `W a = t(algB a)` definitionally, so the `hW_*` facts are facts about `W = t.comap algB`.
    refine ⟨ValuationSpectrum.ofValuation rs, ?_, ?_⟩
    · -- HU-e(1): `w' ∈ Spa(B, B⁺)` = `w'.IsContinuous ∧ ∀ f ∈ B⁺, w'.vle f 1` (`mem_spa_iff`).
      rw [mem_spa_iff]
      refine ⟨?_, ?_⟩
      · -- **Continuity of `w' = ofValuation rs`** (Huber [Hu2] Thm 3.1 reverse, general
        -- f-adic form): the A°°-engine `Spv.isContinuous_of_isInSpvAI_of_lt_one_AOO` at
        -- the concrete pair `presheafValue_concretePair D'` (Tate-free since T901), with
        --   • `h_in` (Huber (d)): the characteristic restriction is microbial, hence in
        --     `Spv(A, I)` for every `I` (`ofValuation_restrictIdealSingle_one_isInSpvAI`);
        --   • `h_le_AOO` (Huber (c), `≤`-form): `hW_lt_AOO` + `restrictIdealSingle_le_one`;
        --   • `h_lt_one` (ideal-of-definition decay): ideal elements are topologically
        --     nilpotent, so `hW_lt_AOO` + `restrictIdealSingle_lt_one`.
        have h_in : Spv.IsInSpvAI (ValuationSpectrum.ofValuation rs)
            (Ideal.map (presheafValue_concretePair D').A₀.subtype
              (presheafValue_concretePair D').I) :=
          ofValuation_restrictIdealSingle_one_isInSpvAI (t.comap algB) hW1 _
        letI : ValuativeRel (presheafValue D') := (ValuationSpectrum.ofValuation rs).toValuativeRel
        haveI hrsC : rs.Compatible := Valuation.Compatible.ofValuation rs
        have hequiv : (ValuativeRel.valuation (presheafValue D')).IsEquiv rs := fun a b =>
          (Valuation.Compatible.vle_iff_le
              (v := ValuativeRel.valuation (presheafValue D')) a b).symm.trans
            (Valuation.Compatible.vle_iff_le (v := rs) a b)
        have hlt : ∀ p q : presheafValue D',
            ((ValuativeRel.valuation (presheafValue D')) p <
                (ValuativeRel.valuation (presheafValue D')) q
              ↔ rs p < rs q) := fun p q => le_iff_le_iff_lt_iff_lt.mp (hequiv q p)
        have h_le_AOO : ∀ a : presheafValue D', IsTopologicallyNilpotent a →
            (ValuativeRel.valuation (presheafValue D')) a ≤ 1 := by
          intro a ha
          have hrs_le : rs a ≤ 1 :=
            restrictIdealSingle_le_one hW1 (le_of_lt (hW_lt_AOO a ha))
          have hkey := (hequiv a 1).mpr (by rw [map_one]; exact hrs_le)
          rwa [map_one] at hkey
        have h_lt_one : ∀ a ∈ (presheafValue_concretePair D').I,
            (ValuativeRel.valuation (presheafValue D'))
              ((presheafValue_concretePair D').A₀.subtype a) < 1 := by
          intro a ha
          have hnilp : IsTopologicallyNilpotent
              ((presheafValue_concretePair D').A₀.subtype a) :=
            (presheafValue_concretePair D').isTopologicallyNilpotent_of_mem ha
          have hrs_lt : rs ((presheafValue_concretePair D').A₀.subtype a) < 1 :=
            restrictIdealSingle_lt_one hW1 (hW_lt_AOO _ hnilp)
          have hkey := (hlt ((presheafValue_concretePair D').A₀.subtype a) 1).mpr
            (by rw [map_one]; exact hrs_lt)
          rwa [map_one] at hkey
        exact Spv.isContinuous_of_isInSpvAI_of_lt_one_AOO (presheafValue_concretePair D')
          (ValuationSpectrum.ofValuation rs) h_in h_le_AOO h_lt_one
      · -- `w' ≤ 1` on `B⁺` (Huber property (b)): `f ∈ B⁺` ⟹ `W f = t(algB f) ≤ 1` (`hW_le`),
        -- lifted to `rs` by `restrictIdealSingle_le_one`, then to `w'.vle` by `hbr`.
        intro f hf
        rw [hbr, map_one]
        exact restrictIdealSingle_le_one hW1 (hW_le f hf)
    · -- HU-e(2): `¬ w'.vle x 1`, i.e. `w'(x) > 1`: `1 < W x = t(algB x)` (`hW_x`, the Huber
      -- witness `s(x⁻¹) < 1` + `x⁻¹·x = 1`), lifted to `rs` by `restrictIdealSingle_one_lt`,
      -- then to `w'.vle` by `hbr`.
      intro hvle
      rw [hbr, map_one] at hvle
      exact absurd hvle (not_le.mpr (restrictIdealSingle_one_lt hW1 hW_x))
  exact hw (hx w hw_spa)

/-- **Wedhorn 7.52(1) + Def 7.14(1) at general complete Huber base**: Spa-bounded
elements of `presheafValue D'` are power-bounded. -/
theorem isPowerBounded_of_forall_vle_one_spa_of_complete_huber
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (D' : RationalLocData A) (x : presheafValue D')
    (hx : ∀ w : Spv (presheafValue D'),
      w ∈ Spa (presheafValue D') (presheafValue D')⁺ → w.vle x 1) :
    @TopologicalRing.IsPowerBounded (presheafValue D') _ inferInstance x :=
  IsRingOfIntegralElements.subset_powerBounded
    (mem_plus_of_forall_spa_vle_one_huber D' x hx)

/-- **Wedhorn 7.52(2) / Prop 8.2 (LL-unit) at general complete Huber base**: for
`R(D'.T/D'.s) ⊆ R(D.T/D.s)`, the image `D'.canonicalMap D.s` is a unit in
`presheafValue D'`. Same route as `isUnit_canonicalMap_s_faithful` (the pair-complete
unit criterion `isUnit_iff_forall_not_vle_zero_of_completePair` is already Tate-free);
only the `IsHuberRing (presheafValue D')` supply changes
(`presheafValue_isHuberRing_huber`). -/
theorem isUnit_canonicalMap_s_huber
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) := by
  haveI : IsHuberRing (presheafValue D') := presheafValue_isHuberRing_huber D'
  haveI : T2Space (presheafValue D') := inferInstance
  haveI : NonarchimedeanRing (presheafValue D') := inferInstance
  letI P_B : PairOfDefinition (presheafValue D') := presheafValue_concretePair D'
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete D'
  rw [isUnit_iff_forall_not_vle_zero_of_completePair P_B (D'.canonicalMap D.s)]
  intro w hw hvle
  have hmem := comap_canonicalMap_mem_rationalOpen D' (canonicalMap_continuous D') hw
  exact (h hmem).2.2 (by simpa only [comap_vle, map_zero] using hvle)

/-- **Wedhorn 7.52(1)/7.18 + Prop 8.2 (LL-bdd) at general complete Huber base**: the
localization lift of `t/D.s` is power-bounded in `presheafValue D'`. -/
theorem locLift_divByS_isPowerBounded_huber
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (t : A) (ht : t ∈ D.T) :
    @TopologicalRing.IsPowerBounded (presheafValue D') _ inferInstance
      (IsLocalization.Away.lift D.s (isUnit_canonicalMap_s_huber D D' h)
        (divByS t D.s)) := by
  set hu := isUnit_canonicalMap_s_huber D D' h with hu_def
  set x := IsLocalization.Away.lift D.s hu (divByS t D.s) with hx_def
  apply isPowerBounded_of_forall_vle_one_spa_of_complete_huber D' x
  intro w hw
  -- Pull back: `comap w ∈ rationalOpen D' ⊆ rationalOpen D`, giving `w(t) ≤ w(D.s)`.
  have hmem := comap_canonicalMap_mem_rationalOpen D' (canonicalMap_continuous D') hw
  have hvle0 : (comap D'.canonicalMap w).vle t D.s := (h hmem).2.1 t ht
  rw [comap_vle] at hvle0
  -- Lift spec: `x · D'.canonicalMap D.s = D'.canonicalMap t`.
  have hspec_alg : divByS t D.s * algebraMap A (Localization.Away D.s) D.s =
      algebraMap A (Localization.Away D.s) t :=
    IsLocalization.mk'_spec _ t ⟨D.s, Submonoid.mem_powers D.s⟩
  have hspec : x * D'.canonicalMap D.s = D'.canonicalMap t := by
    have e1 : x * IsLocalization.Away.lift D.s hu
          (algebraMap A (Localization.Away D.s) D.s) =
        IsLocalization.Away.lift D.s hu (algebraMap A (Localization.Away D.s) t) := by
      rw [hx_def, ← map_mul, hspec_alg]
    rwa [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at e1
  -- Cancel the unit `D'.canonicalMap D.s` to get `w(x) ≤ 1`.
  rw [← hspec] at hvle0
  -- `hvle0 : w.vle (x * D'.canonicalMap D.s) (D'.canonicalMap D.s)`.
  obtain ⟨cinv, hcinv⟩ := hu.exists_right_inv
  have hmul := w.mul_vle_mul_left hvle0 cinv
  rwa [mul_assoc, hcinv, mul_one] at hmul

/-- **`HasLocLiftPowerBounded` at full Huber generality** (Wedhorn Prop 8.2 / Lemma 8.1
via Prop 7.52, [Hu2] Lemma 3.3(i) & Thm 3.1 — none of which assume Tate). Discharges
`IsSheafy`'s class parameter for every complete Huber ring with `A⁺` a ring of integral
elements: the class fields are the two facts Wedhorn's Lemma 8.1 derives from Prop 7.52
("This implies `ϕ(s) ∈ B×` by Proposition 7.52. … This implies `ϕ(t)/ϕ(s) ∈ B⁺` by
Proposition 7.52", wedhorn.txt:3701-3706). Subsumes `hasLocLiftPowerBounded_faithful`
(drops `[IsTateRing A]`). -/
theorem hasLocLiftPowerBounded_huber
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] :
    HasLocLiftPowerBounded A where
  isUnit_canonicalMap_s := fun D D' h => isUnit_canonicalMap_s_huber D D' h
  locLift_divByS_isPowerBounded := fun D D' h t ht =>
    locLift_divByS_isPowerBounded_huber D D' h t ht

/-- **Instance form of the full-Huber LL package** (2026-07-17, M8): NO `[IsTateRing]`,
NO `[IsNoetherianRing]`. Priority above both the sorry-carrying noetherian-Tate
delegation chain and the Tate-only faithful instance, so every complete Huber bundle
synthesizes the general proven package. -/
instance (priority := 1150) hasLocLiftPowerBounded_huber_instance
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] :
    HasLocLiftPowerBounded A :=
  hasLocLiftPowerBounded_huber

end ValuationSpectrum
