/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.RingTheory.Filtration
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Lemma745
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LocalizationTopology

/-!
# Proposition 7.52: Exact support via Zorn

Infrastructure for Wedhorn's Proposition 7.52 — every prime ideal of a Huber ring
is the support of a continuous valuation. The main application is the Zorn
minimization step that produces a valuation in a specific rational open subset.

## Main results

* `locSubring_isOpen` : The ring of definition `D` is open in the localization topology.
* `locPairOfDefinition` : Pair of definition `(D, J)` on `Localization.Away s`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 7.52, §8.1
-/

@[expose] public section

open ValuationSpectrum PairOfDefinition

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### `locSubring` is open in `locTopology` -/

/-- The ring of definition `D = locSubring` is open in the localization topology.
This holds because `D ⊇ locNhd 0`, which is a basic neighborhood of `0`,
and `D` is an additive subgroup. -/
theorem locSubring_isOpen (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    @IsOpen (Localization.Away s) (locTopology P T s hopen)
      (locSubring P T s : Set (Localization.Away s)) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  apply AddSubgroup.isOpen_of_mem_nhds (H := (locSubring P T s).toAddSubgroup) (g := 0)
  exact Filter.mem_of_superset
    ((locBasis P T s hopen).hasBasis_nhds_zero.mem_of_mem (i := 0) trivial)
    (fun _ hx ↦ by obtain ⟨d, _, hd_eq⟩ := hx; rw [← hd_eq]; exact d.property)

/-! ### Pair of definition on the localization -/

/-- The subspace topology on `locSubring` from `locTopology` is the `locIdeal`-adic
topology. The neighborhoods of `0` in the subspace are `{locNhd n ∩ D}`, and since
`locNhd n ⊆ D`, these equal `{J^n}` = the `J`-adic neighborhood basis. -/
theorem locSubring_isAdic (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    @IsAdic (locSubring P T s) _
      ((locTopology P T s hopen).induced (locSubring P T s).subtype)
      (locIdeal P T s) := by
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  haveI : IsTopologicalRing (Localization.Away s) :=
    (locBasis P T s hopen).toRingFilterBasis.isTopologicalRing
  letI : TopologicalSpace (locSubring P T s) :=
    (locTopology P T s hopen).induced (locSubring P T s).subtype
  haveI : IsTopologicalRing (locSubring P T s) :=
    Subring.instIsTopologicalRing (locSubring P T s)
  rw [isAdic_iff]
  constructor
  · intro n
    rw [isOpen_induced_iff]
    refine ⟨locNhd P T s n, ?_, ?_⟩
    · exact ((locBasis P T s hopen).openAddSubgroup n).isOpen
    · ext ⟨x, hx_mem⟩
      simp only [Set.mem_preimage, Subring.coe_subtype, SetLike.mem_coe]
      constructor
      · rintro ⟨d, hd, hd_eq⟩
        rwa [show (⟨x, hx_mem⟩ : locSubring P T s) = d from
          Subtype.ext hd_eq.symm]
      · intro hx; exact ⟨⟨x, hx_mem⟩, hx, rfl⟩
  · intro U hU
    rw [nhds_induced, show (locSubring P T s).subtype 0 = 0 from map_zero _,
      Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨m, _, hm⟩ :=
      (locBasis P T s hopen).hasBasis_nhds_zero.mem_iff.mp hV
    exact ⟨m, fun x hx ↦ hVU (hm ⟨x, hx, rfl⟩)⟩

/-- **Pair of definition on `Localization.Away s`** with the localization topology
(Wedhorn §8.1). The ring of definition is `D = A₀[t₁/s, …, tₙ/s]` and the ideal
of definition is `J = I · D`. -/
noncomputable def locPairOfDefinition (P : PairOfDefinition A) (T : Finset A)
    (s : A) (hopen : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s) :
    @PairOfDefinition (Localization.Away s) _
      (locTopology P T s hopen) :=
  letI : TopologicalSpace (Localization.Away s) := locTopology P T s hopen
  { A₀ := locSubring P T s
    I := locIdeal P T s
    isOpen := locSubring_isOpen P T s hopen
    fg := locIdeal_fg P T s
    isAdic := locSubring_isAdic P T s hopen }

/-! ### Nonemptiness of the support set (Lemma 7.45 gives p ≤ v.supp)

For the Zorn argument, we need the set of primes above `𝔭` that are supports
of continuous valuations to be nonempty. This follows from Lemma 7.45. -/

/-- The set of primes `q ⊇ 𝔭` that are supports of points in `Spa(A, A⁺)`.
Ordered by `⊇` (reverse inclusion) for Zorn minimization. -/
def supportSet (_P : PairOfDefinition A) [PlusSubring A]
    (𝔭 : Ideal A) : Set (Ideal A) :=
  { q | q.IsPrime ∧ 𝔭 ≤ q ∧ ∃ v ∈ Spa A A⁺, v.supp = q }

/-- The support set is nonempty for non-open primes of complete affinoid rings
(Lemma 7.45 of Wedhorn). -/
theorem supportSet_nonempty (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    [PlusSubring A] {𝔭 : Ideal A} [𝔭.IsPrime]
    (h𝔭 : ¬IsOpen (𝔭 : Set A)) (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀) :
    (supportSet P 𝔭).Nonempty := by
  obtain ⟨v, hv_spa, hv_le, _⟩ :=
    P.exists_mem_spa_supp_ge_of_nonOpen_prime h𝔭 hAplus_le_A₀
  exact ⟨v.supp, inferInstance, hv_le, v, hv_spa, rfl⟩

/-! ### Completeness transfer

The Zorn minimization step applies Lemma 7.45 to `Localization.Away a` for
`a ∈ q \ 𝔭`. This requires `IsAdicComplete` on the localized ring's pair of
definition. We split into Hausdorff (provable via Krull) and Precomplete. -/

omit [TopologicalSpace A] [IsTopologicalRing A] in
/-- `Localization.Away s` is a domain when `A` is and `s ≠ 0`. -/
theorem locAway_isDomain [IsDomain A] {s : A} (hs : s ≠ 0) :
    IsDomain (Localization.Away s) :=
  IsLocalization.isDomain_localization (by
    rintro a ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hs))

omit [IsTopologicalRing A] in
/-- `locSubring` is a domain when `A` is and `s ≠ 0` (subring of a domain). -/
theorem locSubring_isDomain [IsDomain A] (P : PairOfDefinition A) (T : Finset A)
    {s : A} (hs : s ≠ 0) : IsDomain (locSubring P T s) :=
  haveI := locAway_isDomain hs; Subring.instIsDomainSubtypeMem _

omit [IsTopologicalRing A] in
/-- `locSubring` is noetherian when `A₀` is, because `locSubring` is a finitely
generated `A₀`-algebra (Hilbert basis theorem). -/
theorem locSubring_isNoetherian (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (T : Finset A) (s : A) : IsNoetherianRing (locSubring P T s) := by
  classical
  letI : Algebra P.A₀ (locSubring P T s) := (algebraMapD P T s).toAlgebra
  let S : Finset (locSubring P T s) := T.attach.image (fun ⟨t, ht⟩ ↦
    ⟨divByS t s, divByS_mem_locSubring P T s ht⟩)
  have hadj : Algebra.adjoin P.A₀ (↑S : Set (locSubring P T s)) = ⊤ := by
    rw [eq_top_iff]; intro ⟨x, hx⟩ _
    suffices hle : locSubring P T s ≤
        (Algebra.adjoin P.A₀ (↑S : Set (locSubring P T s))).toSubring.map
          (locSubring P T s).subtype by
      obtain ⟨y, hy_adj, hy_eq⟩ := hle hx
      rwa [show (⟨x, hx⟩ : locSubring P T s) = y from Subtype.ext hy_eq.symm]
    change Subring.closure _ ≤ _
    apply Subring.closure_le.mpr
    rintro y (⟨a, ha, rfl⟩ | ⟨⟨t, ht⟩, rfl⟩)
    · exact ⟨algebraMapD P T s ⟨a, ha⟩,
        Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : P.A₀), rfl⟩
    · refine ⟨⟨divByS t s, divByS_mem_locSubring P T s ht⟩,
        Algebra.subset_adjoin ?_, rfl⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩)
  haveI : Algebra.FiniteType P.A₀ (locSubring P T s) := ⟨⟨S, hadj⟩⟩
  exact Algebra.FiniteType.isNoetherianRing P.A₀ _

omit [IsTopologicalRing A] in
/-- `J = I · D` is proper when the multiplicative set `{sⁿ}` avoids the ideal
`I · A` in `A`.  (False without disjointness: e.g. `s ∈ I` gives `1 ∈ J`.) -/
theorem locIdeal_ne_top (P : PairOfDefinition A) (T : Finset A) (s : A)
    (hdisjoint : Disjoint (Submonoid.powers s : Set A)
      ((Ideal.map P.A₀.subtype P.I : Ideal A) : Set A)) :
    locIdeal P T s ≠ ⊤ := by
  intro heq
  have h1 : Ideal.map (locSubring P T s).subtype (locIdeal P T s) = ⊤ := by
    rw [heq, Ideal.map_top]
  rw [locIdeal, Ideal.map_map, show (locSubring P T s).subtype.comp (algebraMapD P T s) =
    (algebraMap A (Localization.Away s)).comp P.A₀.subtype from RingHom.ext fun _ ↦ rfl,
    ← Ideal.map_map] at h1
  exact ((IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers s)
    (Localization.Away s) (Ideal.map P.A₀.subtype P.I)).mpr hdisjoint) h1

omit [IsTopologicalRing A] in
/-- **Hausdorff part.** `locSubring` is `locIdeal`-adically separated. Uses Krull's
intersection theorem (`Ideal.iInf_pow_smul_eq_bot_of_noZeroSMulDivisors`). -/
theorem isHausdorff_locSubring [IsDomain A] (P : PairOfDefinition A)
    [IsNoetherianRing P.A₀] (T : Finset A) {s : A} (hs : s ≠ 0)
    (hdisjoint : Disjoint (Submonoid.powers s : Set A)
      ((Ideal.map P.A₀.subtype P.I : Ideal A) : Set A)) :
    IsHausdorff (locIdeal P T s) (locSubring P T s) := by
  haveI := locSubring_isDomain P T hs
  haveI := locSubring_isNoetherian P T s
  apply IsHausdorff.mk
  intro x hx
  have hmem : ∀ n, (x : locSubring P T s) ∈ locIdeal P T s ^ n := by
    intro n
    have h := hx n; rw [SModEq.zero] at h
    exact Submodule.smul_le.mpr (fun _ hr _ _ ↦ Ideal.mul_mem_right _ _ hr) h
  have hbot : (x : locSubring P T s) ∈ (⨅ n, locIdeal P T s ^ n : Ideal _) := by
    rw [Ideal.mem_iInf]; exact hmem
  rwa [Ideal.iInf_pow_eq_bot_of_isDomain (locIdeal P T s)
    (locIdeal_ne_top P T s hdisjoint), Ideal.mem_bot] at hbot

/-! ### Completion route for Prop 7.52

`isPrecomplete_locSubring` is FALSE in general (locSubring is a f.g. ALGEBRA,
not module, over A₀). Counterexample: A₀ = ℤ_p[[X]], I = (p), s = X, T = {1},
D = ℤ_p[[X]][1/X], J = (p). Sequence Σ pᵏ X⁻ᵏ is J-Cauchy with no limit in D.

The correct route for Prop 7.52's Zorn step: work in the COMPLETION
`presheafValue D` (= `Completion(Aₛ, locTopology)`), already defined in
Presheaf.lean. The completion has a natural complete pair of definition:
the closure of `locSubring` in the completion.

### Theorem chain for the completion route

1. `completedLocSubring D` — closure of im(locSubring) in presheafValue D
2. `completedLocSubring_isOpen` — open because locSubring is open and density
3. `completedLocIdeal D` — ideal of definition = im(locIdeal) in the closure
4. `completedLocPairOfDefinition D` — pair of definition on presheafValue D
5. `isAdicComplete_completedLocSubring` — complete (closed subring of complete ring)
6. Apply Lemma 7.45 to presheafValue D → Spa point w on Â[1/s]
7. Restrict w along A →+* presheafValue D to get Spa point on A

### Key helper needed

Step 2 is the core new lemma. It requires:
  `locSubring_isOpen` (proved above) +
  `closure of open additive subgroup in uniform completion is open`
The latter should follow from density of A[1/s] in its completion and
`AddSubgroup.isOpen_of_mem_nhds` applied to the closure. -/

/-! **KEY MISSING STEP for the completion route (step 2).**

The closure of `locSubring` in `presheafValue D` (= Completion(Aₛ)) is open.

**Proof sketch:** `locSubring` is open in `Aₛ` (by `locSubring_isOpen`), hence
it is in `nhds 0`. The embedding `ι : Aₛ → Â` is continuous and dense, so
`ι⁻¹(closure(ι(locSubring)))` contains `locSubring`, which is in `nhds 0`.
By density, `closure(ι(locSubring))` is in `nhds 0` of `Â`.
Since `closure(ι(locSubring))` is an additive subgroup of `Â` containing a
nhds-0 set, it is open by `AddSubgroup.isOpen_of_mem_nhds`.

**Signature** (to be stated in Presheaf.lean using RationalLocData):
  completedLocSubring_isOpen (D : RationalLocData A) :
    IsOpen (closure (D.coeRingHom '' (locSubring D.P D.T D.s : Set _)))

**Dependencies proven this pass:** locSubring_isOpen (step 1), locSubring_isAdic
(topology agreement), locSubring_isNoetherian (Hilbert basis), locIdeal_ne_top
(disjointness), isHausdorff_locSubring (Krull). -/

/-! ### Bridge: locSubring membership ↔ rational-open valuation condition

The key reusable fact for the completion route: if a valuation on the
localization `Aₛ` is bounded (≤ 1) on all elements of `locSubring`, then
the pullback valuation on `A` satisfies the rational-open condition
`v(t) ≤ v(s)` for `t ∈ T`. This is the bridge between:
  (Spa condition on the completion's ring of definition) →
  (rational-open membership for the pulled-back valuation on A).

In Wedhorn's proof of Thm 8.28, this is the step that converts
"v ∈ Spa(Â[1/s], D̂)" into "v|_A ∈ R(T/s)".
-/

omit [IsTopologicalRing A] in
/-- The rational-open condition `v(t) ≤ v(s)` follows from `t/s ∈ locSubring`
and `v(d) ≤ 1` for all `d ∈ locSubring`. Uses `IsLocalization.mk'_spec`.
This bridges the Spa condition on a completed ring of definition to
the rational-open membership of the pulled-back valuation (Wedhorn §8.1). -/
theorem vle_of_locSubring_bounded {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (P : PairOfDefinition A) (T : Finset A) (s : A)
    (v : Valuation (Localization.Away s) Γ₀)
    (hv_bdd : ∀ d ∈ locSubring P T s, v d ≤ 1)
    {t : A} (ht : t ∈ T) :
    v (algebraMap A (Localization.Away s) t) ≤
      v (algebraMap A (Localization.Away s) s) := by
  have hspec : divByS t s * algebraMap A (Localization.Away s) s =
      algebraMap A (Localization.Away s) t :=
    IsLocalization.mk'_spec _ t ⟨s, Submonoid.mem_powers s⟩
  rw [← hspec, v.map_mul]
  rcases eq_or_ne (v (algebraMap A (Localization.Away s) s)) 0 with hs | hs
  · simp [hs]
  · rw [mul_comm]
    exact ((mul_le_mul_right (hv_bdd _ (divByS_mem_locSubring P T s ht)))
      (v (algebraMap A _ s))).trans_eq (mul_one _)

end ValuationSpectrum
