/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AnalyticPoints
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AffinoidRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationCoarsening
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationPrimeConvex
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Valuation Continuity Infrastructure

Reusable infrastructure for proving continuity of valuations on Huber rings,
including the domination theorem, coarsening, restriction to convex subgroups
(`restrictToConvex`), and the v_ext extension construction.

## Main definitions

* `Valuation.coarsenByUnits` : Coarsening a valuation by a convex subgroup.
* `Valuation.restrictToConvex` : Restriction to a convex subgroup (Wedhorn 7.1.2).

## Main results

* `Valuation.isContinuous_of_ideal_pow_lt` : Continuity criterion for valuations.
* `Valuation.isContinuous_of_le_one_and_pow_cofinal` : Continuity from cofinal powers.
* `PairOfDefinition.exists_valuationSubring_of_prime` : Domination theorem.
* `PairOfDefinition.isContinuous_of_restriction_isContinuous` : Wedhorn Lemma 7.44(2).
* `PairOfDefinition.exists_pow_mul_mem_A₀` : Topological nilpotency normalization.
* `PairOfDefinition.vExt_well_defined` : Independence of normalization exponent.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Lemma 7.44, Lemma 7.45
-/

open Filter Topology

/-! ### Section 1: Continuity criterion for valuations on Huber rings -/

namespace Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Continuity criterion for valuations on Huber rings.** A valuation `v` is
continuous if for every `γ > 0`, some power `I^n` maps into
`{ a | v(a) < γ }`. -/
theorem isContinuous_of_ideal_pow_lt
    (P : PairOfDefinition A) (v : Valuation A Γ₀)
    (h : ∀ (γ : Γ₀), 0 < γ → ∃ n : ℕ,
      ∀ (a : P.A₀), a ∈ P.I ^ n → v (P.A₀.subtype a) < γ) :
    v.IsContinuous := by
  intro γ
  by_cases hγ : γ = 0
  · subst hγ; simp [not_lt_zero]
  · obtain ⟨n, hn⟩ := h γ (zero_lt_iff.mpr hγ)
    have h_sub : P.A₀.subtype '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) ⊆
        { a | v a < γ } := by
      rintro _ ⟨y, hy, rfl⟩
      exact hn y hy
    rw [show { a : A | v a < γ } =
      (v.ltAddSubgroup (Units.mk0 γ hγ) : Set A) from by ext; simp [ltAddSubgroup]]
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset
        ((P.pow_image_isOpen n).mem_nhds (Set.mem_image_of_mem _ (P.I ^ n).zero_mem))
        h_sub)

/-- Continuity via cofinal powers of a bound `g < 1`. -/
theorem isContinuous_of_le_one_and_pow_cofinal
    (P : PairOfDefinition A) (v : Valuation A Γ₀)
    (h_le : ∀ (a : P.A₀), v (P.A₀.subtype a) ≤ 1) {g : Γ₀}
    (h_gen : ∀ (a : P.A₀), a ∈ P.I → v (P.A₀.subtype a) ≤ g)
    (h_cofinal : ∀ (γ : Γ₀), 0 < γ → ∃ n : ℕ, g ^ n < γ) :
    v.IsContinuous := by
  apply isContinuous_of_ideal_pow_lt P
  intro γ hγ
  obtain ⟨n, hn⟩ := h_cofinal γ hγ
  suffices key : ∀ (m : ℕ) (a : P.A₀), a ∈ P.I ^ m → v (P.A₀.subtype a) ≤ g ^ m by
    exact ⟨n, fun a ha ↦ lt_of_le_of_lt (key n a ha) hn⟩
  intro m
  induction m with
  | zero => intro a _; simpa using h_le a
  | succ m ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy ↦ ?_) (fun x y hx hy ↦ ?_)
    · calc v (P.A₀.subtype (x * y))
          = v (P.A₀.subtype x) * v (P.A₀.subtype y) := by simp [map_mul]
        _ ≤ g ^ m * g := mul_le_mul' (ih x hx) (h_gen y hy)
        _ = g ^ (m + 1) := (pow_succ g m).symm
    · calc v (P.A₀.subtype (x + y))
          ≤ max (v (P.A₀.subtype x)) (v (P.A₀.subtype y)) := by
            simp only [map_add]; exact v.map_add _ _
        _ ≤ g ^ (m + 1) := max_le hx hy

end Valuation

/-! ### Section 2: Algebraic construction for Lemma 7.45 -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- The composition `A₀ → A → A/𝔭 → Frac(A/𝔭)` as a ring homomorphism. -/
noncomputable def toFractionQuotient (P : PairOfDefinition A)
    (𝔭 : Ideal A) : P.A₀ →+* FractionRing (A ⧸ 𝔭) :=
  ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
    (Ideal.Quotient.mk 𝔭)).comp P.A₀.subtype

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The kernel of `A₀ → Frac(A/𝔭)` equals `𝔭 ∩ A₀` when `𝔭` is prime. -/
theorem ker_toFractionQuotient (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime] :
    RingHom.ker (P.toFractionQuotient 𝔭) = Ideal.comap P.A₀.subtype 𝔭 := by
  ext a
  simp only [RingHom.mem_ker, toFractionQuotient, RingHom.comp_apply,
    Ideal.mem_comap, Subring.coe_subtype]
  constructor
  · intro h
    rwa [← Ideal.Quotient.eq_zero_iff_mem,
      ← (IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).eq_iff, map_zero]
  · intro h
    exact (congr_arg _ (Ideal.Quotient.eq_zero_iff_mem.mpr h)).trans (map_zero _)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The image of `I` under the range-restricted map is proper. -/
theorem image_I_ne_top (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] :
    Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I ≠ ⊤ := by
  haveI : (Ideal.comap P.A₀.subtype 𝔭).IsPrime := Ideal.IsPrime.comap P.A₀.subtype
  intro htop
  apply P.I_sup_prime_ne_top (𝔭₀ := Ideal.comap P.A₀.subtype 𝔭)
  have hker : RingHom.ker (P.toFractionQuotient 𝔭).rangeRestrict =
      Ideal.comap P.A₀.subtype 𝔭 := by
    rw [RingHom.ker_rangeRestrict, P.ker_toFractionQuotient]
  rw [← Ideal.map_top (f := (P.toFractionQuotient 𝔭).rangeRestrict),
    Ideal.map_eq_iff_sup_ker_eq_of_surjective _
      (P.toFractionQuotient 𝔭).rangeRestrict_surjective, top_sup_eq, hker] at htop
  exact htop

/-! ### The domination theorem applied to non-open primes -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Algebraic core of Lemma 7.45.** The domination theorem produces
a `ValuationSubring V` with `image(A₀) ⊆ V` and `image(I) ⊆ V.nonunits`. -/
theorem exists_valuationSubring_of_prime (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.toFractionQuotient 𝔭).range ≤ V.toSubring ∧
      (P.toFractionQuotient 𝔭).range.subtype ''
        (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits :=
  Ideal.image_subset_nonunits_valuationSubring _ P.image_I_ne_top

/-! ### Enlarged domination with rational-open control -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Enlarged domination.** Given a subring `R'` of `Frac(A/𝔭)` containing
`φ(A₀).range`, with the `I`-image ideal proper in `R'`, there exists a
valuation subring `V ⊇ R'` with `I`-images as nonunits. -/
theorem exists_valuationSubring_of_prime_enlarged (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    {R' : Subring (FractionRing (A ⧸ 𝔭))}
    (hR' : (P.toFractionQuotient 𝔭).range ≤ R')
    (hJ : Ideal.map ((P.toFractionQuotient 𝔭).codRestrict R'
      (fun a ↦ hR' ⟨a, rfl⟩)) P.I ≠ ⊤) :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      R' ≤ V.toSubring ∧
      R'.subtype '' (Ideal.map ((P.toFractionQuotient 𝔭).codRestrict R'
        (fun a ↦ hR' ⟨a, rfl⟩)) P.I : Set _) ⊆ V.nonunits :=
  Ideal.image_subset_nonunits_valuationSubring _ hJ

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] in
/-- For `x ∈ V.toSubring`, the valuation satisfies `V.valuation x ≤ 1`. -/
theorem valuation_le_one_of_mem {𝔭 : Ideal A} [𝔭.IsPrime]
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    {x : FractionRing (A ⧸ 𝔭)} (hx : x ∈ V.toSubring) :
    V.valuation x ≤ 1 :=
  V.valuation_le_one ⟨x, hx⟩

/-! ### Support computation -/

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Support of the pullback along `A → Frac(A/𝔭)` equals `𝔭`. -/
theorem supp_comap_quotient_fractionRing {𝔭 : Ideal A} [𝔭.IsPrime]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation (FractionRing (A ⧸ 𝔭)) Γ₀) :
    (v.comap ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
      (Ideal.Quotient.mk 𝔭))).supp = 𝔭 := by
  ext a
  simp only [Valuation.mem_supp_iff, Valuation.comap_apply, RingHom.comp_apply]
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  constructor
  · intro h
    by_contra ha
    have hk : (algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)))
        ((Ideal.Quotient.mk 𝔭) a) ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _
        (IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)))]
      exact fun h0 ↦ ha (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    exact hk (v.zero_iff.mp h)
  · intro h
    simp only [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

end PairOfDefinition

/-! ### Section 3: Concrete valuation from the domination theorem -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- The pulled-back valuation from `V : ValuationSubring(Frac(A/𝔭))` to `A`. -/
noncomputable def pulledBackValuation (_P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    (V : ValuationSubring (FractionRing (A ⧸ 𝔭))) :
    Valuation A V.ValueGroup :=
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  V.valuation.comap
    ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp (Ideal.Quotient.mk 𝔭))

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The pulled-back valuation has support equal to `𝔭`. -/
theorem pulledBackValuation_supp (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime] (V : ValuationSubring (FractionRing (A ⧸ 𝔭))) :
    (P.pulledBackValuation V).supp = 𝔭 :=
  supp_comap_quotient_fractionRing V.valuation

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The pulled-back valuation relates to `V.valuation` via `toFractionQuotient`. -/
theorem pulledBackValuation_eq_valuation_toFractionQuotient (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    (V : ValuationSubring (FractionRing (A ⧸ 𝔭))) (a : P.A₀) :
    P.pulledBackValuation V (P.A₀.subtype a) = V.valuation (P.toFractionQuotient 𝔭 a) :=
  rfl

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The pulled-back valuation has value `≤ 1` on `A₀`. -/
theorem pulledBackValuation_le_one (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hV : (P.toFractionQuotient 𝔭).range ≤ V.toSubring) (a : P.A₀) :
    P.pulledBackValuation V (P.A₀.subtype a) ≤ 1 := by
  rw [pulledBackValuation_eq_valuation_toFractionQuotient]
  exact (ValuationSubring.valuation_le_one_iff V _).mpr (hV ⟨a, rfl⟩)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The pulled-back valuation has value `< 1` on `I`. -/
theorem pulledBackValuation_lt_one (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hnonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits)
    {a : P.A₀} (ha : a ∈ P.I) :
    P.pulledBackValuation V (P.A₀.subtype a) < 1 := by
  rw [pulledBackValuation_eq_valuation_toFractionQuotient]
  exact (ValuationSubring.mem_nonunits_iff V).mp
    (hnonunits (Set.mem_image_of_mem _ (Ideal.mem_map_of_mem _ ha)))

end PairOfDefinition

/-! ### Section 4: Lemma 7.45 -- Analytic point construction -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Lemma 7.45 (algebraic core).** Produces `v` with `supp(v) = 𝔭`,
`v ≤ 1` on `A₀`, and `v < 1` on `I`. -/
theorem exists_valuationSubring_and_properties (P : PairOfDefinition A)
    [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] (_h : ¬IsOpen (𝔭 : Set A)) :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.pulledBackValuation V).supp = 𝔭 ∧
      (∀ a : P.A₀, P.pulledBackValuation V (P.A₀.subtype a) ≤ 1) ∧
      (∀ a : P.A₀, a ∈ P.I → P.pulledBackValuation V (P.A₀.subtype a) < 1) := by
  obtain ⟨V, hrange, hnonunits⟩ := P.exists_valuationSubring_of_prime (𝔭 := 𝔭)
  exact ⟨V, P.pulledBackValuation_supp V,
    P.pulledBackValuation_le_one hrange,
    fun a ha ↦ P.pulledBackValuation_lt_one hnonunits ha⟩

/-! ### Section 5: Continuity via MulArchimedean -/

/-- Valuation bound on `I` follows from bound on generators. -/
theorem valuation_le_on_ideal_of_le_on_generators
    {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {A₀ : Subring R} (v : Valuation R Γ₀) (h_le : ∀ (a : A₀), v (A₀.subtype a) ≤ 1)
    {I : Ideal A₀} {S : Finset A₀} (hS : Ideal.span (↑S : Set A₀) = I)
    {g : Γ₀} (h_gen : ∀ s ∈ S, v (A₀.subtype s) ≤ g) {a : A₀} (ha : a ∈ I) :
    v (A₀.subtype a) ≤ g := by
  rw [← hS] at ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact h_gen x (Finset.mem_coe.mp hx)
  | zero => simp only [map_zero]; exact zero_le
  | add x y _ _ hx hy =>
    calc v (A₀.subtype (x + y))
        ≤ max (v (A₀.subtype x)) (v (A₀.subtype y)) := by
          rw [map_add]; exact v.map_add _ _
      _ ≤ g := max_le hx hy
  | smul r x _ hx =>
    calc v (A₀.subtype (r • x))
        = v (A₀.subtype r) * v (A₀.subtype x) := by
          simp only [smul_eq_mul, map_mul]
      _ ≤ 1 * g := mul_le_mul' (h_le r) hx
      _ = g := one_mul g

omit [IsLinearTopology A A] in
/-- The pulled-back valuation is continuous when `MulArchimedean`. -/
theorem pulledBackValuation_isContinuous
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hrange : (P.toFractionQuotient 𝔭).range ≤ V.toSubring)
    (hnonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits)
    [MulArchimedean V.ValueGroup] :
    (P.pulledBackValuation V).IsContinuous := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  set v := P.pulledBackValuation V with hv_def
  obtain ⟨S, hS⟩ := P.fg
  obtain ⟨a₀, ha₀_I, ha₀_notp⟩ := P.exists_mem_I_not_mem_of_not_isOpen h𝔭
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hS_eq
    have hI_bot : P.I = ⊥ := by rw [← hS, hS_eq, Finset.coe_empty, Ideal.span_empty]
    exact ha₀_notp (by
      have : a₀ ∈ (⊥ : Ideal P.A₀) := hI_bot ▸ ha₀_I
      rw [Ideal.mem_bot.mp this, map_zero]; exact 𝔭.zero_mem)
  set g := S.sup' hSne (fun s ↦ v (P.A₀.subtype s)) with hg_def
  have hg1 : g < 1 := (Finset.sup'_lt_iff hSne).mpr fun s hs ↦
    P.pulledBackValuation_lt_one hnonunits
      (hS ▸ Ideal.subset_span (Finset.mem_coe.mpr hs))
  have h_gen : ∀ a : P.A₀, a ∈ P.I → v (P.A₀.subtype a) ≤ g :=
    fun a ha ↦ valuation_le_on_ideal_of_le_on_generators v
      (P.pulledBackValuation_le_one hrange) hS
      (fun s hs ↦ Finset.le_sup' (fun s ↦ v (P.A₀.subtype s)) hs) ha
  have hg0 : g ≠ 0 := ne_of_gt <|
    lt_of_lt_of_le (zero_lt_iff.mpr (show v (P.A₀.subtype a₀) ≠ 0 by
      rwa [ne_eq, ← Valuation.mem_supp_iff, P.pulledBackValuation_supp V]))
      (h_gen a₀ ha₀_I)
  exact Valuation.isContinuous_of_le_one_and_pow_cofinal P v
    (P.pulledBackValuation_le_one hrange) h_gen
    (fun γ hγ ↦ exists_pow_lt₀ hg1 (Units.mk0 γ hγ.ne'))

omit [IsLinearTopology A A] in
/-- **Lemma 7.45 (conditional on MulArchimedean).** -/
theorem exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hrange : (P.toFractionQuotient 𝔭).range ≤ V.toSubring)
    (hnonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits)
    [MulArchimedean V.ValueGroup]
    (hAplus : ∀ f ∈ (A⁺ : Set A), P.pulledBackValuation V f ≤ 1) :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔭 := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  set w := P.pulledBackValuation V
  refine ⟨ofValuation w, ⟨?_, ?_⟩, ?_⟩
  · exact isContinuous_ofValuation_of w
      (P.pulledBackValuation_isContinuous h𝔭 hrange hnonunits)
  · intro f hf; change w f ≤ w 1; rw [map_one]; exact hAplus f hf
  · rw [supp_ofValuation]; exact P.pulledBackValuation_supp V

end PairOfDefinition

/-! ### Section 6: Coarsening to MulArchimedean value group

The valuation subring `V` from the domination theorem may not have a MulArchimedean
value group. We coarsen by the largest convex subgroup of `(V.ValueGroup)ˣ` that
avoids a chosen I-generator's value (§7.1 of Wedhorn). -/

section CoarsenByUnits

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The composition `Γ₀ → WithZero(Γ₀ˣ) → WithZero(Γ₀ˣ ⧸ H)`
as a `MonoidWithZeroHom`. -/
noncomputable def coarsenMapOfValueGroup
    (H : ConvexSubgroup Γ₀ˣ) :
    Γ₀ →*₀ WithZero (Γ₀ˣ ⧸ H.toSubgroup) :=
  (WithZero.mapMonoidWithZeroHom (QuotientGroup.mk' H.toSubgroup)).comp
    (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom

/-- The coarsening map `Γ₀ → WithZero(Γ₀ˣ ⧸ H)` is monotone. -/
theorem coarsenMapOfValueGroup_monotone (H : ConvexSubgroup Γ₀ˣ) :
    Monotone (coarsenMapOfValueGroup H) := by
  intro a b hab
  unfold coarsenMapOfValueGroup
  simp only [MonoidWithZeroHom.comp_apply]
  apply WithZero.mapMonoidWithZeroHom_monotone _ H.quotientMk_monotone
  exact (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toOrderIso.monotone hab

/-- The coarsening map sends `0` to `0`. -/
theorem coarsenMapOfValueGroup_apply_zero (H : ConvexSubgroup Γ₀ˣ) :
    coarsenMapOfValueGroup H 0 = 0 := map_zero _

/-- The coarsening map sends a unit `g : Γ₀ˣ` to its quotient class. -/
theorem coarsenMapOfValueGroup_apply_unit (H : ConvexSubgroup Γ₀ˣ) (g : Γ₀ˣ) :
    coarsenMapOfValueGroup H (g : Γ₀) =
    ↑(QuotientGroup.mk' H.toSubgroup g) := by
  unfold coarsenMapOfValueGroup
  simp only [MonoidWithZeroHom.comp_apply]
  have : (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom (g : Γ₀) =
      (g : WithZero Γ₀ˣ) := by
    change (WithZero.withZeroUnitsEquiv (G := Γ₀)).symm (g : Γ₀) = ↑g
    exact WithZero.withZeroUnitsEquiv_symm_apply_coe g
  rw [this, WithZero.mapMonoidWithZeroHom_apply_coe]

end CoarsenByUnits

namespace Valuation

variable {R : Type*} [CommRing R]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Coarsening a valuation by a convex subgroup of the units of its value group. -/
noncomputable def coarsenByUnits
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    Valuation R (WithZero (Γ₀ˣ ⧸ H.toSubgroup)) :=
  v.map (coarsenMapOfValueGroup H) (coarsenMapOfValueGroup_monotone H)

/-- Unfolding lemma: `coarsenByUnits` applies the coarsening map to `v r`. -/
theorem coarsenByUnits_apply
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) (r : R) :
    v.coarsenByUnits H r = coarsenMapOfValueGroup H (v r) :=
  Valuation.map_apply _ _ _ _

/-- The support of a coarsened valuation equals the support of the original. -/
theorem coarsenByUnits_supp
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    (v.coarsenByUnits H).supp = v.supp := by
  ext r
  simp only [mem_supp_iff, coarsenByUnits_apply]
  constructor
  · intro h
    by_contra hr
    set u := Units.mk0 (v r) hr
    rw [show coarsenMapOfValueGroup H (v r) = coarsenMapOfValueGroup H (u : Γ₀) from rfl,
      coarsenMapOfValueGroup_apply_unit H u] at h
    exact WithZero.coe_ne_zero h
  · intro h; rw [h, map_zero]

/-- Coarsening preserves the bound `v a ≤ 1`. -/
theorem coarsenByUnits_le_one_of_le_one
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    {a : R} (ha : v a ≤ 1) :
    (v.coarsenByUnits H) a ≤ 1 := by
  have := coarsenMapOfValueGroup_monotone H ha
  simp only [coarsenByUnits_apply, map_one] at this ⊢
  exact this

/-- If `v(a) ≠ 0`, `Units.mk0 (v a) ∉ H`, and `v(a) ≤ 1`,
then `(v.coarsenByUnits H)(a) < 1`. -/
theorem coarsenByUnits_lt_one_of_not_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    {a : R} (ha_ne : v a ≠ 0)
    (ha_not_mem : Units.mk0 (v a) ha_ne ∉ H) (ha_le : v a ≤ 1) :
    v.coarsenByUnits H a < 1 := by
  set u := Units.mk0 (v a) ha_ne with hu_def
  have hu_lt : u < 1 := lt_of_le_of_ne (Units.val_le_val.mp ha_le)
    (fun h ↦ ha_not_mem (h ▸ H.toSubgroup.one_mem))
  rw [coarsenByUnits_apply, show v a = (u : Γ₀) from rfl, coarsenMapOfValueGroup_apply_unit H u]
  exact WithZero.coe_lt_one.mpr (H.quotientMk_lt_one_of_not_mem hu_lt ha_not_mem)

/-! ### Restriction of a valuation to a convex subgroup (Wedhorn's retraction 7.1.2) -/

open Classical in
/-- **Restriction of a valuation to a convex subgroup** (Wedhorn 7.1.2).
The restricted valuation keeps values whose unit part is in `H` and zeros out the rest.
Requires `∀ r, v r ≤ 1` for multiplicativity. -/
noncomputable def restrictToConvex
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) :
    Valuation R (WithZero H.toSubgroup) where
  toFun r :=
    if h : v r = 0 then 0
    else if hm : Units.mk0 (v r) h ∈ H then some ⟨Units.mk0 (v r) h, hm⟩
    else 0
  map_zero' := by simp [map_zero]
  map_one' := by
    simp only [map_one]
    have h1 : (1 : Γ₀) ≠ 0 := one_ne_zero
    have hm : Units.mk0 (1 : Γ₀) h1 ∈ H := by
      rw [show Units.mk0 (1 : Γ₀) h1 = 1 from Units.ext rfl]; exact one_mem H
    simp only [h1, dite_false, dif_pos hm,
      show (1 : WithZero H.toSubgroup) = ((1 : H.toSubgroup) : WithZero H.toSubgroup) from rfl]
    congr 1; exact Subtype.ext (Units.ext rfl)
  map_mul' x y := by
    have not_mem_of_le' {u w : Γ₀ˣ} (hu : u ∉ H) (hu1 : u ≤ 1) (hw1 : w ≤ u) : w ∉ H :=
      fun hw_mem ↦ hu (H.convex hw_mem (one_mem H) hw1 hu1)
    have unit_le_one' : ∀ (r : R) (hr : v r ≠ 0), Units.mk0 (v r) hr ≤ 1 :=
      fun r hr ↦ Units.val_le_val.mp (hle r)
    by_cases hx : v x = 0
    · have hxy : v (x * y) = 0 := by rw [map_mul, hx, zero_mul]
      simp only [hxy, hx, dif_pos, zero_mul]
    by_cases hy : v y = 0
    · have hxy : v (x * y) = 0 := by rw [map_mul, hy, mul_zero]
      simp only [hxy, hy, dif_pos, mul_zero]
    have hxy_ne : v (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx hy
    have huxy_eq : Units.mk0 (v (x * y)) hxy_ne =
        Units.mk0 (v x) hx * Units.mk0 (v y) hy := Units.ext (map_mul v x y)
    by_cases hmx : Units.mk0 (v x) hx ∈ H <;> by_cases hmy : Units.mk0 (v y) hy ∈ H
    · have hmxy : Units.mk0 (v (x * y)) hxy_ne ∈ H := huxy_eq ▸ mul_mem hmx hmy
      simp only [hx, hy, hxy_ne, dif_neg, dif_pos hmx, dif_pos hmy, dif_pos hmxy, not_false_eq_true]
      rw [show (some (⟨Units.mk0 (v x) hx, hmx⟩ : H.toSubgroup) : WithZero H.toSubgroup) =
        (↑(⟨Units.mk0 (v x) hx, hmx⟩ : H.toSubgroup) : WithZero H.toSubgroup) from rfl,
        show (some (⟨Units.mk0 (v y) hy, hmy⟩ : H.toSubgroup) : WithZero H.toSubgroup) =
        (↑(⟨Units.mk0 (v y) hy, hmy⟩ : H.toSubgroup) : WithZero H.toSubgroup) from rfl,
        ← WithZero.coe_mul]
      congr 1
      exact Subtype.ext huxy_eq
    · have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]; intro hmem
        exact hmy (by have := mul_mem (inv_mem hmx) hmem; rwa [inv_mul_cancel_left] at this)
      simp only [hx, hy, hxy_ne, dif_neg, dif_pos hmx, dif_neg hmy, dif_neg hmxy, not_false_eq_true,
        mul_zero]
    · have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]; intro hmem
        exact hmx (by have := mul_mem hmem (inv_mem hmy); rwa [mul_inv_cancel_right] at this)
      simp only [hx, hy, hxy_ne, dif_neg, dif_neg hmx, dif_pos hmy, dif_neg hmxy, not_false_eq_true,
        zero_mul]
    · have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]; intro hmem
        have hle_ux : Units.mk0 (v x) hx * Units.mk0 (v y) hy ≤ Units.mk0 (v x) hx :=
          Units.val_le_val.mp (show (v x) * (v y) ≤ v x from by
            calc v x * v y ≤ v x * 1 := mul_le_mul_right (hle y) (v x)
              _ = v x := mul_one _)
        exact not_mem_of_le' hmx (unit_le_one' x hx) hle_ux hmem
      simp only [hx, hy, hxy_ne, dif_neg, dif_neg hmx, dif_neg hmy, dif_neg hmxy, not_false_eq_true,
        mul_zero]
  map_add_le_max' x y := by
    set f : R → WithZero H.toSubgroup := fun r ↦
      if h : v r = 0 then 0
      else if hm : Units.mk0 (v r) h ∈ H then some ⟨Units.mk0 (v r) h, hm⟩
      else 0
    change f (x + y) ≤ max (f x) (f y)
    by_cases hxy : v (x + y) = 0
    · simp only [f, hxy, dif_pos]; exact bot_le
    by_cases hmxy : Units.mk0 (v (x + y)) hxy ∈ H
    · rcases le_total (v x) (v y) with hvxy | hvyx
      · have hv_le : v (x + y) ≤ v y := (v.map_add x y).trans (max_eq_right hvxy).le
        suffices h : f (x + y) ≤ f y from h.trans (le_max_right _ _)
        have hy : v y ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hxy) hv_le)
        by_cases hmy : Units.mk0 (v y) hy ∈ H
        · simp only [f, hxy, hy, dif_pos hmxy, dif_pos hmy]
          exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
            (Units.val_le_val.mp hv_le))
        · exfalso; exact hmy (H.convex hmxy (one_mem H)
            (Units.val_le_val.mp hv_le) (Units.val_le_val.mp (hle y)))
      · have hv_le : v (x + y) ≤ v x := (v.map_add x y).trans (max_eq_left hvyx).le
        suffices h : f (x + y) ≤ f x from h.trans (le_max_left _ _)
        have hx' : v x ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hxy) hv_le)
        by_cases hmx : Units.mk0 (v x) hx' ∈ H
        · simp only [f, hxy, hx', dif_pos hmxy, dif_pos hmx]
          exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
            (Units.val_le_val.mp hv_le))
        · exfalso; exact hmx (H.convex hmxy (one_mem H)
            (Units.val_le_val.mp hv_le) (Units.val_le_val.mp (hle x)))
    · simp only [f, dif_neg hxy, dif_neg hmxy]; exact bot_le

open Classical in
/-- **Restriction of a valuation to a convex subgroup, generalized.**
Like `restrictToConvex` but requires only that `H` contains every value
`v(a) ≥ 1` (the "ge-one" elements), not that `v ≤ 1` globally.

This is the version needed for **Wedhorn 7.5(iii)** — the retraction
`Spv A → Spv(A, I)` restricts `v` to its characteristic subgroup `cΓ_v(I)`,
which by Wedhorn 7.3 always contains every `v(a) ≥ 1` (it contains `cΓ_v`).
The global `v ≤ 1` hypothesis of `restrictToConvex` is too restrictive for
this retraction. -/
noncomputable def restrictToConvexBounded
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H) :
    Valuation R (WithZero H.toSubgroup) where
  toFun r :=
    if h : v r = 0 then 0
    else if hm : Units.mk0 (v r) h ∈ H then some ⟨Units.mk0 (v r) h, hm⟩
    else 0
  map_zero' := by simp [map_zero]
  map_one' := by
    simp only [map_one]
    have h1 : (1 : Γ₀) ≠ 0 := one_ne_zero
    have hm : Units.mk0 (1 : Γ₀) h1 ∈ H := by
      rw [show Units.mk0 (1 : Γ₀) h1 = 1 from Units.ext rfl]; exact one_mem H
    simp only [h1, dite_false, dif_pos hm,
      show (1 : WithZero H.toSubgroup) = ((1 : H.toSubgroup) : WithZero H.toSubgroup) from rfl]
    congr 1; exact Subtype.ext (Units.ext rfl)
  map_mul' x y := by
    -- Key: if u ∉ H then u < 1 (contrapositive of hH_ge).
    have unit_lt_one_of_not_mem : ∀ (r : R) (hr : v r ≠ 0),
        Units.mk0 (v r) hr ∉ H → v r < 1 := by
      intro r hr hnot
      by_contra h_ge_one
      push Not at h_ge_one
      exact hnot (hH_ge r hr h_ge_one)
    have not_mem_of_le' {u w : Γ₀ˣ} (hu : u ∉ H) (hu1 : u ≤ 1) (hw1 : w ≤ u) : w ∉ H :=
      fun hw_mem ↦ hu (H.convex hw_mem (one_mem H) hw1 hu1)
    by_cases hx : v x = 0
    · have hxy : v (x * y) = 0 := by rw [map_mul, hx, zero_mul]
      simp only [hxy, hx, dif_pos, zero_mul]
    by_cases hy : v y = 0
    · have hxy : v (x * y) = 0 := by rw [map_mul, hy, mul_zero]
      simp only [hxy, hy, dif_pos, mul_zero]
    have hxy_ne : v (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx hy
    have huxy_eq : Units.mk0 (v (x * y)) hxy_ne =
        Units.mk0 (v x) hx * Units.mk0 (v y) hy := Units.ext (map_mul v x y)
    by_cases hmx : Units.mk0 (v x) hx ∈ H <;> by_cases hmy : Units.mk0 (v y) hy ∈ H
    · have hmxy : Units.mk0 (v (x * y)) hxy_ne ∈ H := huxy_eq ▸ mul_mem hmx hmy
      simp only [hx, hy, hxy_ne, dif_neg, dif_pos hmx, dif_pos hmy, dif_pos hmxy, not_false_eq_true]
      rw [show (some (⟨Units.mk0 (v x) hx, hmx⟩ : H.toSubgroup) : WithZero H.toSubgroup) =
        (↑(⟨Units.mk0 (v x) hx, hmx⟩ : H.toSubgroup) : WithZero H.toSubgroup) from rfl,
        show (some (⟨Units.mk0 (v y) hy, hmy⟩ : H.toSubgroup) : WithZero H.toSubgroup) =
        (↑(⟨Units.mk0 (v y) hy, hmy⟩ : H.toSubgroup) : WithZero H.toSubgroup) from rfl,
        ← WithZero.coe_mul]
      congr 1
      exact Subtype.ext huxy_eq
    · have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]; intro hmem
        exact hmy (by have := mul_mem (inv_mem hmx) hmem; rwa [inv_mul_cancel_left] at this)
      simp only [hx, hy, hxy_ne, dif_neg, dif_pos hmx, dif_neg hmy, dif_neg hmxy, not_false_eq_true,
        mul_zero]
    · have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]; intro hmem
        exact hmx (by have := mul_mem hmem (inv_mem hmy); rwa [mul_inv_cancel_right] at this)
      simp only [hx, hy, hxy_ne, dif_neg, dif_neg hmx, dif_pos hmy, dif_neg hmxy, not_false_eq_true,
        zero_mul]
    · -- Both v(x), v(y) ∉ H. By hypothesis, both v(x), v(y) < 1, so v(x)*v(y) < 1 ≤ ...
      -- and v(x)*v(y) ≤ v(x) since v(y) ≤ 1.
      have hvy_lt : v y < 1 := unit_lt_one_of_not_mem y hy hmy
      have hvx_lt : v x < 1 := unit_lt_one_of_not_mem x hx hmx
      have hmxy : Units.mk0 (v (x * y)) hxy_ne ∉ H := by
        rw [huxy_eq]; intro hmem
        have hle_ux : Units.mk0 (v x) hx * Units.mk0 (v y) hy ≤ Units.mk0 (v x) hx :=
          Units.val_le_val.mp (show (v x) * (v y) ≤ v x from by
            calc v x * v y ≤ v x * 1 := mul_le_mul_right hvy_lt.le (v x)
              _ = v x := mul_one _)
        have hvx_le_one : Units.mk0 (v x) hx ≤ 1 := Units.val_le_val.mp hvx_lt.le
        exact not_mem_of_le' hmx hvx_le_one hle_ux hmem
      simp only [hx, hy, hxy_ne, dif_neg, dif_neg hmx, dif_neg hmy, dif_neg hmxy, not_false_eq_true,
        mul_zero]
  map_add_le_max' x y := by
    have unit_lt_one_of_not_mem : ∀ (r : R) (hr : v r ≠ 0),
        Units.mk0 (v r) hr ∉ H → v r < 1 := by
      intro r hr hnot
      by_contra h_ge_one
      push Not at h_ge_one
      exact hnot (hH_ge r hr h_ge_one)
    set f : R → WithZero H.toSubgroup := fun r ↦
      if h : v r = 0 then 0
      else if hm : Units.mk0 (v r) h ∈ H then some ⟨Units.mk0 (v r) h, hm⟩
      else 0
    change f (x + y) ≤ max (f x) (f y)
    by_cases hxy : v (x + y) = 0
    · simp only [f, hxy, dif_pos]; exact bot_le
    by_cases hmxy : Units.mk0 (v (x + y)) hxy ∈ H
    · rcases le_total (v x) (v y) with hvxy | hvyx
      · have hv_le : v (x + y) ≤ v y := (v.map_add x y).trans (max_eq_right hvxy).le
        suffices h : f (x + y) ≤ f y from h.trans (le_max_right _ _)
        have hy : v y ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hxy) hv_le)
        by_cases hmy : Units.mk0 (v y) hy ∈ H
        · simp only [f, hxy, hy, dif_pos hmxy, dif_pos hmy]
          exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
            (Units.val_le_val.mp hv_le))
        · -- v(y) ∉ H → v(y) < 1 → Units.mk0 (v y) hy ≤ 1
          have hvy_lt : v y < 1 := unit_lt_one_of_not_mem y hy hmy
          exfalso; exact hmy (H.convex hmxy (one_mem H)
            (Units.val_le_val.mp hv_le) (Units.val_le_val.mp hvy_lt.le))
      · have hv_le : v (x + y) ≤ v x := (v.map_add x y).trans (max_eq_left hvyx).le
        suffices h : f (x + y) ≤ f x from h.trans (le_max_left _ _)
        have hx' : v x ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hxy) hv_le)
        by_cases hmx : Units.mk0 (v x) hx' ∈ H
        · simp only [f, hxy, hx', dif_pos hmxy, dif_pos hmx]
          exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr
            (Units.val_le_val.mp hv_le))
        · have hvx_lt : v x < 1 := unit_lt_one_of_not_mem x hx' hmx
          exfalso; exact hmx (H.convex hmxy (one_mem H)
            (Units.val_le_val.mp hv_le) (Units.val_le_val.mp hvx_lt.le))
    · simp only [f, dif_neg hxy, dif_neg hmxy]; exact bot_le

/-! ### API for `restrictToConvex` -/

section RestrictToConvexAPI

open Classical in
/-- Unfold `restrictToConvex` application to the underlying `dite` chain. -/
theorem restrictToConvex_unfold
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) (r : R) :
    v.restrictToConvex H hle r =
      (if h : v r = 0 then (0 : WithZero H.toSubgroup)
       else if hm : Units.mk0 (v r) h ∈ H
            then (⟨Units.mk0 (v r) h, hm⟩ : H.toSubgroup)
            else 0) :=
  rfl

open Classical in
/-- Unfold `restrictToConvexBounded` — same `dite` chain as `restrictToConvex`. -/
theorem restrictToConvexBounded_unfold
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H) (r : R) :
    v.restrictToConvexBounded H hH_ge r =
      (if h : v r = 0 then (0 : WithZero H.toSubgroup)
       else if hm : Units.mk0 (v r) h ∈ H
            then (⟨Units.mk0 (v r) h, hm⟩ : H.toSubgroup)
            else 0) :=
  rfl

/-- `restrictToConvexBounded` agrees with `v` on values inside `H`. -/
theorem restrictToConvexBounded_apply_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {r : R} (hr : v r ≠ 0) (hm : Units.mk0 (v r) hr ∈ H) :
    v.restrictToConvexBounded H hH_ge r =
      ((⟨Units.mk0 (v r) hr, hm⟩ : H.toSubgroup) : WithZero H.toSubgroup) := by
  rw [restrictToConvexBounded_unfold, dif_neg hr, dif_pos hm]

/-- `restrictToConvexBounded` sends values outside `H` to `0`. -/
theorem restrictToConvexBounded_apply_not_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {r : R} (hr : v r ≠ 0) (hm : Units.mk0 (v r) hr ∉ H) :
    v.restrictToConvexBounded H hH_ge r = 0 := by
  rw [restrictToConvexBounded_unfold, dif_neg hr, dif_neg hm]

/-- `restrictToConvexBounded` sends the zero value to `0`. -/
theorem restrictToConvexBounded_apply_zero
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {r : R} (hr : v r = 0) :
    v.restrictToConvexBounded H hH_ge r = 0 := by
  rw [restrictToConvexBounded_unfold, dif_pos hr]

/-- The support of `restrictToConvex` contains the support of `v`. -/
theorem supp_le_restrictToConvex_supp
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) :
    v.supp ≤ (v.restrictToConvex H hle).supp := by
  intro r hr
  rw [mem_supp_iff] at hr ⊢
  rw [restrictToConvex_unfold, dif_pos hr]

/-- `restrictToConvex` is `≤ 1` on all elements. -/
theorem restrictToConvex_le_one
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) (r : R) :
    v.restrictToConvex H hle r ≤ 1 := by
  rw [restrictToConvex_unfold]
  split
  · exact bot_le
  next h =>
    split
    next hm =>
      rw [show (1 : WithZero H.toSubgroup) = ((1 : H.toSubgroup) : WithZero H.toSubgroup) from rfl]
      exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr (Units.val_le_val.mp (hle r)))
    · exact bot_le

/-- If `v(r) ≠ 0` and `Units.mk0 (v r) ∉ H`, then `restrictToConvex` sends `r` to `0`. -/
theorem restrictToConvex_eq_zero_of_not_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0)
    (hm : Units.mk0 (v r) hr ∉ H) :
    v.restrictToConvex H hle r = 0 := by
  rw [restrictToConvex_unfold, dif_neg hr, dif_neg hm]

/-- If `v(r) ≠ 0` and `Units.mk0 (v r) ∈ H`, then `restrictToConvex`
sends `r` to a nonzero value. -/
theorem restrictToConvex_pos_of_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0)
    (hm : Units.mk0 (v r) hr ∈ H) :
    0 < v.restrictToConvex H hle r := by
  rw [restrictToConvex_unfold, dif_neg hr, dif_pos hm]
  exact WithZero.zero_lt_coe _

/-- If `v(r) ≠ 0`, `Units.mk0 (v r) ∈ H`, and `v r < 1`, then `restrictToConvex v H r < 1`. -/
theorem restrictToConvex_lt_one_of_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0)
    (hm : Units.mk0 (v r) hr ∈ H) (hlt : v r < 1) :
    v.restrictToConvex H hle r < 1 := by
  rw [restrictToConvex_unfold, dif_neg hr, dif_pos hm]
  rw [show (1 : WithZero H.toSubgroup) = ((1 : H.toSubgroup) : WithZero H.toSubgroup) from rfl]
  exact WithZero.coe_lt_coe.mpr (Subtype.mk_lt_mk.mpr (Units.val_lt_val.mp hlt))

/-- If `v(r) ≠ 0` and `Units.mk0 (v r) ∉ H`, then `restrictToConvex v H r < 1`
(trivially, since it equals 0). -/
theorem restrictToConvex_lt_one_of_not_mem
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0)
    (hm : Units.mk0 (v r) hr ∉ H) :
    v.restrictToConvex H hle r < 1 := by
  rw [restrictToConvex_eq_zero_of_not_mem v H hle hr hm]
  exact zero_lt_one

/-- `restrictToConvex` is `< 1` at `r` whenever `v r < 1` (regardless of H-membership). -/
theorem restrictToConvex_lt_one_of_val_lt_one
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {r : R} (hr : v r ≠ 0) (hlt : v r < 1) :
    v.restrictToConvex H hle r < 1 := by
  by_cases hm : Units.mk0 (v r) hr ∈ H
  · exact restrictToConvex_lt_one_of_mem v H hle hr hm hlt
  · exact restrictToConvex_lt_one_of_not_mem v H hle hr hm

/-- `restrictToConvex` is monotone on elements with `v ≤ 1`:
if `v a ≤ v b`, `v b ≠ 0`, and `Units.mk0 (v b) ∈ H`, then
`restrictToConvex v H a ≤ restrictToConvex v H b`. -/
theorem restrictToConvex_mono_of_le_one
    (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hle : ∀ r : R, v r ≤ 1) {a b : R} (hab : v a ≤ v b)
    (hb_ne : v b ≠ 0) (hb_mem : Units.mk0 (v b) hb_ne ∈ H) :
    v.restrictToConvex H hle a ≤ v.restrictToConvex H hle b := by
  by_cases ha_ne : v a = 0
  · rw [restrictToConvex_unfold, dif_pos ha_ne]; exact bot_le
  · by_cases ha_mem : Units.mk0 (v a) ha_ne ∈ H
    · rw [restrictToConvex_unfold, dif_neg ha_ne, dif_pos ha_mem,
          restrictToConvex_unfold, dif_neg hb_ne, dif_pos hb_mem]
      exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr (Units.val_le_val.mp hab))
    · rw [restrictToConvex_unfold, dif_neg ha_ne, dif_neg ha_mem]; exact bot_le

end RestrictToConvexAPI

end Valuation

/-! ### Section 7: Exact-support Spa-point bridge via ofPrime coarsening

Given a non-open prime `𝔭` of a Huber ring `A` and domination data
`V₀ : ValuationSubring (FractionRing (A ⧸ 𝔭))` (from
`exists_valuationSubring_of_prime`), if there exists a height-1 prime `Q` of
`V₀` that contains all `I`-image nonunits, then `V₀.ofPrime Q` supplies the
`MulArchimedean` upgrade needed by
`exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean` and yields a Spa
point of `A` with **exact support** `v.supp = 𝔭`.

The single remaining input is the **existence of the height-1 prime `Q` of
`V₀` containing all `I`-images**. That is the narrow "maximal convex
subgroup / MulArchimedean exact-support" lemma; the bridge below isolates
it as an explicit named caller hypothesis.

This route **bypasses** `Cor832.liftedIdeal_ne_top_claim` when applicable —
the exact-support conclusion `v.supp = 𝔭` is strictly stronger than the
`p ≤ v.supp` output of the completion route, and it is obtained without
ever touching `presheafValue`-level properness.

**Caveat**: the exact-support Spa point produced here does NOT
automatically satisfy the rational-open constraint `v ∈ rationalOpen D'.T
D'.s` required by `spa_point_nonOpen_of_rational_subset` in
`Presheaf.lean`. Adding that rational-open constraint is a separate task
(caller-supplied or a further bridge). The bridge below closes the
`exists_mem_spa_supp_eq` shape in `ValuationContinuity.lean`, not the
rational-open-restricted variant. -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Monotonicity of `pulledBackValuation` under `V ≤ W`: if the pulled-back
valuation via `V` is `≤ 1` on `f`, then so is the pulled-back valuation via
any coarsening `W ≥ V`. Direct consequence of `mapOfLE`-monotonicity and
`mapOfLE_valuation_apply`. -/
theorem pulledBackValuation_le_one_of_le (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    {V W : ValuationSubring (FractionRing (A ⧸ 𝔭))} (hVW : V ≤ W)
    {f : A} (hf : P.pulledBackValuation V f ≤ 1) :
    P.pulledBackValuation W f ≤ 1 := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  have hmono := V.monotone_mapOfLE W hVW hf
  rw [map_one] at hmono
  change W.valuation _ ≤ 1
  rw [← V.mapOfLE_valuation_apply W hVW]
  exact hmono

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Transfer of nonunit-membership through `ofPrime`: if `x ∈ V₀.nonunits`
and its lift `⟨x, _⟩ : V₀` sits in a prime `Q : Ideal V₀`, then the same
`x` is a nonunit of the coarsening `V₀.ofPrime Q`.

Proof: `idealOfLE V₀ (V₀.ofPrime Q) _` equals `Q` (by
`idealOfLE_ofPrime`), which transfers `Q`-membership on `V₀` to
`maximalIdeal`-membership on `V₀.ofPrime Q`; `coe_mem_nonunits_iff` then
finishes. -/
theorem _root_.ValuationSubring.mem_nonunits_ofPrime_of_val_mem_prime
    {K : Type*} [Field K] (V₀ : ValuationSubring K) (Q : Ideal V₀) [Q.IsPrime]
    {x : K} (hx_V₀ : x ∈ V₀.toSubring)
    (hx_Q : (⟨x, hx_V₀⟩ : V₀) ∈ Q) :
    x ∈ ((V₀.ofPrime Q).nonunits : Set K) := by
  have hle : V₀ ≤ V₀.ofPrime Q := V₀.le_ofPrime Q
  -- Transport `Q`-membership to `idealOfLE`-membership via `idealOfLE_ofPrime`.
  have h_idealOfLE : (⟨x, hx_V₀⟩ : V₀) ∈
      ValuationSubring.idealOfLE V₀ (V₀.ofPrime Q) hle := by
    rw [show ValuationSubring.idealOfLE V₀ (V₀.ofPrime Q) hle = Q from
      ValuationSubring.idealOfLE_ofPrime V₀ Q]
    exact hx_Q
  -- `idealOfLE = (maximalIdeal).comap inclusion` unfolds the membership.
  have h_maxIdeal : V₀.inclusion (V₀.ofPrime Q) hle ⟨x, hx_V₀⟩ ∈
      IsLocalRing.maximalIdeal (V₀.ofPrime Q) := h_idealOfLE
  -- `coe_mem_nonunits_iff` converts maximal-ideal membership to nonunits.
  have : ((V₀.inclusion (V₀.ofPrime Q) hle ⟨x, hx_V₀⟩ : V₀.ofPrime Q) : K) ∈
      (V₀.ofPrime Q).nonunits :=
    (V₀.ofPrime Q).coe_mem_nonunits_iff.mpr h_maxIdeal
  exact this

omit [IsLinearTopology A A] in
/-- **Rational-open refinement of Lemma 7.45 via domination.**

Packages `exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean` with the
extra rational-compatibility hypothesis `hrat_compat` (pulled-back
valuation bounds `t` by `D'.s` for each `t ∈ D'.T`) to produce a Spa
point `v` with both `v ∈ rationalOpen D'.T D'.s` AND `𝔭 ≤ v.supp`
(actually `v.supp = 𝔭`). This is the **rational-open-restricted**
version of the exact-support construction, feeding directly into the
`∃ v ∈ rationalOpen D'.T D'.s, p ≤ v.supp` obligation in
`Presheaf.mem_prime_of_rational_subset_nonOpen`.

The rational-compatibility hypothesis is exactly the one residual that
the dominating valuation subring must satisfy to produce a rational-open
Spa point. It asks that, over the pulled-back valuation, every generator
`t ∈ D'.T` is bounded by `D'.s`. In the enlarged-domination route this is
engineered into the subring `V` by including the quotients
`φ(t) * (φ(D'.s))⁻¹` for each `t`, but the bridge is agnostic about
how `V` is produced. -/
theorem exists_mem_rationalOpen_supp_ge_of_nonOpen_prime_mulArchimedean
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    (T : Finset A) (s : A) (hs : s ∉ 𝔭)
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hrange : (P.toFractionQuotient 𝔭).range ≤ V.toSubring)
    (hnonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V.nonunits)
    [MulArchimedean V.ValueGroup]
    (hAplus : ∀ f ∈ (A⁺ : Set A), P.pulledBackValuation V f ≤ 1)
    (hrat_compat : ∀ t ∈ T,
      P.pulledBackValuation V t ≤ P.pulledBackValuation V s) :
    ∃ v ∈ rationalOpen T s, 𝔭 ≤ v.supp := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  set w := P.pulledBackValuation V with hw_def
  refine ⟨ofValuation w, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · -- ofValuation w is continuous.
    exact isContinuous_ofValuation_of w
      (P.pulledBackValuation_isContinuous h𝔭 hrange hnonunits)
  · -- (ofValuation w).vle f 1 for f ∈ A⁺.
    intro f hf
    change w f ≤ w 1
    rw [map_one]
    exact hAplus f hf
  · -- ∀ t ∈ T, (ofValuation w).vle t s.
    intro t ht
    exact hrat_compat t ht
  · -- ¬ (ofValuation w).vle s 0.
    change ¬ w s ≤ w 0
    rw [map_zero, le_zero_iff]
    -- `w s ≠ 0 ↔ s ∉ w.supp ↔ s ∉ 𝔭` (the latter is our hypothesis).
    intro hzero
    apply hs
    rw [← P.pulledBackValuation_supp V]
    exact (Valuation.mem_supp_iff w s).mpr hzero
  · -- 𝔭 ≤ (ofValuation w).supp.
    rw [supp_ofValuation]
    exact (P.pulledBackValuation_supp V).ge

omit [IsLinearTopology A A] in
/-- **Exact-support Spa point via height-1 `ofPrime` coarsening.**

Given a non-open prime `𝔭` of `A`, domination data `V₀` (with
`hrange` and `hnonunits` as in `exists_valuationSubring_of_prime`), a
height-1 prime `Q` of `V₀` containing all `I`-image nonunits, and the
standard `A⁺`-boundedness hypothesis on the pulled-back valuation of `V₀`,
this theorem produces a Spa point `v ∈ Spa A A⁺` with **exact support**
`v.supp = 𝔭`.

The coarsening `V₀.ofPrime Q` supplies the `MulArchimedean` value group
via `mulArchimedean_ofPrime_of_height_one`; `V ≤ ofPrime V Q` transfers
the range inclusion and `A⁺` bound by monotonicity; the I-image nonunits
transfer by
`ValuationSubring.mem_nonunits_ofPrime_of_val_mem_prime`.

**Missing narrow lemma (caller-supplied)**: existence of the height-1
prime `Q` of `V₀` with `I`-images ⊆ `Q`. For strongly-noetherian Huber
rings this reduces to the "minimal prime above `J := φ(I)` in a
finite-rank valuation ring is height-1" question; see the docblock in
`2026-03-18-valuation-prime-convex.md`. -/
theorem exists_mem_spa_supp_eq_of_nonOpen_prime_via_heightOne_ofPrime
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    {V₀ : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hrange : (P.toFractionQuotient 𝔭).range ≤ V₀.toSubring)
    (hnonunits : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆ V₀.nonunits)
    (Q : Ideal V₀) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (hht1 : ∀ (P' : Ideal V₀) [P'.IsPrime], P' < Q → P' = ⊥)
    (hJ_le_Q : ∀ (x : FractionRing (A ⧸ 𝔭)),
      x ∈ (P.toFractionQuotient 𝔭).range.subtype ''
        (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) →
      ∀ (hx_V₀ : x ∈ V₀.toSubring), (⟨x, hx_V₀⟩ : V₀) ∈ Q)
    (hAplus : ∀ f ∈ (A⁺ : Set A), P.pulledBackValuation V₀ f ≤ 1) :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔭 := by
  -- Set up the coarsened valuation subring.
  haveI : MulArchimedean (V₀.ofPrime Q).ValueGroup :=
    ValuationSubring.mulArchimedean_ofPrime_of_height_one V₀ Q hQ hht1
  have hle : V₀ ≤ V₀.ofPrime Q := V₀.le_ofPrime Q
  -- Transfer of `hrange` through `V₀ ≤ V₀.ofPrime Q`.
  have hrange' : (P.toFractionQuotient 𝔭).range ≤ (V₀.ofPrime Q).toSubring :=
    hrange.trans hle
  -- Transfer of `hnonunits`: each I-image sits in `V₀.ofPrime Q.nonunits`
  -- using the `I-images ⊆ Q` hypothesis.
  have hnonunits' : (P.toFractionQuotient 𝔭).range.subtype ''
      (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆
      (V₀.ofPrime Q).nonunits := by
    intro x hx_image
    have hx_V₀ : x ∈ V₀.toSubring := V₀.nonunits_subset (hnonunits hx_image)
    exact ValuationSubring.mem_nonunits_ofPrime_of_val_mem_prime
      V₀ Q hx_V₀ (hJ_le_Q x hx_image hx_V₀)
  -- Transfer of `hAplus` through `V₀ ≤ V₀.ofPrime Q`.
  have hAplus' : ∀ f ∈ (A⁺ : Set A),
      P.pulledBackValuation (V₀.ofPrime Q) f ≤ 1 :=
    fun f hf ↦ P.pulledBackValuation_le_one_of_le hle (hAplus f hf)
  -- Apply the MulArchimedean Lemma 7.45.
  exact P.exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean
    h𝔭 hrange' hnonunits' hAplus'

/-! ### `hrat_compat` supplier from enlarged-domination data

The rational-compatibility hypothesis `hrat_compat` of
`exists_mem_rationalOpen_supp_ge_of_nonOpen_prime_mulArchimedean` is
engineered into `V` by including the quotients `φ(t) * (φ(s))⁻¹` for
`t ∈ T` in the subring that `V` dominates. The supplier below extracts
this rational compatibility as a **pure algebraic consequence** of the
membership hypothesis `φ(t) * (φ(s))⁻¹ ∈ V.toSubring` together with
`s ∉ 𝔭`.

Composition with `exists_valuationSubring_of_prime_enlarged` (applied to
an `R' := Subring.closure ((P.toFractionQuotient 𝔭).range ∪ {(φ s)⁻¹})`
or similar enlargement) produces `hrat_compat` directly, with the single
remaining residual being the **properness of the I-image inside that
enlarged subring**; see
`exists_valuationSubring_with_rational_compat` below for the composed
statement. -/

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Supplier for `hrat_compat` from membership**: if `V` contains
`φ(t) * (φ(s))⁻¹` in its underlying subring for every `t ∈ T`, and
`s ∉ 𝔭` (so `φ(s)` is nonzero in `Frac(A ⧸ 𝔭)`), then the pulled-back
valuation satisfies the rational-compatibility bound
`P.pulledBackValuation V t ≤ P.pulledBackValuation V s`.

Pure algebraic derivation via `ValuationSubring.valuation_le_iff`. -/
theorem hrat_compat_of_mem_enlarged_domination (P : PairOfDefinition A)
    {𝔭 : Ideal A} [𝔭.IsPrime]
    (T : Finset A) (s : A) (hs : s ∉ 𝔭)
    {V : ValuationSubring (FractionRing (A ⧸ 𝔭))}
    (hdom : ∀ t ∈ T,
      ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
        (Ideal.Quotient.mk 𝔭)) t *
      (((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
        (Ideal.Quotient.mk 𝔭)) s)⁻¹ ∈ V.toSubring) :
    ∀ t ∈ T, P.pulledBackValuation V t ≤ P.pulledBackValuation V s := by
  intro t ht
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  set φ : A →+* FractionRing (A ⧸ 𝔭) :=
    (algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp (Ideal.Quotient.mk 𝔭) with hφ_def
  -- `φ s ≠ 0` from `s ∉ 𝔭` via injectivity of `algebraMap` on the domain quotient.
  have hφs_ne : φ s ≠ 0 := by
    intro hsz
    apply hs
    have hinj := IsFractionRing.injective (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))
    have hsz' : algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭)) ((Ideal.Quotient.mk 𝔭) s) = 0 := hsz
    have := hinj (hsz'.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  -- Membership of the quotient in V.
  have h_in_V : φ t * (φ s)⁻¹ ∈ V.toSubring := hdom t ht
  -- Use `valuation_le_iff`: V.valuation x ≤ V.valuation y ↔ ∃ a : V, (a : K) * y = x.
  change V.valuation (φ t) ≤ V.valuation (φ s)
  rw [V.valuation_le_iff]
  refine ⟨⟨φ t * (φ s)⁻¹, h_in_V⟩, ?_⟩
  change (φ t * (φ s)⁻¹) * φ s = φ t
  rw [mul_assoc, inv_mul_cancel₀ hφs_ne, mul_one]

/-! ### Packaged caller-ready residual for `Presheaf.spa_point_nonOpen_of_rational_subset`

Combining the `hrat_compat` supplier with the existing rational-open
bridge `exists_mem_rationalOpen_supp_ge_of_nonOpen_prime_mulArchimedean`
gives the packaged theorem below. The **single remaining caller residual**
is the existence of a dominating valuation subring `V` with the full
"rational-enlarged" content: domination range, I-image nonunits,
MulArchimedean value group, `A⁺` bound, AND `φ(t) * (φ(s))⁻¹ ∈ V.toSubring`
for each `t ∈ T`.

This packaged statement is what a downstream caller (e.g., Primary's
`Presheaf.spa_point_nonOpen_of_rational_subset` chain) needs to supply.
See the module docblock for the residual map. -/

omit [IsLinearTopology A A] in
/-- **Packaged caller-ready rational-open Spa point** from enlarged
domination with rational quotients.

Consumes the single packaged existence statement
`∃ V, (domination + MulArchimedean + A⁺ bound + rational-quotient
membership)` and produces the exact `∃ v ∈ rationalOpen T s, 𝔭 ≤ v.supp`
shape required by `Presheaf.mem_prime_of_rational_subset_nonOpen`. -/
theorem exists_mem_rationalOpen_supp_ge_of_enlarged_domination
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬IsOpen (𝔭 : Set A))
    (T : Finset A) (s : A) (hs : s ∉ 𝔭)
    (hsupplier : ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.toFractionQuotient 𝔭).range ≤ V.toSubring ∧
      (P.toFractionQuotient 𝔭).range.subtype ''
        (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆
        V.nonunits ∧
      Nonempty (MulArchimedean V.ValueGroup) ∧
      (∀ f ∈ (A⁺ : Set A), P.pulledBackValuation V f ≤ 1) ∧
      (∀ t ∈ T,
        ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
          (Ideal.Quotient.mk 𝔭)) t *
        (((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
          (Ideal.Quotient.mk 𝔭)) s)⁻¹ ∈ V.toSubring)) :
    ∃ v ∈ rationalOpen T s, 𝔭 ≤ v.supp := by
  obtain ⟨V, hrange, hnonunits, ⟨hmarch⟩, hAplus, hdom⟩ := hsupplier
  haveI := hmarch
  exact P.exists_mem_rationalOpen_supp_ge_of_nonOpen_prime_mulArchimedean
    h𝔭 T s hs hrange hnonunits hAplus
    (P.hrat_compat_of_mem_enlarged_domination T s hs hdom)

end PairOfDefinition

/-! ### Reduction of the packaged residual to explicit enlarged-domination data

The packaged existential consumed by
`exists_mem_rationalOpen_supp_ge_of_enlarged_domination` decomposes into
an **explicit enlarged-subring construction** (the subring generated by
`(P.toFractionQuotient 𝔭).range` and `(φ s)⁻¹`) plus two sub-residuals:

* **(a) Enlarged-I-image properness** (the one real analytic blocker):
  the image of `P.I` in the enlarged subring is proper. NOT automatic
  from the domination theorem; depends on Huber / rational-subset content.
* **(b) Height-1 prime with I-image containment**: there exists a
  height-1 prime `Q` of the dominating `V₀` containing the I-image.
  Pure valuation-ring structure theory.

The theorem `PairOfDefinition.exists_packaged_enlarged_domination_of_subResiduals`
below derives the packaged existential from these two sub-residuals. The
**one real blocker** per the manager's framing is sub-residual (a). -/

namespace PairOfDefinition

open ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A]

/-- The **enlarged subring** generated by `(P.toFractionQuotient 𝔭).range`
together with the rational quotients `φ(t) * (φ(s))⁻¹` for `t ∈ T`, inside
`FractionRing (A ⧸ 𝔭)`. `T` is threaded as a parameter so every rational
quotient is in the seed of the closure; `(P.toFractionQuotient 𝔭).range`
is included so the enlarged-domination theorem applies directly. -/
noncomputable def rationalEnlargedSubring (P : PairOfDefinition A)
    (𝔭 : Ideal A) [𝔭.IsPrime] (T : Finset A) (s : A) :
    Subring (FractionRing (A ⧸ 𝔭)) :=
  letI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  Subring.closure
    (((P.toFractionQuotient 𝔭).range : Set _) ∪
      (fun t : A ↦
        ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
          (Ideal.Quotient.mk 𝔭)) t *
        (((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
          (Ideal.Quotient.mk 𝔭)) s)⁻¹) '' (T : Set A))

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- `(P.toFractionQuotient 𝔭).range ≤ P.rationalEnlargedSubring 𝔭 T s`. -/
theorem range_le_rationalEnlargedSubring (P : PairOfDefinition A)
    (𝔭 : Ideal A) [𝔭.IsPrime] (T : Finset A) (s : A) :
    (P.toFractionQuotient 𝔭).range ≤ P.rationalEnlargedSubring 𝔭 T s := by
  intro x hx
  unfold rationalEnlargedSubring
  exact Subring.subset_closure (Or.inl hx)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- Each rational quotient `φ(t) * (φ(s))⁻¹` with `t ∈ T` lies in
`P.rationalEnlargedSubring 𝔭 T s`. Direct from the `T`-image seed. -/
theorem rationalQuotient_mem_rationalEnlargedSubring (P : PairOfDefinition A)
    (𝔭 : Ideal A) [𝔭.IsPrime] (T : Finset A) (s : A) {t : A} (ht : t ∈ T) :
    ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
        (Ideal.Quotient.mk 𝔭)) t *
      (((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
        (Ideal.Quotient.mk 𝔭)) s)⁻¹ ∈
      P.rationalEnlargedSubring 𝔭 T s := by
  unfold rationalEnlargedSubring
  apply Subring.subset_closure
  right
  exact ⟨t, Finset.mem_coe.mpr ht, rfl⟩

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Transfer lemma** (manager-suggested shape): membership in
`Ideal.map rangeRestrict P.I` (range-level) transfers to membership in
`Ideal.map (codRestrict to R') P.I` (R'-level), via the subring inclusion
`range ≤ R'`.

Proof: set `i := Subring.inclusion hR'`; note
`codRestrict ... hR' = i.comp rangeRestrict` by `ext; rfl`; apply
`Ideal.mem_map_of_mem i hy`; use `Ideal.map_map` to collapse the nested
map to the composition; rewrite the composition via the extensional
equality. -/
theorem rangeRestrict_image_mem_codRestrict_image
    (P : PairOfDefinition A) {𝔭 : Ideal A} [𝔭.IsPrime]
    {R' : Subring (FractionRing (A ⧸ 𝔭))}
    (hR' : (P.toFractionQuotient 𝔭).range ≤ R')
    {y : (P.toFractionQuotient 𝔭).range}
    (hy : y ∈ Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I) :
    (⟨y.1, hR' y.2⟩ : R') ∈
      Ideal.map ((P.toFractionQuotient 𝔭).codRestrict R'
        (fun a ↦ hR' ⟨a, rfl⟩)) P.I := by
  set i : (P.toFractionQuotient 𝔭).range →+* R' := Subring.inclusion hR'
  have hcomp :
      (P.toFractionQuotient 𝔭).codRestrict R' (fun a ↦ hR' ⟨a, rfl⟩) =
      i.comp (P.toFractionQuotient 𝔭).rangeRestrict := by
    ext a; rfl
  rw [hcomp, ← Ideal.map_map]
  exact Ideal.mem_map_of_mem i hy

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **Reduction of the packaged residual to two sub-residuals over the
explicit enlarged subring.**

Constructs the packaged existential consumed by
`exists_mem_rationalOpen_supp_ge_of_enlarged_domination` from:

* the explicit enlarged subring `P.rationalEnlargedSubring 𝔭 s`
  (built here, no residual);
* **sub-residual (a)** `hR'_proper` (the analytic blocker): properness
  of the I-image in the enlarged subring;
* **sub-residual (b)** `hQ_heightOne_I` (pure valuation-ring): existence
  of a height-1 prime of the dominating `V₀` containing the I-image;
* the standard `hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀` premise (not a
  residual — standard Huber hypothesis).

The ofPrime coarsening supplies `MulArchimedean` via
`mulArchimedean_ofPrime_of_height_one`; the nonunit transfer uses
`ValuationSubring.mem_nonunits_ofPrime_of_val_mem_prime` and the
manager-supplied `rangeRestrict_image_mem_codRestrict_image` transfer
lemma; the A⁺ bound is inherited from range-domination.

**One real blocker**: sub-residual (a) `hR'_proper`. -/
theorem exists_packaged_enlarged_domination_of_subResiduals
    (P : PairOfDefinition A) [IsAdicComplete P.I P.A₀] [PlusSubring A]
    (hAplus_le_A₀ : (A⁺ : Set A) ⊆ P.A₀)
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (T : Finset A) (s : A) (_hs : s ∉ 𝔭)
    (hR'_proper :
      Ideal.map
        ((P.toFractionQuotient 𝔭).codRestrict (P.rationalEnlargedSubring 𝔭 T s)
          (fun a ↦ (P.range_le_rationalEnlargedSubring 𝔭 T s) ⟨a, rfl⟩))
        P.I ≠ ⊤)
    (hQ_heightOne_I : ∀ V₀ : ValuationSubring (FractionRing (A ⧸ 𝔭)),
        P.rationalEnlargedSubring 𝔭 T s ≤ V₀.toSubring →
        ((P.rationalEnlargedSubring 𝔭 T s).subtype '' (Ideal.map
          ((P.toFractionQuotient 𝔭).codRestrict (P.rationalEnlargedSubring 𝔭 T s)
            (fun a ↦ (P.range_le_rationalEnlargedSubring 𝔭 T s) ⟨a, rfl⟩))
          P.I : Set _) ⊆ V₀.nonunits) →
        ∃ Q : Ideal V₀, ∃ _ : Q.IsPrime, Q ≠ ⊥ ∧
          (∀ (P' : Ideal V₀), P'.IsPrime → P' < Q → P' = ⊥) ∧
          (∀ y : (P.toFractionQuotient 𝔭).range,
            y ∈ Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I →
            ∀ (hy_V₀ : (y : FractionRing (A ⧸ 𝔭)) ∈ V₀.toSubring),
            (⟨(y : FractionRing (A ⧸ 𝔭)), hy_V₀⟩ : V₀) ∈ Q)) :
    ∃ V : ValuationSubring (FractionRing (A ⧸ 𝔭)),
      (P.toFractionQuotient 𝔭).range ≤ V.toSubring ∧
      (P.toFractionQuotient 𝔭).range.subtype ''
        (Ideal.map (P.toFractionQuotient 𝔭).rangeRestrict P.I : Set _) ⊆
        V.nonunits ∧
      Nonempty (MulArchimedean V.ValueGroup) ∧
      (∀ f ∈ (A⁺ : Set A), P.pulledBackValuation V f ≤ 1) ∧
      (∀ t ∈ T,
        ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
          (Ideal.Quotient.mk 𝔭)) t *
        (((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
          (Ideal.Quotient.mk 𝔭)) s)⁻¹ ∈ V.toSubring) := by
  haveI : IsDomain (A ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  -- Apply enlarged domination to get V₀.
  obtain ⟨V₀, hR'_le_V₀, hnonunits_V₀⟩ :=
    P.exists_valuationSubring_of_prime_enlarged
      (R' := P.rationalEnlargedSubring 𝔭 T s)
      (P.range_le_rationalEnlargedSubring 𝔭 T s) hR'_proper
  -- Extract height-1 Q from sub-residual (b).
  obtain ⟨Q, hQ_prime, hQ_ne_bot, hQ_ht1, hQ_contains_I⟩ :=
    hQ_heightOne_I V₀ hR'_le_V₀ hnonunits_V₀
  haveI := hQ_prime
  -- Set V := V₀.ofPrime Q.
  have hle : V₀ ≤ V₀.ofPrime Q := V₀.le_ofPrime Q
  haveI : MulArchimedean (V₀.ofPrime Q).ValueGroup :=
    ValuationSubring.mulArchimedean_ofPrime_of_height_one V₀ Q hQ_ne_bot hQ_ht1
  refine ⟨V₀.ofPrime Q, ?_, ?_, ⟨inferInstance⟩, ?_, ?_⟩
  · -- range ≤ V.toSubring
    exact ((P.range_le_rationalEnlargedSubring 𝔭 T s).trans hR'_le_V₀).trans hle
  · -- I-image ⊆ V.nonunits.
    intro x hx_image
    obtain ⟨y, hy_I, hy_eq⟩ := hx_image
    -- Transfer range-level I-image membership to R'-level via the manager's lemma.
    have hy_R' :
        (⟨y.1, (P.range_le_rationalEnlargedSubring 𝔭 T s) y.2⟩ :
            P.rationalEnlargedSubring 𝔭 T s) ∈
        Ideal.map ((P.toFractionQuotient 𝔭).codRestrict
          (P.rationalEnlargedSubring 𝔭 T s)
          (fun a ↦ (P.range_le_rationalEnlargedSubring 𝔭 T s) ⟨a, rfl⟩)) P.I :=
      P.rangeRestrict_image_mem_codRestrict_image
        (P.range_le_rationalEnlargedSubring 𝔭 T s) hy_I
    -- Embed y.1 into V₀.nonunits via hnonunits_V₀.
    have hy_nonunits_V₀ : (y : FractionRing (A ⧸ 𝔭)) ∈ V₀.nonunits :=
      hnonunits_V₀ ⟨_, hy_R', rfl⟩
    have hy_V₀ : (y : FractionRing (A ⧸ 𝔭)) ∈ V₀.toSubring :=
      V₀.nonunits_subset hy_nonunits_V₀
    -- Apply Q-containment from sub-residual (b).
    have hy_in_Q : (⟨(y : FractionRing (A ⧸ 𝔭)), hy_V₀⟩ : V₀) ∈ Q :=
      hQ_contains_I y hy_I hy_V₀
    -- Rebase at x via hy_eq.
    have hx_V₀ : x ∈ V₀.toSubring := by
      show (x : FractionRing (A ⧸ 𝔭)) ∈ V₀.toSubring
      rw [← hy_eq]; exact hy_V₀
    have hxQ : (⟨x, hx_V₀⟩ : V₀) ∈ Q := by
      have heq : (⟨x, hx_V₀⟩ : V₀) = ⟨(y : FractionRing (A ⧸ 𝔭)), hy_V₀⟩ := by
        apply Subtype.ext
        exact hy_eq.symm
      rw [heq]; exact hy_in_Q
    exact ValuationSubring.mem_nonunits_ofPrime_of_val_mem_prime V₀ Q hx_V₀ hxQ
  · -- A⁺ bound via range domination.
    intro f hf
    apply P.pulledBackValuation_le_one_of_le hle
    change V₀.valuation ((algebraMap (A ⧸ 𝔭) (FractionRing (A ⧸ 𝔭))).comp
      (Ideal.Quotient.mk 𝔭) f) ≤ 1
    apply (V₀.valuation_le_one_iff _).mpr
    apply hR'_le_V₀
    exact (P.range_le_rationalEnlargedSubring 𝔭 T s) ⟨⟨f, hAplus_le_A₀ hf⟩, rfl⟩
  · -- rational-quotient membership in V = V₀.ofPrime Q.
    intro t ht
    exact hle (hR'_le_V₀
      (P.rationalQuotient_mem_rationalEnlargedSubring 𝔭 T s ht))

end PairOfDefinition

/-! ### Height-one vertical generization (Wedhorn Remarks 7.38 / 7.40(5) / 4.12)

Coarsening a continuous valuation by the maximal convex subgroup avoiding a
divisibility-cofinal element `g₀ < 1` of its value group produces a continuous valuation
with `MulArchimedean` quotient value group; the support is unchanged
(`Valuation.coarsen_supp`). This is the vertical-generization step of Wedhorn Lemma 7.45:
combined with the `Cont`-level analytic point of
`exists_cont_analytic_supp_ge_of_nonOpen_prime` (Lemma745), it produces the height-one
analytic point above a non-open prime. -/

section HeightOneGenerization

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **Wedhorn Rem 7.38/7.40(5)+4.12 (generization core).** If `v` is continuous and
`g₀ < 1` is cofinal in the value group (`∀ γ, ∃ n, g₀ ^ n ≤ γ`), then the coarsening of
`v` by `maxAvoid g₀` is continuous and its value group `Γ ⧸ maxAvoid g₀` is
`MulArchimedean`. -/
theorem Valuation.coarsen_maxAvoid_isContinuous_mulArchimedean
    {Γ : Type*} [CommGroup Γ] [LinearOrder Γ] [IsOrderedMonoid Γ]
    (v : Valuation A (WithZero Γ)) (hv : v.IsContinuous)
    {g₀ : Γ} (hg₀_lt : g₀ < 1)
    (hcof : ∀ γ : Γ, ∃ n : ℕ, g₀ ^ n ≤ γ) :
    (v.coarsen (ConvexSubgroup.maxAvoid hg₀_lt.ne)).IsContinuous ∧
      MulArchimedean (Γ ⧸ (ConvexSubgroup.maxAvoid hg₀_lt.ne).toSubgroup) := by
  set H := ConvexSubgroup.maxAvoid hg₀_lt.ne with hH_def
  set π := QuotientGroup.mk' H.toSubgroup with hπ_def
  -- The class of `g₀` is `< 1` in the quotient.
  have hg₀_bar_ne : π g₀ ≠ 1 := fun h1 ↦
    ConvexSubgroup.not_mem_maxAvoid hg₀_lt.ne ((QuotientGroup.eq_one_iff g₀).mp h1)
  have hg₀_bar_lt : π g₀ < 1 :=
    lt_of_le_of_ne (H.quotientMk_le_one hg₀_lt.le) hg₀_bar_ne
  -- Cofinality descends to the quotient.
  have hcof_bar : ∀ d : Γ ⧸ H.toSubgroup, ∃ n : ℕ, π g₀ ^ n ≤ d := by
    intro d
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H.toSubgroup d
    obtain ⟨n, hn⟩ := hcof x
    exact ⟨n, by rw [← map_pow]; exact H.quotientMk_monotone hn⟩
  -- `MulArchimedean` of the quotient: every convex subgroup is trivial.
  have hArch : MulArchimedean (Γ ⧸ H.toSubgroup) := by
    rw [ConvexSubgroup.mulArchimedean_iff_convex_trivial]
    intro K
    by_cases hK : K = ⊥
    · exact Or.inl hK
    refine Or.inr ?_
    have hπ_mono : Monotone π := H.quotientMk_monotone
    -- The pullback of `K` strictly contains `H`, hence contains `g₀` by maximality.
    have hg₀K : π g₀ ∈ K := by
      by_contra hg₀_not
      have hK'_le : K.comap (π : Γ →* _) hπ_mono ≤ H :=
        ConvexSubgroup.le_maxAvoid_of_not_mem
          (fun hmem ↦ hg₀_not (ConvexSubgroup.mem_comap.mp hmem))
      apply hK
      ext d
      simp only [ConvexSubgroup.mem_bot]
      constructor
      · intro hd
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H.toSubgroup d
        have hx_K' : x ∈ K.comap (π : Γ →* _) hπ_mono := ConvexSubgroup.mem_comap.mpr hd
        exact (QuotientGroup.eq_one_iff x).mpr (SetLike.le_def.mp hK'_le hx_K')
      · rintro rfl
        exact K.one_mem
    -- Sandwich: every element of the quotient lies between powers of `π g₀`.
    ext d
    simp only [ConvexSubgroup.mem_top, iff_true]
    obtain ⟨n, hn⟩ := hcof_bar d
    obtain ⟨m, hm⟩ := hcof_bar d⁻¹
    have hd_le : d ≤ (π g₀ ^ m)⁻¹ := by
      rw [← inv_inv d]
      exact inv_le_inv' hm
    exact K.convex (K.pow_mem hg₀K n) (K.inv_mem (K.pow_mem hg₀K m)) hn hd_le
  refine ⟨?_, hArch⟩
  -- Continuity of the coarsening: additive translates of `v`-sublevels.
  intro δ
  rcases eq_or_ne δ 0 with rfl | hδ
  · simp only [not_lt_zero]
    exact isOpen_empty
  obtain ⟨d, rfl⟩ := WithZero.ne_zero_iff_exists.mp hδ
  rw [isOpen_iff_mem_nhds]
  intro a₀ ha₀
  obtain ⟨n, hn⟩ := hcof_bar d
  -- `v`-sublevel at `g₀ ^ (n + 1)`; its class is strictly below `π g₀ ^ n ≤ d`.
  have hsub : ∀ b : A, v b < ↑(g₀ ^ (n + 1)) →
      v.coarsen H b < ↑d := by
    intro b hb
    rcases eq_or_ne (v b) 0 with hb0 | hb0
    · have : v.coarsen H b = 0 := by
        simp [Valuation.coarsen_apply, hb0]
      simp [this]
    obtain ⟨gb, hgb⟩ := WithZero.ne_zero_iff_exists.mp hb0
    have hgb_lt : gb < g₀ ^ (n + 1) := by
      rw [← hgb] at hb
      exact_mod_cast hb
    have hπgb : π gb ≤ π g₀ ^ (n + 1) := by
      rw [← map_pow]
      exact H.quotientMk_monotone hgb_lt.le
    have hstep : π g₀ ^ (n + 1) < π g₀ ^ n := by
      rw [pow_succ]
      exact mul_lt_of_lt_one_right' _ hg₀_bar_lt
    have : v.coarsen H b = ↑(π gb) := by
      simp only [Valuation.coarsen_apply, ← hgb, WithZero.mapMonoidWithZeroHom_apply_coe]
      rfl
    rw [this]
    exact_mod_cast lt_of_le_of_lt hπgb (lt_of_lt_of_le hstep hn)
  have hopen : IsOpen {b : A | v b < ↑(g₀ ^ (n + 1))} := hv _
  have hmem : a₀ + 0 ∈ (a₀ + ·) '' {b : A | v b < ↑(g₀ ^ (n + 1))} :=
    Set.mem_image_of_mem _ (by simp)
  refine Filter.mem_of_superset
    (((Homeomorph.addLeft a₀).isOpenMap _ hopen).mem_nhds (by simpa using hmem)) ?_
  rintro _ ⟨b, hb, rfl⟩
  calc v.coarsen H (a₀ + b) ≤ max (v.coarsen H a₀) (v.coarsen H b) :=
        Valuation.map_add _ _ _
    _ < ↑d := max_lt ha₀ (hsub b hb)

end HeightOneGenerization
