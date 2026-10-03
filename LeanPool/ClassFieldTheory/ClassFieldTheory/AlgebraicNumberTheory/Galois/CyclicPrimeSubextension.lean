/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
/-!
# The prime-degree subextension of a cyclic prime-power extension

This file constructs a prime-degree intermediate field.
For a nontrivial cyclic Galois extension whose group has order
`p ^ exponent`, the index-`p` subgroup constructed in
`SplittingGroupTheory` is sent through the finite Galois
correspondence.  Its fixed field is an actual cyclic Galois extension
of the base of degree `p`.

The finite-place decomposition group in that subextension is obtained
by restricting the decomposition group of `L / K`.  Thus complete
splitting descends to the prime-degree subextension, and nonsplitting
there ascends to `L`.
-/

@[expose] public section

open scoped NumberField IsMulCommutative
open NumberField IsDedekindDomain

noncomputable
section

open AlgebraicNumberTheory.Valuations
open HilbertRamification

section ValuationRestriction

variable {F E : Type}
    [Field F] [Field E] [Algebra F E]

open scoped Classical in
/-- Restrict an actual extension of an absolute value to an
intermediate field. -/
def restrictAbsoluteValueExtensionToIntermediate
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF E)
    (M : IntermediateField F E) :
    AbsoluteValueExtension vF M where
  val :=
    w.1.comp (f := M.val.toRingHom)
      M.val.injective
  property x := by
    change w.1 (algebraMap F E x) = vF x
    exact w.2 x

open scoped Classical in
@[simp]
theorem restrictAbsoluteValueExtensionToIntermediate_apply
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF E)
    (M : IntermediateField F E)
    (x : M) :
    (restrictAbsoluteValueExtensionToIntermediate
      vF w M).1 x = w.1 x :=
  rfl

open scoped Classical in
/-- Regard the original extension as an extension of its restriction
to an intermediate field. -/
def absoluteValueExtensionOverIntermediate
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF E)
    (M : IntermediateField F E) :
    AbsoluteValueExtension
      (restrictAbsoluteValueExtensionToIntermediate
        vF w M).1 E where
  val := w.1
  property _ := rfl

open scoped Classical in
/-- Restriction of an extension of a nontrivial absolute value remains
nontrivial. -/
theorem restrictAbsoluteValueExtensionToIntermediate_isNontrivial
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (w : AbsoluteValueExtension vF E)
    (M : IntermediateField F E) :
    (restrictAbsoluteValueExtensionToIntermediate
      vF w M).1.IsNontrivial := by
  rcases hvF with ⟨a, ha, hva⟩
  refine
    ⟨algebraMap F M a,
      (map_ne_zero (algebraMap F M)).2 ha, ?_⟩
  simpa only
    [(restrictAbsoluteValueExtensionToIntermediate
      vF w M).2 a] using hva

open scoped Classical in
/-- For a normal subextension represented by a field type, its
decomposition group is the restriction image of the decomposition
group upstairs.

The reverse inclusion uses valuation-extension counting over the subextension: a
lift of a valuation-preserving automorphism is corrected by an
automorphism fixing that field. -/
theorem absoluteValueDecompositionGroup_map_restrictNormalHom
    {M : Type*}
    [Field M] [Algebra F M] [Algebra M E]
    [IsScalarTower F M E]
    [IsGalois F E]
    [Normal F M]
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (w : AbsoluteValueExtension vF E) :
    (absoluteValueDecompositionGroup F w.1).map
        (AlgEquiv.restrictNormalHom
          (F := F) (K₁ := E) M) =
      absoluteValueDecompositionGroup F
        (w.1.comp (f := algebraMap M E)
          (algebraMap M E).injective) := by
  let : IsGalois M E :=
    IsGalois.tower_top_of_isGalois F M E
  let vM : AbsoluteValueExtension vF M :=
    { val :=
        w.1.comp (f := algebraMap M E)
          (algebraMap M E).injective
      property := by
        intro x
        change
          w.1 (algebraMap M E (algebraMap F M x)) =
            vF x
        rw [← IsScalarTower.algebraMap_apply F M E]
        exact w.2 x }
  let q :=
    AlgEquiv.restrictNormalHom
      (F := F) (K₁ := E) M
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    change
      ∀ x : E,
        w.1 (σ x) < 1 ↔ w.1 x < 1
      at hσ
    change
      ∀ x : M,
        vM.1 ((q σ) x) < 1 ↔
          vM.1 x < 1
    intro x
    have hleft :
        vM.1 ((q σ) x) =
          w.1 (σ (algebraMap M E x)) := by
      change
        w.1 (algebraMap M E ((q σ) x)) =
          w.1 (σ (algebraMap M E x))
      exact congrArg w.1
        (AlgEquiv.restrictNormal_commutes
          σ M x)
    have hright :
        vM.1 x = w.1 (algebraMap M E x) :=
      rfl
    rw [hleft, hright]
    exact hσ (algebraMap M E x)
  · intro hτ
    obtain ⟨σ : E ≃ₐ[F] E, hσ⟩ :=
      (AlgEquiv.restrictNormalHom_surjective
        (F := F) (K₁ := M) (E := E)) τ
    have hτext :
        absoluteValueExtensionConjugate
            vF vM τ = vM :=
      (mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
        vF hvF vM τ).mp hτ
    let wSigma :
        AbsoluteValueExtension vM.1 E :=
      { val :=
          absoluteValueConjugate w.1 σ
        property := by
          intro x
          calc
            w.1 (σ (algebraMap M E x)) =
                vM.1 ((q σ) x) := by
              change
                w.1 (σ (algebraMap M E x)) =
                  w.1 (algebraMap M E ((q σ) x))
              exact congrArg w.1
                (AlgEquiv.restrictNormal_commutes
                  σ M x).symm
            _ = vM.1 (τ x) := by
              rw [hσ]
            _ = vM.1 x := by
              have hx :=
                congrArg
                  (fun e :
                    AbsoluteValueExtension vF M =>
                      e.1 x)
                  hτext
              exact hx }
    let wOverM : AbsoluteValueExtension vM.1 E :=
      { val := w.1
        property := by
          intro x
          rfl }
    let hvM : vM.1.IsNontrivial := by
      rcases hvF with ⟨a, ha, hva⟩
      refine
        ⟨algebraMap F M a,
          (map_ne_zero (algebraMap F M)).2 ha, ?_⟩
      simpa only [vM.2 a] using hva
    obtain ⟨ηM, hηM⟩ :=
      absoluteValueConjugacy vM.1 hvM
        wOverM wSigma
    let η : E ≃ₐ[F] E :=
      ηM.restrictScalars F
    have hqη : q η = 1 := by
      apply AlgEquiv.ext
      intro x
      apply (algebraMap M E).injective
      calc
        algebraMap M E ((q η) x) =
            η (algebraMap M E x) :=
          AlgEquiv.restrictNormal_commutes
            η M x
        _ = algebraMap M E x :=
          ηM.commutes x
    let δ : E ≃ₐ[F] E :=
      σ * η⁻¹
    have hδ :
        δ ∈ absoluteValueDecompositionGroup F w.1 := by
      change
        ∀ x : E,
          w.1 (δ x) < 1 ↔
            w.1 x < 1
      intro x
      have hx :=
        congrArg
          (fun e : AbsoluteValueExtension vM.1 E =>
            e.1 (ηM⁻¹ x))
          hηM
      change
        w.1 (σ (ηM⁻¹ x)) =
          w.1 (ηM (ηM⁻¹ x))
        at hx
      have hvalue :
          w.1 (δ x) = w.1 x := by
        simpa [δ, η] using hx
      rw [hvalue]
    refine ⟨δ, hδ, ?_⟩
    change q δ = τ
    rw [show δ = σ * η⁻¹ from rfl,
      map_mul, map_inv, hqη, inv_one,
      mul_one, hσ]

end ValuationRestriction

section DecompositionGroupChoice

variable {F L : Type*}
    [Field F] [Field L] [Algebra F L]

open scoped Classical in
/-- Decomposition groups depend only on the valuation class. -/
theorem absoluteValueDecompositionGroup_eq_of_absoluteValue_isEquiv
    (w w' : AbsoluteValue L ℝ)
    (hww' : w.IsEquiv w') :
    absoluteValueDecompositionGroup F w =
      absoluteValueDecompositionGroup F w' := by
  have hlt : ∀ x : L, w x < 1 ↔ w' x < 1 :=
    AbsoluteValue.isEquiv_iff_lt_one_iff.mp hww'
  ext σ
  simp only [mem_absoluteValueDecompositionGroup_iff]
  constructor
  · intro hσ x
    exact
      (hlt (σ x)).symm.trans
        ((hσ x).trans (hlt x))
  · intro hσ x
    exact
      (hlt (σ x)).trans
        ((hσ x).trans (hlt x).symm)

open scoped Classical in
/-- In an abelian Galois extension, conjugating an exact extension does
not change its decomposition subgroup. -/
theorem absoluteValueDecompositionGroup_conjugate_eq_of_isMulCommutative
    [IsMulCommutative (L ≃ₐ[F] L)]
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF L)
    (ρ : L ≃ₐ[F] L) :
    absoluteValueDecompositionGroup F
        (absoluteValueExtensionConjugate
          vF w ρ).1 =
      absoluteValueDecompositionGroup F w.1 := by
  ext τ
  change
    (∀ x : L,
      w.1 (ρ (τ x)) < 1 ↔ w.1 (ρ x) < 1) ↔
      ∀ x : L, w.1 (τ x) < 1 ↔ w.1 x < 1
  constructor
  · intro hτ x
    have hx := hτ (ρ⁻¹ x)
    have hleft :
        ρ (τ (ρ⁻¹ x)) = τ x := by
      calc
        ρ (τ (ρ⁻¹ x)) =
            τ (ρ (ρ⁻¹ x)) := by
          change
            (ρ * τ) (ρ⁻¹ x) =
              (τ * ρ) (ρ⁻¹ x)
          rw [mul_comm]
        _ = τ x := by simp
    have hright : ρ (ρ⁻¹ x) = x := by simp
    rwa [hleft, hright] at hx
  · intro hτ x
    have hx := hτ (ρ x)
    have hcomm :
        ρ (τ x) = τ (ρ x) := by
      change (ρ * τ) x = (τ * ρ) x
      rw [mul_comm]
    rwa [hcomm]

open scoped Classical in
/-- In an abelian Galois extension the decomposition subgroup is
independent of the exact extension above the base place. -/
theorem absoluteValueDecompositionGroup_eq_of_exactExtensions_of_isMulCommutative
    [IsGalois F L]
    [IsMulCommutative (L ≃ₐ[F] L)]
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (w w' : AbsoluteValueExtension vF L) :
    absoluteValueDecompositionGroup F w.1 =
      absoluteValueDecompositionGroup F w'.1 := by
  obtain ⟨ρ, hρ⟩ :=
    absoluteValueConjugacy vF hvF w w'
  rw [hρ,
    absoluteValueDecompositionGroup_conjugate_eq_of_isMulCommutative
      (F := F) vF w ρ]

end DecompositionGroupChoice

section ValuationRestriction

variable {F E : Type}
    [Field F] [Field E] [Algebra F E]

open scoped Classical in
/-- Triviality of a decomposition group is preserved when the chosen
extension is conjugated. -/
theorem absoluteValueDecompositionGroup_conjugate_eq_bot
    (vF : AbsoluteValue F ℝ)
    (w : AbsoluteValueExtension vF E)
    (ρ : E ≃ₐ[F] E)
    (hbot :
      absoluteValueDecompositionGroup F w.1 = ⊥) :
    absoluteValueDecompositionGroup F
        (absoluteValueExtensionConjugate
          vF w ρ).1 = ⊥ := by
  apply le_bot_iff.mp
  intro τ hτ
  rw [Subgroup.mem_bot]
  change
    ∀ x : E,
      w.1 (ρ (τ x)) < 1 ↔
        w.1 (ρ x) < 1
    at hτ
  let δ : E ≃ₐ[F] E :=
    ρ * τ * ρ⁻¹
  have hδ :
      δ ∈ absoluteValueDecompositionGroup F w.1 := by
    change
      ∀ x : E,
        w.1 (δ x) < 1 ↔
          w.1 x < 1
    intro x
    simpa [δ] using hτ (ρ⁻¹ x)
  have hδOne : δ = 1 :=
    Subgroup.mem_bot.mp (hbot ▸ hδ)
  have hconj :=
    congrArg (fun z : E ≃ₐ[F] E =>
      ρ⁻¹ * z * ρ) hδOne
  simpa [δ, mul_assoc] using hconj

open scoped Classical in
/-- For a Galois extension, triviality of the decomposition group is
independent of the chosen extension of the base absolute value. -/
theorem absoluteValueDecompositionGroup_eq_bot_independent_extension
    [IsGalois F E]
    (vF : AbsoluteValue F ℝ)
    (hvF : vF.IsNontrivial)
    (w w' : AbsoluteValueExtension vF E)
    (hbot :
      absoluteValueDecompositionGroup F w.1 = ⊥) :
    absoluteValueDecompositionGroup F w'.1 = ⊥ := by
  obtain ⟨ρ, hρ⟩ :=
    absoluteValueConjugacy vF hvF w w'
  rw [hρ]
  exact
    absoluteValueDecompositionGroup_conjugate_eq_bot
      vF w ρ hbot

end ValuationRestriction

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]

omit [NumberField K] [NumberField L] [IsGalois K L] in
open scoped Classical in
/-- A cyclic group of nonzero prime-power order has an actual normal
subgroup of index `p`. -/
theorem exists_index_prime_normal_subgroup
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    ∃ P : Subgroup (L ≃ₐ[K] L),
      P.index = p ∧
      P.Normal ∧
      Nat.card ((L ≃ₐ[K] L) ⧸ P) = p := by
  have hgroupCard :
      1 < Nat.card (L ≃ₐ[K] L) := by
    rw [hcard]
    exact
      one_lt_pow₀ hp.one_lt hexponent.ne'
  let : Nontrivial (L ≃ₐ[K] L) :=
    Finite.one_lt_card_iff_nontrivial.mp
      hgroupCard
  obtain
      ⟨P, _hbot, hPindex, hPnormal,
        hPquotient⟩ :=
    cyclic_exists_normal_index_prime_supergroup
      hp hexponent hcard
      (⊥ : Subgroup (L ≃ₐ[K] L))
      bot_ne_top
  exact
    ⟨P, hPindex, hPnormal, hPquotient⟩

open scoped Classical in
/-- The chosen index-`p` subgroup of the global cyclic Galois group. -/
noncomputable def cyclicPrimeIndexSubgroup
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    Subgroup (L ≃ₐ[K] L) :=
  (exists_index_prime_normal_subgroup
    (K := K) (L := L)
    hp hexponent hcard).choose

omit [NumberField K] [NumberField L] [IsGalois K L] in
open scoped Classical in
theorem cyclicPrimeIndexSubgroup_index
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    (cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard).index = p :=
  (exists_index_prime_normal_subgroup
    (K := K) (L := L)
    hp hexponent hcard).choose_spec.1

omit [NumberField K] [NumberField L] [IsGalois K L] in
open scoped Classical in
theorem cyclicPrimeIndexSubgroup_normal
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    (cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard).Normal :=
  (exists_index_prime_normal_subgroup
    (K := K) (L := L)
    hp hexponent hcard).choose_spec.2.1

omit [NumberField K] [NumberField L] [IsGalois K L] in
open scoped Classical in
theorem cyclicPrimeIndexSubgroup_quotient_card
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    Nat.card
        ((L ≃ₐ[K] L) ⧸
          cyclicPrimeIndexSubgroup
            (K := K) (L := L)
            hp hexponent hcard) =
      p :=
  (exists_index_prime_normal_subgroup
    (K := K) (L := L)
    hp hexponent hcard).choose_spec.2.2

open scoped Classical in
/-- The actual degree-`p` intermediate field in the cyclic prime-power reduction. -/
noncomputable def cyclicPrimeSubextension
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    IntermediateField K L :=
  IntermediateField.fixedField
    (cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard)

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- The constructed intermediate extension is Galois over `K`. -/
noncomputable instance cyclicPrimeSubextension_isGalois
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    IsGalois K
      (cyclicPrimeSubextension
        (K := K) (L := L)
        hp hexponent hcard) := by
  unfold cyclicPrimeSubextension
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  infer_instance

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- The constructed intermediate extension has degree exactly `p`. -/
theorem cyclicPrimeSubextension_finrank
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    Module.finrank K
        (cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard) =
      p := by
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  calc
    Module.finrank K M =
        Nat.card (M ≃ₐ[K] M) :=
      (IsGalois.card_aut_eq_finrank K M).symm
    _ = Nat.card ((L ≃ₐ[K] L) ⧸ P) :=
      Nat.card_congr
        (IsGalois.normalAutEquivQuotient P).symm.toEquiv
    _ = p :=
      cyclicPrimeIndexSubgroup_quotient_card
        (K := K) (L := L)
        hp hexponent hcard

omit [NumberField K] [NumberField L] in
open scoped Classical in
/-- The Galois group of the constructed degree-`p` extension is
cyclic. -/
theorem cyclicPrimeSubextension_isCyclic
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent) :
    IsCyclic
      (cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard ≃ₐ[K]
        cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard) := by
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  have hquotient :
      IsCyclic ((L ≃ₐ[K] L) ⧸ P) :=
    isCyclic_of_surjective
      (QuotientGroup.mk' P)
      (QuotientGroup.mk'_surjective P)
  exact
    (IsGalois.normalAutEquivQuotient P).isCyclic.mp
      hquotient

open scoped Classical in
/-- The decomposition subgroup in the constructed subextension,
obtained by restricting the decomposition subgroup in `L / K`. -/
noncomputable def cyclicPrimeSubextensionDecompositionGroup
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup
      (cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard ≃ₐ[K]
        cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard) := by
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  letI : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  exact
    (finitePlaceDecompositionGroup
      (K := K) (L := L) v).map
        (AlgEquiv.restrictNormalHom M)

omit [NumberField L] in
open scoped Classical in
/-- The restricted decomposition group agrees with the quotient
decomposition group transported by the fixed-field Galois
correspondence. -/
theorem cyclicPrimeSubextensionDecompositionGroup_eq_quotient_image
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K)) :
    cyclicPrimeSubextensionDecompositionGroup
        (K := K) (L := L)
        hp hexponent hcard v =
      (finitePlaceDecompositionGroupInQuotient
        (K := K) (L := L) v
        (cyclicPrimeIndexSubgroup
          (K := K) (L := L)
          hp hexponent hcard)).map
        (IsGalois.normalAutEquivQuotient
          (cyclicPrimeIndexSubgroup
            (K := K) (L := L)
            hp hexponent hcard)).toMonoidHom := by
  let P :=
    cyclicPrimeIndexSubgroup
      (K := K) (L := L)
      hp hexponent hcard
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : P.Normal :=
    cyclicPrimeIndexSubgroup_normal
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  change
    (finitePlaceDecompositionGroup
      (K := K) (L := L) v).map
        (AlgEquiv.restrictNormalHom M) =
      ((finitePlaceDecompositionGroup
        (K := K) (L := L) v).map
          (QuotientGroup.mk' P)).map
        (IsGalois.normalAutEquivQuotient P).toMonoidHom
  rw [Subgroup.map_map]
  congr 1

omit [NumberField L] in
open scoped Classical in
/-- Complete splitting in `L` implies complete splitting in the
constructed prime-degree subextension. -/
theorem finitePlaceSplitsCompletely_in_cyclicPrimeSubextension
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    cyclicPrimeSubextensionDecompositionGroup
        (K := K) (L := L)
        hp hexponent hcard v = ⊥ := by
  unfold
    cyclicPrimeSubextensionDecompositionGroup
  rw [show
      finitePlaceDecompositionGroup
          (K := K) (L := L) v = ⊥
      from hsplit]
  exact Subgroup.map_bot _

omit [NumberField L] in
open scoped Classical in
/-- Complete splitting in `L` implies complete splitting, in the
standard chosen-extension sense, in the actual fixed intermediate
field. -/
theorem finitePlaceSplitsCompletely_in_cyclicPrimeSubextension_actual
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hsplit :
      FinitePlaceSplitsCompletely
        (K := K) (L := L) v) :
    FinitePlaceSplitsCompletely
      (K := K)
      (L := cyclicPrimeSubextension
        (K := K) (L := L)
        hp hexponent hcard) v := by
  let M :=
    cyclicPrimeSubextension
      (K := K) (L := L)
      hp hexponent hcard
  let : IsGalois K M :=
    cyclicPrimeSubextension_isGalois
      (K := K) (L := L)
      hp hexponent hcard
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let wM :=
    restrictAbsoluteValueExtensionToIntermediate
      vK w M
  have hwBot :
      absoluteValueDecompositionGroup K w.1 = ⊥ :=
    hsplit
  have hwMbot :
      absoluteValueDecompositionGroup K wM.1 = ⊥ := by
    change
      absoluteValueDecompositionGroup K
        (w.1.comp (f := algebraMap M L)
          (algebraMap M L).injective) = ⊥
    rw [← absoluteValueDecompositionGroup_map_restrictNormalHom
      (M := M) vK hvK w]
    rw [hwBot]
    exact Subgroup.map_bot _
  change
    absoluteValueDecompositionGroup K
      (chosenFinitePlaceExtension
        (L := M) v).1 = ⊥
  exact
    absoluteValueDecompositionGroup_eq_bot_independent_extension
      vK hvK wM
      (chosenFinitePlaceExtension (L := M) v)
      hwMbot

omit [NumberField L] in
open scoped Classical in
/-- Contrapositive in the standard chosen-extension sense: a place
nonsplit in the constructed degree-`p` field is nonsplit in `L`. -/
theorem finitePlace_not_splitsCompletely_of_not_in_cyclicPrimeSubextension_actual
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hnonsplit :
      ¬ FinitePlaceSplitsCompletely
        (K := K)
        (L := cyclicPrimeSubextension
          (K := K) (L := L)
          hp hexponent hcard) v) :
    ¬ FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  intro hsplit
  exact
    hnonsplit
      (finitePlaceSplitsCompletely_in_cyclicPrimeSubextension_actual
        (K := K) (L := L)
        hp hexponent hcard v hsplit)

omit [NumberField L] in
open scoped Classical in
/-- Contrapositive form: a finite place nonsplit in the prime-degree
subextension is already nonsplit in `L`. -/
theorem finitePlace_not_splitsCompletely_of_not_in_cyclicPrimeSubextension
    {p exponent : ℕ}
    (hp : p.Prime)
    (hexponent : 0 < exponent)
    (hcard :
      Nat.card (L ≃ₐ[K] L) =
        p ^ exponent)
    (v : HeightOneSpectrum (𝓞 K))
    (hnonsplit :
      cyclicPrimeSubextensionDecompositionGroup
          (K := K) (L := L)
          hp hexponent hcard v ≠ ⊥) :
    ¬ FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  intro hsplit
  exact
    hnonsplit
      (finitePlaceSplitsCompletely_in_cyclicPrimeSubextension
        (K := K) (L := L)
        hp hexponent hcard v hsplit)
