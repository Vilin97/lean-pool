/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictedPowerSeries
import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentCoverExact
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FlatnessResults
import LeanPool.UniformSheafyTateDomains.AdicSpaces.CechCohomology
import Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Tate Acyclicity (Wedhorn Theorem 8.28(b))

We define the class `IsStronglyNoetherianTate` (Wedhorn Definition 6.36) and develop
the proof infrastructure for **Theorem 8.28(b)**: strongly noetherian Tate rings are sheafy.

## Main definitions

* `IsStronglyNoetherianTate` : A Tate ring `A` is *strongly noetherian* if
  `A⟨X₁, …, Xₖ⟩` is noetherian for every `k` (Definition 6.36).

## Main results

* `LaurentCoverAcyclicity.laurentCover_acyclic_discrete` : The 2-element Laurent cover
  is exact for discrete noetherian rings (wraps `LaurentCoverExact.lean`).
* `Refinement.separation_of_finer` : If a finer cover has separation (injective
  augmentation), then the coarser cover has separation too.
* `Refinement.cochainMap_comp_aug` : The augmentation commutes with the refinement
  cochain map.
* `IsSheafy.ofStronglyNoetherianTate_discrete` : Discrete rings are sheafy
  (via `IsSheafy.discrete`).

## Proof outline (Wedhorn pp.82-85)

1. **Laurent cover exactness** (Lemma 8.33): For any `f ∈ A`, the 2-element cover
   `{R(f/1), R(1/f)}` gives an exact Čech complex. (Proved in `LaurentCoverExact.lean`.)
2. **Flatness** (Lemma 8.31 + Prop 8.30): Restriction maps are flat, and the product
   restriction for a cover is faithfully flat. (Proved in `FlatnessResults.lean`.)
3. **Acyclicity propagation** (Lemma 8.34): Products of 2-element Laurent covers are
   acyclic, and every standard rational cover refines such a product.
4. **Refinement transfers separation** (Proposition A.3): If `V` refines `U` and `V`
   has separation, then `U` has separation.

## Current status

### Discrete case (COMPLETE — 0 sorry)
- Laurent cover exactness: `LaurentCoverExact.lean`
- Flatness: `FlatnessResults.lean`
- Discrete sheaf condition: `StructureSheaf.lean` (`IsSheafy.discrete`)
- Separation via refinement: proved below
- Gluing (`discrete_gluing`): Fully proved. The numerator compatibility uses a common
  refinement `D₃` with `s₃ = D₁.s * D₂.s` (via `rationalOpen_inter`), the `hcompat`
  hypothesis, and the Mathlib-style power absorption (following
  `Localization.existsUnique_algebraMap_eq_of_span_eq_top`).

### General (non-discrete) case (algebraic foundation complete)
The algebraic ingredients are all proved:
- Laurent cover injectivity via Krull intersection (`epsilonHom_gen_injective`)
- Row 2 exactness (`row2_exact_at_middle`)
- Tate algebra flatness (`flat_quotient_*_general`)

The remaining gaps for the general case are topological:
- **G2-topo**: Correct T-topology on Tate algebra (I-adic, not product topology)
- **Presheaf identification**: Full isomorphism `presheafValue D ≅ A⟨X⟩/(1-sX)`
- **Categorical wrapping**: Connecting `AbPresheaf`/`FiniteCover` to `RationalCoveringData`

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 6.36, Theorem 8.28(b)
-/

open ValuationSpectrum

/-! ### Class definition -/

/-- A Tate ring `A` is **strongly noetherian** (Definition 6.36 of Wedhorn) if the
restricted power series ring `A⟨X₁, …, Xₖ⟩` is noetherian for every `k ≥ 0`.

Equivalently, every Tate ring topologically of finite type over `A` is noetherian.
This is stronger than just assuming `A` is noetherian. -/
class IsStronglyNoetherianTate (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] extends IsTateRing A, IsStronglyNoetherian A where

/-! ### Laurent cover acyclicity -/

namespace LaurentCoverAcyclicity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-! #### Discrete case -/

/-- The 2-element Laurent cover `{R(f/1), R(1/f)}` yields an exact Čech complex
for discrete rings. This is the discrete case of Lemma 8.33.

The exact sequence `0 → A → B₁ × B₂ → B₁₂ → 0` where:
- `B₁ = A⟨X⟩/(f-X) ≅ A`
- `B₂ = A⟨X⟩/(1-fX) ≅ Localization.Away f`
- `B₁₂ ≅ Localization.Away f`

is proved in `LaurentCoverExact.lean`.

The 2-element Laurent cover is acyclic for discrete noetherian rings.
This wraps `laurentCover_exact` from `LaurentCoverExact.lean`. -/
theorem laurentCover_acyclic_discrete [DiscreteTopology A] [IsNoetherianRing A] (f : A) :
    Function.Injective (LaurentCover.epsilonHom f) ∧
    Function.Surjective (LaurentCover.deltaMap f) ∧
    (∀ x, LaurentCover.deltaMap f (LaurentCover.epsilonHom f x) = 0) ∧
    (∀ p, LaurentCover.deltaMap f p = 0 →
      ∃ a, LaurentCover.epsilonHom f a = p) :=
  LaurentCover.laurentCover_exact f

/-- The epsilon map is injective for any element `f` in a discrete ring (without
the noetherian hypothesis). This uses the simpler proof via the first projection
and the `quotientFSubXEquiv`.

This is the **separation condition** for the 2-element Laurent cover. -/
theorem separation_of_laurentCover_discrete [DiscreteTopology A] (f : A) :
    Function.Injective (LaurentCover.epsilonHom f) :=
  LaurentCover.epsilonHom_injective f

/-! #### General (non-discrete) case -/

/-- The epsilon map `ε : A → B₁(f) × B₂(f)` is injective for non-unit `f` in a
noetherian domain. This uses the Krull intersection theorem.

This is a stronger result than the discrete case: it works for any noetherian domain
with its natural topology, not just discrete rings. -/
theorem separation_of_laurentCover_general [IsDomain A] [IsNoetherianRing A]
    (f : A) (hf : ¬IsUnit f) :
    Function.Injective (LaurentCover.epsilonHom_gen f) :=
  LaurentCover.epsilonHom_gen_injective f hf

/-- Row 2 exactness: the kernel of the difference map `λ` equals the image of the
diagonal `ι`, for rings with T1 topology. This is the exactness at the middle term
of `A → A⟨X⟩² → A⟨ζ, ζ⁻¹⟩`. -/
theorem row2_exact_at_middle [T1Space A] :
    (∀ a : A, LaurentCover.lambdaMap (LaurentCover.iotaHom a) = 0) ∧
    (∀ p : ↥(TateAlgebra A) × ↥(TateAlgebra A),
      LaurentCover.lambdaMap p = 0 → ∃ a : A, LaurentCover.iotaHom a = p) :=
  LaurentCover.row2_exact_at_middle

end LaurentCoverAcyclicity

/-! ### Refinement transfers separation

This section proves the key abstract result: if a finer cover has separation
(injective augmentation), then the coarser cover has separation too.

This is the abstract version of Proposition A.3 of Wedhorn: if `V` refines `U`
and the Čech complex of `V` has separation, then the Čech complex of `U` has
separation.

**Direction convention.** `Refinement V U` means "V refines U" (V is finer):
each `V_j ⊆ U_{τ(j)}`. The cochain map goes `Cech(U) → Cech(V)`. The
augmentation commutes: `cochainMap(cechAug_U(x)) = cechAug_V(x)`.

**Key lemma.** If V refines U and V has separation (cechAug_V injective), then
U has separation (cechAug_U injective). Proof: if cechAug_U(x) = cechAug_U(y),
apply cochainMap to get cechAug_V(x) = cechAug_V(y), then V-separation gives x = y. -/

section RefinementSeparation

universe u v

variable {X : Type u} [TopologicalSpace X]
  {ι : Type v} [Fintype ι] {κ : Type v} [Fintype κ]

/-- The augmentation commutes with the refinement cochain map:
`r.cochainMap(cechAug(U)(x)) = cechAug(V)(x)`.

That is, restricting a global section first to `U`-pieces and then refining to
`V`-pieces gives the same result as restricting the global section directly to
`V`-pieces. This follows from functoriality of the presheaf restriction maps. -/
theorem Refinement.cochainMap_comp_aug (F : AbPresheaf X)
    {V : FiniteCover X κ} {U : FiniteCover X ι}
    (r : Refinement V U) (x : F.obj Set.univ) :
    r.cochainMap F 0 (cechAug F U x) = cechAug F V x := by
  ext σ
  simp only [Refinement.cochainMap, cechAug, F.res_comp]

/-- **Refinement preserves separation (Proposition A.3 of Wedhorn).**

If `V` refines `U` (each `V_j ⊆ U_{τ(j)}`) and `V` has the separation property
(injective augmentation), then `U` also has the separation property.

**Proof.** If `cechAug(U)(x) = cechAug(U)(y)`, applying the refinement cochain
map gives `r.cochainMap(cechAug(U)(x)) = r.cochainMap(cechAug(U)(y))`. By
`cochainMap_comp_aug`, this becomes `cechAug(V)(x) = cechAug(V)(y)`. Since
`V` has separation, `x = y`. -/
theorem Refinement.separation_of_finer (F : AbPresheaf X)
    {V : FiniteCover X κ} {U : FiniteCover X ι}
    (r : Refinement V U) (hV : IsSeparating F V) :
    IsSeparating F U := by
  intro x y hxy
  apply hV
  have h1 := congr_arg (r.cochainMap F 0) hxy
  rwa [r.cochainMap_comp_aug F x, r.cochainMap_comp_aug F y] at h1

/-- **Refinement preserves degree-zero acyclicity (separation part).**

If `V` refines `U` and `V` is degree-zero acyclic, then `U` has separation.
(This extracts just the separation part of the acyclicity.) -/
theorem Refinement.separation_of_degreeZeroAcyclic (F : AbPresheaf X)
    {V : FiniteCover X κ} {U : FiniteCover X ι}
    (r : Refinement V U) (hV : IsDegreeZeroAcyclic F V) :
    IsSeparating F U :=
  r.separation_of_finer F hV.1

end RefinementSeparation

/-! ### The chain from Laurent covers to IsSheafy

We document the complete logical chain from the Laurent cover exactness to the
sheaf condition, with each step either proved or precisely identified as a gap.

**Step 1** (DONE, 0 sorry): For each `f ∈ A`, the Laurent cover `{R(f/1), R(1/f)}`
has an exact Čech complex. In particular, `ε : A → B₁ × B₂` is injective.
- Discrete case: `LaurentCover.laurentCover_exact`
- General case: `LaurentCover.epsilonHom_gen_injective` (needs `¬IsUnit f`)
- Row 2: `LaurentCover.row2_exact_at_middle`

**Step 2** (DONE, 0 sorry for discrete; 4 sorry in saturation engine for general):
The quotient rings `B₁ = A⟨X⟩/(f-X)` and `B₂ = A⟨X⟩/(1-fX)` are flat over `A`.
- Discrete: `TateAlgebra.flat_quotient_fSubX`, `flat_quotient_oneSubfX`
- General: `flat_quotient_fSubX_general`, `flat_quotient_oneSubfX_general`

**Step 3** (DONE, 0 sorry): Refinement preserves separation.
- `Refinement.separation_of_finer`

**Step 4** (GAP — requires Lemma 7.54 + categorical wrapping): Every standard
rational covering is refined by a product of Laurent covers. This requires:
- Decomposing rational subsets `R(T/s)` into basic pieces (Lemma 7.54)
- Constructing `FiniteCover` from `RationalCoveringData`
- Wrapping `presheafValue` as an `AbPresheaf`
- Connecting `IsSeparating` to `productRestriction` injectivity

**Step 5** (DONE for discrete via direct proof): Separation for all rational
coverings gives `IsSheafy`.
- Discrete: `productRestriction_injective_discrete` in `Presheaf.lean`
- General: follows from Steps 1-4 once Step 4 is complete

For the discrete case, Steps 4 and 5 are bypassed by the direct proof
`productRestriction_injective_discrete` which uses a different argument
(trivial valuations at primes + radical ideal membership).
-/

/-! ### Faithful flatness perspective (Corollary 8.32)

For the general (non-discrete) case, the most direct route to `IsSheafy` goes
through faithful flatness rather than Čech cohomology:

1. Each presheaf value `presheafValue Dᵢ` is flat over `A` (Proposition 8.30).
2. The product `∏ presheafValue Dᵢ` is flat over `A` (products of flat modules).
3. The product is faithfully flat because the covering {R(Tᵢ/sᵢ)} covers Spec A
   (the `sᵢ` generate the unit ideal).
4. Faithfully flat maps are injective, giving `IsSheafy`.

For step 1, the flatness of `presheafValue D` follows from:
- The identification `presheafValue D ≅ completion of Localization.Away D.s`
- Localization is flat (Mathlib: `Localization.flat`)
- Completion of flat is flat for noetherian rings (Mathlib: `AdicCompletion.flat`)

For step 3, the surjectivity on spectra follows from the covering condition.

The abstract faithful flatness results are available in Mathlib
(`Module.FaithfullyFlat`). What's needed to complete the general proof is the
topological identification connecting `presheafValue` to `Localization.Away`
(or to the Tate algebra quotients).
-/

section FaithfulFlatPerspective

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A]

omit [PlusSubring A] in
/-- For discrete `A`, each presheaf value in a rational cover is flat over `A`
(Proposition 8.30, discrete case). Re-export of `canonicalMap_flat_discrete`. -/
theorem presheafValue_flat_discrete [DiscreteTopology A] (D : RationalLocData A) :
    @Module.Flat A (presheafValue D) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D)) :=
  canonicalMap_flat_discrete D

omit [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] in
/-- For discrete `A`, the localization `Localization.Away s` is flat over `A`.
This is the algebraic core behind presheaf flatness.

This is an immediate consequence of Mathlib's `Localization.flat`. -/
theorem localization_flat_over (s : A) :
    Module.Flat A (Localization.Away s) :=
  Localization.flat ..

end FaithfulFlatPerspective

/-! ### Theorem 8.28(b): Strongly noetherian Tate rings are sheafy -/

/-- If `s` is a unit in `Away t`, then `Away t` is a localization of `Away s` at the
image of `t`. This is the localization-localization principle: `A[1/t] = A[1/s][1/(image t)]`
when `s` is already a unit in `A[1/t]`. -/
private noncomputable def isLocAway_of_isUnit {A : Type*} [CommRing A] {s t : A}
    (hunit : IsUnit (algebraMap A (Localization.Away t) s)) :
    letI : Algebra (Localization.Away s) (Localization.Away t) :=
      (IsLocalization.Away.lift s hunit).toAlgebra
    IsLocalization.Away (algebraMap A (Localization.Away s) t) (Localization.Away t) := by
  letI : Algebra (Localization.Away s) (Localization.Away t) :=
    (IsLocalization.Away.lift s hunit).toAlgebra
  haveI : IsScalarTower A (Localization.Away s) (Localization.Away t) := by
    constructor; intro a x y; simp only [Algebra.smul_def]
    change IsLocalization.Away.lift s hunit (algebraMap A _ a * x) * y =
      algebraMap A _ a * (IsLocalization.Away.lift s hunit x * y)
    simp only [map_mul, IsLocalization.Away.lift_eq]; ring
  apply IsLocalization.Away.mk
  · change IsUnit (IsLocalization.Away.lift s hunit (algebraMap A _ t))
    rw [IsLocalization.Away.lift_eq]; exact IsLocalization.Away.algebraMap_isUnit t
  · intro z; obtain ⟨n, a, h⟩ := IsLocalization.Away.surj t z
    refine ⟨n, algebraMap A _ a, ?_⟩
    change z * (IsLocalization.Away.lift s hunit (algebraMap A _ t)) ^ n =
      IsLocalization.Away.lift s hunit (algebraMap A _ a)
    simp only [IsLocalization.Away.lift_eq]; exact h
  · intro a b hab
    have hdiff : IsLocalization.Away.lift s hunit (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hab
    obtain ⟨⟨r, ⟨_, m, rfl⟩⟩, hrm⟩ := IsLocalization.surj (Submonoid.powers s) (a - b)
    simp only at hrm
    have h1 : (algebraMap A (Localization.Away t)) r = 0 := by
      have := congr_arg (IsLocalization.Away.lift s hunit) hrm
      rw [map_mul, IsLocalization.Away.lift_eq, map_pow, IsLocalization.Away.lift_eq,
        hdiff, zero_mul] at this
      exact this.symm
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (S := Localization.Away t) t
      (show algebraMap A _ r = algebraMap A _ 0 by rw [h1, map_zero])
    simp only [mul_zero] at hk
    refine ⟨k, ?_⟩
    have hsm_unit : IsUnit (algebraMap A (Localization.Away s) (s ^ m)) :=
      IsLocalization.map_units (Localization.Away s) (⟨s ^ m, m, rfl⟩ : Submonoid.powers s)
    have h2 : (algebraMap A (Localization.Away s) (s ^ m)) *
        (algebraMap A (Localization.Away s) t ^ k * (a - b)) = 0 := by
      rw [mul_comm _ (algebraMap A _ t ^ k * _), mul_assoc, hrm,
        ← map_pow, ← map_mul, hk, map_zero]
    have h3 : algebraMap A (Localization.Away s) t ^ k * (a - b) = 0 :=
      hsm_unit.mul_right_eq_zero.mp h2
    rwa [mul_sub, sub_eq_zero] at h3

/-- The localization uniform space is `⊥` (discrete) when the base ring is discrete.
This is extracted from the proof of `coeRingHom_bijective_of_discrete` for reuse. -/
private theorem discreteUniformity_presheafValue {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
    [PlusSubring A] (D : RationalLocData A) :
    D.uniformSpace = ⊥ := by
  have htop : D.topology = ⊥ := locTopology_eq_bot_of_discrete D
  suffices h : D.uniformSpace.uniformity = Filter.principal SetRel.id by
    exact UniformSpace.ext (h.trans bot_uniformity.symm)
  change Filter.comap (fun p : Localization.Away D.s × Localization.Away D.s ↦
    p.2 - p.1) (@nhds (Localization.Away D.s) D.topology 0) = Filter.principal SetRel.id
  have hpure : @nhds (Localization.Away D.s) D.topology 0 = pure 0 := by
    rw [htop]; letI : TopologicalSpace (Localization.Away D.s) := ⊥
    haveI : DiscreteTopology (Localization.Away D.s) := ⟨rfl⟩
    exact congr_fun (nhds_discrete _) 0
  rw [hpure, Filter.comap_pure]
  ext s; simp only [Filter.mem_principal]
  constructor
  · intro h ⟨a, b⟩ (hab : a = b); exact h (show b - a = 0 by rw [hab, sub_self])
  · intro h ⟨a, b⟩ (hab : b - a = 0); exact h (sub_eq_zero.mp hab).symm

private theorem discreteTopology_presheafValue {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
    [PlusSubring A] (D : RationalLocData A) :
    @DiscreteTopology (presheafValue D) inferInstance := by
  have hbot := discreteUniformity_presheafValue D
  -- The completion of bot uniform space has discrete topology
  -- Key: coe is bijective (surjective uniform embedding), so it's a homeomorphism
  have hbij := coeRingHom_bijective_of_discrete D
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  haveI : DiscreteUniformity (Localization.Away D.s) := ⟨hbot⟩
  -- The source has DiscreteTopology (from DiscreteUniformity)
  -- coe is a uniform embedding
  have hue := UniformSpace.Completion.isUniformEmbedding_coe (Localization.Away D.s)
  -- coe is surjective
  have hsurj := hbij.2
  -- A surjective isUniformEmbedding is a homeomorphism → target is discrete
  have hemb : Topology.IsEmbedding D.coeRingHom := hue.isEmbedding
  -- isEmbedding + surjective → isOpenEmbedding
  have hopen := hemb.isOpenEmbedding_of_surjective hsurj
  -- OpenEmbedding is a homeomorphism when surjective
  rw [show (inferInstance : TopologicalSpace (presheafValue D)) =
    @UniformSpace.toTopologicalSpace _ (@UniformSpace.Completion.uniformSpace _ D.uniformSpace)
    from rfl]
  constructor
  ext U
  exact ⟨fun _ ↦ trivial, fun _ ↦ by
    rw [show U = D.coeRingHom '' (D.coeRingHom ⁻¹' U) from by
      rw [Set.image_preimage_eq _ hsurj]]
    exact hopen.isOpenMap _ (isOpen_discrete _)⟩

open Classical in
/-- The images `{algebraMap A (Away C.base.s) D.s | D ∈ C.covers}` generate the unit
ideal in `Away C.base.s`. This is the covering-implies-unit-ideal condition: if the
span were proper it would sit in a maximal (hence prime) ideal `q`; pulling `q` back
to a prime `p` of `A` with `C.base.s ∉ p` and all `D.s ∈ p` produces a trivial
valuation in `rationalOpen C.base.T C.base.s` not covered by any piece, contradicting
`C.hcover`. Extracted from the `hspan_top` step of `discrete_gluing`. -/
private theorem discrete_gluing_span_top {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    [IsHuberRing A] (C : RationalCoveringData A) :
    Ideal.span (↑(C.covers.image
      (fun D ↦ algebraMap A (Localization.Away C.base.s) D.s)) :
      Set (Localization.Away C.base.s)) = ⊤ := by
  classical
  -- C.base.s is in the radical of span {D.s | D ∈ covers} in A
  -- (by the covering condition + trivial valuation at primes).
  -- So C.base.s^M ∈ span {D.s} for some M.
  -- In Away C.base.s, algebraMap(C.base.s)^M is a unit, so 1 ∈ span {algebraMap D.s}.
  -- Direct proof via by_contra: if span ≠ ⊤, it's contained in a maximal (prime) ideal.
  -- Pull back to A to get a prime p of A not containing C.base.s but containing all D.s.
  -- The covering condition gives a contradiction.
  by_contra hne
  obtain ⟨q, hq_max, hq_le⟩ := Ideal.exists_le_maximal _ hne
  haveI : q.IsPrime := Ideal.IsMaximal.isPrime hq_max
  -- q is a prime of Away C.base.s containing all algebraMap(D.s).
  -- The comap p = q.comap(algebraMap) is a prime of A with C.base.s ∉ p.
  set p := q.comap (algebraMap A (Localization.Away C.base.s)) with hp_def
  have hp_prime : p.IsPrime := Ideal.IsPrime.comap _
  have hDs_in : ∀ D ∈ C.covers, D.s ∈ p := by
    intro D hD
    exact hq_le (Ideal.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨D, hD, rfl⟩)))
  have hbs_notin : C.base.s ∉ p := by
    intro hmem
    -- hmem : C.base.s ∈ p = q.comap(algebraMap), so algebraMap(C.base.s) ∈ q
    have : algebraMap A (Localization.Away C.base.s) C.base.s ∈ q := hmem
    exact Ideal.IsMaximal.ne_top hq_max (Ideal.eq_top_of_isUnit_mem q this
      (IsLocalization.map_units (Localization.Away C.base.s)
        (⟨C.base.s, 1, pow_one _⟩ : Submonoid.powers C.base.s)))
  -- Use the covering condition to get a contradiction.
  haveI := hp_prime
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  let φ : A →+* FractionRing (A ⧸ p) :=
    (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))).comp (Ideal.Quotient.mk p)
  let w : Valuation A (WithZero (Multiplicative ℤ)) :=
    (1 : Valuation (FractionRing (A ⧸ p)) _).comap φ
  let v := ofValuation w
  have hv_spa : v ∈ Spa A A⁺ := by
    refine ⟨?_, ?_⟩
    · apply isContinuous_ofValuation_of; intro γ; exact isOpen_discrete _
    · intro f _; change w f ≤ w 1
      simp only [w, Valuation.comap_apply, map_one]; exact Valuation.one_apply_le_one _
  have hv_supp : v.supp = p := by
    rw [supp_ofValuation]; ext b
    simp only [Valuation.mem_supp_iff, w, Valuation.comap_apply, φ,
      RingHom.comp_apply, Valuation.one_apply_eq_zero_iff]
    exact ⟨fun h ↦ Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero])),
      fun hb ↦ by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero]⟩
  have hw_s : w C.base.s = 1 := by
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    apply Valuation.one_apply_of_ne_zero; intro heq; apply hbs_notin
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero]))
  have hv_rat : v ∈ rationalOpen C.base.T C.base.s :=
    ⟨hv_spa,
      fun t _ ↦ by
        change w t ≤ w C.base.s; rw [hw_s]
        simp only [w, Valuation.comap_apply]
        exact Valuation.one_apply_le_one _,
      by change ¬ (w C.base.s ≤ w 0)
         simp only [hw_s, map_zero, le_zero_iff, one_ne_zero, not_false_eq_true, w]⟩
  obtain ⟨D, hD, hv_D⟩ := C.hcover v hv_rat
  exact (fun hDs ↦ hv_D.2.2 ((v.mem_supp_iff D.s).mp (hv_supp ▸ hDs)))
    (hDs_in D hD)

/-- **Numerator compatibility** for the discrete gluing core. Given local fractions
`g D = algebraMap (r' D) / D.s^N₀` realizing `f` (via `hg : f D = D.coeRingHom (g D)`),
for each pair `(D₁, D₂)` the numerators agree up to a power of `D₁.s * D₂.s`:
`∃ k, (D₁.s * D₂.s)^k * (r' D₁ * D₂.s^N₀) = (D₁.s * D₂.s)^k * (r' D₂ * D₁.s^N₀)`.
The proof builds the common refinement `D₃` with `s₃ = D₁.s * D₂.s` (its `hopen` is
vacuous because `D₁.P.I` is nilpotent in the discrete case), transports `hcompat` to
`ψ₁ (g D₁) = ψ₂ (g D₂)` in `Away D₃.s` through the bijective `coeRingHom`, cross-multiplies
with `hr'`, and reads off the annihilating power via `IsLocalization.Away.exists_of_eq`.
Extracted from the `hcompat_pow` step of `discrete_gluing`. -/
private theorem discrete_gluing_numerator_compat {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    [IsHuberRing A] (C : RationalCoveringData A)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂))
    (g : ∀ D : ↥C.covers, Localization.Away D.1.s)
    (hg : ∀ D : ↥C.covers, f D = D.1.coeRingHom (g D))
    (N₀ : ℕ) (r' : ↥C.covers → A)
    (hr' : ∀ D : ↥C.covers,
        g D * (algebraMap A (Localization.Away D.1.s) D.1.s) ^ N₀ =
        algebraMap A _ (r' D)) :
    ∀ (D₁ D₂ : ↥C.covers), ∃ k : ℕ,
        (D₁.1.s * D₂.1.s) ^ k * (r' D₁ * D₂.1.s ^ N₀) =
        (D₁.1.s * D₂.1.s) ^ k * (r' D₂ * D₁.1.s ^ N₀) := by
  open scoped Pointwise in
  intro D₁ D₂
  -- Construct the common refinement D₃ : RationalLocData A with s₃ = D₁.s * D₂.s.
  -- For discrete rings, the pair of definition has nilpotent I, making hopen vacuous.
  have hI_nilp : ∃ M : ℕ, D₁.1.P.I ^ M = ⊥ := by
    have hI_le : D₁.1.P.I ≤ nilradical D₁.1.P.A₀ := by
      intro ⟨a, ha⟩ haI
      have htn := D₁.1.P.isTopologicallyNilpotent_of_mem haI
      have h0 : ({0} : Set A) ∈ nhds (0 : A) := (isOpen_discrete {0}).mem_nhds rfl
      obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp (htn h0)
      exact ⟨N, Subtype.val_injective (by
        simp only [SubmonoidClass.mk_pow, Set.mem_singleton_iff.mp (hN N le_rfl),
          ZeroMemClass.coe_zero])⟩
    exact (Ideal.FG.isNilpotent_iff_le_nilradical D₁.1.P.fg).mpr hI_le
  obtain ⟨M, hIM⟩ := hI_nilp
  haveI : DecidableEq A := Classical.decEq A
  let D₃ : RationalLocData A :=
    { P := D₁.1.P
      T := insert D₁.1.s D₁.1.T * insert D₂.1.s D₂.1.T
      s := D₁.1.s * D₂.1.s
      hopen := ⟨M, fun b hb ↦ by
        have hb0 : (b : D₁.1.P.A₀) = 0 := by
          have := hIM ▸ hb; rwa [Ideal.mem_bot] at this
        rw [show (↑b : A) = 0 from by rw [hb0]; rfl]
        unfold divByS
        rw [IsLocalization.mk'_zero]
        exact (locSubring D₁.1.P _ _).zero_mem⟩ }
  -- D₃ refines both D₁ and D₂ via rationalOpen_inter.
  have h₃ : rationalOpen D₃.T D₃.s =
      rationalOpen D₁.1.T D₁.1.s ∩ rationalOpen D₂.1.T D₂.1.s := by
    change rationalOpen (insert D₁.1.s D₁.1.T * insert D₂.1.s D₂.1.T) (D₁.1.s * D₂.1.s) =
      rationalOpen D₁.1.T D₁.1.s ∩ rationalOpen D₂.1.T D₂.1.s
    rw [← rationalOpen_inter _ _ _ _ (Finset.mem_insert_self _ _)
      (Finset.mem_insert_self _ _), rationalOpen_insert_s, rationalOpen_insert_s]
  have h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s :=
    h₃ ▸ Set.inter_subset_left
  have h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s :=
    h₃ ▸ Set.inter_subset_right
  -- From hcompat: the restrictions of f D₁ and f D₂ to D₃ agree.
  have hcompat₃ := hcompat D₁ D₂ D₃ h₃₁ h₃₂
  -- Transport to the localization level: restrictionMapAlg sends g to g.
  -- restrictionMap = restrictionMapHom = extensionHom(restrictionMapAlg).
  -- For discrete rings, coeRingHom is bijective, so
  -- restrictionMap(coeRingHom x) = coeRingHom(restrictionMapAlg x).
  -- Since coeRingHom is injective, the equality of restrictions implies
  -- restrictionMapAlg D₁ D₃ (g D₁) = restrictionMapAlg D₂ D₃ (g D₂).
  have hbij₃ := coeRingHom_bijective_of_discrete D₃
  -- The lifts from Away(D_i.s) to Away(D₃.s)
  have hunit_prod : IsUnit (algebraMap A (Localization.Away D₃.s) (D₁.1.s * D₂.1.s)) :=
    IsLocalization.Away.algebraMap_isUnit D₃.s
  rw [map_mul] at hunit_prod
  set ψ₁ : Localization.Away D₁.1.s →+* Localization.Away D₃.s :=
    IsLocalization.Away.lift D₁.1.s (isUnit_of_mul_isUnit_left hunit_prod)
  set ψ₂ : Localization.Away D₂.1.s →+* Localization.Away D₃.s :=
    IsLocalization.Away.lift D₂.1.s (isUnit_of_mul_isUnit_right hunit_prod)
  -- Key property: ψ_i ∘ algebraMap = algebraMap
  have hψ₁_alg : ∀ a : A, ψ₁ (algebraMap A _ a) = algebraMap A _ a := by
    intro a; exact IsLocalization.Away.lift_eq
      (x := D₁.1.s) (isUnit_of_mul_isUnit_left hunit_prod) a
  have hψ₂_alg : ∀ a : A, ψ₂ (algebraMap A _ a) = algebraMap A _ a := by
    intro a; exact IsLocalization.Away.lift_eq
      (x := D₂.1.s) (isUnit_of_mul_isUnit_right hunit_prod) a
  -- From hcompat₃ and bijectivity: ψ₁(g D₁) = ψ₂(g D₂) in Away(D₃.s).
  have hg_eq : ψ₁ (g D₁) = ψ₂ (g D₂) := by
    -- restrictionMap D_i D₃ h (f D_i) passes through coeRingHom and restrictionMapAlg.
    -- restrictionMapAlg D_i D₃ = IsLocalization.Away.lift D_i.s (isUnit_canonicalMap_s ...)
    -- But canonicalMap_s = coeRingHom ∘ algebraMap, and isUnit comes from the subset.
    -- We need to identify restrictionMapAlg D_i D₃ with the same map as ψ_i.
    -- Both are determined by their action on A (via algebraMap) and the unit condition.
    have hψ₁_eq : (restrictionMapAlg D₁.1 D₃ h₃₁ :
        Localization.Away D₁.1.s →+* presheafValue D₃) =
        D₃.coeRingHom.comp ψ₁ := by
      apply IsLocalization.ringHom_ext (Submonoid.powers D₁.1.s); ext a
      simp [restrictionMapAlg, RationalLocData.canonicalMap,
        RationalLocData.coeRingHom, hψ₁_alg]
    have hψ₂_eq : (restrictionMapAlg D₂.1 D₃ h₃₂ :
        Localization.Away D₂.1.s →+* presheafValue D₃) =
        D₃.coeRingHom.comp ψ₂ := by
      apply IsLocalization.ringHom_ext (Submonoid.powers D₂.1.s); ext a
      simp [restrictionMapAlg, RationalLocData.canonicalMap,
        RationalLocData.coeRingHom, hψ₂_alg]
    -- From hcompat₃: restrictionMap D₁ D₃ h₃₁ (f D₁) = restrictionMap D₂ D₃ h₃₂ (f D₂)
    -- f D_i = e(D_i)(g D_i) = D_i.coeRingHom(g D_i)
    -- restrictionMap(coeRingHom(g D_i)) = restrictionMapAlg(g D_i) (by restrictionMapHom_coe)
    have hLHS : restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
        restrictionMapAlg D₁.1 D₃ h₃₁ (g D₁) := by
      change restrictionMapHom D₁.1 D₃ h₃₁ (f D₁) = _
      have hf₁ : f D₁ = D₁.1.coeRingHom (g D₁) := hg D₁
      rw [hf₁]
      letI := D₁.1.uniformSpace; letI := D₁.1.isTopologicalRing
      letI := D₁.1.isUniformAddGroup
      letI := D₃.uniformSpace; letI := D₃.isTopologicalRing
      letI := D₃.isUniformAddGroup
      exact UniformSpace.Completion.extensionHom_coe
        (restrictionMapAlg D₁.1 D₃ h₃₁)
        (restrictionMapAlg_continuous D₁.1 D₃ h₃₁) (g D₁)
    have hRHS : restrictionMap D₂.1 D₃ h₃₂ (f D₂) =
        restrictionMapAlg D₂.1 D₃ h₃₂ (g D₂) := by
      change restrictionMapHom D₂.1 D₃ h₃₂ (f D₂) = _
      have hf₂ : f D₂ = D₂.1.coeRingHom (g D₂) := hg D₂
      rw [hf₂]
      letI := D₂.1.uniformSpace; letI := D₂.1.isTopologicalRing
      letI := D₂.1.isUniformAddGroup
      letI := D₃.uniformSpace; letI := D₃.isTopologicalRing
      letI := D₃.isUniformAddGroup
      exact UniformSpace.Completion.extensionHom_coe
        (restrictionMapAlg D₂.1 D₃ h₃₂)
        (restrictionMapAlg_continuous D₂.1 D₃ h₃₂) (g D₂)
    rw [hLHS, hRHS] at hcompat₃
    -- Now hcompat₃ : restrictionMapAlg D₁ D₃ (g D₁) = restrictionMapAlg D₂ D₃ (g D₂)
    -- Using hψ₁_eq, hψ₂_eq: D₃.coeRingHom(ψ₁(g D₁)) = D₃.coeRingHom(ψ₂(g D₂))
    rw [hψ₁_eq, hψ₂_eq] at hcompat₃
    simp only [RingHom.comp_apply] at hcompat₃
    exact hbij₃.1 hcompat₃
  -- From hr' and the lifts: ψ_i(algebraMap(r' D_i)) = algebraMap(r' D_i) in Away(D₃.s).
  -- And ψ_i(g D_i * algebraMap(D_i.s)^N₀) = ψ_i(g D_i) * algebraMap(D_i.s)^N₀.
  -- So algebraMap(r' D₁) = ψ₁(g D₁) * algebraMap(D₁.s)^N₀ in Away(D₃.s).
  have hcross : algebraMap A (Localization.Away D₃.s) (r' D₁ * D₂.1.s ^ N₀) =
      algebraMap A (Localization.Away D₃.s) (r' D₂ * D₁.1.s ^ N₀) := by
    have hr₁ : ψ₁ (g D₁) * (algebraMap A (Localization.Away D₃.s) D₁.1.s) ^ N₀ =
        algebraMap A _ (r' D₁) := by
      simpa only [map_mul, map_pow, hψ₁_alg] using congr_arg ψ₁ (hr' D₁)
    have hr₂ : ψ₂ (g D₂) * (algebraMap A (Localization.Away D₃.s) D₂.1.s) ^ N₀ =
        algebraMap A _ (r' D₂) := by
      simpa only [map_mul, map_pow, hψ₂_alg] using congr_arg ψ₂ (hr' D₂)
    -- Cross-multiply: both sides equal ψ₁(g D₁) * D₁.s^N₀ * D₂.s^N₀.
    simp only [map_mul, map_pow]
    calc algebraMap A _ (r' D₁) * algebraMap A _ D₂.1.s ^ N₀
        = ψ₁ (g D₁) * (algebraMap A _ D₁.1.s) ^ N₀ * (algebraMap A _ D₂.1.s) ^ N₀ := by
          rw [hr₁]
      _ = ψ₂ (g D₂) * (algebraMap A _ D₁.1.s) ^ N₀ * (algebraMap A _ D₂.1.s) ^ N₀ := by
          rw [hg_eq]
      _ = ψ₂ (g D₂) * (algebraMap A _ D₂.1.s) ^ N₀ * (algebraMap A _ D₁.1.s) ^ N₀ := by
          ring
      _ = algebraMap A _ (r' D₂) * (algebraMap A _ D₁.1.s) ^ N₀ := by
          rw [hr₂]
  -- Extract the power annihilation from the localization equality.
  -- In Away(D₁.s * D₂.s), equality means ∃ k, (D₁.s * D₂.s)^k * diff = 0.
  exact IsLocalization.Away.exists_of_eq (x := D₁.1.s * D₂.1.s) hcross

open Classical in
/-- **Partition-of-unity construction** for the discrete gluing core. Given lift maps
`φ D : Away C.base.s →+* Away D.s` over `algebraMap` (`hφ_alg`), uniform numerators `r''`
with `g D * algebraMap(D.s)^N = algebraMap(r'' D)` (`hr''`) that are pairwise compatible
(`hcompat_r''`), and the unit-ideal span (`hspan_top`), there is a single
`x' : Away C.base.s` with `φ D' x' = g D'` for every `D'`. Choose a partition
`∑ c_D * algebraMap(D.s)^N = 1` from `hspan_top`, set `x' = ∑ c_D * algebraMap(r'' D)`,
and verify `φ D'` after multiplying by the unit `algebraMap(D'.s)^N`, using `hcompat_r''`
to move the numerator past the sum. Extracted from the partition-of-unity tail of
`discrete_gluing`. -/
private theorem discrete_gluing_partition_of_unity {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    [IsHuberRing A] (C : RationalCoveringData A)
    (g : ∀ D : ↥C.covers, Localization.Away D.1.s)
    (φ : ∀ D : ↥C.covers, Localization.Away C.base.s →+* Localization.Away D.1.s)
    (hφ_alg : ∀ (D : ↥C.covers) (a : A),
        φ D (algebraMap A (Localization.Away C.base.s) a) = algebraMap A _ a)
    (N : ℕ) (r'' : ↥C.covers → A)
    (hr'' : ∀ D : ↥C.covers,
        g D * (algebraMap A (Localization.Away D.1.s) D.1.s) ^ N =
        algebraMap A _ (r'' D))
    (hcompat_r'' : ∀ (D₁ D₂ : ↥C.covers),
        algebraMap A (Localization.Away C.base.s) (r'' D₁ * D₂.1.s ^ N) =
        algebraMap A (Localization.Away C.base.s) (r'' D₂ * D₁.1.s ^ N))
    (hspan_top : Ideal.span (↑(C.covers.image
      (fun D ↦ algebraMap A (Localization.Away C.base.s) D.s)) :
      Set (Localization.Away C.base.s)) = ⊤) :
    ∃ x' : Localization.Away C.base.s, ∀ D' : ↥C.covers, φ D' x' = g D' := by
  classical
  -- Step 5: Partition of unity.
  have hspan_range : Ideal.span (Set.range
      (fun D : ↥C.covers ↦ (algebraMap A (Localization.Away C.base.s) D.1.s) ^ N)) = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_pow_eq_top _ hspan_top N]
    apply Ideal.span_mono
    intro x hx
    -- hx : x ∈ (fun x ↦ x ^ N) '' ↑(C.covers.image (fun D ↦ algebraMap A R D.s))
    obtain ⟨y, hy, rfl⟩ := hx
    have hmem := hy
    rw [Finset.mem_coe, Finset.mem_image] at hmem
    obtain ⟨D, hD, rfl⟩ := hmem
    exact ⟨⟨D, hD⟩, rfl⟩
  rw [Ideal.eq_top_iff_one] at hspan_range
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hspan_range
  -- hc : ∑ D, c D * (algebraMap A R D.1.s) ^ N = 1
  -- Step 6: Define x'.
  -- x' = ∑ D, c D * algebraMap A R (r'' D)
  refine ⟨∑ D : ↥C.covers, c D * algebraMap A (Localization.Away C.base.s) (r'' D),
    fun D' ↦ ?_⟩
  -- Step 7: Verify φ_{D'}(x') = g D'.
  -- φ_{D'}(x') * (algebraMap D'.s)^N = algebraMap(r'' D'), and
  -- g D' * (algebraMap D'.s)^N = algebraMap(r'' D'), so cancel the unit.
  -- (algebraMap D'.s)^N is a unit in Away D'.s
  have hunit_N : IsUnit ((algebraMap A (Localization.Away D'.1.s) D'.1.s) ^ N) :=
    IsUnit.pow N (IsLocalization.Away.algebraMap_isUnit D'.1.s)
  apply hunit_N.mul_left_cancel
  rw [mul_comm _ (g D'), hr'' D']
  -- Goal: (algebraMap D'.s)^N * φ(∑ c_D * algebraMap(r'' D)) = algebraMap(r'' D')
  -- φ distributes over the sum.
  simp only [map_sum, map_mul, hφ_alg]
  -- After map_sum, map_mul, hφ_alg, the goal is:
  -- (algebraMap D'.s)^N * ∑ D, φ D' (c D) * algebraMap A _ (r'' D) = algebraMap(r'' D')
  rw [Finset.mul_sum]
  -- Goal: ∑ D, (algebraMap D'.s)^N * (φ D' (c D) * algebraMap(r'' D)) = algebraMap(r'' D')
  -- Rewrite each summand using hcompat_r''.
  have key : ∀ D : ↥C.covers,
      (algebraMap A (Localization.Away D'.1.s) D'.1.s) ^ N *
      (φ D' (c D) * algebraMap A _ (r'' D)) =
      φ D' (c D) * (algebraMap A _ (r'' D') *
        (algebraMap A (Localization.Away D'.1.s) D.1.s) ^ N) := by
    intro D
    rw [← mul_assoc, mul_comm ((algebraMap A _ D'.1.s) ^ N) _, mul_assoc]
    congr 1
    -- Need: (algebraMap D'.s)^N * algebraMap(r'' D) = algebraMap(r'' D') * (algebraMap D.s)^N
    -- From hcompat_r'': algebraMap A R (r'' D * D'.s^N) = algebraMap A R (r'' D' * D.s^N)
    -- Apply φ D' to both sides, using hφ_alg.
    rw [mul_comm]
    -- Apply φ D' to hcompat_r'':
    -- algebraMap(r'' D) * algebraMap(D'.s)^N = algebraMap(r'' D') * algebraMap(D.s)^N
    simpa only [map_mul, map_pow, hφ_alg] using congr_arg (φ D') (hcompat_r'' D D')
  simp_rw [key]
  -- Goal: ∑ D, φ D' (c D) * (algebraMap(r'' D') * (algebraMap D.s)^N) = algebraMap(r'' D')
  simp_rw [mul_comm (algebraMap A _ (r'' D')) _, ← mul_assoc, ← Finset.sum_mul,
    mul_comm _ (algebraMap A _ (r'' D'))]
  -- Goal: (∑ D, φ D' (c D) * (algebraMap D.s)^N) * algebraMap(r'' D') = algebraMap(r'' D')
  suffices hone : (∑ D, φ D' (c D) *
      (algebraMap A (Localization.Away D'.1.s) D.1.s) ^ N) = 1 by
    rw [hone, mul_one]
  -- The sum equals φ D' (∑ D, c D * (algebraMap A R D.s)^N) = φ D' 1 = 1.
  have : ∀ D : ↥C.covers,
      φ D' (c D) * (algebraMap A (Localization.Away D'.1.s) D.1.s) ^ N =
      φ D' (c D * (algebraMap A (Localization.Away C.base.s) D.1.s) ^ N) := by
    intro D; rw [map_mul, map_pow, hφ_alg]
  simp_rw [this, ← map_sum, hc, map_one]

/-- **Discrete gluing lemma**: given compatible sections in presheafValues of cover
pieces, there exists a global section in the base presheafValue that restricts to
each given section.

For discrete rings, this is the algebraic sheaf condition: the Čech complex
`Away C.base.s → ∏ Away D.s ⇒ ∏ Away D₃.s` is exact at `∏ Away D.s`.

**Proof strategy:** Uses the identification `presheafValue D ≅ Away D.s` (discrete),
the covering-implies-unit-ideal condition, and a direct partition-of-unity construction
in the localization ring. -/
private theorem discrete_gluing {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [PlusSubring A] [DiscreteTopology A]
    [IsHuberRing A] (C : RationalCoveringData A)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D := by
  classical
  -- OVERVIEW: The proof separates into two layers:
  -- (A) Find x' : Away C.base.s mapping correctly under restrictionMapAlg
  -- (B) Transport x' to presheafValue via coeRingHom (verified by extensionHom_coe)
  --
  -- Layer (A) is the algebraic content: the Čech H^0 exactness for localizations.
  -- The covering condition gives that {D.s | D ∈ covers} generate the unit ideal
  -- in Away C.base.s. For compatible elements in the further localizations
  -- Away D.s, the standard partition-of-unity argument produces a preimage.
  --
  -- Layer (B) uses: restrictionMap(coeRingHom(x')) = restrictionMapAlg(x')
  -- (the extensionHom_coe property for completions).
  --
  -- ALGEBRAIC CORE: Find x' : Away C.base.s with restrictionMapAlg(x') = f D ∀ D.
  --
  -- Key mathematical facts (all provable from existing infrastructure):
  -- (i) restrictionMapAlg C.base D h = IsLocalization.Away.lift C.base.s (unit_of_s)
  -- (ii) Covering condition ↔ ∀ prime p of Away C.base.s, ∃ D with img(D.s) ∉ p
  -- (iii) Therefore {img(D.s)} generates ⊤ in Away C.base.s
  -- (iv) Partition of unity: ∑ c_D * img(D.s)^N = 1 for suitable N and coefficients
  -- (v) For each D: img(D.s)^N * f_D = img(a_D) in presheafValue D (comes from A)
  -- (vi) Compatible sections are determined by partition of unity:
  --      x' = ∑ c_D * algebraMap(a_D) in Away C.base.s
  -- (vii) Verification uses compatibility + the partition of unity identity.
  --
  -- The formalization of this standard commutative algebra requires:
  -- - Establishing IsLocalization.Away instances for further localizations
  -- - Connecting the covering condition to Ideal.span = ⊤
  -- - The Finset.sum-based construction and verification
  -- This is approximately 200-300 lines of Lean code.
  -- === DISCRETE GLUING (algebraic core) ===
  -- Strategy: Apply Localization.existsUnique_algebraMap_eq_of_span_eq_top
  -- to R = Away C.base.s with s = {algebraMap D.s | D ∈ covers}.
  --
  -- Step 1: Establish key instances
  have hbij : ∀ D : RationalLocData A, Function.Bijective D.coeRingHom :=
    fun D ↦ coeRingHom_bijective_of_discrete D
  have hs_unit : ∀ (D : RationalLocData A) (_ : D ∈ C.covers),
      IsUnit (algebraMap A (Localization.Away D.s) C.base.s) := by
    intro D hD
    have hu := isUnit_canonicalMap_s C.base D (C.hsubset D hD)
    change IsUnit (D.coeRingHom (algebraMap A _ C.base.s)) at hu
    exact (MulEquiv.isUnit_map (f := (RingEquiv.ofBijective D.coeRingHom
      (hbij D)).toMulEquiv) (x := algebraMap A _ C.base.s)).mp hu
  -- Step 2: Factor restrictionMapAlg = coeRingHom ∘ lift
  have lift_factor : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      restrictionMapAlg C.base D (C.hsubset D hD) =
      D.coeRingHom.comp (IsLocalization.Away.lift C.base.s (hs_unit D hD)) := by
    intro D hD
    apply IsLocalization.ringHom_ext (Submonoid.powers C.base.s)
    ext r
    simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
      RationalLocData.canonicalMap, RationalLocData.coeRingHom]
  -- Step 3: For each D, Away D.s is a localization of Away C.base.s at algebraMap D.s.
  -- Set up Algebra instances via the lift.
  -- Step 4: Show {algebraMap D.s | D ∈ covers} generates ⊤ in Away C.base.s.
  -- Uses: C.base.s ∈ radical(span {D.s}) in A ⟹ span = ⊤ in Away C.base.s.
  have hspan_top : Ideal.span (↑(C.covers.image
    (fun D ↦ algebraMap A (Localization.Away C.base.s) D.s)) :
    Set (Localization.Away C.base.s)) = ⊤ :=
    discrete_gluing_span_top C
  -- Step 5: Apply the gluing theorem.
  -- For each D ∈ covers, Away D.s = (Away C.base.s)[1/(algebraMap D.s)]
  -- by isLocAway_of_isUnit.
  -- The compatible sections f D : presheafValue D, transported through the
  -- coeRingHom bijection, give elements of Away D.s that are compatible
  -- under further localization.
  -- Localization.existsUnique_algebraMap_eq_of_span_eq_top gives x' : Away C.base.s.
  --
  -- The formal setup requires Localization.Away instances for the products
  -- (awayToAwayRight/Left compatibility) which involve substantial instance management.
  -- The mathematical content is complete (Steps 1-4 above + the Mathlib theorem).
  -- The remaining work is purely instance-management boilerplate.
  obtain ⟨x', hx'⟩ : ∃ x' : Localization.Away C.base.s,
      ∀ (D : ↥C.covers), restrictionMapAlg C.base D.1 (C.hsubset D.1 D.2) x' = f D := by
    -- For each D, define gD : Away D.s as the preimage of f D under coeRingHom (bijective)
    set e := fun D : RationalLocData A ↦ RingEquiv.ofBijective D.coeRingHom (hbij D)
    set g : ∀ D : ↥C.covers, Localization.Away D.1.s := fun D ↦ (e D.1).symm (f D)
    -- The goal reduces to: ∃ x', ∀ D, lift(x') = g D in Away D.s
    -- Apply the structure sheaf condition on Spec R (R = Away C.base.s).
    -- For each D ∈ covers, set s_D = algebraMap A R D.s.
    -- The canonical Localization.Away s_D (an R-localization) is isomorphic to
    -- Away D.s (an A-localization) via the lift. We transport g D to canonical
    -- localizations and apply Localization.existsUnique_algebraMap_eq_of_span_eq_top.
    set R := Localization.Away C.base.s
    set S : Set R := ↑(C.covers.image (fun D ↦ algebraMap A R D.s))
    -- For each D ∈ covers, equip Away D.s with R-algebra structure via the lift.
    -- The lift φ_D : R →+* Away D.s satisfies φ_D ∘ algebraMap A R = algebraMap A (Away D.s).
    -- Under this, Away D.s is IsLocalization.Away (algebraMap A R D.s) by isLocAway_of_isUnit.
    -- Use IsLocalization.algEquiv to get
    -- θ_D : Localization.Away (algebraMap A R D.s) ≃ₐ[R] Away D.s.
    -- Then g'_D := θ_D.symm (g D) : Localization.Away (algebraMap A R D.s) = Away s_D.
    --
    -- Define g' : Π (a : S), Away a.1 by choosing D with algebraMap D.s = a.
    -- For the Mathlib theorem, we need:
    -- (1) hspan_top gives Ideal.span S = ⊤
    -- (2) f = g' : Π (a : S), Away a.1
    -- (3) Compatibility: awayToAwayRight a.1 b (g' a) = awayToAwayLeft b.1 a (g' b)
    --
    -- For (3), the compatibility in Away(a*b) follows from hcompat transported
    -- through the various isomorphisms.
    --
    -- This is feasible but requires ~100 lines of instance boilerplate.
    -- Instead, we use a more direct approach: replicate the core of the
    -- Mathlib proof using our lift maps φ_D directly, avoiding canonical
    -- localizations and algEquiv entirely.
    --
    -- CORE PROOF (adapted from Localization.existsUnique_algebraMap_eq_of_span_eq_top):
    -- Let φ_D := IsLocalization.Away.lift C.base.s (hs_unit D hD) : R →+* Away D.s.
    -- Step 1: Write g D as a fraction: g D * (algebraMap D.s)^n_D = algebraMap(r_D) in Away D.s.
    -- Equivalently: g D = algebraMap(r_D) * (algebraMap D.s)^(-n_D) in Away D.s.
    -- Step 2: Uniform exponent N, adjusted numerators r'_D = D.s^(N - n_D) * r_D.
    -- Step 3: Show numerator compatibility: r'_{D₁} * D₂.s^N = r'_{D₂} * D₁.s^N in A
    --         (up to powers of D₁.s * D₂.s). This uses hcompat.
    -- Step 4: Absorb the annihilator into the exponent (increase N).
    -- Step 5: Partition of unity: ∑ c_D * (algebraMap D.s)^N = 1 in R.
    -- Step 6: x' = ∑ c_D * algebraMap(r'_D) : R.
    -- Step 7: Verify φ_D(x') = g D using the partition and numerator relation.
    --
    -- This is essentially the Mathlib proof but using φ_D instead of algebraMap R →+*.
    -- The key difference: φ_D is NOT an algebraMap in general, so we can't use
    -- the Mathlib theorem directly. But the proof structure is the same.
    --
    -- Let's implement this.
    -- φ_D := the lift from R to Away D.s
    set φ : ∀ D : ↥C.covers, R →+* Localization.Away D.1.s :=
      fun D ↦ IsLocalization.Away.lift C.base.s (hs_unit D.1 D.2)
    -- Property: φ_D ∘ algebraMap = algebraMap
    have hφ_alg : ∀ (D : ↥C.covers) (a : A),
        φ D (algebraMap A R a) = algebraMap A _ a := by
      intro D a
      exact IsLocalization.Away.lift_eq (x := C.base.s) (hs_unit D.1 D.2) a
    -- φ_D maps algebraMap(D.s) ∈ R to algebraMap(D.s) ∈ Away D.s, which is a unit.
    have hφ_unit : ∀ D : ↥C.covers,
        IsUnit (φ D (algebraMap A R D.1.s)) := by
      intro D; rw [hφ_alg]; exact IsLocalization.Away.algebraMap_isUnit D.1.s
    -- Step 1: Fractions.
    choose nD rD hrD using fun D : ↥C.covers ↦
      IsLocalization.Away.surj D.1.s (g D)
    -- hrD D : g D * (algebraMap D.s)^(nD D) = algebraMap(rD D) in Away D.s.
    -- Step 2: Uniform exponent.
    set N₀ := C.covers.attach.sup nD with hN₀_def
    -- Adjusted numerators.
    set r' : ∀ D : ↥C.covers, A := fun D ↦ D.1.s ^ (N₀ - nD D) * rD D
    have hr' : ∀ D : ↥C.covers,
        g D * (algebraMap A (Localization.Away D.1.s) D.1.s) ^ N₀ =
        algebraMap A _ (r' D) := by
      intro D
      have hle : nD D ≤ N₀ := Finset.le_sup (f := nD) (Finset.mem_attach C.covers D)
      simp only [r', map_mul, map_pow]
      rw [← hrD D, mul_left_comm, ← pow_add, Nat.sub_add_cancel hle]
    -- Step 3: Numerator compatibility (up to powers, then absorbed).
    -- For each pair (D₁, D₂), construct a common refinement D₃ with s₃ = D₁.s * D₂.s.
    -- Use hcompat to show g D₁ and g D₂ agree when lifted to Away(D₃.s).
    -- Cross-multiplying with hr' gives equality up to a power of D₁.s * D₂.s.
    -- Then absorb the power into the numerators (following the Mathlib proof pattern).
    --
    -- Step 3a: Compatibility in Away(D₁.s * D₂.s) for each pair.
    have hcompat_pow : ∀ (D₁ D₂ : ↥C.covers), ∃ k : ℕ,
        (D₁.1.s * D₂.1.s) ^ k * (r' D₁ * D₂.1.s ^ N₀) =
        (D₁.1.s * D₂.1.s) ^ k * (r' D₂ * D₁.1.s ^ N₀) :=
      discrete_gluing_numerator_compat C f hcompat g
        (fun D ↦ ((e D.1).apply_symm_apply (f D)).symm) N₀ r' hr'
    -- Step 3b: Uniform power K and absorption.
    -- Take K as the sup over all pairs.
    choose kD hkD using fun (p : ↥C.covers × ↥C.covers) ↦ hcompat_pow p.1 p.2
    set K := (C.covers.attach ×ˢ C.covers.attach).sup kD with hK_def
    -- Absorption: define r'' D = D.s^K * r' D and N = N₀ + K.
    set N := N₀ + K
    set r'' : ∀ D : ↥C.covers, A := fun D ↦ D.1.s ^ K * r' D
    have hr'' : ∀ D : ↥C.covers,
        g D * (algebraMap A (Localization.Away D.1.s) D.1.s) ^ N =
        algebraMap A _ (r'' D) := by
      intro D; simp only [r'', map_mul, map_pow]
      -- Goal: g D * algebraMap(D.s)^N = algebraMap(D.s)^K * algebraMap(r' D)
      -- where N = N₀ + K and algebraMap(r' D) = g D * algebraMap(D.s)^N₀ (by hr').
      rw [show N = K + N₀ from by omega, pow_add, ← mul_assoc,
        mul_comm (g D) _, mul_assoc, ← hr' D, mul_comm]
    -- Numerator compatibility: exact equality in A after absorption.
    have hcompat_r'' : ∀ (D₁ D₂ : ↥C.covers),
        algebraMap A R (r'' D₁ * D₂.1.s ^ N) =
        algebraMap A R (r'' D₂ * D₁.1.s ^ N) := by
      intro D₁ D₂
      -- It suffices to show exact equality in A.
      congr 1
      -- r'' D₁ * D₂.s^N = D₁.s^K * r' D₁ * D₂.s^(N₀+K)
      --   = D₁.s^K * D₂.s^K * (r' D₁ * D₂.s^N₀)
      -- r'' D₂ * D₁.s^N = D₂.s^K * r' D₂ * D₁.s^(N₀+K)
      --   = D₁.s^K * D₂.s^K * (r' D₂ * D₁.s^N₀)
      -- So it suffices to show (D₁.s * D₂.s)^K * (r' D₁ * D₂.s^N₀ - r' D₂ * D₁.s^N₀) = 0,
      -- i.e., (D₁.s * D₂.s)^K * diff = 0.
      -- From hkD at the pair (D₁, D₂): (D₁.s * D₂.s)^(kD(D₁,D₂)) * diff = 0.
      -- Since K ≥ kD(D₁,D₂), (D₁.s * D₂.s)^K * diff = 0 too.
      have hle : kD (D₁, D₂) ≤ K :=
        Finset.le_sup (f := kD) (Finset.mem_product.mpr
          ⟨Finset.mem_attach _ D₁, Finset.mem_attach _ D₂⟩)
      have hann := hkD (D₁, D₂)
      -- Boost to uniform power K:
      -- (D₁.s * D₂.s)^K * LHS = (D₁.s * D₂.s)^K * RHS.
      have hann_K : (D₁.1.s * D₂.1.s) ^ K * (r' D₁ * D₂.1.s ^ N₀) =
          (D₁.1.s * D₂.1.s) ^ K * (r' D₂ * D₁.1.s ^ N₀) := by
        have hsub : K - kD (D₁, D₂) + kD (D₁, D₂) = K := Nat.sub_add_cancel hle
        calc (D₁.1.s * D₂.1.s) ^ K * (r' D₁ * D₂.1.s ^ N₀)
            = (D₁.1.s * D₂.1.s) ^ (K - kD (D₁, D₂) + kD (D₁, D₂)) *
              (r' D₁ * D₂.1.s ^ N₀) := by rw [hsub]
          _ = (D₁.1.s * D₂.1.s) ^ (K - kD (D₁, D₂)) *
              ((D₁.1.s * D₂.1.s) ^ kD (D₁, D₂) * (r' D₁ * D₂.1.s ^ N₀)) := by
                rw [pow_add]; ring
          _ = (D₁.1.s * D₂.1.s) ^ (K - kD (D₁, D₂)) *
              ((D₁.1.s * D₂.1.s) ^ kD (D₁, D₂) * (r' D₂ * D₁.1.s ^ N₀)) := by
                rw [hann]
          _ = (D₁.1.s * D₂.1.s) ^ (K - kD (D₁, D₂) + kD (D₁, D₂)) *
              (r' D₂ * D₁.1.s ^ N₀) := by rw [pow_add]; ring
          _ = (D₁.1.s * D₂.1.s) ^ K * (r' D₂ * D₁.1.s ^ N₀) := by rw [hsub]
      -- r'' Di * Dj.s^N = Di.s^K * r' Di * Dj.s^(N₀+K).
      -- After expanding, both sides match (D₁.s*D₂.s)^K * (r' Di * Dj.s^N₀).
      rw [mul_pow] at hann_K
      -- hann_K : D₁.s^K * D₂.s^K * (r' D₁ * D₂.s^N₀) = D₁.s^K * D₂.s^K * (r' D₂ * D₁.s^N₀)
      -- Goal: D₁.s^K * r' D₁ * D₂.s^(N₀+K) = D₂.s^K * r' D₂ * D₁.s^(N₀+K)
      change D₁.1.s ^ K * r' D₁ * D₂.1.s ^ (N₀ + K) =
        D₂.1.s ^ K * r' D₂ * D₁.1.s ^ (N₀ + K)
      have hexpand₁ : D₁.1.s ^ K * r' D₁ * D₂.1.s ^ (N₀ + K) =
          D₁.1.s ^ K * D₂.1.s ^ K * (r' D₁ * D₂.1.s ^ N₀) := by ring
      have hexpand₂ : D₂.1.s ^ K * r' D₂ * D₁.1.s ^ (N₀ + K) =
          D₁.1.s ^ K * D₂.1.s ^ K * (r' D₂ * D₁.1.s ^ N₀) := by ring
      rw [hexpand₁, hexpand₂, hann_K]
    -- Step 5: Partition of unity (extracted to discrete_gluing_partition_of_unity):
    -- a single x'' : R with φ D' x'' = g D' for every D'.
    obtain ⟨x'', hx''⟩ : ∃ x' : Localization.Away C.base.s,
        ∀ D' : ↥C.covers, φ D' x' = g D' :=
      discrete_gluing_partition_of_unity C g φ hφ_alg N r'' hr'' hcompat_r'' hspan_top
    -- Reduce: restrictionMapAlg = coeRingHom ∘ lift, so goal ↔ lift x'' = g D';
    -- and f D' = coeRingHom (g D').
    refine ⟨x'', fun D' ↦ ?_⟩
    rw [lift_factor D'.1 D'.2, RingHom.comp_apply, hx'' D']
    exact (e D'.1).apply_symm_apply (f D')
  -- Layer (B): Transport back via coeRingHom.
  -- restrictionMap base D h (coeRingHom x') = extensionHom(restrictionMapAlg)(coeRingHom x')
  --   = restrictionMapAlg x'   (by extensionHom_coe)
  --   = f D                     (by hx')
  refine ⟨C.base.coeRingHom x', fun D ↦ ?_⟩
  change restrictionMapHom C.base D.1 (C.hsubset D.1 D.2) (C.base.coeRingHom x') = f D
  letI := C.base.uniformSpace
  letI := C.base.isTopologicalRing
  letI := C.base.isUniformAddGroup
  letI := D.1.uniformSpace
  letI := D.1.isTopologicalRing
  letI := D.1.isUniformAddGroup
  erw [UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg C.base D.1 (C.hsubset D.1 D.2))
    (restrictionMapAlg_continuous C.base D.1 (C.hsubset D.1 D.2)) x']
  exact hx' D

/-- **Theorem 8.28(b)** of Wedhorn (discrete case): discrete Huber rings are sheafy.

For the embedding condition, the localization topology is `⊥` (discrete) for discrete
base rings, so `presheafValue D` is also discrete. The product restriction is injective
by `productRestriction_injective_discrete`, and an injective map between discrete spaces
is an embedding.

The gluing condition (existence of a global section from compatible local data) requires
the Čech complex exactness for rational coverings. -/
instance IsSheafy.ofStronglyNoetherianTate_discrete
    (A : Type*) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    [PlusSubring A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] :
    IsSheafy A where
  embedding C _hC := by
    -- For the discrete case both source and target are discrete: `presheafValue`
    -- of a discrete ring is discrete (`discreteTopology_presheafValue`), and a
    -- finite Pi of discretes is discrete (`Pi.discreteTopology`). With both
    -- topologies `= ⊥` and `productRestrictionSub` injective (via
    -- `productRestriction_injective_discrete`), the embedding follows: every
    -- subset of the source is the preimage of its image under an injective map
    -- into a discrete target.
    haveI := discreteTopology_presheafValue (A := A) C.base
    haveI : ∀ D : ↑C.covers, DiscreteTopology (presheafValue D.1) :=
      fun _ => discreteTopology_presheafValue _
    haveI : DiscreteTopology (∀ D : ↑C.covers, presheafValue D.1) := Pi.discreteTopology
    have hinj : Function.Injective (productRestrictionSub A C) := by
      intro x y hxy
      exact productRestriction_injective_discrete C
        (funext fun ⟨D, hD⟩ => congr_fun hxy ⟨D, hD⟩)
    refine ⟨⟨?_⟩, hinj⟩
    rw [show (instTopologicalSpacePresheafValue C.base : TopologicalSpace _) = ⊥ from
      DiscreteTopology.eq_bot]
    refine (TopologicalSpace.ext_iff ..).mpr ?_
    intro s
    refine ⟨fun _ => ⟨productRestrictionSub A C '' s, isOpen_discrete _, ?_⟩, fun _ => trivial⟩
    ext x
    exact ⟨fun ⟨y, hy, hyx⟩ => hinj hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  gluing C _hC f hcompat := discrete_gluing C f hcompat

/-! ### General case: specification of remaining work

The general (non-discrete) proof of Theorem 8.28(b) requires assembling the
algebraic foundations with three additional components:

**Component A (Topological identification):** Show that for a Tate ring `A`
with pair of definition `(A₀, I)`, the presheaf value `presheafValue D` is
isomorphic (as a topological ring) to the completion of `Localization.Away D.s`
with respect to the `I`-adic topology. This requires:
- Defining the correct T-topology on `A⟨X⟩` (I-adic, not restricted product)
- Proving that `A⟨X⟩/(1-sX)` with the quotient topology equals the adic completion
- Building the chain: presheafValue D ← completion ← A⟨X⟩/(1-sX) quotient

**Component B (Categorical wrapping):** Connect the `RationalCoveringData` / `presheafValue`
framework (from `Presheaf.lean`) to the `FiniteCover` / `AbPresheaf` / `IsSeparating`
framework (from `CechCohomology.lean`). This requires:
- Constructing `FiniteCover (Spa A A⁺) ι` from `RationalCoveringData A`
- Wrapping `presheafValue` into an `AbPresheaf (Spa A A⁺)`
- Showing `IsSeparating F U` (Čech separation) ↔ `Function.Injective (productRestriction)`

**Component C (Laurent-to-standard refinement):** Prove that every standard rational
covering is refined by a product of 2-element Laurent covers. This requires:
- Lemma 7.54: decomposition of rational subsets into basic pieces
- For basic `R(tᵢ/s)`: showing it equals `R(tᵢ/1) ∩ R(1/s)` (set-theoretic intersection)
- Constructing the refinement map from the product cover to the standard cover

Once Components A, B, C are in place, the proof assembles as:
```
                    ┌─────────────────────────────────────────┐
                    │ Each Laurent cover has separation       │ Step 1 (DONE)
                    │ (epsilon-injectivity, Lemma 8.33)       │
                    └───────────────┬─────────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────────┐
                    │ Product of Laurent covers has            │ Component C
                    │ separation (faithful flatness, Cor 8.32) │
                    └───────────────┬─────────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────────┐
                    │ Standard rational cover has separation   │ Step 3 (DONE)
                    │ (refinement transfer, Prop A.3)          │
                    └───────────────┬─────────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────────┐
                    │ Every rational cover has separation      │ Component B
                    │ (Lemma 7.54 + refinement)                │
                    └───────────────┬─────────────────────────┘
                                    │
                    ┌───────────────▼─────────────────────────┐
                    │ IsSheafy A                               │ Step 5 (DONE)
                    │ (Definition 8.26)                        │
                    └─────────────────────────────────────────┘
```
-/

/-! ### Summary of sorry-free results

The following theorems are proved without sorry and constitute the algebraic
foundation for Theorem 8.28(b):

1. **Laurent cover exact sequence (discrete)**:
   `LaurentCover.laurentCover_exact` — full 4-term exactness

2. **Laurent cover epsilon-injectivity (general)**:
   `LaurentCover.epsilonHom_gen_injective` — via Krull intersection theorem
   `LaurentCover.epsilonHom_injective` — via quotient equivalence (discrete)

3. **Row 2 exactness**:
   `LaurentCover.row2_exact_at_middle` — ker(λ) = im(ι) for T1 rings

4. **Tate algebra flatness (discrete)**:
   `TateAlgebra.flat_quotient_fSubX` — A⟨X⟩/(f-X) flat over A
   `TateAlgebra.flat_quotient_oneSubfX` — A⟨X⟩/(1-fX) flat over A

5. **Refinement transfers separation**:
   `Refinement.separation_of_finer` — abstract Čech result
   `Refinement.cochainMap_comp_aug` — augmentation commutes with refinement

6. **Presheaf flatness (discrete)**:
   `canonicalMap_flat_discrete` — presheaf value flat over A
   `localization_flat_over` — localization flat over A

7. **Discrete sheaf condition**:
   `IsSheafy.discrete` — direct proof in `Presheaf.lean`/`StructureSheaf.lean`
   `IsSheafy.ofStronglyNoetherianTate_discrete` — instance form
-/
