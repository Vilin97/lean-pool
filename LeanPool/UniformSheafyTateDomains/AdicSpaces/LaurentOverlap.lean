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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinement

/-!
# Wedhorn Example 6.39: bivariate Laurent-overlap identification

This module introduces the **bivariate Laurent analog of Example 6.38** (Wedhorn
*Adic Spaces*, Example 6.39 / §8.33), giving a concrete algebraic description of
the presheaf value on the overlap `R(f/1) ∩ R(1/f)` of a two-element Laurent
cover.

For a complete strongly noetherian Tate base `B` and a power-bounded `b : B`:

```
presheafValue (overlapDatum B P b) ≃+* LaurentCover.B₁₂_gen b
```

where `overlapDatum B P b := laurentMinusDatum (trivialPlusDatum B P b) b` is
the iterated rational datum cutting out `{v ∈ Spa B : v(b) = 1}` and
`B₁₂_gen b = B⟨ζ, ζ⁻¹⟩ / (b - ζ)` is the quotient of the bilateral Laurent
Tate algebra by `b - ζ`.

## Proof strategy (Wedhorn Lemma 8.33 / Example 6.38+6.39 direct route)

Following Wedhorn p.83 (proof of Lemma 8.33), the identification
`A⟨ζ, η⟩/(f - ζ, 1 - fη) = A⟨ζ, ζ⁻¹⟩/(f - ζ)` decomposes as:

**Step A** — apply the **bivariate Example 6.38** (Wedhorn p.55, bivariate
case with `T₁ = {b}/1, T₂ = {1}/b` giving the overlap):
```
presheafValue (overlapDatum B P b) ≃+* TateAlgebra₂ B / (b - X, 1 - b·Y)
```

**Step B** — **pure algebra** (no topology): show
```
TateAlgebra₂ B / Ideal.span {b - X, 1 - b·Y}  ≃+*  B₁₂_gen b
```
via the ideal equality `Ideal.span{b - X, 1 - b·Y} = Ideal.span{b - X, X·Y - 1}`
(Wedhorn's "`1 - fη ≡ 1 - ζη` mod `(f - ζ)`") followed by the third iso
theorem applied to `LaurentTateAlgebra B = TateAlgebra₂ B / (XY - 1)`.

Step B is **implemented** in this file as `bivariateOverlap_equiv_B₁₂gen`.
Step A is the substantial residual piece and requires the
bivariate analog of `example638Plus_equiv` / `example638Minus_equiv`
(not yet in the project infrastructure).

## Status

* `overlapDatum B P b` — defined.
* `overlapDatum_s`, `overlapDatum_P`, `overlapDatum_subset_plus` — proved.
* `bivariateOverlap_ideal_eq` (Wedhorn ideal equality) — proved.
* `bivariateOverlap_equiv_B₁₂gen` (Step B) — proved, 0 sorry, axiom-clean.
* `bivariateOverlap_equiv_B₁₂gen_mk` / `_algebraMap` / `_X` / `_Y` —
  forward action lemmas for Step B (`rfl`-level); ready for consumer use.
* `bivariateOverlap_equiv_B₁₂gen_symm_mk` / `_symm_algebraMap` / `_symm_zeta`
  / `_symm_zetaInv` — symm-direction action lemmas (via `symm_apply_apply`),
  enabling backward composition checks.
* **Step A foundational lemmas** (power-boundedness in the overlap completion):
  `one_mem_overlapDatum_T`, `b_sq_mem_overlapDatum_T`,
  `canonicalMap_b_isPowerBounded_in_overlap`, `invS_isPowerBounded_in_overlap`,
  `canonicalMap_b_mul_invS_in_overlap`. Together: `canonicalMap b` is a unit
  in `presheafValue(overlap)` with both it and its inverse power-bounded —
  the Wedhorn Example 6.39 universal-property input.
* **Step A half-forward homs** (plus/minus univariate evalHoms into overlap):
  `overlap_plus_evalHom`, `overlap_minus_evalHom` with generator actions
  (`_algebraMap`, `_X`) and kernel lemmas (`_fSubX_eq_zero`,
  `_oneSubfX_eq_zero`). Factored through the appropriate ideals:
  `overlap_plus_forwardHom : B₁_gen b →+* presheafValue(overlap)`,
  `overlap_minus_forwardHom : B₂_gen b →+* presheafValue(overlap)`.
* `example638Bivariate_equiv` (full T-OV-1) — **LANDED 2026-05-13 audit**.
  Implemented at line 1472, hypothesis-parameterised on three named bridges:
  `hA_complete`, `hnoeth` (Noetherianness of `TateAlgebra.pairSubring₂`),
  `hcont_forward`. All three discharged unconditionally from ambient
  typeclass hypotheses in the consumer wrapper `laneA_τ_preBiv` in
  `LaneAReverseRoundTrip.lean`, which is the unconditional consumer-facing
  form of the bivariate Example 6.38 iso. `#print axioms` clean
  (`[propext, Classical.choice, Quot.sound]`) for `example638Bivariate_equiv`,
  `example638Bivariate_backwardHom`, the two round-trip lemmas, and
  `laneA_τ_preBiv` (the wrapper).

  The forward continuity `hcont_forward` is discharged unconditionally by
  `example638Bivariate_forwardHom_continuous_canonical` in
  `BivariateContinuity.lean` (also axiom-clean).

  Per the round-4 reviewer's direct guidance (ChatGPT Pro, 2026-05-13),
  this is the project's CRITICAL-PATH BLOCKER and it is now landed. The
  remaining T-IDEAL-2 statement audit + Lane C refinement induction are
  separate downstream concerns.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Example 6.38, 6.39, Lemma 8.33.
-/

@[expose] public section

namespace ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

section BivariateOverlap

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]

/-- **The bivariate Laurent-overlap rational datum** at `b ∈ B`:
`overlapDatum B P b := laurentMinusDatum (trivialPlusDatum B P b) b`.

Its data unfolds to:
* `P = P` (same pair of definition)
* `T = (insert 1 {b}).product ({1, b}) |>.image (·.1 * ·.2) = {1, b, b²}`
* `s = 1 * b = b`

The rational open it carves out in `Spa B` is `{v : v(b) = 1}`, i.e., the
locus where `b` is a "unit" at the valuation-theoretic level — this is the
overlap `R(b/1) ∩ R(1/b)` of the two-element Laurent cover at `b`. -/
noncomputable def overlapDatum (P : PairOfDefinition B) (b : B) :
    RationalLocData B :=
  laurentMinusDatum (trivialPlusDatum B P b) b

/-- The `s` of `overlapDatum B P b` is `b` (unfolding `laurentMinusDatum` then
`trivialPlusDatum`: `s = 1 * b = b`). -/
@[simp]
theorem overlapDatum_s (P : PairOfDefinition B) (b : B) :
    (overlapDatum B P b).s = b := by
  change (1 : B) * b = b
  exact one_mul b

/-- The pair of definition of `overlapDatum B P b` is `P` (inherited through
both `laurentMinusDatum` and `trivialPlusDatum`, neither of which modifies `P`). -/
@[simp]
theorem overlapDatum_P (P : PairOfDefinition B) (b : B) :
    (overlapDatum B P b).P = P := rfl

/-- The rational open of `overlapDatum B P b` is contained in the plus half
(the plus datum at `b` being `trivialPlusDatum B P b`). Immediate from
`laurentMinus_subset`. -/
theorem overlapDatum_subset_plus (P : PairOfDefinition B) (b : B) :
    rationalOpen (overlapDatum B P b).T (overlapDatum B P b).s ⊆
      rationalOpen (trivialPlusDatum B P b).T (trivialPlusDatum B P b).s :=
  laurentMinus_subset (trivialPlusDatum B P b) b

/-- `1 ∈ (overlapDatum B P b).T`. Witnessed by the pair `(1, 1)`: both entries
are in the factors `insert 1 {b}` and `{1, b}` respectively, and `1 · 1 = 1`.

Used to invoke `invS_isPowerBounded_of_one_mem_T` on the overlap. -/
theorem one_mem_overlapDatum_T (P : PairOfDefinition B) (b : B) :
    (1 : B) ∈ (overlapDatum B P b).T := by
  classical
  change (1 : B) ∈ Finset.image (fun p : B × B ↦ p.1 * p.2)
      (Finset.product (insert (1 : B) {b}) ({1, b} : Finset B))
  refine Finset.mem_image.mpr ⟨(1, 1), ?_, one_mul 1⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩

/-- `b · b ∈ (overlapDatum B P b).T`. Witnessed by the pair `(b, b)`: both
entries are in the factors, and `b · b = b²`.

Used to show `algebraMap b = divByS (b·b) b` lies in `locSubring` of the overlap
(since `b·b = b² ∈ T`), yielding power-boundedness of `canonicalMap b` in
`presheafValue (overlapDatum B P b)`. -/
theorem b_sq_mem_overlapDatum_T (P : PairOfDefinition B) (b : B) :
    b * b ∈ (overlapDatum B P b).T := by
  classical
  change b * b ∈ Finset.image (fun p : B × B ↦ p.1 * p.2)
      (Finset.product (insert (1 : B) {b}) ({1, b} : Finset B))
  refine Finset.mem_image.mpr ⟨(b, b), ?_, rfl⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self b),
     Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩


section BivariateOverlapPowerBounded

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

/-- **`canonicalMap b` is power-bounded in `presheafValue (overlapDatum B P b)`**.

Proof: in `Localization.Away b`, `algebraMap b = divByS (b·b) b` (both represent
`b` as a fraction). Since `b·b ∈ (overlapDatum).T`, `divByS (b·b) b ∈ locSubring`.
Then `canonicalMap b = coeRingHom(algebraMap b) = coeRingHom(divByS (b·b) b)` is
in `coeRingHom '' locSubring`, which is bounded. Closed under powers by the
subring property. -/
theorem canonicalMap_b_isPowerBounded_in_overlap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    TopologicalRing.IsPowerBounded ((overlapDatum B P b).canonicalMap b) := by
  set D := overlapDatum B P b
  have hs_eq : D.s = b := overlapDatum_s B P b
  have hcm : D.canonicalMap b =
      D.coeRingHom (algebraMap B (Localization.Away D.s) b) := rfl
  rw [hcm]
  have halg_eq : algebraMap B (Localization.Away D.s) b = divByS (b * b) D.s := by
    unfold divByS
    rw [← IsLocalization.mk'_one (M := Submonoid.powers D.s)
          (S := Localization.Away D.s) b]
    apply IsLocalization.mk'_eq_of_eq
    simp only [Submonoid.coe_one, one_mul]
    rw [hs_eq]
  rw [halg_eq]
  have hmem : divByS (b * b) D.s ∈ locSubring D.P D.T D.s := by
    apply divByS_mem_locSubring D.P D.T D.s
    rw [hs_eq] at *
    exact b_sq_mem_overlapDatum_T B P b
  have hpow : ∀ n : ℕ, (divByS (b * b) D.s) ^ n ∈ locSubring D.P D.T D.s :=
    fun n ↦ (locSubring D.P D.T D.s).pow_mem hmem n
  have hrange : Set.range
      ((D.coeRingHom (divByS (b * b) D.s)) ^ · : ℕ → presheafValue D) ⊆
      D.coeRingHom '' (locSubring D.P D.T D.s : Set (Localization.Away D.s)) := by
    rintro _ ⟨n, rfl⟩
    change (D.coeRingHom (divByS (b * b) D.s)) ^ n ∈ _
    rw [← map_pow]
    exact ⟨(divByS (b * b) D.s) ^ n, hpow n, rfl⟩
  exact (CompletionLocalization.coeRingHom_image_locSubring_isBounded D).subset hrange

/-- **`invS` is power-bounded in `presheafValue (overlapDatum B P b)`**.

Consequence of `invS_isPowerBounded_of_one_mem_T` using `one_mem_overlapDatum_T`,
after rewriting `invS D = D.coeRingHom (divByS 1 D.s)` via
`invS_eq_coeRingHom_divByS_one`. -/
theorem invS_isPowerBounded_in_overlap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    TopologicalRing.IsPowerBounded (invS (overlapDatum B P b)) := by
  rw [invS_eq_coeRingHom_divByS_one]
  exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
    (overlapDatum B P b) (one_mem_overlapDatum_T B P b)

/-- **`canonicalMap b · invS = 1`** in `presheafValue (overlapDatum B P b)`.

This is the key property that makes `canonicalMap b` a *unit* in the overlap
completion, with `invS` as its inverse. Both factors are power-bounded by the
two preceding lemmas, which is exactly Wedhorn's "`b` and `b⁻¹` both
power-bounded" setup in Example 6.39.

Since `(overlapDatum).s = b`, this follows from `canonicalMap_s_mul_invS`. -/
theorem canonicalMap_b_mul_invS_in_overlap
    (P : PairOfDefinition B) (b : B) :
    (overlapDatum B P b).canonicalMap b * invS (overlapDatum B P b) = 1 := by
  have hs_eq : (overlapDatum B P b).s = b := overlapDatum_s B P b
  have := canonicalMap_s_mul_invS (overlapDatum B P b)
  rw [hs_eq] at this
  exact this

/-! ### Step A forward building blocks: univariate evalHoms into overlap

The two univariate evaluation homs into `presheafValue (overlapDatum B P b)`:
one sends `TateAlgebra.X ↦ canonicalMap b` (the plus half), the other sends
`TateAlgebra.X ↦ invS = (canonicalMap b)⁻¹` (the minus half). Each factors
through the appropriate quotient ideal (`plusFSubXIdeal b` / `oneSubfXIdeal b`),
yielding ring homs `B₁_gen b →+* presheafValue(overlap)` and
`B₂_gen b →+* presheafValue(overlap)`. These are the two "half" components
of the full bivariate forward direction. -/

/-- **Plus-half evalHom into overlap**: `TateAlgebra B →+* presheafValue (overlap)`
sending `X ↦ canonicalMap b`, via `evalHomBounded`. -/
noncomputable def overlap_plus_evalHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra B) →+* presheafValue (overlapDatum B P b) :=
  TateAlgebraWedhorn.evalHomBounded
    (overlapDatum B P b).canonicalMap
    (canonicalMap_continuous (overlapDatum B P b))
    ((overlapDatum B P b).canonicalMap b)
    (canonicalMap_b_isPowerBounded_in_overlap B P b)

/-- **Minus-half evalHom into overlap**: `TateAlgebra B →+* presheafValue (overlap)`
sending `X ↦ invS` (the inverse of `canonicalMap b` in the overlap completion),
via `evalHomBounded`. -/
noncomputable def overlap_minus_evalHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra B) →+* presheafValue (overlapDatum B P b) :=
  TateAlgebraWedhorn.evalHomBounded
    (overlapDatum B P b).canonicalMap
    (canonicalMap_continuous (overlapDatum B P b))
    (invS (overlapDatum B P b))
    (invS_isPowerBounded_in_overlap B P b)

/-- `overlap_plus_evalHom` sends `algebraMap a` to `canonicalMap a`. -/
theorem overlap_plus_evalHom_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b a : B) :
    overlap_plus_evalHom B P b (algebraMap B _ a) =
      (overlapDatum B P b).canonicalMap a := by
  unfold overlap_plus_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 0]
  · unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    simp only [Finsupp.single_zero, pow_zero, mul_one]
    congr 1
  · intro n hn
    unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    have : (MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (↑(algebraMap B ↥(TateAlgebra B) a) : MvPowerSeries (Fin 1) B) = 0 := by
      change (MvPowerSeries.coeff (Finsupp.single 0 n))
        (MvPowerSeries.C (σ := Fin 1) a) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg (Finsupp.single_ne_zero.mpr hn)]
    simp [this]

/-- `overlap_plus_evalHom` sends `X` to `canonicalMap b`. -/
theorem overlap_plus_evalHom_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    overlap_plus_evalHom B P b TateAlgebra.X =
      (overlapDatum B P b).canonicalMap b := by
  unfold overlap_plus_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 1]
  · simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X, pow_one]
    change (overlapDatum B P b).canonicalMap
      ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 1))
        (MvPowerSeries.X 0)) *
      (overlapDatum B P b).canonicalMap b =
      (overlapDatum B P b).canonicalMap b
    rw [MvPowerSeries.coeff_X, if_pos rfl, map_one, one_mul]
  · intro n hn
    simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X]
    change (overlapDatum B P b).canonicalMap
      ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (MvPowerSeries.X (0 : Fin 1))) *
      (overlapDatum B P b).canonicalMap b ^ n = 0
    classical
    have hcoeff : (MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (MvPowerSeries.X (σ := Fin 1) 0) = 0 := by
      rw [MvPowerSeries.coeff_X]
      apply if_neg
      intro heq
      apply hn
      have : (Finsupp.single 0 n : Fin 1 →₀ ℕ) 0 =
        (Finsupp.single 0 1 : Fin 1 →₀ ℕ) 0 := by rw [heq]
      simpa using this
    simp [hcoeff]

/-- `overlap_minus_evalHom` sends `algebraMap a` to `canonicalMap a`.
Structurally identical proof to `overlap_plus_evalHom_algebraMap`. -/
theorem overlap_minus_evalHom_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b a : B) :
    overlap_minus_evalHom B P b (algebraMap B _ a) =
      (overlapDatum B P b).canonicalMap a := by
  unfold overlap_minus_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 0]
  · unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    simp only [Finsupp.single_zero, pow_zero, mul_one]
    congr 1
  · intro n hn
    unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    have : (MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (↑(algebraMap B ↥(TateAlgebra B) a) : MvPowerSeries (Fin 1) B) = 0 := by
      change (MvPowerSeries.coeff (Finsupp.single 0 n))
        (MvPowerSeries.C (σ := Fin 1) a) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg (Finsupp.single_ne_zero.mpr hn)]
    simp [this]

/-- `overlap_minus_evalHom` sends `X` to `invS`. -/
theorem overlap_minus_evalHom_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    overlap_minus_evalHom B P b TateAlgebra.X =
      invS (overlapDatum B P b) := by
  unfold overlap_minus_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 1]
  · simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X, pow_one]
    change (overlapDatum B P b).canonicalMap
      ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 1))
        (MvPowerSeries.X 0)) *
      invS (overlapDatum B P b) =
      invS (overlapDatum B P b)
    rw [MvPowerSeries.coeff_X, if_pos rfl, map_one, one_mul]
  · intro n hn
    simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X]
    change (overlapDatum B P b).canonicalMap
      ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (MvPowerSeries.X (0 : Fin 1))) *
      invS (overlapDatum B P b) ^ n = 0
    classical
    have hcoeff : (MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (MvPowerSeries.X (σ := Fin 1) 0) = 0 := by
      rw [MvPowerSeries.coeff_X]
      apply if_neg
      intro heq
      apply hn
      have : (Finsupp.single 0 n : Fin 1 →₀ ℕ) 0 =
        (Finsupp.single 0 1 : Fin 1 →₀ ℕ) 0 := by rw [heq]
      simpa using this
    simp [hcoeff]

/-- The plus-half evalHom kills `algebraMap b - X` (both map to `canonicalMap b`). -/
theorem overlap_plus_evalHom_fSubX_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    overlap_plus_evalHom B P b
      (algebraMap B ↥(TateAlgebra B) b - TateAlgebra.X) = 0 := by
  rw [map_sub, overlap_plus_evalHom_algebraMap, overlap_plus_evalHom_X, sub_self]

/-- The minus-half evalHom kills `1 - algebraMap b · X` (since the image of
`algebraMap b · X` is `canonicalMap b · invS = 1`). -/
theorem overlap_minus_evalHom_oneSubfX_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    overlap_minus_evalHom B P b
      (1 - algebraMap B ↥(TateAlgebra B) b * TateAlgebra.X) = 0 := by
  rw [map_sub, map_one, map_mul, overlap_minus_evalHom_algebraMap,
    overlap_minus_evalHom_X, canonicalMap_b_mul_invS_in_overlap, sub_self]

/-- **Plus forward hom** `B₁_gen b →+* presheafValue(overlap)`, obtained by
factoring `overlap_plus_evalHom` through the ideal `(algebraMap b - X)`. -/
noncomputable def overlap_plus_forwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    LaurentCover.B₁_gen b →+* presheafValue (overlapDatum B P b) :=
  Ideal.Quotient.lift _ (overlap_plus_evalHom B P b) (fun y hy ↦ by
    rw [Ideal.mem_span_singleton'] at hy
    obtain ⟨c, hc⟩ := hy
    rw [← hc, map_mul, overlap_plus_evalHom_fSubX_eq_zero, mul_zero])

/-- **Minus forward hom** `B₂_gen b →+* presheafValue(overlap)`, obtained by
factoring `overlap_minus_evalHom` through the ideal `(1 - algebraMap b · X)`. -/
noncomputable def overlap_minus_forwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    LaurentCover.B₂_gen b →+* presheafValue (overlapDatum B P b) :=
  Ideal.Quotient.lift _ (overlap_minus_evalHom B P b) (fun y hy ↦ by
    rw [Ideal.mem_span_singleton'] at hy
    obtain ⟨c, hc⟩ := hy
    rw [← hc, map_mul, overlap_minus_evalHom_oneSubfX_eq_zero, mul_zero])

/-! #### Step A forward: bivariate evaluation into overlap via `evalHomBounded₂`

The bivariate analog of `overlap_plus_evalHom` / `overlap_minus_evalHom`:
a single evaluation hom `TateAlgebra₂ B →+* presheafValue (overlap)` sending
`X ↦ canonicalMap b` and `Y ↦ invS`, built directly from the new bivariate
universal property `TateAlgebraWedhorn.evalHomBounded₂`, together with its
action lemmas and the two kernel closures needed to factor through
`Ideal.span {b - X, 1 - b·Y}`. The resulting quotient hom
`example638Bivariate_forwardHom` is the Step A forward hom of
Wedhorn Example 6.39. -/

/-- **Bivariate evaluation hom into the overlap** (Wedhorn Example 6.39,
Step A forward primitive): `TateAlgebra₂ B →+* presheafValue (overlap)`
sending `X ↦ canonicalMap b` and `Y ↦ invS`, via `evalHomBounded₂`.

Both `canonicalMap b` and `invS` are power-bounded in the overlap
completion (by `canonicalMap_b_isPowerBounded_in_overlap` and
`invS_isPowerBounded_in_overlap`), which are the exact bivariate-eval
hypotheses required by `evalHomBounded₂`. -/
noncomputable def example638Bivariate_evalHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra₂ B) →+* presheafValue (overlapDatum B P b) :=
  TateAlgebraWedhorn.evalHomBounded₂
    (overlapDatum B P b).canonicalMap
    (canonicalMap_continuous (overlapDatum B P b))
    ((overlapDatum B P b).canonicalMap b)
    (invS (overlapDatum B P b))
    (canonicalMap_b_isPowerBounded_in_overlap B P b)
    (invS_isPowerBounded_in_overlap B P b)

/-- `example638Bivariate_evalHom` sends `algebraMap a` to `canonicalMap a`. -/
theorem example638Bivariate_evalHom_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b a : B) :
    example638Bivariate_evalHom B P b (algebraMap B _ a) =
      (overlapDatum B P b).canonicalMap a :=
  TateAlgebraWedhorn.evalHomBounded₂_algebraMap _ _ _ _ _ _ a

/-- `example638Bivariate_evalHom` sends `TateAlgebra₂.X` to `canonicalMap b`. -/
theorem example638Bivariate_evalHom_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Bivariate_evalHom B P b TateAlgebra₂.X =
      (overlapDatum B P b).canonicalMap b :=
  TateAlgebraWedhorn.evalHomBounded₂_X _ _ _ _ _ _

/-- `example638Bivariate_evalHom` sends `TateAlgebra₂.Y` to `invS`. -/
theorem example638Bivariate_evalHom_Y
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Bivariate_evalHom B P b TateAlgebra₂.Y =
      invS (overlapDatum B P b) :=
  TateAlgebraWedhorn.evalHomBounded₂_Y _ _ _ _ _ _

/-- `example638Bivariate_evalHom` kills `algebraMap b - X` (both generators
map to `canonicalMap b`). -/
theorem example638Bivariate_evalHom_fSubX_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Bivariate_evalHom B P b
      (algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X) = 0 := by
  rw [map_sub, example638Bivariate_evalHom_algebraMap,
    example638Bivariate_evalHom_X, sub_self]

/-- `example638Bivariate_evalHom` kills `1 - algebraMap b · Y` (since
`canonicalMap b · invS = 1` in the overlap completion). -/
theorem example638Bivariate_evalHom_oneSubfY_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Bivariate_evalHom B P b
      (1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y) = 0 := by
  rw [map_sub, map_one, map_mul, example638Bivariate_evalHom_algebraMap,
    example638Bivariate_evalHom_Y, canonicalMap_b_mul_invS_in_overlap, sub_self]

/-- **Step A forward hom** (Wedhorn Example 6.39):
`TateAlgebra₂ B ⧸ (b - X, 1 - b·Y) →+* presheafValue (overlap)`,
obtained by factoring `example638Bivariate_evalHom` through the two-generator
ideal. Kernel closure is a direct application of the two `_eq_zero` lemmas
under `Ideal.span_le`. -/
noncomputable def example638Bivariate_forwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra₂ B) ⧸
        Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X,
                    1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y}
      →+* presheafValue (overlapDatum B P b) := by
  refine Ideal.Quotient.lift _ (example638Bivariate_evalHom B P b) (fun y hy ↦ ?_)
  have h_le : Ideal.span
        {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X,
         1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y} ≤
      RingHom.ker (example638Bivariate_evalHom B P b) := by
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact example638Bivariate_evalHom_fSubX_eq_zero B P b
    · exact example638Bivariate_evalHom_oneSubfY_eq_zero B P b
  exact h_le hy

/-- `example638Bivariate_forwardHom` on `mk(algebraMap a)` equals `canonicalMap a`
(immediate from `Ideal.Quotient.lift_mk` + the evalHom action on `algebraMap`). -/
theorem example638Bivariate_forwardHom_mk_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b a : B) :
    example638Bivariate_forwardHom B P b
        (Ideal.Quotient.mk _ (algebraMap B ↥(TateAlgebra₂ B) a)) =
      (overlapDatum B P b).canonicalMap a := by
  change Ideal.Quotient.lift _ (example638Bivariate_evalHom B P b) _
      (Ideal.Quotient.mk _ (algebraMap B ↥(TateAlgebra₂ B) a)) = _
  rw [Ideal.Quotient.lift_mk]
  exact example638Bivariate_evalHom_algebraMap B P b a

/-- `example638Bivariate_forwardHom` on `mk(X)` equals `canonicalMap b`. -/
theorem example638Bivariate_forwardHom_mk_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Bivariate_forwardHom B P b
        (Ideal.Quotient.mk _ (TateAlgebra₂.X : ↥(TateAlgebra₂ B))) =
      (overlapDatum B P b).canonicalMap b := by
  change Ideal.Quotient.lift _ (example638Bivariate_evalHom B P b) _
      (Ideal.Quotient.mk _ (TateAlgebra₂.X : ↥(TateAlgebra₂ B))) = _
  rw [Ideal.Quotient.lift_mk]
  exact example638Bivariate_evalHom_X B P b

/-- `example638Bivariate_forwardHom` on `mk(Y)` equals `invS`. -/
theorem example638Bivariate_forwardHom_mk_Y
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Bivariate_forwardHom B P b
        (Ideal.Quotient.mk _ (TateAlgebra₂.Y : ↥(TateAlgebra₂ B))) =
      invS (overlapDatum B P b) := by
  change Ideal.Quotient.lift _ (example638Bivariate_evalHom B P b) _
      (Ideal.Quotient.mk _ (TateAlgebra₂.Y : ↥(TateAlgebra₂ B))) = _
  rw [Ideal.Quotient.lift_mk]
  exact example638Bivariate_evalHom_Y B P b

end BivariateOverlapPowerBounded

end BivariateOverlap

/-! ### Step B — the algebraic overlap iso

This section implements the PURE ALGEBRAIC identification
```
TateAlgebra₂ B / (b - X, 1 - b·Y)  ≃+*  B₁₂_gen b
```
following Wedhorn p.83 (proof of Lemma 8.33). No topology is needed — this
is an ideal-equality + third-iso-theorem argument.
-/

section BivariateOverlapAlgebra

variable (B : Type*) [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]

open TateAlgebra₂ in
/-- **Key ideal equality** (Wedhorn's "`1 - fη ≡ 1 - ζη` mod `(f - ζ)`"):
inside `TateAlgebra₂ B`, the ideal `(b - X, 1 - b·Y)` equals `(b - X, X·Y - 1)`.

This is the pivotal identity on p.83 of Wedhorn that reduces the bivariate
overlap computation to the Laurent-algebra quotient. Both inclusions are
explicit:
* `1 - b·Y = -Y · (b - X) - (X·Y - 1)` gives `1 - b·Y ∈ (b - X, X·Y - 1)`.
* `X·Y - 1 = -Y · (b - X) - (1 - b·Y)` gives `X·Y - 1 ∈ (b - X, 1 - b·Y)`. -/
theorem bivariateOverlap_ideal_eq (b : B) :
    Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X,
                1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y} =
      Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X,
                  TateAlgebra₂.X * TateAlgebra₂.Y - 1} := by
  set bA := algebraMap B ↥(TateAlgebra₂ B) b
  have h_oneSubbY_eq : (1 - bA * TateAlgebra₂.Y) =
      (-TateAlgebra₂.Y) * (bA - TateAlgebra₂.X) -
        (TateAlgebra₂.X * TateAlgebra₂.Y - 1) := by ring
  have h_XYSubOne_eq : (TateAlgebra₂.X * TateAlgebra₂.Y - 1) =
      (-TateAlgebra₂.Y) * (bA - TateAlgebra₂.X) - (1 - bA * TateAlgebra₂.Y) := by ring
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [h_oneSubbY_eq]
      exact (Ideal.span _).sub_mem
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
        (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  · rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [h_XYSubOne_eq]
      exact (Ideal.span _).sub_mem
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
        (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))

open TateAlgebra₂ LaurentTateAlgebra in
/-- The ideal `laurentIdeal B ⊔ Ideal.span{b - X}` equals `Ideal.span{b - X, X·Y - 1}`
in `TateAlgebra₂ B`. Used to connect the third-iso-theorem output with the
bivariate overlap ideal. -/
theorem laurentIdeal_sup_bSubX (b : B) :
    laurentIdeal B ⊔ Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X} =
      Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X,
                  TateAlgebra₂.X * TateAlgebra₂.Y - 1} := by
  rw [laurentIdeal, ← Ideal.span_union, Set.singleton_union]
  congr 1
  · change ({XY_sub_one} ∪ {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X} : Set _) =
      insert (algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X) {X * Y - 1}
    ext x; simp [or_comm, XY_sub_one]

open TateAlgebra₂ LaurentTateAlgebra in
/-- **Step B of T-OV-1 (pure algebra)**: the bivariate Tate-algebra quotient
`B⟨ζ, η⟩/(b - ζ, 1 - b·η)` is ring-isomorphic to
`B₁₂_gen b = B⟨ζ, ζ⁻¹⟩/(b - ζ)`.

This follows Wedhorn Lemma 8.33 p.83 literally:
1. `Ideal.span{b - X, 1 - b·Y} = Ideal.span{b - X, X·Y - 1}` (by the key
   identity `1 - b·Y ≡ -(XY - 1)` mod `(b - X)`).
2. `TateAlgebra₂ B / Ideal.span{b - X, X·Y - 1}
     ≃+* (TateAlgebra₂ B / laurentIdeal B) / Ideal.span{b - X}.map(mkHom)`
   by the third isomorphism theorem (`DoubleQuot.quotQuotEquivQuotSup` reversed).
3. `LaurentTateAlgebra B / Ideal.span{algebraMap b - ζ} = B₁₂_gen b`
   by definition. -/
noncomputable def bivariateOverlap_equiv_B₁₂gen (b : B) :
    ↥(TateAlgebra₂ B) ⧸ Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X,
                                    1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y}
      ≃+* LaurentCover.B₁₂_gen b :=
  (Ideal.quotEquivOfEq (bivariateOverlap_ideal_eq B b)).trans <|
  (Ideal.quotEquivOfEq (laurentIdeal_sup_bSubX B b).symm).trans <|
  (DoubleQuot.quotQuotEquivQuotSup (laurentIdeal B)
      (Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X})).symm.trans <|
  -- Step 4: identify the inner quotient as `B₁₂_gen b`, which has the same
  -- underlying type and the ideal `laurentFSubZetaIdeal b` coincides with
  -- `Ideal.span{b - X}.map(mkHom)` — both equal `Ideal.span{mkHom(b - X)}`.
  Ideal.quotEquivOfEq (by
    change (Ideal.span {algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X}).map
        (Ideal.Quotient.mk (laurentIdeal B)) =
      LaurentCover.laurentFSubZetaIdeal b
    rw [Ideal.map_span, LaurentCover.laurentFSubZetaIdeal]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, rfl, rfl⟩
      change LaurentTateAlgebra.mkHom
          (algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X) =
        algebraMap B (LaurentTateAlgebra B) b - LaurentTateAlgebra.zeta
      rw [map_sub]
      rfl
    · rintro rfl
      refine ⟨algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X, rfl, ?_⟩
      change LaurentTateAlgebra.mkHom
          (algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X) =
        algebraMap B (LaurentTateAlgebra B) b - LaurentTateAlgebra.zeta
      rw [map_sub]
      rfl)

/-! #### Generator action lemmas for `bivariateOverlap_equiv_B₁₂gen`

These describe how the Step B iso acts on canonical elements (the algebraMap
from B, the generators X and Y of `TateAlgebra₂ B`). They are the compatibility
data needed by any consumer chaining through Step B to establish intertwining
identities (e.g., `laurentOverlapBridge_exists_compatible`). -/

open TateAlgebra₂ LaurentTateAlgebra in
/-- **General action**: the Step B iso sends the class of `x ∈ TateAlgebra₂ B`
to the class of `mkHom x` in `B₁₂_gen b`.

This is the master action lemma from which the generator lemmas follow. -/
theorem bivariateOverlap_equiv_B₁₂gen_mk (b : B) (x : ↥(TateAlgebra₂ B)) :
    bivariateOverlap_equiv_B₁₂gen B b (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
        (LaurentTateAlgebra.mkHom x) := rfl

open TateAlgebra₂ LaurentTateAlgebra in
/-- **Action on algebraMap**: the Step B iso sends `mk(algebraMap a)` to
`algebraMap a` in `B₁₂_gen b`. -/
theorem bivariateOverlap_equiv_B₁₂gen_algebraMap (b a : B) :
    bivariateOverlap_equiv_B₁₂gen B b
        (Ideal.Quotient.mk _ (algebraMap B ↥(TateAlgebra₂ B) a)) =
      algebraMap B (LaurentCover.B₁₂_gen b) a := by
  rw [bivariateOverlap_equiv_B₁₂gen_mk]
  rfl

open TateAlgebra₂ LaurentTateAlgebra in
/-- **Action on X**: the Step B iso sends `mk(X)` to (the class of) `zeta`
in `B₁₂_gen b`. -/
theorem bivariateOverlap_equiv_B₁₂gen_X (b : B) :
    bivariateOverlap_equiv_B₁₂gen B b
        (Ideal.Quotient.mk _ (TateAlgebra₂.X : ↥(TateAlgebra₂ B))) =
      Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
        LaurentTateAlgebra.zeta := by
  rw [bivariateOverlap_equiv_B₁₂gen_mk]
  rfl

open TateAlgebra₂ LaurentTateAlgebra in
/-- **Action on Y**: the Step B iso sends `mk(Y)` to (the class of) `zetaInv`
in `B₁₂_gen b`. -/
theorem bivariateOverlap_equiv_B₁₂gen_Y (b : B) :
    bivariateOverlap_equiv_B₁₂gen B b
        (Ideal.Quotient.mk _ (TateAlgebra₂.Y : ↥(TateAlgebra₂ B))) =
      Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
        LaurentTateAlgebra.zetaInv := by
  rw [bivariateOverlap_equiv_B₁₂gen_mk]
  rfl

/-! #### Step A backward: algebraic primitives

The algebraic half of the backward hom for Wedhorn Example 6.39: in the
bivariate quotient `TateAlgebra₂ B ⧸ (b - X, 1 - b · Y)`, the image of `b`
is a unit (with inverse `mk(Y)`), so the universal property of
`Localization.Away b` gives an algebraic ring hom
`bivariateLocToQuotient : Localization.Away b →+* TateAlgebra₂ B ⧸ (…)`.

This is the bivariate analog of the univariate `plusLocToQuotient`
(Example638.lean:345). The *topological* completion extension step
(analog of `example638Plus_backwardHom`) is deferred to a later ticket
because it requires new infrastructure (canonical topology on
`TateAlgebra₂`, closed-ideal theorem, bivariate quotient completeness
+ T2, continuity of `bivariateLocToQuotient`) — see the T005 blocker
report. -/

/-- In the bivariate quotient `TateAlgebra₂ B ⧸ (b - X, 1 - b · Y)`, the
image of `b ∈ B` under `algebraMap` is a unit, with inverse `mk(Y)`.

Proof: `mk(algMap b) * mk(Y) = mk(algMap b · Y) = mk(1)` holds because
`algMap b · Y - 1 = -(1 - algMap b · Y)` and the second generator lies in
the ideal. Bivariate analog of `isUnit_one_in_quotientPlusFSubX`
(Example638.lean:336, which uses the trivial fact that `1` is a unit). -/
theorem isUnit_b_in_bivariate_quotient (b : B) :
    IsUnit ((Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)).comp
      (algebraMap B ↥(TateAlgebra₂ B)) b) := by
  have h_mul : Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
      (algebraMap B ↥(TateAlgebra₂ B) b) *
    Ideal.Quotient.mk _ TateAlgebra₂.Y = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _)]
    refine Ideal.Quotient.eq.mpr ?_
    have h_sign : algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y - 1 =
        -(1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y) := by ring
    rw [h_sign]
    unfold TateAlgebra.bivariateOverlapIdeal
    exact neg_mem (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  exact (Units.mkOfMulEqOne _ _ h_mul).isUnit

/-- **Algebraic backward hom** `Localization.Away b →+* TateAlgebra₂ B ⧸
bivariateOverlapIdeal b`, via the universal property of `IsLocalization.Away`
applied to `b` (which is a unit in the quotient by
`isUnit_b_in_bivariate_quotient`).

Bivariate analog of `plusLocToQuotient` (Example638.lean:345). Sends
`algebraMap a ↦ mk(algebraMap a)`. The topological extension to the overlap
presheafValue is handled in `bivariateLocToQuotient_continuous`, which
transports this to the overlap datum's source type via a Localization
bridge. -/
noncomputable def bivariateLocToQuotient (b : B) :
    Localization.Away b →+*
      ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b :=
  IsLocalization.Away.lift (x := b) (isUnit_b_in_bivariate_quotient B b)

/-- `bivariateLocToQuotient` sends `algebraMap a` to `mk(algebraMap a)`. -/
theorem bivariateLocToQuotient_algebraMap (b a : B) :
    bivariateLocToQuotient B b (algebraMap B _ a) =
      (Ideal.Quotient.mk _) (algebraMap B ↥(TateAlgebra₂ B) a) := by
  simp only [bivariateLocToQuotient, IsLocalization.Away.lift_eq]
  rfl

/-! Symm-direction action lemmas (for backward composition). -/

/-- The symm direction sends `mk(mkHom x) ∈ B₁₂_gen b` back to `mk(x) ∈ TateAlgebra₂ B / ...`.
Follows by symm application of `bivariateOverlap_equiv_B₁₂gen_mk`. -/
theorem bivariateOverlap_equiv_B₁₂gen_symm_mk (b : B) (x : ↥(TateAlgebra₂ B)) :
    (bivariateOverlap_equiv_B₁₂gen B b).symm
        (Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
          (LaurentTateAlgebra.mkHom x)) =
      Ideal.Quotient.mk _ x := by
  rw [← bivariateOverlap_equiv_B₁₂gen_mk B b x]
  exact (bivariateOverlap_equiv_B₁₂gen B b).symm_apply_apply _

open TateAlgebra₂ LaurentTateAlgebra in
/-- The symm direction sends `algebraMap a ∈ B₁₂_gen b` back to `mk(algebraMap a)`. -/
theorem bivariateOverlap_equiv_B₁₂gen_symm_algebraMap (b a : B) :
    (bivariateOverlap_equiv_B₁₂gen B b).symm
        (algebraMap B (LaurentCover.B₁₂_gen b) a) =
      Ideal.Quotient.mk _ (algebraMap B ↥(TateAlgebra₂ B) a) := by
  rw [← bivariateOverlap_equiv_B₁₂gen_algebraMap B b a]
  exact (bivariateOverlap_equiv_B₁₂gen B b).symm_apply_apply _

open TateAlgebra₂ LaurentTateAlgebra in
/-- The symm direction sends the class of `zeta` back to `mk(X)`. -/
theorem bivariateOverlap_equiv_B₁₂gen_symm_zeta (b : B) :
    (bivariateOverlap_equiv_B₁₂gen B b).symm
        (Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
          LaurentTateAlgebra.zeta) =
      Ideal.Quotient.mk _ (TateAlgebra₂.X : ↥(TateAlgebra₂ B)) := by
  rw [← bivariateOverlap_equiv_B₁₂gen_X B b]
  exact (bivariateOverlap_equiv_B₁₂gen B b).symm_apply_apply _

open TateAlgebra₂ LaurentTateAlgebra in
/-- The symm direction sends the class of `zetaInv` back to `mk(Y)`. -/
theorem bivariateOverlap_equiv_B₁₂gen_symm_zetaInv (b : B) :
    (bivariateOverlap_equiv_B₁₂gen B b).symm
        (Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
          LaurentTateAlgebra.zetaInv) =
      Ideal.Quotient.mk _ (TateAlgebra₂.Y : ↥(TateAlgebra₂ B)) := by
  rw [← bivariateOverlap_equiv_B₁₂gen_Y B b]
  exact (bivariateOverlap_equiv_B₁₂gen B b).symm_apply_apply _

end BivariateOverlapAlgebra

/-! ### Step A ∘ Step B: forward hom from `LaurentCover.B₁₂_gen`

Consumer-facing bridge for Wedhorn Example 6.39 / T-OV-1:
`LaurentCover.B₁₂_gen b →+* presheafValue (overlapDatum B P b)`, obtained by
pre-composing `example638Bivariate_forwardHom` with the inverse of the Step B
algebraic iso `bivariateOverlap_equiv_B₁₂gen`.

This is the forward direction consumed by `laurentOverlapBridge_exists_compatible`
in `LaurentRefinement.lean`; the full iso (Step A+B equivalence) additionally
requires a backward hom via completion extension (analog of
`example638Plus_backwardHom`), which is deferred to a later ticket. -/

section BivariateOverlapComposition

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
  [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

/-- **Composed Step A + Step B forward hom** (Wedhorn Example 6.39):
`LaurentCover.B₁₂_gen b →+* presheafValue (overlapDatum B P b)`,
obtained by composing the Step A forward hom with the inverse of the
Step B algebraic iso. -/
noncomputable def example638Bivariate_forwardHom_B₁₂gen
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    LaurentCover.B₁₂_gen b →+* presheafValue (overlapDatum B P b) :=
  (example638Bivariate_forwardHom B P b).comp
    (bivariateOverlap_equiv_B₁₂gen B b).symm.toRingHom

/-- The composed hom sends `algebraMap a` to `canonicalMap a`. Follows by
chasing `algebraMap a` back through the Step B `symm` to `mk(algebraMap a)`
in `TateAlgebra₂ B ⧸ (b-X, 1-b·Y)`, then applying the Step A forward action. -/
theorem example638Bivariate_forwardHom_B₁₂gen_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b a : B) :
    example638Bivariate_forwardHom_B₁₂gen B P b
        (algebraMap B (LaurentCover.B₁₂_gen b) a) =
      (overlapDatum B P b).canonicalMap a := by
  change example638Bivariate_forwardHom B P b
      ((bivariateOverlap_equiv_B₁₂gen B b).symm
        (algebraMap B (LaurentCover.B₁₂_gen b) a)) = _
  rw [bivariateOverlap_equiv_B₁₂gen_symm_algebraMap]
  exact example638Bivariate_forwardHom_mk_algebraMap B P b a

/-- The composed hom sends the class of `zeta` in `B₁₂_gen b` to `canonicalMap b`. -/
theorem example638Bivariate_forwardHom_B₁₂gen_zeta
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Bivariate_forwardHom_B₁₂gen B P b
        (Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
          LaurentTateAlgebra.zeta) =
      (overlapDatum B P b).canonicalMap b := by
  change example638Bivariate_forwardHom B P b
      ((bivariateOverlap_equiv_B₁₂gen B b).symm
        (Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
          LaurentTateAlgebra.zeta)) = _
  rw [bivariateOverlap_equiv_B₁₂gen_symm_zeta]
  exact example638Bivariate_forwardHom_mk_X B P b

/-- The composed hom sends the class of `zetaInv` in `B₁₂_gen b` to `invS`. -/
theorem example638Bivariate_forwardHom_B₁₂gen_zetaInv
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Bivariate_forwardHom_B₁₂gen B P b
        (Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
          LaurentTateAlgebra.zetaInv) =
      invS (overlapDatum B P b) := by
  change example638Bivariate_forwardHom B P b
      ((bivariateOverlap_equiv_B₁₂gen B b).symm
        (Ideal.Quotient.mk (LaurentCover.laurentFSubZetaIdeal b)
          LaurentTateAlgebra.zetaInv)) = _
  rw [bivariateOverlap_equiv_B₁₂gen_symm_zetaInv]
  exact example638Bivariate_forwardHom_mk_Y B P b

/-! ### Step A backward: continuity of `bivariateLocToQuotient`

Wedhorn Example 6.39 / T-OV-1 continuity step: the algebraic map
`bivariateLocToQuotient : Localization.Away b →+* TateAlgebra₂ B ⧸ bivariateOverlapIdeal b`
is continuous for the overlap `locTopology` (on the overlap datum's source
type `Localization.Away (overlapDatum B P b).s`) to the canonical quotient
topology on the target (from T013). Combined with the target's
`CompleteSpace` + `T2Space` (also from T013), this is the immediate
predecessor for `UniformSpace.Completion.extensionHom` to define
`example638Bivariate_backwardHom`.

Because `(overlapDatum B P b).s = b` only as a *theorem* (not definitional),
we define an auxiliary hom `bivariateLocToQuotient_atOverlap` with source
`Localization.Away (overlapDatum B P b).s` that plugs directly into
`locTopology_continuous_lift` without a type cast. -/

/-- The overlap-source version of `bivariateLocToQuotient`, with source
`Localization.Away (overlapDatum B P b).s` instead of `Localization.Away b`.
Requires an `IsLocalization.Away b` instance on the overlap source, which
we obtain by rewriting along `overlapDatum_s`. -/
noncomputable def bivariateLocToQuotient_atOverlap
    (P : PairOfDefinition B) (b : B) :
    Localization.Away (overlapDatum B P b).s →+*
      ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b := by
  haveI : IsLocalization.Away b (Localization.Away (overlapDatum B P b).s) := by
    rw [overlapDatum_s B P b]; infer_instance
  exact IsLocalization.Away.lift (x := b) (isUnit_b_in_bivariate_quotient B b)

/-- `bivariateLocToQuotient_atOverlap` sends `algebraMap a` to `mk(algebraMap a)`. -/
theorem bivariateLocToQuotient_atOverlap_algebraMap
    (P : PairOfDefinition B) (b a : B) :
    bivariateLocToQuotient_atOverlap B P b
        (algebraMap B (Localization.Away (overlapDatum B P b).s) a) =
      (Ideal.Quotient.mk _) (algebraMap B ↥(TateAlgebra₂ B) a) := by
  haveI : IsLocalization.Away b (Localization.Away (overlapDatum B P b).s) := by
    rw [overlapDatum_s B P b]; infer_instance
  change IsLocalization.Away.lift (x := b) (isUnit_b_in_bivariate_quotient B b)
      (algebraMap B (Localization.Away (overlapDatum B P b).s) a) = _
  rw [IsLocalization.Away.lift_eq]
  rfl

/-- The three distinct values of `bivariateLocToQuotient_atOverlap (divByS t (overlap).s)`
for `t ∈ (overlapDatum B P b).T` (i.e., `{1, b, b²}`) are respectively
`mk(Y)` (the inverse of `mk(algMap b)` in the quotient), `1`, and
`mk(algMap b)`. Each is power-bounded by the T013 helpers, establishing
the bounded-generator hypothesis of `locTopology_continuous_lift`. -/
theorem bivariateLocToQuotient_continuous
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    @Continuous _ _ (overlapDatum B P b).topology
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (bivariateLocToQuotient_atOverlap B P b) := by
  letI : TopologicalSpace (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).topology
  letI : IsTopologicalRing (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isTopologicalAddGroup
  letI : TopologicalSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  letI : IsTopologicalRing (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b
  haveI : NonarchimedeanRing (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_nonarchimedean b
  haveI : IsLocalization.Away b (Localization.Away (overlapDatum B P b).s) := by
    rw [overlapDatum_s B P b]; infer_instance
  have hs : (overlapDatum B P b).s = b := overlapDatum_s B P b
  /- Compute the three relevant `divByS` values (in the overlap source).
  We use `rw [hs]` rather than `subst hs` because `b` appears in
  `overlapDatum B P b` and cannot be substituted away. -/
  have h_loc_bb : divByS b (overlapDatum B P b).s =
      (1 : Localization.Away (overlapDatum B P b).s) := by
    unfold divByS
    rw [hs]
    exact IsLocalization.mk'_self (M := Submonoid.powers b)
      (S := Localization.Away b) (⟨1, pow_one b⟩ : b ∈ Submonoid.powers b)
  have h_loc_bsq : divByS (b * b) (overlapDatum B P b).s =
      algebraMap B (Localization.Away (overlapDatum B P b).s) b := by
    unfold divByS
    rw [hs]
    rw [← IsLocalization.mk'_one (M := Submonoid.powers b)
        (S := Localization.Away b) b]
    apply IsLocalization.mk'_eq_of_eq
    simp only [Submonoid.coe_one, one_mul]
  have h_inv_algmap : divByS 1 (overlapDatum B P b).s *
      algebraMap B (Localization.Away (overlapDatum B P b).s) b = 1 := by
    unfold divByS
    rw [hs]
    rw [IsLocalization.mk'_spec]
    exact map_one _
  /- Reduce `bivariateLocToQuotient_atOverlap (divByS 1 (overlap).s)` to `mk Y`
  via uniqueness of inverse in the quotient. -/
  have h_biv_inv :
      bivariateLocToQuotient_atOverlap B P b (divByS 1 (overlapDatum B P b).s) *
      Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
        (algebraMap B ↥(TateAlgebra₂ B) b) = 1 := by
    rw [← bivariateLocToQuotient_atOverlap_algebraMap B P b b,
        ← map_mul, h_inv_algmap, map_one]
  have h_Y_inv : Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
        TateAlgebra₂.Y *
      Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
        (algebraMap B ↥(TateAlgebra₂ B) b) = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _)]
    refine Ideal.Quotient.eq.mpr ?_
    have h_sign : TateAlgebra₂.Y * algebraMap B ↥(TateAlgebra₂ B) b - 1 =
        -(1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y) := by ring
    rw [h_sign]
    unfold TateAlgebra.bivariateOverlapIdeal
    exact neg_mem (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have h_inv :
      bivariateLocToQuotient_atOverlap B P b (divByS 1 (overlapDatum B P b).s) =
      Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b) TateAlgebra₂.Y :=
    (left_inv_eq_right_inv h_Y_inv (by rw [mul_comm]; exact h_biv_inv)).symm
  /- Main continuity via `locTopology_continuous_lift`. -/
  apply locTopology_continuous_lift (overlapDatum B P b).P (overlapDatum B P b).T
    (overlapDatum B P b).s (overlapDatum B P b).hopen
    (bivariateLocToQuotient_atOverlap B P b)
  · -- (1) Composition with `algebraMap B` is continuous.
    change @Continuous _ _ _ (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      ((bivariateLocToQuotient_atOverlap B P b).comp
        (algebraMap B (Localization.Away (overlapDatum B P b).s)))
    have heq : ∀ a : B,
        ((bivariateLocToQuotient_atOverlap B P b).comp
          (algebraMap B (Localization.Away (overlapDatum B P b).s))) a =
        Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
          (algebraMap B ↥(TateAlgebra₂ B) a) := by
      intro a
      simp only [RingHom.comp_apply]
      exact bivariateLocToQuotient_atOverlap_algebraMap B P b a
    rw [show ⇑((bivariateLocToQuotient_atOverlap B P b).comp
        (algebraMap B (Localization.Away (overlapDatum B P b).s))) =
        (fun a : B ↦ Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
            (algebraMap B ↥(TateAlgebra₂ B) a)) from funext heq]
    exact TateAlgebra.mk_algebraMap_continuous_bivariateOverlap b
  · -- (2) Power-boundedness at each `t ∈ (overlapDatum).T`.
    intro t ht
    classical
    change t ∈ Finset.image (fun p : B × B ↦ p.1 * p.2)
      (Finset.product (insert (1 : B) {b}) ({1, b} : Finset B)) at ht
    obtain ⟨p, hp_mem, hp_eq⟩ := Finset.mem_image.mp ht
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp_mem
    obtain ⟨p1, p2⟩ := p
    -- `hp_eq : (fun p => p.1 * p.2) (p1, p2) = t` beta-reduces to `p1 * p2 = t`.
    change p1 * p2 = t at hp_eq
    subst hp_eq
    change p1 ∈ insert (1 : B) {b} at h1
    change p2 ∈ ({1, b} : Finset B) at h2
    rw [Finset.mem_insert, Finset.mem_singleton] at h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    /- Use `rw` instead of `rcases rfl` to avoid `subst` substituting the
    outer parameter `b` instead of the local `p1`/`p2`. -/
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      rw [h1, h2]
    · -- (p1, p2) = (1, 1), t = 1, `divByS 1 (overlap).s ↦ mk Y`.
      rw [show ((1 : B) * 1) = 1 from mul_one 1, h_inv]
      exact TateAlgebra.mk_Y_isPowerBounded_in_bivariateOverlap b
    · -- (p1, p2) = (1, b), t = b, `divByS b (overlap).s ↦ 1`.
      rw [show ((1 : B) * b) = b from one_mul b, h_loc_bb, map_one]
      exact TopologicalRing.isPowerBounded_one
    · -- (p1, p2) = (b, 1), t = b.
      rw [show (b * (1 : B)) = b from mul_one b, h_loc_bb, map_one]
      exact TopologicalRing.isPowerBounded_one
    · -- (p1, p2) = (b, b), t = b*b.
      rw [h_loc_bsq, bivariateLocToQuotient_atOverlap_algebraMap]
      exact TateAlgebra.mk_algebraMap_b_isPowerBounded_in_bivariateOverlap b

/-! ### Step A backward: extension to completion

Backward ring hom `presheafValue (overlapDatum B P b) →+*
TateAlgebra₂ B ⧸ bivariateOverlapIdeal b`, obtained by extending
`bivariateLocToQuotient_atOverlap` to the completion via
`UniformSpace.Completion.extensionHom`. Mirrors
`Example638Plus_backwardHom` but for the bivariate Laurent overlap. -/

/-- Backward ring hom from the overlap presheaf value to the bivariate quotient,
defined as the completion extension of `bivariateLocToQuotient_atOverlap`.

Requires completeness + T0 of the target (the canonical quotient topology), which
follow from `quotient_bivariateOverlapIdeal_completeSpace` and
`quotient_bivariateOverlapIdeal_t2Space` (T013). -/
noncomputable def example638Bivariate_backwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition)) :
    presheafValue (overlapDatum B P b) →+*
      ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b := by
  letI : UniformSpace (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).uniformSpace
  letI : IsTopologicalRing (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  letI : IsTopologicalRing (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b
  letI : IsTopologicalAddGroup
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b
  letI : UniformSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealUniformSpace b
  letI hQ_uniformAddGroup : @IsUniformAddGroup _
      (TateAlgebra.quotientBivariateOverlapIdealUniformSpace b) _ :=
    @isUniformAddGroup_of_addCommGroup _ _
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b)
  haveI hQ_complete : CompleteSpace
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_completeSpace hA_complete hnoeth b
  haveI hT2Q : @T2Space _ (TateAlgebra.quotientBivariateOverlapIdealTopology b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_t2Space hA_complete hnoeth b
  haveI hT0Q : @T0Space _ (TateAlgebra.quotientBivariateOverlapIdealTopology b) :=
    @T1Space.t0Space _ (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      T2Space.t1Space
  exact @UniformSpace.Completion.extensionHom _ _ _ _ _ _
    (TateAlgebra.quotientBivariateOverlapIdealUniformSpace b) _
    hQ_uniformAddGroup
    (TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b)
    (bivariateLocToQuotient_atOverlap B P b)
    (bivariateLocToQuotient_continuous B P b)
    hQ_complete
    hT0Q

/-- On the dense image `coeRingHom a`, `example638Bivariate_backwardHom` agrees
with `bivariateLocToQuotient_atOverlap`. -/
theorem example638Bivariate_backwardHom_coe
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (a : Localization.Away (overlapDatum B P b).s) :
    example638Bivariate_backwardHom B P b hA_complete hnoeth
        ((overlapDatum B P b).coeRingHom a) =
      bivariateLocToQuotient_atOverlap B P b a := by
  letI : UniformSpace (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).uniformSpace
  letI : IsTopologicalRing (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  letI : IsTopologicalRing (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b
  letI : IsTopologicalAddGroup
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b
  letI : UniformSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealUniformSpace b
  letI hQ_uniformAddGroup : @IsUniformAddGroup _
      (TateAlgebra.quotientBivariateOverlapIdealUniformSpace b) _ :=
    @isUniformAddGroup_of_addCommGroup _ _
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b)
  haveI hQ_complete : CompleteSpace
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_completeSpace hA_complete hnoeth b
  haveI hT2Q : @T2Space _ (TateAlgebra.quotientBivariateOverlapIdealTopology b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_t2Space hA_complete hnoeth b
  haveI hT0Q : @T0Space _ (TateAlgebra.quotientBivariateOverlapIdealTopology b) :=
    @T1Space.t0Space _ (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      T2Space.t1Space
  exact @UniformSpace.Completion.extensionHom_coe _ _ _ _ _ _
    (TateAlgebra.quotientBivariateOverlapIdealUniformSpace b) _
    hQ_uniformAddGroup
    (TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b)
    (bivariateLocToQuotient_atOverlap B P b)
    (bivariateLocToQuotient_continuous B P b)
    hQ_complete
    hT0Q a

/-- `example638Bivariate_backwardHom` sends `canonicalMap a` to `mk(algebraMap a)`. -/
theorem example638Bivariate_backwardHom_canonicalMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (a : B) :
    example638Bivariate_backwardHom B P b hA_complete hnoeth
        ((overlapDatum B P b).canonicalMap a) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
        (algebraMap B ↥(TateAlgebra₂ B) a) := by
  change example638Bivariate_backwardHom B P b hA_complete hnoeth
    ((overlapDatum B P b).coeRingHom
      (algebraMap B (Localization.Away (overlapDatum B P b).s) a)) = _
  rw [example638Bivariate_backwardHom_coe, bivariateLocToQuotient_atOverlap_algebraMap]

/-! ### Step A round trip: forward ∘ backward = id on `presheafValue`

`forward ∘ backward = id` on `presheafValue (overlapDatum B P b)`. Uses
`Completion.ext'` to reduce to dense image agreement on `coeRingHom a` for
`a : Localization.Away (overlapDatum B P b).s`, then reduces via
`IsLocalization.ringHom_ext` to the case `algebraMap c` for `c : B`. -/

/-- `forward ∘ backward = id` on `presheafValue (overlapDatum B P b)`.

**Strategy:** `Completion.ext'` reduces to agreement on the dense image
`coeRingHom a`. There, `backward (coeRingHom a) = bivariateLocToQuotient_atOverlap a`
(by `_backwardHom_coe`), so it remains to show
`forward (bivariateLocToQuotient_atOverlap a) = coeRingHom a`.
Both sides are ring homs `Localization.Away (overlapDatum).s →+* presheafValue`,
so `IsLocalization.ringHom_ext` reduces to checking on `algebraMap c`, where
`forward (bivariateLocToQuotient_atOverlap (algebraMap c)) =
   forward (mk(algebraMap c)) = evalHom(algebraMap c) = canonicalMap c =
   coeRingHom (algebraMap c)`. -/
theorem example638Bivariate_forward_backward_eq_id
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (example638Bivariate_forwardHom B P b)) :
    (example638Bivariate_forwardHom B P b).comp
      (example638Bivariate_backwardHom B P b hA_complete hnoeth) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).uniformSpace
  letI : IsTopologicalRing (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isUniformAddGroup
  letI : TopologicalSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  letI : IsTopologicalRing (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b
  letI : IsTopologicalAddGroup
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b
  letI : UniformSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealUniformSpace b
  letI hQ_uniformAddGroup : @IsUniformAddGroup _
      (TateAlgebra.quotientBivariateOverlapIdealUniformSpace b) _ :=
    @isUniformAddGroup_of_addCommGroup _ _
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b)
  haveI : CompleteSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_completeSpace hA_complete hnoeth b
  apply RingHom.ext
  intro y
  change example638Bivariate_forwardHom B P b
    (example638Bivariate_backwardHom B P b hA_complete hnoeth y) = y
  refine @UniformSpace.Completion.ext' _ _
    (presheafValue (overlapDatum B P b)) _ _ _ _
    (hcont_forward.comp UniformSpace.Completion.continuous_extension)
    continuous_id ?_ y
  intro a
  change example638Bivariate_forwardHom B P b
    (example638Bivariate_backwardHom B P b hA_complete hnoeth
      (UniformSpace.Completion.coeRingHom a)) = UniformSpace.Completion.coeRingHom a
  have hbwd : example638Bivariate_backwardHom B P b hA_complete hnoeth
      (UniformSpace.Completion.coeRingHom a) =
      bivariateLocToQuotient_atOverlap B P b a :=
    example638Bivariate_backwardHom_coe B P b hA_complete hnoeth a
  rw [hbwd]
  suffices h : (example638Bivariate_forwardHom B P b).comp
      (bivariateLocToQuotient_atOverlap B P b) =
      (overlapDatum B P b).coeRingHom by
    have := congr_fun (congrArg DFunLike.coe h) a
    simp only [RingHom.comp_apply] at this
    exact this
  apply IsLocalization.ringHom_ext (Submonoid.powers (overlapDatum B P b).s)
  ext c
  change example638Bivariate_forwardHom B P b
      (bivariateLocToQuotient_atOverlap B P b
        (algebraMap B (Localization.Away (overlapDatum B P b).s) c)) =
    (overlapDatum B P b).coeRingHom (algebraMap B _ c)
  rw [bivariateLocToQuotient_atOverlap_algebraMap]
  exact example638Bivariate_forwardHom_mk_algebraMap B P b c

/-! ### Step A backward hom action on `invS`

`example638Bivariate_backwardHom` sends `invS (overlapDatum)` to `mk Y`.
Follows from `invS = coeRingHom (divByS 1 s)` + `_coe` lemma + the continuity
proof's computation `bivariateLocToQuotient_atOverlap (divByS 1 s) = mk Y`. -/

/-- `example638Bivariate_backwardHom (invS (overlap)) = mk(Y)`.

**Proof:** In the quotient, `mk(X)` is invertible with inverse `mk(Y)` (since
`1 - algebraMap b · Y ∈ bivariateOverlapIdeal` gives `mk(algebraMap b) · mk(Y) = 1`,
and `mk(algebraMap b) = mk(X)`). Uniqueness of inverse then pins down
`backward(invS)` against the identity `canonicalMap b · invS = 1`. -/
theorem example638Bivariate_backwardHom_invS
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition)) :
    example638Bivariate_backwardHom B P b hA_complete hnoeth
        (invS (overlapDatum B P b)) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) TateAlgebra₂.Y := by
  have h_bwd_cb : example638Bivariate_backwardHom B P b hA_complete hnoeth
      ((overlapDatum B P b).canonicalMap b) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
        (algebraMap B ↥(TateAlgebra₂ B) b) :=
    example638Bivariate_backwardHom_canonicalMap B P b hA_complete hnoeth b
  have h_mul : (overlapDatum B P b).canonicalMap b * invS (overlapDatum B P b) = 1 :=
    canonicalMap_b_mul_invS_in_overlap B P b
  have h_applied : example638Bivariate_backwardHom B P b hA_complete hnoeth
      ((overlapDatum B P b).canonicalMap b) *
      example638Bivariate_backwardHom B P b hA_complete hnoeth
        (invS (overlapDatum B P b)) = 1 := by
    rw [← map_mul, h_mul, map_one]
  rw [h_bwd_cb] at h_applied
  rw [TateAlgebra.quotient_algebraMap_b_eq_X_bivariate] at h_applied
  have h_XY_inv : Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
        TateAlgebra₂.X *
      Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
        TateAlgebra₂.Y = 1 := by
    rw [← TateAlgebra.quotient_algebraMap_b_eq_X_bivariate, ← map_mul,
        ← map_one (Ideal.Quotient.mk _)]
    refine Ideal.Quotient.eq.mpr ?_
    have h_sign : algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y - 1 =
        -(1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y) := by ring
    rw [h_sign]
    unfold TateAlgebra.bivariateOverlapIdeal
    exact neg_mem (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  -- Uniqueness of multiplicative inverse in commutative ring.
  -- left_inv_eq_right_inv : b * a = 1 → a * c = 1 → b = c.
  -- We have `mk X * mk Y = 1` (h_XY_inv) and `mk X * backward(invS) = 1` (h_applied).
  -- Flip h_XY_inv via mul_comm to get `mk Y * mk X = 1`, then apply: b = mk Y, a = mk X,
  -- c = backward(invS). Conclusion: mk Y = backward(invS).
  have h_YX_inv : Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
        TateAlgebra₂.Y *
      Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b) TateAlgebra₂.X = 1 := by
    rw [mul_comm]; exact h_XY_inv
  exact (left_inv_eq_right_inv h_YX_inv h_applied).symm

/-! ### Step A round trip: backward ∘ forward = id on quotient

Uses `tateAlgebra₂_polynomial_decomp` (polynomial finite-support decomposition)
+ continuity + density (`tateAlgebra₂_polynomials_dense_canonical`) via
`Continuous.ext_on`. On polynomials, ring-hom agreement on generators
(`algebraMap`, `X`, `Y`) via `_canonicalMap`, `quotient_algebraMap_b_eq_X_bivariate`,
and `_backwardHom_invS` implies agreement through the monomial decomposition. -/

/-- `backward ∘ forward = id` on `TateAlgebra₂ B ⧸ bivariateOverlapIdeal b`.

**Strategy:** `Ideal.Quotient.ringHom_ext` reduces to `backward ∘ evalHom = mk`
as ring homs `TateAlgebra₂ B →+* quotient`. Both continuous. The quotient is T2.
Agree on polynomials (elements with box-finite support) via polynomial
decomposition + generator agreement:
- `algebraMap a`: both give `mk(algebraMap a)`.
- `X`: `backward(evalHom X) = backward(canonicalMap b) = mk(algebraMap b) = mk(X)`.
- `Y`: `backward(evalHom Y) = backward(invS) = mk(Y)` (via `_backwardHom_invS`).
Extend to all of `TateAlgebra₂ B` via density + T2 closure. -/
theorem example638Bivariate_backward_forward_eq_id
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (example638Bivariate_forwardHom B P b)) :
    (example638Bivariate_backwardHom B P b hA_complete hnoeth).comp
      (example638Bivariate_forwardHom B P b) =
      RingHom.id _ := by
  letI : TopologicalSpace ↥(TateAlgebra₂ B) := TateAlgebra.instTopologicalSpaceTateAlgebra₂
  letI : TopologicalSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  haveI hT2Q : @T2Space _ (TateAlgebra.quotientBivariateOverlapIdealTopology b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_t2Space hA_complete hnoeth b
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  change (example638Bivariate_backwardHom B P b hA_complete hnoeth)
    (example638Bivariate_forwardHom B P b (Ideal.Quotient.mk _ x)) =
    Ideal.Quotient.mk _ x
  change (example638Bivariate_backwardHom B P b hA_complete hnoeth)
    (Ideal.Quotient.lift _ (example638Bivariate_evalHom B P b) _
      (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.Quotient.lift_mk]
  letI : UniformSpace (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (overlapDatum B P b).s) :=
    (overlapDatum B P b).isTopologicalRing
  letI : UniformSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealUniformSpace b
  letI : IsTopologicalAddGroup
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b
  letI : IsTopologicalRing (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b
  haveI : CompleteSpace (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_completeSpace hA_complete hnoeth b
  have hbwd_cont : @Continuous _ _
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (example638Bivariate_backwardHom B P b hA_complete hnoeth) :=
    UniformSpace.Completion.continuous_extension
  have hevalHom_cont : @Continuous _ _ TateAlgebra.instTopologicalSpaceTateAlgebra₂
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (example638Bivariate_evalHom B P b) := by
    have heq : (example638Bivariate_evalHom B P b : ↥(TateAlgebra₂ B) → _) =
        (example638Bivariate_forwardHom B P b ∘
          Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) := by
      ext y
      change example638Bivariate_evalHom B P b y =
        example638Bivariate_forwardHom B P b (Ideal.Quotient.mk _ y)
      change _ = Ideal.Quotient.lift _ (example638Bivariate_evalHom B P b) _
        (Ideal.Quotient.mk _ y)
      rw [Ideal.Quotient.lift_mk]
    rw [show (example638Bivariate_evalHom B P b : ↥(TateAlgebra₂ B) → _) =
        example638Bivariate_forwardHom B P b ∘
          (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b) :
            ↥(TateAlgebra₂ B) → _)
        from heq]
    exact hcont_forward.comp continuous_quotient_mk'
  have hLHS_cont : @Continuous _ _ TateAlgebra.instTopologicalSpaceTateAlgebra₂
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      ((example638Bivariate_backwardHom B P b hA_complete hnoeth) ∘
        (example638Bivariate_evalHom B P b)) :=
    hbwd_cont.comp hevalHom_cont
  have hRHS_cont : @Continuous _ _ TateAlgebra.instTopologicalSpaceTateAlgebra₂
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) :=
    continuous_quotient_mk'
  have hS_dense : @Dense (↥(TateAlgebra₂ B)) TateAlgebra.instTopologicalSpaceTateAlgebra₂
      {g : ↥(TateAlgebra₂ B) |
        ∃ N : ℕ, ∀ n : Fin 2 →₀ ℕ, N ≤ n 0 ∨ N ≤ n 1 → g.val n = 0} :=
    TateAlgebra.tateAlgebra₂_polynomials_dense_canonical (A := B)
  have hagree : @Set.EqOn _ _
      ((example638Bivariate_backwardHom B P b hA_complete hnoeth) ∘
        (example638Bivariate_evalHom B P b))
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
      {g | ∃ N : ℕ, ∀ n : Fin 2 →₀ ℕ, N ≤ n 0 ∨ N ≤ n 1 → g.val n = 0} := by
    intro g ⟨N, hN⟩
    have hg_eq := TateAlgebra.tateAlgebra₂_polynomial_decomp g N hN
    have h_mono_agree : ∀ (i j : ℕ) (c : B),
        (example638Bivariate_backwardHom B P b hA_complete hnoeth)
          (example638Bivariate_evalHom B P b
            (algebraMap B ↥(TateAlgebra₂ B) c * TateAlgebra₂.X ^ i *
              TateAlgebra₂.Y ^ j)) =
        Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)
          (algebraMap B ↥(TateAlgebra₂ B) c * TateAlgebra₂.X ^ i *
            TateAlgebra₂.Y ^ j) := by
      intros i j c
      rw [map_mul, map_mul, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow,
          map_mul, map_mul, map_pow, map_pow]
      rw [example638Bivariate_evalHom_algebraMap, example638Bivariate_evalHom_X,
        example638Bivariate_evalHom_Y,
        example638Bivariate_backwardHom_canonicalMap,
        example638Bivariate_backwardHom_canonicalMap,
        example638Bivariate_backwardHom_invS,
        TateAlgebra.quotient_algebraMap_b_eq_X_bivariate]
    simp only [Function.comp]
    rw [hg_eq]
    rw [map_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intros i _
    rw [map_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intros j _
    exact h_mono_agree i j _
  exact congr_fun (Continuous.ext_on hS_dense hLHS_cont hRHS_cont hagree) x

/-! ### Step A full equiv: `example638Bivariate_equiv`

Bivariate analog of `Example638Plus_equiv`, packaging the forward hom and
backward hom into a `RingEquiv` using the two round-trip lemmas. -/

/-- **Bivariate Example 6.38 / Step A of Wedhorn Example 6.39:**
`TateAlgebra₂ B / (algebraMap b − X, 1 − algebraMap b · Y) ≃+*
  presheafValue (overlapDatum B P b)`. Bivariate analog of `example638Plus_equiv`. -/
noncomputable def example638Bivariate_equiv
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (overlapDatum B P b)))
      (example638Bivariate_forwardHom B P b)) :
    ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b ≃+*
      presheafValue (overlapDatum B P b) where
  toFun := example638Bivariate_forwardHom B P b
  invFun := example638Bivariate_backwardHom B P b hA_complete hnoeth
  left_inv x :=
    congr_fun (congrArg DFunLike.coe
      (example638Bivariate_backward_forward_eq_id B P b hA_complete hnoeth hcont_forward)) x
  right_inv y :=
    congr_fun (congrArg DFunLike.coe
      (example638Bivariate_forward_backward_eq_id B P b hA_complete hnoeth hcont_forward)) y
  map_mul' := map_mul _
  map_add' := map_add _

end BivariateOverlapComposition

/-! ### Iterated overlap bridge (Wedhorn Lemma 2.13 bivariate analog)

The A-side iterated rational overlap `laurentMinusDatum (laurentPlusDatum D₀ f) f`
and the B-side bivariate overlap `overlapDatum B P_B f_B` carve out the
`same` rational region (Wedhorn Lemma 2.13): their presheafValues are
canonically ring-isomorphic via the map `Loc_A(D₀.s * f) → Loc_B(f_B)`.

Source ring: `Localization.Away ((laurentOverlapDatum D₀ f).s) = Loc_A(D₀.s * f)`
  (same as `Localization.Away (laurentMinusDatum D₀ f).s`).
Target ring: `Localization.Away ((overlapDatum B P_B f_B).s) = Loc_B(f_B)`
  (same as `Localization.Away (iteratedMinusDatum_B P D₀ f).s`).

The UNDERLYING forward loc hom `Loc_A(D₀.s * f) →+* Loc_B(f_B)` is identical to
`iteratedMinus_forwardLocHom D₀ f` (from `LaurentRefinement.lean`). The
difference from the minus case is the **topologies** on source and target:
overlap's `T` contains extra generators (`{f·D₀.s, f²}` on A-side,
`{1, f_B, f_B²}` on B-side vs `{1}` for minus).

The equivalence is established conditional on continuity of the underlying
forward and backward loc homs for the overlap topologies — this mirrors the
`hcont_eval_B` pattern of `laurentMinusBridge`. The continuity can be
discharged via `locTopology_continuous_lift` + power-boundedness once the
additional overlap generators are handled (a separate ticket). -/

section IteratedOverlapBridge

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- The B-side iterated overlap datum: `RationalLocData (presheafValue D₀)`
with `s = D₀.canonicalMap f` (directly, avoiding `1 * _` transport) and
T = {1, f_B, f_B²}` (matching `overlapDatum B P_B f_B` semantically but
definitionally different).

Rather than reuse `overlapDatum` (whose `.s` is `1 * _`), we define this
with `.s := D₀.canonicalMap f` directly so downstream type-level identifications
work without transport. -/
noncomputable def iteratedOverlapDatum_B
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    RationalLocData (presheafValue D₀) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  -- Transport `overlapDatum` via the `overlapDatum_s` equality so the resulting
  -- `.s` field is literally `D₀.canonicalMap f`.
  exact overlapDatum (presheafValue D₀) (presheafValue_pairOfDefinition_concrete P D₀)
    (D₀.canonicalMap f)

/-- The source localization of the iterated overlap equals the source localization
of the iterated minus (both are `Loc_A(D₀.s * f)`). -/
theorem iteratedOverlap_s_eq_laurentMinus_s
    (D₀ : RationalLocData A) (f : A) :
    (laurentOverlapDatum D₀ f).s = (laurentMinusDatum D₀ f).s := rfl

/-- The target localization of the iterated overlap equals the target of
iterated minus (both are `Loc_B(D₀.canonicalMap f)`). -/
theorem iteratedOverlapDatum_B_s_eq
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀)) :
    (iteratedOverlapDatum_B P D₀ f hLocLift_B).s = D₀.canonicalMap f := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  unfold iteratedOverlapDatum_B
  exact overlapDatum_s (presheafValue D₀)
    (presheafValue_pairOfDefinition_concrete P D₀) (D₀.canonicalMap f)

/-! #### Forward loc hom (reused from iterated minus)

Since `(laurentOverlapDatum D₀ f).s = (laurentMinusDatum D₀ f).s = D₀.s * f`,
and `(iteratedOverlapDatum_B P D₀ f).s = (iteratedMinusDatum_B P D₀ f).s =
D₀.canonicalMap f`, the underlying loc hom is identical. We expose it under
an overlap-specific name for clarity. -/

/-- The forward uncompleted hom for the iterated overlap bridge:
`Loc_A(D₀.s * f) →+* Loc_B(D₀.canonicalMap f)`. Identical function as
`iteratedMinus_forwardLocHom`, exposed under an overlap-specific alias. -/
noncomputable def iteratedOverlap_forwardLocHom
    (D₀ : RationalLocData A) (f : A) :
    Localization.Away ((laurentOverlapDatum D₀ f).s) →+*
      Localization.Away (D₀.canonicalMap f) :=
  iteratedMinus_forwardLocHom D₀ f

/-- Forward loc hom acts on `algebraMap a` as the canonical map
`A → B → Loc_B(f_B)`. -/
theorem iteratedOverlap_forwardLocHom_algebraMap
    (D₀ : RationalLocData A) (f a : A) :
    iteratedOverlap_forwardLocHom D₀ f
      (algebraMap A (Localization.Away (laurentOverlapDatum D₀ f).s) a) =
      iteratedMinus_baseHom D₀ f a :=
  iteratedMinus_forwardLocHom_algebraMap D₀ f a

/-! #### Backward loc hom for the iterated overlap

The backward map targets `presheafValue (laurentOverlapDatum D₀ f)`, which
differs from `presheafValue (laurentMinusDatum D₀ f)` (different topologies
on the same underlying ring). We build it via `IsLocalization.Away.lift`
using that `restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub (D₀.canonicalMap f)`
is a unit (since `f ∈ overlap.T` effectively via insertion). -/

/-- The canonical image of `f` is a unit in `presheafValue (laurentOverlapDatum D₀ f)`.
Because `(laurentOverlapDatum D₀ f).s = D₀.s * f`, `algebraMap f` is a unit
in the source localization, hence a unit under `coeRingHom`. -/
theorem canonicalMap_f_isUnit_in_laurentOverlap
    (D₀ : RationalLocData A) (f : A) :
    IsUnit ((laurentOverlapDatum D₀ f).canonicalMap f) := by
  -- Same proof as `canonicalMap_f_isUnit_in_laurentMinus`: `algebraMap f` is a
  -- unit in `Loc_A(D₀.s*f)`, preserved by `coeRingHom`.
  unfold RationalLocData.canonicalMap
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact RingHom.isUnit_map _ (algebraMap_f_isUnit_in_laurentMinus D₀ f)

/-- `restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub (D₀.canonicalMap f)` is a unit. -/
theorem restrictionMap_canonicalMap_f_isUnit_laurentOverlap
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    IsUnit (restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub
      (D₀.canonicalMap f)) := by
  rw [restrictionMapHom_canonicalMap]
  exact canonicalMap_f_isUnit_in_laurentOverlap D₀ f

/-- Backward uncompleted hom `Loc_B(canonicalMap f) →+* presheafValue (laurentOverlap)`.
Mirrors `iteratedMinus_backwardLocHom` but targets the overlap presheafValue. -/
noncomputable def iteratedOverlap_backwardLocHom
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Localization.Away (D₀.canonicalMap f) →+*
      presheafValue (laurentOverlapDatum D₀ f) :=
  IsLocalization.Away.lift (S := Localization.Away (D₀.canonicalMap f))
    (R := presheafValue D₀) (D₀.canonicalMap f)
    (g := restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub)
    (restrictionMap_canonicalMap_f_isUnit_laurentOverlap D₀ f hsub)

theorem iteratedOverlap_backwardLocHom_algebraMap
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (b : presheafValue D₀) :
    iteratedOverlap_backwardLocHom D₀ f hsub
      (algebraMap (presheafValue D₀)
        (Localization.Away (D₀.canonicalMap f)) b) =
      restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub b :=
  IsLocalization.Away.lift_eq (D₀.canonicalMap f)
    (restrictionMap_canonicalMap_f_isUnit_laurentOverlap D₀ f hsub) b

/-- Uncompleted round-trip (overlap branch): backward ∘ forward on Loc_A(D₀.s*f).
Parallels `iteratedMinus_backward_forward_locHom`. -/
theorem iteratedOverlap_backward_forward_locHom
    (D₀ : RationalLocData A) (f : A)
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    (iteratedOverlap_backwardLocHom D₀ f hsub).comp
      (iteratedOverlap_forwardLocHom D₀ f) =
      (laurentOverlapDatum D₀ f).coeRingHom := by
  -- The source Localization.Away ((laurentOverlapDatum D₀ f).s) IS Localization.Away (D₀.s * f)
  -- definitionally, so IsLocalization instance is available.
  apply IsLocalization.ringHom_ext (Submonoid.powers (laurentOverlapDatum D₀ f).s)
  ext a
  change iteratedOverlap_backwardLocHom D₀ f hsub
    (iteratedOverlap_forwardLocHom D₀ f (algebraMap A _ a)) =
    (laurentOverlapDatum D₀ f).coeRingHom (algebraMap A _ a)
  rw [iteratedOverlap_forwardLocHom_algebraMap,
      iteratedMinus_baseHom, RingHom.comp_apply,
      iteratedOverlap_backwardLocHom_algebraMap,
      restrictionMapHom_canonicalMap]
  rfl

/-! #### Backward uncompleted hom via `IsLocalization.Away.lift` at overlap-datum's `.s`

Rather than pushing through type transport between `Loc_B((iteratedOverlapDatum_B).s)`
and `Loc_B(D₀.canonicalMap f)` (which differ because `(iteratedOverlapDatum_B).s =
1 * D₀.canonicalMap f`), we define the backward hom directly at the target
localization type via `IsLocalization.Away.lift`, using the pattern of
`bivariateLocToQuotient_atOverlap`. -/

/-- Backward uncompleted hom `Loc_B((iteratedOverlapDatum_B).s) →+*
presheafValue (laurentOverlapDatum D₀ f)`. -/
noncomputable def iteratedOverlap_backwardToCompletion
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s) :
    Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s) →+*
      presheafValue (laurentOverlapDatum D₀ f) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) := by
    rw [iteratedOverlapDatum_B_s_eq P D₀ f hLocLift_B]; infer_instance
  exact IsLocalization.Away.lift (x := D₀.canonicalMap f)
    (g := restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub)
    (restrictionMap_canonicalMap_f_isUnit_laurentOverlap D₀ f hsub)

/-- Backward hom acts on `algebraMap b` as `restrictionMapHom D₀ overlap hsub b`. -/
theorem iteratedOverlap_backwardToCompletion_algebraMap
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hsub : rationalOpen (laurentOverlapDatum D₀ f).T (laurentOverlapDatum D₀ f).s ⊆
      rationalOpen D₀.T D₀.s)
    (b : presheafValue D₀) :
    iteratedOverlap_backwardToCompletion P D₀ f hLocLift_B hsub
      (algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) b) =
      restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub b := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI : IsLocalization.Away (D₀.canonicalMap f)
      (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) := by
    rw [iteratedOverlapDatum_B_s_eq P D₀ f hLocLift_B]; infer_instance
  change IsLocalization.Away.lift (x := D₀.canonicalMap f)
      (g := restrictionMapHom D₀ (laurentOverlapDatum D₀ f) hsub)
      (restrictionMap_canonicalMap_f_isUnit_laurentOverlap D₀ f hsub)
      (algebraMap (presheafValue D₀)
        (Localization.Away ((iteratedOverlapDatum_B P D₀ f hLocLift_B).s)) b) = _
  rw [IsLocalization.Away.lift_eq]

end IteratedOverlapBridge

/-! ### Composition route: A-side overlap ≃ rational over B_plus via Wedhorn 2.13

**Composition step 1**: apply `presheafValue_iteratedMinus_equiv` at base
`laurentPlusDatum D₀ f` and element `f` to obtain the identification
`presheafValue (laurentOverlapDatum D₀ f) ≃+*`
`presheafValue (iteratedMinusDatum_B P (laurentPlusDatum D₀ f) f)`.

Requires the `laurentPlusDatum D₀ f` to be LaurentNormalized and its locSubring
noetherian, both taken as typeclass hypotheses. These capture the structural
requirement that `f ∈ D₀.P.A₀` (via `LaurentNormalized.insert_s_T_subset_A₀`)
needed to treat `laurentPlusDatum D₀ f` as a rational datum in its own right. -/

section IteratedOverlapCompositionRoute

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
  [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]

/-- **Composition step 1**: Wedhorn 2.13 applied at the plus base gives
`presheafValue (laurentOverlapDatum D₀ f) ≃+*`
`presheafValue (iteratedMinusDatum_B P (laurentPlusDatum D₀ f) f)`.

`laurentOverlapDatum D₀ f = laurentMinusDatum (laurentPlusDatum D₀ f) f` by
definition, so this is a direct specialization of `presheafValue_iteratedMinus_equiv`. -/
noncomputable def presheafValue_iteratedOverlap_as_minus_at_plus
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    [hplus_noeth : IsNoetherianRing (locSubring (laurentPlusDatum D₀ f).P
      (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)]
    [hplus_norm : LaurentNormalized (laurentPlusDatum D₀ f)] :
    presheafValue (laurentOverlapDatum D₀ f) ≃+*
      presheafValue (iteratedMinusDatum_B P (laurentPlusDatum D₀ f) f) :=
  -- `laurentOverlapDatum D₀ f` unfolds to `laurentMinusDatum (laurentPlusDatum D₀ f) f`
  presheafValue_iteratedMinus_equiv P (laurentPlusDatum D₀ f) f

/-- Composition step 1, naturality on `coeRingHom`: the equiv sends
`(laurentOverlapDatum D₀ f).coeRingHom a` (for `a : Loc_A(D₀.s * f)`) to the
image under the underlying forward loc hom + coeRingHom on the B_plus side.

This is a direct unfolding via `presheafValue_iteratedMinus_equiv_coeRingHom`. -/
theorem presheafValue_iteratedOverlap_as_minus_at_plus_coeRingHom
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    [hplus_noeth : IsNoetherianRing (locSubring (laurentPlusDatum D₀ f).P
      (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)]
    [hplus_norm : LaurentNormalized (laurentPlusDatum D₀ f)]
    (a : Localization.Away (laurentMinusDatum (laurentPlusDatum D₀ f) f).s) :
    presheafValue_iteratedOverlap_as_minus_at_plus P D₀ f
        ((laurentMinusDatum (laurentPlusDatum D₀ f) f).coeRingHom a) =
      (iteratedMinusDatum_B P (laurentPlusDatum D₀ f) f).coeRingHom
        (iteratedMinus_forwardLocHom (laurentPlusDatum D₀ f) f a) :=
  presheafValue_iteratedMinus_equiv_coeRingHom P (laurentPlusDatum D₀ f) f a

/-! #### Reusable naturality primitives: `TateAlgebra.mapRingHom` / `mapRingEquiv`

`MvPowerSeries.map` applies a ring hom coefficient-wise. For restricted
subrings, we need the map to preserve `IsRestricted`. A continuous ring hom
satisfies this: coefficients `aₙ → 0` in the source imply `f(aₙ) → f(0) = 0`
in the target.

These primitives port `restrictedPowerSeriesMap` from `ScottishBook/Stated/Problem029.lean`
to a public, reusable form and extend to ring equivs. -/

/-- `MvPowerSeries.map f` preserves `IsRestricted` when `f` is a continuous ring hom. -/
theorem MvPowerSeries_IsRestricted_map_pub {k : ℕ}
    {R S : Type*} [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S]
    {f : R →+* S} (hf : Continuous f) {g : MvPowerSeries (Fin k) R}
    (hg : MvPowerSeries.IsRestricted g) :
    MvPowerSeries.IsRestricted (MvPowerSeries.map f g) := by
  unfold MvPowerSeries.IsRestricted at *
  simp only [MvPowerSeries.coeff_map]
  exact (f.map_zero ▸ hf.tendsto 0).comp hg

/-- The canonical ring homomorphism `TateAlgebra R →+* TateAlgebra S` induced by
a continuous ring hom `f : R →+* S`. Public port of `restrictedPowerSeriesMap`. -/
noncomputable def TateAlgebra_mapRingHom
    {R S : Type u} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
    [CommRing S] [TopologicalSpace S] [NonarchimedeanRing S]
    (f : R →+* S) (hf : Continuous f) :
    ↥(TateAlgebra R) →+* ↥(TateAlgebra S) :=
  (MvPowerSeries.map f).restrict
    (TateAlgebra R) (TateAlgebra S)
    (fun _ hg ↦ MvPowerSeries_IsRestricted_map_pub hf hg)

/-- `TateAlgebra_mapRingHom` action on the underlying MvPowerSeries. -/
theorem TateAlgebra_mapRingHom_val
    {R S : Type u} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
    [CommRing S] [TopologicalSpace S] [NonarchimedeanRing S]
    (f : R →+* S) (hf : Continuous f) (g : ↥(TateAlgebra R)) :
    (TateAlgebra_mapRingHom f hf g).val = MvPowerSeries.map f g.val := rfl

/-- Ring equivalence `TA R ≃+* TA S` induced by a continuous ring equivalence
`e : R ≃+* S` with continuous inverse.

This is the reusable naturality primitive needed for the T-OVERLAP-COMPAT
composition route step 3: transport of `TA (B_plus) ≃+* TA (B₁_gen f_B)` via
`laurentPlusBridge`. -/
noncomputable def TateAlgebra_mapRingEquiv
    {R S : Type u} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
    [CommRing S] [TopologicalSpace S] [NonarchimedeanRing S]
    (e : R ≃+* S) (he : Continuous e) (he_symm : Continuous e.symm) :
    ↥(TateAlgebra R) ≃+* ↥(TateAlgebra S) where
  toFun := TateAlgebra_mapRingHom e.toRingHom he
  invFun := TateAlgebra_mapRingHom e.symm.toRingHom he_symm
  left_inv g := by
    apply Subtype.ext
    show (TateAlgebra_mapRingHom e.symm.toRingHom he_symm
      (TateAlgebra_mapRingHom e.toRingHom he g)).val = g.val
    rw [TateAlgebra_mapRingHom_val, TateAlgebra_mapRingHom_val]
    change MvPowerSeries.map e.symm.toRingHom (MvPowerSeries.map e.toRingHom g.val) = g.val
    rw [← RingHom.comp_apply, ← MvPowerSeries.map_comp]
    change MvPowerSeries.map ((e.symm.toRingHom).comp e.toRingHom) g.val = g.val
    have h_comp : (e.symm.toRingHom).comp e.toRingHom = RingHom.id R := by
      ext x; exact e.symm_apply_apply x
    rw [h_comp, MvPowerSeries.map_id, RingHom.id_apply]
  right_inv g := by
    apply Subtype.ext
    show (TateAlgebra_mapRingHom e.toRingHom he
      (TateAlgebra_mapRingHom e.symm.toRingHom he_symm g)).val = g.val
    rw [TateAlgebra_mapRingHom_val, TateAlgebra_mapRingHom_val]
    change MvPowerSeries.map e.toRingHom (MvPowerSeries.map e.symm.toRingHom g.val) = g.val
    rw [← RingHom.comp_apply, ← MvPowerSeries.map_comp]
    have h_comp : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by
      ext x; exact e.apply_symm_apply x
    rw [h_comp, MvPowerSeries.map_id, RingHom.id_apply]
  map_mul' := map_mul _
  map_add' := map_add _

/-! #### Reusable algebraic naturality primitive (step 3 supporting lemma)

`bivariateOverlap_ideal_eq_mul_swap`: the ideal `(algMap b - X, 1 - X · Y)`
equals `bivariateOverlapIdeal b = (algMap b - X, 1 - algMap b · Y)` in `TA₂ B`.
Follows from `bivariateOverlap_ideal_eq` + the identity `1 - X · Y = -(X · Y - 1)`
applied to the RHS of that lemma.

**Deferred**: the specific ring-level ideal swap in TA₂ B triggers `ring` tactic
heartbeat timeouts when `B` is a polymorphic variable — unfolding `TateAlgebra₂`
+ `restrictedMvPowerSeriesSubring` during normalization is expensive. The
intended proof is a 5-line `le_antisymm` + `neg_mem`, but packaging it in this
file's `IteratedOverlapCompositionRoute` section runs into whnf costs.
The proof is straightforward as inline rewriting in the downstream
`Ideal.quotEquivOfEq` call; see `bivariateOverlap_equiv_B₁₂gen` (line 630+)
for the pattern used in Step B. -/

/-! #### Documented general-purpose missing primitive

For the full T-OVERLAP-COMPAT composition route (step 3), we need a
reusable `TateAlgebra_mapRingEquiv` (or equivalently `TateAlgebra_of_quotient_equiv`)
that transports TateAlgebra constructions along a ring equivalence of the base.

**Target statement** (missing Mathlib/project-level primitive):

```lean
noncomputable def TateAlgebra_mapRingEquiv
    {R S : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
    [CommRing S] [TopologicalSpace S] [NonarchimedeanRing S]
    (e : R ≃+* S) (he : Continuous e) (he_symm : Continuous e.symm) :
    ↥(TateAlgebra R) ≃+* ↥(TateAlgebra S)
```

or equivalently:

```lean
noncomputable def TateAlgebra_of_quotient_equiv
    {R : Type*} [CommRing R] [TopologicalSpace R] [NonarchimedeanRing R]
    (I : Ideal R) (hI_closed : IsClosed (I : Set R)) :
    ↥(TateAlgebra (R ⧸ I)) ≃+* ↥(TateAlgebra R) ⧸ Ideal.map
      (algebraMap R ↥(TateAlgebra R)) I
```

**Construction outline**:
- Forward via `MvPowerSeries.map (Ideal.Quotient.mk I) : MvPowerSeries σ R → MvPowerSeries σ (R/I)`
  restricted to `IsRestricted` elements (preservation uses continuity of `Ideal.Quotient.mk`).
- Backward via choice function `R/I → R` lifting coefficients; restrictedness
  preserved up to `I`-translate (which vanishes in the quotient).
- Kernel of forward = `{series with coeffs in I}` = `Ideal.map (algebraMap R _) I`
  (using closedness of I for noetherian completion).

**Estimated lines**: ~80 for the ring equiv + `~40` for IsRestricted preservation
+ `~60` for kernel identification = ~180 lines of Mathlib-style proof.

**Why not landed here**: depends on the `MvPowerSeries.map` package's behavior
on restricted subrings, which in turn depends on `continuous_quotient_mk` for
the topology on `R ⧸ I` — this chain isn't currently assembled in the project,
and building it is a multi-primitive development analogous to the full
`presheafValueTateQuotientEquiv` pipeline in `TopologyComparison.lean`.

With this primitive in place, Step 3 of the composition route
(`B₂_gen(canonicalMap_plus f) ≃+* B₁₂_gen f_B`) becomes:
- Apply `TateAlgebra_mapRingEquiv` to `laurentPlusBridge` to get
  `TA B_plus ≃+* TA (B₁_gen f_B)`.
- Apply `TateAlgebra_of_quotient_equiv` to `TA (TA B ⧸ (algMap f_B - X))`
  to get `≃+* TA₂ B ⧸ (algMap f_B - X_1)`.
- Apply third-iso-theorem to identify the combined quotient with
  `TA₂ B ⧸ (algMap f_B - X_1, 1 - X_1 · X_2)`.
- Apply `bivariateOverlap_ideal_eq_mul_swap` to rewrite to
  `bivariateOverlapIdeal f_B`.
- Apply `bivariateOverlap_equiv_B₁₂gen` to finish.

Until the primitive is landed, Step 3 remains a precise math blocker. -/

/-- **Composition step 2**: apply `laurentMinusBridge` at the plus base to get
`presheafValue (laurentOverlapDatum D₀ f) ≃+* B₂_gen ((laurentPlusDatum D₀ f).canonicalMap f)`. -/
noncomputable def presheafValue_iteratedOverlap_to_B₂_at_plus
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    [hplus_noeth : IsNoetherianRing (locSubring (laurentPlusDatum D₀ f).P
      (laurentPlusDatum D₀ f).T (laurentPlusDatum D₀ f).s)]
    [hplus_norm : LaurentNormalized (laurentPlusDatum D₀ f)]
    (hnoeth_B_plus : letI : IsTateRing (presheafValue (laurentPlusDatum D₀ f)) :=
        presheafValue_isTateRing P (laurentPlusDatum D₀ f)
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue (laurentPlusDatum D₀ f))).toPairOfDefinition))
    (hcont_eval_B_plus : letI : IsTateRing (presheafValue (laurentPlusDatum D₀ f)) :=
        presheafValue_isTateRing P (laurentPlusDatum D₀ f)
      let D : RationalLocData (presheafValue (laurentPlusDatum D₀ f)) :=
        iteratedMinusDatum_B P (laurentPlusDatum D₀ f) f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb)) :
    presheafValue (laurentOverlapDatum D₀ f) ≃+*
      LaurentCover.B₂_gen ((laurentPlusDatum D₀ f).canonicalMap f) :=
  -- `laurentOverlapDatum D₀ f = laurentMinusDatum (laurentPlusDatum D₀ f) f` definitionally.
  laurentMinusBridge P (laurentPlusDatum D₀ f) f hnoeth_B_plus hcont_eval_B_plus

/-! #### Continuity primitives for `laurentPlusBridge`

Both directions of `laurentPlusBridge` are continuous — the forward direction
from structural `UniformSpace.Completion.continuous_extension`, the inverse
from the same plus continuity required as a hypothesis to build the bridge
(`hcont_forward_B`). These are the exact primitives needed by
`TateAlgebra_mapRingEquiv` to transport Tate algebras across the bridge,
closing the Step 3 blocker of T-OVERLAP-COMPAT.

The two completion-extension continuity primitives
`iteratedPlus_forwardHom_continuous` and `iteratedPlus_backwardHom_continuous`
live upstream in `Adic spaces/LaurentRefinement.lean` (T146); the wrappers
below thread them through to the equiv level. -/

/-- `presheafValue_iteratedPlus_equiv` is continuous (its underlying function
equals `iteratedPlus_forwardHom`). -/
theorem presheafValue_iteratedPlus_equiv_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    Continuous (presheafValue_iteratedPlus_equiv P D₀ f) :=
  iteratedPlus_forwardHom_continuous P D₀ f

/-- `presheafValue_iteratedPlus_equiv.symm` is continuous. -/
theorem presheafValue_iteratedPlus_equiv_symm_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A) :
    Continuous (presheafValue_iteratedPlus_equiv P D₀ f).symm :=
  iteratedPlus_backwardHom_continuous P D₀ f (laurentPlus_subset D₀ f)

/-- `example638Plus_backwardHom` is continuous (from `presheafValue` canonical
topology to `quotientPlusFSubXIdealTopology` on the target) —
`UniformSpace.Completion.extensionHom` of a continuous ring hom, so continuous
by `continuous_extension`. -/
theorem example638Plus_backwardHom_continuous
    {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
    [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition)) :
    @Continuous _ _
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (quotientPlusFSubXIdealTopology B b)
      (example638Plus_backwardHom B P b hA_complete hnoeth) := by
  letI : UniformSpace (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).isTopologicalRing
  letI : TopologicalSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology B b
  letI : IsTopologicalRing (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology_isTopologicalRing B b
  letI : IsTopologicalAddGroup (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology_isTopologicalAddGroup B b
  letI : UniformSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealUniformSpace B b
  letI : IsUniformAddGroup (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdeal_isUniformAddGroup B b
  haveI : CompleteSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotient_plusFSubXIdeal_completeSpace B hA_complete hnoeth b
  exact UniformSpace.Completion.continuous_extension

/-- `presheafValue_trivialPlus_fSubX_equiv` is continuous — its underlying
function is `example638Plus_equiv.symm.toFun = example638Plus_backwardHom`,
hence continuous by `example638Plus_backwardHom_continuous`. -/
theorem presheafValue_trivialPlus_fSubX_equiv_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f))) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    @Continuous _ _
      (inferInstance : TopologicalSpace (presheafValue (iteratedPlusDatum_B P D₀ f)))
      (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
      (presheafValue_trivialPlus_fSubX_equiv P D₀ f
        hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  haveI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
  haveI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
  letI P_B : PairOfDefinition (presheafValue D₀) :=
    presheafValue_pairOfDefinition_concrete P D₀
  haveI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
  -- presheafValue_trivialPlus_fSubX_equiv = (example638Plus_equiv _ _ _ ... _).symm.
  -- Its toFun = example638Plus_backwardHom.
  exact example638Plus_backwardHom_continuous P_B (D₀.canonicalMap f)
    hA_complete_B hnoeth_B

/-- `presheafValue_trivialPlus_fSubX_equiv.symm` is continuous — follows from
`hcont_forward_B` (the hypothesis on `example638Plus_forwardHom`'s continuity),
since `.symm.toFun = example638Plus_forwardHom`. -/
theorem presheafValue_trivialPlus_fSubX_equiv_symm_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f))) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    @Continuous _ _
      (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
      (inferInstance : TopologicalSpace (presheafValue (iteratedPlusDatum_B P D₀ f)))
      (presheafValue_trivialPlus_fSubX_equiv P D₀ f
        hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B).symm :=
  -- `.symm` of `example638Plus_equiv.symm` is `example638Plus_equiv` itself,
  -- whose toFun is `example638Plus_forwardHom`. Continuity = hcont_forward_B.
  hcont_forward_B

/-- **`laurentPlusBridge` is continuous** — composition of two continuous pieces
(`presheafValue_iteratedPlus_equiv` and `presheafValue_trivialPlus_fSubX_equiv`),
both extensionHom-based, so no `hcont_forward_B` dependency for THIS direction.

Enables `TateAlgebra_mapRingEquiv` at the laurentPlusBridge for the T-OVERLAP-COMPAT
Step 3 construction. -/
theorem laurentPlusBridge_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f))) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    @Continuous _ _
      (inferInstance : TopologicalSpace (presheafValue (laurentPlusDatum D₀ f)))
      (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
      (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
        hA_complete_B hnoeth_B hcont_forward_B) := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  -- laurentPlusBridge = iteratedPlus_equiv.trans trivialPlus_fSubX_equiv.
  -- Continuous ∘ Continuous = Continuous.
  exact (presheafValue_trivialPlus_fSubX_equiv_continuous P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B).comp
    (presheafValue_iteratedPlus_equiv_continuous P D₀ f)

/-- **`laurentPlusBridge.symm` is continuous** — uses `hcont_forward_B`
(the hypothesis present in the bridge's constructor) for the plus-side
forward continuity, combined with the structural continuity of the
iteratedPlus backward hom. -/
theorem laurentPlusBridge_symm_continuous
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f))) :
    letI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
    @Continuous _ _
      (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
      (inferInstance : TopologicalSpace (presheafValue (laurentPlusDatum D₀ f)))
      (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B
        hA_complete_B hnoeth_B hcont_forward_B).symm := by
  haveI : IsTateRing (presheafValue D₀) := presheafValue_isTateRing P D₀
  -- laurentPlusBridge.symm = trivialPlus_fSubX_equiv.symm.trans iteratedPlus_equiv.symm.
  exact (presheafValue_iteratedPlus_equiv_symm_continuous P D₀ f).comp
    (presheafValue_trivialPlus_fSubX_equiv_symm_continuous P D₀ f
      hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B)

end IteratedOverlapCompositionRoute

/-! ### Specialized Laurent-overlap quotient bridge (T-OV-1 Step 3 primitive)

Goal: build the forward direction of
`TateAlgebra (B₁_gen b) ⧸ (1 - Ybar · X_out) ≃+* TA₂ B ⧸ bivariateOverlapIdeal b`.

Forward construction:
1. `evalHom_TA_B_to_bivariateOverlap`: `TA B →+* TA₂ B ⧸ bivariateOverlapIdeal b`
   via `evalHomBounded` sending `X ↦ mk X_{2,1}` and constants `algMap a ↦ mk (algMap a)`.
2. Kills `algMap b - X` (both sides give `mk(algMap b) = mk X_{2,1}` in the overlap quotient).
3. Factor through `plusFSubXIdeal b` to get `baseHom : B₁_gen b →+* target`.
4. `TA_B₁_gen_to_bivariateOverlap_evalHom`: `TA(B₁_gen b) →+* target` via another
   `evalHomBounded` using `baseHom` and `X_out ↦ mk X_{2,2}`.
5. Kills `(1 - Ybar · X_out)`: maps to `1 - mk(X_{2,1}) · mk(X_{2,2})`, which
   equals 0 in the overlap quotient (via `bivariateOverlap_ideal_eq` modulo
   negation of the second generator).
6. Factor through the outer ideal to get the full forward hom.

This session: lands the first-stage evalHom (step 1 above) with its generator
action lemmas. Remaining steps 2–6 will follow as named reusable API.

## Public caller-facing API (Lane A finish line, 2026-04-21)

The specialized Laurent-overlap bridge is complete. Downstream callers have
three entry points, from most specialized to most convenient:

1. **`TA_B₁_gen_quotient_specialized_equiv_of_inputs`** — the core
   parametric `RingEquiv`
   `TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b ≃+* TA₂ B ⧸ bivariateOverlapIdeal b`.
   Takes all five hypotheses separately.

2. **`TA_B₁_gen_quotient_to_B₁₂_gen_equiv`** — composes (1) with the Primary
   algebraic identification `bivariateOverlap_equiv_B₁₂gen` to produce
   `TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b ≃+* LaurentCover.B₁₂_gen b`.
   Takes all five hypotheses separately.

3. **`specializedOverlapBridge`** — same equiv as (2) but takes a single
   `SpecializedOverlapBridgeInputs` bundle. **Recommended for downstream.**

And one exported finish theorem bridging into the downstream consumer API:

4. **`laurentOverlapBridge_exists_compatible_via_primary`** — specializes
   `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
   (LaurentRefinement) by binding `τ_alg := bivariateOverlap_equiv_B₁₂gen`.
   Caller provides `τ_preBiv` + two intertwining witnesses; this theorem
   threads them through to produce the `LaurentOverlapBridgeCompatible`
   witness required by downstream gluing arguments.

**Single remaining mathematical residual**: `ReverseRoundTripInputs.hDense` —
polynomial density on `TA(B₁_gen b)` (the canonical Tate topology). All
decomposition hypotheses are now discharged internally via
`tateAlgebra_polynomial_decomp`.
-/

section TA_B₁_gen_quotient_bridge

variable {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]
  [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

/-- The first-stage evaluation: `TA B →+* TA₂ B ⧸ bivariateOverlapIdeal b`
sending the single TA variable `X` to `mk TateAlgebra₂.X` (the image of the
first bivariate variable), and constants `algebraMap a ↦ mk (algebraMap a)`.

Built via `TateAlgebraWedhorn.evalHomBounded` using:
* base map `mk ∘ algebraMap B (TA₂ B)` (continuous via `mk_algebraMap_continuous_bivariateOverlap`);
* target element `mk TateAlgebra₂.X` (power-bounded via `mk_X_isPowerBounded_in_bivariateOverlap`).

This is the primitive that lets us factor `plusFSubXIdeal b = (algebraMap b - X)`
through the quotient, giving `B₁_gen b → TA₂ B ⧸ bivariateOverlapIdeal b` in the
next step. -/
noncomputable def TA_B_to_bivariateOverlap_evalHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition)) :
    ↥(TateAlgebra B) →+*
      ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b := by
  letI topQ : TopologicalSpace
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  letI ringQ : IsTopologicalRing
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b
  letI addQ : IsTopologicalAddGroup
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b
  letI usQ : UniformSpace
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealUniformSpace b
  haveI : IsUniformAddGroup
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    @isUniformAddGroup_of_addCommGroup _ _ topQ addQ
  haveI : NonarchimedeanRing
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_nonarchimedean b
  haveI : CompleteSpace
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_completeSpace hA_complete hnoeth b
  haveI hT2Q : T2Space
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_t2Space hA_complete hnoeth b
  haveI : T0Space
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    T2Space.t1Space.t0Space
  -- Base map: `mk ∘ algebraMap B (TA₂ B) : B → TA₂ B ⧸ bivariateOverlapIdeal b`.
  let baseMap : B →+* (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)).comp
      (algebraMap B ↥(TateAlgebra₂ B))
  have hbaseMap_cont : Continuous baseMap :=
    TateAlgebra.mk_algebraMap_continuous_bivariateOverlap b
  -- Target element: `mk TateAlgebra₂.X`, power-bounded.
  let tgtElt : ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b :=
    Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b) TateAlgebra₂.X
  have htgtElt_pb : TopologicalRing.IsPowerBounded tgtElt :=
    TateAlgebra.mk_X_isPowerBounded_in_bivariateOverlap b
  exact TateAlgebraWedhorn.evalHomBounded baseMap hbaseMap_cont tgtElt htgtElt_pb

/-- The first-stage evalHom sends `algebraMap a` to `mk (algebraMap a)`.

Proof pattern mirrors `example638Plus_evalHom_algebraMap`: expand `evalHomBounded`
as `∑' n, evalTerm n`, reduce via `tsum_eq_single 0`, and compute the `n = 0`
coefficient of `algebraMap` via `MvPowerSeries.coeff_C`. -/
theorem TA_B_to_bivariateOverlap_evalHom_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (a : B) :
    TA_B_to_bivariateOverlap_evalHom P b hA_complete hnoeth
        (algebraMap B ↥(TateAlgebra B) a) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
        (algebraMap B ↥(TateAlgebra₂ B) a) := by
  unfold TA_B_to_bivariateOverlap_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 0]
  · unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    simp only [Finsupp.single_zero, pow_zero, mul_one]
    change ((Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)).comp
      (algebraMap B ↥(TateAlgebra₂ B)))
        ((MvPowerSeries.coeff (R := B) 0)
          (↑(algebraMap B ↥(TateAlgebra B) a) : MvPowerSeries (Fin 1) B)) = _
    change ((Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)).comp
      (algebraMap B ↥(TateAlgebra₂ B)))
        ((MvPowerSeries.coeff (R := B) 0)
          (MvPowerSeries.C (σ := Fin 1) a)) = _
    classical
    rw [MvPowerSeries.coeff_C, if_pos rfl]
    rfl
  · intro n hn
    unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    have h0 : (MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (↑(algebraMap B ↥(TateAlgebra B) a) : MvPowerSeries (Fin 1) B) = 0 := by
      change (MvPowerSeries.coeff (Finsupp.single 0 n))
        (MvPowerSeries.C (σ := Fin 1) a) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg (Finsupp.single_ne_zero.mpr hn)]
    rw [h0, RingHom.map_zero, zero_mul]

/-- The first-stage evalHom sends `TateAlgebra.X` to `mk TateAlgebra₂.X`.

Proof pattern mirrors `example638Plus_evalHom_X`: expand `evalHomBounded`,
use `tsum_eq_single 1`, and compute the coefficient of `X` at `Finsupp.single 0 1`. -/
theorem TA_B_to_bivariateOverlap_evalHom_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition)) :
    TA_B_to_bivariateOverlap_evalHom P b hA_complete hnoeth TateAlgebra.X =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) TateAlgebra₂.X := by
  unfold TA_B_to_bivariateOverlap_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 1]
  · simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X, pow_one]
    -- coefficient of X at Finsupp.single 0 1 is 1.
    change ((Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)).comp
      (algebraMap B ↥(TateAlgebra₂ B)))
        ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 1))
          (MvPowerSeries.X 0)) *
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) TateAlgebra₂.X = _
    rw [MvPowerSeries.coeff_X, if_pos rfl, RingHom.map_one, one_mul]
  · intro n hn
    simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X]
    -- coefficient of X at Finsupp.single 0 n is 0 for n ≠ 1.
    change ((Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)).comp
      (algebraMap B ↥(TateAlgebra₂ B)))
        ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
          (MvPowerSeries.X 0)) * _ = _
    classical
    rw [MvPowerSeries.coeff_X]
    have hne : (Finsupp.single (0 : Fin 1) n : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 1 := by
      intro h
      have := congrArg (fun f : Fin 1 →₀ ℕ ↦ f 0) h
      simp at this
      exact hn this
    simp only [if_neg hne, map_zero]
    exact zero_mul _

/-! #### Step 2: factor through `plusFSubXIdeal b` to get `B₁_gen b → target`

The forward `TA_B_to_bivariateOverlap_evalHom` kills `plusFSubXIdeal b =
(algebraMap b - X)` because `evalHom(algebraMap b) - evalHom(X) = mk(algebraMap b) - mk(X) = 0`
in `TA₂ B ⧸ bivariateOverlapIdeal b` (by
`TateAlgebra.quotient_algebraMap_b_eq_X_bivariate`). -/

theorem TA_B_to_bivariateOverlap_evalHom_plusFSubX_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition)) :
    TA_B_to_bivariateOverlap_evalHom P b hA_complete hnoeth
      (algebraMap B ↥(TateAlgebra B) b - TateAlgebra.X) = 0 := by
  rw [map_sub, TA_B_to_bivariateOverlap_evalHom_algebraMap,
    TA_B_to_bivariateOverlap_evalHom_X,
    TateAlgebra.quotient_algebraMap_b_eq_X_bivariate]
  exact sub_self _

/-- Forward hom `B₁_gen b →+* TA₂ B ⧸ bivariateOverlapIdeal b`: factored from
`TA_B_to_bivariateOverlap_evalHom` through `plusFSubXIdeal b`. -/
noncomputable def baseHom_B₁_gen_to_bivariateOverlap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition)) :
    LaurentCover.B₁_gen b →+*
      ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b := by
  refine Ideal.Quotient.lift _ (TA_B_to_bivariateOverlap_evalHom P b hA_complete hnoeth)
    (fun y hy ↦ ?_)
  have h_le : Ideal.span
        {algebraMap B ↥(TateAlgebra B) b - TateAlgebra.X} ≤
      RingHom.ker (TA_B_to_bivariateOverlap_evalHom P b hA_complete hnoeth) := by
    rw [Ideal.span_le]
    rintro z (rfl : _ = _)
    exact TA_B_to_bivariateOverlap_evalHom_plusFSubX_eq_zero P b hA_complete hnoeth
  exact h_le hy

/-- `baseHom_B₁_gen_to_bivariateOverlap` on `mk(algebraMap a)` equals
`mk(algebraMap a)`. -/
theorem baseHom_B₁_gen_to_bivariateOverlap_mk_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (a : B) :
    baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth
        ((Ideal.Quotient.mk (plusFSubXIdeal B b))
          (algebraMap B ↥(TateAlgebra B) a)) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
        (algebraMap B ↥(TateAlgebra₂ B) a) := by
  change Ideal.Quotient.lift _ (TA_B_to_bivariateOverlap_evalHom P b hA_complete hnoeth) _
      (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk]
  exact TA_B_to_bivariateOverlap_evalHom_algebraMap P b hA_complete hnoeth a

/-- `baseHom_B₁_gen_to_bivariateOverlap` on `mk(TateAlgebra.X)` equals
`mk(TateAlgebra₂.X)` (which also equals `mk(algebraMap b)` via
`TateAlgebra.quotient_algebraMap_b_eq_X_bivariate`). -/
theorem baseHom_B₁_gen_to_bivariateOverlap_mk_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition)) :
    baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth
        ((Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) TateAlgebra₂.X := by
  change Ideal.Quotient.lift _ (TA_B_to_bivariateOverlap_evalHom P b hA_complete hnoeth) _
      (Ideal.Quotient.mk _ TateAlgebra.X) = _
  rw [Ideal.Quotient.lift_mk]
  exact TA_B_to_bivariateOverlap_evalHom_X P b hA_complete hnoeth

/-! #### Step 3: outer `evalHomBounded` on `TA(B₁_gen b)`

Uses `baseHom_B₁_gen_to_bivariateOverlap` (continuity taken as hypothesis,
mirroring `example638Plus_equiv.hcont_forward`) and target element
`mk TateAlgebra₂.Y` (power-bounded via
`TateAlgebra.mk_Y_isPowerBounded_in_bivariateOverlap`). Requires
`NonarchimedeanRing (B₁_gen b)` as a source instance — extracted below. -/

/-- `B₁_gen b = TateAlgebra B ⧸ plusFSubXIdeal b` is a nonarchimedean ring
under `quotientPlusFSubXIdealTopology`. Extracts the pattern inlined at
`Example638.lean:529` into a reusable named lemma. -/
theorem B₁_gen_nonarchimedeanRing (b : B) :
    @NonarchimedeanRing (LaurentCover.B₁_gen b)
      _ (quotientPlusFSubXIdealTopology B b) := by
  letI : TopologicalSpace (LaurentCover.B₁_gen b) :=
    quotientPlusFSubXIdealTopology B b
  letI hring : IsTopologicalRing (LaurentCover.B₁_gen b) :=
    quotientPlusFSubXIdealTopology_isTopologicalRing B b
  haveI hNA_tate : @NonarchimedeanRing ↥(TateAlgebra B) _
      TateAlgebra.instTopologicalSpaceTateAlgebra :=
    TateAlgebra.tateAlgBasis'.nonarchimedean
  constructor; intro U hU
  have hcont : @Continuous _ _ TateAlgebra.instTopologicalSpaceTateAlgebra
      (quotientPlusFSubXIdealTopology B b)
      (Ideal.Quotient.mk (plusFSubXIdeal B b)) :=
    continuous_quotient_mk'
  have hU' : (Ideal.Quotient.mk (plusFSubXIdeal B b)) ⁻¹' (U : Set _) ∈
      @nhds _ TateAlgebra.instTopologicalSpaceTateAlgebra (0 : ↥(TateAlgebra B)) :=
    hcont.continuousAt.preimage_mem_nhds hU
  obtain ⟨V, hVU⟩ := @NonarchimedeanRing.is_nonarchimedean _ _ _ hNA_tate _ hU'
  exact ⟨{
    toAddSubgroup := V.toAddSubgroup.map
      (Ideal.Quotient.mk (plusFSubXIdeal B b)).toAddMonoidHom
    isOpen' := @QuotientRing.isOpenMap_coe _ TateAlgebra.instTopologicalSpaceTateAlgebra _
      (plusFSubXIdeal B b) TateAlgebra.instIsTopologicalRingTateAlgebra _ V.isOpen
  }, fun x hx ↦ by obtain ⟨y, hy, rfl⟩ := hx; exact hVU hy⟩

/-- Local `TopologicalSpace` instance for `LaurentCover.B₁_gen b`, needed for
the specialized quotient bridge signatures that mention `TateAlgebra (B₁_gen b)`. -/
noncomputable local instance B₁_gen_topologicalSpace (b : B) :
    TopologicalSpace (LaurentCover.B₁_gen b) :=
  quotientPlusFSubXIdealTopology B b

/-- Local `NonarchimedeanRing` instance for `LaurentCover.B₁_gen b`, needed for
forming `TateAlgebra (B₁_gen b)` in signatures. -/
noncomputable local instance B₁_gen_nonarchimedeanRing_inst (b : B) :
    NonarchimedeanRing (LaurentCover.B₁_gen b) :=
  B₁_gen_nonarchimedeanRing b

/-- Outer evaluation hom `TA(B₁_gen b) →+* TA₂ B ⧸ bivariateOverlapIdeal b`
sending `algebraMap(α) ↦ baseHom(α)` (for `α : B₁_gen b`) and the outer TA
variable `X_out ↦ mk TateAlgebra₂.Y`.

Conditional on `hcont_base : Continuous baseHom_B₁_gen_to_bivariateOverlap`
(mirroring `example638Plus_equiv.hcont_forward` pattern). -/
noncomputable def TA_B₁_gen_to_bivariateOverlap_outer_evalHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_base : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth)) :
    ↥(TateAlgebra (LaurentCover.B₁_gen b)) →+*
      ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b := by
  letI topB₁ : TopologicalSpace (LaurentCover.B₁_gen b) :=
    quotientPlusFSubXIdealTopology B b
  haveI ringB₁ : IsTopologicalRing (LaurentCover.B₁_gen b) :=
    quotientPlusFSubXIdealTopology_isTopologicalRing B b
  haveI naB₁ : NonarchimedeanRing (LaurentCover.B₁_gen b) := B₁_gen_nonarchimedeanRing b
  letI topQ : TopologicalSpace
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology b
  letI ringQ : IsTopologicalRing
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalRing b
  letI addQ : IsTopologicalAddGroup
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_isTopologicalAddGroup b
  letI usQ : UniformSpace
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealUniformSpace b
  haveI : IsUniformAddGroup
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    @isUniformAddGroup_of_addCommGroup _ _ topQ addQ
  haveI : NonarchimedeanRing
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotientBivariateOverlapIdealTopology_nonarchimedean b
  haveI : CompleteSpace
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_completeSpace hA_complete hnoeth b
  haveI hT2Q : T2Space
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    TateAlgebra.quotient_bivariateOverlapIdeal_t2Space hA_complete hnoeth b
  haveI : T0Space
      (↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) :=
    T2Space.t1Space.t0Space
  -- Target element: `mk TateAlgebra₂.Y`, power-bounded.
  let tgtElt : ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b :=
    Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b) TateAlgebra₂.Y
  have htgtElt_pb : TopologicalRing.IsPowerBounded tgtElt :=
    TateAlgebra.mk_Y_isPowerBounded_in_bivariateOverlap b
  exact TateAlgebraWedhorn.evalHomBounded
    (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth)
    hcont_base tgtElt htgtElt_pb

/-- Outer evalHom action on `algebraMap_{TA(B₁_gen b)} α` for `α : B₁_gen b`:
equals `baseHom α`. -/
theorem TA_B₁_gen_to_bivariateOverlap_outer_evalHom_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_base : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth))
    (α : LaurentCover.B₁_gen b) :
    TA_B₁_gen_to_bivariateOverlap_outer_evalHom P b hA_complete hnoeth hcont_base
        (algebraMap (LaurentCover.B₁_gen b) _ α) =
      baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth α := by
  unfold TA_B₁_gen_to_bivariateOverlap_outer_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 0]
  · unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    simp only [Finsupp.single_zero, pow_zero, mul_one]
    -- coeff 0 of algebraMap α is α itself.
    change baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth
      ((MvPowerSeries.coeff (R := LaurentCover.B₁_gen b) 0)
        (↑(algebraMap (LaurentCover.B₁_gen b) ↥(TateAlgebra (LaurentCover.B₁_gen b)) α) :
          MvPowerSeries (Fin 1) (LaurentCover.B₁_gen b))) = _
    change baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth
      ((MvPowerSeries.coeff (R := LaurentCover.B₁_gen b) 0)
        (MvPowerSeries.C (σ := Fin 1) α)) = _
    classical
    rw [MvPowerSeries.coeff_C, if_pos rfl]
  · intro n hn
    unfold TateAlgebraWedhorn.evalTerm TateAlgebra.coeff TateAlgebra.toIndex
    have h0 : (MvPowerSeries.coeff (R := LaurentCover.B₁_gen b) (Finsupp.single 0 n))
        (↑(algebraMap (LaurentCover.B₁_gen b) ↥(TateAlgebra (LaurentCover.B₁_gen b)) α) :
          MvPowerSeries (Fin 1) (LaurentCover.B₁_gen b)) = 0 := by
      classical
      change (MvPowerSeries.coeff (Finsupp.single 0 n))
        (MvPowerSeries.C (σ := Fin 1) α) = 0
      rw [MvPowerSeries.coeff_C]
      exact if_neg (Finsupp.single_ne_zero.mpr hn)
    rw [h0, map_zero]
    exact zero_mul _

/-- Outer evalHom action on `TateAlgebra.X` (the TA variable of `TA(B₁_gen b)`):
equals `mk TateAlgebra₂.Y`. -/
theorem TA_B₁_gen_to_bivariateOverlap_outer_evalHom_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_base : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth)) :
    TA_B₁_gen_to_bivariateOverlap_outer_evalHom P b hA_complete hnoeth hcont_base
        TateAlgebra.X =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) TateAlgebra₂.Y := by
  unfold TA_B₁_gen_to_bivariateOverlap_outer_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 1]
  · simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X, pow_one]
    change baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth
        ((MvPowerSeries.coeff (R := LaurentCover.B₁_gen b) (Finsupp.single 0 1))
          (MvPowerSeries.X 0)) *
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) TateAlgebra₂.Y = _
    rw [MvPowerSeries.coeff_X, if_pos rfl, RingHom.map_one, one_mul]
  · intro n hn
    simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X]
    change baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth
        ((MvPowerSeries.coeff (R := LaurentCover.B₁_gen b) (Finsupp.single 0 n))
          (MvPowerSeries.X 0)) * _ = _
    classical
    rw [MvPowerSeries.coeff_X]
    have hne : (Finsupp.single (0 : Fin 1) n : Fin 1 →₀ ℕ) ≠ Finsupp.single 0 1 := by
      intro h
      have := congrArg (fun f : Fin 1 →₀ ℕ ↦ f 0) h
      simp at this
      exact hn this
    simp only [if_neg hne, map_zero]
    exact zero_mul _

/-! #### Step 4: factor through the outer ideal `(1 - Ybar · X_out)` -/

-- Bumped from defaults: bivariate Laurent overlap quotient construction
-- exercises iterated typeclass synthesis through nested completions +
-- TateAlgebra quotients; default heartbeats insufficient.
/-- The outer ideal's generator `1 - Ybar · X_out` maps to 0 under the outer
evalHom, where `Ybar = mk(TateAlgebra.X) ∈ B₁_gen b` and `X_out = TateAlgebra.X`
is the outer TA variable.

The image is `1 - mk(TateAlgebra₂.X) · mk(TateAlgebra₂.Y) = 0` in
`TA₂ B ⧸ bivariateOverlapIdeal b` (via `bivariateOverlap_ideal_eq` — the
generator `1 - algMap b · Y ∈ bivariateOverlapIdeal b` combined with
`algMap b ≡ TateAlgebra₂.X` modulo the other generator, giving
`1 - X · Y ∈ ideal`, i.e., `mk(X · Y) = 1`). -/
theorem TA_B₁_gen_to_bivariateOverlap_outer_evalHom_oneSub_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_base : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth)) :
    TA_B₁_gen_to_bivariateOverlap_outer_evalHom P b hA_complete hnoeth hcont_base
      ((1 : ↥(TateAlgebra (LaurentCover.B₁_gen b))) -
        algebraMap (LaurentCover.B₁_gen b) ↥(TateAlgebra (LaurentCover.B₁_gen b))
          ((Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X) *
        TateAlgebra.X) = 0 := by
  rw [map_sub, map_one, map_mul,
      TA_B₁_gen_to_bivariateOverlap_outer_evalHom_algebraMap,
      TA_B₁_gen_to_bivariateOverlap_outer_evalHom_X,
      baseHom_B₁_gen_to_bivariateOverlap_mk_X]
  -- Goal: 1 - mk X * mk Y = 0 in TA₂ B ⧸ bivariateOverlapIdeal b.
  -- Rewrite 1 = mk 1 and mk X * mk Y = mk (X * Y), then use eq_zero_iff_mem.
  rw [show (1 : ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b) =
      Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b) 1 from rfl,
    ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  -- Goal: 1 - TA₂.X * TA₂.Y ∈ bivariateOverlapIdeal b
  have h_eq : (1 : ↥(TateAlgebra₂ B)) - TateAlgebra₂.X * TateAlgebra₂.Y =
      (1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y) +
        TateAlgebra₂.Y * (algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X) := by
    ring
  rw [h_eq]
  refine add_mem ?_ ?_
  · exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))

/-- **Outer ideal for the specialized Laurent-overlap quotient bridge**:
`1 - Ybar · X_out` in `TA(B₁_gen b)` where `Ybar = mk(TateAlgebra.X) ∈ B₁_gen b`
and `X_out = TateAlgebra.X` is the outer TA variable. -/
noncomputable def outerLaurentOverlapIdeal (b : B) :
    Ideal ↥(TateAlgebra (LaurentCover.B₁_gen b)) :=
  Ideal.span {
    (1 : ↥(TateAlgebra (LaurentCover.B₁_gen b))) -
      algebraMap (LaurentCover.B₁_gen b) ↥(TateAlgebra (LaurentCover.B₁_gen b))
        ((Ideal.Quotient.mk (plusFSubXIdeal B b)) (TateAlgebra.X (A := B))) *
      (TateAlgebra.X (A := LaurentCover.B₁_gen b))
  }

/-- **Specialized Laurent-overlap quotient bridge, forward direction**:
`TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b →+* TA₂ B ⧸ bivariateOverlapIdeal b`.

Factored from `TA_B₁_gen_to_bivariateOverlap_outer_evalHom` through the outer
ideal using the kernel lemma above. -/
noncomputable def TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_base : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth)) :
    ↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b →+*
      ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b := by
  refine Ideal.Quotient.lift _
    (TA_B₁_gen_to_bivariateOverlap_outer_evalHom P b hA_complete hnoeth hcont_base)
    (fun y hy ↦ ?_)
  have h_le : outerLaurentOverlapIdeal b ≤
      RingHom.ker (TA_B₁_gen_to_bivariateOverlap_outer_evalHom P b hA_complete hnoeth
        hcont_base) := by
    unfold outerLaurentOverlapIdeal
    rw [Ideal.span_le]
    rintro z (rfl : _ = _)
    exact TA_B₁_gen_to_bivariateOverlap_outer_evalHom_oneSub_eq_zero
      P b hA_complete hnoeth hcont_base
  exact h_le hy

/-! #### Step 5: action lemmas for the specialized forward quotient bridge

These describe how `TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom` acts on
the images of the three natural generators of
`TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b` (via `Ideal.Quotient.mk`):

* `mk_outer (algMap_{B₁_gen → TA(B₁_gen)} (mk_inner (algMap_B a)))` ↦ `mk(algMap_B a)`
* `mk_outer (algMap_{B₁_gen → TA(B₁_gen)} (mk_inner (TateAlgebra.X_B)))` ↦ `mk(TateAlgebra₂.X)`
* `mk_outer (TateAlgebra.X_{B₁_gen})` ↦ `mk(TateAlgebra₂.Y)`

All three reduce to `Ideal.Quotient.lift_mk` plus the corresponding outer
evalHom action lemma (`TA_B₁_gen_to_bivariateOverlap_outer_evalHom_algebraMap`
or `_X`) — mirroring the `example638Bivariate_forwardHom_mk_algebraMap` pattern. -/

/-- Forward quotient hom action on `mk_outer (algebraMap (mk_inner (algebraMap a)))`:
equals `mk (algebraMap a)` in `TA₂ B ⧸ bivariateOverlapIdeal b`. -/
theorem TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom_mk_algebraMap_mk_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_base : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth))
    (a : B) :
    TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom P b hA_complete hnoeth hcont_base
        ((Ideal.Quotient.mk (outerLaurentOverlapIdeal b))
          (algebraMap (LaurentCover.B₁_gen b) _
            ((Ideal.Quotient.mk (plusFSubXIdeal B b))
              (algebraMap B ↥(TateAlgebra B) a)))) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
        (algebraMap B ↥(TateAlgebra₂ B) a) := by
  change Ideal.Quotient.lift _
      (TA_B₁_gen_to_bivariateOverlap_outer_evalHom P b hA_complete hnoeth hcont_base) _
      (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk,
      TA_B₁_gen_to_bivariateOverlap_outer_evalHom_algebraMap,
      baseHom_B₁_gen_to_bivariateOverlap_mk_algebraMap]

/-- Forward quotient hom action on `mk_outer (algebraMap (mk_inner (TateAlgebra.X)))`:
equals `mk TateAlgebra₂.X` in `TA₂ B ⧸ bivariateOverlapIdeal b`. -/
theorem TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom_mk_algebraMap_mk_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_base : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth)) :
    TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom P b hA_complete hnoeth hcont_base
        ((Ideal.Quotient.mk (outerLaurentOverlapIdeal b))
          (algebraMap (LaurentCover.B₁_gen b) _
            ((Ideal.Quotient.mk (plusFSubXIdeal B b))
              (TateAlgebra.X (A := B))))) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) TateAlgebra₂.X := by
  change Ideal.Quotient.lift _
      (TA_B₁_gen_to_bivariateOverlap_outer_evalHom P b hA_complete hnoeth hcont_base) _
      (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk,
      TA_B₁_gen_to_bivariateOverlap_outer_evalHom_algebraMap,
      baseHom_B₁_gen_to_bivariateOverlap_mk_X]

/-- Forward quotient hom action on `mk_outer (TateAlgebra.X_{B₁_gen})`:
equals `mk TateAlgebra₂.Y` in `TA₂ B ⧸ bivariateOverlapIdeal b`. -/
theorem TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom_mk_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring₂ (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_base : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (TateAlgebra.quotientBivariateOverlapIdealTopology b)
      (baseHom_B₁_gen_to_bivariateOverlap P b hA_complete hnoeth)) :
    TA_B₁_gen_quotient_to_bivariateOverlap_forwardHom P b hA_complete hnoeth hcont_base
        ((Ideal.Quotient.mk (outerLaurentOverlapIdeal b))
          (TateAlgebra.X (A := LaurentCover.B₁_gen b))) =
      (Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b)) TateAlgebra₂.Y := by
  change Ideal.Quotient.lift _
      (TA_B₁_gen_to_bivariateOverlap_outer_evalHom P b hA_complete hnoeth hcont_base) _
      (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk,
      TA_B₁_gen_to_bivariateOverlap_outer_evalHom_X]

/-! #### Step 6: backward direction
`TA₂ B ⧸ bivariateOverlapIdeal b → TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b`

Built via `TateAlgebraWedhorn.evalHomBounded₂` with:
* base map `mk_outer ∘ algMap_{B₁_gen → TA(B₁_gen)} ∘ mk_inner ∘ algMap_B : B → outer quotient`;
* target for `TA₂.X` = `mk_outer(algMap(mk_inner(TateAlgebra.X)))` (image of Ybar);
* target for `TA₂.Y` = `mk_outer(TateAlgebra.X)` (image of outer X_out).

Both continuity of the base and power-boundedness of the two target elements are
taken as explicit hypotheses (mirroring the `hcont_base` pattern on the forward
side). Then we factor through `bivariateOverlapIdeal b` using:

* Kernel on `algMap b - TA₂.X`: both sides collapse to the same element via the
  `plusFSubXIdeal` relation in `B₁_gen b`.
* Kernel on `1 - algMap b · TA₂.Y`: reduces to the `outerLaurentOverlapIdeal`
  relation `1 - Ybar · X_out = 0` after substituting `algMap b ≡ TA.X` in
  `B₁_gen b`. -/

/-- Backward base hom `B →+* TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b` sending
`a ↦ mk_outer(algMap_{B₁_gen → TA(B₁_gen)}(mk_inner(algMap_B a)))`. This is the
four-step composition `B → TA B → B₁_gen b → TA(B₁_gen b) → outer quotient`. -/
noncomputable def outerQuotient_baseHom (b : B) :
    B →+* (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
  (Ideal.Quotient.mk (outerLaurentOverlapIdeal b)).comp
    ((algebraMap (LaurentCover.B₁_gen b) ↥(TateAlgebra (LaurentCover.B₁_gen b))).comp
      ((Ideal.Quotient.mk (plusFSubXIdeal B b)).comp
        (algebraMap B ↥(TateAlgebra B))))

/-- Target element `Ybar` in the outer quotient: the image of
`algMap(mk_inner(TateAlgebra.X))`. This is the image of `TA₂.X` under the
backward hom. -/
noncomputable def outerQuotient_YbarTgt (b : B) :
    ↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b :=
  (Ideal.Quotient.mk (outerLaurentOverlapIdeal b))
    (algebraMap (LaurentCover.B₁_gen b) _
      ((Ideal.Quotient.mk (plusFSubXIdeal B b)) (TateAlgebra.X (A := B))))

/-- Target element `X_out` in the outer quotient: the image of outer
`TateAlgebra.X`. This is the image of `TA₂.Y` under the backward hom. -/
noncomputable def outerQuotient_XoutTgt (b : B) :
    ↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b :=
  (Ideal.Quotient.mk (outerLaurentOverlapIdeal b))
    (TateAlgebra.X (A := LaurentCover.B₁_gen b))

/-- **Backward evalHom₂ bundle** — hypothesis package for constructing the backward
direction `TA₂ B →+* TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b`. Records the
structural requirements on the outer quotient (topology + ring + uniform + complete +
T2 + nonarchimedean), together with the two analytic hypotheses: continuity of the
base hom and power-boundedness of the two target elements `Ybar` and `X_out`. -/
structure BackwardEvalHypotheses (b : B) where
  /-- Topology on the outer quotient. -/
  topOuter : TopologicalSpace
    (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b)
  /-- The outer quotient is a topological ring. -/
  ringOuter : @IsTopologicalRing _ topOuter _
  /-- The outer quotient's additive structure is a topological add group. -/
  addOuter : @IsTopologicalAddGroup _ topOuter _
  /-- The outer quotient is complete in the right-uniform structure induced
  by `topOuter` + `addOuter`. This avoids a coherence mismatch between the
  user-supplied uniform space and the topology. -/
  cOuter : @CompleteSpace _
    (@IsTopologicalAddGroup.rightUniformSpace _ _ topOuter addOuter)
  /-- The outer quotient is T2. -/
  tOuter : @T2Space _ topOuter
  /-- The outer quotient is nonarchimedean. -/
  naOuter : @NonarchimedeanRing _ _ topOuter
  /-- The backward base hom `B →+* outer quotient` is continuous. -/
  hcont_base : @Continuous _ _ _ topOuter (outerQuotient_baseHom b)
  /-- The target of `TA₂.X` — `Ybar` — has power-bounded range. -/
  hpb_Ybar : @TopologicalRing.IsPowerBounded _ _ topOuter (outerQuotient_YbarTgt b)
  /-- The target of `TA₂.Y` — `X_out` — has power-bounded range. -/
  hpb_Xout : @TopologicalRing.IsPowerBounded _ _ topOuter (outerQuotient_XoutTgt b)

/-- **Backward evaluation hom on TA₂ B** `TA₂ B →+* TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b`
sending `TA₂.X ↦ Ybar` and `TA₂.Y ↦ X_out`, built via `evalHomBounded₂` applied to
the hypothesis bundle `BackwardEvalHypotheses`.

This is the first-stage backward evalHom, which will be factored through
`bivariateOverlapIdeal b` in the next step. -/
noncomputable def TA_B_bivariate_to_outerQuotient_evalHom₂
    (b : B) (h : BackwardEvalHypotheses b) :
    ↥(TateAlgebra₂ B) →+*
      ↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b := by
  letI := h.topOuter
  haveI := h.ringOuter
  haveI := h.addOuter
  letI : UniformSpace (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
    @IsTopologicalAddGroup.rightUniformSpace _ _ h.topOuter
      h.addOuter
  haveI : @IsUniformAddGroup _
      (@IsTopologicalAddGroup.rightUniformSpace _ _ h.topOuter h.addOuter) _ :=
    @isUniformAddGroup_of_addCommGroup _ _ h.topOuter h.addOuter
  haveI := h.cOuter
  haveI := h.tOuter
  haveI := h.naOuter
  haveI : T0Space (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
    T2Space.t1Space.t0Space
  exact TateAlgebraWedhorn.evalHomBounded₂
    (outerQuotient_baseHom b) h.hcont_base
    (outerQuotient_YbarTgt b) (outerQuotient_XoutTgt b)
    h.hpb_Ybar h.hpb_Xout

/-- Backward evalHom₂ action on `algebraMap a` for `a : B`: equals `baseHom(a)`. -/
theorem TA_B_bivariate_to_outerQuotient_evalHom₂_algebraMap
    (b : B) (h : BackwardEvalHypotheses b) (a : B) :
    TA_B_bivariate_to_outerQuotient_evalHom₂ b h (algebraMap B _ a) =
      outerQuotient_baseHom b a := by
  letI := h.topOuter
  haveI := h.ringOuter
  haveI := h.addOuter
  letI : UniformSpace (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
    @IsTopologicalAddGroup.rightUniformSpace _ _ h.topOuter
      h.addOuter
  haveI : @IsUniformAddGroup _
      (@IsTopologicalAddGroup.rightUniformSpace _ _ h.topOuter h.addOuter) _ :=
    @isUniformAddGroup_of_addCommGroup _ _ h.topOuter h.addOuter
  haveI := h.cOuter
  haveI := h.tOuter
  haveI := h.naOuter
  haveI : T0Space (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
    T2Space.t1Space.t0Space
  unfold TA_B_bivariate_to_outerQuotient_evalHom₂
  exact TateAlgebraWedhorn.evalHomBounded₂_algebraMap _ _ _ _ _ _ _

/-- Backward evalHom₂ action on `TA₂.X`: equals `Ybar`. -/
theorem TA_B_bivariate_to_outerQuotient_evalHom₂_X
    (b : B) (h : BackwardEvalHypotheses b) :
    TA_B_bivariate_to_outerQuotient_evalHom₂ b h TateAlgebra₂.X =
      outerQuotient_YbarTgt b := by
  letI := h.topOuter
  haveI := h.ringOuter
  haveI := h.addOuter
  letI : UniformSpace (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
    @IsTopologicalAddGroup.rightUniformSpace _ _ h.topOuter
      h.addOuter
  haveI : @IsUniformAddGroup _
      (@IsTopologicalAddGroup.rightUniformSpace _ _ h.topOuter h.addOuter) _ :=
    @isUniformAddGroup_of_addCommGroup _ _ h.topOuter h.addOuter
  haveI := h.cOuter
  haveI := h.tOuter
  haveI := h.naOuter
  haveI : T0Space (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
    T2Space.t1Space.t0Space
  unfold TA_B_bivariate_to_outerQuotient_evalHom₂
  exact TateAlgebraWedhorn.evalHomBounded₂_X _ _ _ _ _ _

/-- Backward evalHom₂ action on `TA₂.Y`: equals `X_out`. -/
theorem TA_B_bivariate_to_outerQuotient_evalHom₂_Y
    (b : B) (h : BackwardEvalHypotheses b) :
    TA_B_bivariate_to_outerQuotient_evalHom₂ b h TateAlgebra₂.Y =
      outerQuotient_XoutTgt b := by
  letI := h.topOuter
  haveI := h.ringOuter
  haveI := h.addOuter
  letI : UniformSpace (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
    @IsTopologicalAddGroup.rightUniformSpace _ _ h.topOuter
      h.addOuter
  haveI : @IsUniformAddGroup _
      (@IsTopologicalAddGroup.rightUniformSpace _ _ h.topOuter h.addOuter) _ :=
    @isUniformAddGroup_of_addCommGroup _ _ h.topOuter h.addOuter
  haveI := h.cOuter
  haveI := h.tOuter
  haveI := h.naOuter
  haveI : T0Space (↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b) :=
    T2Space.t1Space.t0Space
  unfold TA_B_bivariate_to_outerQuotient_evalHom₂
  exact TateAlgebraWedhorn.evalHomBounded₂_Y _ _ _ _ _ _

/-! #### Step 7: kernel lemmas + factored backward quotient hom -/

-- Bumped from default: bivariate Laurent overlap kernel proof exercises
-- nested typeclass synthesis through bivariate Tate algebra quotients.
/-- Kernel lemma for `bivariateOverlapIdeal` generator `algMap b - TA₂.X`:
`evalHom₂(algMap b - TA₂.X) = 0`. Uses `quotient_algebraMap_b_eq_X` in
`B₁_gen b` (image of `algMap b = X` in plusFSubX quotient). -/
theorem TA_B_bivariate_to_outerQuotient_evalHom₂_algMap_b_sub_X_eq_zero
    (b : B) (h : BackwardEvalHypotheses b) :
    TA_B_bivariate_to_outerQuotient_evalHom₂ b h
        (algebraMap B ↥(TateAlgebra₂ B) b - TateAlgebra₂.X) = 0 := by
  rw [map_sub, TA_B_bivariate_to_outerQuotient_evalHom₂_algebraMap,
    TA_B_bivariate_to_outerQuotient_evalHom₂_X]
  -- Goal: baseHom(b) - Ybar = 0
  -- baseHom(b) = mk_outer(algMap(mk_inner(algMap b)))
  -- Ybar = mk_outer(algMap(mk_inner(TA.X)))
  -- Since mk_inner(algMap b) = mk_inner(TA.X), both are equal.
  change (Ideal.Quotient.mk (outerLaurentOverlapIdeal b))
      ((algebraMap (LaurentCover.B₁_gen b) _)
        ((Ideal.Quotient.mk (plusFSubXIdeal B b))
          ((algebraMap B ↥(TateAlgebra B)) b))) -
    outerQuotient_YbarTgt b = 0
  unfold outerQuotient_YbarTgt
  rw [quotient_algebraMap_b_eq_X]
  exact sub_self _

-- Bumped from default: backward quotient hom assembly through bivariate
-- Laurent overlap typeclass chain requires elevated heartbeats.
/-- Kernel lemma for `bivariateOverlapIdeal` generator `1 - algMap b · TA₂.Y`:
`evalHom₂(1 - algMap b · TA₂.Y) = 0`. Uses `quotient_algebraMap_b_eq_X` +
the outer ideal relation `1 - Ybar · X_out ∈ outerLaurentOverlapIdeal`. -/
theorem TA_B_bivariate_to_outerQuotient_evalHom₂_one_sub_algMap_b_Y_eq_zero
    (b : B) (h : BackwardEvalHypotheses b) :
    TA_B_bivariate_to_outerQuotient_evalHom₂ b h
        (1 - algebraMap B ↥(TateAlgebra₂ B) b * TateAlgebra₂.Y) = 0 := by
  rw [map_sub, map_one, map_mul,
    TA_B_bivariate_to_outerQuotient_evalHom₂_algebraMap,
    TA_B_bivariate_to_outerQuotient_evalHom₂_Y]
  -- Goal: 1 - baseHom(b) · X_out = 0
  -- baseHom(b) · X_out = mk_outer(algMap(mk_inner(algMap b)) · TA.X)
  --                    = mk_outer(algMap(mk_inner(TA.X)) · TA.X)  [by plusFSubX relation]
  --                    = mk_outer(1)                              [by outerLaurentOverlap relation]
  change (1 : _) - (Ideal.Quotient.mk (outerLaurentOverlapIdeal b))
      ((algebraMap (LaurentCover.B₁_gen b) _)
        ((Ideal.Quotient.mk (plusFSubXIdeal B b))
          ((algebraMap B ↥(TateAlgebra B)) b))) *
    outerQuotient_XoutTgt b = 0
  unfold outerQuotient_XoutTgt
  rw [quotient_algebraMap_b_eq_X, show (1 : _) =
      Ideal.Quotient.mk (outerLaurentOverlapIdeal b) 1 from rfl,
    ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have h_eq : (1 : ↥(TateAlgebra (LaurentCover.B₁_gen b))) -
      algebraMap (LaurentCover.B₁_gen b) ↥(TateAlgebra (LaurentCover.B₁_gen b))
        ((Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X) *
      TateAlgebra.X =
        (1 : ↥(TateAlgebra (LaurentCover.B₁_gen b))) -
          algebraMap (LaurentCover.B₁_gen b) ↥(TateAlgebra (LaurentCover.B₁_gen b))
            ((Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X) *
          TateAlgebra.X := rfl
  rw [h_eq]
  unfold outerLaurentOverlapIdeal
  exact Ideal.subset_span rfl

/-- **Specialized Laurent-overlap quotient bridge, backward direction**:
`TA₂ B ⧸ bivariateOverlapIdeal b →+* TA(B₁_gen b) ⧸ outerLaurentOverlapIdeal b`.

Factored from `TA_B_bivariate_to_outerQuotient_evalHom₂` through
`bivariateOverlapIdeal b` using the two kernel lemmas. -/
noncomputable def TA_B_bivariate_quotient_to_outerQuotient_backwardHom
    (b : B) (h : BackwardEvalHypotheses b) :
    ↥(TateAlgebra₂ B) ⧸ TateAlgebra.bivariateOverlapIdeal b →+*
      ↥(TateAlgebra (LaurentCover.B₁_gen b)) ⧸ outerLaurentOverlapIdeal b := by
  refine Ideal.Quotient.lift _ (TA_B_bivariate_to_outerQuotient_evalHom₂ b h)
    (fun y hy ↦ ?_)
  have h_le : TateAlgebra.bivariateOverlapIdeal b ≤
      RingHom.ker (TA_B_bivariate_to_outerQuotient_evalHom₂ b h) := by
    unfold TateAlgebra.bivariateOverlapIdeal
    rw [Ideal.span_le]
    rintro z hz
    rcases hz with rfl | rfl
    · exact TA_B_bivariate_to_outerQuotient_evalHom₂_algMap_b_sub_X_eq_zero b h
    · exact TA_B_bivariate_to_outerQuotient_evalHom₂_one_sub_algMap_b_Y_eq_zero b h
  exact h_le hy

/-! #### Step 8: action lemmas for the backward quotient hom -/

/-- Backward quotient hom action on `mk(algMap a)`: equals `outerQuotient_baseHom a`. -/
theorem TA_B_bivariate_quotient_to_outerQuotient_backwardHom_mk_algebraMap
    (b : B) (h : BackwardEvalHypotheses b) (a : B) :
    TA_B_bivariate_quotient_to_outerQuotient_backwardHom b h
        ((Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
          (algebraMap B ↥(TateAlgebra₂ B) a)) =
      outerQuotient_baseHom b a := by
  change Ideal.Quotient.lift _
      (TA_B_bivariate_to_outerQuotient_evalHom₂ b h) _
      (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk,
      TA_B_bivariate_to_outerQuotient_evalHom₂_algebraMap]

/-- Backward quotient hom action on `mk TA₂.X`: equals `Ybar`. -/
theorem TA_B_bivariate_quotient_to_outerQuotient_backwardHom_mk_X
    (b : B) (h : BackwardEvalHypotheses b) :
    TA_B_bivariate_quotient_to_outerQuotient_backwardHom b h
        ((Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
          (TateAlgebra₂.X (A := B))) =
      outerQuotient_YbarTgt b := by
  change Ideal.Quotient.lift _
      (TA_B_bivariate_to_outerQuotient_evalHom₂ b h) _
      (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk, TA_B_bivariate_to_outerQuotient_evalHom₂_X]

/-- Backward quotient hom action on `mk TA₂.Y`: equals `X_out`. -/
theorem TA_B_bivariate_quotient_to_outerQuotient_backwardHom_mk_Y
    (b : B) (h : BackwardEvalHypotheses b) :
    TA_B_bivariate_quotient_to_outerQuotient_backwardHom b h
        ((Ideal.Quotient.mk (TateAlgebra.bivariateOverlapIdeal b))
          (TateAlgebra₂.Y (A := B))) =
      outerQuotient_XoutTgt b := by
  change Ideal.Quotient.lift _
      (TA_B_bivariate_to_outerQuotient_evalHom₂ b h) _
      (Ideal.Quotient.mk _ _) = _
  rw [Ideal.Quotient.lift_mk, TA_B_bivariate_to_outerQuotient_evalHom₂_Y]


/-! #### Step 11: parametric reverse round trip `backward ∘ forward = id`

The reverse round trip requires polynomial density on `TA(B₁_gen b)`. Since
`[IsTateRing (B₁_gen b)]` is not automatic for the quotient, we take the
density + polynomial decomposition on `TA(B₁_gen b)` as explicit hypotheses.

The inner side uses the already-available `[IsTateRing B]` to get density
and decomposition on `TA B` via `tateAlgebra_polynomials_dense_canonical` —
which is sufficient for discharging the inner `Ideal.Quotient.ringHom_ext`
reduction.

**Boundary**: the two hypotheses `hDense_outer` + `hDecomp_outer` would
follow from `[IsTateRing (LaurentCover.B₁_gen b)]`; this instance is not
yet constructed (would require an explicit `PairOfDefinition` on
`B₁_gen b = TA B / plusFSubXIdeal b`, which is substantial work). -/

/-- **Univariate monomial value**: `algebraMap A _ c * X^i` in `TateAlgebra A`
has underlying MvPowerSeries equal to `monomial (Finsupp.single 0 i) c`.
Univariate analog of `TateAlgebra₂_monomial_val`. -/
theorem TateAlgebra_monomial_val {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (c : A) (i : ℕ) :
    (algebraMap A ↥(TateAlgebra A) c * TateAlgebra.X ^ i).val =
      MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) i) c := by
  have hval : (algebraMap A ↥(TateAlgebra A) c * TateAlgebra.X ^ i).val =
      (Subring.subtype (TateAlgebra A))
        (algebraMap A ↥(TateAlgebra A) c * TateAlgebra.X ^ i) := rfl
  rw [hval, map_mul, map_pow]
  change MvPowerSeries.C c * MvPowerSeries.X (0 : Fin 1) ^ i = _
  rw [MvPowerSeries.X_pow_eq,
      (MvPowerSeries.monomial_zero_eq_C_apply (a := c)).symm,
      MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]

/-- Any `l : Fin 1 →₀ ℕ` decomposes as `Finsupp.single 0 (l 0)`. -/
theorem Finsupp_fin1_decomp (l : Fin 1 →₀ ℕ) :
    l = Finsupp.single (0 : Fin 1) (l 0) := by
  apply Finsupp.ext
  intro i
  fin_cases i
  simp

/-- **Polynomial decomposition (univariate)**: for `g : TateAlgebra A` with
coefficients vanishing for indices `n 0 ≥ N`, `g` equals the Finset.sum of its
coefficient-monomials. Univariate analog of `tateAlgebra₂_polynomial_decomp`.
Purely algebraic — requires only `CommRing A`, `TopologicalSpace A`,
`NonarchimedeanRing A`. -/
theorem tateAlgebra_polynomial_decomp
    {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    (g : ↥(TateAlgebra A)) (N : ℕ)
    (hN : ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0) :
    g = ∑ i ∈ Finset.range N,
      algebraMap A ↥(TateAlgebra A)
        (MvPowerSeries.coeff (Finsupp.single 0 i) g.val) * TateAlgebra.X ^ i := by
  classical
  apply Subtype.ext
  funext l
  have hRHS_val_eq : ((∑ i ∈ Finset.range N,
        algebraMap A ↥(TateAlgebra A)
          (MvPowerSeries.coeff (Finsupp.single 0 i) g.val) *
          TateAlgebra.X ^ i : ↥(TateAlgebra A)).val) =
      ∑ i ∈ Finset.range N,
        MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) i)
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) i) g.val) := by
    change (Subring.subtype _) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intros i _
    exact TateAlgebra_monomial_val _ i
  rw [hRHS_val_eq]
  have hsum_val : (∑ i ∈ Finset.range N,
        MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) i)
          (MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) i) g.val)) l =
      ∑ i ∈ Finset.range N,
        (if l = Finsupp.single (0 : Fin 1) i then
          MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) i) g.val
        else 0) := by
    rw [(MvPowerSeries.coeff_apply (∑ i ∈ Finset.range N,
          MvPowerSeries.monomial (Finsupp.single (0 : Fin 1) i)
            (MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) i) g.val)) l).symm, map_sum]
    apply Finset.sum_congr rfl
    intros i _
    exact MvPowerSeries.coeff_monomial _ _ _
  rw [hsum_val]
  by_cases hl : l 0 < N
  · rw [Finset.sum_eq_single (l 0)]
    · rw [if_pos (Finsupp_fin1_decomp l)]
      rw [← Finsupp_fin1_decomp l]
      rfl
    · intros i _ hi
      rw [if_neg]
      intro heq
      apply hi
      have := congrArg (fun f : Fin 1 →₀ ℕ ↦ f 0) heq
      simp at this
      exact this.symm
    · intro h
      exfalso; exact h (Finset.mem_range.mpr hl)
  · push Not at hl
    have hN_apply : g.val l = 0 := hN l hl
    rw [hN_apply]
    symm
    apply Finset.sum_eq_zero
    intros i hi
    rw [if_neg]
    intro heq
    have h_l_i : l 0 = i := by
      have := congrArg (fun f : Fin 1 →₀ ℕ ↦ f 0) heq
      simp at this
      exact this
    have h_i_lt : i < N := Finset.mem_range.mp hi
    rw [h_l_i] at hl
    exact absurd hl (Nat.not_le.mpr h_i_lt)

end TA_B₁_gen_quotient_bridge

/-! ### Lane A finish: exported overlap-bridge theorem with bundled residual

This section exports the **caller-ready overlap-bridge theorem** for downstream
consumers: `laurentOverlapBridge_exists_compatible_via_primary` specializes
`laurentOverlapBridge_exists_compatible_from_bivariate_factorization` by binding
`τ_alg` to the Primary-side algebraic identification
`bivariateOverlap_equiv_B₁₂gen`. Downstream supplies `τ_preBiv` (the presheaf-
level bivariate iso — Step A / S-OV-GLUE) and the two intertwining identities;
this theorem threads them through to produce the `LaurentOverlapBridgeCompatible`
witness required by downstream gluing arguments.

The single named residual for downstream is `τ_preBiv` plus the two compatibility
witnesses; all other structure is fixed. -/

/-- **Exported caller-ready overlap bridge with Primary's `τ_alg` bound**:
specializes `laurentOverlapBridge_exists_compatible_from_bivariate_factorization`
by fixing `τ_alg := bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f)` (Primary's
sorry-free algebraic identification). The caller now only needs to supply
`τ_preBiv` (the presheaf-level bivariate iso) and the two intertwining witnesses
at the composed level. -/
theorem laurentOverlapBridge_exists_compatible_via_primary
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) [IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]
    [LaurentNormalized D₀]
    (f : A)
    (hNoeth_B : IsNoetherianRing (presheafValue D₀))
    (hLocLift_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      HasLocLiftPowerBounded (presheafValue D₀))
    (hA₀Noeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      IsNoetherianRing ↥((presheafValue_pairOfDefinition_concrete P D₀).A₀))
    (hA_complete_B : @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)))
    (hnoeth_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      IsNoetherianRing ↥(TateAlgebra.pairSubring
        (IsTateRing.principalPair (presheafValue D₀)).toPairOfDefinition))
    (hcont_forward_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      letI : HasLocLiftPowerBounded (presheafValue D₀) := hLocLift_B
      letI : IsNoetherianRing (presheafValue D₀) := hNoeth_B
      letI P_B : PairOfDefinition (presheafValue D₀) :=
        presheafValue_pairOfDefinition_concrete P D₀
      letI : IsNoetherianRing ↥P_B.A₀ := hA₀Noeth_B
      @Continuous _ _
        (quotientPlusFSubXIdealTopology (presheafValue D₀) (D₀.canonicalMap f))
        (inferInstance : TopologicalSpace (presheafValue
          (trivialPlusDatum (presheafValue D₀) P_B (D₀.canonicalMap f))))
        (example638Plus_forwardHom (presheafValue D₀) P_B (D₀.canonicalMap f)))
    (hcont_eval_B : letI : IsTateRing (presheafValue D₀) :=
        presheafValue_isTateRing P D₀
      let D : RationalLocData (presheafValue D₀) := iteratedMinusDatum_B P D₀ f
      ∀ hb : TopologicalRing.IsPowerBounded (invS D),
        @Continuous _ _
          (TateAlgebra.quotientOneSubfXIdealTopology D.s)
          (inferInstance : TopologicalSpace (presheafValue D))
          (tateQuotientToPresheafHom D hb))
    (τ_preBiv : presheafValue (laurentOverlapDatum D₀ f) ≃+*
      (↥(TateAlgebra₂ (presheafValue D₀)) ⧸
        TateAlgebra.bivariateOverlapIdeal (D₀.canonicalMap f)))
    (h_plus_compat : ∀ uplus : presheafValue (laurentPlusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentPlusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_plus D₀ f) uplus)) =
        LaurentCover.posLift (D₀.canonicalMap f)
          (laurentPlusBridge P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B
            hnoeth_B hcont_forward_B uplus))
    (h_minus_compat : ∀ uminus : presheafValue (laurentMinusDatum D₀ f),
      (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
          (τ_preBiv (restrictionMap (laurentMinusDatum D₀ f)
              (laurentOverlapDatum D₀ f)
              (laurentOverlap_subset_minus D₀ f) uminus)) =
        LaurentCover.negLift (D₀.canonicalMap f)
          (laurentMinusBridge P D₀ f hnoeth_B hcont_eval_B uminus)) :
    ∃ τ₁₂ : presheafValue (laurentOverlapDatum D₀ f) ≃+*
            LaurentCover.B₁₂_gen (D₀.canonicalMap f),
      LaurentOverlapBridgeCompatible P D₀ f hNoeth_B hLocLift_B
        hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B hcont_eval_B τ₁₂ :=
  laurentOverlapBridge_exists_compatible_from_bivariate_factorization
    P D₀ f hNoeth_B hLocLift_B hA₀Noeth_B hA_complete_B hnoeth_B hcont_forward_B
    hcont_eval_B τ_preBiv (bivariateOverlap_equiv_B₁₂gen (presheafValue D₀) (D₀.canonicalMap f))
    h_plus_compat h_minus_compat

end ValuationSpectrum
