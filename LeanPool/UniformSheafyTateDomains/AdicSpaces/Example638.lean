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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafTateStructure
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.TopologyComparison
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletionLocalization

/-!
# Wedhorn Example 6.38: generic `f − X` / `1 − fX` identifications

Per the reviewer's 2026-04-15 guidance, the load-bearing primitive for closing
the Laurent-branch bridges is Wedhorn Example 6.38 generically: for any
complete strongly noetherian Tate base `B` and any `b ∈ B` power-bounded in
the relevant branch, the Tate-algebra quotient identifies with the
presheafValue of a trivial rational datum on `B`.

This avoids the `HasLocLiftPowerBounded [IsDomain]`-gated route entirely:
the forward map is built from `TateAlgebra B` via evaluation at `b`
(plus) or `1/b` (minus), which is the standard `evalHomBounded`
construction — not the `IsLocalization.Away.lift` route.

## Plus branch
`B⟨X⟩ / (algebraMap b − X) ≃+* presheafValue (trivialPlusDatum P b)`

## Minus branch
`B⟨X⟩ / (1 − algebraMap b · X) ≃+* presheafValue (trivialMinusDatum P b)`

This module was extracted from `IteratedRational.lean` to break an import
cycle: `LaurentRefinement` needs `example638Plus_equiv` to discharge the
`presheafValue_trivialPlus_fSubX_equiv` bridge, but `IteratedRational` itself
imports `LaurentRefinement`. Since these Example 6.38 primitives are fully
generic over a `B` with `RationalLocData B` (depending only on
`PresheafTateStructure`, `TopologyComparison`, `CompletionLocalization`,
`TateAlgebraWedhorn`), we can place them upstream of `LaurentRefinement`.

## References
* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Example 6.38, Prop 6.17.
-/

@[expose] public section

namespace ValuationSpectrum

open UniformSpace

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

section Example638

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [PlusSubring B] [IsHuberRing B] [HasLocLiftPowerBounded B]

/-- Generic trivial plus datum on `B` at `b`: `T = {b}`, `s = 1`.
`hopen` is trivial via `hopen_away_one` (no constraint on `b`, since the ring of
definition already contains `b` when we add it to `T`, in the localization at 1). -/
noncomputable def trivialPlusDatum (P : PairOfDefinition B) (b : B) :
    RationalLocData B where
  P := P
  T := {b}
  s := 1
  hopen := hopen_away_one P {b}

/-- Generic trivial minus datum on `B` at `b`: `T = {1}`, `s = b`.
`hopen` with `N = 0`: for any `c : P.A₀`, `divByS c.val b` factors as
`algebraMap c.val * divByS 1 b`, both in the `locSubring`. -/
noncomputable def trivialMinusDatum (P : PairOfDefinition B) (b : B) :
    RationalLocData B where
  P := P
  T := {1}
  s := b
  hopen := ⟨0, fun c _ => by
    have hmul : algebraMap B (Localization.Away b) c.val *
        divByS (1 : B) b = divByS c.val b := by
      unfold divByS
      rw [← IsLocalization.mk'_one (M := Submonoid.powers b)
            (S := Localization.Away b) c.val,
          ← IsLocalization.mk'_mul, one_mul, mul_one]
    rw [← hmul]
    exact (locSubring _ _ _).mul_mem
      (algebraMap_mem_locSubring _ _ _ c.2)
      (divByS_mem_locSubring _ _ _ (Finset.mem_singleton_self 1))⟩

section Example638PlusForward

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

/-- `canonicalMap b` is power-bounded in `presheafValue (trivialPlusDatum P b)`.

Parallels `invS_isPowerBounded_of_one_mem_T` in `CompletionLocalization.lean`:
`divByS b 1 = algebraMap B _ b` lies in `locSubring P {b} 1` (since `b ∈ T`),
its powers stay in `locSubring`, and `coeRingHom_image_locSubring_isBounded`
gives boundedness of the image in the completion. -/
theorem canonicalMap_b_isPowerBounded_in_trivialPlus
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    TopologicalRing.IsPowerBounded
      ((trivialPlusDatum B P b).canonicalMap b) := by
  set D := trivialPlusDatum B P b
  have hcm : D.canonicalMap b =
      D.coeRingHom (algebraMap B (Localization.Away D.s) b) := rfl
  rw [hcm]
  have halg_eq : algebraMap B (Localization.Away D.s) b = divByS b D.s := by
    change algebraMap B (Localization.Away (1 : B)) b = divByS b 1
    rw [divByS_eq_algebraMap]
  rw [halg_eq]
  have hmem : divByS b D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s (Finset.mem_singleton_self b)
  have hpow : ∀ n : ℕ, (divByS b D.s) ^ n ∈ locSubring D.P D.T D.s :=
    fun n => (locSubring D.P D.T D.s).pow_mem hmem n
  have hrange : Set.range
      ((D.coeRingHom (divByS b D.s)) ^ · : ℕ → presheafValue D) ⊆
      D.coeRingHom '' (locSubring D.P D.T D.s : Set (Localization.Away D.s)) := by
    rintro _ ⟨n, rfl⟩
    change (D.coeRingHom (divByS b D.s)) ^ n ∈ _
    rw [← map_pow]
    exact ⟨(divByS b D.s) ^ n, hpow n, rfl⟩
  exact (CompletionLocalization.coeRingHom_image_locSubring_isBounded D).subset hrange

/-- The generic evaluation hom `TateAlgebra B →+* presheafValue (trivialPlusDatum P b)`
sending `X ↦ canonicalMap b`, via `evalHomBounded`. -/
noncomputable def example638Plus_evalHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra B) →+* presheafValue (trivialPlusDatum B P b) :=
  TateAlgebraWedhorn.evalHomBounded
    (trivialPlusDatum B P b).canonicalMap
    (canonicalMap_continuous (trivialPlusDatum B P b))
    ((trivialPlusDatum B P b).canonicalMap b)
    (canonicalMap_b_isPowerBounded_in_trivialPlus B P b)

/-- `example638Plus_evalHom` sends `algebraMap(a)` to `canonicalMap(a)`. -/
theorem example638Plus_evalHom_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b a : B) :
    example638Plus_evalHom B P b (algebraMap B _ a) =
      (trivialPlusDatum B P b).canonicalMap a := by
  unfold example638Plus_evalHom
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

/-- `example638Plus_evalHom` sends `X` to `canonicalMap b`. -/
theorem example638Plus_evalHom_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Plus_evalHom B P b TateAlgebra.X =
      (trivialPlusDatum B P b).canonicalMap b := by
  unfold example638Plus_evalHom
  simp only [TateAlgebraWedhorn.evalHomBounded, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [tsum_eq_single 1]
  · simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X, pow_one]
    change (trivialPlusDatum B P b).canonicalMap
      ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 1))
        (MvPowerSeries.X 0)) *
      (trivialPlusDatum B P b).canonicalMap b =
      (trivialPlusDatum B P b).canonicalMap b
    rw [MvPowerSeries.coeff_X, if_pos rfl, map_one, one_mul]
  · intro n hn
    simp only [TateAlgebraWedhorn.evalTerm, TateAlgebra.coeff,
      TateAlgebra.toIndex, TateAlgebra.X]
    change (trivialPlusDatum B P b).canonicalMap
      ((MvPowerSeries.coeff (R := B) (Finsupp.single 0 n))
        (MvPowerSeries.X (0 : Fin 1))) *
      (trivialPlusDatum B P b).canonicalMap b ^ n = 0
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

/-- The ideal `(algebraMap b - X)` maps to zero under `example638Plus_evalHom`,
since the eval sends `algebraMap b ↦ canonicalMap b` and `X ↦ canonicalMap b`. -/
theorem example638Plus_evalHom_fSubX_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Plus_evalHom B P b
      (algebraMap B ↥(TateAlgebra B) b - TateAlgebra.X) = 0 := by
  rw [map_sub, example638Plus_evalHom_algebraMap, example638Plus_evalHom_X, sub_self]

/-- Forward ring hom `TateAlgebra B ⧸ (algebraMap b − X) → presheafValue (trivialPlusDatum P b)`,
obtained by factoring `example638Plus_evalHom` through the quotient. -/
noncomputable def example638Plus_forwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra B) ⧸
      Ideal.span {algebraMap B ↥(TateAlgebra B) b - TateAlgebra.X} →+*
        presheafValue (trivialPlusDatum B P b) :=
  Ideal.Quotient.lift _ (example638Plus_evalHom B P b) (fun y hy => by
    rw [Ideal.mem_span_singleton'] at hy
    obtain ⟨c, hc⟩ := hy
    rw [← hc, map_mul, example638Plus_evalHom_fSubX_eq_zero, mul_zero])

end Example638PlusForward

section Example638PlusBackwardTopology

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

open TateAlgebra

/-- The ideal `(algebraMap b − X)` in `TateAlgebra B`. This is the plus-branch
analog of `oneSubfXIdeal` (which is `(1 − f·X)`). -/
noncomputable def plusFSubXIdeal (b : B) : Ideal ↥(TateAlgebra B) :=
  Ideal.span {algebraMap B ↥(TateAlgebra B) b - TateAlgebra.X}

/-- The quotient topology on `TateAlgebra B ⧸ plusFSubXIdeal b` using the canonical
Tate topology on `TateAlgebra B`. -/
@[reducible]
noncomputable def quotientPlusFSubXIdealTopology (b : B) :
    TopologicalSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra _
    (plusFSubXIdeal B b)

/-- The quotient `TateAlgebra B ⧸ plusFSubXIdeal b` is a topological ring. -/
noncomputable instance quotientPlusFSubXIdealTopology_isTopologicalRing (b : B) :
    @IsTopologicalRing (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      (quotientPlusFSubXIdealTopology B b) _ :=
  @topologicalRing_quotient ↥(TateAlgebra B)
    instTopologicalSpaceTateAlgebra _
    (plusFSubXIdeal B b) (instIsTopologicalRingTateAlgebra)

/-- The quotient `TateAlgebra B ⧸ plusFSubXIdeal b` has the `IsTopologicalAddGroup`
structure. -/
noncomputable instance quotientPlusFSubXIdealTopology_isTopologicalAddGroup (b : B) :
    @IsTopologicalAddGroup (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      (quotientPlusFSubXIdealTopology B b) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (quotientPlusFSubXIdealTopology B b)
    (quotientPlusFSubXIdealTopology_isTopologicalRing B b)

/-- The uniform space on the quotient `TateAlgebra B ⧸ plusFSubXIdeal b`. -/
@[reducible, instance]
noncomputable def quotientPlusFSubXIdealUniformSpace (b : B) :
    UniformSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (quotientPlusFSubXIdealTopology B b)
    (quotientPlusFSubXIdealTopology_isTopologicalAddGroup B b)

/-- The `IsUniformAddGroup` instance for the canonical quotient topology on
`TateAlgebra B ⧸ plusFSubXIdeal b`. -/
noncomputable instance quotientPlusFSubXIdeal_isUniformAddGroup (b : B) :
    @IsUniformAddGroup (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      (quotientPlusFSubXIdealUniformSpace B b) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ (quotientPlusFSubXIdealTopology B b)
    (quotientPlusFSubXIdealTopology_isTopologicalAddGroup B b)

/-- The ideal `(algebraMap b − X)` is closed in `TateAlgebra B` under the canonical
topology. Corollary of `tateAlgebra_isClosed_ideal` which applies to any ideal
when `pairSubring.A₀` is noetherian. -/
theorem plusFSubXIdeal_isClosed
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (b : B) :
    IsClosed ((plusFSubXIdeal B b : Ideal ↥(TateAlgebra B)) :
      Set ↥(TateAlgebra B)) := by
  haveI : IsNoetherianRing ↥(tateAlgebra_pairOfDefinition (A := B)).A₀ := hnoeth
  exact tateAlgebra_isClosed_ideal hA_complete (plusFSubXIdeal B b)

/-- The quotient `TateAlgebra B ⧸ plusFSubXIdeal b` is T2. -/
theorem quotient_plusFSubXIdeal_t2Space
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (b : B) :
    T2Space (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) := by
  haveI : IsClosed ((plusFSubXIdeal B b).toAddSubgroup : Set ↥(TateAlgebra B)) :=
    plusFSubXIdeal_isClosed B hA_complete hnoeth b
  infer_instance

/-- The quotient `TateAlgebra B ⧸ plusFSubXIdeal b` is complete under the
canonical quotient topology. Mirror of `quotient_oneSubfXIdeal_completeSpace`. -/
theorem quotient_plusFSubXIdeal_completeSpace
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (b : B) :
    @CompleteSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      (quotientPlusFSubXIdealUniformSpace B b) := by
  letI τ : TopologicalSpace ↥(TateAlgebra B) := instTopologicalSpaceTateAlgebra
  haveI _hring : IsTopologicalRing ↥(TateAlgebra B) := instIsTopologicalRingTateAlgebra
  haveI haddgrp : IsTopologicalAddGroup ↥(TateAlgebra B) :=
    IsTopologicalRing.to_topologicalAddGroup
  haveI : FirstCountableTopology ↥(TateAlgebra B) := instFirstCountableTopologyTateAlgebra
  haveI hCS : @CompleteSpace ↥(TateAlgebra B)
      (IsTopologicalAddGroup.rightUniformSpace ↥(TateAlgebra B)) :=
    tateAlgebraTopology'_completeSpace hA_complete
  haveI : IsClosed ((plusFSubXIdeal B b).toAddSubgroup : Set ↥(TateAlgebra B)) :=
    plusFSubXIdeal_isClosed B hA_complete hnoeth b
  exact @QuotientAddGroup.completeSpace_right' ↥(TateAlgebra B) _ τ haddgrp ‹_›
    (plusFSubXIdeal B b).toAddSubgroup inferInstance hCS

end Example638PlusBackwardTopology

section Example638PlusBackwardAlgebraic

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

open TateAlgebra

/-- In `TateAlgebra B ⧸ plusFSubXIdeal B b`, the canonical image of `1` is a unit
(it's just `1` itself). This is used to apply `IsLocalization.Away.lift` at
`1 : B` to build the algebraic backward map. -/
theorem isUnit_one_in_quotientPlusFSubX (b : B) :
    IsUnit ((Ideal.Quotient.mk (plusFSubXIdeal B b)).comp
      (algebraMap B ↥(TateAlgebra B)) (1 : B)) := by
  rw [RingHom.comp_apply, map_one, map_one]
  exact isUnit_one

/-- Algebraic backward hom `Localization.Away 1 →+* TateAlgebra B ⧸ plusFSubXIdeal B b`
using the universal property of `IsLocalization.Away` (since `1` is trivially a unit
everywhere). Sends `algebraMap a ↦ mk(algebraMap a)`. -/
noncomputable def plusLocToQuotient (b : B) :
    Localization.Away (1 : B) →+*
      ↥(TateAlgebra B) ⧸ plusFSubXIdeal B b :=
  IsLocalization.Away.lift (x := (1 : B))
    (isUnit_one_in_quotientPlusFSubX B b)

/-- `plusLocToQuotient` sends `algebraMap a` to `mk(algebraMap a)`. -/
theorem plusLocToQuotient_algebraMap (b a : B) :
    plusLocToQuotient B b (algebraMap B _ a) =
      (Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) a) := by
  simp [plusLocToQuotient, IsLocalization.Away.lift_eq]

end Example638PlusBackwardAlgebraic

section Example638PlusBackwardContinuity

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

open TateAlgebra

/-- The composite `mk ∘ algebraMap : B → TateAlgebra B ⧸ plusFSubXIdeal B b`
is continuous. Uses `tateAlgebra_algebraMap_continuous` for the first factor
and `continuous_quotient_mk'` for the second. -/
theorem mk_algebraMap_continuous_plusFSubX (b : B) :
    @Continuous _ _ _ (quotientPlusFSubXIdealTopology B b)
      (fun a : B => (Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) a)) := by
  letI : TopologicalSpace ↥(TateAlgebra B) := instTopologicalSpaceTateAlgebra
  have h2 : @Continuous _ _ _ (quotientPlusFSubXIdealTopology B b)
      (Ideal.Quotient.mk (plusFSubXIdeal B b)) := continuous_quotient_mk'
  exact h2.comp tateAlgebra_algebraMap_continuous

/-- In the quotient `TateAlgebra B ⧸ plusFSubXIdeal B b`, the classes of
`algebraMap B _ b` and `X` are equal. (Since `algebraMap b - X ∈ plusFSubXIdeal`.) -/
theorem quotient_algebraMap_b_eq_X (b : B) :
    (Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) b) =
      (Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X := by
  rw [Ideal.Quotient.eq]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- `X : TateAlgebra B` is in the pair subring of the principal pair of definition.
Holds because `X` has coefficients `1` at `Finsupp.single 0 1` and `0` elsewhere,
and `1 ∈ A₀` always. -/
theorem TateAlgebra_X_mem_pairSubring :
    TateAlgebra.X (A := B) ∈
      TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition := by
  intro s
  simp only [TateAlgebra.X]
  classical
  rw [MvPowerSeries.coeff_X]
  split
  · exact ((IsTateRing.principalPair B).toPairOfDefinition).A₀.one_mem
  · exact ((IsTateRing.principalPair B).toPairOfDefinition).A₀.zero_mem

/-- `X : TateAlgebra B` is power-bounded in the canonical Tate topology.
Reason: `X` is in the ring of definition `pairSubring`, which is bounded
(by `PairOfDefinition.isBounded_A₀`), and bounded implies power-bounded
(closure under powers in the subring). -/
theorem TateAlgebra_X_isPowerBounded :
    @TopologicalRing.IsPowerBounded _ _ instTopologicalSpaceTateAlgebra
      (TateAlgebra.X (A := B)) := by
  letI : TopologicalSpace ↥(TateAlgebra B) := instTopologicalSpaceTateAlgebra
  haveI : IsTopologicalRing ↥(TateAlgebra B) := instIsTopologicalRingTateAlgebra
  have hX_in : TateAlgebra.X (A := B) ∈
      TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition :=
    TateAlgebra_X_mem_pairSubring B
  have hpow : ∀ n : ℕ, TateAlgebra.X (A := B) ^ n ∈
      TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition :=
    fun n => (TateAlgebra.pairSubring _).pow_mem hX_in n
  have hbd : TopologicalRing.IsBounded
      (TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition :
        Set ↥(TateAlgebra B)) :=
    PairOfDefinition.isBounded_A₀
      (A := ↥(TateAlgebra B)) (tateAlgebra_pairOfDefinition (A := B))
  exact hbd.subset (by rintro _ ⟨n, rfl⟩; exact hpow n)

/-- `mk : TateAlgebra B → quotient` preserves boundedness of subsets.
Uses that `mk` is a continuous open map (quotient map). -/
theorem IsBounded_mk_image_of_IsBounded (b : B) {S : Set ↥(TateAlgebra B)}
    (hS : TopologicalRing.IsBounded S) :
    @TopologicalRing.IsBounded _ _ (quotientPlusFSubXIdealTopology B b)
      ((Ideal.Quotient.mk (plusFSubXIdeal B b)) '' S) := by
  letI : TopologicalSpace ↥(TateAlgebra B) := instTopologicalSpaceTateAlgebra
  letI : IsTopologicalRing ↥(TateAlgebra B) := instIsTopologicalRingTateAlgebra
  letI : TopologicalSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology B b
  letI : IsTopologicalRing (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology_isTopologicalRing B b
  intro U hU
  have hcont : @Continuous _ _ instTopologicalSpaceTateAlgebra
      (quotientPlusFSubXIdealTopology B b)
      (Ideal.Quotient.mk (plusFSubXIdeal B b)) :=
    continuous_quotient_mk'
  have hU_pre : (Ideal.Quotient.mk (plusFSubXIdeal B b)) ⁻¹' U ∈
      @nhds _ instTopologicalSpaceTateAlgebra (0 : ↥(TateAlgebra B)) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU)
  obtain ⟨V, hV, hSV⟩ := hS _ hU_pre
  obtain ⟨W, hWV, hW_open, hW_zero⟩ := _root_.mem_nhds_iff.mp hV
  have hmkW_open : IsOpen ((Ideal.Quotient.mk (plusFSubXIdeal B b)) '' W) :=
    @QuotientRing.isOpenMap_coe _ instTopologicalSpaceTateAlgebra _
      (plusFSubXIdeal B b) instIsTopologicalRingTateAlgebra _ hW_open
  refine ⟨(Ideal.Quotient.mk (plusFSubXIdeal B b)) '' W,
    _root_.mem_nhds_iff.mpr ⟨_, le_refl _, hmkW_open, ⟨0, hW_zero, map_zero _⟩⟩, ?_⟩
  rintro _ ⟨_, ⟨s, hs, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
  change (Ideal.Quotient.mk (plusFSubXIdeal B b)) s *
    (Ideal.Quotient.mk (plusFSubXIdeal B b)) w ∈ U
  rw [← map_mul]
  exact hSV ⟨s, hs, w, hWV hw, rfl⟩

/-- In the quotient `TateAlgebra B ⧸ plusFSubXIdeal B b`, the image of
`algebraMap b` is power-bounded. Uses `TateAlgebra_X_isPowerBounded` +
`IsBounded_mk_image_of_IsBounded`. -/
theorem mk_algebraMap_b_isPowerBounded_in_quotientPlusFSubX
    (b : B) :
    @TopologicalRing.IsPowerBounded _ _ (quotientPlusFSubXIdealTopology B b)
      ((Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) b)) := by
  rw [quotient_algebraMap_b_eq_X B b]
  have hrange_eq : (Set.range
        ((Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X ^ · :
          ℕ → ↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)) =
      (Ideal.Quotient.mk (plusFSubXIdeal B b)) ''
        Set.range (TateAlgebra.X (A := B) ^ · : ℕ → _) := by
    ext y; constructor
    · rintro ⟨n, rfl⟩
      refine ⟨TateAlgebra.X ^ n, ⟨n, rfl⟩, ?_⟩
      rw [map_pow]
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, by rw [map_pow]⟩
  change @TopologicalRing.IsBounded _ _ (quotientPlusFSubXIdealTopology B b) _
  rw [hrange_eq]
  exact IsBounded_mk_image_of_IsBounded B b (TateAlgebra_X_isPowerBounded B)

/-- `plusLocToQuotient B b` is continuous from the `trivialPlusDatum` localization
topology on `Localization.Away 1` to the quotient topology on
`TateAlgebra B ⧸ plusFSubXIdeal B b`.

**Strategy:** Apply `locTopology_continuous_lift`. This reduces to two conditions:
1. `plusLocToQuotient ∘ algebraMap B (Localization.Away 1) = mk ∘ algebraMap B (TateAlgebra B)`
   is continuous. Uses `tateAlgebra_algebraMap_continuous` + `continuous_quotient_mk'`.
2. For each `t ∈ T = {b}`, `plusLocToQuotient(divByS t 1)` is power-bounded in
   the quotient. Since `divByS b 1 = algebraMap b`, this is
   `mk(algebraMap b)`, which equals `mk(X)` in the quotient (by
   `quotient_algebraMap_b_eq_X`). `mk(X)` is power-bounded because `X` lies in
   the ring of definition `pairSubring`. -/
theorem plusLocToQuotient_continuous (P : PairOfDefinition B) (b : B) :
    @Continuous _ _ (trivialPlusDatum B P b).topology
      (quotientPlusFSubXIdealTopology B b)
      (plusLocToQuotient B b) := by
  letI : TopologicalSpace (Localization.Away (1 : B)) := (trivialPlusDatum B P b).topology
  letI : IsTopologicalRing (Localization.Away (1 : B)) := (trivialPlusDatum B P b).isTopologicalRing
  letI : IsTopologicalAddGroup (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).isTopologicalAddGroup
  letI : TopologicalSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology B b
  letI hring : IsTopologicalRing (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology_isTopologicalRing B b
  letI hadd : IsTopologicalAddGroup (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology_isTopologicalAddGroup B b
  haveI hNA_tate : @NonarchimedeanRing ↥(TateAlgebra B) _ instTopologicalSpaceTateAlgebra :=
    tateAlgBasis'.nonarchimedean
  haveI : @NonarchimedeanRing (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      _ (quotientPlusFSubXIdealTopology B b) := by
    constructor; intro U hU
    have hcont : @Continuous _ _ instTopologicalSpaceTateAlgebra
        (quotientPlusFSubXIdealTopology B b)
        (Ideal.Quotient.mk (plusFSubXIdeal B b)) :=
      continuous_quotient_mk'
    have hU' : (Ideal.Quotient.mk (plusFSubXIdeal B b)) ⁻¹' (U : Set _) ∈
        @nhds _ instTopologicalSpaceTateAlgebra (0 : ↥(TateAlgebra B)) :=
      hcont.continuousAt.preimage_mem_nhds hU
    obtain ⟨V, hVU⟩ := @NonarchimedeanRing.is_nonarchimedean _ _ _ hNA_tate _ hU'
    exact ⟨{
      toAddSubgroup := V.toAddSubgroup.map
        (Ideal.Quotient.mk (plusFSubXIdeal B b)).toAddMonoidHom
      isOpen' := @QuotientRing.isOpenMap_coe _ instTopologicalSpaceTateAlgebra _
        (plusFSubXIdeal B b) instIsTopologicalRingTateAlgebra _ V.isOpen
    }, fun x hx => by obtain ⟨y, hy, rfl⟩ := hx; exact hVU hy⟩
  apply locTopology_continuous_lift (trivialPlusDatum B P b).P (trivialPlusDatum B P b).T
    (trivialPlusDatum B P b).s (trivialPlusDatum B P b).hopen
    (plusLocToQuotient B b)
  · change @Continuous _ _ _ (quotientPlusFSubXIdealTopology B b)
        ((plusLocToQuotient B b).comp (algebraMap B (Localization.Away (1 : B))))
    have heq : (plusLocToQuotient B b).comp
        (algebraMap B (Localization.Away (1 : B))) =
        (Ideal.Quotient.mk (plusFSubXIdeal B b)).comp
          (algebraMap B ↥(TateAlgebra B)) := by
      ext a
      simp only [RingHom.comp_apply]
      exact plusLocToQuotient_algebraMap B b a
    rw [show ⇑((plusLocToQuotient B b).comp (algebraMap B (Localization.Away (1 : B)))) =
          ⇑((Ideal.Quotient.mk (plusFSubXIdeal B b)).comp (algebraMap B ↥(TateAlgebra B)))
          from congr_arg _ heq]
    exact mk_algebraMap_continuous_plusFSubX B b
  · intro t ht
    have htb : t = b := Finset.mem_singleton.mp ht
    rw [htb]
    change @TopologicalRing.IsPowerBounded _ _ (quotientPlusFSubXIdealTopology B b)
      (plusLocToQuotient B b (divByS b (trivialPlusDatum B P b).s))
    change @TopologicalRing.IsPowerBounded _ _ (quotientPlusFSubXIdealTopology B b)
      (plusLocToQuotient B b (divByS b (1 : B)))
    rw [divByS_eq_algebraMap, plusLocToQuotient_algebraMap]
    exact mk_algebraMap_b_isPowerBounded_in_quotientPlusFSubX B b

end Example638PlusBackwardContinuity

section Example638PlusBackwardCompletion

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

open TateAlgebra

/-- Backward ring hom `presheafValue (trivialPlusDatum B P b) →+*
TateAlgebra B ⧸ plusFSubXIdeal B b`, obtained by extending `plusLocToQuotient`
to the completion via `UniformSpace.Completion.extensionHom`.

Requires completeness + T0 of the target (the canonical quotient topology), which
follow from `quotient_plusFSubXIdeal_completeSpace` and `quotient_plusFSubXIdeal_t2Space`. -/
noncomputable def example638Plus_backwardHom
    (P : PairOfDefinition B) (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition)) :
    presheafValue (trivialPlusDatum B P b) →+*
      ↥(TateAlgebra B) ⧸ plusFSubXIdeal B b := by
  letI : UniformSpace (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).uniformSpace
  letI : IsTopologicalRing (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).isUniformAddGroup
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
  haveI hT2Q : @T2Space _ (quotientPlusFSubXIdealTopology B b) :=
    quotient_plusFSubXIdeal_t2Space B hA_complete hnoeth b
  haveI hT0Q : @T0Space _ (quotientPlusFSubXIdealTopology B b) :=
    @T1Space.t0Space _ (quotientPlusFSubXIdealTopology B b) (T2Space.t1Space)
  exact @UniformSpace.Completion.extensionHom _ _ _ _ _ _
    (quotientPlusFSubXIdealUniformSpace B b) _
    (quotientPlusFSubXIdeal_isUniformAddGroup B b)
    (quotientPlusFSubXIdealTopology_isTopologicalRing B b)
    (plusLocToQuotient B b)
    (plusLocToQuotient_continuous B P b)
    (quotient_plusFSubXIdeal_completeSpace B hA_complete hnoeth b)
    hT0Q

/-- On the dense image `coeRingHom a`, `example638Plus_backwardHom` agrees with
`plusLocToQuotient`. -/
theorem example638Plus_backwardHom_coe
    (P : PairOfDefinition B) (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (a : Localization.Away (1 : B)) :
    example638Plus_backwardHom B P b hA_complete hnoeth
        ((trivialPlusDatum B P b).coeRingHom a) =
      plusLocToQuotient B b a := by
  letI : UniformSpace (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).uniformSpace
  letI : IsTopologicalRing (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).isUniformAddGroup
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
  haveI hT2Q : @T2Space _ (quotientPlusFSubXIdealTopology B b) :=
    quotient_plusFSubXIdeal_t2Space B hA_complete hnoeth b
  haveI hT0Q : @T0Space _ (quotientPlusFSubXIdealTopology B b) :=
    @T1Space.t0Space _ (quotientPlusFSubXIdealTopology B b) (T2Space.t1Space)
  exact @UniformSpace.Completion.extensionHom_coe _ _ _ _ _ _
    (quotientPlusFSubXIdealUniformSpace B b) _
    (quotientPlusFSubXIdeal_isUniformAddGroup B b)
    (quotientPlusFSubXIdealTopology_isTopologicalRing B b)
    (plusLocToQuotient B b)
    (plusLocToQuotient_continuous B P b)
    (quotient_plusFSubXIdeal_completeSpace B hA_complete hnoeth b)
    hT0Q a

/-- `example638Plus_backwardHom` sends `canonicalMap a` to `mk(algebraMap a)`. -/
theorem example638Plus_backwardHom_canonicalMap
    (P : PairOfDefinition B) (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (a : B) :
    example638Plus_backwardHom B P b hA_complete hnoeth
        ((trivialPlusDatum B P b).canonicalMap a) =
      (Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) a) := by
  change example638Plus_backwardHom B P b hA_complete hnoeth
    ((trivialPlusDatum B P b).coeRingHom
      (algebraMap B (Localization.Away (1 : B)) a)) = _
  rw [example638Plus_backwardHom_coe, plusLocToQuotient_algebraMap]

end Example638PlusBackwardCompletion

section Example638PlusRoundTrip

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

open TateAlgebra

/-- `backward ∘ forward = id` on `TateAlgebra B ⧸ plusFSubXIdeal B b`. -/
theorem example638Plus_backward_forward_eq_id
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b)) :
    (example638Plus_backwardHom B P b hA_complete hnoeth).comp
      (example638Plus_forwardHom B P b) =
      RingHom.id _ := by
  letI : TopologicalSpace ↥(TateAlgebra B) := instTopologicalSpaceTateAlgebra
  letI : TopologicalSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology B b
  haveI hT2Q : @T2Space _ (quotientPlusFSubXIdealTopology B b) :=
    quotient_plusFSubXIdeal_t2Space B hA_complete hnoeth b
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  change (example638Plus_backwardHom B P b hA_complete hnoeth)
    (example638Plus_forwardHom B P b (Ideal.Quotient.mk _ x)) =
    Ideal.Quotient.mk _ x
  change (example638Plus_backwardHom B P b hA_complete hnoeth)
    (Ideal.Quotient.lift _ (example638Plus_evalHom B P b) _
      (Ideal.Quotient.mk _ x)) = _
  rw [Ideal.Quotient.lift_mk]
  letI : UniformSpace (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).isTopologicalRing
  letI : UniformSpace (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (trivialPlusDatum B P b).s) :=
    (trivialPlusDatum B P b).isTopologicalRing
  letI : UniformSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealUniformSpace B b
  letI : IsUniformAddGroup (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdeal_isUniformAddGroup B b
  letI : IsTopologicalRing (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology_isTopologicalRing B b
  haveI : CompleteSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotient_plusFSubXIdeal_completeSpace B hA_complete hnoeth b
  have hbwd_cont : @Continuous _ _
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (quotientPlusFSubXIdealTopology B b)
      (example638Plus_backwardHom B P b hA_complete hnoeth) :=
    UniformSpace.Completion.continuous_extension
  have hevalHom_cont : @Continuous _ _ instTopologicalSpaceTateAlgebra
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_evalHom B P b) := by
    have heq : (example638Plus_evalHom B P b : ↥(TateAlgebra B) → _) =
        (example638Plus_forwardHom B P b ∘ Ideal.Quotient.mk (plusFSubXIdeal B b)) := by
      ext y
      change example638Plus_evalHom B P b y =
        example638Plus_forwardHom B P b (Ideal.Quotient.mk _ y)
      change _ = Ideal.Quotient.lift _ (example638Plus_evalHom B P b) _
        (Ideal.Quotient.mk _ y)
      rw [Ideal.Quotient.lift_mk]
    rw [show (example638Plus_evalHom B P b : ↥(TateAlgebra B) → _) =
        example638Plus_forwardHom B P b ∘
          (Ideal.Quotient.mk (plusFSubXIdeal B b) : ↥(TateAlgebra B) → _)
        from heq]
    exact hcont_forward.comp continuous_quotient_mk'
  have hLHS_cont : @Continuous _ _ instTopologicalSpaceTateAlgebra
      (quotientPlusFSubXIdealTopology B b)
      ((example638Plus_backwardHom B P b hA_complete hnoeth) ∘
        (example638Plus_evalHom B P b)) :=
    hbwd_cont.comp hevalHom_cont
  have hRHS_cont : @Continuous _ _ instTopologicalSpaceTateAlgebra
      (quotientPlusFSubXIdealTopology B b)
      (Ideal.Quotient.mk (plusFSubXIdeal B b)) :=
    continuous_quotient_mk'
  have hS_dense : @Dense (↥(TateAlgebra B)) instTopologicalSpaceTateAlgebra
      {g : ↥(TateAlgebra B) |
        ∃ N : ℕ, ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0} :=
    tateAlgebra_polynomials_dense_canonical (A := B)
  have hagree : @Set.EqOn _ _
      ((example638Plus_backwardHom B P b hA_complete hnoeth) ∘
        (example638Plus_evalHom B P b))
      (Ideal.Quotient.mk (plusFSubXIdeal B b))
      {g | ∃ N : ℕ, ∀ n : Fin 1 →₀ ℕ, N ≤ n 0 → g.val n = 0} := by
    intro g ⟨N, hN⟩
    revert g
    induction N with
    | zero =>
      intro g hN
      have hg0 : g = 0 := by
        ext n
        exact hN (TateAlgebra.toIndex n)
          (by simp [TateAlgebra.toIndex, Finsupp.single_eq_same])
      simp [hg0, Function.comp]
    | succ k ih =>
      intro g hN
      set a := TateAlgebra.coeff k g with ha_def
      set gk : ↥(TateAlgebra B) := algebraMap B _ a * TateAlgebra.X ^ k with hgk_def
      have hcoeff_X_pow : ∀ m j : ℕ,
          TateAlgebra.coeff m (TateAlgebra.X ^ j : ↥(TateAlgebra B)) =
          if m = j then 1 else 0 := by
        intro m j; revert m; induction j with
        | zero => intro m; simp [pow_zero, TateAlgebra.coeff, TateAlgebra.toIndex,
            MvPowerSeries.coeff_one]
        | succ j ihj =>
          intro m; rw [pow_succ, mul_comm]
          cases m with
          | zero => rw [TateAlgebra.coeff_zero_X_mul, if_neg (by omega)]
          | succ m => rw [TateAlgebra.coeff_succ_X_mul, ihj m]; simp
      have hg'_vanish : ∀ n : Fin 1 →₀ ℕ, k ≤ n 0 → (g - gk).val n = 0 := by
        intro n hn
        rw [TateAlgebra.eq_toIndex n]
        change TateAlgebra.coeff (n 0) (g - gk) = 0
        rw [TateAlgebra.coeff_sub, hgk_def, TateAlgebra.coeff_algebraMap_mul,
          hcoeff_X_pow (n 0) k]
        by_cases hnk : n 0 = k
        · rw [if_pos hnk, mul_one, ha_def, hnk, sub_self]
        · rw [if_neg hnk, mul_zero, sub_zero]
          have hn_gt : k + 1 ≤ n 0 := by omega
          change (MvPowerSeries.coeff (TateAlgebra.toIndex (n 0))) g.val = 0
          rw [MvPowerSeries.coeff_apply]
          exact hN _ (by simp [TateAlgebra.toIndex, Finsupp.single_eq_same]; omega)
      have hg'_agree : ((example638Plus_backwardHom B P b hA_complete hnoeth) ∘
          example638Plus_evalHom B P b) (g - gk) =
          (Ideal.Quotient.mk (plusFSubXIdeal B b)) (g - gk) := ih hg'_vanish
      have hgk_agree :
          (example638Plus_backwardHom B P b hA_complete hnoeth)
            (example638Plus_evalHom B P b gk) =
          (Ideal.Quotient.mk (plusFSubXIdeal B b)) gk := by
        rw [hgk_def, map_mul, map_pow, example638Plus_evalHom_algebraMap,
          example638Plus_evalHom_X, map_mul, map_pow,
          example638Plus_backwardHom_canonicalMap,
          example638Plus_backwardHom_canonicalMap, map_mul, map_pow,
          quotient_algebraMap_b_eq_X]
      have hg_eq : g = (g - gk) + gk := by ring
      simp only [Function.comp] at hg'_agree ⊢
      rw [hg_eq, map_add, map_add, hg'_agree, hgk_agree, ← map_add]
  exact congr_fun (Continuous.ext_on hS_dense hLHS_cont hRHS_cont hagree) x

/-- `forward ∘ backward = id` on `presheafValue (trivialPlusDatum B P b)`. -/
theorem example638Plus_forward_backward_eq_id
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b)) :
    (example638Plus_forwardHom B P b).comp
      (example638Plus_backwardHom B P b hA_complete hnoeth) =
      RingHom.id _ := by
  letI : UniformSpace (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).uniformSpace
  letI : IsUniformAddGroup (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).isUniformAddGroup
  letI : IsTopologicalRing (Localization.Away (1 : B)) :=
    (trivialPlusDatum B P b).isTopologicalRing
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
  apply RingHom.ext
  intro y
  change example638Plus_forwardHom B P b
    (example638Plus_backwardHom B P b hA_complete hnoeth y) = y
  refine @UniformSpace.Completion.ext' _ _
    (presheafValue (trivialPlusDatum B P b)) _ _ _ _
    (hcont_forward.comp
      UniformSpace.Completion.continuous_extension)
    continuous_id ?_ y
  intro a
  change example638Plus_forwardHom B P b
    (example638Plus_backwardHom B P b hA_complete hnoeth
      (UniformSpace.Completion.coeRingHom a)) = UniformSpace.Completion.coeRingHom a
  have hbwd : example638Plus_backwardHom B P b hA_complete hnoeth
      (UniformSpace.Completion.coeRingHom a) =
      plusLocToQuotient B b a :=
    example638Plus_backwardHom_coe B P b hA_complete hnoeth a
  rw [hbwd]
  suffices h : (example638Plus_forwardHom B P b).comp (plusLocToQuotient B b) =
      (trivialPlusDatum B P b).coeRingHom from congr_fun (congrArg DFunLike.coe h) a
  apply IsLocalization.ringHom_ext (Submonoid.powers (1 : B))
  ext c
  change example638Plus_forwardHom B P b
      (plusLocToQuotient B b (algebraMap B (Localization.Away (1 : B)) c)) =
    (trivialPlusDatum B P b).coeRingHom (algebraMap B _ c)
  rw [plusLocToQuotient_algebraMap]
  change Ideal.Quotient.lift _ (example638Plus_evalHom B P b) _
      ((Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) c)) =
    (trivialPlusDatum B P b).coeRingHom (algebraMap B _ c)
  rw [Ideal.Quotient.lift_mk, example638Plus_evalHom_algebraMap]
  rfl

end Example638PlusRoundTrip

section Example638PlusEquiv

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

open TateAlgebra

/-- **R3 plus-branch identification (Wedhorn Example 6.38):** for a principal
Tate ring `B` and `b : B`, the Tate-algebra quotient `B⟨X⟩/(algebraMap b − X)`
(with canonical quotient topology) is ring-isomorphic to
`presheafValue (trivialPlusDatum P b)`, the completion of `Localization.Away 1`
(≃ `B`) with the localization topology.

The `hcont_forward` hypothesis is needed for the round-trip identities — it
asserts that `example638Plus_forwardHom` is continuous with the canonical
quotient topology on its source. This is the plus-branch analogue of the
continuity hypothesis carried by `example638Minus_equiv`. -/
noncomputable def example638Plus_equiv
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b)) :
    ↥(TateAlgebra B) ⧸ plusFSubXIdeal B b ≃+*
      presheafValue (trivialPlusDatum B P b) where
  toFun := example638Plus_forwardHom B P b
  invFun := example638Plus_backwardHom B P b hA_complete hnoeth
  left_inv x :=
    congr_fun (congrArg DFunLike.coe
      (example638Plus_backward_forward_eq_id B P b hA_complete hnoeth hcont_forward)) x
  right_inv y :=
    congr_fun (congrArg DFunLike.coe
      (example638Plus_forward_backward_eq_id B P b hA_complete hnoeth hcont_forward)) y
  map_mul' := map_mul _
  map_add' := map_add _

/-- The forward direction of `example638Plus_equiv` sends `mk(algebraMap a)` to
`canonicalMap a`. -/
theorem example638Plus_equiv_mk_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b))
    (a : B) :
    example638Plus_equiv B P b hA_complete hnoeth hcont_forward
        ((Ideal.Quotient.mk (plusFSubXIdeal B b))
          (algebraMap B ↥(TateAlgebra B) a)) =
      (trivialPlusDatum B P b).canonicalMap a := by
  change example638Plus_forwardHom B P b
      ((Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) a)) = _
  change Ideal.Quotient.lift _ (example638Plus_evalHom B P b) _
      ((Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) a)) = _
  rw [Ideal.Quotient.lift_mk]
  exact example638Plus_evalHom_algebraMap B P b a

/-- The forward direction of `example638Plus_equiv` sends `mk(X)` to `canonicalMap b`. -/
theorem example638Plus_equiv_mk_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b)) :
    example638Plus_equiv B P b hA_complete hnoeth hcont_forward
        ((Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X) =
      (trivialPlusDatum B P b).canonicalMap b := by
  change example638Plus_forwardHom B P b
      ((Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X) = _
  change Ideal.Quotient.lift _ (example638Plus_evalHom B P b) _
      ((Ideal.Quotient.mk (plusFSubXIdeal B b)) TateAlgebra.X) = _
  rw [Ideal.Quotient.lift_mk]
  exact example638Plus_evalHom_X B P b

/-- The inverse direction of `example638Plus_equiv` sends `canonicalMap a` to
`mk(algebraMap a)`. -/
theorem example638Plus_equiv_symm_canonicalMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b))
    (a : B) :
    (example638Plus_equiv B P b hA_complete hnoeth hcont_forward).symm
        ((trivialPlusDatum B P b).canonicalMap a) =
      (Ideal.Quotient.mk (plusFSubXIdeal B b))
        (algebraMap B ↥(TateAlgebra B) a) := by
  change example638Plus_backwardHom B P b hA_complete hnoeth
      ((trivialPlusDatum B P b).canonicalMap a) = _
  exact example638Plus_backwardHom_canonicalMap B P b hA_complete hnoeth a

end Example638PlusEquiv

section Example638PlusEquivTopology

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

open TateAlgebra

/-- **T145: `example638Plus_forwardHom` is a topological homeomorphism**
from the canonical quotient `B⟨X⟩ ⧸ (algebraMap b − X)` to the presheafValue of
the trivial plus datum. -/
theorem example638Plus_isHomeomorph
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b))
    (hBaire : @BaireSpace (presheafValue (trivialPlusDatum B P b)) _)
    (hSigma : @SigmaCompactSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      (quotientPlusFSubXIdealTopology B b)) :
    @IsHomeomorph _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b) := by
  letI τC : TopologicalSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology B b
  letI : IsTopologicalRing (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology_isTopologicalRing B b
  letI : IsTopologicalAddGroup (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology_isTopologicalAddGroup B b
  letI uC : UniformSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealUniformSpace B b
  haveI : @IsUniformAddGroup _ uC _ :=
    quotientPlusFSubXIdeal_isUniformAddGroup B b
  haveI : @CompleteSpace _ uC :=
    quotient_plusFSubXIdeal_completeSpace B hA_complete hnoeth b
  haveI : T2Space (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotient_plusFSubXIdeal_t2Space B hA_complete hnoeth b
  let e := example638Plus_equiv B P b hA_complete hnoeth hcont_forward
  have hbij : Function.Bijective (example638Plus_forwardHom B P b) :=
    ⟨e.injective, e.surjective⟩
  have hopen : @IsOpenMap _ _ τC _ (example638Plus_forwardHom B P b) :=
    @AddMonoidHom.isOpenMap_of_complete_countable
      (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      (presheafValue (trivialPlusDatum B P b))
      _ uC ‹_› _ hSigma
      _ _ _ hBaire _
      (example638Plus_forwardHom B P b).toAddMonoidHom
      hbij.2 hcont_forward
  exact {
    continuous := hcont_forward
    isOpenMap := hopen
    bijective := hbij
  }

/-- **T145: `example638Plus_equiv` is `IsInducing`** (forward direction:
`B⟨X⟩ ⧸ (algebraMap b − X) → presheafValue (trivialPlusDatum P b)`). -/
theorem example638Plus_equiv_isInducing
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b))
    (hBaire : @BaireSpace (presheafValue (trivialPlusDatum B P b)) _)
    (hSigma : @SigmaCompactSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      (quotientPlusFSubXIdealTopology B b)) :
    @Topology.IsInducing _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      ((example638Plus_equiv B P b hA_complete hnoeth hcont_forward) :
        ↥(TateAlgebra B) ⧸ plusFSubXIdeal B b →
          presheafValue (trivialPlusDatum B P b)) :=
  (example638Plus_isHomeomorph B P b hA_complete hnoeth hcont_forward hBaire
    hSigma).isInducing

/-- **T145: `(example638Plus_equiv).symm` is `IsInducing`** (inverse direction:
`presheafValue (trivialPlusDatum P b) → B⟨X⟩ ⧸ (algebraMap b − X)`).

This is the form consumed by the Laurent plus bridge identification
`presheafValue_trivialPlus_fSubX_equiv` in `LaurentRefinement.lean`, which
is defined as `(example638Plus_equiv ...).symm`. -/
theorem example638Plus_equiv_symm_isInducing
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_forward : @Continuous _ _
      (quotientPlusFSubXIdealTopology B b)
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (example638Plus_forwardHom B P b))
    (hBaire : @BaireSpace (presheafValue (trivialPlusDatum B P b)) _)
    (hSigma : @SigmaCompactSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b)
      (quotientPlusFSubXIdealTopology B b)) :
    @Topology.IsInducing _ _
      (inferInstance : TopologicalSpace (presheafValue (trivialPlusDatum B P b)))
      (quotientPlusFSubXIdealTopology B b)
      (((example638Plus_equiv B P b hA_complete hnoeth hcont_forward).symm) :
        presheafValue (trivialPlusDatum B P b) →
          ↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) := by
  letI τC : TopologicalSpace (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) :=
    quotientPlusFSubXIdealTopology B b
  have h := example638Plus_isHomeomorph B P b hA_complete hnoeth hcont_forward
    hBaire hSigma
  let H : (↥(TateAlgebra B) ⧸ plusFSubXIdeal B b) ≃ₜ
      presheafValue (trivialPlusDatum B P b) :=
    h.homeomorph (example638Plus_forwardHom B P b)
  have h_eq : (((example638Plus_equiv B P b hA_complete hnoeth hcont_forward).symm) :
        presheafValue _ → _) = (H.symm : presheafValue _ → _) := by
    funext y
    apply H.injective
    rw [Homeomorph.apply_symm_apply]
    change example638Plus_forwardHom B P b _ = y
    exact (example638Plus_equiv B P b hA_complete hnoeth hcont_forward).right_inv y
  rw [h_eq]
  exact H.symm.isInducing

end Example638PlusEquivTopology

section Example638MinusForward

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- `invS D = D.coeRingHom (divByS 1 D.s)`: both are the inverse of
`D.canonicalMap D.s` in `presheafValue D`, hence equal. -/
theorem invS_eq_coeRingHom_divByS_one (D : RationalLocData A) :
    invS D = D.coeRingHom (divByS 1 D.s) := by
  have h1 : D.canonicalMap D.s * invS D = 1 := canonicalMap_s_mul_invS D
  have halg : algebraMap A (Localization.Away D.s) D.s * divByS 1 D.s = 1 := by
    rw [← invSelf_eq_divByS, IsLocalization.Away.mul_invSelf]
  have h2 : D.canonicalMap D.s * D.coeRingHom (divByS 1 D.s) = 1 := by
    change D.coeRingHom (algebraMap A (Localization.Away D.s) D.s) *
      D.coeRingHom (divByS 1 D.s) = 1
    rw [← map_mul, halg, map_one]
  have hu : IsUnit (D.canonicalMap D.s) := isUnit_s_in_presheafValue D
  exact hu.mul_left_cancel (h1.trans h2.symm)

/-- `invS` in the trivial minus datum is power-bounded (via `1 ∈ D.T = {1}`). -/
theorem invS_isPowerBounded_in_trivialMinus
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    TopologicalRing.IsPowerBounded (invS (trivialMinusDatum B P b)) := by
  rw [invS_eq_coeRingHom_divByS_one]
  exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T
    (trivialMinusDatum B P b) (Finset.mem_singleton_self 1)

/-- The generic evaluation hom `TateAlgebra B →+* presheafValue (trivialMinusDatum P b)`
sending `X ↦ invS = 1 / canonicalMap b`, via `tateEvalPresheafHom`. -/
noncomputable def example638Minus_evalHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra B) →+* presheafValue (trivialMinusDatum B P b) :=
  tateEvalPresheafHom (trivialMinusDatum B P b)
    (invS_isPowerBounded_in_trivialMinus B P b)

/-- `example638Minus_evalHom` sends `algebraMap(a)` to `canonicalMap(a)`. -/
theorem example638Minus_evalHom_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b a : B) :
    example638Minus_evalHom B P b (algebraMap B _ a) =
      (trivialMinusDatum B P b).canonicalMap a :=
  tateEvalPresheafHom_algebraMap (trivialMinusDatum B P b)
    (invS_isPowerBounded_in_trivialMinus B P b) a

/-- `example638Minus_evalHom` sends `X` to `invS` = `1 / canonicalMap b`. -/
theorem example638Minus_evalHom_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Minus_evalHom B P b TateAlgebra.X =
      invS (trivialMinusDatum B P b) :=
  tateEvalPresheafHom_X (trivialMinusDatum B P b)
    (invS_isPowerBounded_in_trivialMinus B P b)

/-- Key identity: `canonicalMap b * invS = 1` in `presheafValue (trivialMinusDatum P b)`.
Since `(trivialMinusDatum P b).s = b`, this is just `canonicalMap_s_mul_invS`. -/
theorem canonicalMap_b_mul_invS_eq_one_in_trivialMinus
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    (trivialMinusDatum B P b).canonicalMap b *
      invS (trivialMinusDatum B P b) = 1 :=
  canonicalMap_s_mul_invS (trivialMinusDatum B P b)

/-- The ideal `(1 - algebraMap b · X)` maps to zero under `example638Minus_evalHom`. -/
theorem example638Minus_evalHom_oneSubfX_eq_zero
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Minus_evalHom B P b
      (1 - algebraMap B ↥(TateAlgebra B) b * TateAlgebra.X) = 0 := by
  rw [map_sub, map_one, map_mul, example638Minus_evalHom_algebraMap,
      example638Minus_evalHom_X,
      canonicalMap_b_mul_invS_eq_one_in_trivialMinus, sub_self]

/-- Forward ring hom
`TateAlgebra B ⧸ (1 − algebraMap b · X) → presheafValue (trivialMinusDatum P b)`,
obtained by factoring `example638Minus_evalHom` through the quotient. -/
noncomputable def example638Minus_forwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ↥(TateAlgebra B) ⧸ oneSubfXIdeal b →+*
        presheafValue (trivialMinusDatum B P b) :=
  Ideal.Quotient.lift _ (example638Minus_evalHom B P b) (fun y hy => by
    rw [oneSubfXIdeal, Ideal.mem_span_singleton'] at hy
    obtain ⟨c, hc⟩ := hy
    rw [← hc, map_mul, example638Minus_evalHom_oneSubfX_eq_zero, mul_zero])

end Example638MinusForward

section Example638MinusBackward

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

/-- `T = {1}` hypothesis for `trivialMinusDatum`: every `t ∈ {1}` is
power-bounded, namely `1` itself. -/
theorem trivialMinusDatum_hT_pb
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    ∀ t ∈ (trivialMinusDatum B P b).T, TopologicalRing.IsPowerBounded t := by
  intro t ht
  rw [Finset.mem_singleton.mp ht]
  exact TopologicalRing.isPowerBounded_one

/-- Backward ring hom `presheafValue (trivialMinusDatum B P b) →+* TateAlgebra B ⧸ oneSubfXIdeal b`,
obtained by reusing `presheafValueToCanonicalQuotient` at `D = trivialMinusDatum B P b`
(whose `.s = b`). Uses completeness/T2 of the canonical quotient via
`quotient_oneSubfXIdeal_completeSpace` and `quotient_oneSubfXIdeal_t2Space`. -/
noncomputable def example638Minus_backwardHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition)) :
    presheafValue (trivialMinusDatum B P b) →+*
      ↥(TateAlgebra B) ⧸ oneSubfXIdeal b :=
  presheafValueToCanonicalQuotient (trivialMinusDatum B P b)
    hA_complete hnoeth (trivialMinusDatum_hT_pb B P b)

/-- On the dense image `coeRingHom a`, `example638Minus_backwardHom` agrees
with `locToQuotientOneSubfX_gen b`. -/
theorem example638Minus_backwardHom_coe
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (a : Localization.Away b) :
    example638Minus_backwardHom B P b hA_complete hnoeth
        ((trivialMinusDatum B P b).coeRingHom a) =
      locToQuotientOneSubfX_gen b a :=
  presheafValueToCanonicalQuotient_coe (trivialMinusDatum B P b)
    hA_complete hnoeth (trivialMinusDatum_hT_pb B P b) a

/-- `example638Minus_backwardHom` sends `canonicalMap a` to `mk(algebraMap a)`. -/
theorem example638Minus_backwardHom_canonicalMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (a : B) :
    example638Minus_backwardHom B P b hA_complete hnoeth
        ((trivialMinusDatum B P b).canonicalMap a) =
      (Ideal.Quotient.mk (oneSubfXIdeal b))
        (algebraMap B ↥(TateAlgebra B) a) := by
  change example638Minus_backwardHom B P b hA_complete hnoeth
    ((trivialMinusDatum B P b).coeRingHom
      (algebraMap B (Localization.Away b) a)) = _
  rw [example638Minus_backwardHom_coe, locToQuotientOneSubfX_gen_algebraMap]

/-- `example638Minus_backwardHom` sends `invS` to `mk(X)`. -/
theorem example638Minus_backwardHom_invS
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition)) :
    example638Minus_backwardHom B P b hA_complete hnoeth
        (invS (trivialMinusDatum B P b)) =
      (Ideal.Quotient.mk (oneSubfXIdeal b)) TateAlgebra.X := by
  rw [invS_eq_coeRingHom_divByS_one]
  have hdiv : divByS (1 : B) (trivialMinusDatum B P b).s =
      IsLocalization.Away.invSelf (S := Localization.Away b) b := by
    change divByS (1 : B) b = IsLocalization.Away.invSelf b
    rw [← invSelf_eq_divByS]
  rw [hdiv, example638Minus_backwardHom_coe, locToQuotientOneSubfX_gen_invSelf]

/-- Identification: `example638Minus_forwardHom` equals
`tateQuotientToPresheafHom` applied at `D = trivialMinusDatum B P b`. -/
theorem example638Minus_forwardHom_eq_tateQuotientToPresheafHom
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B) :
    example638Minus_forwardHom B P b =
      tateQuotientToPresheafHom (trivialMinusDatum B P b)
        (invS_isPowerBounded_in_trivialMinus B P b) := rfl

/-- Identification: `example638Minus_backwardHom` equals
`presheafValueToCanonicalQuotient` applied at `D = trivialMinusDatum B P b`. -/
theorem example638Minus_backwardHom_eq_presheafValueToCanonicalQuotient
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition)) :
    example638Minus_backwardHom B P b hA_complete hnoeth =
      presheafValueToCanonicalQuotient (trivialMinusDatum B P b)
        hA_complete hnoeth (trivialMinusDatum_hT_pb B P b) := rfl

end Example638MinusBackward

section Example638MinusRoundTrip

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

/-- `backward ∘ forward = id` on `TateAlgebra B ⧸ oneSubfXIdeal b`.
Reduces to `tateQuotientToPresheaf_comp_presheafToCanonicalQuotient`. -/
theorem example638Minus_backward_forward_eq_id
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_eval : @Continuous _ _
      (TateAlgebra.quotientOneSubfXIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (trivialMinusDatum B P b)))
      (tateQuotientToPresheafHom (trivialMinusDatum B P b)
        (invS_isPowerBounded_in_trivialMinus B P b))) :
    (example638Minus_backwardHom B P b hA_complete hnoeth).comp
      (example638Minus_forwardHom B P b) =
      RingHom.id _ := by
  rw [example638Minus_forwardHom_eq_tateQuotientToPresheafHom,
    example638Minus_backwardHom_eq_presheafValueToCanonicalQuotient]
  apply RingHom.ext
  intro q
  change presheafValueToCanonicalQuotient (trivialMinusDatum B P b)
      hA_complete hnoeth (trivialMinusDatum_hT_pb B P b)
      (tateQuotientToPresheafHom (trivialMinusDatum B P b)
        (invS_isPowerBounded_in_trivialMinus B P b) q) = q
  exact presheafToCanonicalQuotient_comp_tateQuotientToPresheaf
    (trivialMinusDatum B P b)
    (invS_isPowerBounded_in_trivialMinus B P b)
    hA_complete hnoeth (trivialMinusDatum_hT_pb B P b)
    hcont_eval q

/-- `forward ∘ backward = id` on `presheafValue (trivialMinusDatum B P b)`.
Reduces to `tateQuotientToPresheaf_comp_presheafToCanonicalQuotient`. -/
theorem example638Minus_forward_backward_eq_id
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_eval : @Continuous _ _
      (TateAlgebra.quotientOneSubfXIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (trivialMinusDatum B P b)))
      (tateQuotientToPresheafHom (trivialMinusDatum B P b)
        (invS_isPowerBounded_in_trivialMinus B P b))) :
    (example638Minus_forwardHom B P b).comp
      (example638Minus_backwardHom B P b hA_complete hnoeth) =
      RingHom.id _ := by
  rw [example638Minus_forwardHom_eq_tateQuotientToPresheafHom,
    example638Minus_backwardHom_eq_presheafValueToCanonicalQuotient]
  apply RingHom.ext
  intro x
  change tateQuotientToPresheafHom (trivialMinusDatum B P b)
      (invS_isPowerBounded_in_trivialMinus B P b)
      (presheafValueToCanonicalQuotient (trivialMinusDatum B P b)
        hA_complete hnoeth (trivialMinusDatum_hT_pb B P b) x) = x
  exact tateQuotientToPresheaf_comp_presheafToCanonicalQuotient
    (trivialMinusDatum B P b)
    (invS_isPowerBounded_in_trivialMinus B P b)
    hA_complete hnoeth (trivialMinusDatum_hT_pb B P b)
    hcont_eval x

end Example638MinusRoundTrip

section Example638MinusEquiv

variable [IsTateRing B] [IsNoetherianRing B] [T2Space B] [NonarchimedeanRing B]

/-- **R3 minus-branch identification:** for a principal Tate ring `B` and
`b : B`, the Tate-algebra quotient `B⟨X⟩/(1 − bX)` (with canonical quotient
topology) is ring-isomorphic to `presheafValue (trivialMinusDatum P b)`, the
completion of `Localization.Away b` with the localization topology.

This is a direct specialisation of `presheafValueCanonicalQuotientEquiv` at
`D = trivialMinusDatum B P b` (whose `.s = b`), wrapped in `.symm` to reverse
the direction and exposed under the R3 primitive names. -/
noncomputable def example638Minus_equiv
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_eval : @Continuous _ _
      (TateAlgebra.quotientOneSubfXIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (trivialMinusDatum B P b)))
      (tateQuotientToPresheafHom (trivialMinusDatum B P b)
        (invS_isPowerBounded_in_trivialMinus B P b))) :
    ↥(TateAlgebra B) ⧸ oneSubfXIdeal b ≃+*
      presheafValue (trivialMinusDatum B P b) where
  toFun := example638Minus_forwardHom B P b
  invFun := example638Minus_backwardHom B P b hA_complete hnoeth
  left_inv x :=
    congr_fun (congrArg DFunLike.coe
      (example638Minus_backward_forward_eq_id B P b hA_complete hnoeth hcont_eval)) x
  right_inv y :=
    congr_fun (congrArg DFunLike.coe
      (example638Minus_forward_backward_eq_id B P b hA_complete hnoeth hcont_eval)) y
  map_mul' := map_mul _
  map_add' := map_add _

/-- The forward direction of `example638Minus_equiv` sends `mk(algebraMap a)` to
`canonicalMap a`. -/
theorem example638Minus_equiv_mk_algebraMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_eval : @Continuous _ _
      (TateAlgebra.quotientOneSubfXIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (trivialMinusDatum B P b)))
      (tateQuotientToPresheafHom (trivialMinusDatum B P b)
        (invS_isPowerBounded_in_trivialMinus B P b)))
    (a : B) :
    example638Minus_equiv B P b hA_complete hnoeth hcont_eval
        ((Ideal.Quotient.mk (oneSubfXIdeal b))
          (algebraMap B ↥(TateAlgebra B) a)) =
      (trivialMinusDatum B P b).canonicalMap a := by
  change example638Minus_forwardHom B P b
      ((Ideal.Quotient.mk (oneSubfXIdeal b))
        (algebraMap B ↥(TateAlgebra B) a)) = _
  change Ideal.Quotient.lift _ (example638Minus_evalHom B P b) _
      ((Ideal.Quotient.mk (oneSubfXIdeal b))
        (algebraMap B ↥(TateAlgebra B) a)) = _
  rw [Ideal.Quotient.lift_mk]
  exact example638Minus_evalHom_algebraMap B P b a

/-- The forward direction of `example638Minus_equiv` sends `mk(X)` to `invS`. -/
theorem example638Minus_equiv_mk_X
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_eval : @Continuous _ _
      (TateAlgebra.quotientOneSubfXIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (trivialMinusDatum B P b)))
      (tateQuotientToPresheafHom (trivialMinusDatum B P b)
        (invS_isPowerBounded_in_trivialMinus B P b))) :
    example638Minus_equiv B P b hA_complete hnoeth hcont_eval
        ((Ideal.Quotient.mk (oneSubfXIdeal b)) TateAlgebra.X) =
      invS (trivialMinusDatum B P b) := by
  change example638Minus_forwardHom B P b
      ((Ideal.Quotient.mk (oneSubfXIdeal b)) TateAlgebra.X) = _
  change Ideal.Quotient.lift _ (example638Minus_evalHom B P b) _
      ((Ideal.Quotient.mk (oneSubfXIdeal b)) TateAlgebra.X) = _
  rw [Ideal.Quotient.lift_mk]
  exact example638Minus_evalHom_X B P b

/-- The inverse direction of `example638Minus_equiv` sends `canonicalMap a` to
`mk(algebraMap a)`. -/
theorem example638Minus_equiv_symm_canonicalMap
    (P : PairOfDefinition B) [IsNoetherianRing P.A₀] (b : B)
    (hA_complete : @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair B).toPairOfDefinition))
    (hcont_eval : @Continuous _ _
      (TateAlgebra.quotientOneSubfXIdealTopology b)
      (inferInstance : TopologicalSpace (presheafValue (trivialMinusDatum B P b)))
      (tateQuotientToPresheafHom (trivialMinusDatum B P b)
        (invS_isPowerBounded_in_trivialMinus B P b)))
    (a : B) :
    (example638Minus_equiv B P b hA_complete hnoeth hcont_eval).symm
        ((trivialMinusDatum B P b).canonicalMap a) =
      (Ideal.Quotient.mk (oneSubfXIdeal b))
        (algebraMap B ↥(TateAlgebra B) a) := by
  change example638Minus_backwardHom B P b hA_complete hnoeth
      ((trivialMinusDatum B P b).canonicalMap a) = _
  exact example638Minus_backwardHom_canonicalMap B P b hA_complete hnoeth a

end Example638MinusEquiv

end Example638

end ValuationSpectrum
