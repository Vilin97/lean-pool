/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.SheafyEndpoints
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ExampleUnitDisc

/-!
# Laurent compatibility: the CDVF endpoints specialise to the frozen Laurent theorems (K10)

The FJP→CDVF campaign generalised the finite-jet pinching algebra from the Laurent base
`K = LaurentSeries F` to an arbitrary complete discretely valued nonarchimedean field, in
the namespace `FiniteJetOver` (`FJP/Over/…`). The original Laurent development lives in the
`FiniteJet` namespace (`FJP/FiniteJet…`), and its five headline theorems — `FiniteJet.`
`finiteJet_isSheafy` / `isUniform` / `isDomain` / `not_noetherian` / `not_stablyUniform`
(`FJP/FiniteJetMain.lean`) — are **frozen**.

This file demonstrates that the generic development **recovers** those five theorems as thin
specialisations at `K = LaurentSeries F`, per the campaign ground rule "old Laurent API
becomes a thin specialization of the new generic development" — **without touching** the old
files or the frozen statements.

## The two ingredients

* **The pinching algebras coincide definitionally.**
  `FiniteJetOver.JetA (LaurentSeries F)` and `FiniteJet.JetA F` are both `↥(jetSupport …)`
  over the same ring `RestrictedLaurent (LaurentSeries F)`, hence equal by `rfl`
  (`jetA_eq`). So a `FiniteJetOver` conclusion about `JetA (LaurentSeries F)` *is* a
  conclusion about the Laurent `FiniteJet.JetA F`.

* **`𝒪[LaurentSeries F]` is a discrete valuation ring.** The layer-2 `_of_dvr` endpoints
  need `[IsDiscreteValuationRing 𝒪[K]]`; here `𝒪[LaurentSeries F] ≅ F⟦X⟧` is a DVR. We
  transport mathlib's `IsDiscreteValuationRing F⟦X⟧` (`PowerSeries/Inverse.lean`) along the
  ring isomorphism `F⟦X⟧ ≃+* 𝒪[LaurentSeries F]` assembled from
  `LaurentSeries.powerSeriesEquivSubring` and the campaign's `FiniteJetOver.`
  `unitBallEquivInteger`.

The three remaining base-field instances the endpoints require for `LaurentSeries F` are
already available: `NontriviallyNormedField` and `IsUltrametricDist` from mathlib's rank-one
valued-field API (`Valued.toNontriviallyNormedField`, through the `Valuation.RankOne`
instance of `ExampleUnitDisc.lean`), and `CompleteSpace` from `ExampleLaurentSeries.lean`.

## Two technical notes, both about the `𝒪[·]` elaboration

* The pinned mathlib does not expose `RingEquivClass.isDiscreteValuationRing`; the transport
  `isDiscreteValuationRing_of_ringEquiv` is reproved here from the available primitives
  `IsPrincipalIdealRing.of_surjective`, `RingEquiv.isLocalRing`, `MulEquiv.isField`.
* `LaurentSeries F` carries *two* valued structures: mathlib's native `Valued … ℤᵐ⁰` and the
  norm-induced `NormedField.toValued … ℝ≥0` (the one the endpoints use). Writing
  `𝒪[LaurentSeries F]` literally resolves to the former, whereas the DVR the endpoints need
  is on the latter; so the transported term's type is obtained **by inference** from
  `unitBallEquivInteger`'s codomain rather than by spelling the notation.
-/

noncomputable section

open scoped NormedField Valued LaurentSeries PowerSeries

namespace FiniteJet.Compat

/-- **DVR transport along a ring isomorphism** (pinned-mathlib gap filler): a ring
isomorphic to a discrete valuation ring is itself one. Reproves the absent
`RingEquivClass.isDiscreteValuationRing` from `IsPrincipalIdealRing.of_surjective`,
`RingEquiv.isLocalRing` and `MulEquiv.isField`. -/
theorem isDiscreteValuationRing_of_ringEquiv {A B : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] (e : A ≃+* B) :
    IsDiscreteValuationRing B := by
  letI : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  letI : IsLocalRing B := e.isLocalRing
  refine { not_a_field' := ?_ }
  rw [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq]
  exact fun hB => IsDiscreteValuationRing.not_isField A (MulEquiv.isField hB e.toMulEquiv)

variable (F : Type*) [Field F]

/-! ### The definitional identification `FiniteJetOver.JetA (LaurentSeries F) = FiniteJet.JetA F` -/

/-- The generic pinching algebra over `LaurentSeries F` is **definitionally** the Laurent
pinching algebra: both are `↥(jetSupport …)` over `RestrictedLaurent (LaurentSeries F)`. -/
theorem jetA_eq : FiniteJetOver.JetA (LaurentSeries F) = FiniteJet.JetA F := rfl

/-! ### `𝒪[LaurentSeries F]` is a discrete valuation ring -/

/-- The unit ball of `LaurentSeries F` (`{‖·‖ ≤ 1}`) is, as a subring, the image of `F⟦X⟧`:
`‖f‖ ≤ 1` exactly when `f` is a power series. -/
theorem unitBall_eq_powerSeries_as_subring :
    FiniteJet.unitBall (LaurentSeries F) = LaurentSeries.powerSeries_as_subring F := by
  ext x
  rw [FiniteJet.mem_unitBall_iff, Valued.toNormedField.norm_le_one_iff,
    LaurentSeries.val_le_one_iff_eq_coe]
  constructor
  · rintro ⟨G, rfl⟩; exact ⟨G, trivial, rfl⟩
  · rintro ⟨G, -, rfl⟩; exact ⟨G, rfl⟩

/-- `F⟦X⟧ ≃+* (unit ball of `LaurentSeries F`)`, via `LaurentSeries.powerSeriesEquivSubring`
and `unitBall_eq_powerSeries_as_subring`. -/
def powerSeriesEquivUnitBall : F⟦X⟧ ≃+* FiniteJet.unitBall (LaurentSeries F) :=
  (LaurentSeries.powerSeriesEquivSubring F).trans
    (RingEquiv.subringCongr (unitBall_eq_powerSeries_as_subring F).symm)

/-- `F⟦X⟧ ≃+* 𝒪[LaurentSeries F]` (the norm-induced valuation ring the endpoints use),
composing `powerSeriesEquivUnitBall` with the campaign's `FiniteJetOver.unitBallEquivInteger`.
The codomain is left to inference so that it is the `NormedField.toValued` integer — the one
the endpoints require — and not mathlib's native `ℤᵐ⁰` integer of `LaurentSeries F`. -/
def powerSeriesEquivInteger :=
  (powerSeriesEquivUnitBall F).trans (FiniteJetOver.unitBallEquivInteger (LaurentSeries F))

/-! ### The frozen five, recovered from the generic `_of_dvr` endpoints

Each statement is the frozen `FiniteJet.finiteJet_*` type verbatim (`jetA_eq` makes the
generic and Laurent pinching algebras definitionally the same), proved by the corresponding
`FiniteJetOver.…_of_dvr` endpoint. The `haveI` feeds the discrete-valuation-ring hypothesis
built above; `isDomain` and `not_noetherian` need no base-field hypothesis at all. -/

/-- **[FJP] Theorem 1.3 (sheafy), Laurent case, recovered.** Specialises
`FiniteJetOver.isSheafy_JetA_of_dvr` to `K = LaurentSeries F`; the type is the frozen
`FiniteJet.finiteJet_isSheafy F`. -/
theorem finiteJet_isSheafy : ValuationSpectrum.IsSheafy (FiniteJet.JetA F) := by
  haveI := isDiscreteValuationRing_of_ringEquiv (powerSeriesEquivInteger F)
  exact FiniteJetOver.isSheafy_JetA_of_dvr (LaurentSeries F)

/-- **[FJP] Theorem 1.3 (uniform), Laurent case, recovered.** -/
theorem finiteJet_isUniform : TopologicalRing.IsUniform (FiniteJet.JetA F) := by
  haveI := isDiscreteValuationRing_of_ringEquiv (powerSeriesEquivInteger F)
  exact FiniteJetOver.finiteJet_isUniform_of_dvr (LaurentSeries F)

/-- **[FJP] Theorem 1.3 (domain), Laurent case, recovered.** -/
theorem finiteJet_isDomain : IsDomain (FiniteJet.JetA F) :=
  FiniteJetOver.finiteJet_isDomain (LaurentSeries F)

/-- **[FJP] Theorem 1.3 (nonnoetherian), Laurent case, recovered.** -/
theorem finiteJet_not_noetherian : ¬ IsNoetherianRing (FiniteJet.JetA F) :=
  FiniteJetOver.finiteJet_not_noetherian (LaurentSeries F)

/-- **[FJP] Theorem 1.3 (not stably uniform), Laurent case, recovered.** -/
theorem finiteJet_not_stablyUniform : ¬ TopologicalRing.IsStablyUniform (FiniteJet.JetA F) := by
  haveI := isDiscreteValuationRing_of_ringEquiv (powerSeriesEquivInteger F)
  exact FiniteJetOver.finiteJet_not_stablyUniform_of_dvr (LaurentSeries F)

end FiniteJet.Compat
