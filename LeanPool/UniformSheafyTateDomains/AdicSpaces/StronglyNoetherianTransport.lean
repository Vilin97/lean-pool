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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletionModelIndependence

/-!
# Transport of strong noetherianity; the one-model wrapper (P3)

* `restrictedMvPowerSeriesEquiv` — a bicontinuous ring equivalence `B ≃+* B'`
  transports coefficientwise to the restricted power series subrings
  (`A⟨T₁,…,Tₖ⟩`, Wedhorn (5.6.1)): continuity preserves convergence of the
  coefficients to `0`.
* `isStronglyNoetherian_congr` — strong noetherianity (Wedhorn Prop & Def 6.36,
  `A`-level restricted-series form) is invariant under bicontinuous ring
  equivalences.
* `IsStronglyNoetherianTateRing A` — the **source-facing one-model predicate**:
  *some* completion model is strongly noetherian (Definition 6.36(i) is a condition
  on `Â`; by model comparison one model suffices).
* `completionModel_isStronglyNoetherian_congr` — one model is strongly noetherian
  iff every model is, through the **clean** comparison
  (`CompletionModelIndependence.lean`, whole-space topology equality) and the
  transport — with no ambient `PlusSubring`/`HasLocLiftPowerBounded`/noetherian/
  completeness hypotheses (P2.14 cleanup done).
* `isSheafyTateRing_of_stronglyNoetherianTateRing` — the one-model wrapper: a Tate
  ring with *one* strongly noetherian completion model is sheafy
  (`IsSheafyTateRing`); hypothesis-clean.
-/

@[expose] public section

noncomputable section

open Filter

universe u

namespace ValuationSpectrum

section Transport

variable {B B' : Type u} [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]
  [CommRing B'] [TopologicalSpace B'] [NonarchimedeanRing B']

/-- Coefficientwise transport of restricted power series along a continuous ring
homomorphism. -/
def restrictedMapHom (e : B →+* B') (he : Continuous e) (k : ℕ) :
    restrictedMvPowerSeriesSubring k B →+* restrictedMvPowerSeriesSubring k B' :=
  RingHom.codRestrict
    ((MvPowerSeries.map e).comp (restrictedMvPowerSeriesSubring k B).subtype)
    (restrictedMvPowerSeriesSubring k B')
    (by
      rintro ⟨f, hf⟩
      show MvPowerSeries.IsRestricted (MvPowerSeries.map e f)
      unfold MvPowerSeries.IsRestricted
      have hcoeff : (fun s : Fin k →₀ ℕ =>
          MvPowerSeries.coeff s (MvPowerSeries.map e f)) =
          (⇑e) ∘ (fun s : Fin k →₀ ℕ => MvPowerSeries.coeff s f) := by
        funext s
        exact MvPowerSeries.coeff_map e s f
      rw [hcoeff, show (0 : B') = e 0 from (map_zero e).symm]
      exact (he.tendsto 0).comp hf)

@[simp] theorem restrictedMapHom_coe (e : B →+* B') (he : Continuous e) (k : ℕ)
    (f : restrictedMvPowerSeriesSubring k B) :
    (restrictedMapHom e he k f : MvPowerSeries (Fin k) B') =
      MvPowerSeries.map e (f : MvPowerSeries (Fin k) B) := rfl

/-- **Restricted power series transport along a bicontinuous ring equivalence.** -/
def restrictedMvPowerSeriesEquiv (e : B ≃+* B') (he : Continuous e)
    (he' : Continuous e.symm) (k : ℕ) :
    restrictedMvPowerSeriesSubring k B ≃+* restrictedMvPowerSeriesSubring k B' where
  toFun := restrictedMapHom e.toRingHom he k
  invFun := restrictedMapHom e.symm.toRingHom he' k
  left_inv f := by
    refine Subtype.ext ?_
    show MvPowerSeries.map e.symm.toRingHom
      (MvPowerSeries.map e.toRingHom (f : MvPowerSeries (Fin k) B)) =
      (f : MvPowerSeries (Fin k) B)
    have hcomp := MvPowerSeries.map_map (σ := Fin k) e.toRingHom e.symm.toRingHom
      (f : MvPowerSeries (Fin k) B)
    rw [hcomp, show e.symm.toRingHom.comp e.toRingHom = RingHom.id B from
      RingHom.ext fun b => e.symm_apply_apply b, MvPowerSeries.map_id]
    rfl
  right_inv f := by
    refine Subtype.ext ?_
    show MvPowerSeries.map e.toRingHom
      (MvPowerSeries.map e.symm.toRingHom (f : MvPowerSeries (Fin k) B')) =
      (f : MvPowerSeries (Fin k) B')
    have hcomp := MvPowerSeries.map_map (σ := Fin k) e.symm.toRingHom e.toRingHom
      (f : MvPowerSeries (Fin k) B')
    rw [hcomp, show e.toRingHom.comp e.symm.toRingHom = RingHom.id B' from
      RingHom.ext fun b => e.apply_symm_apply b, MvPowerSeries.map_id]
    rfl
  map_mul' := map_mul _
  map_add' := map_add _

/-- **Strong noetherianity is invariant under bicontinuous ring equivalences**
(Wedhorn Prop & Def 6.36, restricted-series form; coefficientwise transport +
noetherianity along a surjection). -/
theorem isStronglyNoetherian_congr
    (e : B ≃+* B') (he : Continuous e) (he' : Continuous e.symm) :
    IsStronglyNoetherian B ↔ IsStronglyNoetherian B' := by
  constructor
  · intro hB
    refine ⟨fun k => ?_⟩
    haveI : IsNoetherianRing (restrictedMvPowerSeriesSubring k B) :=
      hB.isNoetherianRing_restricted k
    exact isNoetherianRing_of_surjective
      (restrictedMvPowerSeriesSubring k B) (restrictedMvPowerSeriesSubring k B')
      (restrictedMvPowerSeriesEquiv e he he' k).toRingHom
      (restrictedMvPowerSeriesEquiv e he he' k).surjective
  · intro hB'
    refine ⟨fun k => ?_⟩
    haveI : IsNoetherianRing (restrictedMvPowerSeriesSubring k B') :=
      hB'.isNoetherianRing_restricted k
    exact isNoetherianRing_of_surjective
      (restrictedMvPowerSeriesSubring k B') (restrictedMvPowerSeriesSubring k B)
      (restrictedMvPowerSeriesEquiv e.symm he' he k).toRingHom
      (restrictedMvPowerSeriesEquiv e.symm he' he k).surjective

end Transport

/-! ### The one-model predicate and wrapper -/

section OneModel

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A]

variable (A) in
/-- **The source-facing strongly-noetherian predicate for a (possibly noncomplete)
Tate ring** (Wedhorn Proposition & Definition 6.36: a condition on the completion
`Â`): *some* completion model is strongly noetherian. By
`completionModel_isStronglyNoetherian_congr` (hypothesis-clean), one model
suffices for all.

The `[IsTateRing A]` binder is deliberate and visible in the signature: the name
promises Tate scope (Definition 6.36 and Theorem 8.28(b) are used at Tate scope in
this project), so the predicate is only offered for Tate rings even though the
underlying `∃`-statement would typecheck for any Huber ring. -/
def IsStronglyNoetherianTateRing [IsTateRing A] : Prop :=
  ∃ P : PairOfDefinition A, IsStronglyNoetherian (CompletionModel A P)

/-- **Model-independence of strong noetherianity** — one completion model is
strongly noetherian iff every model is, through the clean canonical comparison
equivalence and the restricted-series transport — no ambient hypotheses. -/
theorem completionModel_isStronglyNoetherian_congr (P P' : PairOfDefinition A) :
    IsStronglyNoetherian (CompletionModel A P) ↔
      IsStronglyNoetherian (CompletionModel A P') :=
  isStronglyNoetherian_congr (completionModelCompare P P')
    (completionModelCompare_continuous P P')
    (completionModelCompare_symm_continuous P P')

/-- **The one-model wrapper** (Wedhorn Theorem 8.28(b) with the Definition 6.36
hypothesis in its `∃`-model form): a Tate ring one of whose completion models is
strongly noetherian is sheafy in the ring-level sense. Hypothesis-clean (the
model passage is the clean comparison). -/
theorem isSheafyTateRing_of_stronglyNoetherianTateRing [IsTateRing A]
    (h : IsStronglyNoetherianTateRing A) : IsSheafyTateRing A := by
  obtain ⟨P₀, hP₀⟩ := h
  refine isSheafyTateRing_of_stronglyNoetherian_completion (fun P => ?_)
  exact (completionModel_isStronglyNoetherian_congr P₀ P).mp hP₀

/-- One model strongly noetherian iff all models are (the `∃ ↔ ∀` collapse). -/
theorem isStronglyNoetherianTateRing_iff_forall [IsTateRing A] :
    IsStronglyNoetherianTateRing A ↔
      ∀ P : PairOfDefinition A, IsStronglyNoetherian (CompletionModel A P) := by
  constructor
  · rintro ⟨P₀, hP₀⟩ P
    exact (completionModel_isStronglyNoetherian_congr P₀ P).mp hP₀
  · intro h
    obtain ⟨P⟩ := IsHuberRing.exists_pairOfDefinition (A := A)
    exact ⟨P, h P⟩

end OneModel

end ValuationSpectrum
