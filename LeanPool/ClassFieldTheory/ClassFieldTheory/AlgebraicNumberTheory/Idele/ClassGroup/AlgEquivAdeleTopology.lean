/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.InfiniteAlgEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivFiniteIntegral
/-!
# Continuity of adelic transport under a number-field equivalence

The archimedean factor is a product of continuous completion maps. The
finite factor is a continuous map of restricted products because each
completion map preserves the local valuation subring.
-/

@[expose] public section

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- The existing algebraic transport of adeles is continuous. -/
theorem continuous_adeleCongr (e : K ≃ₐ[ℚ] M) :
    Continuous (adeleCongr e) := by
  let f : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K) :=
    (finitePlaceCongr e).symm
  have hf : Filter.Tendsto f Filter.cofinite Filter.cofinite :=
    (finitePlaceCongr e).symm.injective.tendsto_cofinite
  let φ : (W : HeightOneSpectrum (𝓞 M)) →
      (f W).adicCompletion K → W.adicCompletion M :=
    fun W => finitePlaceAdicCompletionCongrHom e W
  have hφ : ∀ᶠ W : HeightOneSpectrum (𝓞 M) in Filter.cofinite,
      Set.MapsTo (φ W)
        ((f W).adicCompletionIntegers K : Set ((f W).adicCompletion K))
        (W.adicCompletionIntegers M : Set (W.adicCompletion M)) :=
    Filter.Eventually.of_forall (fun W =>
      finitePlaceAdicCompletionCongrHom_mapsToIntegers e W)
  let transport : FiniteAdeleRing (𝓞 K) K → FiniteAdeleRing (𝓞 M) M :=
    RestrictedProduct.mapAlong
      (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun W : HeightOneSpectrum (𝓞 M) => W.adicCompletion M)
      f hf φ hφ
  have htransport : Continuous transport :=
    RestrictedProduct.mapAlong_continuous
      (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun W : HeightOneSpectrum (𝓞 M) => W.adicCompletion M)
      f hf φ hφ
      (fun W => finitePlaceAdicCompletionCongrHom_continuous e W)
  have hfinite : Continuous
      (fun a : NumberField.AdeleRing (𝓞 K) K => (adeleCongr e a).2) := by
    have hsource : Continuous
        (fun a : NumberField.AdeleRing (𝓞 K) K => a.2) :=
      continuous_snd
    refine (htransport.comp hsource).congr ?_
    intro a
    apply DFunLike.coe_injective
    funext W
    change finitePlaceAdicCompletionCongrHom e W
      (a.2 ((finitePlaceCongr e).symm W)) =
        (adeleCongr e a).2 W
    exact (adeleCongr_finiteComponent e a W).symm
  have hinfinite : Continuous
      (fun a : NumberField.AdeleRing (𝓞 K) K => (adeleCongr e a).1) := by
    apply continuous_pi
    intro W
    have hsource : Continuous
        (fun a : NumberField.AdeleRing (𝓞 K) K =>
          a.1 ((ClassFieldTheory.infinitePlaceEquivOfRingEquiv
            e.toRingEquiv).symm W)) :=
      (continuous_apply _).comp continuous_fst
    exact ((infinitePlaceCompletionCongrHom_continuous e W).comp hsource).congr
      (fun a => (adeleCongr_infiniteComponent e a W).symm)
  exact hinfinite.prodMk hfinite

end
