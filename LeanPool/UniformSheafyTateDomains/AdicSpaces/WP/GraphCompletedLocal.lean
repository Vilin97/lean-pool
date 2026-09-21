/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.GraphFlat

/-!
# The completed-local comparison for the graph model (L1)

([hrw-decomposition] L1.)  The head and its graph model have the same completed
local rings at a maximal ideal of the model and its contraction: the graph model
is flat over the head (Wedhorn 8.30, `flat_headToQ`) and the special fibre is
trivial (BETA, `levelOne_bijective_headToQ`), so the adic completions agree
level by level; the extended contraction is the maximal ideal itself
(`map_comap_headToQ_eq`), and completing at a maximal ideal is the same as
completing its localization (`AdicCompletion.localizationEquiv`).
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver FiniteJet.GraphKoszul IsLocalRing

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {w : ℕ → ℕ} {N : ℕ}

/-- **L1** ([hrw-decomposition]): for a maximal ideal `𝔮` of the graph model,
the completed local ring of the head at the contraction agrees with that of the
model at `𝔮`. -/
theorem qHead_completedLocal_comparison' (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) :
    haveI : (𝔮.comap (headToQ DH)).IsPrime := 𝔮.comap_isPrime (headToQ DH)
    Nonempty
      (completedLocal (WPHead K w N) (𝔮.comap (headToQ DH)) ≃+*
        completedLocal (QHead DH) 𝔮) := by
  haveI hcm : (𝔮.comap (headToQ DH)).IsMaximal :=
    comap_headToQ_isMaximal w N ϖ hK₀ DH hDH 𝔮 h𝔮
  letI : Algebra (WPHead K w N) (QHead DH) := (headToQ DH).toAlgebra
  haveI hflat : Module.Flat (WPHead K w N) (QHead DH) :=
    flat_headToQ ϖ hK₀ DH hDH
  have h1 : Function.Bijective
      (levelMap (A := WPHead K w N) (B := QHead DH)
        (𝔮.comap (headToQ DH)) 1) :=
    levelOne_bijective_headToQ ϖ hK₀ DH hDH 𝔮 h𝔮
  have hmapeq : Ideal.map (algebraMap (WPHead K w N) (QHead DH))
      (𝔮.comap (headToQ DH)) = 𝔮 :=
    map_comap_headToQ_eq ϖ hK₀ DH hDH 𝔮 h𝔮
  -- the two completions of the graph model agree
  have e2 : AdicCompletion (Ideal.map (algebraMap (WPHead K w N) (QHead DH))
      (𝔮.comap (headToQ DH))) (QHead DH) ≃+*
      AdicCompletion 𝔮 (QHead DH) := by
    rw [hmapeq]
  -- the flat comparison of adic completions
  have e1 : AdicCompletion (𝔮.comap (headToQ DH)) (WPHead K w N) ≃+*
      AdicCompletion (Ideal.map (algebraMap (WPHead K w N) (QHead DH))
        (𝔮.comap (headToQ DH))) (QHead DH) :=
    adicCompletionEquivOfFlatOfLevelOne _ h1
  -- completing at a maximal ideal is completing its localization
  have eA : AdicCompletion (𝔮.comap (headToQ DH)) (WPHead K w N) ≃+*
      completedLocal (WPHead K w N) (𝔮.comap (headToQ DH)) :=
    AdicCompletion.localizationEquiv (𝔮.comap (headToQ DH))
      (Localization.AtPrime (𝔮.comap (headToQ DH)))
  have eB : AdicCompletion 𝔮 (QHead DH) ≃+* completedLocal (QHead DH) 𝔮 :=
    AdicCompletion.localizationEquiv 𝔮 (Localization.AtPrime 𝔮)
  exact ⟨eA.symm.trans (e1.trans (e2.trans eB))⟩

/-- **L4 through maximals, unconditional in the head leaves**: the
head-localization reducedness hypothesis, now with the completed-local
comparison discharged (8.30-conditionally). -/
theorem headLocsReduced'' (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    HeadLocsReduced K w := by
  intro N DH hDH
  haveI hQnoeth : IsNoetherianRing (QHead DH) :=
    isNoetherianRing_qHead ϖ hK₀ hDH
  suffices h : IsReduced (QHead DH) by
    exact isReduced_of_injective
      (headLocEquiv ϖ hK₀ DH hDH).toRingHom
      (headLocEquiv ϖ hK₀ DH hDH).injective
  refine isReduced_of_forall_completedLocal_reduced _ ?_
  intro 𝔮 h𝔮
  haveI := h𝔮.isPrime
  haveI hcm : (𝔮.comap (headToQ DH)).IsMaximal :=
    comap_headToQ_isMaximal w N ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI hcp : (𝔮.comap (headToQ DH)).IsPrime := hcm.isPrime
  obtain ⟨e⟩ := qHead_completedLocal_comparison' ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI : IsReduced
      (completedLocal (WPHead K w N) (𝔮.comap (headToQ DH))) :=
    head_completedLocal_reduced_of_isMaximal w N ϖ hK₀ _ hcm
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end WeightedParity
