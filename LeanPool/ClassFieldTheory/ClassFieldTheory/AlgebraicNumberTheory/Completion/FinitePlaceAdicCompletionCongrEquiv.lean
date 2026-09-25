/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
/-!
# Adic completions under a number-field equivalence

The existing continuous maps of adic completions along an equivalence of
number fields are mutual inverses. This bundles them as a field equivalence
for transporting local Hilbert pairings.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Field M] [NumberField M]

/-- The finite completion at corresponding places, viewed as a field
equivalence rather than merely a continuous map. -/
def finitePlaceAdicCompletionCongrEquiv
    (e : K ≃ₐ[ℚ] M) (W : HeightOneSpectrum (𝓞 M)) :
    ((finitePlaceCongr e).symm W).adicCompletion K ≃+*
      W.adicCompletion M := by
  letI : Algebra K M := e.toRingHom.toAlgebra
  letI : Algebra M K := e.symm.toRingHom.toAlgebra
  let w := (finitePlaceCongr e).symm W
  have hKM : finitePlaceBelow (K := K) W = w := by
    apply HeightOneSpectrum.ext
    rfl
  have hMK : finitePlaceBelow (K := M) w = W := by
    have he : finitePlaceCongr e w = W :=
      (finitePlaceCongr e).apply_symm_apply W
    apply HeightOneSpectrum.ext
    rw [← he]
    rfl
  haveI : IsScalarTower K M K := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change x = e.symm (e x)
    exact (e.symm_apply_apply x).symm
  haveI : IsScalarTower M K M := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change x = e (e.symm x)
    exact (e.apply_symm_apply x).symm
  let f : w.adicCompletion K →+* W.adicCompletion M :=
    finitePlaceAdicCompletionMap K M w ⟨W, hKM⟩
  let g : W.adicCompletion M →+* w.adicCompletion K :=
    finitePlaceAdicCompletionMap M K W ⟨w, hMK⟩
  exact RingEquiv.ofRingHom f g
    (by
      apply RingHom.ext
      intro x
      change f (g x) = x
      rw [finitePlaceAdicCompletionMap_comp M M (M := K)
        W w W hMK hKM (finitePlaceBelow_self W) x]
      exact finitePlaceAdicCompletionMap_self_apply M W x)
    (by
      apply RingHom.ext
      intro x
      change g (f x) = x
      rw [finitePlaceAdicCompletionMap_comp K K (M := M)
        w W w hKM hMK (finitePlaceBelow_self w) x]
      exact finitePlaceAdicCompletionMap_self_apply K w x)

end
