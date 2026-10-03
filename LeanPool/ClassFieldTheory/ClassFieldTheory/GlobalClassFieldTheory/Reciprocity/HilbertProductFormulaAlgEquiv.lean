/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertFamilyAlgEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteHilbertFactorNaturality
public import Mathlib.Algebra.BigOperators.Finprod
/-!
# Transport of the Hilbert product formula

The product formula is invariant under a number-field equivalence. The
finite product is reindexed by the induced equivalence of finite places,
and the ordinary infinite product by the equivalence of infinite places.
-/

@[expose] public section

open scoped BigOperators NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- The Hilbert product formula survives transport of the local-pairing
family across a number-field equivalence. -/
theorem globalHilbertPairingFamilyCongr_productFormula
    {F : Type u} {G : Type v}
    [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃ₐ[ℚ] G) (n : ℕ+)
    (hmuF : (primitiveRoots (n : ℕ) F).Nonempty)
    (hmuG : (primitiveRoots (n : ℕ) G).Nonempty)
    (BF : GlobalHilbertPairingFamily F n)
    (hBF : ∀ a b : Fˣ,
      (∏ v : InfinitePlace F,
          globalInfinitePlaceHilbertSymbol F n v a b) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 F),
          GlobalHilbertPairingFamily.finiteFactor F BF hmuF v a b = 1) :
    ∀ a b : Gˣ,
      (∏ W : InfinitePlace G,
          globalInfinitePlaceHilbertSymbol G n W a b) *
        ∏ᶠ W : HeightOneSpectrum (𝓞 G),
          GlobalHilbertPairingFamily.finiteFactor G
            (globalHilbertPairingFamilyCongr e n hmuF BF) hmuG W a b = 1 := by
  let eu : Fˣ ≃* Gˣ := Units.mapEquiv e.toRingEquiv.toMulEquiv
  let er : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) G :=
    rootsOfUnityEquivOfRingEquiv e.toRingEquiv n hmuF
  let eFin := finitePlaceCongr e
  let eInf := infinitePlaceEquivOfRingEquiv e.toRingEquiv
  intro a b
  let a₀ : Fˣ := eu.symm a
  let b₀ : Fˣ := eu.symm b
  let fInf : InfinitePlace F → rootsOfUnity (n : ℕ) F :=
    fun v => globalInfinitePlaceHilbertSymbol F n v a₀ b₀
  let fFin : HeightOneSpectrum (𝓞 F) → rootsOfUnity (n : ℕ) F :=
    fun v => GlobalHilbertPairingFamily.finiteFactor F BF hmuF v a₀ b₀
  have hInf (W : InfinitePlace G) :
      globalInfinitePlaceHilbertSymbol G n W a b =
        er (fInf (eInf.symm W)) := by
    have h := globalInfinitePlaceHilbertSymbol_congr
      e.toRingEquiv n hmuF W a₀ b₀
    change er (fInf (eInf.symm W)) =
      globalInfinitePlaceHilbertSymbol G n W
        (eu a₀) (eu b₀) at h
    rw [eu.apply_symm_apply, eu.apply_symm_apply] at h
    exact h.symm
  have hFin (W : HeightOneSpectrum (𝓞 G)) :
      GlobalHilbertPairingFamily.finiteFactor G
          (globalHilbertPairingFamilyCongr e n hmuF BF) hmuG W a b =
        er (fFin (eFin.symm W)) := by
    have h := globalHilbertPairingFamilyCongr_finiteFactor
      e n hmuF hmuG BF W a₀ b₀
    change er (fFin (eFin.symm W)) =
      GlobalHilbertPairingFamily.finiteFactor G
        (globalHilbertPairingFamilyCongr e n hmuF BF) hmuG W
        (eu a₀) (eu b₀) at h
    rw [eu.apply_symm_apply, eu.apply_symm_apply] at h
    exact h.symm
  have hInfProd :
      (∏ W : InfinitePlace G,
        globalInfinitePlaceHilbertSymbol G n W a b) =
      er (∏ v : InfinitePlace F, fInf v) := by
    calc
      _ = ∏ W : InfinitePlace G, er (fInf (eInf.symm W)) := by
        apply Fintype.prod_congr
        intro W
        exact hInf W
      _ = er (∏ W : InfinitePlace G, fInf (eInf.symm W)) :=
        (map_prod er _ _).symm
      _ = er (∏ v : InfinitePlace F, fInf v) := by
        rw [Equiv.prod_comp eInf.symm fInf]
  have hFinProd :
      (∏ᶠ W : HeightOneSpectrum (𝓞 G),
        GlobalHilbertPairingFamily.finiteFactor G
          (globalHilbertPairingFamilyCongr e n hmuF BF) hmuG W a b) =
      er (∏ᶠ v : HeightOneSpectrum (𝓞 F), fFin v) := by
    calc
      _ = ∏ᶠ W : HeightOneSpectrum (𝓞 G), er (fFin (eFin.symm W)) :=
        finprod_congr hFin
      _ = er (∏ᶠ W : HeightOneSpectrum (𝓞 G), fFin (eFin.symm W)) :=
        (MulEquiv.map_finprod er _).symm
      _ = er (∏ᶠ v : HeightOneSpectrum (𝓞 F), fFin v) := by
        rw [finprod_comp_equiv eFin.symm]
  calc
    _ = er (∏ v : InfinitePlace F, fInf v) *
          er (∏ᶠ v : HeightOneSpectrum (𝓞 F), fFin v) := by
            rw [hInfProd, hFinProd]
    _ = er ((∏ v : InfinitePlace F, fInf v) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F), fFin v) :=
      (map_mul er _ _).symm
    _ = er 1 := congrArg er (hBF a₀ b₀)
    _ = 1 := map_one er

end ClassFieldTheory
