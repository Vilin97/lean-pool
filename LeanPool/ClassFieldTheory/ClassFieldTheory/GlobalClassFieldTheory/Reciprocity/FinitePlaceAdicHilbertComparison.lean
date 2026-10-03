/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicLocalField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibHilbertProductFormula
/-!
# Comparison of finite-place Hilbert factors

The finite-place factor of the transported adic pairing agrees with the
established finite-place Hilbert symbol.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

/-- The established finite-place symbol becomes the local Mathlib-facing
Hilbert symbol after mapping to the absolute-value completion. -/
private theorem globalFinitePlaceHilbertSymbol_map_eq_local
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    let C := (HeightOneSpectrum.adicAbv F v).Completion
    letI : ValuativeRel C :=
      GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
    let eFC : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) C :=
      letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
      rootsOfUnityEquivOfPrimitiveRoots (algebraMap F C).injective hmu
    eFC (globalFinitePlaceHilbertSymbol F n hnF hmu v a b) =
      localHilbertSymbol C n
        (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_natCast_ne_zero
          F n hnF v)
        (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty
          F n hmu v)
        (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertCompletionUnit F v a)
        (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertCompletionUnit F v b) := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  let : ValuativeRel C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let eFC : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) C :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F C).injective hmu
  change eFC
    (KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
        F n hnF hmu v a b)) =
    KummerTheory.nthRootsSubgroupEquivRootsOfUnity C (n : ℕ)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceLocalHilbertSymbol
        F n hnF hmu v a b)
  apply Subtype.ext
  have h := congrArg Subtype.val
    (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_map_eq_localHilbertSymbol
      F n hnF hmu v a b)
  change Units.map (algebraMap F C).toMonoidHom
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
        F n hnF hmu v a b) =
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalHilbertSymbol
      F n hnF hmu v a b
  exact h

/-- Mapping roots of unity from the number field to the adic completion
agrees with mapping first to the absolute-value completion. -/
private theorem rootsOfUnity_finiteCompletion_comp
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F))
    (hmuC : (primitiveRoots (n : ℕ)
      (HeightOneSpectrum.adicAbv F v).Completion).Nonempty)
    (z : rootsOfUnity (n : ℕ) F) :
    let C := (HeightOneSpectrum.adicAbv F v).Completion
    let D := v.adicCompletion F
    letI : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let eFC : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) C :=
      rootsOfUnityEquivOfPrimitiveRoots (algebraMap F C).injective hmu
    let eFD : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) D :=
      rootsOfUnityEquivOfPrimitiveRoots (algebraMap F D).injective hmu
    let eCD : rootsOfUnity (n : ℕ) C ≃* rootsOfUnity (n : ℕ) D :=
      rootsOfUnityEquivOfRingEquiv
        (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
    eFD z = eCD (eFC z) := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  let D := v.adicCompletion F
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let eFC : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) C :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F C).injective hmu
  let eFD : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) D :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F D).injective hmu
  let eCD : rootsOfUnity (n : ℕ) C ≃* rootsOfUnity (n : ℕ) D :=
    rootsOfUnityEquivOfRingEquiv
      (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv n hmuC
  apply Subtype.ext
  apply Units.ext
  change algebraMap F D ((z : Fˣ) : F) =
    (relativeFinitePlaceCompletionAlgEquiv v)
      (algebraMap F C ((z : Fˣ) : F))
  exact (relativeFinitePlaceCompletionAlgEquiv v).commutes ((z : Fˣ) : F) |>.symm

/-- The finite factor of the adic local Hilbert family is the established
global finite-place Hilbert symbol. -/
theorem finitePlaceAdicHilbertPairingFamily_finiteFactor
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    GlobalHilbertPairingFamily.finiteFactor F
      (finitePlaceAdicHilbertPairingFamily F n hmu) hmu v a b =
        globalFinitePlaceHilbertSymbol F n hnF hmu v a b := by
  let C := (HeightOneSpectrum.adicAbv F v).Completion
  let D := v.adicCompletion F
  let e : C ≃+* D := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  let : ValuativeRel C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField C :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let hnC : ((n : ℕ) : C) ≠ 0 :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_natCast_ne_zero F n hnF v
  let hmuC : (primitiveRoots (n : ℕ) C).Nonempty :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty
      F n hmu v
  let eFC : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) C :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F C).injective hmu
  let eFD : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) D :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F D).injective hmu
  let eCD : rootsOfUnity (n : ℕ) C ≃* rootsOfUnity (n : ℕ) D :=
    rootsOfUnityEquivOfRingEquiv e n hmuC
  let aC : Cˣ :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertCompletionUnit F v a
  let bC : Cˣ :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertCompletionUnit F v b
  let aD : Dˣ := Units.map (algebraMap F D).toMonoidHom a
  let bD : Dˣ := Units.map (algebraMap F D).toMonoidHom b
  have hunit (x : Fˣ) :
      (Units.mapEquiv e.toMulEquiv).symm
        (Units.map (algebraMap F D).toMonoidHom x) =
      GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertCompletionUnit F v x := by
    apply Units.ext
    apply e.injective
    change e (e.symm (algebraMap F D (x : F))) =
      e (algebraMap F C (x : F))
    rw [e.apply_symm_apply]
    exact (relativeFinitePlaceCompletionAlgEquiv v).commutes (x : F) |>.symm
  have hfactorD :
      eFD (GlobalHilbertPairingFamily.finiteFactor F
        (finitePlaceAdicHilbertPairingFamily F n hmu) hmu v a b) =
        eCD (localHilbertSymbol C n hnC hmuC aC bC) := by
    change eFD (eFD.symm
      ((hilbertPairingOfRingEquiv e n hmuC
        (localHilbertPairing C n hnC hmuC))
        (powerClass D n aD) (powerClass D n bD))) = _
    rw [eFD.apply_symm_apply, hilbertPairingOfRingEquiv_apply,
      powerClassGroupEquivOfRingEquiv_symm_powerClass,
      powerClassGroupEquivOfRingEquiv_symm_powerClass,
      hunit a, hunit b, localHilbertPairing_powerClass]
  have hglobal :
      eFC (globalFinitePlaceHilbertSymbol F n hnF hmu v a b) =
        localHilbertSymbol C n hnC hmuC aC bC :=
    globalFinitePlaceHilbertSymbol_map_eq_local F n hnF hmu v a b
  apply eFD.injective
  calc
    eFD (GlobalHilbertPairingFamily.finiteFactor F
        (finitePlaceAdicHilbertPairingFamily F n hmu) hmu v a b) =
        eCD (localHilbertSymbol C n hnC hmuC aC bC) := hfactorD
    _ = eCD (eFC (globalFinitePlaceHilbertSymbol F n hnF hmu v a b)) := by
          rw [hglobal]
    _ = eFD (globalFinitePlaceHilbertSymbol F n hnF hmu v a b) :=
      (rootsOfUnity_finiteCompletion_comp F n hmu v hmuC _).symm

end ClassFieldTheory
