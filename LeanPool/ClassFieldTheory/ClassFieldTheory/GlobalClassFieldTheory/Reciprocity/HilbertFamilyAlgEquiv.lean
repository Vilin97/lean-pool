/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertFiniteFactorNaturality
/-!
# Hilbert-pairing families under equivalences of number fields

A number-field equivalence permutes finite places and identifies the
corresponding adic completions. The local pairings and their finite factors
can therefore be transported without changing their normalization.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- A primitive root in the number field remains primitive in every finite
adic completion. -/
theorem primitiveRoots_nonempty_adicCompletion
    (F : Type u) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) :
    (primitiveRoots (n : ℕ) (v.adicCompletion F)).Nonempty := by
  obtain ⟨ζ, hζ⟩ := hmu
  exact ⟨algebraMap F (v.adicCompletion F) ζ,
    (mem_primitiveRoots n.pos).2
      (((mem_primitiveRoots n.pos).1 hζ).map_of_injective
        (algebraMap F (v.adicCompletion F)).injective)⟩

/-- Transport a global family through the finite-place and adic-completion
equivalences induced by an equivalence of number fields. -/
def globalHilbertPairingFamilyCongr
    {F : Type u} {G : Type v}
    [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃ₐ[ℚ] G) (n : ℕ+)
    (hmuF : (primitiveRoots (n : ℕ) F).Nonempty)
    (BF : GlobalHilbertPairingFamily F n) :
    GlobalHilbertPairingFamily G n := fun W =>
  hilbertPairingOfRingEquiv
    (finitePlaceAdicCompletionCongrEquiv e W) n
    (primitiveRoots_nonempty_adicCompletion F n hmuF
      ((finitePlaceCongr e).symm W))
    (BF ((finitePlaceCongr e).symm W))

/-- Local Hilbert-pairing laws survive transport of the global family. -/
theorem globalHilbertPairingFamilyCongr_isLocallyHilbert
    {F : Type u} {G : Type v}
    [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃ₐ[ℚ] G) (n : ℕ+)
    (hmuF : (primitiveRoots (n : ℕ) F).Nonempty)
    (BF : GlobalHilbertPairingFamily F n)
    (hBF : GlobalHilbertPairingFamily.IsLocallyHilbert F BF) :
    GlobalHilbertPairingFamily.IsLocallyHilbert G
      (globalHilbertPairingFamilyCongr e n hmuF BF) := by
  intro W
  exact hilbertPairingOfRingEquiv_isLocalHilbertPairing
    (finitePlaceAdicCompletionCongrEquiv e W) n
    (primitiveRoots_nonempty_adicCompletion F n hmuF
      ((finitePlaceCongr e).symm W))
    (BF ((finitePlaceCongr e).symm W))
    (hBF ((finitePlaceCongr e).symm W))

/-- At corresponding places, finite factors of the transported family are
related by the equivalence of global roots of unity. -/
theorem globalHilbertPairingFamilyCongr_finiteFactor
    {F : Type u} {G : Type v}
    [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃ₐ[ℚ] G) (n : ℕ+)
    (hmuF : (primitiveRoots (n : ℕ) F).Nonempty)
    (hmuG : (primitiveRoots (n : ℕ) G).Nonempty)
    (BF : GlobalHilbertPairingFamily F n)
    (W : HeightOneSpectrum (𝓞 G)) (a b : Fˣ) :
    rootsOfUnityEquivOfRingEquiv e.toRingEquiv n hmuF
        (GlobalHilbertPairingFamily.finiteFactor F BF hmuF
          ((finitePlaceCongr e).symm W) a b) =
      GlobalHilbertPairingFamily.finiteFactor G
        (globalHilbertPairingFamilyCongr e n hmuF BF) hmuG W
        (Units.mapEquiv e.toRingEquiv.toMulEquiv a)
        (Units.mapEquiv e.toRingEquiv.toMulEquiv b) := by
  let w := (finitePlaceCongr e).symm W
  let : Algebra F G := e.toRingHom.toAlgebra
  have hKM : finitePlaceBelow (K := F) W = w := by
    apply HeightOneSpectrum.ext
    rfl
  have hcomm (x : F) :
      finitePlaceAdicCompletionCongrEquiv e W
          (algebraMap F (w.adicCompletion F) x) =
        algebraMap G (W.adicCompletion G) (e x) := by
    change finitePlaceAdicCompletionMap F G w ⟨W, hKM⟩
        (x : w.adicCompletion F) =
      algebraMap G (W.adicCompletion G) (e x)
    rw [finitePlaceAdicCompletionMap_coe]
    rfl
  exact globalHilbertPairingFamily_finiteFactor_congr
    e.toRingEquiv n hmuF hmuG w W
    (finitePlaceAdicCompletionCongrEquiv e W) hcomm
    (primitiveRoots_nonempty_adicCompletion F n hmuF w)
    BF (globalHilbertPairingFamilyCongr e n hmuF BF) rfl a b

/-- Finite support of global evaluations is invariant under an equivalence
of number fields. -/
theorem globalHilbertPairingFamilyCongr_hasFiniteSupport
    {F : Type u} {G : Type v}
    [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃ₐ[ℚ] G) (n : ℕ+)
    (hmuF : (primitiveRoots (n : ℕ) F).Nonempty)
    (hmuG : (primitiveRoots (n : ℕ) G).Nonempty)
    (BF : GlobalHilbertPairingFamily F n)
    (hBF : GlobalHilbertPairingFamily.HasFiniteSupport F BF hmuF) :
    GlobalHilbertPairingFamily.HasFiniteSupport G
      (globalHilbertPairingFamilyCongr e n hmuF BF) hmuG := by
  let eu : Fˣ ≃* Gˣ := Units.mapEquiv e.toRingEquiv.toMulEquiv
  let er : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) G :=
    rootsOfUnityEquivOfRingEquiv e.toRingEquiv n hmuF
  intro a b
  have hsource : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 F) =>
        er (GlobalHilbertPairingFamily.finiteFactor F BF hmuF v
          (eu.symm a) (eu.symm b))) :=
    (hBF (eu.symm a) (eu.symm b)).fun_comp (map_one er)
  have hreindex := hsource.fun_comp_of_injective
    (finitePlaceCongr e).symm.injective
  convert hreindex using 1
  funext W
  have hfactor := globalHilbertPairingFamilyCongr_finiteFactor
    e n hmuF hmuG BF W (eu.symm a) (eu.symm b)
  change er (GlobalHilbertPairingFamily.finiteFactor F BF hmuF
      ((finitePlaceCongr e).symm W) (eu.symm a) (eu.symm b)) =
    GlobalHilbertPairingFamily.finiteFactor G
      (globalHilbertPairingFamilyCongr e n hmuF BF) hmuG W
      (eu (eu.symm a)) (eu (eu.symm b)) at hfactor
  rw [eu.apply_symm_apply, eu.apply_symm_apply] at hfactor
  exact hfactor.symm

end ClassFieldTheory
