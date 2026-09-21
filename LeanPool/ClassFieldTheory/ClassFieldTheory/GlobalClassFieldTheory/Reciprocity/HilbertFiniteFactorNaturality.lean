/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingFiniteFactor
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport
/-!
# Naturality of the finite Hilbert factor

The factor obtained by evaluating a local pairing on global units commutes
with equivalences of both the number fields and their completions. The
commuting square for the two field embeddings is the only geometric input.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u v

/-- Transporting a local Hilbert pairing through a compatible equivalence of
completions transports its finite factor through the equivalence of global
roots of unity. -/
theorem globalHilbertPairingFamily_finiteFactor_congr
    {F : Type u} {G : Type v}
    [Field F] [NumberField F] [Field G] [NumberField G]
    (e : F ≃+* G) (n : ℕ+)
    (hmuF : (primitiveRoots (n : ℕ) F).Nonempty)
    (hmuG : (primitiveRoots (n : ℕ) G).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (W : HeightOneSpectrum (𝓞 G))
    (ec : v.adicCompletion F ≃+* W.adicCompletion G)
    (hcomm : ∀ x : F,
      ec (algebraMap F (v.adicCompletion F) x) =
        algebraMap G (W.adicCompletion G) (e x))
    (hmuC : (primitiveRoots (n : ℕ) (v.adicCompletion F)).Nonempty)
    (BF : GlobalHilbertPairingFamily F n)
    (BG : GlobalHilbertPairingFamily G n)
    (hB : BG W = hilbertPairingOfRingEquiv ec n hmuC (BF v))
    (a b : Fˣ) :
    rootsOfUnityEquivOfRingEquiv e n hmuF
        (GlobalHilbertPairingFamily.finiteFactor F BF hmuF v a b) =
      GlobalHilbertPairingFamily.finiteFactor G BG hmuG W
        (Units.mapEquiv e.toMulEquiv a)
        (Units.mapEquiv e.toMulEquiv b) := by
  let C := v.adicCompletion F
  let D := W.adicCompletion G
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let eFC : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) C :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F C).injective hmuF
  let eGD : rootsOfUnity (n : ℕ) G ≃* rootsOfUnity (n : ℕ) D :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap G D).injective hmuG
  let eCD : rootsOfUnity (n : ℕ) C ≃* rootsOfUnity (n : ℕ) D :=
    rootsOfUnityEquivOfRingEquiv ec n hmuC
  let eFG : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) G :=
    rootsOfUnityEquivOfRingEquiv e n hmuF
  have hroots (z : rootsOfUnity (n : ℕ) F) :
      eGD (eFG z) = eCD (eFC z) := by
    apply Subtype.ext
    apply Units.ext
    change algebraMap G D (e ((z : Fˣ) : F)) =
      ec (algebraMap F C ((z : Fˣ) : F))
    exact (hcomm _).symm
  have hunit (x : Fˣ) :
      (Units.mapEquiv ec.toMulEquiv).symm
          (Units.map (algebraMap G D).toMonoidHom
            (Units.mapEquiv e.toMulEquiv x)) =
        Units.map (algebraMap F C).toMonoidHom x := by
    apply Units.ext
    apply ec.injective
    change ec (ec.symm (algebraMap G D (e (x : F)))) =
      ec (algebraMap F C (x : F))
    rw [ec.apply_symm_apply]
    exact (hcomm _).symm
  apply eGD.injective
  change eGD (eFG (eFC.symm
      (BF v
        (powerClass C n
          (Units.map (algebraMap F C).toMonoidHom a))
        (powerClass C n
          (Units.map (algebraMap F C).toMonoidHom b))))) =
    eGD (eGD.symm
      (BG W
        (powerClass D n
          (Units.map (algebraMap G D).toMonoidHom
            (Units.mapEquiv e.toMulEquiv a)))
        (powerClass D n
          (Units.map (algebraMap G D).toMonoidHom
            (Units.mapEquiv e.toMulEquiv b)))))
  rw [eGD.apply_symm_apply, hroots, eFC.apply_symm_apply, hB,
    hilbertPairingOfRingEquiv_apply,
    powerClassGroupEquivOfRingEquiv_symm_powerClass,
    powerClassGroupEquivOfRingEquiv_symm_powerClass,
    hunit a, hunit b]

end ClassFieldTheory
