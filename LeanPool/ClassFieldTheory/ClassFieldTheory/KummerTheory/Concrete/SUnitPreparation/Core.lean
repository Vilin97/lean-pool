/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.EnlargedSUnitRestriction
import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.SUnitPreparation.PrimePowerKernelCoordinates
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.FullSUnitKummerExtension
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitLocalPowerKernel
import LeanPool.ClassFieldTheory.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.FiniteRadicalSupport
/-!
# Rank and kernel coordinates for S-unit preparation

The endpoint of the S-unit preparation construction: the rank bound, the exact restriction-kernel cardinality, and prime-power coordinates.
-/

open scoped NumberField Classical IsMulCommutative NNReal ValuativeRel
open NumberField IsDedekindDomain
open LocalFieldTheory

noncomputable section

namespace KummerTheory

variable {K : Type*} [Field K]
    [numberFieldK : NumberField K]

/-- The cardinal comparison in the finite S-unit preparation argument: if
`Gal(E/K) ≃ (Z/nZ)^r`, then `r ≤ s` for the source-produced enlarged
set of places. -/
theorem galoisRank_le_totalPlaceCard_enlargedS
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hn : 1 < (n : ℕ))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    r ≤
      totalPlaceCard (K := K)
        (enlargeByFiniteKummerRadicalSupport
          (K := K) (L := E) n hmu S) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Finite Gal(N/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  have hcardE :
      Nat.card Gal(E/K) = (n : ℕ) ^ r := by
    rw [Nat.card_congr eG.toEquiv, Nat.card_pi]
    simp
  have hcardN :
      Nat.card Gal(N/K) =
        (n : ℕ) ^ totalPlaceCard (K := K) S' :=
    card_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  have hexponentE :
      ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1 :=
    galois_pow_eq_one_of_equiv_pi_zmod E n r eG
  have hcardLe :
      Nat.card Gal(E/K) ≤ Nat.card Gal(N/K) :=
    Nat.card_le_card_of_surjective
      (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        hexponentE S)
      (enlargedSUnitKummerRestrictionHom_surjective
        (K := K) (Omega := Omega) E n hmu
        hexponentE S)
  rw [hcardE, hcardN] at hcardLe
  exact (Nat.pow_le_pow_iff_right hn).mp hcardLe

/-- The restriction kernel in the finite S-unit preparation argument has the expected
cardinality `n ^ (s - r)`.  Both fields and the restriction map are the
concrete objects constructed above. -/
theorem card_enlargedSUnitKummerRestrictionHom_ker
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hn : 1 < (n : ℕ))
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nat.card
        (enlargedSUnitKummerRestrictionHom
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod E n r eG)
          S).ker =
      (n : ℕ) ^
        (totalPlaceCard (K := K)
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := E) n hmu S) - r) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Finite Gal(N/K) :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  have hexponentE :
      ∀ sigma : Gal(E/K), sigma ^ (n : ℕ) = 1 :=
    galois_pow_eq_one_of_equiv_pi_zmod E n r eG
  let f : Gal(N/K) →* Gal(E/K) :=
    enlargedSUnitKummerRestrictionHom
      (K := K) (Omega := Omega) E n hmu hexponentE S
  have hf :
      Function.Surjective f :=
    enlargedSUnitKummerRestrictionHom_surjective
      (K := K) (Omega := Omega) E n hmu hexponentE S
  have hcardE :
      Nat.card Gal(E/K) = (n : ℕ) ^ r := by
    rw [Nat.card_congr eG.toEquiv, Nat.card_pi]
    simp
  have hcardN :
      Nat.card Gal(N/K) =
        (n : ℕ) ^ totalPlaceCard (K := K) S' :=
    card_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  have hquotient :
      Nat.card (Gal(N/K) ⧸ f.ker) =
        Nat.card Gal(E/K) :=
    Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective
        f hf).toEquiv
  have hfactor :
      (n : ℕ) ^ totalPlaceCard (K := K) S' =
        (n : ℕ) ^ r * Nat.card f.ker := by
    rw [← hcardN, ← hcardE, ← hquotient]
    exact
      Subgroup.card_eq_card_quotient_mul_card_subgroup
        f.ker
  have hr :
      r ≤ totalPlaceCard (K := K) S' :=
    galoisRank_le_totalPlaceCard_enlargedS
      (K := K) (Omega := Omega) E n hn hmu r eG S
  have hsplit :
      (n : ℕ) ^ totalPlaceCard (K := K) S' =
        (n : ℕ) ^ r *
          (n : ℕ) ^
            (totalPlaceCard (K := K) S' - r) := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  have hcancel :
      (n : ℕ) ^ r * Nat.card f.ker =
        (n : ℕ) ^ r *
          (n : ℕ) ^
            (totalPlaceCard (K := K) S' - r) :=
    hfactor.symm.trans hsplit
  exact Nat.eq_of_mul_eq_mul_left
    (pow_pos n.pos r) hcancel

/-- In the prime-power case, the actual relative Galois group
`Gal(N/E)` is a free `ZMod n`-module of rank `s - r`.  This is the
concrete basis source used to choose the fields `N_i` in the finite S-unit preparation argument. -/
theorem
    exists_enlargedSUnitKummerRestrictionKernelEquivPiZMod
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Nonempty
      ((enlargedSUnitKummerRestrictionHom
          (K := K) (Omega := Omega) E n hmu
          (galois_pow_eq_one_of_equiv_pi_zmod E n r eG)
          S).ker ≃*
        (Fin
            (totalPlaceCard (K := K)
              (enlargeByFiniteKummerRadicalSupport
                (K := K) (L := E) n hmu S) - r) →
          Multiplicative (ZMod (n : ℕ)))) := by
  let S' :=
    enlargeByFiniteKummerRadicalSupport
      (K := K) (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension
      (K := K) (Omega := Omega) n S'
  let G := Gal(N/K)
  let H := Gal(E/K)
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hnOne : 1 < (n : ℕ) := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  have hexponentE :
      ∀ sigma : H, sigma ^ (n : ℕ) = 1 :=
    galois_pow_eq_one_of_equiv_pi_zmod E n r eG
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois
      (K := K) (Omega := Omega) n S'
  let : Finite G :=
    finite_fullSUnitKummerExtension_galois
      (K := K) (Omega := Omega) n hnK hmu S'
  let : IsMulCommutative G :=
    KummerTheory.kummerRadicalExtension_isMulCommutative
      n hmu (fullSUnitKummerSubgroup (K := K) n S').1
  let : Module (ZMod (n : ℕ)) (Additive G) :=
    additiveZModModuleOfPowEqOne (n : ℕ)
      (fullSUnitKummerExtension_galois_pow_eq_one
        (K := K) (Omega := Omega) n hmu S')
  let : Module (ZMod (n : ℕ)) (Additive H) :=
    additiveZModModuleOfPowEqOne (n : ℕ) hexponentE
  have hfreeG : Module.Free (ZMod (n : ℕ)) (Additive G) :=
    fullSUnitKummerExtension_galois_moduleFree
      (K := K) (Omega := Omega) n hnK hmu S'
  let eH :
      Additive H ≃ₗ[ZMod (n : ℕ)]
        (Fin r → ZMod (n : ℕ)) :=
    additivePiLinearEquiv (n : ℕ) eG
  have hfreeH : Module.Free (ZMod (n : ℕ)) (Additive H) :=
    Module.Free.of_equiv eH.symm
  let f : G →* H :=
    enlargedSUnitKummerRestrictionHom
      (K := K) (Omega := Omega) E n hmu
        hexponentE S
  have hf : Function.Surjective f :=
    enlargedSUnitKummerRestrictionHom_surjective
      (K := K) (Omega := Omega) E n hmu
        hexponentE S
  have hcard :
      Nat.card f.ker =
        (n : ℕ) ^
          (totalPlaceCard (K := K) S' - r) :=
    card_enlargedSUnitKummerRestrictionHom_ker
      (K := K) (Omega := Omega) E n hnOne
        hmu r eG S
  exact
    exists_kernelMulEquiv_pi_zmod_of_primePower
      (G := G) (H := H)
      (n : ℕ) p v
      (totalPlaceCard (K := K) S' - r)
      hp hv hn hfreeG hfreeH f hf hcard

/-- A chosen coordinate equivalence for the actual relative Galois
group in the finite S-unit preparation argument. -/
noncomputable def
    chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod
    {Omega : Type*} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (enlargedSUnitKummerRestrictionHom
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod E n r eG)
        S).ker ≃*
      (Fin
          (totalPlaceCard (K := K)
            (enlargeByFiniteKummerRadicalSupport
              (K := K) (L := E) n hmu S) - r) →
        Multiplicative (ZMod (n : ℕ))) :=
  Classical.choice
    (exists_enlargedSUnitKummerRestrictionKernelEquivPiZMod
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S)

end KummerTheory
