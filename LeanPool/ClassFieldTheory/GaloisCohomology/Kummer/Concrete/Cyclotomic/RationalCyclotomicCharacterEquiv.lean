/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacter
import Mathlib.FieldTheory.Galois.Profinite
/-!
# The rational cyclotomic character equivalence

Finite cyclotomic levels are detected by their prime-power reductions,
using mathlib's Chinese-remainder equivalence for `ZMod`.  Surjectivity
is obtained from the finite-intersection property for the closed fibers
of the restriction maps to those levels.
-/

noncomputable section

namespace KummerTheory

open ClassFormation

local instance (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

/-- The `p ^ k` reduction of the cyclotomic character can be read from
any finite cyclotomic level whose order is divisible by `p ^ k`. -/
theorem rationalCyclotomicCharacterPrimeProduct_toZModPow_of_dvd
    (σ : rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField)
    (p : Nat.Primes) (k : ℕ) (n : ℕ+)
    (h : p.1 ^ k ∣ (n : ℕ)) :
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      ZMod.unitsMap h
        (IsCyclotomicExtension.Rat.galEquivZMod
          (n : ℕ) (rationalCyclotomicLevel n)
          (σ.restrictNormal (rationalCyclotomicLevel n))) := by
  let m : ℕ+ := ⟨p.1 ^ k, pow_pos p.2.pos k⟩
  let F := rationalCyclotomicLevel m
  let K := rationalCyclotomicLevel n
  let : IsCyclotomicExtension {p.1 ^ k} ℚ F := by
    change IsCyclotomicExtension {(m : ℕ)} ℚ
      (rationalCyclotomicLevel m)
    exact rationalCyclotomicLevel_isCyclotomicExtension m
  have hFK : F ≤ K :=
    rationalCyclotomicLevel_mono h
  let ζ : F :=
    IsCyclotomicExtension.zeta (p.1 ^ k) ℚ F
  have hζ : IsPrimitiveRoot ζ (p.1 ^ k) :=
    IsCyclotomicExtension.zeta_spec (p.1 ^ k) ℚ F
  let x : rationalCyclotomicField :=
    algebraMap F rationalCyclotomicField ζ
  have hζx : IsPrimitiveRoot x (p.1 ^ k) :=
    hζ.map_of_injective
      (algebraMap F rationalCyclotomicField).injective
  let y : K :=
    IntermediateField.inclusion hFK ζ
  have hy : y ^ (n : ℕ) = 1 := by
    apply Subtype.ext
    change x ^ (n : ℕ) = 1
    exact (hζx.pow_eq_one_iff_dvd _).2 h
  let a :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (p.1 ^ k) F (σ.restrictNormal F)
  let b :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (n : ℕ) K (σ.restrictNormal K)
  have ha :
      (σ.restrictNormal F) ζ =
        ζ ^ a.val.val := by
    exact
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
        (p.1 ^ k) F (σ.restrictNormal F) hζ.pow_eq_one
  have hb :
      (σ.restrictNormal K) y =
        y ^ b.val.val := by
    exact
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
        (n : ℕ) K (σ.restrictNormal K) hy
  change
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      ZMod.unitsMap h b
  calc
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
        a := by
      simpa only [a, F, m] using
        rationalCyclotomicCharacterPrimeProduct_toZModPow σ p k
    _ = ZMod.unitsMap h b := by
      suffices x ^ a.val.val = x ^ b.val.val by
        rw [(hζx.isOfFinOrder (NeZero.ne _)).pow_inj_mod,
          ← hζx.eq_orderOf,
          ← ZMod.natCast_eq_natCast_iff',
          ZMod.natCast_val, ZMod.natCast_val,
          ZMod.cast_id] at this
        rwa [Units.ext_iff]
      calc
        x ^ a.val.val =
            algebraMap F rationalCyclotomicField
              (ζ ^ a.val.val) := by
          rw [map_pow]
        _ = algebraMap F rationalCyclotomicField
              ((σ.restrictNormal F) ζ) := by
          rw [ha]
        _ = σ x :=
          AlgEquiv.restrictNormal_commutes σ F ζ
        _ = algebraMap K rationalCyclotomicField
              ((σ.restrictNormal K) y) :=
          (AlgEquiv.restrictNormal_commutes σ K y).symm
        _ = algebraMap K rationalCyclotomicField
              (y ^ b.val.val) := by
          rw [hb]
        _ = x ^ b.val.val := by
          rw [map_pow]
          congr 1

/-- The product of the `p`-adic cyclotomic characters separates
automorphisms of the actual rational cyclotomic field. -/
theorem rationalCyclotomicCharacterPrimeProduct_injective :
    Function.Injective rationalCyclotomicCharacterPrimeProduct := by
  intro σ τ hστ
  have hrestrict (n : ℕ+) :
      σ.restrictNormal (rationalCyclotomicLevel n) =
        τ.restrictNormal (rationalCyclotomicLevel n) := by
    let K := rationalCyclotomicLevel n
    apply
      (IsCyclotomicExtension.Rat.galEquivZMod
        (n : ℕ) K).injective
    apply Units.ext
    let e :=
      ZMod.equivPi (n := (n : ℕ)) n.2.ne'
    apply e.injective
    funext q
    have hqPrime : q.1.Prime :=
      Nat.prime_of_mem_primeFactors q.2
    let p : Nat.Primes := ⟨q.1, hqPrime⟩
    let k := (n : ℕ).factorization q.1
    have hpow :
        p.1 ^ k ∣ (n : ℕ) :=
      (hqPrime.pow_dvd_iff_le_factorization n.2.ne').2 le_rfl
    have hpCoordinate :=
      congrArg (fun z => z p) hστ
    have hpReduction :=
      congrArg (Units.map (PadicInt.toZModPow k).toMonoidHom)
        hpCoordinate
    rw [
      rationalCyclotomicCharacterPrimeProduct_toZModPow_of_dvd
        σ p k n hpow,
      rationalCyclotomicCharacterPrimeProduct_toZModPow_of_dvd
        τ p k n hpow] at hpReduction
    have heval (z : ZMod (n : ℕ)) :
        e z q =
          ZMod.castHom hpow (ZMod (p.1 ^ k)) z := by
      change
        ((Pi.evalRingHom
            (fun r : (n : ℕ).primeFactors =>
              ZMod (r.1 ^ (n : ℕ).factorization r.1)) q).comp
          e.toRingHom) z =
            ZMod.castHom hpow (ZMod (p.1 ^ k)) z
      exact RingHom.congr_fun (Subsingleton.elim _ _) z
    rw [heval, heval]
    simpa only [p, k, ZMod.unitsMap_val,
      ZMod.castHom_apply] using
      congrArg
        (fun u : (ZMod (p.1 ^ k))ˣ =>
          (u : ZMod (p.1 ^ k)))
        hpReduction
  let E : IntermediateField ℚ rationalCyclotomicField :=
    { AlgHom.equalizer σ.toAlgHom τ.toAlgHom with
      inv_mem' := by
        intro x hx
        change σ x = τ x at hx
        change σ x⁻¹ = τ x⁻¹
        simpa only [map_inv₀] using congrArg Inv.inv hx }
  have hlevel (n : ℕ+) :
      rationalCyclotomicLevel n ≤ E := by
    intro x hx
    change σ x = τ x
    let y : rationalCyclotomicLevel n := ⟨x, hx⟩
    calc
      σ x =
          algebraMap (rationalCyclotomicLevel n)
            rationalCyclotomicField
            ((σ.restrictNormal
              (rationalCyclotomicLevel n)) y) :=
        (AlgEquiv.restrictNormal_commutes σ
          (rationalCyclotomicLevel n) y).symm
      _ = algebraMap (rationalCyclotomicLevel n)
            rationalCyclotomicField
            ((τ.restrictNormal
              (rationalCyclotomicLevel n)) y) := by
        rw [hrestrict n]
      _ = τ x :=
        AlgEquiv.restrictNormal_commutes τ
          (rationalCyclotomicLevel n) y
  have hE : E = ⊤ := by
    apply top_unique
    rw [← iSup_rationalCyclotomicLevel]
    exact iSup_le hlevel
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ E := by
    rw [hE]
    trivial
  change x ∈ AlgHom.equalizer σ.toAlgHom τ.toAlgHom at hx
  exact (AlgHom.mem_equalizer σ.toAlgHom τ.toAlgHom x).mp hx

/-- The canonical rational cyclotomic character is injective. -/
theorem rationalCyclotomicCharacter_injective :
    Function.Injective rationalCyclotomicCharacter := by
  intro σ τ hστ
  apply rationalCyclotomicCharacterPrimeProduct_injective
  have h :=
    congrArg
      (fun u : ZHatˣ =>
        zHatUnitsContinuousMulEquivPrimeProduct u)
      hστ
  simpa [rationalCyclotomicCharacter] using h

/-- The canonical rational cyclotomic character is surjective. -/
theorem rationalCyclotomicCharacter_surjective :
    Function.Surjective rationalCyclotomicCharacter := by
  intro u
  let τ (n : ℕ+) :
      rationalCyclotomicLevel n ≃ₐ[ℚ]
        rationalCyclotomicLevel n :=
    (IsCyclotomicExtension.Rat.galEquivZMod
      (n : ℕ) (rationalCyclotomicLevel n)).symm
        (Units.map
          (zHatReductionRingHom (n : ℕ) n.2) u)
  let C (n : ℕ+) :
      Set
        (rationalCyclotomicField ≃ₐ[ℚ]
          rationalCyclotomicField) :=
    {σ |
      σ.restrictNormal (rationalCyclotomicLevel n) = τ n}
  have hclosed (n : ℕ+) : IsClosed (C n) := by
    let : FiniteDimensional ℚ (rationalCyclotomicLevel n) :=
      IsCyclotomicExtension.finiteDimensional
        {(n : ℕ)} ℚ (rationalCyclotomicLevel n)
    change IsClosed
      {σ :
          rationalCyclotomicField ≃ₐ[ℚ]
            rationalCyclotomicField |
        σ.restrictNormal (rationalCyclotomicLevel n) = τ n}
    refine @isClosed_eq
      (rationalCyclotomicLevel n ≃ₐ[ℚ]
        rationalCyclotomicLevel n)
      (rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)
      inferInstance inferInstance krullTopology_t2
      _ _ ?_ ?_
    · exact
        InfiniteGalois.restrictNormalHom_continuous
          (k := ℚ) (K := rationalCyclotomicField)
          (rationalCyclotomicLevel n)
    · exact continuous_const
  have hfip (s : Finset ℕ+) :
      (⋂ n ∈ s, C n).Nonempty := by
    let N : ℕ+ :=
      ⟨∏ n ∈ s, (n : ℕ),
        Finset.prod_pos fun n _ => n.2⟩
    obtain ⟨σ, hσN⟩ :=
      (AlgEquiv.restrictNormalHom_surjective
        (F := ℚ)
        (K₁ := rationalCyclotomicLevel N)
        (E := rationalCyclotomicField)) (τ N)
    refine ⟨σ, ?_⟩
    rw [Set.mem_iInter₂]
    intro n hn
    have hnN : (n : ℕ) ∣ (N : ℕ) := by
      change
        (n : ℕ) ∣
          ∏ m ∈ s, (m : ℕ)
      exact
        Finset.dvd_prod_of_mem
          (fun m : ℕ+ => (m : ℕ)) hn
    let F := rationalCyclotomicLevel n
    let K := rationalCyclotomicLevel N
    have hFK : F ≤ K :=
      rationalCyclotomicLevel_mono hnN
    let algFK : Algebra F K :=
      RingHom.toAlgebra
        (IntermediateField.inclusion hFK).toRingHom
    let : SMul F K :=
      @Algebra.toSMul F K _ _ algFK
    let : Algebra F K := algFK
    let : IsScalarTower ℚ F K :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower ℚ F rationalCyclotomicField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower ℚ K rationalCyclotomicField :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower F K rationalCyclotomicField :=
      IsScalarTower.of_algebraMap_eq' rfl
    have hτ :
        (AlgEquiv.restrictNormalHom F) (τ N) = τ n := by
      apply
        (IsCyclotomicExtension.Rat.galEquivZMod
          (n : ℕ) F).injective
      change
        IsCyclotomicExtension.Rat.galEquivZMod
            (n : ℕ) F ((τ N).restrictNormal F) =
          IsCyclotomicExtension.Rat.galEquivZMod
            (n : ℕ) F (τ n)
      rw [
        IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
          (N : ℕ) K F hnN (τ N)]
      simp only [K, F, τ, MulEquiv.apply_symm_apply]
      apply Units.ext
      change
        ZMod.castHom hnN (ZMod (n : ℕ))
            (zHatReduction (N : ℕ) N.2 (u : ZHat)) =
          zHatReduction (n : ℕ) n.2 (u : ZHat)
      exact
        zHatReduction_transition
          n.2 N.2 hnN (u : ZHat)
    change σ.restrictNormal F = τ n
    calc
      σ.restrictNormal F =
          (AlgEquiv.restrictNormalHom F)
            ((AlgEquiv.restrictNormalHom K) σ) :=
        IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply F K σ
      _ = (AlgEquiv.restrictNormalHom F) (τ N) := by
        have hσN' :
            (AlgEquiv.restrictNormalHom K) σ = τ N := by
          simpa only [K] using hσN
        exact congrArg
          (AlgEquiv.restrictNormalHom F)
          hσN'
      _ = τ n := hτ
  obtain ⟨σ, hσ⟩ :=
    CompactSpace.iInter_nonempty hclosed hfip
  refine ⟨σ, ?_⟩
  apply zHatUnitsContinuousMulEquivPrimeProduct.injective
  change
    zHatUnitsContinuousMulEquivPrimeProduct
        (zHatUnitsContinuousMulEquivPrimeProduct.symm
          (rationalCyclotomicCharacterPrimeProduct σ)) =
      zHatUnitsContinuousMulEquivPrimeProduct u
  rw [
    zHatUnitsContinuousMulEquivPrimeProduct.apply_symm_apply]
  funext p
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  let n : ℕ+ :=
    ⟨p.1 ^ k, pow_pos p.2.pos k⟩
  have hσn : σ ∈ C n :=
    Set.mem_iInter.mp hσ n
  change
    σ.restrictNormal (rationalCyclotomicLevel n) =
      τ n at hσn
  have hleft :=
    rationalCyclotomicCharacterPrimeProduct_toZModPow
      σ p k
  rw [hσn] at hleft
  change
    Units.map (PadicInt.toZModPow k).toMonoidHom
        (rationalCyclotomicCharacterPrimeProduct σ p) =
      (IsCyclotomicExtension.Rat.galEquivZMod
        (n : ℕ) (rationalCyclotomicLevel n))
        ((IsCyclotomicExtension.Rat.galEquivZMod
          (n : ℕ) (rationalCyclotomicLevel n)).symm
          (Units.map
            (zHatReductionRingHom (n : ℕ) n.2).toMonoidHom u))
      at hleft
  rw [MulEquiv.apply_symm_apply] at hleft
  have hright :
      Units.map (PadicInt.toZModPow k).toMonoidHom
          (zHatUnitsContinuousMulEquivPrimeProduct u p) =
        Units.map
          (zHatReductionRingHom
            (p.1 ^ k) (pow_pos p.2.pos k)) u := by
    apply Units.ext
    change
      PadicInt.toZModPow k
          (zHatUnitsContinuousMulEquivPrimeProduct u p :
            ℤ_[p.1]) =
        zHatReduction (p.1 ^ k)
          (pow_pos p.2.pos k) (u : ZHat)
    rw [
      zHatUnitsContinuousMulEquivPrimeProduct_coe_apply]
    simpa only [RingHom.comp_apply, zHatPadicReduction,
      zHatReductionRingHom_apply] using
      RingHom.congr_fun
        (toZModPow_zHatToPadicInt p k) (u : ZHat)
  exact
    congrArg
      (fun z : (ZMod (p.1 ^ k))ˣ =>
        (z : ZMod (p.1 ^ k)))
      (hleft.trans hright.symm)

/-- The canonical topological equivalence
`Gal(ℚ(μ∞)/ℚ) ≃ ℤ̂ˣ`. -/
noncomputable def rationalCyclotomicCharacterContinuousMulEquiv :
    (rationalCyclotomicField ≃ₐ[ℚ]
      rationalCyclotomicField) ≃ₜ* ZHatˣ :=
  let e :=
    MulEquiv.ofBijective
      rationalCyclotomicCharacter.toMonoidHom
      ⟨rationalCyclotomicCharacter_injective,
        rationalCyclotomicCharacter_surjective⟩
  ContinuousMulEquiv.mk'
    (rationalCyclotomicCharacter.continuous_toFun.homeoOfEquivCompactToT2
      (f := e.toEquiv))
    e.map_mul

/-- Evaluating the actual profinite-unit cyclotomic character at a
prime recovers the corresponding genuine `p`-adic cyclotomic
character. -/
@[simp]
theorem
    zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter
    (σ :
      rationalCyclotomicField ≃ₐ[ℚ]
        rationalCyclotomicField)
    (p : Nat.Primes) :
    zHatUnitsContinuousMulEquivPrimeProduct
        (rationalCyclotomicCharacterContinuousMulEquiv σ) p =
      rationalCyclotomicCharacterPrimeProduct σ p := by
  change
    zHatUnitsContinuousMulEquivPrimeProduct
        (rationalCyclotomicCharacter σ) p =
      rationalCyclotomicCharacterPrimeProduct σ p
  have h :=
    zHatUnitsContinuousMulEquivPrimeProduct.apply_symm_apply
      (rationalCyclotomicCharacterPrimeProduct σ)
  exact congrFun h p

end KummerTheory
