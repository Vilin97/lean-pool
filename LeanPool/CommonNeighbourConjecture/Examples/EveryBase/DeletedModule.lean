/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import LeanPool.CommonNeighbourConjecture.Examples.EveryBase.FrobeniusGroup

/-!
# The binary deleted permutation module

This file constructs the deleted permutation module for an odd finite
permutation set.  The explicit equivariant retraction is used in the
irreducibility proof: every endomorphism of the deleted module extends to the
full permutation module, while the all-ones operator restricts to zero.
-/

noncomputable section

namespace SaxlCounterexamples.EveryBase

open scoped BigOperators

/-- The binary field used throughout the deleted-module construction. -/
abbrev F2 := ZMod 2

/-- The binary permutation module on `Ω`. -/
abbrev PermMod (Ω : Type*) := Ω → F2

variable {H Ω : Type*} [Group H] [MulAction H Ω] [Fintype Ω]

instance permModDistribMulAction : DistribMulAction H (PermMod Ω) where
  smul g f x := f (g⁻¹ • x)
  one_smul f := by
    funext x
    change f ((1 : H)⁻¹ • x) = f x
    rw [inv_one, one_smul]
  mul_smul g h f := by
    funext x
    change f ((g * h)⁻¹ • x) = f (h⁻¹ • g⁻¹ • x)
    rw [mul_inv_rev, mul_smul]
  smul_add _ _ _ := rfl
  smul_zero _ := rfl

instance permModSMulCommClass : SMulCommClass H F2 (PermMod Ω) where
  smul_comm _ _ _ := by funext x; rfl

/-- Sum all coordinates of a vector in the permutation module. -/
def coordSum : PermMod Ω →ₗ[F2] F2 where
  toFun f := ∑ x, f x
  map_add' f g := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a f := by
    change (∑ x, a * f x) = a * ∑ x, f x
    rw [Finset.mul_sum]

theorem coordSum_smul (g : H) (f : PermMod Ω) :
    coordSum (g • f) = coordSum f := by
  exact (MulAction.toPerm g).symm.sum_comp f

/-- The deleted binary permutation module, i.e. the coordinate-sum kernel. -/
def DeletedModule (Ω : Type*) [Fintype Ω] :=
  LinearMap.ker (coordSum (Ω := Ω))

instance deletedModuleDistribMulAction :
    DistribMulAction H (DeletedModule Ω) where
  smul g v := ⟨g • (v : PermMod Ω), by
    change coordSum (g • (v : PermMod Ω)) = 0
    rw [coordSum_smul]
    exact v.property⟩
  one_smul v := by
    apply Subtype.ext
    change (1 : H) • (v : PermMod Ω) = (v : PermMod Ω)
    exact one_smul H _
  mul_smul g h v := by
    apply Subtype.ext
    change (g * h) • (v : PermMod Ω) = g • h • (v : PermMod Ω)
    exact mul_smul g h _
  smul_add _ _ _ := by apply Subtype.ext; rfl
  smul_zero _ := by apply Subtype.ext; rfl

instance deletedModuleSMulCommClass :
    SMulCommClass H F2 (DeletedModule Ω) where
  smul_comm _ _ _ := by apply Subtype.ext; rfl

/-- The inclusion of the deleted module into the full permutation module. -/
def deletedIncl : DeletedModule Ω →ₗ[F2] PermMod Ω :=
  (DeletedModule Ω).subtype

theorem coordSum_one (hΩodd : Odd (Fintype.card Ω)) :
    coordSum (1 : PermMod Ω) = 1 := by
  simp only [coordSum, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa using hΩodd.natCast_zmod_two

/-- Since `|Ω|` is odd, adding the coordinate sum times the all-ones vector
is an equivariant retraction onto the deleted module. -/
def deletedProj (hΩodd : Odd (Fintype.card Ω)) :
    PermMod Ω →ₗ[F2] DeletedModule Ω where
  toFun f := ⟨f + coordSum f • (fun _ ↦ (1 : F2)), by
    change coordSum (f + coordSum f • (1 : PermMod Ω)) = 0
    rw [map_add, map_smul, coordSum_one hΩodd]
    simpa [smul_eq_mul] using ZModModule.add_self (coordSum f)⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_add, Pi.add_apply, map_add, Pi.smul_apply,
      smul_eq_mul, mul_one]
    abel
  map_smul' a f := by
    apply Subtype.ext
    funext x
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, Pi.add_apply,
      map_smul, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem deletedProj_incl (hΩodd : Odd (Fintype.card Ω))
    (v : DeletedModule Ω) :
    deletedProj hΩodd (deletedIncl v) = v := by
  apply Subtype.ext
  funext x
  simp [deletedProj, deletedIncl, LinearMap.mem_ker.mp v.property]

theorem deletedProj_smul (hΩodd : Odd (Fintype.card Ω))
    (g : H) (f : PermMod Ω) :
    deletedProj hΩodd (g • f) = g • deletedProj hΩodd f := by
  apply Subtype.ext
  change (g • f : PermMod Ω) + coordSum (g • f) • (1 : PermMod Ω) =
    g • (f + coordSum f • (1 : PermMod Ω))
  rw [coordSum_smul]
  rfl

/-- Extend a deleted-module endomorphism to the full permutation module by
the canonical inclusion/retraction pair. -/
def extendDeletedEnd (hΩodd : Odd (Fintype.card Ω))
    (T : DeletedModule Ω →ₗ[F2] DeletedModule Ω) :
    PermMod Ω →ₗ[F2] PermMod Ω :=
  deletedIncl.comp (T.comp (deletedProj hΩodd))

@[simp] theorem extendDeletedEnd_incl (hΩodd : Odd (Fintype.card Ω))
    (T : DeletedModule Ω →ₗ[F2] DeletedModule Ω)
    (v : DeletedModule Ω) :
    extendDeletedEnd hΩodd T (deletedIncl v) = deletedIncl (T v) := by
  simp [extendDeletedEnd]

theorem extendDeletedEnd_smul (hΩodd : Odd (Fintype.card Ω))
    (T : DeletedModule Ω →ₗ[F2] DeletedModule Ω)
    (hT : ∀ (g : H) (v : DeletedModule Ω), T (g • v) = g • T v)
    (g : H) (f : PermMod Ω) :
    extendDeletedEnd hΩodd T (g • f) = g • extendDeletedEnd hΩodd T f := by
  simp only [extendDeletedEnd, LinearMap.comp_apply]
  rw [deletedProj_smul hΩodd, hT]
  rfl

/-- The deleted permutation module for the affine group over `Fq d`. -/
abbrev Vq (d : Nat) := DeletedModule (Fq d)

noncomputable instance fqDecidableEq (d : Nat) : DecidableEq (Fq d) :=
  Classical.typeDecidableEq _

noncomputable instance hqFintype (d : Nat) : Fintype (Hq d) :=
  Fintype.ofEquiv (Multiplicative (Fq d) × Cq d)
    { toFun := fun z ↦ ⟨z.1, z.2⟩
      invFun := fun z ↦ (z.left, z.right)
      left_inv := by rintro ⟨x, g⟩; rfl
      right_inv := by rintro ⟨x, g⟩; rfl }

instance hqNontrivial (d : Nat) : Nontrivial (Hq d) := by
  refine ⟨⟨⟨Multiplicative.ofAdd 0, 1⟩,
    ⟨Multiplicative.ofAdd 1, 1⟩, ?_⟩⟩
  intro h
  have hleft := congrArg (fun g : Hq d ↦ g.left.toAdd) h
  exact zero_ne_one hleft

noncomputable instance vqFintype (d : Nat) : Fintype (Vq d) :=
  Fintype.ofFinite (Vq d)

theorem coordSum_ne_zero_q (d : Nat) (hd : Odd d) :
    coordSum (Ω := Fq d) ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h (1 : PermMod (Fq d))
  rw [coordSum_one (by
    rw [Fintype.card_eq_nat_card]
    exact fq_odd_card d hd), LinearMap.zero_apply] at h1
  exact one_ne_zero h1

/-- The deleted module has the paper's dimension `3^d - 1`. -/
theorem vq_finrank (d : Nat) (hd : Odd d) :
    Module.finrank F2 (Vq d) = 3 ^ d - 1 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (coordSum_ne_zero_q d hd)
  rw [Module.finrank_pi F2, Fintype.card_eq_nat_card, fq_card d hd] at h
  exact Nat.eq_sub_of_add_eq h

/-- Consequently `Vq d` has exactly `2^(3^d-1)` elements. -/
theorem vq_card (d : Nat) (hd : Odd d) :
    Nat.card (Vq d) = 2 ^ (3 ^ d - 1) := by
  rw [Module.natCard_eq_pow_finrank (K := F2), vq_finrank d hd]
  norm_num

/-- The natural representation of `Hq d` on its deleted module. -/
def hqRepresentation (d : Nat) : Representation F2 (Hq d) (Vq d) :=
  Representation.ofDistribMulAction F2 (Hq d) (Vq d)

/-- The characteristic vector of `{0,1}`, written as a deleted vector. -/
noncomputable def pairVector (d : Nat) : Vq d :=
  ⟨Pi.basisFun F2 (Fq d) 0 + Pi.basisFun F2 (Fq d) 1, by
    change coordSum (Pi.basisFun F2 (Fq d) 0 +
      Pi.basisFun F2 (Fq d) 1) = 0
    rw [map_add]
    have hsum (a : Fq d) : coordSum (Pi.basisFun F2 (Fq d) a) = 1 := by
      rw [Pi.basisFun_apply]
      simp [coordSum, Pi.single_apply]
    rw [hsum, hsum]
    exact ZModModule.add_self 1⟩

@[simp] theorem pairVector_apply (d : Nat) (x : Fq d) :
    (pairVector d : PermMod (Fq d)) x =
      Pi.basisFun F2 (Fq d) 0 x + Pi.basisFun F2 (Fq d) 1 x := rfl

theorem pairVector_coe_eq_twoPointVector (d : Nat) :
    (pairVector d : PermMod (Fq d)) = twoPointVector d := by
  exact (twoPointVector_eq_basisSum d).symm

theorem pairVector_zero (d : Nat) :
    (pairVector d : PermMod (Fq d)) 0 = 1 := by
  rw [pairVector_apply, Pi.basisFun_apply, Pi.basisFun_apply]
  simp

theorem pairVector_ne_zero (d : Nat) : pairVector d ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : Vq d ↦ (v : PermMod (Fq d)) 0) h
  rw [pairVector_zero] at h0
  exact one_ne_zero h0

instance vqNontrivial (d : Nat) : Nontrivial (Vq d) :=
  ⟨⟨pairVector d, 0, pairVector_ne_zero d⟩⟩

theorem pairVector_isRegular (d : Nat) (hd : Odd d) :
    Saxl.IsRegularVector (Hq d) (Vq d) (pairVector d) := by
  intro g hg
  have hfix : ∀ x : Fq d,
      twoPointVector d (g⁻¹ • x) = twoPointVector d x := by
    intro x
    have h := congrArg (fun v : Vq d ↦ (v : PermMod (Fq d)) x) hg
    change (pairVector d : PermMod (Fq d)) (g⁻¹ • x) =
      (pairVector d : PermMod (Fq d)) x at h
    simpa only [pairVector_coe_eq_twoPointVector] using h
  have hinv : g⁻¹ = 1 :=
    hq_eq_one_of_twoPointVector_comp_eq d hd g⁻¹ hfix
  exact inv_eq_one.mp hinv

/-- Paper Lemma 6.1: the two-point vector gives a regular `Hq d`-orbit. -/
theorem hq_regularOrbit_exists (d : Nat) (hd : Odd d) :
    ∃ v : Vq d, Saxl.IsRegularVector (Hq d) (Vq d) v :=
  ⟨pairVector d, pairVector_isRegular d hd⟩

/-- Paper Lemma 6.1: the deleted-module action is faithful. -/
theorem hq_faithful (d : Nat) (hd : Odd d) : FaithfulSMul (Hq d) (Vq d) := by
  rw [faithfulSMul_iff]
  intro g hfix
  exact pairVector_isRegular d hd g (hfix (pairVector d))

/-- The complement-of-zero vector used in the displayed obstruction. -/
noncomputable def hqBadSeedVector (d : Nat) (hd : Odd d) : Vq d :=
  ⟨(1 : PermMod (Fq d)) + Pi.basisFun F2 (Fq d) 0, by
    change coordSum ((1 : PermMod (Fq d)) +
      Pi.basisFun F2 (Fq d) 0) = 0
    rw [map_add, coordSum_one (by
      rw [Fintype.card_eq_nat_card]
      exact fq_odd_card d hd)]
    have hsum : coordSum (Pi.basisFun F2 (Fq d) 0) = 1 := by
      rw [Pi.basisFun_apply]
      simp [coordSum, Pi.single_apply]
    rw [hsum]
    exact ZModModule.add_self 1⟩

@[simp] theorem hqBadSeedVector_apply (d : Nat) (hd : Odd d) (x : Fq d) :
    (hqBadSeedVector d hd : PermMod (Fq d)) x =
      if x = 0 then 0 else 1 := by
  rw [hqBadSeedVector]
  simp only [Pi.add_apply, Pi.one_apply, Pi.basisFun_apply]
  by_cases hx : x = 0
  · subst x
    simp [ZModModule.add_self]
  · simp [hx]

/-- The displayed bad seed vector is not regular: every nonidentity square
multiplier fixes both `0` and its complement. -/
theorem hqBadSeedVector_not_regular
    (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d) :
    ¬ Saxl.IsRegularVector (Hq d) (Vq d) (hqBadSeedVector d hd) := by
  have hcard : 1 < Nat.card (Cq d) := by
    rw [cq_card d hd]
    have hpow : 27 ≤ 3 ^ d := by
      calc
        27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ d := Nat.pow_le_pow_right (by omega) hd3
    omega
  let : Nontrivial (Cq d) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a, ha⟩ := exists_ne (1 : Cq d)
  let h : Hq d := ⟨Multiplicative.ofAdd 0, a⟩
  have hne : h ≠ 1 := by
    intro heq
    apply ha
    simpa [h] using congrArg SemidirectProduct.right heq
  intro hregular
  apply hne
  apply hregular h
  apply Subtype.ext
  funext x
  change (hqBadSeedVector d hd : PermMod (Fq d)) (h⁻¹ • x) =
    (hqBadSeedVector d hd : PermMod (Fq d)) x
  rw [hqBadSeedVector_apply, hqBadSeedVector_apply]
  congr 1
  apply propext
  have hzero : h⁻¹ • (0 : Fq d) = 0 := by
    simp [h]
  constructor
  · intro hx
    exact (MulAction.toPerm h⁻¹).injective (hx.trans hzero.symm)
  · rintro rfl
    exact hzero

/-- The coordinate map from the deleted module to binary-valued functions. -/
def deletedCoord (d : Nat) : Vq d →+ (Fq d → F2) :=
  (Vq d).subtype.toAddHom

end SaxlCounterexamples.EveryBase
