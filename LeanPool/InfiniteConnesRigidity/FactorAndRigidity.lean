/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import LeanPool.InfiniteConnesRigidity.SpectralAndPropertyT
import LeanPool.InfiniteConnesRigidity.GroupConstruction

/-!
# Factor equivalence and infinite Connes-rigidity family
-/

noncomputable section

namespace ConnesRigidity
section

open Function

universe u v w z

section TwoTorsion

variable (E : Type u) [AddCommGroup E]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev twoTorsion : AddSubgroup E := AddSubgroup.torsionBy E (2 : ℤ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_twoTorsion (x : E) :
    x ∈ twoTorsion E ↔ (2 : ℕ) • x = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def doubledSubgroup : AddSubgroup E :=
  (nsmulAddMonoidHom (α := E) 2).range

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem mem_doubledSubgroup (x : E) :
    x ∈ doubledSubgroup E ↔ ∃ y : E, (2 : ℕ) • y = x :=
  Iff.rfl

variable (hfour : ∀ x : E, (4 : ℕ) • x = 0)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def doubleIntoTwoTorsion : E →+ twoTorsion E where
  toFun x :=
    ⟨(2 : ℕ) • x, (mem_twoTorsion E _).2 <| by
      simpa only [← mul_nsmul, Nat.reduceMul] using hfour x⟩
  map_zero' := by
    apply Subtype.ext
    simp only [nsmul_zero, ZeroMemClass.coe_zero]
  map_add' x y := by
    apply Subtype.ext
    simp only [smul_add, AddMemClass.mk_add_mk]



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def doubledWithinTwoTorsion : AddSubgroup (twoTorsion E) :=
  (doubleIntoTwoTorsion E hfour).range

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem mem_doubledWithinTwoTorsion (x : twoTorsion E) :
    x ∈ doubledWithinTwoTorsion E hfour ↔
      ∃ y : E, (2 : ℕ) • y = (x : E) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    exact Subtype.ext hy

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev twoTorsionQuotient :=
  (twoTorsion E) ⧸ doubledWithinTwoTorsion E hfour

end TwoTorsion

section Isomorphism

variable {E : Type u} {E' : Type v} [AddCommGroup E] [AddCommGroup E']









end Isomorphism

section ExactExtension

variable (P : Type u) (E : Type v) (B₀ : Type w)
  [AddCommGroup P] [AddCommGroup E] [AddCommGroup B₀]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure ExponentFourExtension where
  iota : P →+ E
  sigma : E →+ B₀
  retraction : B₀ →+ P
  shift : P →+ P
  iota_injective : Function.Injective iota
  sigma_surjective : Function.Surjective sigma
  sigma_ker : sigma.ker = iota.range
  retraction_surjective : Function.Surjective retraction
  shift_injective : Function.Injective shift
  doubling : ∀ x : E,
    (2 : ℕ) • x = iota (shift (retraction (sigma x)))

namespace ExponentFourExtension

variable {P E B₀}
variable (F : ExponentFourExtension P E B₀)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem sigma_iota (v : P) : F.sigma (F.iota v) = 0 := by
  have hv : F.iota v ∈ F.sigma.ker := by
    rw [F.sigma_ker]
    exact ⟨v, rfl⟩
  exact hv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exponent_four (F : ExponentFourExtension P E B₀) (x : E) :
    (4 : ℕ) • x = 0 := by
  calc
    (4 : ℕ) • x = (2 : ℕ) • ((2 : ℕ) • x) := by
      rw [← mul_nsmul]
    _ = F.iota (F.shift (F.retraction (F.sigma ((2 : ℕ) • x)))) :=
      F.doubling ((2 : ℕ) • x)
    _ = 0 := by
      rw [F.doubling x, F.sigma_iota, map_zero, map_zero, map_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_twoTorsion_iff (x : E) :
    x ∈ twoTorsion E ↔ F.retraction (F.sigma x) = 0 := by
  rw [mem_twoTorsion, F.doubling]
  constructor
  · intro h
    apply F.shift_injective
    apply F.iota_injective
    simpa only [map_zero] using h
  · intro h
    simp only [h, map_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem doubledSubgroup_eq_iota_shift_range :
    doubledSubgroup E = F.shift.range.map F.iota := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (mem_doubledSubgroup E x).1 hx
    refine ⟨F.shift (F.retraction (F.sigma y)),
      ⟨F.retraction (F.sigma y), rfl⟩, ?_⟩
    exact (F.doubling y).symm.trans hy
  · rintro ⟨_, ⟨v, rfl⟩, hv⟩
    obtain ⟨b, hb⟩ := F.retraction_surjective v
    obtain ⟨y, hy⟩ := F.sigma_surjective b
    apply (mem_doubledSubgroup E x).2
    refine ⟨y, ?_⟩
    calc
      (2 : ℕ) • y = F.iota (F.shift (F.retraction (F.sigma y))) :=
        F.doubling y
      _ = F.iota (F.shift v) := by rw [hy, hb]
      _ = x := hv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def iotaIntoTwoTorsion : P →+ twoTorsion E where
  toFun v :=
    ⟨F.iota v, (F.mem_twoTorsion_iff _).2 <| by simp only [sigma_iota, map_zero]⟩
  map_zero' := Subtype.ext (F.iota.map_zero)
  map_add' x y := Subtype.ext (F.iota.map_add x y)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem iota_mem_doubledWithinTwoTorsion_iff (v : P) :
    F.iotaIntoTwoTorsion v ∈
        doubledWithinTwoTorsion E F.exponent_four ↔
      v ∈ F.shift.range := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ :=
      (mem_doubledWithinTwoTorsion E F.exponent_four _).1 h
    have hi : F.iota (F.shift (F.retraction (F.sigma y))) = F.iota v := by
      exact (F.doubling y).symm.trans hy
    exact ⟨F.retraction (F.sigma y), F.iota_injective hi⟩
  · intro hv
    have hi : F.iota v ∈ doubledSubgroup E := by
      rw [F.doubledSubgroup_eq_iota_shift_range]
      exact ⟨v, hv, rfl⟩
    obtain ⟨y, hy⟩ := (mem_doubledSubgroup E (F.iota v)).1 hi
    exact (mem_doubledWithinTwoTorsion E F.exponent_four _).2 ⟨y, hy⟩

end ExponentFourExtension

end ExactExtension

section QuotientAction

variable (K : Type u) (E : Type v)
  [Group K] [AddCommGroup E] [DistribMulAction K E]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance twoTorsionDistribMulAction : DistribMulAction K (twoTorsion E) where
  smul k x :=
    ⟨k • (x : E), (mem_twoTorsion E _).2 <| by
      simpa only [two_nsmul, smul_add, smul_zero] using
        congrArg (fun y : E => k • y) ((mem_twoTorsion E _).1 x.property)⟩
  one_smul x := Subtype.ext (one_smul K (x : E))
  mul_smul k l x := Subtype.ext (mul_smul k l (x : E))
  smul_zero k := Subtype.ext (smul_zero k)
  smul_add k x y := Subtype.ext (smul_add k (x : E) (y : E))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem twoTorsion_smul_val (k : K) (x : twoTorsion E) :
    ((k • x : twoTorsion E) : E) = k • (x : E) := rfl

variable (hfour : ∀ x : E, (4 : ℕ) • x = 0)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem smul_mem_doubledWithinTwoTorsion
    (k : K) {x : twoTorsion E} (hx : x ∈ doubledWithinTwoTorsion E hfour) :
    k • x ∈ doubledWithinTwoTorsion E hfour := by
  obtain ⟨y, hy⟩ := (mem_doubledWithinTwoTorsion E hfour x).1 hx
  apply (mem_doubledWithinTwoTorsion E hfour (k • x)).2
  refine ⟨k • y, ?_⟩
  simpa only [two_nsmul, twoTorsion_smul_val, smul_add] using congrArg (fun z : E => k • z) hy

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def twoTorsionQuotientSmulAddHom (k : K) :
    twoTorsionQuotient E hfour →+ twoTorsionQuotient E hfour :=
  QuotientAddGroup.map
    (doubledWithinTwoTorsion E hfour)
    (doubledWithinTwoTorsion E hfour)
    (DistribSMul.toAddMonoidHom (twoTorsion E) k)
    (fun _ hx => smul_mem_doubledWithinTwoTorsion K E hfour k hx)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance twoTorsionQuotientSMul : SMul K (twoTorsionQuotient E hfour) where
  smul k := twoTorsionQuotientSmulAddHom K E hfour k

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem twoTorsionQuotient_smul_mk (k : K) (x : twoTorsion E) :
    k • (QuotientAddGroup.mk' (doubledWithinTwoTorsion E hfour) x) =
      QuotientAddGroup.mk' (doubledWithinTwoTorsion E hfour) (k • x) := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance twoTorsionQuotientDistribMulAction :
    DistribMulAction K (twoTorsionQuotient E hfour) :=
  Function.Surjective.distribMulAction
    (QuotientAddGroup.mk' (doubledWithinTwoTorsion E hfour))
    (QuotientAddGroup.mk'_surjective (doubledWithinTwoTorsion E hfour))
    (fun _ _ => rfl)

end QuotientAction

section FiniteOrbits

variable (K : Type u) (A : Type v)
  [Group K] [AddCommGroup A] [DistribMulAction K A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def finiteOrbitSubgroup : AddSubgroup A where
  carrier := {a | (MulAction.orbit K a).Finite}
  zero_mem' := by
    simp only [MulAction.orbit, Set.mem_ofPred_eq, smul_zero, Set.range_const, Set.finite_singleton]
  add_mem' := by
    intro x y hx hy
    refine (hx.image2 (· + ·) hy).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨g • x, ⟨g, rfl⟩, g • y, ⟨g, rfl⟩, ?_⟩
    exact (smul_add g x y).symm
  neg_mem' := by
    intro x hx
    refine (hx.image Neg.neg).subset ?_
    rintro _ ⟨g, rfl⟩
    refine ⟨g • x, ⟨g, rfl⟩, ?_⟩
    exact (smul_neg g x).symm



variable {K A}
variable {K' : Type w} {A' : Type z}
  [Group K'] [AddCommGroup A'] [DistribMulAction K' A']









end FiniteOrbits

section QuotientEquivariance

variable {K : Type u} {K' : Type v} {E : Type w} {E' : Type z}
  [Group K] [Group K'] [AddCommGroup E] [AddCommGroup E']
  [DistribMulAction K E] [DistribMulAction K' E']

variable (hfour : ∀ x : E, (4 : ℕ) • x = 0)
variable (hfour' : ∀ x : E', (4 : ℕ) • x = 0)



end QuotientEquivariance

section FiniteOrbitKernel

variable {K : Type u} {A : Type v} {B₀ : Type w}
  [Group K] [AddCommGroup A] [AddCommGroup B₀]
  [DistribMulAction K A] [DistribMulAction K B₀]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem orbit_image_eq_of_equivariantHom
    (p : A →+ B₀)
    (hp : ∀ (k : K) (a : A), p (k • a) = k • p a)
    (a : A) :
    p '' MulAction.orbit K a = MulAction.orbit K (p a) := by
  ext b
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (hp k a).symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k • a, ⟨k, rfl⟩, (hp k a).trans hk⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteOrbit_iff_equivariantHom_eq_zero
    (p : A →+ B₀) [Finite p.ker]
    (hp : ∀ (k : K) (a : A), p (k • a) = k • p a)
    (hB : ∀ b : B₀, b ≠ 0 → ¬(MulAction.orbit K b).Finite)
    (a : A) :
    (MulAction.orbit K a).Finite ↔ p a = 0 := by
  constructor
  · intro ha
    by_contra hpa
    apply hB (p a) hpa
    rw [← orbit_image_eq_of_equivariantHom p hp a]
    exact ha.image p
  · intro ha
    apply (Set.toFinite (p.ker : Set A)).subset
    rintro _ ⟨k, rfl⟩
    change k • a ∈ p.ker
    rw [AddMonoidHom.mem_ker, hp, ha, smul_zero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def finiteOrbitSubgroupKerEquiv
    (p : A →+ B₀) [Finite p.ker]
    (hp : ∀ (k : K) (a : A), p (k • a) = k • p a)
    (hB : ∀ b : B₀, b ≠ 0 → ¬(MulAction.orbit K b).Finite) :
    finiteOrbitSubgroup K A ≃+ p.ker where
  toFun a := ⟨a, (AddMonoidHom.mem_ker).2
    ((finiteOrbit_iff_equivariantHom_eq_zero p hp hB a).1 a.property)⟩
  invFun a := ⟨a, (finiteOrbit_iff_equivariantHom_eq_zero p hp hB a).2
    ((AddMonoidHom.mem_ker).1 a.property)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finite_ker_of_shiftedQuotient_equiv
    (n : ℕ) (p : A →+ B₀)
    (e : ShiftedQuotient n ≃+ p.ker) : Finite p.ker :=
  Finite.of_injective
    (fun x : p.ker => shiftedQuotientCoeffEquiv n (e.symm x))
    ((shiftedQuotientCoeffEquiv n).injective.comp e.symm.injective)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def finiteOrbitSubgroupShiftedQuotientEquiv
    (n : ℕ) (p : A →+ B₀)
    (hp : ∀ (k : K) (a : A), p (k • a) = k • p a)
    (hB : ∀ b : B₀, b ≠ 0 → ¬(MulAction.orbit K b).Finite)
    (e : ShiftedQuotient n ≃+ p.ker) :
    finiteOrbitSubgroup K A ≃+ ShiftedQuotient n := by
  letI : Finite p.ker := finite_ker_of_shiftedQuotient_equiv n p e
  exact (finiteOrbitSubgroupKerEquiv p hp hB).trans e.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteOrbitSubgroup_card_eq_two_pow_four_mul
    (n : ℕ) (p : A →+ B₀)
    (hp : ∀ (k : K) (a : A), p (k • a) = k • p a)
    (hB : ∀ b : B₀, b ≠ 0 → ¬(MulAction.orbit K b).Finite)
    (e : ShiftedQuotient n ≃+ p.ker) :
    Nat.card (finiteOrbitSubgroup K A) = 2 ^ (4 * n) := by
  rw [Nat.card_congr
    (finiteOrbitSubgroupShiftedQuotientEquiv n p hp hB e).toEquiv]
  exact shiftedQuotient_card n

end FiniteOrbitKernel

namespace ExponentFourExtension

variable {P : Type u} {E : Type v} {B₀ : Type w}
  [AddCommGroup P] [AddCommGroup E] [AddCommGroup B₀]
  (D : ExponentFourExtension P E B₀)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def sigmaIntoRetractionKer : twoTorsion E →+ D.retraction.ker where
  toFun x := ⟨D.sigma x, (D.mem_twoTorsion_iff x).1 x.property⟩
  map_zero' := Subtype.ext D.sigma.map_zero
  map_add' x y := Subtype.ext (D.sigma.map_add x y)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem doubledWithin_le_sigmaIntoRetractionKer_ker :
    doubledWithinTwoTorsion E D.exponent_four ≤ D.sigmaIntoRetractionKer.ker := by
  intro x hx
  obtain ⟨e, he⟩ := (mem_doubledWithinTwoTorsion E D.exponent_four x).1 hx
  apply Subtype.ext
  change D.sigma (x : E) = 0
  rw [← he, D.doubling, D.sigma_iota]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientSigma : twoTorsionQuotient E D.exponent_four →+ D.retraction.ker :=
  QuotientAddGroup.lift (doubledWithinTwoTorsion E D.exponent_four)
    D.sigmaIntoRetractionKer D.doubledWithin_le_sigmaIntoRetractionKer_ker

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientSigma_mk (x : twoTorsion E) :
    D.quotientSigma
      ((QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four)) x) =
      D.sigmaIntoRetractionKer x :=
  QuotientAddGroup.lift_mk' (doubledWithinTwoTorsion E D.exponent_four)
    D.doubledWithin_le_sigmaIntoRetractionKer_ker x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientIotaBase : P →+ twoTorsionQuotient E D.exponent_four :=
  (QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four)).comp
    D.iotaIntoTwoTorsion



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem shift_range_le_quotientIotaBase_ker :
    D.shift.range ≤ D.quotientIotaBase.ker := by
  rintro _ ⟨p, rfl⟩
  change (QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four))
    (D.iotaIntoTwoTorsion (D.shift p)) = 0
  apply (QuotientAddGroup.eq_zero_iff _).2
  exact (D.iota_mem_doubledWithinTwoTorsion_iff (D.shift p)).2 ⟨p, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientIota : (P ⧸ D.shift.range) →+
    twoTorsionQuotient E D.exponent_four :=
  QuotientAddGroup.lift D.shift.range D.quotientIotaBase
    D.shift_range_le_quotientIotaBase_ker

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientIota_mk (p : P) :
    D.quotientIota ((QuotientAddGroup.mk' D.shift.range) p) =
      D.quotientIotaBase p :=
  QuotientAddGroup.lift_mk' D.shift.range D.shift_range_le_quotientIotaBase_ker p

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientIota_injective : Function.Injective D.quotientIota := by
  apply (AddMonoidHom.ker_eq_bot_iff D.quotientIota).1
  apply bot_unique
  intro q hq
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk'_surjective D.shift.range q
  change D.quotientIota ((QuotientAddGroup.mk' D.shift.range) p) = 0 at hq
  rw [D.quotientIota_mk] at hq
  change (QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four))
    (D.iotaIntoTwoTorsion p) = 0 at hq
  have hdouble : D.iotaIntoTwoTorsion p ∈
      doubledWithinTwoTorsion E D.exponent_four :=
    (QuotientAddGroup.eq_zero_iff _).1 hq
  obtain ⟨e, he⟩ :=
    (mem_doubledWithinTwoTorsion E D.exponent_four _).1 hdouble
  have hp : D.shift (D.retraction (D.sigma e)) = p := by
    apply D.iota_injective
    exact (D.doubling e).symm.trans he
  change (QuotientAddGroup.mk' D.shift.range) p = 0
  apply (QuotientAddGroup.eq_zero_iff p).2
  exact ⟨D.retraction (D.sigma e), hp⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientSigma_ker_eq_quotientIota_range :
    D.quotientSigma.ker = D.quotientIota.range := by
  ext a
  obtain ⟨x, rfl⟩ :=
    QuotientAddGroup.mk'_surjective (doubledWithinTwoTorsion E D.exponent_four) a
  constructor
  · intro hx
    change D.quotientSigma
      ((QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four)) x) = 0 at hx
    rw [D.quotientSigma_mk] at hx
    have hker : (x : E) ∈ D.sigma.ker := by
      change D.sigma (x : E) = 0
      exact congrArg Subtype.val hx
    rw [D.sigma_ker] at hker
    obtain ⟨p, hp⟩ := hker
    refine ⟨(QuotientAddGroup.mk' D.shift.range) p, ?_⟩
    rw [D.quotientIota_mk]
    change
      (QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four))
          (D.iotaIntoTwoTorsion p) =
        (QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four)) x
    congr 1
    exact Subtype.ext hp
  · rintro ⟨q, hq⟩
    obtain ⟨p, rfl⟩ := QuotientAddGroup.mk'_surjective D.shift.range q
    rw [D.quotientIota_mk] at hq
    change D.quotientSigma
      ((QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four)) x) = 0
    rw [← hq]
    change D.quotientSigma
      ((QuotientAddGroup.mk' (doubledWithinTwoTorsion E D.exponent_four))
        (D.iotaIntoTwoTorsion p)) = 0
    rw [D.quotientSigma_mk]
    apply Subtype.ext
    exact D.sigma_iota p

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientIotaIntoKernel : (P ⧸ D.shift.range) →+ D.quotientSigma.ker where
  toFun q :=
    ⟨D.quotientIota q, by
      rw [D.quotientSigma_ker_eq_quotientIota_range]
      exact ⟨q, rfl⟩⟩
  map_zero' := Subtype.ext D.quotientIota.map_zero
  map_add' q r := Subtype.ext (D.quotientIota.map_add q r)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def quotientIotaKernelEquiv :
    (P ⧸ D.shift.range) ≃+ D.quotientSigma.ker := by
  apply AddEquiv.ofBijective D.quotientIotaIntoKernel
  constructor
  · intro q r hqr
    apply D.quotientIota_injective
    exact congrArg Subtype.val hqr
  · intro a
    have ha : (a : twoTorsionQuotient E D.exponent_four) ∈
        D.quotientIota.range := by
      rw [← D.quotientSigma_ker_eq_quotientIota_range]
      exact a.property
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, Subtype.ext hq⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def shiftedQuotientToKernelEquiv
    (D : ExponentFourExtension V E B₀) (n : ℕ)
    (hshift : D.shift = (shiftVector n).toAddMonoidHom) :
    ShiftedQuotient n ≃+ D.quotientSigma.ker := by
  have hrange : D.shift.range = (shiftedSubmodule n).toAddSubgroup := by
    rw [hshift, ← LinearMap.range_toAddSubgroup, shiftVector_range]
  let e : ShiftedQuotient n ≃+ (V ⧸ D.shift.range) :=
    QuotientAddGroup.congr (shiftedSubmodule n).toAddSubgroup D.shift.range
      (AddEquiv.refl V) (by simpa only [AddEquiv.coe_addMonoidHom_refl,
                              AddSubgroup.map_id] using hrange.symm)
  exact e.trans D.quotientIotaKernelEquiv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def quotientSigmaToB : twoTorsionQuotient E D.exponent_four →+ B₀ :=
  D.retraction.ker.subtype.comp D.quotientSigma



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientSigmaToB_ker_eq :
    D.quotientSigmaToB.ker = D.quotientSigma.ker := by
  ext a
  change (D.quotientSigma a : B₀) = 0 ↔ D.quotientSigma a = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def quotientSigmaToBKernelEquiv :
    D.quotientSigma.ker ≃+ D.quotientSigmaToB.ker := by
  rw [D.quotientSigmaToB_ker_eq]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotientSigmaToB_smul
    {K : Type z} [Group K]
    [DistribMulAction K E] [DistribMulAction K B₀]
    (hsigma : ∀ (k : K) (x : E), D.sigma (k • x) = k • D.sigma x)
    (k : K) (a : twoTorsionQuotient E D.exponent_four) :
    D.quotientSigmaToB (k • a) = k • D.quotientSigmaToB a := by
  induction a using Quotient.inductionOn with
  | _ x =>
      change D.sigma (k • (x : E)) = k • D.sigma (x : E)
      exact hsigma k x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem finiteOrbitSubgroup_card_toB
    (D : ExponentFourExtension V E B₀)
    {K : Type z} [Group K]
    [DistribMulAction K E] [DistribMulAction K B₀]
    (hsigma : ∀ (k : K) (x : E), D.sigma (k • x) = k • D.sigma x)
    (hinfinite : ∀ b : B₀, b ≠ 0 → ¬(MulAction.orbit K b).Finite)
    (n : ℕ) (hshift : D.shift = (shiftVector n).toAddMonoidHom) :
    Nat.card (finiteOrbitSubgroup K
      (twoTorsionQuotient E D.exponent_four)) = 2 ^ (4 * n) := by
  exact finiteOrbitSubgroup_card_eq_two_pow_four_mul n D.quotientSigmaToB
    (D.quotientSigmaToB_smul hsigma) hinfinite
    ((D.shiftedQuotientToKernelEquiv n hshift).trans
      D.quotientSigmaToBKernelEquiv)

end ExponentFourExtension

private theorem two_pow_four_injective {m n : ℕ}
    (h : 2 ^ (4 * m) = 2 ^ (4 * n)) : m = n := by
  have hfour : 4 * m = 4 * n := Nat.pow_right_injective (by decide : 2 ≤ 2) h
  omega

end

section

open ConnesRigidity

section

universe u v w z

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def involutionGenerated (G : Type u) [Group G] : Subgroup G :=
  Subgroup.closure {g : G | g ^ (2 : ℕ) = 1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def torsionSquareGenerated (G : Type u) [Group G] : Subgroup G :=
  Subgroup.closure {g : G | ∃ z : G, IsOfFinOrder z ∧ g = z ^ (2 : ℕ)}

section CharacteristicSubgroups

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mulEquiv_map_involutionGenerated (e : G ≃* H) :
    (involutionGenerated G).map e.toMonoidHom = involutionGenerated H := by
  rw [involutionGenerated, involutionGenerated, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ^ (2 : ℕ) = 1 at hx
    change e x ^ (2 : ℕ) = 1
    simpa only [map_pow, map_one] using congrArg e hx
  · intro hy
    change y ^ (2 : ℕ) = 1 at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ^ (2 : ℕ) = 1
    simpa only [map_pow, map_one] using congrArg e.symm hy

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mulEquiv_map_torsionSquareGenerated (e : G ≃* H) :
    (torsionSquareGenerated G).map e.toMonoidHom =
      torsionSquareGenerated H := by
  rw [torsionSquareGenerated, torsionSquareGenerated, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, hz, rfl⟩
    exact ⟨e z, e.toMonoidHom.isOfFinOrder hz, by simp only [MulEquiv.toMonoidHom_eq_coe,
                                                    MonoidHom.coe_coe, map_pow]⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(e.symm z) ^ (2 : ℕ), ?_, ?_⟩
    · exact ⟨e.symm z, e.symm.toMonoidHom.isOfFinOrder hz, rfl⟩
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_pow, MulEquiv.apply_symm_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem involutionGenerated_characteristic (G : Type u) [Group G] :
    (involutionGenerated G).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr mulEquiv_map_involutionGenerated

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem torsionSquareGenerated_characteristic (G : Type u) [Group G] :
    (torsionSquareGenerated G).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr mulEquiv_map_torsionSquareGenerated

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance involutionGenerated_normal (G : Type u) [Group G] :
    (involutionGenerated G).Normal := by
  let : (involutionGenerated G).Characteristic :=
    involutionGenerated_characteristic G
  infer_instance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance torsionSquareGenerated_normal (G : Type u) [Group G] :
    (torsionSquareGenerated G).Normal := by
  let : (torsionSquareGenerated G).Characteristic :=
    torsionSquareGenerated_characteristic G
  infer_instance

end CharacteristicSubgroups

section IntrinsicSubquotient

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def intrinsicDenominator (I D : Subgroup G) : Subgroup I :=
  D.comap I.subtype

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance intrinsicDenominator_normal (I D : Subgroup G) [D.Normal] :
    (intrinsicDenominator I D).Normal :=
  Subgroup.normal_comap I.subtype

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem intrinsicDenominator_conj_map
    (I D : Subgroup G) [I.Normal] [D.Normal] (g : G) :
    (intrinsicDenominator I D).map (MulAut.conjNormal g : I ≃* I) =
      intrinsicDenominator I D := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (inferInstance : D.Normal).conj_mem (y : G) hy g
  · intro hx
    refine ⟨(MulAut.conjNormal g).symm x, ?_, ?_⟩
    · change (↑((MulAut.conjNormal g).symm x) : G) ∈ D
      rw [MulAut.conjNormal_symm_apply]
      simpa only [inv_inv] using (inferInstance : D.Normal).conj_mem (x : G) hx g⁻¹
    · exact (MulAut.conjNormal g).apply_symm_apply x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev intrinsicSubquotient (I D : Subgroup G) :=
  I ⧸ intrinsicDenominator I D

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def intrinsicConjugationAut
    (I D : Subgroup G) [I.Normal] [D.Normal] (g : G) :
    MulAut (intrinsicSubquotient I D) :=
  QuotientGroup.congr (intrinsicDenominator I D) (intrinsicDenominator I D)
    (MulAut.conjNormal g) (intrinsicDenominator_conj_map I D g)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def intrinsicConjugationAction
    (I D : Subgroup G) [I.Normal] [D.Normal] :
    G →* MulAut (intrinsicSubquotient I D) where
  toFun := intrinsicConjugationAut I D
  map_one' := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | _ x =>
      change QuotientGroup.mk' (intrinsicDenominator I D)
          (MulAut.conjNormal (1 : G) x) =
        QuotientGroup.mk' (intrinsicDenominator I D) x
      congr 1
      exact DFunLike.congr_fun
        (map_one (MulAut.conjNormal : G →* MulAut I)) x
  map_mul' g h := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | _ x =>
      change QuotientGroup.mk' (intrinsicDenominator I D)
          (MulAut.conjNormal (g * h) x) =
        QuotientGroup.mk' (intrinsicDenominator I D)
          (MulAut.conjNormal g (MulAut.conjNormal h x))
      congr 1
      exact DFunLike.congr_fun
        (map_mul (MulAut.conjNormal : G →* MulAut I) g h) x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def intrinsicRestrictedEquiv
    {I : Subgroup G} {I' : Subgroup H}
    (e : G ≃* H) (hI : I.map (e : G →* H) = I') : I ≃* I' :=
  (e.subgroupMap I).trans (MulEquiv.subgroupCongr hI)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem intrinsicRestrictedEquiv_apply_val
    {I : Subgroup G} {I' : Subgroup H}
    (e : G ≃* H) (hI : I.map (e : G →* H) = I') (x : I) :
    (intrinsicRestrictedEquiv (I := I) (I' := I') e hI x : H) = e x := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem intrinsicRestrictedEquiv_map_denominator
    {I D : Subgroup G} {I' D' : Subgroup H}
    (e : G ≃* H) (hI : I.map (e : G →* H) = I')
    (hD : D.map (e : G →* H) = D') :
    (intrinsicDenominator I D).map
      (intrinsicRestrictedEquiv e hI : I →* I') =
        intrinsicDenominator I' D' := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change e (y : G) ∈ D'
    rw [← hD]
    exact Subgroup.mem_map_of_mem (K := D) (e : G →* H) hy
  · intro hx
    let y : I := (intrinsicRestrictedEquiv e hI).symm x
    refine ⟨y, ?_,
      (intrinsicRestrictedEquiv e hI).apply_symm_apply x⟩
    change (y : G) ∈ D
    have hx' : (x : H) ∈ D' := hx
    rw [← hD] at hx'
    obtain ⟨z, hz, heq⟩ := hx'
    have hy : (y : G) = z := by
      apply e.injective
      calc
        e (y : G) = (x : H) := by
          change (intrinsicRestrictedEquiv e hI y : H) = (x : H)
          exact congrArg Subtype.val
            ((intrinsicRestrictedEquiv e hI).apply_symm_apply x)
        _ = e z := heq.symm
    simpa only [hy, SetLike.mem_coe] using hz

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def intrinsicSubquotientEquiv
    {I D : Subgroup G} {I' D' : Subgroup H}
    [D.Normal] [D'.Normal]
    (e : G ≃* H) (hI : I.map (e : G →* H) = I')
    (hD : D.map (e : G →* H) = D') :
    intrinsicSubquotient I D ≃* intrinsicSubquotient I' D' :=
  QuotientGroup.congr (intrinsicDenominator I D)
    (intrinsicDenominator I' D')
    (intrinsicRestrictedEquiv e hI)
    (intrinsicRestrictedEquiv_map_denominator e hI hD)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem intrinsicSubquotientEquiv_conjugation
    {I D : Subgroup G} {I' D' : Subgroup H}
    [I.Normal] [D.Normal] [I'.Normal] [D'.Normal]
    (e : G ≃* H) (hI : I.map (e : G →* H) = I')
    (hD : D.map (e : G →* H) = D') (g : G)
    (q : intrinsicSubquotient I D) :
    intrinsicSubquotientEquiv e hI hD
        (intrinsicConjugationAction I D g q) =
      intrinsicConjugationAction I' D' (e g)
        (intrinsicSubquotientEquiv e hI hD q) := by
  induction q using QuotientGroup.induction_on with
  | _ x =>
    change QuotientGroup.mk' (intrinsicDenominator I' D')
        (intrinsicRestrictedEquiv e hI (MulAut.conjNormal g x)) =
      QuotientGroup.mk' (intrinsicDenominator I' D')
        (MulAut.conjNormal (e g) (intrinsicRestrictedEquiv e hI x))
    congr 1
    apply Subtype.ext
    simp only [intrinsicRestrictedEquiv_apply_val, MulAut.conjNormal_apply, map_mul, map_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def HasFiniteIntrinsicOrbit
    (I D : Subgroup G) [I.Normal] [D.Normal]
    (q : intrinsicSubquotient I D) : Prop :=
  Set.Finite (Set.range fun g : G => intrinsicConjugationAction I D g q)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem intrinsic_conjugation_orbit_image
    {I D : Subgroup G} {I' D' : Subgroup H}
    [I.Normal] [D.Normal] [I'.Normal] [D'.Normal]
    (e : G ≃* H) (hI : I.map (e : G →* H) = I')
    (hD : D.map (e : G →* H) = D')
    (q : intrinsicSubquotient I D) :
    Set.range (fun h : H => intrinsicConjugationAction I' D' h
      (intrinsicSubquotientEquiv e hI hD q)) =
      intrinsicSubquotientEquiv e hI hD ''
        Set.range (fun g : G => intrinsicConjugationAction I D g q) := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨intrinsicConjugationAction I D (e.symm h) q,
      ⟨e.symm h, rfl⟩, ?_⟩
    simpa only [MulEquiv.apply_symm_apply] using
      intrinsicSubquotientEquiv_conjugation e hI hD (e.symm h) q
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g,
      (intrinsicSubquotientEquiv_conjugation e hI hD g q).symm⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasFiniteIntrinsicOrbit_iff
    {I D : Subgroup G} {I' D' : Subgroup H}
    [I.Normal] [D.Normal] [I'.Normal] [D'.Normal]
    (e : G ≃* H) (hI : I.map (e : G →* H) = I')
    (hD : D.map (e : G →* H) = D')
    (q : intrinsicSubquotient I D) :
    HasFiniteIntrinsicOrbit I' D' (intrinsicSubquotientEquiv e hI hD q) ↔
      HasFiniteIntrinsicOrbit I D q := by
  unfold HasFiniteIntrinsicOrbit
  rw [intrinsic_conjugation_orbit_image e hI hD q]
  exact Set.finite_image_iff (intrinsicSubquotientEquiv e hI hD).injective.injOn

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def IntrinsicFiniteOrbitCarrier
    (I D : Subgroup G) [I.Normal] [D.Normal] :=
  {q : intrinsicSubquotient I D // HasFiniteIntrinsicOrbit I D q}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def intrinsicFiniteOrbitEquiv
    {I D : Subgroup G} {I' D' : Subgroup H}
    [I.Normal] [D.Normal] [I'.Normal] [D'.Normal]
    (e : G ≃* H) (hI : I.map (e : G →* H) = I')
    (hD : D.map (e : G →* H) = D') :
    IntrinsicFiniteOrbitCarrier I D ≃ IntrinsicFiniteOrbitCarrier I' D' :=
  (intrinsicSubquotientEquiv e hI hD).toEquiv.subtypeEquiv
    (fun q => (hasFiniteIntrinsicOrbit_iff e hI hD q).symm)

end IntrinsicSubquotient

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperGroupCardinalInvariant : GroupCardinalInvariant.{u} where
  carrier G := IntrinsicFiniteOrbitCarrier
    (involutionGenerated G) (torsionSquareGenerated G)
  mapMulEquiv e := intrinsicFiniteOrbitEquiv e
    (mulEquiv_map_involutionGenerated e)
    (mulEquiv_map_torsionSquareGenerated e)

section AbstractOrbitBridge

variable {G : Type u} [Group G]
variable {I D : Subgroup G} [I.Normal] [D.Normal]
variable {K : Type v} [Group K]
variable {A : Type w} [AddCommGroup A] [DistribMulAction K A]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem intrinsic_conjugation_orbit_image_additive
    (projection : G →* K) (hprojection : Function.Surjective projection)
    (e : intrinsicSubquotient I D ≃* Multiplicative A)
    (he : ∀ (g : G) (q : intrinsicSubquotient I D),
      Multiplicative.toAdd (e (intrinsicConjugationAction I D g q)) =
        projection g • Multiplicative.toAdd (e q))
    (q : intrinsicSubquotient I D) :
    (fun x => Multiplicative.toAdd (e x)) ''
        Set.range (fun g : G => intrinsicConjugationAction I D g q) =
      MulAction.orbit K (Multiplicative.toAdd (e q)) := by
  ext a
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact MulAction.mem_orbit_iff.mpr ⟨projection g, (he g q).symm⟩
  · intro ha
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp ha
    obtain ⟨g, rfl⟩ := hprojection k
    refine ⟨intrinsicConjugationAction I D g q, ⟨g, rfl⟩, ?_⟩
    exact (he g q).trans hk

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasFiniteIntrinsicOrbit_iff_finiteOrbit
    (projection : G →* K) (hprojection : Function.Surjective projection)
    (e : intrinsicSubquotient I D ≃* Multiplicative A)
    (he : ∀ (g : G) (q : intrinsicSubquotient I D),
      Multiplicative.toAdd (e (intrinsicConjugationAction I D g q)) =
        projection g • Multiplicative.toAdd (e q))
    (q : intrinsicSubquotient I D) :
    HasFiniteIntrinsicOrbit I D q ↔
      (MulAction.orbit K (Multiplicative.toAdd (e q))).Finite := by
  unfold HasFiniteIntrinsicOrbit
  rw [← intrinsic_conjugation_orbit_image_additive
    projection hprojection e he q]
  exact (Set.finite_image_iff
    (Multiplicative.toAdd.injective.comp e.injective).injOn).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def intrinsicFiniteOrbitCarrierEquivFiniteOrbitSubgroup
    (projection : G →* K) (hprojection : Function.Surjective projection)
    (e : intrinsicSubquotient I D ≃* Multiplicative A)
    (he : ∀ (g : G) (q : intrinsicSubquotient I D),
      Multiplicative.toAdd (e (intrinsicConjugationAction I D g q)) =
        projection g • Multiplicative.toAdd (e q)) :
    IntrinsicFiniteOrbitCarrier I D ≃ finiteOrbitSubgroup K A where
  toFun q := ⟨Multiplicative.toAdd (e q.val),
    (hasFiniteIntrinsicOrbit_iff_finiteOrbit
      projection hprojection e he q.val).mp q.property⟩
  invFun a := ⟨e.symm (Multiplicative.ofAdd a),
    (hasFiniteIntrinsicOrbit_iff_finiteOrbit
      projection hprojection e he _).mpr <| by
      have ha : (MulAction.orbit K (a : A)).Finite := a.property
      simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using ha⟩
  left_inv q := by
    apply Subtype.ext
    exact e.symm_apply_apply q.val
  right_inv a := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      (e.apply_symm_apply (Multiplicative.ofAdd (a : A)))

end AbstractOrbitBridge

section SemidirectCanonicalSubgroups

variable {E : Type u} {K : Type v} [AddCommGroup E] [Group K]
variable (φ : K →* MulAut (Multiplicative E))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem involutionGenerated_semidirect_eq
    (hK : ∀ k : K, IsOfFinOrder k → k = 1) :
    involutionGenerated (Multiplicative E ⋊[φ] K) =
      (twoTorsion E).toSubgroup.map
        (SemidirectProduct.inl : Multiplicative E →*
          Multiplicative E ⋊[φ] K) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    intro x hx
    change x ^ (2 : ℕ) = 1 at hx
    have hfin : IsOfFinOrder x :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hx⟩
    have hright : x.right = 1 := hK x.right
      ((SemidirectProduct.rightHom :
        Multiplicative E ⋊[φ] K →* K).isOfFinOrder hfin)
    have hrepr : x = SemidirectProduct.inl x.left := by
      apply SemidirectProduct.ext
      · rfl
      · simpa only [SemidirectProduct.right_inl] using hright
    have hleft : x.left ^ (2 : ℕ) = 1 := by
      apply SemidirectProduct.inl_injective (φ := φ)
      calc
        SemidirectProduct.inl (x.left ^ (2 : ℕ)) =
            (SemidirectProduct.inl x.left : Multiplicative E ⋊[φ] K) ^
              (2 : ℕ) := map_pow SemidirectProduct.inl x.left 2
        _ = x ^ (2 : ℕ) :=
          congrArg (fun y => y ^ (2 : ℕ)) hrepr.symm
        _ = 1 := hx
        _ = SemidirectProduct.inl 1 :=
          (map_one (SemidirectProduct.inl : Multiplicative E →*
            Multiplicative E ⋊[φ] K)).symm
    have htwo : (2 : ℕ) • Multiplicative.toAdd x.left = 0 := by
      simpa only [toAdd_pow, toAdd_one] using congrArg Multiplicative.toAdd hleft
    refine ⟨x.left, ?_, hrepr.symm⟩
    exact (mem_twoTorsion E _).2 htwo
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    apply Subgroup.subset_closure
    change (SemidirectProduct.inl a : Multiplicative E ⋊[φ] K) ^
      (2 : ℕ) = 1
    rw [← map_pow]
    have ha' : (2 : ℕ) • Multiplicative.toAdd a = 0 :=
      (mem_twoTorsion E _).1 ha
    have hone : a ^ (2 : ℕ) = 1 := by
      apply Multiplicative.toAdd.injective
      simpa only [toAdd_pow, toAdd_one] using ha'
    simp only [hone, map_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem torsionSquareGenerated_semidirect_eq
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (hK : ∀ k : K, IsOfFinOrder k → k = 1) :
    torsionSquareGenerated (Multiplicative E ⋊[φ] K) =
      (doubledSubgroup E).toSubgroup.map
        (SemidirectProduct.inl : Multiplicative E →*
          Multiplicative E ⋊[φ] K) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨z, hz, rfl⟩
    have hright : z.right = 1 := hK z.right
      ((SemidirectProduct.rightHom :
        Multiplicative E ⋊[φ] K →* K).isOfFinOrder hz)
    have hrepr : z = SemidirectProduct.inl z.left := by
      apply SemidirectProduct.ext
      · rfl
      · simpa only [SemidirectProduct.right_inl] using hright
    refine ⟨z.left ^ (2 : ℕ), ?_, ?_⟩
    · change Multiplicative.toAdd (z.left ^ (2 : ℕ)) ∈
        doubledSubgroup E
      apply (mem_doubledSubgroup E _).2
      exact ⟨Multiplicative.toAdd z.left, by simp only [toAdd_pow]⟩
    · calc
        SemidirectProduct.inl (z.left ^ (2 : ℕ)) =
            (SemidirectProduct.inl z.left :
              Multiplicative E ⋊[φ] K) ^ (2 : ℕ) :=
          map_pow SemidirectProduct.inl z.left 2
        _ = z ^ (2 : ℕ) :=
          congrArg (fun x => x ^ (2 : ℕ)) hrepr.symm
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have ha' : Multiplicative.toAdd a ∈ doubledSubgroup E := ha
    obtain ⟨y, hy⟩ := (mem_doubledSubgroup E _).1 ha'
    apply Subgroup.subset_closure
    refine ⟨SemidirectProduct.inl (Multiplicative.ofAdd y), ?_, ?_⟩
    · apply SemidirectProduct.inl.isOfFinOrder
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨4, by decide, ?_⟩
      apply Multiplicative.toAdd.injective
      simpa only [toAdd_pow, toAdd_ofAdd, toAdd_one] using hfour y
    · rw [← map_pow]
      congr 1
      apply Multiplicative.toAdd.injective
      simpa only [toAdd_pow, toAdd_ofAdd] using hy.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def semidirectTwoTorsionInl :
    Multiplicative (twoTorsion E) →*
      (Multiplicative E ⋊[φ] K) :=
  (SemidirectProduct.inl : Multiplicative E →*
    (Multiplicative E ⋊[φ] K)).comp
      (AddMonoidHom.toMultiplicative (twoTorsion E).subtype)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectTwoTorsionInl_injective :
    Function.Injective (semidirectTwoTorsionInl φ) := by
  intro x y h
  apply Multiplicative.ofAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd
    (SemidirectProduct.inl_injective (φ := φ) h)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectTwoTorsionInl_range :
    (semidirectTwoTorsionInl φ).range =
      (twoTorsion E).toSubgroup.map
        (SemidirectProduct.inl : Multiplicative E →*
          (Multiplicative E ⋊[φ] K)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Multiplicative.ofAdd (Multiplicative.toAdd y).val,
      (Multiplicative.toAdd y).property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Multiplicative.ofAdd
      ⟨Multiplicative.toAdd y, hy⟩, rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def semidirectTwoTorsionInclusionEquiv
    (I : Subgroup (Multiplicative E ⋊[φ] K))
    (hI : I = (twoTorsion E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K))) :
    Multiplicative (twoTorsion E) ≃* I :=
  (MonoidHom.ofInjective (semidirectTwoTorsionInl_injective φ)).trans
    (MulEquiv.subgroupCongr
      ((semidirectTwoTorsionInl_range φ).trans hI.symm))



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectTwoTorsionInclusionEquiv_map_doubled
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (I D : Subgroup (Multiplicative E ⋊[φ] K))
    (hI : I = (twoTorsion E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K)))
    (hD : D = (doubledSubgroup E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K))) :
    (doubledWithinTwoTorsion E hfour).toSubgroup.map
      (semidirectTwoTorsionInclusionEquiv φ I hI).toMonoidHom =
        intrinsicDenominator I D := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ((semidirectTwoTorsionInclusionEquiv φ I hI y : I) :
      (Multiplicative E ⋊[φ] K)) ∈ D
    rw [hD]
    refine ⟨Multiplicative.ofAdd
      (Multiplicative.toAdd y).val, ?_, rfl⟩
    exact (mem_doubledWithinTwoTorsion E hfour _).1 hy
  · intro hx
    change ((x : I) : (Multiplicative E ⋊[φ] K)) ∈ D at hx
    rw [hD] at hx
    obtain ⟨z, hz, heq⟩ := hx
    let y : Multiplicative (twoTorsion E) :=
      (semidirectTwoTorsionInclusionEquiv φ I hI).symm x
    refine ⟨y, ?_,
      (semidirectTwoTorsionInclusionEquiv φ I hI).apply_symm_apply x⟩
    change (Multiplicative.toAdd y) ∈
      doubledWithinTwoTorsion E hfour
    apply (mem_doubledWithinTwoTorsion E hfour _).2
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, ?_⟩
    have hzy : Multiplicative.toAdd z =
        (Multiplicative.toAdd y).val := by
      apply Multiplicative.ofAdd.injective
      apply SemidirectProduct.inl_injective (φ := φ)
      calc
        SemidirectProduct.inl z =
            (x : Multiplicative E ⋊[φ] K) := heq
        _ = SemidirectProduct.inl
          (Multiplicative.ofAdd (Multiplicative.toAdd y).val) := by
            have hxy :=
              (semidirectTwoTorsionInclusionEquiv φ I hI).apply_symm_apply x
            exact (congrArg Subtype.val hxy).symm
    exact hw.trans hzy

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def multiplicativeTwoTorsionQuotientEquiv
    (hfour : ∀ x : E, (4 : ℕ) • x = 0) :
    Multiplicative (twoTorsion E) ⧸
      (doubledWithinTwoTorsion E hfour).toSubgroup ≃*
        Multiplicative (twoTorsionQuotient E hfour) := by
  let p : Multiplicative (twoTorsion E) →*
      Multiplicative (twoTorsionQuotient E hfour) :=
    AddMonoidHom.toMultiplicative
      (QuotientAddGroup.mk'
        (doubledWithinTwoTorsion E hfour))
  have hker : p.ker =
      (doubledWithinTwoTorsion E hfour).toSubgroup := by
    change (QuotientAddGroup.mk'
      (doubledWithinTwoTorsion E hfour)).ker.toSubgroup = _
    rw [QuotientAddGroup.ker_mk']
  have hsurj : Function.Surjective p := by
    intro q
    obtain ⟨x, hx⟩ :=
      QuotientAddGroup.mk'_surjective
        (doubledWithinTwoTorsion E hfour)
        (Multiplicative.toAdd q)
    exact ⟨Multiplicative.ofAdd x,
      congrArg Multiplicative.ofAdd hx⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective p hsurj)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def semidirectIntrinsicSubquotientEquiv
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (I D : Subgroup (Multiplicative E ⋊[φ] K)) [D.Normal]
    (hI : I = (twoTorsion E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K)))
    (hD : D = (doubledSubgroup E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K))) :
    intrinsicSubquotient I D ≃*
      Multiplicative (twoTorsionQuotient E hfour) :=
  (QuotientGroup.congr
    (doubledWithinTwoTorsion E hfour).toSubgroup
    (intrinsicDenominator I D)
    (semidirectTwoTorsionInclusionEquiv φ I hI)
    (semidirectTwoTorsionInclusionEquiv_map_doubled
      φ hfour I D hI hD)).symm.trans
        (multiplicativeTwoTorsionQuotientEquiv hfour)

end SemidirectCanonicalSubgroups

end

end

end ConnesRigidity

namespace ConnesRigidity

section

universe u v w z

section SemidirectRepresentative

variable {E : Type u} {K : Type v} [AddCommGroup E] [Group K]
variable (φ : K →* MulAut (Multiplicative E))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem multiplicativeTwoTorsionQuotientEquiv_mk
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (x : Multiplicative (twoTorsion E)) :
    multiplicativeTwoTorsionQuotientEquiv hfour
        (QuotientGroup.mk'
          (doubledWithinTwoTorsion E hfour).toSubgroup x) =
      Multiplicative.ofAdd
        (QuotientAddGroup.mk'
          (doubledWithinTwoTorsion E hfour)
          (Multiplicative.toAdd x)) := by
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectIntrinsicSubquotientEquiv_mk_inclusion
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (I D : Subgroup (Multiplicative E ⋊[φ] K)) [D.Normal]
    (hI : I = (twoTorsion E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K)))
    (hD : D = (doubledSubgroup E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K)))
    (x : Multiplicative (twoTorsion E)) :
    semidirectIntrinsicSubquotientEquiv φ hfour I D hI hD
        (QuotientGroup.mk' (intrinsicDenominator I D)
          (semidirectTwoTorsionInclusionEquiv φ I hI x)) =
      Multiplicative.ofAdd
        (QuotientAddGroup.mk'
          (doubledWithinTwoTorsion E hfour)
          (Multiplicative.toAdd x)) := by
  let quotientEquiv := QuotientGroup.congr
    (doubledWithinTwoTorsion E hfour).toSubgroup
    (intrinsicDenominator I D)
    (semidirectTwoTorsionInclusionEquiv φ I hI)
    (semidirectTwoTorsionInclusionEquiv_map_doubled
      φ hfour I D hI hD)
  change multiplicativeTwoTorsionQuotientEquiv hfour
      (quotientEquiv.symm
        (QuotientGroup.mk' (intrinsicDenominator I D)
          (semidirectTwoTorsionInclusionEquiv φ I hI x))) = _
  have hmk : quotientEquiv
      (QuotientGroup.mk'
        (doubledWithinTwoTorsion E hfour).toSubgroup x) =
      QuotientGroup.mk' (intrinsicDenominator I D)
        (semidirectTwoTorsionInclusionEquiv φ I hI x) := rfl
  rw [← hmk, quotientEquiv.symm_apply_apply]
  exact multiplicativeTwoTorsionQuotientEquiv_mk hfour x

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectIntrinsicSubquotientEquiv_conjugation
    [DistribMulAction K E]
    (hact : ∀ (k : K) (x : E),
      k • x = Multiplicative.toAdd (φ k (Multiplicative.ofAdd x)))
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (I D : Subgroup (Multiplicative E ⋊[φ] K)) [I.Normal] [D.Normal]
    (hI : I = (twoTorsion E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K)))
    (hD : D = (doubledSubgroup E).toSubgroup.map
      (SemidirectProduct.inl : Multiplicative E →*
        (Multiplicative E ⋊[φ] K)))
    (g : Multiplicative E ⋊[φ] K)
    (q : intrinsicSubquotient I D) :
    Multiplicative.toAdd
        (semidirectIntrinsicSubquotientEquiv φ hfour I D hI hD
          (intrinsicConjugationAction I D g q)) =
      g.right • Multiplicative.toAdd
        (semidirectIntrinsicSubquotientEquiv φ hfour I D hI hD q) := by
  induction q using QuotientGroup.induction_on with
  | _ x =>
    obtain ⟨y, rfl⟩ :=
      (semidirectTwoTorsionInclusionEquiv φ I hI).surjective x
    let y' : Multiplicative (twoTorsion E) :=
      Multiplicative.ofAdd (g.right • Multiplicative.toAdd y)
    have hconj : MulAut.conjNormal g
        (semidirectTwoTorsionInclusionEquiv φ I hI y) =
          semidirectTwoTorsionInclusionEquiv φ I hI y' := by
      apply Subtype.ext
      change g * SemidirectProduct.inl
          (Multiplicative.ofAdd (Multiplicative.toAdd y).val) * g⁻¹ =
        SemidirectProduct.inl (Multiplicative.ofAdd
          (Multiplicative.toAdd y').val)
      change g * SemidirectProduct.inl
          (Multiplicative.ofAdd (Multiplicative.toAdd y).val) * g⁻¹ =
        SemidirectProduct.inl
          (Multiplicative.ofAdd (g.right •
            (Multiplicative.toAdd y).val))
      rw [hact]
      change g * SemidirectProduct.inl
          (Multiplicative.ofAdd (Multiplicative.toAdd y).val) * g⁻¹ =
        SemidirectProduct.inl
          (φ g.right
            (Multiplicative.ofAdd (Multiplicative.toAdd y).val))
      apply SemidirectProduct.ext
      · simp only [mul_assoc, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
          SemidirectProduct.right_inl, map_one, SemidirectProduct.inv_left, map_inv,
          MulAut.inv_apply, MulAut.one_apply, mul_comm, map_mul, MulEquiv.apply_symm_apply,
          mul_inv_cancel_left]
      · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one,
          SemidirectProduct.inv_right, mul_inv_cancel]
    change Multiplicative.toAdd
        (semidirectIntrinsicSubquotientEquiv φ hfour I D hI hD
          (QuotientGroup.mk' (intrinsicDenominator I D)
            (MulAut.conjNormal g
              (semidirectTwoTorsionInclusionEquiv φ I hI y)))) = _
    rw [hconj]
    change Multiplicative.toAdd
        (semidirectIntrinsicSubquotientEquiv φ hfour I D hI hD
          (QuotientGroup.mk' (intrinsicDenominator I D)
            (semidirectTwoTorsionInclusionEquiv φ I hI y'))) =
      g.right • Multiplicative.toAdd
        (semidirectIntrinsicSubquotientEquiv φ hfour I D hI hD
          (QuotientGroup.mk' (intrinsicDenominator I D)
            (semidirectTwoTorsionInclusionEquiv φ I hI y)))
    rw [semidirectIntrinsicSubquotientEquiv_mk_inclusion,
      semidirectIntrinsicSubquotientEquiv_mk_inclusion]
    change QuotientAddGroup.mk' (doubledWithinTwoTorsion E hfour)
        (g.right • Multiplicative.toAdd y) =
      g.right • QuotientAddGroup.mk'
        (doubledWithinTwoTorsion E hfour)
        (Multiplicative.toAdd y)
    exact (twoTorsionQuotient_smul_mk K E hfour g.right
      (Multiplicative.toAdd y)).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def semidirectCanonicalFiniteOrbitEquiv
    [DistribMulAction K E]
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (hK : ∀ k : K, IsOfFinOrder k → k = 1)
    (hact : ∀ (k : K) (x : E),
      k • x = Multiplicative.toAdd (φ k (Multiplicative.ofAdd x))) :
    IntrinsicFiniteOrbitCarrier
      (involutionGenerated (Multiplicative E ⋊[φ] K))
      (torsionSquareGenerated (Multiplicative E ⋊[φ] K)) ≃
        finiteOrbitSubgroup K (twoTorsionQuotient E hfour) := by
  let I := involutionGenerated (Multiplicative E ⋊[φ] K)
  let D := torsionSquareGenerated (Multiplicative E ⋊[φ] K)
  let hI := involutionGenerated_semidirect_eq φ hK
  let hD := torsionSquareGenerated_semidirect_eq φ hfour hK
  let q := semidirectIntrinsicSubquotientEquiv φ hfour I D hI hD
  refine intrinsicFiniteOrbitCarrierEquivFiniteOrbitSubgroup
    (SemidirectProduct.rightHom :
      (Multiplicative E ⋊[φ] K) →* K)
    (fun k => ⟨SemidirectProduct.inr k, rfl⟩) q ?_
  exact semidirectIntrinsicSubquotientEquiv_conjugation
    φ hact hfour I D hI hD

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperInvariant_semidirect_carrier_equiv
    [DistribMulAction K E]
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (hK : ∀ k : K, IsOfFinOrder k → k = 1)
    (hact : ∀ (k : K) (x : E),
      k • x = Multiplicative.toAdd (φ k (Multiplicative.ofAdd x)))
    (G : ConnesRigidity.CountableDiscreteGroup.{max u v})
    (eG : G ≃* (Multiplicative E ⋊[φ] K)) :
    paperGroupCardinalInvariant.carrier G ≃
      finiteOrbitSubgroup K (twoTorsionQuotient E hfour) :=
  (intrinsicFiniteOrbitEquiv eG
    (mulEquiv_map_involutionGenerated eG)
    (mulEquiv_map_torsionSquareGenerated eG)).trans
      (semidirectCanonicalFiniteOrbitEquiv φ hfour hK hact)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperInvariant_semidirect_value_eq
    [DistribMulAction K E]
    (hfour : ∀ x : E, (4 : ℕ) • x = 0)
    (hK : ∀ k : K, IsOfFinOrder k → k = 1)
    (hact : ∀ (k : K) (x : E),
      k • x = Multiplicative.toAdd (φ k (Multiplicative.ofAdd x)))
    (G : ConnesRigidity.CountableDiscreteGroup.{max u v})
    (eG : G ≃* (Multiplicative E ⋊[φ] K)) :
    paperGroupCardinalInvariant.value G =
      Nat.card (finiteOrbitSubgroup K
        (twoTorsionQuotient E hfour)) :=
  Nat.card_congr
    (paperInvariant_semidirect_carrier_equiv
      φ hfour hK hact G eG)

end SemidirectRepresentative

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal NNReal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev gammaInl (n : ℕ) : Multiplicative (E n) →* Gamma n :=
  SemidirectProduct.inl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev gammaInr (n : ℕ) : K →* Gamma n :=
  SemidirectProduct.inr

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev gammaProjection (n : ℕ) : Gamma n →* K :=
  SemidirectProduct.rightHom

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gammaSplitAbelianExtension (n : ℕ) :
    SplitAbelianExtension (E n) (gammaGroup n) actingGroup where
  inclusion := gammaInl n
  quotient := gammaProjection n
  splitting := gammaInr n
  quotient_splitting := SemidirectProduct.rightHom_comp_inr
  exact := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  action := (MulAutMultiplicative (E n)).toMonoidHom.comp (kEAction n)
  conjugation k η := by
    let k' : K := k
    change (SemidirectProduct.inr (φ := kEAction n) k' : Gamma n) *
      (SemidirectProduct.inl (φ := kEAction n)
        (Multiplicative.ofAdd η) : Gamma n) *
        (SemidirectProduct.inr (φ := kEAction n) k' : Gamma n)⁻¹ =
      (SemidirectProduct.inl (φ := kEAction n)
        ((kEAction n k') (Multiplicative.ofAdd η)) : Gamma n)
    have hinv :
        (SemidirectProduct.inr (φ := kEAction n) k' : Gamma n)⁻¹ =
          SemidirectProduct.inr (φ := kEAction n) k'⁻¹ := by
      exact (map_inv (SemidirectProduct.inr
        (N := Multiplicative (E n)) (G := K) (φ := kEAction n)) k').symm
    rw [hinv]
    exact (SemidirectProduct.inl_aut (φ := kEAction n) k'
      (Multiplicative.ofAdd η)).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_detectors_ne (n : ℕ) :
    (iota n e) ≠ (epsilon n e) := by
  intro h
  have htwo : (2 : ℕ) • (iota n e) = 0 := by
    calc
      (2 : ℕ) • iota n e = iota n (e + e) := by
        simp only [two_nsmul, map_add]
      _ = 0 := by rw [add_self_eq_zero]; exact map_zero _
  have hquadratic : (2 : ℕ) • epsilon n e = 0 := by
    rw [← h]
    exact htwo
  exact epsilon_two_nsmul_ne_zero n hquadratic

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaDualMeasurable (n : ℕ) :
    MeasurableSpace (DiscreteCharacterSpace (E n)) :=
  borel (DiscreteCharacterSpace (E n))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaDualBorel (n : ℕ) :
    BorelSpace (DiscreteCharacterSpace (E n)) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaKernelDecidableEq (n : ℕ) : DecidableEq (E n) :=
  Classical.decEq _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaCircleMeasurable : MeasurableSpace Circle := borel Circle

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaCircleBorel : BorelSpace Circle := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gammaDetectionSet (n : ℕ) (η : E n) :
    Set (DiscreteCharacterSpace (E n)) :=
  {χ | χ (Multiplicative.ofAdd η) ≠ 1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaDetectionSet_measurable (n : ℕ) (η : E n) :
    MeasurableSet (gammaDetectionSet n η) := by
  unfold gammaDetectionSet
  have hcontinuous : Continuous
      (fun χ : DiscreteCharacterSpace (E n) ↦
        χ (Multiplicative.ofAdd η)) := by
    change Continuous
      (fun χ : ((Multiplicative (E n)) →ₜ* Circle) ↦
        χ (Multiplicative.ofAdd η))
    exact continuous_eval_const _
  exact (hcontinuous.measurable (measurableSet_singleton (1 : Circle))).compl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaCharacter_pow_four (n : ℕ)
    (χ : DiscreteCharacterSpace (E n)) (η : E n) :
    χ (Multiplicative.ofAdd η) ^ 4 = 1 := by
  rw [← map_pow]
  have hη : (Multiplicative.ofAdd η) ^ (4 : ℕ) =
      (1 : Multiplicative (E n)) := by
    apply Multiplicative.toAdd.injective
    simpa only [toAdd_pow, toAdd_ofAdd, toAdd_one] using E_four_nsmul n η
  rw [hη, map_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaFourthRootEnergy_lower_bound (z : Circle) (hz : z ^ 4 = 1)
    (hne : z ≠ 1) : (2 : ℝ) ≤ ‖(z : ℂ) - 1‖ ^ 2 := by
  have hz' : (z : ℂ) ^ 4 = 1 := congrArg (fun w : Circle => (w : ℂ)) hz
  have hsq : ((z : ℂ) ^ 2) ^ 2 = 1 := by
    simpa only [← pow_mul, Nat.reduceMul] using hz'
  rcases sq_eq_one_iff.mp hsq with hplus | hminus
  · have hne' : (z : ℂ) ≠ 1 := by
      intro h
      apply hne
      exact Subtype.ext h
    have hneg : (z : ℂ) = -1 :=
      (sq_eq_one_iff.mp hplus).resolve_left hne'
    rw [hneg]
    norm_num
  · have hnorm : Complex.normSq (z : ℂ) = 1 := by
      exact Circle.normSq_coe z
    have hre : (z : ℂ).re = 0 := by
      have hreal := congrArg Complex.re hminus
      simp only [pow_two, Complex.mul_re, Complex.neg_re,
        Complex.one_re] at hreal
      rw [Complex.normSq_apply] at hnorm
      nlinarith [sq_nonneg (z : ℂ).re]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, hre, Complex.one_re, zero_sub, mul_neg, mul_one, neg_neg,
      Complex.sub_im, Complex.one_im, sub_zero, ge_iff_le]
    rw [Complex.normSq_apply] at hnorm
    nlinarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaCharacterEnergy_indicator_le (n : ℕ)
    (χ : DiscreteCharacterSpace (E n)) (η : E n) :
    (gammaDetectionSet n η).indicator (fun _ ↦ (2 : ℝ)) χ ≤
      ‖((χ (Multiplicative.ofAdd η) : Circle) : ℂ) - 1‖ ^ 2 := by
  by_cases h : χ (Multiplicative.ofAdd η) = 1
  · simp only [gammaDetectionSet, ne_eq, Set.mem_ofPred_eq, h, not_true_eq_false, not_false_eq_true,
      Set.indicator_of_notMem, Circle.coe_one, sub_self, norm_zero, OfNat.ofNat_ne_zero, zero_pow,
      Std.le_refl]
  · simpa only [gammaDetectionSet, ne_eq, Set.mem_ofPred_eq, h, not_false_eq_true,
      Set.indicator_of_mem] using
      gammaFourthRootEnergy_lower_bound (χ (Multiplicative.ofAdd η))
        (gammaCharacter_pow_four n χ η) h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaCharacterEnergy_integrable (n : ℕ)
    (μ : ProbabilityMeasure (DiscreteCharacterSpace (E n))) (η : E n) :
    Integrable
      (fun χ : DiscreteCharacterSpace (E n) ↦
        ‖((χ (Multiplicative.ofAdd η) : Circle) : ℂ) - 1‖ ^ 2)
      (μ : Measure (DiscreteCharacterSpace (E n))) := by
  have heval : Continuous
      (fun χ : DiscreteCharacterSpace (E n) ↦
        χ (Multiplicative.ofAdd η)) := by
    change Continuous
      (fun χ : ((Multiplicative (E n)) →ₜ* Circle) ↦
        χ (Multiplicative.ofAdd η))
    exact continuous_eval_const _
  have hcomplex : Continuous
      (fun χ : DiscreteCharacterSpace (E n) ↦
        ((χ (Multiplicative.ofAdd η) : Circle) : ℂ)) :=
    continuous_subtype_val.comp heval
  have hcont : Continuous
      (fun χ : DiscreteCharacterSpace (E n) ↦
        ‖((χ (Multiplicative.ofAdd η) : Circle) : ℂ) - 1‖ ^ 2) :=
    ((hcomplex.sub (continuous_const : Continuous
      (fun _ : DiscreteCharacterSpace (E n) ↦ (1 : ℂ)))).norm).pow 2
  simpa only [integrableOn_univ] using hcont.continuousOn.integrableOn_compact
    (μ := (μ : Measure (DiscreteCharacterSpace (E n)))) isCompact_univ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaTwoMulDetectedMass_le_energy (n : ℕ)
    (μ : ProbabilityMeasure (DiscreteCharacterSpace (E n))) (η : E n) :
    2 * (μ : Measure (DiscreteCharacterSpace (E n))).real
      (gammaDetectionSet n η) ≤ spectralDetectionEnergy μ η := by
  let μ' : Measure (DiscreteCharacterSpace (E n)) := μ
  let S := gammaDetectionSet n η
  have hs : MeasurableSet S := gammaDetectionSet_measurable n η
  have hindicator : Integrable (S.indicator (fun _ ↦ (2 : ℝ))) μ' :=
    (integrable_const (μ := μ') (2 : ℝ)).indicator hs
  have henergy : Integrable
      (fun χ : DiscreteCharacterSpace (E n) ↦
        ‖((χ (Multiplicative.ofAdd η) : Circle) : ℂ) - 1‖ ^ 2) μ' :=
    gammaCharacterEnergy_integrable n μ η
  calc
    2 * (μ : Measure (DiscreteCharacterSpace (E n))).real
        (gammaDetectionSet n η) =
      ∫ χ, S.indicator (fun _ ↦ (2 : ℝ)) χ ∂μ' := by
        rw [integral_indicator_const _ hs]
        simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn, smul_eq_mul, mul_comm, μ', S]
    _ ≤ ∫ χ : DiscreteCharacterSpace (E n),
          ‖((χ (Multiplicative.ofAdd η) : Circle) : ℂ) - 1‖ ^ 2 ∂μ' := by
      exact integral_mono hindicator henergy
        (fun χ => gammaCharacterEnergy_indicator_le n χ η)
    _ = spectralDetectionEnergy μ η := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gammaDetectedSet (n : ℕ) : Set (DiscreteCharacterSpace (E n)) :=
  gammaDetectionSet n ((iota n e)) ∪
    gammaDetectionSet n ((epsilon n e))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaTwoMulDetectedUnionMass_le_energy (n : ℕ)
    (μ : ProbabilityMeasure (DiscreteCharacterSpace (E n))) :
    2 * (μ : Measure (DiscreteCharacterSpace (E n))).real
      (gammaDetectedSet n) ≤
      spectralDetectionEnergy μ ((iota n e)) +
        spectralDetectionEnergy μ ((epsilon n e)) := by
  have hlinear := gammaTwoMulDetectedMass_le_energy n μ
    ((iota n e))
  have hquadratic := gammaTwoMulDetectedMass_le_energy n μ
    ((epsilon n e))
  have hunion := measureReal_union_le
    (μ := (μ : Measure (DiscreteCharacterSpace (E n))))
    (gammaDetectionSet n ((iota n e)))
    (gammaDetectionSet n ((epsilon n e)))
  change (μ : Measure (DiscreteCharacterSpace (E n))).real
    (gammaDetectedSet n) ≤ _ at hunion
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_hasFiniteSpectralDetection_of_measureGap (n : ℕ)
    (hgap : ∀ μ : ProbabilityMeasure (DiscreteCharacterSpace (E n)),
      IsInvariantSpectralMeasure (gammaSplitAbelianExtension n).action μ →
        (1 / 7 : ℝ) * (1 - spectralTrivialAtom μ) ≤
          (μ : Measure (DiscreteCharacterSpace (E n))).real
            (gammaDetectedSet n)) :
    HasFiniteSpectralDetection (gammaSplitAbelianExtension n)
      {(iota n e), (epsilon n e)} (2 / 7 : ℝ) := by
  intro μ hμ
  have hmass := hgap μ hμ
  have henergy := gammaTwoMulDetectedUnionMass_le_energy n μ
  have hcombined : (2 / 7 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      spectralDetectionEnergy μ ((iota n e)) +
        spectralDetectionEnergy μ ((epsilon n e)) := by
    linarith
  simpa only [Finset.mem_singleton, gamma_detectors_ne n, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, ge_iff_le] using hcombined

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev BinaryBoundedPolynomial (N : ℕ) := Polynomial.degreeLT (ZMod 2) N

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev BinaryPolynomialVector (N : ℕ) := Fin 4 → BinaryBoundedPolynomial N

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev BinaryMonicPolynomial (N : ℕ) :=
  {p : Polynomial (ZMod 2) // p.Monic ∧ p.natDegree = N}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def boundedPolynomialEquiv (N : ℕ) :
    BinaryBoundedPolynomial N ≃ (Fin N → ZMod 2) :=
  (Polynomial.degreeLTEquiv (ZMod 2) N).toEquiv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable instance boundedPolynomialFintype (N : ℕ) :
    Fintype (BinaryBoundedPolynomial N) :=
  Fintype.ofEquiv (Fin N → ZMod 2) (boundedPolynomialEquiv N).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem card_boundedPolynomial (N : ℕ) :
    Fintype.card (BinaryBoundedPolynomial N) = 2 ^ N := by
  rw [Fintype.card_congr (boundedPolynomialEquiv N), Fintype.card_fun,
    Fintype.card_fin, ZMod.card]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def monicPolynomialEquiv (N : ℕ) :
    BinaryMonicPolynomial N ≃ BinaryBoundedPolynomial N :=
  Polynomial.monicEquivDegreeLT N

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable instance monicPolynomialFintype (N : ℕ) :
    Fintype (BinaryMonicPolynomial N) :=
  Fintype.ofEquiv (BinaryBoundedPolynomial N) (monicPolynomialEquiv N).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem card_monicPolynomial (N : ℕ) :
    Fintype.card (BinaryMonicPolynomial N) = 2 ^ N := by
  rw [Fintype.card_congr (monicPolynomialEquiv N), card_boundedPolynomial]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem card_binaryPolynomialVector (N : ℕ) :
    Fintype.card (BinaryPolynomialVector N) = 2 ^ (4 * N) := by
  rw [Fintype.card_fun, Fintype.card_fin, card_boundedPolynomial]
  simp only [Nat.mul_comm, pow_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem eight_mul_countingScale (N : ℕ) (hN : 0 < N) :
    8 * (2 ^ (4 * N - 3)) = 2 ^ (4 * N) := by
  have hexp : 4 * N - 3 + 3 = 4 * N := by omega
  calc
    8 * 2 ^ (4 * N - 3) = 2 ^ (4 * N - 3) * 2 ^ 3 := by
      simp only [Nat.mul_comm, Nat.reducePow]
    _ = 2 ^ (4 * N - 3 + 3) := by rw [pow_add]
    _ = 2 ^ (4 * N) := by rw [hexp]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem two_mul_previous_box (N : ℕ) (hN : 0 < N) :
    2 * 2 ^ (4 * (N - 1)) = (2 ^ (4 * N - 3)) := by
  have hexp : 4 * (N - 1) + 1 = 4 * N - 3 := by omega
  calc
    2 * 2 ^ (4 * (N - 1)) = 2 ^ (4 * (N - 1)) * 2 ^ 1 := by
      simp only [Nat.mul_comm, pow_one]
    _ = 2 ^ (4 * (N - 1) + 1) := by rw [pow_add]
    _ = 2 ^ (4 * N - 3) := by rw [hexp]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def primitiveCount (N : ℕ) : ℕ :=
  if N = 0 then 0 else 7 * (2 ^ (4 * N - 3)) + 1



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitiveCount_eq (N : ℕ) (hN : 0 < N) :
    primitiveCount N = 7 * 2 ^ (4 * N - 3) + 1 := by
  simp only [primitiveCount, Nat.ne_of_gt hN, ↓reduceIte]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitiveCount_subtraction (N : ℕ) (hN : 0 < N) :
    (2 ^ (4 * N) - 1) - 2 * (2 ^ (4 * (N - 1)) - 1) =
      primitiveCount N := by
  have hscale := eight_mul_countingScale N hN
  have hprevious := two_mul_previous_box N hN
  have hpositive : 0 < 2 ^ (4 * (N - 1)) := pow_pos (by omega) _
  rw [primitiveCount_eq N hN]
  change (2 ^ (4 * N) - 1) - 2 * (2 ^ (4 * (N - 1)) - 1) =
    7 * (2 ^ (4 * N - 3)) + 1
  omega

end

section

open scoped BigOperators

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def vectorGCD (v : V) : R :=
  (Finset.univ : Finset (Fin 4)).gcd v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def IsPrimitiveVector (v : V) : Prop :=
  vectorGCD v = 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def coordinateIdeal (v : V) : Ideal R :=
  Ideal.span (Set.range v)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev PrimitivePolynomialVector (N : ℕ) :=
  {v : BinaryPolynomialVector N // IsPrimitiveVector (fun i ↦ (v i : R))}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def polynomialVectorVal {N : ℕ} (v : BinaryPolynomialVector N) : V :=
  fun i ↦ (v i : R)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem polynomialVectorVal_eq_zero_iff {N : ℕ}
    (v : BinaryPolynomialVector N) :
    polynomialVectorVal v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    apply Subtype.ext
    exact congrFun h i
  · rintro rfl
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev NonzeroPolynomialVector (N : ℕ) :=
  {v : BinaryPolynomialVector N // v ≠ 0}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable instance primitivePolynomialVectorFintype (N : ℕ) :
    Fintype (PrimitivePolynomialVector N) := by
  classical
  exact Fintype.ofFinite _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem vectorGCD_dvd (v : V) (i : Fin 4) :
    vectorGCD v ∣ v i := by
  exact Finset.gcd_dvd (Finset.mem_univ i)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem coordinateIdeal_eq_span_vectorGCD (v : V) :
    coordinateIdeal v = Ideal.span ({vectorGCD v} : Set R) := by
  apply le_antisymm
  · rw [coordinateIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.mpr (vectorGCD_dvd v i)
  · rw [Ideal.span_le]
    intro x hx
    have hx' : x = vectorGCD v := Set.mem_singleton_iff.mp hx
    subst x
    obtain ⟨g, hg⟩ :=
      Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin 4)) v
    change vectorGCD v ∈ coordinateIdeal v
    rw [vectorGCD, hg]
    exact (coordinateIdeal v).sum_mem
      (fun i _ ↦ Ideal.mul_mem_right _ _
        (show v i ∈ coordinateIdeal v from
          Ideal.mem_span_range_self))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem isPrimitiveVector_iff_coordinateIdeal_eq_top (v : V) :
    IsPrimitiveVector v ↔ coordinateIdeal v = ⊤ := by
  change vectorGCD v = 1 ↔ coordinateIdeal v = ⊤
  rw [coordinateIdeal_eq_span_vectorGCD,
    Ideal.span_singleton_eq_top, ← normalize_eq_one,
    show normalize (vectorGCD v) = vectorGCD v from Finset.normalize_gcd]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem vectorGCD_eq_zero_iff (v : V) :
    vectorGCD v = 0 ↔ v = 0 := by
  rw [vectorGCD, Finset.gcd_eq_zero_iff]
  simp only [Finset.mem_univ, forall_const, funext_iff, Pi.zero_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem vectorGCD_ne_zero {v : V} (hv : v ≠ 0) :
    vectorGCD v ≠ 0 := by
  simpa only [ne_eq, vectorGCD_eq_zero_iff] using hv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem vectorGCD_monic {v : V} (hv : v ≠ 0) :
    (vectorGCD v).Monic := by
  have hnormalized : normalize (vectorGCD v) = vectorGCD v := by
    exact Finset.normalize_gcd
  rw [← hnormalized]
  exact Polynomial.monic_normalize (vectorGCD_ne_zero hv)

private theorem IsPrimitiveVector.ne_zero {v : V} (hv : IsPrimitiveVector v) :
    v ≠ 0 := by
  intro hzero
  have hgzero : vectorGCD v = 0 :=
    (vectorGCD_eq_zero_iff v).mpr hzero
  exact zero_ne_one (hgzero.symm.trans hv)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem vectorGCD_mul (g : R) (hg : g.Monic) (v : V) :
    vectorGCD (fun i ↦ g * v i) = g * vectorGCD v := by
  unfold vectorGCD
  rw [Finset.gcd_mul_left, hg.normalize_eq_self]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem vectorGCD_div_eq_one {v : V} (hv : v ≠ 0) :
    vectorGCD (fun i ↦ v i / vectorGCD v) = 1 := by
  obtain ⟨i, _, hi⟩ := Finset.gcd_ne_zero_iff.mp (vectorGCD_ne_zero hv)
  change Finset.univ.gcd (fun i ↦ v i / Finset.univ.gcd v) = 1
  exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem bounded_natDegree_lt {N : ℕ}
    (p : BinaryBoundedPolynomial N) (hp : (p : R) ≠ 0) :
    (p : R).natDegree < N := by
  apply (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
  exact Polynomial.mem_degreeLT.mp p.property

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_degreeLT_of_natDegree_lt {N : ℕ} (p : R)
    (hp : p = 0 ∨ p.natDegree < N) :
    p ∈ Polynomial.degreeLT F N := by
  rcases hp with rfl | hp
  · exact (Polynomial.degreeLT F N).zero_mem
  · apply Polynomial.mem_degreeLT.mpr
    by_cases hpzero : p = 0
    · simp only [hpzero, Polynomial.degree_zero, WithBot.bot_lt_natCast]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hpzero).mp hp





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem card_eq_sum_card_fibers {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (f : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} := by
  classical
  calc
    Fintype.card α = Fintype.card (Σ b : β, {a : α // f a = b}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : β, Fintype.card {a : α // f a = b} := Fintype.card_sigma

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem card_eq_sum_card_products {α β : Type*} [Fintype α] [Fintype β]
    (G P : β → Type*) [∀ b, Fintype (G b)] [∀ b, Fintype (P b)]
    (f : α → β) (e : ∀ b, {a : α // f a = b} ≃ G b × P b) :
    Fintype.card α = ∑ b : β, Fintype.card (G b) * Fintype.card (P b) := by
  classical
  calc
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} :=
      card_eq_sum_card_fibers f
    _ = ∑ b : β, Fintype.card (G b) * Fintype.card (P b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Fintype.card_congr (e b), Fintype.card_prod]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem card_nonzeroPolynomialVector (N : ℕ) :
    Fintype.card (NonzeroPolynomialVector N) = 2 ^ (4 * N) - 1 := by
  classical
  rw [show Fintype.card (NonzeroPolynomialVector N) =
      Fintype.card (BinaryPolynomialVector N) -
        Fintype.card {v : BinaryPolynomialVector N // v = 0} from
      Fintype.card_subtype_compl (fun v : BinaryPolynomialVector N ↦ v = 0)]
  rw [Fintype.card_subtype_eq, card_binaryPolynomialVector]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem vectorGCD_natDegree_lt {N : ℕ}
    (v : NonzeroPolynomialVector N) :
    (vectorGCD (polynomialVectorVal v.val)).natDegree < N := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, v.val i ≠ 0 := by
    by_contra h
    apply v.property
    apply funext
    intro i
    exact not_ne_iff.mp (not_exists.mp h i)
  have hi' : (v.val i : R) ≠ 0 := by
    intro hzero
    apply hi
    apply Subtype.ext
    simpa only [ne_eq, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] using hzero
  exact lt_of_le_of_lt
    (Polynomial.natDegree_le_of_dvd (vectorGCD_dvd _ i) hi')
    (bounded_natDegree_lt (v.val i) hi')

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gcdDegreeMap (N : ℕ) : NonzeroPolynomialVector N → Fin N :=
  fun v ↦ ⟨(vectorGCD (polynomialVectorVal v.val)).natDegree,
    vectorGCD_natDegree_lt v⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem nonzeroVector_coe_ne_zero {N : ℕ}
    (v : NonzeroPolynomialVector N) :
    polynomialVectorVal v.val ≠ 0 := by
  exact fun hzero ↦ v.property
    ((polynomialVectorVal_eq_zero_iff v.val).mp hzero)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotient_isPrimitive {N : ℕ}
    (v : NonzeroPolynomialVector N) :
    IsPrimitiveVector
      (fun i ↦ (v.val i : R) /
        vectorGCD (polynomialVectorVal v.val)) := by
  exact vectorGCD_div_eq_one (nonzeroVector_coe_ne_zero v)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem quotient_mem_degreeLT {N : ℕ} {d : Fin N}
    (v : {v : NonzeroPolynomialVector N // gcdDegreeMap N v = d})
    (i : Fin 4) :
    (v.val.val i : R) / vectorGCD (polynomialVectorVal v.val.val) ∈
      Polynomial.degreeLT F (N - d.val) := by
  let p : R := v.val.val i
  let g : R := vectorGCD (polynomialVectorVal v.val.val)
  have hg : g.Monic := vectorGCD_monic (nonzeroVector_coe_ne_zero v.val)
  have hd : g.natDegree = d.val := congrArg Fin.val v.property
  apply mem_degreeLT_of_natDegree_lt
  by_cases hq : p / g = 0
  · exact Or.inl hq
  · right
    have hp : p ≠ 0 := by
      intro hzero
      simp only [hzero, EuclideanDomain.zero_div, not_true_eq_false] at hq
    have hpbound : p.natDegree < N := bounded_natDegree_lt (v.val.val i) hp
    have hg_le : g.natDegree ≤ p.natDegree :=
      Polynomial.natDegree_le_of_dvd (vectorGCD_dvd _ i) hp
    have hdegree : (p / g).natDegree = p.natDegree - g.natDegree := by
      rw [← Polynomial.divByMonic_eq_div p hg,
        Polynomial.natDegree_divByMonic p hg]
    rw [hdegree, hd]
    omega

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def fiberFactor {N : ℕ} {d : Fin N}
    (v : {v : NonzeroPolynomialVector N // gcdDegreeMap N v = d}) :
    BinaryMonicPolynomial d.val :=
  ⟨vectorGCD (polynomialVectorVal v.val.val),
    vectorGCD_monic (nonzeroVector_coe_ne_zero v.val),
    congrArg Fin.val v.property⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def fiberPrimitive {N : ℕ} {d : Fin N}
    (v : {v : NonzeroPolynomialVector N // gcdDegreeMap N v = d}) :
    PrimitivePolynomialVector (N - d.val) :=
  ⟨fun i ↦ ⟨(v.val.val i : R) /
    vectorGCD (polynomialVectorVal v.val.val), quotient_mem_degreeLT v i⟩,
   quotient_isPrimitive v.val⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def fiberToProduct {N : ℕ} {d : Fin N}
    (v : {v : NonzeroPolynomialVector N // gcdDegreeMap N v = d}) :
    BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val) :=
  ⟨fiberFactor v, fiberPrimitive v⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem product_mem_degreeLT {N : ℕ} (d : Fin N)
    (x : BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val))
    (i : Fin 4) :
    x.1.val * (x.2.val i : R) ∈ Polynomial.degreeLT F N := by
  apply mem_degreeLT_of_natDegree_lt
  by_cases hw : (x.2.val i : R) = 0
  · exact Or.inl (by simp only [hw, mul_zero])
  · right
    have hwbound := bounded_natDegree_lt (x.2.val i) hw
    have hdegree := x.1.property.1.natDegree_mul' hw
    rw [hdegree, x.1.property.2]
    omega

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def productVector {N : ℕ} (d : Fin N)
    (x : BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val)) :
    BinaryPolynomialVector N :=
  fun i ↦ ⟨x.1.val * (x.2.val i : R), product_mem_degreeLT d x i⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem productVector_gcd {N : ℕ} (d : Fin N)
    (x : BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val)) :
    vectorGCD (polynomialVectorVal (productVector d x)) = x.1.val := by
  change vectorGCD (fun i ↦ x.1.val * (x.2.val i : R)) = x.1.val
  rw [vectorGCD_mul x.1.val x.1.property.1, x.2.property, mul_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem productVector_ne_zero {N : ℕ} (d : Fin N)
    (x : BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val)) :
    productVector d x ≠ 0 := by
  intro hzero
  have hraw : polynomialVectorVal (productVector d x) = 0 := by
    rw [hzero]
    rfl
  have hgzero : vectorGCD (polynomialVectorVal (productVector d x)) = 0 := by
    rw [hraw]
    exact (vectorGCD_eq_zero_iff _).mpr rfl
  rw [productVector_gcd d x] at hgzero
  exact x.1.property.1.ne_zero hgzero

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def productToNonzero {N : ℕ} (d : Fin N)
    (x : BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val)) :
    NonzeroPolynomialVector N :=
  ⟨productVector d x, productVector_ne_zero d x⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem productToNonzero_gcdDegree {N : ℕ} (d : Fin N)
    (x : BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val)) :
    gcdDegreeMap N (productToNonzero d x) = d := by
  apply Fin.ext
  change (vectorGCD (polynomialVectorVal (productVector d x))).natDegree = d.val
  rw [productVector_gcd d x, x.1.property.2]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def productToFiber {N : ℕ} (d : Fin N)
    (x : BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val)) :
    {v : NonzeroPolynomialVector N // gcdDegreeMap N v = d} :=
  ⟨productToNonzero d x, productToNonzero_gcdDegree d x⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem productToFiber_fiberToProduct {N : ℕ} {d : Fin N}
    (v : {v : NonzeroPolynomialVector N // gcdDegreeMap N v = d}) :
    productToFiber d (fiberToProduct v) = v := by
  apply Subtype.ext
  apply Subtype.ext
  apply funext
  intro i
  apply Subtype.ext
  change
    vectorGCD (polynomialVectorVal v.val.val) *
      ((v.val.val i : R) / vectorGCD (polynomialVectorVal v.val.val)) =
        (v.val.val i : R)
  exact EuclideanDomain.mul_div_cancel'
    (vectorGCD_monic (nonzeroVector_coe_ne_zero v.val)).ne_zero
    (vectorGCD_dvd _ i)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem fiberToProduct_productToFiber {N : ℕ} (d : Fin N)
    (x : BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val)) :
    fiberToProduct (productToFiber d x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    exact productVector_gcd d x
  · apply Subtype.ext
    apply funext
    intro i
    apply Subtype.ext
    change
      (x.1.val * (x.2.val i : R)) /
        vectorGCD (polynomialVectorVal (productVector d x)) = (x.2.val i : R)
    rw [productVector_gcd d x,
      ← Polynomial.divByMonic_eq_div _ x.1.property.1]
    exact Polynomial.mul_divByMonic_cancel_left _ x.1.property.1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def gcdDegreeFiberEquiv {N : ℕ} (d : Fin N) :
    {v : NonzeroPolynomialVector N // gcdDegreeMap N v = d} ≃
      BinaryMonicPolynomial d.val × PrimitivePolynomialVector (N - d.val) where
  toFun := fiberToProduct
  invFun := productToFiber d
  left_inv := productToFiber_fiberToProduct
  right_inv := fiberToProduct_productToFiber d

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitive_gcd_convolution (N : ℕ) :
    2 ^ (4 * N) - 1 =
      ∑ d : Fin N,
        2 ^ d.val * Fintype.card (PrimitivePolynomialVector (N - d.val)) := by
  rw [← card_nonzeroPolynomialVector]
  calc
    Fintype.card (NonzeroPolynomialVector N) =
      ∑ d : Fin N, Fintype.card (BinaryMonicPolynomial d.val) *
        Fintype.card (PrimitivePolynomialVector (N - d.val)) :=
          card_eq_sum_card_products
            (fun d : Fin N ↦ BinaryMonicPolynomial d.val)
            (fun d : Fin N ↦ PrimitivePolynomialVector (N - d.val))
            (gcdDegreeMap N) gcdDegreeFiberEquiv
    _ = _ := by simp_rw [card_monicPolynomial]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitive_gcd_convolution_range (N : ℕ) :
    2 ^ (4 * N) - 1 =
      ∑ d ∈ Finset.range N,
        2 ^ d * Fintype.card (PrimitivePolynomialVector (N - d)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact primitive_gcd_convolution N

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitive_convolution_shift (P : ℕ → ℕ) (n : ℕ) :
    (∑ d ∈ Finset.range (n + 1), 2 ^ d * P (n + 1 - d)) =
      P (n + 1) + 2 * ∑ d ∈ Finset.range n, 2 ^ d * P (n - d) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero]
  have hterm : ∀ d : ℕ, n + 1 - (d + 1) = n - d := by
    intro d
    omega
  simp_rw [hterm, pow_succ]
  rw [Finset.mul_sum]
  simp only [Nat.mul_comm, Nat.add_comm, Nat.mul_left_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitive_card_of_convolution (P : ℕ → ℕ)
    (hP : ∀ N : ℕ, 2 ^ (4 * N) - 1 =
      ∑ d ∈ Finset.range N, 2 ^ d * P (N - d))
    (N : ℕ) (hN : 0 < N) :
    P N = 7 * 2 ^ (4 * N - 3) + 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hcurrent := hP (n + 1)
  have hprevious := hP n
  rw [primitive_convolution_shift] at hcurrent
  rw [← hprevious] at hcurrent
  have hsub := primitiveCount_subtraction (n + 1) (by omega)
  rw [primitiveCount_eq (n + 1) (by omega)] at hsub
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] at hsub ⊢
  have hpositive : 0 < 2 ^ (4 * n) := pow_pos (by omega) _
  omega

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem card_primitivePolynomialVector (N : ℕ) (hN : 0 < N) :
    Fintype.card (PrimitivePolynomialVector N) =
      7 * 2 ^ (4 * N - 3) + 1 := by
  exact primitive_card_of_convolution
    (fun n ↦ Fintype.card (PrimitivePolynomialVector n))
    primitive_gcd_convolution_range N hN

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem binaryPolynomial_unit_eq_one {p : R} (hp : IsUnit p) : p = 1 := by
  obtain ⟨a, ha, hpa⟩ := Polynomial.isUnit_iff.mp hp
  have ha' : a = 1 := by
    fin_cases a
    · exact (ha.ne_zero rfl).elim
    · rfl
  simpa only [ha', map_one] using hpa.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitiveVector_specialLinear_completion_of_coordinateIdeal (v : V)
    (hv : Ideal.span (Set.range v) = ⊤) :
    ∃ g : Q, Matrix.SpecialLinearGroup.toLin' g e = v := by
  have hone : (1 : R) ∈ Ideal.span (Set.range v) := by rw [hv]; trivial
  obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hone
  let f : V →ₗ[R] R := Fintype.linearCombination R c
  have hfv : f v = 1 := by
    simpa [f, Fintype.linearCombination_apply, smul_eq_mul, mul_comm] using hc
  let N : Submodule R V := LinearMap.ker f
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun R (Fin 4)) N
  have hli : ∀ (a : R), ∀ x ∈ N, a • v + x = 0 → a = 0 := by
    intro a x hx h
    have hx' : f x = 0 := LinearMap.mem_ker.mp hx
    have hz := congrArg f h
    simpa [map_add, map_smul, hfv, hx'] using hz
  have hsp : ∀ z : V, ∃ a : R, z + a • v ∈ N := by
    intro z
    refine ⟨-(f z), ?_⟩
    apply LinearMap.mem_ker.mpr
    simp [map_add, map_smul, hfv]
  let bfull : Module.Basis (Fin (n + 1)) R V :=
    Module.Basis.mkFinCons v b hli hsp
  have hn : n + 1 = 4 := by
    have hcard := Fintype.card_congr
      (bfull.indexEquiv (Pi.basisFun R (Fin 4)))
    simpa using hcard
  let bfour : Module.Basis (Fin 4) R V := bfull.reindex (finCongr hn)
  have hbzero : bfour 0 = v := by
    have hz : (finCongr hn).symm (0 : Fin 4) = (0 : Fin (n + 1)) :=
      Fin.ext rfl
    dsimp only [bfour]
    rw [Module.Basis.reindex_apply, hz]
    change Module.Basis.mkFinCons v b hli hsp 0 = v
    simpa only [Fin.cons_zero] using congrFun
      (Module.Basis.coe_mkFinCons v b hli hsp) (0 : Fin (n + 1))
  let A : Matrix (Fin 4) (Fin 4) R :=
    (Pi.basisFun R (Fin 4)).toMatrix bfour
  let : Invertible A := Module.Basis.invertibleToMatrix
    (Pi.basisFun R (Fin 4)) bfour
  have hdet : A.det = 1 :=
    binaryPolynomial_unit_eq_one (Matrix.isUnit_det_of_invertible A)
  refine ⟨⟨A, hdet⟩, ?_⟩
  apply funext
  intro i
  change A.mulVec e i = v i
  simp [A, Matrix.mulVec, dotProduct, e, Module.Basis.toMatrix_apply,
    hbzero]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitiveVector_specialLinear_completion (v : V)
    (hv : IsPrimitiveVector v) :
    ∃ g : Q, Matrix.SpecialLinearGroup.toLin' g e = v := by
  apply primitiveVector_specialLinear_completion_of_coordinateIdeal
  exact (isPrimitiveVector_iff_coordinateIdeal_eq_top v).mp hv

end

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem e_isPrimitiveVector : IsPrimitiveVector e := by
  apply (isPrimitiveVector_iff_coordinateIdeal_eq_top e).mpr
  apply Ideal.eq_top_of_isUnit_mem
    (I := coordinateIdeal e)
    (x := (1 : R))
  · have h : e (0 : Fin 4) ∈ coordinateIdeal e :=
      Ideal.mem_span_range_self
    simpa only [e, Fin.isValue, ↓reduceIte] using h
  · exact isUnit_one

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitiveVector_actingGroup_completion_of_surjective
    (hsurj : Function.Surjective pi₂)
    (v : V) (hv : IsPrimitiveVector v) :
    ∃ k : K, kLinear k e = v := by
  obtain ⟨g, hg⟩ := primitiveVector_specialLinear_completion v hv
  obtain ⟨k, hk⟩ := hsurj g
  refine ⟨k, ?_⟩
  change Matrix.SpecialLinearGroup.toLin' (pi₂ k) e = v
  rw [hk]
  exact hg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitiveVector_actingGroup_completion
    (v : V) (hv : IsPrimitiveVector v) :
    ∃ k : K, kLinear k e = v :=
  primitiveVector_actingGroup_completion_of_surjective pi₂_surjective v hv





end

section

open scoped BigOperators

variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem binary_quadratic_support_quarter_direct
    (f : W → F) (b : W → W → F)
    (_hzero : f 0 = 0)
    (hadd : ∀ x y, f (x + y) = f x + f y + b x y)
    (hbadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hf : ∃ x, f x ≠ 0) :
    Fintype.card W ≤
      4 * ((Finset.univ : Finset W).filter (fun x ↦ f x ≠ 0)).card := by
  classical
  let support : Finset W := Finset.univ.filter (fun x ↦ f x ≠ 0)
  let offset (u v : W) (c : Fin 2 × Fin 2) : W :=
    (if c.1 = 0 then 0 else u) + (if c.2 = 0 then 0 else v)
  let cover (u v : W) : (↥support × (Fin 2 × Fin 2)) → W :=
    fun p ↦ p.1.val + offset u v p.2
  have hcover_card (u v : W)
      (hsurj : Function.Surjective (cover u v)) :
      Fintype.card W ≤ 4 * support.card := by
    have hcard := Fintype.card_le_of_surjective (cover u v) hsurj
    simpa only [ge_iff_le, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Nat.reduceMul,
      Nat.mul_comm] using hcard
  change Fintype.card W ≤ 4 * support.card
  by_cases hb : ∃ u v : W, b u v ≠ 0
  · obtain ⟨u, v, huv⟩ := hb
    have hone : b u v = 1 :=
      ConnesRigidity.FeedbackBooleanPolynomial.eq_one_of_ne_zero_zmod_two _ huv
    have hsquare (x : W) :
        f x + f (x + u) + f (x + v) + f ((x + u) + v) = b u v := by
      simp only [hadd x u, hadd x v, hadd (x + u) v, hbadd x u v]
      have hx : f x + f x = 0 := add_self_eq_zero (f x)
      have hu : f u + f u = 0 := add_self_eq_zero (f u)
      have hv : f v + f v = 0 := add_self_eq_zero (f v)
      have hxu : b x u + b x u = 0 := add_self_eq_zero (b x u)
      have hxv : b x v + b x v = 0 := add_self_eq_zero (b x v)
      linear_combination 2 * hx + hu + hv + hxu + hxv
    apply hcover_card u v
    intro x
    by_cases hx : f x ≠ 0
    · exact ⟨(⟨x, by simpa only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
                       support] using hx⟩, (0, 0)), by simp only [Fin.isValue, ↓reduceIte,
                                                               add_zero, cover, offset]⟩
    by_cases hxu : f (x + u) ≠ 0
    · refine ⟨(⟨x + u, by simpa only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
                            support] using hxu⟩, (1, 0)), ?_⟩
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte, add_zero, add_assoc, add_self_eq_zero, cover,
        offset]
    by_cases hxv : f (x + v) ≠ 0
    · refine ⟨(⟨x + v, by simpa only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
                            support] using hxv⟩, (0, 1)), ?_⟩
      simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_add, add_assoc, add_self_eq_zero,
        add_zero, cover, offset]
    have hxuv : f ((x + u) + v) ≠ 0 := by
      intro hz
      have hsq := hsquare x
      rw [not_ne_iff.mp hx, not_ne_iff.mp hxu, not_ne_iff.mp hxv, hz] at hsq
      simp only [add_zero, hone, zero_ne_one] at hsq
    refine ⟨(⟨(x + u) + v, by simpa only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
                                support] using hxuv⟩, (1, 1)), ?_⟩
    change ((x + u) + v) + (u + v) = x
    have hu : u + u = 0 := add_self_eq_zero u
    have hv : v + v = 0 := add_self_eq_zero v
    calc
      ((x + u) + v) + (u + v) = x + (u + u) + (v + v) := by abel
      _ = x := by rw [hu, hv]; simp only [add_zero]
  · have hbzero : ∀ u v : W, b u v = 0 := by
      intro u v
      by_contra h
      exact hb ⟨u, v, h⟩
    obtain ⟨u, hu⟩ := hf
    have hone : f u = 1 :=
      ConnesRigidity.FeedbackBooleanPolynomial.eq_one_of_ne_zero_zmod_two _ hu
    apply hcover_card u 0
    intro x
    by_cases hx : f x ≠ 0
    · exact ⟨(⟨x, by simpa only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
                       support] using hx⟩, (0, 0)), by simp only [Fin.isValue, ↓reduceIte,
                                                               add_zero, cover, offset]⟩
    have hxu : f (x + u) ≠ 0 := by
      rw [hadd x u, not_ne_iff.mp hx, hbzero]
      simp only [hone, zero_add, add_zero, ne_eq, one_ne_zero, not_false_eq_true]
    refine ⟨(⟨x + u, by simpa only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
                          support] using hxu⟩, (1, 0)), ?_⟩
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, add_zero, add_assoc, add_self_eq_zero, cover,
      offset]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem polarization_add_left_direct (u v w : V) :
    polarization (u + v) w = polarization u w + polarization v w := by
  apply Subtype.ext
  change
    (u + v) ⊗ₜ[F] w + w ⊗ₜ[F] (u + v) =
      (u ⊗ₜ[F] w + w ⊗ₜ[F] u) +
        (v ⊗ₜ[F] w + w ⊗ₜ[F] v)
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def boundedVectorLinearDirect (N : ℕ) : BinaryPolynomialVector N →ₗ[F] V where
  toFun := polynomialVectorVal
  map_add' x y := by
    funext i
    rfl
  map_smul' c x := by
    funext i
    rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem divided_square_truncated_support_quarter_direct
    (N : ℕ) (q : Y)
    (hq : ∃ x : BinaryPolynomialVector N,
      q (diagonal (polynomialVectorVal x)) ≠ 0) :
    Fintype.card (BinaryPolynomialVector N) ≤
      4 * ((Finset.univ : Finset (BinaryPolynomialVector N)).filter
        (fun x ↦ q (diagonal (polynomialVectorVal x)) ≠ 0)).card := by
  let j := boundedVectorLinearDirect N
  apply binary_quadratic_support_quarter_direct
    (fun x ↦ q (diagonal (j x)))
    (fun x y ↦ q (polarization (j x) (j y)))
  · change q (diagonal 0) = 0
    have hd : diagonal (0 : V) = 0 := by
      apply Subtype.ext
      simp only [diagonal_val, square, TensorProduct.tmul_zero, ZeroMemClass.coe_zero]
    rw [hd, map_zero]
  · intro x y
    change q (diagonal (j (x + y))) =
      q (diagonal (j x)) + q (diagonal (j y)) +
        q (polarization (j x) (j y))
    rw [map_add, diagonal_add, map_add, map_add]
  · intro x y z
    change q (polarization (j (x + y)) (j z)) =
      q (polarization (j x) (j z)) + q (polarization (j y) (j z))
    rw [map_add, polarization_add_left_direct, map_add]
  · exact hq

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem character_truncated_detection_quarter_direct
    (N : ℕ) (z : X × Y)
    (hz : ∃ x : BinaryPolynomialVector N,
      z.1 (polynomialVectorVal x) ≠ 0 ∨
        z.2 (diagonal (polynomialVectorVal x)) ≠ 0) :
    Fintype.card (BinaryPolynomialVector N) ≤
      4 * ((Finset.univ : Finset (BinaryPolynomialVector N)).filter
        (fun x ↦ z.1 (polynomialVectorVal x) ≠ 0 ∨
          z.2 (diagonal (polynomialVectorVal x)) ≠ 0)).card := by
  classical
  obtain ⟨x, hx | hx⟩ := hz
  · have hlinear := binary_quadratic_support_quarter_direct
      (W := BinaryPolynomialVector N)
      (fun y ↦ z.1 (polynomialVectorVal y))
      (fun _ _ ↦ 0)
      (by
        change z.1 ((boundedVectorLinearDirect N) 0) = 0
        rw [map_zero, map_zero])
      (by
        intro u v
        change z.1 (polynomialVectorVal (u + v)) =
          z.1 (polynomialVectorVal u) + z.1 (polynomialVectorVal v) + 0
        rw [show polynomialVectorVal (u + v) =
          polynomialVectorVal u + polynomialVectorVal v from
            (boundedVectorLinearDirect N).map_add u v, map_add]
        simp only [add_zero])
      (by simp only [add_zero, implies_true])
      ⟨x, hx⟩
    have hsubset :
        ((Finset.univ : Finset (BinaryPolynomialVector N)).filter
          (fun y ↦ z.1 (polynomialVectorVal y) ≠ 0)) ⊆
        ((Finset.univ : Finset (BinaryPolynomialVector N)).filter
          (fun y ↦ z.1 (polynomialVectorVal y) ≠ 0 ∨
            z.2 (diagonal (polynomialVectorVal y)) ≠ 0)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact Or.inl hy
    have hcard := Finset.card_le_card hsubset
    omega
  · have hquadratic :=
      divided_square_truncated_support_quarter_direct N z.2 ⟨x, hx⟩
    have hsubset :
        ((Finset.univ : Finset (BinaryPolynomialVector N)).filter
          (fun y ↦ z.2 (diagonal (polynomialVectorVal y)) ≠ 0)) ⊆
        ((Finset.univ : Finset (BinaryPolynomialVector N)).filter
          (fun y ↦ z.1 (polynomialVectorVal y) ≠ 0 ∨
            z.2 (diagonal (polynomialVectorVal y)) ≠ 0)) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact Or.inr hy
    have hcard := Finset.card_le_card hsubset
    omega

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def primitiveTruncationFinset (N : ℕ) :
    Finset (BinaryPolynomialVector N) := by
  classical
  exact Finset.univ.filter
    (fun v ↦ IsPrimitiveVector (polynomialVectorVal v))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem mem_primitiveTruncationFinset (N : ℕ)
    (v : BinaryPolynomialVector N) :
    v ∈ primitiveTruncationFinset N ↔
      IsPrimitiveVector (polynomialVectorVal v) := by
  classical
  simp only [primitiveTruncationFinset, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem primitiveTruncationFinset_card (N : ℕ) (hN : 0 < N) :
    (primitiveTruncationFinset N).card =
      7 * 2 ^ (4 * N - 3) + 1 := by
  classical
  change (Finset.univ.filter
    (fun v : BinaryPolynomialVector N ↦
      IsPrimitiveVector (polynomialVectorVal v))).card = _
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {v : BinaryPolynomialVector N //
        IsPrimitiveVector (polynomialVectorVal v)} =
      Fintype.card (PrimitivePolynomialVector N) :=
        Fintype.card_congr (Equiv.refl _)
    _ = _ := card_primitivePolynomialVector N hN

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem character_truncated_detection_primitive_seventh
    (N : ℕ) (hN : 0 < N) (z : X × Y)
    (hz : ∃ x : BinaryPolynomialVector N,
      z.1 (polynomialVectorVal x) ≠ 0 ∨
        z.2 (diagonal (polynomialVectorVal x)) ≠ 0) :
    (primitiveTruncationFinset N).card ≤
      7 * ((primitiveTruncationFinset N).filter
        (fun x ↦ z.1 (polynomialVectorVal x) ≠ 0 ∨
          z.2 (diagonal (polynomialVectorVal x)) ≠ 0)).card := by
  classical
  let detecting : Finset (BinaryPolynomialVector N) :=
    Finset.univ.filter
      (fun x ↦ z.1 (polynomialVectorVal x) ≠ 0 ∨
        z.2 (diagonal (polynomialVectorVal x)) ≠ 0)
  have hbound := DetectionGap.primitive_detecting_seventh
    (Finset.univ : Finset (BinaryPolynomialVector N))
    (primitiveTruncationFinset N) detecting
    (2 ^ (4 * N - 3))
    (Finset.subset_univ _)
    (Finset.filter_subset _ _)
    (by
      simp only [Finset.card_univ, card_binaryPolynomialVector]
      exact DetectionGap.cube_card_eq_eight_mul_scale N hN)
    (primitiveTruncationFinset_card N hN)
    (character_truncated_detection_quarter_direct N z hz)
  have hset : detecting ∩ primitiveTruncationFinset N =
      (primitiveTruncationFinset N).filter
        (fun x ↦ z.1 (polynomialVectorVal x) ≠ 0 ∨
          z.2 (diagonal (polynomialVectorVal x)) ≠ 0) := by
    ext x
    simp only [ne_eq, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_primitiveTruncationFinset, and_comm, detecting]
  rwa [hset] at hbound

end

section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators


/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measure_detection_gap_of_uniform_primitive_counts
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (primitive : Finset ι)
    (detect : ι → Set α) [DecidableRel (fun x v ↦ x ∈ detect v)]
    (active : Set α) (e : ι)
    (he : e ∈ primitive)
    (hdetect : ∀ v ∈ primitive, MeasurableSet (detect v))
    (hactive : MeasurableSet active)
    (hpointwise : ∀ x ∈ active,
      primitive.card ≤ 7 * (primitive.filter (fun v ↦ x ∈ detect v)).card)
    (huniform : ∀ v ∈ primitive, μ (detect v) = μ (detect e)) :
    μ active ≤ 7 * μ (detect e) := by
  classical
  have hpoint : ∀ x : α,
      (primitive.card : ℝ≥0∞) * active.indicator 1 x ≤
        7 * ∑ v ∈ primitive, (detect v).indicator 1 x := by
    intro x
    by_cases hx : x ∈ active
    · have hcard : (primitive.card : ℝ≥0∞) ≤
          7 * ((primitive.filter (fun v ↦ x ∈ detect v)).card : ℝ≥0∞) := by
        exact_mod_cast hpointwise x hx
      simpa only [hx, indicator_of_mem, Pi.one_apply, mul_one, indicator_apply, Finset.sum_boole,
        ge_iff_le] using hcard
    · simp only [hx, not_false_eq_true, indicator_of_notMem, mul_zero, indicator_apply,
        Pi.one_apply, Finset.sum_boole, zero_le]
  have hweighted := lintegral_mono (μ := μ) hpoint
  rw [lintegral_const_mul (primitive.card : ℝ≥0∞)
      (measurable_one.indicator hactive)] at hweighted
  rw [lintegral_indicator_one hactive] at hweighted
  rw [lintegral_const_mul (7 : ℝ≥0∞)
      (Finset.measurable_fun_sum primitive
        (fun v hv ↦ measurable_one.indicator (hdetect v hv)))] at hweighted
  have hsplit :
      (∫⁻ x, ∑ v ∈ primitive, (detect v).indicator 1 x ∂μ) =
        ∑ v ∈ primitive, μ (detect v) := by
    rw [lintegral_finsetSum primitive
      (fun v hv ↦ measurable_one.indicator (hdetect v hv))]
    apply Finset.sum_congr rfl
    intro v hv
    exact lintegral_indicator_one (hdetect v hv)
  rw [hsplit] at hweighted
  have hsum : (∑ v ∈ primitive, μ (detect v)) =
      (primitive.card : ℝ≥0∞) * μ (detect e) := by
    calc
      (∑ v ∈ primitive, μ (detect v)) = ∑ _v ∈ primitive, μ (detect e) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact huniform v hv
      _ = (primitive.card : ℝ≥0∞) * μ (detect e) := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hsum] at hweighted
  have hcardzero : (primitive.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨e, he⟩
  have hcardtop : (primitive.card : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.mul_le_mul_iff_left hcardzero hcardtop).mp
  simpa only [mul_comm, mul_left_comm] using hweighted

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measureReal_detection_gap_of_uniform_primitive_counts
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (primitive : Finset ι)
    (detect : ι → Set α) [DecidableRel (fun x v ↦ x ∈ detect v)]
    (active : Set α) (e : ι)
    (he : e ∈ primitive)
    (hdetect : ∀ v ∈ primitive, MeasurableSet (detect v))
    (hactive : MeasurableSet active)
    (hpointwise : ∀ x ∈ active,
      primitive.card ≤ 7 * (primitive.filter (fun v ↦ x ∈ detect v)).card)
    (huniform : ∀ v ∈ primitive, μ (detect v) = μ (detect e)) :
    μ.real active ≤ 7 * μ.real (detect e) := by
  have hgap := measure_detection_gap_of_uniform_primitive_counts
    μ primitive detect active e he hdetect hactive hpointwise huniform
  have hfinite : (7 : ℝ≥0∞) * μ (detect e) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top (measure_ne_top μ _)
  have hreal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) hfinite).2 hgap
  simpa only [measureReal_def, ge_iff_le, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hreal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem measureReal_iUnion_le_of_monotone
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (U : ℕ → Set α)
    (hmono : Monotone U)
    {c : ℝ} (hbound : ∀ n, μ.real (U n) ≤ c) :
    μ.real (⋃ n, U n) ≤ c := by
  have hfinite : μ (⋃ n, U n) ≠ ⊤ := measure_ne_top μ _
  have hlim : Tendsto (fun n ↦ μ.real (U n)) atTop
      (𝓝 (μ.real (⋃ n, U n))) := by
    exact (ENNReal.tendsto_toReal hfinite).comp
      (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  exact le_of_tendsto' hlim hbound

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem probability_detection_gap_of_exhaustion
    {α : Type*} [MeasurableSpace α]
    (μ : ProbabilityMeasure α) (zero : α) (U : ℕ → Set α)
    (hzero : MeasurableSet ({zero} : Set α))
    (hmono : Monotone U)
    (hunion : (⋃ n, U n) = ({zero} : Set α)ᶜ)
    {p : ℝ} (hbound : ∀ n, (μ : Measure α).real (U n) ≤ 7 * p) :
    (1 / 7 : ℝ) * (1 - (μ : Measure α).real {zero}) ≤ p := by
  have h := measureReal_iUnion_le_of_monotone
    (μ : Measure α) U hmono hbound
  rw [hunion, measureReal_compl hzero, probReal_univ] at h
  linarith

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance dualProductMeasurable : MeasurableSpace (X × Y) :=
  borel (X × Y)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance dualProductBorel : BorelSpace (X × Y) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def dualPointAction (k : K) (z : X × Y) : X × Y :=
  (z.1.comp (kLinear k⁻¹).toLinearMap,
    z.2.comp (kDividedSquareLinear k⁻¹).toLinearMap)





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem continuous_dualPointAction (k : K) :
    Continuous (dualPointAction k) := by
  exact ((continuous_X_precomp (kLinear k⁻¹).toLinearMap).comp
    continuous_fst).prodMk
      ((continuous_Y_precomp (kDividedSquareLinear k⁻¹).toLinearMap).comp
        continuous_snd)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def IsInvariantDualProbability (μ : ProbabilityMeasure (X × Y)) : Prop :=
  ∀ k : K, (μ : Measure (X × Y)).map (dualPointAction k) = μ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def dualDetects (z : X × Y) (v : V) : Prop :=
  z.1 v ≠ 0 ∨ z.2 (diagonal v) ≠ 0

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def dualDetectionSet (v : V) : Set (X × Y) :=
  {z | dualDetects z v}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualDetectionSet_measurable (v : V) :
    MeasurableSet (dualDetectionSet v) := by
  have hlinear : Continuous (fun z : X × Y ↦ z.1 v) :=
    (continuous_X_eval v).comp continuous_fst
  have hquadratic : Continuous (fun z : X × Y ↦ z.2 (diagonal v)) :=
    (continuous_Y_eval (diagonal v)).comp continuous_snd
  change MeasurableSet
    ({z : X × Y | z.1 v = 0}ᶜ ∪ {z : X × Y | z.2 (diagonal v) = 0}ᶜ)
  exact ((isClosed_eq hlinear continuous_const).measurableSet.compl).union
    ((isClosed_eq hquadratic continuous_const).measurableSet.compl)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualDetects_action (k : K) (z : X × Y) (v : V) :
    dualDetects (dualPointAction k z) (kLinear k v) ↔
      dualDetects z v := by
  have hv : kLinear k⁻¹ (kLinear k v) = v := by
    rw [map_inv]
    exact (kLinear k).symm_apply_apply v
  have hdiag :
      kDividedSquareLinear k⁻¹ (diagonal (kLinear k v)) = diagonal v := by
    rw [kDividedSquareLinear_diagonal, hv]
  change
    (z.1 (kLinear k⁻¹ (kLinear k v)) ≠ 0 ∨
      z.2 (kDividedSquareLinear k⁻¹ (diagonal (kLinear k v))) ≠ 0) ↔
        (z.1 v ≠ 0 ∨ z.2 (diagonal v) ≠ 0)
  rw [hv, hdiag]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualDetectionSet_action_preimage (k : K) (v : V) :
    dualPointAction k ⁻¹' dualDetectionSet (kLinear k v) =
      dualDetectionSet v := by
  ext z
  exact dualDetects_action k z v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem invariantDual_detection_measure
    (μ : ProbabilityMeasure (X × Y))
    (hμ : IsInvariantDualProbability μ)
    (v : V) (hv : IsPrimitiveVector v) :
    (μ : Measure (X × Y)) (dualDetectionSet v) =
      (μ : Measure (X × Y)) (dualDetectionSet e) := by
  obtain ⟨k, hk⟩ := primitiveVector_actingGroup_completion v hv
  have hmap := congrArg
    (fun ν : Measure (X × Y) ↦ ν (dualDetectionSet v)) (hμ k)
  rw [Measure.map_apply (continuous_dualPointAction k).measurable
    (dualDetectionSet_measurable v)] at hmap
  have hpre : dualPointAction k ⁻¹' dualDetectionSet v =
      dualDetectionSet e := by
    rw [← hk]
    exact dualDetectionSet_action_preimage k e
  rw [hpre] at hmap
  exact hmap.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def boxDetectionSet (N : ℕ) : Set (X × Y) :=
  ⋃ v : {v : V // ∀ i, v i ∈ Polynomial.degreeLT (ZMod 2) N},
    dualDetectionSet v.1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem boxDetectionSet_measurable (N : ℕ) :
    MeasurableSet (boxDetectionSet N) := by
  exact MeasurableSet.iUnion fun v ↦
    dualDetectionSet_measurable v.1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem monotone_boxDetectionSet : Monotone boxDetectionSet := by
  intro n m hnm z hz
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr
    ⟨⟨v.1, fun i ↦ Polynomial.degreeLT_mono hnm (v.2 i)⟩, hv⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem exists_boundedPolynomialVector (v : V) :
    ∃ (N : ℕ) (w : BinaryPolynomialVector N), polynomialVectorVal w = v := by
  classical
  let N : ℕ := (∑ i : Fin 4, (v i).natDegree) + 1
  have hbound (i : Fin 4) : (v i).natDegree < N := by
    have hle : (v i).natDegree ≤ ∑ j : Fin 4, (v j).natDegree :=
      Finset.single_le_sum
        (f := fun j : Fin 4 ↦ (v j).natDegree)
        (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    omega
  refine ⟨N, fun i ↦ ⟨v i, ?_⟩, rfl⟩
  apply Polynomial.mem_degreeLT.mpr
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree
    (WithBot.coe_lt_coe.mpr (hbound i))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualPair_eq_zero_of_no_detection (z : X × Y)
    (h : ∀ v : V, ¬ dualDetects z v) : z = 0 := by
  have hlinear : z.1 = 0 := by
    apply LinearMap.ext
    intro v
    have hv := h v
    simp only [dualDetects, ne_eq, not_or, Decidable.not_not] at hv
    exact hv.1
  have hquadratic : z.2 = 0 := by
    apply linearMap_ext_on_diagonal
    intro v
    have hv := h v
    simp only [dualDetects, ne_eq, not_or, Decidable.not_not] at hv
    exact hv.2
  exact Prod.ext hlinear hquadratic

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem iUnion_boxDetectionSet :
    (⋃ N : ℕ, boxDetectionSet N) = ({(0, 0)} : Set (X × Y))ᶜ := by
  ext z
  constructor
  · intro hz hzero
    have hzzero : z = (0, 0) := by simpa only [mem_singleton_iff] using hzero
    obtain ⟨N, hzN⟩ := Set.mem_iUnion.mp hz
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hzN
    change dualDetects z v.1 at hv
    simp only [dualDetects, hzzero, LinearMap.zero_apply, ne_eq, not_true_eq_false, or_self] at hv
  · intro hz
    have hne : z ≠ (0, 0) := by simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hz
    have hexists : ∃ v : V, dualDetects z v := by
      by_contra hnone
      push Not at hnone
      exact hne (dualPair_eq_zero_of_no_detection z hnone)
    obtain ⟨v, hv⟩ := hexists
    obtain ⟨N, w, hw⟩ := exists_boundedPolynomialVector v
    apply Set.mem_iUnion.mpr
    refine ⟨N, Set.mem_iUnion.mpr
      ⟨⟨polynomialVectorVal w, fun i ↦ (w i).property⟩, ?_⟩⟩
    change dualDetects z (polynomialVectorVal w)
    rw [hw]
    exact hv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def boundedStandardVector (N : ℕ) (hN : 0 < N) :
    BinaryPolynomialVector N := by
  intro i
  refine ⟨e i, ?_⟩
  apply Polynomial.mem_degreeLT.mpr
  by_cases hi : i = 0
  · simp only [e, hi, Fin.isValue, ↓reduceIte, Polynomial.degree_one, Nat.cast_pos, hN]
  · simp only [e, Fin.isValue, hi, ↓reduceIte, Polynomial.degree_zero, WithBot.bot_lt_natCast]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem polynomialVectorVal_boundedStandardVector
    (N : ℕ) (hN : 0 < N) :
    polynomialVectorVal (boundedStandardVector N hN) = e := by
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem boundedStandardVector_mem_primitiveTruncationFinset
    (N : ℕ) (hN : 0 < N) :
    boundedStandardVector N hN ∈ primitiveTruncationFinset N := by
  rw [mem_primitiveTruncationFinset]
  exact e_isPrimitiveVector

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem invariantDual_boxDetection_bound
    (μ : ProbabilityMeasure (X × Y))
    (hμ : IsInvariantDualProbability μ)
    (N : ℕ) (hN : 0 < N) :
    (μ : Measure (X × Y)).real (boxDetectionSet N) ≤
      7 * (μ : Measure (X × Y)).real (dualDetectionSet e) := by
  classical
  let standard : BinaryPolynomialVector N := boundedStandardVector N hN
  have hstandard : standard ∈ primitiveTruncationFinset N :=
    boundedStandardVector_mem_primitiveTruncationFinset N hN
  have hpoint : ∀ z ∈ boxDetectionSet N,
      (primitiveTruncationFinset N).card ≤
        7 * ((primitiveTruncationFinset N).filter
          (fun v ↦ z ∈ dualDetectionSet
            (polynomialVectorVal v))).card := by
    intro z hz
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hz
    let v : BinaryPolynomialVector N := fun i ↦ ⟨w.1 i, w.2 i⟩
    have hv : z ∈ dualDetectionSet (polynomialVectorVal v) := hw
    have hseventh := character_truncated_detection_primitive_seventh
      N hN z ⟨v, hv⟩
    have hpredicate :
        (fun v : BinaryPolynomialVector N ↦
          z ∈ dualDetectionSet (polynomialVectorVal v)) =
        (fun v ↦ z.1 (polynomialVectorVal v) ≠ 0 ∨
          z.2 (diagonal (polynomialVectorVal v)) ≠ 0) := by
      funext v
      rfl
    simpa only [hpredicate] using hseventh
  have huniform : ∀ v ∈ primitiveTruncationFinset N,
      (μ : Measure (X × Y))
          (dualDetectionSet (polynomialVectorVal v)) =
        (μ : Measure (X × Y))
          (dualDetectionSet (polynomialVectorVal standard)) := by
    intro v hv
    rw [polynomialVectorVal_boundedStandardVector]
    apply invariantDual_detection_measure μ hμ (polynomialVectorVal v)
    exact (mem_primitiveTruncationFinset N v).mp hv
  have hbound := measureReal_detection_gap_of_uniform_primitive_counts
    (μ : Measure (X × Y)) (primitiveTruncationFinset N)
    (fun v : BinaryPolynomialVector N ↦
      dualDetectionSet (polynomialVectorVal v))
    (boxDetectionSet N) standard hstandard
    (fun v _ ↦ dualDetectionSet_measurable (polynomialVectorVal v))
    (boxDetectionSet_measurable N) hpoint huniform
  simpa [standard] using hbound

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem dualProbability_detection_gap
    (μ : ProbabilityMeasure (X × Y))
    (hμ : IsInvariantDualProbability μ) :
    (1 / 7 : ℝ) *
        (1 - (μ : Measure (X × Y)).real ({(0, 0)} : Set (X × Y))) ≤
      (μ : Measure (X × Y)).real (dualDetectionSet e) := by
  apply probability_detection_gap_of_exhaustion
    μ (0, 0) boxDetectionSet
    (isClosed_singleton.measurableSet)
    monotone_boxDetectionSet iUnion_boxDetectionSet
  intro N
  by_cases hN : 0 < N
  · exact invariantDual_boxDetection_bound μ hμ N hN
  · have hzero : N = 0 := by omega
    subst N
    exact (measureReal_mono (μ := (μ : Measure (X × Y)))
      (monotone_boxDetectionSet (show (0 : ℕ) ≤ 1 by omega))).trans
        (invariantDual_boxDetection_bound μ hμ 1 (by omega))

end

section

open MeasureTheory

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
variable [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def homeomorphPushProbability (e : α ≃ₜ β)
    (μ : ProbabilityMeasure α) : ProbabilityMeasure β :=
  μ.map e.continuous.measurable.aemeasurable



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem homeomorphPushProbability_invariant
    (e : α ≃ₜ β) (μ : ProbabilityMeasure α)
    (sourceAction : ι → α → α) (targetAction : ι → β → β)
    (hsource : ∀ i, Measurable (sourceAction i))
    (htarget : ∀ i, Measurable (targetAction i))
    (hequiv : ∀ i x, e (sourceAction i x) = targetAction i (e x))
    (hμ : ∀ i, (μ : Measure α).map (sourceAction i) = μ) :
    ∀ i, ((homeomorphPushProbability e μ : ProbabilityMeasure β) : Measure β).map
      (targetAction i) = homeomorphPushProbability e μ := by
  intro i
  change ((μ : Measure α).map e).map (targetAction i) =
    (μ : Measure α).map e
  rw [Measure.map_map (htarget i) e.continuous.measurable]
  have hcomp : targetAction i ∘ e = e ∘ sourceAction i := by
    funext x
    exact (hequiv i x).symm
  rw [hcomp, ← Measure.map_map e.continuous.measurable (hsource i), hμ i]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem homeomorphPushProbability_measureReal
    (e : α ≃ₜ β) (μ : ProbabilityMeasure α)
    (s : Set β) (hs : MeasurableSet s) :
    ((homeomorphPushProbability e μ : ProbabilityMeasure β) : Measure β).real s =
      (μ : Measure α).real (e ⁻¹' s) := by
  exact map_measureReal_apply e.continuous.measurable hs

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem homeomorphPushProbability_measureReal_singleton
    [MeasurableSingletonClass β]
    (e : α ≃ₜ β) (μ : ProbabilityMeasure α) (x : α) :
    ((homeomorphPushProbability e μ : ProbabilityMeasure β) : Measure β).real
        {e x} =
      (μ : Measure α).real {x} := by
  rw [homeomorphPushProbability_measureReal e μ {e x}
    (measurableSet_singleton (e x))]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff, EmbeddingLike.apply_eq_iff_eq]

end

section

open ConnesRigidity MeasureTheory


/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaDetectionDualMeasurable (n : ℕ) :
    MeasurableSpace (DiscreteCharacterSpace (E n)) :=
  borel (DiscreteCharacterSpace (E n))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaDetectionDualBorel (n : ℕ) :
    BorelSpace (DiscreteCharacterSpace (E n)) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaDetectionPairMeasurable : MeasurableSpace (X × Y) :=
  borel (X × Y)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaDetectionPairBorel : BorelSpace (X × Y) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance gammaDetectionKernelDecidableEq (n : ℕ) : DecidableEq (E n) :=
  Classical.decEq _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gammaPairHomeomorph (n : ℕ)
    (bidual : CarryGroup n ≃ₜ DiscreteCharacterSpace (E n)) :
    DiscreteCharacterSpace (E n) ≃ₜ X × Y :=
  bidual.symm.trans (carryHomeomorph n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carry_evalFour_ne_zero_of_quadratic_ne_zero
    (n : ℕ) (v : V) (z : CarryGroup n)
    (h : z.quadratic (diagonal v) ≠ 0) :
    CarryGroup.evalFour n v z ≠ 0 := by
  rw [CarryGroup.evalFour_apply]
  generalize shift n z.linear v = a
  generalize z.quadratic (diagonal v) = b at h ⊢
  fin_cases a <;> fin_cases b <;>
    first | exact (h rfl).elim | decide

section EvaluationHomeomorphism

variable (n : ℕ)
variable (bidual : CarryGroup n ≃ₜ DiscreteCharacterSpace (E n))
variable (hbidual : ∀ (z : CarryGroup n) (η : E n),
  bidual z (Multiplicative.ofAdd η) =
    Additive.toMul η (Multiplicative.ofAdd z))

include hbidual

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaBidual_equivariant (k : K) (z : CarryGroup n) :
    dualCharacterAction (gammaSplitAbelianExtension n).action k (bidual z) =
      bidual (kCarryAddAut n k z) := by
  apply PontryaginDual.ext
  intro η
  change bidual z
      (Multiplicative.ofAdd
        (Multiplicative.toAdd
          (kEAction n k⁻¹
            (Multiplicative.ofAdd (Multiplicative.toAdd η))))) =
    bidual (kCarryAddAut n k z)
      (Multiplicative.ofAdd (Multiplicative.toAdd η))
  rw [hbidual, hbidual, kEAction_apply]
  rw [map_inv, inv_inv]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaPairHomeomorph_equivariant (k : K)
    (χ : DiscreteCharacterSpace (E n)) :
    gammaPairHomeomorph n bidual
        (dualCharacterAction (gammaSplitAbelianExtension n).action k χ) =
      dualPointAction k (gammaPairHomeomorph n bidual χ) := by
  have hcarry :
      bidual.symm
          (dualCharacterAction (gammaSplitAbelianExtension n).action k χ) =
        kCarryAddAut n k (bidual.symm χ) := by
    apply bidual.injective
    rw [bidual.apply_symm_apply]
    calc
      dualCharacterAction (gammaSplitAbelianExtension n).action k χ =
          dualCharacterAction (gammaSplitAbelianExtension n).action k
            (bidual (bidual.symm χ)) := by rw [bidual.apply_symm_apply]
      _ = bidual (kCarryAddAut n k (bidual.symm χ)) :=
        gammaBidual_equivariant n bidual hbidual k (bidual.symm χ)
  change
    carryHomeomorph n
        (bidual.symm
          (dualCharacterAction (gammaSplitAbelianExtension n).action k χ)) =
      dualPointAction k (carryHomeomorph n (bidual.symm χ))
  rw [hcarry]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaDualCharacterAction_continuous (k : K) :
    Continuous (dualCharacterAction (gammaSplitAbelianExtension n).action k) := by
  have h := (gammaPairHomeomorph n bidual).symm.continuous.comp
    ((continuous_dualPointAction k).comp
      (gammaPairHomeomorph n bidual).continuous)
  apply h.congr
  intro χ
  change
    (gammaPairHomeomorph n bidual).symm
        (dualPointAction k (gammaPairHomeomorph n bidual χ)) =
      dualCharacterAction (gammaSplitAbelianExtension n).action k χ
  rw [← gammaPairHomeomorph_equivariant n bidual hbidual k χ,
    Homeomorph.symm_apply_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gammaPairProbability
    (μ : ProbabilityMeasure (DiscreteCharacterSpace (E n))) :
    ProbabilityMeasure (X × Y) :=
  homeomorphPushProbability (gammaPairHomeomorph n bidual) μ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaPairProbability_invariant
    (μ : ProbabilityMeasure (DiscreteCharacterSpace (E n)))
    (hμ : IsInvariantSpectralMeasure
      (gammaSplitAbelianExtension n).action μ) :
    IsInvariantDualProbability (gammaPairProbability n bidual μ) := by
  exact homeomorphPushProbability_invariant
    (gammaPairHomeomorph n bidual) μ
    (fun k : K ↦
      dualCharacterAction (gammaSplitAbelianExtension n).action k)
    dualPointAction
    (fun k ↦ (gammaDualCharacterAction_continuous n bidual hbidual k).measurable)
    (fun k ↦ (continuous_dualPointAction k).measurable)
    (gammaPairHomeomorph_equivariant n bidual hbidual)
    hμ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaBidual_zero :
    bidual (0 : CarryGroup n) =
      (1 : DiscreteCharacterSpace (E n)) := by
  apply PontryaginDual.ext
  intro η
  change bidual (0 : CarryGroup n)
      (Multiplicative.ofAdd (Multiplicative.toAdd η)) = 1
  rw [hbidual]
  exact map_one _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaPairHomeomorph_trivial :
    gammaPairHomeomorph n bidual
        (1 : DiscreteCharacterSpace (E n)) = (0, 0) := by
  rw [← gammaBidual_zero n bidual hbidual]
  change carryHomeomorph n (bidual.symm (bidual 0)) = (0, 0)
  rw [bidual.symm_apply_apply]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaDetectedSet_preimage_subset :
    gammaPairHomeomorph n bidual ⁻¹' dualDetectionSet e ⊆
      gammaDetectedSet n := by
  intro χ hχ
  let z := bidual.symm χ
  change z.linear e ≠ 0 ∨ z.quadratic (diagonal e) ≠ 0 at hχ
  rcases hχ with hlinear | hquadratic
  · left
    change χ (Multiplicative.ofAdd (iota n e)) ≠ 1
    have hχz : χ = bidual z := (bidual.apply_symm_apply χ).symm
    rw [hχz, hbidual, iota_apply]
    intro hzero
    exact hlinear (ZMod.injective_toCircle
      (hzero.trans ZMod.toCircle.map_zero_eq_one.symm))
  · right
    change χ (Multiplicative.ofAdd (epsilon n e)) ≠ 1
    have hχz : χ = bidual z := (bidual.apply_symm_apply χ).symm
    rw [hχz, hbidual, epsilon_apply]
    intro hzero
    apply carry_evalFour_ne_zero_of_quadratic_ne_zero n e z hquadratic
    exact ZMod.injective_toCircle
      (hzero.trans ZMod.toCircle.map_zero_eq_one.symm)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaProbability_detection_gap_of_bidual
    (μ : ProbabilityMeasure (DiscreteCharacterSpace (E n)))
    (hμ : IsInvariantSpectralMeasure
      (gammaSplitAbelianExtension n).action μ) :
    (1 / 7 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (μ : Measure (DiscreteCharacterSpace (E n))).real
        (gammaDetectedSet n) := by
  let ν := gammaPairProbability n bidual μ
  have hν : IsInvariantDualProbability ν :=
    gammaPairProbability_invariant n bidual hbidual μ hμ
  have hgap := dualProbability_detection_gap ν hν
  have hatom :
      (ν : Measure (X × Y)).real ({(0, 0)} : Set (X × Y)) =
        spectralTrivialAtom μ := by
    rw [← gammaPairHomeomorph_trivial n bidual hbidual]
    exact homeomorphPushProbability_measureReal_singleton
      (gammaPairHomeomorph n bidual) μ 1
  have hdetected :
      (ν : Measure (X × Y)).real (dualDetectionSet e) ≤
        (μ : Measure (DiscreteCharacterSpace (E n))).real
          (gammaDetectedSet n) := by
    change
      ((homeomorphPushProbability (gammaPairHomeomorph n bidual) μ :
        ProbabilityMeasure (X × Y)) : Measure (X × Y)).real
          (dualDetectionSet e) ≤ _
    rw [homeomorphPushProbability_measureReal
      (gammaPairHomeomorph n bidual) μ (dualDetectionSet e)
      (dualDetectionSet_measurable e)]
    exact measureReal_mono
      (gammaDetectedSet_preimage_subset n bidual hbidual)
  rw [hatom] at hgap
  exact hgap.trans hdetected

end EvaluationHomeomorphism

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_probability_detection_gap (n : ℕ)
    (μ : ProbabilityMeasure (DiscreteCharacterSpace (E n)))
    (hμ : IsInvariantSpectralMeasure
      (gammaSplitAbelianExtension n).action μ) :
    (1 / 7 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (μ : Measure (DiscreteCharacterSpace (E n))).real
        (gammaDetectedSet n) :=
  gammaProbability_detection_gap_of_bidual n
    (carryBidualHomeomorph n)
    (fun z η ↦ carryBidualHomeomorph_apply n z η) μ hμ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_hasFiniteSpectralDetection (n : ℕ) :
    HasFiniteSpectralDetection (gammaSplitAbelianExtension n)
      {(iota n e), (epsilon n e)} (2 / 7 : ℝ) :=
  gamma_hasFiniteSpectralDetection_of_measureGap n
    (gamma_probability_detection_gap n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_hasKazhdanPropertyT_unconditional (n : ℕ)
    (hUniversalLattice : ErshovJaikinUniversalLatticePropertyT) :
    HasKazhdanPropertyT (gammaGroup n) := by
  classical
  let : MeasurableSpace (DiscreteCharacterSpace (E n)) :=
    borel (DiscreteCharacterSpace (E n))
  let : BorelSpace (DiscreteCharacterSpace (E n)) := ⟨rfl⟩
  exact spectral_criterion_unconditional
    (gammaSplitAbelianExtension n)
    (actingGroup_hasKazhdanPropertyT hUniversalLattice)
    {(iota n e), (epsilon n e)}
    (by norm_num)
    (gamma_hasFiniteSpectralDetection n)

end

section

open ConnesRigidity
open scoped ENNReal

section

universe u v

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def l2CurryFiber {ι : Type u} {κ : Type v}
    (ξ : GroupL2 (ι × κ)) (i : ι) : GroupL2 κ :=
  ⟨fun k => ξ (i, k), by
    change Memℓp (fun k => ξ (i, k)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact ((lp.memℓp ξ).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).prod_factor i⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem l2Curry_mem {ι : Type u} {κ : Type v}
    (ξ : GroupL2 (ι × κ)) :
    (fun i => l2CurryFiber ξ i) ∈ lp (fun _ : ι => GroupL2 κ) 2 := by
  change Memℓp (fun i => l2CurryFiber ξ i) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have hprod : Summable (fun p : ι × κ =>
      ‖ξ p‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  apply hprod.prod.congr
  intro i
  rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem l2Uncurry_mem {ι : Type u} {κ : Type v}
    (ξ : lp (fun _ : ι => GroupL2 κ) 2) :
    (fun p : ι × κ => ξ p.1 p.2) ∈ GroupL2 (ι × κ) := by
  change Memℓp (fun p : ι × κ => ξ p.1 p.2) 2
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  apply (summable_prod_of_nonneg (fun _ => by positivity)).2
  constructor
  · intro i
    exact (lp.memℓp (ξ i)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  · have hout : Summable (fun i =>
        ‖ξ i‖ ^ (2 : ℝ≥0∞).toReal) :=
      (lp.memℓp ξ).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    convert hout using 1
    funext i
    rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def l2Curry (ι : Type u) (κ : Type v) :
    GroupL2 (ι × κ) ≃ₗᵢ[ℂ] lp (fun _ : ι => GroupL2 κ) 2 where
  toLinearEquiv :=
    { toFun := fun ξ => ⟨fun i => l2CurryFiber ξ i, l2Curry_mem ξ⟩
      invFun := fun ξ => ⟨fun p => ξ p.1 p.2, l2Uncurry_mem ξ⟩
      left_inv := by
        intro ξ
        ext p
        rfl
      right_inv := by
        intro ξ
        ext i k
        rfl
      map_add' := by
        intro ξ η
        ext i k
        rfl
      map_smul' := by
        intro c ξ
        ext i k
        rfl }
  norm_map' := by
    intro ξ
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change
      (∑' i, ‖l2CurryFiber ξ i‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) =
        (∑' p, ‖ξ p‖ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal)
    congr 1
    have hprod : Summable (fun p : ι × κ =>
        ‖ξ p‖ ^ (2 : ℝ≥0∞).toReal) :=
      (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    rw [hprod.tsum_prod]
    apply tsum_congr
    intro i
    rw [lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rfl





variable {A : Type u} {K : Type v} [Group A] [Group K]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def semidirectFubiniCoordinates (φ : K →* MulAut A) :
    SemidirectProduct A K φ ≃ K × A :=
  SemidirectProduct.equivProd.trans (Equiv.prodComm A K)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def semidirectFubini (φ : K →* MulAut A) :
    GroupL2 (SemidirectProduct A K φ) ≃ₗᵢ[ℂ]
      lp (fun _ : K => GroupL2 A) 2 :=
  (l2Reindex (semidirectFubiniCoordinates φ)).trans (l2Curry K A)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem semidirectFubini_apply
    (φ : K →* MulAut A)
    (ξ : GroupL2 (SemidirectProduct A K φ)) (k : K) (a : A) :
    semidirectFubini φ ξ k a =
      ξ (⟨a, k⟩ : SemidirectProduct A K φ) := rfl



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectFubini_leftRegular_apply
    (φ : K →* MulAut A)
    (g : SemidirectProduct A K φ)
    (ξ : GroupL2 (SemidirectProduct A K φ))
    (k : K) (a : A) :
    semidirectFubini φ
        ((leftRegularUnitary g :
          GroupL2 (SemidirectProduct A K φ) →L[ℂ]
            GroupL2 (SemidirectProduct A K φ)) ξ) k a =
      semidirectFubini φ ξ (g.right⁻¹ * k)
        (φ g.right⁻¹ (g.left⁻¹ * a)) := by
  change ξ ⟨φ g.right⁻¹ g.left⁻¹ * φ g.right⁻¹ a,
    g.right⁻¹ * k⟩ = ξ ⟨φ g.right⁻¹ (g.left⁻¹ * a),
      g.right⁻¹ * k⟩
  rw [map_mul]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectFubini_leftRegular_inl_apply
    (φ : K →* MulAut A) (b : A)
    (ξ : GroupL2 (SemidirectProduct A K φ))
    (k : K) (a : A) :
    semidirectFubini φ
        ((leftRegularUnitary
          (SemidirectProduct.inl b : SemidirectProduct A K φ) :
          GroupL2 (SemidirectProduct A K φ) →L[ℂ]
            GroupL2 (SemidirectProduct A K φ)) ξ) k a =
      semidirectFubini φ ξ k (b⁻¹ * a) := by
  simpa only [semidirectFubini_apply, leftRegularUnitary_apply, SemidirectProduct.mk_eq_inl_mul_inr,
    map_mul, map_inv, SemidirectProduct.right_inl, inv_one, one_mul, SemidirectProduct.left_inl,
    map_one, MulAut.one_apply] using semidirectFubini_leftRegular_apply φ
    (SemidirectProduct.inl b) ξ k a

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirectFubini_leftRegular_inr_apply
    (φ : K →* MulAut A) (h : K)
    (ξ : GroupL2 (SemidirectProduct A K φ))
    (k : K) (a : A) :
    semidirectFubini φ
        ((leftRegularUnitary
          (SemidirectProduct.inr h : SemidirectProduct A K φ) :
          GroupL2 (SemidirectProduct A K φ) →L[ℂ]
            GroupL2 (SemidirectProduct A K φ)) ξ) k a =
      semidirectFubini φ ξ (h⁻¹ * k) (φ h⁻¹ a) := by
  simpa only [semidirectFubini_apply, leftRegularUnitary_apply, SemidirectProduct.mk_eq_inl_mul_inr,
    map_inv, MulAut.inv_apply, map_mul, SemidirectProduct.right_inr, SemidirectProduct.left_inr,
    inv_one, one_mul] using semidirectFubini_leftRegular_apply φ
    (SemidirectProduct.inr h) ξ k a







end

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal

section

universe u v w

variable {A : Type u} [AddCommGroup A]
variable {H : Type v} [Group H]
variable {Ω : Type w} [AddCommGroup Ω] [TopologicalSpace Ω]
  [MeasurableSpace Ω]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def normalFourierCoordinates
    (X : HaarProbabilityAction H Ω)
    (F : GroupL2 A ≃ₗᵢ[ℂ] crossedBaseHilbert X) :
    GroupL2 (Multiplicative A) ≃ₗᵢ[ℂ] crossedBaseHilbert X :=
  (l2Reindex (Multiplicative.toAdd : Multiplicative A ≃ A)).trans F

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def groupFactorUnitary
    (φ : H →* MulAut (Multiplicative A))
    (X : HaarProbabilityAction H Ω)
    (F : GroupL2 A ≃ₗᵢ[ℂ] crossedBaseHilbert X) :
    GroupL2 (SemidirectProduct (Multiplicative A) H φ) ≃ₗᵢ[ℂ]
      crossedHilbert X :=
  (semidirectFubini φ).trans
    (crossedFiberwiseEquiv (K := H) (normalFourierCoordinates X F))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem groupFactorUnitary_apply
    (φ : H →* MulAut (Multiplicative A))
    (X : HaarProbabilityAction H Ω)
    (F : GroupL2 A ≃ₗᵢ[ℂ] crossedBaseHilbert X)
    (ξ : GroupL2 (SemidirectProduct (Multiplicative A) H φ))
    (h : H) :
    groupFactorUnitary φ X F ξ h =
      F ((l2Reindex (Multiplicative.toAdd : Multiplicative A ≃ A))
        (semidirectFubini φ ξ h)) := rfl





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem groupFactorUnitary_conj_inl
    (φ : H →* MulAut (Multiplicative A))
    (X : HaarProbabilityAction H Ω)
    (F : GroupL2 A ≃ₗᵢ[ℂ] crossedBaseHilbert X)
    (a : A) :
    (groupFactorUnitary φ X F).conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd a) :
          SemidirectProduct (Multiplicative A) H φ) :
            GroupL2 (SemidirectProduct (Multiplicative A) H φ) →L[ℂ]
              GroupL2 (SemidirectProduct (Multiplicative A) H φ)) =
      crossedFiberwiseOperator (K := H)
        ((normalFourierCoordinates X F).conjStarAlgEquiv
          (leftRegularUnitary (Multiplicative.ofAdd a) :
            GroupL2 (Multiplicative A) →L[ℂ]
              GroupL2 (Multiplicative A))) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext h
  change normalFourierCoordinates X F
      (semidirectFubini φ
        ((leftRegularUnitary
          (SemidirectProduct.inl (Multiplicative.ofAdd a) :
            SemidirectProduct (Multiplicative A) H φ) :
              GroupL2 (SemidirectProduct (Multiplicative A) H φ) →L[ℂ]
                GroupL2 (SemidirectProduct (Multiplicative A) H φ))
          ((groupFactorUnitary φ X F).symm ξ)) h) =
      normalFourierCoordinates X F
        ((leftRegularUnitary (Multiplicative.ofAdd a) :
          GroupL2 (Multiplicative A) →L[ℂ]
            GroupL2 (Multiplicative A))
          ((normalFourierCoordinates X F).symm (ξ h)))
  congr 1
  ext b
  rw [semidirectFubini_leftRegular_inl_apply]
  change (semidirectFubini φ
      ((groupFactorUnitary φ X F).symm ξ) h)
        ((Multiplicative.ofAdd a)⁻¹ * b) =
      ((normalFourierCoordinates X F).symm (ξ h))
        ((Multiplicative.ofAdd a)⁻¹ * b)
  congr 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def gammaGroupFactorUnitary (n : ℕ) :
    GroupL2 (gammaGroup n) ≃ₗᵢ[ℂ]
      crossedHilbert (paperCarryHaarAction n) :=
  groupFactorUnitary (kEAction n) (paperCarryHaarAction n)
    (carryFourierEquiv n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def lambdaGroupFactorUnitary :
    GroupL2 lambdaGroup ≃ₗᵢ[ℂ]
      crossedHilbert paperSplitHaarAction := by
  change GroupL2 (SemidirectProduct (Multiplicative D) K kDAction) ≃ₗᵢ[ℂ]
    crossedHilbert paperSplitHaarAction
  exact groupFactorUnitary kDAction paperSplitHaarAction splitFourierEquiv

end

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitComplexCharacter_kDLinear (k : K) (d : D) (z : X × Y) :
    splitComplexCharacter (kDLinear k d) z =
      splitComplexCharacter d (paperSplitHaarAction.action k⁻¹ z) := by
  change
    (ZMod.toCircle
      (z.1 (kLinear k d.1) + z.2 (kDividedSquareLinear k d.2)) : ℂ) =
      (ZMod.toCircle
        ((kXLinear k⁻¹ z.1) d.1 +
          (kYLinear k⁻¹ z.2) d.2) : ℂ)
  simp only [kXLinear_apply, kYLinear_apply, inv_inv]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitCharacterL2_kDLinear (k : K) (d : D) :
    splitCharacterL2 (kDLinear k d) =
      crossedActionL2Equiv paperSplitHaarAction k (splitCharacterL2 d) := by
  let hp : MeasurePreserving
      (paperSplitPerm k⁻¹ : X × Y → X × Y) productHaar productHaar :=
    paperSplitHaarAction.action_preserves_measure k⁻¹
  change splitCharacterL2 (kDLinear k d) =
    Lp.compMeasurePreserving (paperSplitPerm k⁻¹) hp (splitCharacterL2 d)
  apply Lp.ext
  have hsource := ContinuousMap.coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := productHaar) (𝕜 := ℂ)
      (splitComplexCharacter d)
  have hsource' := hp.quasiMeasurePreserving.ae_eq_comp hsource
  have htarget := ContinuousMap.coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := productHaar) (𝕜 := ℂ)
      (splitComplexCharacter (kDLinear k d))
  filter_upwards [htarget,
    Lp.coeFn_compMeasurePreserving (splitCharacterL2 d) hp,
    hsource'] with z htarget hcomp hsource'
  calc
    splitCharacterL2 (kDLinear k d) z =
        splitComplexCharacter (kDLinear k d) z := htarget
    _ = splitComplexCharacter d (paperSplitPerm k⁻¹ z) :=
      splitComplexCharacter_kDLinear k d z
    _ = splitCharacterL2 d (paperSplitPerm k⁻¹ z) := hsource'.symm
    _ = Lp.compMeasurePreserving (paperSplitPerm k⁻¹) hp
        (splitCharacterL2 d) z := hcomp.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitL2Reindex_single [DecidableEq D]
    (k : K) (d : D) (c : ℂ) :
    l2Reindex (kDLinear k).toEquiv (lp.single 2 d c) =
      lp.single 2 (kDLinear k d) c := by
  ext e
  simp only [l2Reindex_apply, lp.single_apply, Pi.single_apply,
    Equiv.symm_apply_eq]
  rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitFourierEquiv_single_smul [DecidableEq D]
    (d : D) (c : ℂ) :
    splitFourierEquiv (lp.single 2 d c) = c • splitCharacterL2 d := by
  classical
  have hsingle : lp.single (E := fun _ : D => ℂ) 2 d c =
      c • lp.single (E := fun _ : D => ℂ) 2 d (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using (lp.single_smul (E := fun _ : D => ℂ) 2 d c (1 : ℂ))
  rw [hsingle, map_smul, splitFourierEquiv_single]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitCharacterL2_zero :
    splitCharacterL2 0 = Lp.const 2 productHaar (1 : ℂ) := by
  apply Lp.ext
  filter_upwards [
    ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := productHaar) (𝕜 := ℂ) (splitComplexCharacter 0),
    Lp.coeFn_const (μ := productHaar) (p := 2) (1 : ℂ)]
    with z hcharacter hone
  calc
    splitCharacterL2 0 z = splitComplexCharacter 0 z := hcharacter
    _ = 1 := by rw [splitComplexCharacter_zero]; rfl
    _ = Lp.const 2 productHaar (1 : ℂ) z := hone.symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitFourierEquiv_zero_single [DecidableEq D] :
    splitFourierEquiv (lp.single 2 (0 : D) (1 : ℂ)) =
      Lp.const 2 productHaar (1 : ℂ) :=
  (splitFourierEquiv_single (0 : D)).trans splitCharacterL2_zero

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitFourierEquiv_kDLinear (k : K) (ξ : GroupL2 D) :
    splitFourierEquiv (l2Reindex (kDLinear k).toEquiv ξ) =
      crossedActionL2Equiv paperSplitHaarAction k
        (splitFourierEquiv ξ) := by
  classical
  let left : GroupL2 D →L[ℂ] Lp ℂ 2 productHaar :=
    splitFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (l2Reindex (kDLinear k).toEquiv).toContinuousLinearEquiv.toContinuousLinearMap
  let right : GroupL2 D →L[ℂ] Lp ℂ 2 productHaar :=
    (crossedActionL2Equiv paperSplitHaarAction k).toContinuousLinearEquiv.toContinuousLinearMap.comp
      splitFourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h : left = right := by
    apply lp.ext_continuousLinearMap (by simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true])
    intro d
    apply ContinuousLinearMap.ext
    intro c
    change splitFourierEquiv
        (l2Reindex (kDLinear k).toEquiv (lp.single 2 d c)) =
      crossedActionL2Equiv paperSplitHaarAction k
        (splitFourierEquiv (lp.single 2 d c))
    rw [splitL2Reindex_single, splitFourierEquiv_single_smul,
      splitFourierEquiv_single_smul]
    let hp : MeasurePreserving
        (paperSplitPerm k⁻¹ : X × Y → X × Y) productHaar productHaar :=
      paperSplitHaarAction.action_preserves_measure k⁻¹
    change c • splitCharacterL2 (kDLinear k d) =
      (Lp.compMeasurePreservingₗ ℂ (paperSplitPerm k⁻¹) hp)
        (c • splitCharacterL2 d)
    rw [map_smul]
    exact congrArg (fun x : Lp ℂ 2 productHaar => c • x)
      (splitCharacterL2_kDLinear k d)
  exact DFunLike.congr_fun h ξ

end

section


open ConnesRigidity MeasureTheory
open scoped ENNReal

section

universe u v w

variable {A : Type u} [AddCommGroup A]
variable {H : Type v} [Group H]
variable {Ω : Type w} [AddCommGroup Ω] [TopologicalSpace Ω]
  [MeasurableSpace Ω]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem groupFactorUnitary_conj_inr
    (φ : H →* MulAut (Multiplicative A))
    (X : HaarProbabilityAction H Ω)
    (F : GroupL2 A ≃ₗᵢ[ℂ] crossedBaseHilbert X)
    (hcov : ∀ (k : H) (ξ : GroupL2 (Multiplicative A)),
      normalFourierCoordinates X F
        (l2Reindex (φ k).toEquiv ξ) =
      crossedActionL2Equiv X k (normalFourierCoordinates X F ξ))
    (k : H) :
    (groupFactorUnitary φ X F).conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr k :
          SemidirectProduct (Multiplicative A) H φ) :
          GroupL2 (SemidirectProduct (Multiplicative A) H φ) →L[ℂ]
            GroupL2 (SemidirectProduct (Multiplicative A) H φ)) =
      (crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply lp.ext
  funext h
  change normalFourierCoordinates X F
      (semidirectFubini φ
        ((leftRegularUnitary
          (SemidirectProduct.inr k :
            SemidirectProduct (Multiplicative A) H φ) :
            GroupL2 (SemidirectProduct (Multiplicative A) H φ) →L[ℂ]
              GroupL2 (SemidirectProduct (Multiplicative A) H φ))
          ((groupFactorUnitary φ X F).symm ξ)) h) =
      crossedActionL2Equiv X k (ξ (k⁻¹ * h))
  have hnormal :
      semidirectFubini φ
        ((leftRegularUnitary
          (SemidirectProduct.inr k :
            SemidirectProduct (Multiplicative A) H φ) :
            GroupL2 (SemidirectProduct (Multiplicative A) H φ) →L[ℂ]
              GroupL2 (SemidirectProduct (Multiplicative A) H φ))
          ((groupFactorUnitary φ X F).symm ξ)) h =
      l2Reindex (φ k).toEquiv
        (semidirectFubini φ ((groupFactorUnitary φ X F).symm ξ)
          (k⁻¹ * h)) := by
    ext a
    rw [semidirectFubini_leftRegular_inr_apply, l2Reindex_apply]
    apply congrArg (fun b : Multiplicative A =>
      (semidirectFubini φ
        ((groupFactorUnitary φ X F).symm ξ) (k⁻¹ * h)) b)
    change φ k⁻¹ a = (φ k).symm a
    rw [map_inv]
    rfl
  rw [hnormal, hcov]
  congr 1
  exact congrArg (fun z => z (k⁻¹ * h))
    ((groupFactorUnitary φ X F).apply_symm_apply ξ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem carryTaggedFourierCovariance (n : ℕ) (k : K)
    (ξ : GroupL2 (Multiplicative (E n))) :
    normalFourierCoordinates (paperCarryHaarAction n) (carryFourierEquiv n)
      (l2Reindex (kEAction n k).toEquiv ξ) =
      crossedActionL2Equiv (paperCarryHaarAction n) k
        (normalFourierCoordinates (paperCarryHaarAction n)
          (carryFourierEquiv n) ξ) := by
  change
    carryFourierEquiv n
      (l2Reindex (Multiplicative.toAdd : Multiplicative (E n) ≃ E n)
        (l2Reindex (kEAction n k).toEquiv ξ)) =
      crossedActionL2Equiv (paperCarryHaarAction n) k
        (carryFourierEquiv n
          (l2Reindex (Multiplicative.toAdd : Multiplicative (E n) ≃ E n) ξ))
  have hreindex :
      l2Reindex (Multiplicative.toAdd : Multiplicative (E n) ≃ E n)
        (l2Reindex (kEAction n k).toEquiv ξ) =
      l2Reindex (carryEAddAction n k).toEquiv
        (l2Reindex (Multiplicative.toAdd : Multiplicative (E n) ≃ E n) ξ) := by
    ext η
    rfl
  rw [hreindex]
  exact carryFourier_kEAction n k
    (l2Reindex (Multiplicative.toAdd : Multiplicative (E n) ≃ E n) ξ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitTaggedFourierCovariance (k : K)
    (ξ : GroupL2 (Multiplicative D)) :
    normalFourierCoordinates paperSplitHaarAction splitFourierEquiv
      (l2Reindex (kDAction k).toEquiv ξ) =
      crossedActionL2Equiv paperSplitHaarAction k
        (normalFourierCoordinates paperSplitHaarAction splitFourierEquiv ξ) := by
  change
    splitFourierEquiv
      (l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D)
        (l2Reindex (kDAction k).toEquiv ξ)) =
      crossedActionL2Equiv paperSplitHaarAction k
        (splitFourierEquiv
          (l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D) ξ))
  have hreindex :
      l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D)
        (l2Reindex (kDAction k).toEquiv ξ) =
      l2Reindex (kDLinear k).toEquiv
        (l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D) ξ) := by
    ext d
    rfl
  rw [hreindex]
  exact splitFourierEquiv_kDLinear k
    (l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D) ξ)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaGroupFactorUnitary_conj_inr (n : ℕ) (k : K) :
    (gammaGroupFactorUnitary n).conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr k : Gamma n) :
          GroupL2 (Gamma n) →L[ℂ] GroupL2 (Gamma n)) =
      (crossedGroupUnitary
        (paperCarryHaarAction n) k).toContinuousLinearEquiv.toContinuousLinearMap := by
  change
    (groupFactorUnitary (kEAction n) (paperCarryHaarAction n)
      (carryFourierEquiv n)).conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr k :
          SemidirectProduct (Multiplicative (E n)) K (kEAction n)) :
          GroupL2 (SemidirectProduct (Multiplicative (E n)) K (kEAction n))
            →L[ℂ]
          GroupL2 (SemidirectProduct (Multiplicative (E n)) K (kEAction n))) =
      (crossedGroupUnitary (paperCarryHaarAction n) k).toContinuousLinearEquiv.toContinuousLinearMap
  exact groupFactorUnitary_conj_inr
    (kEAction n) (paperCarryHaarAction n) (carryFourierEquiv n)
    (carryTaggedFourierCovariance n) k

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaGroupFactorUnitary_conj_inr (k : K) :
    lambdaGroupFactorUnitary.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr k : Lambda) :
          GroupL2 Lambda →L[ℂ] GroupL2 Lambda) =
      (crossedGroupUnitary
        paperSplitHaarAction k).toContinuousLinearEquiv.toContinuousLinearMap := by
  change
    (groupFactorUnitary kDAction paperSplitHaarAction splitFourierEquiv).conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr k :
          SemidirectProduct (Multiplicative D) K kDAction) :
          GroupL2 (SemidirectProduct (Multiplicative D) K kDAction)
            →L[ℂ]
          GroupL2 (SemidirectProduct (Multiplicative D) K kDAction)) =
      (crossedGroupUnitary paperSplitHaarAction k).toContinuousLinearEquiv.toContinuousLinearMap
  apply groupFactorUnitary_conj_inr
  exact splitTaggedFourierCovariance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaGroupFactorUnitary_conj_inl (n : ℕ) (η : E n) :
    (gammaGroupFactorUnitary n).conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd η) : Gamma n) :
          GroupL2 (Gamma n) →L[ℂ] GroupL2 (Gamma n)) =
      crossedMultiplier (paperCarryHaarAction n)
        (carryCharacterCoefficient n η) := by
  calc
    _ = crossedFiberwiseOperator (K := K)
        ((normalFourierCoordinates (paperCarryHaarAction n)
          (carryFourierEquiv n)).conjStarAlgEquiv
            (leftRegularUnitary (Multiplicative.ofAdd η) :
              GroupL2 (Multiplicative (E n)) →L[ℂ]
                GroupL2 (Multiplicative (E n)))) :=
      groupFactorUnitary_conj_inl (A := E n) (H := K)
        (kEAction n) (paperCarryHaarAction n) (carryFourierEquiv n) η
    _ = crossedMultiplier (paperCarryHaarAction n)
        (carryCharacterCoefficient n η) := by
      change crossedFiberwiseOperator (K := K) _ =
        crossedFiberwiseOperator (K := K) _
      congr 1
      exact carryFourier_conjugates_normal_generator n η

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem split_normalFourierCoordinates_eq :
    normalFourierCoordinates paperSplitHaarAction splitFourierEquiv =
      splitFourierEquiv := by
  apply LinearIsometryEquiv.ext
  intro ξ
  congr 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaGroupFactorUnitary_conj_inl (d : D) :
    lambdaGroupFactorUnitary.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd d) : Lambda) :
          GroupL2 Lambda →L[ℂ] GroupL2 Lambda) =
      crossedMultiplier paperSplitHaarAction
        (splitCharacterCoefficient d) := by
  calc
    _ = crossedFiberwiseOperator (K := K)
        ((normalFourierCoordinates paperSplitHaarAction
          splitFourierEquiv).conjStarAlgEquiv
            (leftRegularUnitary (Multiplicative.ofAdd d) :
              GroupL2 (Multiplicative D) →L[ℂ]
                GroupL2 (Multiplicative D))) :=
      groupFactorUnitary_conj_inl (A := D) (H := K)
        kDAction paperSplitHaarAction splitFourierEquiv d
    _ = crossedMultiplier paperSplitHaarAction
        (splitCharacterCoefficient d) := by
      change crossedFiberwiseOperator (K := K) _ =
        crossedFiberwiseOperator (K := K) _
      congr 1
      rw [split_normalFourierCoordinates_eq]
      exact splitFourier_conjugates_normal_generator d

end

end

section

open ConnesRigidity

universe u v w x

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure PaperFactorUnitaryWitness
    (G : CountableDiscreteGroup.{u})
    (H : CountableDiscreteGroup.{v}) where
  unitary : GroupL2 G ≃ₗᵢ[ℂ] GroupL2 H
  maps_group_factor :
    ∀ T : GroupL2 G →L[ℂ] GroupL2 G,
      T ∈ groupVonNeumannAlgebra G ↔
        unitary.conjStarAlgEquiv T ∈ groupVonNeumannAlgebra H
  maps_vacuum : unitary (delta G 1) = delta H 1

namespace PaperFactorUnitaryWitness

variable {G : CountableDiscreteGroup.{u}}
variable {H : CountableDiscreteGroup.{v}}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def toStarAlgEquiv (U : PaperFactorUnitaryWitness G H) :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ]
      GroupVonNeumannAlgebra H where
  toFun x :=
    ⟨U.unitary.conjStarAlgEquiv x,
      (U.maps_group_factor x).mp x.property⟩
  invFun y :=
    ⟨U.unitary.conjStarAlgEquiv.symm y, by
      apply (U.maps_group_factor (U.unitary.conjStarAlgEquiv.symm y)).mpr
      have h := U.unitary.conjStarAlgEquiv.apply_symm_apply
        (y : GroupL2 H →L[ℂ] GroupL2 H)
      rw [h]
      exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact U.unitary.conjStarAlgEquiv.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact U.unitary.conjStarAlgEquiv.apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul U.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
      (y : GroupL2 G →L[ℂ] GroupL2 G)
  map_add' x y := by
    apply Subtype.ext
    exact map_add U.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
      (y : GroupL2 G →L[ℂ] GroupL2 G)
  map_star' x := by
    apply Subtype.ext
    exact map_star U.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
  map_smul' c x := by
    apply Subtype.ext
    change
      U.unitary.conjStarAlgEquiv
        (c • (x : GroupL2 G →L[ℂ] GroupL2 G)) =
        c • U.unitary.conjStarAlgEquiv
          (x : GroupL2 G →L[ℂ] GroupL2 G)
    exact map_smul U.unitary.conjStarAlgEquiv c
      (x : GroupL2 G →L[ℂ] GroupL2 G)



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem starAlgEquiv_isNormal
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) :
    IsNormalStarAlgEquiv e := by
  have hforward : ∀ (S : Set A) (p : A),
      IsProjectionSupremum S p →
        IsProjectionSupremum (e '' S) (e p) := by
    intro S p hp
    refine ⟨hp.1.map e, ?_, ?_⟩
    · rintro q ⟨r, hr, rfl⟩
      refine ⟨(hp.2.1 r hr).1.map e, ?_⟩
      simpa only [ProjectionLE, map_mul] using congrArg e (hp.2.1 r hr).2
    · intro r hr hupper
      have hr' : IsStarProjection (e.symm r) := hr.map e.symm
      have hbound : ∀ q ∈ S, ProjectionLE q (e.symm r) := by
        intro q hq
        have h := hupper (e q) ⟨q, hq, rfl⟩
        simpa only [ProjectionLE, map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm h
      simpa only [ProjectionLE, map_mul, StarAlgEquiv.apply_symm_apply] using
        congrArg e (hp.2.2 (e.symm r) hr' hbound)
  refine ⟨hforward, ?_⟩
  intro S p hp
  have h :=
    (show ∀ (T : Set B) (q : B),
        IsProjectionSupremum T q →
          IsProjectionSupremum (e.symm '' T) (e.symm q) by
      intro T q hq
      refine ⟨hq.1.map e.symm, ?_, ?_⟩
      · rintro r ⟨s, hs, rfl⟩
        refine ⟨(hq.2.1 s hs).1.map e.symm, ?_⟩
        simpa only [ProjectionLE, map_mul] using congrArg e.symm (hq.2.1 s hs).2
      · intro r hr hupper
        have hr' : IsStarProjection (e r) := hr.map e
        have hbound : ∀ s ∈ T, ProjectionLE s (e r) := by
          intro s hs
          have hs' := hupper (e.symm s) ⟨s, hs, rfl⟩
          simpa only [ProjectionLE, map_mul, StarAlgEquiv.apply_symm_apply] using congrArg e hs'
        simpa only [ProjectionLE, map_mul, StarAlgEquiv.symm_apply_apply] using
          congrArg e.symm (hq.2.2 (e r) hr' hbound)) S p hp
  exact h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem trace_preserving (U : PaperFactorUnitaryWitness G H)
    (x : GroupVonNeumannAlgebra G) :
    canonicalTrace H (U.toStarAlgEquiv x) = canonicalTrace G x := by
  change inner ℂ (delta H 1)
      (U.unitary ((x : GroupL2 G →L[ℂ] GroupL2 G)
        (U.unitary.symm (delta H 1)))) =
    inner ℂ (delta G 1)
      ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))
  rw [← U.maps_vacuum, U.unitary.symm_apply_apply]
  exact U.unitary.inner_map_map (delta G 1)
    ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def toTracialGroupFactorEquiv
    (U : PaperFactorUnitaryWitness G H) :
    TracialGroupFactorEquiv G H where
  toStarAlgEquiv := U.toStarAlgEquiv
  normal := starAlgEquiv_isNormal U.toStarAlgEquiv
  trace_preserving := U.trace_preserving

end PaperFactorUnitaryWitness

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure PointedVonNeumannModel
    (ℋ : Type u)
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] where
  algebra : VonNeumannAlgebra ℋ
  vacuum : ℋ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def crossedPointedModel
    {J : Type u} [Group J]
    {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    (A : HaarProbabilityAction J Ω) :
    PointedVonNeumannModel (crossedHilbert A) where
  algebra := (crossedProductModel A).algebra
  vacuum := crossedVacuum A

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure SpatialGroupFactorPresentation
    (G : CountableDiscreteGroup.{u})
    {ℋ : Type v}
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    (M : PointedVonNeumannModel ℋ) where
  unitary : GroupL2 G ≃ₗᵢ[ℂ] ℋ
  maps_group_factor :
    ∀ T : GroupL2 G →L[ℂ] GroupL2 G,
      T ∈ groupVonNeumannAlgebra G ↔
        unitary.conjStarAlgEquiv T ∈ M.algebra
  maps_vacuum : unitary (delta G 1) = M.vacuum

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure SpatialVonNeumannTransport
    {ℋ : Type u} {𝒦 : Type v}
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
    (M : PointedVonNeumannModel ℋ)
    (N : PointedVonNeumannModel 𝒦) where
  unitary : ℋ ≃ₗᵢ[ℂ] 𝒦
  maps_algebra :
    ∀ T : ℋ →L[ℂ] ℋ,
      T ∈ M.algebra ↔ unitary.conjStarAlgEquiv T ∈ N.algebra
  maps_vacuum : unitary M.vacuum = N.vacuum

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def spatialCrossedTransport
    {J : Type u} [Group J]
    {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
    {Ξ : Type w} [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]
    {A : HaarProbabilityAction J Ω}
    {B : HaarProbabilityAction J Ξ}
    (e : EquivariantHaarEquiv A B) :
    SpatialVonNeumannTransport
      (crossedPointedModel A) (crossedPointedModel B) where
  unitary := crossedHaarHilbertEquiv e
  maps_algebra := crossedHaarHilbertEquiv_mem_algebra_iff e
  maps_vacuum := crossedHaarHilbertEquiv_vacuum e

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperHaarTransport (n : ℕ) :
    SpatialVonNeumannTransport
      (crossedPointedModel (paperCarryHaarAction n))
      (crossedPointedModel paperSplitHaarAction) :=
  spatialCrossedTransport (paperCommonHaarEquiv n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def factorUnitaryWitness_of_spatialPresentations
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    {ℋ : Type w} {𝒦 : Type x}
    [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
    [NormedAddCommGroup 𝒦] [InnerProductSpace ℂ 𝒦] [CompleteSpace 𝒦]
    {M : PointedVonNeumannModel ℋ}
    {N : PointedVonNeumannModel 𝒦}
    (γ : SpatialGroupFactorPresentation G M)
    (lambdaPresentation : SpatialGroupFactorPresentation H N)
    (transport : SpatialVonNeumannTransport M N) :
    PaperFactorUnitaryWitness G H where
  unitary := γ.unitary.trans
    (transport.unitary.trans lambdaPresentation.unitary.symm)
  maps_group_factor := by
    intro T
    have hconj :
        (γ.unitary.trans
          (transport.unitary.trans lambdaPresentation.unitary.symm)).conjStarAlgEquiv
            T =
          lambdaPresentation.unitary.conjStarAlgEquiv.symm
            (transport.unitary.conjStarAlgEquiv
              (γ.unitary.conjStarAlgEquiv T)) := by
      rw [LinearIsometryEquiv.conjStarAlgEquiv_trans,
        LinearIsometryEquiv.conjStarAlgEquiv_trans,
        LinearIsometryEquiv.symm_conjStarAlgEquiv]
      rfl
    rw [hconj]
    calc
      T ∈ groupVonNeumannAlgebra G ↔
          γ.unitary.conjStarAlgEquiv T ∈ M.algebra :=
        γ.maps_group_factor T
      _ ↔ transport.unitary.conjStarAlgEquiv
          (γ.unitary.conjStarAlgEquiv T) ∈ N.algebra :=
        transport.maps_algebra (γ.unitary.conjStarAlgEquiv T)
      _ ↔ lambdaPresentation.unitary.conjStarAlgEquiv.symm
          (transport.unitary.conjStarAlgEquiv
            (γ.unitary.conjStarAlgEquiv T)) ∈
            groupVonNeumannAlgebra H := by
        symm
        rw [lambdaPresentation.maps_group_factor]
        rw [lambdaPresentation.unitary.conjStarAlgEquiv.apply_symm_apply]
  maps_vacuum := by
    change lambdaPresentation.unitary.symm
      (transport.unitary (γ.unitary (delta G 1))) = delta H 1
    rw [γ.maps_vacuum, transport.maps_vacuum,
      ← lambdaPresentation.maps_vacuum,
      lambdaPresentation.unitary.symm_apply_apply]

end

end

section

open ConnesRigidity

section

universe u

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem vonNeumannClosure_eq_of_factor_generators
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (S T : Set (H →L[ℂ] H))
    (hsub : T ⊆ S)
    (hfactor : ∀ x ∈ S, ∃ a ∈ T, ∃ b ∈ T, x = a * b) :
    vonNeumannClosure S = vonNeumannClosure T := by
  have hcent : StarSubalgebra.centralizer ℂ S =
      StarSubalgebra.centralizer ℂ T := by
    ext z
    simp only [StarSubalgebra.mem_centralizer_iff]
    constructor
    · intro hz x hx
      exact hz x (hsub hx)
    · intro hz x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hfactor x hx
      obtain ⟨ha₀, ha₁⟩ := hz a ha
      obtain ⟨hb₀, hb₁⟩ := hz b hb
      constructor
      · calc
          (a * b) * z = a * (b * z) := by rw [mul_assoc]
          _ = a * (z * b) := by rw [hb₀]
          _ = (a * z) * b := by rw [mul_assoc]
          _ = (z * a) * b := by rw [ha₀]
          _ = z * (a * b) := by rw [mul_assoc]
      · rw [star_mul]
        calc
          (star b * star a) * z = star b * (star a * z) := by rw [mul_assoc]
          _ = star b * (z * star a) := by rw [ha₁]
          _ = (star b * z) * star a := by rw [mul_assoc]
          _ = (z * star b) * star a := by rw [hb₁]
          _ = z * (star b * star a) := by rw [mul_assoc]
  apply VonNeumannAlgebra.ext
  intro z
  change z ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H)) ↔
    z ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ T : Set (H →L[ℂ] H))
  rw [hcent]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirect_vonNeumannClosure_eq_inl_inr
    {A K : Type u} [Group A] [Group K] (φ : K →* MulAut A) :
    vonNeumannClosure
      (Set.range fun x : A ⋊[φ] K =>
        (leftRegularRepresentation (A ⋊[φ] K) x :
          GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K))) =
      vonNeumannClosure
        ((Set.range fun a : A =>
          (leftRegularRepresentation (A ⋊[φ] K)
            (SemidirectProduct.inl a) :
            GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K))) ∪
        (Set.range fun k : K =>
          (leftRegularRepresentation (A ⋊[φ] K)
            (SemidirectProduct.inr k) :
            GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K)))) := by
  apply vonNeumannClosure_eq_of_factor_generators
  · rintro _ (⟨a, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨SemidirectProduct.inl a, rfl⟩
    · exact ⟨SemidirectProduct.inr k, rfl⟩
  · rintro _ ⟨g, rfl⟩
    refine ⟨(leftRegularRepresentation (A ⋊[φ] K)
        (SemidirectProduct.inl g.left) :
        GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K)),
      Or.inl ⟨g.left, rfl⟩,
      (leftRegularRepresentation (A ⋊[φ] K)
        (SemidirectProduct.inr g.right) :
        GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K)),
      Or.inr ⟨g.right, rfl⟩, ?_⟩
    change
      (leftRegularRepresentation (A ⋊[φ] K) g :
        GroupL2 (A ⋊[φ] K) →L[ℂ] GroupL2 (A ⋊[φ] K)) = _
    conv_lhs =>
      rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [map_mul]
    rfl

end

end

section

open ConnesRigidity MeasureTheory
open scoped ENNReal

section


universe u v w

variable {A : Type u} [AddCommGroup A]
variable {H : Type v} [Group H]
variable {Ω : Type w} [AddCommGroup Ω] [TopologicalSpace Ω]
  [MeasurableSpace Ω]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem delta_eq_single (G : CountableDiscreteGroup)
    [d : DecidableEq G] (g : G) :
    delta G g = lp.single 2 g (1 : ℂ) := by
  have heq : d = Classical.decEq G := Subsingleton.elim _ _
  cases heq
  rfl

open Classical in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem groupFactorUnitary_vacuum
    (φ : H →* MulAut (Multiplicative A))
    (X : HaarProbabilityAction H Ω)
    (F : GroupL2 A ≃ₗᵢ[ℂ] crossedBaseHilbert X)
    (hF : letI : IsProbabilityMeasure X.measure := X.probability
      F (lp.single 2 (0 : A) (1 : ℂ)) = Lp.const 2 X.measure (1 : ℂ)) :
    groupFactorUnitary φ X F
        (lp.single 2 (1 : SemidirectProduct (Multiplicative A) H φ) (1 : ℂ)) =
      crossedVacuum X := by
  classical
  let : IsProbabilityMeasure X.measure := X.probability
  apply lp.ext
  funext h
  rw [groupFactorUnitary_apply]
  by_cases hh : h = 1
  · subst h
    have hcoord :
        l2Reindex (Multiplicative.toAdd : Multiplicative A ≃ A)
            (semidirectFubini φ
              (lp.single 2 (1 : SemidirectProduct (Multiplicative A) H φ)
                (1 : ℂ)) 1) =
          lp.single 2 (0 : A) (1 : ℂ) := by
      ext a
      simp only [l2Reindex_apply, Multiplicative.toAdd_symm_eq, semidirectFubini_apply,
        lp.single_apply, SemidirectProduct.mk_eq_inl_mul_inr, map_one, mul_one, Pi.single_apply,
        SemidirectProduct.ext_iff, SemidirectProduct.left_inl, SemidirectProduct.one_left,
        ofAdd_eq_one, SemidirectProduct.right_inl, SemidirectProduct.one_right, and_true]
    rw [hcoord, hF]
    simp only [crossedVacuum, lp.single_apply, Pi.single_eq_same]
  · have hcoord :
        l2Reindex (Multiplicative.toAdd : Multiplicative A ≃ A)
            (semidirectFubini φ
              (lp.single 2 (1 : SemidirectProduct (Multiplicative A) H φ)
                (1 : ℂ)) h) = 0 := by
      ext a
      simp only [l2Reindex_apply, Multiplicative.toAdd_symm_eq, semidirectFubini_apply,
        lp.single_apply, SemidirectProduct.mk_eq_inl_mul_inr, ne_eq, SemidirectProduct.ext_iff,
        SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
        map_one, SemidirectProduct.left_inr, mul_one, SemidirectProduct.one_left, ofAdd_eq_one,
        SemidirectProduct.mul_right, SemidirectProduct.right_inr, one_mul,
        SemidirectProduct.one_right, hh, and_false, not_false_eq_true, Pi.single_eq_of_ne,
        ZeroMemClass.coe_zero, PreLp.zero_apply]
    rw [hcoord, map_zero]
    simp only [crossedVacuum, lp.single_apply, ne_eq, hh, not_false_eq_true, Pi.single_eq_of_ne]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gammaGroupFactorUnitary_vacuum (n : ℕ) :
    gammaGroupFactorUnitary n (delta (gammaGroup n) 1) =
      crossedVacuum (paperCarryHaarAction n) := by
  change
    groupFactorUnitary (kEAction n) (paperCarryHaarAction n)
      (carryFourierEquiv n) (delta (gammaGroup n) 1) =
        crossedVacuum (paperCarryHaarAction n)
  rw [@delta_eq_single (gammaGroup n)
    (@instDecidableEqSemidirectProduct (Multiplicative (E n)) K _ _
      (kEAction n) (Classical.decEq _) (Classical.decEq _)) 1]
  exact groupFactorUnitary_vacuum (kEAction n)
    (paperCarryHaarAction n) (carryFourierEquiv n)
    (@carryFourierEquiv_zero_single n (Classical.decEq (E n)))

open Classical in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaDelta_apply (g : Lambda) :
    delta lambdaGroup 1 (show lambdaGroup from g) =
      if g = (1 : Lambda) then 1 else 0 := by
  classical
  rw [delta_eq_single lambdaGroup (1 : lambdaGroup)]
  by_cases hg : g = (1 : Lambda)
  · subst g
    rw [ite_eq_left rfl]
    exact lp.single_apply_self (E := fun _ : lambdaGroup => ℂ)
      2 (1 : lambdaGroup) (1 : ℂ)
  · rw [ite_eq_right hg]
    exact lp.single_apply_ne (E := fun _ : lambdaGroup => ℂ)
      2 (1 : lambdaGroup) (1 : ℂ) hg

open Classical in
/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem splitVacuum_apply (k : K) :
  crossedVacuum paperSplitHaarAction k =
      if k = 1 then Lp.const 2 productHaar (1 : ℂ) else 0 := by
  classical
  by_cases hk : k = (1 : K)
  · subst k
    rw [ite_eq_left rfl]
    change
      (@lp.single K (fun _ ↦ Lp ℂ 2 productHaar) _
        (fun a b ↦ Classical.propDecidable (a = b))
        2 (1 : K) (Lp.const 2 productHaar (1 : ℂ))) 1 =
          Lp.const 2 productHaar (1 : ℂ)
    exact @lp.single_apply_self K (fun _ ↦ Lp ℂ 2 productHaar) _
      (fun a b ↦ Classical.propDecidable (a = b))
      2 (1 : K) (Lp.const 2 productHaar (1 : ℂ))
  · rw [ite_eq_right hk]
    change
      (@lp.single K (fun _ ↦ Lp ℂ 2 productHaar) _
        (fun a b ↦ Classical.propDecidable (a = b))
        2 (1 : K) (Lp.const 2 productHaar (1 : ℂ))) k = 0
    exact @lp.single_apply_ne K (fun _ ↦ Lp ℂ 2 productHaar) _
      (fun a b ↦ Classical.propDecidable (a = b))
      2 (1 : K) (Lp.const 2 productHaar (1 : ℂ)) k hk

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaGroupFactorUnitary_vacuum :
    lambdaGroupFactorUnitary (delta lambdaGroup 1) =
      crossedVacuum paperSplitHaarAction := by
  classical
  apply lp.ext
  funext k
  change
    splitFourierEquiv
      (l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D)
        (semidirectFubini (A := Multiplicative D) (K := K)
          kDAction (delta lambdaGroup 1) k)) =
      crossedVacuum paperSplitHaarAction k
  by_cases hk : k = 1
  · subst k
    have hfiber :
        l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D)
            (semidirectFubini (A := Multiplicative D) (K := K)
              kDAction (delta lambdaGroup 1) 1) =
          lp.single 2 (0 : D) (1 : ℂ) := by
      ext d
      change delta lambdaGroup 1
        (⟨Multiplicative.ofAdd d, 1⟩ : Lambda) =
        (lp.single (E := fun _ : D => ℂ) 2 (0 : D) (1 : ℂ)) d
      rw [lambdaDelta_apply]
      by_cases hd : d = 0
      · subst d
        have hpoint : (⟨Multiplicative.ofAdd (0 : D), 1⟩ : Lambda) = 1 := by
          apply SemidirectProduct.ext <;> rfl
        rw [ite_eq_left hpoint]
        exact (lp.single_apply_self (E := fun _ : D => ℂ)
          2 (0 : D) (1 : ℂ)).symm
      · have hpoint :
            (⟨Multiplicative.ofAdd d, 1⟩ : Lambda) ≠ 1 := by
          intro hpoint
          apply hd
          have hleft := congrArg
            (fun g : Lambda => Multiplicative.toAdd g.left) hpoint
          simpa only [toAdd_ofAdd, SemidirectProduct.one_left, toAdd_one] using hleft
        rw [ite_eq_right hpoint]
        exact (lp.single_apply_ne (E := fun _ : D => ℂ)
          2 (0 : D) (1 : ℂ) hd).symm
    rw [hfiber, splitFourierEquiv_zero_single]
    rw [splitVacuum_apply, ite_eq_left rfl]
  · have hfiber :
        l2Reindex (Multiplicative.toAdd : Multiplicative D ≃ D)
            (semidirectFubini (A := Multiplicative D) (K := K)
              kDAction (delta lambdaGroup 1) k) = 0 := by
      ext d
      change delta lambdaGroup 1
        (⟨Multiplicative.ofAdd d, k⟩ : Lambda) = 0
      rw [lambdaDelta_apply]
      have hpoint :
          (⟨Multiplicative.ofAdd d, k⟩ : Lambda) ≠ 1 := by
        intro hpoint
        apply hk
        simpa only [SemidirectProduct.one_right] using congrArg SemidirectProduct.right hpoint
      rw [ite_eq_right hpoint]
    rw [hfiber, map_zero]
    rw [splitVacuum_apply, ite_eq_right hk]

end

end

section

open ConnesRigidity

section

universe u v w

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem conj_image_union_range_eq
    {H : Type u} {J : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    {ι κ : Type w}
    (U : H ≃ₗᵢ[ℂ] J)
    (A : ι → (H →L[ℂ] H)) (B : κ → (H →L[ℂ] H))
    (C : ι → (J →L[ℂ] J)) (D : κ → (J →L[ℂ] J))
    (hA : ∀ i, U.conjStarAlgEquiv (A i) = C i)
    (hB : ∀ k, U.conjStarAlgEquiv (B k) = D k) :
    U.conjStarAlgEquiv '' (Set.range A ∪ Set.range B) =
      Set.range C ∪ Set.range D := by
  ext T
  constructor
  · rintro ⟨S, (⟨i, rfl⟩ | ⟨k, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, (hA i).symm⟩
    · exact Or.inr ⟨k, (hB k).symm⟩
  · rintro (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨A i, Or.inl ⟨i, rfl⟩, hA i⟩
    · exact ⟨B k, Or.inr ⟨k, rfl⟩, hB k⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem maps_group_factor_of_two_generator_families
    (G : CountableDiscreteGroup.{u})
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι κ : Type w}
    (U : GroupL2 G ≃ₗᵢ[ℂ] H)
    (A : ι → (GroupL2 G →L[ℂ] GroupL2 G))
    (B : κ → (GroupL2 G →L[ℂ] GroupL2 G))
    (C : ι → (H →L[ℂ] H))
    (D : κ → (H →L[ℂ] H))
    (M : VonNeumannAlgebra H)
    (hgroup : groupVonNeumannAlgebra G =
      vonNeumannClosure (Set.range A ∪ Set.range B))
    (hA : ∀ i, U.conjStarAlgEquiv (A i) = C i)
    (hB : ∀ k, U.conjStarAlgEquiv (B k) = D k)
    (htarget : vonNeumannClosure (Set.range C ∪ Set.range D) = M)
    (T : GroupL2 G →L[ℂ] GroupL2 G) :
    T ∈ groupVonNeumannAlgebra G ↔ U.conjStarAlgEquiv T ∈ M := by
  rw [hgroup, ← htarget,
    ← conj_image_union_range_eq U A B C D hA hB]
  exact (conj_mem_vonNeumannClosure_image_iff
    U (Set.range A ∪ Set.range B) T).symm

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperCarryFactorPresentation (n : ℕ) :
    SpatialGroupFactorPresentation (gammaGroup n)
      (crossedPointedModel (paperCarryHaarAction n)) where
  unitary := gammaGroupFactorUnitary n
  maps_group_factor := by
    intro T
    exact maps_group_factor_of_two_generator_families
      (gammaGroup n)
      (gammaGroupFactorUnitary n)
      (fun η : E n ↦
        (leftRegularRepresentation (Gamma n)
          (SemidirectProduct.inl (Multiplicative.ofAdd η)) :
            GroupL2 (Gamma n) →L[ℂ] GroupL2 (Gamma n)))
      (fun k : K ↦
        (leftRegularRepresentation (Gamma n)
          (SemidirectProduct.inr k) :
            GroupL2 (Gamma n) →L[ℂ] GroupL2 (Gamma n)))
      (fun η : E n ↦ crossedMultiplier (paperCarryHaarAction n)
        (carryCharacterCoefficient n η))
      (fun k : K ↦
        (crossedGroupUnitary
          (paperCarryHaarAction n) k).toContinuousLinearEquiv.toContinuousLinearMap)
      (crossedProductModel (paperCarryHaarAction n)).algebra
      (by
        change
          vonNeumannClosure
            (Set.range fun g : Gamma n ↦
              (leftRegularRepresentation (Gamma n) g :
                GroupL2 (Gamma n) →L[ℂ] GroupL2 (Gamma n))) = _
        rw [semidirect_vonNeumannClosure_eq_inl_inr (kEAction n)]
        congr 1)
      (gammaGroupFactorUnitary_conj_inl n)
      (gammaGroupFactorUnitary_conj_inr n)
      (carry_character_vonNeumannClosure_eq_full n)
      T
  maps_vacuum := gammaGroupFactorUnitary_vacuum n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperSplitFactorPresentation :
    SpatialGroupFactorPresentation lambdaGroup
      (crossedPointedModel paperSplitHaarAction) where
  unitary := lambdaGroupFactorUnitary
  maps_group_factor := by
    intro T
    exact maps_group_factor_of_two_generator_families
      lambdaGroup
      lambdaGroupFactorUnitary
      (fun d : D ↦
        (leftRegularRepresentation Lambda
          (SemidirectProduct.inl (Multiplicative.ofAdd d)) :
            GroupL2 Lambda →L[ℂ] GroupL2 Lambda))
      (fun k : K ↦
        (leftRegularRepresentation Lambda
          (SemidirectProduct.inr k) :
            GroupL2 Lambda →L[ℂ] GroupL2 Lambda))
      (fun d : D ↦ crossedMultiplier paperSplitHaarAction
        (splitCharacterCoefficient d))
      (fun k : K ↦
        (crossedGroupUnitary paperSplitHaarAction k).toContinuousLinearEquiv.toContinuousLinearMap)
      (crossedProductModel paperSplitHaarAction).algebra
      (by
        change
          vonNeumannClosure
            (Set.range fun g : Lambda ↦
              (leftRegularRepresentation Lambda g :
                GroupL2 Lambda →L[ℂ] GroupL2 Lambda)) = _
        have h := @semidirect_vonNeumannClosure_eq_inl_inr
          (Multiplicative D) K
          (inferInstance : Group (Multiplicative D))
          (inferInstance : Group K) kDAction
        change
          vonNeumannClosure
            (Set.range fun g : Lambda ↦
              (leftRegularRepresentation Lambda g :
                GroupL2 Lambda →L[ℂ] GroupL2 Lambda)) = _ at h
        rw [h]
        congr 1)
      lambdaGroupFactorUnitary_conj_inl
      lambdaGroupFactorUnitary_conj_inr
      split_character_vonNeumannClosure_eq_full
      T
  maps_vacuum := lambdaGroupFactorUnitary_vacuum

end

end

section

universe u v w

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def HasNoOrderFour (G : Type u) [Group G] : Prop :=
  ∀ g : G, g ^ 4 = 1 → g ^ 2 = 1

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem orderOf_eq_four_iff {G : Type u} [Group G] (g : G) :
    orderOf g = 4 ↔ g ^ 4 = 1 ∧ g ^ 2 ≠ 1 := by
  constructor
  · intro hg
    refine ⟨?_, ?_⟩
    · simpa only [hg] using pow_orderOf_eq_one g
    · intro hsquare
      have hdiv : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hsquare
      norm_num [hg] at hdiv
  · rintro ⟨hfour, hsquare⟩
    simpa only [Nat.reduceAdd, Nat.reducePow] using
      (orderOf_eq_prime_pow (p := 2) (n := 1)
        (by simpa only [pow_one, ne_eq] using hsquare)
        (by simpa only [Nat.reduceAdd, Nat.reducePow] using hfour))

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem mem_ker_of_pow_four_eq_one_of_no_nontrivial_torsion
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (π : G →* Q)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1)
    {g : G} (hg : g ^ 4 = 1) :
    g ∈ π.ker := by
  apply MonoidHom.mem_ker.mpr
  apply hQ
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨4, by norm_num, ?_⟩
  simpa only [map_pow, map_one] using congrArg π hg

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasNoOrderFour_of_quotient_without_nontrivial_torsion
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (π : G →* Q)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1)
    (hker : ∀ g : G, g ∈ π.ker → g ^ 2 = 1) :
    HasNoOrderFour G := by
  intro g hg
  exact hker g
    (mem_ker_of_pow_four_eq_one_of_no_nontrivial_torsion π hQ hg)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem hasNoOrderFour_of_quotient_without_nontrivial_torsion_of_kernel_le_range
    {G : Type u} {Q : Type v} {N : Type w}
    [Group G] [Group Q] [Group N]
    (π : G →* Q) (ι : N →* G)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1)
    (hker : π.ker ≤ ι.range)
    (hN : ∀ n : N, n ^ 2 = 1) :
    HasNoOrderFour G := by
  apply hasNoOrderFour_of_quotient_without_nontrivial_torsion π hQ
  intro g hg
  obtain ⟨n, hn⟩ := hker hg
  subst g
  simpa only [map_pow, map_one] using congrArg ι (hN n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem semidirect_hasNoOrderFour_of_no_nontrivial_torsion_of_exponentTwo
    {N : Type u} {Q : Type v} [Group N] [Group Q]
    (φ : Q →* MulAut N)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1)
    (hN : ∀ n : N, n ^ 2 = 1) :
    HasNoOrderFour (N ⋊[φ] Q) := by
  apply hasNoOrderFour_of_quotient_without_nontrivial_torsion_of_kernel_le_range
    (SemidirectProduct.rightHom : (N ⋊[φ] Q) →* Q)
    (SemidirectProduct.inl : N →* N ⋊[φ] Q)
    hQ
  · exact le_of_eq SemidirectProduct.range_inl_eq_ker_rightHom.symm
  · exact hN

end

section

open ConnesRigidity MeasureTheory

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance spectralGapDiscreteTopology : TopologicalSpace D := ⊥

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance spectralGapDiscrete : DiscreteTopology D := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance spectralGapDualMeasurable :
    MeasurableSpace (DiscreteCharacterSpace D) :=
  borel (DiscreteCharacterSpace D)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance spectralGapDualBorel :
    BorelSpace (DiscreteCharacterSpace D) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance spectralGapPairMeasurable : MeasurableSpace (X × Y) :=
  borel (X × Y)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance spectralGapPairBorel : BorelSpace (X × Y) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem pairDualHomeomorph_zero :
    pairDualHomeomorph ((0 : X), (0 : Y)) =
      (1 : DiscreteCharacterSpace D) := by
  apply PontryaginDual.ext
  intro d
  change ZMod.toCircle ((0 : X) (Multiplicative.toAdd d).1 +
    (0 : Y) (Multiplicative.toAdd d).2) = 1
  simp only [LinearMap.zero_apply, add_zero, AddChar.map_zero_eq_one]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralPairAction_equivariance
    (k : K) (χ : DiscreteCharacterSpace D) :
    dualPointAction k (pairDualHomeomorph.symm χ) =
      pairDualHomeomorph.symm
        (dualCharacterAction moduleAddAction k χ) := by
  apply pairDualHomeomorph.injective
  rw [pairDualHomeomorph.apply_symm_apply]
  change pairDualHomeomorph
      (dualPairAction k (pairDualHomeomorph.symm χ)) =
    dualCharacterAction (A := D) (H := actingGroup)
      moduleAddAction k χ
  rw [pairDualHomeomorph_equivariant,
    pairDualHomeomorph.apply_symm_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralDualCharacterAction_continuous (k : K) :
    Continuous (dualCharacterAction (A := D) (H := actingGroup)
      moduleAddAction k) := by
  have hcont := pairDualHomeomorph.continuous.comp
    ((continuous_dualPointAction k).comp pairDualHomeomorph.symm.continuous)
  apply hcont.congr
  intro χ
  change pairDualHomeomorph
      (dualPointAction k (pairDualHomeomorph.symm χ)) =
    dualCharacterAction moduleAddAction k χ
  rw [spectralPairAction_equivariance k χ,
    pairDualHomeomorph.apply_symm_apply]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def spectralPairProbability
    (μ : ProbabilityMeasure (DiscreteCharacterSpace D)) :
    ProbabilityMeasure (X × Y) :=
  homeomorphPushProbability pairDualHomeomorph.symm μ



/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralPairProbability_invariant
    (μ : ProbabilityMeasure (DiscreteCharacterSpace D))
    (hμ : IsInvariantSpectralMeasure moduleAddAction μ) :
    IsInvariantDualProbability (spectralPairProbability μ) := by
  exact homeomorphPushProbability_invariant
    pairDualHomeomorph.symm μ
    (fun k : K ↦ dualCharacterAction moduleAddAction k)
    dualPointAction
    (fun k ↦ (spectralDualCharacterAction_continuous k).measurable)
    (fun k ↦ (continuous_dualPointAction k).measurable)
    (fun k χ ↦ (spectralPairAction_equivariance k χ).symm)
    hμ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralZeroAtom_preimage :
    pairDualHomeomorph.symm ⁻¹' ({(0, 0)} : Set (X × Y)) =
      ({1} : Set (DiscreteCharacterSpace D)) := by
  ext χ
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hχ
    calc
      χ = pairDualHomeomorph (pairDualHomeomorph.symm χ) :=
        (pairDualHomeomorph.apply_symm_apply χ).symm
      _ = pairDualHomeomorph ((0 : X), (0 : Y)) := congrArg _ hχ
      _ = 1 := pairDualHomeomorph_zero
  · intro hχ
    have hpair := congrArg pairDualHomeomorph.symm hχ
    rw [← pairDualHomeomorph_zero,
      pairDualHomeomorph.symm_apply_apply] at hpair
    exact hpair

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def spectralDetectedSet : Set (DiscreteCharacterSpace D) :=
  {χ | χ (Multiplicative.ofAdd (e, 0)) ≠ 1 ∨
    χ (Multiplicative.ofAdd (0, diagonal e)) ≠ 1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectralDetectedSet_preimage :
    pairDualHomeomorph.symm ⁻¹' dualDetectionSet e =
      spectralDetectedSet := by
  ext χ
  change
    ((dualToPair χ).1 e ≠ 0 ∨
      (dualToPair χ).2 (diagonal e) ≠ 0) ↔
    (χ (Multiplicative.ofAdd (e, 0)) ≠ 1 ∨
      χ (Multiplicative.ofAdd (0, diagonal e)) ≠ 1)
  have hlinear :
      (dualToPair χ).1 e ≠ 0 ↔
        χ (Multiplicative.ofAdd (e, 0)) ≠ 1 := by
    simpa only [dualToPair_linear_apply, ne_eq, pairToDual_dualToPair] using
      (pairToDual_linear_ne_one_iff (dualToPair χ) e).symm
  have hquadratic :
      (dualToPair χ).2 (diagonal e) ≠ 0 ↔
        χ (Multiplicative.ofAdd (0, diagonal e)) ≠ 1 := by
    simpa only [dualToPair_quadratic_apply, ne_eq, pairToDual_dualToPair] using
      (pairToDual_quadratic_ne_one_iff
        (dualToPair χ) (diagonal e)).symm
  exact or_congr hlinear hquadratic

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem spectral_probability_detection_gap
    (μ : ProbabilityMeasure (DiscreteCharacterSpace D))
    (hμ : IsInvariantSpectralMeasure moduleAddAction μ) :
    (1 / 7 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (μ : Measure (DiscreteCharacterSpace D)).real
        spectralDetectedSet := by
  let ν := spectralPairProbability μ
  have hν : IsInvariantDualProbability ν :=
    spectralPairProbability_invariant μ hμ
  have hgap := dualProbability_detection_gap ν hν
  have hatom :
      (ν : Measure (X × Y)).real ({(0, 0)} : Set (X × Y)) =
        spectralTrivialAtom μ := by
    change ((μ : Measure (DiscreteCharacterSpace D)).map
      pairDualHomeomorph.symm).real ({(0, 0)} : Set (X × Y)) = _
    rw [map_measureReal_apply pairDualHomeomorph.symm.continuous.measurable
      (isClosed_singleton.measurableSet), spectralZeroAtom_preimage]
    rfl
  have hdetected :
      (ν : Measure (X × Y)).real (dualDetectionSet e) =
        (μ : Measure (DiscreteCharacterSpace D)).real
          spectralDetectedSet := by
    change ((μ : Measure (DiscreteCharacterSpace D)).map
      pairDualHomeomorph.symm).real (dualDetectionSet e) = _
    rw [map_measureReal_apply pairDualHomeomorph.symm.continuous.measurable
      (dualDetectionSet_measurable e), spectralDetectedSet_preimage]
  rw [hatom, hdetected] at hgap
  exact hgap

end

section

open ConnesRigidity MeasureTheory

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def lambdaModuleGroup : CountableDiscreteGroup where
  Carrier := Multiplicative D
  group := inferInstance
  countable := inferInstance

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_isICC_of_infinite_module_orbits
    (hK : IsICC actingGroup)
    (hD : ∀ d : D, d ≠ 0 →
      (Set.range fun k : K ↦ kDLinear k d).Infinite) :
    IsICC lambdaGroup := by
  have horbit : ∀ a : lambdaModuleGroup, a ≠ 1 →
      (Set.range fun k : actingGroup ↦ kDAction k a).Infinite := by
    intro a ha
    have ha' : Multiplicative.toAdd a ≠ (0 : D) := by
      intro h
      apply ha
      apply Multiplicative.toAdd.injective
      exact h
    have hinfinite := hD (Multiplicative.toAdd a) ha'
    have htagged :
        (Multiplicative.ofAdd ''
          (Set.range fun k : K ↦ kDLinear k (Multiplicative.toAdd a))).Infinite :=
      hinfinite.image (by
        intro x hx y hy hxy
        exact congrArg Multiplicative.toAdd hxy)
    apply htagged.mono
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨k, ?_⟩
    apply Multiplicative.toAdd.injective
    rfl
  exact semidirect_isICC lambdaModuleGroup actingGroup kDAction hK horbit

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_isICC_of_module_orbits
    (hD : ∀ d : D, d ≠ 0 →
      (Set.range fun k : K ↦ kDLinear k d).Infinite) :
    IsICC lambdaGroup :=
  lambda_isICC_of_infinite_module_orbits actingGroup_isICC hD

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_isICC : IsICC lambdaGroup :=
  lambda_isICC_of_module_orbits k_D_orbit_infinite

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance lambdaDiscreteTopology : TopologicalSpace D := ⊥

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance lambdaDiscrete : DiscreteTopology D := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance lambdaDecidableEq : DecidableEq D := Classical.decEq _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance lambdaDualMeasurable : MeasurableSpace (DiscreteCharacterSpace D) :=
  borel (DiscreteCharacterSpace D)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance lambdaDualBorel : BorelSpace (DiscreteCharacterSpace D) := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance lambdaCircleMeasurable : MeasurableSpace Circle := borel Circle

/-- Cross-module support for the infinite Connes-rigidity construction. -/
public
local instance lambdaCircleBorel : BorelSpace Circle := ⟨rfl⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def lambdaSplitAbelianExtension :
    SplitAbelianExtension D lambdaGroup actingGroup where
  inclusion := lambdaInl
  quotient := lambdaProjection
  splitting := lambdaInr
  quotient_splitting := SemidirectProduct.rightHom_comp_inr
  exact := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  action := (MulAutMultiplicative D).toMonoidHom.comp kDAction
  conjugation k d := by
    change lambdaInr k * lambdaInl (Multiplicative.ofAdd d) *
      (lambdaInr k)⁻¹ =
        lambdaInl (Multiplicative.ofAdd
          ((Multiplicative.toAdd
            (((MulAutMultiplicative D).toMonoidHom.comp kDAction) k)) d))
    rw [← lambda_conjugation k (Multiplicative.ofAdd d)]
    rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_detectors_ne :
    (e, 0) ≠ (0, diagonal e) := by
  intro h
  apply e_ne_zero
  exact congrArg Prod.fst h

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def lambdaDetectionSet (d : D) : Set (DiscreteCharacterSpace D) :=
  {χ | χ (Multiplicative.ofAdd d) ≠ 1}

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaDetectionSet_measurable (d : D) :
    MeasurableSet (lambdaDetectionSet d) := by
  unfold lambdaDetectionSet
  have hcontinuous : Continuous
      (fun χ : DiscreteCharacterSpace D ↦ χ (Multiplicative.ofAdd d)) := by
    change Continuous (fun χ : ((Multiplicative D) →ₜ* Circle) ↦
      χ (Multiplicative.ofAdd d))
    exact continuous_eval_const _
  exact (hcontinuous.measurable (measurableSet_singleton (1 : Circle))).compl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaCharacter_sq (χ : DiscreteCharacterSpace D) (d : D) :
    (χ (Multiplicative.ofAdd d) : ℂ) ^ 2 = 1 := by
  have hcircle : χ (Multiplicative.ofAdd d) ^ 2 = 1 := by
    rw [← map_pow, pow_two]
    change χ (Multiplicative.ofAdd (d + d)) = 1
    rw [D_add_self]
    exact map_one χ
  exact congrArg (fun z : Circle ↦ (z : ℂ)) hcircle

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaCharacterEnergy_eq_indicator
    (χ : DiscreteCharacterSpace D) (d : D) :
    ‖((χ (Multiplicative.ofAdd d) : Circle) : ℂ) - 1‖ ^ 2 =
      (lambdaDetectionSet d).indicator (fun _ ↦ (4 : ℝ)) χ := by
  by_cases h : χ (Multiplicative.ofAdd d) = 1
  · simp only [h, Circle.coe_one, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, lambdaDetectionSet, Set.mem_ofPred_eq, not_true_eq_false,
      Set.indicator_of_notMem]
  · have hne : (χ (Multiplicative.ofAdd d) : ℂ) ≠ 1 := by
      intro heq
      apply h
      exact Subtype.ext heq
    have hneg : (χ (Multiplicative.ofAdd d) : ℂ) = -1 :=
      (sq_eq_one_iff.mp (lambdaCharacter_sq χ d)).resolve_left hne
    simp only [hneg, lambdaDetectionSet, ne_eq, Set.mem_ofPred_eq, h, not_false_eq_true,
      Set.indicator_of_mem]
    norm_num [Complex.norm_def]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaSpectralEnergy_eq_four_mul_measure
    (μ : ProbabilityMeasure (DiscreteCharacterSpace D)) (d : D) :
    spectralDetectionEnergy μ d =
      4 * (μ : Measure (DiscreteCharacterSpace D)).real
        (lambdaDetectionSet d) := by
  unfold spectralDetectionEnergy
  simp_rw [lambdaCharacterEnergy_eq_indicator]
  rw [integral_indicator_const _ (lambdaDetectionSet_measurable d)]
  simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn, smul_eq_mul, mul_comm]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def lambdaDetectedSet : Set (DiscreteCharacterSpace D) :=
  lambdaDetectionSet (e, 0) ∪
    lambdaDetectionSet (0, diagonal e)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambdaFourMulDetectedMass_le_energy
    (μ : ProbabilityMeasure (DiscreteCharacterSpace D)) :
    4 * (μ : Measure (DiscreteCharacterSpace D)).real lambdaDetectedSet ≤
      spectralDetectionEnergy μ (e, 0) +
        spectralDetectionEnergy μ (0, diagonal e) := by
  let μ' : Measure (DiscreteCharacterSpace D) := μ
  let S₁ := lambdaDetectionSet (e, 0)
  let S₂ := lambdaDetectionSet (0, diagonal e)
  have hs₁ : MeasurableSet S₁ :=
    lambdaDetectionSet_measurable (e, 0)
  have hs₂ : MeasurableSet S₂ :=
    lambdaDetectionSet_measurable (0, diagonal e)
  have h₁ : Integrable (S₁.indicator (fun _ ↦ (4 : ℝ))) μ' :=
    (integrable_const (μ := μ') (4 : ℝ)).indicator hs₁
  have h₂ : Integrable (S₂.indicator (fun _ ↦ (4 : ℝ))) μ' :=
    (integrable_const (μ := μ') (4 : ℝ)).indicator hs₂
  have hu : Integrable ((S₁ ∪ S₂).indicator (fun _ ↦ (4 : ℝ))) μ' :=
    (integrable_const (μ := μ') (4 : ℝ)).indicator (hs₁.union hs₂)
  calc
    4 * (μ : Measure (DiscreteCharacterSpace D)).real lambdaDetectedSet =
        ∫ χ, (S₁ ∪ S₂).indicator (fun _ ↦ (4 : ℝ)) χ ∂μ' := by
          rw [integral_indicator_const _ (hs₁.union hs₂)]
          simp only [lambdaDetectedSet, ProbabilityMeasure.measureReal_eq_coe_coeFn, smul_eq_mul,
            mul_comm, μ', S₁, S₂]
    _ ≤ ∫ χ, S₁.indicator (fun _ ↦ (4 : ℝ)) χ +
          S₂.indicator (fun _ ↦ (4 : ℝ)) χ ∂μ' := by
          apply integral_mono hu (h₁.add h₂)
          intro χ
          by_cases hχ₁ : χ ∈ S₁ <;> by_cases hχ₂ : χ ∈ S₂ <;>
            simp [hχ₁, hχ₂]
    _ = spectralDetectionEnergy μ (e, 0) +
          spectralDetectionEnergy μ (0, diagonal e) := by
          rw [integral_add h₁ h₂,
            integral_indicator_const _ hs₁,
            integral_indicator_const _ hs₂,
            lambdaSpectralEnergy_eq_four_mul_measure,
            lambdaSpectralEnergy_eq_four_mul_measure]
          simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn, smul_eq_mul, mul_comm, μ', S₁, S₂]

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_spectral_detection_gap
    (μ : ProbabilityMeasure (DiscreteCharacterSpace D))
    (hμ : IsInvariantSpectralMeasure
      lambdaSplitAbelianExtension.action μ) :
    (1 / 7 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (μ : Measure (DiscreteCharacterSpace D)).real lambdaDetectedSet := by
  change
    (1 / 7 : ℝ) * (1 - spectralTrivialAtom μ) ≤
      (μ : Measure (DiscreteCharacterSpace D)).real spectralDetectedSet
  exact spectral_probability_detection_gap μ hμ

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_hasFiniteSpectralDetection :
    HasFiniteSpectralDetection lambdaSplitAbelianExtension
      {(e, 0), (0, diagonal e)} (4 / 7 : ℝ) := by
  intro μ hμ
  have hgap := lambda_spectral_detection_gap μ hμ
  have henergy := lambdaFourMulDetectedMass_le_energy μ
  have hcombined :
      (4 / 7 : ℝ) * (1 - spectralTrivialAtom μ) ≤
        spectralDetectionEnergy μ (e, 0) +
          spectralDetectionEnergy μ (0, diagonal e) := by
    linarith
  simpa only [Finset.mem_singleton, lambda_detectors_ne, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton, ge_iff_le] using hcombined

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_hasKazhdanPropertyT_unconditional
    (hUniversalLattice : ErshovJaikinUniversalLatticePropertyT) :
    HasKazhdanPropertyT lambdaGroup :=
  spectral_criterion_unconditional
    lambdaSplitAbelianExtension
    (actingGroup_hasKazhdanPropertyT hUniversalLattice)
    {(e, 0), (0, diagonal e)} (by norm_num)
    lambda_hasFiniteSpectralDetection

end

section

open ConnesRigidity

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperFactorUnitaryWitness (n : ℕ) :
    PaperFactorUnitaryWitness (gammaGroup n) lambdaGroup :=
  factorUnitaryWitness_of_spatialPresentations
    (paperCarryFactorPresentation n)
    paperSplitFactorPresentation
    (paperHaarTransport n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperTracialGroupFactorEquiv (n : ℕ) :
    TracialGroupFactorEquiv (gammaGroup n) lambdaGroup :=
  (paperFactorUnitaryWitness n).toTracialGroupFactorEquiv

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paper_factors_isomorphic (n : ℕ) :
    TracialGroupFactorsIsomorphic (gammaGroup n) lambdaGroup :=
  ⟨paperTracialGroupFactorEquiv n⟩

end

end

section

open ConnesRigidity





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance paperDividedSquareDistribMulAction : DistribMulAction K B where
  smul k b := kDividedSquareLinear k b
  one_smul b := by
    change kDividedSquareLinear 1 b = b
    simp only [map_one, LinearEquiv.coe_one, id_eq]
  mul_smul k l b := by
    change kDividedSquareLinear (k * l) b =
      kDividedSquareLinear k (kDividedSquareLinear l b)
    rw [map_mul]
    rfl
  smul_zero k := by
    change kDividedSquareLinear k 0 = 0
    exact (kDividedSquareLinear k).map_zero
  smul_add k b c := (kDividedSquareLinear k).map_add b c

/-- Cross-module support for the infinite Connes-rigidity construction. -/
@[simp]
private theorem paperDividedSquare_smul (k : K) (b : B) :
    k • b = kDividedSquareLinear k b := rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private instance paperDualDistribMulAction (n : ℕ) : DistribMulAction K (E n) where
  smul k η := Multiplicative.toAdd
    (kEAction n k (Multiplicative.ofAdd η))
  one_smul η := by
    change Multiplicative.toAdd (kEAction n 1 (Multiplicative.ofAdd η)) = η
    rw [map_one]
    rfl
  mul_smul k l η := by
    change Multiplicative.toAdd
      (kEAction n (k * l) (Multiplicative.ofAdd η)) =
      Multiplicative.toAdd (kEAction n k
        (Multiplicative.ofAdd (Multiplicative.toAdd
          (kEAction n l (Multiplicative.ofAdd η)))))
    rw [map_mul]
    rfl
  smul_zero k := by
    change Multiplicative.toAdd (kEAction n k 1) = 0
    rw [map_one]
    rfl
  smul_add k η θ := by
    change Multiplicative.toAdd
      (kEAction n k (Multiplicative.ofAdd η * Multiplicative.ofAdd θ)) =
      Multiplicative.toAdd (kEAction n k (Multiplicative.ofAdd η)) +
        Multiplicative.toAdd (kEAction n k (Multiplicative.ofAdd θ))
    rw [map_mul]
    rfl







/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev paperTwoTorsionQuotient (n : ℕ) :=
  twoTorsionQuotient (E n) (E_four_nsmul n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private abbrev paperFiniteOrbitSubgroup (n : ℕ) :=
  finiteOrbitSubgroup K (paperTwoTorsionQuotient n)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperDividedSquare_orbit_infinite (b : B) (hb : b ≠ 0) :
    ¬(MulAction.orbit K b).Finite := by
  simpa only [MulAction.orbit, paperDividedSquare_smul,
    Set.not_finite] using k_dividedSquare_orbit_infinite b hb

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperExponentFourExtension (n : ℕ) : ExponentFourExtension V (E n) B where
  iota := iota n
  sigma := sigma n
  retraction := d.toAddMonoidHom
  shift := (shiftVector n).toAddMonoidHom
  iota_injective := iota_injective n
  sigma_surjective := sigma_surjective n
  sigma_ker := sigma_ker n
  retraction_surjective := d_surjective
  shift_injective := shiftVector_injective n
  doubling := two_nsmul_eta n

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperFiniteOrbit_card (n : ℕ) :
    Nat.card (paperFiniteOrbitSubgroup n) = 2 ^ (4 * n) := by
  let D := paperExponentFourExtension n
  exact D.finiteOrbitSubgroup_card_toB
    (fun k η => sigma_equivariant_raw n k η)
    paperDividedSquare_orbit_infinite n rfl

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperInvariant_card (n : ℕ) :
    paperGroupCardinalInvariant.value (gammaGroup n) = 2 ^ (4 * n) := by
  calc
    paperGroupCardinalInvariant.value (gammaGroup n) =
        Nat.card (paperFiniteOrbitSubgroup n) :=
      paperInvariant_semidirect_value_eq (kEAction n) (E_four_nsmul n)
        K_no_nontrivial_torsion (fun _ _ => rfl)
        (gammaGroup n) (MulEquiv.refl (Gamma n))
    _ = 2 ^ (4 * n) := paperFiniteOrbit_card n

private theorem gamma_parameter_eq_of_mulEquiv {m n : ℕ}
    (f : gammaGroup m ≃* gammaGroup n) : m = n := by
  apply two_pow_four_injective
  calc
    2 ^ (4 * m) = paperGroupCardinalInvariant.value (gammaGroup m) :=
      (paperInvariant_card m).symm
    _ = paperGroupCardinalInvariant.value (gammaGroup n) :=
      paperGroupCardinalInvariant.value_mulEquiv f
    _ = 2 ^ (4 * n) := paperInvariant_card n

private theorem gamma_pairwise_nonisomorphic {m n : ℕ} (hmn : m ≠ n) :
    ¬GroupsIsomorphic (gammaGroup m) (gammaGroup n) := by
  rintro ⟨f⟩
  exact hmn (gamma_parameter_eq_of_mulEquiv f)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private structure PaperAnalyticInput where
  suslinRelative : SuslinRelativeElementaryGeneration

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperLambda_hasNoOrderFour : HasNoOrderFour Lambda := by
  change HasNoOrderFour (SemidirectProduct (Multiplicative D) K kDAction)
  apply semidirect_hasNoOrderFour_of_no_nontrivial_torsion_of_exponentTwo
    (N := Multiplicative D) (Q := K) kDAction K_no_nontrivial_torsion
  intro d
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  change Multiplicative.toAdd d + Multiplicative.toAdd d = 0
  exact D_add_self _

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperLambda_orderOf_ne_four (g : lambdaGroup) : orderOf g ≠ 4 := by
  intro hg
  obtain ⟨hfour, htwo⟩ := (orderOf_eq_four_iff g).mp hg
  exact htwo (paperLambda_hasNoOrderFour g hfour)

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperFamilyInput_of_universalLattice
    (hUniversal : ErshovJaikinUniversalLatticePropertyT) :
    PaperFamilyInput where
  Lambda := lambdaGroup
  Gamma := gammaGroup
  invariant := paperGroupCardinalInvariant
  invariant_card := paperInvariant_card
  lambda_no_order_four := paperLambda_orderOf_ne_four
  gamma_order_four := gamma_has_order_four
  lambda_fg := hasKazhdanPropertyT_finitelyGenerated lambdaGroup
    (lambda_hasKazhdanPropertyT_unconditional hUniversal)
  gamma_fg n := hasKazhdanPropertyT_finitelyGenerated (gammaGroup n)
    (gamma_hasKazhdanPropertyT_unconditional n hUniversal)
  lambda_icc := lambda_isICC
  gamma_icc := gamma_isICC
  lambda_propertyT := lambda_hasKazhdanPropertyT_unconditional hUniversal
  gamma_propertyT n := gamma_hasKazhdanPropertyT_unconditional n hUniversal
  factors_isomorphic := paper_factors_isomorphic
  embeddings := gammaExactIndexEmbedding

namespace PaperAnalyticInput

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem universalLattice (input : PaperAnalyticInput) :
    ErshovJaikinUniversalLatticePropertyT :=
  universalLatticePropertyT_of_suslinRelative input.suslinRelative

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_propertyT (input : PaperAnalyticInput) :
    HasKazhdanPropertyT lambdaGroup :=
  lambda_hasKazhdanPropertyT_unconditional input.universalLattice

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_propertyT (input : PaperAnalyticInput) (n : ℕ) :
    HasKazhdanPropertyT (gammaGroup n) :=
  gamma_hasKazhdanPropertyT_unconditional n input.universalLattice

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem lambda_icc : IsICC lambdaGroup :=
  lambda_isICC

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem gamma_icc (n : ℕ) : IsICC (gammaGroup n) :=
  gamma_isICC n

private theorem gamma_not_isomorphic_lambda (n : ℕ) :
    ¬GroupsIsomorphic (gammaGroup n) lambdaGroup :=
  not_groupsIsomorphic_of_orderFour (gamma_has_order_four n)
    paperLambda_orderOf_ne_four

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def toPaperFamilyInput (input : PaperAnalyticInput) :
    PaperFamilyInput :=
  paperFamilyInput_of_universalLattice input.universalLattice





/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def infinitePropertyTFiber (input : PaperAnalyticInput) :
    InfinitePropertyTFiber :=
  input.toPaperFamilyInput.toInfinitePropertyTFiber





end PaperAnalyticInput

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private theorem paperAnalyticInput : PaperAnalyticInput :=
  ⟨suslinRelativeElementaryGeneration⟩

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private def paperInfinitePropertyTFiber : InfinitePropertyTFiber :=
  paperAnalyticInput.infinitePropertyTFiber

end

end ConnesRigidity

end

namespace ConnesRigidity

section

/-- Cross-module support for the infinite Connes-rigidity construction. -/
private noncomputable def manuscriptInfinitePropertyTFiber : InfinitePropertyTFiber :=
  paperInfinitePropertyTFiber

/-- There are infinitely many pairwise nonisomorphic finitely generated ICC
property-(T) groups whose tracial group factors are all isomorphic. -/
public
theorem exists_infinite_pairwise_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors :
    ∃ (Λ : ConnesRigidity.CountableDiscreteGroup.{0})
      (Γ : ℕ → ConnesRigidity.CountableDiscreteGroup.{0}),
      Group.FG Λ ∧
      (∀ n, Group.FG (Γ n)) ∧
      ConnesRigidity.IsICC Λ ∧
      (∀ n, ConnesRigidity.IsICC (Γ n)) ∧
      ConnesRigidity.HasKazhdanPropertyT Λ ∧
      (∀ n, ConnesRigidity.HasKazhdanPropertyT (Γ n)) ∧
      (∀ n, ConnesRigidity.TracialGroupFactorsIsomorphic (Γ n) Λ) ∧
      (∀ m n, ConnesRigidity.TracialGroupFactorsIsomorphic (Γ m) (Γ n)) ∧
      (∀ ⦃m n : ℕ⦄, m ≠ n →
        ¬ConnesRigidity.GroupsIsomorphic (Γ m) (Γ n)) ∧
      (∀ n, ¬ConnesRigidity.GroupsIsomorphic Λ (Γ n)) := by
  let F := manuscriptInfinitePropertyTFiber
  refine ⟨F.Lambda, F.Gamma, F.lambda_fg, F.gamma_fg,
    F.lambda_icc, F.gamma_icc, F.lambda_propertyT, F.gamma_propertyT,
    F.factors_isomorphic, ?_, ?_, F.lambda_not_isomorphic⟩
  · intro m n
    exact groupFactorsIsomorphic_trans (F.factors_isomorphic m)
      (groupFactorsIsomorphic_symm (F.factors_isomorphic n))
  · intro m n hmn
    exact F.gamma_pairwise_nonisomorphic hmn

/-- A short registry alias for the infinite Connes-rigidity counterexample theorem. -/
public
abbrev infiniteConnesRigidity :=
  exists_infinite_pairwise_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors

end

end ConnesRigidity
