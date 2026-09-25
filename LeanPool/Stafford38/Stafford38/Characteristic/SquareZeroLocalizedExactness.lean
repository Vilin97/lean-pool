/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.ConcreteSquareZeroTraceData
public import LeanPool.Stafford38.Stafford38.Characteristic.MinimalPrimeFiniteLengthLocalization
public import LeanPool.Stafford38.Stafford38.Characteristic.SquareZeroOreLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.OreLocalization.Ring


/-!
# Localization preserves the square-zero deformation sequence

Mathlib constructs the localization of a left module over a left Ore set as
`OreLocalization S N`.  Applied to the opposite deformation ring, this is the
localization of the original right module.  This file proves directly on Ore
fractions that the square-zero parameter remains exact.  It also constructs
the specialization map to the ordinary commutative localization of the
special fibre and proves that its kernel is the same parameter image.

The results are not conditional localized-exactness interfaces: the localized
module, parameter action, and specialization map are concrete constructions.
The only typeclass parameter is Mathlib's `OreSet`; its existence for the
pulled-back denominators is proved in `SquareZeroOreLocalization`.
-/

@[expose] public section

namespace Stafford38.Characteristic.SquareZeroLocalizedExactness

open Stafford38.Characteristic.SquareZeroTraceData
open Stafford38.Characteristic.SquareZeroOreLocalization

noncomputable section

universe u_k u_R u_B u_N u_G

variable {k : Type u_k} {R : Type u_R} {B : Type u_B}
variable {N : Type u_N} {G : Type u_G}
variable [Field k] [CommRing R] [Algebra k R]
variable [Ring B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
variable [SMulCommClass k Bᵐᵒᵖ N]
variable [AddCommGroup G] [Module k G] [Module R G]

variable (D : RightSquareZeroTraceData k R B N G)

/-- Denominators in the opposite deformation ring lying over `S`. -/
abbrev OppositeDenominators (S : Submonoid R) : Submonoid Bᵐᵒᵖ :=
  S.comap (oppositeSpecializationMonoidHom D)

/-- The concrete localized opposite-ring module supplied by Mathlib's Ore
localization construction. -/
abbrev LocalizedDeformationModule (S : Submonoid R)
    [OreLocalization.OreSet (OppositeDenominators D S)] :=
  OreLocalization (OppositeDenominators D S) N

/-- A pulled-back Ore denominator specializes to a denominator in `S`. -/
def denominatorMap (S : Submonoid R) :
    OppositeDenominators D S →* S where
  toFun s := ⟨oppositeSpecializationMonoidHom D s, s.property⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

section Ore

variable (S : Submonoid R)
variable [OreLocalization.OreSet (OppositeDenominators D S)]

/-- Action of the square-zero parameter on the localized module.  It is the
original opposite-ring action, extended by the Ore localization module
construction. -/
def localizedCAct :
    LocalizedDeformationModule D S →+ LocalizedDeformationModule D S where
  toFun x := MulOpposite.op D.c • x
  map_zero' := smul_zero _
  map_add' x y := smul_add _ x y

@[simp]
theorem localizedCAct_apply
    (x : LocalizedDeformationModule D S) :
    localizedCAct D S x = MulOpposite.op D.c • x :=
  rfl

/-- On a displayed Ore fraction, the localized parameter acts on its
numerator without changing its denominator. -/
theorem localizedCAct_oreDiv
    (m : N) (s : OppositeDenominators D S) :
    localizedCAct D S (m /ₒ s) =
      (MulOpposite.op D.c • m) /ₒ s := by
  change MulOpposite.op D.c • (m /ₒ s) = _
  rw [← OreLocalization.oreDiv_one_smul]
  simpa using OreLocalization.oreDiv_smul_char
    (MulOpposite.op D.c) m 1 s (MulOpposite.op D.c) s
      (show (s : Bᵐᵒᵖ) * MulOpposite.op D.c =
        MulOpposite.op D.c * s from by
          apply MulOpposite.unop_injective
          exact D.c_center.comm s.val.unop)

/-- The localized parameter still squares to zero. -/
theorem localizedCAct_sq_eq_zero
    (x : LocalizedDeformationModule D S) :
    localizedCAct D S (localizedCAct D S x) = 0 := by
  change MulOpposite.op D.c • (MulOpposite.op D.c • x) = 0
  rw [← mul_smul]
  have hc : MulOpposite.op D.c * MulOpposite.op D.c = 0 := by
    apply MulOpposite.unop_injective
    simpa [pow_two] using D.c_sq
  rw [hc, zero_smul]

/-- Ore localization preserves the exact square-zero parameter sequence:
the kernel of multiplication by `c` remains its image. -/
theorem localizedCAct_ker_eq_range :
    AddMonoidHom.ker (localizedCAct D S) =
      AddMonoidHom.range (localizedCAct D S) := by
  apply le_antisymm
  · intro x hx
    induction x using OreLocalization.ind with
    | _ m s =>
      rw [AddMonoidHom.mem_ker, localizedCAct_oreDiv] at hx
      have hfrac : (MulOpposite.op D.c • m) /ₒ s =
          (0 : N) /ₒ (1 : OppositeDenominators D S) := by
        simpa using hx
      obtain ⟨u, v, hv, huv⟩ :=
        OreLocalization.oreDiv_eq_iff.mp hfrac
      have hvc : v • (MulOpposite.op D.c • m) = 0 := by
        simpa using hv.symm
      have hcm : MulOpposite.op D.c • (v • m) = 0 := by
        rw [← mul_smul]
        rw [show MulOpposite.op D.c * v = v * MulOpposite.op D.c by
          apply MulOpposite.unop_injective
          exact (D.c_center.comm v.unop).symm]
        simpa [mul_smul] using hvc
      have hker : v • m ∈ LinearMap.ker D.cAct := by
        rw [LinearMap.mem_ker, D.cAct_apply]
        exact hcm
      rw [D.c_exact] at hker
      obtain ⟨q, hq⟩ := hker
      have hq' : MulOpposite.op D.c • q = v • m := by
        simpa [D.cAct_apply] using hq
      have hvs : v * (s : Bᵐᵒᵖ) ∈ OppositeDenominators D S := by
        rw [← huv]
        have hu1 : (u : Bᵐᵒᵖ) *
            ((1 : OppositeDenominators D S) : Bᵐᵒᵖ) = u := by simp
        rw [hu1]
        exact u.property
      let t : OppositeDenominators D S := ⟨v * s, hvs⟩
      refine ⟨q /ₒ t, ?_⟩
      rw [localizedCAct_oreDiv, hq']
      calc
        (v • m) /ₒ t = m /ₒ s := by
          symm
          exact OreLocalization.expand m s v hvs
        _ = m /ₒ s := rfl
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    rw [AddMonoidHom.mem_ker]
    exact localizedCAct_sq_eq_zero D S y

/-- Specialization of an Ore-localized deformation fraction to the ordinary
commutative localization of the special fibre. -/
def localizedSpecializationFun :
    LocalizedDeformationModule D S → LocalizedModule S G :=
  OreLocalization.liftExpand
    (fun m s => LocalizedModule.mk (D.rho m) (denominatorMap D S s))
    (by
      intro m t s hts
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      simp only [one_smul]
      have hrho : D.rho (t • m) = D.pi t.unop • D.rho m := by
        simpa using D.rho_action t.unop m
      rw [hrho]
      change
        (oppositeSpecializationMonoidHom D
            (⟨t * s, hts⟩ : OppositeDenominators D S)) • D.rho m =
          (denominatorMap D S s : R) •
            (D.pi t.unop • D.rho m)
      simp only [map_mul]
      rw [mul_smul]
      change D.pi t.unop • D.pi s.val.unop • D.rho m =
        D.pi s.val.unop • D.pi t.unop • D.rho m
      rw [smul_comm])

@[simp]
theorem localizedSpecializationFun_oreDiv
    (m : N) (s : OppositeDenominators D S) :
    localizedSpecializationFun D S (m /ₒ s) =
      LocalizedModule.mk (D.rho m) (denominatorMap D S s) :=
  rfl

/-- The localized specialization is an additive homomorphism. -/
def localizedSpecialization :
    LocalizedDeformationModule D S →+ LocalizedModule S G where
  toFun := localizedSpecializationFun D S
  map_zero' := by
    change localizedSpecializationFun D S 0 = 0
    rw [← OreLocalization.zero_oreDiv
      (1 : OppositeDenominators D S)]
    rw [localizedSpecializationFun_oreDiv]
    simp
  map_add' x y := by
    induction x using OreLocalization.ind with
    | _ m s =>
      induction y using OreLocalization.ind with
      | _ n t =>
        rw [OreLocalization.oreDiv_add_oreDiv]
        simp only [localizedSpecializationFun_oreDiv]
        rw [LocalizedModule.mk_add_mk]
        apply LocalizedModule.mk_eq.mpr
        refine ⟨1, ?_⟩
        simp only [one_smul]
        rw [map_add]
        have hm : D.rho (OreLocalization.oreDenom (s : Bᵐᵒᵖ) t • m) =
            D.pi (OreLocalization.oreDenom (s : Bᵐᵒᵖ) t).val.unop •
              D.rho m := by
          have h := D.rho_action
            (OreLocalization.oreDenom (s : Bᵐᵒᵖ) t).val.unop m
          rwa [MulOpposite.op_unop] at h
        have hn : D.rho (OreLocalization.oreNum (s : Bᵐᵒᵖ) t • n) =
            D.pi (OreLocalization.oreNum (s : Bᵐᵒᵖ) t).unop •
              D.rho n := by
          simpa using D.rho_action
            (OreLocalization.oreNum (s : Bᵐᵒᵖ) t).unop n
        rw [hm, hn]
        have hore := OreLocalization.ore_eq (s : Bᵐᵒᵖ) t
        have hab := congrArg (oppositeSpecializationMonoidHom D) hore
        simp only [map_mul] at hab ⊢
        have hab' :
            (denominatorMap D S
                (OreLocalization.oreDenom (s : Bᵐᵒᵖ) t) : R) *
                (denominatorMap D S s : R) =
              D.pi (OreLocalization.oreNum (s : Bᵐᵒᵖ) t).unop *
                (denominatorMap D S t : R) := by
          exact hab
        simp only [smul_add, Submonoid.smul_def, Submonoid.coe_mul,
          ← mul_smul]
        congr 1
        · congr 1
          rw [show D.pi
              (OreLocalization.oreDenom (s : Bᵐᵒᵖ) t).val.unop =
                (denominatorMap D S
                  (OreLocalization.oreDenom (s : Bᵐᵒᵖ) t) : R) from rfl]
          ring
        · congr 1
          calc
            (denominatorMap D S s : R) *
                  (denominatorMap D S t : R) *
                  D.pi (OreLocalization.oreNum (s : Bᵐᵒᵖ) t).unop =
                (D.pi (OreLocalization.oreNum (s : Bᵐᵒᵖ) t).unop *
                  (denominatorMap D S t : R)) *
                  (denominatorMap D S s : R) := by ring
            _ = ((denominatorMap D S
                    (OreLocalization.oreDenom (s : Bᵐᵒᵖ) t) : R) *
                  (denominatorMap D S s : R)) *
                  (denominatorMap D S s : R) := by rw [← hab']

@[simp]
theorem localizedSpecialization_apply
    (x : LocalizedDeformationModule D S) :
    localizedSpecialization D S x = localizedSpecializationFun D S x :=
  rfl

/-- Specialization remains surjective after localization.  A commutative
denominator is lifted through the surjective deformation specialization. -/
theorem localizedSpecialization_surjective :
    Function.Surjective (localizedSpecialization D S) := by
  intro y
  induction y using LocalizedModule.induction_on with
  | _ g s =>
    obtain ⟨m, hm⟩ := D.rho_surjective g
    obtain ⟨b, hb⟩ := D.pi_surjective (s : R)
    have hbS : oppositeSpecializationMonoidHom D (MulOpposite.op b) ∈ S := by
      change D.pi b ∈ S
      rw [hb]
      exact s.property
    let t : OppositeDenominators D S := ⟨MulOpposite.op b, hbS⟩
    have hden : denominatorMap D S t = s := by
      apply Subtype.ext
      exact hb
    refine ⟨m /ₒ t, ?_⟩
    rw [localizedSpecialization_apply,
      localizedSpecializationFun_oreDiv, hm, hden]

/-- The localized specialization kills the localized parameter image. -/
theorem localizedSpecialization_localizedCAct_eq_zero
    (x : LocalizedDeformationModule D S) :
    localizedSpecialization D S (localizedCAct D S x) = 0 := by
  induction x using OreLocalization.ind with
  | _ m s =>
    rw [localizedCAct_oreDiv, localizedSpecialization_apply,
      localizedSpecializationFun_oreDiv]
    have hrho : D.rho (MulOpposite.op D.c • m) = 0 := by
      rw [D.rho_action, D.pi_c, zero_smul]
    rw [hrho, LocalizedModule.zero_mk]

/-- The specialization kernel after Ore localization is exactly the image of
the localized square-zero parameter. -/
theorem localizedSpecialization_ker_eq_range :
    AddMonoidHom.ker (localizedSpecialization D S) =
      AddMonoidHom.range (localizedCAct D S) := by
  apply le_antisymm
  · intro x hx
    induction x using OreLocalization.ind with
    | _ m s =>
      rw [AddMonoidHom.mem_ker, localizedSpecialization_apply,
        localizedSpecializationFun_oreDiv] at hx
      have hzero :
          LocalizedModule.mk (D.rho m) (denominatorMap D S s) =
            LocalizedModule.mk (0 : G) (1 : S) := by
        simpa using hx
      obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hzero
      have hurho' : u • D.rho m = 0 := by
        simpa using hu
      have hurho : (u : R) • D.rho m = 0 := hurho'
      obtain ⟨b, hb⟩ := D.pi_surjective (u : R)
      let v : Bᵐᵒᵖ := MulOpposite.op b
      have hvrho : D.rho (v • m) = 0 := by
        have h := D.rho_action b m
        change D.rho (v • m) = D.pi b • D.rho m at h
        rw [h, hb]
        exact hurho
      have hvker : v • m ∈ LinearMap.ker D.rho := by
        exact LinearMap.mem_ker.mpr hvrho
      rw [D.rho_ker] at hvker
      obtain ⟨q, hq⟩ := hvker
      have hq' : MulOpposite.op D.c • q = v • m := by
        simpa [D.cAct_apply] using hq
      have hvS : v ∈ OppositeDenominators D S := by
        change D.pi b ∈ S
        rw [hb]
        exact u.property
      have hvs : v * (s : Bᵐᵒᵖ) ∈ OppositeDenominators D S :=
        mul_mem hvS s.property
      let t : OppositeDenominators D S := ⟨v * s, hvs⟩
      refine ⟨q /ₒ t, ?_⟩
      rw [localizedCAct_oreDiv, hq']
      symm
      exact OreLocalization.expand m s v hvs
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    rw [AddMonoidHom.mem_ker]
    exact localizedSpecialization_localizedCAct_eq_zero D S y

/-- Quotienting the localized deformation module by the parameter image gives
the ordinary commutative localization of the special fibre. -/
noncomputable def localizedSpecialFibreAddEquiv :
    (LocalizedDeformationModule D S ⧸
        AddMonoidHom.range (localizedCAct D S)) ≃+
      LocalizedModule S G :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (localizedSpecialization_ker_eq_range D S).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (localizedSpecialization D S)
      (localizedSpecialization_surjective D S))

/-- The complete localized exactness package needed by the local trace
argument: both parameter exactness and specialization exactness hold, and the
specialization is onto the ordinary localized special fibre. -/
theorem localized_squareZero_exactness :
    AddMonoidHom.ker (localizedCAct D S) =
        AddMonoidHom.range (localizedCAct D S) ∧
      Function.Surjective (localizedSpecialization D S) ∧
      AddMonoidHom.ker (localizedSpecialization D S) =
        AddMonoidHom.range (localizedCAct D S) :=
  ⟨localizedCAct_ker_eq_range D S,
    localizedSpecialization_surjective D S,
    localizedSpecialization_ker_eq_range D S⟩


end Ore

/-- Exactness for one explicit choice of Mathlib's pulled-back Ore-set
structure.  This packages only already constructed maps and equations. -/
def LocalizedExactnessFor (S : Submonoid R)
    (h : OreLocalization.OreSet (OppositeDenominators D S)) : Prop :=
  letI := h
  AddMonoidHom.ker (localizedCAct D S) =
      AddMonoidHom.range (localizedCAct D S) ∧
    Function.Surjective (localizedSpecialization D S) ∧
    AddMonoidHom.ker (localizedSpecialization D S) =
      AddMonoidHom.range (localizedCAct D S)

/-- The Ore-set existence theorem and the fraction-level exactness proof
together produce a genuine localized deformation sequence for every
multiplicative set in the special fibre. -/
theorem exists_localizedExactnessFor (S : Submonoid R) :
    ∃ h : OreLocalization.OreSet (OppositeDenominators D S),
      LocalizedExactnessFor D S h := by
  obtain ⟨h⟩ := nonempty_oreSet_comap_op D S
  refine ⟨h, ?_⟩
  let := h
  exact localized_squareZero_exactness D S

/-- At a minimal prime over the special-fibre annihilator, the localized
deformation exact sequence exists and its commutative special fibre is
simultaneously nonzero and of finite length. -/
theorem exists_minimalPrimeLocalizedExactnessAndFiniteLength
    [IsNoetherianRing R] [Module.Finite R G]
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Module.annihilator R G).minimalPrimes) :
    ∃ h : OreLocalization.OreSet
        (OppositeDenominators D P.primeCompl),
      LocalizedExactnessFor D P.primeCompl h ∧
        Nontrivial (LocalizedModule P.primeCompl G) ∧
        IsFiniteLength (Localization P.primeCompl)
          (LocalizedModule P.primeCompl G) := by
  obtain ⟨h, hexact⟩ := exists_localizedExactnessFor D P.primeCompl
  refine ⟨h, hexact, ?_⟩
  exact
    MinimalPrimeFiniteLengthLocalization.localizedModule_nontrivial_and_isFiniteLength
    P hP


end

end Stafford38.Characteristic.SquareZeroLocalizedExactness

namespace Stafford38.CharacteristicConcreteSquareZeroTraceData

open Stafford38.Characteristic.SquareZeroLocalizedExactness
open Stafford38.EulerSurjectivity
open Stafford38.WeylIteratedEquivalence

noncomputable section

universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- The concrete filtered Weyl two-jet admits a localized exact deformation
sequence at every prime of its commutative symbol ring. -/
theorem exists_primeLocalizedExactness
    (I : RightIdeal (PresentedWeyl k n))
    (P : Ideal (Stafford38.Characteristic.SymbolRing k n)) [P.IsPrime] :
    ∃ h : OreLocalization.OreSet
        (OppositeDenominators (filteredQuotientTwoJetTraceData k I)
          P.primeCompl),
      LocalizedExactnessFor (filteredQuotientTwoJetTraceData k I)
        P.primeCompl h :=
  exists_localizedExactnessFor
    (filteredQuotientTwoJetTraceData k I) P.primeCompl


end


end Stafford38.CharacteristicConcreteSquareZeroTraceData
