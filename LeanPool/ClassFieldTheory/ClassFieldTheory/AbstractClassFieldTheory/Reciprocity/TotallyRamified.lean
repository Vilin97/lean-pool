/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core

/-! # Totally Ramified -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# The abstract reciprocity theorem: the totally ramified calculation

This file isolates the calculation.  The input from the finite reciprocity equivalence is an
  equality in an actual finite norm quotient.  Such an equality is
first turned into an equality of actual norms.  For the cyclic totally
ramified extension `M / M⁰`, the class-field axiom then supplies the element `a` with
`aᵒ-a = v-u`.  The element written in this construction as
`π_L^k v a^(1-σ_tilde)` is descended from `A_M` to the actual fixed group
`A_{M⁰}`, and its valuation is computed to be `k`.  The final invocation of
the valuation endpoint in the reciprocity reduction exact row therefore gives `k = 0`.

The only comparison not made in this file is the finite reciprocity equivalence
identification of a reciprocity value with the prime-norm class.  No
compatibility record or theorem-shaped certificate is introduced for that
comparison.
-/

noncomputable
section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-! ## The linear calculation behind the fixed element -/

/-- The additive form of the calculation.  Here `g` is `σ`, `t`
is `σ_tilde`, `c = π_Σ^k`, and `b = π_L^k v`.  The hypotheses say
that `t` fixes `c`, that `g` and `t` have the same action on `b`, and that
`b-c = a^g-a`.  Commutativity of the cyclic quotient then shows that
`b+a-a^t` is fixed by `g`. -/
private theorem abstractReciprocity_fixedCombination
    {Q : IntegralRepGroupType} [CommGroup Q] (M : Rep ℤ Q)
    (g t : Q) (c b a : M.V)
    (htc : M.ρ t c = c)
    (hgb : M.ρ g b = M.ρ t b)
    (hbc : b - c = M.ρ g a - a) :
    M.ρ g (b + a - M.ρ t a) = b + a - M.ρ t a := by
  have hcomm : M.ρ g (M.ρ t a) = M.ρ t (M.ρ g a) := by
    calc
      M.ρ g (M.ρ t a) = M.ρ (g * t) a := by
        rw [map_mul]
        rfl
      _ = M.ρ (t * g) a := by rw [mul_comm]
      _ = M.ρ t (M.ρ g a) := by
        rw [map_mul]
        rfl
  have hb : b = c + M.ρ g a - a := by
    calc
      b = (b - c) + c := by abel
      _ = (M.ρ g a - a) + c := by rw [hbc]
      _ = c + M.ρ g a - a := by abel
  have htbc := congrArg (fun z : M.V ↦ M.ρ t z) hbc
  have htbc' : M.ρ t b - c =
      M.ρ t (M.ρ g a) - M.ρ t a := by
    simpa only [map_sub, htc] using htbc
  have htb : M.ρ t b =
      c + M.ρ t (M.ρ g a) - M.ρ t a := by
    calc
      M.ρ t b = (M.ρ t b - c) + c := by abel
      _ = (M.ρ t (M.ρ g a) - M.ρ t a) + c := by rw [htbc']
      _ = c + M.ρ t (M.ρ g a) - M.ρ t a := by abel
  calc
    M.ρ g (b + a - M.ρ t a) =
        M.ρ g b + M.ρ g a - M.ρ g (M.ρ t a) := by
      simp only [map_add, map_sub]
    _ = M.ρ t b + M.ρ g a - M.ρ t (M.ρ g a) := by
      rw [hgb, hcomm]
    _ = c + M.ρ g a - M.ρ t a := by rw [htb]; abel
    _ = b + a - M.ρ t a := by rw [hb]; abel

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The representative extracted from a zero prime-norm class can be
written as `π_L^k v` with an actual unit `v ∈ U_L`.  This is the
prime/valuation calculation: both
`L / K` and the Frobenius fixed field `Σ / K` have relative residue
degree one. -/
theorem primeNormClass_eq_zero_exists_unit_norm_eq
    (v : ValuationData D A)
    (K L S : FiniteAbstractField G)
    (hLK : L.field.toSubgroup ≤ K.field.toSubgroup)
    (hSK : S.field.toSubgroup ≤ K.field.toSubgroup)
    (hTot : (DegreeData.AbstractExtension.mk
      L.field K.field hLK).IsTotallyRamified D)
    [hLKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field hLK)]
    [hSKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S.field hSK)]
    (hSigmaResidue :
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        S.field K.field hSK).residueDegree D : ℕ) = 1)
    (k : ℕ)
    (piS : ambientFixedAddSubgroup A S.field)
    (piL : ambientFixedAddSubgroup A L.field)
    (hpiS : v.IsPrimeElement S piS)
    (hpiL : v.IsPrimeElement L piL)
    (hclass :
      finiteNormClass A K.field L.field hLK
          (relativeNorm A K.field S.field hSK (k • piS)) = 0) :
    ∃ w : v.unitAddSubgroup L,
      relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field S.field hSK (k • piS) := by
  obtain ⟨b, hb⟩ :=
    (finiteNormClass_eq_zero_iff
      A K.field L.field hLK _).1 hclass
  let EL : FiniteAbstractFieldExtension G :=
    { field := L
      base := K
      below := hLK
      finiteQuotient := hLKfinite }
  let ES : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion S.field K hSK
  have hvalB : v.valuationAt L b = k • v.oneValue := by
    apply Subtype.ext
    have hL := v.normalizedValuation_tower EL b
    have hS := v.normalizedValuation_tower ES (k • piS)
    have hTotEL : EL.IsTotallyRamified D := by
      simpa [EL, FiniteAbstractFieldExtension.IsTotallyRamified,
        FiniteAbstractFieldExtension.toFiniteAbstractExtension] using hTot
    have hresidue : (EL.residueDegree D : ℕ) = 1 :=
      EL.toFiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified
        D hTotEL
    change (EL.residueDegree D : ℕ) •
        ((v.valuationAt L b : v.valueGroup) : ZHat) =
      ((v.valuationAt K (relativeNorm A K.field L.field hLK b) :
        v.valueGroup) : ZHat) at hL
    rw [hresidue, one_nsmul] at hL
    have hSigmaResidue' : (ES.residueDegree D : ℕ) = 1 := by
      let ES₀ :=
        DegreeData.FiniteAbstractExtension.ofInclusion S.field K.field hSK
      have hSigmaCard :
          ES₀.toAbstractExtension.relativeResidueDegreeCardinal D = 1 := by
        calc
          ES₀.toAbstractExtension.relativeResidueDegreeCardinal D =
              ((ES₀.residueDegree D : ℕ) : Cardinal) :=
            ES₀.relativeResidueDegreeCardinal_eq_coe D
          _ = 1 := by rw [hSigmaResidue]; simp
      apply Nat.cast_injective (R := Cardinal)
      unfold FiniteAbstractFieldExtension.residueDegree
      rw [← ES.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D]
      simpa [ES, ES₀, FiniteAbstractFieldExtension.toFiniteAbstractExtension,
        FiniteAbstractFieldExtension.ofInclusion,
        DegreeData.FiniteAbstractExtension.toAbstractExtension,
        DegreeData.FiniteAbstractExtension.ofInclusion] using hSigmaCard
    change (ES.residueDegree D : ℕ) •
        ((v.valuationAt S (k • piS) : v.valueGroup) : ZHat) =
      ((v.valuationAt K
        (relativeNorm A K.field S.field hSK (k • piS)) :
          v.valueGroup) : ZHat) at hS
    rw [hSigmaResidue', one_nsmul] at hS
    calc
      ((v.valuationAt L b : v.valueGroup) : ZHat) =
          ((v.valuationAt K (relativeNorm A K.field L.field hLK b) :
            v.valueGroup) : ZHat) := hL
      _ = ((v.valuationAt K
          (relativeNorm A K.field S.field hSK (k • piS)) :
            v.valueGroup) : ZHat) := by rw [hb]
      _ = ((v.valuationAt S (k • piS) : v.valueGroup) : ZHat) := hS.symm
      _ = ((k • v.oneValue : v.valueGroup) : ZHat) := by
        congr 1
        rw [map_nsmul, hpiS]
  let wL : ambientFixedAddSubgroup A L.field := b - k • piL
  have hw : v.valuationAt L wL = 0 := by
    change v.valuationAt L (b - k • piL) = 0
    rw [map_sub, map_nsmul, hvalB, hpiL, sub_self]
  let w : v.unitAddSubgroup L :=
    ⟨wL, (v.mem_unitAddSubgroup_iff L wL).2 hw⟩
  refine ⟨w, ?_⟩
  calc
    relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field L.field hLK b := by
      congr 1
      apply Subtype.ext
      dsimp [w, wL]
      abel
    _ = relativeNorm A K.field S.field hSK (k • piS) := hb

/-- Normalized valuation is invariant under the actual quotient action.
This is the quotient-representation form of the unit-cohomology axiom's
`valuationAt_normalExtensionAction`. -/
theorem valuationAt_extensionFixedRepresentation_action
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (q : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (a : (extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal).V) :
    v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ q a)) =
      v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal a) := by
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro r
  let aL : ambientFixedAddSubgroup A E.field.field :=
    extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal a
  have heq :
      extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ
            (QuotientGroup.mk r) a) =
        normalExtensionAction A E.base.field E.field.field E.below
          hnormal r aL := by
    apply Subtype.ext
    rfl
  rw [heq]
  exact v.valuationAt_normalExtensionAction E hnormal r aL

/-- The class-field axiom, in representative form: equality of two actual relative
norms yields the element `a` for which `a^σ-a = v-u`. -/
theorem abstractReciprocity_exists_hMinusOne_primitive
    (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (u w : ambientFixedAddSubgroup A E.field.field)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w =
      relativeNorm A E.base.field E.field.field E.below u) :
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ a : M.V,
      M.ρ g a - a =
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal).symm
          (w - u) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  let M := extensionFixedRepresentation A E.base.field E.field.field
    E.below hnormal
  let z : M.V :=
    (extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal).symm (w - u)
  have hzNorm : M.norm.hom z = 0 := by
    apply Subtype.ext
    calc
      (M.norm.hom z).1 =
          ((relativeNorm A E.base.field E.field.field E.below (w - u) :
            ambientFixedAddSubgroup A E.base.field) : A.V) :=
        extensionFixedRepresentation_norm_coe A E.base.field E.field.field
          E.below hnormal z
      _ = ((relativeNorm A E.base.field E.field.field E.below w -
          relativeNorm A E.base.field E.field.field E.below u :
            ambientFixedAddSubgroup A E.base.field) : A.V) := by
        rw [map_sub]
      _ = 0 := by rw [hnorm, sub_self]; rfl
  let Ecf : FiniteCyclicSubextension E.base :=
    { field := E.field.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  have hzero : Limits.IsZero (tateCohomology M (-1)) := by
    simpa [Ecf,
      FiniteCyclicSubextension.fixedRepresentation] using
        hcf.tateHMinusOne_isZero E.base Ecf
  obtain ⟨a, ha⟩ :=
    CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
      M g hg hzero z hzNorm
  exact ⟨a, ha⟩

/-- The full source-producing calculation.  It returns both the
`H⁻¹` primitive `a` and an actual element of `A_K` (with `K = M⁰` and
`L = M`) whose inclusion has normalized valuation `k`.

The two action equations are not comparison data: they are the literal
claims used in this construction, namely that `σ_tilde` fixes `π_Σ`, and that `σ` and
`σ_tilde` have the same action on the element coming from `L`. -/
theorem abstractReciprocity_totallyRamified_fixedSource
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (t : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (k : ℕ)
    (piSigma piL u : ambientFixedAddSubgroup A E.field.field)
    (w : v.unitAddSubgroup E.field)
    (hpiL : v.IsPrimeElement E.field piL)
    (hprime : k • piSigma = u + k • piL)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w.1 =
      relativeNorm A E.base.field E.field.field E.below u)
    (htSigma : relativeCosetAction A E.base.field E.field.field
      E.below piSigma t = piSigma.1)
    (hgt : relativeCosetAction A E.base.field E.field.field E.below
        (k • piL + w.1) g =
      relativeCosetAction A E.base.field E.field.field E.below
        (k • piL + w.1) t) :
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ (a : M.V) (x : ambientFixedAddSubgroup A E.base.field),
      fixedFieldInclusion A E.base.field E.field.field E.below x =
          extensionFixedRepresentationEquiv A E.base.field E.field.field
            E.below hnormal
            ((extensionFixedRepresentationEquiv A E.base.field E.field.field
              E.below hnormal).symm
                (k • piL + w.1) + a - M.ρ t a) ∧
        ((v.valuationAt E.field
          (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ZHat) =
          Int.castRingHom ZHat (k : ℤ) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
  let : IsCyclic
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
    isCyclic_of_generator g hg
  let : CommGroup
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A E.base.field E.field.field
    E.below hnormal
  let e := extensionFixedRepresentationEquiv A E.base.field E.field.field
    E.below hnormal
  let piSigmaM : M.V := e.symm piSigma
  let piLM : M.V := e.symm piL
  let uM : M.V := e.symm u
  let wM : M.V := e.symm w.1
  obtain ⟨a, ha⟩ :=
    abstractReciprocity_exists_hMinusOne_primitive hcf E hnormal
      g hg u w.1 hnorm
  have hSigmaM : M.ρ t piSigmaM = piSigmaM := by
    apply Subtype.ext
    calc
      (M.ρ t piSigmaM).1 =
          relativeCosetAction A E.base.field E.field.field E.below piSigma t := by
        simpa [M, e, piSigmaM] using
          extensionFixedRepresentation_action_coe
            A E.base.field E.field.field E.below hnormal t piSigmaM
      _ = piSigma.1 := htSigma
      _ = piSigmaM.1 := rfl
  have hSigmaPow : M.ρ t (k • piSigmaM) = k • piSigmaM := by
    calc
      M.ρ t (k • piSigmaM) = k • M.ρ t piSigmaM :=
        map_nsmul (M.ρ t) k piSigmaM
      _ = k • piSigmaM := by rw [hSigmaM]
  let bM : M.V := k • piLM + wM
  have hbAction : M.ρ g bM = M.ρ t bM := by
    apply Subtype.ext
    calc
      (M.ρ g bM).1 =
          relativeCosetAction A E.base.field E.field.field E.below
            (k • piL + w.1) g := by
        simpa [M, e, bM, piLM, wM] using
          extensionFixedRepresentation_action_coe A E.base.field E.field.field
            E.below hnormal g bM
      _ = relativeCosetAction A E.base.field E.field.field E.below
          (k • piL + w.1) t := hgt
      _ = (M.ρ t bM).1 := by
        simpa [M, e, bM, piLM, wM] using
          (extensionFixedRepresentation_action_coe
            A E.base.field E.field.field E.below hnormal t bM).symm
  have hbc : bM - k • piSigmaM = M.ρ g a - a := by
    rw [ha]
    apply Subtype.ext
    have hprime' : k • piSigma.1 = u.1 + k • piL.1 := by
      simpa using congrArg
        (fun z : ambientFixedAddSubgroup A E.field.field ↦ (z : A.V)) hprime
    change k • piL.1 + w.1.1 - k • piSigma.1 = w.1.1 - u.1
    rw [hprime']
    abel
  let xM : M.V := bM + a - M.ρ t a
  have hxM : M.ρ g xM = xM := by
    exact abstractReciprocity_fixedCombination M g t (k • piSigmaM) bM a
      hSigmaPow hbAction hbc
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let xCycle : T.moduleCatLeftHomologyData.K := ⟨xM, by
    change M.ρ g xM - xM = 0
    exact sub_eq_zero.mpr hxM⟩
  let x : ambientFixedAddSubgroup A E.base.field :=
    (cyclicFixedCycleEquiv A E.base.field E.field.field E.below
      hnormal E.finiteQuotient g hg).symm xCycle
  refine ⟨a, x, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · have hActionVal :=
      v.valuationAt_extensionFixedRepresentation_action
        E hnormal t a
    have hxFormula : fixedFieldInclusion A E.base.field E.field.field E.below x =
        k • piL + w.1 + e a - e (M.ρ t a) := by
      apply Subtype.ext
      rfl
    have hval :
        v.valuationAt E.field
          (fixedFieldInclusion A E.base.field E.field.field E.below x) =
          k • v.oneValue := by
      rw [hxFormula, map_sub, map_add, map_add, map_nsmul,
        hpiL, w.2, hActionVal]
      abel
    calc
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ZHat) =
          ((k • v.oneValue : v.valueGroup) : ZHat) :=
        congrArg Subtype.val hval
      _ = k • (1 : ZHat) := rfl
      _ = Int.castRingHom ZHat (k : ℤ) := by
        simp

end ValuationData

end
end ClassFormation
