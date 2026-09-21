/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.PrimalityTransfer
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Monomial

/-!
# Irreducibility transfer from a leading Archimedean class

This module formalizes the residue-one irreducibility transfer used in LM24,
Proposition 8.3.6(5). If a nonconstant integer-part element has open truncation one and its
leading split is irreducible, then the original element is irreducible.

Every factor of the element is fixed by truncation at its leading class. The fixed integer-part
subring is ring-equivalent to the split integer part. Finally, an ambient unit occurring in a
factorisation with constant coefficient one is already a unit of that integer part.
-/

public noncomputable section

namespace HahnSeries.Nonpositive

open FiniteArchimedeanClass

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

private theorem irreducible_truncationIntegerPart_of_irreducible_of_constantCoeff_eq_one
    {S : Subring R} {b : truncationIntegerPart G S}
    (hirr : Irreducible (b : Nonpositive G R))
    (hconstant : constantCoeff (b : Nonpositive G R) = 1) :
    Irreducible b := by
  rw [irreducible_iff]
  refine ⟨fun hunit ↦ hirr.not_isUnit
    ((truncationIntegerPart G S).subtype.isUnit_map hunit), ?_⟩
  intro c d hfactor
  have hfactorAmbient : (b : Nonpositive G R) = c * d :=
    congrArg Subtype.val hfactor
  rcases hirr.isUnit_or_isUnit hfactorAmbient with hcUnit | hdUnit
  · left
    have hcoeffProduct :
        constantCoeff (c : Nonpositive G R) *
          constantCoeff (d : Nonpositive G R) = 1 := by
      calc
        _ = constantCoeff ((c : Nonpositive G R) * (d : Nonpositive G R)) :=
          (map_mul (constantCoeff (Γ := G) (R := R))
            (c : Nonpositive G R) (d : Nonpositive G R)).symm
        _ = constantCoeff (b : Nonpositive G R) := by rw [hfactorAmbient]
        _ = 1 := hconstant
    let dConstant : truncationIntegerPart G S :=
      ⟨C (constantCoeff (d : Nonpositive G R)), by
        rw [mem_truncationIntegerPart]
        simpa [constantCoeff_apply] using
          (mem_truncationIntegerPart (R := R) (Γ := G)).mp d.2⟩
    apply isUnit_iff_exists.mpr
    refine ⟨dConstant, ?_⟩
    have hprod : c * dConstant = 1 := by
      apply Subtype.ext
      change (c : Nonpositive G R) * C (constantCoeff (d : Nonpositive G R)) = 1
      rw [eq_C_constantCoeff_of_isUnit hcUnit, ← map_mul, hcoeffProduct, map_one]
    exact ⟨hprod, by simpa [mul_comm] using hprod⟩
  · right
    have hcoeffProduct :
        constantCoeff (c : Nonpositive G R) *
          constantCoeff (d : Nonpositive G R) = 1 := by
      calc
        _ = constantCoeff ((c : Nonpositive G R) * (d : Nonpositive G R)) :=
          (map_mul (constantCoeff (Γ := G) (R := R))
            (c : Nonpositive G R) (d : Nonpositive G R)).symm
        _ = constantCoeff (b : Nonpositive G R) := by rw [hfactorAmbient]
        _ = 1 := hconstant
    let cConstant : truncationIntegerPart G S :=
      ⟨C (constantCoeff (c : Nonpositive G R)), by
        rw [mem_truncationIntegerPart]
        simpa [constantCoeff_apply] using
          (mem_truncationIntegerPart (R := R) (Γ := G)).mp c.2⟩
    apply isUnit_iff_exists.mpr
    refine ⟨cConstant, ?_⟩
    have hprod : d * cConstant = 1 := by
      apply Subtype.ext
      change (d : Nonpositive G R) * C (constantCoeff (c : Nonpositive G R)) = 1
      rw [eq_C_constantCoeff_of_isUnit hdUnit, ← map_mul, mul_comm,
        hcoeffProduct, map_one]
    exact ⟨hprod, by simpa [mul_comm] using hprod⟩

/-- In the residue-one branch, irreducibility of the ambient split series implies
irreducibility in its split integer part. -/
theorem irreducible_splitTruncationIntegerPart_of_tau_eq_one
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (S : Subring R⟦ball K c⟧) (x : Nonpositive G R)
    (htau : tauBall c x = 1)
    (hirr : Irreducible (splitTruncation u c x)) :
    Irreducible
      (splitTruncationIntegerPart u c S x (htau.symm ▸ S.one_mem)) := by
  have hirr' : Irreducible
      (splitTruncationIntegerPart u c S x (htau.symm ▸ S.one_mem) :
        Nonpositive (u.stratum c) R⟦ball K c⟧) := by
    rw [coe_splitTruncationIntegerPart]
    exact hirr
  apply irreducible_truncationIntegerPart_of_irreducible_of_constantCoeff_eq_one hirr'
  rw [coe_splitTruncationIntegerPart, constantCoeff_splitTruncation, htau]

/-- Irreducibility in the leading fixed integer-part subring implies irreducibility in the full
integer part. -/
theorem irreducible_of_irreducible_leadingFixedIntegerPartElement
    (Z : Subring R) (b : truncationIntegerPart G Z)
    (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hirr : Irreducible
      (leadingFixedIntegerPartElement (K := K) Z b horder)) :
    Irreducible b := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro hunit
    have hunitAmbient : IsUnit (b : Nonpositive G R) :=
      (truncationIntegerPart G Z).subtype.isUnit_map hunit
    have hsupport := support_eq_singleton_zero_of_isUnit hunitAmbient
    have hbOrderMem : ((b : Nonpositive G R) : R⟦G⟧).order ∈
        ((b : Nonpositive G R) : R⟦G⟧).support := by
      rw [HahnSeries.mem_support]
      exact HahnSeries.coeff_order_eq_zero.not.mpr
        (fun h ↦ hb0 (Subtype.ext h))
    rw [hsupport, Set.mem_singleton_iff] at hbOrderMem
    exact horder hbOrderMem
  · intro c d hfactor
    have hcDvd : (c : Nonpositive G R) ∣ (b : Nonpositive G R) :=
      ⟨d, congrArg Subtype.val hfactor⟩
    have hdDvd : (d : Nonpositive G R) ∣ (b : Nonpositive G R) :=
      ⟨c, by simpa [mul_comm] using congrArg Subtype.val hfactor⟩
    have hcFixed := T_leadingClass_of_dvd (K := K)
      (b : Nonpositive G R) hb0 horder hcDvd
    have hdFixed := T_leadingClass_of_dvd (K := K)
      (b : Nonpositive G R) hb0 horder hdDvd
    let cFixed : fixedIntegerPartSubring (K := K) (G := G) (R := R)
        (leadingClass (b : Nonpositive G R) horder) Z :=
      ⟨c, (mem_fixedIntegerPartSubring_iff _ Z c).mpr hcFixed⟩
    let dFixed : fixedIntegerPartSubring (K := K) (G := G) (R := R)
        (leadingClass (b : Nonpositive G R) horder) Z :=
      ⟨d, (mem_fixedIntegerPartSubring_iff _ Z d).mpr hdFixed⟩
    have hfactorFixed :
        leadingFixedIntegerPartElement (K := K) Z b horder =
          cFixed * dFixed := by
      apply Subtype.ext
      rw [coe_leadingFixedIntegerPartElement]
      simpa [cFixed, dFixed] using hfactor
    rcases hirr.isUnit_or_isUnit hfactorFixed with hcUnit | hdUnit
    · exact Or.inl
        ((fixedIntegerPartSubring (K := K) (G := G) (R := R)
          (leadingClass (b : Nonpositive G R) horder) Z).subtype.isUnit_map hcUnit)
    · exact Or.inr
        ((fixedIntegerPartSubring (K := K) (G := G) (R := R)
          (leadingClass (b : Nonpositive G R) horder) Z).subtype.isUnit_map hdUnit)

/-- LM24, Proposition 8.3.6(5), residue-one case: if the leading split of a nonzero,
nonconstant integer-part element is irreducible, then the original element is irreducible. -/
theorem irreducible_of_irreducible_splitTruncation_of_tau_eq_one
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (htau : tauBall (K := K) (leadingClass (b : Nonpositive G R) horder)
      (b : Nonpositive G R) = 1)
    (hirr : Irreducible
      (splitTruncation u (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R))) :
    Irreducible b := by
  let sigma := leadingClass (b : Nonpositive G R) horder
  let bFixed := leadingFixedIntegerPartElement (K := K) Z b horder
  let e := splitFixedIntegerPartRingEquiv u sigma Z
  let S := innerIntegerPartSubring (K := K) (G := G) sigma Z
  have hsplitIrr : Irreducible
      (splitTruncationIntegerPart u sigma S (b : Nonpositive G R)
        (htau.symm ▸ S.one_mem)) :=
    irreducible_splitTruncationIntegerPart_of_tau_eq_one u sigma S b htau hirr
  have heq : e bFixed =
      splitTruncationIntegerPart u sigma S (b : Nonpositive G R)
        (htau.symm ▸ S.one_mem) := by
    rw [show e bFixed = splitTruncationIntegerPart u sigma S
        (b : Nonpositive G R)
        (tauBall_mem_innerIntegerPartSubring sigma Z b) by
      exact splitFixedIntegerPartRingEquiv_leadingFixedIntegerPartElement
        u Z b horder]
  have hfixedIrr : Irreducible bFixed := by
    have hmapped := hsplitIrr.map e.symm
    rw [← heq] at hmapped
    simpa using hmapped
  exact irreducible_of_irreducible_leadingFixedIntegerPartElement
    Z b hb0 horder hfixedIrr

end HahnSeries.Nonpositive
