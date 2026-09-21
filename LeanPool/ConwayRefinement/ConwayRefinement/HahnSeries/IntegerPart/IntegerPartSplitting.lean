/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.SplitTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.TruncationPrimality

/-!
# Splitting a leading-class Hahn-series integer part

This module formalizes LM24, Fact 2.4.2(5). The elements of the truncation integer part fixed by
the closed-class cut are identified with an outer truncation integer part whose coefficient
subring is the embedded inner truncation integer part. Keeping that exact coefficient subring is
essential: replacing it by the whole inner Hahn field loses the source integer-part condition.
-/

open FiniteArchimedeanClass

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

def fixedIntegerPartSubring (c : FiniteArchimedeanClass G) (Z : Subring R) :
    Subring (truncationIntegerPart G Z) :=
  (truncationSubring (K := K) (R := R) c).comap
    (truncationIntegerPart G Z).subtype

/-- Membership in the fixed integer-part subring is exactly invariance under closed-class
truncation of the underlying nonpositive Hahn series. -/
theorem mem_fixedIntegerPartSubring_iff (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : truncationIntegerPart G Z) :
    x ∈ fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z ↔
      T (K := K) c (x : Nonpositive G R) = x := by
  change (x : Nonpositive G R) ∈ truncationSubring (K := K) (R := R) c ↔ _
  exact mem_truncationSubring_iff c (x : Nonpositive G R)

theorem coeff_zero_tauBall (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    (tauBall (K := K) c x).coeff 0 = (x : R⟦G⟧).coeff 0 := by
  rw [tauBall_coeff]
  exact coeff_tau_of_mem c x (Submodule.zero_mem _)

def innerIntegerPartSubring (c : FiniteArchimedeanClass G) (Z : Subring R) :
    Subring R⟦ball K c⟧ :=
  (truncationIntegerPart (ball K c) Z).map
    (nonpositiveSubring (ball K c) R).subtype

/-- Membership in the embedded inner integer part means nonpositive support and constant
coefficient in `Z`. -/
theorem mem_innerIntegerPartSubring_iff (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : R⟦ball K c⟧) :
    x ∈ innerIntegerPartSubring (K := K) (G := G) c Z ↔
      x.support ⊆ Set.Iic 0 ∧ x.coeff 0 ∈ Z := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Subring.mem_map.mp hx
    rw [← hxy]
    exact ⟨support_subset y, (mem_truncationIntegerPart (R := R) (Γ := ball K c)).mp hy⟩
  · rintro ⟨hsupport, hcoeff⟩
    let y : Nonpositive (ball K c) R := ⟨x, hsupport⟩
    apply Subring.mem_map.mpr
    exact ⟨y, (mem_truncationIntegerPart (R := R) (Γ := ball K c)).mpr hcoeff, rfl⟩

theorem tauBall_mem_innerIntegerPartSubring
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : truncationIntegerPart G Z) :
    tauBall (K := K) c (x : Nonpositive G R) ∈ innerIntegerPartSubring c Z := by
  apply Subring.mem_map.mpr
  let y : Nonpositive (ball K c) R := ⟨tauBall c x, ?_⟩
  · refine ⟨y, ?_, rfl⟩
    rw [mem_truncationIntegerPart]
    rw [show (y : R⟦ball K c⟧).coeff 0 = (tauBall c x).coeff 0 by rfl]
    rw [coeff_zero_tauBall]
    exact (mem_truncationIntegerPart (Γ := G) (R := R)).mp x.2
  · intro b hb
    rw [HahnSeries.mem_support] at hb
    rw [tauBall_coeff] at hb
    change (HahnSeries.coeff
      (((tau (K := K) c (x : Nonpositive G R) : Nonpositive G R) : R⟦G⟧))
        (b : G) ≠ 0) at hb
    rw [coeff_tau_of_mem c (x : Nonpositive G R) b.2] at hb
    exact Subtype.coe_le_coe.mp (support_subset (x : Nonpositive G R) hb)

def splitRawRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    : Nonpositive G R →+* (R⟦ball K c⟧)⟦u.stratum c⟧ :=
  (HahnSeries.archimedeanSplitRingEquiv u c).toRingHom.comp (TClosedRingHom c)

@[simp]
theorem splitRawRingHom_apply
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    splitRawRingHom u c x = HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x) := by
  rw [splitRawRingHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    TClosedRingHom_apply]
  rfl

def splitIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) : truncationIntegerPart G Z →+*
      truncationIntegerPart (u.stratum c)
        (innerIntegerPartSubring (K := K) (G := G) c Z) where
  toFun x := ⟨⟨splitRawRingHom u c (x : Nonpositive G R), by
      rw [splitRawRingHom_apply]
      exact support_archimedeanSplitRingEquiv_TClosed_subset u c
        (x : Nonpositive G R)⟩, by
      rw [mem_truncationIntegerPart]
      change (splitRawRingHom u c (x : Nonpositive G R)).coeff 0 ∈
        innerIntegerPartSubring (K := K) (G := G) c Z
      rw [splitRawRingHom_apply, coeff_zero_archimedeanSplitRingEquiv_TClosed]
      exact tauBall_mem_innerIntegerPartSubring c Z x⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one (splitRawRingHom u c)
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul (splitRawRingHom u c) (x : Nonpositive G R) y
  map_zero' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_zero (splitRawRingHom u c)
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (splitRawRingHom u c) (x : Nonpositive G R) y

/-- The integer-part split has the underlying nonpositive split truncation. -/
@[simp]
theorem coe_splitIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) (x : truncationIntegerPart G Z) :
    ((splitIntegerPartRingHom u c Z x :
      truncationIntegerPart (u.stratum c) (innerIntegerPartSubring c Z)) :
        Nonpositive (u.stratum c) R⟦ball K c⟧) =
      splitTruncation u c (x : Nonpositive G R) := by
  apply Subtype.ext
  rw [coe_splitTruncation]
  change splitRawRingHom u c (x : Nonpositive G R) = _
  rw [splitRawRingHom_apply]

def splitFixedIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) :
    fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z →+*
      truncationIntegerPart (u.stratum c)
        (innerIntegerPartSubring (K := K) (G := G) c Z) :=
  (splitIntegerPartRingHom u c Z).comp
    (fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z).subtype

@[simp]
theorem coe_splitFixedIntegerPartRingHom
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) (x : fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z) :
    ((splitFixedIntegerPartRingHom u c Z x :
      truncationIntegerPart (u.stratum c) (innerIntegerPartSubring c Z)) :
        Nonpositive (u.stratum c) R⟦ball K c⟧) =
      splitTruncation u c (x : Nonpositive G R) :=
  by
    apply Subtype.ext
    rw [coe_splitTruncation]
    change (splitRawRingHom u c (x : Nonpositive G R)) = _
    rw [splitRawRingHom_apply]

def unsplitIntegerPart
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (innerIntegerPartSubring (K := K) (G := G) c Z)) :
    fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z := by
  let yOuter : Nonpositive (u.stratum c) R⟦ball K c⟧ := y
  have hyZeroInner : (((yOuter : (R⟦ball K c⟧)⟦u.stratum c⟧).coeff 0).support ⊆
      Set.Iic 0) := by
    have hyMem : (yOuter : (R⟦ball K c⟧)⟦u.stratum c⟧).coeff 0 ∈
        innerIntegerPartSubring (K := K) (G := G) c Z :=
      (mem_truncationIntegerPart (Γ := u.stratum c) (R := R⟦ball K c⟧)).mp y.2
    obtain ⟨z, hz, hzy⟩ := Subring.mem_map.mp hyMem
    rw [← hzy]
    exact support_subset z
  let zClosed := (HahnSeries.archimedeanSplitRingEquiv u c).symm
    (yOuter : (R⟦ball K c⟧)⟦u.stratum c⟧)
  let z : Nonpositive G R :=
    ⟨HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c) zClosed, by
      rw [mem_nonpositiveSubring]
      rw [HahnSeries.support_embDomain]
      rintro _ ⟨g, hg, rfl⟩
      rw [closedBallOrderEmbedding_apply]
      exact Subtype.coe_le_coe.mpr
        (support_archimedeanSplitRingEquiv_symm_subset_Iic u c
          (yOuter : (R⟦ball K c⟧)⟦u.stratum c⟧)
          (support_subset yOuter) hyZeroInner hg)⟩
  have hzeroEmbedding : closedBallOrderEmbedding (K := K) c (0 : closedBall K c) = 0 := by
    rw [closedBallOrderEmbedding_apply]
    rfl
  have hzCoeff : (z : R⟦G⟧).coeff 0 ∈ Z := by
    have hyMem : (yOuter : (R⟦ball K c⟧)⟦u.stratum c⟧).coeff 0 ∈
        innerIntegerPartSubring (K := K) (G := G) c Z :=
      (mem_truncationIntegerPart (Γ := u.stratum c) (R := R⟦ball K c⟧)).mp y.2
    obtain ⟨w, hw, hwy⟩ := Subring.mem_map.mp hyMem
    rw [mem_truncationIntegerPart] at hw
    change (HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c) zClosed).coeff 0 ∈ Z
    rw [← hzeroEmbedding]
    rw [HahnSeries.embDomain_coeff]
    have hcoeff := congrArg (fun q : (R⟦ball K c⟧)⟦u.stratum c⟧ ↦
      (q.coeff 0).coeff 0)
      ((HahnSeries.archimedeanSplitRingEquiv u c).apply_symm_apply (yOuter : _))
    rw [HahnSeries.archimedeanSplitRingEquiv_coeff] at hcoeff
    rw [show HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
      (toLex (0, 0)) = 0 by simp] at hcoeff
    change ((HahnSeries.archimedeanSplitRingEquiv u c).symm
      (yOuter : (R⟦ball K c⟧)⟦u.stratum c⟧)).coeff 0 ∈ Z
    rw [hcoeff, ← hwy]
    exact hw
  refine ⟨⟨z, (mem_truncationIntegerPart (Γ := G) (R := R)).mpr hzCoeff⟩, ?_⟩
  apply (mem_truncationSubring_iff c z).mpr
  apply Subtype.ext
  ext g
  by_cases hg : g ∈ closedBall K c
  · rw [coeff_T_of_mem c z hg]
  · rw [coeff_T_of_not_mem c z hg]
    symm
    apply HahnSeries.embDomain_of_notMem_range
    exact fun ⟨h, hh⟩ ↦ hg (by
      rw [closedBallOrderEmbedding_apply] at hh
      exact hh ▸ h.2)

@[simp]
theorem coe_unsplitIntegerPart
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (innerIntegerPartSubring (K := K) (G := G) c Z)) :
    (((unsplitIntegerPart u c Z y : truncationIntegerPart G Z) : Nonpositive G R) :
      R⟦G⟧) =
      HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c)
        ((HahnSeries.archimedeanSplitRingEquiv u c).symm
          (y : (R⟦ball K c⟧)⟦u.stratum c⟧)) :=
  by
    rfl

theorem TClosed_of_fixed (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (hx : T (K := K) c x = x) :
    TClosed (K := K) c x =
      HahnSeries.restrictDomain (closedBallOrderEmbedding (K := K) c) (x : R⟦G⟧) := by
  ext g
  rw [TClosed_coeff, hx, HahnSeries.restrictDomain_coeff,
    closedBallOrderEmbedding_apply]

-- Checking both inverses traverses the full nested subtype and Hahn-series equivalence stack.
def splitFixedIntegerPartRingEquiv
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) :
    fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z ≃+*
      truncationIntegerPart (u.stratum c)
        (innerIntegerPartSubring (K := K) (G := G) c Z) where
  toFun := splitFixedIntegerPartRingHom u c Z
  invFun := unsplitIntegerPart u c Z
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    dsimp only [unsplitIntegerPart]
    change HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c)
      ((HahnSeries.archimedeanSplitRingEquiv u c).symm
        (((splitFixedIntegerPartRingHom u c Z x : _) :
          Nonpositive (u.stratum c) R⟦ball K c⟧) :
            (R⟦ball K c⟧)⟦u.stratum c⟧)) = (x : R⟦G⟧)
    rw [coe_splitFixedIntegerPartRingHom]
    rw [coe_splitTruncation]
    rw [RingEquiv.symm_apply_apply, embDomain_TClosed]
    exact congrArg Subtype.val ((mem_truncationSubring_iff c (x : Nonpositive G R)).mp x.2)
  right_inv y := by
    apply Subtype.ext
    rw [coe_splitFixedIntegerPartRingHom]
    apply Subtype.ext
    rw [coe_splitTruncation]
    rw [TClosed_of_fixed c (unsplitIntegerPart u c Z y : Nonpositive G R)
      ((mem_truncationSubring_iff c _).mp (unsplitIntegerPart u c Z y).2)]
    rw [coe_unsplitIntegerPart]
    change HahnSeries.archimedeanSplitRingEquiv u c
      (HahnSeries.restrictDomain (closedBallOrderEmbedding (K := K) c)
        (HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c)
          ((HahnSeries.archimedeanSplitRingEquiv u c).symm
            (y : (R⟦ball K c⟧)⟦u.stratum c⟧)))) =
        (y : (R⟦ball K c⟧)⟦u.stratum c⟧)
    rw [HahnSeries.restrictDomain_embDomain, RingEquiv.apply_symm_apply]
  map_mul' := (splitFixedIntegerPartRingHom u c Z).map_mul
  map_add' := (splitFixedIntegerPartRingHom u c Z).map_add

/-- The fixed integer-part equivalence applies by the split ring homomorphism. -/
@[simp]
theorem splitFixedIntegerPartRingEquiv_apply
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) (x : fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z) :
    splitFixedIntegerPartRingEquiv u c Z x = splitFixedIntegerPartRingHom u c Z x :=
  (rfl)

/-- The inverse fixed integer-part equivalence is the explicit unsplit construction. -/
@[simp]
theorem splitFixedIntegerPartRingEquiv_symm_apply
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R)
    (y : truncationIntegerPart (u.stratum c)
      (innerIntegerPartSubring (K := K) (G := G) c Z)) :
    (splitFixedIntegerPartRingEquiv u c Z).symm y = unsplitIntegerPart u c Z y :=
  (rfl)

theorem coe_splitFixedIntegerPartRingEquiv
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (Z : Subring R) (x : fixedIntegerPartSubring (K := K) (G := G) (R := R) c Z) :
    ((splitFixedIntegerPartRingEquiv u c Z x :
      truncationIntegerPart (u.stratum c) (innerIntegerPartSubring c Z)) :
        Nonpositive (u.stratum c) R⟦ball K c⟧) =
      splitTruncation u c (x : Nonpositive G R) := by
  change ((splitFixedIntegerPartRingHom u c Z x : _) :
    Nonpositive (u.stratum c) R⟦ball K c⟧) = _
  exact coe_splitFixedIntegerPartRingHom u c Z x

end HahnSeries.Nonpositive
