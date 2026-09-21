/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.IrreducibilityTransfer
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduced
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ArchimedeanAssumptions
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.CardinalIntegerPart
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.IntegerPart
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveCoefficientMap
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveDomainEquiv
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalForm
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.SignedFull
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.Transfer
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.RealArchimedeanStratum

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncationIrreducible
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEmbedding
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEquiv
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedCharacterization
import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.DegreeTransfer

/-!
# Real leading splits of surreal Hahn series

Embed a nonpositive real-exponent Hahn series into the surreal exponent group. Its leading
Archimedean class is the real class, its open truncation retains only the constant coefficient,
and splitting at that class simply extends each coefficient by a constant infinitesimal Hahn
series.

The irreducibility theorem combines this description with the residue-one case of LM24,
Proposition 8.3.6(5): irreducibility after coefficient extension implies irreducibility in the
surreal truncation integer part. The same description shows that a constant-coefficient-one series
is reduced in the sense of LM24, Definition 8.2.1, after the embedding.

The last section passes to Conway's omnific integers. A real-exponent series with integer
constant coefficient determines the omnific integer `ofRealSeries` whose signed Conway normal form
is the embedded series; its Conway coefficients, support, normal form, and length are read off
from the series, and irreducibility and reducedness transfer. This is the natural route to
omnific integers whose Conway normal forms have real exponents.

## References

* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, cited as [LM24].
-/

universe u v

open scoped HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

open FiniteArchimedeanClass

variable {R : Type v} [Field R]

private def realToSurrealAddMonoidHom : ℝ →+ Surreal.{u} :=
  Real.toSurrealRingHom.toRingHom.toAddMonoidHom

/-- Map a real-exponent nonpositive Hahn series into the surreal exponent group. -/
def mapRealDomainToSurreal : Nonpositive ℝ R →+* Nonpositive Surreal.{u} R :=
  mapDomain realToSurrealAddMonoidHom
    (by
      intro r s h
      change (r : Surreal.{u}) = (s : Surreal.{u}) at h
      exact_mod_cast h)
    (fun r s ↦ Real.toSurreal_le_iff)

/-- Mapping the real exponent domain into the surreal numbers is injective. -/
theorem mapRealDomainToSurreal_injective :
    Function.Injective (mapRealDomainToSurreal :
      Nonpositive ℝ R → Nonpositive Surreal.{u} R) := by
  intro a b hab
  apply mapDomain_injective realToSurrealAddMonoidHom
    (by
      intro x y h
      change (x : Surreal.{u}) = (y : Surreal.{u}) at h
      exact_mod_cast h)
    (fun x y ↦ Real.toSurreal_le_iff)
  change mapRealDomainToSurreal a = mapRealDomainToSurreal b
  exact hab

@[simp]
theorem mapRealDomainToSurreal_coeff_real (a : Nonpositive ℝ R) (r : ℝ) :
    (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).coeff (r : Surreal.{u}) =
      (a : R⟦ℝ⟧).coeff r := by
  exact mapDomain_coeff_image realToSurrealAddMonoidHom
    (by
      intro x y h
      change (x : Surreal.{u}) = (y : Surreal.{u}) at h
      exact_mod_cast h)
    (fun x y ↦ Real.toSurreal_le_iff) a r

/-- Mapping the real exponent domain preserves the constant coefficient. -/
theorem constantCoeff_mapRealDomainToSurreal (a : Nonpositive ℝ R) :
    constantCoeff (mapRealDomainToSurreal a : Nonpositive Surreal.{u} R) =
      constantCoeff a := by
  rw [mapRealDomainToSurreal]
  exact constantCoeff_mapDomain realToSurrealAddMonoidHom
    (by
      intro x y h
      change (x : Surreal.{u}) = (y : Surreal.{u}) at h
      exact_mod_cast h)
    (fun x y ↦ Real.toSurreal_le_iff) a

/-- Mapping the real exponent domain sends the support pointwise into the surreal real line. -/
theorem mapRealDomainToSurreal_support (a : Nonpositive ℝ R) :
    (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).support =
      (fun r : ℝ ↦ (r : Surreal.{u})) '' (a : R⟦ℝ⟧).support := by
  exact support_mapDomain realToSurrealAddMonoidHom
    (by
      intro x y h
      change (x : Surreal.{u}) = (y : Surreal.{u}) at h
      exact_mod_cast h)
    (fun x y ↦ Real.toSurreal_le_iff) a

/-- Mapping the real exponent domain preserves support order type, up to universe lift. -/
theorem lift_supportOrderType_mapRealDomainToSurreal (a : Nonpositive ℝ R) :
    Ordinal.lift.{0, u + 1}
        (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).supportOrderType =
      Ordinal.lift.{u + 1, 0} (a : R⟦ℝ⟧).supportOrderType := by
  rw [mapRealDomainToSurreal]
  exact lift_supportOrderType_mapDomain realToSurrealAddMonoidHom
    (by
      intro x y h
      change (x : Surreal.{u}) = (y : Surreal.{u}) at h
      exact_mod_cast h)
    (fun x y ↦ Real.toSurreal_le_iff) a

/-- The leading Archimedean class of a nonconstant series supported on the embedded real line is
the real Archimedean class. -/
theorem leadingClass_mapRealDomainToSurreal_eq_realFiniteClass
    {a : Nonpositive ℝ R} (ha : a ≠ 0)
    (horder : ((mapRealDomainToSurreal a : Nonpositive Surreal.{u} R) :
      R⟦Surreal.{u}⟧).order ≠ 0) :
    leadingClass (mapRealDomainToSurreal a) horder =
      Surreal.realFiniteClass := by
  apply Subtype.ext
  rw [leadingClass_val, Surreal.realFiniteClass_val]
  have hmappedNe : (mapRealDomainToSurreal a : Nonpositive Surreal.{u} R) ≠ 0 :=
    fun hzero ↦ ha (mapRealDomainToSurreal_injective (by simpa using hzero))
  have horderMem : ((mapRealDomainToSurreal a : Nonpositive Surreal.{u} R) :
      R⟦Surreal.{u}⟧).order ∈
        (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).support := by
    rw [HahnSeries.mem_support]
    exact HahnSeries.coeff_order_eq_zero.not.mpr
      (fun h ↦ hmappedNe (Subtype.ext h))
  rw [mapRealDomainToSurreal_support] at horderMem
  obtain ⟨r, _hr, hrorder⟩ := horderMem
  rw [← hrorder]
  apply Surreal.mk_realCast
  intro hr0
  subst r
  apply horder
  simpa using hrorder.symm

/-- The open truncation at the real Archimedean class retains only the constant coefficient of a
series whose exponents are embedded reals. -/
theorem tau_mapRealDomainToSurreal
    (a : Nonpositive ℝ R) :
    tau (K := ℝ)
        (Surreal.realFiniteClass : FiniteArchimedeanClass Surreal.{u})
        (mapRealDomainToSurreal a) =
      C (constantCoeff a) := by
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext g
  by_cases hgBall : g ∈ ball ℝ
      (Surreal.realFiniteClass : FiniteArchimedeanClass Surreal.{u})
  · rw [coeff_tau_of_mem _ _ hgBall]
    by_cases hg0 : g = 0
    · subst g
      rw [coe_C, HahnSeries.C_apply]
      simp only [HahnSeries.coeff_single_same]
      have hcoeff := mapRealDomainToSurreal_coeff_real a 0
      have hzero : ((0 : ℝ) : Surreal.{u}) = 0 :=
        Real.toSurrealRingHom.map_zero
      rw [constantCoeff_apply]
      rw [← hzero]
      exact hcoeff
    · have hgNotSupport : g ∉
          (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).support := by
        rw [mapRealDomainToSurreal_support]
        rintro ⟨r, _hr, hrg⟩
        have hrealG : g ∈
            (Surreal.realStratum : Submodule ℝ Surreal.{u}) := by
          rw [Surreal.mem_realStratum_iff]
          exact ⟨r, hrg⟩
        have hzero := Submodule.disjoint_def.mp
          Surreal.disjoint_ball_realStratum
          g hgBall hrealG
        exact hg0 hzero
      have hcoeff : (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).coeff g = 0 := by
        rw [← not_ne_iff, ← HahnSeries.mem_support]
        exact hgNotSupport
      rw [hcoeff, coe_C, HahnSeries.C_apply,
        HahnSeries.coeff_single_of_ne hg0]
  · rw [coeff_tau_of_not_mem _ _ hgBall]
    have hg0 : g ≠ 0 := by
      intro hzero
      subst g
      exact hgBall (zero_mem _)
    rw [coe_C, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hg0]

/-- The real-supported series belongs to a truncation integer part whenever its constant
coefficient belongs to the chosen coefficient subring. -/
def mapRealDomainToSurrealIntegerPart (Z : Subring R) (a : Nonpositive ℝ R)
    (haConstant : constantCoeff a ∈ Z) :
    HahnSeries.truncationIntegerPart Surreal.{u} Z :=
  ⟨mapRealDomainToSurreal a, by
    rw [mem_truncationIntegerPart, ← constantCoeff_apply]
    exact (constantCoeff_mapDomain realToSurrealAddMonoidHom
      (by
        intro x y h
        change (x : Surreal.{u}) = (y : Surreal.{u}) at h
        exact_mod_cast h)
      (fun x y ↦ Real.toSurreal_le_iff) a).symm ▸ haConstant⟩

@[simp]
theorem coe_mapRealDomainToSurrealIntegerPart
    (Z : Subring R) (a : Nonpositive ℝ R)
    (haConstant : constantCoeff a ∈ Z) :
    (mapRealDomainToSurrealIntegerPart Z a haConstant : Nonpositive Surreal.{u} R) =
      mapRealDomainToSurreal a :=
  (rfl)

/-- Splitting a real-supported surreal Hahn series at the real Archimedean class extends its
coefficients by constant infinitesimal Hahn series and leaves its real exponents unchanged. -/
theorem splitTruncation_mapRealDomainToSurreal
    (u : HahnEmbedding.ArchimedeanStrata ℝ Surreal.{u}) (a : Nonpositive ℝ R) :
    splitTruncation (Surreal.archimedeanStrataWithReal u)
        Surreal.realFiniteClass (mapRealDomainToSurreal a) =
      embDomainRingEquiv
        (Surreal.archimedeanStrataWithRealOrderAddMonoidIso u)
        (nonpositiveCoefficientMap
          (HahnSeries.C : R →+* R⟦ball ℝ Surreal.realFiniteClass⟧) a) := by
  apply Subtype.ext
  apply HahnSeries.ext
  funext s
  apply HahnSeries.ext
  funext b
  let e := Surreal.archimedeanStrataWithRealOrderAddMonoidIso u
  let r := e.symm s
  have hs : e r = s := e.apply_symm_apply s
  rw [← hs]
  rw [coe_splitTruncation, coe_embDomainRingEquiv,
    HahnSeries.archimedeanSplitRingEquiv_coeff,
    TClosed_coeff, coeff_T_of_mem]
  · rw [HahnSeries.embDomainRingEquiv_coeff,
      coe_nonpositiveCoefficientMap]
    rw [HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall_apply]
    by_cases hb0 : (b : Surreal.{u}) = 0
    · have hb : b = 0 := Subtype.ext hb0
      subst b
      simp only [ofLex_toLex]
      rw [Surreal.coe_archimedeanStrataWithRealOrderAddMonoidIso]
      rw [show ((0 : ball ℝ Surreal.realFiniteClass) : Surreal.{u}) = 0 from rfl, add_zero]
      rw [mapRealDomainToSurreal_coeff_real]
      simp [HahnSeries.C_apply]
    · have hb : b ≠ 0 := fun h ↦ hb0 (congrArg Subtype.val h)
      have hleft : (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).coeff
          ((e r : (Surreal.archimedeanStrataWithReal u).stratum
            Surreal.realFiniteClass) + (b : Surreal.{u})) = 0 := by
        rw [← not_ne_iff, ← HahnSeries.mem_support,
          mapRealDomainToSurreal_support]
        rintro ⟨q, _hq, hqeq⟩
        have hrealB : (b : Surreal.{u}) ∈ Surreal.realStratum := by
          rw [Surreal.mem_realStratum_iff]
          refine ⟨q - r, ?_⟩
          have hscoe : (e r : Surreal.{u}) = (r : Surreal.{u}) := by
            exact Surreal.coe_archimedeanStrataWithRealOrderAddMonoidIso _ _
          change (q : Surreal.{u}) = (e r : Surreal.{u}) + (b : Surreal.{u}) at hqeq
          rw [hscoe] at hqeq
          rw [show ((q - r : ℝ) : Surreal.{u}) = (q : Surreal.{u}) - (r : Surreal.{u}) by
            exact Real.toSurrealRingHom.map_sub q r]
          apply sub_eq_iff_eq_add.mpr
          simpa [add_comm] using hqeq
        have hzero := Submodule.disjoint_def.mp Surreal.disjoint_ball_realStratum
          (b : Surreal.{u}) b.2 hrealB
        exact hb (Subtype.ext hzero)
      simp only [ofLex_toLex]
      rw [hleft]
      change 0 = (HahnSeries.C ((a : R⟦ℝ⟧).coeff r)).coeff b
      exact (HahnSeries.coeff_single_of_ne hb).symm
  · exact (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall
      (Surreal.archimedeanStrataWithReal u) Surreal.realFiniteClass (toLex (e r, b))).2

/-- A real-supported constant-one series gives an irreducible surreal truncation-integer-part
element when its coefficient extension to the infinitesimal Hahn field is irreducible. -/
theorem irreducible_mapRealDomainToSurrealIntegerPart
    (u : HahnEmbedding.ArchimedeanStrata ℝ Surreal.{u}) (Z : Subring R)
    (a : Nonpositive ℝ R) (ha : a ≠ 0)
    (haOrder : (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).order ≠ 0)
    (haConstant : constantCoeff a = 1)
    (hirr : Irreducible
      (nonpositiveCoefficientMap
        (HahnSeries.C : R →+* R⟦ball ℝ
          (Surreal.realFiniteClass : FiniteArchimedeanClass Surreal.{u})⟧) a)) :
    Irreducible
      (mapRealDomainToSurrealIntegerPart Z a
        (haConstant.symm ▸ Z.one_mem) :
          HahnSeries.truncationIntegerPart Surreal.{u} Z) := by
  let b : HahnSeries.truncationIntegerPart Surreal.{u} Z :=
    mapRealDomainToSurrealIntegerPart Z a
      (haConstant.symm ▸ Z.one_mem)
  have hbCoe : (b : Nonpositive Surreal.{u} R) = mapRealDomainToSurreal a :=
    (rfl)
  have hbOrder : ((b : Nonpositive Surreal.{u} R) : R⟦Surreal.{u}⟧).order ≠ 0 := by
    rw [hbCoe]
    exact haOrder
  have hb0 : (b : Nonpositive Surreal.{u} R) ≠ 0 := by
    rw [hbCoe]
    intro hzero
    exact ha (mapRealDomainToSurreal_injective (by simpa using hzero))
  have hleading : leadingClass (b : Nonpositive Surreal.{u} R) hbOrder =
      Surreal.realFiniteClass := by
    apply Subtype.ext
    rw [leadingClass_val]
    have hval := congrArg Subtype.val
      (leadingClass_mapRealDomainToSurreal_eq_realFiniteClass ha haOrder)
    rw [leadingClass_val] at hval
    simpa only [hbCoe] using hval
  apply irreducible_of_irreducible_splitTruncation_of_tau_eq_one
    (Surreal.archimedeanStrataWithReal u) Z b hb0 hbOrder
  · rw [hleading]
    apply tauBall_eq_one_of_tau_eq_one
    rw [hbCoe, tau_mapRealDomainToSurreal, haConstant]
    apply Subtype.ext
    simpa only [coe_C, Subring.coe_one] using
      (HahnSeries.C_one (Γ := Surreal.{u}) (R := R))
  · rw [hleading, hbCoe,
      splitTruncation_mapRealDomainToSurreal]
    exact hirr.map
      (embDomainRingEquiv
        (Surreal.archimedeanStrataWithRealOrderAddMonoidIso u))

/-- A real-supported series with constant coefficient one is reduced after embedding its exponents
into the surreal numbers: its open truncation at the leading class is the constant one. -/
theorem isReduced_mapRealDomainToSurreal {a : Nonpositive ℝ R}
    (haOrder : (mapRealDomainToSurreal a : R⟦Surreal.{u}⟧).order ≠ 0)
    (haConstant : constantCoeff a = 1) :
    IsReduced (mapRealDomainToSurreal a : Nonpositive Surreal.{u} R) := by
  have ha : a ≠ 0 := fun h ↦ haOrder (by
    rw [h, map_zero, ZeroMemClass.coe_zero, HahnSeries.order_zero])
  have hmappedNe : (mapRealDomainToSurreal a : Nonpositive Surreal.{u} R) ≠ 0 :=
    fun hzero ↦ ha (mapRealDomainToSurreal_injective (by simpa using hzero))
  apply (isReduced_iff_tau_leadingClass_eq_zero_or_one (K := ℝ) _ hmappedNe haOrder).mpr
  right
  rw [leadingClass_mapRealDomainToSurreal_eq_realFiniteClass ha haOrder,
    tau_mapRealDomainToSurreal, haConstant]
  apply Subtype.ext
  simpa only [coe_C, Subring.coe_one] using (HahnSeries.C_one (Γ := Surreal.{u}) (R := R))

end HahnSeries.Nonpositive

/-! ### Surreal numbers whose signed Conway normal form has real exponents -/

namespace Surreal

open HahnSeries.Nonpositive

variable {x : Surreal.{u}} {a : HahnSeries.Nonpositive ℝ ℝ}

/-- The Conway coefficient at `-r` of a surreal whose signed Conway normal form is a
real-exponent series is the series coefficient at `r`. -/
theorem coeff_neg_realCast_of_toSignedFullHahnSeries_eq
    (hx : x.toSignedFullHahnSeries = mapRealDomainToSurreal a) (r : ℝ) :
    x.coeff (-(r : Surreal.{u})) = (a : ℝ⟦ℝ⟧).coeff r := by
  rw [← coeff_toSignedFullHahnSeries, hx, mapRealDomainToSurreal_coeff_real]

/-- The Conway support of a surreal whose signed Conway normal form is a real-exponent series is
the negated image of the series support. -/
theorem support_of_toSignedFullHahnSeries_eq
    (hx : x.toSignedFullHahnSeries = mapRealDomainToSurreal a) :
    x.support = (fun r : ℝ ↦ -(r : Surreal.{u})) '' (a : ℝ⟦ℝ⟧).support := by
  ext i
  constructor
  · intro hi
    have hsigned : -i ∈ x.toSignedFullHahnSeries.support :=
      mem_support_toSignedFullHahnSeries.mpr (by rwa [neg_neg])
    rw [hx, mapRealDomainToSurreal_support] at hsigned
    obtain ⟨r, hr, hri⟩ := hsigned
    have hri' : (r : Surreal.{u}) = -i := hri
    refine ⟨r, hr, ?_⟩
    change -(r : Surreal.{u}) = i
    rw [hri', neg_neg]
  · rintro ⟨r, hr, rfl⟩
    apply mem_support_toSignedFullHahnSeries.mp
    rw [hx, mapRealDomainToSurreal_support]
    exact ⟨r, hr, rfl⟩

/-- The Conway normal form of a surreal whose signed Conway normal form is a real-exponent series
is the surreal Hahn series supported on negated reals whose coefficient at `-r` is the series
coefficient at `r`. -/
theorem toHahnSeries_eq_of_toSignedFullHahnSeries_eq
    (hx : x.toSignedFullHahnSeries = mapRealDomainToSurreal a) (N : SurrealHahnSeries.{u})
    (hN : ∀ r : ℝ, N.coeff (-(r : Surreal.{u})) = (a : ℝ⟦ℝ⟧).coeff r)
    (hNsupport : N.support ⊆ Set.range (fun r : ℝ ↦ -(r : Surreal.{u}))) :
    x.toHahnSeries = N := by
  apply SurrealHahnSeries.ext
  funext i
  rw [coeff_toHahnSeries]
  by_cases hi : i ∈ Set.range (fun r : ℝ ↦ -(r : Surreal.{u}))
  · obtain ⟨r, rfl⟩ := hi
    change x.coeff (-(r : Surreal.{u})) = N.coeff (-(r : Surreal.{u}))
    rw [hN, coeff_neg_realCast_of_toSignedFullHahnSeries_eq hx]
  · have hxi : x.coeff i = 0 := by
      rw [← notMem_support_iff, support_of_toSignedFullHahnSeries_eq hx]
      rintro ⟨r, -, hri⟩
      exact hi ⟨r, hri⟩
    have hNi : N.coeff i = 0 := by
      by_contra hne
      exact hi (hNsupport (SurrealHahnSeries.mem_support_iff.mpr hne))
    rw [hxi, hNi]

/-- The lifted Conway length of a surreal whose signed Conway normal form is a real-exponent
series is the lifted support order type of the series. -/
theorem lift_length_of_toSignedFullHahnSeries_eq
    (hx : x.toSignedFullHahnSeries = mapRealDomainToSurreal a) :
    Ordinal.lift.{u + 1, u} x.length =
      Ordinal.lift.{u + 1, 0} (a : ℝ⟦ℝ⟧).supportOrderType := by
  have h : Ordinal.lift.{0, u + 1}
      (mapRealDomainToSurreal a : ℝ⟦Surreal.{u}⟧).supportOrderType =
        Ordinal.lift.{u + 1, 0} (a : ℝ⟦ℝ⟧).supportOrderType :=
    lift_supportOrderType_mapRealDomainToSurreal a
  rw [← hx, toSignedFullHahnSeries_eq, HahnSeries.supportOrderType_embDomainRingEquiv,
    supportOrderType_toFullHahnSeries, Ordinal.lift_id'] at h
  exact h

end Surreal

/-! ### Omnific integers with real Conway exponents -/

namespace Surreal.OmnificInteger

open HahnSeries.Nonpositive

variable (a : HahnSeries.Nonpositive ℝ ℝ)

private theorem cardSupp_mapRealDomainToSurreal_lt :
    (mapRealDomainToSurreal a : ℝ⟦Surreal.{u}⟧).cardSupp < Surreal.smallSupportCardinal.{u} := by
  have hsmall : Small.{u, u + 1} (mapRealDomainToSurreal a : ℝ⟦Surreal.{u}⟧).support := by
    rw [mapRealDomainToSurreal_support]
    infer_instance
  rw [HahnSeries.cardSupp, Surreal.smallSupportCardinal_eq_univ]
  simpa only [Cardinal.lift_id] using (Cardinal.small_iff_lift_mk_lt_univ
    (α := (mapRealDomainToSurreal a : ℝ⟦Surreal.{u}⟧).support)).mp hsmall

private def boundedOfRealSeries (ha : constantCoeff a ∈ Surreal.realIntegerSubring) :
    SignedSmallSupportIntegerPart.{u} :=
  ⟨⟨mapRealDomainToSurreal a, cardSupp_mapRealDomainToSurreal_lt a⟩, by
    rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
    refine ⟨support_subset _, ?_⟩
    rw [← constantCoeff_apply, constantCoeff_mapRealDomainToSurreal]
    exact ha⟩

private theorem toTruncationIntegerPartRingHom_boundedOfRealSeries
    (ha : constantCoeff a ∈ Surreal.realIntegerSubring) :
    HahnSeries.CardSuppLTTruncationIntegerPart.toTruncationIntegerPartRingHom
        Surreal.realIntegerSubring (boundedOfRealSeries a ha) =
      mapRealDomainToSurrealIntegerPart Surreal.realIntegerSubring a ha := by
  apply Subtype.ext
  apply Subtype.ext
  rw [HahnSeries.CardSuppLTTruncationIntegerPart.coe_toTruncationIntegerPartRingHom,
    HahnSeries.CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom,
    coe_mapRealDomainToSurrealIntegerPart]
  rfl

/-- The omnific integer whose signed Conway normal form is the real-exponent series `a`: the
Conway normal form `∑ a_r ω ^ (-r)` over the support of `a`. -/
def ofRealSeries (ha : constantCoeff a ∈ Surreal.realIntegerSubring) :
    Surreal.OmnificInteger.{u} :=
  signedSmallSupportIntegerPartRingEquiv.symm (boundedOfRealSeries a ha)

variable (ha : constantCoeff a ∈ Surreal.realIntegerSubring)

/-- The signed Conway normal form of `ofRealSeries a ha` is `a` with surreal exponents. -/
theorem toSignedFullHahnSeries_ofRealSeries :
    (ofRealSeries.{u} a ha).1.toSignedFullHahnSeries = mapRealDomainToSurreal a := by
  have h := signedSmallSupportIntegerPartRingEquiv.apply_symm_apply (boundedOfRealSeries a ha)
  rw [signedSmallSupportIntegerPartRingEquiv_apply] at h
  have hraw := congrArg (fun q : SignedSmallSupportIntegerPart.{u} ↦
    ((q : HahnSeries.CardSuppLTField (G := Surreal) (R := ℝ)
      (κ := Surreal.smallSupportCardinal.{u})) : HahnSeries Surreal ℝ)) h
  rw [coe_toSignedSmallSupportIntegerPart] at hraw
  exact hraw

/-- The signed nonpositive Hahn series of `ofRealSeries a ha` is `a` with surreal exponents. -/
theorem toSignedNonpositiveHahn_ofRealSeries :
    (ofRealSeries.{u} a ha).toSignedNonpositiveHahn = mapRealDomainToSurreal a := by
  apply Subtype.ext
  rw [coe_toSignedNonpositiveHahn, toSignedFullHahnSeries_ofRealSeries]

/-- The Conway normal form of `ofRealSeries a ha` has the support order type of `a`, lifted to
the universe of the surreal model. -/
theorem length_ofRealSeries :
    (ofRealSeries.{u} a ha).1.length = Ordinal.lift.{u, 0} (a : ℝ⟦ℝ⟧).supportOrderType := by
  apply Ordinal.lift_inj.{u + 1, u}.mp
  rw [Ordinal.lift_lift]
  exact Surreal.lift_length_of_toSignedFullHahnSeries_eq (toSignedFullHahnSeries_ofRealSeries a ha)

/-- `ofRealSeries a ha` is irreducible when `a` is irreducible in the surreal truncation integer
part. -/
theorem irreducible_ofRealSeries
    (hirr : Irreducible (mapRealDomainToSurrealIntegerPart Surreal.realIntegerSubring a ha :
      HahnSeries.truncationIntegerPart Surreal.{u} Surreal.realIntegerSubring)) :
    Irreducible (ofRealSeries.{u} a ha) := by
  have h : Irreducible (boundedOfRealSeries a ha) := by
    apply
      HahnSeries.CardSuppLTTruncationIntegerPart.irreducible_of_irreducible_toTruncationIntegerPart
        Surreal.realIntegerSubring
    rw [toTruncationIntegerPartRingHom_boundedOfRealSeries]
    exact hirr
  exact h.map signedSmallSupportIntegerPartRingEquiv.symm

/-- `ofRealSeries a ha` is reduced when `a` is nonzero and nonconstant with constant coefficient
one. -/
theorem isReduced_ofRealSeries
    (haOrder : (mapRealDomainToSurreal a : ℝ⟦Surreal.{u}⟧).order ≠ 0)
    (haConstant : constantCoeff a = 1) :
    IsReduced (ofRealSeries.{u} a ha).toSignedNonpositiveHahn := by
  rw [toSignedNonpositiveHahn_ofRealSeries]
  exact isReduced_mapRealDomainToSurreal haOrder haConstant

end Surreal.OmnificInteger
