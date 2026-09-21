/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.ArchimedeanSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ClassTruncation
public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Reduction at an Archimedean class

LM24, Definition 8.2.4 divides the closed-class truncation `T_σ(x)` by the open-class
truncation `τ_σ(x)` when the latter is nonzero. This module establishes the structural facts
needed for that division. Under the iterated Hahn-series presentation `ι_σ`, `τ_σ(x)` is a
coefficient-series scalar, while `T_σ(x)` has only nonpositive outer exponents.

The scalar statement is essential: the inverse of a negative monomial has positive exponent, so
the quotient cannot be justified by claiming that the full nonpositive Hahn-series ring is closed
under inversion.
-/

public noncomputable section

namespace HahnSeries.Nonpositive

open FiniteArchimedeanClass HahnEmbedding

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

/-- The ordered inclusion of a closed Archimedean ball into the ambient exponent group. -/
def closedBallOrderEmbedding (c : FiniteArchimedeanClass G) : closedBall K c ↪o G where
  toFun := (↑)
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

@[simp]
theorem closedBallOrderEmbedding_apply (c : FiniteArchimedeanClass G)
    (g : closedBall K c) : closedBallOrderEmbedding c g = (g : G) :=
  (rfl)

/-- The ordered inclusion of an open Archimedean ball into the ambient exponent group. -/
def ballOrderEmbedding (c : FiniteArchimedeanClass G) : ball K c ↪o G where
  toFun := (↑)
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

@[simp]
theorem ballOrderEmbedding_apply (c : FiniteArchimedeanClass G) (g : ball K c) :
    ballOrderEmbedding c g = (g : G) :=
  (rfl)

/-- The closed-class truncation, with its exponent domain restricted to the closed ball. -/
def TClosed (c : FiniteArchimedeanClass G) (x : Nonpositive G R) : R⟦closedBall K c⟧ :=
  HahnSeries.restrictDomain (closedBallOrderEmbedding c)
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧)

/-- The closed-class truncation is exponent-domain restriction of the ambient truncation. -/
theorem TClosed_eq (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    TClosed (K := K) c x =
      HahnSeries.restrictDomain (closedBallOrderEmbedding c)
        ((T (K := K) c x : Nonpositive G R) : R⟦G⟧) :=
  (rfl)

@[simp]
theorem TClosed_coeff (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (g : closedBall K c) :
    (TClosed (K := K) c x).coeff g =
      ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff g := by
  rw [TClosed, HahnSeries.restrictDomain_coeff]
  rfl

/-- The open-class truncation, with its exponent domain restricted to the open ball. -/
def tauBall (c : FiniteArchimedeanClass G) (x : Nonpositive G R) : R⟦ball K c⟧ :=
  HahnSeries.restrictDomain (ballOrderEmbedding c)
    ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧)

@[simp]
theorem tauBall_coeff (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (g : ball K c) :
    (tauBall (K := K) c x).coeff g =
      ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff g := by
  rw [tauBall, HahnSeries.restrictDomain_coeff]
  rfl

/-- The open-class truncation, regarded as a series on the containing closed ball. -/
def tauClosed (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    R⟦closedBall K c⟧ :=
  HahnSeries.restrictDomain (closedBallOrderEmbedding c)
    ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧)

/-- Under the Archimedean splitting, the open-class truncation is a scalar coefficient series. -/
theorem archimedeanSplitRingEquiv_tauClosed
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    HahnSeries.archimedeanSplitRingEquiv u c (tauClosed c x) =
      HahnSeries.C (tauBall c x) := by
  ext s b
  rw [HahnSeries.archimedeanSplitRingEquiv_coeff]
  rw [tauClosed, HahnSeries.restrictDomain_coeff]
  by_cases hs : s = 0
  · subst s
    change ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff
      (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
        (toLex (0, b)) : G) = _
    rw [HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall_apply]
    have hcoe0 : ((0 : u.stratum c) : G) = 0 := rfl
    rw [show (ofLex (toLex ((0 : u.stratum c), b))).1 = 0 by rfl,
      show (ofLex (toLex ((0 : u.stratum c), b))).2 = b by rfl, hcoe0, zero_add]
    exact
      (show ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff (b : G) =
        ((HahnSeries.C (tauBall c x)).coeff 0).coeff b by
        rw [coeff_tau_of_mem (K := K) c x b.2]
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
        rw [tauBall, HahnSeries.restrictDomain_coeff]
        change (x : R⟦G⟧).coeff (b : G) =
          ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff (b : G)
        exact (coeff_tau_of_mem (K := K) c x b.2).symm)
  · have hnotmem :
        (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
          (toLex (s, b)) : G) ∉ ball K c := by
      intro hmem
      have hsball : (s : G) ∈ ball K c := by
        rw [HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall_apply] at hmem
        simpa using sub_mem hmem b.2
      have hzero : (s : G) = 0 :=
        Submodule.disjoint_def.mp (u.disjoint_ball_stratum c) (s : G) hsball s.2
      exact hs (Subtype.ext hzero)
    change ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff
      (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
        (toLex (s, b)) : G) = _
    rw [coeff_tau_of_not_mem (K := K) c x hnotmem]
    simp [hs]

/-- The outer constant coefficient of the split closed-class truncation is the open-class
truncation. This is LM24's identity `π(ισ(Tσ(x))) = τσ(x)`. -/
theorem coeff_zero_archimedeanSplitRingEquiv_TClosed
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    (HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x)).coeff 0 =
      tauBall c x := by
  ext b
  rw [HahnSeries.archimedeanSplitRingEquiv_coeff]
  rw [TClosed, HahnSeries.restrictDomain_coeff]
  change ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff
    (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
      (toLex (0, b)) : G) = _
  rw [HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall_apply]
  have hcoe0 : ((0 : u.stratum c) : G) = 0 := rfl
  simp only [ofLex_toLex, hcoe0, zero_add]
  rw [coeff_T_of_mem (K := K) c x
    ((FiniteArchimedeanClass.ball_lt_closedBall (K := K)).le b.2)]
  rw [tauBall, HahnSeries.restrictDomain_coeff]
  exact (coeff_tau_of_mem (K := K) c x b.2).symm

/-- The split closed-class truncation has no positive outer exponent. -/
theorem support_archimedeanSplitRingEquiv_TClosed_subset
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    (HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x)).support ⊆ Set.Iic 0 := by
  intro s hs
  rw [HahnSeries.mem_support] at hs
  obtain ⟨b, hb⟩ : ∃ b : ball K c,
      ((HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x)).coeff s).coeff b ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hs
    ext b
    exact hall b
  rw [HahnSeries.archimedeanSplitRingEquiv_coeff] at hb
  rw [TClosed, HahnSeries.restrictDomain_coeff] at hb
  change ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff
    (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
      (toLex (s, b))) ≠ 0 at hb
  rw [coeff_T_of_mem (K := K) c x
    (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
      (toLex (s, b))).2] at hb
  have hnonpos := support_subset x hb
  rw [HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall_apply] at hnonpos
  simp only [ofLex_toLex] at hnonpos
  change ((s : G) + (b : G)) ≤ 0 at hnonpos
  have hlex : toLex (s, b) ≤ 0 := by
    apply (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c).map_le_map_iff'.mp
    apply Subtype.coe_le_coe.mp
    convert hnonpos using 1 <;>
      simp [HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall_apply]
  rcases Prod.Lex.le_iff.mp hlex with hsle | ⟨hszero, _⟩
  · exact hsle.le
  · simpa using hszero.le

private theorem support_div_C_subset {A H : Type*} [Field A]
    [AddCommGroup H] [LinearOrder H] [IsOrderedAddMonoid H]
    (x : A⟦H⟧) (a : A) :
    (x / (HahnSeries.C a : A⟦H⟧)).support ⊆ x.support := by
  intro h hh
  rw [div_eq_mul_inv, ← map_inv₀ HahnSeries.C] at hh
  obtain ⟨i, hi, j, hj, hij⟩ := HahnSeries.support_mul_subset hh
  have hj0 : j = 0 := HahnSeries.support_single_subset hj
  have hih : i = h := by simpa [hj0] using hij
  simpa [hih] using hi

/-- Dividing the split closed-class truncation by the open-class scalar does not introduce
positive outer exponents. -/
theorem support_archimedeanSplitRingEquiv_TClosed_div_C_subset
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    ((HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x)) /
      (HahnSeries.C (tauBall c x) :
        (R⟦ball K c⟧)⟦u.stratum c⟧)).support ⊆ Set.Iic 0 :=
  (support_div_C_subset _ _).trans (support_archimedeanSplitRingEquiv_TClosed_subset u c x)

/-- In the nonzero branch of LM24's reduction, the outer-zero coefficient of the quotient is
one. This rules out positive infinitesimal exponents at the only outer boundary where the outer
support condition alone would be insufficient. -/
theorem coeff_zero_archimedeanSplitRingEquiv_TClosed_div_C
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (htau : tauBall (K := K) c x ≠ 0) :
    (((HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x)) /
      (HahnSeries.C (tauBall c x) :
        (R⟦ball K c⟧)⟦u.stratum c⟧)).coeff 0) = 1 := by
  rw [div_eq_mul_inv]
  rw [HahnSeries.C_apply, HahnSeries.inv_single]
  simp only [neg_zero]
  rw [HahnSeries.coeff_mul_single_zero]
  rw [coeff_zero_archimedeanSplitRingEquiv_TClosed]
  exact mul_inv_cancel₀ htau

private def splitQuotient (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    (R⟦ball K c⟧)⟦u.stratum c⟧ :=
  HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x) /
    HahnSeries.C (tauBall c x)

/-- If an iterated Hahn series has no positive outer exponents and its coefficient at outer
exponent zero has no positive inner exponents, then its image back on the closed Archimedean ball
has no positive exponents. -/
theorem support_archimedeanSplitRingEquiv_symm_subset_Iic
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (y : (R⟦ball K c⟧)⟦u.stratum c⟧)
    (hyOuter : y.support ⊆ Set.Iic 0)
    (hyZero : (y.coeff 0).support ⊆ Set.Iic 0) :
    ((HahnSeries.archimedeanSplitRingEquiv u c).symm y).support ⊆ Set.Iic 0 := by
  intro g hg
  let p := HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall u c g
  let s : u.stratum c := (ofLex p).1
  let b : ball K c := (ofLex p).2
  have hsplitBack :
      HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c p = g :=
    ArchimedeanStrata.stratumLexBallEquivClosedBall_closedBallEquivStratumLexBall
      u c g
  have hcoeff : (y.coeff s).coeff b ≠ 0 := by
    have h := congrArg (fun z : (R⟦ball K c⟧)⟦u.stratum c⟧ ↦
        (z.coeff s).coeff b)
      ((HahnSeries.archimedeanSplitRingEquiv u c).apply_symm_apply y)
    rw [HahnSeries.archimedeanSplitRingEquiv_coeff] at h
    rw [show HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
      (toLex (s, b)) = g by
        change HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c p = g
        exact hsplitBack] at h
    exact fun hzero ↦ hg (h.trans hzero)
  have hsupp : s ∈ y.support := by
    rw [HahnSeries.mem_support]
    intro hzero
    exact hcoeff (congrArg (fun z : R⟦ball K c⟧ ↦ z.coeff b) hzero)
  have hsnonpos : s ≤ 0 := hyOuter hsupp
  rcases hsnonpos.eq_or_lt with hs0 | hsneg
  · have hbzero : b ≤ 0 := by
      apply hyZero
      rw [HahnSeries.mem_support]
      simpa [hs0] using hcoeff
    have hpnonpos : p ≤ 0 := by
      apply Prod.Lex.le_iff.mpr
      exact Or.inr ⟨hs0, hbzero⟩
    rw [← hsplitBack, ←
      (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c).map_zero]
    apply
      (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c).map_le_map_iff'.mpr
    exact hpnonpos
  · have hpneg : p < 0 := Prod.Lex.lt_iff.mpr (Or.inl hsneg)
    have hgneg : g < 0 := by
      rw [← hsplitBack]
      apply lt_of_not_ge
      intro hge
      rw [←
        (HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c).map_zero] at hge
      let e := HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
      have hpge : 0 ≤ p := by
        exact e.map_le_map_iff'.mp hge
      exact (not_le_of_gt hpneg) hpge
    exact hgneg.le

private theorem support_splitQuotient_symm_subset
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (htau : tauBall (K := K) c x ≠ 0) :
    ((HahnSeries.archimedeanSplitRingEquiv u c).symm
      (splitQuotient u c x)).support ⊆ Set.Iic 0 := by
  apply support_archimedeanSplitRingEquiv_symm_subset_Iic u c
  · exact support_archimedeanSplitRingEquiv_TClosed_div_C_subset u c x
  · change
      ((((HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x)) /
        HahnSeries.C (tauBall c x)).coeff 0).support ⊆ Set.Iic 0)
    rw [coeff_zero_archimedeanSplitRingEquiv_TClosed_div_C u c x htau]
    intro b hb
    exact (HahnSeries.support_single_subset hb).le

/-- The nonzero quotient branch in LM24, Definition 8.2.4, as a nonpositive Hahn series. -/
def reductionQuotient (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (htau : tauBall (K := K) c x ≠ 0) : Nonpositive G R :=
  ⟨HahnSeries.embDomain (closedBallOrderEmbedding c)
      ((HahnSeries.archimedeanSplitRingEquiv u c).symm (splitQuotient u c x)), by
    change (HahnSeries.embDomain (closedBallOrderEmbedding c)
      ((HahnSeries.archimedeanSplitRingEquiv u c).symm
        (splitQuotient u c x))).support ⊆ Set.Iic 0
    rw [HahnSeries.support_embDomain]
    rintro _ ⟨g, hg, rfl⟩
    exact support_splitQuotient_symm_subset u c x htau hg⟩

/-- In the nonzero branch of LM24's reduction, the coefficient at the exponent zero is one: the
outer-zero coefficient of the split quotient is the constant one. -/
theorem coeff_zero_reductionQuotient (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (htau : tauBall (K := K) c x ≠ 0) :
    ((reductionQuotient u c x htau : Nonpositive G R) : R⟦G⟧).coeff 0 = 1 := by
  change (HahnSeries.embDomain (closedBallOrderEmbedding c)
    ((HahnSeries.archimedeanSplitRingEquiv u c).symm (splitQuotient u c x))).coeff 0 = 1
  have h0 : (0 : G) = closedBallOrderEmbedding (K := K) c 0 := by
    rw [closedBallOrderEmbedding_apply]; rfl
  rw [h0, HahnSeries.embDomain_coeff]
  have hsplit := HahnSeries.archimedeanSplitRingEquiv_coeff u c
    ((HahnSeries.archimedeanSplitRingEquiv u c).symm (splitQuotient u c x)) 0 0
  rw [RingEquiv.apply_symm_apply] at hsplit
  have hzero : HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
      (toLex ((0 : u.stratum c), (0 : ball K c))) = 0 := by
    apply Subtype.ext
    rw [HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall_apply]
    simp
  rw [hzero] at hsplit
  rw [← hsplit]
  change ((HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x) /
    HahnSeries.C (tauBall c x)).coeff 0).coeff 0 = 1
  rw [coeff_zero_archimedeanSplitRingEquiv_TClosed_div_C u c x htau]
  rw [HahnSeries.coeff_one, if_pos rfl]

/-- LM24's `ρ_σ`: divide the closed-class truncation by the open-class truncation when the
latter is nonzero, and otherwise retain the closed-class truncation. -/
def rho (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R) : Nonpositive G R :=
  by
    classical
    exact if htau : tauBall (K := K) c x = 0 then T (K := K) c x
      else reductionQuotient u c x htau

/-- The open-ball restriction vanishes exactly when the original open-class truncation does. -/
theorem tauBall_eq_zero_iff (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    tauBall (K := K) c x = 0 ↔ tau (K := K) c x = 0 := by
  constructor
  · intro hzero
    apply Subtype.ext
    ext g
    by_cases hg : g ∈ ball K c
    · have hcoeff := congrArg (fun y : R⟦ball K c⟧ ↦
          y.coeff ⟨g, hg⟩) hzero
      rw [tauBall, HahnSeries.restrictDomain_coeff] at hcoeff
      change ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff g = 0 at hcoeff
      exact hcoeff
    · rw [coeff_tau_of_not_mem (K := K) c x hg]
      simp
  · intro hzero
    ext b
    rw [tauBall, HahnSeries.restrictDomain_coeff]
    change ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff (b : G) = 0
    rw [hzero]
    simp

/-- Restricting an open-class truncation equal to one to its open ball yields one. -/
theorem tauBall_eq_one_of_tau_eq_one (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (htau : tau (K := K) c x = 1) :
    tauBall (K := K) c x = 1 := by
  ext b
  rw [tauBall, HahnSeries.restrictDomain_coeff]
  change ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).coeff (b : G) = _
  rw [htau]
  simp

/-- In the zero branch, LM24's reduction is the closed-class truncation. -/
theorem rho_of_tau_eq_zero (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (htau : tau (K := K) c x = 0) :
    rho u c x = T (K := K) c x := by
  rw [rho]
  split
  · rfl
  · rename_i hne
    exact (hne ((tauBall_eq_zero_iff c x).mpr htau)).elim

/-- In the nonzero branch, LM24's reduction uses the quotient constructed through the
Archimedean splitting. -/
theorem rho_of_tau_ne_zero (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (htau : tau (K := K) c x ≠ 0) :
    rho u c x = reductionQuotient u c x
      (fun hzero ↦ htau ((tauBall_eq_zero_iff c x).mp hzero)) := by
  rw [rho]
  split
  · rename_i hzero
    exact (htau ((tauBall_eq_zero_iff c x).mp hzero)).elim
  · rfl

theorem support_T_subset_range (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).support ⊆
      Set.range (closedBallOrderEmbedding (K := K) c) := by
  intro g hg
  have hmem : g ∈ closedBall K c := by
    by_contra hnot
    exact hg (coeff_T_of_not_mem (K := K) c x hnot)
  exact ⟨⟨g, hmem⟩, rfl⟩

private theorem support_tau_subset_range (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).support ⊆
      Set.range (closedBallOrderEmbedding (K := K) c) := by
  intro g hg
  have hmem : g ∈ closedBall K c := by
    by_contra hnot
    have hnotBall : g ∉ ball K c := fun hball ↦
      hnot ((FiniteArchimedeanClass.ball_lt_closedBall (K := K)).le hball)
    exact hg (coeff_tau_of_not_mem (K := K) c x hnotBall)
  exact ⟨⟨g, hmem⟩, rfl⟩

theorem embDomain_TClosed (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c) (TClosed (K := K) c x) =
      ((T (K := K) c x : Nonpositive G R) : R⟦G⟧) :=
  HahnSeries.embDomain_restrictDomain _ _ (support_T_subset_range c x)

/-- The closed-class truncation with its exponent domain restricted, as a ring homomorphism. -/
def TClosedRingHom (c : FiniteArchimedeanClass G) :
    Nonpositive G R →+* R⟦closedBall K c⟧ where
  toFun := TClosed c
  map_zero' := by
    ext g
    rw [TClosed, HahnSeries.restrictDomain_coeff, map_zero]
    rfl
  map_one' := by
    ext g
    rw [TClosed, HahnSeries.restrictDomain_coeff, map_one]
    change (1 : R⟦G⟧).coeff (g : G) = (1 : R⟦closedBall K c⟧).coeff g
    simp
  map_add' x y := by
    ext g
    rw [TClosed, HahnSeries.restrictDomain_coeff, map_add]
    change (((T (K := K) c x : Nonpositive G R) : R⟦G⟧) +
      ((T (K := K) c y : Nonpositive G R) : R⟦G⟧)).coeff (g : G) = _
    rw [HahnSeries.coeff_add, HahnSeries.coeff_add]
    rw [TClosed, TClosed, HahnSeries.restrictDomain_coeff,
      HahnSeries.restrictDomain_coeff]
    rfl
  map_mul' x y := by
    apply (HahnSeries.embDomain_injective
      (R := R) (f := closedBallOrderEmbedding (K := K) c))
    rw [HahnSeries.embDomain_mul (f := closedBallOrderEmbedding (K := K) c)
      (fun _ _ ↦ rfl)]
    change HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c)
        (TClosed (K := K) c (x * y)) = _
    rw [embDomain_TClosed]
    rw [map_mul]
    change ((T (K := K) c x : Nonpositive G R) : R⟦G⟧) *
        ((T (K := K) c y : Nonpositive G R) : R⟦G⟧) = _
    rw [← embDomain_TClosed, ← embDomain_TClosed]

@[simp]
theorem TClosedRingHom_apply (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    TClosedRingHom (K := K) c x = TClosed c x :=
  (rfl)

private theorem embDomain_tauClosed (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c) (tauClosed (K := K) c x) =
      ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧) :=
  HahnSeries.embDomain_restrictDomain _ _ (support_tau_subset_range c x)

/-- The nonzero reduction quotient multiplied by the open-class truncation recovers the
closed-class truncation. This is the defining quotient identity from LM24, Definition 8.2.4. -/
theorem reductionQuotient_mul_tau (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R)
    (htau : tauBall (K := K) c x ≠ 0) :
    reductionQuotient u c x htau * tau (K := K) c x = T (K := K) c x := by
  apply Subtype.ext
  change HahnSeries.embDomain (closedBallOrderEmbedding c)
      ((HahnSeries.archimedeanSplitRingEquiv u c).symm (splitQuotient u c x)) *
      ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧) =
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧)
  rw [← embDomain_tauClosed (K := K) c x, ← embDomain_TClosed (K := K) c x]
  rw [← HahnSeries.embDomain_mul (f := closedBallOrderEmbedding (K := K) c)
    (fun _ _ ↦ rfl)]
  apply congrArg (HahnSeries.embDomain (closedBallOrderEmbedding (K := K) c))
  apply (HahnSeries.archimedeanSplitRingEquiv u c).injective
  rw [map_mul, RingEquiv.apply_symm_apply]
  rw [archimedeanSplitRingEquiv_tauClosed]
  change splitQuotient u c x * HahnSeries.C (tauBall c x) =
    HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x)
  rw [splitQuotient, div_eq_mul_inv, mul_assoc]
  let a : (R⟦ball K c⟧)⟦u.stratum c⟧ := HahnSeries.C (tauBall c x)
  have hC : a ≠ 0 := HahnSeries.C_ne_zero htau
  have hinv : a⁻¹ * a = 1 := by
    rw [mul_comm]
    exact Field.mul_inv_cancel a hC
  change HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x) * (a⁻¹ * a) = _
  rw [hinv, mul_one]

/-- At a class containing the whole series, a nonzero fixed point of `rho` has open truncation
zero or one. This is the fixed-class core of LM24, Proposition 8.2.5 (3) iff (4). -/
theorem rho_eq_self_iff_tau_eq_zero_or_one
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : x ≠ 0) (hT : T (K := K) c x = x) :
    rho u c x = x ↔ tau (K := K) c x = 0 ∨ tau (K := K) c x = 1 := by
  constructor
  · intro hrho
    by_cases htau : tau (K := K) c x = 0
    · exact Or.inl htau
    · right
      have hmul := reductionQuotient_mul_tau u c x
        (fun hzero ↦ htau ((tauBall_eq_zero_iff c x).mp hzero))
      rw [← rho_of_tau_ne_zero u c x htau, hrho, hT] at hmul
      exact mul_left_cancel₀ hx (hmul.trans (mul_one x).symm)
  · rintro (htau | htau)
    · rw [rho_of_tau_eq_zero u c x htau, hT]
    · have htauNe : tau (K := K) c x ≠ 0 := by rw [htau]; exact one_ne_zero
      have hmul := reductionQuotient_mul_tau u c x
        (fun hzero ↦ htauNe ((tauBall_eq_zero_iff c x).mp hzero))
      have hmul' : reductionQuotient u c x
          (fun hzero ↦ htauNe ((tauBall_eq_zero_iff c x).mp hzero)) = x := by
        have hone : reductionQuotient u c x
            (fun hzero ↦ htauNe ((tauBall_eq_zero_iff c x).mp hzero)) * 1 =
            reductionQuotient u c x
              (fun hzero ↦ htauNe ((tauBall_eq_zero_iff c x).mp hzero)) :=
          mul_one _
        exact hone.symm.trans ((congrArg
          (fun t : Nonpositive G R ↦ reductionQuotient u c x
            (fun hzero ↦ htauNe ((tauBall_eq_zero_iff c x).mp hzero)) * t)
          htau.symm).trans (hmul.trans hT))
      exact (rho_of_tau_ne_zero u c x htauNe).trans hmul'

/-- At the class of a nonzero, nonconstant series' lowest exponent, LM24's reduction fixes the
series exactly when its open-class truncation is zero or one. This is Proposition 8.2.5
`(3) ↔ (4)` away from the separate constant-series case. -/
theorem rho_leadingClass_eq_self_iff_tau_eq_zero_or_one
    (u : HahnEmbedding.ArchimedeanStrata K G) (x : Nonpositive G R) (hx : x ≠ 0)
    (horder : (x : R⟦G⟧).order ≠ 0) :
    rho u (leadingClass x horder) x = x ↔
      tau (K := K) (leadingClass x horder) x = 0 ∨
        tau (K := K) (leadingClass x horder) x = 1 :=
  rho_eq_self_iff_tau_eq_zero_or_one u (leadingClass x horder) x hx
    (T_leadingClass x horder)

end HahnSeries.Nonpositive
