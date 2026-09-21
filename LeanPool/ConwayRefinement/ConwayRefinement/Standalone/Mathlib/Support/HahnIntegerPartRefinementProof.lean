/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.HahnIntegerPartRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.Mathlib.Examples.HahnIntegerPartRefinementCriterion

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.Refinement
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.PrimalPreimage
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.Module.ArchimedeanBallSplitting
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.CoinitialComplete
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.LimitTailPrimality
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.ArchimedeanBall
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Real.Embedding
import Mathlib.SetTheory.Cardinal.Rat

/-!
# Proof of refinement in cardinal-bounded Hahn integer parts

The finite-class argument uses conditions `(A1)`--`(A3)` from LM24. The common-tail hypotheses
extend primality to every bounded generalised-power-series integer part, and primality gives the
four-factor refinement property.
-/

public noncomputable section

open Cardinal
open HahnSeries.CardSuppLTTruncationIntegerPart

namespace ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinement

universe u v

variable {G : Type u} {R : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module ℚ G] [IsOrderedModule ℚ G]
variable [Field R]

local instance : PosSMulStrictMono ℚ G := PosSMulMono.toPosSMulStrictMono

omit [IsOrderedAddMonoid G] [Module ℚ G] [IsOrderedModule ℚ G] in
theorem mem_hahnIntegerPart_iff {Z : Subring R} {κ : Cardinal.{u}} {x : HahnSeries G R} :
    x ∈ hahnIntegerPart Z κ ↔
      x.cardSupp < κ ∧ x.support ⊆ Set.Iic 0 ∧ x.coeff 0 ∈ Z :=
  Iff.rfl

omit [Module ℚ G] [IsOrderedModule ℚ G] in
theorem isFractionFieldOfHahnIntegerPart_iff {Z : Subring R} {κ : Cardinal.{u}} :
    IsFractionFieldOfHahnIntegerPart (G := G) Z κ ↔
      ∀ x : HahnSeries G R, x.cardSupp < κ →
        ∃ a b : HahnSeries G R,
          a ∈ hahnIntegerPart Z κ ∧ b ∈ hahnIntegerPart Z κ ∧ b ≠ 0 ∧ x = a / b :=
  Iff.rfl

omit [IsOrderedAddMonoid G] [Module ℚ G] [IsOrderedModule ℚ G] in
theorem mem_integerHahnPart_iff {κ : Cardinal.{u}} {x : HahnSeries G R} :
    x ∈ integerHahnPart κ ↔
      x.cardSupp < κ ∧ x.support ⊆ Set.Iic 0 ∧ ∃ z : ℤ, (z : R) = x.coeff 0 :=
  Iff.rfl

theorem assumptionA1_iff {s : HahnEmbedding.ArchimedeanStrata ℚ G} :
    AssumptionA1 s ↔
      ∀ c : FiniteArchimedeanClass G, Nonempty (s.stratum c ≃+o ℝ) :=
  Iff.rfl

theorem generatesFractionField_iff {Z : Subring R} :
    GeneratesFractionField Z ↔
      ∀ x : R, ∃ a b : Z, b ≠ 0 ∧ x = (a : R) / (b : R) :=
  Iff.rfl

theorem assumptionA2_iff {Z : Subring R} {κ : Cardinal.{u}} :
    AssumptionA2 (G := G) Z κ ↔
      ∀ c : FiniteArchimedeanClass G,
        κ ≤ Order.cof ↑(FiniteArchimedeanClass.ball ℚ c) ∨
          (Subsingleton ↑(FiniteArchimedeanClass.ball ℚ c) ∧ GeneratesFractionField Z) :=
  Iff.rfl

theorem assumptionA3_iff {Z : Subring R} :
    AssumptionA3 Z ↔
      ∀ z a b : Z, z ∣ a * b →
        ∃ z₁ z₂ : Z, z₁ ∣ a ∧ z₂ ∣ b ∧ z = z₁ * z₂ :=
  Iff.rfl

omit [Module ℚ G] [IsOrderedModule ℚ G] in
theorem isLimitFamily_iff {T : Set (FiniteArchimedeanClass G)} :
    IsLimitFamily T ↔ T.Nonempty ∧ ∀ c ∈ T, ∃ d ∈ T, c < d :=
  Iff.rfl

omit [AddCommGroup G] [IsOrderedAddMonoid G] [Module ℚ G] [IsOrderedModule ℚ G] in
theorem isKappaSaturated_iff {κ : Cardinal.{u}} :
    IsKappaSaturated (G := G) κ ↔
      ∀ L R : Set G, #L < κ → #R < κ →
        (∀ l ∈ L, ∀ r ∈ R, l < r) →
          ∃ x : G, (∀ l ∈ L, l < x) ∧ ∀ r ∈ R, x < r :=
  Iff.rfl

/-- The standalone common-tail definition agrees with the canonical common-tail subspace used by
the proof. -/
theorem commonTail_eq_tailSubmodule
    (T : Set (FiniteArchimedeanClass G)) :
    commonTail T = _root_.FiniteArchimedeanClass.tailSubmodule ℚ T := by
  ext x
  rw [mem_commonTail_iff,
    _root_.FiniteArchimedeanClass.mem_tailSubmodule_iff,
    _root_.FiniteArchimedeanClass.mem_tailKernel_iff]

/-- The standalone and canonical common-tail subspaces are order-isomorphic. -/
def commonTailSubtypeOrderIso (T : Set (FiniteArchimedeanClass G)) :
    commonTail T ≃o _root_.FiniteArchimedeanClass.tailSubmodule ℚ T where
  toFun x := ⟨x, by
    rw [← commonTail_eq_tailSubmodule (G := G) T]
    exact x.2⟩
  invFun x := ⟨x, by
    rw [commonTail_eq_tailSubmodule (G := G) T]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The two independently stated common-tail quotients are the same ordered additive group. -/
noncomputable def commonTailOrderAddMonoidIso
    (T : Set (FiniteArchimedeanClass G)) :
    (G ⧸ commonTail T) ≃+o
      (G ⧸ _root_.FiniteArchimedeanClass.tailSubmodule ℚ T) := by
  let h := commonTail_eq_tailSubmodule (G := G) T
  refine { (Submodule.quotEquivOfEq (commonTail T)
      (_root_.FiniteArchimedeanClass.tailSubmodule ℚ T) h).toAddEquiv with
    map_le_map_iff' := ?_ }
  intro a b
  refine Submodule.Quotient.induction_on (commonTail T) a fun a ↦ ?_
  refine Submodule.Quotient.induction_on (commonTail T) b fun b ↦ ?_
  change
    ((Submodule.Quotient.mk a :
        G ⧸ _root_.FiniteArchimedeanClass.tailSubmodule ℚ T) ≤
      Submodule.Quotient.mk b) ↔
    ((Submodule.Quotient.mk a : G ⧸ commonTail T) ≤
      Submodule.Quotient.mk b)
  have htarget :
      ((Submodule.Quotient.mk a :
          G ⧸ _root_.FiniteArchimedeanClass.tailSubmodule ℚ T) ≤
        Submodule.Quotient.mk b) ↔
        a ≤ b ∨ b - a ∈ _root_.FiniteArchimedeanClass.tailSubmodule ℚ T := by
    exact _root_.ConvexQuotient.mk_le_mk_iff
  have hsource :
      ((Submodule.Quotient.mk a : G ⧸ commonTail T) ≤
        Submodule.Quotient.mk b) ↔ a ≤ b ∨ b - a ∈ commonTail T := by
    exact ConvexQuotient.mk_le_mk_iff
  exact htarget.trans ((or_congr Iff.rfl (by rw [h])).trans hsource.symm)

/-- The independent common-tail quotient presentations have the same additive uniformity. -/
noncomputable def commonTailUniformEquiv
    (T : Set (FiniteArchimedeanClass G)) :
    (G ⧸ commonTail T) ≃ᵤ
      (G ⧸ _root_.FiniteArchimedeanClass.tailSubmodule ℚ T) := by
  let e := commonTailOrderAddMonoidIso (G := G) T
  exact
    { e.toEquiv with
      uniformContinuous_toFun :=
        uniformContinuous_of_continuousAt_zero e.toAddEquiv
          e.toOrderIso.continuous.continuousAt
      uniformContinuous_invFun :=
        uniformContinuous_of_continuousAt_zero e.symm.toAddEquiv
          e.symm.toOrderIso.continuous.continuousAt }

omit [AddCommGroup G] [IsOrderedAddMonoid G] [Module ℚ G] [IsOrderedModule ℚ G] in
private theorem fillsCuts_of_isKappaSaturated {κ : Cardinal.{u}}
    (hG : IsKappaSaturated (G := G) κ) {ι : Type u} (hι : #ι < κ) :
    FillsCuts ι G := by
  rw [isKappaSaturated_iff] at hG
  rw [fillsCuts_iff]
  intro L R hLR
  have hL : #(Set.range L) < κ := Cardinal.mk_range_le.trans_lt hι
  have hR : #(Set.range R) < κ := Cardinal.mk_range_le.trans_lt hι
  obtain ⟨x, hxL, hxR⟩ := hG (Set.range L) (Set.range R) hL hR
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hLR i j)
  exact ⟨x, fun i ↦ (hxL _ ⟨i, rfl⟩).le, fun j ↦ (hxR _ ⟨j, rfl⟩).le⟩

@[blueprint "lem:saturated-archimedean-strata-real"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Archimedean strata of saturated ordered groups")
  (statement := /--
    Let $\kappa>\aleph_0$ and let $G$ be a $\kappa$-saturated ordered rational
    vector space.  Every Archimedean stratum in any Hahn splitting of $G$ is
    order additively isomorphic to $\mathbb R$.
  -/)
  (proof := /--
    Embed a stratum order additively into $\mathbb R$ and fix a positive
    element whose image is $\rho>0$.  For $y\in\mathbb R$, the rational
    multiples $q\rho<y$ and $q\rho>y$ define two countable subsets of $G$.
    Saturation supplies an element between them.  It lies in the corresponding
    closed Archimedean ball; project it to the stratum using the lexicographic
    splitting of that ball.  Comparison with every rational multiple forces
    the projected element to map to $y$.  Thus the embedding is surjective.
  -/)]
private theorem stratum_orderAddEquiv_real_of_isKappaSaturated
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hG : IsKappaSaturated (G := G) κ)
    (s : HahnEmbedding.ArchimedeanStrata ℚ G) (c : FiniteArchimedeanClass G) :
    Nonempty (s.stratum c ≃+o ℝ) := by
  rw [isKappaSaturated_iff] at hG
  let S := s.stratum c
  obtain ⟨f, hf⟩ := Archimedean.exists_orderAddMonoidHom_real_injective S
  have hfmono : StrictMono f :=
    (OrderHomClass.monotone f).strictMono_of_injective hf
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : S)
  let a : S := |a₀|
  have ha : 0 < a := abs_pos.mpr ha₀
  let ρ : ℝ := f a
  have hρ : 0 < ρ := by
    change 0 < f a
    simpa using hfmono ha
  have hsurj : Function.Surjective f := by
    intro y
    let L : Set G := {x | ∃ q : ℚ, (q : ℝ) * ρ < y ∧ x = (q • a : S)}
    let R : Set G := {x | ∃ q : ℚ, y < (q : ℝ) * ρ ∧ x = (q • a : S)}
    have hLcard : #L < κ := by
      refine (Cardinal.mk_le_mk_of_subset (s := L)
        (t := Set.range (fun q : ULift.{u} ℚ ↦ ((q.down • a : S) : G))) ?_).trans_lt ?_
      · rintro x ⟨q, -, rfl⟩
        exact ⟨ULift.up q, rfl⟩
      · refine Cardinal.mk_range_le.trans_lt ?_
        rw [Cardinal.mk_uLift, Cardinal.mkRat, Cardinal.lift_aleph0]
        exact hκ
    have hRcard : #R < κ := by
      refine (Cardinal.mk_le_mk_of_subset (s := R)
        (t := Set.range (fun q : ULift.{u} ℚ ↦ ((q.down • a : S) : G))) ?_).trans_lt ?_
      · rintro x ⟨q, -, rfl⟩
        exact ⟨ULift.up q, rfl⟩
      · refine Cardinal.mk_range_le.trans_lt ?_
        rw [Cardinal.mk_uLift, Cardinal.mkRat, Cardinal.lift_aleph0]
        exact hκ
    have hLR : ∀ l ∈ L, ∀ r ∈ R, l < r := by
      rintro l ⟨q, hqy, rfl⟩ r ⟨q', hyq', rfl⟩
      apply Subtype.coe_lt_coe.mp
      apply hfmono.lt_iff_lt.mp
      rw [map_rat_smul, map_rat_smul]
      change (q : ℝ) * ρ < (q' : ℝ) * ρ
      exact hqy.trans hyq'
    obtain ⟨x, hxL, hxR⟩ := hG L R hLcard hRcard hLR
    obtain ⟨qₗ, hqₗ⟩ := exists_rat_lt (y / ρ)
    obtain ⟨qᵣ, hqᵣ⟩ := exists_rat_gt (y / ρ)
    have hqₗ' : (qₗ : ℝ) * ρ < y := by rwa [lt_div_iff₀ hρ] at hqₗ
    have hqᵣ' : y < (qᵣ : ℝ) * ρ := by rwa [div_lt_iff₀ hρ] at hqᵣ
    have hqₗL : ((qₗ • a : S) : G) ∈ L := ⟨qₗ, hqₗ', rfl⟩
    have hqᵣR : ((qᵣ • a : S) : G) ∈ R := ⟨qᵣ, hqᵣ', rfl⟩
    have hstratumClosed (z : S) : (z : G) ∈ FiniteArchimedeanClass.closedBall ℚ c := by
      rw [← s.ball_sup_stratum_eq c]
      exact Submodule.mem_sup_right z.2
    have hxclosed : x ∈ FiniteArchimedeanClass.closedBall ℚ c := by
      have hl := hstratumClosed (qₗ • a)
      have hr := hstratumClosed (qᵣ • a)
      exact FiniteArchimedeanClass.closedBall_ordConnected c |>.out hl hr
        ⟨(hxL _ hqₗL).le, (hxR _ hqᵣR).le⟩
    let xClosed : FiniteArchimedeanClass.closedBall ℚ c := ⟨x, hxclosed⟩
    let p := s.closedBallEquivStratumLexBall c xClosed
    let z : S := (ofLex p).1
    have hfirst_le_of_mem_L (q : ℚ) (hq : (q : ℝ) * ρ < y) : q • a ≤ z := by
      have hqL : ((q • a : S) : G) ∈ L := ⟨q, hq, rfl⟩
      let qClosed : FiniteArchimedeanClass.closedBall ℚ c :=
        ⟨((q • a : S) : G), hstratumClosed (q • a)⟩
      have hqClosed : s.stratumLexBallEquivClosedBall c
          (toLex (q • a, (0 : FiniteArchimedeanClass.ball ℚ c))) = qClosed := by
        apply Subtype.ext
        rw [s.stratumLexBallEquivClosedBall_apply]
        simp [qClosed]
      have hlt : s.closedBallEquivStratumLexBall c qClosed < p := by
        change s.closedBallEquivStratumLexBall c qClosed <
          s.closedBallEquivStratumLexBall c xClosed
        apply (s.closedBallEquivStratumLexBall c).toOrderIso.lt_iff_lt.mpr
        exact hxL _ hqL
      rw [← hqClosed,
        s.closedBallEquivStratumLexBall_stratumLexBallEquivClosedBall] at hlt
      exact (Prod.Lex.lt_iff.mp hlt).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
    have hfirst_ge_of_mem_R (q : ℚ) (hq : y < (q : ℝ) * ρ) : z ≤ q • a := by
      have hqR : ((q • a : S) : G) ∈ R := ⟨q, hq, rfl⟩
      let qClosed : FiniteArchimedeanClass.closedBall ℚ c :=
        ⟨((q • a : S) : G), hstratumClosed (q • a)⟩
      have hqClosed : s.stratumLexBallEquivClosedBall c
          (toLex (q • a, (0 : FiniteArchimedeanClass.ball ℚ c))) = qClosed := by
        apply Subtype.ext
        rw [s.stratumLexBallEquivClosedBall_apply]
        simp [qClosed]
      have hlt : p < s.closedBallEquivStratumLexBall c qClosed := by
        change s.closedBallEquivStratumLexBall c xClosed <
          s.closedBallEquivStratumLexBall c qClosed
        apply (s.closedBallEquivStratumLexBall c).toOrderIso.lt_iff_lt.mpr
        exact hxR _ hqR
      rw [← hqClosed,
        s.closedBallEquivStratumLexBall_stratumLexBallEquivClosedBall] at hlt
      exact (Prod.Lex.lt_iff.mp hlt).elim (fun h ↦ h.le) (fun h ↦ h.1.le)
    refine ⟨z, le_antisymm ?_ ?_⟩
    · by_contra hnot
      have hyfz : y < f z := lt_of_not_ge hnot
      obtain ⟨q, hq₁, hq₂⟩ :=
        exists_rat_btwn ((div_lt_div_iff_of_pos_right hρ).mpr hyfz)
      have hyq : y < (q : ℝ) * ρ := (div_lt_iff₀ hρ).mp hq₁
      have hqfz : (q : ℝ) * ρ < f z := (lt_div_iff₀ hρ).mp hq₂
      have hzq := hfirst_ge_of_mem_R q hyq
      have := hfmono.monotone hzq
      rw [map_rat_smul] at this
      exact (not_le_of_gt hqfz) this
    · by_contra hnot
      have hfzy : f z < y := lt_of_not_ge hnot
      obtain ⟨q, hq₁, hq₂⟩ :=
        exists_rat_btwn ((div_lt_div_iff_of_pos_right hρ).mpr hfzy)
      have hfzq : f z < (q : ℝ) * ρ := (div_lt_iff₀ hρ).mp hq₁
      have hqy : (q : ℝ) * ρ < y := (lt_div_iff₀ hρ).mp hq₂
      have hqz := hfirst_le_of_mem_L q hqy
      have := hfmono.monotone hqz
      rw [map_rat_smul] at this
      exact (not_le_of_gt hfzq) this
  exact ⟨{ AddEquiv.ofBijective f ⟨hf, hsurj⟩ with
    map_le_map_iff' := hfmono.le_iff_le }⟩

@[blueprint "lem:saturated-common-tail-quotient-complete"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Cauchy completeness of common-tail quotients")
  (statement := /--
    Let $G$ be a $\kappa$-saturated ordered rational vector space.  Let $T$ be
    a nonempty set of fewer than $\kappa$ nonzero Archimedean classes with no
    least member in the magnitude order, and let $H_T$ consist of the
    exponents beyond every class in $T$.  Then $G/H_T$ is Cauchy complete for
    its additive uniformity.
  -/)
  (proof := /--
    Positive representatives of the classes in $T$ descend to a coinitial
    family in $G/H_T$, and rational halving gives arbitrarily small doubled
    scales.  Every cut between two $T$-indexed families in $G$ is filled by
    $\kappa$-saturation; by
    \ref{lem:cut-filling-order-reflecting-surjection}, the monotone quotient
    map, which reflects strict inequalities, transfers this cut-filling
    property to $G/H_T$.  Apply
    \ref{lem:complete-of-coinitial-scales-and-cut-filling}.
  -/)]
private theorem completeSpace_tailQuotient_of_isKappaSaturated
    {κ : Cardinal.{u}} (hG : IsKappaSaturated (G := G) κ)
    (T : Set (FiniteArchimedeanClass G)) (hT : IsLimitFamily T) (hTcard : #T < κ) :
    Nonempty (CompleteSpace (G ⧸ commonTail T)) := by
  rw [isLimitFamily_iff] at hT
  letI : Nonempty T := Set.nonempty_coe_sort.mpr hT.1
  let Q := G ⧸ commonTail T
  let ε : T → Q := fun c ↦
    Submodule.Quotient.mk (FiniteArchimedeanClass.positiveRepresentative c.1)
  have hε : ∀ c, 0 < ε c := by
    intro c
    apply ConvexQuotient.mk_lt_mk_iff.mpr
    refine ⟨FiniteArchimedeanClass.positiveRepresentative_pos c.1, ?_⟩
    intro hmem
    have hmem' : FiniteArchimedeanClass.positiveRepresentative c.1 ∈
        (commonTail T).toAddSubgroup := by
      simpa only [sub_zero] using hmem
    have hmem'' : FiniteArchimedeanClass.positiveRepresentative c.1 ∈ commonTail T := hmem'
    obtain ⟨d, hdT, hcd⟩ := hT.2 c.1 c.2
    have hdle := mem_commonTail_iff.mp hmem'' ⟨d, hdT⟩
    rw [FiniteArchimedeanClass.mk_positiveRepresentative] at hdle
    exact (not_le_of_gt hcd) hdle
  have hcoinitial : ∀ x : Q, 0 < x → ∃ c, ε c ≤ x := by
    intro x hx
    exact FiniteArchimedeanClass.exists_tailQuotient_positiveRepresentative_le hx
  have hhalf : ∀ x : Q, 0 < x → ∃ y : Q, 0 < y ∧ y + y ≤ x := by
    intro x hx
    refine ⟨(2 : ℚ)⁻¹ • x, smul_pos (by norm_num) hx, ?_⟩
    rw [← add_smul]
    norm_num
  have hfillG : FillsCuts T G := fillsCuts_of_isKappaSaturated hG hTcard
  have hfillQ : FillsCuts T Q := FillsCuts.of_surjective
    (Submodule.Quotient.mk_surjective (commonTail T))
    (fun _ _ h ↦ ConvexQuotient.mk_le_mk h)
    (fun _ _ h ↦ ConvexQuotient.lt_of_mk_lt_mk h) hfillG
  exact ⟨completeSpace_of_coinitial_of_exists_half ε hε hcoinitial hhalf hfillQ⟩

@[blueprint "lem:saturated-common-tail-cofinality"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Cofinality of common tails in saturated ordered groups")
  (statement := /--
    Let $\kappa>\aleph_0$, let $G$ be a $\kappa$-saturated ordered rational
    vector space, and let $T$ be a nonempty set of fewer than $\kappa$
    nonzero Archimedean classes with no least member in the magnitude order.
    Then the common tail $H_T$ has cofinality at least $\kappa$.
  -/)
  (proof := /--
    If a set $S\subseteq H_T$ of cardinality less than $\kappa$ were cofinal,
    use $S\cup\{0\}$ as the left side of a cut.  On the right put all rational
    fractions of positive representatives of classes in $T$.  Saturation
    fills the cut by a positive element of $H_T$ lying strictly above every
    member of $S$, a contradiction.
  -/)]
private theorem cofinal_commonTail_of_isKappaSaturated
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hG : IsKappaSaturated (G := G) κ)
    (T : Set (FiniteArchimedeanClass G)) (hT : IsLimitFamily T) (hTcard : #T < κ) :
    κ ≤ Order.cof ↑(commonTail T) := by
  rw [isKappaSaturated_iff] at hG
  rw [isLimitFamily_iff] at hT
  rw [Order.le_cof_iff]
  intro s hs
  by_contra hcard
  have hscard : #s < κ := lt_of_not_ge hcard
  let L : Set G := {0} ∪ ((↑) : commonTail T → G) '' s
  let R : Set G := Set.range fun p : T × ℕ ↦
    ((p.2 + 1 : ℚ)⁻¹) • FiniteArchimedeanClass.positiveRepresentative p.1.1
  have hLcard : #L < κ := by
    refine (Cardinal.mk_union_le _ _).trans_lt ?_
    apply Cardinal.add_lt_of_lt hκ.le
    · simpa using Cardinal.one_lt_aleph0.trans hκ
    · exact Cardinal.mk_image_le.trans_lt hscard
  have hprod : #(T × ℕ) < κ := by
    simpa using Cardinal.mul_lt_of_lt hκ.le hTcard hκ
  have hRcard : #R < κ := Cardinal.mk_range_le.trans_lt hprod
  have hLR : ∀ x ∈ L, ∀ y ∈ R, x < y := by
    intro x hx y hy
    obtain rfl | ⟨z, hz, rfl⟩ := hx
    · obtain ⟨⟨c, n⟩, rfl⟩ := hy
      exact smul_pos (inv_pos.mpr (by positivity))
        (FiniteArchimedeanClass.positiveRepresentative_pos c.1)
    · obtain ⟨⟨c, n⟩, rfl⟩ := hy
      by_cases hz0 : (z : G) = 0
      · rw [hz0]
        exact smul_pos (inv_pos.mpr (by positivity))
          (FiniteArchimedeanClass.positiveRepresentative_pos c.1)
      obtain ⟨d, hdT, hcd⟩ := hT.2 c.1 c.2
      have hzTail : (z : G) ∈ FiniteArchimedeanClass.tailKernel T :=
        (FiniteArchimedeanClass.mem_tailSubmodule_iff (K := ℚ)).mp z.2
      have hdz : d.1 ≤ ArchimedeanClass.mk (z : G) :=
        FiniteArchimedeanClass.mem_tailKernel_iff.mp hzTail ⟨d, hdT⟩
      have hcd' : c.1.1 < d.1 := hcd
      have hcz : c.1.1 < ArchimedeanClass.mk (z : G) := hcd'.trans_le hdz
      rcases le_total (z : G) 0 with hzneg | hznonneg
      · exact hzneg.trans_lt (smul_pos (inv_pos.mpr (by positivity))
          (FiniteArchimedeanClass.positiveRepresentative_pos c.1))
      · apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg
        · rw [ArchimedeanClass.mk_smul _ (inv_ne_zero (by positivity)),
            FiniteArchimedeanClass.mk_positiveRepresentative]
          exact hcz
        · exact smul_nonneg (inv_nonneg.mpr (by positivity))
            (FiniteArchimedeanClass.positiveRepresentative_pos c.1).le
  obtain ⟨y, hyL, hyR⟩ := hG L R hLcard hRcard hLR
  have hypos : 0 < y := hyL 0 (Set.mem_union_left _ (Set.mem_singleton 0))
  have hyright (c : T) (n : ℕ) :
      y < ((n + 1 : ℚ)⁻¹) • FiniteArchimedeanClass.positiveRepresentative c.1 :=
    hyR _ (Set.mem_range_self (c, n))
  have hyTail : y ∈ commonTail T := by
    rw [FiniteArchimedeanClass.mem_tailSubmodule_iff,
      FiniteArchimedeanClass.mem_tailKernel_iff]
    intro c
    obtain ⟨d, hdT, hcd⟩ := hT.2 c.1 c.2
    have hcd' : c.1.1 < d.1 := hcd
    apply hcd'.le.trans
    rw [← FiniteArchimedeanClass.mk_positiveRepresentative d,
      ArchimedeanClass.mk_le_mk]
    refine ⟨1, ?_⟩
    rw [abs_of_pos (FiniteArchimedeanClass.positiveRepresentative_pos d), abs_of_pos hypos]
    simpa using (hyright ⟨d, hdT⟩ 0).le
  have hnot : ¬ IsCofinal s := by
    rw [not_isCofinal_iff]
    exact ⟨⟨y, hyTail⟩, fun z hz ↦
      hyL (z : G) (Set.mem_union_right _ (Set.mem_image_of_mem _ hz))⟩
  exact hnot hs

@[blueprint "lem:saturated-inner-ball-cofinality"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Cofinality of Archimedean inner balls in saturated ordered groups")
  (statement := /--
    Let $\kappa>\aleph_0$ and let $G$ be a $\kappa$-saturated ordered rational
    vector space.  At every nonzero Archimedean class, the strict inner ball
    has cofinality at least $\kappa$.
  -/)
  (proof := /--
    If a set $S$ of cardinality less than $\kappa$ were cofinal in the strict
    inner ball below the class of $a\ne0$, place $S\cup\{0\}$ on the left of a
    cut and the elements $|a|/(n+1)$ on the right.  Saturation gives a positive
    element still in the strict inner ball and strictly above $S$, a
    contradiction.
  -/)]
private theorem le_cof_ball_of_isKappaSaturated
    {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hG : IsKappaSaturated (G := G) κ)
    (c : FiniteArchimedeanClass G) :
    κ ≤ Order.cof ↑(FiniteArchimedeanClass.ball ℚ c) := by
  rw [isKappaSaturated_iff] at hG
  induction c using FiniteArchimedeanClass.ind with
  | mk a ha =>
    rw [Order.le_cof_iff]
    intro s hs
    by_contra hcard
    have hscard : #s < κ := lt_of_not_ge hcard
    let L : Set G := {0} ∪
      (fun z : FiniteArchimedeanClass.ball ℚ (FiniteArchimedeanClass.mk a ha) ↦
        (z : G)) '' s
    let R : Set G := Set.range fun n : ℕ ↦ ((n + 1 : ℚ)⁻¹) • |a|
    have hLcard : #L < κ := by
      refine (Cardinal.mk_union_le _ _).trans_lt ?_
      apply Cardinal.add_lt_of_lt hκ.le
      · simpa using Cardinal.one_lt_aleph0.trans hκ
      · exact Cardinal.mk_image_le.trans_lt hscard
    have hRle : #R ≤ Cardinal.lift.{u} #ℕ := by
      simpa only [R, Cardinal.lift_uzero] using
        Cardinal.lift_mk_le_lift_mk_of_surjective
          (Set.rangeFactorization_surjective
            (f := fun n : ℕ ↦ ((n + 1 : ℚ)⁻¹) • |a|))
    have hRcard : #R < κ := hRle.trans_lt (by
      rw [Cardinal.mk_nat, Cardinal.lift_aleph0]
      exact hκ)
    have hLR : ∀ x ∈ L, ∀ y ∈ R, x < y := by
      intro x hx y hy
      obtain rfl | ⟨z, hz, rfl⟩ := hx
      · obtain ⟨n, rfl⟩ := hy
        exact smul_pos (inv_pos.mpr (by positivity)) (abs_pos.mpr ha)
      · obtain ⟨n, rfl⟩ := hy
        by_cases hz0 : (z : G) = 0
        · change (z : G) < ((n + 1 : ℚ)⁻¹) • |a|
          rw [hz0]
          exact smul_pos (inv_pos.mpr (by positivity)) (abs_pos.mpr ha)
        have hzclass : ArchimedeanClass.mk a < ArchimedeanClass.mk (z : G) := by
          have hzclass' := (FiniteArchimedeanClass.mem_ball_iff ℚ).mp z.property hz0
          exact hzclass'
        apply ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg
        · rw [ArchimedeanClass.mk_smul _ (inv_ne_zero (by positivity)),
            ArchimedeanClass.mk_abs]
          exact hzclass
        · exact smul_nonneg (inv_nonneg.mpr (by positivity)) (abs_nonneg a)
    obtain ⟨y, hyL, hyR⟩ := hG L R hLcard hRcard hLR
    have hypos : 0 < y := hyL 0 (Set.mem_union_left _ (Set.mem_singleton 0))
    have hyright (n : ℕ) : y < ((n + 1 : ℚ)⁻¹) • |a| :=
      hyR _ (Set.mem_range_self n)
    have hyball : y ∈ FiniteArchimedeanClass.ball ℚ
        (FiniteArchimedeanClass.mk a ha) := by
      rw [FiniteArchimedeanClass.mem_ball_iff]
      intro hy0
      rw [FiniteArchimedeanClass.mk_lt_mk ha hy0, ArchimedeanClass.mk_lt_mk]
      intro n
      rw [abs_of_pos hypos]
      obtain rfl | hn := n.eq_zero_or_pos
      · simpa using abs_pos.mpr ha
      · have hbound := hyright (n - 1)
        have hcast : (((n - 1 : ℕ) : ℚ) + 1) = n := by
          exact_mod_cast Nat.sub_add_cancel hn
        rw [hcast] at hbound
        have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
        have hnQ0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
        have hmul := smul_lt_smul_of_pos_left hbound hnQ
        simpa only [smul_smul, mul_inv_cancel₀ hnQ0, one_smul,
          Nat.cast_smul_eq_nsmul] using hmul
    have hnot : ¬ IsCofinal s := by
      rw [not_isCofinal_iff]
      exact ⟨⟨y, hyball⟩, fun z hz ↦
        hyL (z : G) (Set.mem_union_right _ (Set.mem_image_of_mem _ hz))⟩
    exact hnot hs

/-- The standalone form of `(A1)` is exactly LM24's condition at every nonzero class. -/
theorem assumptionA1_iff_lm24 (s : HahnEmbedding.ArchimedeanStrata ℚ G) :
    AssumptionA1 s ↔ ∀ c, LM24.AssumptionA1AtFiniteClass s c := by
  rw [assumptionA1_iff]
  exact forall_congr' fun c ↦ (LM24.assumptionA1AtFiniteClass_iff s c).symm

/-- Generating `R` by fractions is equivalent to the fraction subring being all of `R`. -/
theorem generatesFractionField_iff_fracSubring_eq_top (Z : Subring R) :
    GeneratesFractionField Z ↔ Subring.fracSubring Z = ⊤ := by
  rw [generatesFractionField_iff]
  constructor
  · intro h
    apply top_unique
    intro x _
    obtain ⟨a, b, _hb, rfl⟩ := h x
    rw [div_eq_mul_inv]
    exact (Subring.fracSubring Z).mul_mem (Subring.le_fracSubring a.2)
      (Subring.inv_mem_fracSubring (Subring.le_fracSubring b.2))
  · intro h x
    have hx : x ∈ Subring.fracSubring Z := by rw [h]; trivial
    obtain ⟨b, hb, hb0, hbx⟩ := Subring.exists_den hx
    have hbZ0 : (⟨b, hb⟩ : Z) ≠ 0 := fun hzero ↦ hb0 (congrArg Subtype.val hzero)
    refine ⟨⟨b * x, hbx⟩, ⟨b, hb⟩, hbZ0, ?_⟩
    change x = (b * x) / b
    exact (mul_div_cancel_left₀ x hb0).symm

omit [Module ℚ G] [IsOrderedModule ℚ G] in
/-- The standalone fraction-field condition is the corresponding fraction-subring equality. -/
theorem isFractionFieldOfHahnIntegerPart_iff_fracSubring_eq_top
    {κ : Cardinal} [Fact (ℵ₀ < κ)] (Z : Subring R) :
    IsFractionFieldOfHahnIntegerPart (G := G) Z κ ↔
      Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z) = ⊤ := by
  rw [isFractionFieldOfHahnIntegerPart_iff]
  let S := HahnSeries.cardSuppLTTruncationIntegerPart
    (G := G) (R := R) (κ := κ) Z
  constructor
  · intro h
    apply top_unique
    intro x _
    obtain ⟨a₀, b₀, ha₀, hb₀, hb₀ne, hx⟩ := h (x : HahnSeries G R) x.2
    have ha₀' := (mem_hahnIntegerPart_iff.mp ha₀)
    have hb₀' := (mem_hahnIntegerPart_iff.mp hb₀)
    let a : HahnSeries.CardSuppLTField (G := G) (R := R) (κ := κ) := ⟨a₀, ha₀'.1⟩
    let b : HahnSeries.CardSuppLTField (G := G) (R := R) (κ := κ) := ⟨b₀, hb₀'.1⟩
    have haS : a ∈ S := by
      rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
      exact ⟨ha₀'.2.1, ha₀'.2.2⟩
    have hbS : b ∈ S := by
      rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
      exact ⟨hb₀'.2.1, hb₀'.2.2⟩
    have hxb : x = a / b := by
      apply Subtype.ext
      exact hx
    rw [hxb, div_eq_mul_inv]
    exact (Subring.fracSubring S).mul_mem (Subring.le_fracSubring haS)
      (Subring.inv_mem_fracSubring (Subring.le_fracSubring hbS))
  · intro h x hx
    let X : HahnSeries.CardSuppLTField (G := G) (R := R) (κ := κ) := ⟨x, hx⟩
    have hXF : X ∈ Subring.fracSubring S := by
      rw [h]
      trivial
    obtain ⟨b, hbS, hb0, hbX⟩ := Subring.exists_den hXF
    have hb0' : (b : HahnSeries G R) ≠ 0 := by
      intro hzero
      apply hb0
      exact Subtype.ext hzero
    refine ⟨((b * X : HahnSeries.CardSuppLTField (G := G) (R := R) (κ := κ)) :
        HahnSeries G R), (b : HahnSeries G R), ?_, ?_, hb0', ?_⟩
    · rw [mem_hahnIntegerPart_iff]
      exact ⟨(b * X).2,
        (HahnSeries.mem_cardSuppLTTruncationIntegerPart.mp hbX).1,
        (HahnSeries.mem_cardSuppLTTruncationIntegerPart.mp hbX).2⟩
    · rw [mem_hahnIntegerPart_iff]
      exact ⟨b.2,
        (HahnSeries.mem_cardSuppLTTruncationIntegerPart.mp hbS).1,
        (HahnSeries.mem_cardSuppLTTruncationIntegerPart.mp hbS).2⟩
    · change x = ((b : HahnSeries G R) * x) / (b : HahnSeries G R)
      exact (mul_div_cancel_left₀ x hb0').symm

/-- Saturation supplies the two common-tail hypotheses of the bounded Hahn theorem. -/
@[blueprint "lem:saturated-common-tail-conditions"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Common-tail conditions in saturated ordered groups")
  (statement := /--
    Let $\kappa>\aleph_0$, let $G$ be a $\kappa$-saturated ordered rational
    vector space, and let $Z$ be a subring of a field $R$.  For every nonempty
    set $T$ of fewer than $\kappa$ nonzero Archimedean classes with no least
    member in the magnitude order, the quotient $G/H_T$ is Cauchy complete in
    its additive uniformity, and the bounded Hahn field $R((H_T))_\kappa$ is
    the fraction field of $Z+R((H_T^{<0}))_\kappa$.
  -/)
  (proof := /--
    Quotient completeness follows from
    \ref{lem:saturated-common-tail-quotient-complete}.  By
    \ref{lem:saturated-common-tail-cofinality},
    $\kappa\le\operatorname{cof}(H_T)$; hence
    \ref{thm:bounded-hahn-integer-part-fraction-field} gives the asserted
    fraction-field equality.
  -/)]
private theorem limitTailConditions_of_isKappaSaturated
    {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)] (Z : Subring R)
    (hG : IsKappaSaturated (G := G) κ) : LimitTailConditions (G := G) Z κ := by
  constructor
  · intro T hT hTcard
    exact completeSpace_tailQuotient_of_isKappaSaturated hG T hT hTcard
  · intro T hT hTcard
    apply (isFractionFieldOfHahnIntegerPart_iff_fracSubring_eq_top
      (G := commonTail T) Z).mpr
    exact HahnSeries.fracSubring_cardSuppLTTruncationIntegerPart_eq_top_of_le_cof Z
      (cofinal_commonTail_of_isKappaSaturated Fact.out hG T hT hTcard)

/-- The standalone disjunction `(A2)` is exactly LM24's condition at every nonzero class. -/
theorem assumptionA2_iff_lm24 (Z : Subring R) (κ : Cardinal) :
    AssumptionA2 (G := G) Z κ ↔
      ∀ c : FiniteArchimedeanClass G,
        LM24.AssumptionA2AtFiniteClass (K := ℚ) κ Z c := by
  rw [assumptionA2_iff]
  apply forall_congr'
  intro c
  rw [LM24.assumptionA2AtFiniteClass_iff]
  constructor
  · rintro (hcof | ⟨hzero, hfrac⟩)
    · exact Or.inl hcof
    · exact Or.inr ⟨hzero, (generatesFractionField_iff_fracSubring_eq_top Z).mp hfrac⟩
  · rintro (hcof | ⟨hzero, hfrac⟩)
    · exact Or.inl hcof
    · exact Or.inr ⟨hzero, (generatesFractionField_iff_fracSubring_eq_top Z).mpr hfrac⟩

/-- The standalone form of `(A3)` says exactly that `Z` is pre-Schreier. -/
theorem assumptionA3_iff_decompositionMonoid (Z : Subring R) :
    AssumptionA3 Z ↔ DecompositionMonoid Z := by
  rw [assumptionA3_iff]
  constructor
  · intro h
    rw [decompositionMonoid_iff]
    intro z a b hab
    exact h z a b hab
  · intro h
    rw [decompositionMonoid_iff] at h
    intro z a b hab
    exact h z hab

/-- Conditions `(A1)`--`(A3)` and the common-tail conditions make the bounded Hahn integer part
pre-Schreier. -/
@[blueprint "thm:hahn-integer-part-pre-schreier"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Pre-Schreier property of bounded Hahn integer parts")
  (statement := /--
    Let $G$ be an ordered rational vector space, $R$ a field of characteristic
    zero, $\kappa>\aleph_0$ a regular cardinal, and $Z\subseteq R$ a
    pre-Schreier subring.  Choose an additive complement to the strict inner
    ball at every nonzero Archimedean class.  Assume every complement is order
    additively isomorphic to $\mathbb R$, and that at each such class either
    the strict inner ball has cofinality at least $\kappa$, or it is zero and
    every element of $R$ is a fraction of elements of $Z$.

    For every nonempty set $T$ of fewer than $\kappa$ nonzero Archimedean
    classes having no least member in the magnitude order, let $H_T$ be the
    rational subspace of exponents lying beyond every class in $T$.  Assume
    that $G/H_T$ is Cauchy complete for its additive uniformity and that the
    bounded Hahn field on $H_T$ is the fraction field of its bounded Hahn
    integer part.  Then $Z+R((G^{<0}))_\kappa$ is pre-Schreier.
  -/)
  (proof := /--
    The real-complement and inner-ball hypotheses are LM24 conditions $(A1)$
    and $(A2)$, while the pre-Schreier hypothesis on $Z$ is condition $(A3)$.
    By \ref{thm:hahn-integer-part-primality}, every element of the bounded Hahn
    integer part is primal.  This is exactly the pre-Schreier property.
  -/)]
theorem decompositionMonoid_of_assumptions [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R) (s : HahnEmbedding.ArchimedeanStrata ℚ G)
    (hA1 : AssumptionA1 s) (hA2 : AssumptionA2 (G := G) Z κ)
    (hA3 : AssumptionA3 Z) (hlimit : LimitTailConditions (G := G) Z κ) :
    DecompositionMonoid (HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z) := by
  letI : DecompositionMonoid Z := (assumptionA3_iff_decompositionMonoid Z).mp hA3
  rw [decompositionMonoid_iff]
  intro x
  apply isPrimal_of_finite_class_assumptions_and_limit_tail_conditions Z s
    ((assumptionA1_iff_lm24 s).mp hA1) ((assumptionA2_iff_lm24 Z κ).mp hA2)
  · intro T hTne hTgt hTcard
    obtain ⟨hcomplete⟩ :=
      hlimit.cauchy_complete_quotient T (isLimitFamily_iff.mpr ⟨hTne, hTgt⟩) hTcard
    letI := hcomplete
    exact ⟨(commonTailUniformEquiv (G := G) T).completeSpace_iff.mp inferInstance⟩
  · intro T hTne hTgt hTcard
    have hfraction := hlimit.fraction_field_commonTail T
      (isLimitFamily_iff.mpr ⟨hTne, hTgt⟩) hTcard
    rw [commonTail_eq_tailSubmodule] at hfraction
    exact (isFractionFieldOfHahnIntegerPart_iff_fracSubring_eq_top
      (G := _root_.FiniteArchimedeanClass.tailSubmodule ℚ T) Z).mp hfraction

/-- Saturation makes the bounded Hahn integer part pre-Schreier. -/
@[blueprint "cor:hahn-integer-part-pre-schreier-of-saturation"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Pre-Schreier Hahn integer parts over saturated exponent groups")
  (statement := /--
    Let $\kappa>\aleph_0$ be regular, let $G$ be a $\kappa$-saturated ordered
    rational vector space, let $R$ be a field of characteristic zero, and let
    $Z\subseteq R$ be pre-Schreier.  Then
    $Z+R((G^{<0}))_\kappa$ is pre-Schreier.
  -/)
  (proof := /--
    Saturation gives real Archimedean strata by
    \ref{lem:saturated-archimedean-strata-real}, the cofinal alternative in
    condition $(A2)$ by \ref{lem:saturated-inner-ball-cofinality}, and the
    completeness and fraction-field conditions at common tails by
    \ref{lem:saturated-common-tail-conditions}.  These are the hypotheses of
    \ref{thm:hahn-integer-part-pre-schreier}.
  -/)]
theorem decompositionMonoid_of_saturation [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R) (hA3 : AssumptionA3 Z) (hG : IsKappaSaturated (G := G) κ) :
    DecompositionMonoid (HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z) := by
  let s : HahnEmbedding.ArchimedeanStrata ℚ G := Classical.choice inferInstance
  have hA1 : AssumptionA1 s := by
    rw [assumptionA1_iff]
    exact stratum_orderAddEquiv_real_of_isKappaSaturated Fact.out hG s
  have hA2 : AssumptionA2 (G := G) Z κ := by
    rw [assumptionA2_iff]
    intro c
    exact Or.inl (le_cof_ball_of_isKappaSaturated Fact.out hG c)
  have hlimit := limitTailConditions_of_isKappaSaturated Z hG
  exact decompositionMonoid_of_assumptions Z s hA1 hA2 hA3 hlimit

/-- Conditions `(A1)`--`(A3)` and the common-tail conditions imply four-factor refinement. -/
@[blueprint "thm:hahn-integer-part-refinement"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Refinement of bounded generalised-power-series integer parts")
  (statement := /--
    Under the hypotheses of \ref{thm:hahn-integer-part-pre-schreier}, every
    equality $ab=cd$ in $Z+R((G^{<0}))_\kappa$ admits elements
    $e,f,g,h$ in the same ring such that
    \[
      a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh.
    \]
  -/)
  (proof := /--
    By \ref{thm:hahn-integer-part-pre-schreier}, the bounded
    generalised-power-series integer part is pre-Schreier.  The standard
    equivalence between primality of every element and four-factor refinement
    gives the displayed factors, which are then viewed as elements of the
    ambient generalised-power-series field.
  -/)
  (highlight)]
theorem of_assumptions : HahnIntegerPartRefinementCriterion (G := G) (R := R) := by
  intro hR
  letI : CharZero R := hR
  intro κ hκcountable hκregular Z s hA1 hA2 hA3 hlimit
  letI : Fact (ℵ₀ < κ) := ⟨hκcountable⟩
  letI : Fact κ.IsRegular := ⟨hκregular⟩
  let S := HahnSeries.cardSuppLTTruncationIntegerPart
    (G := G) (R := R) (κ := κ) Z
  letI : DecompositionMonoid S :=
    decompositionMonoid_of_assumptions Z s hA1 hA2 hA3 hlimit
  let inclusion : HahnSeries.CardSuppLTField (G := G) (R := R) (κ := κ) →+*
      HahnSeries G R := (HahnSeries.cardSuppLTSubfield G R κ).subtype
  let E := Subring.equivMapOfInjective S inclusion Subtype.val_injective
  letI : DecompositionMonoid (S.map inclusion) :=
    MulEquiv.decompositionMonoid E.symm.toMulEquiv
  have hmem (x : HahnSeries G R) : x ∈ S.map inclusion ↔ x ∈ hahnIntegerPart Z κ := by
    rw [Subring.mem_map, mem_hahnIntegerPart_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp hy
      exact ⟨y.2, hy'.1, hy'.2⟩
    · rintro ⟨hxcard, hxsupp, hxzero⟩
      refine ⟨⟨x, hxcard⟩, ?_, rfl⟩
      exact (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mpr ⟨hxsupp, hxzero⟩
  intro a b c d ha hb hc hd habcd
  simpa only [hmem] using
    Subring.exists_fourFactorRefinement_of_decompositionMonoid (S.map inclusion)
      (hmem a |>.mpr ha) (hmem b |>.mpr hb) (hmem c |>.mpr hc) (hmem d |>.mpr hd) habcd

/-- Saturation supplies `(A1)`, `(A2)`, quotient completeness, and the common-tail
fraction-field condition. -/
@[blueprint "cor:hahn-integer-part-refinement-of-saturation"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Refinement over saturated exponent groups")
  (statement := /--
    Let $\kappa>\aleph_0$ be regular, let $G$ be a $\kappa$-saturated ordered
    rational vector space, let $R$ be a field of characteristic zero, and let
    $Z\subseteq R$ be pre-Schreier.  Then every equality
    $ab=cd$ in $Z+R((G^{<0}))_\kappa$ has a refinement
    \[
      a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh
    \]
    in the same ring.
  -/)
  (proof := /--
    By \ref{lem:saturated-archimedean-strata-real}, saturation supplies
    condition $(A1)$.  By \ref{lem:saturated-inner-ball-cofinality}, it also
    supplies the cofinal alternative in condition $(A2)$ at every nonzero
    Archimedean class.  For each limit family,
    \ref{lem:saturated-common-tail-conditions} supplies quotient completeness
    and says that every bounded common-tail series is a fraction of two
    elements of the bounded common-tail Hahn integer part.  These are all the
    hypotheses of
    \ref{thm:hahn-integer-part-refinement}.
  -/)]
theorem of_saturation [CharZero R]
    {κ : Cardinal.{u}} (hκcount : ℵ₀ < κ) (hκregular : κ.IsRegular)
    (Z : Subring R) (hA3 : AssumptionA3 Z) (hG : IsKappaSaturated (G := G) κ) :
    ∀ a b c d : HahnSeries G R,
      a ∈ hahnIntegerPart Z κ → b ∈ hahnIntegerPart Z κ →
      c ∈ hahnIntegerPart Z κ → d ∈ hahnIntegerPart Z κ → a * b = c * d →
        ∃ e f g h : HahnSeries G R,
          e ∈ hahnIntegerPart Z κ ∧ f ∈ hahnIntegerPart Z κ ∧
          g ∈ hahnIntegerPart Z κ ∧ h ∈ hahnIntegerPart Z κ ∧
            a = e * f ∧ b = g * h ∧ c = e * g ∧ d = f * h := by
  letI : Fact (ℵ₀ < κ) := ⟨hκcount⟩
  letI : Fact κ.IsRegular := ⟨hκregular⟩
  let s : HahnEmbedding.ArchimedeanStrata ℚ G := Classical.choice inferInstance
  have hA1 : AssumptionA1 s := by
    rw [assumptionA1_iff]
    exact stratum_orderAddEquiv_real_of_isKappaSaturated hκcount hG s
  have hA2 : AssumptionA2 (G := G) Z κ := by
    rw [assumptionA2_iff]
    intro c
    exact Or.inl (le_cof_ball_of_isKappaSaturated hκcount hG c)
  have hlimit := limitTailConditions_of_isKappaSaturated Z hG
  exact of_assumptions (inferInstance : CharZero R) κ hκcount hκregular
    Z s hA1 hA2 hA3 hlimit

private def integerCoefficientSubring : Subring R :=
  (Int.castRingHom R).range

private noncomputable def integerCoefficientSubringEquiv [CharZero R] :
    ℤ ≃+* integerCoefficientSubring (R := R) :=
  RingEquiv.ofBijective (Int.castRingHom R).rangeRestrict
    ⟨Int.cast_injective, RingHom.rangeRestrict_surjective _⟩

private theorem integerCoefficientSubring_preSchreier [CharZero R] :
    AssumptionA3 (integerCoefficientSubring (R := R)) := by
  apply assumptionA3_iff.mpr
  intro z
  let e := integerCoefficientSubringEquiv (R := R)
  change IsPrimal z
  rw [← e.apply_symm_apply z]
  exact (RingEquiv.isPrimal_iff e (e.symm z)).mpr
    (DecompositionMonoid.primal (e.symm z))

omit [IsOrderedAddMonoid G] [Module ℚ G] [IsOrderedModule ℚ G] in
private theorem mem_hahnIntegerPart_integerCoefficientSubring_iff
    {κ : Cardinal.{u}} {x : HahnSeries G R} :
    x ∈ hahnIntegerPart (integerCoefficientSubring (R := R)) κ ↔
      x ∈ integerHahnPart κ := by
  rw [mem_hahnIntegerPart_iff, mem_integerHahnPart_iff]
  constructor
  · rintro ⟨hcard, hsupp, ⟨z, hz⟩⟩
    exact ⟨hcard, hsupp, z, hz⟩
  · rintro ⟨hcard, hsupp, z, hz⟩
    exact ⟨hcard, hsupp, ⟨z, hz⟩⟩

/-- Uncountable regular saturation implies refinement with integer constant coefficients. -/
@[blueprint "cor:integer-hahn-refinement-of-saturation"
  (phase := "Bounded generalised-power-series integer parts")
  (title := "Refinement of saturated Hahn integer parts with integer constants")
  (statement := /--
    Let $\kappa>\aleph_0$ be regular, let $G$ be a $\kappa$-saturated ordered
    rational vector space, and let $R$ be a field of characteristic zero.
    Then every equality $ab=cd$ in
    $\mathbb Z+R((G^{<0}))_\kappa$ has a refinement
    \[
      a=ef,\qquad b=gh,\qquad c=eg,\qquad d=fh
    \]
    in the same ring.
  -/)
  (proof := /--
    The image of $\mathbb Z$ in $R$ is pre-Schreier.  Apply
    \ref{cor:hahn-integer-part-refinement-of-saturation} with
    this coefficient ring and rewrite membership as the requirement that the
    constant coefficient be an integer.
  -/)]
theorem of_saturation_integer_coefficients [CharZero R] :
    HahnIntegerPartRefinement (G := G) (R := R) := by
  intro κ hκcount hκregular hG a b c d ha hb hc hd habcd
  have hrefine := of_saturation (G := G) (R := R) hκcount hκregular
    (integerCoefficientSubring (R := R))
    (integerCoefficientSubring_preSchreier (R := R)) hG
  simpa only [mem_hahnIntegerPart_integerCoefficientSubring_iff] using
    hrefine a b c d
      (mem_hahnIntegerPart_integerCoefficientSubring_iff.mpr ha)
      (mem_hahnIntegerPart_integerCoefficientSubring_iff.mpr hb)
      (mem_hahnIntegerPart_integerCoefficientSubring_iff.mpr hc)
      (mem_hahnIntegerPart_integerCoefficientSubring_iff.mpr hd) habcd

end ConwayRefinement.Standalone.Hahn.HahnIntegerPartRefinement
