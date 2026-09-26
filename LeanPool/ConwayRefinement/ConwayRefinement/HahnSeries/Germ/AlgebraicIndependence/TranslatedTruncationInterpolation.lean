/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.OrderedIntervalCantorBendixson
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Derivative
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood

/-!
# Interpolation of translated truncations

The series `translateTruncGT w c center` translates the strict upper truncation of `w` to a chosen
center. Its support lies in one half-open interval. If every proper translated truncation of `w`
inside that interval has degree below `α`, then the `α`-th derivative of the translated support is
contained in the singleton consisting of its center.
-/

open Set Filter Topology TopologicalSpace
open scoped NatOrdinal

universe u v w

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [CommRing R]

/-- Place the exponents above `c` of `w` at `center`. -/
def translateTruncGT (w : Nonpositive G R) (c center : G) : R⟦G⟧ :=
  translate center (truncGT c (w : HahnSeries G R))

/-- A translated strict upper truncation is supported in its designated half-open interval. -/
theorem support_translateTruncGT_subset (w : Nonpositive G R) (c center : G) :
    (translateTruncGT w c center).support ⊆ Ioc (center + c) center := by
  rw [translateTruncGT, support_translate, support_truncGT]
  rintro x ⟨y, ⟨hy, hcy⟩, rfl⟩
  exact ⟨by simpa [add_comm] using add_lt_add_left hcy center,
    by simpa using add_le_add_left (w.property hy) center⟩

variable [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [NoZeroDivisors R] [CharZero R]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := R))

/-- If every proper translated truncation above `c` has degree below `α`, then the `α`-th
derivative of the translated strict upper truncation is supported at its center. -/
theorem cantorBendixson_translateTruncGT_subset_singleton
    (w : Nonpositive G R) (c center : G) (α : NatOrdinal.{u})
    (hcut : ∀ η, c < η → η < 0 → ν (translatedTruncLE η w) < α) :
    ((translateTruncGT w c center).closedSupport.cantorBendixson α.val : Set G) ⊆ {center} := by
  intro y hy
  have hys : y ∈ (translateTruncGT w c center).closedSupport :=
    (translateTruncGT w c center).closedSupport.cantorBendixson_le α.val hy
  have hybounds : y ∈ Icc (center + c) center :=
    closure_minimal
      ((support_translateTruncGT_subset w c center).trans Ioc_subset_Icc_self) isClosed_Icc
      ((mem_closedSupport _ _).mp hys)
  by_cases hyc : y = center
  · exact hyc ▸ Set.mem_singleton center
  have hleft : center + c ∉ (translateTruncGT w c center).closedSupport := by
    intro hm
    have hm' : c ∈ (truncGT c (w : HahnSeries G R)).closedSupport := by
      apply ((truncGT c (w : HahnSeries G R)).mem_closedSupport_translate center c).mp
      exact hm
    exact (w : HahnSeries G R).notMem_closedSupport_truncGT c hm'
  have hlefty : center + c < y := lt_of_le_of_ne hybounds.1 fun he ↦
    hleft (he ▸ hys)
  let η := -center + y
  have hcη : c < η := by
    dsimp only [η]
    have h := add_lt_add_left hlefty (-center)
    simpa [add_assoc, add_comm, add_left_comm] using h
  have hη0 : η < 0 := by
    dsimp only [η]
    have h := add_lt_add_left (lt_of_le_of_ne hybounds.2 hyc) (-center)
    simpa [add_assoc, add_comm, add_left_comm] using h
  have hyη : center + η = y := by simp only [η, add_neg_cancel_left]
  have hrank : (translateTruncGT w c center).cantorBendixsonRank y =
      (w : HahnSeries G R).cantorBendixsonRank η := by
    rw [translateTruncGT, ← hyη, (truncGT c (w : HahnSeries G R)).cantorBendixsonRank_translate,
      (w : HahnSeries G R).cantorBendixsonRank_truncGT_of_lt hcη]
  have hyrank : α.val ≤ (translateTruncGT w c center).cantorBendixsonRank y :=
    ((translateTruncGT w c center).mem_support_derivative_iff y α.val).mp hy |>.2
  have hηmem : η ∈ (w : HahnSeries G R).closedSupport := by
    have hm : η ∈ (truncGT c (w : HahnSeries G R)).closedSupport := by
      apply ((truncGT c (w : HahnSeries G R)).mem_closedSupport_translate center η).mp
      rw [hyη]
      exact hys
    apply (mem_closedSupport _ _).mpr
    exact closure_mono (support_truncGT_subset c (w : HahnSeries G R))
      ((mem_closedSupport _ _).mp hm)
  have hzero : 0 ∈ (translatedTruncLE η w : Nonpositive G R).1.closedSupport := by
    have hm := ((truncLE η (w : HahnSeries G R)).mem_closedSupport_translate (-η) η).mpr
      ((w : HahnSeries G R).mem_closedSupport_truncLE η |>.mpr hηmem)
    apply (mem_closedSupport _ _).mpr
    rw [coe_translatedTruncLE]
    exact (mem_closedSupport _ _).mp (by simpa only [neg_add_cancel] using hm)
  have hdegree := hcut η hcη hη0
  rw [cantorBendixsonDegreeValuation_of_mem (translatedTruncLE η w) hzero,
    WithBot.coe_lt_coe] at hdegree
  have hsr : ((translatedTruncLE η w : Nonpositive G R).1).cantorBendixsonRank 0 =
      (w : HahnSeries G R).cantorBendixsonRank η := by
    simpa only [coe_translatedTruncLE] using
      (w : HahnSeries G R).cantorBendixsonRank_translated_truncLE η
  rw [hsr] at hdegree
  exact ((not_le_of_gt (NatOrdinal.of.lt_iff_lt.mp hdegree)) (hrank ▸ hyrank)).elim

/-- Every homogeneous class has a representative and a negative cutoff above any fixed negative
lower bound such that all proper translated truncations above the cutoff have lower degree. -/
theorem exists_representative_with_lower_truncation_degree (α : NatOrdinal.{u})
    (a : (cantorBendixsonDegreeValuation (G := G) (R := R)).Component α)
    {d : G} (hd : d < 0) :
    ∃ w : Nonpositive G R, ∃ c : G,
      ∃ hw : cantorBendixsonDegreeValuation w ≤ α,
      d ≤ c ∧ c < 0 ∧
      (cantorBendixsonDegreeValuation (G := G) (R := R)).componentMk α
        ⟨w, ((cantorBendixsonDegreeValuation (G := G) (R := R)).mem_filtrationLE_iff α w).mpr
          hw⟩ = a ∧
      ∀ η, c < η → η < 0 →
        cantorBendixsonDegreeValuation (translatedTruncLE η w) < α := by
  induction a using MaxAddDegree.componentInductionOn with
  | H b =>
    have hb : cantorBendixsonDegreeValuation (b : Nonpositive G R) ≤ α :=
      ((cantorBendixsonDegreeValuation (G := G) (R := R)).mem_filtrationLE_iff α
        (b : Nonpositive G R)).mp b.property
    obtain ⟨l, hl, hcut⟩ := eventually_nhdsLT_iff_exists.mp
      (eventually_degree_translatedTruncLE_lt (b : Nonpositive G R) α hb)
    let c := max l d
    have hdc : d ≤ c := le_max_right _ _
    have hc0 : c < 0 := max_lt hl hd
    refine ⟨(b : Nonpositive G R), c, hb, hdc, hc0, ?_, ?_⟩
    · rfl
    · intro η hcη hη0
      exact hcut η ((le_max_left l d).trans_lt hcη) hη0

variable {ι : Type w} [LinearOrder ι]

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [NoZeroDivisors R] [CharZero R] in
/-- At one center, the translated weak truncation of the entire ordered interval sum differs from
the source of that translated strict upper truncation only at or below its cutoff. -/
theorem support_translatedTruncLE_orderedIntervalHsum_sub_source_subset
    (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦G⟧) (cut center : ι → G)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j)
    (i : ι) (w : Nonpositive G R) (c : G)
    (hcut : cut i = center i + c) (hfi : f i = translateTruncGT w c (center i)) :
    (translate (-center i) (truncLE (center i)
      (orderedIntervalHsum hι f cut center hsupp hord)) - (w : HahnSeries G R)).support ⊆
      Iic c := by
  have hown : translate (-center i) (f i) = truncGT c (w : HahnSeries G R) := by
    rw [hfi, translateTruncGT, translate_neg_apply]
  have hfirst : (translate (-center i) (truncLE (center i)
      (orderedIntervalHsum hι f cut center hsupp hord)) -
        translate (-center i) (f i)).support ⊆ Iic c := by
    have h := HahnSeries.support_translatedTruncLE_orderedIntervalHsum_sub_component_subset
      hι f cut center hsupp hord i
    rw [hcut] at h
    simpa only [add_sub_cancel_left] using h
  have hsecond : (translate (-center i) (f i) - (w : HahnSeries G R)).support ⊆ Iic c := by
    rw [hown]
    have he : truncGT c (w : HahnSeries G R) - (w : HahnSeries G R) =
        -truncLE c (w : HahnSeries G R) := by
      calc
        truncGT c (w : HahnSeries G R) - (w : HahnSeries G R) =
            truncGT c (w : HahnSeries G R) -
              (truncLE c (w : HahnSeries G R) + truncGT c (w : HahnSeries G R)) :=
          (congrArg (fun z : HahnSeries G R ↦ truncGT c (w : HahnSeries G R) - z)
            (truncLE_add_truncGT c (w : HahnSeries G R))).symm
        _ = -truncLE c (w : HahnSeries G R) := by abel
    rw [he, support_neg, support_truncLE]
    exact inter_subset_right
  have he : translate (-center i) (truncLE (center i)
      (orderedIntervalHsum hι f cut center hsupp hord)) - (w : HahnSeries G R) =
      (translate (-center i) (truncLE (center i)
        (orderedIntervalHsum hι f cut center hsupp hord)) - translate (-center i) (f i)) +
        (translate (-center i) (f i) - (w : HahnSeries G R)) := by
    abel
  rw [he]
  exact (support_add_subset _ _).trans (union_subset hfirst hsecond)

/-- At its center, one translated strict upper truncation represents the translated truncation of
the entire ordered sum in the same homogeneous component. All other intervals and the discarded
lower part contribute only a series bounded strictly below zero. -/
theorem componentMk_centered_orderedIntervalHsum_eq
    (α : NatOrdinal.{u}) (hι : (Set.univ : Set ι).IsPWO)
    (f : ι → R⟦G⟧) (cut center : ι → G)
    (hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i))
    (hord : ∀ i j, i < j → center i ≤ cut j)
    (i : ι) (w : Nonpositive G R) (c : G)
    (hc : c < 0) (hcut : cut i = center i + c)
    (hfi : f i = translateTruncGT w c (center i))
    (hw : ν w ≤ α) :
    let q : Nonpositive G R :=
      ⟨translate (-center i) (truncLE (center i)
        (orderedIntervalHsum hι f cut center hsupp hord)), support_translated_truncLE _ _⟩
    ∃ hq : ν q ≤ α,
      (ν).componentMk α ⟨q, ((ν).mem_filtrationLE_iff α q).mpr hq⟩ =
        (ν).componentMk α ⟨w, ((ν).mem_filtrationLE_iff α w).mpr hw⟩ := by
  dsimp only
  let q : Nonpositive G R :=
    ⟨translate (-center i) (truncLE (center i)
      (orderedIntervalHsum hι f cut center hsupp hord)), support_translated_truncLE _ _⟩
  have herr : ((q : HahnSeries G R) - (w : HahnSeries G R)).support ⊆ Iic c :=
    support_translatedTruncLE_orderedIntervalHsum_sub_source_subset
      hι f cut center hsupp hord i w c hcut hfi
  let e : Nonpositive G R :=
    ⟨(q : HahnSeries G R) - w, herr.trans (Iic_subset_Iic.mpr hc.le)⟩
  have hedeg : ν e = ⊥ := (cantorBendixsonDegreeValuation_eq_bot_iff e).mpr ⟨c, hc, herr⟩
  have hqe : q = e + w := by
    apply Subtype.ext
    change (q : HahnSeries G R) = ((q : HahnSeries G R) - w) + w
    abel
  have hq : ν q ≤ α := by
    rw [hqe]
    exact ((ν).map_add_le_max e w).trans (max_le (by rw [hedeg]; exact bot_le) hw)
  refine ⟨hq, ((ν).componentMk_eq_componentMk_iff α _ _).mpr ?_⟩
  change ν e < α
  rw [hedeg]
  exact WithBot.bot_lt_coe α

open Classical in
/-- Prescribed homogeneous classes on one exact rank level can be assembled at arbitrary
cofinality into a successor-filtered Hahn series. Its translated truncation at every rank-level
center has the prescribed lower homogeneous class. -/
theorem exists_prescribed_components_on_rankLevel (α β : NatOrdinal.{u})
    (p : Nonpositive G R) (hp : ν p ≤ (α + 1 : NatOrdinal))
    (a : {x // x ∈ (p : HahnSeries G R).closedSupport ∧
      (p : HahnSeries G R).closedSupport.cantorBendixsonRank
        (p : HahnSeries G R).closedSupport_isPWO x = α.val} → (ν).Component β) :
    ∃ b : Nonpositive G R, ∃ hb : ν b ≤ (β + 1 : NatOrdinal),
      (∀ i : {x // x ∈ (p : HahnSeries G R).closedSupport ∧
          (p : HahnSeries G R).closedSupport.cantorBendixsonRank
            (p : HahnSeries G R).closedSupport_isPWO x = α.val},
          ∃ hi : ν (translatedTruncLE (i : G) b) ≤ β,
            (ν).componentMk β
              ⟨translatedTruncLE (i : G) b,
                ((ν).mem_filtrationLE_iff β _).mpr hi⟩ = a i) ∧
        cantorBendixsonLayerDeriv β
            ((ν).componentMk (β + 1)
              ⟨b, ((ν).mem_filtrationLE_iff (β + 1) b).mpr hb⟩) =
          ((fun γ ↦ if h : γ ∈ (p : HahnSeries G R).closedSupport ∧
              (p : HahnSeries G R).closedSupport.cantorBendixsonRank
                (p : HahnSeries G R).closedSupport_isPWO γ = α.val then
              a ⟨γ, h⟩ else 0) :
            Filter.Germ (𝓝[<] (0 : G)) ((ν).Component β)) := by
  classical
  let I := {x // x ∈ (p : HahnSeries G R).closedSupport ∧
    (p : HahnSeries G R).closedSupport.cantorBendixsonRank
      (p : HahnSeries G R).closedSupport_isPWO x = α.val}
  have hI : (Set.univ : Set I).IsPWO :=
    (p : HahnSeries G R).closedSupport.rankLevel_univ_isPWO
      (p : HahnSeries G R).closedSupport_isPWO α.val
  obtain ⟨z, hzlt, _, hzord⟩ :=
    (p : HahnSeries G R).closedSupport.exists_rankLevel_leftCuts
      (p : HahnSeries G R).closedSupport_isPWO α.val
  have hd (i : I) : z i - (i : G) < 0 := sub_neg.mpr (hzlt i)
  choose w c hw hdc hc hcomp hproper using fun i : I ↦
    exists_representative_with_lower_truncation_degree β (a i) (hd i)
  let center : I → G := fun i ↦ i
  let cut : I → G := fun i ↦ (i : G) + c i
  let f : I → R⟦G⟧ := fun i ↦ translateTruncGT (w i) (c i) (i : G)
  have hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i) := by
    intro i
    exact support_translateTruncGT_subset (w i) (c i) i
  have hord : ∀ i j : I, i < j → center i ≤ cut j := by
    intro i j hij
    have hzj : z j ≤ (j : G) + c j := by
      calc
        z j = (j : G) + (z j - (j : G)) := by abel
        _ ≤ (j : G) + c j := by
          simpa only [add_comm] using add_le_add_left (hdc j) (j : G)
    exact (hzord i j hij).trans hzj
  let B : R⟦G⟧ := orderedIntervalHsum hI f cut center hsupp hord
  have hBsupport : B.support ⊆ Iic 0 := by
    change (orderedIntervalHsum hI f cut center hsupp hord).support ⊆ Iic 0
    rw [support_orderedIntervalHsum]
    intro g hg
    rw [Set.mem_iUnion] at hg
    obtain ⟨i, hgi⟩ := hg
    exact (hsupp i hgi).2.trans (closure_minimal p.property isClosed_Iic
      ((mem_closedSupport _ _).mp i.property.1))
  let b : Nonpositive G R := ⟨B, hBsupport⟩
  have hstage : ∀ i, ((f i).closedSupport.cantorBendixson β.val : Set G) ⊆
      {center i} := by
    intro i
    exact cantorBendixson_translateTruncGT_subset_singleton (w i) (c i) i β (hproper i)
  have hcenter : closure (Set.range center) ⊆
      ((p : HahnSeries G R).closedSupport.cantorBendixson α.val : Set G) := by
    have hrange : Set.range center =
        {x | x ∈ (p : HahnSeries G R).closedSupport ∧
          (p : HahnSeries G R).closedSupport.cantorBendixsonRank
            (p : HahnSeries G R).closedSupport_isPWO x = α.val} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact i.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange,
      (p : HahnSeries G R).closedSupport.closure_rank_level_eq
        (p : HahnSeries G R).closedSupport_isPWO α.val]
  have hpRank : (p : HahnSeries G R).cantorBendixsonRank 0 ≤ α.val + 1 := by
    by_cases hm : 0 ∈ (p : HahnSeries G R).closedSupport
    · rw [cantorBendixsonDegreeValuation_of_mem p hm, WithBot.coe_le_coe] at hp
      have h := NatOrdinal.of.symm.monotone hp
      change NatOrdinal.val (NatOrdinal.of ((p : HahnSeries G R).cantorBendixsonRank 0)) ≤
        NatOrdinal.val (α + 1) at h
      simpa only [NatOrdinal.val_of, NatOrdinal.val_add_one] using h
    · rw [cantorBendixsonRank_eq,
        (p : HahnSeries G R).closedSupport.cantorBendixsonRank_of_notMem
          (p : HahnSeries G R).closedSupport_isPWO hm]
      exact zero_le
  have hpnext : 0 ∉
      ((p : HahnSeries G R).closedSupport.cantorBendixson
        ((α.val + 1) + 1) : Set G) := by
    intro hm
    have hr := ((p : HahnSeries G R).mem_support_derivative_iff 0 _).mp hm |>.2
    exact (not_le_of_gt (hpRank.trans_lt (lt_add_one _))) hr
  have hBrank : B.cantorBendixsonRank 0 ≤ β.val + 1 := by
    exact cantorBendixsonRank_orderedIntervalHsum_le_add_one_of_centerStage
      hI f cut center hsupp hord β.val α.val
      (p : HahnSeries G R).closedSupport hstage hcenter 0 hpnext
  have hb : ν b ≤ (β + 1 : NatOrdinal) := by
    by_cases hm : 0 ∈ (b : HahnSeries G R).closedSupport
    · rw [cantorBendixsonDegreeValuation_of_mem b hm, WithBot.coe_le_coe]
      have h := NatOrdinal.of.monotone hBrank
      have hbB : (b : HahnSeries G R) = B := rfl
      rw [hbB]
      exact h.trans_eq (by rw [← NatOrdinal.val_add_one, NatOrdinal.of_val])
    · rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
        cantorBendixsonValue_of_notMem _ (by simpa only [mem_closedSupport] using hm),
        NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]
      exact bot_le
  have hpoint : ∀ i : I, ∃ hi : ν (translatedTruncLE (i : G) b) ≤ β,
      (ν).componentMk β
        ⟨translatedTruncLE (i : G) b, ((ν).mem_filtrationLE_iff β _).mpr hi⟩ = a i := by
    intro i
    have hlocal := componentMk_centered_orderedIntervalHsum_eq β hI f cut center hsupp hord
      i (w i) (c i) (hc i) rfl rfl (hw i)
    dsimp only [b, B] at hlocal
    obtain ⟨hi, heq⟩ := hlocal
    let q : Nonpositive G R :=
      ⟨translate (-(i : G)) (truncLE (i : G)
        (orderedIntervalHsum hI f cut center hsupp hord)), support_translated_truncLE _ _⟩
    have hqt : q = translatedTruncLE (i : G) b := by
      apply Subtype.ext
      rw [coe_translatedTruncLE]
    rw [← hqt]
    exact ⟨hi, heq.trans (hcomp i)⟩
  have hBderiv : (B.closedSupport.cantorBendixson β.val : Set G) ⊆
      closure (Set.range center) := by
    exact cantorBendixson_orderedIntervalHsum_subset_closure_range
      hI f cut center hsupp hord β.val hstage
  have hgerm : cantorBendixsonLayerDeriv β
      ((ν).componentMk (β + 1)
        ⟨b, ((ν).mem_filtrationLE_iff (β + 1) b).mpr hb⟩) =
      ((fun γ ↦ if h : γ ∈ (p : HahnSeries G R).closedSupport ∧
          (p : HahnSeries G R).closedSupport.cantorBendixsonRank
            (p : HahnSeries G R).closedSupport_isPWO γ = α.val then
          a ⟨γ, h⟩ else 0) :
        Filter.Germ (𝓝[<] (0 : G)) ((ν).Component β)) := by
    rw [cantorBendixsonLayerDeriv_componentMk, Filter.Germ.coe_eq]
    filter_upwards [eventually_degree_translatedTruncLE_le p α hp,
      eventually_degree_translatedTruncLE_le b β hb] with γ hpγ hbγ
    by_cases hs : γ ∈ (p : HahnSeries G R).closedSupport ∧
        (p : HahnSeries G R).closedSupport.cantorBendixsonRank
          (p : HahnSeries G R).closedSupport_isPWO γ = α.val
    · rw [dite_eq_left hs, cantorBendixsonDerivAt_eq β b γ hbγ]
      exact (hpoint ⟨γ, hs⟩).choose_spec
    · rw [dite_eq_right hs]
      by_contra hne
      have hbexact := (cantorBendixsonDerivAt_ne_zero_iff β b γ hbγ).mp hne
      have hbB : (b : HahnSeries G R) = B := rfl
      have hbclosed : γ ∈ B.closedSupport := by
        rw [← hbB]
        exact hbexact.1
      have hbmem : γ ∈ (B.closedSupport.cantorBendixson β.val : Set G) := by
        apply (B.mem_support_derivative_iff γ β.val).mpr
        refine ⟨(mem_closedSupport _ _).mp hbclosed, ?_⟩
        simpa only [cantorBendixsonRank_eq, hbB] using hbexact.2.ge
      have hpmem := ((p : HahnSeries G R).mem_support_derivative_iff γ α.val).mp
        (hcenter (hBderiv hbmem))
      apply hs
      refine ⟨(mem_closedSupport _ _).mpr hpmem.1, ?_⟩
      rw [← cantorBendixsonRank_eq]
      exact cantorBendixsonRank_eq_of_mem_derivative_of_degree_translatedTruncLE_le
        α p γ ((mem_closedSupport _ _).mpr hpmem.1) hpmem.2 hpγ
  exact ⟨b, hb, hpoint, hgerm⟩

open Classical in
/-- Prescribed nonpositive series at every exact top-rank point assemble with literal pointwise
degree bounds. When every translated truncation of `p`, including the one at cutoff zero, has
degree at most `β`, the exact rank-`β` points of its closed support accumulate nowhere, so the
assembly loses no stage at any cutoff. The assembled series matches each prescription at its
center up to a series bounded strictly below zero, and its translated truncation at every other
nonpositive cutoff, including zero, has degree strictly below `ρ`. -/
theorem exists_prescribed_truncations_on_topRankLevel (β ρ : NatOrdinal.{u})
    (p : Nonpositive G R)
    (hp : ∀ x : G, x ≤ 0 → ν (translatedTruncLE x p) ≤ β)
    (w : {x // x ∈ (p : HahnSeries G R).closedSupport ∧
      (p : HahnSeries G R).closedSupport.cantorBendixsonRank
        (p : HahnSeries G R).closedSupport_isPWO x = β.val} → Nonpositive G R)
    (hw : ∀ i, ν (w i) ≤ ρ) :
    ∃ c : Nonpositive G R,
      (∀ i : {x // x ∈ (p : HahnSeries G R).closedSupport ∧
          (p : HahnSeries G R).closedSupport.cantorBendixsonRank
            (p : HahnSeries G R).closedSupport_isPWO x = β.val},
        ν (translatedTruncLE (i : G) c - w i) = ⊥) ∧
      ∀ y : G, y ≤ 0 →
        ¬(y ∈ (p : HahnSeries G R).closedSupport ∧
          (p : HahnSeries G R).closedSupport.cantorBendixsonRank
            (p : HahnSeries G R).closedSupport_isPWO y = β.val) →
        ν (translatedTruncLE y c) < ρ := by
  classical
  let I := {x // x ∈ (p : HahnSeries G R).closedSupport ∧
    (p : HahnSeries G R).closedSupport.cantorBendixsonRank
      (p : HahnSeries G R).closedSupport_isPWO x = β.val}
  have hI : (Set.univ : Set I).IsPWO :=
    (p : HahnSeries G R).closedSupport.rankLevel_univ_isPWO
      (p : HahnSeries G R).closedSupport_isPWO β.val
  obtain ⟨z, hzlt, -, hzord⟩ :=
    (p : HahnSeries G R).closedSupport.exists_rankLevel_leftCuts
      (p : HahnSeries G R).closedSupport_isPWO β.val
  have hcuts : ∀ i : I, ∃ ci : G, z i - (i : G) ≤ ci ∧ ci < 0 ∧
      ∀ η, ci < η → η < 0 → ν (translatedTruncLE η (w i)) < ρ := by
    intro i
    obtain ⟨l, hl, hcut⟩ := eventually_nhdsLT_iff_exists.mp
      (eventually_degree_translatedTruncLE_lt (w i) ρ (hw i))
    refine ⟨max l (z i - (i : G)), le_max_right _ _,
      max_lt hl (sub_neg.mpr (hzlt i)), fun η hlη hη0 ↦ ?_⟩
    exact hcut η ((le_max_left _ _).trans_lt hlη) hη0
  choose cc hdc hcneg hccut using hcuts
  let center : I → G := fun i ↦ i
  let cut : I → G := fun i ↦ (i : G) + cc i
  let f : I → R⟦G⟧ := fun i ↦ translateTruncGT (w i) (cc i) (i : G)
  have hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i) := fun i ↦
    support_translateTruncGT_subset (w i) (cc i) i
  have hord : ∀ i j : I, i < j → center i ≤ cut j := by
    intro i j hij
    have hzj : z j ≤ (j : G) + cc j := by
      calc
        z j = (j : G) + (z j - (j : G)) := by abel
        _ ≤ (j : G) + cc j := by
          simpa only [add_comm] using add_le_add_left (hdc j) (j : G)
    exact (hzord i j hij).trans hzj
  let B : R⟦G⟧ := orderedIntervalHsum hI f cut center hsupp hord
  have hBsupport : B.support ⊆ Iic 0 := by
    change (orderedIntervalHsum hI f cut center hsupp hord).support ⊆ Iic 0
    rw [support_orderedIntervalHsum]
    intro g hg
    rw [Set.mem_iUnion] at hg
    obtain ⟨i, hgi⟩ := hg
    exact (hsupp i hgi).2.trans (closure_minimal p.property isClosed_Iic
      ((mem_closedSupport _ _).mp i.property.1))
  let c : Nonpositive G R := ⟨B, hBsupport⟩
  refine ⟨c, ?_, ?_⟩
  · intro i
    have herr := support_translatedTruncLE_orderedIntervalHsum_sub_source_subset
      hI f cut center hsupp hord i (w i) (cc i) rfl rfl
    apply (cantorBendixsonDegreeValuation_eq_bot_iff _).mpr
    refine ⟨cc i, hcneg i, ?_⟩
    have hcoe : ((translatedTruncLE (i : G) c - w i : Nonpositive G R) : HahnSeries G R) =
        translate (-(i : G)) (truncLE (i : G) B) - (w i : HahnSeries G R) := by
      rw [AddSubgroupClass.coe_sub, coe_translatedTruncLE]
    rw [hcoe]
    exact herr
  · intro y hy0 hyn
    have hstage : ∀ i, ((f i).closedSupport.cantorBendixson ρ.val : Set G) ⊆ {center i} :=
      fun i ↦ cantorBendixson_translateTruncGT_subset_singleton (w i) (cc i) i ρ (hccut i)
    have hderiv : ((orderedIntervalHsum hI f cut center hsupp hord).closedSupport.cantorBendixson
        ρ.val : Set G) ⊆ closure (Set.range center) :=
      cantorBendixson_orderedIntervalHsum_subset_closure_range hI f cut center hsupp hord
        ρ.val hstage
    have hrange : Set.range center = {x : G | x ∈ (p : HahnSeries G R).closedSupport ∧
        (p : HahnSeries G R).closedSupport.cantorBendixsonRank
          (p : HahnSeries G R).closedSupport_isPWO x = β.val} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact i.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    have hlevel : ∀ x : G,
        x ∈ ((p : HahnSeries G R).closedSupport.cantorBendixson β.val : Set G) →
        x ∈ (p : HahnSeries G R).closedSupport ∧
          (p : HahnSeries G R).closedSupport.cantorBendixsonRank
            (p : HahnSeries G R).closedSupport_isPWO x = β.val := by
      intro x hx
      obtain ⟨hxs, hxr⟩ := ((p : HahnSeries G R).closedSupport.mem_cantorBendixson_iff
        (p : HahnSeries G R).closedSupport_isPWO x β.val).mp hx
      have hx0 : x ≤ 0 := closure_minimal p.property isClosed_Iic
        ((mem_closedSupport _ _).mp hxs)
      have hd := hp x hx0
      rw [degree_translatedTruncLE_eq, ite_eq_left hxs, WithBot.coe_le_coe] at hd
      have hval := NatOrdinal.of.symm.monotone hd
      change NatOrdinal.val (NatOrdinal.of ((p : HahnSeries G R).cantorBendixsonRank x)) ≤
        NatOrdinal.val β at hval
      rw [NatOrdinal.val_of, cantorBendixsonRank_eq] at hval
      exact ⟨hxs, le_antisymm hval hxr⟩
    have hclosure : closure (Set.range center) ⊆
        {x : G | x ∈ (p : HahnSeries G R).closedSupport ∧
          (p : HahnSeries G R).closedSupport.cantorBendixsonRank
            (p : HahnSeries G R).closedSupport_isPWO x = β.val} := by
      rw [hrange, (p : HahnSeries G R).closedSupport.closure_rank_level_eq
        (p : HahnSeries G R).closedSupport_isPWO β.val]
      exact hlevel
    have hcB : (c : HahnSeries G R) = orderedIntervalHsum hI f cut center hsupp hord := rfl
    have hyd : y ∉ ((c : HahnSeries G R).closedSupport.cantorBendixson ρ.val : Set G) := by
      rw [hcB]
      exact fun hyd ↦ hyn (hclosure (hderiv hyd))
    rw [degree_translatedTruncLE_eq]
    by_cases hym : y ∈ (c : HahnSeries G R).closedSupport
    · rw [ite_eq_left hym]
      have hrlt : (c : HahnSeries G R).cantorBendixsonRank y < ρ.val := by
        by_contra hge
        exact hyd (((c : HahnSeries G R).mem_support_derivative_iff y ρ.val).mpr
          ⟨(mem_closedSupport _ _).mp hym, not_lt.mp hge⟩)
      rw [WithBot.coe_lt_coe, ← NatOrdinal.of_val ρ]
      exact NatOrdinal.of.lt_iff_lt.mpr hrlt
    · rw [ite_eq_right hym]
      exact WithBot.bot_lt_coe ρ

end HahnSeries.Nonpositive
