/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import
  LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.TranslatedTruncationInterpolation

/-!
# Interpolation of translated truncations on a set

The construction places a prescribed homogeneous class at each point of an exact-rank set.
Nothing requires those points to come from a single series: the proof only uses that they are
partially well ordered, sit at or below zero, admit ordered disjoint left cuts, and are carried by
some derivative stage of a closed set at which the origin has already dropped out.

This file gives the interpolation theorem over such a set. The level of one series is one case;
finite unions of levels give the version needed for a family of prescriptions.

The one condition that is not merely structural is that the set be recovered from its closure near
zero: a point of the closure that is not in the set must not occur arbitrarily close to zero. For a
rank level that holds because the truncations eventually drop, and it is what stops the assembled
derivative from being nonzero away from the prescribed points.
-/

universe u v w

open scoped NatOrdinal Topology

open Filter Set TopologicalSpace HahnSeries

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {R : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := R))

open Classical in
/-- Prescribed homogeneous classes on a partially well ordered, nonpositive, left-separated set
carried by a derivative stage assemble into one class a degree higher whose derivative germ is the
prescribed function, provided the set is recovered from its closure near zero. -/
theorem exists_prescribed_components_on_set (β : NatOrdinal.{u}) (S : Set G)
    (hSneg : S ⊆ Iic 0)
    (hSpwo : (Set.univ : Set ↥S).IsPWO)
    (z : ↥S → G) (hzlt : ∀ i : ↥S, z i < (i : G))
    (hzord : ∀ i j : ↥S, (i : G) < (j : G) → (i : G) ≤ z j)
    (t : Closeds G) (r : Ordinal.{u})
    (hcarry : closure S ⊆ (t.cantorBendixson r : Set G))
    (hdrop : (0 : G) ∉ (t.cantorBendixson ((r + 1) + 1) : Set G))
    (hnear : ∀ᶠ γ in 𝓝[<] (0 : G), γ ∈ closure S → γ ∈ S)
    (a : ↥S → (ν).Component β) :
    ∃ b : Nonpositive G R, ∃ hb : ν b ≤ (β + 1 : NatOrdinal),
      (∀ i : ↥S, ∃ hi : ν (translatedTruncLE (i : G) b) ≤ β,
        (ν).componentMk β
          ⟨translatedTruncLE (i : G) b, ((ν).mem_filtrationLE_iff β _).mpr hi⟩ = a i) ∧
      cantorBendixsonLayerDeriv β
          ((ν).componentMk (β + 1) ⟨b, ((ν).mem_filtrationLE_iff (β + 1) b).mpr hb⟩) =
        ((fun γ ↦ if h : γ ∈ S then a ⟨γ, h⟩ else 0) :
          Filter.Germ (𝓝[<] (0 : G)) ((ν).Component β)) := by
  classical
  have hd (i : ↥S) : z i - (i : G) < 0 := sub_neg.mpr (hzlt i)
  choose w c hw hdc hc hcomp hproper using fun i : ↥S ↦
    exists_representative_with_lower_truncation_degree β (a i) (hd i)
  set center : ↥S → G := fun i ↦ i with hcenterdef
  set cut : ↥S → G := fun i ↦ (i : G) + c i with hcutdef
  set f : ↥S → R⟦G⟧ := fun i ↦ translateTruncGT (w i) (c i) (i : G) with hfdef
  have hsupp : ∀ i, (f i).support ⊆ Ioc (cut i) (center i) := fun i ↦
    support_translateTruncGT_subset (w i) (c i) i
  have hord : ∀ i j : ↥S, i < j → center i ≤ cut j := by
    intro i j hij
    have hzj : z j ≤ (j : G) + c j := by
      calc
        z j = (j : G) + (z j - (j : G)) := by abel
        _ ≤ (j : G) + c j := by simpa only [add_comm] using add_le_add_left (hdc j) (j : G)
    exact (hzord i j hij).trans hzj
  set B : R⟦G⟧ := orderedIntervalHsum hSpwo f cut center hsupp hord with hBdef
  have hBsupport : B.support ⊆ Iic 0 := by
    rw [hBdef, support_orderedIntervalHsum]
    intro g hg
    rw [Set.mem_iUnion] at hg
    obtain ⟨i, hgi⟩ := hg
    exact (hsupp i hgi).2.trans (hSneg i.property)
  set b : Nonpositive G R := ⟨B, hBsupport⟩ with hbdef
  have hstage : ∀ i, ((f i).closedSupport.cantorBendixson β.val : Set G) ⊆ {center i} := fun i ↦
    cantorBendixson_translateTruncGT_subset_singleton (w i) (c i) i β (hproper i)
  have hrange : Set.range center = S := by
    ext x
    exact ⟨by rintro ⟨i, rfl⟩; exact i.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hcenter : closure (Set.range center) ⊆ (t.cantorBendixson r : Set G) := by
    rw [hrange]; exact hcarry
  have hBrank : B.cantorBendixsonRank 0 ≤ β.val + 1 :=
    cantorBendixsonRank_orderedIntervalHsum_le_add_one_of_centerStage
      hSpwo f cut center hsupp hord β.val r t hstage hcenter 0 hdrop
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
  have hpoint : ∀ i : ↥S, ∃ hi : ν (translatedTruncLE (i : G) b) ≤ β,
      (ν).componentMk β
        ⟨translatedTruncLE (i : G) b, ((ν).mem_filtrationLE_iff β _).mpr hi⟩ = a i := by
    intro i
    have hlocal := componentMk_centered_orderedIntervalHsum_eq β hSpwo f cut center hsupp hord
      i (w i) (c i) (hc i) rfl rfl (hw i)
    dsimp only [hbdef, hBdef] at hlocal
    obtain ⟨hi, heq⟩ := hlocal
    set q : Nonpositive G R :=
      ⟨translate (-(i : G)) (truncLE (i : G)
        (orderedIntervalHsum hSpwo f cut center hsupp hord)), support_translated_truncLE _ _⟩
      with hqdef
    have hqt : q = translatedTruncLE (i : G) b := by
      apply Subtype.ext
      rw [coe_translatedTruncLE]
    rw [← hqt]
    exact ⟨hi, heq.trans (hcomp i)⟩
  have hBderiv : (B.closedSupport.cantorBendixson β.val : Set G) ⊆ closure (Set.range center) :=
    cantorBendixson_orderedIntervalHsum_subset_closure_range
      hSpwo f cut center hsupp hord β.val hstage
  refine ⟨b, hb, hpoint, ?_⟩
  rw [cantorBendixsonLayerDeriv_componentMk, Filter.Germ.coe_eq]
  filter_upwards [eventually_degree_translatedTruncLE_le b β hb, hnear] with γ hbγ hnearγ
  by_cases hs : γ ∈ S
  · rw [dite_eq_left hs, cantorBendixsonDerivAt_eq β b γ hbγ]
    exact (hpoint ⟨γ, hs⟩).choose_spec
  · rw [dite_eq_right hs]
    by_contra hne
    have hbexact := (cantorBendixsonDerivAt_ne_zero_iff β b γ hbγ).mp hne
    have hbB : (b : HahnSeries G R) = B := rfl
    have hbclosed : γ ∈ B.closedSupport := by rw [← hbB]; exact hbexact.1
    have hbmem : γ ∈ (B.closedSupport.cantorBendixson β.val : Set G) := by
      apply (B.mem_support_derivative_iff γ β.val).mpr
      refine ⟨(mem_closedSupport _ _).mp hbclosed, ?_⟩
      simpa only [cantorBendixsonRank_eq, hbB] using hbexact.2.ge
    exact hs (hnearγ (by rw [← hrange]; exact hBderiv hbmem))

open Classical in
/-- **Interpolation over a discrete set of centers.** A discrete set whose closure adds nothing
near zero carries its own derivative bookkeeping. Its accumulation points avoid a neighbourhood of
zero, so zero is not an accumulation point of them, and the second derivative stage of its closure
misses zero. Prescribed classes at its points therefore assemble with no further hypotheses. -/
theorem exists_prescribed_components_on_set_of_isDiscrete (β : NatOrdinal.{u}) (S : Set G)
    (hSneg : S ⊆ Iic 0) (hSpwo : (Set.univ : Set ↥S).IsPWO) (hSdisc : IsDiscrete S)
    (hnear : ∀ᶠ γ in 𝓝[<] (0 : G), γ ∈ closure S → γ ∈ S)
    (a : ↥S → (ν).Component β) :
    ∃ b : Nonpositive G R, ∃ hb : ν b ≤ (β + 1 : NatOrdinal),
      (∀ i : ↥S, ∃ hi : ν (translatedTruncLE (i : G) b) ≤ β,
        (ν).componentMk β
          ⟨translatedTruncLE (i : G) b, ((ν).mem_filtrationLE_iff β _).mpr hi⟩ = a i) ∧
      cantorBendixsonLayerDeriv β
          ((ν).componentMk (β + 1) ⟨b, ((ν).mem_filtrationLE_iff (β + 1) b).mpr hb⟩) =
        ((fun γ ↦ if h : γ ∈ S then a ⟨γ, h⟩ else 0) :
          Filter.Germ (𝓝[<] (0 : G)) ((ν).Component β)) := by
  classical
  obtain ⟨z, hzlt, -, hzord⟩ := TopologicalSpace.Closeds.exists_leftCuts_of_isDiscrete S hSdisc
  obtain ⟨η, hη, hcut⟩ := eventually_nhdsLT_iff_exists.mp hnear
  set t : Closeds G := ⟨closure S, isClosed_closure⟩ with htdef
  have hcarry : closure S ⊆ (t.cantorBendixson (0 : Ordinal.{u}) : Set G) := by
    rw [TopologicalSpace.Closeds.cantorBendixson_zero]
    exact subset_rfl
  -- the accumulation points of the centers avoid a whole left neighbourhood of zero
  have hacc : ∀ γ : G, η < γ → γ < 0 → γ ∉ derivedSet S := by
    intro γ hηγ hγ0 hγ
    have hγS : γ ∈ S := hcut γ hηγ hγ0 (derivedSet_subset_closure S hγ)
    rw [isDiscrete_iff_nhdsNE] at hSdisc
    exact (mem_derivedSet.mp hγ).ne (hSdisc γ hγS)
  have hderived : ((t.derived : Closeds G) : Set G) = derivedSet S := by
    rw [TopologicalSpace.Closeds.coe_derived]
    exact derivedSet_closure S
  have hdrop : (0 : G) ∉ (t.cantorBendixson ((0 : Ordinal.{u}) + 1 + 1) : Set G) := by
    rw [TopologicalSpace.Closeds.cantorBendixson_add_one,
      TopologicalSpace.Closeds.cantorBendixson_add_one,
      TopologicalSpace.Closeds.cantorBendixson_zero,
      TopologicalSpace.Closeds.coe_derived, mem_derivedSet, accPt_iff_nhds]
    intro hacc0
    obtain ⟨y, hy, hyne⟩ := hacc0 (Ioi η) ((isOpen_Ioi).mem_nhds hη)
    have hyd : y ∈ derivedSet S := by rw [← hderived]; exact hy.2
    have hyle : y ≤ 0 :=
      closure_minimal hSneg isClosed_Iic (derivedSet_subset_closure S hyd)
    exact hacc y hy.1 (lt_of_le_of_ne hyle hyne) hyd
  exact exists_prescribed_components_on_set β S hSneg hSpwo z hzlt hzord t 0 hcarry hdrop hnear a

end HahnSeries.Nonpositive

end
