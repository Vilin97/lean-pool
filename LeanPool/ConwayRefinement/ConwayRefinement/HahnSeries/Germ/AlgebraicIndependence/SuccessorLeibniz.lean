/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Derivative
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Leibniz
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart
import Mathlib.Tactic.Abel

/-!
# Product rule for translated truncations of homogeneous representatives

The finite convolution remainder has strictly smaller Cantor–Bendixson rank than the homogeneous
component immediately below a successor product. When both grades are successors, both
translated truncation terms survive in that component. If the second grade has zero finite
Cantor coefficient (including grade zero), its term vanishes there.

These are eventual equalities in the associated graded ring, retaining arbitrary complete
ordered exponent groups. They use the Cantor–Bendixson convolution bound, not the real-exponent
ordinal-value product theorem.
-/

public noncomputable section
open Set Filter Topology
open scoped NatOrdinal
universe u v
namespace HahnSeries.Nonpositive
variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := R))

private theorem value_le_wpow_of_degree_le (b : Nonpositive G R) (α : NatOrdinal.{u})
    (hb : ν b ≤ α) : cantorBendixsonValuation b ≤ ω^ α := by
  by_cases hm : 0 ∈ (b : HahnSeries G R).closedSupport
  · rw [cantorBendixsonDegreeValuation_of_mem _ hm, WithBot.coe_le_coe] at hb
    rw [cantorBendixsonValuation_apply,
      cantorBendixsonValue_of_mem _ ((mem_closedSupport _ _).mp hm),
      NatOrdinal.of_omega0_opow]
    exact NatOrdinal.wpow_le_wpow.mpr hb
  · rw [cantorBendixsonValuation_apply,
      cantorBendixsonValue_of_notMem _ (by simpa only [mem_closedSupport] using hm),
      NatOrdinal.of_zero]
    exact zero_le

/-- The translated product remainder lies strictly below the lowered product degree near zero. -/
theorem eventually_degree_leibnizRemainder_lt (b c : Nonpositive G R)
    (α β : NatOrdinal.{u}) (hb : ν b ≤ (α + 1 : NatOrdinal)) (hc : ν c ≤ β) :
    ∀ᶠ γ in 𝓝[<] (0 : G),
      ν (translatedTruncLE γ (b * c) - translatedTruncLE γ b * c -
        b * translatedTruncLE γ c) < (α + β : NatOrdinal) := by
  have h := eventually_cantorBendixsonValue_leibnizRemainder_lt_of_le_wpow
    (b : HahnSeries G R) c b.property c.property α β
    (by simpa only [cantorBendixsonValuation_apply] using value_le_wpow_of_degree_le b _ hb)
    (by simpa only [cantorBendixsonValuation_apply] using value_le_wpow_of_degree_le c _ hc)
  filter_upwards [h] with γ hγ
  rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
    NatOrdinal.cantorDegree_lt_coe_iff]
  change NatOrdinal.of (((translatedTruncLE γ (b * c) : HahnSeries G R) -
    (translatedTruncLE γ b : HahnSeries G R) * c -
    (b : HahnSeries G R) * translatedTruncLE γ c)).cantorBendixsonValue < _
  simpa only [coe_translatedTruncLE, Subring.coe_mul] using hγ

private theorem homogeneousMk_eq_add_of_sub_sub_lt (δ : NatOrdinal.{u})
    (a b c : (ν).filtrationLE δ)
    (h : ν ((a : Nonpositive G R) - b - c) < δ) :
    (ν).homogeneousMk δ a = (ν).homogeneousMk δ b + (ν).homogeneousMk δ c := by
  rw [← map_add, (ν).homogeneousMk_apply, (ν).homogeneousMk_apply]
  apply congrArg (DirectSum.of (ν).Component δ)
  apply ((ν).componentMk_eq_componentMk_iff _ _ _).mpr
  simpa only [AddSubgroup.coe_add, sub_add_eq_sub_sub] using h

private theorem homogeneousMk_congr {α β : NatOrdinal.{u}} (h : α = β)
    (a : (ν).filtrationLE α) (b : (ν).filtrationLE β)
    (hab : (a : Nonpositive G R) = b) :
    (ν).homogeneousMk α a = (ν).homogeneousMk β b := by
  subst β
  exact congrArg ((ν).homogeneousMk α) (Subtype.ext hab)

/-- Both successor factors contribute to the homogeneous product rule near zero. -/
theorem eventually_homogeneousDerivAt_mul_succ (α β : NatOrdinal.{u})
    (b : (ν).filtrationLE (α + 1)) (c : (ν).filtrationLE (β + 1)) :
    ∀ᶠ γ in 𝓝[<] (0 : G),
      DirectSum.of (ν).Component (α + β + 1)
          (cantorBendixsonDerivAt (α + β + 1) ((b : Nonpositive G R) * c) γ) =
        DirectSum.of (ν).Component α (cantorBendixsonDerivAt α b γ) *
          (ν).homogeneousMk (β + 1) c +
        (ν).homogeneousMk (α + 1) b *
          DirectSum.of (ν).Component β (cantorBendixsonDerivAt β c γ) := by
  have hb := ((ν).mem_filtrationLE_iff _ _).mp b.property
  have hc := ((ν).mem_filtrationLE_iff _ _).mp c.property
  have hbc : ν ((b : Nonpositive G R) * c) ≤ (α + β + 1 + 1 : NatOrdinal) := by
    have h := MaxAddDegree.degree_mul_le_add hb hc
    simpa only [← WithBot.coe_add, add_assoc, add_left_comm, add_comm] using h
  filter_upwards [eventually_degree_translatedTruncLE_le (b : Nonpositive G R) α hb,
    eventually_degree_translatedTruncLE_le (c : Nonpositive G R) β hc,
    eventually_degree_translatedTruncLE_le ((b : Nonpositive G R) * (c : Nonpositive G R))
      (α + β + 1) hbc,
    eventually_degree_leibnizRemainder_lt (b : Nonpositive G R) (c : Nonpositive G R)
      α (β + 1) hb hc]
    with γ hbg hcg hbcg hrem
  rw [cantorBendixsonDerivAt_eq _ _ _ hbg, cantorBendixsonDerivAt_eq _ _ _ hcg,
    cantorBendixsonDerivAt_eq _ _ _ hbcg, ← (ν).homogeneousMk_apply,
    ← (ν).homogeneousMk_apply, ← (ν).homogeneousMk_apply,
    (ν).homogeneousMk_mul, (ν).homogeneousMk_mul]
  let x : (ν).filtrationLE (α + β + 1) :=
    ⟨translatedTruncLE γ (b : Nonpositive G R) * (c : Nonpositive G R),
      ((ν).mem_filtrationLE_iff _ _).mpr (by
      simpa only [← WithBot.coe_add, add_assoc] using MaxAddDegree.degree_mul_le_add hbg hc)⟩
  let y : (ν).filtrationLE (α + β + 1) :=
    ⟨(b : Nonpositive G R) * translatedTruncLE γ (c : Nonpositive G R),
      ((ν).mem_filtrationLE_iff _ _).mpr (by
        simpa only [← WithBot.coe_add, add_assoc, add_left_comm, add_comm] using
          MaxAddDegree.degree_mul_le_add hb hcg)⟩
  have hx : (ν).homogeneousMk (α + (β + 1))
      ((ν).mulFiltrationLE ⟨translatedTruncLE γ (b : Nonpositive G R),
        ((ν).mem_filtrationLE_iff _ _).mpr hbg⟩ c) =
      (ν).homogeneousMk (α + β + 1) x :=
    homogeneousMk_congr (by ac_rfl) _ _ (by rw [(ν).coe_mulFiltrationLE])
  have hy : (ν).homogeneousMk (α + 1 + β)
      ((ν).mulFiltrationLE b ⟨translatedTruncLE γ (c : Nonpositive G R),
        ((ν).mem_filtrationLE_iff _ _).mpr hcg⟩) =
      (ν).homogeneousMk (α + β + 1) y :=
    homogeneousMk_congr (by ac_rfl) _ _ (by rw [(ν).coe_mulFiltrationLE])
  rw [hx, hy]
  apply homogeneousMk_eq_add_of_sub_sub_lt
  simpa only [add_assoc] using hrem

private theorem add_succ_lt_add_of_constantCoeff_eq_zero
    (α : NatOrdinal.{u}) {β β' : NatOrdinal.{u}}
    (hβ : β.constantCoeff = 0) (hlt : β' < β) : α + 1 + β' < α + β := by
  have h := ((NatOrdinal.isSuccPrelimit_iff_constantCoeff_eq_zero β).mpr hβ).add_one_lt hlt
  simpa only [add_assoc, add_left_comm, add_comm] using add_lt_add_left h α

/-- A factor with zero finite Cantor coefficient contributes no term in the lowered degree. -/
theorem eventually_degree_mul_translatedTruncLE_lt_limit (α β : NatOrdinal.{u})
    (hβ : β.constantCoeff = 0) (b c : Nonpositive G R)
    (hb : ν b ≤ (α + 1 : NatOrdinal)) (hc : ν c ≤ β) :
    ∀ᶠ γ in 𝓝[<] (0 : G),
      ν (b * translatedTruncLE γ c) < (α + β : NatOrdinal) := by
  filter_upwards [eventually_degree_translatedTruncLE_lt c β hc] with γ hγ
  have hm := (ν).map_mul_le_add b (translatedTruncLE γ c)
  cases he : ν (translatedTruncLE γ c) using WithBot.recBotCoe with
  | bot =>
    rw [he, WithBot.add_bot] at hm
    exact hm.trans_lt (WithBot.bot_lt_coe _)
  | coe β' =>
    have hlt : β' < β := by simpa only [he, WithBot.coe_lt_coe] using hγ
    apply hm.trans_lt
    have hle := add_le_add hb (le_rfl : (↑β' : WithBot NatOrdinal) ≤ ↑β')
    rw [he]
    apply hle.trans_lt
    rw [← WithBot.coe_add, WithBot.coe_lt_coe]
    exact add_succ_lt_add_of_constantCoeff_eq_zero α hβ hlt

/-- If the second grade is zero or a limit, only the first truncation term survives. -/
theorem eventually_homogeneousDerivAt_mul_limit (α β : NatOrdinal.{u})
    (hβ : β.constantCoeff = 0)
    (b : (ν).filtrationLE (α + 1)) (c : (ν).filtrationLE β) :
    ∀ᶠ γ in 𝓝[<] (0 : G),
      DirectSum.of (ν).Component (α + β)
          (cantorBendixsonDerivAt (α + β) ((b : Nonpositive G R) * (c : Nonpositive G R)) γ) =
        DirectSum.of (ν).Component α (cantorBendixsonDerivAt α b γ) *
          (ν).homogeneousMk β c := by
  have hb := ((ν).mem_filtrationLE_iff _ _).mp b.property
  have hc := ((ν).mem_filtrationLE_iff _ _).mp c.property
  have hbc : ν ((b : Nonpositive G R) * (c : Nonpositive G R)) ≤ (α + β + 1 : NatOrdinal) := by
    have h := MaxAddDegree.degree_mul_le_add hb hc
    simpa only [← WithBot.coe_add, add_assoc, add_left_comm, add_comm] using h
  filter_upwards [eventually_degree_translatedTruncLE_le (b : Nonpositive G R) α hb,
    eventually_degree_translatedTruncLE_le ((b : Nonpositive G R) * (c : Nonpositive G R))
      (α + β) hbc,
    eventually_degree_leibnizRemainder_lt (b : Nonpositive G R) (c : Nonpositive G R)
      α β hb hc,
    eventually_degree_mul_translatedTruncLE_lt_limit α β hβ
      (b : Nonpositive G R) (c : Nonpositive G R) hb hc]
    with γ hbg hbcg hrem hlimit
  rw [cantorBendixsonDerivAt_eq _ _ _ hbg, cantorBendixsonDerivAt_eq _ _ _ hbcg,
    ← (ν).homogeneousMk_apply, ← (ν).homogeneousMk_apply, (ν).homogeneousMk_mul,
    (ν).homogeneousMk_apply, (ν).homogeneousMk_apply]
  apply congrArg (DirectSum.of (ν).Component (α + β))
  apply ((ν).componentMk_eq_componentMk_iff _ _ _).mpr
  rw [(ν).coe_mulFiltrationLE]
  change ν (translatedTruncLE γ ((b : Nonpositive G R) * (c : Nonpositive G R)) -
    translatedTruncLE γ (b : Nonpositive G R) * (c : Nonpositive G R)) < (α + β : NatOrdinal)
  have hs : translatedTruncLE γ ((b : Nonpositive G R) * (c : Nonpositive G R)) -
      translatedTruncLE γ (b : Nonpositive G R) * (c : Nonpositive G R) =
      (translatedTruncLE γ ((b : Nonpositive G R) * (c : Nonpositive G R)) -
        translatedTruncLE γ (b : Nonpositive G R) * (c : Nonpositive G R) -
        (b : Nonpositive G R) * translatedTruncLE γ (c : Nonpositive G R)) +
      (b : Nonpositive G R) * translatedTruncLE γ (c : Nonpositive G R) := by abel
  rw [hs]
  exact ((ν).map_add_le_max _ _).trans_lt (max_lt hrem hlimit)

end HahnSeries.Nonpositive
