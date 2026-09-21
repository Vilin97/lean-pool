/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Graded
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.LeastTermSup
public import Mathlib.Order.Filter.Germ.Basic
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood

/-!
# Translated truncation from degree `α + 1` to degree `α`

Translated weak truncation induces an additive map from the homogeneous component of degree
`α + 1` to germs, at negative cutoffs approaching zero, of the component of degree `α`.
The strict drop in Cantor–Bendixson rank makes the map independent of representatives. Local rank
reconstruction proves injectivity: eventual disappearance in the lower component forces the
original representative into the strict filtration.

The exponent group retains its ordered uniform structure, assumed Cauchy complete, in any
universe; no Archimedean or countability hypothesis is imposed. The map is additive here. Scalar
linearity and a product rule are separate assertions, not consequences of injectivity alone.
-/

public noncomputable section
open Set Filter Topology
open scoped NatOrdinal
universe u v
namespace HahnSeries.Nonpositive
variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [CommRing R]

/-- Weak truncation at a cutoff, translated to exponent zero, as an additive endomorphism. -/
def translatedTruncLE (γ : G) : Nonpositive G R →+ Nonpositive G R where
  toFun b := ⟨translate (-γ) (truncLE γ (b : HahnSeries G R)), support_translated_truncLE _ _⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' b c := by
    apply Subtype.ext
    change translate (-γ) (truncLE γ ((b : HahnSeries G R) + (c : HahnSeries G R))) = _
    rw [truncLE_add, map_add]
    rfl

/-- The underlying Hahn series of the translated weak truncation. -/
@[simp]
theorem coe_translatedTruncLE (γ : G) (b : Nonpositive G R) :
    (translatedTruncLE γ b : HahnSeries G R) = translate (-γ) (truncLE γ b) := (rfl)

/-- At cutoff zero the translated weak truncation is the identity. -/
@[simp]
theorem translatedTruncLE_zero (b : Nonpositive G R) : translatedTruncLE (0 : G) b = b := by
  apply Subtype.ext
  rw [coe_translatedTruncLE, neg_zero, translate_zero_apply,
    truncLE_eq_self_of_support_subset_Iic b.property]

variable [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [NoZeroDivisors R] [CharZero R]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := R))

private theorem degree_lt_succ_iff (d : WithBot NatOrdinal.{u}) (α : NatOrdinal.{u}) :
    d < (↑(α + 1) : WithBot NatOrdinal) ↔ d ≤ α := by
  cases d using WithBot.recBotCoe with
  | bot => simp
  | coe d =>
    rw [WithBot.coe_lt_coe, WithBot.coe_le_coe]
    exact Order.lt_add_one_iff

open Classical in
/-- The degree of a translated weak truncation is the Cantor–Bendixson rank at its cutoff, and
bottom away from the closed support. -/
theorem degree_translatedTruncLE_eq (b : Nonpositive G R) (γ : G) :
    ν (translatedTruncLE γ b) =
      if γ ∈ (b : HahnSeries G R).closedSupport then
        (NatOrdinal.of ((b : HahnSeries G R).cantorBendixsonRank γ) : WithBot NatOrdinal)
      else ⊥ := by
  rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
    coe_translatedTruncLE, HahnSeries.cantorBendixsonValue_translated_truncLE]
  by_cases hm : γ ∈ (b : HahnSeries G R).closedSupport
  · simp only [ite_eq_left hm, NatOrdinal.of_omega0_opow, NatOrdinal.cantorDegree_wpow]
  · simp only [ite_eq_right hm, NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]

/-- Translated truncations have degree strictly below any bound for the original degree,
at all sufficiently close negative cutoffs. -/
theorem eventually_degree_translatedTruncLE_lt (b : Nonpositive G R) (α : NatOrdinal.{u})
    (hb : ν b ≤ α) :
    ∀ᶠ γ in 𝓝[<] (0 : G), ν (translatedTruncLE γ b) < α := by
  classical
  by_cases hmem : 0 ∈ (b : HahnSeries G R).closedSupport
  · have hbr : NatOrdinal.of ((b : HahnSeries G R).cantorBendixsonRank 0) ≤ α := by
      rwa [cantorBendixsonDegreeValuation_of_mem _ hmem, WithBot.coe_le_coe] at hb
    have hv : (b : HahnSeries G R).cantorBendixsonValue ≠ 0 := by
      rw [cantorBendixsonValue_of_mem _ ((mem_closedSupport _ _).mp hmem)]
      exact Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero
    have hcut := ((b : HahnSeries G R).eventually_value_translated_truncLE_lt hv).filter_mono
      (nhdsWithin_le_nhds (s := Iio (0 : G)))
    filter_upwards [hcut, self_mem_nhdsWithin] with γ hγ hγ0
    rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
      NatOrdinal.cantorDegree_lt_coe_iff, coe_translatedTruncLE]
    have h := NatOrdinal.of.strictMono (hγ (ne_of_lt hγ0))
    rw [cantorBendixsonValue_of_mem _ ((mem_closedSupport _ _).mp hmem),
      NatOrdinal.of_omega0_opow] at h
    exact h.trans_le (NatOrdinal.wpow_le_wpow.mpr hbr)
  · have hnh : ((b : HahnSeries G R).closedSupport : Set G)ᶜ ∈ 𝓝 (0 : G) :=
      (b : HahnSeries G R).closedSupport.isClosed.isOpen_compl.mem_nhds hmem
    filter_upwards [nhdsWithin_le_nhds hnh] with γ hγ
    change γ ∉ (b : HahnSeries G R).closedSupport at hγ
    rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
      coe_translatedTruncLE, cantorBendixsonValue_translated_truncLE, ite_eq_right hγ,
      NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]
    exact WithBot.bot_lt_coe α

/-- A successor-degree representative has translated truncations in the preceding weak
filtration near zero. -/
theorem eventually_degree_translatedTruncLE_le (b : Nonpositive G R) (α : NatOrdinal.{u})
    (hb : ν b ≤ (α + 1 : NatOrdinal)) :
    ∀ᶠ γ in 𝓝[<] (0 : G), ν (translatedTruncLE γ b) ≤ α :=
  (eventually_degree_translatedTruncLE_lt b (α + 1) hb).mono fun _ h ↦
    (degree_lt_succ_iff _ _).mp h

/-- Vanishing of the lower-rank truncations forces a successor representative into the
strict filtration. -/
theorem degree_lt_succ_of_eventually_translatedTruncLE_lt (b : Nonpositive G R)
    (α : NatOrdinal.{u}) (hb : ν b ≤ (α + 1 : NatOrdinal))
    (hcut : ∀ᶠ γ in 𝓝[<] (0 : G), ν (translatedTruncLE γ b) < α) :
    ν b < (α + 1 : NatOrdinal) := by
  classical
  by_contra hlt
  have he : ν b = (α + 1 : NatOrdinal) := hb.antisymm (not_lt.mp hlt)
  have hmem : 0 ∈ (b : HahnSeries G R).closedSupport := by
    by_contra hn
    have hz : ν b = ⊥ := by
      rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
        cantorBendixsonValue_of_notMem _ (by simpa only [mem_closedSupport] using hn),
        NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]
    rw [hz] at he
    exact WithBot.bot_ne_coe he
  have hr : (b : HahnSeries G R).cantorBendixsonRank 0 = α.val + 1 := by
    rw [cantorBendixsonDegreeValuation_of_mem _ hmem, WithBot.coe_eq_coe] at he
    have h := congrArg NatOrdinal.val he
    simpa only [NatOrdinal.val_of, NatOrdinal.val_add_one] using h
  have hv : (b : HahnSeries G R).cantorBendixsonValue =
      Ordinal.omega0 ^ (α.val + 1) := by
    rw [cantorBendixsonValue_of_mem _ ((mem_closedSupport _ _).mp hmem), hr]
  have h := cantorBendixsonValue_reconstruction (b : HahnSeries G R) 0 b.property
    α.val 0 1 zero_lt_one hv (by
      filter_upwards [hcut] with γ hγ heγ
      rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
        coe_translatedTruncLE, heγ, NatOrdinal.of_omega0_opow, NatOrdinal.of_val,
        NatOrdinal.cantorDegree_wpow] at hγ
      exact (lt_irrefl _ hγ).elim)
  rw [cantorBendixsonValue_zero, zero_add, Ordinal.opow_one] at h
  exact (not_le_of_gt Ordinal.omega0_pos) h

open Classical in
/-- The lower homogeneous class of the translated truncation, with zero outside its domain.
For a successor-filtered input this convention is immaterial in the left filter germ. -/
def cantorBendixsonDerivAt (α : NatOrdinal.{u}) (b : Nonpositive G R) (γ : G) : (ν).Component α :=
  if h : ν (translatedTruncLE γ b) ≤ α then
    (ν).componentMk α ⟨translatedTruncLE γ b, ((ν).mem_filtrationLE_iff _ _).mpr h⟩
  else 0

/-- Within the lower weak filtration, the derivative value is the homogeneous quotient class. -/
theorem cantorBendixsonDerivAt_eq (α : NatOrdinal.{u}) (b : Nonpositive G R) (γ : G)
    (h : ν (translatedTruncLE γ b) ≤ α) :
    cantorBendixsonDerivAt α b γ =
      (ν).componentMk α ⟨translatedTruncLE γ b, ((ν).mem_filtrationLE_iff _ _).mpr h⟩ := by
  rw [cantorBendixsonDerivAt, dite_eq_left h]

/-- Under the successor-filtration bound, the pointwise derivative is nonzero exactly at the
points of the representative's closed support having the prescribed Cantor–Bendixson rank. -/
theorem cantorBendixsonDerivAt_ne_zero_iff (α : NatOrdinal.{u})
    (b : Nonpositive G R) (γ : G) (h : ν (translatedTruncLE γ b) ≤ α) :
    cantorBendixsonDerivAt α b γ ≠ 0 ↔
      γ ∈ (b : HahnSeries G R).closedSupport ∧
        (b : HahnSeries G R).cantorBendixsonRank γ = α.val := by
  classical
  rw [cantorBendixsonDerivAt_eq α b γ h, ne_eq, (ν).componentMk_eq_zero_iff,
    not_lt]
  have hdegree := degree_translatedTruncLE_eq b γ
  rw [hdegree]
  by_cases hm : γ ∈ (b : HahnSeries G R).closedSupport
  · rw [ite_eq_left hm, WithBot.coe_le_coe]
    constructor
    · intro hle
      refine ⟨hm, ?_⟩
      have heq : NatOrdinal.of ((b : HahnSeries G R).cantorBendixsonRank γ) = α :=
        le_antisymm (by simpa only [hdegree, ite_eq_left hm, WithBot.coe_le_coe] using h) hle
      have := congrArg NatOrdinal.val heq
      simpa only [NatOrdinal.val_of] using this
    · rintro ⟨_, hr⟩
      rw [hr, NatOrdinal.of_val]
  · rw [ite_eq_right hm]
    exact ⟨fun hbot ↦ ((not_le_of_gt (WithBot.bot_lt_coe α)) hbot).elim,
      fun hmem ↦ (hm hmem.1).elim⟩

/-- A derivative-stage point has exact rank when its translated truncation lies in the
corresponding weak filtration. -/
theorem cantorBendixsonRank_eq_of_mem_derivative_of_degree_translatedTruncLE_le
    (α : NatOrdinal.{u}) (b : Nonpositive G R) (γ : G)
    (hm : γ ∈ (b : HahnSeries G R).closedSupport)
    (hr : α.val ≤ (b : HahnSeries G R).cantorBendixsonRank γ)
    (h : ν (translatedTruncLE γ b) ≤ α) :
    (b : HahnSeries G R).cantorBendixsonRank γ = α.val := by
  have hzero : 0 ∈ (translatedTruncLE γ b : Nonpositive G R).1.closedSupport := by
    have ht := ((truncLE γ (b : HahnSeries G R)).mem_closedSupport_translate (-γ) γ).mpr
      ((b : HahnSeries G R).mem_closedSupport_truncLE γ |>.mpr hm)
    simpa only [coe_translatedTruncLE, neg_add_cancel] using ht
  rw [cantorBendixsonDegreeValuation_of_mem (translatedTruncLE γ b) hzero,
    WithBot.coe_le_coe] at h
  have hval := NatOrdinal.of.symm.monotone h
  change NatOrdinal.val
      (NatOrdinal.of ((translatedTruncLE γ b : Nonpositive G R).1.cantorBendixsonRank 0)) ≤
    NatOrdinal.val α at hval
  rw [NatOrdinal.val_of] at hval
  have hsr : ((translatedTruncLE γ b : Nonpositive G R).1).cantorBendixsonRank 0 =
      (b : HahnSeries G R).cantorBendixsonRank γ := by
    simpa only [coe_translatedTruncLE] using
      (b : HahnSeries G R).cantorBendixsonRank_translated_truncLE γ
  rw [hsr] at hval
  exact hval.antisymm hr

private theorem eventually_derivAt_add (α : NatOrdinal.{u}) (b c : Nonpositive G R)
    (hb : ν b ≤ (α + 1 : NatOrdinal)) (hc : ν c ≤ (α + 1 : NatOrdinal)) :
    ∀ᶠ γ in 𝓝[<] (0 : G), cantorBendixsonDerivAt α (b + c) γ =
      cantorBendixsonDerivAt α b γ + cantorBendixsonDerivAt α c γ := by
  have hbc : ν (b + c) ≤ (α + 1 : NatOrdinal) :=
    ((ν).map_add_le_max b c).trans (max_le hb hc)
  filter_upwards [eventually_degree_translatedTruncLE_le b α hb,
    eventually_degree_translatedTruncLE_le c α hc,
    eventually_degree_translatedTruncLE_le (b + c) α hbc] with γ hbg hcg hbcg
  rw [cantorBendixsonDerivAt_eq _ _ _ hbg, cantorBendixsonDerivAt_eq _ _ _ hcg,
    cantorBendixsonDerivAt_eq _ _ _ hbcg, ← map_add]
  apply congrArg ((ν).componentMk α)
  apply Subtype.ext
  exact map_add (translatedTruncLE γ) b c

private def filtrationDeriv (α : NatOrdinal.{u}) :
    (ν).filtrationLE (α + 1) →+ Filter.Germ (𝓝[<] (0 : G)) ((ν).Component α) where
  toFun b := ((fun γ ↦ cantorBendixsonDerivAt α (b : Nonpositive G R) γ) :
    Filter.Germ (𝓝[<] (0 : G)) ((ν).Component α))
  map_zero' := by
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    apply Filter.Eventually.of_forall
    intro γ
    have hzero : ν (translatedTruncLE γ 0) ≤ α := by simp
    change cantorBendixsonDerivAt α 0 γ = 0
    rw [cantorBendixsonDerivAt_eq _ _ _ hzero,
      (ν).componentMk_eq_zero_iff]
    change ν (translatedTruncLE γ 0) < α
    simp
  map_add' b c := by
    rw [← Filter.Germ.coe_add, Filter.Germ.coe_eq]
    exact eventually_derivAt_add α (b : Nonpositive G R) (c : Nonpositive G R)
      (((ν).mem_filtrationLE_iff _ _).mp b.property)
      (((ν).mem_filtrationLE_iff _ _).mp c.property)

private theorem lowerFiltration_le_filtrationDeriv_ker (α : NatOrdinal.{u}) :
    (ν).lowerFiltration (α + 1) ≤ (filtrationDeriv (G := G) (R := R) α).ker := by
  intro b hb
  change (filtrationDeriv α) b = 0
  change ((fun γ ↦ cantorBendixsonDerivAt α (b : Nonpositive G R) γ) :
    Filter.Germ (𝓝[<] (0 : G)) ((ν).Component α)) = 0
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  have hble : ν (b : Nonpositive G R) ≤ α :=
    (degree_lt_succ_iff _ _).mp (((ν).mem_lowerFiltration_iff _ _).mp hb)
  filter_upwards [eventually_degree_translatedTruncLE_lt (b : Nonpositive G R) α hble]
    with γ hγ
  change cantorBendixsonDerivAt α (b : Nonpositive G R) γ = 0
  rw [cantorBendixsonDerivAt_eq _ _ _ hγ.le, (ν).componentMk_eq_zero_iff]
  exact hγ

/-- Translated weak truncation induces an additive map from each successor homogeneous
component to left filter germs in the preceding component. -/
def cantorBendixsonLayerDeriv (α : NatOrdinal.{u}) :
    (ν).Component (α + 1) →+ Filter.Germ (𝓝[<] (0 : G)) ((ν).Component α) :=
  QuotientAddGroup.lift ((ν).lowerFiltration (α + 1)) (filtrationDeriv α)
    (lowerFiltration_le_filtrationDeriv_ker α)

/-- The map from degree `α + 1` to degree `α` is represented by translated truncation of any
representative. -/
theorem cantorBendixsonLayerDeriv_componentMk (α : NatOrdinal.{u})
    (b : (ν).filtrationLE (α + 1)) :
    cantorBendixsonLayerDeriv α ((ν).componentMk (α + 1) b) =
      ((fun γ ↦ cantorBendixsonDerivAt α (b : Nonpositive G R) γ) :
        Filter.Germ (𝓝[<] (0 : G)) ((ν).Component α)) := by
  rw [cantorBendixsonLayerDeriv, ← (ν).coe_component_eq_componentMk]
  rfl

/-- A successor homogeneous class is detected by its translated truncations near zero. -/
theorem cantorBendixsonLayerDeriv_injective (α : NatOrdinal.{u}) :
    Function.Injective (cantorBendixsonLayerDeriv (G := G) (R := R) α) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using MaxAddDegree.componentInductionOn with
  | H b =>
    rw [cantorBendixsonLayerDeriv_componentMk, ← Filter.Germ.coe_zero,
      Filter.Germ.coe_eq] at hx
    apply ((ν).componentMk_eq_zero_iff _ _).mpr
    have hb := ((ν).mem_filtrationLE_iff _ _).mp b.property
    apply degree_lt_succ_of_eventually_translatedTruncLE_lt (b : Nonpositive G R) α hb
    filter_upwards [hx, eventually_degree_translatedTruncLE_le (b : Nonpositive G R) α hb]
      with γ hγ hbound
    change cantorBendixsonDerivAt α (b : Nonpositive G R) γ = 0 at hγ
    rw [cantorBendixsonDerivAt_eq _ _ _ hbound, (ν).componentMk_eq_zero_iff] at hγ
    exact hγ

/-- **Exact lower-rank attainment.** If a series has degree exactly `α` at zero, then every
degree below `α` is attained exactly by its translated truncations at negative cutoffs
arbitrarily close to zero. Points of each lower exact rank are dense in the corresponding
derivative, and zero lies in that derivative without belonging to the level, so the level
accumulates at zero. No cofinal sequence of cutoffs is chosen. -/
theorem exists_lt_and_degree_translatedTruncLE_eq (b : Nonpositive G R) (α ρ : NatOrdinal.{u})
    (hb : ν b = (α : WithBot NatOrdinal)) (hρα : ρ < α) {l : G} (hl : l < 0) :
    ∃ γ : G, l < γ ∧ γ < 0 ∧ ν (translatedTruncLE γ b) = (ρ : WithBot NatOrdinal) := by
  classical
  have hmem : (0 : G) ∈ (b : HahnSeries G R).closedSupport := by
    by_contra hn
    rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
      cantorBendixsonValue_of_notMem _ (by simpa only [mem_closedSupport] using hn),
      NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero] at hb
    exact WithBot.bot_ne_coe hb
  have hrank : (b : HahnSeries G R).cantorBendixsonRank 0 = α.val := by
    rw [cantorBendixsonDegreeValuation_of_mem b hmem, WithBot.coe_eq_coe] at hb
    have h := congrArg NatOrdinal.val hb
    simpa only [NatOrdinal.val_of] using h
  have hρval : ρ.val < α.val := NatOrdinal.of.symm.strictMono hρα
  have hrank' : ρ.val ≤ (b : HahnSeries G R).closedSupport.cantorBendixsonRank
      (b : HahnSeries G R).closedSupport_isPWO 0 := by
    rw [← cantorBendixsonRank_eq, hrank]
    exact hρval.le
  have h0mem : (0 : G) ∈
      ((b : HahnSeries G R).closedSupport.cantorBendixson ρ.val : Set G) :=
    ((b : HahnSeries G R).closedSupport.mem_cantorBendixson_iff
      (b : HahnSeries G R).closedSupport_isPWO 0 ρ.val).mpr ⟨hmem, hrank'⟩
  have hclosure := (b : HahnSeries G R).closedSupport.closure_rank_level_eq
    (b : HahnSeries G R).closedSupport_isPWO ρ.val
  have h0cl : (0 : G) ∈ closure {x : G | x ∈ (b : HahnSeries G R).closedSupport ∧
      (b : HahnSeries G R).closedSupport.cantorBendixsonRank
        (b : HahnSeries G R).closedSupport_isPWO x = ρ.val} := by
    rw [hclosure]
    exact h0mem
  obtain ⟨p, hp⟩ := exists_ne (0 : G)
  obtain ⟨e, he⟩ : ∃ e : G, 0 < e := by
    rcases lt_or_gt_of_ne hp with h | h
    · exact ⟨-p, neg_pos.mpr h⟩
    · exact ⟨p, h⟩
  obtain ⟨γ, hγmem, hγlevel⟩ := mem_closure_iff.mp h0cl (Ioo l e) isOpen_Ioo ⟨hl, he⟩
  have hγ0 : γ ≤ 0 := closure_minimal b.property isClosed_Iic
    ((mem_closedSupport _ _).mp hγlevel.1)
  have hrank0 : (b : HahnSeries G R).closedSupport.cantorBendixsonRank
      (b : HahnSeries G R).closedSupport_isPWO 0 = α.val :=
    ((b : HahnSeries G R).cantorBendixsonRank_eq 0).symm.trans hrank
  have hγne : γ ≠ 0 := by
    intro h0
    rw [h0] at hγlevel
    exact absurd (hrank0.symm.trans hγlevel.2) (ne_of_gt hρval)
  refine ⟨γ, hγmem.1, lt_of_le_of_ne hγ0 hγne, ?_⟩
  rw [degree_translatedTruncLE_eq, ite_eq_left hγlevel.1, cantorBendixsonRank_eq, hγlevel.2,
    NatOrdinal.of_val]

/-- Below a degree that is a limit ordinal, no eventual bound on the truncation degrees holds:
attainment at the
successor of any proposed bound refutes it. -/
theorem not_forall_degree_translatedTruncLE_le (b : Nonpositive G R) (α β : NatOrdinal.{u})
    (hb : ν b = (α : WithBot NatOrdinal)) (hβα : (β + 1 : NatOrdinal) < α) {l : G} (hl : l < 0) :
    ¬ ∀ γ : G, l < γ → γ < 0 → ν (translatedTruncLE γ b) ≤ (β : WithBot NatOrdinal) := by
  intro hbound
  obtain ⟨γ, hlγ, hγ0, hγeq⟩ :=
    exists_lt_and_degree_translatedTruncLE_eq b α (β + 1) hb hβα hl
  have hle := hbound γ hlγ hγ0
  rw [hγeq, WithBot.coe_le_coe] at hle
  exact absurd hle (not_le_of_gt (lt_add_one β))

/-- **Proper cutoffs bound the degree at zero.** If every translated truncation at a strictly
negative cutoff has degree at most `τ`, then the series has degree at most `τ + 1`. The stage
`τ + 1` of the closed support meets only zero, so the next stage is empty. -/
theorem degree_le_add_one_of_forall_neg_le (b : Nonpositive G R) (τ : NatOrdinal.{u})
    (h : ∀ y : G, y < 0 → ν (translatedTruncLE y b) ≤ (τ : WithBot NatOrdinal)) :
    ν b ≤ ((τ + 1 : NatOrdinal) : WithBot NatOrdinal) := by
  classical
  have hstage : ((b : HahnSeries G R).closedSupport.cantorBendixson (τ.val + 1) : Set G) ⊆
      {0} := by
    intro z hz
    obtain ⟨hzs, hzr⟩ := ((b : HahnSeries G R).mem_support_derivative_iff z (τ.val + 1)).mp hz
    have hz0 : z ≤ 0 := closure_minimal b.property isClosed_Iic hzs
    rcases eq_or_lt_of_le hz0 with hz0' | hzneg
    · exact Set.mem_singleton_iff.mpr hz0'
    · exfalso
      have hmem : z ∈ (b : HahnSeries G R).closedSupport := (mem_closedSupport _ _).mpr hzs
      have hd := h z hzneg
      rw [degree_translatedTruncLE_eq, ite_eq_left hmem, WithBot.coe_le_coe] at hd
      have hval := NatOrdinal.of.symm.monotone hd
      change NatOrdinal.val (NatOrdinal.of ((b : HahnSeries G R).cantorBendixsonRank z)) ≤
        NatOrdinal.val τ at hval
      rw [NatOrdinal.val_of] at hval
      exact absurd hzr (not_le_of_gt (lt_of_le_of_lt hval (lt_add_one τ.val)))
  have hnext : ((b : HahnSeries G R).closedSupport.cantorBendixson ((τ.val + 1) + 1) :
      Set G) = ∅ := by
    rw [TopologicalSpace.Closeds.cantorBendixson_add_one]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rw [TopologicalSpace.Closeds.coe_derived, mem_derivedSet] at hz
    exact (Set.finite_singleton (0 : G)).not_infinite
      (Set.Infinite.of_accPt (hz.mono (Filter.principal_mono.mpr hstage)))
  by_cases hm : 0 ∈ (b : HahnSeries G R).closedSupport
  · rw [cantorBendixsonDegreeValuation_of_mem b hm, WithBot.coe_le_coe]
    have hrank : (b : HahnSeries G R).cantorBendixsonRank 0 ≤ τ.val + 1 := by
      rw [cantorBendixsonRank_eq]
      apply TopologicalSpace.Closeds.cantorBendixsonRank_le_of_notMem _ _ 0
      rw [hnext]
      exact Set.notMem_empty 0
    have h := NatOrdinal.of.monotone hrank
    rw [← NatOrdinal.val_add_one, NatOrdinal.of_val] at h
    exact h
  · rw [cantorBendixsonDegreeValuation_apply, cantorBendixsonValuation_apply,
      cantorBendixsonValue_of_notMem _ (by simpa only [mem_closedSupport] using hm),
      NatOrdinal.of_zero, NatOrdinal.cantorDegree_zero]
    exact bot_le

/-- **No uniform degree bound below a nonzero degree.** Let a series have degree exactly `lam`,
and let `sigma` be zero or have every Cantor term at least the last Cantor term of `lam`. Then no
bound strictly below `lam ⊕ sigma` dominates `ν(u^{|γ}) ⊕ sigma` on any left interval: the
ordinal approach lemma produces a degree below `lam` whose shift already reaches the proposed
bound, and exact lower-rank attainment realizes that degree at a cutoff inside the interval.

This is the obstruction used when the leading-coefficient degree has the required least term. -/
theorem not_forall_add_lt_of_degree_eq (b : Nonpositive G R) (lam sigma bound : NatOrdinal.{u})
    (hb : ν b = (lam : WithBot NatOrdinal)) (hlam : lam ≠ 0)
    (hsigma : sigma = 0 ∨ NatOrdinal.leastTerm lam ≤ NatOrdinal.leastTerm sigma)
    (hbound : bound < lam + sigma) {l : G} (hl : l < 0) :
    ¬ ∀ γ : G, l < γ → γ < 0 →
      ∀ ρ : NatOrdinal.{u}, ν (translatedTruncLE γ b) = (ρ : WithBot NatOrdinal) →
        ρ + sigma < bound := by
  intro hforall
  obtain ⟨ρ, hρlam, hρbound⟩ :=
    NatOrdinal.exists_lt_le_add_of_lastCantorTerm_le hlam hsigma hbound
  obtain ⟨γ, hlγ, hγ0, hγeq⟩ := exists_lt_and_degree_translatedTruncLE_eq b lam ρ hb hρlam hl
  exact absurd (hforall γ hlγ hγ0 ρ hγeq) (not_lt.mpr hρbound)

end HahnSeries.Nonpositive
