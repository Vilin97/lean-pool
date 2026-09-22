/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Standalone.CombinatorialGames.PrincipalRVAlgebraicIndependence
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.Polynomiality

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValue
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportSupremum
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NegativeMonomialIdeal
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.AlgebraicIndependence.TruncationExpansion
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.Extension

/-!
# Proof of algebraic independence in `P̂`

The standalone ring `nonpos K` is `K((ℝ^{≤0}))`, and its `ordinalValue` is Berarducci's ordinal
value. Standalone decomposability agrees with membership in
`(P̂_+)² ∩ P_β = ∑_{i ⊕ j = β, i, j ≠ 0} P_i P_j`. A minimal homogeneous family extends to a
minimal homogeneous generating system of `P̂`; polynomiality of that system gives algebraic
independence of the original family.
-/

universe u

open scoped NatOrdinal HahnSeries
open Berarducci HahnSeries MvPolynomial OrdinalGraded

public noncomputable section

namespace ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence

variable {K : Type u} [Field K]

/-! ### The ring -/

/-- The standalone and development presentations of `K((ℝ^{≤0}))` are the same `K`-algebra. -/
@[expose] def seriesAlgEquiv : nonpos K ≃ₐ[K] Series K where
  toFun a := ⟨(a : HahnSeries ℝ K), (HahnSeries.mem_nonpositiveSubring ℝ K).mpr a.2⟩
  invFun s := ⟨(s : HahnSeries ℝ K), (HahnSeries.mem_nonpositiveSubring ℝ K).mp s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' k := by
    rw [HahnSeries.Nonpositive.algebraMap_apply]
    exact Subtype.ext <| by
      rw [Subalgebra.coe_algebraMap, HahnSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, HahnSeries.Nonpositive.coe_C]

/-- Regard the standalone presentation as Berarducci's series ring. -/
abbrev toSeries (a : nonpos K) : Series K := seriesAlgEquiv a

/-- Regard Berarducci's series ring in the standalone presentation. -/
abbrev ofSeries (s : Series K) : nonpos K := seriesAlgEquiv.symm s

@[simp] theorem coe_toSeries (a : nonpos K) :
    ((toSeries a : Series K) : HahnSeries ℝ K) = (a : HahnSeries ℝ K) := rfl

@[simp] theorem toSeries_ofSeries (s : Series K) : toSeries (ofSeries s) = s := rfl

theorem toSeries_algebraMap (k : K) :
    toSeries (algebraMap K (nonpos K) k) = HahnSeries.Nonpositive.C k := by
  rw [← HahnSeries.Nonpositive.algebraMap_apply]
  exact seriesAlgEquiv.commutes k

theorem toSeries_sub (a b : nonpos K) : toSeries (a - b) = toSeries a - toSeries b :=
  map_sub seriesAlgEquiv a b

theorem toSeries_add (a b : nonpos K) : toSeries (a + b) = toSeries a + toSeries b :=
  map_add seriesAlgEquiv a b

theorem toSeries_mul (a b : nonpos K) : toSeries (a * b) = toSeries a * toSeries b :=
  map_mul seriesAlgEquiv a b

theorem toSeries_sum {ι : Type*} (s : Finset ι) (f : ι → nonpos K) :
    toSeries (∑ i ∈ s, f i) = ∑ i ∈ s, toSeries (f i) :=
  map_sum seriesAlgEquiv f s

theorem toSeries_aeval {ι : Type*} (b : ι → nonpos K) (F : MvPolynomial ι K) :
    toSeries (aeval b F) = aeval (fun i ↦ toSeries (b i)) F := by
  change seriesAlgEquiv.toAlgHom (aeval b F) = aeval (fun i ↦ seriesAlgEquiv (b i)) F
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

/-! ### The ordinal value -/

theorem ot_eq (x : HahnSeries ℝ K) : ot x = HahnSeries.supportOrderType x := by
  haveI : WellFoundedLT x.support := (supportIsWellOrder x).wf
  exact (HahnSeries.supportOrderType_eq_typeLT (OrderIso.refl _)).symm

theorem memJ_iff (a : nonpos K) :
    MemJ a ↔ toSeries a ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero]
  rcases eq_or_ne (toSeries a) 0 with h0 | h0
  · rw [h0, HahnSeries.Nonpositive.supportSup_zero]
    refine ⟨fun _ ↦ WithBot.bot_lt_coe 0, fun _ ↦ ⟨-1, by norm_num, fun y hy ↦ ?_⟩⟩
    have : (a : HahnSeries ℝ K) = 0 := by
      have := congrArg (fun s : Series K ↦ (s : HahnSeries ℝ K)) h0
      simpa using this
    rw [this, HahnSeries.support_zero] at hy
    exact absurd hy (Set.notMem_empty y)
  · have h0' : (a : HahnSeries ℝ K) ≠ 0 := fun h ↦ h0 (Subtype.ext h)
    rw [HahnSeries.Nonpositive.supportSup_of_ne h0, ← WithBot.coe_zero, WithBot.coe_lt_coe]
    constructor
    · rintro ⟨s, hs, hsupp⟩
      exact (csSup_le (HahnSeries.support_nonempty_iff.mpr h0') hsupp).trans_lt hs
    · intro h
      exact ⟨_, h, fun y hy ↦ le_csSup (HahnSeries.Nonpositive.bddAbove_support (toSeries a)) hy⟩

theorem isNearConstant_iff (a : nonpos K) :
    IsNearConstant a ↔ toSeries a ∈ Berarducci.nearConstantSubgroup K := by
  rw [Berarducci.mem_nearConstantSubgroup_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨toSeries (a - algebraMap K (nonpos K) k), (memJ_iff _).mp hk, k, ?_⟩
    rw [toSeries_sub, toSeries_algebraMap, sub_add_cancel]
  · rintro ⟨j, hj, k, hjk⟩
    refine ⟨k, (memJ_iff _).mpr ?_⟩
    rw [toSeries_sub, toSeries_algebraMap, ← hjk, add_sub_cancel_right]
    exact hj

/-- The standalone ordinal value is Berarducci's. -/
theorem ordinalValue_eq (a : nonpos K) : ordinalValue a = Berarducci.ordinalValue (toSeries a) := by
  classical
  unfold ordinalValue
  by_cases hJ : MemJ a
  · rw [ite_eq_left hJ, Berarducci.ordinalValue_of_mem_negativeMonomialIdeal ((memJ_iff a).mp hJ)]
  rw [ite_eq_right hJ]
  by_cases hN : IsNearConstant a
  · rw [ite_eq_left hN,
      Berarducci.ordinalValue_of_mem_nearConstantSubgroup_of_not_mem_negativeMonomialIdeal
        ((isNearConstant_iff a).mp hN) (fun h ↦ hJ ((memJ_iff a).mpr h))]
  rw [ite_eq_right hN,
    Berarducci.ordinalValue_of_not_mem_nearConstantSubgroup
      (fun h ↦ hN ((isNearConstant_iff a).mpr h))]
  congr 1
  ext o
  simp only [Set.mem_setOf_eq, Berarducci.mem_representativeOrderTypes_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨toSeries c, ?_, by rw [ot_eq]; rfl⟩
    have := (isNearConstant_iff _).mp hc
    rwa [toSeries_sub] at this
  · rintro ⟨c, hc, rfl⟩
    refine ⟨ofSeries c, ?_, by rw [ot_eq]; rfl⟩
    rw [isNearConstant_iff, toSeries_sub, toSeries_ofSeries]
    exact hc

/-! ### Decomposables -/

/-- A representative of the sum of two classes differs from the sum of representatives by a
series of small value. -/
theorem ordinalValue_sub_lt_of_represents {a a₁ a₂ : Series K} {β : NatOrdinal}
    {y₁ y₂ : PrincipalSubring K} (h : Represents a β (y₁ + y₂)) (h₁ : Represents a₁ β y₁)
    (h₂ : Represents a₂ β y₂) : Berarducci.ordinalValue (a - (a₁ + a₂)) < ω^ β := by
  have h12 := h₁.add h₂
  obtain ⟨ha, hae⟩ := represents_iff.mp h
  obtain ⟨ha12, ha12e⟩ := represents_iff.mp h12
  have := DirectSum.of_injective β (hae.trans ha12e.symm)
  exact (principalComponentMk_eq_iff β _ _ ha ha12).mp this

/-- The standalone decomposables contain every series representing an element of
`(P̂_+)² ∩ P_β` (`decomposableAt`). -/
theorem isDecomposable_of_mem_decomposableAt {β : NatOrdinal} {y : PrincipalSubring K}
    (hy : y ∈ decomposableAt (principalGrading K) β) {a : nonpos K}
    (ha : Represents (toSeries a) β y) : IsDecomposable β a := by
  classical
  -- the submodule of elements of `P_β` all of whose representatives are decomposable
  let N : Submodule K (PrincipalSubring K) :=
    { carrier := {y | y ∈ principalGrading K β ∧
        ∀ a : nonpos K, Represents (toSeries a) β y → IsDecomposable β a}
      zero_mem' := by
        refine ⟨zero_mem _, fun a ha ↦ ?_⟩
        refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, fun k ↦ k.elim0, fun k ↦ k.elim0,
          fun k ↦ k.elim0, ?_⟩
        rw [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, ordinalValue_eq]
        exact ha.ordinalValue_lt_of_eq_zero
      add_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨add_mem hy₁ hy₂, fun a ha ↦ ?_⟩
        -- representatives of `y₁`, `y₂`
        obtain ⟨z₁, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ _ y₁).mp hy₁
        obtain ⟨z₂, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ _ y₂).mp hy₂
        simp only [DirectSum.lof_eq_of] at h₁ h₂ ha
        obtain ⟨s₁, hs₁, hz₁⟩ := exists_principalComponentMk β z₁
        obtain ⟨s₂, hs₂, hz₂⟩ := exists_principalComponentMk β z₂
        have hr₁ : Represents (toSeries (ofSeries s₁)) β
            (DirectSum.of (PrincipalComponent K) β z₁) := by
          rw [toSeries_ofSeries]; exact represents_iff.mpr ⟨hs₁, congrArg _ hz₁⟩
        have hr₂ : Represents (toSeries (ofSeries s₂)) β
            (DirectSum.of (PrincipalComponent K) β z₂) := by
          rw [toSeries_ofSeries]; exact represents_iff.mpr ⟨hs₂, congrArg _ hz₂⟩
        obtain ⟨n₁, β₁, β₁', u₁, w₁, hβ₁, hu₁, hw₁, hv₁⟩ := h₁ _ hr₁
        obtain ⟨n₂, β₂, β₂', u₂, w₂, hβ₂, hu₂, hw₂, hv₂⟩ := h₂ _ hr₂
        refine ⟨n₁ + n₂, Fin.append β₁ β₂, Fin.append β₁' β₂', Fin.append u₁ u₂, Fin.append w₁ w₂,
          fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_, ?_⟩
        · refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) k
          · simp only [Fin.append_left]; exact hβ₁ k
          · simp only [Fin.append_right]; exact hβ₂ k
        · refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) k
          · simp only [Fin.append_left]; exact hu₁ k
          · simp only [Fin.append_right]; exact hu₂ k
        · refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) k
          · simp only [Fin.append_left]; exact hw₁ k
          · simp only [Fin.append_right]; exact hw₂ k
        · rw [Fin.sum_univ_add]
          simp only [Fin.append_left, Fin.append_right]
          rw [ordinalValue_eq] at hv₁ hv₂ ⊢
          simp only [toSeries_sub, toSeries_add, toSeries_sum, toSeries_ofSeries] at hv₁ hv₂ ⊢
          have hsmall := ordinalValue_sub_lt_of_represents ha hr₁ hr₂
          rw [toSeries_ofSeries, toSeries_ofSeries] at hsmall
          have heq : toSeries a - (∑ k, toSeries (u₁ k * w₁ k) + ∑ k, toSeries (u₂ k * w₂ k)) =
              (toSeries a - (s₁ + s₂)) + (s₁ - ∑ k, toSeries (u₁ k * w₁ k)) +
                (s₂ - ∑ k, toSeries (u₂ k * w₂ k)) := by abel
          rw [heq]
          refine (ordinalValue_add_le_max _ _).trans_lt (max_lt ?_ hv₂)
          exact (ordinalValue_add_le_max _ _).trans_lt (max_lt hsmall hv₁)
      smul_mem' := by
        rintro k y ⟨hy, h⟩
        refine ⟨Submodule.smul_mem _ k hy, fun a ha ↦ ?_⟩
        obtain ⟨z, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ _ y).mp hy
        rw [DirectSum.lof_eq_of] at h ha
        obtain ⟨s, hs, hz⟩ := exists_principalComponentMk β z
        have hr : Represents (toSeries (ofSeries s)) β
            (DirectSum.of (PrincipalComponent K) β z) := by
          rw [toSeries_ofSeries]; exact represents_iff.mpr ⟨hs, congrArg _ hz⟩
        obtain ⟨n, β₀, β₀', u, w, hβ₀, hu, hw, hv⟩ := h _ hr
        -- `C k · s` represents `k • y`
        have hrk : Represents (HahnSeries.Nonpositive.C k * s) β
            (k • DirectSum.of (PrincipalComponent K) β z) := by
          have hr' : Represents s β (DirectSum.of (PrincipalComponent K) β z) := by
            rw [← toSeries_ofSeries s]; exact hr
          have := (represents_C (K := K) k).mul hr'
          rw [zero_add] at this
          rw [Algebra.smul_def]
          exact this
        refine ⟨n, β₀, β₀', fun i ↦ algebraMap K (nonpos K) k * u i, w, hβ₀, fun i ↦ ?_, hw, ?_⟩
        · rw [ordinalValue_eq, toSeries_mul, toSeries_algebraMap]
          have hui := hu i
          rw [ordinalValue_eq] at hui
          exact Lifts.ordinalValue_C_mul_lt k hui
        · rw [ordinalValue_eq, toSeries_sub, toSeries_sum]
          rw [ordinalValue_eq, toSeries_sub, toSeries_sum, toSeries_ofSeries] at hv
          have hsmall :
              Berarducci.ordinalValue (toSeries a - HahnSeries.Nonpositive.C k * s) < ω^ β := by
            obtain ⟨h1, h1e⟩ := represents_iff.mp ha
            obtain ⟨h2, h2e⟩ := represents_iff.mp hrk
            exact (principalComponentMk_eq_iff β _ _ h1 h2).mp
              (DirectSum.of_injective β (h1e.trans h2e.symm))
          have heq : toSeries a - ∑ i, toSeries (algebraMap K (nonpos K) k * u i * w i) =
              (toSeries a - HahnSeries.Nonpositive.C k * s) +
                HahnSeries.Nonpositive.C k * (s - ∑ i, toSeries (u i * w i)) := by
            simp only [toSeries_mul, toSeries_algebraMap, mul_sub, Finset.mul_sum, mul_assoc]
            abel
          rw [heq]
          exact (ordinalValue_add_le_max _ _).trans_lt
            (max_lt hsmall (Lifts.ordinalValue_C_mul_lt k hv)) }
  -- the decomposables lie in `N`
  have hle : decomposableAt (principalGrading K) β ≤ N := by
    refine decomposableAt_le (principalGrading K) fun i j hi hj hij ↦
      Submodule.mul_le.mpr fun m hm n hn ↦ ?_
    refine ⟨hij ▸ SetLike.mul_mem_graded hm hn, fun a ha ↦ ?_⟩
    obtain ⟨zm, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ _ m).mp hm
    obtain ⟨zn, rfl⟩ := (DirectSum.mem_rangeLof_iff K _ _ n).mp hn
    simp only [DirectSum.lof_eq_of] at ha
    obtain ⟨sm, hsm, hzm⟩ := exists_principalComponentMk i zm
    obtain ⟨sn, hsn, hzn⟩ := exists_principalComponentMk j zn
    have hrm : Represents sm i (DirectSum.of (PrincipalComponent K) i zm) :=
      represents_iff.mpr ⟨hsm, congrArg _ hzm⟩
    have hrn : Represents sn j (DirectSum.of (PrincipalComponent K) j zn) :=
      represents_iff.mpr ⟨hsn, congrArg _ hzn⟩
    have hrmn := (hrm.mul hrn).of_eq hij
    refine ⟨1, fun _ ↦ i, fun _ ↦ j, fun _ ↦ ofSeries sm, fun _ ↦ ofSeries sn,
      fun _ ↦ ⟨hi, hj, hij⟩, fun _ ↦ ?_, fun _ ↦ ?_, ?_⟩
    · rw [ordinalValue_eq, toSeries_ofSeries]; exact hsm
    · rw [ordinalValue_eq, toSeries_ofSeries]; exact hsn
    · rw [Fin.sum_univ_one, ordinalValue_eq, toSeries_sub, toSeries_mul, toSeries_ofSeries,
        toSeries_ofSeries]
      obtain ⟨h1, h1e⟩ := represents_iff.mp ha
      obtain ⟨h2, h2e⟩ := represents_iff.mp hrmn
      exact (principalComponentMk_eq_iff β _ _ h1 h2).mp
        (DirectSum.of_injective β (h1e.trans h2e.symm))
  exact (hle hy).2 a ha

/-! ### Minimal homogeneous families -/

variable {ι : Type} (deg : ι → NatOrdinal) (b : ι → nonpos K)
  (hB : IsMinimalHomogeneousFamily deg b)
include hB

theorem ordinalValue_toSeries_lt (i : ι) :
    Berarducci.ordinalValue (toSeries (b i)) < ω^ (deg i + 1) := by
  rw [← ordinalValue_eq]; exact hB.mem i

/-- The classes of the generators. -/
def classes (i : ι) : PrincipalSubring K :=
  DirectSum.of (PrincipalComponent K) (deg i)
    (principalComponentMk (deg i) (toSeries (b i)) (ordinalValue_toSeries_lt deg b hB i))

/-- The lifts of the classes: the series themselves. -/
def lifts : Lifts deg (classes deg b hB) where
  lift i := toSeries (b i)
  represents i := represents_iff.mpr ⟨ordinalValue_toSeries_lt deg b hB i, rfl⟩

/-- The classes of the given family are independent modulo the decomposables. -/
theorem independent_classes (β : NatOrdinal) (c : ι →₀ K) (hc : ∀ i ∈ c.support, deg i = β)
    (hdec : Finsupp.linearCombination K (classes deg b hB) c ∈
      decomposableAt (principalGrading K) β) : c = 0 := by
  classical
  refine hB.independent β c hc ?_
  refine isDecomposable_of_mem_decomposableAt hdec ?_
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, toSeries_sum]
  refine represents_sum _ _ _ _ fun i hi ↦ ?_
  rw [toSeries_mul, toSeries_algebraMap, Algebra.smul_def]
  have := (represents_C (K := K) (c i)).mul ((lifts deg b hB).represents i)
  rw [zero_add, hc i hi] at this
  exact this

omit hB in
/-- Renaming the variables along a degree-preserving map preserves homogeneity. -/
theorem isWeightedHomogeneous_rename {ι' : Type*} {e : ι → ι'} {wt' : ι' → NatOrdinal}
    (hwt : ∀ i, wt' (e i) = deg i) {F : MvPolynomial ι K} {α : NatOrdinal}
    (hF : IsWeightedHomogeneous deg F α) : IsWeightedHomogeneous wt' (rename e F) α := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero e F d hd
  rw [← hF hu, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c ↦ c • wt' i) (fun _ ↦ zero_smul ℕ _)
      (fun _ _ _ ↦ add_smul _ _ _)]
  exact Finsupp.sum_congr fun i _ ↦ by rw [hwt]

end ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence

namespace ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence

namespace MinimalFamiliesAlgebraicallyIndependent

open ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence

/-- Every minimal homogeneous family in `P̂` is algebraically independent. -/
theorem of_algebraicIndependence (K : Type u) [Field K] :
    PrincipalRVAlgebraicIndependence.MinimalFamiliesAlgebraicallyIndependent K := by
  intro hK
  letI := hK
  intro ι deg b hB α F hF hval
  -- Extend the family to a minimal homogeneous generating system of `P̂`.
  obtain ⟨ι', wt', x', e, he, hwt', hx', hmin⟩ :=
    exists_isMinimalSystem_extension (principalGrading K) hB.ne_zero
      (fun i ↦ of_mem_principalGrading _ _) (independent_classes deg b hB)
  have hinj := Berarducci.injectiveAt_of_isMinimalSystem hmin α
  -- `F(classes) = 0` in `P̂`
  have hrep := (lifts deg b hB).aeval_represents hF
  have h0 : Berarducci.ordinalValue (aeval (lifts deg b hB).lift F) < ω^ α := by
    have : aeval (lifts deg b hB).lift F = toSeries (aeval b F) := (toSeries_aeval b F).symm
    rw [this, ← ordinalValue_eq]
    exact hval
  obtain ⟨hu, heq⟩ := represents_iff.mp hrep
  have hzero : aeval (classes deg b hB) F = 0 := by
    rw [← heq, (principalComponentMk_eq_zero_iff α _ hu).mpr h0, map_zero]
  -- hence `F`, read in the extended variables, vanishes, so `F = 0`
  have hren : rename e F = 0 := by
    refine (injectiveAt_iff α).mp hinj _ (isWeightedHomogeneous_rename deg hwt' hF) ?_
    rw [aeval_rename]
    have : x' ∘ e = classes deg b hB := funext hx'
    rw [this]
    exact hzero
  exact rename_injective e he (by rw [hren, map_zero])

end MinimalFamiliesAlgebraicallyIndependent

end ConwayRefinement.Standalone.PrincipalRVAlgebraicIndependence
