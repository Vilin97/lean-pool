/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.UniqueAlgebraicExtensions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.Algebra.Tower
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.LocalRingEquiv
/-!
# the fundamental inequality and identity

The first part follows the proof on pp. 149--150: residue-basis lifts are
multiplied by representatives of distinct value-group cosets, and the
resulting family is linearly independent over the base field.  The second
part uses the actual valuation rings.  For a discrete Henselian base and a
finite separable extension, the finite norm-formula theorem identifies the target valuation ring
with the integral closure, so the local Dedekind ramification identity applies
without completeness.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

open Module

private def ramificationAddValuation {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) : AddValuation K (WithTop ℝ) :=
  AddValuation.of v
    ((v.eq_top_iff 0).mpr rfl)
    (LubinTate.Valuations.exponentialValuation_one v)
    v.add_le_min v.map_mul

@[simp]
private theorem ramificationAddValuation_apply {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) (x : K) :
    ramificationAddValuation v x = v x :=
  rfl

private theorem ramificationAddValuation_finset_sum_eq_of_unique_min
    {K I : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) (s : Finset I) (f : I → K) (j : I)
    (hj : j ∈ s) (hjtop : v (f j) ≠ ⊤)
    (hmin : ∀ i ∈ s, i ≠ j → v (f j) < v (f i)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  classical
  rw [← Finset.sum_erase_add s f hj, add_comm]
  apply (ramificationAddValuation v).map_add_eq_of_lt_left
  apply (ramificationAddValuation v).map_lt_sum hjtop
  intro i hi
  rcases Finset.mem_erase.mp hi with ⟨hij, his⟩
  exact hmin i his hij

/-- A finite sum of nonzero terms of pairwise distinct values cannot vanish. -/
private theorem exponentialValuation_finset_sum_ne_zero_of_value_ne
    {K I : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) (s : Finset I) (f : I → K)
    (hne : ∃ i ∈ s, f i ≠ 0)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      f i ≠ 0 → f j ≠ 0 → v (f i) ≠ v (f j)) :
    ∑ i ∈ s, f i ≠ 0 := by
  classical
  let T := s.filter fun i ↦ f i ≠ 0
  have hT : T.Nonempty := by
    rcases hne with ⟨i, his, hfi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨his, hfi⟩⟩
  obtain ⟨j, hjT, hjmin⟩ := T.exists_min_image (fun i ↦ v (f i)) hT
  have hjS : j ∈ s := (Finset.mem_filter.mp hjT).1
  have hfj : f j ≠ 0 := (Finset.mem_filter.mp hjT).2
  have hmin : ∀ i ∈ T, i ≠ j → v (f j) < v (f i) := by
    intro i hiT hij
    have hiS : i ∈ s := (Finset.mem_filter.mp hiT).1
    have hfi : f i ≠ 0 := (Finset.mem_filter.mp hiT).2
    exact lt_of_le_of_ne (hjmin i hiT)
      (hpair j hjS i hiS hij.symm hfj hfi)
  have hvalue :=
    ramificationAddValuation_finset_sum_eq_of_unique_min
      v T f j hjT (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hfj) hmin
  have hsum : (∑ i ∈ T, f i) = ∑ i ∈ s, f i := by
    dsimp [T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hfi : f i = 0 <;> simp [hfi]
  rw [hsum] at hvalue
  intro hzero
  rw [hzero, (v.eq_top_iff 0).mpr rfl] at hvalue
  exact (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hfj) hvalue.symm

/-- The map of valuation rings induced by an exact extension of exponential
exponential valuations. -/
def exponentialValuationRingMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    LubinTate.Valuations.exponentialValuationSubring v →+*
      LubinTate.Valuations.exponentialValuationSubring w :=
  (algebraMap K L).restrict _ _ fun a ha ↦ by
    change (0 : WithTop ℝ) ≤ w (algebraMap K L a)
    rw [hExt]
    exact ha

@[simp]
theorem exponentialValuationRingMap_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (a : LubinTate.Valuations.exponentialValuationSubring v) :
    ((exponentialValuationRingMap v w hExt a :
      LubinTate.Valuations.exponentialValuationSubring w) : L) =
        algebraMap K L (a : K) :=
  rfl

/-- Exact extension makes the induced map of valuation rings local. -/
theorem exponentialValuationRingMap_isLocalHom
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    IsLocalHom (exponentialValuationRingMap v w hExt) := by
  constructor
  intro a ha
  have hwzero :
      w (((exponentialValuationRingMap v w hExt) a :
        LubinTate.Valuations.exponentialValuationSubring w) : L) = 0 :=
    LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit w ha
  have hvzero : v (a : K) = 0 := by
    rw [exponentialValuationRingMap_apply, hExt] at hwzero
    exact hwzero
  exact LubinTate.Valuations.isUnit_of_exponentialValuation_eq_zero v hvzero

/-- A nontrivial residue-linear combination of lifts is a unit in the target
valuation ring. This is the residue-basis step in the proof of the
fundamental inequality. -/
private theorem exponentialValuation_residueCombination_value_zero
    {K L J : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype J]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := exponentialValuationRingMap v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : IsLocalHom i :=
        exponentialValuationRingMap_isLocalHom v w hExt
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      LinearIndependent (IsLocalRing.ResidueField V)
        (fun j ↦ IsLocalRing.residue W (omega j)))
    (c : J → LubinTate.Valuations.exponentialValuationSubring v)
    (hc : ∃ j, IsLocalRing.residue
      (LubinTate.Valuations.exponentialValuationSubring v) (c j) ≠ 0) :
    w (∑ j, algebraMap K L (c j : K) * (omega j : L)) = 0 := by
  classical
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  let s : W := ∑ j, i (c j) * omega j
  have hres_ne : IsLocalRing.residue W s ≠ 0 := by
    intro hs
    have hcoeff_zero :
        ∀ j, IsLocalRing.residue V (c j) = 0 := by
      apply (Fintype.linearIndependent_iff.mp homega
        (fun j ↦ IsLocalRing.residue V (c j)))
      rw [← hs]
      dsimp only [s]
      simp only [map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← IsLocalRing.ResidueField.map_residue i]
      rfl
    rcases hc with ⟨j, hj⟩
    exact hj (hcoeff_zero j)
  have hsunit : IsUnit s := by
    exact (IsLocalRing.residue_ne_zero_iff_isUnit s).mp hres_ne
  have hsvalue : w (s : L) = 0 :=
    LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit w hsunit
  have hs_coe :
      (s : L) = ∑ j, algebraMap K L (c j : K) * (omega j : L) := by
    dsimp only [s]
    change W.subtype (∑ j, i (c j) * omega j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    congr 1
  rw [hs_coe] at hsvalue
  exact hsvalue

/-- Dividing by an element of no larger value produces an element of the
valuation ring. -/
private theorem exponentialValuation_div_nonneg_of_le
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K)
    {a b : K} (hb : b ≠ 0) (hba : v b ≤ v a) :
    (0 : WithTop ℝ) ≤ v (a / b) := by
  by_cases ha : a = 0
  · simp [ha, (v.eq_top_iff 0).mpr rfl]
  · obtain ⟨ra, hra⟩ :=
      LubinTate.Valuations.exponentialValuation_exists_real_of_ne_zero v ha
    obtain ⟨rb, hrb⟩ :=
      LubinTate.Valuations.exponentialValuation_exists_real_of_ne_zero v hb
    have hrle : rb ≤ ra := by
      rw [hra, hrb] at hba
      exact WithTop.coe_le_coe.mp hba
    rw [div_eq_mul_inv, v.map_mul,
      LubinTate.Valuations.exponentialValuation_inv_value v hb hrb, hra]
    exact WithTop.coe_nonneg.mpr (sub_nonneg.mpr hrle)

/-- A nonzero linear combination of residue-basis lifts has the value of one
of its nonzero base coefficients. -/
private theorem exponentialValuation_residueCombination_value_in_base
    {K L J : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype J]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := exponentialValuationRingMap v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : IsLocalHom i :=
        exponentialValuationRingMap_isLocalHom v w hExt
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      LinearIndependent (IsLocalRing.ResidueField V)
        (fun j ↦ IsLocalRing.residue W (omega j)))
    (a : J → K) (ha : ∃ j, a j ≠ 0) :
    ∃ a₀ : K, a₀ ≠ 0 ∧
      w (∑ j, algebraMap K L (a j) * (omega j : L)) =
        w (algebraMap K L a₀) := by
  classical
  let S : Finset J := Finset.univ.filter fun j ↦ a j ≠ 0
  have hS : S.Nonempty := by
    rcases ha with ⟨j, hj⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨j₀, hj₀S, hj₀min⟩ :=
    S.exists_min_image (fun j ↦ v (a j)) hS
  have hj₀ : a j₀ ≠ 0 := (Finset.mem_filter.mp hj₀S).2
  let c : J → LubinTate.Valuations.exponentialValuationSubring v := fun j ↦
    ⟨a j / a j₀, by
      by_cases hj : a j = 0
      · simp [hj]
      · apply exponentialValuation_div_nonneg_of_le v hj₀
        exact hj₀min j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  have hcj₀ : IsLocalRing.residue
      (LubinTate.Valuations.exponentialValuationSubring v) (c j₀) ≠ 0 := by
    have hcj₀eq : c j₀ = 1 := by
      ext
      simp [c, hj₀]
    rw [hcj₀eq, map_one]
    exact one_ne_zero
  have hcvalue :=
    exponentialValuation_residueCombination_value_zero
      v w hExt omega homega c ⟨j₀, hcj₀⟩
  have hfactor :
      (∑ j, algebraMap K L (a j) * (omega j : L)) =
        algebraMap K L (a j₀) *
          (∑ j, algebraMap K L (c j : K) * (omega j : L)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [c]
    rw [← mul_assoc, ← map_mul]
    field_simp
  refine ⟨a j₀, hj₀, ?_⟩
  rw [hfactor, w.map_mul, hcvalue, add_zero]

/-- The actual additive value group `v(Kˣ)`, realized as a subgroup of
`ℝ`. -/
def exponentialValueSubgroup
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K) :
    AddSubgroup ℝ where
  carrier := {r | ∃ x : K, x ≠ 0 ∧ v x = (r : WithTop ℝ)}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro r s ⟨x, hx, hr⟩ ⟨y, hy, hs⟩
    refine ⟨x * y, mul_ne_zero hx hy, ?_⟩
    rw [v.map_mul, hr, hs, WithTop.coe_add]
  neg_mem' := by
    rintro r ⟨x, hx, hr⟩
    refine ⟨x⁻¹, inv_ne_zero hx, ?_⟩
    exact LubinTate.Valuations.exponentialValuation_inv_value v hx hr

/-- Conversely to the valuation-ring criterion, if the valuation ring attached to an exponential
exponential valuation is a DVR, its real value group is discrete. -/
theorem discreteExponentialValuation_of_isDiscreteValuationRing
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K)
    [IsDiscreteValuationRing (LubinTate.Valuations.exponentialValuationSubring v)] :
    LubinTate.Valuations.DiscreteExponentialValuation v := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hpi0V : pi ≠ 0 := hpi.ne_zero
  have hpi0 : (pi : K) ≠ 0 := by
    intro hz
    exact hpi0V (Subtype.ext hz)
  have hpiMax : pi ∈ IsLocalRing.maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hpi.not_isUnit
  have hpipos : (0 : WithTop ℝ) < v (pi : K) := by
    rw [← LubinTate.Valuations.exponentialMaxIdeal_eq_maximalIdeal v] at hpiMax
    exact hpiMax
  let s : ℝ := (v (pi : K)).untop₀
  have hpival : v (pi : K) = (s : WithTop ℝ) :=
    (WithTop.coe_untop₀_of_ne_top
      (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hpi0)).symm
  have hs : 0 < s := by
    rw [hpival] at hpipos
    exact WithTop.coe_lt_coe.mp hpipos
  refine ⟨s, hs, ?_, (pi : K), hpival⟩
  intro x hx
  rcases LubinTate.Valuations.exponentialValuationRing_mem_or_inv_mem v x with hxV | hxinvV
  · let xV : V := ⟨x, hxV⟩
    have hxV0 : xV ≠ 0 := by
      intro hz
      exact hx (congrArg Subtype.val hz)
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxV0 hpi
    have huval : v (((u : Vˣ) : V) : K) = 0 :=
      LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit v u.isUnit
    have hxEq : x = (((u : Vˣ) : V) : K) * (pi : K) ^ n :=
      congrArg Subtype.val hu
    refine ⟨(n : ℤ), ?_⟩
    rw [hxEq, v.map_mul, huval, zero_add,
      LubinTate.Valuations.discretePrimeElement_pow_value v hpival]
    norm_num
  · let xinvV : V := ⟨x⁻¹, hxinvV⟩
    have hxinv0 : xinvV ≠ 0 := by
      intro hz
      exact (inv_ne_zero hx) (congrArg Subtype.val hz)
    obtain ⟨n, u, hu⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxinv0 hpi
    have huval : v (((u : Vˣ) : V) : K) = 0 :=
      LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit v u.isUnit
    have hxinvEq : x⁻¹ = (((u : Vˣ) : V) : K) * (pi : K) ^ n :=
      congrArg Subtype.val hu
    have hxinvVal : v x⁻¹ = (((n : ℝ) * s : ℝ) : WithTop ℝ) := by
      rw [hxinvEq, v.map_mul, huval, zero_add,
        LubinTate.Valuations.discretePrimeElement_pow_value v hpival]
    have hxVal :=
      LubinTate.Valuations.exponentialValuation_inv_value v (inv_ne_zero hx) hxinvVal
    refine ⟨-(n : ℤ), ?_⟩
    rw [inv_inv] at hxVal
    convert hxVal using 1
    norm_num

private theorem discretePrimeElement_zpow_value_scaled
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K)
    {pi : K} {s : ℝ} (hpi0 : pi ≠ 0)
    (hpival : v pi = (s : WithTop ℝ)) (m : ℤ) :
    v (pi ^ m) = ((((m : ℝ) * s : ℝ)) : WithTop ℝ) := by
  cases m with
  | ofNat n =>
      simpa [zpow_natCast] using
        LubinTate.Valuations.discretePrimeElement_pow_value v hpival n
  | negSucc n =>
      have hpow0 : pi ^ (n + 1) ≠ 0 := pow_ne_zero _ hpi0
      have hpowval :=
        LubinTate.Valuations.discretePrimeElement_pow_value v hpival (n + 1)
      have hinv :=
        LubinTate.Valuations.exponentialValuation_inv_value v hpow0 hpowval
      rw [zpow_negSucc, hinv]
      apply congrArg (fun z : ℝ ↦ (z : WithTop ℝ))
      norm_num [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
      ring

/-- A discrete value group with least positive value `s` is literally the
cyclic subgroup `sℤ` of `ℝ`. -/
private theorem exponentialValueSubgroup_eq_zmultiples
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K)
    {s : ℝ}
    (hvalues : ∀ x : K, x ≠ 0 → ∃ m : ℤ,
      v x = ((((m : ℝ) * s : ℝ)) : WithTop ℝ))
    {pi : K} (hpival : v pi = (s : WithTop ℝ)) :
    exponentialValueSubgroup v = AddSubgroup.zmultiples s := by
  have hpi0 : pi ≠ 0 :=
    LubinTate.Valuations.discretePrimeElement_ne_zero_of_value v hpival
  ext r
  constructor
  · rintro ⟨x, hx, hr⟩
    obtain ⟨m, hm⟩ := hvalues x hx
    have hre : r = (m : ℝ) * s := by
      rw [hr] at hm
      exact WithTop.coe_eq_coe.mp hm
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨m, ?_⟩
    simpa [zsmul_eq_mul] using hre.symm
  · rw [AddSubgroup.mem_zmultiples_iff]
    rintro ⟨m, rfl⟩
    refine ⟨pi ^ m, zpow_ne_zero m hpi0, ?_⟩
    simpa [zsmul_eq_mul] using
      discretePrimeElement_zpow_value_scaled v hpi0 hpival m

/-- The element of least positive discrete discrete value generates the maximal
ideal of its valuation ring. -/
private theorem maximalIdeal_eq_span_discretePrimeElement
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K)
    {s : ℝ} (hs : 0 < s)
    (hvalues : ∀ x : K, x ≠ 0 → ∃ m : ℤ,
      v x = ((((m : ℝ) * s : ℝ)) : WithTop ℝ))
    {pi : K} (hpival : v pi = (s : WithTop ℝ)) :
    IsLocalRing.maximalIdeal (LubinTate.Valuations.exponentialValuationSubring v) =
      Ideal.span ({LubinTate.Valuations.discretePrimeElementInValuationSubring
        v hs.le hpival} : Set (LubinTate.Valuations.exponentialValuationSubring v)) := by
  let piV := LubinTate.Valuations.discretePrimeElementInValuationSubring v hs.le hpival
  apply le_antisymm
  · intro x hx
    by_cases hx0 : (x : K) = 0
    · have : x = 0 := Subtype.ext hx0
      simp [this]
    · obtain ⟨n, hn⟩ :=
        LubinTate.Valuations.discreteExponentialValuation_subring_exists_nat_value
          hs hvalues hx0
      have hxpos : (0 : WithTop ℝ) < v (x : K) := by
        rw [← LubinTate.Valuations.exponentialMaxIdeal_eq_maximalIdeal v] at hx
        exact hx
      have hn0 : n ≠ 0 := by
        intro hnzero
        subst n
        have hxval0 : v (x : K) = 0 := by simpa using hn
        rw [hxval0] at hxpos
        simp at hxpos
      have hsle : ((s : ℝ) : WithTop ℝ) ≤ v (x : K) := by
        rw [hn]
        exact WithTop.coe_le_coe.mpr (by
          have hnle : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
          nlinarith)
      have hxpow : x ∈ LubinTate.Valuations.uniformizerPowerIdeal piV 1 :=
        (LubinTate.Valuations.discrete_uniformizerPowerIdeal_mem_iff_value_ge
          v hs hpival 1 x).2 (by simpa using hsle)
      simpa [piV, LubinTate.Valuations.uniformizerPowerIdeal] using hxpow
  · rw [Ideal.span_le]
    intro x hx
    have hxpi : x = piV := by simpa [piV] using hx
    subst x
    rw [← LubinTate.Valuations.exponentialMaxIdeal_eq_maximalIdeal v]
    change (0 : WithTop ℝ) < v pi
    rw [hpival]
    exact WithTop.coe_lt_coe.mpr hs

/-- The ideal-theoretic ramification index is exactly the scaling factor
between the least positive generators of the two discrete value groups. -/
private theorem exists_valueGroup_generators_scaled_by_ramificationIdx
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hv : LubinTate.Valuations.DiscreteExponentialValuation v)
    (hw : LubinTate.Valuations.DiscreteExponentialValuation w)
    [IsDiscreteValuationRing (LubinTate.Valuations.exponentialValuationSubring v)]
    [IsDiscreteValuationRing (LubinTate.Valuations.exponentialValuationSubring w)] :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := exponentialValuationRingMap v w hExt
    letI : Algebra V W := i.toAlgebra
    let e := Ideal.ramificationIdx'
      (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W)
    ∃ s t : ℝ, t ≠ 0 ∧
      exponentialValueSubgroup v = AddSubgroup.zmultiples s ∧
      exponentialValueSubgroup w = AddSubgroup.zmultiples t ∧
      s = (e : ℝ) * t := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let e := Ideal.ramificationIdx'
    (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W)
  rcases hv with ⟨s, hs, hvalues, pi, hpival⟩
  rcases hw with ⟨t, ht, hwvalues, Pi, hPival⟩
  let piV := LubinTate.Valuations.discretePrimeElementInValuationSubring v hs.le hpival
  let PiW := LubinTate.Valuations.discretePrimeElementInValuationSubring w ht.le hPival
  have hVspan : IsLocalRing.maximalIdeal V = Ideal.span ({piV} : Set V) :=
    maximalIdeal_eq_span_discretePrimeElement v hs hvalues hpival
  have hWspan : IsLocalRing.maximalIdeal W = Ideal.span ({PiW} : Set W) :=
    maximalIdeal_eq_span_discretePrimeElement w ht hwvalues hPival
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    exact (algebraMap K L).injective (congrArg Subtype.val hab)
  have hmap :=
    ValuationTheory.map_maximalIdeal_eq_pow_ramificationIdx
      (R := V) (S := W) hi
  change Ideal.map i (IsLocalRing.maximalIdeal V) =
    IsLocalRing.maximalIdeal W ^ e at hmap
  have hspan : Ideal.span ({i piV} : Set W) =
      Ideal.span ({PiW ^ e} : Set W) := by
    calc
      Ideal.span ({i piV} : Set W) =
          Ideal.map i (IsLocalRing.maximalIdeal V) := by
        rw [hVspan, Ideal.map_span, Set.image_singleton]
      _ = IsLocalRing.maximalIdeal W ^ e := hmap
      _ = Ideal.span ({PiW} : Set W) ^ e := by rw [hWspan]
      _ = Ideal.span ({PiW ^ e} : Set W) :=
        Ideal.span_singleton_pow PiW e
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have huval : w ((((u : Wˣ) : W) : L)) = 0 :=
    LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit w u.isUnit
  have hfield := congrArg (fun z : W ↦ (z : L)) hu
  have hvalue := congrArg w hfield
  have hscale : s = (e : ℝ) * t := by
    change w (algebraMap K L pi * (((u : Wˣ) : W) : L)) =
      w ((Pi : L) ^ e) at hvalue
    rw [w.map_mul, hExt, hpival, huval, add_zero,
      LubinTate.Valuations.discretePrimeElement_pow_value w hPival] at hvalue
    exact WithTop.coe_eq_coe.mp hvalue
  refine ⟨s, t, ne_of_gt ht,
    exponentialValueSubgroup_eq_zmultiples v hvalues hpival,
    exponentialValueSubgroup_eq_zmultiples w hwvalues hPival,
    hscale⟩

/-- Exact extension embeds the base value group in the target value group. -/
theorem exponentialValueSubgroup_le_of_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    exponentialValueSubgroup v ≤ exponentialValueSubgroup w := by
  rintro r ⟨a, ha, hval⟩
  refine ⟨algebraMap K L a, (map_ne_zero (algebraMap K L)).mpr ha, ?_⟩
  rw [hExt, hval]

/-- The actual quotient `w(Lˣ) / v(Kˣ)` of value groups.  The `comap`
is the base subgroup viewed inside the target subgroup. -/
def ExponentialValueGroupQuotient
    {K L : Type*} [Field K] [Field L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L) :=
  exponentialValueSubgroup w ⧸
    (exponentialValueSubgroup v).comap
      (exponentialValueSubgroup w).subtype

/-- The ramification index as the actual value-group quotient cardinality. -/
def exponentialRamificationIndex
    {K L : Type*} [Field K] [Field L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L) : ℕ :=
  Nat.card (ExponentialValueGroupQuotient v w)

/-- If the target value group is `tℤ` and the base value group is
`(e t)ℤ`, their actual quotient has cardinality `e`. -/
private theorem exponentialRamificationIndex_eq_of_cyclic_valueSubgroups
    {K L : Type*} [Field K] [Field L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    {s t : ℝ} (ht : t ≠ 0) (e : ℕ)
    (hvgroup :
      exponentialValueSubgroup v = AddSubgroup.zmultiples s)
    (hwgroup :
      exponentialValueSubgroup w = AddSubgroup.zmultiples t)
    (hscale : s = (e : ℝ) * t) :
    exponentialRamificationIndex v w = e := by
  let Gamma := exponentialValueSubgroup w
  let H : AddSubgroup Gamma :=
    (exponentialValueSubgroup v).comap
      (exponentialValueSubgroup w).subtype
  let g : Gamma := ⟨t, by
    change t ∈ exponentialValueSubgroup w
    rw [hwgroup]
    exact AddSubgroup.mem_zmultiples t⟩
  let phi : ℤ →+ Gamma := zmultiplesHom Gamma g
  have hphi : Function.Surjective phi := by
    intro z
    have hz : (z : ℝ) ∈ AddSubgroup.zmultiples t := by
      rw [← hwgroup]
      exact z.property
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hz
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa [phi, g] using hn
  have hcomap : H.comap phi = AddSubgroup.zmultiples (e : ℤ) := by
    ext n
    constructor
    · intro hn
      change phi n ∈ H at hn
      change (((phi n : Gamma) : ℝ)) ∈
        exponentialValueSubgroup v at hn
      have hn' : ((n : ℝ) * t) ∈ exponentialValueSubgroup v := by
        simpa [phi, g, zsmul_eq_mul] using hn
      rw [hvgroup, hscale, AddSubgroup.mem_zmultiples_iff] at hn'
      obtain ⟨m, hm⟩ := hn'
      rw [AddSubgroup.mem_zmultiples_iff]
      refine ⟨m, ?_⟩
      have hreal : (m * (e : ℤ) : ℤ) = n := by
        have hcast : (((m * (e : ℤ) : ℤ) : ℝ)) = (n : ℝ) := by
          apply mul_right_cancel₀ ht
          simpa [zsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hm
        exact_mod_cast hcast
      simp [hreal]
    · intro hn
      rw [AddSubgroup.mem_zmultiples_iff] at hn
      obtain ⟨m, rfl⟩ := hn
      change phi (m • (e : ℤ)) ∈ H
      change (((phi (m • (e : ℤ)) : Gamma) : ℝ)) ∈
        exponentialValueSubgroup v
      rw [hvgroup, hscale, AddSubgroup.mem_zmultiples_iff]
      refine ⟨m, ?_⟩
      simp [phi, g, zsmul_eq_mul]
      ring
  change Nat.card (Gamma ⧸ H) = e
  calc
    Nat.card (Gamma ⧸ H) = H.index := rfl
    _ = (H.comap phi).index :=
      (H.index_comap_of_surjective hphi).symm
    _ = (AddSubgroup.zmultiples (e : ℤ)).index := by rw [hcomap]
    _ = Nat.card (ℤ ⧸ AddSubgroup.zmultiples (e : ℤ)) := rfl
    _ = Nat.card (ZMod e) :=
      Nat.card_congr (Int.quotientZMultiplesNatEquivZMod e).toEquiv
    _ = e := Nat.card_zmod e

/-- For discrete source and target valuation rings, the quotient-cardinality
ramification index agrees with mathlib's local Dedekind ramification index. -/
theorem exponentialRamificationIndex_eq_ideal_ramificationIdx
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hv : LubinTate.Valuations.DiscreteExponentialValuation v)
    [IsDiscreteValuationRing (LubinTate.Valuations.exponentialValuationSubring v)]
    [IsDiscreteValuationRing (LubinTate.Valuations.exponentialValuationSubring w)] :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := exponentialValuationRingMap v w hExt
    letI : Algebra V W := i.toAlgebra
    exponentialRamificationIndex v w =
      Ideal.ramificationIdx'
        (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let e := Ideal.ramificationIdx'
    (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W)
  have hw : LubinTate.Valuations.DiscreteExponentialValuation w :=
    discreteExponentialValuation_of_isDiscreteValuationRing w
  obtain ⟨s, t, ht, hvgroup, hwgroup, hscale⟩ :=
    exists_valueGroup_generators_scaled_by_ramificationIdx
      v w hExt hv hw
  exact exponentialRamificationIndex_eq_of_cyclic_valueSubgroups
    v w ht e hvgroup hwgroup hscale

/-- The actual residue degree of an exact valued extension. -/
def exponentialResidueDegree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) : ℕ := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  letI : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  letI : Algebra V W := i.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  exact Module.finrank (IsLocalRing.ResidueField V)
    (IsLocalRing.ResidueField W)

/-- The residue finrank is exactly mathlib's local inertia degree. -/
theorem exponentialResidueDegree_eq_ideal_inertiaDeg
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := exponentialValuationRingMap v w hExt
    letI : IsLocalHom i :=
      exponentialValuationRingMap_isLocalHom v w hExt
    letI : Algebra V W := i.toAlgebra
    exponentialResidueDegree v w hExt =
      (IsLocalRing.maximalIdeal W).inertiaDeg V := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let Amap : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) := Amap
  let : (IsLocalRing.maximalIdeal W).LiesOver
      (IsLocalRing.maximalIdeal V) :=
    ⟨(ValuationTheory.DiscreteValuationField.ResidueField.comap_maximalIdeal_eq i).symm⟩
  change Module.finrank (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) =
    (IsLocalRing.maximalIdeal W).inertiaDeg V
  let Astd : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    Ideal.Quotient.algebraOfLiesOver
      (IsLocalRing.maximalIdeal W) (IsLocalRing.maximalIdeal V)
  have hmap :
      @algebraMap (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) _ _ Amap =
        @algebraMap (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) _ _ Astd := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hAlg : Amap = Astd := by
    apply Algebra.algebra_ext
    intro r
    exact DFunLike.congr_fun hmap r
  have hfin :
      @Module.finrank (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) _ _
          (@Algebra.toModule _ _ _ _ Amap) =
        @Module.finrank (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) _ _
          (@Algebra.toModule _ _ _ _ Astd) := by
    rw [hAlg]
  have h := (Ideal.inertiaDeg_eq_of_isMaximal
    (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W)).symm
  exact h

/-- The canonical multiplicative presentation `exp (-v(x))` of an exponential
exponential valuation. -/
noncomputable def exponentialAssociatedAbsoluteValue
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K) :
    AbsoluteValue K ℝ := by
  classical
  refine
    { toFun := fun x ↦ if x = 0 then 0 else Real.exp (-(v x).untop₀)
      map_mul' := ?_
      nonneg' := ?_
      eq_zero' := ?_
      add_le' := ?_ }
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    have hreal : (v (x * y)).untop₀ =
        (v x).untop₀ + (v y).untop₀ := by
      apply WithTop.coe_eq_coe.mp
      rw [WithTop.coe_add,
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hxy),
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx),
        WithTop.coe_untop₀_of_ne_top
          (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hy)]
      exact v.map_mul x y
    simp only [hx, hy, hxy, ite_false]
    rw [hreal, neg_add, Real.exp_add]
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, Real.exp_nonneg]
  · intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, Real.exp_ne_zero]
  · intro x y
    by_cases hx : x = 0
    · subst x
      simp
    by_cases hy : y = 0
    · subst y
      simp
    by_cases hxy : x + y = 0
    · simp only [hx, hy, hxy, ite_false, ite_true]
      positivity
    let r := (v x).untop₀
    let s := (v y).untop₀
    let t := (v (x + y)).untop₀
    have hvr : v x = (r : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx)).symm
    have hvs : v y = (s : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hy)).symm
    have hvt : v (x + y) = (t : WithTop ℝ) :=
      (WithTop.coe_untop₀_of_ne_top
        (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hxy)).symm
    have hmin : min r s ≤ t := by
      have h := v.add_le_min x y
      rw [hvr, hvs, hvt] at h
      exact WithTop.coe_le_coe.mp (by simpa only [WithTop.coe_min] using h)
    have hmain : Real.exp (-t) ≤ Real.exp (-r) + Real.exp (-s) := by
      refine (Real.exp_le_exp.mpr (neg_le_neg hmin)).trans ?_
      by_cases hrs : r ≤ s
      · rw [min_eq_left hrs]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [min_eq_right (le_of_not_ge hrs)]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)
    simpa only [hx, hy, hxy, ite_false, r, s, t] using hmain

/-- The canonical multiplicative presentation is associated to `v`, with
the fixed base `e = exp 1`. -/
theorem exponentialAssociatedAbsoluteValue_associated
    {K : Type*} [Field K] (v : LubinTate.Valuations.ExponentialValuation K) :
    LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1)
      (exponentialAssociatedAbsoluteValue v) := by
  refine ⟨Real.one_lt_exp_iff.mpr zero_lt_one, ?_⟩
  intro x hx
  refine ⟨(v x).untop₀, ?_, ?_⟩
  · exact (WithTop.coe_untop₀_of_ne_top
      (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hx)).symm
  · simp [exponentialAssociatedAbsoluteValue, hx, Real.exp_one_rpow]

/-- An absolute value associated to a exponential valuation is
nonarchimedean; the strong triangle inequality is the exponential
ultrametric inequality transported through the decreasing map
`r ↦ q ^ (-r)`. -/
theorem associatedAbsoluteValue_nonarchimedean
    {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) (q : ℝ)
    (abv : AbsoluteValue K ℝ)
    (hassoc : LubinTate.Valuations.AssociatedAbsoluteValue v q abv) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue abv := by
  apply LubinTate.Valuations.nonarchimedean_of_strong_triangle
  intro x y
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  by_cases hxy : x + y = 0
  · simp [hxy]
  obtain ⟨r, hvr, habvr⟩ := hassoc.2 x hx
  obtain ⟨s, hvs, habvs⟩ := hassoc.2 y hy
  obtain ⟨t, hvt, habvt⟩ := hassoc.2 (x + y) hxy
  have hmin : min r s ≤ t := by
    have h := v.add_le_min x y
    rw [hvr, hvs, hvt] at h
    exact WithTop.coe_le_coe.mp (by simpa only [WithTop.coe_min] using h)
  rw [habvr, habvs, habvt]
  have hpow : q ^ (-t) ≤ q ^ (-(min r s)) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hassoc.1)
      (neg_le_neg hmin)
  refine hpow.trans ?_
  by_cases hrs : r ≤ s
  · rw [min_eq_left hrs]
    exact le_max_left _ _
  · have hsr : s ≤ r := le_of_not_ge hrs
    rw [min_eq_right hsr]
    exact le_max_right _ _

/-- Associated additive and multiplicative presentations have the same
valuation subring. -/
theorem associatedAbsoluteValue_valuationSubring_eq
    {K : Type*} [Field K]
    (v : LubinTate.Valuations.ExponentialValuation K) (q : ℝ)
    (abv : AbsoluteValue K ℝ)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue abv)
    (hassoc : LubinTate.Valuations.AssociatedAbsoluteValue v q abv) :
    LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v =
      absoluteValueValuationSubring abv hnonarch := by
  ext x
  rw [LubinTate.Valuations.mem_exponentialValuationSubringAsValuationSubring_iff,
    mem_absoluteValueValuationSubring_iff]
  by_cases hx : x = 0
  · subst x
    simp [(v.eq_top_iff 0).mpr rfl]
  · exact (LubinTate.Valuations.associatedAbsoluteValue_le_one_iff hassoc hx).symm

/-- Exact extension of associated exponential valuations gives exact
extension of the associated absolute values. -/
theorem associatedAbsoluteValue_extends
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (q : ℝ) (av : AbsoluteValue K ℝ) (aw : AbsoluteValue L ℝ)
    (hav : LubinTate.Valuations.AssociatedAbsoluteValue v q av)
    (haw : LubinTate.Valuations.AssociatedAbsoluteValue w q aw) :
    ∀ a : K, aw (algebraMap K L a) = av a := by
  intro a
  by_cases ha : a = 0
  · subst a
    simp
  · have hma : algebraMap K L a ≠ 0 :=
      (map_ne_zero (algebraMap K L)).mpr ha
    obtain ⟨r, hvr, havr⟩ := hav.2 a ha
    obtain ⟨s, hws, haws⟩ := haw.2 (algebraMap K L a) hma
    have hrs : r = s := by
      rw [hExt, hvr] at hws
      exact WithTop.coe_eq_coe.mp hws
    rw [havr, haws, hrs]

/-- A literal equality with the integral-closure subring produces the
corresponding `IsIntegralClosure` instance. -/
private theorem isIntegralClosure_of_subring_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (V : Subring K) (W : Subring L)
    [Algebra V L]
    (h : W = (integralClosure V L).toSubring) :
    IsIntegralClosure W V L := by
  refine
    { algebraMap_injective := by
        exact W.subtype_injective
      isIntegral_iff := ?_ }
  intro x
  constructor
  · intro hx
    have hxW : x ∈ W := by
      rw [h]
      exact hx
    exact ⟨⟨x, hxW⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    change (y : L) ∈ (integralClosure V L).toSubring
    rw [← h]
    exact y.property

/-- the finite norm-formula theorem applied directly to the exponential presentation: a chosen
extension of a Henselian valuation has valuation ring equal to the actual
integral closure. The required multiplicative presentations are constructed
internally. -/
theorem exponentialValuationSubring_eq_integralClosure_of_henselian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w).toSubring =
      (integralClosure
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v) L).toSubring := by
  let av := exponentialAssociatedAbsoluteValue v
  let aw := exponentialAssociatedAbsoluteValue w
  have hav : LubinTate.Valuations.AssociatedAbsoluteValue v (Real.exp 1) av :=
    exponentialAssociatedAbsoluteValue_associated v
  have haw : LubinTate.Valuations.AssociatedAbsoluteValue w (Real.exp 1) aw :=
    exponentialAssociatedAbsoluteValue_associated w
  have havNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue av :=
    associatedAbsoluteValue_nonarchimedean v (Real.exp 1) av hav
  have hawNonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue aw :=
    associatedAbsoluteValue_nonarchimedean w (Real.exp 1) aw haw
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let Va := absoluteValueValuationSubring av havNonarch
  let Wa := absoluteValueValuationSubring aw hawNonarch
  have hV : Vv = Va :=
    associatedAbsoluteValue_valuationSubring_eq
      v (Real.exp 1) av havNonarch hav
  have hW : Wv = Wa :=
    associatedAbsoluteValue_valuationSubring_eq
      w (Real.exp 1) aw hawNonarch haw
  have hhensA : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization Va.valuation := by
    rw [← hV]
    exact hhens
  have habsExt : ∀ a : K, aw (algebraMap K L a) = av a :=
    associatedAbsoluteValue_extends
      v w hExt (Real.exp 1) av aw hav haw
  have hWaExt : Va.valuation.HasExtension Wa.valuation :=
    absoluteValueValuation_hasExtension_of_extends
      av aw havNonarch hawNonarch habsExt
  let : Va.valuation.HasExtension Wa.valuation := hWaExt
  obtain ⟨B, hB, _hBuniq⟩ :=
    normFormula_algebraic_extension (K := K) (L := L)
      av havNonarch hhensA
  obtain ⟨C, hC, hCuniq⟩ :=
    henselianUniqueExtension_unique_algebraic_valuationSubring_extension_of_henselian
      (K := K) (L := L) av havNonarch hhensA
  have hWaC : Wa = C := hCuniq Wa hWaExt
  have hBC : B = C := hCuniq B hB.1
  have hWaB : Wa = B := hWaC.trans hBC.symm
  calc
    Wv.toSubring = Wa.toSubring := congrArg ValuationSubring.toSubring hW
    _ = B.toSubring := congrArg ValuationSubring.toSubring hWaB
    _ = (integralClosure Va L).toSubring := hB.2
    _ = (integralClosure Vv L).toSubring := by rw [hV]

/-- The value-coset class of a nonzero target-field element. -/
def exponentialValueCoset
    {K L : Type*} [Field K] [Field L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (x : L) (hx : x ≠ 0) : ExponentialValueGroupQuotient v w :=
  QuotientAddGroup.mk ⟨(w x).untop₀, ⟨x, hx,
    (WithTop.coe_untop₀_of_ne_top
      (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w hx)).symm⟩⟩

/-- Every class in the actual value-group quotient is represented by the
value of a nonzero element of the target field. -/
private theorem exponentialValueCoset_units_surjective
    {K L : Type*} [Field K] [Field L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L) :
    Function.Surjective
      (fun x : Lˣ ↦ exponentialValueCoset v w (x : L) x.ne_zero) := by
  intro q
  obtain ⟨gamma, hgamma⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x, hx, hvalue⟩ := gamma.property
  refine ⟨Units.mk0 x hx, ?_⟩
  rw [← hgamma]
  unfold exponentialValueCoset
  apply congrArg QuotientAddGroup.mk
  apply Subtype.ext
  simp [hvalue]

/-- Equality after cross-multiplying by nonzero base elements forces equality
of the corresponding value-group quotient classes. -/
theorem exponentialValueCoset_eq_of_cross_value_eq
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0)
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcross :
      w (algebraMap K L a * x) = w (algebraMap K L b * y)) :
    exponentialValueCoset v w x hx = exponentialValueCoset v w y hy := by
  have hvaTop : v a ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v ha
  have hvbTop : v b ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero v hb
  have hxTop : w x ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w hx
  have hyTop : w y ≠ ⊤ :=
    LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w hy
  have hva : v a = (((v a).untop₀ : ℝ) : WithTop ℝ) :=
    (WithTop.coe_untop₀_of_ne_top hvaTop).symm
  have hvb : v b = (((v b).untop₀ : ℝ) : WithTop ℝ) :=
    (WithTop.coe_untop₀_of_ne_top hvbTop).symm
  have hvx : w x = (((w x).untop₀ : ℝ) : WithTop ℝ) :=
    (WithTop.coe_untop₀_of_ne_top hxTop).symm
  have hvy : w y = (((w y).untop₀ : ℝ) : WithTop ℝ) :=
    (WithTop.coe_untop₀_of_ne_top hyTop).symm
  have hreal :
      (v a).untop₀ + (w x).untop₀ =
        (v b).untop₀ + (w y).untop₀ := by
    rw [w.map_mul, w.map_mul, hExt, hExt, hva, hvb, hvx, hvy] at hcross
    exact WithTop.coe_eq_coe.mp (by simpa [WithTop.coe_add] using hcross)
  let gammaX : exponentialValueSubgroup w :=
    ⟨(w x).untop₀, ⟨x, hx, hvx⟩⟩
  let gammaY : exponentialValueSubgroup w :=
    ⟨(w y).untop₀, ⟨y, hy, hvy⟩⟩
  change QuotientAddGroup.mk gammaX = QuotientAddGroup.mk gammaY
  rw [QuotientAddGroup.eq_iff_sub_mem]
  change (w x).untop₀ - (w y).untop₀ ∈
    exponentialValueSubgroup v
  refine ⟨b / a, div_ne_zero hb ha, ?_⟩
  rw [div_eq_mul_inv, v.map_mul,
    LubinTate.Valuations.exponentialValuation_inv_value v ha hva, hvb]
  apply congrArg (fun z : ℝ ↦ (z : WithTop ℝ))
  linarith

/-- A family in `Lˣ` represents distinct cosets modulo the values coming
from `Kˣ` exactly in the cross-multiplication form used in the proof.
This definition avoids choosing subtraction representatives in `WithTop ℝ`. -/
def DistinctExponentialValueCosetRepresentatives
    {K L I : Type*} [Field K] [Field L] [Algebra K L]
    (_v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L) (pi : I → L) : Prop :=
  (∀ i, pi i ≠ 0) ∧
    Pairwise fun i j ↦
      ∀ a b : K, a ≠ 0 → b ≠ 0 →
        w (algebraMap K L a * pi i) ≠
          w (algebraMap K L b * pi j)

/-- Injectivity of the actual value-coset map supplies the pairwise
distinctness condition used by the constructive proof. -/
theorem distinctExponentialValueCosetRepresentatives_of_injective
    {K L I : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (pi : I → L) (hpi0 : ∀ i, pi i ≠ 0)
    (hinj : Function.Injective
      (fun i ↦ exponentialValueCoset v w (pi i) (hpi0 i))) :
    DistinctExponentialValueCosetRepresentatives v w pi := by
  refine ⟨hpi0, ?_⟩
  intro i j hij a b ha hb hcross
  apply hij
  apply hinj
  exact exponentialValueCoset_eq_of_cross_value_eq
    v w hExt (hpi0 i) (hpi0 j) ha hb hcross

/-- The constructive core of the fundamental inequality.  Distinct value-coset
representatives multiplied by linearly independent residue lifts form a
linearly independent family over the base field.  Repeated roots or a degree
formula are not built into the statement: this is the actual
linear-independence argument. -/
theorem ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent
    {K L I J : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype I] [Fintype J]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (pi : I → L) (hpi : DistinctExponentialValueCosetRepresentatives v w pi)
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := exponentialValuationRingMap v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : IsLocalHom i :=
        exponentialValuationRingMap_isLocalHom v w hExt
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      LinearIndependent (IsLocalRing.ResidueField V)
        (fun j ↦ IsLocalRing.residue W (omega j))) :
    LinearIndependent K
      (fun p : I × J ↦ (omega p.2 : L) * pi p.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a hsum p
  let s : I → L := fun i ↦
    ∑ j, algebraMap K L (a (i, j)) * (omega j : L)
  have hsum' : ∑ i, s i * pi i = 0 := by
    simpa only [s, Fintype.sum_prod_type, Algebra.smul_def,
      Finset.sum_mul, mul_assoc] using hsum
  by_contra hap
  have hinner : ∀ i, s i ≠ 0 →
      ∃ a₀ : K, a₀ ≠ 0 ∧
        w (s i) = w (algebraMap K L a₀) := by
    intro i hsi
    have hai : ∃ j, a (i, j) ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hsi
      simp [s, hnone]
    exact exponentialValuation_residueCombination_value_in_base
      v w hExt omega homega (fun j ↦ a (i, j)) hai
  have hpvalue :=
    exponentialValuation_residueCombination_value_in_base
      v w hExt omega homega (fun j ↦ a (p.1, j)) ⟨p.2, hap⟩
  change ∃ a₀ : K, a₀ ≠ 0 ∧
      w (s p.1) = w (algebraMap K L a₀) at hpvalue
  obtain ⟨ap, hapzero, hpvalue⟩ := hpvalue
  have hsp : s p.1 ≠ 0 := by
    intro hzero
    rw [hzero, (w.eq_top_iff 0).mpr rfl] at hpvalue
    exact (LubinTate.Valuations.exponentialValuation_ne_top_of_ne_zero w
      ((map_ne_zero (algebraMap K L)).mpr hapzero)) hpvalue.symm
  have hsum_ne : ∑ i, s i * pi i ≠ 0 := by
    apply exponentialValuation_finset_sum_ne_zero_of_value_ne
      w Finset.univ (fun i ↦ s i * pi i)
    · exact ⟨p.1, Finset.mem_univ _, mul_ne_zero hsp (hpi.1 p.1)⟩
    · intro i hi j hj hij hterm_i hterm_j
      have hsi : s i ≠ 0 := by
        intro hzero
        exact hterm_i (by simp [hzero])
      have hsj : s j ≠ 0 := by
        intro hzero
        exact hterm_j (by simp [hzero])
      obtain ⟨ai, hai, hvi⟩ := hinner i hsi
      obtain ⟨aj, haj, hvj⟩ := hinner j hsj
      have hwi :
          w (s i * pi i) = w (algebraMap K L ai * pi i) := by
        rw [w.map_mul, w.map_mul, hvi]
      have hwj :
          w (s j * pi j) = w (algebraMap K L aj * pi j) := by
        rw [w.map_mul, w.map_mul, hvj]
      intro heq
      exact (hpi.2 hij ai aj hai haj)
        (hwi.symm.trans (heq.trans hwj))
  exact hsum_ne hsum'

/-- The linearly-independent product family does not require the two
indexing sets to have been proved finite in advance.  Every finite part is
contained in a product of finite parts, to which the preceding constructive
argument applies. -/
theorem ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent_arbitrary
    {K L I J : Type*} [Field K] [Field L] [Algebra K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (pi : I → L) (hpi : DistinctExponentialValueCosetRepresentatives v w pi)
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := exponentialValuationRingMap v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : IsLocalHom i :=
        exponentialValuationRingMap_isLocalHom v w hExt
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      LinearIndependent (IsLocalRing.ResidueField V)
        (fun j ↦ IsLocalRing.residue W (omega j))) :
    LinearIndependent K
      (fun p : I × J ↦ (omega p.2 : L) * pi p.1) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let sI : Finset I := s.image Prod.fst
  let sJ : Finset J := s.image Prod.snd
  let piI : sI → L := fun i ↦ pi i
  let omegaJ : sJ → LubinTate.Valuations.exponentialValuationSubring w := fun j ↦ omega j
  have hpiI : DistinctExponentialValueCosetRepresentatives v w piI := by
    refine ⟨fun i ↦ hpi.1 i, ?_⟩
    intro i j hij
    apply hpi.2
    intro h
    apply hij
    exact Subtype.ext h
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  let : Algebra V W := i.toAlgebra
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  have homegaJ : LinearIndependent (IsLocalRing.ResidueField V)
      (fun j : sJ ↦ IsLocalRing.residue W (omegaJ j)) := by
    exact homega.comp Subtype.val Subtype.val_injective
  have hprod : LinearIndependent K
      (fun p : sI × sJ ↦ (omegaJ p.2 : L) * piI p.1) :=
    ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent
      v w hExt piI hpiI omegaJ homegaJ
  let emb : s → sI × sJ := fun p ↦
    (⟨p.1.1, Finset.mem_image.mpr ⟨p, p.2, rfl⟩⟩,
      ⟨p.1.2, Finset.mem_image.mpr ⟨p, p.2, rfl⟩⟩)
  have hemb : Function.Injective emb := by
    intro p q hpq
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z ↦ (z.1 : I)) hpq)
      (congrArg (fun z ↦ (z.2 : J)) hpq)
  change LinearIndependent K
    ((fun p : sI × sJ ↦ (omegaJ p.2 : L) * piI p.1) ∘ emb)
  exact hprod.comp emb hemb

/-- Fundamental inequality in constructive cardinal form.  Thus any complete
set of `e` value-coset representatives and any residue basis of size `f`
give `e f ≤ [L : K]`; no extension record carrying a pre-assumed degree
formula is used. -/
theorem ramificationInvariants_valueCosets_mul_residueLifts_card_le_finrank
    {K L I J : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Fintype I] [Fintype J]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (pi : I → L) (hpi : DistinctExponentialValueCosetRepresentatives v w pi)
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := exponentialValuationRingMap v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : IsLocalHom i :=
        exponentialValuationRingMap_isLocalHom v w hExt
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      LinearIndependent (IsLocalRing.ResidueField V)
        (fun j ↦ IsLocalRing.residue W (omega j))) :
    Fintype.card I * Fintype.card J ≤ Module.finrank K L := by
  have hli :=
    ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent
      v w hExt pi hpi omega homega
  simpa using hli.fintype_card_le_finrank

/-- Fundamental inequality with the ramification index identified as the
cardinality of the actual quotient `w(Lˣ)/v(Kˣ)`. -/
theorem ramificationInvariants_actual_valueGroup_card_mul_residueLifts_card_le_finrank
    {K L I J : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Fintype I] [Fintype J]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (pi : I → L) (hpi0 : ∀ i, pi i ≠ 0)
    (hpi : Function.Bijective
      (fun i ↦ exponentialValueCoset v w (pi i) (hpi0 i)))
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (homega :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := exponentialValuationRingMap v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : IsLocalHom i :=
        exponentialValuationRingMap_isLocalHom v w hExt
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      LinearIndependent (IsLocalRing.ResidueField V)
        (fun j ↦ IsLocalRing.residue W (omega j))) :
    exponentialRamificationIndex v w * Fintype.card J ≤ Module.finrank K L := by
  have hdistinct :=
    distinctExponentialValueCosetRepresentatives_of_injective
      v w hExt pi hpi0 hpi.1
  have hle :=
    ramificationInvariants_valueCosets_mul_residueLifts_card_le_finrank
      v w hExt pi hdistinct omega homega
  have he : exponentialRamificationIndex v w = Fintype.card I := by
    rw [exponentialRamificationIndex]
    calc
      Nat.card (ExponentialValueGroupQuotient v w) = Nat.card I :=
        Nat.card_congr (Equiv.ofBijective
          (fun i ↦ exponentialValueCoset v w (pi i) (hpi0 i)) hpi).symm
      _ = Fintype.card I := Nat.card_eq_fintype_card
  rwa [he]

/-- the fundamental inequality, general fundamental inequality with both invariants
identified literally: `e` is the cardinality of `w(Lˣ)/v(Kˣ)` and `f` is
the residue-field finrank.  The supplied `pi` and `omega` are genuine complete
systems of value-coset representatives and residue-basis lifts. -/
theorem ramificationInvariants_fundamental_inequality_of_representatives
    {K L I J : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Fintype I] [Fintype J]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (pi : I → L) (hpi0 : ∀ i, pi i ≠ 0)
    (hpi : Function.Bijective
      (fun i ↦ exponentialValueCoset v w (pi i) (hpi0 i)))
    (omega : J → LubinTate.Valuations.exponentialValuationSubring w)
    (beta :
      let V := LubinTate.Valuations.exponentialValuationSubring v
      let W := LubinTate.Valuations.exponentialValuationSubring w
      let i := exponentialValuationRingMap v w hExt
      letI : Algebra V W := i.toAlgebra
      letI : IsLocalHom i :=
        exponentialValuationRingMap_isLocalHom v w hExt
      letI : Algebra (IsLocalRing.ResidueField V)
          (IsLocalRing.ResidueField W) :=
        (IsLocalRing.ResidueField.map i).toAlgebra
      Basis J (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField W))
    (homega :
      let W := LubinTate.Valuations.exponentialValuationSubring w
      ∀ j, IsLocalRing.residue W (omega j) = beta j) :
    exponentialRamificationIndex v w * exponentialResidueDegree v w hExt ≤
      Module.finrank K L := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let : Algebra (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) :=
    (IsLocalRing.ResidueField.map i).toAlgebra
  have homegaLI : LinearIndependent (IsLocalRing.ResidueField V)
      (fun j ↦ IsLocalRing.residue W (omega j)) := by
    rw [show (fun j ↦ IsLocalRing.residue W (omega j)) = beta from
      funext homega]
    exact beta.linearIndependent
  have hle :=
    ramificationInvariants_actual_valueGroup_card_mul_residueLifts_card_le_finrank
      v w hExt pi hpi0 hpi omega homegaLI
  have hf : exponentialResidueDegree v w hExt = Fintype.card J := by
    change Module.finrank (IsLocalRing.ResidueField V)
      (IsLocalRing.ResidueField W) = Fintype.card J
    exact Module.finrank_eq_card_basis beta
  rwa [hf]

/-- The fundamental inequality in its explicit form.  The value
coset representatives and the residue-basis lifts are chosen internally.
Their indexing sets are proved finite from the product family's linear
independence, rather than assumed finite at the theorem boundary. -/
theorem ramificationInvariants_fundamental_inequality
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    exponentialRamificationIndex v w * exponentialResidueDegree v w hExt ≤
      Module.finrank K L := by
  classical
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra

  let Q := ExponentialValueGroupQuotient v w
  have hsur : Function.Surjective
      (fun x : Lˣ ↦ exponentialValueCoset v w (x : L) x.ne_zero) :=
    exponentialValueCoset_units_surjective v w
  let sigma : Q → Lˣ := fun q ↦ Classical.choose (hsur q)
  let pi : Q → L := fun q ↦ (sigma q : L)
  have hpi0 : ∀ q, pi q ≠ 0 := fun q ↦ (sigma q).ne_zero
  have hpiClass : ∀ q,
      exponentialValueCoset v w (pi q) (hpi0 q) = q := by
    intro q
    exact Classical.choose_spec (hsur q)
  have hpiBij : Function.Bijective
      (fun q ↦ exponentialValueCoset v w (pi q) (hpi0 q)) := by
    constructor
    · intro q r hqr
      simpa only [hpiClass] using hqr
    · intro q
      exact ⟨q, hpiClass q⟩
  have hpiDistinct : DistinctExponentialValueCosetRepresentatives v w pi :=
    distinctExponentialValueCosetRepresentatives_of_injective
      v w hExt pi hpi0 hpiBij.1
  have honeLI : LinearIndependent k
      (fun _ : Unit ↦ IsLocalRing.residue W (1 : W)) := by
    rw [linearIndependent_unique_iff]
    simp
  have hprodQ :=
    ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent_arbitrary
      v w hExt pi hpiDistinct (fun _ : Unit ↦ (1 : W)) honeLI
  have hfiniteQ : Finite Q :=
    (hprodQ.comp (fun q ↦ (q, ())) (by
      intro q r hqr
      exact congrArg Prod.fst hqr)).finite
  let : Finite Q := hfiniteQ
  let : Fintype Q := Fintype.ofFinite Q

  let J := Module.Free.ChooseBasisIndex k ell
  let beta : Basis J k ell := Module.Free.chooseBasis k ell
  let omega : J → W := fun j ↦
    Classical.choose (IsLocalRing.residue_surjective (beta j))
  have homega : ∀ j, IsLocalRing.residue W (omega j) = beta j := by
    intro j
    exact Classical.choose_spec (IsLocalRing.residue_surjective (beta j))
  have homegaLI : LinearIndependent k
      (fun j ↦ IsLocalRing.residue W (omega j)) := by
    rw [show (fun j ↦ IsLocalRing.residue W (omega j)) = beta from
      funext homega]
    exact beta.linearIndependent
  let piOne : Unit → L := fun _ ↦ 1
  have hpiOne : DistinctExponentialValueCosetRepresentatives v w piOne := by
    refine ⟨by intro; simp [piOne], ?_⟩
    intro a b hab
    exact (hab (Subsingleton.elim a b)).elim
  have hprodJ :=
    ramificationInvariants_valueCosets_mul_residueLifts_linearIndependent_arbitrary
      v w hExt piOne hpiOne omega homegaLI
  have hfiniteJ : Finite J :=
    (hprodJ.comp (fun j ↦ ((), j)) (by
      intro a b hab
      exact congrArg Prod.snd hab)).finite
  let : Finite J := hfiniteJ
  let : Fintype J := Fintype.ofFinite J

  exact ramificationInvariants_fundamental_inequality_of_representatives
    v w hExt pi hpi0 hpiBij omega beta homega

/-- the fundamental inequality, equality case.  For a finite separable extension of a
Henselian discretely valued field, the chosen extension valuation ring is
first identified with the actual integral closure by the norm-formula and
unique-extension theorems.
Its DVR structure and module-finiteness are then derived, so the local
Dedekind identity gives `[L : K] = e f` for the actual value-group and residue
invariants.  No completeness hypothesis is used. -/
theorem ramificationInvariants_fundamental_identity_of_discrete_of_separable
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hvdisc : LubinTate.Valuations.DiscreteExponentialValuation v)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    Module.finrank K L =
      exponentialRamificationIndex v w * exponentialResidueDegree v w hExt := by
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := exponentialValuationRingMap v w hExt
  let : IsLocalHom i :=
    exponentialValuationRingMap_isLocalHom v w hExt
  let algVW : Algebra V W := i.toAlgebra
  let : Algebra V W := algVW
  let : SMul V W := algVW.toSMul
  let algVL : Algebra V L := ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : SMul W L := (inferInstance : Algebra W L).toSMul
  let : SMul V K := (inferInstance : Algebra V K).toSMul
  let : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := W) (A := L) (by
      intro x
      rfl)
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by
      intro x
      rfl)
  have hclosure : Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      v w hExt hhens
  have hclosureSubring : W = (integralClosure V L).toSubring := by
    change W = (integralClosure V L).toSubring at hclosure
    exact hclosure
  let : IsIntegralClosure W V L :=
    isIntegralClosure_of_subring_eq V W hclosureSubring
  let : IsDiscreteValuationRing V :=
    LubinTate.Valuations.discreteExponentialValuationSubring_isDiscreteValuationRing hvdisc
  let : IsFractionRing V K := by
    change IsFractionRing Vv K
    have hfr : IsFractionRing Vv.valuation.valuationSubring K :=
      (Valuation.valuationSubring.integers
        (v := Vv.valuation)).isFractionRing
    rw [Vv.valuationSubring_valuation] at hfr
    exact hfr
  let : IsFractionRing W L := by
    change IsFractionRing Wv L
    have hfr : IsFractionRing Wv.valuation.valuationSubring L :=
      (Valuation.valuationSubring.integers
        (v := Wv.valuation)).isFractionRing
    rw [Wv.valuationSubring_valuation] at hfr
    exact hfr
  let : IsDedekindDomain V := inferInstance
  let : Module.Finite V W := IsIntegralClosure.finite V K L W
  let : IsDedekindDomain W :=
    IsIntegralClosure.isDedekindDomain V K L W
  have hWnotField : ¬ IsField W := by
    intro hfield
    let : Field W := hfield.toField
    obtain ⟨s, hs, _hvalues, pi, hpival⟩ := hvdisc
    have hpi0 : pi ≠ 0 :=
      LubinTate.Valuations.discretePrimeElement_ne_zero_of_value v hpival
    let piV : V :=
      LubinTate.Valuations.discretePrimeElementInValuationSubring v hs.le hpival
    have hpiV0 : piV ≠ 0 := by
      intro hzero
      exact hpi0 (congrArg Subtype.val hzero)
    have hi : Function.Injective i := by
      intro a b hab
      apply Subtype.ext
      exact (algebraMap K L).injective (congrArg Subtype.val hab)
    have hiPi0 : i piV ≠ 0 := by
      simpa using hi.ne hpiV0
    have hiPiUnit : IsUnit (i piV) := isUnit_iff_ne_zero.mpr hiPi0
    have hzero :=
      LubinTate.Valuations.exponentialValuation_eq_zero_of_isUnit w hiPiUnit
    have hvalue : w ((((i piV : W)) : L)) = (s : WithTop ℝ) := by
      change w (algebraMap K L pi) = (s : WithTop ℝ)
      rw [hExt, hpival]
    rw [hvalue] at hzero
    have hs0 : s = 0 :=
      WithTop.coe_eq_coe.mp (by simpa using hzero)
    exact (ne_of_gt hs) hs0
  let : IsNoetherianRing W := inferInstance
  let : IsDiscreteValuationRing W :=
    ((IsDiscreteValuationRing.TFAE W hWnotField).out 3 1).mp
      (show IsDedekindDomain W from inferInstance)
  have hideal :
      Ideal.ramificationIdx'
          (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) *
        (IsLocalRing.maximalIdeal W).inertiaDeg V = Module.finrank K L := by
    classical
    have := FaithfulSMul.of_field_isFractionRing V W K L
    have hp := IsDiscreteValuationRing.not_a_field V
    have hprimes := IsLocalRing.primesOver_eq (A := W) hp
    have hq (q : (IsLocalRing.maximalIdeal V).primesOver W) :
        (q : Ideal W) = IsLocalRing.maximalIdeal W :=
      Set.mem_singleton_iff.mp (hprimes ▸ q.property)
    let : Unique ((IsLocalRing.maximalIdeal V).primesOver W) :=
      { default :=
          ⟨IsLocalRing.maximalIdeal W, hprimes ▸ Set.mem_singleton _⟩
        uniq := fun q =>
          Subtype.ext (Set.mem_singleton_iff.mp (hprimes ▸ q.property)) }
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp,
      IsFractionRing.finrank_eq V K W L]
    simpa only [show algebraMap V W = i from rfl, Fintype.sum_unique, hq] using
      (Ideal.sum_ramification_inertia_eq_finrank
        (IsLocalRing.maximalIdeal V) W)
  rw [exponentialRamificationIndex_eq_ideal_ramificationIdx v w hExt hvdisc,
    exponentialResidueDegree_eq_ideal_inertiaDeg v w hExt]
  exact hideal.symm

end Valuations
end AlgebraicNumberTheory

end
