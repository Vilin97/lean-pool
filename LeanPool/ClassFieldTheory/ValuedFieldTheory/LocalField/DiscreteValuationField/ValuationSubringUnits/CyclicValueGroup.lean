/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import Mathlib.Algebra.Order.Group.Cyclic
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.Data.Int.WithZero
public import Mathlib.RingTheory.Valuation.Archimedean
public import Mathlib.RingTheory.Valuation.RankOne
/-!
# Cyclic value groups and normalized uniformizers

This file supplies the ordered-group and rank-one facts used for actual
multiplicative valuation ranges, together with normalized uniformizer results
for `ℤᵐ⁰`-valued valuations.
-/

@[expose] public section

noncomputable
section

universe u x

open WithZero
open scoped NNReal Valued WithZero

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace WithZeroValuation

variable {R : Type u}
variable {Gamma : Type x} [LinearOrderedCommGroupWithZero Gamma]

/-- A nontrivial `ℤᵐ⁰`-valued valuation is rank one via the standard strictly
monotone embedding `ℤᵐ⁰ -> ℝ≥0`.  This is kept as an explicit definition, not
a global instance, so later finite-dimensional closedness arguments can opt in
without changing typeclass search everywhere. -/
@[implicit_reducible]
noncomputable def rankOne
    [Ring R]
    (v : _root_.Valuation R ℤᵐ⁰) [v.IsNontrivial] : v.RankOne where
  hom' :=
    (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
      MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' :=
    (WithZeroMulInt.toNNReal_strictMono
      (by norm_num : (1 : ℝ≥0) < 2)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial :=
    _root_.Valuation.IsNontrivial.exists_val_nontrivial (v := v)

/-- A cyclic linearly ordered commutative group is multiplicatively
Archimedean.  Mathlib supplies the valuation-theoretic equivalence
`RankOne <-> MulArchimedean`; this lemma supplies the missing ordered-group
input for actual valuation ranges whose unit group has already been proved
cyclic. -/
theorem isCyclic_mulArchimedean
    (G : Type*) [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
    [IsCyclic G] :
    MulArchimedean G := by
  classical
  by_cases hsub : Subsingleton G
  · refine ⟨fun _ y hy => ?_⟩
    exact (hy.ne' (Subsingleton.elim y 1)).elim
  have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
  let a : G := LinearOrderedCommGroup.Subgroup.genLTOne (⊤ : Subgroup G)
  let b : G := a⁻¹
  have hb : 1 < b := by
    have ha : a < 1 := by
      simpa [a] using
      LinearOrderedCommGroup.Subgroup.genLTOne_lt_one (⊤ : Subgroup G)
    simpa [b] using (one_lt_inv'.2 ha)
  have hbtop : Subgroup.zpowers b = (⊤ : Subgroup G) := by
    have hatop : Subgroup.zpowers a = (⊤ : Subgroup G) := by
      simp [a]
    simpa [b, Subgroup.zpowers_inv] using hatop
  refine ⟨fun x y hy => ?_⟩
  have hxmem : x ∈ Subgroup.zpowers b := by
    rw [hbtop]
    trivial
  have hymem : y ∈ Subgroup.zpowers b := by
    rw [hbtop]
    trivial
  rw [Subgroup.mem_zpowers_iff] at hxmem hymem
  rcases hxmem with ⟨m, rfl⟩
  rcases hymem with ⟨l, hy_eq⟩
  rw [← hy_eq] at hy
  have hlpos : 0 < l :=
    (zpow_lt_zpow_iff_right hb).1 (by simpa using hy)
  obtain ⟨n, hn⟩ := Archimedean.arch m hlpos
  refine ⟨n, ?_⟩
  rw [← hy_eq]
  have hmn : m ≤ l * (n : ℤ) := by
    simpa [nsmul_eq_mul, mul_comm] using hn
  calc
    b ^ m ≤ b ^ (l * (n : ℤ)) :=
      (zpow_le_zpow_iff_right hb).2 hmn
    _ = (b ^ l) ^ n := by
      rw [zpow_mul, zpow_natCast]

/-- If the nonzero part of a value group is cyclic, the value group is
multiplicatively Archimedean. -/
theorem units_isCyclic_mulArchimedean
    (Gamma : Type x) [LinearOrderedCommGroupWithZero Gamma]
    [IsCyclic Gammaˣ] :
    MulArchimedean Gamma := by
  have : MulArchimedean Gammaˣ :=
    isCyclic_mulArchimedean Gammaˣ
  exact (Units.mulArchimedean_iff (G₀ := Gamma)).1 inferInstance

/-- A nontrivial valuation whose ambient value group has cyclic unit group is
rank one.  This is used only after restricting an abstract complete-DVF
valuation to its actual range. -/
@[implicit_reducible]
noncomputable def rankOneOfUnitsIsCyclic
    [Ring R]
    (v : _root_.Valuation R Gamma) [v.IsNontrivial] [IsCyclic Gammaˣ] :
    v.RankOne := by
  haveI : MulArchimedean Gamma :=
    units_isCyclic_mulArchimedean Gamma
  haveI :
      MulArchimedean
        (MonoidWithZeroHom.ValueGroup₀
          (MonoidWithZeroHom.ofClass v)) :=
    MulArchimedean.comap
      MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exact
    Classical.choice
      ((_root_.Valuation.nonempty_rankOne_iff_mulArchimedean
        (v := v)).2 inferInstance)

open LinearOrderedCommGroup

/-- For a valuation with values in the standard group `ℤᵐ⁰`, an element of
value `exp (-1)` is a uniformizer. -/
theorem isUniformizer_of_valuation_eq_exp_neg_one
    {K : Type u} [Field K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [v.IsRankOneDiscrete] (π : K)
    (hπ : v π = WithZero.exp (-1 : ℤ)) :
    v.IsUniformizer π := by
  rw [_root_.Valuation.IsUniformizer.iff, hπ]
  simpa using
    (congrArg Units.val
      (_root_.Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
        (v := v) ⟨π, hπ⟩)).symm

/-- A surjective standard `ℤᵐ⁰`-valued valuation has a normalized
uniformizer in its valuation subring. -/
theorem exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
    {K : Type u} [Field K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) :
    ∃ π : v.valuationSubring,
      v (π : K) = WithZero.exp (-1 : ℤ) := by
  rcases hv (WithZero.exp (-1 : ℤ)) with ⟨π, hπ⟩
  have hπmem : π ∈ v.valuationSubring := by
    change v π ≤ 1
    rw [hπ]
    change WithZero.exp (-1 : ℤ) ≤ WithZero.exp (0 : ℤ)
    rw [WithZero.exp_le_exp]
    norm_num
  exact ⟨⟨π, hπmem⟩, hπ⟩


end WithZeroValuation
end LocalFieldTheory.DiscreteValuationField

end
