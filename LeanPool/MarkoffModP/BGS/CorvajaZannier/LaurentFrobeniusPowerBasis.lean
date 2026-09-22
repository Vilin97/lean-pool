/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.LaurentFrobeniusBasis
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The Laurent-series power basis over exponent dilation

Every Laurent series splits uniquely into its `q` exponent residue classes.
Together with the residue-class independence theorem, this proves that
`1, z, ..., z^(q-1)` is a basis of `K((z))` over `K((z^q))` and that the
extension has degree `q`.
-/

open HahnSeries

noncomputable section

namespace BGS.CorvajaZannier

variable (K : Type*) [Field K]

/-- The Laurent series obtained from the coefficients of `f` in one residue
class modulo `q`. -/
def laurentResidueComponent {q : ℕ} (hq : 0 < q)
    (f : LaurentSeries K) (i : Fin q) : LaurentSeries K :=
  HahnSeries.ofSuppBddBelow
    (fun n : ℤ ↦ f.coeff ((q : ℤ) * n + (i : ℤ))) (by
      refine ⟨min 0 (f.order - (i : ℤ)), ?_⟩
      intro n hn
      change f.coeff ((q : ℤ) * n + (i : ℤ)) ≠ 0 at hn
      have hord : f.order ≤ (q : ℤ) * n + (i : ℤ) :=
        HahnSeries.order_le_of_coeff_ne_zero hn
      by_cases hn0 : 0 ≤ n
      · exact (min_le_left _ _).trans hn0
      · have hnneg : n < 0 := lt_of_not_ge hn0
        have hqone : (1 : ℤ) ≤ q := by exact_mod_cast hq
        have hmul : (q : ℤ) * n ≤ n := by nlinarith
        exact (min_le_right _ _).trans (by linarith))

@[simp]
theorem coeff_laurentResidueComponent {q : ℕ} (hq : 0 < q)
    (f : LaurentSeries K) (i : Fin q) (n : ℤ) :
    (laurentResidueComponent K hq f i).coeff n =
      f.coeff ((q : ℤ) * n + (i : ℤ)) :=
  rfl

/-- A residue component, embedded back by exponent dilation and regarded as a
scalar in `K((z^q))`. -/
def laurentResidueScalar {q : ℕ} (hq : 0 < q)
    (f : LaurentSeries K) (i : Fin q) : laurentExponentSubfield K hq :=
  ⟨(laurentExponentDilation K hq) (laurentResidueComponent K hq f i),
    ⟨laurentResidueComponent K hq f i, rfl⟩⟩

theorem laurentUndilate_residueScalar {q : ℕ} (hq : 0 < q)
    (f : LaurentSeries K) (i : Fin q) :
    laurentUndilate K hq (laurentResidueScalar K hq f i) =
      laurentResidueComponent K hq f i := by
  apply laurentExponentDilation_injective K hq
  rw [laurentExponentDilation_undilate]
  rfl

/-- Euclidean division gives the exponent residue in `Fin q`. -/
def laurentExponentResidue {q : ℕ} (hq : 0 < q) (m : ℤ) : Fin q :=
  ⟨(m % (q : ℤ)).toNat, by
    have hnonneg : 0 ≤ m % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    have hlt : m % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
    rw [Int.toNat_lt hnonneg]
    exact hlt⟩

@[simp]
theorem coe_laurentExponentResidue {q : ℕ} (hq : 0 < q) (m : ℤ) :
    ((laurentExponentResidue hq m : Fin q) : ℤ) = m % (q : ℤ) := by
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hnonneg : 0 ≤ m % (q : ℤ) := Int.emod_nonneg _ hqz
  simp [laurentExponentResidue, Int.toNat_of_nonneg hnonneg]

theorem exponent_ediv_residue {q : ℕ} (hq : 0 < q) (m : ℤ) :
    (q : ℤ) * (m / (q : ℤ)) + (laurentExponentResidue hq m : ℤ) = m := by
  rw [coe_laurentExponentResidue]
  linarith [Int.emod_add_mul_ediv m (q : ℤ)]

/-- Reassemble a Laurent series from its `q` residue components. -/
theorem sum_residueScalar_smul_parameter_pow {q : ℕ} (hq : 0 < q)
    (f : LaurentSeries K) :
    (∑ i : Fin q,
      laurentResidueScalar K hq f i • laurentParameter K ^ (i : ℕ)) = f := by
  ext m
  let i₀ : Fin q := laurentExponentResidue hq m
  let n : ℤ := m / (q : ℤ)
  have hm : (q : ℤ) * n + (i₀ : ℤ) = m := by
    exact exponent_ediv_residue hq m
  rw [← hm]
  simp only [HahnSeries.coeff_sum,
    coeff_subfield_smul_parameter_pow K hq]
  rw [Finset.sum_ite_eq Finset.univ i₀]
  simp only [Finset.mem_univ, ite_true]
  rw [laurentUndilate_residueScalar, coeff_laurentResidueComponent, hm]

/-- The powers `1,z,...,z^(q-1)` span `K((z))` over `K((z^q))`. -/
theorem span_laurentParameter_pow_eq_top {q : ℕ} (hq : 0 < q) :
    Submodule.span (laurentExponentSubfield K hq)
      (Set.range (fun i : Fin q ↦ laurentParameter K ^ (i : ℕ))) = ⊤ := by
  apply top_unique
  intro f _
  rw [← sum_residueScalar_smul_parameter_pow K hq f]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i))

/-- The source's Laurent power basis. -/
noncomputable def laurentParameterPowerBasis {q : ℕ} (hq : 0 < q) :
    Module.Basis (Fin q) (laurentExponentSubfield K hq) (LaurentSeries K) :=
  Module.Basis.mk (linearIndependent_laurentParameter_pow K hq)
    (span_laurentParameter_pow_eq_top K hq).ge

@[simp]
theorem laurentParameterPowerBasis_apply {q : ℕ} (hq : 0 < q) (i : Fin q) :
    laurentParameterPowerBasis K hq i = laurentParameter K ^ (i : ℕ) :=
  Module.Basis.mk_apply _ _ i

/-- The exponent-dilation Laurent subfield has index exactly `q`. -/
theorem finrank_laurentExponentSubfield {q : ℕ} (hq : 0 < q) :
    Module.finrank (laurentExponentSubfield K hq) (LaurentSeries K) = q := by
  rw [Module.finrank_eq_card_basis (laurentParameterPowerBasis K hq)]
  exact Fintype.card_fin q

end BGS.CorvajaZannier
