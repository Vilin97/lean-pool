/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram

VENDORED into AINTLIB (2026-07-04) from WilliamCoram/PhD (PhD/PR'd/MvRestricted.lean,
with PhD/PR'd/Algebra/Order/Antidiag/Prod.lean inlined), pending its mathlib PR.
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Multivariate restricted power series over a normed ring (vendored) -/

namespace Finset

lemma nonempty_antidiagonal {M : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] (a : M) :
    (Finset.antidiagonal a).Nonempty :=
  ⟨(0, a), by simp⟩

end Finset

/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/




/-!
# Multivariate restricted power series

`IsRestrictedGauss` : We say a multivariate power series over a normed ring `R` is restricted for a
tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section

namespace MvPowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] {σ : Type*}

/-- A multivariate power series over a normed ring `R` is restricted for a
  tuple `c` if `‖coeff t f‖ * ∏ i ∈ t.support, c i ^ t i → 0` under the cofinite filter. -/
def IsRestrictedGauss (c : σ → ℝ) (f : MvPowerSeries σ R) :=
  Tendsto (fun (t : σ →₀ ℕ) ↦ ‖coeff t f‖ * t.prod (c · ^ ·)) cofinite (𝓝 0)

@[simp]
lemma isRestrictedGauss_abs_iff (c : σ → ℝ) (f : MvPowerSeries σ R) :
    IsRestrictedGauss |c| f ↔ IsRestrictedGauss c f := by
  simp [IsRestrictedGauss, NormedAddGroup.tendsto_nhds_zero, Finsupp.prod]

lemma isRestrictedGauss_zero (c : σ → ℝ) : IsRestrictedGauss c (0 : MvPowerSeries σ R) := by
  simpa [IsRestrictedGauss] using tendsto_const_nhds

lemma isRestrictedGauss_monomial (c : σ → ℝ) (n : σ →₀ ℕ) (a : R) :
    IsRestrictedGauss c (monomial n a) := by
  classical
  refine tendsto_nhds_of_eventually_eq (Set.Subsingleton.finite ?_)
  aesop (add simp [Set.Subsingleton, coeff_monomial])

lemma isRestrictedGauss_one (c : σ → ℝ) : IsRestrictedGauss c (1 : MvPowerSeries σ R) :=
  isRestrictedGauss_monomial c 0 1

lemma isRestrictedGauss_C (c : σ → ℝ) (a : R) : IsRestrictedGauss c (C a) := by
  simpa [monomial_zero_eq_C_apply] using isRestrictedGauss_monomial c 0 a

lemma isRestrictedGauss.add (c : σ → ℝ) {f g : MvPowerSeries σ R} (hf : IsRestrictedGauss c f)
    (hg : IsRestrictedGauss c g) : IsRestrictedGauss c (f + g) := by
  rw [← isRestrictedGauss_abs_iff, IsRestrictedGauss] at *
  refine tendsto_const_nhds.squeeze (add_zero (0 : ℝ) ▸ hf.add hg) (fun n ↦ ?_) fun n ↦ ?_
  · dsimp [Finsupp.prod]; positivity -- TODO: add positivity extension for Finsupp.prod
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le ..) (by dsimp [Finsupp.prod]; positivity)

lemma isRestrictedGauss.neg (c : σ → ℝ) {f : MvPowerSeries σ R} (hf : IsRestrictedGauss c f) :
    IsRestrictedGauss c (-f) := by
  rw [← isRestrictedGauss_abs_iff, IsRestrictedGauss] at *
  simpa [IsRestrictedGauss] using hf

open IsUltrametricDist

/- TODO: Find a home for this lemma. -/
lemma tendsto_sup'_antidiagonal_cofinite
    {M R : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] {f : M × M → R}
    [LinearOrder R] {F : Filter R} (hf : Tendsto f cofinite F) :
    Tendsto (fun a ↦ (Finset.antidiagonal a).sup' (Finset.nonempty_antidiagonal _) f)
      cofinite F := by
  intro U hU
  refine ((((hf hU).image Prod.fst)).add ((hf hU).image Prod.snd)).subset ?_
  simp only [Set.subset_def, Set.mem_compl_iff, Set.mem_preimage]
  intro x hx
  obtain ⟨i, hi, e⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_antidiagonal x) f
  obtain rfl : i.1 + i.2 = x := by simpa using hi
  exact Set.add_mem_add (by simpa using ⟨i.2, e ▸ hx⟩) (by simpa using ⟨i.1, e ▸ hx⟩)

lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S]
    [IsUltrametricDist S] {C : M → ℝ} (hC : ∀ a b, C (a + b) = C a * C b) {f g : M → S}
    (hf : Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  wlog hC' : 0 ≤ C generalizing C
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa using this (C := |C|) (by simp [hC]) (by simpa using hf.norm)
      (by simpa using hg.norm) (fun _ => by simp)
  refine .squeeze tendsto_const_nhds
    (tendsto_sup'_antidiagonal_cofinite (tendsto_mul_cofinite_nhds_zero hf hg))
    (fun x => by simpa using (mul_nonneg (by simp) (hC' x))) fun a ↦ ?_
  have : 0 ≤ C a := hC' a
  grw [(Finset.nonempty_antidiagonal _).norm_sum_le_sup'_norm, Finset.sup'_mul₀ this]
  refine Finset.sup'_mono_fun fun x hx ↦ ?_
  grw [mul_mul_mul_comm, ← hC, Finset.mem_antidiagonal.mp hx, ← norm_mul_le]

lemma isRestrictedGauss.mul [IsUltrametricDist R] (c : σ → ℝ) {f g : MvPowerSeries σ R}
    (hf : IsRestrictedGauss c f) (hg : IsRestrictedGauss c g) : IsRestrictedGauss c (f * g) := by
  classical
  rw [← isRestrictedGauss_abs_iff, IsRestrictedGauss] at *
  exact tendsto_antidiagonal (by simp [Finsupp.prod_add_index', pow_add]) hf hg

/-- Additive subgroup structure on `MvPowerSeries σ R`. -/
def isAddSubgroup (c : σ → ℝ) : AddSubgroup (MvPowerSeries σ R) where
  carrier := IsRestrictedGauss c
  zero_mem' := isRestrictedGauss_zero c
  add_mem' := isRestrictedGauss.add c
  neg_mem' := isRestrictedGauss.neg c

variable [IsUltrametricDist R]

/-- Ring structure on `MvPowerSeries σ R`. -/
def isSubring (c : σ → ℝ) : Subring (MvPowerSeries σ R) where
  __ := isAddSubgroup c
  one_mem' := isRestrictedGauss_one c
  mul_mem' := isRestrictedGauss.mul c

variable (R) in
/-- The type of restricted `MvPowerSeries σ R`. -/
def Restricted (c : σ → ℝ) : Type _ := isSubring (R := R) c

/-- Ring structure on `Restricted R c`. -/
noncomputable
instance (c : σ → ℝ) : Ring (Restricted R c) :=
  Subring.toRing (isSubring c)

/-- Commutative ring structure over a commutative base, through the single
canonical subring path (keeps the `Ring` instance definitionally aligned). -/
noncomputable
instance (priority := 50) {R' : Type*} [NormedCommRing R'] [IsUltrametricDist R']
    (c : σ → ℝ) : CommRing (Restricted R' c) :=
  inferInstanceAs (CommRing ↥(isSubring (R := R') c))

end MvPowerSeries
