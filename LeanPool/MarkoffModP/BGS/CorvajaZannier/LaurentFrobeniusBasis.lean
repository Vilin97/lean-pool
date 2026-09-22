/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.LaurentSeries

/-!
# Exponent dilation on Laurent series

This file isolates the *parameter* map `z |-> z^q` on `K((z))`.  It is not
the coefficientwise Frobenius: coefficients are left unchanged.
-/

open HahnSeries

noncomputable section

namespace BGS.CorvajaZannier

variable (K : Type*) [Field K]

/-- Multiplication of Laurent exponents by `q`. -/
def laurentExponentDilationIndex (q : ℕ) : ℤ →+ ℤ where
  toFun n := (q : ℤ) * n
  map_zero' := by simp
  map_add' _ _ := by ring

@[simp]
theorem laurentExponentDilationIndex_apply (q : ℕ) (n : ℤ) :
    laurentExponentDilationIndex q n = (q : ℤ) * n := rfl

theorem laurentExponentDilationIndex_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (laurentExponentDilationIndex q) := by
  intro a b hab
  simp only [laurentExponentDilationIndex_apply] at hab
  exact mul_left_cancel₀ (by exact_mod_cast hq.ne') hab

theorem laurentExponentDilationIndex_le_iff {q : ℕ} (hq : 0 < q) (a b : ℤ) :
    laurentExponentDilationIndex q a ≤ laurentExponentDilationIndex q b ↔ a ≤ b := by
  simp only [laurentExponentDilationIndex_apply]
  exact Int.mul_le_mul_left (by exact_mod_cast hq)

/-- The `K`-algebra embedding of Laurent series induced by `z |-> z^q`.

This map dilates exponents and fixes every coefficient.  In particular it is
different from coefficientwise Frobenius unless extra hypotheses identify the
two maps on a chosen constant field.
-/
def laurentExponentDilation {q : ℕ} (hq : 0 < q) :
    LaurentSeries K →ₐ[K] LaurentSeries K :=
  { HahnSeries.embDomainRingHom (R := K) (Γ := ℤ) (Γ' := ℤ)
      (laurentExponentDilationIndex q)
      (laurentExponentDilationIndex_injective hq)
      (laurentExponentDilationIndex_le_iff hq) with
    commutes' := by
      intro a
      rw [LaurentSeries.algebraMap_apply]
      change HahnSeries.embDomain _ (HahnSeries.C a) = HahnSeries.C a
      exact HahnSeries.embDomainRingHom_C }

theorem laurentExponentDilation_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (laurentExponentDilation K hq) :=
  by
    change Function.Injective
      (HahnSeries.embDomain (R := K) (Γ := ℤ) (Γ' := ℤ) _)
    exact HahnSeries.embDomain_injective

@[simp]
theorem coeff_laurentExponentDilation_mul {q : ℕ} (hq : 0 < q)
    (f : LaurentSeries K) (n : ℤ) :
    ((laurentExponentDilation K hq) f).coeff ((q : ℤ) * n) = f.coeff n :=
  by
    change (HahnSeries.embDomain (R := K) (Γ := ℤ) (Γ' := ℤ) _ f).coeff _ = _
    exact HahnSeries.embDomain_coeff

@[simp]
theorem laurentExponentDilation_single {q : ℕ} (hq : 0 < q)
    (n : ℤ) (a : K) :
    (laurentExponentDilation K hq) (HahnSeries.single n a) =
      HahnSeries.single ((q : ℤ) * n) a :=
  by
    change HahnSeries.embDomain (R := K) (Γ := ℤ) (Γ' := ℤ) _
      (HahnSeries.single n a) = _
    exact HahnSeries.embDomain_single

/-- The embedded copy `K((z^q))` inside `K((z))`. -/
abbrev laurentExponentSubfield {q : ℕ} (hq : 0 < q) :
    IntermediateField K (LaurentSeries K) :=
  (laurentExponentDilation K hq).fieldRange

/-- A chosen inverse image under exponent dilation. -/
def laurentUndilate {q : ℕ} (hq : 0 < q)
    (a : laurentExponentSubfield K hq) : LaurentSeries K :=
  Classical.choose (AlgHom.mem_fieldRange.mp a.property)

@[simp]
theorem laurentExponentDilation_undilate {q : ℕ} (hq : 0 < q)
    (a : laurentExponentSubfield K hq) :
    (laurentExponentDilation K hq) (laurentUndilate K hq a) = a :=
  Classical.choose_spec (AlgHom.mem_fieldRange.mp a.property)

/-- The Laurent parameter `z`. -/
def laurentParameter : LaurentSeries K := HahnSeries.single 1 1

@[simp]
theorem laurentParameter_pow (n : ℕ) :
    laurentParameter K ^ n = HahnSeries.single (n : ℤ) 1 := by
  simp [laurentParameter, HahnSeries.single_pow]

private theorem dilation_notin_wrong_residue {q : ℕ} (hq : 0 < q)
    (i j : Fin q) (hij : i ≠ j) (n : ℤ) :
    (q : ℤ) * n + (i : ℤ) - (j : ℤ) ∉
      Set.range (laurentExponentDilationIndex q) := by
  rintro ⟨m, hm⟩
  simp only [laurentExponentDilationIndex_apply] at hm
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hi0 : (0 : ℤ) ≤ i := Int.natCast_nonneg _
  have hj0 : (0 : ℤ) ≤ j := Int.natCast_nonneg _
  have hiq : (i : ℤ) < q := by exact_mod_cast i.isLt
  have hjq : (j : ℤ) < q := by exact_mod_cast j.isLt
  have heq : (q : ℤ) * (m - n) = (i : ℤ) - (j : ℤ) := by
    nlinarith
  have hmn : m - n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : (q : ℤ) * (m - n) ≤ -q := by nlinarith
      nlinarith
    · have : (q : ℤ) ≤ q * (m - n) := by nlinarith
      nlinarith
  apply hij
  apply Fin.ext
  exact_mod_cast (by nlinarith [heq, hmn] : (i : ℤ) = j)

theorem coeff_subfield_smul_parameter_pow {q : ℕ} (hq : 0 < q)
    (a : laurentExponentSubfield K hq) (i j : Fin q) (n : ℤ) :
    (a • laurentParameter K ^ (j : ℕ)).coeff ((q : ℤ) * n + (i : ℤ)) =
      if i = j then (laurentUndilate K hq a).coeff n else 0 := by
  rw [laurentParameter_pow, Algebra.smul_def, HahnSeries.coeff_mul_single]
  simp only [mul_one]
  change ((a : LaurentSeries K)).coeff ((q : ℤ) * n + (i : ℤ) - (j : ℤ)) = _
  split_ifs with hij
  · subst j
    rw [add_sub_cancel_right]
    rw [← laurentExponentDilation_undilate K hq a]
    exact coeff_laurentExponentDilation_mul K hq _ _
  · rw [← laurentExponentDilation_undilate K hq a]
    change (HahnSeries.embDomain (R := K) (Γ := ℤ) (Γ' := ℤ) _
      (laurentUndilate K hq a)).coeff
        ((q : ℤ) * n + (i : ℤ) - (j : ℤ)) = 0
    exact HahnSeries.embDomain_of_notMem_range
      (dilation_notin_wrong_residue hq i j hij n)

/-- The residue classes of exponents prove that
`1, z, ..., z^(q-1)` are linearly independent over the embedded field
`K((z^q))`.

This is the local linear-disjointness half of the Laurent-series argument.  It
does not assert spanning; the complementary spanning statement requires an
explicit residue-component decomposition of arbitrary Laurent series.
-/
theorem linearIndependent_laurentParameter_pow {q : ℕ} (hq : 0 < q) :
    LinearIndependent (laurentExponentSubfield K hq)
      (fun i : Fin q ↦ laurentParameter K ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hcoeff (n : ℤ) : (laurentUndilate K hq (g i)).coeff n = 0 := by
    have hc := congrArg
      (fun f : LaurentSeries K ↦ f.coeff ((q : ℤ) * n + (i : ℤ))) hg
    simp only [HahnSeries.coeff_sum,
      coeff_subfield_smul_parameter_pow K hq] at hc
    simpa using hc
  have hundilate : laurentUndilate K hq (g i) = 0 := by
    ext n
    simpa using hcoeff n
  apply Subtype.ext
  change (g i : LaurentSeries K) = 0
  rw [← laurentExponentDilation_undilate K hq (g i), hundilate, map_zero]

end BGS.CorvajaZannier
