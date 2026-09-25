/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Padic.PrincipalUnits
/-!
# Standard p-adic norm-subgroup intersections

The p-adic prime element used by the cyclotomic norm calculation has
normalized valuation `-1`.  This file records the corresponding orientation
of the standard unramified/principal-unit intersection lemma.
-/

@[expose] public section

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory
open LocalFieldTheory.Padic
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The intersection of the degree-`f` unramified condition and the
depth-`n` principal-unit condition is contained in the standard p-adic
subgroup with prime exponent `f`. -/
theorem unramifiedNormSubgroup_inf_padicPrincipalSubgroup_le
    (p f n : ℕ) [Fact p.Prime]
    [IsNonarchimedeanLocalField ℚ_[p]] :
    unramifiedNormSubgroup ℚ_[p] f ⊓
        LocalFieldTheory.uniformizerPrincipalSubgroup ℚ_[p] (padicPrimeUnit p) 1 n ≤
      LocalFieldTheory.uniformizerPrincipalSubgroup ℚ_[p] (padicPrimeUnit p) f n := by
  intro x hx
  rcases Subgroup.mem_sup.mp hx.2 with ⟨y, hy, z, hz, hyz⟩
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, hky⟩
  have hky' : (padicPrimeUnit p) ^ k = y := by
    simpa using hky
  change z ∈ (principalUnits ℚ_[p] n).map
    (integerUnitsToFieldUnits ℚ_[p]) at hz
  rcases hz with ⟨u, hu, huz⟩
  have hvz : valuationMap ℚ_[p] (Additive.ofMul z) = 0 := by
    rw [← huz]
    exact v_integerUnitsToFieldUnits ℚ_[p] u
  have hvx : valuationMap ℚ_[p] (Additive.ofMul x) = -k := by
    calc
      valuationMap ℚ_[p] (Additive.ofMul x) =
          valuationMap ℚ_[p] (Additive.ofMul (y * z)) :=
        congrArg _ hyz.symm
      _ = valuationMap ℚ_[p] (Additive.ofMul y) +
          valuationMap ℚ_[p] (Additive.ofMul z) :=
        valuationMap_ofMul_mul ℚ_[p] y z
      _ = valuationMap ℚ_[p]
            (Additive.ofMul ((padicPrimeUnit p) ^ k)) + 0 := by
        rw [hky', hvz]
      _ = k * (-1) + 0 := by
        rw [valuationMap_ofMul_zpow, valuationMap_padicPrimeUnit]
      _ = -k := by ring
  have hfneg : (f : ℤ) ∣ -k := by
    rw [← hvx]
    exact (mem_unramifiedNormSubgroup_iff ℚ_[p] f x).1 hx.1
  obtain ⟨t, ht⟩ := hfneg
  have hk : k = (f : ℤ) * (-t) := by
    calc
      k = -(-k) := by ring
      _ = -((f : ℤ) * t) := by rw [ht]
      _ = (f : ℤ) * (-t) := by ring
  have hyTarget : y ∈ Subgroup.zpowers ((padicPrimeUnit p) ^ f) := by
    rw [← hky', Subgroup.mem_zpowers_iff]
    refine ⟨-t, ?_⟩
    calc
      ((padicPrimeUnit p) ^ f) ^ (-t) =
          ((padicPrimeUnit p) ^ (f : ℤ)) ^ (-t) := by
        rw [zpow_natCast]
      _ = (padicPrimeUnit p) ^ ((f : ℤ) * (-t)) := by
        rw [zpow_mul]
      _ = (padicPrimeUnit p) ^ k := by rw [← hk]
  exact Subgroup.mem_sup.mpr ⟨y, hyTarget, z, ⟨u, hu, huz⟩, hyz⟩

end LocalClassFieldTheory

end
