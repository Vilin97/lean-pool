/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Core.ConicParametrization
public import LeanPool.MarkoffModP.BGS.Markoff.Core.FiniteRotationEigenvalues

/-!
# Periodic points on semisimple fibers

This module proves the point-level implication needed in the opening.  It does not infer finite
matrix order from periodicity of a single vector.  Instead it uses the explicit conic
parametrization: on a nonparabolic fiber, rotation multiplies the eigen-coordinate by a chosen
matrix eigenvalue, so a positive return forces that eigenvalue to be torsion.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Every trace parameter over an algebraically closed field is `w + w⁻¹` for a nonzero
eigenvalue `w`. -/
theorem exists_splitTorusTrace_eq (t : K) :
    ∃ w : Kˣ, t = splitTorusTrace w := by
  let f : K[X] := X ^ 2 - C t * X + 1
  have hfdegree : f.degree ≠ 0 := by
    have hfshape : IsMonicOfDegree f 2 := by
      simpa [f] using isMonicOfDegree_sub_add_two t (1 : K)
    rw [degree_eq_natDegree hfshape.monic.ne_zero, hfshape.natDegree_eq]
    norm_num
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root f hfdegree
  have hreigen : r ^ 2 - t * r + 1 = 0 := by simpa [f] using hr
  have hrne : r ≠ 0 := by
    intro hrzero
    simp [hrzero] at hreigen
  let w : Kˣ := Units.mk0 r hrne
  refine ⟨w, ?_⟩
  have hmul : t * r = r ^ 2 + 1 := by linear_combination -hreigen
  change t = r + r⁻¹
  apply mul_right_cancel₀ hrne
  rw [hmul]
  field_simp

omit [IsAlgClosed K] in
private theorem eigenvalue_nonparabolic
    {t : K} {w : Kˣ} (htrace : t = splitTorusTrace w) (ht : t ^ 2 ≠ 4) :
    (w : K) ^ 2 ≠ 1 := by
  intro hw
  apply ht
  have hinv : ((w⁻¹ : Kˣ) : K) = (w : K) := by
    apply (mul_right_cancel₀ (Units.ne_zero w))
    simpa [pow_two] using hw.symm
  apply sub_eq_zero.mp
  rw [htrace, splitTorusTrace_sq_sub_four, hinv, sub_self, zero_pow]
  norm_num

omit [IsAlgClosed K] in
private theorem torsion_of_trace_zero {w : Kˣ} (htrace : splitTorusTrace w = 0) :
    IsOfFinOrder w := by
  have hwSquare : (w : K) ^ 2 = -1 := by
    have h : (w : K) + (w : K)⁻¹ = 0 := by
      simpa [splitTorusTrace] using htrace
    have hmul := congrArg (fun q : K => q * (w : K)) h
    simp [add_mul, Units.ne_zero w] at hmul
    linear_combination hmul
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨4, by norm_num, ?_⟩
  apply Units.ext
  change (w : K) ^ 4 = 1
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hwSquare]
  norm_num

/-- A positive return of a point on a nonparabolic normalized fiber produces a torsion
eigenvalue representing the fixed trace coordinate. -/
theorem periodic_nonparabolic_fiber_has_torsion_eigenvalue
    {t : K} (ht : t ^ 2 ≠ 4) {x : NormalizedPoint K}
    (hx : x ∈ normalizedFiber1 t) {n : ℕ} (hn : 0 < n)
    (hperiodic : (normalizedRotate1^[n]) x = x) :
    ∃ w : Kˣ, IsOfFinOrder w ∧ t = splitTorusTrace w := by
  obtain ⟨w, htrace⟩ := exists_splitTorusTrace_eq t
  have hw := eigenvalue_nonparabolic htrace ht
  by_cases htZero : t = 0
  · refine ⟨w, torsion_of_trace_zero ?_, htrace⟩
    rw [← htrace, htZero]
  · let xp : ↑(normalizedFiber1 (splitTorusTrace w)) := ⟨x, by
      rw [← htrace]
      exact hx⟩
    let s : Kˣ := (splitFiberEquiv w hw (htrace ▸ htZero)).symm xp
    have hxrepr : splitFiberPoint w s = x := by
      exact congrArg Subtype.val ((splitFiberEquiv w hw (htrace ▸ htZero)).apply_symm_apply xp)
    rw [← hxrepr] at hperiodic
    have hpower := (iterate_normalizedRotate1_splitFiberPoint_eq_self_iff w s hw n).mp hperiodic
    refine ⟨w, ?_, htrace⟩
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, hpower⟩

end BGS.Markoff
