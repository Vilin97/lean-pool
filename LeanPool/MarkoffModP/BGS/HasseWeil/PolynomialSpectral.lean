/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ZetaExtensionTrace
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Spectral parameters from a zeta numerator

This file records the elementary factorization needed after rationality of a
curve zeta function has produced a numerator polynomial.  A complex
polynomial whose constant coefficient is one is uniquely the product of the
factors `1 - alpha * X`, where the parameters `alpha` are the inverses of its
roots, counted with multiplicity.

The substantive arithmetic input remains the construction of the zeta
numerator and its logarithmic-derivative point-count identity.  No spectral
norm estimate is used here.
-/

@[expose] public section

namespace BGS.HasseWeil

open Polynomial
open scoped BigOperators Polynomial

noncomputable section

/-- The reciprocal root parameter attached to the `i`-th root of `P`, with
roots enumerated by the canonical sorted list underlying their multiset. -/
def reciprocalRootParameter (P : Polynomial ℂ) (i : Fin P.natDegree) : ℂ :=
  ((P.roots.toList.get
    (Fin.cast (by simp [IsAlgClosed.card_roots_eq_natDegree]) i))⁻¹)

/-- Summing powers of the indexed reciprocal-root family agrees with the
multiset power sum, including root multiplicities. -/
theorem sum_reciprocalRootParameter_pow
    (P : Polynomial ℂ) (m : ℕ) :
    ∑ i, reciprocalRootParameter P i ^ m =
      (P.roots.map fun r => r⁻¹ ^ m).sum := by
  unfold reciprocalRootParameter
  have hlen : P.natDegree = P.roots.toList.length :=
    ((Multiset.length_toList P.roots).trans
      IsAlgClosed.card_roots_eq_natDegree).symm
  let e : Fin P.natDegree ≃ Fin P.roots.toList.length :=
    Fin.castOrderIso hlen
  calc
    ∑ i, (P.roots.toList.get (Fin.cast hlen i))⁻¹ ^ m =
        ∑ j : Fin P.roots.toList.length,
          (P.roots.toList.get j)⁻¹ ^ m := by
      apply Fintype.sum_equiv e
      intro i
      rfl
    _ = (P.roots.map fun r => r⁻¹ ^ m).sum := by
      simpa [Multiset.sum_coe] using
        (Fin.sum_univ_fun_getElem P.roots.toList (fun r => r⁻¹ ^ m))

/-- A complex polynomial normalized by `P(0) = 1` factors into reciprocal
linear factors, with one factor for every root counted with multiplicity. -/
theorem polynomial_eq_prod_one_sub_C_mul_X_of_coeff_zero_eq_one
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 1) :
    P = (P.roots.map fun r => 1 - C r⁻¹ * X).prod := by
  have hP : P ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hP0
    norm_num at hP0
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hroot0 (r : ℂ) (hr : r ∈ P.roots) : r ≠ 0 := by
    intro hr0
    subst r
    have hEval : P.eval 0 = 0 := (mem_roots hP).mp hr
    rw [← coeff_zero_eq_eval_zero, hP0] at hEval
    norm_num at hEval
  let R : Polynomial ℂ := (P.roots.map fun r => X - C r).prod
  let c : ℂ := (P.roots.map fun r => -r⁻¹).prod
  have hfactor (r : ℂ) (hr : r ∈ P.roots) :
      1 - C r⁻¹ * X = C (-r⁻¹) * (X - C r) := by
    rw [mul_sub, ← C_mul]
    simp [hroot0 r hr]
    ring
  have hQ : (P.roots.map fun r => 1 - C r⁻¹ * X).prod = C c * R := by
    dsimp [R, c]
    have hmap :
        P.roots.map (fun r => 1 - C r⁻¹ * X) =
          P.roots.map (fun r => C (-r⁻¹) * (X - C r)) := by
      apply Multiset.map_congr rfl
      intro r hr
      exact hfactor r hr
    rw [hmap, Multiset.prod_map_mul]
    have hCprod :
        (P.roots.map fun r => C (-r⁻¹)).prod =
          C (P.roots.map fun r => -r⁻¹).prod := by
      simpa only [Multiset.map_map, Function.comp_apply] using
        (map_multiset_prod C (P.roots.map fun r => -r⁻¹)).symm
    rw [hCprod]
  have hPprod : P = C P.leadingCoeff * R := by
    simpa only [R] using hsplits.eq_prod_roots
  have hR0eq : R.coeff 0 = (P.roots.map fun r => -r).prod := by
    dsimp [R]
    simp [coeff_zero_eq_eval_zero, eval_multiset_prod]
  have hR0 : R.coeff 0 ≠ 0 := by
    rw [hR0eq]
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨z, hz, hneg⟩ := Multiset.mem_map.mp hzero
    exact hroot0 z hz (neg_eq_zero.mp hneg)
  have hc : c * R.coeff 0 = 1 := by
    rw [hR0eq]
    dsimp [c]
    rw [← Multiset.prod_map_mul]
    apply Multiset.prod_eq_one
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
    simp [hroot0 r hr]
  have hlc : P.leadingCoeff * R.coeff 0 = 1 := by
    have hcoeff := congrArg (fun Q : Polynomial ℂ => Q.coeff 0) hPprod
    simpa [hP0] using hcoeff.symm
  have hscalar : P.leadingCoeff = c := by
    apply mul_right_cancel₀ hR0
    rw [hlc, hc]
  calc
    P = C P.leadingCoeff * R := hPprod
    _ = C c * R := by rw [hscalar]
    _ = (P.roots.map fun r => 1 - C r⁻¹ * X).prod := hQ.symm

/-- The reciprocal-root factorization with the parameters indexed by
`Fin P.natDegree`, ready for the finite power sums used in the spectral
point-count formula. -/
theorem polynomial_eq_prod_reciprocalRootParameter
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 1) :
    P = ∏ i, (1 - C (reciprocalRootParameter P i) * X) := by
  have hlen : P.natDegree = P.roots.toList.length :=
    ((Multiset.length_toList P.roots).trans
      IsAlgClosed.card_roots_eq_natDegree).symm
  let e : Fin P.natDegree ≃ Fin P.roots.toList.length :=
    Fin.castOrderIso hlen
  calc
    P = (P.roots.map fun r => 1 - C r⁻¹ * X).prod :=
      polynomial_eq_prod_one_sub_C_mul_X_of_coeff_zero_eq_one P hP0
    _ =
        (P.roots.toList.map fun r => 1 - C r⁻¹ * X).prod := by
      let f : ℂ → Polynomial ℂ := fun r => 1 - C r⁻¹ * X
      have hs := congrArg (fun s : Multiset ℂ => (s.map f).prod)
        (Multiset.coe_toList P.roots)
      simpa only [f, Multiset.map_coe, Multiset.prod_coe] using hs.symm
    _ = ∏ j : Fin P.roots.toList.length,
          (1 - C (P.roots.toList.get j)⁻¹ * X) := by
      simpa using
        (Fin.prod_univ_fun_getElem P.roots.toList
          (fun r => 1 - C r⁻¹ * X)).symm
    _ = ∏ i : Fin P.natDegree,
          (1 - C (P.roots.toList.get (Fin.cast hlen i))⁻¹ * X) := by
      symm
      apply Fintype.prod_equiv e
      intro i
      rfl
    _ = ∏ i, (1 - C (reciprocalRootParameter P i) * X) := by
      rfl

end

end BGS.HasseWeil
