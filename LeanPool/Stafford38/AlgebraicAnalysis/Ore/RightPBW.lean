/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.RightHilbertBasis
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Right-coefficient PBW data for one derivation-Ore stage

The checked Ore interface gives the opposite-ring right action and the
triangular coefficient identities.  We prove directly that the candidate
monomials form a genuine right basis; the proof uses finite-support maximal
degree induction, so no freeness or flatness assumption is introduced.
-/

namespace AlgebraicAnalysis.OreRightPBW

open Polynomial
open Module
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreRightQuotient
open AlgebraicAnalysis.OreDerivationRightHilbertBasis

noncomputable section

universe u

variable {B : Type u} [Ring B]

/-- The candidate right-coefficient PBW monomial of order `n`. -/
def rightPBWMonomial (D : OreDivisionDerivation B) (n : ℕ) : NormalOre D :=
  normalForm D (Polynomial.X ^ n)

/-- The finitely supported right-coefficient combination of PBW monomials. -/
def rightPBWCombination (D : OreDivisionDerivation B) :
    (ℕ →₀ Bᵐᵒᵖ) →ₗ[Bᵐᵒᵖ] NormalOre D :=
  Finsupp.linearCombination Bᵐᵒᵖ (rightPBWMonomial D)

lemma rightPBWCombination_single (D : OreDivisionDerivation B)
    (n : ℕ) (b : Bᵐᵒᵖ) :
    rightPBWCombination D (Finsupp.single n b) =
      b • rightPBWMonomial D n := by
  simp [rightPBWCombination]

lemma rightPBWCombination_term_as_normalForm
    (D : OreDivisionDerivation B) (n : ℕ) (b : Bᵐᵒᵖ) :
    b • rightPBWMonomial D n =
      normalForm D (OreDivision.rightMul D (Polynomial.X ^ n)
        (Polynomial.C b.unop)) := by
  rw [rightPBWMonomial, normalOre_op_smul_def, ← normalForm_C,
    ← normalForm_mul]
lemma rightPBWCombination_finsupp_as_normalForm
     (D : OreDivisionDerivation B) (c : ℕ →₀ Bᵐᵒᵖ) :
    rightPBWCombination D c =
      normalForm D
        (c.sum fun n b => OreDivision.rightMul D (Polynomial.X ^ n)
          (Polynomial.C b.unop)) := by
  rw [rightPBWCombination, Finsupp.linearCombination_apply]
  rw [Finsupp.sum]
  rw [Finsupp.sum]
  change _ = normalFormAddHom D
    (∑ a ∈ c.support,
      OreDivision.rightMul D (Polynomial.X ^ a)
        (Polynomial.C (c a).unop))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n b
  exact rightPBWCombination_term_as_normalForm D n (c n)

lemma rightPBWCombination_eq_zero
    [Nontrivial B] (D : OreDivisionDerivation B) (c : ℕ →₀ Bᵐᵒᵖ)
    (hc : rightPBWCombination D c = 0) : c = 0 := by
  classical
  by_contra hcz
  have hne : c.support.Nonempty := Finsupp.support_nonempty_iff.mpr hcz
  let m : ℕ := c.support.max' hne
  have hm : m ∈ c.support := c.support.max'_mem hne
  have hle : ∀ a ∈ c.support, a ≤ m := by
    intro a ha
    exact Finset.le_max' c.support a ha
  have hpoly :
      c.sum (fun n b => OreDivision.rightMul D (Polynomial.X ^ n)
        (Polynomial.C b.unop)) = 0 := by
    have hnf :
        normalForm D
            (c.sum (fun n b => OreDivision.rightMul D (Polynomial.X ^ n)
              (Polynomial.C b.unop))) = 0 := by
      rw [← rightPBWCombination_finsupp_as_normalForm D c]
      exact hc
    apply normalForm_injective D
    simpa using hnf
  have hcoeff := congrArg (fun p : Polynomial B => p.coeff m) hpoly
  simp only [Finsupp.sum] at hcoeff
  dsimp at hcoeff
  rw [← Polynomial.lcoeff_apply, map_sum] at hcoeff
  have hterm : ∀ a ∈ c.support,
      (OreDivision.rightMul D (Polynomial.X ^ a)
        (Polynomial.C (c a).unop)).coeff m =
        if a = m then (c a).unop else 0 := by
    intro a ha
    have ha_le := hle a ha
    have hdeg : (Polynomial.X ^ a : Polynomial B).degree ≤
        (m : WithBot ℕ) := by
      rw [Polynomial.degree_X_pow]
      exact_mod_cast ha_le
    have htop := rightMul_coeff_C_of_degree_le D
      (Polynomial.X ^ a) (c a).unop m hdeg
    by_cases ham : a = m
    · subst a
      simpa using htop
    · rw [htop]
      have hcoeffX : (Polynomial.X ^ a : Polynomial B).coeff m = 0 := by
        rw [Polynomial.coeff_X_pow]
        split_ifs with h
        · exact False.elim (ham h.symm)
        · rfl
      rw [hcoeffX, zero_mul]
      simp [ham]
  rw [Finset.sum_eq_single m (fun a ha hneam => by
    exact hterm a ha |>.trans (by simp [hneam]))
    (by intro hnot; exact False.elim (hnot hm))] at hcoeff
  have hcm' :
      (OreDivision.rightMul D (Polynomial.X ^ m)
        (Polynomial.C (c m).unop)).coeff m = 0 := by
    simpa [Polynomial.lcoeff_apply] using hcoeff
  have hcm : c m = 0 := by
    have htop := hterm m hm
    rw [ite_eq_left rfl] at htop
    have hcm'' : (c m).unop = 0 := by simpa [htop] using hcm'
    exact MulOpposite.opEquiv.symm.injective hcm''
  exact (Finsupp.mem_support_iff.mp hm) hcm

theorem rightPBWCombination_injective
    [Nontrivial B] (D : OreDivisionDerivation B) :
    Function.Injective (rightPBWCombination D) := by
  intro c d h
  have hz : rightPBWCombination D (c - d) = 0 := by
    rw [map_sub, h, sub_self]
  have hcd := rightPBWCombination_eq_zero D (c - d) hz
  exact sub_eq_zero.mp hcd

lemma rightPBWMonomial_mem_span (D : OreDivisionDerivation B)
    (b : B) (n : ℕ) :
    normalForm D (Polynomial.monomial n b) ∈
      Submodule.span Bᵐᵒᵖ (Set.range (rightPBWMonomial D)) := by
  rw [normalForm_monomial_reverse]
  apply Submodule.sum_mem
  intro ij hij
  rw [← Nat.cast_smul_eq_nsmul Bᵐᵒᵖ]
  apply Submodule.smul_mem
  have hpow : rightPBWMonomial D ij.2 ∈
      Submodule.span Bᵐᵒᵖ (Set.range (rightPBWMonomial D)) := by
    apply Submodule.subset_span
    exact ⟨ij.2, rfl⟩
  have hscalar : (MulOpposite.op ((D^[ij.1]) b)) •
      rightPBWMonomial D ij.2 ∈
      Submodule.span Bᵐᵒᵖ (Set.range (rightPBWMonomial D)) :=
    Submodule.smul_mem _ _ hpow
  by_cases heven : Even ij.1
  · rw [heven.neg_one_pow]
    simpa only [one_mul, rightPBWMonomial] using hscalar
  · have hodd : Odd ij.1 := Nat.not_even_iff_odd.mp heven
    rw [hodd.neg_one_pow]
    simpa only [neg_one_mul, rightPBWMonomial] using
      (Submodule.span Bᵐᵒᵖ (Set.range (rightPBWMonomial D))).neg_mem hscalar

theorem rightPBW_span_eq_top (D : OreDivisionDerivation B) :
    Submodule.span Bᵐᵒᵖ (Set.range (rightPBWMonomial D)) = ⊤ := by
  apply top_unique
  intro z hz
  obtain ⟨p, rfl⟩ := normalForm_surjective D z
  change normalFormAddHom D p ∈ _
  rw [← Polynomial.sum_monomial_eq p, Polynomial.sum_def,
    map_sum (normalFormAddHom D)]
  apply Submodule.sum_mem
  intro n hn
  exact rightPBWMonomial_mem_span D (p.coeff n) n

theorem rightOrePBW_linearIndependent
    [Nontrivial B] (D : OreDivisionDerivation B) :
    LinearIndependent Bᵐᵒᵖ (rightPBWMonomial D) :=
  (linearIndependent_iff_injective_finsuppLinearCombination).2
    (rightPBWCombination_injective D)

/-- The right PBW basis of a one-stage derivation-Ore extension. -/
def rightOrePBWBasis [Nontrivial B] (D : OreDivisionDerivation B) :
    Basis ℕ Bᵐᵒᵖ (NormalOre D) :=
  Basis.mk (rightOrePBW_linearIndependent D)
    (rightPBW_span_eq_top D).ge

@[simp]
theorem rightOrePBWBasis_apply [Nontrivial B]
    (D : OreDivisionDerivation B) (n : ℕ) :
    rightOrePBWBasis D n = rightPBWMonomial D n := by
  exact Basis.mk_apply _ _ _

theorem rightOrePBWBasis_repr_symm_single [Nontrivial B]
    (D : OreDivisionDerivation B) (n : ℕ) (b : Bᵐᵒᵖ) :
    (rightOrePBWBasis D).repr.symm (Finsupp.single n b) =
      b • rightPBWMonomial D n := by
  rw [(rightOrePBWBasis D).repr_symm_single, rightOrePBWBasis_apply]

theorem rightPBWMonomial_zero (D : OreDivisionDerivation B) :
    rightPBWMonomial D 0 = 1 := by
  simp [rightPBWMonomial, normalForm_one]

@[simp]
theorem rightPBWMonomial_op_smul
    (D : OreDivisionDerivation B) (b : Bᵐᵒᵖ) (n : ℕ) :
    b • rightPBWMonomial D n =
      normalForm D (Polynomial.X ^ n) * normalCoefficient D b.unop := by
  exact normalOre_op_smul_def D b (rightPBWMonomial D n)

/-- The finite window generated by the candidate right PBW monomials. -/
def rightPBWWindow (D : OreDivisionDerivation B) (n : ℕ) :
    Submodule Bᵐᵒᵖ (NormalOre D) :=
  Submodule.span Bᵐᵒᵖ
    (Set.range fun j : Fin n => rightPBWMonomial D (j : ℕ))

theorem normalForm_mem_rightPBWWindow_of_degree_lt
    (D : OreDivisionDerivation B) (p : Polynomial B) (n : ℕ)
    (hp : p = 0 ∨ p.natDegree < n) :
    normalForm D p ∈ rightPBWWindow D n := by
  simpa [rightPBWWindow, rightPBWMonomial, rightCoefficientWindow] using
    (normalForm_mem_rightCoefficientWindow_of_degree_lt D p n hp)
theorem rightPBWWindow_finite
     (D : OreDivisionDerivation B) (n : ℕ) :
    Module.Finite Bᵐᵒᵖ (rightPBWWindow D n) := by
  exact Module.Finite.span_of_finite Bᵐᵒᵖ
    (Set.finite_range (fun j : Fin n => rightPBWMonomial D (j : ℕ)))

@[simp]
theorem rightPBWMonomial_apply (D : OreDivisionDerivation B) (n : ℕ) :
    rightPBWMonomial D n = normalForm D (Polynomial.X ^ n) := rfl

/-- Right multiplication by a PBW monomial has the expected top coefficient.
This is the triangular input for an eventual basis proof. -/
theorem rightMul_Xpow_top_coefficient
    [Nontrivial B] (D : OreDivisionDerivation B) (p : Polynomial B)
    (n j : ℕ) (hp : p.degree ≤ (n : WithBot ℕ)) :
    (rightMul D p (Polynomial.X ^ j)).coeff (n + j) = p.coeff n := by
  exact rightMul_Xpow_coeff_of_degree_le D p n j hp

theorem rightMul_Xpow_degree_le
    [Nontrivial B]
    (D : OreDivisionDerivation B) (p : Polynomial B) (j : ℕ) :
      (rightMul D p (Polynomial.X ^ j)).degree ≤
      (p.natDegree + j : WithBot ℕ) := by
  have h := rightMul_degree_le D p (Polynomial.X ^ j)
  have hX : (Polynomial.X ^ j : Polynomial B).natDegree = j := by
    exact Polynomial.natDegree_X_pow _
  rw [hX] at h
  exact h

/-! ## Monic principal quotients -/

/-- A vector in the first `N` right-PBW slots has a coefficient-left normal
form of degree strictly less than `N`.  This is the converse, at the level
needed for division, of `normalForm_mem_rightPBWWindow_of_degree_lt`. -/
theorem exists_lowDegreePolynomial_eq_of_mem_rightPBWWindow
    [Nontrivial B] (D : OreDivisionDerivation B) (N : ℕ)
    {z : NormalOre D} (hz : z ∈ rightPBWWindow D N) :
    ∃ r : Polynomial B,
      (r = 0 ∨ r.natDegree < N) ∧ normalForm D r = z := by
  change z ∈ Submodule.span Bᵐᵒᵖ
    (Set.range fun j : Fin N ↦ normalForm D (Polynomial.X ^ (j : ℕ))) at hz
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Bᵐᵒᵖ).mp hz
  let r : Polynomial B := ∑ j : Fin N,
    rightMul D (Polynomial.X ^ (j : ℕ)) (Polynomial.C (c j).unop)
  refine ⟨r, ?_, ?_⟩
  · by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr ((Polynomial.natDegree_lt_iff_degree_lt hr).mpr (by
        rw [Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        change (Polynomial.lcoeff B m) (∑ j : Fin N,
          rightMul D (Polynomial.X ^ (j : ℕ))
            (Polynomial.C (c j).unop)) = 0
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        apply Polynomial.coeff_eq_zero_of_degree_lt
        have hdeg := rightMul_degree_le D
          (Polynomial.X ^ (j : ℕ)) (Polynomial.C (c j).unop)
        rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at hdeg
        exact lt_of_le_of_lt hdeg (by exact_mod_cast j.isLt.trans_le hm)))
  · change normalFormAddHom D (∑ j : Fin N,
      rightMul D (Polynomial.X ^ (j : ℕ))
        (Polynomial.C (c j).unop)) = z
    rw [map_sum, ← hc]
    apply Finset.sum_congr rfl
    intro j hj
    change normalForm D (rightMul D (Polynomial.X ^ (j : ℕ))
      (Polynomial.C (c j).unop)) = _
    rw [normalForm_mul]
    simp only [normalForm_C, normalOre_op_smul_def]

/-- Monic right multiples and the finite right-PBW remainder window are exact
complements.  Equivalently, monic right division is both exhaustive and
unique as a decomposition over the opposite coefficient ring. -/
theorem monicPrincipalRightIdeal_isCompl_rightPBWWindow
    [Nontrivial B] (D : OreDivisionDerivation B)
    (H : Polynomial B) (hH : H.Monic) :
    IsCompl (twoGeneratorCoeffSubmodule D H 0)
      (rightPBWWindow D H.natDegree) := by
  apply IsCompl.of_le
  · intro z hz
    have hzI := hz.1
    have hzW := hz.2
    change z ∈ twoGeneratorRightIdeal D H 0 at hzI
    rw [twoGeneratorRightIdeal, Submodule.mem_span_pair] at hzI
    obtain ⟨a, b, hab⟩ := hzI
    have hzeroTerm : b • normalForm D (0 : Polynomial B) = 0 := by
      rw [normalForm_zero, smul_zero]
    rw [hzeroTerm, add_zero] at hab
    change normalForm D H * a.unop = z at hab
    obtain ⟨q, hq⟩ := normalForm_surjective D a.unop
    obtain ⟨r, hrsmall, hrz⟩ :=
      exists_lowDegreePolynomial_eq_of_mem_rightPBWWindow D H.natDegree hzW
    have hdecomp : r = rightMul D H q + 0 := by
      apply normalForm_injective D
      rw [normalForm_add, normalForm_zero, normalForm_mul, add_zero, hq]
      exact hrz.trans hab.symm
    have hzero := (right_division_unique D H r q 0 0 r hH
      hdecomp (by simp [rightMul_zero]) (Or.inl rfl) hrsmall).2
    have hr0 : r = 0 := hzero.symm
    rw [← hrz, hr0, normalForm_zero]
    exact Submodule.zero_mem _
  · intro z hz
    obtain ⟨p, rfl⟩ := normalForm_surjective D z
    obtain ⟨q, r, hdecomp, hrsmall⟩ := right_division_exists D H p hH
    rw [Submodule.mem_sup]
    refine ⟨normalForm D (rightMul D H q),
      normalForm_rightMul_H_mem_twoGeneratorCoeffSubmodule D H 0 q,
      normalForm D r,
      normalForm_mem_rightPBWWindow_of_degree_lt D r H.natDegree hrsmall,
      ?_⟩
    rw [← normalForm_add, ← hdecomp]

/-- The basis of the finite right-PBW remainder window. -/
def rightPBWWindowBasis [Nontrivial B]
    (D : OreDivisionDerivation B) (N : ℕ) :
    Basis (Fin N) Bᵐᵒᵖ (rightPBWWindow D N) :=
  Basis.span ((rightOrePBW_linearIndependent D).comp
    (fun j : Fin N ↦ (j : ℕ)) Fin.val_injective)

/-- A monic principal right quotient of a derivation-Ore extension is free of
rank `H.natDegree` over the opposite coefficient ring, with basis represented
by `1, X, …, X^(H.natDegree-1)`.  The `0` second generator is only a literal
encoding of the principal right ideal inside the existing quotient API. -/
def monicPrincipalRightQuotientBasis [Nontrivial B]
    (D : OreDivisionDerivation B) (H : Polynomial B) (hH : H.Monic) :
    Basis (Fin H.natDegree) Bᵐᵒᵖ (TwoGeneratorQuotient D H 0) :=
  (rightPBWWindowBasis D H.natDegree).map
    (Submodule.quotientEquivOfIsCompl
      (twoGeneratorCoeffSubmodule D H 0)
      (rightPBWWindow D H.natDegree)
      (monicPrincipalRightIdeal_isCompl_rightPBWWindow D H hH)).symm

@[simp]
theorem monicPrincipalRightQuotientBasis_apply [Nontrivial B]
    (D : OreDivisionDerivation B) (H : Polynomial B) (hH : H.Monic)
    (j : Fin H.natDegree) :
    monicPrincipalRightQuotientBasis D H hH j =
      Submodule.Quotient.mk (normalForm D (Polynomial.X ^ (j : ℕ))) := by
  rw [monicPrincipalRightQuotientBasis, Basis.map_apply,
    Submodule.quotientEquivOfIsCompl_symm_apply]
  congr 1
  change (((rightPBWWindowBasis D H.natDegree) j :
    rightPBWWindow D H.natDegree) : NormalOre D) =
      normalForm D (Polynomial.X ^ (j : ℕ))
  exact congrArg Subtype.val
    (Basis.span_apply ((rightOrePBW_linearIndependent D).comp
      (fun j : Fin H.natDegree ↦ (j : ℕ)) Fin.val_injective) j)


end
end AlgebraicAnalysis.OreRightPBW
