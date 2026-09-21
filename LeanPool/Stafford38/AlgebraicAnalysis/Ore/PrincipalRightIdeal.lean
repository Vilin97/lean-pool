/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.RightQuotient

/-!
# Principal right ideals in a derivation Ore normal form

This module isolates the generic minimal-degree and right-principal-ideal
arguments for a derivation Ore extension over a division ring.  The
coefficient ring may be noncommutative.  The right-sided orientation is
explicit: division has the divisor on the left and the quotient on the right.

No simplicity, localization, or left-PID statement is asserted here.
-/

namespace AlgebraicAnalysis.OrePrincipalRightIdeal

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity

noncomputable section

variable {B : Type*} [DivisionRing B]

lemma rightMul_C_left (D : OreDivisionDerivation B) (c : B) (p : Polynomial B) :
    OreDivision.rightMul D (Polynomial.C c) p = Polynomial.C c * p := by
  apply Polynomial.ext
  intro n
  rw [OreDivision.rightMul, Polynomial.coeff_sum]
  rw [Polynomial.sum_def]
  by_cases hc : c = 0
  · subst c
    simp [OreDivision.rightMulMonomial_coeff]
  · simp only [OreDivision.rightMulMonomial_coeff]
    rw [Polynomial.support_C hc]
    simp [hc]

lemma rightMul_coeff_C_top (D : OreDivisionDerivation B) (p : Polynomial B)
    (b : B) (hp : p ≠ 0) :
    (OreDivision.rightMul D p (Polynomial.C b)).coeff p.natDegree =
      p.leadingCoeff * b := by
  rw [OreDivision.rightMul, Polynomial.coeff_sum]
  rw [Polynomial.sum_def]
  by_cases hb : b = 0
  · subst b
    simp
  · rw [Polynomial.support_C hb]
    simp
    exact OreDivision.rightMulMonomial_coeff_top D p hp b 0

lemma degree_lt_of_degree_le_of_coeff_zero
    (p : Polynomial B) (n : ℕ) (hdeg : p.degree ≤ (n : WithBot ℕ))
    (hcoef : p.coeff n = 0) :
    p.degree < (n : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hnm
  by_cases hmn : m = n
  · simpa [hmn] using hcoef
  · have hnm' : n < m := lt_of_le_of_ne hnm (Ne.symm hmn)
    apply Polynomial.coeff_eq_zero_of_degree_lt
    exact lt_of_le_of_lt hdeg (WithBot.coe_lt_coe.mpr hnm')

/-- A monic minimum-degree member of a two-sided ideal commutes with every
coefficient.  This is a minimal-degree reduction, not a simplicity theorem. -/
theorem minimal_monic_member_commutes_coefficients
    (D : OreDivisionDerivation B) (I : TwoSidedIdeal (NormalOre D))
    (p : Polynomial B) (hp : p.Monic) (hpI : normalForm D p ∈ I)
    (hmin : ∀ q : Polynomial B, q ≠ 0 → normalForm D q ∈ I →
      p.natDegree ≤ q.natDegree) (b : B) :
    OreDivision.rightMul D p (Polynomial.C b) =
      OreDivision.rightMul D (Polynomial.C b) p := by
  let q := OreDivision.rightMul D p (Polynomial.C b) -
    OreDivision.rightMul D (Polynomial.C b) p
  have hqI : normalForm D q ∈ I := by
    have hright : normalForm D (OreDivision.rightMul D p (Polynomial.C b)) ∈ I := by
      rw [normalForm_mul]
      exact I.mul_mem_right _ _ hpI
    have hleft : normalForm D (OreDivision.rightMul D (Polynomial.C b) p) ∈ I := by
      rw [normalForm_mul]
      exact I.mul_mem_left _ _ hpI
    change normalForm D
      (OreDivision.rightMul D p (Polynomial.C b) +
        -OreDivision.rightMul D (Polynomial.C b) p) ∈ I
    rw [normalForm_add, normalForm_neg]
    exact I.sub_mem hright hleft
  have hqdeg : q.degree ≤ (p.natDegree : WithBot ℕ) := by
    apply le_trans (degree_sub_le _ _)
    apply max_le
    · have h := OreDivision.rightMul_degree_le D p (Polynomial.C b)
      simpa using h
    · have h := OreDivision.rightMul_degree_le D (Polynomial.C b) p
      simpa using h
  have hqcoef : q.coeff p.natDegree = 0 := by
    dsimp [q]
    rw [Polynomial.coeff_sub, rightMul_coeff_C_top D p b hp.ne_zero,
      rightMul_C_left]
    rw [Polynomial.coeff_C_mul]
    simp [hp.leadingCoeff]
  have hqlt : q.degree < (p.natDegree : WithBot ℕ) :=
    degree_lt_of_degree_le_of_coeff_zero q p.natDegree hqdeg hqcoef
  by_cases hq0 : q = 0
  · exact sub_eq_zero.mp hq0
  · have hnat : p.natDegree ≤ q.natDegree := hmin q hq0 hqI
    have hqdeg' : q.degree = (q.natDegree : WithBot ℕ) :=
      Polynomial.degree_eq_natDegree hq0
    rw [hqdeg'] at hqlt
    have hltNat : q.natDegree < p.natDegree := WithBot.coe_lt_coe.mp hqlt
    exact False.elim ((not_le_of_gt hltNat) hnat)

/-- Every nonzero two-sided ideal has a monic member of minimum normal-form
degree.  The leading coefficient is normalized within the ideal. -/
theorem exists_monic_minimal_member
    (D : OreDivisionDerivation B) (I : TwoSidedIdeal (NormalOre D))
    (hI : ∃ z : NormalOre D, z ∈ I ∧ z ≠ 0) :
    ∃ p : Polynomial B, p.Monic ∧ normalForm D p ∈ I ∧
      ∀ q : Polynomial B, q ≠ 0 → normalForm D q ∈ I →
        p.natDegree ≤ q.natDegree := by
  classical
  obtain ⟨z, hzI, hz0⟩ := hI
  obtain ⟨p, rfl⟩ := normalForm_surjective D z
  have hp0 : p ≠ 0 := by
    intro hp
    apply hz0
    simpa [hp] using (normalForm_zero D)
  let P : ℕ → Prop := fun n => ∃ q : Polynomial B,
    q ≠ 0 ∧ normalForm D q ∈ I ∧ q.natDegree = n
  have hex : ∃ n, P n := ⟨p.natDegree, p, hp0, hzI, rfl⟩
  let n : ℕ := Nat.find hex
  obtain ⟨p₀, hp₀0, hp₀I, hp₀deg⟩ := Nat.find_spec hex
  let c : B := p₀.leadingCoeff⁻¹
  let p' : Polynomial B := Polynomial.C c * p₀
  have hc : c ≠ 0 := by
    dsimp [c]
    exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp₀0)
  have hp'0 : p' ≠ 0 := by
    dsimp [p']
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hp₀0
  have hnat : p'.natDegree = p₀.natDegree := by
    have hdeg : p'.degree = p₀.degree := by
      dsimp [p']
      exact Polynomial.degree_C_mul hc
    rw [Polynomial.degree_eq_natDegree hp'0,
      Polynomial.degree_eq_natDegree hp₀0] at hdeg
    exact WithBot.coe_eq_coe.mp hdeg
  have hp'I : normalForm D p' ∈ I := by
    dsimp [p']
    rw [← rightMul_C_left]
    rw [normalForm_mul]
    exact I.mul_mem_left _ _ hp₀I
  have hp'Monic : p'.Monic := by
    change p'.leadingCoeff = 1
    change p'.coeff p'.natDegree = 1
    rw [hnat,
      Polynomial.coeff_C_mul, Polynomial.coeff_natDegree]
    dsimp [c]
    exact inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp₀0)
  refine ⟨p', hp'Monic, hp'I, ?_⟩
  intro q hq hqI
  have hqn : P q.natDegree := ⟨q, hq, hqI, rfl⟩
  have hnle : n ≤ q.natDegree := Nat.find_min' hex hqn
  calc
    p'.natDegree = p₀.natDegree := hnat
    _ = n := hp₀deg
    _ ≤ q.natDegree := hnle

/-!
The remaining declarations are the right-sided Euclidean/PID stage for a
normal-form differential Ore extension.  They use the same leading-term
argument and make no claim about left ideals.
-/

/-- The right ideal generated by a normal-form polynomial. -/
def normalOrePrincipalRightIdeal (D : OreDivisionDerivation B) (p : Polynomial B) :
    Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D) :=
  Submodule.span (NormalOre D)ᵐᵒᵖ ({normalForm D p} : Set (NormalOre D))

/-- The right ideal generated by an arbitrary element of `NormalOre D`. -/
def normalOrePrincipalRightIdealElement (D : OreDivisionDerivation B)
    (a : NormalOre D) :
    Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D) :=
  Submodule.span (NormalOre D)ᵐᵒᵖ ({a} : Set (NormalOre D))

/-- Right Euclidean division transported from polynomial normal form. -/
theorem normalOre_right_division [Nontrivial B]
    (D : OreDivisionDerivation B) (d : Polynomial B) (hd : d.Monic)
    (a : NormalOre D) :
    ∃ q r : Polynomial B,
      a = normalForm D (OreDivision.rightMul D d q) + normalForm D r ∧
        (r = 0 ∨ r.natDegree < d.natDegree) := by
  obtain ⟨p, rfl⟩ := normalForm_surjective D a
  obtain ⟨q, r, hdiv, hrem⟩ := right_division_exists D d p hd
  refine ⟨q, r, ?_, hrem⟩
  rw [hdiv, normalForm_add]

lemma rightMul_C_degree_eq (D : OreDivisionDerivation B) (p : Polynomial B)
    (c : B) (hp : p ≠ 0) (hc : c ≠ 0) :
    (OreDivision.rightMul D p (Polynomial.C c)).degree = p.degree := by
  have hle := OreDivision.rightMul_degree_le D p (Polynomial.C c)
  have hle' : (OreDivision.rightMul D p (Polynomial.C c)).degree ≤
      (p.natDegree : WithBot ℕ) := by simpa using hle
  have htop : (OreDivision.rightMul D p (Polynomial.C c)).coeff p.natDegree =
      p.leadingCoeff * c := by
    exact rightMul_coeff_C_top D p c hp
  have htop0 : (OreDivision.rightMul D p (Polynomial.C c)).coeff p.natDegree ≠ 0 := by
    rw [htop]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) hc
  have hge : (p.natDegree : WithBot ℕ) ≤
      (OreDivision.rightMul D p (Polynomial.C c)).degree := by
    by_contra hnot
    have hlt : (OreDivision.rightMul D p (Polynomial.C c)).degree <
        (p.natDegree : WithBot ℕ) := lt_of_not_ge hnot
    exact htop0 (Polynomial.coeff_eq_zero_of_degree_lt hlt)
  rw [Polynomial.degree_eq_natDegree hp]
  exact le_antisymm hle' hge

/-- A nonzero right submodule has a monic member of minimum normal-form
degree.  Normalization uses right multiplication by the inverse coefficient. -/
theorem exists_monic_minimal_right_member
    (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D))
    (hI : ∃ z : NormalOre D, z ∈ I ∧ z ≠ 0) :
    ∃ p : Polynomial B, p.Monic ∧ normalForm D p ∈ I ∧
      ∀ q : Polynomial B, q ≠ 0 → normalForm D q ∈ I →
        p.natDegree ≤ q.natDegree := by
  classical
  obtain ⟨z, hzI, hz0⟩ := hI
  obtain ⟨p, rfl⟩ := normalForm_surjective D z
  have hp0 : p ≠ 0 := by
    intro hp
    apply hz0
    simpa [hp] using (normalForm_zero D)
  let P : ℕ → Prop := fun n => ∃ q : Polynomial B,
    q ≠ 0 ∧ normalForm D q ∈ I ∧ q.natDegree = n
  have hex : ∃ n, P n := ⟨p.natDegree, p, hp0, hzI, rfl⟩
  let n : ℕ := Nat.find hex
  obtain ⟨p₀, hp₀0, hp₀I, hp₀deg⟩ := Nat.find_spec hex
  let c : B := p₀.leadingCoeff⁻¹
  let p' : Polynomial B := OreDivision.rightMul D p₀ (Polynomial.C c)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp₀0)
  have hp'0 : p' ≠ 0 := by
    intro hz
    have hz' := congrArg (fun z : Polynomial B => z.coeff p₀.natDegree) hz
    change (OreDivision.rightMul D p₀ (Polynomial.C c)).coeff p₀.natDegree = 0 at hz'
    rw [rightMul_coeff_C_top D p₀ c hp₀0] at hz'
    exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp₀0) hc) hz'
  have hdeg : p'.degree = p₀.degree := by
    dsimp [p']
    exact rightMul_C_degree_eq D p₀ c hp₀0 hc
  have hnat : p'.natDegree = p₀.natDegree := by
    rw [Polynomial.degree_eq_natDegree hp'0,
      Polynomial.degree_eq_natDegree hp₀0] at hdeg
    exact WithBot.coe_eq_coe.mp hdeg
  have hp'I : normalForm D p' ∈ I := by
    dsimp [p']
    rw [normalForm_mul]
    rw [← op_smul_eq_mul]
    exact I.smul_mem (MulOpposite.op (normalForm D (Polynomial.C c))) hp₀I
  have hp'Monic : p'.Monic := by
    change p'.leadingCoeff = 1
    change p'.coeff p'.natDegree = 1
    have htop := rightMul_coeff_C_top D p₀ c hp₀0
    rw [hnat]
    dsimp [p']
    rw [htop]
    dsimp [c]
    exact mul_inv_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hp₀0)
  refine ⟨p', hp'Monic, hp'I, ?_⟩
  intro q hq hqI
  have hqn : P q.natDegree := ⟨q, hq, hqI, rfl⟩
  have hnle : n ≤ q.natDegree := Nat.find_min' hex hqn
  calc
    p'.natDegree = p₀.natDegree := hnat
    _ = n := hp₀deg
    _ ≤ q.natDegree := hnle

/-- Every nonzero right ideal is generated by one monic normal-form element.
The ideal equality is on the right: `I = p (NormalOre D)`. -/
theorem rightIdeal_eq_principal_of_nonzero
    (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D))
    (hI : ∃ z : NormalOre D, z ∈ I ∧ z ≠ 0) :
    ∃ p : Polynomial B, p.Monic ∧
      I = normalOrePrincipalRightIdeal D p := by
  obtain ⟨p, hp, hpI, hmin⟩ := exists_monic_minimal_right_member D I hI
  refine ⟨p, hp, ?_⟩
  apply le_antisymm
  · intro z hz
    change z ∈ Submodule.span (NormalOre D)ᵐᵒᵖ
      ({normalForm D p} : Set (NormalOre D))
    obtain ⟨q, rfl⟩ := normalForm_surjective D z
    obtain ⟨u, r, hdecomp, hrem⟩ := right_division_exists D p q hp
    have hprod : normalForm D (OreDivision.rightMul D p u) ∈ I := by
      rw [normalForm_mul]
      rw [← op_smul_eq_mul]
      exact I.smul_mem (MulOpposite.op (normalForm D u)) hpI
    have hrI : normalForm D r ∈ I := by
      have hqeq : normalForm D q =
          normalForm D (OreDivision.rightMul D p u) + normalForm D r := by
        rw [← normalForm_add, ← hdecomp]
      have hsub := I.sub_mem hz hprod
      rw [hqeq] at hsub
      simpa using hsub
    have hr0 : r = 0 := by
      by_cases hr : r = 0
      · exact hr
      · have hlt := hrem.resolve_left hr
        have hcontr := hmin r hr hrI
        exact False.elim ((Nat.not_lt_of_ge hcontr) hlt)
    subst r
    rw [hdecomp, add_zero, normalForm_mul]
    rw [← op_smul_eq_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.2
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hpI

/-- Every right ideal of `NormalOre D` is principal, including the zero ideal.
This is a one-sided PID statement; no left-PID claim is made. -/
theorem rightIdeal_isPrincipal
    (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) :
    ∃ a : NormalOre D, I = normalOrePrincipalRightIdealElement D a := by
  by_cases hI : ∃ z : NormalOre D, z ∈ I ∧ z ≠ 0
  · obtain ⟨p, hp, hEq⟩ := rightIdeal_eq_principal_of_nonzero D I hI
    exact ⟨normalForm D p, hEq⟩
  · have hbot : I = ⊥ := by
      apply le_antisymm
      · intro z hz
        by_contra hz0
        exact hI ⟨z, hz, hz0⟩
      · exact bot_le
    have hzero : normalOrePrincipalRightIdealElement D (0 : NormalOre D) = ⊥ := by
      apply le_antisymm
      · apply Submodule.span_le.2
        intro z hz
        simpa using hz
      · exact bot_le
    refine ⟨0, ?_⟩
    rw [hbot, hzero]


end

end AlgebraicAnalysis.OrePrincipalRightIdeal
