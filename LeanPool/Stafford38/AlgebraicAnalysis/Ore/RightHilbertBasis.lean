/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.RightQuotient
import Mathlib.RingTheory.Noetherian.Filter

/-!
# The derivation-Ore right Hilbert-basis theorem

This file is a right-sided version of the leading-coefficient proof for a
differential Ore extension.  Coefficients are allowed to be noncommutative:
right ideals of the coefficient ring are represented as submodules for the
opposite scalar ring.
-/

namespace AlgebraicAnalysis.OreDerivationRightHilbertBasis

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open AlgebraicAnalysis.OreRightQuotient

noncomputable section

universe u

variable {B : Type u} [Ring B]

/-- The right Hilbert-basis assertion for one derivation-Ore stage. -/
def DerivationOreRightHilbertBasis : Prop :=
  ∀ {B : Type u} [Ring B], IsNoetherianRing Bᵐᵒᵖ →
    ∀ D : OreDivisionDerivation B,
      IsNoetherianRing (NormalOre D)ᵐᵒᵖ

@[simp] theorem rightScalar_smul_def (b : Bᵐᵒᵖ) (c : B) :
    b • c = c * b.unop := by
  rw [MulOpposite.smul_eq_mul_unop]

private theorem rightScalar_top_span :
    Submodule.span Bᵐᵒᵖ ({1} : Set B) = ⊤ := by
  apply top_unique
  intro c hc
  have h1 : (1 : B) ∈ Submodule.span Bᵐᵒᵖ ({1} : Set B) :=
    Submodule.subset_span (by simp)
  have hc' := Submodule.smul_mem
    (Submodule.span Bᵐᵒᵖ ({1} : Set B)) (MulOpposite.op c) h1
  simpa [rightScalar_smul_def] using hc'

private theorem rightScalar_module_finite : Module.Finite Bᵐᵒᵖ B := by
  refine ⟨?_⟩
  refine ⟨({1} : Finset B), ?_⟩
  change Submodule.span Bᵐᵒᵖ (({1} : Finset B) : Set B) = ⊤
  simpa only [Finset.coe_singleton] using
    (rightScalar_top_span (B := B))

private theorem rightScalar_isNoetherian
    [IsNoetherianRing Bᵐᵒᵖ] : IsNoetherian Bᵐᵒᵖ B := by
  letI : Module.Finite Bᵐᵒᵖ B := rightScalar_module_finite
  exact isNoetherian_of_isNoetherianRing_of_finite Bᵐᵒᵖ B

/-- Additive equivalence between coefficient-left polynomials and normal forms. -/
def normalPolyEquiv (D : OreDivisionDerivation B) :
    Polynomial B ≃+ NormalOre D :=
  { normalFormAddEquiv D with }

lemma rightMul_coeff_C_of_degree_le
    (D : OreDivisionDerivation B) (p : Polynomial B) (b : B) (n : ℕ)
    (hp : p.degree ≤ (n : WithBot ℕ)) :
    (rightMul D p (Polynomial.C b)).coeff n = p.coeff n * b := by
  by_cases hp0 : p = 0
  · subst p
    simp [OreDivision.rightMul, OreDivision.rightMulMonomial,
      OreDivision.rightTerm]
  have hpnat : p.natDegree ≤ n :=
    Polynomial.natDegree_le_of_degree_le hp
  by_cases heq : p.natDegree = n
  · rw [show Polynomial.C b = Polynomial.monomial 0 b by simp,
      rightMul_monomial]
    have htop := rightMulMonomial_coeff_top D p hp0 b 0
    rw [Nat.add_zero] at htop
    simpa [Polynomial.leadingCoeff, heq] using htop
  · have hlt : p.natDegree < n := lt_of_le_of_ne hpnat heq
    have hprod : (rightMul D p (Polynomial.C b)).degree <
        (n : WithBot ℕ) := by
      have hle := rightMul_degree_le D p (Polynomial.C b)
      have hnatC : (Polynomial.C b).natDegree = 0 := by simp
      rw [hnatC] at hle
      have hle' : (rightMul D p (Polynomial.C b)).degree ≤
          (p.natDegree : WithBot ℕ) := by simpa using hle
      exact lt_of_le_of_lt hle' (WithBot.coe_lt_coe.2 hlt)
    have hzprod := Polynomial.coeff_eq_zero_of_degree_lt hprod
    have hz : p.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      rw [Polynomial.degree_eq_natDegree hp0]
      exact WithBot.coe_lt_coe.2 hlt
    simp [hzprod, hz]

/-- The degree-at-most-`n` submodule of normal forms. -/
def normalDegreeLE (D : OreDivisionDerivation B) (n : ℕ) :
    Submodule Bᵐᵒᵖ (NormalOre D) :=
  { carrier := {z | ((normalPolyEquiv D).symm z).degree ≤ (n : WithBot ℕ)}
    zero_mem' := by
      change ((normalPolyEquiv D).symm (0 : NormalOre D)).degree ≤ _
      rw [(normalPolyEquiv D).symm.map_zero]
      simp
    add_mem' := by
      intro x y hx hy
      change ((normalPolyEquiv D).symm (x + y)).degree ≤ _
      rw [(normalPolyEquiv D).symm.map_add]
      exact le_trans (Polynomial.degree_add_le _ _) (max_le hx hy)
    smul_mem' := by
      intro b z hz
      obtain ⟨p, rfl⟩ := normalForm_surjective D z
      change ((normalPolyEquiv D).symm (b • normalForm D p)).degree ≤ _
      change ((normalPolyEquiv D).symm ((normalPolyEquiv D) p)).degree ≤ _ at hz
      rw [(normalPolyEquiv D).symm_apply_apply] at hz
      have hpdeg : p.degree ≤ (n : WithBot ℕ) := hz
      have hpnat : p.natDegree ≤ n :=
        Polynomial.natDegree_le_of_degree_le hpdeg
      have hmul : b • normalForm D p =
          normalForm D (rightMul D p (Polynomial.C b.unop)) := by
        rw [normalOre_op_smul_def, ← normalForm_C, ← normalForm_mul]
      rw [hmul]
      change ((normalPolyEquiv D).symm
        ((normalPolyEquiv D) (rightMul D p (Polynomial.C b.unop)))).degree ≤ _
      rw [(normalPolyEquiv D).symm_apply_apply]
      exact (rightMul_degree_le D p (Polynomial.C b.unop)).trans
        (by
          simp only [Polynomial.natDegree_C, Nat.cast_zero, add_zero]
          exact_mod_cast hpnat) }

/-- The `n`th coefficient functional on the degree window. -/
def normalCoeffNth (D : OreDivisionDerivation B) (n : ℕ) :
    normalDegreeLE D n →ₗ[Bᵐᵒᵖ] B where
  toFun z := ((normalPolyEquiv D).symm z).coeff n
  map_add' x y := by
    change ((normalPolyEquiv D).symm (x + y)).coeff n = _
    rw [(normalPolyEquiv D).symm.map_add, Polynomial.coeff_add]
  map_smul' b z := by
    let p := (normalPolyEquiv D).symm z.1
    have hp : p.degree ≤ (n : WithBot ℕ) := by
      change ((normalPolyEquiv D).symm z.1).degree ≤ _
      exact z.2
    have hz : normalForm D p = z.1 := by
      change (normalPolyEquiv D) p = z.1
      exact (normalPolyEquiv D).apply_symm_apply z.1
    change ((normalPolyEquiv D).symm (b • z.1)).coeff n =
      b • ((normalPolyEquiv D).symm z.1).coeff n
    rw [← hz]
    rw [normalOre_op_smul_def, ← normalForm_C, ← normalForm_mul]
    change ((normalPolyEquiv D).symm
        ((normalPolyEquiv D) (rightMul D p (Polynomial.C b.unop)))).coeff n =
      b • ((normalPolyEquiv D).symm ((normalPolyEquiv D) p)).coeff n
    rw [(normalPolyEquiv D).symm_apply_apply,
      (normalPolyEquiv D).symm_apply_apply]
    rw [rightMul_coeff_C_of_degree_le D p b.unop n hp]
    rfl

/-- The degree window cut out by a right ideal. -/
def rightIdealDegreeLE (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) (n : ℕ) :
    Submodule Bᵐᵒᵖ (NormalOre D) :=
  normalDegreeLE D n ⊓ rightIdealAsCoeffSubmodule D I

/-- The leading-coefficient submodule at a fixed degree. -/
def leadingCoeffNth (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) (n : ℕ) :
    Submodule Bᵐᵒᵖ B :=
  let J := rightIdealDegreeLE D I n
  let incl : J →ₗ[Bᵐᵒᵖ] normalDegreeLE D n :=
    { toFun := fun z => ⟨z.1, z.2.1⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro b x; rfl }
  let f : J →ₗ[Bᵐᵒᵖ] B := (normalCoeffNth D n).comp incl
  Submodule.map f (⊤ : Submodule Bᵐᵒᵖ J)

lemma mem_leadingCoeffNth (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) (n : ℕ) (c : B) :
    c ∈ leadingCoeffNth D I n ↔
      ∃ p : Polynomial B, normalForm D p ∈ I ∧
        p.degree ≤ (n : WithBot ℕ) ∧ p.coeff n = c := by
  constructor
  · intro hc
    change c ∈ Submodule.map _ (⊤ : Submodule Bᵐᵒᵖ (rightIdealDegreeLE D I n)) at hc
    rw [Submodule.mem_map] at hc
    rcases hc with ⟨z, hz, rfl⟩
    let p := (normalPolyEquiv D).symm z.1
    refine ⟨p, ?_, ?_, ?_⟩
    · change normalForm D p ∈ I
      have hpz : normalForm D p = z.1 := by
        change (normalPolyEquiv D) p = z.1
        exact (normalPolyEquiv D).apply_symm_apply z.1
      rw [hpz]
      simpa [rightIdealAsCoeffSubmodule] using z.2.2
    · change p.degree ≤ (n : WithBot ℕ)
      exact z.2.1
    · change ((normalPolyEquiv D).symm z.1).coeff n = _
      rfl
  · rintro ⟨p, hpI, hpdeg, hpc⟩
    let z : rightIdealDegreeLE D I n :=
      ⟨normalForm D p, (by
        change ((normalPolyEquiv D).symm ((normalPolyEquiv D) p)).degree ≤ _
        rw [(normalPolyEquiv D).symm_apply_apply]
        exact hpdeg), hpI⟩
    refine ⟨z, Submodule.mem_top, ?_⟩
    dsimp [z, normalCoeffNth]
    have hinv : (normalPolyEquiv D).symm (normalForm D p) = p := by
      change (normalPolyEquiv D).symm ((normalPolyEquiv D) p) = p
      exact (normalPolyEquiv D).symm_apply_apply p
    rw [hinv]
    exact hpc

lemma rightMul_Xpow_coeff_of_degree_le
    [Nontrivial B]
    (D : OreDivisionDerivation B) (p : Polynomial B) (n j : ℕ)
    (hp : p.degree ≤ (n : WithBot ℕ)) :
    (rightMul D p (Polynomial.X ^ j)).coeff (n + j) = p.coeff n := by
  by_cases hp0 : p = 0
  · subst p
    simp [OreDivision.rightMul, OreDivision.rightMulMonomial,
      OreDivision.rightTerm, Polynomial.sum_def]
  have hpnat : p.natDegree ≤ n :=
    Polynomial.natDegree_le_of_degree_le hp
  by_cases heq : p.natDegree = n
  · rw [Polynomial.X_pow_eq_monomial, rightMul_monomial]
    have htop := rightMulMonomial_coeff_top D p hp0 1 j
    simpa [Polynomial.leadingCoeff, heq] using htop
  · have hlt : p.natDegree < n := lt_of_le_of_ne hpnat heq
    have hprod : (rightMul D p (Polynomial.X ^ j)).degree <
        ((n + j : ℕ) : WithBot ℕ) := by
      have hle := rightMul_degree_le D p (Polynomial.X ^ j)
      have hnatX : (Polynomial.X ^ j : Polynomial B).natDegree = j := by
        simp
      rw [hnatX] at hle
      have hlt' : p.natDegree + j < n + j := Nat.add_lt_add_right hlt j
      exact lt_of_le_of_lt hle (WithBot.coe_lt_coe.2 hlt')
    have hzprod := Polynomial.coeff_eq_zero_of_degree_lt hprod
    have hz : p.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_degree_lt
      rw [Polynomial.degree_eq_natDegree hp0]
      exact WithBot.coe_lt_coe.2 hlt
    simp [hzprod, hz]

lemma leadingCoeffNth_mono [Nontrivial B] (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D))
    {m n : ℕ} (hmn : m ≤ n) :
    leadingCoeffNth D I m ≤ leadingCoeffNth D I n := by
  intro c hc
  rw [mem_leadingCoeffNth] at hc ⊢
  rcases hc with ⟨p, hpI, hpdeg, hpc⟩
  refine ⟨rightMul D p (Polynomial.X ^ (n - m)), ?_, ?_, ?_⟩
  · rw [normalForm_mul]
    have hmem := I.smul_mem
      (MulOpposite.op (normalForm D (Polynomial.X ^ (n - m)))) hpI
    simpa [op_smul_eq_mul] using hmem
  · have hpnat : p.natDegree ≤ m :=
      Polynomial.natDegree_le_of_degree_le hpdeg
    have hdeg := rightMul_degree_le D p (Polynomial.X ^ (n - m))
    have hnat : (Polynomial.X ^ (n - m) : Polynomial B).natDegree = n - m :=
      Polynomial.natDegree_X_pow _
    rw [hnat] at hdeg
    have hadd : p.natDegree + (n - m) ≤ n := by
      exact (Nat.add_le_add_right hpnat (n - m)).trans_eq
        (Nat.add_sub_of_le hmn)
    exact hdeg.trans (by exact_mod_cast hadd)
  · have hc' := rightMul_Xpow_coeff_of_degree_le D p m (n - m) hpdeg
    rw [Nat.add_sub_of_le hmn] at hc'
    exact hc'.trans hpc

/-- The monotone chain of leading-coefficient submodules. -/
def leadingCoeffChain [Nontrivial B] (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) :
    ℕ →o Submodule Bᵐᵒᵖ B where
  toFun n := leadingCoeffNth D I n
  monotone' _m _n h := leadingCoeffNth_mono D I h

theorem exists_leadingCoeff_stable
    [Nontrivial B]
    [IsNoetherianRing Bᵐᵒᵖ]
    (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) :
    ∃ N : ℕ, ∀ n, N ≤ n → leadingCoeffNth D I n = leadingCoeffNth D I N := by
  letI : IsNoetherian Bᵐᵒᵖ B := rightScalar_isNoetherian
  let f := leadingCoeffChain D I
  have hconst : Filter.EventuallyConst
      (f : ℕ → Submodule Bᵐᵒᵖ B) Filter.atTop :=
    eventuallyConst_of_isNoetherian f
  rcases Filter.eventuallyConst_atTop.mp hconst with ⟨N, hN⟩
  exact ⟨N, fun n hn => hN n hn⟩

lemma normalDegreeLE_le_window (D : OreDivisionDerivation B) (n : ℕ) :
    normalDegreeLE D n ≤ rightCoefficientWindow D (n + 1) := by
  intro z hz
  let p := (normalPolyEquiv D).symm z
  have hpdeg : p.degree ≤ (n : WithBot ℕ) := by
    change ((normalPolyEquiv D).symm z).degree ≤ _
    exact hz
  have hp : p = 0 ∨ p.natDegree < n + 1 := by
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · right
      have hpnat : p.natDegree ≤ n :=
        Polynomial.natDegree_le_of_degree_le hpdeg
      omega
  have hw := normalForm_mem_rightCoefficientWindow_of_degree_lt
    D p (n + 1) hp
  have hzval : normalForm D p = z := by
    change (normalPolyEquiv D) p = z
    exact (normalPolyEquiv D).apply_symm_apply z
  rw [← hzval]
  exact hw

/-- The degree window embedded in the finite coefficient window. -/
def normalDegreeLEToWindow (D : OreDivisionDerivation B) (n : ℕ) :
    normalDegreeLE D n →ₗ[Bᵐᵒᵖ] rightCoefficientWindow D (n + 1) where
  toFun z := ⟨z.1, normalDegreeLE_le_window D n z.2⟩
  map_add' x y := by rfl
  map_smul' b x := by rfl

/-- Inclusion of an ideal degree window into the full degree window. -/
def normalDegreeIncl (D : OreDivisionDerivation B) (n : ℕ)
    (J : Submodule Bᵐᵒᵖ (NormalOre D))
    (hJ : J ≤ normalDegreeLE D n) :
    J →ₗ[Bᵐᵒᵖ] normalDegreeLE D n where
  toFun z := ⟨z.1, hJ z.2⟩
  map_add' x y := by rfl
  map_smul' b x := by rfl

theorem rightIdealDegreeLE_fg
    [IsNoetherianRing Bᵐᵒᵖ]
    (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) (n : ℕ) :
    (rightIdealDegreeLE D I n).FG := by
  letI : Module.Finite Bᵐᵒᵖ (rightCoefficientWindow D (n + 1)) :=
    Module.Finite.span_of_finite Bᵐᵒᵖ (Set.finite_range
      (fun j : Fin (n + 1) => normalForm D (Polynomial.X ^ (j : ℕ))))
  letI : IsNoetherian Bᵐᵒᵖ (rightCoefficientWindow D (n + 1)) :=
    isNoetherian_of_isNoetherianRing_of_finite Bᵐᵒᵖ
      (rightCoefficientWindow D (n + 1))
  letI : Module.Finite Bᵐᵒᵖ (normalDegreeLE D n) :=
    Module.Finite.of_injective
      (normalDegreeLEToWindow D n) (by
        intro x y h
        apply Subtype.ext
        exact congrArg
          (fun z : rightCoefficientWindow D (n + 1) => (z : NormalOre D)) h)
  letI : IsNoetherian Bᵐᵒᵖ (normalDegreeLE D n) :=
    isNoetherian_of_isNoetherianRing_of_finite Bᵐᵒᵖ
      (normalDegreeLE D n)
  let incl := normalDegreeIncl D n (rightIdealDegreeLE D I n) inf_le_left
  letI : Module.Finite Bᵐᵒᵖ (rightIdealDegreeLE D I n) :=
    Module.Finite.of_injective incl (by
      intro x y h
      apply Subtype.ext
      exact congrArg
        (fun z : normalDegreeLE D n => (z : NormalOre D)) h)
  have htop : (⊤ : Submodule Bᵐᵒᵖ (rightIdealDegreeLE D I n)).FG :=
    Module.finite_def.mp (inferInstance :
      Module.Finite Bᵐᵒᵖ (rightIdealDegreeLE D I n))
  exact (Submodule.fg_top (rightIdealDegreeLE D I n)).mp htop

theorem normalOre_rightIdeal_fg_of_op_noetherian
    [Nontrivial B] [IsNoetherianRing Bᵐᵒᵖ]
    (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) : I.FG := by
  obtain ⟨N, hstable⟩ := exists_leadingCoeff_stable D I
  obtain ⟨s, hs⟩ := rightIdealDegreeLE_fg D I N
  let K : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D) :=
    Submodule.span (NormalOre D)ᵐᵒᵖ (s : Set (NormalOre D))
  have hKsub : K ≤ I := by
    apply Submodule.span_le.2
    intro z hz
    have hzJ : z ∈ rightIdealDegreeLE D I N := by
      rw [← hs]
      exact Submodule.subset_span hz
    exact hzJ.2
  refine ⟨s, ?_⟩
  apply le_antisymm hKsub
  intro z hz
  obtain ⟨p, rfl⟩ := normalForm_surjective D z
  have hBspan_le :
      Submodule.span Bᵐᵒᵖ (s : Set (NormalOre D)) ≤
        rightIdealAsCoeffSubmodule D K := by
    apply Submodule.span_le.2
    intro x hx
    exact Submodule.subset_span hx
  have hgen : ∀ n : ℕ, ∀ p : Polynomial B,
      p.natDegree = n → normalForm D p ∈ I → normalForm D p ∈ K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hpn hpI
      by_cases hp0 : p = 0
      · subst p
        simp [normalForm_zero]
      by_cases hsmall : p.natDegree ≤ N
      · have hpdeg : p.degree ≤ (N : WithBot ℕ) := by
          rw [Polynomial.degree_eq_natDegree hp0]
          exact WithBot.coe_le_coe.2 hsmall
        have hnormalP : normalForm D p ∈ normalDegreeLE D N := by
          have hinv : (normalPolyEquiv D).symm (normalForm D p) = p := by
            change (normalPolyEquiv D).symm ((normalPolyEquiv D) p) = p
            exact (normalPolyEquiv D).symm_apply_apply p
          change ((normalPolyEquiv D).symm (normalForm D p)).degree ≤
            (N : WithBot ℕ)
          rw [hinv]
          exact hpdeg
        have hpJ : normalForm D p ∈ rightIdealDegreeLE D I N :=
          ⟨hnormalP, hpI⟩
        have hpB : normalForm D p ∈
            Submodule.span Bᵐᵒᵖ (s : Set (NormalOre D)) := by
          rw [hs]
          exact hpJ
        exact hBspan_le hpB
      · have hlarge : N < p.natDegree := lt_of_not_ge hsmall
        let c := p.leadingCoeff
        have hcne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
        have hpc : p.coeff n = c := by
          dsimp [c]
          rw [Polynomial.leadingCoeff, hpn]
        have hcN : c ∈ leadingCoeffNth D I N := by
          rw [← hstable p.natDegree (le_of_lt hlarge)]
          rw [mem_leadingCoeffNth]
          refine ⟨p, hpI, ?_, ?_⟩
          · exact Polynomial.degree_le_natDegree
          · dsimp [c]
        rcases (mem_leadingCoeffNth D I N c).mp hcN with
          ⟨q, hqI, hqdeg, hqcoeff⟩
        let u := rightMul D q (Polynomial.X ^ (n - N))
        have huI : normalForm D u ∈ I := by
          rw [normalForm_mul]
          have hmem := I.smul_mem
            (MulOpposite.op (normalForm D (Polynomial.X ^ (n - N)))) hqI
          simpa [u, op_smul_eq_mul] using hmem
        have huK : normalForm D u ∈ K := by
          have hnormalQ : normalForm D q ∈ normalDegreeLE D N := by
            have hinv : (normalPolyEquiv D).symm (normalForm D q) = q := by
              change (normalPolyEquiv D).symm ((normalPolyEquiv D) q) = q
              exact (normalPolyEquiv D).symm_apply_apply q
            change ((normalPolyEquiv D).symm (normalForm D q)).degree ≤
              (N : WithBot ℕ)
            rw [hinv]
            exact hqdeg
          have hqJ : normalForm D q ∈ rightIdealDegreeLE D I N :=
            ⟨hnormalQ, hqI⟩
          have hqB : normalForm D q ∈
              Submodule.span Bᵐᵒᵖ (s : Set (NormalOre D)) := by
            rw [hs]
            exact hqJ
          have hmulK := K.smul_mem
            (MulOpposite.op (normalForm D (Polynomial.X ^ (n - N))))
            (hBspan_le hqB)
          simpa [u, normalForm_mul, op_smul_eq_mul] using hmulK
        have hucoeff : u.coeff n = c := by
          dsimp [u]
          have hqcoeff' :=
            rightMul_Xpow_coeff_of_degree_le D q N (n - N) hqdeg
          have hNn : N ≤ n := hpn ▸ le_of_lt hlarge
          rw [Nat.add_sub_of_le hNn] at hqcoeff'
          rw [hqcoeff']
          exact hqcoeff
        have hu0 : u ≠ 0 := by
          intro hu
          have hthis : u.coeff n = (0 : Polynomial B).coeff n := by
            simpa using congrArg (fun r : Polynomial B => r.coeff n) hu
          rw [hucoeff] at hthis
          exact hcne (by simpa using hthis)
        have hule : u.degree ≤ (n : WithBot ℕ) := by
          dsimp [u]
          have hdeg := rightMul_degree_le D q (Polynomial.X ^ (n - N))
          have hqnat : q.natDegree ≤ N :=
            Polynomial.natDegree_le_of_degree_le hqdeg
          have hnatX : (Polynomial.X ^ (n - N) : Polynomial B).natDegree =
              n - N := Polynomial.natDegree_X_pow _
          rw [hnatX] at hdeg
          have hadd : q.natDegree + (n - N) ≤ n := by
            exact (Nat.add_le_add_right hqnat (n - N)).trans_eq
              (Nat.add_sub_of_le (hpn ▸ le_of_lt hlarge))
          exact hdeg.trans (by exact_mod_cast hadd)
        have hun : u.natDegree = n := by
          apply le_antisymm
          · exact Polynomial.natDegree_le_of_degree_le hule
          · apply Polynomial.le_natDegree_of_mem_supp
            rw [Polynomial.mem_support_iff]
            exact hucoeff.trans_ne hcne
        have hudeg : u.degree = (n : WithBot ℕ) := by
          rw [Polynomial.degree_eq_natDegree hu0, hun]
        have hpdeg : p.degree = (n : WithBot ℕ) := by
          rw [Polynomial.degree_eq_natDegree hp0, hpn]
        have hplead : p.leadingCoeff = u.leadingCoeff := by
          rw [Polynomial.leadingCoeff, hpn,
            Polynomial.leadingCoeff, hun, hpc, hucoeff]
        let r := p - u
        have hrI : normalForm D r ∈ I := by
          dsimp [r]
          rw [show normalForm D (p - u) =
              normalForm D p - normalForm D u from
            map_sub (normalFormAddHom D) p u]
          exact I.sub_mem hpI huI
        have hrdeg : r.degree < (n : WithBot ℕ) := by
          dsimp [r]
          have hsub := Polynomial.degree_sub_lt (hpdeg.trans hudeg.symm) hp0 hplead
          simpa [hpdeg] using hsub
        by_cases hr0 : r = 0
        · have hpr : p = u := sub_eq_zero.mp hr0
          rw [hpr]
          exact huK
        · have hrnat : r.natDegree < n := by
            have hrdeg' : (r.natDegree : WithBot ℕ) <
                (n : WithBot ℕ) := by
              rw [Polynomial.degree_eq_natDegree hr0] at hrdeg
              exact hrdeg
            exact WithBot.coe_lt_coe.mp hrdeg'
          have hrK := ih r.natDegree hrnat r rfl hrI
          have huK' := huK
          change normalForm D p ∈ K
          rw [show p = u + r by dsimp [r]; abel, normalForm_add]
          exact K.add_mem huK' hrK
  exact hgen p.natDegree p rfl hz

theorem normalOre_op_isNoetherian_of_nontrivial
    [Nontrivial B] [IsNoetherianRing Bᵐᵒᵖ]
    (D : OreDivisionDerivation B) :
    IsNoetherianRing (NormalOre D)ᵐᵒᵖ := by
  refine ⟨?_⟩
  intro J
  let e : NormalOre D ≃ₗ[(NormalOre D)ᵐᵒᵖ] (NormalOre D)ᵐᵒᵖ :=
    MulOpposite.opLinearEquiv (NormalOre D)ᵐᵒᵖ
  let I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D) :=
    J.comap e.toLinearMap
  have hI : I.FG := normalOre_rightIdeal_fg_of_op_noetherian D I
  have hmap : I.map e.toLinearMap = J := by
    exact Submodule.map_comap_eq_of_surjective e.surjective J
  rw [← hmap]
  exact hI.map e.toLinearMap

theorem normalOre_op_isNoetherian_of_subsingleton
    [Subsingleton B] (D : OreDivisionDerivation B) :
    IsNoetherianRing (NormalOre D)ᵐᵒᵖ := by
  letI : Subsingleton (NormalOre D) :=
    ⟨fun x y => by
      obtain ⟨p, rfl⟩ := normalForm_surjective D x
      obtain ⟨q, rfl⟩ := normalForm_surjective D y
      exact congrArg (normalForm D) (Subsingleton.elim p q)⟩
  rw [isNoetherianRing_iff]
  exact isNoetherian_of_subsingleton
    (NormalOre D)ᵐᵒᵖ (NormalOre D)ᵐᵒᵖ

theorem derivationOre_rightHilbertBasis :
    DerivationOreRightHilbertBasis.{u} := by
  intro B _ hB D
  letI : IsNoetherianRing Bᵐᵒᵖ := hB
  by_cases hnt : Nontrivial B
  · letI : Nontrivial B := hnt
    exact normalOre_op_isNoetherian_of_nontrivial D
  · haveI : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
    exact normalOre_op_isNoetherian_of_subsingleton D

end

end AlgebraicAnalysis.OreDerivationRightHilbertBasis
