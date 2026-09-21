/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.Associated.ExponentReduction
public import LeanPool.CarlsonFunctions.Carlson.R.Relations
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Polynomial dependence of associated Carlson R-functions

This file proves [Carl77, Lemma 8.4-2 and Theorem 8.4-3]. The algebraic exponent reduction
uses the recurrence from `Carlson.R.AssociatedRecurrence`, retaining a denominator-cleared
identity valid throughout the variable domain. Repeated parameter raising then reduces
associated functions to a common parameter vector. Finite-dimensional linear algebra over
the polynomial ring gives a nontrivial polynomial relation between any `card ι + 1` of them.

`exists_polynomial_relation_associatedRContinued` extends this conclusion to arbitrary
complex exponents and Dirichlet parameters for the regularized continued functions.
The nodes remain in `carlsonRVariableDomain` (the product of right half-planes).

The choice of common parameters also ensures Gamma regularity at both ends of the exponent
recurrence, including the exceptional integral cases discussed by Carlson. The empty index
type is handled separately. There are no admitted proofs in this file.
-/

open Complex ProbabilityTheory
@[expose] public noncomputable section CarlsonR
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

private abbrev CarlsonVariableFunctions (ι : Type*) :=
  {z : ι → ℂ // z ∈ carlsonRVariableDomain} → ℂ

/-- Polynomial scalars act by evaluation on the variable domain. -/
local instance : Module (MvPolynomial ι ℂ)
    ({z : ι → ℂ // z ∈ carlsonRVariableDomain} → ℂ) :=
  Module.compHom _ (RingHom.pi
    (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} => MvPolynomial.eval z.1))

omit [Fintype ι] in
private theorem polynomial_smul_apply (p : MvPolynomial ι ℂ)
    (f : CarlsonVariableFunctions ι) (z : {z : ι → ℂ // z ∈ carlsonRVariableDomain}) :
    (p • f) z = p.eval z.1 * f z := rfl

/-- The parameter-raising identity with Gamma normalization cleared. -/
private theorem sum_mul_carlsonRIntegral_eq_update_add_one
    (t : ℂ) {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) (i : ι) :
    (∑ j, b j) * carlsonRIntegral t b z =
      ((∑ j, b j) + t) * carlsonRIntegral t (addDirichletUnit b i) z -
        t * z i * carlsonRIntegral (t - 1) (addDirichletUnit b i) z := by
  let : Nonempty ι := ⟨i⟩
  have hc := ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb)
  simp only [carlsonRIntegral, sum_addDirichletUnit, Gamma_add_one _ hc]
  rw [regCarlsonRIntegral_eq_update_add_one t hb hz i]
  ring

open scoped Classical in
/-- Repeatedly raising individual parameters puts the original function in the same
denominator-closed span as all exponent shifts at the raised parameter vector. -/
private theorem carlsonRIntegral_mem_of_nat_shift
    (P : Submodule (MvPolynomial ι ℂ) (CarlsonVariableFunctions ι))
    (n : ι → ℕ) (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) (t : ℂ)
    (hupper : ∀ m : ℤ, (fun z => carlsonRIntegral (t + m)
      (fun i => b i + n i) z.1) ∈ denominatorClosure P) :
    (fun z => carlsonRIntegral t b z.1) ∈ denominatorClosure P := by
  induction n using (measure (fun n : ι → ℕ => ∑ i, n i)).wf.induction generalizing b t with
  | h n ih =>
    by_cases hn : n = 0
    · simpa [hn] using hupper 0
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
    let n' := Function.update n i (n i - 1)
    have hlt : (∑ j, n' j) < ∑ j, n j := by
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hji : j = i <;> simp [n', hji]
      · exact ⟨i, Finset.mem_univ _, by simp [n']; omega⟩
    have hB : (fun j => addDirichletUnit b i j + (n' j : ℂ)) =
        (fun j => b j + (n j : ℂ)) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp only [addDirichletUnit, n', Function.update_self]
        rw [Nat.cast_sub (by omega : 1 ≤ n i)]
        push_cast
        ring
      · simp [addDirichletUnit, n', hji]
    have hb' := addDirichletUnit_mem_mvBetaConvergent hb i
    have h₀ := ih n' hlt (addDirichletUnit b i) hb' t
      (fun m => by simpa only [hB] using hupper m)
    have h₁ := ih n' hlt (addDirichletUnit b i) hb' (t - 1) (fun m => by
      rw [hB, show t - 1 + (m : ℂ) = t + (m - 1 : ℤ) by push_cast; ring]
      exact hupper (m - 1))
    let : Nonempty ι := ⟨i⟩
    have hc := ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hb)
    apply denominatorClosure_cancel P (c := MvPolynomial.C (∑ j, b j))
      (by simpa only [ne_eq, MvPolynomial.C_eq_zero] using hc)
    have heq : MvPolynomial.C (σ := ι) (∑ j, b j) •
        (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} => carlsonRIntegral t b z.1) =
        MvPolynomial.C (σ := ι) ((∑ j, b j) + t) •
          (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} =>
            carlsonRIntegral t (addDirichletUnit b i) z.1) -
        (MvPolynomial.C t * MvPolynomial.X i) •
          (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} =>
            carlsonRIntegral (t - 1) (addDirichletUnit b i) z.1) := by
      ext z
      simp only [Pi.sub_apply, polynomial_smul_apply, map_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      exact sum_mul_carlsonRIntegral_eq_update_add_one t hb z.2 i
    rw [heq]
    exact (denominatorClosure P).sub_mem
      ((denominatorClosure P).smul_mem _ h₀) ((denominatorClosure P).smul_mem _ h₁)

private theorem isCarlsonGammaRegular_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    IsCarlsonGammaRegular w := by
  intro n hn
  have he := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at he
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Choose common raised parameters and a shifted exponent with both recurrence endpoints
Gamma-regular. Positive real parts avoid all exceptional integral cases at once. -/
private theorem exists_common_carlsonAssociated_parameters [Nonempty ι]
    (t : ℂ) (b : ι → ℂ)
    (s : Fin (Fintype.card ι + 1) → CarlsonRAssociatedShift ι) :
    ∃ N : ℕ, ∃ B : ι → ℂ, B ∈ mvBetaConvergent ∧
      IsCarlsonGammaRegular (1 - (t - N)) ∧
      IsCarlsonGammaRegular ((∑ i, B i) + (t - N) - Fintype.card ι + 2) ∧
      ∀ j, ∃ n : ι → ℕ, B = fun i => (s j).parameterValue b i + n i := by
  obtain ⟨N, hN⟩ := exists_nat_gt t.re
  obtain ⟨L, hL⟩ := exists_nat_gt ((N : ℝ) + Fintype.card ι - t.re)
  choose n hn using fun i => exists_nat_gt (-(b i).re)
  let k : ι → ℕ := fun i => Finset.univ.sup (fun j => ((s j).parameter i).toNat) + n i
  have hk (j) (i) : (s j).parameter i ≤ (k i : ℤ) := by
    have h := Finset.le_sup (f := fun j => ((s j).parameter i).toNat) (Finset.mem_univ j)
    dsimp [k]
    omega
  let c : ι → ℂ := fun i => b i + k i
  have hc : c ∈ mvBetaConvergent := by
    intro i
    have hi := hn i
    have hki : (n i : ℝ) ≤ (k i : ℝ) := by
      exact_mod_cast (Nat.le_add_left (n i) (Finset.univ.sup (fun j => ((s j).parameter i).toNat)))
    change 0 < (b i + (k i : ℂ)).re
    simp only [add_re, natCast_re]
    linarith
  let B : ι → ℂ := fun i => c i + L
  have hB : B ∈ mvBetaConvergent := by
    intro i
    change 0 < (c i + (L : ℂ)).re
    simp only [add_re, natCast_re]
    exact add_pos_of_pos_of_nonneg (hc i) (Nat.cast_nonneg L)
  refine ⟨N, B, hB, isCarlsonGammaRegular_of_re_pos ?_,
    isCarlsonGammaRegular_of_re_pos ?_, ?_⟩
  · simp only [sub_re, one_re, natCast_re]
    linarith
  · have hcpos := sum_re_pos_of_mem_mvBetaConvergent hc
    have hkpos : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
    have hsum : (∑ i, B i).re = (∑ i, c i).re + Fintype.card ι * L := by
      simp [B, Finset.sum_add_distrib]
    simp only [add_re, sub_re, natCast_re, re_ofNat, hsum]
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  · intro j
    refine ⟨fun i => ((k i : ℤ) + L - (s j).parameter i).toNat, ?_⟩
    ext i
    have hnonneg : 0 ≤ (k i : ℤ) + L - (s j).parameter i := by
      have := hk j i
      omega
    have he : (((((k i : ℤ) + L - (s j).parameter i).toNat : ℕ) : ℤ) : ℂ) =
        ((k i : ℤ) + L - (s j).parameter i : ℤ) :=
      congrArg (Int.cast : ℤ → ℂ) (Int.toNat_of_nonneg hnonneg)
    simp only [Int.cast_natCast, Int.cast_sub, Int.cast_add] at he
    dsimp [B, c, CarlsonRAssociatedShift.parameterValue]
    rw [he]
    ring

/-- Carlson's existence theorem 8.4-3: any `card ι + 1` associated R-functions satisfy a
nontrivial homogeneous relation with polynomial coefficients. -/
theorem exists_polynomial_relation_associatedR
    (t : ℂ) (b : ι → ℂ)
    (s : Fin (Fintype.card ι + 1) → CarlsonRAssociatedShift ι)
    (hconv : ∀ j, (s j).parameterValue b ∈ mvBetaConvergent) :
    ∃ A : Fin (Fintype.card ι + 1) → MvPolynomial ι ℂ,
      (∃ j, A j ≠ 0) ∧
      ∀ z ∈ carlsonRVariableDomain,
        ∑ j, (A j).eval z *
          carlsonRIntegral ((s j).exponentValue t) ((s j).parameterValue b) z = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    let _ := hι
    refine ⟨fun _ => 1, ⟨0, one_ne_zero⟩, ?_⟩
    simp [carlsonRIntegral]
  | inr hι =>
    let _ := hι
    obtain ⟨N, B, hB, hT, hBT, hshift⟩ :=
      exists_common_carlsonAssociated_parameters t b s
    let v : Fin (Fintype.card ι) → CarlsonVariableFunctions ι :=
      fun j z => carlsonRIntegral ((t - N) - (j : ℕ)) B z.1
    let P := Submodule.span (MvPolynomial ι ℂ) (Set.range v)
    have hfixed (m : ℤ) : (fun z => carlsonRIntegral ((t - N) + m) B z.1) ∈
        denominatorClosure P := by
      obtain ⟨d, hd, p, hp⟩ :=
        exists_polynomial_carlsonAssociated_exponent_reduction (t - N) B m hB hT hBT
      refine ⟨d, hd, ?_⟩
      have heq : d • (fun z => carlsonRIntegral ((t - N) + m) B z.1) =
          ∑ j, p j • v j := by
        ext z
        simp only [Finset.sum_apply]
        exact hp z.1 z.2
      rw [heq]
      exact P.sum_mem fun j _ => P.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    let w : Fin (Fintype.card ι + 1) → CarlsonVariableFunctions ι :=
      fun j z => carlsonRIntegral ((s j).exponentValue t) ((s j).parameterValue b) z.1
    have hw (j) : w j ∈ denominatorClosure P := by
      obtain ⟨n, hn⟩ := hshift j
      apply carlsonRIntegral_mem_of_nat_shift P n _ (hconv j)
      intro m
      rw [← hn, show (s j).exponentValue t + (m : ℂ) =
        (t - N) + ((N : ℤ) + (s j).exponent + m : ℤ) by
          dsimp [CarlsonRAssociatedShift.exponentValue]; push_cast; ring]
      exact hfixed _
    obtain ⟨a, ha, hrel⟩ := exists_relation_of_mem_denominatorClosure v w (by simp) hw
    refine ⟨a, ha, ?_⟩
    intro z hz
    have heq := congrFun hrel ⟨z, hz⟩
    simp only [Finset.sum_apply, Pi.zero_apply] at heq
    exact heq

open scoped Classical in
/-- In the regularized normalization, raising parameters preserves any polynomial
submodule containing the raised functions. No scalar denominator is cancelled. -/
private theorem regCarlsonRContinued_mem_of_nat_shift
    (P : Submodule (MvPolynomial ι ℂ) (CarlsonVariableFunctions ι))
    (n : ι → ℕ) (b : ι → ℂ) (t : ℂ)
    (hupper : ∀ m : ℤ, (fun z => regCarlsonRContinued (t + m) z.1 z.2
      (fun i => b i + n i)) ∈ P) :
    (fun z => regCarlsonRContinued t z.1 z.2 b) ∈ P := by
  induction n using (measure (fun n : ι → ℕ => ∑ i, n i)).wf.induction generalizing b t with
  | h n ih =>
    by_cases hn : n = 0
    · simpa [hn] using hupper 0
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
    let n' := Function.update n i (n i - 1)
    have hlt : (∑ j, n' j) < ∑ j, n j := by
      apply Finset.sum_lt_sum
      · intro j _
        by_cases hji : j = i <;> simp [n', hji]
      · exact ⟨i, Finset.mem_univ _, by simp [n']; omega⟩
    have hB : (fun j => addDirichletUnit b i j + (n' j : ℂ)) =
        (fun j => b j + (n j : ℂ)) := by
      ext j
      by_cases hji : j = i
      · subst j
        simp only [addDirichletUnit, n', Function.update_self]
        rw [Nat.cast_sub (by omega : 1 ≤ n i)]
        push_cast
        ring
      · simp [addDirichletUnit, n', hji]
    have h₀ := ih n' hlt (addDirichletUnit b i) t
      (fun m => by simpa only [hB] using hupper m)
    have h₁ := ih n' hlt (addDirichletUnit b i) (t - 1) (fun m => by
      rw [hB, show t - 1 + (m : ℂ) = t + (m - 1 : ℤ) by push_cast; ring]
      exact hupper (m - 1))
    have heq : (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} =>
        regCarlsonRContinued t z.1 z.2 b) =
        MvPolynomial.C (σ := ι) ((∑ j, b j) + t) •
          (fun z => regCarlsonRContinued t z.1 z.2 (addDirichletUnit b i)) -
        (MvPolynomial.C t * MvPolynomial.X i) •
          (fun z => regCarlsonRContinued (t - 1) z.1 z.2 (addDirichletUnit b i)) := by
      ext z
      simp only [Pi.sub_apply, polynomial_smul_apply, map_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      exact regCarlsonRContinued_eq_addDirichletUnit t b z.2 i
    rw [heq]
    exact P.sub_mem (P.smul_mem _ h₀) (P.smul_mem _ h₁)

/-- Carlson's Theorem 8.4-3 on the entire Dirichlet-parameter space. The relation
is nontrivial as a polynomial identity, not merely a pointwise scalar dependence.
Gamma regularization includes all exceptional total parameters. -/
theorem exists_polynomial_relation_associatedRContinued
    (t : ℂ) (b : ι → ℂ)
    (s : Fin (Fintype.card ι + 1) → CarlsonRAssociatedShift ι) :
    ∃ A : Fin (Fintype.card ι + 1) → MvPolynomial ι ℂ,
      (∃ j, A j ≠ 0) ∧
      ∀ (z : ι → ℂ) (hz : z ∈ carlsonRVariableDomain),
        ∑ j, (A j).eval z *
          regCarlsonRContinued ((s j).exponentValue t) z hz ((s j).parameterValue b) = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have hzero (u : ℂ) (z c : ι → ℂ) (hz : z ∈ carlsonRVariableDomain) :
        regCarlsonRContinued u z hz c = 0 := by
      rw [regCarlsonRContinued_eq_integral u hz (by intro i; exact isEmptyElim i)]
      simp [regCarlsonRIntegral, regCarlsonDirichletAverage, regDirichletIntegral]
    exact ⟨fun _ => 1, ⟨0, one_ne_zero⟩, fun z hz => by simp [hzero]⟩
  | inr hι =>
    obtain ⟨N, B, hB, hT, hBT, hshift⟩ := exists_common_carlsonAssociated_parameters t b s
    let v : Fin (Fintype.card ι) → CarlsonVariableFunctions ι :=
      fun j z => carlsonRIntegral ((t - N) - (j : ℕ)) B z.1
    let P := Submodule.span (MvPolynomial ι ℂ) (Set.range v)
    have hfixed (m : ℤ) : (fun z => carlsonRIntegral ((t - N) + m) B z.1) ∈
        denominatorClosure P := by
      obtain ⟨d, hd, p, hp⟩ :=
        exists_polynomial_carlsonAssociated_exponent_reduction (t - N) B m hB hT hBT
      refine ⟨d, hd, ?_⟩
      have heq : d • (fun z => carlsonRIntegral ((t - N) + m) B z.1) =
          ∑ j, p j • v j := by
        ext z
        simp only [Finset.sum_apply]
        exact hp z.1 z.2
      rw [heq]
      exact P.sum_mem fun j _ => P.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    have hfixedReg (m : ℤ) :
        (fun z => regCarlsonRContinued ((t - N) + m) z.1 z.2 B) ∈ denominatorClosure P := by
      have hGamma := Gamma_ne_zero_of_re_pos (sum_re_pos_of_mem_mvBetaConvergent hB)
      have heq : (fun z : {z : ι → ℂ // z ∈ carlsonRVariableDomain} =>
          regCarlsonRContinued ((t - N) + m) z.1 z.2 B) =
          MvPolynomial.C (σ := ι) (Gamma (∑ i, B i))⁻¹ •
            (fun z => carlsonRIntegral ((t - N) + m) B z.1) := by
        ext z
        simp only [polynomial_smul_apply, MvPolynomial.eval_C, carlsonRIntegral,
          regCarlsonRContinued_eq_integral _ z.2 hB]
        rw [← mul_assoc, inv_mul_cancel₀ hGamma, one_mul]
      rw [heq]
      exact (denominatorClosure P).smul_mem _ (hfixed m)
    let w : Fin (Fintype.card ι + 1) → CarlsonVariableFunctions ι :=
      fun j z => regCarlsonRContinued ((s j).exponentValue t) z.1 z.2 ((s j).parameterValue b)
    have hw (j) : w j ∈ denominatorClosure P := by
      obtain ⟨n, hn⟩ := hshift j
      apply regCarlsonRContinued_mem_of_nat_shift (denominatorClosure P) n _ _
      intro m
      rw [← hn, show (s j).exponentValue t + (m : ℂ) =
        (t - N) + ((N : ℤ) + (s j).exponent + m : ℤ) by
          dsimp [CarlsonRAssociatedShift.exponentValue]; push_cast; ring]
      exact hfixedReg _
    obtain ⟨a, ha, hrel⟩ := exists_relation_of_mem_denominatorClosure v w (by simp) hw
    refine ⟨a, ha, ?_⟩
    intro z hz
    have heq := congrFun hrel ⟨z, hz⟩
    simp only [Finset.sum_apply, Pi.zero_apply] at heq
    exact heq

end DirichletTransform
end CarlsonR
