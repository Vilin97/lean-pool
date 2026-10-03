/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Boolean algebraic normal forms

A squarefree monomial is a finite set of input variables. Multiplication is
set union, so the resulting monoid algebra over `ZMod 2` is exactly the Boolean
ANF quotient in canonical normal form.
-/

public section

namespace UnrestrictedBooleanMul

noncomputable section

/-- The two-element field of Boolean coefficients. -/
abbrev F₂ := ZMod 2

/-- A squarefree monomial in `m` Boolean variables. -/
@[ext]
structure Monomial (m : Nat) where
  /-- Variables occurring in this squarefree monomial. -/
  vars : Finset (Fin m)
deriving @[expose] DecidableEq

namespace Monomial

/-- Identify a squarefree monomial with its finite set of variables. -/
def equivFinset {m : Nat} : Monomial m ≃ Finset (Fin m) where
  toFun := Monomial.vars
  invFun := Monomial.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance {m : Nat} : Fintype (Monomial m) :=
  Fintype.ofEquiv (Finset (Fin m)) equivFinset.symm

end Monomial

instance {m : Nat} : CommMonoid (Monomial m) where
  one := ⟨∅⟩
  mul s t := ⟨s.vars ∪ t.vars⟩
  one_mul s := by apply Monomial.ext; exact Finset.empty_union s.vars
  mul_one s := by apply Monomial.ext; exact Finset.union_empty s.vars
  mul_assoc r s t := by apply Monomial.ext; exact Finset.union_assoc r.vars s.vars t.vars
  mul_comm s t := by apply Monomial.ext; exact Finset.union_comm s.vars t.vars

@[simp]
theorem Monomial.one_vars {m : Nat} : (1 : Monomial m).vars = ∅ := rfl

@[simp]
theorem Monomial.mul_vars {m : Nat} (s t : Monomial m) : (s * t).vars = s.vars ∪ t.vars := rfl

@[simp]
theorem Monomial.singleton_mul_singleton {m : Nat} (i j : Fin m) :
    (⟨{i}⟩ : Monomial m) * ⟨{j}⟩ = ⟨{i, j}⟩ := by
  apply Monomial.ext
  simp

/-- Canonical Boolean algebraic normal forms in `m` variables. -/
abbrev ANF (m : Nat) := MonoidAlgebra F₂ (Monomial m)

/-- The ANF consisting of one squarefree monomial. -/
@[expose] def monomial {m : Nat} (s : Finset (Fin m)) : ANF m :=
  MonoidAlgebra.single ⟨s⟩ 1

@[simp]
theorem coeff_monomial {m : Nat} (s t : Finset (Fin m)) :
    (monomial s : ANF m).coeff ⟨t⟩ = if s = t then 1 else 0 := by
  rw [monomial]
  change (Finsupp.single (⟨s⟩ : Monomial m) (1 : F₂)) (⟨t⟩ : Monomial m) =
    if s = t then 1 else 0
  rw [Finsupp.single_apply]
  simp only [Monomial.mk.injEq]

/-- Extract a product coefficient bilinearly, before expanding either ANF. -/
theorem coeff_sum_smul_mul_sum_smul {m : Nat} {ι κ : Type*}
    [Fintype ι] [Fintype κ] (p : ι → ANF m) (q : κ → ANF m)
    (a : ι → F₂) (b : κ → F₂) (s : Monomial m) :
    ((∑ i, a i • p i) * ∑ j, b j • q j).coeff s =
      ∑ i, ∑ j, (a i * b j) * (p i * q j).coeff s := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

/-- The `i`th input variable. -/
@[expose] def X {m : Nat} (i : Fin m) : ANF m := monomial {i}

@[simp]
theorem monomial_mul {m : Nat} (s t : Finset (Fin m)) :
    monomial s * monomial t = monomial (s ∪ t) := by
  rw [monomial, monomial, MonoidAlgebra.single_mul_single]
  change MonoidAlgebra.single (⟨s ∪ t⟩ : Monomial m) (1 * 1) =
    MonoidAlgebra.single (⟨s ∪ t⟩ : Monomial m) 1
  rw [one_mul]

theorem X_mul_self {m : Nat} (i : Fin m) : X i * X i = X i := by
  simp [X]

@[simp]
theorem anf_add_self {m : Nat} (p : ANF m) : p + p = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext s
  exact CharTwo.add_self_eq_zero (p.coeff s)

@[simp]
theorem anf_two_eq_zero {m : Nat} : (2 : ANF m) = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext s
  simp [CharTwo.two_eq_zero]

@[simp]
theorem anf_four_eq_zero {m : Nat} : (4 : ANF m) = 0 := by
  apply MonoidAlgebra.coeff_injective
  ext s
  simp [CharTwo.ofNat_eq_mod]

/-- Evaluation of a canonical ANF on a Boolean input. -/
@[expose]
def eval {m : Nat} (p : ANF m) (x : Fin m → F₂) : F₂ :=
  p.coeff.sum fun s c => c * ∏ i ∈ s.vars, x i

@[simp]
theorem eval_monomial {m : Nat} (s : Finset (Fin m)) (x : Fin m → F₂) :
    eval (monomial s) x = ∏ i ∈ s, x i := by
  simp [eval, monomial]

@[simp]
theorem eval_X {m : Nat} (i : Fin m) (x : Fin m → F₂) : eval (X i) x = x i := by
  simp [X]

@[simp]
theorem anf_one_coeff {m : Nat} (s : Monomial m) :
    (1 : ANF m).coeff s = if s = 1 then 1 else 0 := by
  rw [MonoidAlgebra.one_def]
  change (Finsupp.single (1 : Monomial m) (1 : F₂)) s = if s = 1 then 1 else 0
  rw [Finsupp.single_apply]
  simp only [eq_comm]

theorem f2_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem prod_union_f2 {m : Nat} (x : Fin m → F₂) (s t : Finset (Fin m)) :
    (∏ i ∈ s ∪ t, x i) = (∏ i ∈ s, x i) * ∏ i ∈ t, x i := by
  have hz : ((∏ i ∈ s ∪ t, x i) = 0) ↔
      ((∏ i ∈ s, x i) * ∏ i ∈ t, x i) = 0 := by
    constructor
    · intro h
      rcases Finset.prod_eq_zero_iff.mp h with ⟨i, hi, hxi⟩
      rcases Finset.mem_union.mp hi with his | hit
      · rw [Finset.prod_eq_zero his hxi, zero_mul]
      · rw [Finset.prod_eq_zero hit hxi, mul_zero]
    · intro h
      rcases mul_eq_zero.mp h with hs | ht
      · rcases Finset.prod_eq_zero_iff.mp hs with ⟨i, hi, hxi⟩
        exact Finset.prod_eq_zero (Finset.mem_union_left t hi) hxi
      · rcases Finset.prod_eq_zero_iff.mp ht with ⟨i, hi, hxi⟩
        exact Finset.prod_eq_zero (Finset.mem_union_right s hi) hxi
  rcases f2_eq_zero_or_one (∏ i ∈ s ∪ t, x i) with h | h
  · rw [h, hz.mp h]
  · rcases f2_eq_zero_or_one ((∏ i ∈ s, x i) * ∏ i ∈ t, x i) with k | k
    · have bad : (1 : F₂) = 0 := h.symm.trans (hz.mpr k)
      exact (one_ne_zero bad).elim
    · rw [h, k]

/-- Evaluation of a squarefree monomial as a monoid homomorphism. -/
@[expose]
def monomialEval {m : Nat} (x : Fin m → F₂) : Monomial m →* F₂ where
  toFun s := ∏ i ∈ s.vars, x i
  map_one' := by simp
  map_mul' s t := prod_union_f2 x s.vars t.vars

/-- Evaluation at a Boolean point as an `F₂`-algebra homomorphism. -/
@[expose]
noncomputable def evalHom {m : Nat} (x : Fin m → F₂) : ANF m →ₐ[F₂] F₂ :=
  MonoidAlgebra.lift F₂ F₂ (Monomial m) (monomialEval x)

theorem eval_eq_evalHom {m : Nat} (p : ANF m) (x : Fin m → F₂) :
    eval p x = evalHom x p := by
  simp [eval, evalHom, monomialEval, MonoidAlgebra.lift_apply]

@[simp] theorem eval_zero' {m : Nat} (x : Fin m → F₂) : eval 0 x = 0 := by
  rw [eval_eq_evalHom]
  exact map_zero (evalHom x)

@[simp] theorem eval_one' {m : Nat} (x : Fin m → F₂) : eval 1 x = 1 := by
  rw [eval_eq_evalHom]
  exact map_one (evalHom x)

@[simp] theorem eval_add' {m : Nat} (p q : ANF m) (x : Fin m → F₂) :
    eval (p + q) x = eval p x + eval q x := by
  simp only [eval_eq_evalHom, map_add]

@[simp] theorem eval_mul' {m : Nat} (p q : ANF m) (x : Fin m → F₂) :
    eval (p * q) x = eval p x * eval q x := by
  simp only [eval_eq_evalHom, map_mul]

@[simp] theorem eval_smul' {m : Nat} (c : F₂) (p : ANF m) (x : Fin m → F₂) :
    eval (c • p) x = c * eval p x := by
  rw [eval_eq_evalHom, map_smul]
  rfl

/-- Simultaneous evaluation at all Boolean inputs, as a linear map. -/
noncomputable def evalLinearMap (m : Nat) : ANF m →ₗ[F₂] ((Fin m → F₂) → F₂) where
  toFun p := eval p
  map_add' p q := by funext x; exact eval_add' p q x
  map_smul' c p := by funext x; exact eval_smul' c p x

/-- The Boolean polynomial which is one at `x` and zero at every other input. -/
def pointIndicator {m : Nat} (x : Fin m → F₂) : ANF m :=
  ∏ i, if x i = 1 then X i else 1 + X i

@[simp]
theorem eval_pointIndicator {m : Nat} (x y : Fin m → F₂) :
    eval (pointIndicator x) y = if y = x then 1 else 0 := by
  classical
  simp only [pointIndicator, eval_eq_evalHom, map_prod]
  simp only [← eval_eq_evalHom]
  by_cases h : y = x
  · subst y
    simp only [ite_true]
    apply Finset.prod_eq_one
    intro i _
    rcases f2_eq_zero_or_one (x i) with hxi | hxi
    · simp [hxi]
    · simp [hxi]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases f2_eq_zero_or_one (x i) with hxi | hxi
    · have hyi : y i = 1 := by
        rcases f2_eq_zero_or_one (y i) with hyi | hyi
        · exact (hi (hyi.trans hxi.symm)).elim
        · exact hyi
      simp [hxi, hyi, CharTwo.add_self_eq_zero]
    · have hyi : y i = 0 := by
        rcases f2_eq_zero_or_one (y i) with hyi | hyi
        · exact hyi
        · exact (hi (hyi.trans hxi.symm)).elim
      simp [hxi, hyi]

theorem evalLinearMap_surjective (m : Nat) : Function.Surjective (evalLinearMap m) := by
  intro f
  refine ⟨∑ x, f x • pointIndicator x, ?_⟩
  funext y
  simp [evalLinearMap, eval_pointIndicator]

theorem evalLinearMap_finrank (m : Nat) :
    Module.finrank F₂ (ANF m) = Module.finrank F₂ ((Fin m → F₂) → F₂) := by
  calc
    Module.finrank F₂ (ANF m) = Module.finrank F₂ (Monomial m →₀ F₂) :=
      (MonoidAlgebra.coeffLinearEquiv F₂).finrank_eq
    _ = Module.finrank F₂ ((Fin m → F₂) → F₂) := by
      rw [Module.finrank_finsupp_self, Module.finrank_fintype_fun_eq_card]
      rw [Fintype.card_congr Monomial.equivFinset, Fintype.card_finset, Fintype.card_fun]
      simp

/-- Canonical Boolean ANFs are determined by their values on Boolean inputs. -/
theorem eval_injective (m : Nat) : Function.Injective (fun p : ANF m ↦ eval p) := by
  change Function.Injective (evalLinearMap m)
  rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank (evalLinearMap_finrank m)]
  exact evalLinearMap_surjective m

/-- Canonical Boolean ANFs are linearly equivalent to all Boolean functions. -/
noncomputable def evalLinearEquiv (m : Nat) : ANF m ≃ₗ[F₂] ((Fin m → F₂) → F₂) :=
  LinearEquiv.ofBijective (evalLinearMap m) ⟨eval_injective m, evalLinearMap_surjective m⟩

/-- The subspace of constants and input-linear functions. -/
@[expose] noncomputable def affine (m : Nat) : Submodule F₂ (ANF m) :=
  Submodule.span F₂ ({1} ∪ Set.range X)

theorem one_mem_affine (m : Nat) : (1 : ANF m) ∈ affine m := by
  apply Submodule.subset_span
  exact Set.mem_union_left _ (Set.mem_singleton 1)

theorem X_mem_affine {m : Nat} (i : Fin m) : X i ∈ affine m := by
  apply Submodule.subset_span
  exact Set.mem_union_right _ ⟨i, rfl⟩

end

end UnrestrictedBooleanMul
