/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.Circuit
public import Lean.Elab.Tactic.Omega

/-!
# Binary polynomial multiplication targets
-/

public section

namespace UnrestrictedBooleanMul

noncomputable section

/-- The variable `a_i` among the `2n` multiplication inputs. -/
@[expose] def aVar (n : Nat) (i : Fin n) : ANF (2 * n) :=
  X ⟨i.val, by omega⟩

/-- The variable `b_j` among the `2n` multiplication inputs. -/
@[expose] def bVar (n : Nat) (j : Fin n) : ANF (2 * n) :=
  X ⟨n + j.val, by omega⟩

@[simp]
theorem aVar_mem_affine (n : Nat) (i : Fin n) : aVar n i ∈ affine (2 * n) :=
  X_mem_affine _

@[simp]
theorem bVar_mem_affine (n : Nat) (j : Fin n) : bVar n j ∈ affine (2 * n) :=
  X_mem_affine _

/-- Coefficient `s` of the product of two `n`-term binary polynomials. -/
@[expose] def mulCoefficient (n : Nat) (s : Nat) : ANF (2 * n) :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i.val + j.val = s then aVar n i * bVar n j else 0

/-- Binary `n`-term polynomial multiplication in Boolean ANF. -/
@[expose] def Mul (n : Nat) : Fin (2 * n - 1) → ANF (2 * n) :=
  fun s => mulCoefficient n s.val

/-- The linear target space spanned by all multiplication coordinates. -/
@[expose] def mulTarget (n : Nat) : Submodule F₂ (ANF (2 * n)) :=
  Submodule.span F₂ (Set.range (Mul n))

/-- Affine functions plus the multiplication target. -/
@[expose] def mulAmbient (n : Nat) : Submodule F₂ (ANF (2 * n)) :=
  affine (2 * n) ⊔ mulTarget n

theorem Mul_mem_target (n : Nat) (s : Fin (2 * n - 1)) : Mul n s ∈ mulTarget n := by
  apply Submodule.subset_span
  exact ⟨s, rfl⟩

/-- Coefficient projection onto a chosen finite family of squarefree monomials. -/
@[expose] def coefficientProjection {m d : Nat} (anchor : Fin d → Monomial m) :
    ANF m →ₗ[F₂] (Fin d → F₂) where
  toFun p i := p.coeff (anchor i)
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

theorem coefficient_eq_zero_of_mem_affine {m : Nat} {p : ANF m} (hp : p ∈ affine m)
    (s : Monomial m) (hs : s.vars.card = 2) : p.coeff s = 0 := by
  refine Submodule.span_induction (p := fun (p : ANF m) _ => p.coeff s = 0) ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with hq | hq
    · have hqone : q = 1 := by simpa only [Set.mem_singleton_iff] using hq
      subst q
      have hne : (1 : Monomial m) ≠ s := by
        intro h
        have hc := congrArg (fun t : Monomial m => t.vars.card) h
        simp [hs] at hc
      rw [MonoidAlgebra.one_def]
      simp [hne]
    · rcases hq with ⟨i, rfl⟩
      have hne : (⟨{i}⟩ : Monomial m) ≠ s := by
        intro h
        have hc := congrArg (fun t : Monomial m => t.vars.card) h
        simp [hs] at hc
      simp [X, monomial, hne]
  · simp
  · intro p q _hp _hq hpq hqq
    simp [hpq, hqq]
  · intro c p _hp hpq
    simp [hpq]

theorem coefficientProjection_kills_affine {m d : Nat} (anchor : Fin d → Monomial m)
    (degree_two : ∀ i, (anchor i).vars.card = 2) :
    affine m ≤ LinearMap.ker (coefficientProjection anchor) := by
  intro p hp
  rw [LinearMap.mem_ker]
  funext i
  exact coefficient_eq_zero_of_mem_affine hp (anchor i) (degree_two i)

end

end UnrestrictedBooleanMul
