/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.Polynomial


/-!
# Poisson closure and vertical translation

This file proves a polynomial statement used by the coisotropic part of the
Stafford argument.  If a Poisson ideal vanishes at a point of the zero section
and contains a polynomial in the base variables, then it also vanishes after
the fibre coordinate is translated by any scalar multiple of the differential
of that base polynomial at the point.

Only polynomial rings, ideals, partial derivatives, and evaluation maps occur
here.  In particular, no variety, characteristic support, conormal bundle, or
geometric integration theorem is represented by these declarations.
-/

@[expose] public section

namespace Stafford38.Geometry.CoisotropicTranslation

open Stafford38.Characteristic

noncomputable section

variable {k : Type*} [Field k] {n : ℕ}

/-- Embed a polynomial in the base coordinates into the phase-space ring. -/
def baseLift : MvPolynomial (Fin n) k →ₐ[k] SymbolRing k n :=
  MvPolynomial.rename Sum.inl

/-- Evaluate the differential of a base polynomial at a base point. -/
def differentialAt (y : Fin n → k) (f : MvPolynomial (Fin n) k) (i : Fin n) : k :=
  MvPolynomial.eval y (MvPolynomial.pderiv i f)

/-- The zero-section point over `y`. -/
def zeroSectionPoint (y : Fin n → k) : PhaseVar n → k
  | Sum.inl i => y i
  | Sum.inr _ => 0

/-- The point obtained from `(y, 0)` by translating the fibre by `t df_y`. -/
def differentialTranslatePoint
    (y : Fin n → k) (f : MvPolynomial (Fin n) k) (t : k) : PhaseVar n → k
  | Sum.inl i => y i
  | Sum.inr i => t * differentialAt y f i

/-- The polynomial line `t ↦ g(y, t v)` in the fibre over `y`. -/
def fibreLinePolynomial
    (y v : Fin n → k) (g : SymbolRing k n) : Polynomial k :=
  MvPolynomial.aeval (Sum.elim (fun i => Polynomial.C (y i))
    (fun i => Polynomial.C (v i) * Polynomial.X)) g

/-- Directional derivative in the fibre variables. -/
def verticalDeriv (v : Fin n → k) (g : SymbolRing k n) : SymbolRing k n :=
  ∑ i, MvPolynomial.C (v i) * MvPolynomial.pderiv (Sum.inr i) g

@[simp]
theorem verticalDeriv_C (v : Fin n → k) (a : k) :
    verticalDeriv v (MvPolynomial.C a) = 0 := by
  simp [verticalDeriv]

theorem verticalDeriv_add (v : Fin n → k) (g h : SymbolRing k n) :
    verticalDeriv v (g + h) = verticalDeriv v g + verticalDeriv v h := by
  simp [verticalDeriv, mul_add, Finset.sum_add_distrib]

theorem verticalDeriv_mul (v : Fin n → k) (g h : SymbolRing k n) :
    verticalDeriv v (g * h) = verticalDeriv v g * h + g * verticalDeriv v h := by
  simp only [verticalDeriv, MvPolynomial.pderiv_mul, mul_add,
    Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ac_rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ac_rfl

@[simp]
theorem verticalDeriv_X_base (v : Fin n → k) (i : Fin n) :
    verticalDeriv v (MvPolynomial.X (Sum.inl i)) = 0 := by
  simp [verticalDeriv]

@[simp]
theorem verticalDeriv_X_fibre (v : Fin n → k) (i : Fin n) :
    verticalDeriv v (MvPolynomial.X (Sum.inr i)) = MvPolynomial.C (v i) := by
  classical
  simp [verticalDeriv, Pi.single_apply]

@[simp]
theorem fibreLinePolynomial_C
    (y v : Fin n → k) (a : k) :
    fibreLinePolynomial y v (MvPolynomial.C a) = Polynomial.C a := by
  simp [fibreLinePolynomial]

@[simp]
theorem fibreLinePolynomial_zero (y v : Fin n → k) :
    fibreLinePolynomial y v 0 = 0 := by
  simp [fibreLinePolynomial]

@[simp]
theorem fibreLinePolynomial_add
    (y v : Fin n → k) (g h : SymbolRing k n) :
    fibreLinePolynomial y v (g + h) =
      fibreLinePolynomial y v g + fibreLinePolynomial y v h := by
  simp [fibreLinePolynomial]

@[simp]
theorem fibreLinePolynomial_mul
    (y v : Fin n → k) (g h : SymbolRing k n) :
    fibreLinePolynomial y v (g * h) =
      fibreLinePolynomial y v g * fibreLinePolynomial y v h := by
  simp [fibreLinePolynomial]

theorem fibreLinePolynomial_sum {ι : Type*} [Fintype ι]
    (y v : Fin n → k) (g : ι → SymbolRing k n) :
    fibreLinePolynomial y v (∑ i, g i) = ∑ i, fibreLinePolynomial y v (g i) := by
  simp [fibreLinePolynomial]

@[simp]
theorem fibreLinePolynomial_X_base
    (y v : Fin n → k) (i : Fin n) :
    fibreLinePolynomial y v (MvPolynomial.X (Sum.inl i)) = Polynomial.C (y i) := by
  simp [fibreLinePolynomial]

@[simp]
theorem fibreLinePolynomial_X_fibre
    (y v : Fin n → k) (i : Fin n) :
    fibreLinePolynomial y v (MvPolynomial.X (Sum.inr i)) =
      Polynomial.C (v i) * Polynomial.X := by
  simp [fibreLinePolynomial]

theorem derivative_fibreLinePolynomial
    (y v : Fin n → k) (g : SymbolRing k n) :
    Polynomial.derivative (fibreLinePolynomial y v g) =
      fibreLinePolynomial y v (verticalDeriv v g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [verticalDeriv]
  | add p q hp hq =>
      simp only [fibreLinePolynomial_add, Polynomial.derivative_add, hp, hq]
      rw [verticalDeriv_add, fibreLinePolynomial_add]
  | mul_X p i hp =>
      rcases i with i | i
      · simp only [fibreLinePolynomial_mul, fibreLinePolynomial_X_base, Polynomial.derivative_mul,
          Polynomial.derivative_C,   hp]
        simp [verticalDeriv_mul]
      · simp only [fibreLinePolynomial_mul, fibreLinePolynomial_X_fibre, Polynomial.derivative_mul,
          Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, zero_add, mul_one, hp]
        simp [verticalDeriv_mul]

theorem eval_fibreLinePolynomial (y v : Fin n → k)
    (g : SymbolRing k n) (t : k) :
    Polynomial.eval t (fibreLinePolynomial y v g) =
      MvPolynomial.eval (Sum.elim y (fun i => t * v i)) g := by
  change Polynomial.aeval t
      (MvPolynomial.aeval (Sum.elim (fun i => Polynomial.C (y i))
        (fun i => Polynomial.C (v i) * Polynomial.X)) g) = _
  rw [MvPolynomial.comp_aeval_apply]
  change MvPolynomial.aeval _ g = MvPolynomial.aeval _ g
  apply DFunLike.congr_fun
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with i | i
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    simp
  · rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    simp only [Sum.elim_inr, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp
    ring

theorem eval_zero_fibreLinePolynomial (y v : Fin n → k)
    (g : SymbolRing k n) :
    Polynomial.eval 0 (fibreLinePolynomial y v g) =
      MvPolynomial.eval (zeroSectionPoint y) g := by
  rw [eval_fibreLinePolynomial]
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  rcases i with i | i <;> simp [zeroSectionPoint]

theorem pderiv_baseLift_base (f : MvPolynomial (Fin n) k) (i : Fin n) :
    MvPolynomial.pderiv (Sum.inl i) (baseLift f) =
      baseLift (MvPolynomial.pderiv i f) := by
  exact MvPolynomial.pderiv_rename Sum.inl_injective i f

theorem pderiv_baseLift_fibre (f : MvPolynomial (Fin n) k) (i : Fin n) :
    MvPolynomial.pderiv (Sum.inr i) (baseLift f) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hi
  rcases MvPolynomial.mem_vars_rename Sum.inl f hi with ⟨j, hj, hji⟩
  exact Sum.inl_ne_inr hji

theorem fibreLinePolynomial_baseLift
    (y v : Fin n → k) (f : MvPolynomial (Fin n) k) :
    fibreLinePolynomial y v (baseLift f) = Polynomial.C (MvPolynomial.eval y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [baseLift, fibreLinePolynomial]
  | add p q hp hq => simp only [map_add, fibreLinePolynomial_add, hp, hq,
       map_add]
  | mul_X p j hp =>
      rw [map_mul, fibreLinePolynomial_mul, hp, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, map_mul]
      simp [baseLift]

theorem fibreLinePolynomial_baseLift_pderiv
    (y v : Fin n → k) (f : MvPolynomial (Fin n) k) (i : Fin n) :
    fibreLinePolynomial y v
        (MvPolynomial.pderiv (Sum.inl i) (baseLift f)) =
      Polynomial.C (differentialAt y f i) := by
  rw [pderiv_baseLift_base, fibreLinePolynomial_baseLift]
  rfl

theorem fibreLinePolynomial_poissonBracket_baseLift
    (y : Fin n → k) (f : MvPolynomial (Fin n) k) (g : SymbolRing k n) :
    fibreLinePolynomial y (differentialAt y f) (poissonBracket (baseLift f) g) =
      fibreLinePolynomial y (differentialAt y f)
        (verticalDeriv (differentialAt y f) g) := by
  simp only [poissonBracket, pderiv_baseLift_base, pderiv_baseLift_fibre, zero_mul,
    sub_zero, verticalDeriv, fibreLinePolynomial_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [fibreLinePolynomial_mul, fibreLinePolynomial_baseLift, differentialAt]

/-! ## Iterated Hamiltonian differentiation -/

/-- Iteration of bracketing on the left by one base equation. -/
def hamiltonIter (f : MvPolynomial (Fin n) k) : ℕ → SymbolRing k n → SymbolRing k n
  | 0, g => g
  | m + 1, g => poissonBracket (baseLift f) (hamiltonIter f m g)

theorem iterate_derivative_fibreLinePolynomial
    (y : Fin n → k) (f : MvPolynomial (Fin n) k)
    (g : SymbolRing k n) (m : ℕ) :
    (Polynomial.derivative^[m])
        (fibreLinePolynomial y (differentialAt y f) g) =
      fibreLinePolynomial y (differentialAt y f) (hamiltonIter f m g) := by
  induction m with
  | zero => rfl
  | succ m hm =>
      rw [Function.iterate_succ_apply', hm, derivative_fibreLinePolynomial,
        ← fibreLinePolynomial_poissonBracket_baseLift]
      rfl

theorem hamiltonIter_mem
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) :
    ∀ m, hamiltonIter f m g ∈ J := by
  intro m
  induction m with
  | zero => exact hg
  | succ m hm => exact hJ (baseLift f) hf (hamiltonIter f m g)

theorem polynomial_eq_zero_of_eval_iterate_derivative_zero
    [CharZero k]
    (q : Polynomial k)
    (h : ∀ m, Polynomial.eval 0 ((Polynomial.derivative^[m]) q) = 0) :
    q = 0 := by
  ext m
  have hm0 : ((Polynomial.derivative^[m]) q).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact h m
  have hm : (Nat.factorial m : k) * q.coeff m = 0 := by
    simpa only [Polynomial.coeff_iterate_derivative, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul] using hm0
  have hc : q.coeff m = 0 :=
    (mul_eq_zero.mp hm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero m)
  simpa using hc

theorem fibreLinePolynomial_eq_zero_of_poisson
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) :
    fibreLinePolynomial y (differentialAt y f) g = 0 := by
  apply polynomial_eq_zero_of_eval_iterate_derivative_zero
  intro m
  rw [iterate_derivative_fibreLinePolynomial, eval_zero_fibreLinePolynomial]
  exact hzero _ (hamiltonIter_mem J hJ f hf g hg m)

/-! ## The exact translation statement -/

/--
A zero-section common zero of a Poisson ideal remains a common zero after
vertical translation by `t df_y`, for every scalar `t`, whenever the base
polynomial `f` belongs to the ideal.

The radical hypothesis customary in the geometric application is unnecessary
for this polynomial implication; see the wrapper below.
-/
theorem zeroSection_stable_under_differential_translation
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (hJ : IsPoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) (t : k) :
    MvPolynomial.eval (differentialTranslatePoint y f t) g = 0 := by
  have heval :
      MvPolynomial.eval (differentialTranslatePoint y f t) g =
        MvPolynomial.eval (Sum.elim y (fun i => t * differentialAt y f i)) g := by
    apply MvPolynomial.eval₂_congr
    intro i c hi hc
    rcases i with i | i <;> rfl
  rw [heval, ← eval_fibreLinePolynomial]
  rw [fibreLinePolynomial_eq_zero_of_poisson J hJ y hzero f hf g hg]
  exact Polynomial.eval_zero

/-- The same statement with the radical hypothesis carried explicitly. -/
theorem radicalPoisson_zeroSection_stable_under_differential_translation
    [CharZero k]
    (J : Ideal (SymbolRing k n)) (_hJrad : J.IsRadical) (hJ : IsPoisson J)
    (y : Fin n → k)
    (hzero : ∀ g ∈ J, MvPolynomial.eval (zeroSectionPoint y) g = 0)
    (f : MvPolynomial (Fin n) k) (hf : baseLift f ∈ J)
    (g : SymbolRing k n) (hg : g ∈ J) (t : k) :
    MvPolynomial.eval (differentialTranslatePoint y f t) g = 0 :=
  zeroSection_stable_under_differential_translation J hJ y hzero f hf g hg t


end

end Stafford38.Geometry.CoisotropicTranslation
