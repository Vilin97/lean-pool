/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.Mul

/-!
# Exact small cases and explicit upper-bound circuits
-/

public section

namespace UnrestrictedBooleanMul

noncomputable section

theorem submodule_add_mem {m : Nat} {S : Submodule F₂ (ANF m)} {x y : ANF m}
    (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
  Submodule.add_mem S hx hy

namespace TargetCoordinates

/-- Anchor monomials recovering the 1-term product coefficients. -/
def oneAnchor : Fin 1 → Monomial 2 := ![⟨{0, 1}⟩]
/-- Anchor monomials recovering the 2-term product coefficients. -/
def twoAnchor : Fin 3 → Monomial 4 := ![⟨{0, 2}⟩, ⟨{0, 3}⟩, ⟨{1, 3}⟩]
/-- Anchor monomials recovering the 3-term product coefficients. -/
def threeAnchor : Fin 5 → Monomial 6 :=
  ![⟨{0, 3}⟩, ⟨{0, 4}⟩, ⟨{0, 5}⟩, ⟨{1, 5}⟩, ⟨{2, 5}⟩]

/-- Extract the anchor coefficients for a 1-term product. -/
def oneProjection : ANF 2 →ₗ[F₂] (Fin 1 → F₂) := coefficientProjection oneAnchor
/-- Extract the anchor coefficients for a 2-term product. -/
def twoProjection : ANF 4 →ₗ[F₂] (Fin 3 → F₂) := coefficientProjection twoAnchor
/-- Extract the anchor coefficients for a 3-term product. -/
def threeProjection : ANF 6 →ₗ[F₂] (Fin 5 → F₂) := coefficientProjection threeAnchor

theorem oneAnchor_degree (i : Fin 1) : (oneAnchor i).vars.card = 2 := by
  fin_cases i
  decide

theorem twoAnchor_degree (i : Fin 3) : (twoAnchor i).vars.card = 2 := by
  fin_cases i <;> decide

theorem threeAnchor_degree (i : Fin 5) : (threeAnchor i).vars.card = 2 := by
  fin_cases i <;> decide

theorem oneProjection_kills_affine : affine 2 ≤ LinearMap.ker oneProjection :=
  coefficientProjection_kills_affine oneAnchor oneAnchor_degree

theorem twoProjection_kills_affine : affine 4 ≤ LinearMap.ker twoProjection :=
  coefficientProjection_kills_affine twoAnchor twoAnchor_degree

theorem threeProjection_kills_affine : affine 6 ≤ LinearMap.ker threeProjection :=
  coefficientProjection_kills_affine threeAnchor threeAnchor_degree

theorem oneProjection_Mul (i : Fin 1) :
    oneProjection (Mul 1 i) = (Pi.basisFun F₂ (Fin 1)) i := by
  fin_cases i
  ext j
  fin_cases j
  simp [oneProjection, coefficientProjection, oneAnchor, Mul, mulCoefficient, aVar, bVar, X,
    monomial_mul, Pi.basisFun]

theorem twoProjection_Mul (i : Fin 3) :
    twoProjection (Mul 2 i) = (Pi.basisFun F₂ (Fin 3)) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp only [twoProjection, coefficientProjection, twoAnchor, Fin.isValue, Mul,
      mulCoefficient, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, Nat.reduceMul, aVar, X, bVar,
      monomial_mul, Finset.singleton_union, Fin.sum_univ_succ, and_true, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, add_zero, Fin.reduceFinMk, Finset.univ_unique, Fin.default_eq_zero,
      Fin.succ_ne_zero, and_false, ↓reduceIte, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, Fin.zero_eta, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
      coeff_monomial, Pi.basisFun, Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm,
      LinearEquiv.refl_apply, Pi.single_eq_same, Fin.mk_one, Matrix.cons_val_one, ne_eq,
      one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne, ite_eq_right_iff, imp_false,
      Matrix.cons_val, Fin.reduceEq, Fin.val_succ, Fin.val_eq_zero, zero_add,
      Nat.add_eq_right, Nat.reduceAdd, Finset.sum_ite_irrel, Finset.sum_const,
      Finset.card_singleton, one_smul, zero_ne_one, MonoidAlgebra.coeff_add, Finsupp.coe_add,
      Pi.add_apply, add_eq_left, Nat.reduceEqDiff, OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat
      ] <;> decide

theorem threeProjection_Mul (i : Fin 5) :
    threeProjection (Mul 3 i) = (Pi.basisFun F₂ (Fin 5)) i := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp only [threeProjection, coefficientProjection, threeAnchor, Fin.isValue, Mul,
      mulCoefficient, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, Nat.reduceMul, aVar, X, bVar,
      monomial_mul, Finset.singleton_union, Fin.sum_univ_succ, and_true, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod, add_zero, Fin.reduceFinMk, Fin.succ_ne_zero, and_false, ↓reduceIte,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, Fin.zero_eta,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, coeff_monomial, Pi.basisFun,
      Module.Basis.coe_ofEquivFun, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
      Pi.single_eq_same, Fin.mk_one, Matrix.cons_val_one, ne_eq, one_ne_zero,
      not_false_eq_true, Pi.single_eq_of_ne, ite_eq_right_iff, imp_false, Matrix.cons_val,
      Fin.reduceEq, Fin.val_succ, zero_add, Nat.add_eq_right, Nat.reduceAdd,
      Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, Nat.reduceEqDiff, zero_ne_one,
      MonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, add_eq_left,
      Finset.sum_ite_irrel, Finset.sum_const, Finset.card_singleton, one_smul,
      OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat]
      <;> decide

end TargetCoordinates

namespace UpperCircuits

/-! ## One term -/

/-- Left AND-gate inputs of the explicit 1-gate circuit for 1-term multiplication. -/
def oneLeft : Fin 1 → ANF 2 := ![aVar 1 0]
/-- Right AND-gate inputs of the explicit 1-gate circuit for 1-term multiplication. -/
def oneRight : Fin 1 → ANF 2 := ![bVar 1 0]

/-- An explicit 1-gate circuit for 1-term Boolean polynomial multiplication. -/
def one : Circuit 2 1 :=
  Circuit.ofAffineProducts oneLeft oneRight
    (by intro i; fin_cases i; exact aVar_mem_affine 1 0)
    (by intro i; fin_cases i; exact bVar_mem_affine 1 0)

theorem one_computes : one.Computes (Mul 1) := by
  intro s
  fin_cases s
  simpa [Mul, mulCoefficient, one, oneLeft, oneRight] using gate_mem_finalWire one (0 : Fin 1)

/-! ## Two terms (Karatsuba) -/

/-- Left AND-gate inputs of the explicit 3-gate circuit for 2-term multiplication. -/
def twoLeft : Fin 3 → ANF 4 :=
  ![aVar 2 0, aVar 2 1, aVar 2 0 + aVar 2 1]

/-- Right AND-gate inputs of the explicit 3-gate circuit for 2-term multiplication. -/
def twoRight : Fin 3 → ANF 4 :=
  ![bVar 2 0, bVar 2 1, bVar 2 0 + bVar 2 1]

/-- An explicit 3-gate circuit for 2-term Boolean polynomial multiplication. -/
def two : Circuit 4 3 :=
  Circuit.ofAffineProducts twoLeft twoRight
    (by
      intro i; fin_cases i
      · exact aVar_mem_affine 2 0
      · exact aVar_mem_affine 2 1
      · exact submodule_add_mem (aVar_mem_affine 2 0) (aVar_mem_affine 2 1))
    (by
      intro i; fin_cases i
      · exact bVar_mem_affine 2 0
      · exact bVar_mem_affine 2 1
      · exact submodule_add_mem (bVar_mem_affine 2 0) (bVar_mem_affine 2 1))

/-- Recover the 2-term product coefficients by XORs of the circuit outputs. -/
def twoRecombine : Fin 3 → ANF 4 :=
  ![two.gate 0, two.gate 0 + two.gate 1 + two.gate 2, two.gate 1]

theorem two_formula : Mul 2 = twoRecombine := by
  funext s
  fin_cases s
  all_goals
    simp [Mul, mulCoefficient, Fin.sum_univ_succ, twoRecombine, two, twoLeft, twoRight,
      Circuit.ofAffineProducts]
    try ring_nf
  all_goals simp

theorem two_computes : two.Computes (Mul 2) := by
  rw [two_formula]
  intro s
  fin_cases s
  · exact gate_mem_finalWire two 0
  · exact submodule_add_mem
      (submodule_add_mem (gate_mem_finalWire two 0) (gate_mem_finalWire two 1))
      (gate_mem_finalWire two 2)
  · exact gate_mem_finalWire two 1

/-! ## Three terms (six products) -/

/-- Left AND-gate inputs of the explicit 6-gate circuit for 3-term multiplication. -/
def threeLeft : Fin 6 → ANF 6 :=
  ![aVar 3 0, aVar 3 1, aVar 3 0 + aVar 3 1,
    aVar 3 2, aVar 3 0 + aVar 3 2, aVar 3 1 + aVar 3 2]

/-- Right AND-gate inputs of the explicit 6-gate circuit for 3-term multiplication. -/
def threeRight : Fin 6 → ANF 6 :=
  ![bVar 3 0, bVar 3 1, bVar 3 0 + bVar 3 1,
    bVar 3 2, bVar 3 0 + bVar 3 2, bVar 3 1 + bVar 3 2]

/-- An explicit 6-gate circuit for 3-term Boolean polynomial multiplication. -/
def three : Circuit 6 6 :=
  Circuit.ofAffineProducts threeLeft threeRight
    (by
      intro i; fin_cases i
      · exact aVar_mem_affine 3 0
      · exact aVar_mem_affine 3 1
      · exact submodule_add_mem (aVar_mem_affine 3 0) (aVar_mem_affine 3 1)
      · exact aVar_mem_affine 3 2
      · exact submodule_add_mem (aVar_mem_affine 3 0) (aVar_mem_affine 3 2)
      · exact submodule_add_mem (aVar_mem_affine 3 1) (aVar_mem_affine 3 2))
    (by
      intro i; fin_cases i
      · exact bVar_mem_affine 3 0
      · exact bVar_mem_affine 3 1
      · exact submodule_add_mem (bVar_mem_affine 3 0) (bVar_mem_affine 3 1)
      · exact bVar_mem_affine 3 2
      · exact submodule_add_mem (bVar_mem_affine 3 0) (bVar_mem_affine 3 2)
      · exact submodule_add_mem (bVar_mem_affine 3 1) (bVar_mem_affine 3 2))

/-- Recover the 3-term product coefficients by XORs of the circuit outputs. -/
def threeRecombine : Fin 5 → ANF 6 :=
  ![three.gate 0,
    three.gate 0 + three.gate 1 + three.gate 2,
    three.gate 0 + three.gate 1 + three.gate 3 + three.gate 4,
    three.gate 1 + three.gate 3 + three.gate 5,
    three.gate 3]

theorem three_formula : Mul 3 = threeRecombine := by
  funext s
  fin_cases s <;>
    simp [Mul, mulCoefficient, Fin.sum_univ_succ, threeRecombine, three, threeLeft,
      threeRight, Circuit.ofAffineProducts] <;> ring_nf <;> simp

theorem three_computes : three.Computes (Mul 3) := by
  rw [three_formula]
  intro s
  fin_cases s
  · exact gate_mem_finalWire three 0
  · exact submodule_add_mem
      (submodule_add_mem (gate_mem_finalWire three 0) (gate_mem_finalWire three 1))
      (gate_mem_finalWire three 2)
  · exact submodule_add_mem
      (submodule_add_mem
        (submodule_add_mem (gate_mem_finalWire three 0) (gate_mem_finalWire three 1))
        (gate_mem_finalWire three 3))
      (gate_mem_finalWire three 4)
  · exact submodule_add_mem
      (submodule_add_mem (gate_mem_finalWire three 1) (gate_mem_finalWire three 3))
      (gate_mem_finalWire three 5)
  · exact gate_mem_finalWire three 3

/-! ## Four terms (two-level Karatsuba--Ofman) -/

/-- Left AND-gate inputs of the explicit 9-gate circuit for 4-term multiplication. -/
def fourLeft : Fin 9 → ANF 8 :=
  ![aVar 4 0, aVar 4 1, aVar 4 0 + aVar 4 1,
    aVar 4 2, aVar 4 3, aVar 4 2 + aVar 4 3,
    aVar 4 0 + aVar 4 2, aVar 4 1 + aVar 4 3,
    aVar 4 0 + aVar 4 1 + aVar 4 2 + aVar 4 3]

/-- Right AND-gate inputs of the explicit 9-gate circuit for 4-term multiplication. -/
def fourRight : Fin 9 → ANF 8 :=
  ![bVar 4 0, bVar 4 1, bVar 4 0 + bVar 4 1,
    bVar 4 2, bVar 4 3, bVar 4 2 + bVar 4 3,
    bVar 4 0 + bVar 4 2, bVar 4 1 + bVar 4 3,
    bVar 4 0 + bVar 4 1 + bVar 4 2 + bVar 4 3]

/-- An explicit 9-gate circuit for 4-term Boolean polynomial multiplication. -/
def four : Circuit 8 9 :=
  Circuit.ofAffineProducts fourLeft fourRight
    (by
      intro i; fin_cases i
      · exact aVar_mem_affine 4 0
      · exact aVar_mem_affine 4 1
      · exact submodule_add_mem (aVar_mem_affine 4 0) (aVar_mem_affine 4 1)
      · exact aVar_mem_affine 4 2
      · exact aVar_mem_affine 4 3
      · exact submodule_add_mem (aVar_mem_affine 4 2) (aVar_mem_affine 4 3)
      · exact submodule_add_mem (aVar_mem_affine 4 0) (aVar_mem_affine 4 2)
      · exact submodule_add_mem (aVar_mem_affine 4 1) (aVar_mem_affine 4 3)
      · exact submodule_add_mem
          (submodule_add_mem
            (submodule_add_mem (aVar_mem_affine 4 0) (aVar_mem_affine 4 1))
            (aVar_mem_affine 4 2))
          (aVar_mem_affine 4 3))
    (by
      intro i; fin_cases i
      · exact bVar_mem_affine 4 0
      · exact bVar_mem_affine 4 1
      · exact submodule_add_mem (bVar_mem_affine 4 0) (bVar_mem_affine 4 1)
      · exact bVar_mem_affine 4 2
      · exact bVar_mem_affine 4 3
      · exact submodule_add_mem (bVar_mem_affine 4 2) (bVar_mem_affine 4 3)
      · exact submodule_add_mem (bVar_mem_affine 4 0) (bVar_mem_affine 4 2)
      · exact submodule_add_mem (bVar_mem_affine 4 1) (bVar_mem_affine 4 3)
      · exact submodule_add_mem
          (submodule_add_mem
            (submodule_add_mem (bVar_mem_affine 4 0) (bVar_mem_affine 4 1))
            (bVar_mem_affine 4 2))
          (bVar_mem_affine 4 3))

/-- Recover the 4-term product coefficients by XORs of the circuit outputs. -/
def fourRecombine : Fin 7 → ANF 8 :=
  ![four.gate 0,
    four.gate 2 + four.gate 0 + four.gate 1,
    four.gate 1 + four.gate 6 + four.gate 0 + four.gate 3,
    (four.gate 8 + four.gate 6 + four.gate 7) +
      (four.gate 2 + four.gate 0 + four.gate 1) +
      (four.gate 5 + four.gate 3 + four.gate 4),
    four.gate 3 + four.gate 7 + four.gate 1 + four.gate 4,
    four.gate 5 + four.gate 3 + four.gate 4,
    four.gate 4]

theorem four_formula : Mul 4 = fourRecombine := by
  funext s
  fin_cases s <;>
    simp [Mul, mulCoefficient, Fin.sum_univ_succ, fourRecombine, four, fourLeft, fourRight,
      Circuit.ofAffineProducts] <;> ring_nf <;> simp

theorem four_computes : four.Computes (Mul 4) := by
  rw [four_formula]
  intro s
  fin_cases s
  · exact gate_mem_finalWire four 0
  · exact submodule_add_mem
      (submodule_add_mem (gate_mem_finalWire four 2) (gate_mem_finalWire four 0))
      (gate_mem_finalWire four 1)
  · exact submodule_add_mem
      (submodule_add_mem
        (submodule_add_mem (gate_mem_finalWire four 1) (gate_mem_finalWire four 6))
        (gate_mem_finalWire four 0))
      (gate_mem_finalWire four 3)
  · exact submodule_add_mem
      (submodule_add_mem
        (submodule_add_mem
          (submodule_add_mem (gate_mem_finalWire four 8) (gate_mem_finalWire four 6))
          (gate_mem_finalWire four 7))
        (submodule_add_mem
          (submodule_add_mem (gate_mem_finalWire four 2) (gate_mem_finalWire four 0))
          (gate_mem_finalWire four 1)))
      (submodule_add_mem
        (submodule_add_mem (gate_mem_finalWire four 5) (gate_mem_finalWire four 3))
        (gate_mem_finalWire four 4))
  · exact submodule_add_mem
      (submodule_add_mem
        (submodule_add_mem (gate_mem_finalWire four 3) (gate_mem_finalWire four 7))
        (gate_mem_finalWire four 1))
      (gate_mem_finalWire four 4)
  · exact submodule_add_mem
      (submodule_add_mem (gate_mem_finalWire four 5) (gate_mem_finalWire four 3))
      (gate_mem_finalWire four 4)
  · exact gate_mem_finalWire four 4

end UpperCircuits

theorem mul_zero_upper : HasCircuit (Mul 0) 0 :=
  ⟨⟨Circuit.empty 0, fun i => Fin.elim0 i⟩⟩

theorem mul_one_upper : HasCircuit (Mul 1) 1 :=
  ⟨⟨UpperCircuits.one, UpperCircuits.one_computes⟩⟩

theorem mul_two_upper : HasCircuit (Mul 2) 3 :=
  ⟨⟨UpperCircuits.two, UpperCircuits.two_computes⟩⟩

theorem mul_three_upper : HasCircuit (Mul 3) 6 :=
  ⟨⟨UpperCircuits.three, UpperCircuits.three_computes⟩⟩

theorem mul_four_upper : HasCircuit (Mul 4) 9 :=
  ⟨⟨UpperCircuits.four, UpperCircuits.four_computes⟩⟩

theorem mul_one_dimension_lower (r : Nat) (h : HasCircuit (Mul 1) r) : 1 ≤ r := by
  rcases h with ⟨⟨C, computes⟩⟩
  exact circuit_lower_bound_of_projection C (Mul 1) TargetCoordinates.oneProjection
    TargetCoordinates.oneProjection_kills_affine TargetCoordinates.oneProjection_Mul computes

theorem mul_two_dimension_lower (r : Nat) (h : HasCircuit (Mul 2) r) : 3 ≤ r := by
  rcases h with ⟨⟨C, computes⟩⟩
  exact circuit_lower_bound_of_projection C (Mul 2) TargetCoordinates.twoProjection
    TargetCoordinates.twoProjection_kills_affine TargetCoordinates.twoProjection_Mul computes

theorem mc_mul_zero : MC(Mul 0) = 0 :=
  mc_eq_of_lower_upper mul_zero_upper (fun _ _ => Nat.zero_le _)

theorem mc_mul_one : MC(Mul 1) = 1 :=
  mc_eq_of_lower_upper mul_one_upper mul_one_dimension_lower

theorem mc_mul_two : MC(Mul 2) = 3 :=
  mc_eq_of_lower_upper mul_two_upper mul_two_dimension_lower

end

end UnrestrictedBooleanMul
