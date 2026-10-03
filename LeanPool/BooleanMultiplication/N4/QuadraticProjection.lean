/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.TwoForm

/-!
# Quadratic ANF projection

This is the coefficient-level bridge between Boolean ANFs and alternating
two-forms.  Diagonal entries are set to zero; off-diagonal entries are the
squarefree quadratic coefficients.  Products of affine ANFs therefore become
decomposable alternating forms.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Extract the coefficients of the eight linear monomials. -/
@[expose]
def anfLinearProjection : ANF 8 →ₗ[F₂] LinearForm where
  toFun p i := p.coeff ⟨{i}⟩
  map_add' p q := by ext i; simp
  map_smul' a p := by ext i; simp

/-- Extract quadratic coefficients, with repeated-index coordinates zero. -/
@[expose] def anfTwoProjection : ANF 8 →ₗ[F₂] TwoForm where
  toFun p i j := if i = j then 0 else p.coeff ⟨{i, j}⟩
  map_add' p q := by
    funext i j
    by_cases h : i = j <;> simp [h]
  map_smul' a p := by
    funext i j
    by_cases h : i = j <;> simp [h]

theorem anfTwoProjection_one : anfTwoProjection (1 : ANF 8) = 0 := by
  funext i j
  by_cases h : i = j
  · change (if i = j then 0 else (1 : ANF 8).coeff ⟨{i, j}⟩) = 0
    rw [ite_eq_left h]
  · change (if i = j then 0 else (1 : ANF 8).coeff ⟨{i, j}⟩) = 0
    rw [ite_eq_right h]
    rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · rename_i heq
      have hc := congrArg (fun s : Monomial 8 => s.vars.card) heq
      simp [h] at hc
    · rfl

theorem anfTwoProjection_X (i : Fin 8) : anfTwoProjection (X i) = 0 := by
  funext j k
  by_cases hjk : j = k
  · change (if j = k then 0 else (X i).coeff ⟨{j, k}⟩) = 0
    rw [ite_eq_left hjk]
  · change (if j = k then 0 else (X i).coeff ⟨{j, k}⟩) = 0
    rw [ite_eq_right hjk, X, coeff_monomial]
    split
    · rename_i heq
      have hc := congrArg Finset.card heq
      simp [hjk] at hc
    · rfl

@[simp] theorem anfLinearProjection_one :
    anfLinearProjection (1 : ANF 8) = 0 := by
  funext i
  change (1 : ANF 8).coeff ⟨{i}⟩ = 0
  rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split
  · rename_i heq
    have hc := congrArg (fun s : Monomial 8 => s.vars.card) heq
    simp at hc
  · rfl

@[simp] theorem anfLinearProjection_X (i j : Fin 8) :
    anfLinearProjection (X i) j = if j = i then 1 else 0 := by
  simp [anfLinearProjection, X, coeff_monomial, eq_comm]

theorem anfTwoProjection_kills_affine :
    affine 8 ≤ LinearMap.ker anfTwoProjection := by
  intro p hp
  refine Submodule.span_induction (p := fun p _ => anfTwoProjection p = 0)
    ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with hq | hq
    · simp only [Set.mem_singleton_iff] at hq
      subst q
      exact anfTwoProjection_one
    · rcases hq with ⟨i, rfl⟩
      exact anfTwoProjection_X i
  · exact map_zero anfTwoProjection
  · intro p q _ _ hp hq
    rw [map_add, hp, hq, add_zero]
  · intro a p _ hp
    rw [map_smul, hp, smul_zero]

theorem vectorWedge_add_left_qp (u v w : LinearForm) :
    vectorWedge (u + v) w = vectorWedge u w + vectorWedge v w := by
  funext i j
  simp only [vectorWedge, Pi.add_apply]
  ring

theorem vectorWedge_add_right_qp (u v w : LinearForm) :
    vectorWedge u (v + w) = vectorWedge u v + vectorWedge u w := by
  funext i j
  simp only [vectorWedge, Pi.add_apply]
  ring

theorem vectorWedge_smul_left_qp (a : F₂) (u v : LinearForm) :
    vectorWedge (a • u) v = a • vectorWedge u v := by
  funext i j
  simp only [vectorWedge, Pi.smul_apply, smul_eq_mul]
  ring

theorem vectorWedge_smul_right_qp (a : F₂) (u v : LinearForm) :
    vectorWedge u (a • v) = a • vectorWedge u v := by
  funext i j
  simp only [vectorWedge, Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem vectorWedge_zero_left_qp (v : LinearForm) :
    vectorWedge 0 v = 0 := by
  funext i j
  simp [vectorWedge]

@[simp] theorem vectorWedge_zero_right_qp (u : LinearForm) :
    vectorWedge u 0 = 0 := by
  funext i j
  simp [vectorWedge]

theorem anfTwoProjection_X_mul_X (i j : Fin 8) :
    anfTwoProjection (X i * X j) =
      vectorWedge (anfLinearProjection (X i)) (anfLinearProjection (X j)) := by
  by_cases hij : i = j
  · subst j
    rw [X_mul_self, anfTwoProjection_X]
    funext k l
    simp only [Pi.zero_apply, vectorWedge, anfLinearProjection_X]
    by_cases hki : k = i <;> by_cases hli : l = i <;>
      simp_all; ring_nf; simp [N3Certificate.two_eq_zero_f2]
  · funext k l
    by_cases hkl : k = l
    · subst l
      change (if k = k then 0 else (X i * X j).coeff ⟨{k, k}⟩) =
        vectorWedge (anfLinearProjection (X i))
          (anfLinearProjection (X j)) k k
      rw [ite_eq_left rfl]
      simp only [anfLinearProjection_X, vectorWedge]
      exact (@CharTwo.add_self_eq_zero F₂ _ _ _).symm
    · have hpair : ({i, j} : Finset (Fin 8)) = {k, l} ↔
          (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
        constructor
        · intro h
          have hi : i = k ∨ i = l := by
            have : i ∈ ({k, l} : Finset (Fin 8)) := by
              rw [← h]
              simp
            simpa using this
          rcases hi with hik | hil
          · left
            refine ⟨hik, ?_⟩
            have hj : j = k ∨ j = l := by
              have : j ∈ ({k, l} : Finset (Fin 8)) := by
                rw [← h]
                simp
              simpa using this
            exact hj.resolve_left (fun hjk => hij (hik.trans hjk.symm))
          · right
            refine ⟨hil, ?_⟩
            have hj : j = k ∨ j = l := by
              have : j ∈ ({k, l} : Finset (Fin 8)) := by
                rw [← h]
                simp
              simpa using this
            exact hj.resolve_right (fun hjl => hij (hil.trans hjl.symm))
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · rfl
          · exact Finset.pair_comm _ _
      have hmul : X i * X j = monomial {i, j} := by simp [X]
      rw [hmul]
      change (if k = l then 0 else (monomial {i, j}).coeff ⟨{k, l}⟩) =
        vectorWedge (anfLinearProjection (X i))
          (anfLinearProjection (X j)) k l
      rw [ite_eq_right hkl]
      rw [coeff_monomial]
      simp only [anfLinearProjection_X, vectorWedge]
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        by_cases hli : l = i <;> by_cases hlj : l = j <;>
          simp_all [eq_comm]

theorem anfTwoProjection_mul_of_affine {p q : ANF 8}
    (hp : p ∈ affine 8) (hq : q ∈ affine 8) :
    IsDecomposableTwo (anfTwoProjection (p * q)) := by
  refine ⟨anfLinearProjection p, anfLinearProjection q, ?_⟩
  refine Submodule.span_induction (p := fun p _ => ∀ q, q ∈ affine 8 →
      anfTwoProjection (p * q) =
        vectorWedge (anfLinearProjection p) (anfLinearProjection q))
    ?_ ?_ ?_ ?_ hp q hq
  · intro x hx q hq
    rcases hx with hx | hx
    · simp only [Set.mem_singleton_iff] at hx
      subst x
      rw [one_mul, anfTwoProjection_kills_affine hq,
        anfLinearProjection_one]
      funext i j
      simp [vectorWedge]
    · rcases hx with ⟨i, rfl⟩
      refine Submodule.span_induction (p := fun q _ =>
          anfTwoProjection (X i * q) =
            vectorWedge (anfLinearProjection (X i)) (anfLinearProjection q))
        ?_ ?_ ?_ ?_ hq
      · intro y hy
        rcases hy with hy | hy
        · simp only [Set.mem_singleton_iff] at hy
          subst y
          rw [mul_one, anfTwoProjection_X, anfLinearProjection_one]
          funext k l
          simp [vectorWedge]
        · rcases hy with ⟨j, rfl⟩
          exact anfTwoProjection_X_mul_X i j
      · simp []
      · intro y z _ _ hy hz
        rw [mul_add, map_add, map_add, vectorWedge_add_right_qp, hy, hz]
      · intro a y _ hy
        rw [mul_smul_comm, map_smul, map_smul,
          vectorWedge_smul_right_qp, hy]
  · simp []
  · intro x y _ _ hx hy q hq
    rw [add_mul, map_add, map_add, vectorWedge_add_left_qp,
      hx q hq, hy q hq]
  · intro a x _ hx q hq
    rw [smul_mul_assoc, map_smul, map_smul,
      vectorWedge_smul_left_qp, hx q hq]

theorem anfTwoProjection_aVar_mul_bVar (i j : Fin 4) :
    anfTwoProjection (aVar 4 i * bVar 4 j) =
      vectorWedge (anfLinearProjection (aVar 4 i))
        (anfLinearProjection (bVar 4 j)) := by
  simpa [aVar, bVar, aCoord, bCoord] using
    anfTwoProjection_X_mul_X (aCoord i) (bCoord j)

@[simp] theorem anfTwoProjection_ite_zero (P : Prop) [Decidable P]
    (p : ANF 8) :
    anfTwoProjection (if P then p else 0) =
      if P then anfTwoProjection p else 0 := by
  by_cases h : P <;> simp [h]

private theorem anfTwoProjection_Mul_0 :
    anfTwoProjection (Mul 4 (0 : Fin 7)) =
      targetTwo (targetBasis (0 : Fin 7)) := by
  rw [Mul, mulCoefficient]
  simp (disch := decide) only [Nat.reduceMul, Nat.add_one_sub_one, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, aVar, bVar,
    Fin.sum_univ_succ, and_true, add_zero, Fin.reduceFinMk, Fin.succ_ne_zero, and_false,
    ↓reduceIte, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, Fin.zero_eta,
    targetBasis, Pi.basisFun_apply]
  simp_rw [anfTwoProjection_X_mul_X]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) [targetTwo, vectorWedge]

private theorem anfTwoProjection_Mul_1 :
    anfTwoProjection (Mul 4 (1 : Fin 7)) =
      targetTwo (targetBasis (1 : Fin 7)) := by
  rw [Mul, mulCoefficient]
  simp (disch := decide) only [Nat.reduceMul, Nat.add_one_sub_one, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.one_mod, aVar, bVar, Fin.sum_univ_succ, Nat.zero_mod, add_zero,
    Fin.reduceFinMk, Fin.val_succ, zero_add, Nat.add_eq_right, Fin.val_eq_zero_iff,
    Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, Finset.univ_unique, Fin.default_eq_zero,
    Fin.val_eq_zero, Finset.sum_const_zero, zero_ne_one, Fin.zero_eta, Fin.succ_ne_zero,
    Finset.sum_ite_eq', Finset.mem_univ, Fin.mk_one, map_add, targetBasis, Pi.basisFun_apply]
  simp_rw [anfTwoProjection_X_mul_X]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) [targetTwo, vectorWedge]

private theorem anfTwoProjection_Mul_2 :
    anfTwoProjection (Mul 4 (2 : Fin 7)) =
      targetTwo (targetBasis (2 : Fin 7)) := by
  rw [Mul, mulCoefficient]
  simp (disch := decide) only [Nat.reduceMul, Nat.add_one_sub_one, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, aVar, bVar, Fin.sum_univ_succ, Nat.zero_mod,
    add_zero, Fin.reduceFinMk, Fin.val_succ, zero_add, Nat.reduceEqDiff, Nat.reduceAdd,
    Nat.add_eq_right, Fin.val_eq_zero_iff, Finset.univ_unique, Fin.default_eq_zero,
    Fin.val_eq_zero, ↓reduceIte, Finset.sum_const_zero, OfNat.zero_ne_ofNat, zero_ne_one,
    Fin.zero_eta, Fin.succ_ne_zero, Fin.mk_one, Finset.sum_ite_eq', Finset.mem_univ, map_add,
    targetBasis, Pi.basisFun_apply]
  simp_rw [anfTwoProjection_X_mul_X]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) [targetTwo, vectorWedge]

private theorem anfTwoProjection_Mul_3 :
    anfTwoProjection (Mul 4 (3 : Fin 7)) =
      targetTwo (targetBasis (3 : Fin 7)) := by
  rw [Mul, mulCoefficient]
  simp (disch := decide) only [Nat.reduceMul, Nat.add_one_sub_one, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, aVar, bVar, Fin.sum_univ_succ, Nat.zero_mod,
    add_zero, Fin.reduceFinMk, Fin.val_succ, zero_add, Nat.reduceEqDiff, Nat.reduceAdd,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, Nat.add_eq_right,
    Fin.val_eq_zero_iff, Finset.sum_ite_irrel, Finset.sum_const, Finset.card_singleton,
    one_smul,  OfNat.zero_ne_ofNat, ↓reduceIte, zero_ne_one,
    Fin.zero_eta, Fin.succ_ne_zero, Fin.mk_one, map_add, targetBasis, Pi.basisFun_apply]
  simp_rw [anfTwoProjection_X_mul_X]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) [targetTwo, vectorWedge]

private theorem anfTwoProjection_Mul_4 :
    anfTwoProjection (Mul 4 (4 : Fin 7)) =
      targetTwo (targetBasis (4 : Fin 7)) := by
  rw [Mul, mulCoefficient]
  simp (disch := decide) only [Nat.reduceMul, Nat.add_one_sub_one, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, aVar, bVar, Fin.sum_univ_succ, Nat.zero_mod,
    add_zero, Fin.reduceFinMk, Fin.val_succ, zero_add, Nat.reduceEqDiff, Nat.reduceAdd,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, Finset.sum_ite_irrel,
    Finset.sum_const, Finset.card_singleton, one_smul,
    OfNat.zero_ne_ofNat, ↓reduceIte, zero_ne_one, Nat.add_eq_right, Fin.val_eq_zero_iff,
    Fin.mk_one, Fin.succ_ne_zero, OfNat.one_ne_ofNat, map_add, targetBasis, Pi.basisFun_apply]
  simp_rw [anfTwoProjection_X_mul_X]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) [targetTwo, vectorWedge]

private theorem anfTwoProjection_Mul_5 :
    anfTwoProjection (Mul 4 (5 : Fin 7)) =
      targetTwo (targetBasis (5 : Fin 7)) := by
  rw [Mul, mulCoefficient]
  simp (disch := decide) only [Nat.reduceMul, Nat.add_one_sub_one, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, aVar, bVar, Fin.sum_univ_succ, Nat.zero_mod,
    add_zero, Fin.reduceFinMk, Fin.val_succ, zero_add, Nat.reduceEqDiff, Nat.reduceAdd,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, Finset.sum_ite_irrel,
    Finset.sum_const, Finset.card_singleton, one_smul,
    OfNat.zero_ne_ofNat, ↓reduceIte, zero_ne_one, Nat.add_eq_right, Fin.val_eq_zero_iff,
    OfNat.one_ne_ofNat, Fin.succ_ne_zero, map_add, targetBasis, Pi.basisFun_apply]
  simp_rw [anfTwoProjection_X_mul_X]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) [targetTwo, vectorWedge]

private theorem anfTwoProjection_Mul_6 :
    anfTwoProjection (Mul 4 (6 : Fin 7)) =
      targetTwo (targetBasis (6 : Fin 7)) := by
  rw [Mul, mulCoefficient]
  simp (disch := decide) only [Nat.reduceMul, Nat.add_one_sub_one, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.mod_succ, aVar, bVar, Fin.sum_univ_succ, Nat.zero_mod, add_zero,
    Fin.reduceFinMk, Fin.val_succ, zero_add, Nat.reduceEqDiff, Nat.reduceAdd,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, Finset.sum_ite_irrel,
    Finset.sum_const, Finset.card_singleton, one_smul,
    OfNat.zero_ne_ofNat, ↓reduceIte, zero_ne_one, OfNat.one_ne_ofNat, targetBasis,
    Pi.basisFun_apply]
  simp_rw [anfTwoProjection_X_mul_X]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp (disch := decide) [targetTwo, vectorWedge]

theorem anfTwoProjection_Mul (s : Fin 7) :
    anfTwoProjection (Mul 4 s) = targetTwo (targetBasis s) := by
  fin_cases s
  · exact anfTwoProjection_Mul_0
  · exact anfTwoProjection_Mul_1
  · exact anfTwoProjection_Mul_2
  · exact anfTwoProjection_Mul_3
  · exact anfTwoProjection_Mul_4
  · exact anfTwoProjection_Mul_5
  · exact anfTwoProjection_Mul_6

theorem targetBasis_reconstruction (c : TargetCoeff) :
    (∑ s : Fin 7, c s • targetBasis s) = c := by
  funext i
  fin_cases i <;>
    simp [targetBasis, Fin.sum_univ_succ, Pi.basisFun]

theorem anfTwoProjection_targetANF (c : TargetCoeff) :
    anfTwoProjection (targetANF c) = targetTwo c := by
  rw [targetANF, map_sum]
  simp_rw [map_smul, anfTwoProjection_Mul]
  change (∑ s : Fin 7, c s • targetTwoLinear (targetBasis s)) = targetTwoLinear c
  have h := congrArg targetTwoLinear (targetBasis_reconstruction c)
  simpa only [map_sum, map_smul] using h

end

end N4
end UnrestrictedBooleanMul
