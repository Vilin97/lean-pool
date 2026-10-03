/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.ReedMuller

/-!
# Semantic bridge for quadratic ANFs

The Reed--Muller argument is phrased recursively as a code.  This file
connects that code to canonical Boolean ANFs without enumerating functions.
Only sparse evaluations and finite sums of monomials are used.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The constant coefficient of a recursively encoded affine polynomial. -/
def AffineCode.constantCoeff : {n : Nat} → AffineCode n → F₂
  | 0, .nil c => c
  | _ + 1, .cons a _ => a.constantCoeff

/-- The linear coefficients of a recursively encoded affine polynomial. -/
def AffineCode.linearCoeff : {n : Nat} →
    AffineCode n → Fin n → F₂
  | 0, .nil _ => fun i => Fin.elim0 i
  | _ + 1, .cons a d => Fin.cases d a.linearCoeff

theorem AffineCode.eval_eq_coeff_formula {n : Nat} (a : AffineCode n)
    (x : Fin n → F₂) :
    a.eval x = a.constantCoeff + ∑ i, a.linearCoeff i * x i := by
  induction a with
  | nil c => simp [AffineCode.constantCoeff, AffineCode.linearCoeff]
  | @cons n a d ih =>
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [AffineCode.constantCoeff, AffineCode.linearCoeff, Fin.sum_univ_succ, ih]
      ring

/-- Encode an affine polynomial from its constant and linear coefficients. -/
def AffineCode.ofCoeffs : (n : Nat) → F₂ →
    (Fin n → F₂) → AffineCode n
  | 0, c, _ => .nil c
  | _ + 1, c, l => .cons (AffineCode.ofCoeffs _ c (fun i => l i.succ)) (l 0)

@[simp] theorem AffineCode.eval_ofCoeffs (n : Nat) (c : F₂)
    (l : Fin n → F₂) (x : Fin n → F₂) :
    (AffineCode.ofCoeffs n c l).eval x = c + ∑ i, l i * x i := by
  induction n with
  | zero => simp [AffineCode.ofCoeffs]
  | succ n ih =>
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [AffineCode.ofCoeffs, Fin.sum_univ_succ, ih]
      ring

/-- Convert an eight-variable affine code to its squarefree Boolean ANF. -/
def AffineCode.anf (a : AffineCode 8) : ANF 8 :=
  a.constantCoeff • (1 : ANF 8) + ∑ i, a.linearCoeff i • X i

theorem AffineCode.anf_mem_affine (a : AffineCode 8) :
    a.anf ∈ affine 8 := by
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (one_mem_affine 8)
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (X_mem_affine i)

@[simp] theorem AffineCode.eval_anf (a : AffineCode 8)
    (x : Fin 8 → F₂) :
    UnrestrictedBooleanMul.eval a.anf x = a.eval x := by
  rw [a.eval_eq_coeff_formula]
  have hsum : UnrestrictedBooleanMul.eval
      (∑ i, a.linearCoeff i • X i) x =
        ∑ i, a.linearCoeff i * x i := by
    rw [eval_eq_evalHom, map_sum]
    simp_rw [map_smul, ← eval_eq_evalHom, eval_X]
    rfl
  simp [AffineCode.anf, eval_add', eval_smul', hsum]

/-- The ANF agrees on every Boolean input with a quadratic code. -/
def QuadraticSemantic (p : ANF 8) : Prop :=
  ∃ q : QuadraticCode 8, ∀ x, q.eval x = eval p x

/-- The subspace of ANFs representing quadratic Boolean functions. -/
def quadraticSemanticSpace : Submodule F₂ (ANF 8) where
  carrier := {p | QuadraticSemantic p}
  zero_mem' := by
    refine ⟨QuadraticCode.zero 8, ?_⟩
    intro x
    simp
  add_mem' := by
    rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a.add b, ?_⟩
    intro x
    simp [ha, hb, eval_add']
  smul_mem' := by
    rintro k p ⟨q, hq⟩
    refine ⟨q.smul k, ?_⟩
    intro x
    simp [hq, eval_smul']

theorem affine_monomial_semantic (i : Fin 8) :
    X i ∈ quadraticSemanticSpace := by
  let a := AffineCode.ofCoeffs 8 0 (fun j => if j = i then 1 else 0)
  refine ⟨a.toQuadratic, ?_⟩
  intro x
  simp [a, eval_X]

theorem one_semantic : (1 : ANF 8) ∈ quadraticSemanticSpace := by
  let a := AffineCode.ofCoeffs 8 1 (fun _ => 0)
  refine ⟨a.toQuadratic, ?_⟩
  intro x
  simp [a, eval_one']

theorem quadratic_monomial_semantic (i j : Fin 8) :
    X i * X j ∈ quadraticSemanticSpace := by
  let a := AffineCode.ofCoeffs 8 0 (fun k => if k = i then 1 else 0)
  let b := AffineCode.ofCoeffs 8 0 (fun k => if k = j then 1 else 0)
  refine ⟨QuadraticCode.mulAffine a b, ?_⟩
  intro x
  simp [a, b, eval_mul', eval_X]

/-- Retain only the coefficients of squarefree monomials of degree at most two. -/
@[expose] def lowReconstruct (p : ANF 8) : ANF 8 :=
  ∑ s : Monomial 8,
    if s.vars.card ≤ 2 then p.coeff s • monomial s.vars else 0

theorem lowReconstruct_eq {p : ANF 8} (hp : DegreeLE 2 p) :
    lowReconstruct p = p := by
  apply MonoidAlgebra.coeff_injective
  ext t
  simp only [lowReconstruct, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single t]
  · by_cases ht : t.vars.card ≤ 2
    · have hself : (monomial t.vars : ANF 8).coeff t = 1 := by
        rw [show t = ⟨t.vars⟩ by cases t; rfl]
        simp
      simp [ht, hself]
    · have hpt : p.coeff t = 0 := hp t (by omega)
      simp [ht, hpt]
  · intro c _hc hct
    have hvars : c.vars ≠ t.vars := by
      intro h
      apply hct
      exact Monomial.ext h
    have hcoeff : (monomial c.vars : ANF 8).coeff t = 0 := by
      rw [show t = ⟨t.vars⟩ by cases t; rfl]
      simp [hvars]
    split_ifs
    · change p.coeff c * (monomial c.vars : ANF 8).coeff t = 0
      rw [hcoeff, mul_zero]
    · simp
  · simp

theorem monomial_semantic_of_card_le_two (s : Monomial 8)
    (hs : s.vars.card ≤ 2) :
    monomial s.vars ∈ quadraticSemanticSpace := by
  interval_cases hcard : s.vars.card
  · have hs0 : s.vars = ∅ := Finset.card_eq_zero.mp hcard
    rw [hs0]
    have hmono : (monomial ∅ : ANF 8) = 1 := by
      rw [monomial, MonoidAlgebra.one_def]
      congr 1
    rw [hmono]
    exact one_semantic
  · rcases Finset.card_eq_one.mp hcard with ⟨i, hi⟩
    rw [hi]
    exact affine_monomial_semantic i
  · rcases Finset.card_eq_two.mp hcard with ⟨i, j, hij, hsij⟩
    rw [hsij]
    simpa [X] using quadratic_monomial_semantic i j

theorem quadratic_semantic_of_degreeLE {p : ANF 8} (hp : DegreeLE 2 p) :
    p ∈ quadraticSemanticSpace := by
  rw [← lowReconstruct_eq hp]
  apply Submodule.sum_mem
  intro s _
  split_ifs with hs
  · exact Submodule.smul_mem _ _ (monomial_semantic_of_card_le_two s hs)
  · exact Submodule.zero_mem _

/-- The Boolean assignment whose nonzero coordinates form the given finite set. -/
@[expose] def supportAssignment (t : Finset (Fin 8)) : Fin 8 → F₂ :=
  fun i => if i ∈ t then 1 else 0

theorem prod_supportAssignment (s t : Finset (Fin 8)) :
    ∏ i ∈ s, supportAssignment t i = if s ⊆ t then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have ih' : (∏ i ∈ s, if i ∈ t then (1 : F₂) else 0) =
          if s ⊆ t then 1 else 0 := by
        simpa [supportAssignment] using ih
      by_cases hit : i ∈ t <;>
        simp [his, hit, ih', supportAssignment, Finset.insert_subset_iff]

theorem eval_monomial_supportAssignment (s t : Finset (Fin 8)) :
    eval (monomial s) (supportAssignment t) =
      if s ⊆ t then 1 else 0 := by
  rw [eval_monomial, prod_supportAssignment]

/-- Evaluate an ANF on the indicator assignment of a finite set. -/
@[expose]
def sparseEvalMap (t : Finset (Fin 8)) : ANF 8 →ₗ[F₂] F₂ :=
  (evalHom (supportAssignment t)).toLinearMap

/-- The second finite difference at zero in two coordinate directions. -/
@[expose]
def pairPolarMap (i j : Fin 8) : ANF 8 →ₗ[F₂] F₂ :=
  sparseEvalMap ∅ + sparseEvalMap {i} + sparseEvalMap {j} +
    sparseEvalMap {i, j}

/-- Extract the coefficient supported on the specified pair of variables. -/
@[expose]
def pairCoeffMap (i j : Fin 8) : ANF 8 →ₗ[F₂] F₂ where
  toFun p := p.coeff ⟨{i, j}⟩
  map_add' p q := by simp
  map_smul' k p := by simp

theorem subset_pair_polar_identity (s : Finset (Fin 8)) (i j : Fin 8)
    (hij : i ≠ j) :
    (if s ⊆ ∅ then (1 : F₂) else 0) +
      (if s ⊆ {i} then 1 else 0) +
      (if s ⊆ {j} then 1 else 0) +
      (if s ⊆ {i, j} then 1 else 0) =
        if s = {i, j} then 1 else 0 := by
  by_cases hs : s ⊆ {i, j}
  · by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
    · have hseq : s = {i, j} := by
        apply Finset.Subset.antisymm hs
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hi
        · exact hj
      subst s
      have hpair_i : ¬ ({i, j} : Finset (Fin 8)) ⊆ {i} := by
        intro h
        have hjpair : j ∈ ({i, j} : Finset (Fin 8)) := by simp
        have hji : j ∈ ({i} : Finset (Fin 8)) := h hjpair
        exact hij (Finset.mem_singleton.mp hji).symm
      have hpair_j : ¬ ({i, j} : Finset (Fin 8)) ⊆ {j} := by
        intro h
        have hipair : i ∈ ({i, j} : Finset (Fin 8)) := by simp
        have hij' : i ∈ ({j} : Finset (Fin 8)) := h hipair
        exact hij (Finset.mem_singleton.mp hij')
      simp [hpair_i, hpair_j]
    · have hseq : s = {i} := by
        apply Finset.Subset.antisymm
        · intro x hx
          have hx' := hs hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
          rcases hx' with rfl | rfl
          · simp
          · exact (hj hx).elim
        · intro x hx
          have hxi : x = i := by simpa using hx
          subst x
          exact hi
      subst s
      have hne : ({i} : Finset (Fin 8)) ≠ {i, j} := by
        intro h
        have hjmem : j ∈ ({i} : Finset (Fin 8)) := by rw [h]; simp
        exact hij (Finset.mem_singleton.mp hjmem).symm
      simp only [Finset.subset_empty, Finset.singleton_ne_empty, ↓reduceIte, Std.le_refl,
        zero_add, Finset.subset_singleton_iff, Finset.singleton_inj, hij, or_self, add_zero,
        Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton, or_false, hne]
      exact CharTwo.add_self_eq_zero 1
    · have hseq : s = {j} := by
        apply Finset.Subset.antisymm
        · intro x hx
          have hx' := hs hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
          rcases hx' with rfl | rfl
          · exact (hi hx).elim
          · simp
        · intro x hx
          have hxj : x = j := by simpa using hx
          subst x
          exact hj
      subst s
      have hji : j ≠ i := Ne.symm hij
      have hne : ({j} : Finset (Fin 8)) ≠ {i, j} := by
        intro h
        have himem : i ∈ ({j} : Finset (Fin 8)) := by rw [h]; simp
        exact hij (Finset.mem_singleton.mp himem)
      simp only [Finset.subset_empty, Finset.singleton_ne_empty, ↓reduceIte,
        Finset.subset_singleton_iff, Finset.singleton_inj, hji, or_self, add_zero,
        Std.le_refl, zero_add, Finset.subset_insert, hne]
      exact CharTwo.add_self_eq_zero 1
    · have hseq : s = ∅ := by
        ext x
        constructor
        · intro hx
          have hx' := hs hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
          rcases hx' with rfl | rfl
          · exact (hi hx).elim
          · exact (hj hx).elim
        · simp
      subst s
      have hne : (∅ : Finset (Fin 8)) ≠ {i, j} := by
        intro h
        have hiempty : i ∈ (∅ : Finset (Fin 8)) := by rw [h]; simp
        simp at hiempty
      simp only [Finset.empty_subset, ite_true, hne, ite_false]
      calc
        (1 : F₂) + 1 + 1 + 1 = (1 + 1) + (1 + 1) := by ac_rfl
        _ = 0 := by rfl
  · have hnone (t : Finset (Fin 8)) (ht : t ⊆ {i, j}) : ¬ s ⊆ t := by
      intro hst
      exact hs (hst.trans ht)
    have hne : s ≠ {i, j} := by
      intro h
      exact hs (by simp [h])
    simp [hs, hne, hnone ∅ (by simp), hnone {i} (by simp), hnone {j} (by simp)]

theorem sparseEvalMap_single (t : Finset (Fin 8)) (s : Monomial 8)
    (c : F₂) :
    sparseEvalMap t (MonoidAlgebra.single s c) =
      c * (if s.vars ⊆ t then 1 else 0) := by
  change evalHom (supportAssignment t) (MonoidAlgebra.single s c) = _
  rw [← eval_eq_evalHom]
  have hsingle : (MonoidAlgebra.single s c : ANF 8) =
      c • monomial s.vars := by
    apply MonoidAlgebra.coeff_injective
    ext u
    rw [show s = ⟨s.vars⟩ by cases s; rfl]
    simp [monomial]
  rw [hsingle, eval_smul', eval_monomial_supportAssignment]

theorem pairPolarMap_eq_pairCoeffMap (i j : Fin 8) (hij : i ≠ j) :
    pairPolarMap i j = pairCoeffMap i j := by
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext
  intro c
  change pairPolarMap i j (MonoidAlgebra.single s c) =
    pairCoeffMap i j (MonoidAlgebra.single s c)
  simp only [pairPolarMap, LinearMap.add_apply]
  rw [sparseEvalMap_single, sparseEvalMap_single,
    sparseEvalMap_single, sparseEvalMap_single]
  change
    c * (if s.vars ⊆ ∅ then 1 else 0) +
      c * (if s.vars ⊆ {i} then 1 else 0) +
      c * (if s.vars ⊆ {j} then 1 else 0) +
      c * (if s.vars ⊆ {i, j} then 1 else 0) =
        (MonoidAlgebra.single s c : ANF 8).coeff ⟨{i, j}⟩
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hid := subset_pair_polar_identity s.vars i j hij
  have heq : s = ⟨{i, j}⟩ ↔ s.vars = {i, j} := by
    constructor
    · intro h
      simp [h]
    · intro h
      exact Monomial.ext h
  calc
    _ = c * ((if s.vars ⊆ ∅ then 1 else 0) +
        (if s.vars ⊆ {i} then 1 else 0) +
        (if s.vars ⊆ {j} then 1 else 0) +
        (if s.vars ⊆ {i, j} then 1 else 0)) := by ring
    _ = c * (if s.vars = {i, j} then 1 else 0) := by rw [hid]
    _ = if s = ⟨{i, j}⟩ then c else 0 := by
      by_cases hs : s.vars = {i, j}
      · rw [ite_eq_left hs, ite_eq_left (heq.mpr hs), mul_one]
      · rw [ite_eq_right hs, ite_eq_right (fun h => hs (heq.mp h)), mul_zero]

theorem anfTwoProjection_congr_of_eval_eq {p q : ANF 8}
    (h : ∀ x, eval p x = eval q x) :
    anfTwoProjection p = anfTwoProjection q := by
  exact congrArg anfTwoProjection (eval_injective 8 (funext h))

/-- The constant-one quadratic code in eight variables. -/
def quadraticOneCode : QuadraticCode 8 :=
  (AffineCode.ofCoeffs 8 1 (fun _ => 0)).toQuadratic

/-- The quadratic expression `1 + p + q + g` used for the zero-zero fiber. -/
def fiber00 (p q g : QuadraticCode 8) : QuadraticCode 8 :=
  ((quadraticOneCode.add p).add q).add g

/-- The quadratic expression `q + g` used for the zero-one fiber. -/
def fiber01 (q g : QuadraticCode 8) : QuadraticCode 8 := q.add g
/-- The quadratic expression `p + g` used for the one-zero fiber. -/
def fiber10 (p g : QuadraticCode 8) : QuadraticCode 8 := p.add g

theorem fiber_truth_identity (u v : F₂) :
    truthBit (1 + u + v + u * v) + truthBit (v + u * v) +
      truthBit (u + u * v) + truthBit (u * v) = 1 := by
  decide +revert

theorem fiber_weights_sum (p q g : QuadraticCode 8)
    (hg : ∀ x, g.eval x = p.eval x * q.eval x) :
    truthWeight (fiber00 p q g).eval +
      truthWeight (fiber01 q g).eval +
      truthWeight (fiber10 p g).eval + truthWeight g.eval = 256 := by
  unfold truthWeight
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hone (x : Fin 8 → F₂) : quadraticOneCode.eval x = 1 := by
    simp [quadraticOneCode]
  simp_rw [fiber00, fiber01, fiber10, QuadraticCode.eval_add,
    hone, hg, fiber_truth_identity]
  simp

theorem QuadraticCode.exists_eval_ne_zero_of_weight_pos
    {q : QuadraticCode 8} (h : 0 < truthWeight q.eval) :
    ∃ x, q.eval x ≠ 0 := by
  by_contra hz
  push Not at hz
  have hall : ∀ x, q.eval x = 0 := hz
  unfold truthWeight at h
  simp [hall, truthBit] at h

theorem QuadraticCode.eval_eq_zero_of_weight_zero
    {q : QuadraticCode 8} (h : truthWeight q.eval = 0) :
    ∀ x, q.eval x = 0 := by
  intro x
  have hx := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Nat.zero_le _)).mp h x (Finset.mem_univ x)
  by_contra hne
  simp [truthBit, hne] at hx

theorem quadratic_product_projection_alternative
    {p q g : ANF 8} (hgate : g = p * q)
    (hp : DegreeLE 2 p) (hq : DegreeLE 2 q) (hg : DegreeLE 2 g) :
    anfTwoProjection g ∈
        Submodule.span F₂ {anfTwoProjection p, anfTwoProjection q} ∨
      IsDecomposableTwo (anfTwoProjection g) := by
  rcases quadratic_semantic_of_degreeLE hp with ⟨pc, hpc⟩
  rcases quadratic_semantic_of_degreeLE hq with ⟨qc, hqc⟩
  rcases quadratic_semantic_of_degreeLE hg with ⟨gc, hgc⟩
  have hcode (x : Fin 8 → F₂) : gc.eval x = pc.eval x * qc.eval x := by
    rw [hgc, hgate, eval_mul', ← hpc, ← hqc]
  have htotal := fiber_weights_sum pc qc gc hcode
  by_cases h00 : truthWeight (fiber00 pc qc gc).eval = 0
  · left
    have hz := QuadraticCode.eval_eq_zero_of_weight_zero h00
    have heval : ∀ x, eval g x = eval ((1 : ANF 8) + p + q) x := by
      intro x
      have hx := hz x
      simp only [fiber00, quadraticOneCode, QuadraticCode.eval_add,
        AffineCode.eval_toQuadratic, AffineCode.eval_ofCoeffs,] at hx
      rw [eval_add', eval_add', eval_one', ← hpc, ← hqc, ← hgc]
      exact (f2_eq_iff_add_eq_zero _ _).2 (by
        simpa [add_assoc, add_comm, add_left_comm] using hx)
    have hproj := anfTwoProjection_congr_of_eval_eq heval
    rw [map_add, map_add, anfTwoProjection_one, zero_add] at hproj
    rw [hproj]
    apply Submodule.add_mem
    · apply Submodule.subset_span
      simp
    · apply Submodule.subset_span
      simp
  · by_cases h01 : truthWeight (fiber01 qc gc).eval = 0
    · left
      have hz := QuadraticCode.eval_eq_zero_of_weight_zero h01
      have heval : ∀ x, eval g x = eval q x := by
        intro x
        have hx := hz x
        simp only [fiber01, QuadraticCode.eval_add] at hx
        rw [← hgc, ← hqc]
        exact (f2_eq_iff_add_eq_zero _ _).2 (by simpa [add_comm] using hx)
      rw [anfTwoProjection_congr_of_eval_eq heval]
      apply Submodule.subset_span
      simp
    · by_cases h10 : truthWeight (fiber10 pc gc).eval = 0
      · left
        have hz := QuadraticCode.eval_eq_zero_of_weight_zero h10
        have heval : ∀ x, eval g x = eval p x := by
          intro x
          have hx := hz x
          simp only [fiber10, QuadraticCode.eval_add] at hx
          rw [← hgc, ← hpc]
          exact (f2_eq_iff_add_eq_zero _ _).2 (by simpa [add_comm] using hx)
        rw [anfTwoProjection_congr_of_eval_eq heval]
        apply Submodule.subset_span
        simp
      · by_cases h11 : truthWeight gc.eval = 0
        · left
          have hz := QuadraticCode.eval_eq_zero_of_weight_zero h11
          have heval : ∀ x, eval g x = eval (0 : ANF 8) x := by
            intro x
            rw [← hgc, hz]
            simp
          rw [anfTwoProjection_congr_of_eval_eq heval, map_zero]
          exact Submodule.zero_mem _
        · have hp00 : 0 < truthWeight (fiber00 pc qc gc).eval :=
            Nat.pos_of_ne_zero h00
          have hp01 : 0 < truthWeight (fiber01 qc gc).eval :=
            Nat.pos_of_ne_zero h01
          have hp10 : 0 < truthWeight (fiber10 pc gc).eval :=
            Nat.pos_of_ne_zero h10
          have hp11 : 0 < truthWeight gc.eval := Nat.pos_of_ne_zero h11
          have hl00 := QuadraticCode.minimum_weight (n := 8) (by omega)
            (QuadraticCode.exists_eval_ne_zero_of_weight_pos hp00)
          have hl01 := QuadraticCode.minimum_weight (n := 8) (by omega)
            (QuadraticCode.exists_eval_ne_zero_of_weight_pos hp01)
          have hl10 := QuadraticCode.minimum_weight (n := 8) (by omega)
            (QuadraticCode.exists_eval_ne_zero_of_weight_pos hp10)
          have hl11 := QuadraticCode.minimum_weight (n := 8) (by omega)
            (QuadraticCode.exists_eval_ne_zero_of_weight_pos hp11)
          have hw11 : truthWeight gc.eval = 64 := by norm_num at hl00 hl01 hl10 hl11 ⊢; omega
          rcases QuadraticCode.minimum_word_factor (n := 8) (by omega)
              (QuadraticCode.exists_eval_ne_zero_of_weight_pos hp11)
              (by norm_num; exact hw11) with ⟨a, b, hab⟩
          right
          have heval : ∀ x, eval g x = eval (a.anf * b.anf) x := by
            intro x
            rw [eval_mul', a.eval_anf, b.eval_anf, ← hab, hgc]
          rw [anfTwoProjection_congr_of_eval_eq heval]
          exact anfTwoProjection_mul_of_affine a.anf_mem_affine b.anf_mem_affine

end

end N4
end UnrestrictedBooleanMul
