/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1

/-!
# Linear regression

over ℝ or ℂ
-/

/-- The model subspace for simple linear regression: the span of the data vector
`x` and the all-ones vector inside `EuclideanSpace R (Fin n)`. -/
noncomputable def K₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) :=
    @Submodule.span R (EuclideanSpace R (Fin n)) _ _ _ {WithLp.toLp 2 x, WithLp.toLp 2 fun _ => 1}

theorem hxK₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) : WithLp.toLp 2 x ∈ K₁ x :=
    Submodule.mem_span_of_mem (Set.mem_insert (WithLp.toLp 2 x) {WithLp.toLp 2 fun _ ↦ 1})
theorem h1K₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) : WithLp.toLp 2 (fun _ ↦ 1) ∈ K₁ x :=
    Submodule.mem_span_of_mem (Set.mem_insert_of_mem (WithLp.toLp 2 x) rfl)

theorem topsub₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) :
    ⊤ ≤ Submodule.span R (Set.range ![(⟨WithLp.toLp 2 x, hxK₁ x⟩ : K₁ x),
      (⟨WithLp.toLp 2 fun _ => 1, h1K₁ x⟩ : K₁ x)]) := by
  refine top_le_iff.mpr (Submodule.eq_top_iff'.mpr ?_)
  intro a
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton]
  apply Submodule.mem_span_pair.mpr
  obtain ⟨c,d,hcd⟩ := Submodule.mem_span_pair.mp a.2
  use d, c
  rw [Subtype.ext_iff]
  push_cast
  rw [← hcd]
  rw [add_comm]



/-- The two spanning vectors of `K₁ x` as elements of the subspace, used as a basis. -/
def Kvec₁ {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) :=
    ![(⟨WithLp.toLp 2 x, hxK₁ x⟩ : K₁ x), (⟨WithLp.toLp 2 fun _ => 1, h1K₁ x⟩ : K₁ x)]


/-- Given points `(x i, y i)`, obtain the coordinates `[c, d]` such that
`y = c x + d` is the best fit regression line. -/
noncomputable def regression_coordinates₁ {n : ℕ} {R : Type*} [RCLike R] (x y : Fin n → R)
    (lin_indep : LinearIndependent R (Kvec₁ x)) :
    Fin 2 → R := fun i => ((Module.Basis.mk lin_indep (topsub₁ _)).repr
      ⟨Submodule.starProjection (K₁ x) (WithLp.toLp 2 y),
       Submodule.starProjection_apply_mem (K₁ x) (WithLp.toLp 2 y)⟩) i


local notation x "ᵀ" => Matrix.transpose x

/-- The design matrix `[x | 1]` of simple linear regression. -/
def A {m : ℕ} {R : Type*} [RCLike R] (x : Fin m → R) : Matrix (Fin m) (Fin 2) R :=
    ![x, fun _ => 1]ᵀ -- or maybe (Matrix.of ![x, fun _ => 1])ᵀ

/-- The least-squares coefficients `(AᵀA)⁻¹ Aᵀ y` for the design matrix `A x`. -/
noncomputable def getCoeffs {m : ℕ} {R : Type*} [RCLike R] (x y : Fin m → R) :=
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A x)ᵀ) (A x))⁻¹ ((A x)ᵀ))
  (fun i (_ : Fin 1) => y i)

/-- getCoeffs is supposed to mimize this -/
def theDistance {m : ℕ} {R : Type*} [RCLike R] (x y : Fin m → R)
  (M : Matrix (Fin 2) (Fin 1) R) : R :=
  Finset.sum (Finset.univ : Finset (Fin m))
    (fun i => by exact (y i - (M 0 0 + (M 1 0) * (x i)))^2)

lemma matrix_smul {m : ℕ} {R : Type*} [RCLike R] (b : Matrix (Fin m) (Fin 1) R)
    (v : Matrix (Fin 2) (Fin 2) R) (c : R)
    (o : Matrix (Fin m) (Fin 2) R) (i : Matrix (Fin 2) (Fin m) R) :
    o * (c • v * i * b) = c • (o * (v * i * b)) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul]


lemma getx {m : ℕ} {R : Type*} [RCLike R] (x : Fin m → R) (c : R) (e : Matrix (Fin 2) (Fin 1) R) :
    ((c • e) 0 0 • x + (c • e) 1 0 • fun (_ : Fin m) ↦ (1:R)) =
    fun i ↦ (c • (Matrix.mulᵣ (A x) e)) i 0 := by
  have ho (o : R) :  c * e 0 0 * o + c * e 1 0
    =  c * (e 0 0 * o + e 1 0) := by rw [mul_assoc,left_distrib]
  by_cases H : c = 0
  · rw [H]
    simp only [
      Fin.isValue, Matrix.smul_apply, smul_eq_mul, zero_mul, zero_smul, add_zero, Matrix.mulᵣ_eq]
    ext i
    simp
  · unfold A
    ext i
    simp only [
      Fin.isValue, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply, mul_one,
      Matrix.mulᵣ_eq]
    rw [ho]
    apply (IsUnit.mul_right_inj (Ne.isUnit H)).mpr
    rw [mul_comm]
    /- this looks hard now but we can spell it out for Lean
     in great detail: -/
    have : e 1 0 = (fun x : Fin m => 1) i * e 1 0 := by
        simp
    rw [this]
    have : x i = (fun i => x i) i := by simp
    rw [this]
    have : x = fun i => x i := rfl
    nth_rw 2 [this]
    unfold Matrix.transpose
    have : (fun i => x i) = ![fun i ↦ x i, fun x ↦ 1] 0 := rfl
    nth_rw 1 [this]
    have : (fun x => 1) = ![fun i ↦ x i, fun x ↦ 1] 1 := rfl
    nth_rw 2 [this]
    generalize ![fun i ↦ x i, fun x ↦ 1] = q
    have : q 0 i * e 0 0 + q 1 i * e 1 0
        = ∑ j : Fin 2, q j i * e j 0 := by simp
    rw [this]
    congr


lemma getDet {n : ℕ} {R : Type*} [RCLike R] (x : Fin n → R) :
    !![∑ i : Fin n, x i ^ 2, ∑ i : Fin n, x i; ∑ i : Fin n, x i, n]⁻¹ =
        ((∑ i : Fin n, x i ^ 2) * n - (∑ i : Fin n, x i) ^ 2)⁻¹ •
      !![(n : R), -(∑ i : Fin n, x i); -(∑ i : Fin n, x i), ∑ i : Fin n, x i ^ 2] := by
    rw [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two]
    simp only [
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Ring.inverse_eq_inv', Matrix.smul_of, Matrix.smul_cons, smul_eq_mul,
      mul_neg, Matrix.smul_empty, EmbeddingLike.apply_eq_iff_eq, Matrix.vecCons_inj,
      mul_eq_mul_right_iff, inv_inj, sub_right_inj, Nat.cast_eq_zero, neg_inj, and_true]
    constructor
    · constructor
      · ring_nf
        left
        trivial
      · left
        ring_nf
    · constructor <;>
      · left
        ring_nf

lemma matmulcase {m : ℕ} {R : Type*} [RCLike R] (x : Fin m → R) :
    Matrix.mulᵣ ![x, fun _ ↦ 1] (![x, fun _ ↦ 1]ᵀ) = !![∑ i, x i ^ 2, ∑ i, x i; ∑ i, x i, ↑m] := by
    unfold Matrix.mulᵣ
    rw [Matrix.transpose_transpose]
    ext i j
    fin_cases i
    · fin_cases j
      · simp only [
          Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.dotProductᵣ_eq, FinVec.map_eq, Fin.zero_eta,
          Fin.isValue, Matrix.of_apply, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val',
          Matrix.cons_val_fin_one]
        suffices  x ⬝ᵥ x = ∑ i, x i * x i by
            rw [this]
            congr
            ext i
            symm
            exact pow_two (x i)
        rfl
      · simp only [
          Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.dotProductᵣ_eq, FinVec.map_eq, Fin.zero_eta,
          Fin.isValue, Fin.mk_one, Matrix.of_apply, Function.comp_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val']
        suffices  x ⬝ᵥ (fun _ => 1) = ∑ i, x i * 1 by
            rw [this]
            congr
            ext i
            symm
            simp
        rfl
    · fin_cases j
      · simp only [
          Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.dotProductᵣ_eq, FinVec.map_eq, Fin.mk_one,
          Fin.isValue, Fin.zero_eta, Matrix.of_apply, Function.comp_apply, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val']
        suffices  (fun x ↦ 1) ⬝ᵥ x = ∑ i, 1 * x i by
            rw [this]
            congr
            ext i
            symm
            simp
        rfl
      · simp only [
          Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.dotProductᵣ_eq, FinVec.map_eq, Fin.mk_one,
          Fin.isValue, Matrix.of_apply, Function.comp_apply, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Matrix.cons_val']
        suffices  (fun x ↦ (1 : R)) ⬝ᵥ (fun x => 1) = ∑ i : Fin m, 1 * 1 by
            rw [this]
            simp
        rfl

lemma matrix_algebra {n t o w : ℕ} {R : Type*} [RCLike R]
    (B : Matrix (Fin n) (Fin t) R)
    (hB : IsUnit (Bᵀ * B).det)
    (m : Fin t → Fin o → R)
    (P : Matrix (Fin n) (Fin w) R) :
    mᵀ * Bᵀ * P = mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P)) := by
  suffices  (mᵀ * Bᵀ * P) = (mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) by
    rw [this]
  have h₁ : (Bᵀ * B) * ((Bᵀ * B)⁻¹) = 1 := Matrix.mul_nonsing_inv (Bᵀ * B) hB
  have h₀ :  mᵀ * Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))
          =  mᵀ * (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) := by
        simp [Matrix.mul_assoc]
  rw [h₀]
  have : mᵀ * Bᵀ * P = mᵀ * (Bᵀ * P) := by
    simp [Matrix.mul_assoc]
  rw [this]
  suffices  (Bᵀ * P) = (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ * P))) by
    rw [this]
  have : Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ    * P)) =
        (Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ))) * P := by
    simp [Matrix.mul_assoc]
  rw [this]
  suffices Bᵀ = Bᵀ * (B * ((Bᵀ * B)⁻¹ * Bᵀ)) by
    nth_rw 1 [this]
  repeat rw [← Matrix.mul_assoc]
  rw [h₁]
  simp

/-- The fitted values "y-hat" of the regression line at each data point `x i`. -/
noncomputable def hat {m : ℕ} (x y : Fin m → ℝ) (h : LinearIndependent ℝ (Kvec₁ x)) : Fin m → ℝ :=
    by
  intro i
  let c := regression_coordinates₁ x y h
  exact c 0 * x i + c 1

/-- The value "y bar". -/
noncomputable def bar {m : ℕ} (y : Fin m → ℝ) : ℝ :=
    (1 / m) * ∑ i : Fin m, y i


/-- A data vector is nonconstant if it takes at least two distinct values. -/
def nonconstant {m : ℕ} (x : Fin m → ℝ) := ∃ i, ∃ j, x i ≠ x j

lemma isunit_of_nonconstant {m : ℕ} (x : Fin m → ℝ)
    (hx : (∑ i, (x i ^ 2)) * ↑m - (∑ i, x i) ^ 2 ≠ 0) :
    IsUnit (A xᵀ * A x).det := by
  unfold A
  rw [Matrix.transpose_transpose]
  rw [← Matrix.mulᵣ_eq]
  rw [matmulcase]
  simp only [Matrix.det_fin_two_of, isUnit_iff_ne_zero, ne_eq]
  contrapose! hx
  linarith



lemma sum_of_constant' {m : ℕ} (x : Fin m → ℝ) (h : nonconstant x) :
    (∑ (f ∈ {j : Fin 2 → Fin m | j 0 ≠ j 1 }),
    (x (f 0) - x (f 1)) ^ 2) ≠ 0 := by -- OH BUT ALL THE DIAGONAL STUFF IS UNNECESSARY?
  contrapose! h
  unfold nonconstant
  push Not
  intro i j
  by_cases H : i = j
  · rw [H]
  · let f : Fin 2 → Fin m := ![i, j]
    suffices (x i - x j)^2 = 0 by
        simp at this
        linarith
    apply le_antisymm
    · calc _ ≤ ∑ f : Fin 2 → Fin m with f 0 ≠ f 1, (x (f 0) - x (f 1)) ^ 2 := by
            have hu : Finset.filter (fun f : Fin 2 → Fin m => f 0 ≠ f 1) (Finset.univ)
              = Finset.filter (fun f : Fin 2 → Fin m => f 0 ≠ f 1 ∧ f = ![i,j]) (Finset.univ)
              ∪ Finset.filter (fun f : Fin 2 → Fin m => f 0 ≠ f 1 ∧ f ≠ ![i,j]) (Finset.univ)
                := by ext;simp;tauto
            rw [hu]
            rw [Finset.sum_union]
            · simp only [Fin.isValue, ne_eq, Nat.succ_eq_add_one, Nat.reduceAdd, ge_iff_le]
              have : ∑ x_1 with x_1 0 ≠ x_1 1 ∧ x_1 = ![i, j], (x (x_1 0) - x (x_1 1)) ^ 2
                = (x i - x j)^2 := by
                    calc _ = ∑ x_1 with x_1 = ![i, j], (x (x_1 0) - x (x_1 1)) ^ 2 := by
                            congr
                            ext l
                            simp only [
                              Fin.isValue, ne_eq, Nat.succ_eq_add_one, Nat.reduceAdd,
                              and_iff_right_iff_imp]
                            intro hl
                            rw [hl]
                            simp
                            tauto
                         _ = _ := by
                                calc _ = ∑ x_1 with x_1 = ![i, j],
                                    (x (![i, j] 0) - x (![i, j] 1)) ^ 2 := by
                                        apply le_antisymm <;>
                                        · refine Finset.sum_le_sum ?_
                                          intro l hl
                                          simp only [
                                            Nat.succ_eq_add_one, Nat.reduceAdd, Finset.mem_filter,
                                            Finset.mem_univ, true_and] at hl
                                          rw [hl]
                                     _ = (x (![i, j] 0) - x (![i, j] 1)) ^ 2 := by
                                            simp only [
                                              Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
                                              Matrix.cons_val_zero, Matrix.cons_val_one,
                                              Matrix.cons_val_fin_one, Finset.sum_const,
                                              nsmul_eq_mul]
                                            have : Finset.filter (fun x_1 => x_1 = ![i,j])
                                                Finset.univ = {![i,j]} := by
                                                ext
                                                simp
                                            rw [this]
                                            simp
                                     _ = _ := by simp
              rw [this]
              suffices 0 ≤ ∑ x_1 with ¬x_1 0 = x_1 1 ∧ ¬x_1 = ![i, j],
                  (x (x_1 0) - x (x_1 1)) ^ 2 by
                linarith
              refine Finset.sum_nonneg ?_
              intro k _
              positivity
            · refine Finset.disjoint_filter.mpr ?_
              tauto
           _ ≤ _ := by rw [h]
    · positivity

attribute [local instance] Classical.propDecidable

/-- A "missing lemma" in Mathlib? -/
lemma Finset.sum_iUnion {k : ℕ} {T : Type*} [Fintype T]
    (A : Fin k → Finset T) (X : T → ℝ)
    (h : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint A) :
    ∑ i : T with i ∈ (⋃ j, A j), X i = ∑ j, ∑ i with i ∈ A j, X i := by
    have := @Finset.sum_biUnion T (Fin k) ℝ _ (fun i => X i)
        _ Finset.univ A h
    simp only at this
    have h₀ : ∑ j, ∑ i with i ∈ A j, X i
        = ∑ j, ∑ i ∈ A j, X i := by simp only [Finset.filter_univ_mem]
    rw [h₀]
    rw [← this]
    congr
    ext i
    simp

lemma decompose_pair_sum {n : ℕ} (f : Fin n → ℝ) :  ∑ x : Fin 2 → Fin n, f (x 0)
                                             = ∑ i, ∑ g : Fin 2 → Fin n with g 0 = i, f (g 0) := by
    let A : Fin n → Finset (Fin 2 → Fin n) := by
        intro j
        exact Finset.filter (fun f => f 0 = j) Finset.univ
    have := @Finset.sum_iUnion n (Fin 2 → Fin n) _ A (fun σ => f (σ 0))
        (by
            simp only [Finset.coe_univ, Fin.isValue, A]
            apply Set.pairwiseDisjoint_filter)
    unfold A at this
    have h₀ : ⋃ j, (↑(Finset.filter (fun i : Fin 2 → Fin n => i 0 = j) Finset.univ) :
        Set (Fin 2 → Fin n)) = Set.univ := by
        ext
        simp
    rw [h₀] at this
    simp only [
      Set.mem_univ, Finset.filter_true, Fin.isValue, Finset.mem_filter, Finset.mem_univ,
      true_and] at this
    exact this


lemma diagonalSq {m : ℕ} (x : Fin m → ℝ)
  (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1, x (x_2 0) ^ 2 = ∑ i, x i ^ 2 := by
    have := @Finset.sum_bijective ({σ : Fin 2 → Fin m // σ 1 = x_1}) (
        Fin m) ℝ _ Finset.univ Finset.univ
        (fun σ => x (σ.1 0)^2) (fun i => x i^2) (fun σ => σ.1 0) (by
            constructor
            · intro σ τ h
              simp only [Fin.isValue] at h
              ext i
              fin_cases i
              · simp only [Fin.isValue, Fin.zero_eta]
                rw [h]
              · simp only [Fin.isValue, Fin.mk_one]
                rw [σ.2, τ.2]
            · intro z
              use ⟨![z,x_1], by simp⟩
              simp) (by simp) (by simp)
    simp only [Fin.isValue] at this
    rw [← this]
    change
     (@Finset.sum (Fin 2 → Fin m) ℝ _ {x_2 | x_2 1 = x_1} fun x_2 ↦ x (x_2 0) ^ 2) =
      @Finset.sum { σ : Fin 2 → Fin m // σ 1 = x_1 } ℝ _ Finset.univ (fun x_2 => x (x_2.1 0) ^ 2)
    rw [Finset.sum_subtype]
    intro σ
    simp

lemma sum_ij_xi2 {m : ℕ} (x : Fin m → ℝ) :
        ∑ σ : Fin 2 → Fin m, (x (σ 0) ^ 2) =
    m * ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 0) * x (σ 1)
     := by
  have : ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 1)
       = ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 0) := by
    repeat rw [Finset.sum_filter]
    congr
    ext i
    split_ifs with g₀
    · rw [g₀]
    · rfl
  rw [this]
  have :  ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 0)
    =  ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) ^2 := by
        congr
        ring_nf
  rw [this]
  have hf := @Finset.sum_iUnion m (Fin 2 → Fin m) _
    (fun j : Fin m => Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 1 = j ∧ x_1 0 = j) Finset.univ)
    (fun x_1 => x (x_1 0)^2) (by
        refine Finset.pairwiseDisjoint_iff.mpr ?_
        intro i _ j _ h₀
        have : ∃ x_1 : Fin 2 → Fin m,
            x_1 ∈ ({x_1 | x_1 1 = i ∧ x_1 0 = i} ∩ {x_1 | x_1 1 = j ∧ x_1 0 = j}) := by
            refine Set.inter_nonempty_iff_exists_left.mp ?_
            refine Set.toFinset_nonempty.mp ?_
            simp only [Fin.isValue, Set.toFinset_inter, Set.toFinset_setOf]
            exact h₀
        obtain ⟨k,hk⟩ := this
        simp only [Fin.isValue, Set.mem_inter_iff, Set.mem_setOf_eq] at hk
        apply Eq.trans hk.1.1.symm
        tauto)
  simp only [
    Fin.isValue, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_iUnion, Set.mem_setOf_eq,
    exists_eq_left', Finset.mem_filter] at hf
  rw [hf]
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_2 0) ^ 2
    = ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 := by
    apply le_antisymm <;> (
    apply Finset.sum_le_sum
    intro i hi
    simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [← hi.2])
  simp_rw [this]
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2
    =  ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 * 1 := by simp
  simp_rw [this]
  have (x_1 : Fin m) :
    ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 * 1
    = x (x_1) ^ 2 * ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, 1
    := by rw [Finset.mul_sum]
  simp_rw [this]
  simp only [Fin.isValue, Finset.sum_const, nsmul_eq_mul, mul_one]
  have (i : Fin m) : @Finset.card (Fin 2 → Fin m) {σ | σ 1 = i ∧ σ 0 = i}
   = 1 := by
   have : Finset.filter (fun σ : Fin 2 → Fin m => σ 1 = i ∧ σ 0 = i) Finset.univ = {![i,i]} := by
    ext σ
    simp only [
      Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and, Nat.succ_eq_add_one, Nat.reduceAdd,
      Finset.mem_singleton]
    constructor
    · intro hσ
      ext j
      fin_cases j <;> tauto
    · intro hσ
      rw [hσ]
      simp
   rw [this]
   simp
  simp_rw [this]
  simp only [Fin.isValue, Nat.cast_one, mul_one]
  have : ∑ x_1 : Fin 2 → Fin m, x (x_1 0) ^2
   = ∑ x_1 : Fin 2 → Fin m with ∃ j, x_1 1 = j, x (x_1 0) ^2 := by
    repeat rw [Finset.sum_filter]
    congr
    ext i
    split_ifs with g₀
    · rfl
    · exfalso;apply g₀;use i 1
  rw [this]
  have : ∑ x_1 : Fin 2 → Fin m with ∃ j, x_1 1 = j, x (x_1 0) ^2
    = ∑ x_1 with x_1 ∈ (⋃ j, {x_1 : Fin 2 → Fin m | x_1 1 = j}), x (x_1 0) ^2 := by
    repeat rw [Finset.sum_filter]
    simp
  rw [this]
  have hf := @Finset.sum_iUnion m (Fin 2 → Fin m) _
    (fun j : Fin m => Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 1 = j) Finset.univ)
    (fun x_1 => x (x_1 0)^2) (by
        refine Finset.pairwiseDisjoint_iff.mpr ?_
        intro i _ j _ h₀
        have : ∃ x_1 : Fin 2 → Fin m, x_1 ∈ ({x_1 | x_1 1 = i} ∩ {x_1 | x_1 1 = j}) := by
            refine Set.inter_nonempty_iff_exists_left.mp ?_
            refine Set.toFinset_nonempty.mp ?_
            simp only [Fin.isValue, Set.toFinset_inter, Set.toFinset_setOf]
            exact h₀
        obtain ⟨k,hk⟩ := this
        simp only [Fin.isValue, Set.mem_inter_iff, Set.mem_setOf_eq] at hk
        apply Eq.trans hk.1.symm
        tauto)
  have := @Finset.sum_biUnion (Fin 2 → Fin m) (Fin m) ℝ _ (fun x_1 => x (x_1 0) ^ 2)
    _ Finset.univ (fun j => {x_1 | x_1 1 = j}) (by apply Set.pairwiseDisjoint_filter)
  simp only [Fin.isValue] at this
  suffices  m * ∑ x_1, x x_1 ^ 2 = ∑ x_1 ∈ Finset.univ.biUnion fun j ↦
      {x_1 : Fin 2 → Fin m | x_1 1 = j}, x (x_1 0) ^ 2 by
    rw [this]
    congr
    simp only [Fin.isValue, Set.mem_iUnion, Set.mem_setOf_eq, exists_eq', Finset.filter_true]
    ext i
    simp
  rw [this]
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1, x (x_2 0) ^ 2
                     = ∑ i : Fin m, x (i) ^ 2 := by
    apply diagonalSq
  simp_rw [this]
  generalize  ∑ x_1, x x_1 ^ 2 = X
  simp


lemma offDiagonalSq {m : ℕ} (x : Fin m → ℝ) :
    (∑ (f : Fin 2 → Fin m) with f 0 ≠ f 1, x (f 1) ^ 2) =
    (m - 1) * ∑ i : Fin m, x i ^ 2 := by
  have h₀ := @sum_ij_xi2 m x
  have h₁ : ∑ σ : Fin 2 → Fin m, x (σ 1) ^ 2 =
         ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 1) ^ 2
       + ∑ σ : Fin 2 → Fin m with σ 0 ≠ σ 1, x (σ 1) ^ 2 := by
       rw [← Finset.sum_union]
       · simp only [Fin.isValue, ne_eq]
         congr
         ext σ
         simp
         tauto
       · apply Finset.disjoint_filter_filter_not
  have h₂ : ∑ σ : Fin 2 → Fin m with σ 0 ≠ σ 1, x (σ 1) ^ 2
         =  ∑ σ : Fin 2 → Fin m, x (σ 1) ^ 2
         - ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 1) ^ 2 := by linarith
  rw [h₂]
  have h₅ : ∑ x_1 : Fin 2 → Fin m, x (x_1 0) ^ 2
       = ∑ x_1 : Fin 2 → Fin m, x (x_1 1) ^ 2 := by
    have := @Finset.sum_bijective (Fin 2 → Fin m) (Fin 2 → Fin m)
        ℝ _ (Finset.univ)
        (Finset.univ)
        (fun σ => x (σ 0)^2)
        (fun σ => x (σ 1)^2)
        (fun σ => ![σ 1, σ 0])
        (by
            constructor
            · intro x y h
              simp at h
              ext i
              fin_cases i <;> tauto
            · intro x
              use ![x 1, x 0]
              simp only [
                Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
              ext i
              fin_cases i <;> tauto) (by
                intro σ
                simp) (by
                intro σ
                simp)
    convert this
  have h₄ : ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 1) ^ 2 = ∑ i, x i^2 := by
    have := @Finset.sum_bijective ({σ : Fin 2 → Fin m // σ 0 = σ 1}) (
        Fin m) ℝ _ Finset.univ Finset.univ
        (fun σ => x (σ.1 1)^2) (fun i => x i^2) (fun σ => σ.1 0) (by
            constructor
            · intro σ τ h
              simp only [Fin.isValue] at h
              ext i
              fin_cases i
              · simp only [Fin.isValue, Fin.zero_eta]
                rw [h]
              · simp only [Fin.isValue, Fin.mk_one]
                rw [← σ.2, ← τ.2]
                rw [h]
            · intro z
              use ⟨![z,z], by simp⟩
              simp) (by simp) (by simp only [
              Fin.isValue, Finset.mem_univ, forall_const, Subtype.forall];intro a ha;rw [ha])
    simp only [Fin.isValue] at this
    rw [← this]
    rw [Finset.sum_subtype]
    intro σ
    simp
  have h₃ : ∑ σ : Fin 2 → Fin m, x (σ 1) ^ 2  = m * ∑ i, x i^2 := by
    rw [← h₄]
    rw [← h₅]
    rw [h₀]
    suffices ∑ σ : Fin 2 → Fin m with σ 0 = σ 1, x (σ 0) * x (σ 1) =  ∑ σ : Fin 2 →
        Fin m with σ 0 = σ 1, x (σ 1) ^ 2 by
        rw [this]
    apply le_antisymm <;> (
    apply Finset.sum_le_sum
    intro i hi
    simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hi]
    ring_nf
    simp)
  linarith


lemma determinant_value_nonzero_of_nonconstant {m : ℕ} (x : Fin m → ℝ) (h : nonconstant x) :
  (∑ i, (x i ^ 2)) * ↑m - (∑ i, x i) ^ 2 ≠ 0 := by
  contrapose! h
  rw [Fintype.sum_pow] at h
  simp only [Fin.prod_univ_two, Fin.isValue] at h
  have : (Finset.univ : Finset (Fin 2 → Fin m)) =
      Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 0 = x_1 1) Finset.univ
    ∪ Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 0 ≠ x_1 1) Finset.univ := by
    ext;simp;tauto
  have : ∑ x_1 : Fin 2 → Fin m, (x (x_1 0) * x (x_1 1))
    = ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 1)
    + ∑ x_1 : Fin 2 → Fin m with x_1 0 ≠ x_1 1, x (x_1 0) * x (x_1 1)
    := by
        nth_rw 1 [this]
        rw [Finset.sum_union]
        apply Finset.disjoint_filter_filter_not
  rw [this] at h
  -- helper start
  have : ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 1)
       = ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 0) := by
    repeat rw [Finset.sum_filter]
    congr
    ext i
    split_ifs with g₀
    · rw [g₀]
    · rfl
  rw [this] at h
  have :  ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) * x (x_1 0)
    =  ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) ^2 := by
        congr
        ring_nf
  rw [this] at h
  have : ∑ x_1 : Fin 2 → Fin m with x_1 0 = x_1 1, x (x_1 0) ^2
   = ∑ x_1 : Fin 2 → Fin m with ∃ j, x_1 0 = j ∧ x_1 1 = j, x (x_1 0) ^2 := by
    repeat rw [Finset.sum_filter]
    congr
    ext i
    split_ifs with g₀ g₁ g₂
    · rw [g₀]
    · push Not at g₁
      specialize g₁ (i 0) (rfl)
      tauto
    · exfalso;apply g₀;obtain ⟨j,hj⟩ := g₂;apply Eq.trans hj.1 hj.2.symm
    · rfl
  have : ∑ x_1 : Fin 2 → Fin m with ∃ j, x_1 0 = j ∧ x_1 1 = j, x (x_1 0) ^2
    = ∑ x_1 with x_1 ∈ (⋃ j, {x_1 : Fin 2 → Fin m | x_1 0 = j ∧ x_1 1 = j}), x (x_1 0) ^2 := by
    repeat rw [Finset.sum_filter]
    simp
  have hf := @Finset.sum_iUnion m (Fin 2 → Fin m) _
    (fun j : Fin m => Finset.filter (fun x_1 : Fin 2 → Fin m => x_1 1 = j ∧ x_1 0 = j) Finset.univ)
    (fun x_1 => x (x_1 0)^2) (by
        refine Finset.pairwiseDisjoint_iff.mpr ?_
        intro i _ j _ h₀
        have : ∃ x_1 : Fin 2 → Fin m,
            x_1 ∈ ({x_1 | x_1 1 = i ∧ x_1 0 = i} ∩ {x_1 | x_1 1 = j ∧ x_1 0 = j}) := by
            refine Set.inter_nonempty_iff_exists_left.mp ?_
            refine Set.toFinset_nonempty.mp ?_
            simp only [Fin.isValue, Set.toFinset_inter, Set.toFinset_setOf]
            exact h₀
        obtain ⟨k,hk⟩ := this
        simp only [Fin.isValue, Set.mem_inter_iff, Set.mem_setOf_eq] at hk
        apply Eq.trans hk.1.1.symm
        tauto)
  simp only [
    Fin.isValue, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_iUnion, Set.mem_setOf_eq,
    exists_eq_left', Finset.mem_filter] at hf
  rw [hf] at h
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_2 0) ^ 2
    = ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 := by
    apply le_antisymm <;> (
    apply Finset.sum_le_sum
    intro i hi
    simp only [Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [← hi.2])
  simp_rw [this] at h
  have (x_1 : Fin m) : ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2
    =  ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 * 1 := by simp
  simp_rw [this] at h
  have (x_1 : Fin m) :
    ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, x (x_1) ^ 2 * 1
    = x (x_1) ^ 2 * ∑ x_2 : Fin 2 → Fin m with x_2 1 = x_1 ∧ x_2 0 = x_1, 1
    := by rw [Finset.mul_sum]
  simp_rw [this] at h
  simp only [Fin.isValue, Finset.sum_const, nsmul_eq_mul, mul_one, ne_eq] at h
  have (i : Fin m) : @Finset.card (Fin 2 → Fin m) {σ | σ 1 = i ∧ σ 0 = i}
   = 1 := by
   have : Finset.filter (fun σ : Fin 2 → Fin m => σ 1 = i ∧ σ 0 = i) Finset.univ = {![i,i]} := by
    ext σ
    simp only [
      Fin.isValue, Finset.mem_filter, Finset.mem_univ, true_and, Nat.succ_eq_add_one, Nat.reduceAdd,
      Finset.mem_singleton]
    constructor
    · intro hσ
      ext j
      fin_cases j <;> tauto
    · intro hσ
      rw [hσ]
      simp
   rw [this]
   simp
  simp_rw [this] at h
  simp only [Nat.cast_one, mul_one, Fin.isValue] at h
  have h : (∑ i, x i ^ 2) * ((m:ℝ) - 1)
      - (∑ x_1 : Fin 2 → Fin m with ¬x_1 0 = x_1 1, x (x_1 0) * x (x_1 1)) = 0 := by
    rw [← h]
    linarith
  rw [mul_comm] at h
  suffices ∑ σ : Fin 2 → Fin m with σ 0 ≠ σ 1, (x (σ 0) - x (σ 1))^2 = 0 by
    have := @sum_of_constant' m x
    tauto
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  simp only [Fin.isValue, ne_eq]
  rw [← offDiagonalSq] at h
  rw [sub_eq_zero] at h
  have : ∑ x_1 : Fin 2 → Fin m with ¬x_1 0 = x_1 1, x (x_1 0) ^ 2
       = ∑ x_1 : Fin 2 → Fin m with ¬x_1 0 = x_1 1, x (x_1 1) ^ 2 := by
    have := @Finset.sum_bijective (Fin 2 → Fin m) (Fin 2 → Fin m)
        ℝ _ (Finset.filter (fun σ => σ 0 ≠ σ 1) Finset.univ)
        (Finset.filter (fun σ => σ 0 ≠ σ 1) Finset.univ)
        (fun σ => x (σ 0)^2)
        (fun σ => x (σ 1)^2)
        (fun σ => ![σ 1, σ 0])
        (by
            constructor
            · intro x y h
              simp at h
              ext i
              fin_cases i <;> tauto
            · intro x
              use ![x 1, x 0]
              simp only [
                Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
              ext i
              fin_cases i <;> tauto) (by
                intro σ
                simp
                tauto) (by
                intro σ
                simp)
    convert this
  rw [this]
  ring_nf
  conv =>
    left
    left
    rw [mul_comm]
  have (x_1 : Fin 2 → Fin m) : x (x_1 0) * x (x_1 1) * 2
    = 2 * (x (x_1 0) * x (x_1 1)) := by ring_nf
  simp_rw [this]
  have := @Finset.mul_sum (Fin 2 → Fin m) ℝ _ (Finset.filter (fun σ => σ 0 ≠ σ 1) Finset.univ)
    (fun σ => x (σ 0) * x (σ 1)) 2
  rw [← this]
  suffices ∑ x_1 : Fin 2 → Fin m with ¬x_1 0 = x_1 1, x (x_1 1) ^ 2
         - ∑ i : Fin 2 → Fin m with i 0 ≠ i 1, x (i 0) * x (i 1) = 0
   by linarith
  rw [h]
  ring_nf



/-- The explicit `3 × 2` design matrix `[x | 1]` for three data points. -/
def A₃ (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![
  x 0, 1;
  x 1, 1;
  x 2, 1
]

/-- The least-squares coefficients for three data points using `A₃`. -/
noncomputable def getCoeffs₃ (x y : Fin 3 → ℝ) :=
  Matrix.mulᵣ (Matrix.mulᵣ (Matrix.mulᵣ ((A₃ x)ᵀ) (A₃ x))⁻¹ ((A₃ x)ᵀ))
  !![y 0; y 1; y 2]

lemma getx₃ (x : Fin 3 → ℝ) (c : ℝ) (e : Matrix (Fin 2) (Fin 1) ℝ) :
    ((c • e) 0 0 • x + (c • e) 1 0 • fun (_ : Fin 3) ↦ (1:ℝ)) =
    fun i ↦ (c • (!![x 0, 1; x 1, 1; x 2, 1] * e)) i 0 := by
  have ho (o : ℝ) :  c * e 0 0 * o + c * e 1 0
    =  c * (e 0 0 * o + e 1 0) := by rw [mul_assoc,left_distrib]
  by_cases H : c = 0
  · rw [H]
    simp only [
      Fin.isValue, Matrix.smul_apply, smul_eq_mul, zero_mul, zero_smul, add_zero, Matrix.cons_mul,
      Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.empty_mul, Equiv.symm_apply_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one]
    ext i
    simp
  · ext i
    fin_cases i <;> (
        simp only [
          Fin.isValue, Matrix.smul_apply, smul_eq_mul, Fin.zero_eta, Pi.add_apply, Pi.smul_apply,
          mul_one, Matrix.cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.empty_mul,
          Equiv.symm_apply_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
          Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
        rw [ho]
        apply (IsUnit.mul_right_inj (Ne.isUnit H)).mpr
        simp only [
          Fin.isValue, Matrix.vecMul, Matrix.cons_dotProduct, Matrix.head_val', Matrix.tail_val',
          one_mul, Matrix.dotProduct_of_isEmpty, add_zero]
        rw [mul_comm]
        congr
    )

lemma getDet₃ (x₀ x₁ x₂ : ℝ) :
  !![x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2, x₀ + x₁ + x₂; x₀ + x₁ + x₂, 3]⁻¹ =
    (2 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 - x₀ * x₁ - x₀ * x₂ - x₁ * x₂))⁻¹ •
      !![3, -(x₀ + x₁ + x₂); -(x₀ + x₁ + x₂), x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2] := by
    rw [Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two]
    simp only [
      Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, Ring.inverse_eq_inv', neg_add_rev, Matrix.smul_of, Matrix.smul_cons,
      smul_eq_mul, Matrix.smul_empty, mul_inv_rev, EmbeddingLike.apply_eq_iff_eq,
      Matrix.vecCons_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false, and_true]
    repeat rw [← mul_inv]
    constructor
    · constructor
      · ring_nf
      · left
        congr
        ring_nf
    · constructor <;>
      · left
        congr
        ring_nf

example : getCoeffs₃ ![0,1,2] ![0,1,1] = !![1/2;1/6] := by
  unfold getCoeffs₃ A₃
  have (a : ℝ) : ![(0:ℝ),1,a] 2 = a := rfl
  repeat rw [this]
  have (a : ℝ) : ![(0:ℝ),1,a] 1 = 1 := rfl
  repeat rw [this]
  have (a : ℝ) : ![(0:ℝ),1,a] 0 = 0 := rfl
  repeat rw [this]
  have : !![(0:ℝ), 1; 1, 1; 2, 1]ᵀ
       = !![0, 1, 2; 1, 1, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this]
  rw [Matrix.inv_def]
  simp
  grind
example (a b c : ℝ) : getCoeffs₃ ![a,b,c] ![0,0,0] = ![![0],![0]] := by
  unfold getCoeffs₃
  generalize ((A₃ ![a, b, c]ᵀ.mulᵣ (A₃ ![a, b, c]))⁻¹.mulᵣ (A₃ ![a, b, c]ᵀ)) = x
  have : x = !![x 0 0, x 0 1, x 0 2;
                x 1 0, x 1 1, x 1 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this]
  ext i j; fin_cases i <;> fin_cases j <;> simp


/-

#Specific material
-/

/-- Multivariate regression. -/
noncomputable def K₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) :=
    @Submodule.span ℝ (EuclideanSpace ℝ (Fin n)) _ _ _
    {WithLp.toLp 2 x₀, WithLp.toLp 2 x₁, WithLp.toLp 2 fun _ => 1}
theorem hxK₂₀ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : WithLp.toLp 2 x₀ ∈ K₂ x₀ x₁ :=
    Submodule.mem_span_of_mem (Set.mem_insert (WithLp.toLp 2 x₀) _)
theorem hxK₂₁ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : WithLp.toLp 2 x₁ ∈ K₂ x₀ x₁ :=
    Submodule.mem_span_of_mem (by simp)
theorem h1K₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) : WithLp.toLp 2 (fun _ ↦ 1) ∈ K₂ x₀ x₁ :=
    Submodule.mem_span_of_mem (by simp)
theorem topsub₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) :
    ⊤ ≤ Submodule.span ℝ (Set.range ![
      (⟨WithLp.toLp 2 x₀, hxK₂₀ x₀ x₁⟩ : K₂ x₀ x₁),
      (⟨WithLp.toLp 2 x₁, hxK₂₁ x₀ x₁⟩ : K₂ x₀ x₁),
      (⟨WithLp.toLp 2 fun _ => 1, h1K₂ x₀ x₁⟩ : K₂ x₀ x₁)]) := by
  refine top_le_iff.mpr (Submodule.eq_top_iff'.mpr ?_)
  intro a
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton]
  apply Submodule.mem_span_triple.mpr
  obtain ⟨c,d,e,h⟩ := Submodule.mem_span_triple.mp a.2
  use c, e, d
  rw [Subtype.ext_iff]
  push_cast
  rw [← h]
  abel
/-- The three spanning vectors of `K₂ x₀ x₁` as elements of the subspace. -/
def Kvec₂ {n : ℕ} (x₀ x₁ : Fin n → ℝ) := ![
  (⟨WithLp.toLp 2 x₀, hxK₂₀ x₀ x₁⟩ : K₂ x₀ x₁),
  (⟨WithLp.toLp 2 x₁, hxK₂₁ x₀ x₁⟩ : K₂ x₀ x₁),
  (⟨WithLp.toLp 2 fun _ => 1, h1K₂ x₀ x₁⟩ : K₂ x₀ x₁)]

/-- The multivariate (two-predictor) least-squares regression coordinates. -/
noncomputable def regression_coordinates₂ {n : ℕ} (x₀ x₁ y : Fin n → ℝ)
    (lin_indep : LinearIndependent ℝ (Kvec₂ x₀ x₁)) :
    Fin 3 → ℝ := fun i => ((Module.Basis.mk lin_indep (topsub₂ _ _)).repr
      ⟨Submodule.starProjection (K₂ x₀ x₁) (WithLp.toLp 2 y),
       Submodule.starProjection_apply_mem (K₂ x₀ x₁) (WithLp.toLp 2 y)⟩) i


lemma hvo₀₁₁ (w : EuclideanSpace ℝ (Fin 3))
    (hw : w ∈ K₁ ![0, 1, 2]) :
    inner ℝ (WithLp.toLp 2 ![0, 1, 1] - WithLp.toLp 2 ![1 / 6, 4 / 6, 7 / 6]) w = 0 := by
  obtain ⟨a,b,h⟩ := Submodule.mem_span_pair.mp hw
  rw [← h]
  simp only [
    inner, Nat.succ_eq_add_one, Nat.reduceAdd, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    mul_one, one_div, PiLp.sub_apply, star_trivial, RCLike.mul_re, RCLike.re_to_real,
    RCLike.im_to_real, mul_zero, sub_zero]
  rw [Fin.sum_univ_three]
  -- repeat rw [Pi.sub_apply]
  simp
  grind
