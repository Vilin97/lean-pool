/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import LeanPool.BruhatTits.Utils.RingHom
import LeanPool.BruhatTits.Utils.Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# LeanPool.BruhatTits.Utils.Matrix
-/

open Module

open BigOperators
namespace Matrix

variable {R : Type*}
variable {n m n' m' : Type*}

section «Coeffs»

/-- The set of coefficients appearing in a matrix. -/
noncomputable def coeffs (g : Matrix n m R) : Set R :=
  Set.image2 g Set.univ Set.univ

lemma mem_coeffs (g : Matrix n m R) (i : n) (j : m) : g i j ∈ g.coeffs := by
  simp [coeffs]

lemma coeffs_nonempty [Nonempty n] [Nonempty m] (g : Matrix n m R) : g.coeffs.Nonempty :=
  have ⟨i⟩ := (inferInstance : Nonempty n)
  have ⟨j⟩ := (inferInstance : Nonempty m)
  ⟨g i j, g.mem_coeffs i j⟩

lemma finite_coeffs [Finite n] [Finite m] (g : Matrix n m R) :
    (coeffs g).Finite := by
  simp only [coeffs]
  exact Set.toFinite (Set.image2 g Set.univ Set.univ)

@[simp]
lemma transpose_coeffs (g : Matrix n m R) : g.transpose.coeffs = g.coeffs := by
  ext a
  simp only [coeffs, transpose_apply]
  constructor
  · rintro ⟨i, -, j, -, hij⟩
    simp only [Set.mem_image2, Set.mem_univ, true_and]
    use j, i
  · rintro ⟨i, -, j, -, hij⟩
    simp only [Set.mem_image2, Set.mem_univ, true_and]
    use j, i

lemma coeffs_reindex (g : Matrix n m R) (e : n ≃ n') (f : m ≃ m') :
    (reindex e f g).coeffs = g.coeffs := by
  ext a
  simp only [coeffs, reindex_apply, submatrix_apply, Set.mem_image2, Set.mem_univ, true_and]
  constructor
  · rintro ⟨i, j, hij⟩
    use e.symm i, f.symm j
  · intro ⟨i, j, hij⟩
    use e i, f j
    simpa

lemma coeffs_fromBlocks (A : Matrix n n' R) (B : Matrix n m R) (C : Matrix m' n' R)
    (D : Matrix m' m R) :
    (A.fromBlocks B C D).coeffs =
        A.coeffs ∪ B.coeffs ∪ C.coeffs ∪ D.coeffs := by
  ext a
  simp only [coeffs]
  aesop

lemma coeffs_zero [Zero R] [Nonempty n] [Nonempty m] : (0 : Matrix n m R).coeffs = {0} := by
  classical
  ext a
  simp only [coeffs, zero_apply, Set.mem_image2, Set.mem_univ, true_and, exists_const,
    Set.mem_singleton_iff]
  tauto

@[simp]
lemma coeffs_one [One R] [Zero R] [DecidableEq n] : (1 : Matrix n n R).coeffs ⊆ {0, 1} := by
  intro a
  simp only [coeffs, Set.mem_image2, Set.mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_exists_index]
  intro i j hij
  by_cases h : i = j
  · subst h
    simpa [one_apply_eq] using Or.inr hij.symm
  · simpa [one_apply_ne h] using Or.inl hij.symm

lemma one_mem_coeffs_one [One R] [Zero R] [Nonempty n] [DecidableEq n] :
    1 ∈ (1 : Matrix n n R).coeffs := by
  obtain ⟨i⟩ := ‹Nonempty n›
  simp only [coeffs, Set.mem_image2, Set.mem_univ, true_and]
  use i, i
  simp

lemma coeffs_unique [Unique n] [Unique m] (g : Matrix n m R) :
    g.coeffs = {g default default} := by
  ext
  simp [coeffs, Unique.eq_default, eq_comm]

end «Coeffs»

section «Map»

variable [CommRing R] [DecidableEq m] [DecidableEq n] [Fintype n] [Fintype m]

variable {S : Type*} [CommRing S] {F : Type*} (f : R →+* S)

@[simp]
lemma map_ite (p : Prop) (a b : R) [Decidable p] :
    f (if p then a else b) = if p then f a else f b := by
  split_ifs <;> rfl

omit [Fintype n] in
@[simp]
lemma map_transvection (i j : n) (c : R) : (transvection i j c).map f = transvection i j (f c) := by
  ext a b
  simp only [map_apply, transvection, add_apply, map_add, Matrix.single_apply]
  split_ifs <;> (by_cases hab : a = b <;> simp [Matrix.one_apply, hab])

lemma map_listProd : (L : List (Matrix n n R)) →
    List.prod (List.map (fun g ↦ g.map f) L) = (List.prod L).map f
  | [] => by simp [List.map_nil, List.prod_nil, map_zero, _root_.map_one, map_one]
  | g :: gs => by simp [List.map_cons, List.prod_cons, map_listProd]

lemma map_listProd_toGL : (L : List (GL n R)) →
    (List.prod (List.map (fun g ↦ g.val.map f) L)) = (List.prod L).val.map f
  | [] => by simp [List.map_nil, List.prod_nil, Units.val_one, map_zero, _root_.map_one,
    map_one]
  | g :: gs => by simp [List.map_cons, List.prod_cons, map_listProd_toGL, Units.val_mul]

end «Map»

variable [CommRing R]

section «CoeffsSup»

variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

section «Finite»

variable [Finite n] [Finite m] [Finite n'] [Finite m'] [Nonempty n] [Nonempty m]
  [Nonempty n'] [Nonempty m']

/-- The supremum of the coefficients. -/
noncomputable def coeffsSup (g : Matrix n m R) : Γ₀ :=
  Finset.sup' (finite_coeffs g).toFinset (by simpa using coeffs_nonempty g) v

lemma coeff_le_coeffs_sup (g : Matrix n m R)
    (i : n) (j : m) : v (g i j) ≤ g.coeffsSup v :=
  Finset.le_sup' _ (by simpa using mem_coeffs g i j)

lemma coeffs_sup_le {g : Matrix n m R} {a : Γ₀}
    (h : ∀ (i : n) (j : m), v (g i j) ≤ a) :
    g.coeffsSup v ≤ a := by
  apply Finset.sup'_le
  intro b hb
  simp only [coeffs, Set.Finite.mem_toFinset, Set.mem_image2, Set.mem_univ, true_and] at hb
  obtain ⟨i, j, rfl⟩ := hb
  exact h i j

lemma coeffs_sup_exists_repr (g : Matrix n m R) :
    ∃ p : n × m, v (g p.1 p.2) = g.coeffsSup v := by
  simp only [coeffsSup]
  by_contra h
  simp only [Prod.exists, not_exists] at h
  have : g.coeffsSup v < g.coeffsSup v := by
    simp only [coeffsSup, Finset.sup'_lt_iff]
    intro a ha
    simp only [coeffs, Set.Finite.mem_toFinset, Set.mem_image2, Set.mem_univ, true_and] at ha
    obtain ⟨i, j, rfl⟩ := ha
    exact lt_of_le_of_ne (coeff_le_coeffs_sup v g i j) (h i j)
  simp_all

/-- A matrix position where the coefficient supremum is attained. -/
noncomputable def coeffsSupAt (g : Matrix n m R) : n × m :=
  (g.coeffs_sup_exists_repr v).choose

lemma coeffs_sup_at_sup (g : Matrix n m R) :
    v (g (g.coeffsSupAt v).1 (g.coeffsSupAt v).2) = g.coeffsSup v :=
  (g.coeffs_sup_exists_repr v).choose_spec

/-- The supremum of the coefficients is invariant under transposition. -/
lemma coeffs_sup_transpose (g : Matrix n m R) :
    g.transpose.coeffsSup v = g.coeffsSup v := by
  simp only [coeffsSup, transpose_coeffs]

lemma coeffs_sup_fromBlocks (A : Matrix n n' R) (B : Matrix n m R)
    (C : Matrix m' n' R) (D : Matrix m' m R) :
    (A.fromBlocks B C D).coeffsSup v =
      A.coeffsSup v ⊔ B.coeffsSup v ⊔ C.coeffsSup v ⊔ D.coeffsSup v := by
  classical
  simp only [coeffsSup, ← Finset.sup'_union, coeffs_fromBlocks]
  congr
  ext
  simp
  tauto

end «Finite»

section «Fintype»

variable [DecidableEq m] [Fintype n] [Fintype m]

@[simp]
lemma mul_swap_coeffs (g : Matrix m m R) (i j : m) :
    (g * swap R i j).coeffs = g.coeffs := by
  ext a
  simp only [coeffs]
  constructor
  · rintro ⟨l, -, k, -, hlk⟩
    by_cases hjl : k = j
    · subst hjl
      simp only [mul_swap_apply_right] at hlk
      simp only [Set.mem_image2, Set.mem_univ, true_and]
      use l, i
    · by_cases hik : k = i
      · subst hik
        simp only [mul_swap_apply_left] at hlk
        simp only [Set.mem_image2, Set.mem_univ, true_and]
        use l, j
      · rw [mul_swap_of_ne hik hjl] at hlk
        simp only [Set.mem_image2, Set.mem_univ, true_and]
        use l, k
  · rintro ⟨l, -, k, -, hlk⟩
    by_cases hjl : k = j
    · subst hjl
      simp only [Set.mem_image2, Set.mem_univ, true_and]
      use l, i
      simpa
    · simp only [Set.mem_image2, Set.mem_univ, true_and]
      by_cases hik : k = i
      · subst hik
        use l, j
        simpa
      · use l, k
        simpa only [mul_swap_of_ne hik hjl]

@[simp]
lemma swap_mul_coeffs (g : Matrix m m R) (i j : m) :
    (swap R i j * g).coeffs = g.coeffs := by
  classical
  rw [← transpose_coeffs]
  simp only [transpose_mul, transpose_swap, mul_swap_coeffs, transpose_coeffs]

omit [Fintype n] in
@[simp]
lemma coeffs_sup_mul_swap [Nonempty m] (g : Matrix m m R) (i j : m) :
    (g * swap R i j).coeffsSup v = g.coeffsSup v := by
  simp only [coeffsSup, mul_swap_coeffs]

@[simp]
lemma coeffs_sup_swap_mul [Nonempty m] (g : Matrix m m R) (i j : m) :
    (swap R i j * g).coeffsSup v = g.coeffsSup v := by
  simp only [coeffsSup, swap_mul_coeffs]

end «Fintype»

section «FiniteLemmas»

variable [Finite n] [Finite m] [Finite n'] [Finite m']
variable [DecidableEq n'] [DecidableEq m']

omit [DecidableEq n'] [DecidableEq m'] in
lemma coeffs_sup_reindex [Nonempty n] [Nonempty m] [Nonempty n'] [Nonempty m']
    (g : Matrix n m R) (e : n ≃ n') (f : m ≃ m') :
    (reindex e f g).coeffsSup v = g.coeffsSup v := by
  letI : Fintype n := Fintype.ofFinite n
  letI : Fintype m := Fintype.ofFinite m
  letI : Fintype n' := Fintype.ofFinite n'
  letI : Fintype m' := Fintype.ofFinite m'
  simp only [coeffsSup, coeffs_reindex]

omit [DecidableEq n'] [DecidableEq m'] in
lemma coeffs_sup_toBlock₁₁_le_coeffs_sup [Nonempty n] [Nonempty m']
    (g : Matrix (n ⊕ n') (m' ⊕ m) R) :
    g.toBlocks₁₁.coeffsSup v ≤ g.coeffsSup v := by
  letI : Fintype n := Fintype.ofFinite n
  letI : Fintype m := Fintype.ofFinite m
  letI : Fintype n' := Fintype.ofFinite n'
  letI : Fintype m' := Fintype.ofFinite m'
  rw [← coeffs_sup_at_sup]
  simp only [toBlocks₁₁, of_apply]
  apply coeff_le_coeffs_sup

lemma coeffs_sup_zero [Nonempty n] [Nonempty m] :
    (0 : Matrix n m R).coeffsSup v = 0 := by
  letI : Fintype n := Fintype.ofFinite n
  letI : Fintype m := Fintype.ofFinite m
  simp [coeffsSup, coeffs_zero, map_zero]

lemma coeffs_sup_one [Nonempty n] [DecidableEq n] : (1 : Matrix n n R).coeffsSup v = 1 := by
  letI : Fintype n := Fintype.ofFinite n
  simp only [coeffsSup]
  apply le_antisymm
  · simp only [Finset.sup'_le_iff]
    intro b hb
    simp only [Set.Finite.mem_toFinset] at hb
    apply coeffs_one at hb
    aesop
  · simp only [Finset.le_sup'_iff]
    use 1
    simpa using one_mem_coeffs_one

lemma coeffs_sup_unique [Unique n] (g : Matrix n n R) :
    g.coeffsSup v = v (g default default) := by
  letI : Fintype n := Fintype.ofFinite n
  simp [coeffsSup, coeffs_unique]

end «FiniteLemmas»

end «CoeffsSup»

section «GeneralLinearGroup»

variable [DecidableEq n] [Fintype n]

/-- `GL` version of `toMatrix`. -/
def _root_.Matrix.TransvectionStruct.toGL (t : TransvectionStruct n R) : GL n R where
  val := t.toMatrix
  inv := t.inv.toMatrix
  val_inv := t.mul_inv
  inv_val := t.inv_mul

/-- The transpose of an invertible matrix as an element of `GL`. -/
@[simps val]
def _root_.Matrix.GL.transpose (g : GL n R) : GL n R where
  val := g.val.transpose
  inv := g.inv.transpose
  val_inv := by
    rw [← Matrix.transpose_mul]
    simp
  inv_val := by
    rw [← Matrix.transpose_mul]
    simp

lemma _root_.Matrix.GL.val_inv_transpose (g : GL n R) :
    ↑(Matrix.GL.transpose g)⁻¹ = g.inv.transpose :=
  rfl

/-- A diagonal matrix with unit diagonal entries as an element of `GL`. -/
@[simps val]
def _root_.Matrix.GL.diagonal (g : n → Rˣ) : GL n R where
  val := Matrix.diagonal (fun j ↦ g j)
  inv := Matrix.diagonal (fun j ↦ (g j).inv)
  val_inv := by simp
  inv_val := by simp

lemma _root_.Matrix.GL.val_inv_diagonal (g : n → Rˣ) :
    ↑(Matrix.GL.diagonal g)⁻¹ = Matrix.diagonal (fun j ↦ (g j).inv) :=
  rfl

lemma _root_.Matrix.GL.diagonal_det (g : n → Rˣ) :
    GeneralLinearGroup.det (GL.diagonal g) = ∏ i : n, g i := by
  ext
  simp

variable [DecidableEq m] [Fintype m]

/-- The block diagonal sum of two general linear matrices. -/
@[simps val]
def _root_.Matrix.GL.diagonalBlocks (g : GL n R) (h : GL m R) : GL (n ⊕ m) R where
  val := Matrix.fromBlocks g 0 0 h
  inv := Matrix.fromBlocks g.inv 0 0 h.inv
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp

lemma _root_.Matrix.GL.val_inv_diagonalBlocks (g : GL n R) (h : GL m R) :
    ↑(Matrix.GL.diagonalBlocks g h)⁻¹ = Matrix.fromBlocks g.inv 0 0 h.inv :=
  rfl

/-- Reindex the rows and columns of an element of `GL` along an equivalence. -/
@[simps val]
def _root_.Matrix.GL.reindex (e : n ≃ m) (g : GL n R) : GL m R where
  val := Matrix.reindex e e g
  inv := Matrix.reindex e e g.inv
  val_inv := by simp
  inv_val := by simp

lemma _root_.Matrix.GL.val_inv_reindex (e : n ≃ m) (g : GL n R) :
    ↑(Matrix.GL.reindex e g)⁻¹ = Matrix.reindex e e g.inv :=
  rfl

lemma _root_.Matrix.GL.conj_diagonal_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d : ι → Rˣ) (g : GL ι R) (i j : ι) :
    MulAut.conj (Matrix.GL.diagonal d) g i j = (d i) * (d j)⁻¹ * g i j := by
  have heq : Ring.inverse (fun j ↦ (d j).val) = fun j ↦ (d j).inv := by
    let u : (ι → R)ˣ := .mkOfMulEqOne (fun j ↦ d j) (fun j ↦ (d j).inv) ?_
    · exact Ring.inverse_unit u
    · ext; simp
  simp only [MulAut.conj_apply, Units.val_mul, Matrix.GL.val_diagonal, Matrix.coe_units_inv]
  rw [Matrix.inv_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, heq]
  have hdj : (fun j ↦ (d j).inv) j = (((d j)⁻¹ : Rˣ) : R) := by
    exact Units.inv_eq_val_inv (d j)
  rw [hdj]
  ring

lemma _root_.Matrix.GL.isMulCentral_diagonal {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : Rˣ) :
    IsMulCentral (Matrix.GL.diagonal fun _ : ι ↦ a) := by
  rw [isMulCentral_iff]
  refine ⟨fun g ↦ ?_, fun g h ↦ ?_, fun g h ↦ ?_⟩
  · ext i j
    simp [mul_comm]
  · rw [mul_assoc]
  · rw [mul_assoc]

namespace GeneralLinearGroup

lemma apply_ne_zero_of_isDiag [Nontrivial R] (g : GL n R) (h : g.val.IsDiag)
    (j : n) : g j j ≠ 0 := by
  intro hzero
  apply g.det_ne_zero
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  by_cases hij : i = j
  · subst hij
    exact hzero
  · exact h hij

lemma coe_mul_inv (g : GL n R) : g.val * g.val⁻¹ = 1 := by
  simp

lemma coe_inv_mul (g : GL n R) : g.val⁻¹ * g.val = 1 := by
  simp

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {K : Type*} [CommRing K]
variable {R : Subring K}

section «Basis»

/-- The columns of an invertible matrix over `K` yields a basis of `ι → K`. -/
noncomputable def toBasis (g : GL ι K) : Basis ι K (ι → K) :=
  Basis.ofEquivFun (toLin g⁻¹).toLinearEquiv

@[simp]
lemma toBasis_coe_apply (g : GL ι K) (i : ι) : g.toBasis i = (fun j ↦ g j i) := by
  simp only [toBasis, map_inv, Basis.coe_ofEquivFun]
  change (toLin g⁻¹).toLinearEquiv.symm (Pi.single i 1) = fun j ↦ g j i
  have h : Pi.single i 1 = g.inv *ᵥ (fun j ↦ g j i) := by
    simp only [Units.inv_eq_val_inv, coe_units_inv]
    rw [show (fun j ↦ g j i) = g.val *ᵥ Pi.single i 1 from by ext; simp]
    have : Nonempty ι := ⟨ i ⟩
    rw [mulVec_mulVec, coe_inv_mul]
    rw [one_mulVec]
  rw [h]
  erw [← toLin_apply g]
  rw [toLin_apply g, ← h]
  ext
  simp

/-- From an invertible matrix over `K`, we obtain an `R` submodule by taking
the span of the columns. -/
def toSubmodule (g : GL ι K) : Submodule R (ι → K) :=
  Submodule.span R (Set.range (fun col row ↦ g.val row col))

lemma mem_toSubmodule (g : GL ι K) (x : ι → K) :
    x ∈ g.toSubmodule (R := R) ↔ ∃ (y : ι → R), g *ᵥ (Subtype.val ∘ y) = x := by
  simp only [toSubmodule]
  constructor
  · intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      use Pi.single i 1
      ext
      simp
    · use 0
      simp only [Pi.comp_zero, ZeroMemClass.coe_zero, Function.const_zero, mulVec_zero]
    · intro v w _ _ hv hw
      obtain ⟨v, hv⟩ := hv
      obtain ⟨w, hw⟩ := hw
      use v + w
      simp only [Subtype.val_comp_add]
      rw [mulVec_add, hw, hv]
    · intro a x _ hv
      obtain ⟨v, hv⟩ := hv
      use a • v
      simp only [Subtype.val_comp_smul]
      rw [mulVec_smul, hv]
  · rintro ⟨v, rfl⟩
    let b := Pi.basisFun R ι
    have hv : v ∈ Submodule.span R (Set.range b) := Basis.mem_span b v
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · intro v hv
      obtain ⟨i, rfl⟩ := hv
      apply Submodule.subset_span
      use i
      simp only [b]
      simp only [Pi.basisFun_apply, Pi.single]
      change _ = g.val *ᵥ (Subtype.val ∘ Pi.single i 1)
      ext
      simp
    · simp only [Pi.comp_zero, ZeroMemClass.coe_zero, Function.const_zero, mulVec_zero,
        Submodule.zero_mem]
    · intro v w _ _ hv hw
      rw [Subtype.val_comp_add, mulVec_add]
      exact Submodule.add_mem _ hv hw
    · intro a v _ hv
      rw [Subtype.val_comp_smul, mulVec_smul]
      exact Submodule.smul_mem _ _ hv

end «Basis»

/-- Invertible matrices over `K` act on `R`-submodules of `ι → K`. -/
instance instSMulSubmoduleSubtypeMemSubringForallLeanPool :
    SMul (GL ι K) (Submodule R (ι → K)) where
  smul g M := Submodule.map ((toLin g).val : (ι → K) →ₗ[R] ι → K) M

lemma smul_def (g : GL ι K) (M : Submodule R (ι → K)) :
    g • M = Submodule.map (g.val.mulVecLin : (ι → K) →ₗ[R] ι → K) M :=
  rfl

lemma mem_smul (g : GL ι K) (M : Submodule R (ι → K)) (x : ι → K) :
    x ∈ g • M ↔ ∃ y ∈ M, g.val *ᵥ y = x := by
  rw [smul_def]
  simp

open Pointwise in
lemma diagonal_smul (f : ι → Kˣ) (M : Submodule R (ι → K)) (hf : ∀ i j, f i = f j) (i : ι) :
    GL.diagonal f • M = f i • M := by
  have : f = fun _ ↦ f i := by
    ext : 1
    apply hf
  rw [this, SetLike.ext'_iff]
  ext x
  simp [mem_smul, Set.mem_smul_set, Units.smul_def]

/-- Invertible matrices over `K` act on `R`-submodules of `ι → K`. -/
instance instMulActionSubmoduleSubtypeMemSubringForallLeanPool :
    MulAction (GL ι K) (Submodule R (ι → K)) where
  one_smul M := by
    rw [smul_def]
    ext
    simp
  mul_smul g h M := by
    simp_rw [smul_def]
    ext
    simp

/-- The canonical `R`-linear isomorphism from `M` to `g • M` induced by `g`. -/
def equivSMulGL (g : GL ι K) (M : Submodule R (ι → K)) :
    M ≃ₗ[R] (g • M : Submodule R (ι → K)) :=
  ((toLin g).toLinearEquiv.restrictScalars R).submoduleMap M

lemma smul_toSubmodule (g h : GL ι K) :
    g • (h.toSubmodule (R := R)) = (g * h).toSubmodule (R := R) := by
  ext x
  simp [mem_smul, mem_toSubmodule]

/-- The linear equivalence induced by a matrix in the coordinates of a basis. -/
noncomputable def toLinearEquivOfBasis {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (b : Basis ι R M) (g : GL ι R) : M ≃ₗ[R] M :=
  let f : (ι → R) ≃ₗ[R] ι → R := (toLin g).toLinearEquiv
  b.equivFun ≪≫ₗ f ≪≫ₗ b.equivFun.symm

/-- The basis obtained by acting on coordinates by a matrix in `GL`. -/
noncomputable def smulBasis {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M] (g : GL ι R)
    (b : Basis ι R M) : Basis ι R M :=
  b.map (toLinearEquivOfBasis b g)

noncomputable instance instSMulMulOppositeSubtypeMemSubringBasisForallSubmoduleLeanPool
    (M : Submodule R (ι → K)) : SMul (GL ι R)ᵐᵒᵖ (Basis ι R M) where
  smul := fun ⟨g⟩ b ↦ smulBasis g b

lemma basis_smul_def {M : Submodule R (ι → K)} (g : GL ι R) (b : Basis ι R M) :
    (MulOpposite.op g) • b = smulBasis g b :=
  rfl

@[simp]
lemma ofLinearEquiv_toLinearEquiv {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    (f : M ≃ₗ[R] M) : (LinearMap.GeneralLinearGroup.ofLinearEquiv f).toLinearEquiv = f :=
  rfl

/-- For fixed `R`-submodule `M` of `ι → K`, `GL ι R` acts transitively on `ι`-indexed
`R` basis of `M`. -/
instance (M : Submodule R (ι → K)) :
    MulAction.IsPretransitive (GL ι R)ᵐᵒᵖ (Basis ι R M) where
  exists_smul_eq b b' := by
    let e : M ≃ₗ[R] M := b.equiv b' (Equiv.refl ι)
    let e' : (ι → R) ≃ₗ[R] ι → R :=
      b.equivFun.symm ≪≫ₗ e ≪≫ₗ b.equivFun
    let g : GL ι R := toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e')
    use ⟨g⟩
    erw [basis_smul_def]
    simp only [smulBasis, g, e', e,
      toLinearEquivOfBasis, MulEquiv.apply_symm_apply, ofLinearEquiv_toLinearEquiv]
    change b.map (b.equivFun ≪≫ₗ b.equivFun.symm ≪≫ₗ b.equiv b' (Equiv.refl ι) ≪≫ₗ (b.equivFun ≪≫ₗ
      b.equivFun.symm)) = b'
    simp

/-- The diagonal embedding from the units of `R` to the general linear group. -/
@[simps]
def embDiagonal (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    Rˣ →* GL ι R where
  toFun x := Matrix.GL.diagonal (fun _ ↦ x)
  map_one' := by ext; simp
  map_mul' x y := by
    ext i j
    by_cases h : i = j <;> simp [h]

lemma isMulCentral_embDiagonal {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Rˣ) :
    IsMulCentral (Matrix.GeneralLinearGroup.embDiagonal R ι u) :=
  Matrix.GL.isMulCentral_diagonal u

end «GeneralLinearGroup»

end GeneralLinearGroup

section «UpperTriangular»

/-- The subgroup of `GL(ι, R)` consisting of upper triangular matrices
  (wrt. to the ordering on ι). -/
def _root_.Matrix.GeneralLinearGroup.upperTriangularSubgroup (R : Type*) [CommRing R]
    (ι : Type*) [Fintype ι] [DecidableEq ι] [LinearOrder ι] :
    Subgroup (GL ι R) where
  carrier := { g | g.val.BlockTriangular id }
  mul_mem' {x y} hx hy := hx.mul hy
  one_mem' := Matrix.blockTriangular_one
  inv_mem' {x} hx := by
    letI : Invertible x.val := ⟨x.inv, x.4, x.3⟩
    convert Matrix.blockTriangular_inv_of_blockTriangular hx
    simp

@[simp]
lemma _root_.Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
    (R : Type*) [CommRing R] (ι : Type*)
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] (g : GL ι R) :
    g ∈ GeneralLinearGroup.upperTriangularSubgroup R ι ↔
      g.val.BlockTriangular id :=
  .rfl

@[simp]
lemma _root_.Matrix.BlockTriangular.fin_two_iff {R : Type*} [Zero R]
    (M : Matrix (Fin 2) (Fin 2) R) :
    M.BlockTriangular id ↔ M 1 0 = 0 := by
  simp [Matrix.BlockTriangular]

end «UpperTriangular»

end Matrix
