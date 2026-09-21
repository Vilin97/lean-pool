/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.ConcreteInducedZAction

/-!
# Commutator expansion for source-row action equations

This file proves the algebraic calculation between two common-basis first-order
source equations and the induced commutator action on the special fibre.  It is
independent of the Weyl presentation, localization, Artinianity, and trace
arguments.

The deformation module remains only a left module over the noncommutative ring.
The parameter is central and square-zero.  Exactness of its action is used only
after the commutator has been expanded.  The commutators with the first-order
matrices disappear only after applying the commutative specialization.

The result records the actual specialized action of the source expansion and
isolates the remaining trace-comparison obligation.  It does not assert an
equality with a residue-mapped coefficient matrix.
-/

namespace Stafford38.Characteristic.SourceActionCommutatorExpansion

open Matrix
open Stafford38.Characteristic
open Stafford38.Characteristic.ConcreteEquation33SourceMatrices
open Stafford38.Characteristic.ConcreteInducedZAction
open Stafford38.Characteristic.ArtinianEquation33TraceProducer

noncomputable section

universe u

variable {B Abar W V : Type u}
variable [Ring B] [CommRing Abar]
variable [AddCommGroup W] [Module B W]
variable [AddCommGroup V] [Module Abar V]
variable {r : ℕ}

local notation "ι" => Fin (r + 1)

/-- Apply a source-row matrix to a list of lifted basis vectors.  The first
index is the input vector and the second index is its output coefficient. -/
def sourceRowAction (M : Matrix ι ι B) (e : ι → W) (i : ι) : W :=
  ∑ j, M i j • e j

theorem smul_sourceRowAction (a : B) (M : Matrix ι ι B) (e : ι → W) (i : ι) :
    a • sourceRowAction M e i = ∑ j, (a * M i j) • e j := by
  simp only [sourceRowAction]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (mul_smul a (M i j) (e j)).symm

theorem sourceRowAction_mul (M N : Matrix ι ι B) (e : ι → W) (i : ι) :
    sourceRowAction M (fun j => sourceRowAction N e j) i =
      sourceRowAction (M * N) e i := by
  simp only [sourceRowAction, Matrix.mul_apply]
  calc
    (∑ j, M i j • ∑ k, N j k • e k) =
        ∑ j, ∑ k, M i j • (N j k • e k) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.smul_sum]
    _ = ∑ j, ∑ k, (M i j * N j k) • e k := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          exact (mul_smul (M i j) (N j k) (e k)).symm
    _ = ∑ k, ∑ j, (M i j * N j k) • e k := by
          exact Finset.sum_comm
    _ = ∑ k, (∑ j, M i j * N j k) • e k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_smul]

theorem sourceRowAction_add (M N : Matrix ι ι B) (e : ι → W) (i : ι) :
    sourceRowAction (M + N) e i =
      sourceRowAction M e i + sourceRowAction N e i := by
  simp [sourceRowAction, add_smul, Finset.sum_add_distrib]

theorem sourceRowAction_sub (M N : Matrix ι ι B) (e : ι → W) (i : ι) :
    sourceRowAction (M - N) e i =
      sourceRowAction M e i - sourceRowAction N e i := by
  simp [sourceRowAction, sub_smul, Finset.sum_sub_distrib]

theorem sourceRowAction_right_scalar
    (a : B) (M : Matrix ι ι B) (e : ι → W) (i : ι) :
    sourceRowAction M (fun j => a • e j) i =
      ∑ j, (M i j * a) • e j := by
  simp only [sourceRowAction]
  apply Finset.sum_congr rfl
  intro j hj
  exact (mul_smul (M i j) a (e j)).symm

theorem sourceRowAction_left_scalar
    (a : B) (M : Matrix ι ι B) (e : ι → W) (i : ι) :
    sourceRowAction (fun p q => a * M p q) e i =
      a • sourceRowAction M e i := by
  rw [smul_sourceRowAction]
  rfl

/-- Move a noncommutative scalar through a source row.  The error is the
entrywise scalar commutator. -/
theorem action_sourceRow_decomp
    (a : B) (M : Matrix ι ι B) (e : ι → W) (i : ι) :
    a • sourceRowAction M e i =
      sourceRowAction M (fun j => a • e j) i +
        sourceRowAction (scalarMatrixCommutator a M) e i := by
  simp only [sourceRowAction, scalarMatrixCommutator]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [sub_smul]
  rw [← mul_smul (M i j) a (e j)]
  rw [← sub_smul, ← add_smul]
  rw [show M i j * a + (a * M i j - M i j * a) = a * M i j by
    noncomm_ring]
  exact (mul_smul a (M i j) (e j)).symm

theorem sourceRowAction_parameter_mul
    (c : B) (hcentral : ∀ a : B, c * a = a * c)
    (M N : Matrix ι ι B) (e : ι → W) (i : ι) :
    sourceRowAction M (fun j => c • sourceRowAction N e j) i =
      c • sourceRowAction (M * N) e i := by
  simp only [sourceRowAction]
  calc
    (∑ j, M i j • (c • ∑ k, N j k • e k)) =
        ∑ j, c • (M i j • ∑ k, N j k • e k) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← mul_smul (M i j) c,
            ← hcentral (M i j)]
          exact mul_smul c (M i j) _
    _ = c • ∑ j, M i j • ∑ k, N j k • e k := by
          rw [Finset.smul_sum]
    _ = c • sourceRowAction (M * N) e i := by
          congr 1
          exact sourceRowAction_mul M N e i

theorem sourceRowAction_fun_add
    (M : Matrix ι ι B) (f g : ι → W) (i : ι) :
    sourceRowAction M (fun j => f j + g j) i =
      sourceRowAction M f i + sourceRowAction M g i := by
  simp [sourceRowAction, Finset.sum_add_distrib, add_smul]

theorem action_parameter_comm
    (c a : B) (hcentral : ∀ b : B, c * b = b * c) (w : W) :
    a • (c • w) = c • (a • w) := by
  rw [← mul_smul, ← hcentral a]
  exact mul_smul c a w

/-- Expanding one operator acting on the first-order source equation for a
second operator. -/
theorem action_on_source_equation
    (c x : B) (hcentral : ∀ a : B, c * a = a * c)
    (hc2 : c * c = 0)
    (A Bm Gamma Theta : Matrix ι ι B) (e : ι → W)
    (hx : ∀ j, x • e j = sourceRowAction A e j +
      c • sourceRowAction Gamma e j) (i : ι) :
    x • (sourceRowAction Bm e i + c • sourceRowAction Theta e i) =
      sourceRowAction (Bm * A) e i + c • sourceRowAction (Bm * Gamma) e i +
        sourceRowAction (scalarMatrixCommutator x Bm) e i +
        c • sourceRowAction (Theta * A) e i +
        c • sourceRowAction (scalarMatrixCommutator x Theta) e i := by
  have hdouble (w : W) : c • (c • w) = 0 := by
    rw [← mul_smul c c, hc2, zero_smul]
  have hxe : (fun j => x • e j) =
      (fun j => sourceRowAction A e j + c • sourceRowAction Gamma e j) := by
    funext j
    exact hx j
  calc
    x • (sourceRowAction Bm e i + c • sourceRowAction Theta e i) =
        x • sourceRowAction Bm e i +
          x • (c • sourceRowAction Theta e i) := by
          simp only [smul_add]
    _ = (sourceRowAction Bm (fun j => x • e j) i +
          sourceRowAction (scalarMatrixCommutator x Bm) e i) +
        c • (sourceRowAction Theta (fun j => x • e j) i +
          sourceRowAction (scalarMatrixCommutator x Theta) e i) := by
          rw [action_sourceRow_decomp,
            action_parameter_comm c x hcentral,
            action_sourceRow_decomp]
    _ = (sourceRowAction Bm (fun j => sourceRowAction A e j +
          c • sourceRowAction Gamma e j) i +
          sourceRowAction (scalarMatrixCommutator x Bm) e i) +
        c • (sourceRowAction Theta (fun j => sourceRowAction A e j +
          c • sourceRowAction Gamma e j) i +
          sourceRowAction (scalarMatrixCommutator x Theta) e i) := by
          rw [hxe]
    _ = sourceRowAction (Bm * A) e i + c • sourceRowAction (Bm * Gamma) e i +
          sourceRowAction (scalarMatrixCommutator x Bm) e i +
          c • sourceRowAction (Theta * A) e i +
          c • sourceRowAction (scalarMatrixCommutator x Theta) e i := by
          rw [sourceRowAction_fun_add, sourceRowAction_fun_add,
            sourceRowAction_mul,
            sourceRowAction_parameter_mul c hcentral Bm Gamma e i,
            sourceRowAction_mul,
            sourceRowAction_parameter_mul c hcentral Theta Gamma e i]
          simp only [smul_add, hdouble, zero_add, add_zero]
          abel

/-- The matrix appearing after the parameter has been removed from the
commutator expansion.  The two entrywise scalar commutators are omitted because
they vanish under every commutative ring specialization. -/
def sourceExpansionMatrix
    (X Y Omega : Matrix ι ι B)
    (A Bm Gamma Theta : Matrix ι ι B) : Matrix ι ι B :=
  X - Y + Omega + (Bm * Gamma + Theta * A - A * Theta - Gamma * Bm)

/-- The unspecialized source-row matrix produced by the commutator expansion.
The two entrywise scalar commutators disappear only after applying a
commutative specialization. -/
def fullSourceExpansionMatrix
    (x y : B) (X Y Omega : Matrix ι ι B)
    (A Bm Gamma Theta : Matrix ι ι B) : Matrix ι ι B :=
  sourceExpansionMatrix X Y Omega A Bm Gamma Theta +
    scalarMatrixCommutator x Theta - scalarMatrixCommutator y Gamma

theorem map_fullSourceExpansionMatrix
    (f : B →+* Abar) (x y : B) (X Y Omega : Matrix ι ι B)
    (A Bm Gamma Theta : Matrix ι ι B) (i j : ι) :
    f (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta i j) =
      f (sourceExpansionMatrix X Y Omega A Bm Gamma Theta i j) := by
  simp [fullSourceExpansionMatrix, sourceExpansionMatrix,
    scalarMatrixCommutator, map_sub, mul_comm]

/-- After a commutative specialization, the source expansion has zero trace
when the three residue matrices are strictly upper triangular.  This is an
algebraic trace statement for the displayed source expansion; it does not
identify that expansion with the induced action on the residual module. -/
theorem sourceExpansionMatrix_map_trace_eq_zero
    (f : B →+* Abar)
    (X Y Omega A Bm Gamma Theta : Matrix ι ι B)
    (hX : IsStrictUpperTriangularOver X)
    (hY : IsStrictUpperTriangularOver Y)
    (hOmega : IsStrictUpperTriangularOver Omega) :
    Matrix.trace
      ((sourceExpansionMatrix X Y Omega A Bm Gamma Theta).map f) = 0 := by
  have hR : IsStrictUpperTriangularOver (X - Y + Omega) := by
    intro i j hji
    simp [hX i j hji, hY i j hji, hOmega i j hji]
  have hRmap : IsStrictUpperTriangularOver
      ((X - Y + Omega).map f) := by
    intro i j hji
    simp [Matrix.map_apply, hR i j hji]
  have htraceR : Matrix.trace ((X - Y + Omega).map f) = 0 := by
    rw [Matrix.trace]
    apply Finset.sum_eq_zero
    intro i _hi
    exact hRmap i i le_rfl
  have htraceComm (M N : Matrix ι ι B) :
      Matrix.trace ((M * N - N * M).map f) = 0 := by
    have hmap : (M * N - N * M).map f =
        M.map f * N.map f - N.map f * M.map f := by
      ext i j
      simp [Matrix.map_apply, Matrix.mul_apply]
    rw [hmap, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  calc
    Matrix.trace ((sourceExpansionMatrix X Y Omega A Bm Gamma Theta).map f) =
        Matrix.trace ((X - Y + Omega).map f) +
          Matrix.trace ((Bm * Gamma + Theta * A - A * Theta - Gamma * Bm).map f) := by
      rw [sourceExpansionMatrix]
      have hmap :
          ((X - Y + Omega) +
            (Bm * Gamma + Theta * A - A * Theta - Gamma * Bm)).map f =
          (X - Y + Omega).map f +
            (Bm * Gamma + Theta * A - A * Theta - Gamma * Bm).map f := by
        ext i j
        simp [Matrix.map_apply]
      rw [hmap, Matrix.trace_add]
    _ = 0 +
          Matrix.trace ((Bm * Gamma + Theta * A - A * Theta - Gamma * Bm).map f) := by
      rw [htraceR]
    _ = 0 := by
      have hdecomp : Bm * Gamma + Theta * A - A * Theta - Gamma * Bm =
          (Bm * Gamma - Gamma * Bm) + (Theta * A - A * Theta) := by
        abel
      rw [hdecomp]
      have hmap :
          ((Bm * Gamma - Gamma * Bm) + (Theta * A - A * Theta)).map f =
            (Bm * Gamma - Gamma * Bm).map f +
              (Theta * A - A * Theta).map f := by
        ext i j
        simp [Matrix.map_apply]
      rw [hmap, Matrix.trace_add, htraceComm, htraceComm]
      simp

theorem rowAction_congr
    (M N : Matrix ι ι B) (e : ι → W) (i : ι)
    (h : ∀ p q, M p q = N p q) :
    sourceRowAction M e i = sourceRowAction N e i := by
  simp only [sourceRowAction]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h i j]

/-- The exact source-row commutator expansion before specialization. -/
theorem commutator_on_source_equations
    (c x y z : B) (hcentral : ∀ a : B, c * a = a * c)
    (hc2 : c * c = 0)
    (hxy : x * y - y * x = c * z)
    (A Bm Gamma Theta X Y Omega : Matrix ι ι B) (e : ι → W)
    (hx : ∀ i, x • e i = sourceRowAction A e i +
      c • sourceRowAction Gamma e i)
    (hy : ∀ i, y • e i = sourceRowAction Bm e i +
      c • sourceRowAction Theta e i)
    (hX : ∀ i j, c * X i j = scalarMatrixCommutator x Bm i j)
    (hY : ∀ i j, c * Y i j = scalarMatrixCommutator y A i j)
    (hOmega : ∀ i j, c * Omega i j =
      sourceMatrixCommutator Bm A i j) (i : ι) :
    c • (z • e i) = c • sourceRowAction
      (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta) e i := by
  have hxy_action : x • (y • e i) =
      sourceRowAction (Bm * A) e i + c • sourceRowAction (Bm * Gamma) e i +
        sourceRowAction (scalarMatrixCommutator x Bm) e i +
        c • sourceRowAction (Theta * A) e i +
        c • sourceRowAction (scalarMatrixCommutator x Theta) e i := by
    rw [hy i]
    exact action_on_source_equation c x hcentral hc2 A Bm Gamma Theta e hx i
  have hyx_action : y • (x • e i) =
      sourceRowAction (A * Bm) e i + c • sourceRowAction (A * Theta) e i +
        sourceRowAction (scalarMatrixCommutator y A) e i +
        c • sourceRowAction (Gamma * Bm) e i +
        c • sourceRowAction (scalarMatrixCommutator y Gamma) e i := by
    rw [hx i]
    exact action_on_source_equation c y hcentral hc2 Bm A Theta Gamma e hy i
  have hXrow : sourceRowAction (scalarMatrixCommutator x Bm) e i =
      c • sourceRowAction X e i := by
    calc
      sourceRowAction (scalarMatrixCommutator x Bm) e i =
          sourceRowAction (fun p q => c * X p q) e i := by
            apply rowAction_congr
            intro p q
            exact (hX p q).symm
      _ = c • sourceRowAction X e i := sourceRowAction_left_scalar c X e i
  have hYrow : sourceRowAction (scalarMatrixCommutator y A) e i =
      c • sourceRowAction Y e i := by
    calc
      sourceRowAction (scalarMatrixCommutator y A) e i =
          sourceRowAction (fun p q => c * Y p q) e i := by
            apply rowAction_congr
            intro p q
            exact (hY p q).symm
      _ = c • sourceRowAction Y e i := sourceRowAction_left_scalar c Y e i
  have hOmega_row : sourceRowAction (sourceMatrixCommutator Bm A) e i =
      c • sourceRowAction Omega e i := by
    calc
      sourceRowAction (sourceMatrixCommutator Bm A) e i =
          sourceRowAction (fun p q => c * Omega p q) e i := by
            apply rowAction_congr
            intro p q
            exact (hOmega p q).symm
      _ = c • sourceRowAction Omega e i := sourceRowAction_left_scalar c Omega e i
  calc
    c • (z • e i) = (c * z) • e i := (mul_smul c z _).symm
    _ = (x * y - y * x) • e i := by rw [hxy]
    _ = x • (y • e i) - y • (x • e i) := by
      rw [sub_smul, mul_smul, mul_smul]
    _ = (sourceRowAction (Bm * A) e i + c • sourceRowAction (Bm * Gamma) e i +
          sourceRowAction (scalarMatrixCommutator x Bm) e i +
          c • sourceRowAction (Theta * A) e i +
          c • sourceRowAction (scalarMatrixCommutator x Theta) e i) -
        (sourceRowAction (A * Bm) e i + c • sourceRowAction (A * Theta) e i +
          sourceRowAction (scalarMatrixCommutator y A) e i +
          c • sourceRowAction (Gamma * Bm) e i +
          c • sourceRowAction (scalarMatrixCommutator y Gamma) e i) := by
      rw [hxy_action, hyx_action]
    _ = c • sourceRowAction
        (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta) e i := by
      have hBArow : sourceRowAction (Bm * A) e i -
          sourceRowAction (A * Bm) e i = c • sourceRowAction Omega e i := by
        calc
          sourceRowAction (Bm * A) e i - sourceRowAction (A * Bm) e i =
              sourceRowAction (sourceMatrixCommutator Bm A) e i := by
                simp [sourceMatrixCommutator, sourceRowAction_sub]
          _ = c • sourceRowAction Omega e i := hOmega_row
      rw [hXrow, hYrow]
      calc
        (sourceRowAction (Bm * A) e i + c • sourceRowAction (Bm * Gamma) e i +
            c • sourceRowAction X e i + c • sourceRowAction (Theta * A) e i +
            c • sourceRowAction (scalarMatrixCommutator x Theta) e i) -
          (sourceRowAction (A * Bm) e i + c • sourceRowAction (A * Theta) e i +
            c • sourceRowAction Y e i + c • sourceRowAction (Gamma * Bm) e i +
            c • sourceRowAction (scalarMatrixCommutator y Gamma) e i) =
          (sourceRowAction (Bm * A) e i - sourceRowAction (A * Bm) e i) +
            (c • sourceRowAction (Bm * Gamma) e i - c • sourceRowAction (A * Theta) e i +
              c • sourceRowAction X e i - c • sourceRowAction Y e i +
              c • sourceRowAction (Theta * A) e i - c • sourceRowAction (Gamma * Bm) e i +
              c • sourceRowAction (scalarMatrixCommutator x Theta) e i -
              c • sourceRowAction (scalarMatrixCommutator y Gamma) e i) := by
                abel
        _ = c • sourceRowAction
            (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta) e i := by
          rw [hBArow]
          simp [fullSourceExpansionMatrix, sourceExpansionMatrix,
            sourceRowAction_add, sourceRowAction_sub, neg_one_smul]
          abel_nf
          simp [neg_one_smul]
          abel

theorem rho_sourceRowAction
    (f : B →+* Abar) (rho : W →+ V)
    (hact : ∀ a w, rho (a • w) = f a • rho w)
    (M : Matrix ι ι B) (e : ι → W) (i : ι) :
    rho (sourceRowAction M e i) =
      ∑ j, f (M i j) • rho (e j) := by
  simp only [sourceRowAction, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact hact (M i j) (e j)

/-- After exact parameter descent, the commutator cofactor acts on the special
fibre by the specialized source expansion.  This is the precise action-level
conclusion needed before any trace comparison. -/
theorem rho_commutator_on_source_equations
    (c x y z : B) (f : B →+* Abar) (rho : W →+ V)
    (hcentral : ∀ a : B, c * a = a * c)
    (hc2 : c * c = 0) (hfc : f c = 0)
    (hxy : x * y - y * x = c * z)
    (hact : ∀ a w, rho (a • w) = f a • rho w)
    (hExact : AddMonoidHom.ker
        (parameterAct (W := W) c) =
      AddMonoidHom.range (parameterAct (W := W) c))
    (A Bm Gamma Theta X Y Omega : Matrix ι ι B) (e : ι → W)
    (hx : ∀ i, x • e i = sourceRowAction A e i +
      c • sourceRowAction Gamma e i)
    (hy : ∀ i, y • e i = sourceRowAction Bm e i +
      c • sourceRowAction Theta e i)
    (hX : ∀ i j, c * X i j = scalarMatrixCommutator x Bm i j)
    (hY : ∀ i j, c * Y i j = scalarMatrixCommutator y A i j)
    (hOmega : ∀ i j, c * Omega i j =
      sourceMatrixCommutator Bm A i j) (i : ι) :
    f z • rho (e i) =
      ∑ j, f (sourceExpansionMatrix X Y Omega A Bm Gamma Theta i j) •
        rho (e j) := by
  have hkill : ∀ w : W, c • w = 0 → rho w = 0 := by
    intro w hw
    have hwker : w ∈ AddMonoidHom.ker
        (parameterAct (W := W) c) := by
      exact AddMonoidHom.mem_ker.mpr hw
    rw [hExact] at hwker
    obtain ⟨v, hv⟩ := hwker
    rw [← hv]
    change rho (c • v) = 0
    rw [hact, hfc, zero_smul]
  have hdouble := commutator_on_source_equations c x y z hcentral hc2 hxy
      A Bm Gamma Theta X Y Omega e hx hy hX hY hOmega i
  have hparameter : c •
      (z • e i - sourceRowAction
        (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta) e i) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr hdouble
  have hdesc := hkill _ hparameter
  have hdesc' : rho (z • e i) =
      rho (sourceRowAction
        (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta) e i) := by
    rw [map_sub] at hdesc
    exact sub_eq_zero.mp hdesc
  have hexpansion : f z • rho (e i) =
      ∑ j, f (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta i j) •
        rho (e j) := by
    calc
      f z • rho (e i) = rho (z • e i) := (hact z (e i)).symm
      _ = rho (sourceRowAction
          (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta) e i) := hdesc'
      _ = _ := rho_sourceRowAction f rho hact _ _ _
  calc
    f z • rho (e i) =
        ∑ j, f (fullSourceExpansionMatrix x y X Y Omega A Bm Gamma Theta i j) •
          rho (e j) := hexpansion
    _ = ∑ j, f (sourceExpansionMatrix X Y Omega A Bm Gamma Theta i j) •
        rho (e j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_fullSourceExpansionMatrix]


end

end Stafford38.Characteristic.SourceActionCommutatorExpansion
