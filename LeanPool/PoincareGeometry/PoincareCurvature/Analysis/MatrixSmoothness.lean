/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Smoothness of the matrix determinant, adjugate, and nonsingular inverse

This module records the *base-polymorphic, arbitrary-order* smoothness of the matrix
determinant, adjugate, and (nonsingular) inverse, viewed as maps on the finite-dimensional
real normed space `ι → ι → ℝ` of matrix entries.

The determinant and adjugate are polynomial maps of the entries, hence `ContDiff ℝ n` for every
order `n`; the inverse is `A⁻¹ = (det A)⁻¹ • adjugate A`, so it is `ContMDiffOn` on the locus where
the determinant is nonzero.

## Motivation

The spatial Riemannian *raising* machinery reduces raising a co-vector to inverting the local-frame
Gram matrix, and its existing smoothness support
(`CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv`) is proved only for a fixed base
manifold `M` and at the single order `2`.  Running that argument jointly over the *space-time* base
`ℝ × M` — the joint `(t, x)` smoothness of the Ricci–DeTurck gauge field for a genuinely
time-dependent metric — requires exactly these facts for an *arbitrary* base manifold and at
*arbitrary* order.  This module isolates that field-independent linear-algebra core so it can be
reused verbatim over any base.
-/

@[expose] public section

open scoped Manifold
open Matrix

namespace PoincareCurvature.MatrixSmoothness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : WithTop ℕ∞}

/-- The determinant, as a function of the matrix entries, is `ContDiff ℝ n` for every order `n`
(it is a polynomial in the entries). -/
theorem contDiff_det :
    ContDiff ℝ n (fun A : ι → ι → ℝ => (show Matrix ι ι ℝ from A).det) := by
  classical
  let f : (ι → ι → ℝ) → ℝ :=
    fun A => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i
  have hf : ContDiff ℝ n f := by
    rw [contDiff_iff_contDiffAt]
    intro A
    refine ContDiffAt.sum ?_
    intro σ _
    refine (contDiffAt_const : ContDiffAt ℝ n
      (fun _ : ι → ι → ℝ => ((Equiv.Perm.sign σ : ℤ) : ℝ)) A).mul ?_
    refine contDiffAt_prod ?_
    intro i _
    simpa using
      (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (n := n) (i := σ i) (j := i)).contDiffAt
  have hEq : f = fun A : ι → ι → ℝ => Matrix.det (show Matrix ι ι ℝ from A) := by
    funext A
    symm
    simpa using (Matrix.det_apply' (show Matrix ι ι ℝ from A))
  simpa [hEq] using hf

/-- Updating a single row of a matrix with a fixed vector is `ContDiff ℝ n` in the entries. -/
theorem contDiff_updateRow (i j : ι) :
    ContDiff ℝ n
      (fun A : ι → ι → ℝ =>
        (show ι → ι → ℝ from
          Matrix.updateRow (show Matrix ι ι ℝ from A) j (Pi.single i (1 : ℝ)))) := by
  classical
  rw [contDiff_pi]
  intro k
  change ContDiff ℝ n (fun A : ι → ι → ℝ => Function.update A j (Pi.single i (1 : ℝ)) k)
  by_cases hk : k = j
  · subst hk
    simpa [Function.update] using
      (contDiff_const : ContDiff ℝ n (fun _ : ι → ι → ℝ => (Pi.single i (1 : ℝ) : ι → ℝ)))
  · simpa [Function.update, hk] using
      (contDiff_apply (𝕜 := ℝ) (E := ι → ℝ) (n := n) (i := k))

/-- The adjugate, as a function of the matrix entries, is `ContDiff ℝ n` for every order `n`
(each entry is a signed minor, hence a polynomial in the entries). -/
theorem contDiff_adjugate :
    ContDiff ℝ n
      (fun A : ι → ι → ℝ =>
        (show ι → ι → ℝ from Matrix.adjugate (show Matrix ι ι ℝ from A))) := by
  classical
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  change ContDiff ℝ n (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j)
  have hEq :
      (fun A : ι → ι → ℝ => Matrix.adjugate (Matrix.of A) i j) =
        (fun A : ι → ι → ℝ => ((Matrix.of A).updateRow j (Pi.single i (1 : ℝ))).det) := by
    funext A
    exact Matrix.adjugate_apply (Matrix.of A) i j
  rw [hEq]
  convert (contDiff_det (ι := ι) (n := n)).comp
    (contDiff_updateRow (ι := ι) (n := n) i j) using 1 <;> rfl

section Manifold

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The determinant of a `ContMDiffOn` family of matrices is `ContMDiffOn` (as a scalar function). -/
theorem contMDiffOn_matrixDet {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u) :
    ContMDiffOn J 𝓘(ℝ) n (fun x => (show Matrix ι ι ℝ from A x).det) u := by
  intro x hx
  exact (contDiff_det (ι := ι) (n := n)).comp_contMDiffWithinAt (hA x hx)

/-- The adjugate of a `ContMDiffOn` family of matrices is `ContMDiffOn`. -/
theorem contMDiffOn_matrixAdjugate {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u) :
    ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n
      (fun x => (show ι → ι → ℝ from Matrix.adjugate (show Matrix ι ι ℝ from A x))) u := by
  intro x hx
  exact (contDiff_adjugate (ι := ι) (n := n)).comp_contMDiffWithinAt (hA x hx)

/-- The reciprocal determinant of a `ContMDiffOn` family of matrices is `ContMDiffOn` on the locus
where the determinant is nonzero. -/
theorem contMDiffOn_matrixDetInv {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u)
    (hdet : ∀ x ∈ u, (show Matrix ι ι ℝ from A x).det ≠ 0) :
    ContMDiffOn J 𝓘(ℝ) n (fun x => ((show Matrix ι ι ℝ from A x).det)⁻¹) u :=
  (contMDiffOn_matrixDet (J := J) (n := n) hA).inv₀ hdet

/-- **Smoothness of the nonsingular matrix inverse.**  If `A : N → (ι → ι → ℝ)` is a `ContMDiffOn`
family of matrices over an arbitrary base and its determinant is nonzero throughout, then the
entrywise inverse `x ↦ (A x)⁻¹` is `ContMDiffOn` at the same order.

This is the base-polymorphic, arbitrary-order generalisation of the spatial, order-`2`
`CovariantDerivative.contMDiffOn_localFrameGramMatrix_inv`, and is the linear-algebra tool
underlying joint space-time Riemannian raising. -/
theorem contMDiffOn_matrixInv {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u)
    (hdet : ∀ x ∈ u, (show Matrix ι ι ℝ from A x).det ≠ 0) :
    ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n
      (fun x => (show ι → ι → ℝ from ((show Matrix ι ι ℝ from A x)⁻¹ : Matrix ι ι ℝ))) u := by
  refine ContMDiffOn.congr
    (ContMDiffOn.smul
      (contMDiffOn_matrixDetInv (J := J) (n := n) hA hdet)
      (contMDiffOn_matrixAdjugate (J := J) (n := n) hA)) ?_
  intro x hx
  change (show Matrix ι ι ℝ from A x)⁻¹ =
    ((show Matrix ι ι ℝ from A x).det)⁻¹ •
      Matrix.adjugate (show Matrix ι ι ℝ from A x)
  rw [Matrix.inv_def, Ring.inverse_eq_inv]

omit [DecidableEq ι] in
/-- The `(i, j)` entry of a `ContMDiffOn` family of matrices is a `ContMDiffOn` scalar function. -/
theorem contMDiffOn_matrixEntry {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u) (i j : ι) :
    ContMDiffOn J 𝓘(ℝ) n (fun x => A x i j) u := by
  intro x hx
  exact (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (n := n) (i := i) (j := j)).comp_contMDiffWithinAt
    (hA x hx)

omit [DecidableEq ι] in
/-- The `j`-th component of a `ContMDiffOn` family of vectors is a `ContMDiffOn` scalar function. -/
theorem contMDiffOn_vecEntry {b : N → (ι → ℝ)} {u : Set N}
    (hb : ContMDiffOn J 𝓘(ℝ, ι → ℝ) n b u) (j : ι) :
    ContMDiffOn J 𝓘(ℝ) n (fun x => b x j) u := by
  intro x hx
  exact (contDiff_apply (𝕜 := ℝ) (E := ℝ) (n := n) (i := j)).comp_contMDiffWithinAt (hb x hx)

/-- **Smoothness of the matrix–vector product.**  If `A : N → (ι → ι → ℝ)` and `b : N → (ι → ℝ)` are
`ContMDiffOn` families over an arbitrary base, then `x ↦ (A x) *ᵥ (b x)` is `ContMDiffOn`. -/
theorem contMDiffOn_mulVec {A : N → (ι → ι → ℝ)} {b : N → (ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u)
    (hb : ContMDiffOn J 𝓘(ℝ, ι → ℝ) n b u) :
    ContMDiffOn J 𝓘(ℝ, ι → ℝ) n
      (fun x => (show ι → ℝ from (show Matrix ι ι ℝ from A x).mulVec (b x))) u := by
  classical
  rw [contMDiffOn_pi_space]
  intro i
  have hsum : ∀ s : Finset ι,
      ContMDiffOn J 𝓘(ℝ) n (fun x => s.sum fun j => A x i j * b x j) u := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (contMDiffOn_const : ContMDiffOn J 𝓘(ℝ) n (fun _ : N => (0 : ℝ)) u)
    · intro j s hj hs
      have hfirst : ContMDiffOn J 𝓘(ℝ) n (fun x => A x i j * b x j) u := by
        refine ContMDiffOn.congr
          (ContMDiffOn.smul (contMDiffOn_matrixEntry (J := J) (n := n) hA i j)
            (contMDiffOn_vecEntry (J := J) (n := n) hb j)) ?_
        intro x hx
        simp [Pi.smul_apply', smul_eq_mul]
      refine ContMDiffOn.congr (hfirst.add hs) ?_
      intro x hx
      simp [Finset.sum_insert, hj]
  refine ContMDiffOn.congr (hsum Finset.univ) ?_
  intro x hx
  rfl

/-- **Smoothness of the linear solve `A⁻¹ *ᵥ b` (Cramer solve).**  On the locus where `A` is
nonsingular, the solution `x ↦ (A x)⁻¹ *ᵥ (b x)` of the linear system `(A x) y = b x` is
`ContMDiffOn`.  This is exactly the shape of the raised-covector coefficient formula
`cᵢ = ∑ⱼ (Gram⁻¹)ᵢⱼ · ω(frameⱼ)`, so it packages `contMDiffOn_matrixInv` for use in joint
space-time Riemannian raising. -/
theorem contMDiffOn_matrixInv_mulVec {A : N → (ι → ι → ℝ)} {b : N → (ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u)
    (hb : ContMDiffOn J 𝓘(ℝ, ι → ℝ) n b u)
    (hdet : ∀ x ∈ u, (show Matrix ι ι ℝ from A x).det ≠ 0) :
    ContMDiffOn J 𝓘(ℝ, ι → ℝ) n
      (fun x => (show ι → ℝ from ((show Matrix ι ι ℝ from A x)⁻¹ : Matrix ι ι ℝ).mulVec (b x))) u :=
  contMDiffOn_mulVec (J := J) (n := n)
    (contMDiffOn_matrixInv (J := J) (n := n) hA hdet) hb

omit [DecidableEq ι] in
/-- The transpose of a `ContMDiffOn` family of matrices is `ContMDiffOn` (each entry of the
transpose is an entry of the original matrix). -/
theorem contMDiffOn_transpose {A : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u) :
    ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n
      (fun x => (show ι → ι → ℝ from (show Matrix ι ι ℝ from A x)ᵀ)) u := by
  rw [contMDiffOn_pi_space]
  intro i
  rw [contMDiffOn_pi_space]
  intro j
  change ContMDiffOn J 𝓘(ℝ) n (fun x => A x j i) u
  exact contMDiffOn_matrixEntry (J := J) (n := n) hA j i

/-- **Smoothness of the matrix–matrix product.**  If `A B : N → (ι → ι → ℝ)` are `ContMDiffOn`
families of matrices over an arbitrary base, then `x ↦ (A x) * (B x)` is `ContMDiffOn` at the same
order.  Together with `contMDiffOn_matrixInv` and `contMDiffOn_mulVec` this completes the elementary
matrix calculus (products, inverses, contractions) needed to run local Riemannian tensor formulas —
e.g. Christoffel/curvature contractions `g⁻¹ · (∂g) · g⁻¹` — jointly over the space-time base. -/
theorem contMDiffOn_matrix_mul {A B : N → (ι → ι → ℝ)} {u : Set N}
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A u)
    (hB : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n B u) :
    ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n
      (fun x => (show ι → ι → ℝ from
        (show Matrix ι ι ℝ from A x) * (show Matrix ι ι ℝ from B x))) u := by
  classical
  rw [contMDiffOn_pi_space]
  intro i
  rw [contMDiffOn_pi_space]
  intro k
  have hsum : ∀ s : Finset ι,
      ContMDiffOn J 𝓘(ℝ) n (fun x => s.sum fun j => A x i j * B x j k) u := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (contMDiffOn_const : ContMDiffOn J 𝓘(ℝ) n (fun _ : N => (0 : ℝ)) u)
    · intro j s hj hs
      have hfirst : ContMDiffOn J 𝓘(ℝ) n (fun x => A x i j * B x j k) u := by
        refine ContMDiffOn.congr
          (ContMDiffOn.smul (contMDiffOn_matrixEntry (J := J) (n := n) hA i j)
            (contMDiffOn_matrixEntry (J := J) (n := n) hB j k)) ?_
        intro x hx
        simp [Pi.smul_apply', smul_eq_mul]
      refine ContMDiffOn.congr (hfirst.add hs) ?_
      intro x hx
      simp [Finset.sum_insert, hj]
  refine ContMDiffOn.congr (hsum Finset.univ) ?_
  intro x hx
  change (∑ j, A x i j * B x j k) = ∑ j, A x i j * B x j k
  rfl

/-- **Smoothness of the dot product.**  If `a b : N → (ι → ℝ)` are `ContMDiffOn` families of vectors
over an arbitrary base, then the scalar dot product `x ↦ (a x) ⬝ᵥ (b x)` is `ContMDiffOn`.  This is
the bilinear-pairing building block for scalar tensor contractions (e.g. quadratic forms
`x ↦ (c x) ⬝ᵥ ((A x) *ᵥ (c x))`) over the space-time base. -/
theorem contMDiffOn_dotProduct {a b : N → (ι → ℝ)} {u : Set N}
    (ha : ContMDiffOn J 𝓘(ℝ, ι → ℝ) n a u)
    (hb : ContMDiffOn J 𝓘(ℝ, ι → ℝ) n b u) :
    ContMDiffOn J 𝓘(ℝ) n (fun x => (a x) ⬝ᵥ (b x)) u := by
  classical
  have hsum : ∀ s : Finset ι,
      ContMDiffOn J 𝓘(ℝ) n (fun x => s.sum fun j => a x j * b x j) u := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using (contMDiffOn_const : ContMDiffOn J 𝓘(ℝ) n (fun _ : N => (0 : ℝ)) u)
    · intro j s hj hs
      have hfirst : ContMDiffOn J 𝓘(ℝ) n (fun x => a x j * b x j) u := by
        refine ContMDiffOn.congr
          (ContMDiffOn.smul (contMDiffOn_vecEntry (J := J) (n := n) ha j)
            (contMDiffOn_vecEntry (J := J) (n := n) hb j)) ?_
        intro x hx
        simp [Pi.smul_apply', smul_eq_mul]
      refine ContMDiffOn.congr (hfirst.add hs) ?_
      intro x hx
      simp [Finset.sum_insert, hj]
  refine ContMDiffOn.congr (hsum Finset.univ) ?_
  intro x hx
  rfl

/-- **Smoothness of a coordinate bilinear form.**  If `A : N → (ι → ι → ℝ)` is a `ContMDiffOn`
family of matrices and `u v : N → (ι → ℝ)` are `ContMDiffOn` families of vectors over an arbitrary
base, then the scalar `x ↦ (u x) ⬝ᵥ ((A x) *ᵥ (v x))` is `ContMDiffOn`.  This is exactly the local
coordinate expression `Uᵀ G V` for evaluating a matrix-valued tensor `A` (e.g. the metric readout
`G`) on two vector fields — the tensor-evaluation building block for the joint space-time smoothness
of Gram matrices and one-form pairings. -/
theorem contMDiffOn_bilinForm {A : N → (ι → ι → ℝ)} {u v : N → (ι → ℝ)} {s : Set N}
    (hu : ContMDiffOn J 𝓘(ℝ, ι → ℝ) n u s)
    (hA : ContMDiffOn J 𝓘(ℝ, ι → ι → ℝ) n A s)
    (hv : ContMDiffOn J 𝓘(ℝ, ι → ℝ) n v s) :
    ContMDiffOn J 𝓘(ℝ) n
      (fun x => (u x) ⬝ᵥ (show ι → ℝ from (show Matrix ι ι ℝ from A x) *ᵥ (v x))) s :=
  contMDiffOn_dotProduct (J := J) (n := n) hu
    (contMDiffOn_mulVec (J := J) (n := n) hA hv)

end Manifold

end PoincareCurvature.MatrixSmoothness
